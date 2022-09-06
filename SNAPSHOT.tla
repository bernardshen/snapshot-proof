------------------------------ MODULE SNAPSHOT ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT NumMN, NumClient, FAILNUM, STOP
ASSUME FAILNUM < NumMN

MNs     == 1..NumMN
Clients == (NumMN + 1)..(NumMN + NumClient) 
Nodes   == 1..(NumMN + NumClient)
Master  == NumMN + NumClient + 1

FailRec  == [val |-> -1, commitID |-> -1]
EmptyMsg == [type |-> "E", client |-> -1, rec |-> FailRec]
RecType  == [val : Int, commitID : Int]
MsgType  == [type : STRING, client : Int, rec : RecType]

(*--algorithm SNAPSHOT {
    variable db = [n \in MNs |-> [val|->0, commitID|->0]],
             up = [n \in Nodes |-> TRUE],
             FailNum = FAILNUM,
             Primary = 1,
             Backups = MNs \ {Primary},
             fretInt = [n \in Clients |-> 0],
             fretRec = [n \in Clients |-> FailRec],
             chan    = [n \in (Clients \cup {Master}) |-> <<>>],
             prepareChange = FALSE,
             configID      = [n \in Clients |-> 0],
             clientState   = [n \in Clients |-> 0],
             commitHist    = [n \in Clients |-> <<0>>];
             
    define {
        getVoteMin(voteVal, origVal, swapVal) == IF origVal \in voteVal 
                                        THEN CHOOSE i \in ((voteVal \ {origVal}) \union {swapVal}): (\A j \in ((voteVal \ {origVal}) \union {swapVal}): i <= j)
                                        ELSE -1
        getVoteVal(votes) == {votes[i].val : i \in Backups} 
        getVoteCnt(voteVal, votes) == [i \in voteVal |-> Cardinality(UNION {{j \in Backups: votes[j].val = i}})]
        getMajorityVoteVal(voteVal, voteCnt) == CHOOSE i \in voteVal: (\A j \in voteVal: voteCnt[j] <= voteCnt[i])
        MaxIdxLessThan(_seq, val) == CHOOSE i \in 1..Len(_seq) : 
                                \A j \in 1..Len(_seq): _seq[j] <= val => i >= j
        InsertAfter(_seq, idx, val) == SubSeq(_seq, 1, idx) \o <<val>> \o SubSeq(_seq, idx+1, Len(_seq))
        genNewVal(oldVal, self) == ((oldVal + 1000) \div 1000) * 1000 + self
        aliveSubset(S) == {n \in S: up[n]}
        getFirstAliveIn(S) == IF Cardinality(aliveSubset(S)) > 0 
                              THEN CHOOSE i \in S: up[i] /\ \A j \in aliveSubset(S): i <= j
                              ELSE -1
        buildMsg(_type, _client, _rec) == [ type   |-> _type, 
                                            client |-> _client,
                                            rec    |-> _rec ]
    }
    
    \* RDMA CAS operation
    \* return the original value in the store if the node is up
    \* return -1 to indicate the node failure
    macro CAS(retRec, id, oldRec, newRec) {
        assert oldRec \in RecType /\ newRec \in RecType;
        retRec := IF up[id] THEN db[id] ELSE FailRec;
        if (db[id].val = oldRec.val /\ up[id]) {
            db[id] := newRec;
        };
    }
    
    \* RDMA READ operation
    macro RDMA_READ(id, retRec) {
        retRec := IF up[id] THEN db[id] ELSE FailRec;
    } 
    
    \* synchronized network send
    macro send(des, msg) {
        assert msg \in MsgType;
        chan[des] := Append(chan[des], msg);
    }
    
    \* synchronized network recv
    macro recv(msg) {
        await Len(chan[self]) > 0;
        msg := Head(chan[self]);
        chan[self] := Tail(chan[self]);
    }
    
    \* SNAPSHOT_Read operation
    procedure SNAPSHOT_Read()
    variable retRec = FailRec, msg = EmptyMsg;
    {
    R_ST:
        RDMA_READ(Primary, retRec);
        if (retRec.val = -1) {
            send(Master, buildMsg("Req", self, FailRec));
            clientState[self] := -1;
    R_recv:
            recv(msg);
            retRec := msg.rec;
            clientState[self] := 0;
        };
    R_fini:
        fretRec[self] := retRec;
        return
    }
    
    \* Evalute rules used by SNAPSHOT_Write
    procedure EvalRules(votes = [n \in Backups |-> FailRec], origRec = FailRec, swapRec = FailRec)
    variable voteVal = getVoteVal(votes),
             voteCnt = getVoteCnt(voteVal, votes),
             majVoteVal = -1, tmpWin = -3, checkRec = FailRec;
    {
    EVAL_ST1:
        assert origRec \in RecType /\ swapRec \in RecType;
        majVoteVal := getMajorityVoteVal(voteVal, voteCnt);
        if (-1 \in voteVal) { tmpWin := -1; }
        else if (voteCnt[majVoteVal] = Cardinality(Backups)) {
            tmpWin := IF majVoteVal = origRec.val THEN 0 ELSE 3;
        } else if (2 * voteCnt[majVoteVal] > Cardinality(Backups)) {
            tmpWin := IF majVoteVal = origRec.val THEN 1 ELSE 3;
        };
        if (tmpWin = -3) {
    EVAL_recheck:
            call SNAPSHOT_Read();
    EVAL_recheck_rep:
            checkRec := fretRec[self];
    EVAL_ST2:
            if (checkRec.val = swapRec.val) {
                tmpWin := 5;
            } else if (checkRec.val # origRec.val) { 
                tmpWin := 4; 
            } else if (getVoteMin(voteVal, origRec.val, swapRec.val) = swapRec.val) {
                tmpWin := 2;
            } else { 
                tmpWin := 3; 
            }
        };
    EVAL_FINI:
        fretInt[self] := tmpWin;
        return
    }
    
    \* SNAPSHOT_Write operation
    procedure SNAPSHOT_Write()
    variable origRec = FailRec, swapRec = FailRec, retRec = FailRec, 
             votes = [n \in MNs |-> FailRec],
             Q = {}, committed = FALSE, win = -1, curCommitID = -1,
             tmpMsg = EmptyMsg, numRetry = 2;
    {
    W_read:
        call SNAPSHOT_Read();
    W_read_fini:
        origRec  := fretRec[self];
        swapRec  := [val      |-> genNewVal(origRec.val, self), 
                     commitID |-> origRec.commitID + 1];           \* construct a new value => each round there will be only one winner
        curCommitID := origRec.commitID;                       \* record current commitID
        \* CAS all backups
        Q := Backups;
        if (Q = {}) {
            CAS(retRec, Primary, origRec, swapRec);
            commitHist[self] := IF retRec.val = origRec.val
                                THEN Append(commitHist[self], curCommitID + 1)
                                ELSE commitHist[self];
            fretInt[self] := IF retRec.val = origRec.val THEN 0 ELSE -1;
    W_return_cas_primary:
            return;
        };
    W_cas_bk:
        while (Q # {}) {
            with (p \in Q) {
                CAS(votes[p], p, origRec, swapRec);
                Q := Q \ {p};
            }
        };
        \* Evalute rules
        call EvalRules(votes, origRec, swapRec);
    W_eval_rules:
        win := fretInt[self];
        if (win = 0) {
            curCommitID := curCommitID + 1;
            commitHist[self] := Append(commitHist[self], curCommitID);
    W_cas_primary_1:
            CAS(retRec, Primary, origRec, swapRec);
        } else if (win = 1 \/ win  = 2) {
            curCommitID := curCommitID + 1;
            commitHist[self] := Append(commitHist[self], curCommitID);
            db := [ n \in MNs |-> IF n \in Backups /\ up[n]
                                        THEN swapRec ELSE db[n]   ];
    W_cas_primary_2:
            CAS(retRec, Primary, origRec, swapRec);
        } else if (win = 3) {
    W_wait_commit:
            while (committed = FALSE) {
                RDMA_READ(Primary, retRec);
                if (retRec.val = -1 \/ retRec.val = origRec.val) {
                    \* retry the operation if primary is failed or the origRec remains old
                    fretInt[self] := -1;
    W_retry_return:
                    return;
                } else {
                    committed := TRUE;
                    curCommitID := IF retRec.val = swapRec.val
                                   THEN curCommitID + 1 ELSE curCommitID;
                    commitHist[self] := Append(commitHist[self], curCommitID);
                }
            }
        } else if (win = 4 \/ win = 5) {
            curCommitID := IF win = 4 THEN curCommitID ELSE curCommitID + 1;
            commitHist[self] := Append(commitHist[self], curCommitID);
        } else {
            \* deal with backup failure
            assert win = -1;
            send(Master, buildMsg("Req", self, FailRec));
            clientState[self] := -1;
    W_bk_failure_wait:
            recv(tmpMsg);
            clientState[self] := 0;
            retRec := tmpMsg.rec;
            curCommitID := IF retRec.val = swapRec.val THEN curCommitID + 1 ELSE curCommitID;
            commitHist[self] := Append(commitHist[self], curCommitID);
        };
    W_fini_0:
        fretInt[self] := 0;
        return;
    }
    
    fair process (c \in Clients)
    variable cntr = 0, retVal = -1; 
    {
    C:
        while (cntr < STOP) {
            if (prepareChange = TRUE) {
                clientState[self] := -1;
    C_wait_prepare:
                await prepareChange = FALSE;
                clientState[self] := 0;
                configID[self] := configID[self] + 1;
            };
    C_start_write:
            clientState[self] := 0;
            call SNAPSHOT_Write();
    C_after_write:
            retVal := fretInt[self];
            cntr := IF retVal = -1 THEN cntr ELSE cntr + 1;
        };
        clientState[self] := -1;
    }
    
    fair process (mn \in MNs)
    {
    MN:
        while (FailNum > 0) {
            if (FailNum > 0 /\ up[self]) {
                up[self] := FALSE;
                FailNum  := FailNum - 1;
            };
        }
    }
    
    fair process (m \in {Master})
    variable firstAlive = -1, activeNodes = {}, 
             replyMsg = EmptyMsg, globalConfig = 0;
    {
    MASTER:+
        while (TRUE) {
            if (\E n \in ({Primary} \union Backups): up[n] = FALSE) {
                \* 1. broadcast prepare membership change and wait all reply 
                \*      => should be same as disconnect clients that do not reply
                prepareChange := TRUE;
    M_wait_stop:+
                await \A i \in Clients: clientState[i] = -1;
                \* 2. make slots consistent and reply to clients
    M_stopped:+
                activeNodes := aliveSubset({Primary} \union Backups);
                firstAlive  := IF getFirstAliveIn(Backups) = -1 
                               THEN getFirstAliveIn(MNs) ELSE getFirstAliveIn(Backups);
                assert firstAlive \in MNs;
                if (\E i, j \in (activeNodes \cap MNs): db[i].val # db[j].val) {
                    db := [ n \in MNs |-> IF up[n] THEN db[firstAlive] ELSE db[n] ];
                };
                Primary := IF up[Primary] THEN Primary ELSE firstAlive;
                Backups := (activeNodes \cap MNs) \ {Primary};
                globalConfig := globalConfig + 1;
                replyMsg := buildMsg("Rep", Master, db[firstAlive]);
    M_reply_msg:
                while (Len(chan[self]) # 0) {
                    send(Head(chan[self]).client, replyMsg);
    M_reply_msg_proceed:
                    chan[self] := Tail(chan[self]);
                };
    M_proceed_clients:
                prepareChange := FALSE;
    M_wait_new_round:
                await \A i \in Clients: pc[i] # "Done" => configID[i] = globalConfig;
            };
        }
    }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "76d81de4" /\ chksum(tla) = "2e2c901e")
\* Procedure variable retRec of procedure SNAPSHOT_Read at line 82 col 14 changed to retRec_
\* Procedure variable origRec of procedure SNAPSHOT_Write at line 137 col 14 changed to origRec_
\* Procedure variable swapRec of procedure SNAPSHOT_Write at line 137 col 33 changed to swapRec_
\* Procedure variable votes of procedure SNAPSHOT_Write at line 138 col 14 changed to votes_
VARIABLES db, up, FailNum, Primary, Backups, fretInt, fretRec, chan, 
          prepareChange, configID, clientState, commitHist, pc, stack

(* define statement *)
getVoteMin(voteVal, origVal, swapVal) == IF origVal \in voteVal
                                THEN CHOOSE i \in ((voteVal \ {origVal}) \union {swapVal}): (\A j \in ((voteVal \ {origVal}) \union {swapVal}): i <= j)
                                ELSE -1
getVoteVal(votes) == {votes[i].val : i \in Backups}
getVoteCnt(voteVal, votes) == [i \in voteVal |-> Cardinality(UNION {{j \in Backups: votes[j].val = i}})]
getMajorityVoteVal(voteVal, voteCnt) == CHOOSE i \in voteVal: (\A j \in voteVal: voteCnt[j] <= voteCnt[i])
MaxIdxLessThan(_seq, val) == CHOOSE i \in 1..Len(_seq) :
                        \A j \in 1..Len(_seq): _seq[j] <= val => i >= j
InsertAfter(_seq, idx, val) == SubSeq(_seq, 1, idx) \o <<val>> \o SubSeq(_seq, idx+1, Len(_seq))
genNewVal(oldVal, self) == ((oldVal + 1000) \div 1000) * 1000 + self
aliveSubset(S) == {n \in S: up[n]}
getFirstAliveIn(S) == IF Cardinality(aliveSubset(S)) > 0
                      THEN CHOOSE i \in S: up[i] /\ \A j \in aliveSubset(S): i <= j
                      ELSE -1
buildMsg(_type, _client, _rec) == [ type   |-> _type,
                                    client |-> _client,
                                    rec    |-> _rec ]

VARIABLES retRec_, msg, votes, origRec, swapRec, voteVal, voteCnt, majVoteVal, 
          tmpWin, checkRec, origRec_, swapRec_, retRec, votes_, Q, committed, 
          win, curCommitID, tmpMsg, numRetry, cntr, retVal, firstAlive, 
          activeNodes, replyMsg, globalConfig

vars == << db, up, FailNum, Primary, Backups, fretInt, fretRec, chan, 
           prepareChange, configID, clientState, commitHist, pc, stack, 
           retRec_, msg, votes, origRec, swapRec, voteVal, voteCnt, 
           majVoteVal, tmpWin, checkRec, origRec_, swapRec_, retRec, votes_, 
           Q, committed, win, curCommitID, tmpMsg, numRetry, cntr, retVal, 
           firstAlive, activeNodes, replyMsg, globalConfig >>

ProcSet == (Clients) \cup (MNs) \cup ({Master})

Init == (* Global variables *)
        /\ db = [n \in MNs |-> [val|->0, commitID|->0]]
        /\ up = [n \in Nodes |-> TRUE]
        /\ FailNum = FAILNUM
        /\ Primary = 1
        /\ Backups = MNs \ {Primary}
        /\ fretInt = [n \in Clients |-> 0]
        /\ fretRec = [n \in Clients |-> FailRec]
        /\ chan = [n \in (Clients \cup {Master}) |-> <<>>]
        /\ prepareChange = FALSE
        /\ configID = [n \in Clients |-> 0]
        /\ clientState = [n \in Clients |-> 0]
        /\ commitHist = [n \in Clients |-> <<0>>]
        (* Procedure SNAPSHOT_Read *)
        /\ retRec_ = [ self \in ProcSet |-> FailRec]
        /\ msg = [ self \in ProcSet |-> EmptyMsg]
        (* Procedure EvalRules *)
        /\ votes = [ self \in ProcSet |-> [n \in Backups |-> FailRec]]
        /\ origRec = [ self \in ProcSet |-> FailRec]
        /\ swapRec = [ self \in ProcSet |-> FailRec]
        /\ voteVal = [ self \in ProcSet |-> getVoteVal(votes[self])]
        /\ voteCnt = [ self \in ProcSet |-> getVoteCnt(voteVal[self], votes[self])]
        /\ majVoteVal = [ self \in ProcSet |-> -1]
        /\ tmpWin = [ self \in ProcSet |-> -3]
        /\ checkRec = [ self \in ProcSet |-> FailRec]
        (* Procedure SNAPSHOT_Write *)
        /\ origRec_ = [ self \in ProcSet |-> FailRec]
        /\ swapRec_ = [ self \in ProcSet |-> FailRec]
        /\ retRec = [ self \in ProcSet |-> FailRec]
        /\ votes_ = [ self \in ProcSet |-> [n \in MNs |-> FailRec]]
        /\ Q = [ self \in ProcSet |-> {}]
        /\ committed = [ self \in ProcSet |-> FALSE]
        /\ win = [ self \in ProcSet |-> -1]
        /\ curCommitID = [ self \in ProcSet |-> -1]
        /\ tmpMsg = [ self \in ProcSet |-> EmptyMsg]
        /\ numRetry = [ self \in ProcSet |-> 2]
        (* Process c *)
        /\ cntr = [self \in Clients |-> 0]
        /\ retVal = [self \in Clients |-> -1]
        (* Process m *)
        /\ firstAlive = [self \in {Master} |-> -1]
        /\ activeNodes = [self \in {Master} |-> {}]
        /\ replyMsg = [self \in {Master} |-> EmptyMsg]
        /\ globalConfig = [self \in {Master} |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "C"
                                        [] self \in MNs -> "MN"
                                        [] self \in {Master} -> "MASTER"]

R_ST(self) == /\ pc[self] = "R_ST"
              /\ retRec_' = [retRec_ EXCEPT ![self] = IF up[Primary] THEN db[Primary] ELSE FailRec]
              /\ IF retRec_'[self].val = -1
                    THEN /\ Assert((buildMsg("Req", self, FailRec)) \in MsgType, 
                                   "Failure of assertion at line 69, column 9 of macro called at line 87, column 13.")
                         /\ chan' = [chan EXCEPT ![Master] = Append(chan[Master], (buildMsg("Req", self, FailRec)))]
                         /\ clientState' = [clientState EXCEPT ![self] = -1]
                         /\ pc' = [pc EXCEPT ![self] = "R_recv"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "R_fini"]
                         /\ UNCHANGED << chan, clientState >>
              /\ UNCHANGED << db, up, FailNum, Primary, Backups, fretInt, 
                              fretRec, prepareChange, configID, commitHist, 
                              stack, msg, votes, origRec, swapRec, voteVal, 
                              voteCnt, majVoteVal, tmpWin, checkRec, origRec_, 
                              swapRec_, retRec, votes_, Q, committed, win, 
                              curCommitID, tmpMsg, numRetry, cntr, retVal, 
                              firstAlive, activeNodes, replyMsg, globalConfig >>

R_recv(self) == /\ pc[self] = "R_recv"
                /\ Len(chan[self]) > 0
                /\ msg' = [msg EXCEPT ![self] = Head(chan[self])]
                /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
                /\ retRec_' = [retRec_ EXCEPT ![self] = msg'[self].rec]
                /\ clientState' = [clientState EXCEPT ![self] = 0]
                /\ pc' = [pc EXCEPT ![self] = "R_fini"]
                /\ UNCHANGED << db, up, FailNum, Primary, Backups, fretInt, 
                                fretRec, prepareChange, configID, commitHist, 
                                stack, votes, origRec, swapRec, voteVal, 
                                voteCnt, majVoteVal, tmpWin, checkRec, 
                                origRec_, swapRec_, retRec, votes_, Q, 
                                committed, win, curCommitID, tmpMsg, numRetry, 
                                cntr, retVal, firstAlive, activeNodes, 
                                replyMsg, globalConfig >>

R_fini(self) == /\ pc[self] = "R_fini"
                /\ fretRec' = [fretRec EXCEPT ![self] = retRec_[self]]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ retRec_' = [retRec_ EXCEPT ![self] = Head(stack[self]).retRec_]
                /\ msg' = [msg EXCEPT ![self] = Head(stack[self]).msg]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << db, up, FailNum, Primary, Backups, fretInt, 
                                chan, prepareChange, configID, clientState, 
                                commitHist, votes, origRec, swapRec, voteVal, 
                                voteCnt, majVoteVal, tmpWin, checkRec, 
                                origRec_, swapRec_, retRec, votes_, Q, 
                                committed, win, curCommitID, tmpMsg, numRetry, 
                                cntr, retVal, firstAlive, activeNodes, 
                                replyMsg, globalConfig >>

SNAPSHOT_Read(self) == R_ST(self) \/ R_recv(self) \/ R_fini(self)

EVAL_ST1(self) == /\ pc[self] = "EVAL_ST1"
                  /\ Assert(origRec[self] \in RecType /\ swapRec[self] \in RecType, 
                            "Failure of assertion at line 106, column 9.")
                  /\ majVoteVal' = [majVoteVal EXCEPT ![self] = getMajorityVoteVal(voteVal[self], voteCnt[self])]
                  /\ IF -1 \in voteVal[self]
                        THEN /\ tmpWin' = [tmpWin EXCEPT ![self] = -1]
                        ELSE /\ IF voteCnt[self][majVoteVal'[self]] = Cardinality(Backups)
                                   THEN /\ tmpWin' = [tmpWin EXCEPT ![self] = IF majVoteVal'[self] = origRec[self].val THEN 0 ELSE 3]
                                   ELSE /\ IF 2 * voteCnt[self][majVoteVal'[self]] > Cardinality(Backups)
                                              THEN /\ tmpWin' = [tmpWin EXCEPT ![self] = IF majVoteVal'[self] = origRec[self].val THEN 1 ELSE 3]
                                              ELSE /\ TRUE
                                                   /\ UNCHANGED tmpWin
                  /\ IF tmpWin'[self] = -3
                        THEN /\ pc' = [pc EXCEPT ![self] = "EVAL_recheck"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "EVAL_FINI"]
                  /\ UNCHANGED << db, up, FailNum, Primary, Backups, fretInt, 
                                  fretRec, chan, prepareChange, configID, 
                                  clientState, commitHist, stack, retRec_, msg, 
                                  votes, origRec, swapRec, voteVal, voteCnt, 
                                  checkRec, origRec_, swapRec_, retRec, votes_, 
                                  Q, committed, win, curCommitID, tmpMsg, 
                                  numRetry, cntr, retVal, firstAlive, 
                                  activeNodes, replyMsg, globalConfig >>

EVAL_recheck(self) == /\ pc[self] = "EVAL_recheck"
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "SNAPSHOT_Read",
                                                               pc        |->  "EVAL_recheck_rep",
                                                               retRec_   |->  retRec_[self],
                                                               msg       |->  msg[self] ] >>
                                                           \o stack[self]]
                      /\ retRec_' = [retRec_ EXCEPT ![self] = FailRec]
                      /\ msg' = [msg EXCEPT ![self] = EmptyMsg]
                      /\ pc' = [pc EXCEPT ![self] = "R_ST"]
                      /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                      fretInt, fretRec, chan, prepareChange, 
                                      configID, clientState, commitHist, votes, 
                                      origRec, swapRec, voteVal, voteCnt, 
                                      majVoteVal, tmpWin, checkRec, origRec_, 
                                      swapRec_, retRec, votes_, Q, committed, 
                                      win, curCommitID, tmpMsg, numRetry, cntr, 
                                      retVal, firstAlive, activeNodes, 
                                      replyMsg, globalConfig >>

EVAL_recheck_rep(self) == /\ pc[self] = "EVAL_recheck_rep"
                          /\ checkRec' = [checkRec EXCEPT ![self] = fretRec[self]]
                          /\ pc' = [pc EXCEPT ![self] = "EVAL_ST2"]
                          /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                          fretInt, fretRec, chan, 
                                          prepareChange, configID, clientState, 
                                          commitHist, stack, retRec_, msg, 
                                          votes, origRec, swapRec, voteVal, 
                                          voteCnt, majVoteVal, tmpWin, 
                                          origRec_, swapRec_, retRec, votes_, 
                                          Q, committed, win, curCommitID, 
                                          tmpMsg, numRetry, cntr, retVal, 
                                          firstAlive, activeNodes, replyMsg, 
                                          globalConfig >>

EVAL_ST2(self) == /\ pc[self] = "EVAL_ST2"
                  /\ IF checkRec[self].val = swapRec[self].val
                        THEN /\ tmpWin' = [tmpWin EXCEPT ![self] = 5]
                        ELSE /\ IF checkRec[self].val # origRec[self].val
                                   THEN /\ tmpWin' = [tmpWin EXCEPT ![self] = 4]
                                   ELSE /\ IF getVoteMin(voteVal[self], origRec[self].val, swapRec[self].val) = swapRec[self].val
                                              THEN /\ tmpWin' = [tmpWin EXCEPT ![self] = 2]
                                              ELSE /\ tmpWin' = [tmpWin EXCEPT ![self] = 3]
                  /\ pc' = [pc EXCEPT ![self] = "EVAL_FINI"]
                  /\ UNCHANGED << db, up, FailNum, Primary, Backups, fretInt, 
                                  fretRec, chan, prepareChange, configID, 
                                  clientState, commitHist, stack, retRec_, msg, 
                                  votes, origRec, swapRec, voteVal, voteCnt, 
                                  majVoteVal, checkRec, origRec_, swapRec_, 
                                  retRec, votes_, Q, committed, win, 
                                  curCommitID, tmpMsg, numRetry, cntr, retVal, 
                                  firstAlive, activeNodes, replyMsg, 
                                  globalConfig >>

EVAL_FINI(self) == /\ pc[self] = "EVAL_FINI"
                   /\ fretInt' = [fretInt EXCEPT ![self] = tmpWin[self]]
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ voteVal' = [voteVal EXCEPT ![self] = Head(stack[self]).voteVal]
                   /\ voteCnt' = [voteCnt EXCEPT ![self] = Head(stack[self]).voteCnt]
                   /\ majVoteVal' = [majVoteVal EXCEPT ![self] = Head(stack[self]).majVoteVal]
                   /\ tmpWin' = [tmpWin EXCEPT ![self] = Head(stack[self]).tmpWin]
                   /\ checkRec' = [checkRec EXCEPT ![self] = Head(stack[self]).checkRec]
                   /\ votes' = [votes EXCEPT ![self] = Head(stack[self]).votes]
                   /\ origRec' = [origRec EXCEPT ![self] = Head(stack[self]).origRec]
                   /\ swapRec' = [swapRec EXCEPT ![self] = Head(stack[self]).swapRec]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << db, up, FailNum, Primary, Backups, fretRec, 
                                   chan, prepareChange, configID, clientState, 
                                   commitHist, retRec_, msg, origRec_, 
                                   swapRec_, retRec, votes_, Q, committed, win, 
                                   curCommitID, tmpMsg, numRetry, cntr, retVal, 
                                   firstAlive, activeNodes, replyMsg, 
                                   globalConfig >>

EvalRules(self) == EVAL_ST1(self) \/ EVAL_recheck(self)
                      \/ EVAL_recheck_rep(self) \/ EVAL_ST2(self)
                      \/ EVAL_FINI(self)

W_read(self) == /\ pc[self] = "W_read"
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "SNAPSHOT_Read",
                                                         pc        |->  "W_read_fini",
                                                         retRec_   |->  retRec_[self],
                                                         msg       |->  msg[self] ] >>
                                                     \o stack[self]]
                /\ retRec_' = [retRec_ EXCEPT ![self] = FailRec]
                /\ msg' = [msg EXCEPT ![self] = EmptyMsg]
                /\ pc' = [pc EXCEPT ![self] = "R_ST"]
                /\ UNCHANGED << db, up, FailNum, Primary, Backups, fretInt, 
                                fretRec, chan, prepareChange, configID, 
                                clientState, commitHist, votes, origRec, 
                                swapRec, voteVal, voteCnt, majVoteVal, tmpWin, 
                                checkRec, origRec_, swapRec_, retRec, votes_, 
                                Q, committed, win, curCommitID, tmpMsg, 
                                numRetry, cntr, retVal, firstAlive, 
                                activeNodes, replyMsg, globalConfig >>

W_read_fini(self) == /\ pc[self] = "W_read_fini"
                     /\ origRec_' = [origRec_ EXCEPT ![self] = fretRec[self]]
                     /\ swapRec_' = [swapRec_ EXCEPT ![self] = [val      |-> genNewVal(origRec_'[self].val, self),
                                                                commitID |-> origRec_'[self].commitID + 1]]
                     /\ curCommitID' = [curCommitID EXCEPT ![self] = origRec_'[self].commitID]
                     /\ Q' = [Q EXCEPT ![self] = Backups]
                     /\ IF Q'[self] = {}
                           THEN /\ Assert(origRec_'[self] \in RecType /\ swapRec_'[self] \in RecType, 
                                          "Failure of assertion at line 55, column 9 of macro called at line 152, column 13.")
                                /\ retRec' = [retRec EXCEPT ![self] = IF up[Primary] THEN db[Primary] ELSE FailRec]
                                /\ IF db[Primary].val = origRec_'[self].val /\ up[Primary]
                                      THEN /\ db' = [db EXCEPT ![Primary] = swapRec_'[self]]
                                      ELSE /\ TRUE
                                           /\ db' = db
                                /\ commitHist' = [commitHist EXCEPT ![self] = IF retRec'[self].val = origRec_'[self].val
                                                                              THEN Append(commitHist[self], curCommitID'[self] + 1)
                                                                              ELSE commitHist[self]]
                                /\ fretInt' = [fretInt EXCEPT ![self] = IF retRec'[self].val = origRec_'[self].val THEN 0 ELSE -1]
                                /\ pc' = [pc EXCEPT ![self] = "W_return_cas_primary"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "W_cas_bk"]
                                /\ UNCHANGED << db, fretInt, commitHist, 
                                                retRec >>
                     /\ UNCHANGED << up, FailNum, Primary, Backups, fretRec, 
                                     chan, prepareChange, configID, 
                                     clientState, stack, retRec_, msg, votes, 
                                     origRec, swapRec, voteVal, voteCnt, 
                                     majVoteVal, tmpWin, checkRec, votes_, 
                                     committed, win, tmpMsg, numRetry, cntr, 
                                     retVal, firstAlive, activeNodes, replyMsg, 
                                     globalConfig >>

W_return_cas_primary(self) == /\ pc[self] = "W_return_cas_primary"
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ origRec_' = [origRec_ EXCEPT ![self] = Head(stack[self]).origRec_]
                              /\ swapRec_' = [swapRec_ EXCEPT ![self] = Head(stack[self]).swapRec_]
                              /\ retRec' = [retRec EXCEPT ![self] = Head(stack[self]).retRec]
                              /\ votes_' = [votes_ EXCEPT ![self] = Head(stack[self]).votes_]
                              /\ Q' = [Q EXCEPT ![self] = Head(stack[self]).Q]
                              /\ committed' = [committed EXCEPT ![self] = Head(stack[self]).committed]
                              /\ win' = [win EXCEPT ![self] = Head(stack[self]).win]
                              /\ curCommitID' = [curCommitID EXCEPT ![self] = Head(stack[self]).curCommitID]
                              /\ tmpMsg' = [tmpMsg EXCEPT ![self] = Head(stack[self]).tmpMsg]
                              /\ numRetry' = [numRetry EXCEPT ![self] = Head(stack[self]).numRetry]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << db, up, FailNum, Primary, 
                                              Backups, fretInt, fretRec, chan, 
                                              prepareChange, configID, 
                                              clientState, commitHist, retRec_, 
                                              msg, votes, origRec, swapRec, 
                                              voteVal, voteCnt, majVoteVal, 
                                              tmpWin, checkRec, cntr, retVal, 
                                              firstAlive, activeNodes, 
                                              replyMsg, globalConfig >>

W_cas_bk(self) == /\ pc[self] = "W_cas_bk"
                  /\ IF Q[self] # {}
                        THEN /\ \E p \in Q[self]:
                                  /\ Assert(origRec_[self] \in RecType /\ swapRec_[self] \in RecType, 
                                            "Failure of assertion at line 55, column 9 of macro called at line 163, column 17.")
                                  /\ votes_' = [votes_ EXCEPT ![self][p] = IF up[p] THEN db[p] ELSE FailRec]
                                  /\ IF db[p].val = origRec_[self].val /\ up[p]
                                        THEN /\ db' = [db EXCEPT ![p] = swapRec_[self]]
                                        ELSE /\ TRUE
                                             /\ db' = db
                                  /\ Q' = [Q EXCEPT ![self] = Q[self] \ {p}]
                             /\ pc' = [pc EXCEPT ![self] = "W_cas_bk"]
                             /\ UNCHANGED << stack, votes, origRec, swapRec, 
                                             voteVal, voteCnt, majVoteVal, 
                                             tmpWin, checkRec >>
                        ELSE /\ /\ origRec' = [origRec EXCEPT ![self] = origRec_[self]]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "EvalRules",
                                                                         pc        |->  "W_eval_rules",
                                                                         voteVal   |->  voteVal[self],
                                                                         voteCnt   |->  voteCnt[self],
                                                                         majVoteVal |->  majVoteVal[self],
                                                                         tmpWin    |->  tmpWin[self],
                                                                         checkRec  |->  checkRec[self],
                                                                         votes     |->  votes[self],
                                                                         origRec   |->  origRec[self],
                                                                         swapRec   |->  swapRec[self] ] >>
                                                                     \o stack[self]]
                                /\ swapRec' = [swapRec EXCEPT ![self] = swapRec_[self]]
                                /\ votes' = [votes EXCEPT ![self] = votes_[self]]
                             /\ voteVal' = [voteVal EXCEPT ![self] = getVoteVal(votes'[self])]
                             /\ voteCnt' = [voteCnt EXCEPT ![self] = getVoteCnt(voteVal'[self], votes'[self])]
                             /\ majVoteVal' = [majVoteVal EXCEPT ![self] = -1]
                             /\ tmpWin' = [tmpWin EXCEPT ![self] = -3]
                             /\ checkRec' = [checkRec EXCEPT ![self] = FailRec]
                             /\ pc' = [pc EXCEPT ![self] = "EVAL_ST1"]
                             /\ UNCHANGED << db, votes_, Q >>
                  /\ UNCHANGED << up, FailNum, Primary, Backups, fretInt, 
                                  fretRec, chan, prepareChange, configID, 
                                  clientState, commitHist, retRec_, msg, 
                                  origRec_, swapRec_, retRec, committed, win, 
                                  curCommitID, tmpMsg, numRetry, cntr, retVal, 
                                  firstAlive, activeNodes, replyMsg, 
                                  globalConfig >>

W_eval_rules(self) == /\ pc[self] = "W_eval_rules"
                      /\ win' = [win EXCEPT ![self] = fretInt[self]]
                      /\ IF win'[self] = 0
                            THEN /\ curCommitID' = [curCommitID EXCEPT ![self] = curCommitID[self] + 1]
                                 /\ commitHist' = [commitHist EXCEPT ![self] = Append(commitHist[self], curCommitID'[self])]
                                 /\ pc' = [pc EXCEPT ![self] = "W_cas_primary_1"]
                                 /\ UNCHANGED << db, chan, clientState >>
                            ELSE /\ IF win'[self] = 1 \/ win'[self]  = 2
                                       THEN /\ curCommitID' = [curCommitID EXCEPT ![self] = curCommitID[self] + 1]
                                            /\ commitHist' = [commitHist EXCEPT ![self] = Append(commitHist[self], curCommitID'[self])]
                                            /\ db' = [ n \in MNs |-> IF n \in Backups /\ up[n]
                                                                           THEN swapRec_[self] ELSE db[n]   ]
                                            /\ pc' = [pc EXCEPT ![self] = "W_cas_primary_2"]
                                            /\ UNCHANGED << chan, clientState >>
                                       ELSE /\ IF win'[self] = 3
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "W_wait_commit"]
                                                       /\ UNCHANGED << chan, 
                                                                       clientState, 
                                                                       commitHist, 
                                                                       curCommitID >>
                                                  ELSE /\ IF win'[self] = 4 \/ win'[self] = 5
                                                             THEN /\ curCommitID' = [curCommitID EXCEPT ![self] = IF win'[self] = 4 THEN curCommitID[self] ELSE curCommitID[self] + 1]
                                                                  /\ commitHist' = [commitHist EXCEPT ![self] = Append(commitHist[self], curCommitID'[self])]
                                                                  /\ pc' = [pc EXCEPT ![self] = "W_fini_0"]
                                                                  /\ UNCHANGED << chan, 
                                                                                  clientState >>
                                                             ELSE /\ Assert(win'[self] = -1, 
                                                                            "Failure of assertion at line 204, column 13.")
                                                                  /\ Assert((buildMsg("Req", self, FailRec)) \in MsgType, 
                                                                            "Failure of assertion at line 69, column 9 of macro called at line 205, column 13.")
                                                                  /\ chan' = [chan EXCEPT ![Master] = Append(chan[Master], (buildMsg("Req", self, FailRec)))]
                                                                  /\ clientState' = [clientState EXCEPT ![self] = -1]
                                                                  /\ pc' = [pc EXCEPT ![self] = "W_bk_failure_wait"]
                                                                  /\ UNCHANGED << commitHist, 
                                                                                  curCommitID >>
                                            /\ db' = db
                      /\ UNCHANGED << up, FailNum, Primary, Backups, fretInt, 
                                      fretRec, prepareChange, configID, stack, 
                                      retRec_, msg, votes, origRec, swapRec, 
                                      voteVal, voteCnt, majVoteVal, tmpWin, 
                                      checkRec, origRec_, swapRec_, retRec, 
                                      votes_, Q, committed, tmpMsg, numRetry, 
                                      cntr, retVal, firstAlive, activeNodes, 
                                      replyMsg, globalConfig >>

W_cas_primary_1(self) == /\ pc[self] = "W_cas_primary_1"
                         /\ Assert(origRec_[self] \in RecType /\ swapRec_[self] \in RecType, 
                                   "Failure of assertion at line 55, column 9 of macro called at line 175, column 13.")
                         /\ retRec' = [retRec EXCEPT ![self] = IF up[Primary] THEN db[Primary] ELSE FailRec]
                         /\ IF db[Primary].val = origRec_[self].val /\ up[Primary]
                               THEN /\ db' = [db EXCEPT ![Primary] = swapRec_[self]]
                               ELSE /\ TRUE
                                    /\ db' = db
                         /\ pc' = [pc EXCEPT ![self] = "W_fini_0"]
                         /\ UNCHANGED << up, FailNum, Primary, Backups, 
                                         fretInt, fretRec, chan, prepareChange, 
                                         configID, clientState, commitHist, 
                                         stack, retRec_, msg, votes, origRec, 
                                         swapRec, voteVal, voteCnt, majVoteVal, 
                                         tmpWin, checkRec, origRec_, swapRec_, 
                                         votes_, Q, committed, win, 
                                         curCommitID, tmpMsg, numRetry, cntr, 
                                         retVal, firstAlive, activeNodes, 
                                         replyMsg, globalConfig >>

W_cas_primary_2(self) == /\ pc[self] = "W_cas_primary_2"
                         /\ Assert(origRec_[self] \in RecType /\ swapRec_[self] \in RecType, 
                                   "Failure of assertion at line 55, column 9 of macro called at line 182, column 13.")
                         /\ retRec' = [retRec EXCEPT ![self] = IF up[Primary] THEN db[Primary] ELSE FailRec]
                         /\ IF db[Primary].val = origRec_[self].val /\ up[Primary]
                               THEN /\ db' = [db EXCEPT ![Primary] = swapRec_[self]]
                               ELSE /\ TRUE
                                    /\ db' = db
                         /\ pc' = [pc EXCEPT ![self] = "W_fini_0"]
                         /\ UNCHANGED << up, FailNum, Primary, Backups, 
                                         fretInt, fretRec, chan, prepareChange, 
                                         configID, clientState, commitHist, 
                                         stack, retRec_, msg, votes, origRec, 
                                         swapRec, voteVal, voteCnt, majVoteVal, 
                                         tmpWin, checkRec, origRec_, swapRec_, 
                                         votes_, Q, committed, win, 
                                         curCommitID, tmpMsg, numRetry, cntr, 
                                         retVal, firstAlive, activeNodes, 
                                         replyMsg, globalConfig >>

W_wait_commit(self) == /\ pc[self] = "W_wait_commit"
                       /\ IF committed[self] = FALSE
                             THEN /\ retRec' = [retRec EXCEPT ![self] = IF up[Primary] THEN db[Primary] ELSE FailRec]
                                  /\ IF retRec'[self].val = -1 \/ retRec'[self].val = origRec_[self].val
                                        THEN /\ fretInt' = [fretInt EXCEPT ![self] = -1]
                                             /\ pc' = [pc EXCEPT ![self] = "W_retry_return"]
                                             /\ UNCHANGED << commitHist, 
                                                             committed, 
                                                             curCommitID >>
                                        ELSE /\ committed' = [committed EXCEPT ![self] = TRUE]
                                             /\ curCommitID' = [curCommitID EXCEPT ![self] = IF retRec'[self].val = swapRec_[self].val
                                                                                             THEN curCommitID[self] + 1 ELSE curCommitID[self]]
                                             /\ commitHist' = [commitHist EXCEPT ![self] = Append(commitHist[self], curCommitID'[self])]
                                             /\ pc' = [pc EXCEPT ![self] = "W_wait_commit"]
                                             /\ UNCHANGED fretInt
                             ELSE /\ pc' = [pc EXCEPT ![self] = "W_fini_0"]
                                  /\ UNCHANGED << fretInt, commitHist, retRec, 
                                                  committed, curCommitID >>
                       /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                       fretRec, chan, prepareChange, configID, 
                                       clientState, stack, retRec_, msg, votes, 
                                       origRec, swapRec, voteVal, voteCnt, 
                                       majVoteVal, tmpWin, checkRec, origRec_, 
                                       swapRec_, votes_, Q, win, tmpMsg, 
                                       numRetry, cntr, retVal, firstAlive, 
                                       activeNodes, replyMsg, globalConfig >>

W_retry_return(self) == /\ pc[self] = "W_retry_return"
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ origRec_' = [origRec_ EXCEPT ![self] = Head(stack[self]).origRec_]
                        /\ swapRec_' = [swapRec_ EXCEPT ![self] = Head(stack[self]).swapRec_]
                        /\ retRec' = [retRec EXCEPT ![self] = Head(stack[self]).retRec]
                        /\ votes_' = [votes_ EXCEPT ![self] = Head(stack[self]).votes_]
                        /\ Q' = [Q EXCEPT ![self] = Head(stack[self]).Q]
                        /\ committed' = [committed EXCEPT ![self] = Head(stack[self]).committed]
                        /\ win' = [win EXCEPT ![self] = Head(stack[self]).win]
                        /\ curCommitID' = [curCommitID EXCEPT ![self] = Head(stack[self]).curCommitID]
                        /\ tmpMsg' = [tmpMsg EXCEPT ![self] = Head(stack[self]).tmpMsg]
                        /\ numRetry' = [numRetry EXCEPT ![self] = Head(stack[self]).numRetry]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                        fretInt, fretRec, chan, prepareChange, 
                                        configID, clientState, commitHist, 
                                        retRec_, msg, votes, origRec, swapRec, 
                                        voteVal, voteCnt, majVoteVal, tmpWin, 
                                        checkRec, cntr, retVal, firstAlive, 
                                        activeNodes, replyMsg, globalConfig >>

W_bk_failure_wait(self) == /\ pc[self] = "W_bk_failure_wait"
                           /\ Len(chan[self]) > 0
                           /\ tmpMsg' = [tmpMsg EXCEPT ![self] = Head(chan[self])]
                           /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
                           /\ clientState' = [clientState EXCEPT ![self] = 0]
                           /\ retRec' = [retRec EXCEPT ![self] = tmpMsg'[self].rec]
                           /\ curCommitID' = [curCommitID EXCEPT ![self] = IF retRec'[self].val = swapRec_[self].val THEN curCommitID[self] + 1 ELSE curCommitID[self]]
                           /\ commitHist' = [commitHist EXCEPT ![self] = Append(commitHist[self], curCommitID'[self])]
                           /\ pc' = [pc EXCEPT ![self] = "W_fini_0"]
                           /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                           fretInt, fretRec, prepareChange, 
                                           configID, stack, retRec_, msg, 
                                           votes, origRec, swapRec, voteVal, 
                                           voteCnt, majVoteVal, tmpWin, 
                                           checkRec, origRec_, swapRec_, 
                                           votes_, Q, committed, win, numRetry, 
                                           cntr, retVal, firstAlive, 
                                           activeNodes, replyMsg, globalConfig >>

W_fini_0(self) == /\ pc[self] = "W_fini_0"
                  /\ fretInt' = [fretInt EXCEPT ![self] = 0]
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ origRec_' = [origRec_ EXCEPT ![self] = Head(stack[self]).origRec_]
                  /\ swapRec_' = [swapRec_ EXCEPT ![self] = Head(stack[self]).swapRec_]
                  /\ retRec' = [retRec EXCEPT ![self] = Head(stack[self]).retRec]
                  /\ votes_' = [votes_ EXCEPT ![self] = Head(stack[self]).votes_]
                  /\ Q' = [Q EXCEPT ![self] = Head(stack[self]).Q]
                  /\ committed' = [committed EXCEPT ![self] = Head(stack[self]).committed]
                  /\ win' = [win EXCEPT ![self] = Head(stack[self]).win]
                  /\ curCommitID' = [curCommitID EXCEPT ![self] = Head(stack[self]).curCommitID]
                  /\ tmpMsg' = [tmpMsg EXCEPT ![self] = Head(stack[self]).tmpMsg]
                  /\ numRetry' = [numRetry EXCEPT ![self] = Head(stack[self]).numRetry]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << db, up, FailNum, Primary, Backups, fretRec, 
                                  chan, prepareChange, configID, clientState, 
                                  commitHist, retRec_, msg, votes, origRec, 
                                  swapRec, voteVal, voteCnt, majVoteVal, 
                                  tmpWin, checkRec, cntr, retVal, firstAlive, 
                                  activeNodes, replyMsg, globalConfig >>

SNAPSHOT_Write(self) == W_read(self) \/ W_read_fini(self)
                           \/ W_return_cas_primary(self) \/ W_cas_bk(self)
                           \/ W_eval_rules(self) \/ W_cas_primary_1(self)
                           \/ W_cas_primary_2(self) \/ W_wait_commit(self)
                           \/ W_retry_return(self)
                           \/ W_bk_failure_wait(self) \/ W_fini_0(self)

C(self) == /\ pc[self] = "C"
           /\ IF cntr[self] < STOP
                 THEN /\ IF prepareChange = TRUE
                            THEN /\ clientState' = [clientState EXCEPT ![self] = -1]
                                 /\ pc' = [pc EXCEPT ![self] = "C_wait_prepare"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "C_start_write"]
                                 /\ UNCHANGED clientState
                 ELSE /\ clientState' = [clientState EXCEPT ![self] = -1]
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << db, up, FailNum, Primary, Backups, fretInt, fretRec, 
                           chan, prepareChange, configID, commitHist, stack, 
                           retRec_, msg, votes, origRec, swapRec, voteVal, 
                           voteCnt, majVoteVal, tmpWin, checkRec, origRec_, 
                           swapRec_, retRec, votes_, Q, committed, win, 
                           curCommitID, tmpMsg, numRetry, cntr, retVal, 
                           firstAlive, activeNodes, replyMsg, globalConfig >>

C_start_write(self) == /\ pc[self] = "C_start_write"
                       /\ clientState' = [clientState EXCEPT ![self] = 0]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "SNAPSHOT_Write",
                                                                pc        |->  "C_after_write",
                                                                origRec_  |->  origRec_[self],
                                                                swapRec_  |->  swapRec_[self],
                                                                retRec    |->  retRec[self],
                                                                votes_    |->  votes_[self],
                                                                Q         |->  Q[self],
                                                                committed |->  committed[self],
                                                                win       |->  win[self],
                                                                curCommitID |->  curCommitID[self],
                                                                tmpMsg    |->  tmpMsg[self],
                                                                numRetry  |->  numRetry[self] ] >>
                                                            \o stack[self]]
                       /\ origRec_' = [origRec_ EXCEPT ![self] = FailRec]
                       /\ swapRec_' = [swapRec_ EXCEPT ![self] = FailRec]
                       /\ retRec' = [retRec EXCEPT ![self] = FailRec]
                       /\ votes_' = [votes_ EXCEPT ![self] = [n \in MNs |-> FailRec]]
                       /\ Q' = [Q EXCEPT ![self] = {}]
                       /\ committed' = [committed EXCEPT ![self] = FALSE]
                       /\ win' = [win EXCEPT ![self] = -1]
                       /\ curCommitID' = [curCommitID EXCEPT ![self] = -1]
                       /\ tmpMsg' = [tmpMsg EXCEPT ![self] = EmptyMsg]
                       /\ numRetry' = [numRetry EXCEPT ![self] = 2]
                       /\ pc' = [pc EXCEPT ![self] = "W_read"]
                       /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                       fretInt, fretRec, chan, prepareChange, 
                                       configID, commitHist, retRec_, msg, 
                                       votes, origRec, swapRec, voteVal, 
                                       voteCnt, majVoteVal, tmpWin, checkRec, 
                                       cntr, retVal, firstAlive, activeNodes, 
                                       replyMsg, globalConfig >>

C_after_write(self) == /\ pc[self] = "C_after_write"
                       /\ retVal' = [retVal EXCEPT ![self] = fretInt[self]]
                       /\ cntr' = [cntr EXCEPT ![self] = IF retVal'[self] = -1 THEN cntr[self] ELSE cntr[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "C"]
                       /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                       fretInt, fretRec, chan, prepareChange, 
                                       configID, clientState, commitHist, 
                                       stack, retRec_, msg, votes, origRec, 
                                       swapRec, voteVal, voteCnt, majVoteVal, 
                                       tmpWin, checkRec, origRec_, swapRec_, 
                                       retRec, votes_, Q, committed, win, 
                                       curCommitID, tmpMsg, numRetry, 
                                       firstAlive, activeNodes, replyMsg, 
                                       globalConfig >>

C_wait_prepare(self) == /\ pc[self] = "C_wait_prepare"
                        /\ prepareChange = FALSE
                        /\ clientState' = [clientState EXCEPT ![self] = 0]
                        /\ configID' = [configID EXCEPT ![self] = configID[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "C_start_write"]
                        /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                        fretInt, fretRec, chan, prepareChange, 
                                        commitHist, stack, retRec_, msg, votes, 
                                        origRec, swapRec, voteVal, voteCnt, 
                                        majVoteVal, tmpWin, checkRec, origRec_, 
                                        swapRec_, retRec, votes_, Q, committed, 
                                        win, curCommitID, tmpMsg, numRetry, 
                                        cntr, retVal, firstAlive, activeNodes, 
                                        replyMsg, globalConfig >>

c(self) == C(self) \/ C_start_write(self) \/ C_after_write(self)
              \/ C_wait_prepare(self)

MN(self) == /\ pc[self] = "MN"
            /\ IF FailNum > 0
                  THEN /\ IF FailNum > 0 /\ up[self]
                             THEN /\ up' = [up EXCEPT ![self] = FALSE]
                                  /\ FailNum' = FailNum - 1
                             ELSE /\ TRUE
                                  /\ UNCHANGED << up, FailNum >>
                       /\ pc' = [pc EXCEPT ![self] = "MN"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << up, FailNum >>
            /\ UNCHANGED << db, Primary, Backups, fretInt, fretRec, chan, 
                            prepareChange, configID, clientState, commitHist, 
                            stack, retRec_, msg, votes, origRec, swapRec, 
                            voteVal, voteCnt, majVoteVal, tmpWin, checkRec, 
                            origRec_, swapRec_, retRec, votes_, Q, committed, 
                            win, curCommitID, tmpMsg, numRetry, cntr, retVal, 
                            firstAlive, activeNodes, replyMsg, globalConfig >>

mn(self) == MN(self)

MASTER(self) == /\ pc[self] = "MASTER"
                /\ IF \E n \in ({Primary} \union Backups): up[n] = FALSE
                      THEN /\ prepareChange' = TRUE
                           /\ pc' = [pc EXCEPT ![self] = "M_wait_stop"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "MASTER"]
                           /\ UNCHANGED prepareChange
                /\ UNCHANGED << db, up, FailNum, Primary, Backups, fretInt, 
                                fretRec, chan, configID, clientState, 
                                commitHist, stack, retRec_, msg, votes, 
                                origRec, swapRec, voteVal, voteCnt, majVoteVal, 
                                tmpWin, checkRec, origRec_, swapRec_, retRec, 
                                votes_, Q, committed, win, curCommitID, tmpMsg, 
                                numRetry, cntr, retVal, firstAlive, 
                                activeNodes, replyMsg, globalConfig >>

M_wait_stop(self) == /\ pc[self] = "M_wait_stop"
                     /\ \A i \in Clients: clientState[i] = -1
                     /\ pc' = [pc EXCEPT ![self] = "M_stopped"]
                     /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                     fretInt, fretRec, chan, prepareChange, 
                                     configID, clientState, commitHist, stack, 
                                     retRec_, msg, votes, origRec, swapRec, 
                                     voteVal, voteCnt, majVoteVal, tmpWin, 
                                     checkRec, origRec_, swapRec_, retRec, 
                                     votes_, Q, committed, win, curCommitID, 
                                     tmpMsg, numRetry, cntr, retVal, 
                                     firstAlive, activeNodes, replyMsg, 
                                     globalConfig >>

M_stopped(self) == /\ pc[self] = "M_stopped"
                   /\ activeNodes' = [activeNodes EXCEPT ![self] = aliveSubset({Primary} \union Backups)]
                   /\ firstAlive' = [firstAlive EXCEPT ![self] = IF getFirstAliveIn(Backups) = -1
                                                                 THEN getFirstAliveIn(MNs) ELSE getFirstAliveIn(Backups)]
                   /\ Assert(firstAlive'[self] \in MNs, 
                             "Failure of assertion at line 269, column 17.")
                   /\ IF \E i, j \in (activeNodes'[self] \cap MNs): db[i].val # db[j].val
                         THEN /\ db' = [ n \in MNs |-> IF up[n] THEN db[firstAlive'[self]] ELSE db[n] ]
                         ELSE /\ TRUE
                              /\ db' = db
                   /\ Primary' = IF up[Primary] THEN Primary ELSE firstAlive'[self]
                   /\ Backups' = (activeNodes'[self] \cap MNs) \ {Primary'}
                   /\ globalConfig' = [globalConfig EXCEPT ![self] = globalConfig[self] + 1]
                   /\ replyMsg' = [replyMsg EXCEPT ![self] = buildMsg("Rep", Master, db'[firstAlive'[self]])]
                   /\ pc' = [pc EXCEPT ![self] = "M_reply_msg"]
                   /\ UNCHANGED << up, FailNum, fretInt, fretRec, chan, 
                                   prepareChange, configID, clientState, 
                                   commitHist, stack, retRec_, msg, votes, 
                                   origRec, swapRec, voteVal, voteCnt, 
                                   majVoteVal, tmpWin, checkRec, origRec_, 
                                   swapRec_, retRec, votes_, Q, committed, win, 
                                   curCommitID, tmpMsg, numRetry, cntr, retVal >>

M_reply_msg(self) == /\ pc[self] = "M_reply_msg"
                     /\ IF Len(chan[self]) # 0
                           THEN /\ Assert(replyMsg[self] \in MsgType, 
                                          "Failure of assertion at line 69, column 9 of macro called at line 279, column 21.")
                                /\ chan' = [chan EXCEPT ![(Head(chan[self]).client)] = Append(chan[(Head(chan[self]).client)], replyMsg[self])]
                                /\ pc' = [pc EXCEPT ![self] = "M_reply_msg_proceed"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "M_proceed_clients"]
                                /\ chan' = chan
                     /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                     fretInt, fretRec, prepareChange, configID, 
                                     clientState, commitHist, stack, retRec_, 
                                     msg, votes, origRec, swapRec, voteVal, 
                                     voteCnt, majVoteVal, tmpWin, checkRec, 
                                     origRec_, swapRec_, retRec, votes_, Q, 
                                     committed, win, curCommitID, tmpMsg, 
                                     numRetry, cntr, retVal, firstAlive, 
                                     activeNodes, replyMsg, globalConfig >>

M_reply_msg_proceed(self) == /\ pc[self] = "M_reply_msg_proceed"
                             /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
                             /\ pc' = [pc EXCEPT ![self] = "M_reply_msg"]
                             /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                             fretInt, fretRec, prepareChange, 
                                             configID, clientState, commitHist, 
                                             stack, retRec_, msg, votes, 
                                             origRec, swapRec, voteVal, 
                                             voteCnt, majVoteVal, tmpWin, 
                                             checkRec, origRec_, swapRec_, 
                                             retRec, votes_, Q, committed, win, 
                                             curCommitID, tmpMsg, numRetry, 
                                             cntr, retVal, firstAlive, 
                                             activeNodes, replyMsg, 
                                             globalConfig >>

M_proceed_clients(self) == /\ pc[self] = "M_proceed_clients"
                           /\ prepareChange' = FALSE
                           /\ pc' = [pc EXCEPT ![self] = "M_wait_new_round"]
                           /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                           fretInt, fretRec, chan, configID, 
                                           clientState, commitHist, stack, 
                                           retRec_, msg, votes, origRec, 
                                           swapRec, voteVal, voteCnt, 
                                           majVoteVal, tmpWin, checkRec, 
                                           origRec_, swapRec_, retRec, votes_, 
                                           Q, committed, win, curCommitID, 
                                           tmpMsg, numRetry, cntr, retVal, 
                                           firstAlive, activeNodes, replyMsg, 
                                           globalConfig >>

M_wait_new_round(self) == /\ pc[self] = "M_wait_new_round"
                          /\ \A i \in Clients: pc[i] # "Done" => configID[i] = globalConfig[self]
                          /\ pc' = [pc EXCEPT ![self] = "MASTER"]
                          /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                          fretInt, fretRec, chan, 
                                          prepareChange, configID, clientState, 
                                          commitHist, stack, retRec_, msg, 
                                          votes, origRec, swapRec, voteVal, 
                                          voteCnt, majVoteVal, tmpWin, 
                                          checkRec, origRec_, swapRec_, retRec, 
                                          votes_, Q, committed, win, 
                                          curCommitID, tmpMsg, numRetry, cntr, 
                                          retVal, firstAlive, activeNodes, 
                                          replyMsg, globalConfig >>

m(self) == MASTER(self) \/ M_wait_stop(self) \/ M_stopped(self)
              \/ M_reply_msg(self) \/ M_reply_msg_proceed(self)
              \/ M_proceed_clients(self) \/ M_wait_new_round(self)

Next == (\E self \in ProcSet:  \/ SNAPSHOT_Read(self) \/ EvalRules(self)
                               \/ SNAPSHOT_Write(self))
           \/ (\E self \in Clients: c(self))
           \/ (\E self \in MNs: mn(self))
           \/ (\E self \in {Master}: m(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : /\ WF_vars(c(self))
                                 /\ WF_vars(SNAPSHOT_Write(self))
                                 /\ WF_vars(SNAPSHOT_Read(self))
                                 /\ WF_vars(EvalRules(self))
        /\ \A self \in MNs : WF_vars(mn(self))
        /\ \A self \in {Master} : /\ WF_vars(m(self))
                                  /\ SF_vars(MASTER(self)) /\ SF_vars(M_wait_stop(self)) /\ SF_vars(M_stopped(self))

\* END TRANSLATION 

Termination == <>(\A self \in Clients: pc[self] = "Done")

Lin == (\A self \in Clients: pc[self] = "Done") => 
                \A n \in Clients: Len(commitHist[n]) = STOP + 1
                                  /\ \A i, j \in 1..Len(commitHist[n]): i < j => commitHist[n][j] <= commitHist[n][j]

Consistent == (\A self \in Clients: pc[self] = "Done") => \A i, j \in MNs: (up[i] /\ up[j]) => db[i].val = db[j].val
=============================================================================
\* Modification History
\* Last modified Tue Sep 06 19:48:33 CST 2022 by berna
\* Created Sun Sep 04 11:12:43 CST 2022 by berna
