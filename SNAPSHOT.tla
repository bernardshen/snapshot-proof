------------------------------ MODULE SNAPSHOT ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT NumMN, NumClient, FAILNUM, STOP

MNs     == 1..NumMN
Clients == (NumMN + 1)..(NumMN + NumClient) 
Nodes   == 1..(NumMN + NumClient)

FailRec == [val |-> -1, commitID |-> -1]

(*--algorithm SNAPSHOT {
    variable db = [n \in MNs |-> [val|->0, commitID|->0]],
             up = [n \in Nodes |-> TRUE],
             FailNum = FAILNUM,
             Primary = 1,
             Backups = MNs \ {1},
             retv = [n \in Clients |-> 0],
             commitHist = <<0>>;
             
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
    }
    
    macro CAS(ret, id, old, new) {
        \* return the original value in the store if the node is up
        \* return -1 to indicate the node failure
        ret := IF up[id] THEN db[id] ELSE FailRec;
        if (db[id].val = old.val /\ up[id]) {
            db[id] := new
        }
    }

    macro SNAPSHOT_Read(ret) {
        ret := IF up[Primary] THEN db[Primary] ELSE FailRec;
    }
    
    procedure EvalRules(votes = [n \in Backups |-> FailRec], origVal=FailRec, swapVal=FailRec)
    variable voteVal = getVoteVal(votes),
             voteCnt = getVoteCnt(voteVal, votes),
             majVoteVal = -1;
    {
    EVAL_ST: 
        majVoteVal := getMajorityVoteVal(voteVal, voteCnt);
        if (-1 \in voteVal) { retv[self] := -1; }
        else if (voteCnt[majVoteVal] = NumMN - 1) {
            retv[self] := IF majVoteVal = origVal.val THEN 0 ELSE 3;
        } else if (2 * voteCnt[majVoteVal] > NumMN - 1) {
            retv[self] := IF majVoteVal = origVal.val THEN 1 ELSE 3;
        } else if (db[Primary].val # origVal.val) {     \* need to read the primary again before using rule 3
            retv[self] := 4;
        } else if (getVoteMin(voteVal, origVal.val, swapVal.val) = swapVal.val) {
            retv[self] := 2;
        } else {
            retv[self] := 3;
        };
    EVAL_FINI:
        return
    }
    
    procedure EvalRulesN(votes = [n \in Backups |-> FailRec], origVal = FailRec, swapVal = FailRec)
    variable voteVal = getVoteVal(votes),
             voteCnt = getVoteCnt(voteVal, votes),
             majVoteVal = -1, tmp = -3, pr = FailRec;
    {
    EVALN_ST1:
        majVoteVal := getMajorityVoteVal(voteVal, voteCnt);
        if (-1 \in voteVal) { tmp := -1; }
        else if (voteCnt[majVoteVal] = NumMN - 1) {
            tmp := IF majVoteVal = origVal.val THEN 0 ELSE 3;
        } else if (2 * voteCnt[majVoteVal] > NumMN - 1) {
            tmp := IF majVoteVal = origVal.val THEN 1 ELSE 3;
        };
        if (tmp = -3) {
    EVALN_recheck:
            SNAPSHOT_Read(pr);
    EVALN_ST2:
            if (pr.val # origVal.val) { tmp := 4; }
            else if (getVoteMin(voteVal, origVal.val, swapVal.val) = swapVal.val) {
                tmp := 2;
            } else { 
                tmp := 3; 
            }
        };
    EVALN_FINI:
        retv[self] := tmp;
        return
    }
    
    procedure SNAPSHOT_Write()
    variable orig = FailRec, nVal = FailRec, ret = FailRec, 
             votes = [n \in Backups |-> FailRec],
             Q = {}, committed = FALSE, win = -1, curCommitID = -1;
    {
    W_prepare:
        SNAPSHOT_Read(orig);
        nVal := [val      |-> ((orig.val + 1000) \div 1000) * 1000 + self, 
                 commitID |-> orig.commitID + 1];
        curCommitID := orig.commitID;
        Q := Backups;
    W_cas_bk:
        while (Q # {}) {
            with (p \in Q) {
                CAS(votes[p], p, orig, nVal);
                Q := Q \ {p};
            }
        };
\*        call EvalRules(votes, orig, nVal);
        call EvalRulesN(votes, orig, nVal);
    W_modify_rest:
        win := retv[self];
        if (win = 1 \/ win = 2) {
            Q := Backups;
    W_consist_backup:
            while (Q # {}) {
                with (p \in Q) {
                    db[p] := IF up[p] THEN nVal ELSE db[p];
                    Q := Q \ {p};
                }
            }
        } else if (win = 3) {
    W_wait_commit:
            while (committed = FALSE) {
                SNAPSHOT_Read(ret);
                if (ret.val # orig.val) { committed := TRUE; }
                else if (ret.val = -1) {
                    skip;
                }
            };
        };
    W_commit:
        if (win = 0 \/ win = 1 \/ win = 2) {
            CAS(ret, Primary, orig, nVal);
            assert ret.val = -1 \/ ret.val = orig.val;
            curCommitID := curCommitID + 1;
            assert curCommitID = nVal.commitID;
            commitHist := commitHist \o <<curCommitID>>;
        } else if (win = 3 \/ win = 4) {
            commitHist := InsertAfter(commitHist,
                                      MaxIdxLessThan(commitHist, curCommitID),
                                      curCommitID);
        } else {
            assert win = -1; \* deal with backup failure
        };
    W_fini_0:
        retv[self] := 0;
        return;
    }
    
    fair process (c \in Clients)
    variable cntr = 0, readVal = -1; 
    {
    start:
        while (cntr < STOP) {
            call SNAPSHOT_Write();
    proceed:
            cntr := cntr + 1;
        }
    }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "6e81a701" /\ chksum(tla) = "5a5dec5d")
\* Procedure variable voteVal of procedure EvalRules at line 47 col 14 changed to voteVal_
\* Procedure variable voteCnt of procedure EvalRules at line 48 col 14 changed to voteCnt_
\* Procedure variable majVoteVal of procedure EvalRules at line 49 col 14 changed to majVoteVal_
\* Procedure variable votes of procedure SNAPSHOT_Write at line 100 col 14 changed to votes_
\* Parameter votes of procedure EvalRules at line 46 col 25 changed to votes_E
\* Parameter origVal of procedure EvalRules at line 46 col 62 changed to origVal_
\* Parameter swapVal of procedure EvalRules at line 46 col 79 changed to swapVal_
VARIABLES db, up, FailNum, Primary, Backups, retv, commitHist, pc, stack

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

VARIABLES votes_E, origVal_, swapVal_, voteVal_, voteCnt_, majVoteVal_, votes, 
          origVal, swapVal, voteVal, voteCnt, majVoteVal, tmp, pr, orig, nVal, 
          ret, votes_, Q, committed, win, curCommitID, cntr, readVal

vars == << db, up, FailNum, Primary, Backups, retv, commitHist, pc, stack, 
           votes_E, origVal_, swapVal_, voteVal_, voteCnt_, majVoteVal_, 
           votes, origVal, swapVal, voteVal, voteCnt, majVoteVal, tmp, pr, 
           orig, nVal, ret, votes_, Q, committed, win, curCommitID, cntr, 
           readVal >>

ProcSet == (Clients)

Init == (* Global variables *)
        /\ db = [n \in MNs |-> [val|->0, commitID|->0]]
        /\ up = [n \in Nodes |-> TRUE]
        /\ FailNum = FAILNUM
        /\ Primary = 1
        /\ Backups = MNs \ {1}
        /\ retv = [n \in Clients |-> 0]
        /\ commitHist = <<0>>
        (* Procedure EvalRules *)
        /\ votes_E = [ self \in ProcSet |-> [n \in Backups |-> FailRec]]
        /\ origVal_ = [ self \in ProcSet |-> FailRec]
        /\ swapVal_ = [ self \in ProcSet |-> FailRec]
        /\ voteVal_ = [ self \in ProcSet |-> getVoteVal(votes_E[self])]
        /\ voteCnt_ = [ self \in ProcSet |-> getVoteCnt(voteVal_[self], votes_E[self])]
        /\ majVoteVal_ = [ self \in ProcSet |-> -1]
        (* Procedure EvalRulesN *)
        /\ votes = [ self \in ProcSet |-> [n \in Backups |-> FailRec]]
        /\ origVal = [ self \in ProcSet |-> FailRec]
        /\ swapVal = [ self \in ProcSet |-> FailRec]
        /\ voteVal = [ self \in ProcSet |-> getVoteVal(votes[self])]
        /\ voteCnt = [ self \in ProcSet |-> getVoteCnt(voteVal[self], votes[self])]
        /\ majVoteVal = [ self \in ProcSet |-> -1]
        /\ tmp = [ self \in ProcSet |-> -3]
        /\ pr = [ self \in ProcSet |-> FailRec]
        (* Procedure SNAPSHOT_Write *)
        /\ orig = [ self \in ProcSet |-> FailRec]
        /\ nVal = [ self \in ProcSet |-> FailRec]
        /\ ret = [ self \in ProcSet |-> FailRec]
        /\ votes_ = [ self \in ProcSet |-> [n \in Backups |-> FailRec]]
        /\ Q = [ self \in ProcSet |-> {}]
        /\ committed = [ self \in ProcSet |-> FALSE]
        /\ win = [ self \in ProcSet |-> -1]
        /\ curCommitID = [ self \in ProcSet |-> -1]
        (* Process c *)
        /\ cntr = [self \in Clients |-> 0]
        /\ readVal = [self \in Clients |-> -1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start"]

EVAL_ST(self) == /\ pc[self] = "EVAL_ST"
                 /\ majVoteVal_' = [majVoteVal_ EXCEPT ![self] = getMajorityVoteVal(voteVal_[self], voteCnt_[self])]
                 /\ IF -1 \in voteVal_[self]
                       THEN /\ retv' = [retv EXCEPT ![self] = -1]
                       ELSE /\ IF voteCnt_[self][majVoteVal_'[self]] = NumMN - 1
                                  THEN /\ retv' = [retv EXCEPT ![self] = IF majVoteVal_'[self] = origVal_[self].val THEN 0 ELSE 3]
                                  ELSE /\ IF 2 * voteCnt_[self][majVoteVal_'[self]] > NumMN - 1
                                             THEN /\ retv' = [retv EXCEPT ![self] = IF majVoteVal_'[self] = origVal_[self].val THEN 1 ELSE 3]
                                             ELSE /\ IF db[Primary].val # origVal_[self].val
                                                        THEN /\ retv' = [retv EXCEPT ![self] = 4]
                                                        ELSE /\ IF getVoteMin(voteVal_[self], origVal_[self].val, swapVal_[self].val) = swapVal_[self].val
                                                                   THEN /\ retv' = [retv EXCEPT ![self] = 2]
                                                                   ELSE /\ retv' = [retv EXCEPT ![self] = 3]
                 /\ pc' = [pc EXCEPT ![self] = "EVAL_FINI"]
                 /\ UNCHANGED << db, up, FailNum, Primary, Backups, commitHist, 
                                 stack, votes_E, origVal_, swapVal_, voteVal_, 
                                 voteCnt_, votes, origVal, swapVal, voteVal, 
                                 voteCnt, majVoteVal, tmp, pr, orig, nVal, ret, 
                                 votes_, Q, committed, win, curCommitID, cntr, 
                                 readVal >>

EVAL_FINI(self) == /\ pc[self] = "EVAL_FINI"
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ voteVal_' = [voteVal_ EXCEPT ![self] = Head(stack[self]).voteVal_]
                   /\ voteCnt_' = [voteCnt_ EXCEPT ![self] = Head(stack[self]).voteCnt_]
                   /\ majVoteVal_' = [majVoteVal_ EXCEPT ![self] = Head(stack[self]).majVoteVal_]
                   /\ votes_E' = [votes_E EXCEPT ![self] = Head(stack[self]).votes_E]
                   /\ origVal_' = [origVal_ EXCEPT ![self] = Head(stack[self]).origVal_]
                   /\ swapVal_' = [swapVal_ EXCEPT ![self] = Head(stack[self]).swapVal_]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << db, up, FailNum, Primary, Backups, retv, 
                                   commitHist, votes, origVal, swapVal, 
                                   voteVal, voteCnt, majVoteVal, tmp, pr, orig, 
                                   nVal, ret, votes_, Q, committed, win, 
                                   curCommitID, cntr, readVal >>

EvalRules(self) == EVAL_ST(self) \/ EVAL_FINI(self)

EVALN_ST1(self) == /\ pc[self] = "EVALN_ST1"
                   /\ majVoteVal' = [majVoteVal EXCEPT ![self] = getMajorityVoteVal(voteVal[self], voteCnt[self])]
                   /\ IF -1 \in voteVal[self]
                         THEN /\ tmp' = [tmp EXCEPT ![self] = -1]
                         ELSE /\ IF voteCnt[self][majVoteVal'[self]] = NumMN - 1
                                    THEN /\ tmp' = [tmp EXCEPT ![self] = IF majVoteVal'[self] = origVal[self].val THEN 0 ELSE 3]
                                    ELSE /\ IF 2 * voteCnt[self][majVoteVal'[self]] > NumMN - 1
                                               THEN /\ tmp' = [tmp EXCEPT ![self] = IF majVoteVal'[self] = origVal[self].val THEN 1 ELSE 3]
                                               ELSE /\ TRUE
                                                    /\ tmp' = tmp
                   /\ IF tmp'[self] = -3
                         THEN /\ pc' = [pc EXCEPT ![self] = "EVALN_recheck"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "EVALN_FINI"]
                   /\ UNCHANGED << db, up, FailNum, Primary, Backups, retv, 
                                   commitHist, stack, votes_E, origVal_, 
                                   swapVal_, voteVal_, voteCnt_, majVoteVal_, 
                                   votes, origVal, swapVal, voteVal, voteCnt, 
                                   pr, orig, nVal, ret, votes_, Q, committed, 
                                   win, curCommitID, cntr, readVal >>

EVALN_recheck(self) == /\ pc[self] = "EVALN_recheck"
                       /\ pr' = [pr EXCEPT ![self] = IF up[Primary] THEN db[Primary] ELSE FailRec]
                       /\ pc' = [pc EXCEPT ![self] = "EVALN_ST2"]
                       /\ UNCHANGED << db, up, FailNum, Primary, Backups, retv, 
                                       commitHist, stack, votes_E, origVal_, 
                                       swapVal_, voteVal_, voteCnt_, 
                                       majVoteVal_, votes, origVal, swapVal, 
                                       voteVal, voteCnt, majVoteVal, tmp, orig, 
                                       nVal, ret, votes_, Q, committed, win, 
                                       curCommitID, cntr, readVal >>

EVALN_ST2(self) == /\ pc[self] = "EVALN_ST2"
                   /\ IF pr[self].val # origVal[self].val
                         THEN /\ tmp' = [tmp EXCEPT ![self] = 4]
                         ELSE /\ IF getVoteMin(voteVal[self], origVal[self].val, swapVal[self].val) = swapVal[self].val
                                    THEN /\ tmp' = [tmp EXCEPT ![self] = 2]
                                    ELSE /\ tmp' = [tmp EXCEPT ![self] = 3]
                   /\ pc' = [pc EXCEPT ![self] = "EVALN_FINI"]
                   /\ UNCHANGED << db, up, FailNum, Primary, Backups, retv, 
                                   commitHist, stack, votes_E, origVal_, 
                                   swapVal_, voteVal_, voteCnt_, majVoteVal_, 
                                   votes, origVal, swapVal, voteVal, voteCnt, 
                                   majVoteVal, pr, orig, nVal, ret, votes_, Q, 
                                   committed, win, curCommitID, cntr, readVal >>

EVALN_FINI(self) == /\ pc[self] = "EVALN_FINI"
                    /\ retv' = [retv EXCEPT ![self] = tmp[self]]
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ voteVal' = [voteVal EXCEPT ![self] = Head(stack[self]).voteVal]
                    /\ voteCnt' = [voteCnt EXCEPT ![self] = Head(stack[self]).voteCnt]
                    /\ majVoteVal' = [majVoteVal EXCEPT ![self] = Head(stack[self]).majVoteVal]
                    /\ tmp' = [tmp EXCEPT ![self] = Head(stack[self]).tmp]
                    /\ pr' = [pr EXCEPT ![self] = Head(stack[self]).pr]
                    /\ votes' = [votes EXCEPT ![self] = Head(stack[self]).votes]
                    /\ origVal' = [origVal EXCEPT ![self] = Head(stack[self]).origVal]
                    /\ swapVal' = [swapVal EXCEPT ![self] = Head(stack[self]).swapVal]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                    commitHist, votes_E, origVal_, swapVal_, 
                                    voteVal_, voteCnt_, majVoteVal_, orig, 
                                    nVal, ret, votes_, Q, committed, win, 
                                    curCommitID, cntr, readVal >>

EvalRulesN(self) == EVALN_ST1(self) \/ EVALN_recheck(self)
                       \/ EVALN_ST2(self) \/ EVALN_FINI(self)

W_prepare(self) == /\ pc[self] = "W_prepare"
                   /\ orig' = [orig EXCEPT ![self] = IF up[Primary] THEN db[Primary] ELSE FailRec]
                   /\ nVal' = [nVal EXCEPT ![self] = [val      |-> ((orig'[self].val + 1000) \div 1000) * 1000 + self,
                                                      commitID |-> orig'[self].commitID + 1]]
                   /\ curCommitID' = [curCommitID EXCEPT ![self] = orig'[self].commitID]
                   /\ Q' = [Q EXCEPT ![self] = Backups]
                   /\ pc' = [pc EXCEPT ![self] = "W_cas_bk"]
                   /\ UNCHANGED << db, up, FailNum, Primary, Backups, retv, 
                                   commitHist, stack, votes_E, origVal_, 
                                   swapVal_, voteVal_, voteCnt_, majVoteVal_, 
                                   votes, origVal, swapVal, voteVal, voteCnt, 
                                   majVoteVal, tmp, pr, ret, votes_, committed, 
                                   win, cntr, readVal >>

W_cas_bk(self) == /\ pc[self] = "W_cas_bk"
                  /\ IF Q[self] # {}
                        THEN /\ \E p \in Q[self]:
                                  /\ votes_' = [votes_ EXCEPT ![self][p] = IF up[p] THEN db[p] ELSE FailRec]
                                  /\ IF db[p].val = orig[self].val /\ up[p]
                                        THEN /\ db' = [db EXCEPT ![p] = nVal[self]]
                                        ELSE /\ TRUE
                                             /\ db' = db
                                  /\ Q' = [Q EXCEPT ![self] = Q[self] \ {p}]
                             /\ pc' = [pc EXCEPT ![self] = "W_cas_bk"]
                             /\ UNCHANGED << stack, votes, origVal, swapVal, 
                                             voteVal, voteCnt, majVoteVal, tmp, 
                                             pr >>
                        ELSE /\ /\ origVal' = [origVal EXCEPT ![self] = orig[self]]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "EvalRulesN",
                                                                         pc        |->  "W_modify_rest",
                                                                         voteVal   |->  voteVal[self],
                                                                         voteCnt   |->  voteCnt[self],
                                                                         majVoteVal |->  majVoteVal[self],
                                                                         tmp       |->  tmp[self],
                                                                         pr        |->  pr[self],
                                                                         votes     |->  votes[self],
                                                                         origVal   |->  origVal[self],
                                                                         swapVal   |->  swapVal[self] ] >>
                                                                     \o stack[self]]
                                /\ swapVal' = [swapVal EXCEPT ![self] = nVal[self]]
                                /\ votes' = [votes EXCEPT ![self] = votes_[self]]
                             /\ voteVal' = [voteVal EXCEPT ![self] = getVoteVal(votes'[self])]
                             /\ voteCnt' = [voteCnt EXCEPT ![self] = getVoteCnt(voteVal'[self], votes'[self])]
                             /\ majVoteVal' = [majVoteVal EXCEPT ![self] = -1]
                             /\ tmp' = [tmp EXCEPT ![self] = -3]
                             /\ pr' = [pr EXCEPT ![self] = FailRec]
                             /\ pc' = [pc EXCEPT ![self] = "EVALN_ST1"]
                             /\ UNCHANGED << db, votes_, Q >>
                  /\ UNCHANGED << up, FailNum, Primary, Backups, retv, 
                                  commitHist, votes_E, origVal_, swapVal_, 
                                  voteVal_, voteCnt_, majVoteVal_, orig, nVal, 
                                  ret, committed, win, curCommitID, cntr, 
                                  readVal >>

W_modify_rest(self) == /\ pc[self] = "W_modify_rest"
                       /\ win' = [win EXCEPT ![self] = retv[self]]
                       /\ IF win'[self] = 1 \/ win'[self] = 2
                             THEN /\ Q' = [Q EXCEPT ![self] = Backups]
                                  /\ pc' = [pc EXCEPT ![self] = "W_consist_backup"]
                             ELSE /\ IF win'[self] = 3
                                        THEN /\ pc' = [pc EXCEPT ![self] = "W_wait_commit"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "W_commit"]
                                  /\ Q' = Q
                       /\ UNCHANGED << db, up, FailNum, Primary, Backups, retv, 
                                       commitHist, stack, votes_E, origVal_, 
                                       swapVal_, voteVal_, voteCnt_, 
                                       majVoteVal_, votes, origVal, swapVal, 
                                       voteVal, voteCnt, majVoteVal, tmp, pr, 
                                       orig, nVal, ret, votes_, committed, 
                                       curCommitID, cntr, readVal >>

W_consist_backup(self) == /\ pc[self] = "W_consist_backup"
                          /\ IF Q[self] # {}
                                THEN /\ \E p \in Q[self]:
                                          /\ db' = [db EXCEPT ![p] = IF up[p] THEN nVal[self] ELSE db[p]]
                                          /\ Q' = [Q EXCEPT ![self] = Q[self] \ {p}]
                                     /\ pc' = [pc EXCEPT ![self] = "W_consist_backup"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "W_commit"]
                                     /\ UNCHANGED << db, Q >>
                          /\ UNCHANGED << up, FailNum, Primary, Backups, retv, 
                                          commitHist, stack, votes_E, origVal_, 
                                          swapVal_, voteVal_, voteCnt_, 
                                          majVoteVal_, votes, origVal, swapVal, 
                                          voteVal, voteCnt, majVoteVal, tmp, 
                                          pr, orig, nVal, ret, votes_, 
                                          committed, win, curCommitID, cntr, 
                                          readVal >>

W_wait_commit(self) == /\ pc[self] = "W_wait_commit"
                       /\ IF committed[self] = FALSE
                             THEN /\ ret' = [ret EXCEPT ![self] = IF up[Primary] THEN db[Primary] ELSE FailRec]
                                  /\ IF ret'[self].val # orig[self].val
                                        THEN /\ committed' = [committed EXCEPT ![self] = TRUE]
                                        ELSE /\ IF ret'[self].val = -1
                                                   THEN /\ TRUE
                                                   ELSE /\ TRUE
                                             /\ UNCHANGED committed
                                  /\ pc' = [pc EXCEPT ![self] = "W_wait_commit"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "W_commit"]
                                  /\ UNCHANGED << ret, committed >>
                       /\ UNCHANGED << db, up, FailNum, Primary, Backups, retv, 
                                       commitHist, stack, votes_E, origVal_, 
                                       swapVal_, voteVal_, voteCnt_, 
                                       majVoteVal_, votes, origVal, swapVal, 
                                       voteVal, voteCnt, majVoteVal, tmp, pr, 
                                       orig, nVal, votes_, Q, win, curCommitID, 
                                       cntr, readVal >>

W_commit(self) == /\ pc[self] = "W_commit"
                  /\ IF win[self] = 0 \/ win[self] = 1 \/ win[self] = 2
                        THEN /\ ret' = [ret EXCEPT ![self] = IF up[Primary] THEN db[Primary] ELSE FailRec]
                             /\ IF db[Primary].val = orig[self].val /\ up[Primary]
                                   THEN /\ db' = [db EXCEPT ![Primary] = nVal[self]]
                                   ELSE /\ TRUE
                                        /\ db' = db
                             /\ Assert(ret'[self].val = -1 \/ ret'[self].val = orig[self].val, 
                                       "Failure of assertion at line 142, column 13.")
                             /\ curCommitID' = [curCommitID EXCEPT ![self] = curCommitID[self] + 1]
                             /\ Assert(curCommitID'[self] = nVal[self].commitID, 
                                       "Failure of assertion at line 144, column 13.")
                             /\ commitHist' = commitHist \o <<curCommitID'[self]>>
                        ELSE /\ IF win[self] = 3 \/ win[self] = 4
                                   THEN /\ commitHist' = InsertAfter(commitHist,
                                                                     MaxIdxLessThan(commitHist, curCommitID[self]),
                                                                     curCommitID[self])
                                   ELSE /\ Assert(win[self] = -1, 
                                                  "Failure of assertion at line 151, column 13.")
                                        /\ UNCHANGED commitHist
                             /\ UNCHANGED << db, ret, curCommitID >>
                  /\ pc' = [pc EXCEPT ![self] = "W_fini_0"]
                  /\ UNCHANGED << up, FailNum, Primary, Backups, retv, stack, 
                                  votes_E, origVal_, swapVal_, voteVal_, 
                                  voteCnt_, majVoteVal_, votes, origVal, 
                                  swapVal, voteVal, voteCnt, majVoteVal, tmp, 
                                  pr, orig, nVal, votes_, Q, committed, win, 
                                  cntr, readVal >>

W_fini_0(self) == /\ pc[self] = "W_fini_0"
                  /\ retv' = [retv EXCEPT ![self] = 0]
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ orig' = [orig EXCEPT ![self] = Head(stack[self]).orig]
                  /\ nVal' = [nVal EXCEPT ![self] = Head(stack[self]).nVal]
                  /\ ret' = [ret EXCEPT ![self] = Head(stack[self]).ret]
                  /\ votes_' = [votes_ EXCEPT ![self] = Head(stack[self]).votes_]
                  /\ Q' = [Q EXCEPT ![self] = Head(stack[self]).Q]
                  /\ committed' = [committed EXCEPT ![self] = Head(stack[self]).committed]
                  /\ win' = [win EXCEPT ![self] = Head(stack[self]).win]
                  /\ curCommitID' = [curCommitID EXCEPT ![self] = Head(stack[self]).curCommitID]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                  commitHist, votes_E, origVal_, swapVal_, 
                                  voteVal_, voteCnt_, majVoteVal_, votes, 
                                  origVal, swapVal, voteVal, voteCnt, 
                                  majVoteVal, tmp, pr, cntr, readVal >>

SNAPSHOT_Write(self) == W_prepare(self) \/ W_cas_bk(self)
                           \/ W_modify_rest(self) \/ W_consist_backup(self)
                           \/ W_wait_commit(self) \/ W_commit(self)
                           \/ W_fini_0(self)

start(self) == /\ pc[self] = "start"
               /\ IF cntr[self] < STOP
                     THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "SNAPSHOT_Write",
                                                                   pc        |->  "proceed",
                                                                   orig      |->  orig[self],
                                                                   nVal      |->  nVal[self],
                                                                   ret       |->  ret[self],
                                                                   votes_    |->  votes_[self],
                                                                   Q         |->  Q[self],
                                                                   committed |->  committed[self],
                                                                   win       |->  win[self],
                                                                   curCommitID |->  curCommitID[self] ] >>
                                                               \o stack[self]]
                          /\ orig' = [orig EXCEPT ![self] = FailRec]
                          /\ nVal' = [nVal EXCEPT ![self] = FailRec]
                          /\ ret' = [ret EXCEPT ![self] = FailRec]
                          /\ votes_' = [votes_ EXCEPT ![self] = [n \in Backups |-> FailRec]]
                          /\ Q' = [Q EXCEPT ![self] = {}]
                          /\ committed' = [committed EXCEPT ![self] = FALSE]
                          /\ win' = [win EXCEPT ![self] = -1]
                          /\ curCommitID' = [curCommitID EXCEPT ![self] = -1]
                          /\ pc' = [pc EXCEPT ![self] = "W_prepare"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << stack, orig, nVal, ret, votes_, Q, 
                                          committed, win, curCommitID >>
               /\ UNCHANGED << db, up, FailNum, Primary, Backups, retv, 
                               commitHist, votes_E, origVal_, swapVal_, 
                               voteVal_, voteCnt_, majVoteVal_, votes, origVal, 
                               swapVal, voteVal, voteCnt, majVoteVal, tmp, pr, 
                               cntr, readVal >>

proceed(self) == /\ pc[self] = "proceed"
                 /\ cntr' = [cntr EXCEPT ![self] = cntr[self] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "start"]
                 /\ UNCHANGED << db, up, FailNum, Primary, Backups, retv, 
                                 commitHist, stack, votes_E, origVal_, 
                                 swapVal_, voteVal_, voteCnt_, majVoteVal_, 
                                 votes, origVal, swapVal, voteVal, voteCnt, 
                                 majVoteVal, tmp, pr, orig, nVal, ret, votes_, 
                                 Q, committed, win, curCommitID, readVal >>

c(self) == start(self) \/ proceed(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ EvalRules(self) \/ EvalRulesN(self)
                               \/ SNAPSHOT_Write(self))
           \/ (\E self \in Clients: c(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : /\ WF_vars(c(self))
                                 /\ WF_vars(SNAPSHOT_Write(self))
                                 /\ WF_vars(EvalRulesN(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Lin == (\A self \in ProcSet: pc[self] = "Done") => 
            /\ Len(commitHist) = NumClient * STOP + 1
            /\ \A i, j \in 1..Len(commitHist): (i < j => commitHist[i] <= commitHist[j])

Consistent == (\A self \in ProcSet: pc[self] = "Done") => \A i, j \in MNs: db[i] = db[j]
=============================================================================
\* Modification History
\* Last modified Mon Sep 05 16:37:46 CST 2022 by berna
\* Created Sun Sep 04 11:12:43 CST 2022 by berna
