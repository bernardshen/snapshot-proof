------------------------------ MODULE SNAPSHOT ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT NumMN, NumClient, FAILNUM, STOP

MNs     == 1..NumMN
Clients == (NumMN + 1)..(NumMN + NumClient) 
Nodes   == 1..(NumMN + NumClient)

(*--algorithm SNAPSHOT {
    variable db = [n \in MNs |-> 0],
             up = [n \in Nodes |-> TRUE],
             FailNum = FAILNUM,
             Primary = 1,
             Backups = MNs \ {1},
             retv = [n \in Clients |-> 0],
             primaryHist = <<0>>;
             
    define {
        getVoteMin(voteVal, origVal, swapVal) == IF origVal \in voteVal 
                                        THEN CHOOSE i \in ((voteVal \ {origVal}) \union {swapVal}): (\A j \in ((voteVal \ {origVal}) \union {swapVal}): i <= j)
                                        ELSE -1
        getVoteVal(votes) == {votes[i] : i \in Backups} 
        getVoteCnt(voteVal, votes) == [i \in voteVal |-> Cardinality(UNION {{j \in Backups: votes[j] = i}})]
        getMajorityVoteVal(voteVal, voteCnt) == CHOOSE i \in voteVal: (\A j \in voteVal: voteCnt[j] <= voteCnt[i]) 
    }
    
    macro CAS(ret, id, old, new) {
        \* return the original value in the store if the node is up
        \* return -1 to indicate the node failure
        ret := IF up[id] THEN db[id] ELSE -1;
        if (db[id] = old /\ up[id]) {
            db[id] := new
        }
    }

    macro SNAPSHOT_Read(ret) {
        ret := IF up[Primary] THEN db[Primary] ELSE -1;
    }
    
    procedure EvalRules(votes = [n \in Backups |-> -1], origVal=0, swapVal=0)
    variable voteVal = getVoteVal(votes),
             voteCnt = getVoteCnt(voteVal, votes),
             majVoteVal = -1;
    {
    EVAL_ST:
        majVoteVal := getMajorityVoteVal(voteVal, voteCnt);
        if (-1 \in voteVal) { retv[self] := -1; }
        else if (voteCnt[majVoteVal] = NumMN - 1) {
            retv[self] := IF majVoteVal = origVal THEN 0 ELSE 3;
        } else if (2 * voteCnt[majVoteVal] > NumMN - 1) {
            retv[self] := IF majVoteVal = origVal THEN 1 ELSE 3;
        } else if (db[Primary] # origVal) {     \* need to read the primary again before using rule 3
            retv[self] := 4;
        } else if (getVoteMin(voteVal, origVal, swapVal) = swapVal) {
            retv[self] := 2;
        } else {
            retv[self] := 3;
        };
    EVAL_FINI:
        return
    }
    
    procedure SNAPSHOT_Write()
    variable orig = -1, ret = -1, nVal = 0,
             votes = [n \in Backups |-> -1],
             Q = {}, committed = FALSE, win = -1;
    {
    W_prepare:
        SNAPSHOT_Read(orig);
        nVal := orig + 1000 + self;
        Q := Backups;
    W_cas_bk:
        while (Q # {}) {
            with (p \in Q) {
                CAS(votes[p], p, orig, nVal);
                Q := Q \ {p};
            }
        };
        call EvalRules(votes, orig, nVal);
    W_modify_rest:
        win := retv[self];
        assert win \in {-1, 0, 1, 2, 3, 4};
        if (win = 1 \/ win = 2) {
            Q := Backups;
    W_modify_all_bk:
            while (Q # {}) {
                with (p \in Q) {
                    db[p] := IF up[p] THEN nVal ELSE db[p];
                    Q := Q \ {p};
                }
            };
            CAS(ret, Primary, orig, nVal);
            assert ret = -1 \/ ret = orig;
            primaryHist := primaryHist \o <<nVal>>;
        } else if (win = 0) {
            CAS(ret, Primary, orig, nVal);
            assert ret = -1 \/ ret = orig;
            primaryHist := primaryHist \o <<nVal>>;
        } else if (win = 3) {
            committed := FALSE;
    W_wait_commit:
            while (committed = FALSE) {
                SNAPSHOT_Read(ret);
                if (ret # orig) { committed := TRUE; }
                else if (ret = -1) {
                    skip; \* deal with primary failure
                }
            }
        } else if (win = 4) {
            skip; \* the write round has already finished because the loser is too 
        } else {
            assert win = -1;
            skip; \* deal with failure
        };
    W_fini_0:
        retv[self] := 0;
        return;
    }
    
    fair process (c \in Clients)
    variable cntr = 0, readVal = -1; 
    {
    start:+
        while (cntr <= STOP) {
        either {
\*            SNAPSHOT_Read(readVal);
            skip;
        }
        or { 
            call SNAPSHOT_Write();
        }; 
    proceed:+
        cntr := cntr + 1;
        }
    }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "b4f3332a" /\ chksum(tla) = "772580b5")
\* Procedure variable votes of procedure SNAPSHOT_Write at line 66 col 14 changed to votes_
VARIABLES db, up, FailNum, Primary, Backups, retv, primaryHist, pc, stack

(* define statement *)
getVoteMin(voteVal, origVal, swapVal) == IF origVal \in voteVal
                                THEN CHOOSE i \in ((voteVal \ {origVal}) \union {swapVal}): (\A j \in ((voteVal \ {origVal}) \union {swapVal}): i <= j)
                                ELSE -1
getVoteVal(votes) == {votes[i] : i \in Backups}
getVoteCnt(voteVal, votes) == [i \in voteVal |-> Cardinality(UNION {{j \in Backups: votes[j] = i}})]
getMajorityVoteVal(voteVal, voteCnt) == CHOOSE i \in voteVal: (\A j \in voteVal: voteCnt[j] <= voteCnt[i])

VARIABLES votes, origVal, swapVal, voteVal, voteCnt, majVoteVal, orig, ret, 
          nVal, votes_, Q, committed, win, cntr, readVal

vars == << db, up, FailNum, Primary, Backups, retv, primaryHist, pc, stack, 
           votes, origVal, swapVal, voteVal, voteCnt, majVoteVal, orig, ret, 
           nVal, votes_, Q, committed, win, cntr, readVal >>

ProcSet == (Clients)

Init == (* Global variables *)
        /\ db = [n \in MNs |-> 0]
        /\ up = [n \in Nodes |-> TRUE]
        /\ FailNum = FAILNUM
        /\ Primary = 1
        /\ Backups = MNs \ {1}
        /\ retv = [n \in Clients |-> 0]
        /\ primaryHist = <<0>>
        (* Procedure EvalRules *)
        /\ votes = [ self \in ProcSet |-> [n \in Backups |-> -1]]
        /\ origVal = [ self \in ProcSet |-> 0]
        /\ swapVal = [ self \in ProcSet |-> 0]
        /\ voteVal = [ self \in ProcSet |-> getVoteVal(votes[self])]
        /\ voteCnt = [ self \in ProcSet |-> getVoteCnt(voteVal[self], votes[self])]
        /\ majVoteVal = [ self \in ProcSet |-> -1]
        (* Procedure SNAPSHOT_Write *)
        /\ orig = [ self \in ProcSet |-> -1]
        /\ ret = [ self \in ProcSet |-> -1]
        /\ nVal = [ self \in ProcSet |-> 0]
        /\ votes_ = [ self \in ProcSet |-> [n \in Backups |-> -1]]
        /\ Q = [ self \in ProcSet |-> {}]
        /\ committed = [ self \in ProcSet |-> FALSE]
        /\ win = [ self \in ProcSet |-> -1]
        (* Process c *)
        /\ cntr = [self \in Clients |-> 0]
        /\ readVal = [self \in Clients |-> -1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "start"]

EVAL_ST(self) == /\ pc[self] = "EVAL_ST"
                 /\ majVoteVal' = [majVoteVal EXCEPT ![self] = getMajorityVoteVal(voteVal[self], voteCnt[self])]
                 /\ IF -1 \in voteVal[self]
                       THEN /\ retv' = [retv EXCEPT ![self] = -1]
                       ELSE /\ IF voteCnt[self][majVoteVal'[self]] = NumMN - 1
                                  THEN /\ retv' = [retv EXCEPT ![self] = IF majVoteVal'[self] = origVal[self] THEN 0 ELSE 3]
                                  ELSE /\ IF 2 * voteCnt[self][majVoteVal'[self]] > NumMN - 1
                                             THEN /\ retv' = [retv EXCEPT ![self] = IF majVoteVal'[self] = origVal[self] THEN 1 ELSE 3]
                                             ELSE /\ IF db[Primary] # origVal[self]
                                                        THEN /\ retv' = [retv EXCEPT ![self] = 4]
                                                        ELSE /\ IF getVoteMin(voteVal[self], origVal[self], swapVal[self]) = swapVal[self]
                                                                   THEN /\ retv' = [retv EXCEPT ![self] = 2]
                                                                   ELSE /\ retv' = [retv EXCEPT ![self] = 3]
                 /\ pc' = [pc EXCEPT ![self] = "EVAL_FINI"]
                 /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                 primaryHist, stack, votes, origVal, swapVal, 
                                 voteVal, voteCnt, orig, ret, nVal, votes_, Q, 
                                 committed, win, cntr, readVal >>

EVAL_FINI(self) == /\ pc[self] = "EVAL_FINI"
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ voteVal' = [voteVal EXCEPT ![self] = Head(stack[self]).voteVal]
                   /\ voteCnt' = [voteCnt EXCEPT ![self] = Head(stack[self]).voteCnt]
                   /\ majVoteVal' = [majVoteVal EXCEPT ![self] = Head(stack[self]).majVoteVal]
                   /\ votes' = [votes EXCEPT ![self] = Head(stack[self]).votes]
                   /\ origVal' = [origVal EXCEPT ![self] = Head(stack[self]).origVal]
                   /\ swapVal' = [swapVal EXCEPT ![self] = Head(stack[self]).swapVal]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << db, up, FailNum, Primary, Backups, retv, 
                                   primaryHist, orig, ret, nVal, votes_, Q, 
                                   committed, win, cntr, readVal >>

EvalRules(self) == EVAL_ST(self) \/ EVAL_FINI(self)

W_prepare(self) == /\ pc[self] = "W_prepare"
                   /\ orig' = [orig EXCEPT ![self] = IF up[Primary] THEN db[Primary] ELSE -1]
                   /\ nVal' = [nVal EXCEPT ![self] = orig'[self] + 1000 + self]
                   /\ Q' = [Q EXCEPT ![self] = Backups]
                   /\ pc' = [pc EXCEPT ![self] = "W_cas_bk"]
                   /\ UNCHANGED << db, up, FailNum, Primary, Backups, retv, 
                                   primaryHist, stack, votes, origVal, swapVal, 
                                   voteVal, voteCnt, majVoteVal, ret, votes_, 
                                   committed, win, cntr, readVal >>

W_cas_bk(self) == /\ pc[self] = "W_cas_bk"
                  /\ IF Q[self] # {}
                        THEN /\ \E p \in Q[self]:
                                  /\ votes_' = [votes_ EXCEPT ![self][p] = IF up[p] THEN db[p] ELSE -1]
                                  /\ IF db[p] = orig[self] /\ up[p]
                                        THEN /\ db' = [db EXCEPT ![p] = nVal[self]]
                                        ELSE /\ TRUE
                                             /\ db' = db
                                  /\ Q' = [Q EXCEPT ![self] = Q[self] \ {p}]
                             /\ pc' = [pc EXCEPT ![self] = "W_cas_bk"]
                             /\ UNCHANGED << stack, votes, origVal, swapVal, 
                                             voteVal, voteCnt, majVoteVal >>
                        ELSE /\ /\ origVal' = [origVal EXCEPT ![self] = orig[self]]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "EvalRules",
                                                                         pc        |->  "W_modify_rest",
                                                                         voteVal   |->  voteVal[self],
                                                                         voteCnt   |->  voteCnt[self],
                                                                         majVoteVal |->  majVoteVal[self],
                                                                         votes     |->  votes[self],
                                                                         origVal   |->  origVal[self],
                                                                         swapVal   |->  swapVal[self] ] >>
                                                                     \o stack[self]]
                                /\ swapVal' = [swapVal EXCEPT ![self] = nVal[self]]
                                /\ votes' = [votes EXCEPT ![self] = votes_[self]]
                             /\ voteVal' = [voteVal EXCEPT ![self] = getVoteVal(votes'[self])]
                             /\ voteCnt' = [voteCnt EXCEPT ![self] = getVoteCnt(voteVal'[self], votes'[self])]
                             /\ majVoteVal' = [majVoteVal EXCEPT ![self] = -1]
                             /\ pc' = [pc EXCEPT ![self] = "EVAL_ST"]
                             /\ UNCHANGED << db, votes_, Q >>
                  /\ UNCHANGED << up, FailNum, Primary, Backups, retv, 
                                  primaryHist, orig, ret, nVal, committed, win, 
                                  cntr, readVal >>

W_modify_rest(self) == /\ pc[self] = "W_modify_rest"
                       /\ win' = [win EXCEPT ![self] = retv[self]]
                       /\ Assert(win'[self] \in {-1, 0, 1, 2, 3, 4}, 
                                 "Failure of assertion at line 83, column 9.")
                       /\ IF win'[self] = 1 \/ win'[self] = 2
                             THEN /\ Q' = [Q EXCEPT ![self] = Backups]
                                  /\ pc' = [pc EXCEPT ![self] = "W_modify_all_bk"]
                                  /\ UNCHANGED << db, primaryHist, ret, 
                                                  committed >>
                             ELSE /\ IF win'[self] = 0
                                        THEN /\ ret' = [ret EXCEPT ![self] = IF up[Primary] THEN db[Primary] ELSE -1]
                                             /\ IF db[Primary] = orig[self] /\ up[Primary]
                                                   THEN /\ db' = [db EXCEPT ![Primary] = nVal[self]]
                                                   ELSE /\ TRUE
                                                        /\ db' = db
                                             /\ Assert(ret'[self] = -1 \/ ret'[self] = orig[self], 
                                                       "Failure of assertion at line 98, column 13.")
                                             /\ primaryHist' = primaryHist \o <<nVal[self]>>
                                             /\ pc' = [pc EXCEPT ![self] = "W_fini_0"]
                                             /\ UNCHANGED committed
                                        ELSE /\ IF win'[self] = 3
                                                   THEN /\ committed' = [committed EXCEPT ![self] = FALSE]
                                                        /\ pc' = [pc EXCEPT ![self] = "W_wait_commit"]
                                                   ELSE /\ IF win'[self] = 4
                                                              THEN /\ TRUE
                                                              ELSE /\ Assert(win'[self] = -1, 
                                                                             "Failure of assertion at line 113, column 13.")
                                                                   /\ TRUE
                                                        /\ pc' = [pc EXCEPT ![self] = "W_fini_0"]
                                                        /\ UNCHANGED committed
                                             /\ UNCHANGED << db, primaryHist, 
                                                             ret >>
                                  /\ Q' = Q
                       /\ UNCHANGED << up, FailNum, Primary, Backups, retv, 
                                       stack, votes, origVal, swapVal, voteVal, 
                                       voteCnt, majVoteVal, orig, nVal, votes_, 
                                       cntr, readVal >>

W_modify_all_bk(self) == /\ pc[self] = "W_modify_all_bk"
                         /\ IF Q[self] # {}
                               THEN /\ \E p \in Q[self]:
                                         /\ db' = [db EXCEPT ![p] = IF up[p] THEN nVal[self] ELSE db[p]]
                                         /\ Q' = [Q EXCEPT ![self] = Q[self] \ {p}]
                                    /\ pc' = [pc EXCEPT ![self] = "W_modify_all_bk"]
                                    /\ UNCHANGED << primaryHist, ret >>
                               ELSE /\ ret' = [ret EXCEPT ![self] = IF up[Primary] THEN db[Primary] ELSE -1]
                                    /\ IF db[Primary] = orig[self] /\ up[Primary]
                                          THEN /\ db' = [db EXCEPT ![Primary] = nVal[self]]
                                          ELSE /\ TRUE
                                               /\ db' = db
                                    /\ Assert(ret'[self] = -1 \/ ret'[self] = orig[self], 
                                              "Failure of assertion at line 94, column 13.")
                                    /\ primaryHist' = primaryHist \o <<nVal[self]>>
                                    /\ pc' = [pc EXCEPT ![self] = "W_fini_0"]
                                    /\ Q' = Q
                         /\ UNCHANGED << up, FailNum, Primary, Backups, retv, 
                                         stack, votes, origVal, swapVal, 
                                         voteVal, voteCnt, majVoteVal, orig, 
                                         nVal, votes_, committed, win, cntr, 
                                         readVal >>

W_wait_commit(self) == /\ pc[self] = "W_wait_commit"
                       /\ IF committed[self] = FALSE
                             THEN /\ ret' = [ret EXCEPT ![self] = IF up[Primary] THEN db[Primary] ELSE -1]
                                  /\ IF ret'[self] # orig[self]
                                        THEN /\ committed' = [committed EXCEPT ![self] = TRUE]
                                        ELSE /\ IF ret'[self] = -1
                                                   THEN /\ TRUE
                                                   ELSE /\ TRUE
                                             /\ UNCHANGED committed
                                  /\ pc' = [pc EXCEPT ![self] = "W_wait_commit"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "W_fini_0"]
                                  /\ UNCHANGED << ret, committed >>
                       /\ UNCHANGED << db, up, FailNum, Primary, Backups, retv, 
                                       primaryHist, stack, votes, origVal, 
                                       swapVal, voteVal, voteCnt, majVoteVal, 
                                       orig, nVal, votes_, Q, win, cntr, 
                                       readVal >>

W_fini_0(self) == /\ pc[self] = "W_fini_0"
                  /\ retv' = [retv EXCEPT ![self] = 0]
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ orig' = [orig EXCEPT ![self] = Head(stack[self]).orig]
                  /\ ret' = [ret EXCEPT ![self] = Head(stack[self]).ret]
                  /\ nVal' = [nVal EXCEPT ![self] = Head(stack[self]).nVal]
                  /\ votes_' = [votes_ EXCEPT ![self] = Head(stack[self]).votes_]
                  /\ Q' = [Q EXCEPT ![self] = Head(stack[self]).Q]
                  /\ committed' = [committed EXCEPT ![self] = Head(stack[self]).committed]
                  /\ win' = [win EXCEPT ![self] = Head(stack[self]).win]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << db, up, FailNum, Primary, Backups, 
                                  primaryHist, votes, origVal, swapVal, 
                                  voteVal, voteCnt, majVoteVal, cntr, readVal >>

SNAPSHOT_Write(self) == W_prepare(self) \/ W_cas_bk(self)
                           \/ W_modify_rest(self) \/ W_modify_all_bk(self)
                           \/ W_wait_commit(self) \/ W_fini_0(self)

start(self) == /\ pc[self] = "start"
               /\ IF cntr[self] <= STOP
                     THEN /\ \/ /\ TRUE
                                /\ pc' = [pc EXCEPT ![self] = "proceed"]
                                /\ UNCHANGED <<stack, orig, ret, nVal, votes_, Q, committed, win>>
                             \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "SNAPSHOT_Write",
                                                                         pc        |->  "proceed",
                                                                         orig      |->  orig[self],
                                                                         ret       |->  ret[self],
                                                                         nVal      |->  nVal[self],
                                                                         votes_    |->  votes_[self],
                                                                         Q         |->  Q[self],
                                                                         committed |->  committed[self],
                                                                         win       |->  win[self] ] >>
                                                                     \o stack[self]]
                                /\ orig' = [orig EXCEPT ![self] = -1]
                                /\ ret' = [ret EXCEPT ![self] = -1]
                                /\ nVal' = [nVal EXCEPT ![self] = 0]
                                /\ votes_' = [votes_ EXCEPT ![self] = [n \in Backups |-> -1]]
                                /\ Q' = [Q EXCEPT ![self] = {}]
                                /\ committed' = [committed EXCEPT ![self] = FALSE]
                                /\ win' = [win EXCEPT ![self] = -1]
                                /\ pc' = [pc EXCEPT ![self] = "W_prepare"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << stack, orig, ret, nVal, votes_, Q, 
                                          committed, win >>
               /\ UNCHANGED << db, up, FailNum, Primary, Backups, retv, 
                               primaryHist, votes, origVal, swapVal, voteVal, 
                               voteCnt, majVoteVal, cntr, readVal >>

proceed(self) == /\ pc[self] = "proceed"
                 /\ cntr' = [cntr EXCEPT ![self] = cntr[self] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "start"]
                 /\ UNCHANGED << db, up, FailNum, Primary, Backups, retv, 
                                 primaryHist, stack, votes, origVal, swapVal, 
                                 voteVal, voteCnt, majVoteVal, orig, ret, nVal, 
                                 votes_, Q, committed, win, readVal >>

c(self) == start(self) \/ proceed(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: EvalRules(self) \/ SNAPSHOT_Write(self))
           \/ (\E self \in Clients: c(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : /\ WF_vars(c(self))
                                 /\ SF_vars(start(self)) /\ SF_vars(proceed(self))
                                 /\ WF_vars(SNAPSHOT_Write(self))
                                 /\ WF_vars(EvalRules(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Mon Sep 05 09:50:07 CST 2022 by berna
\* Created Sun Sep 04 11:12:43 CST 2022 by berna
