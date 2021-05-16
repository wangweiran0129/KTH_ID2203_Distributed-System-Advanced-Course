--------------------------- MODULE LeaderElection ---------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS 
    N, \* Number of processes
    STOP \* Max number of rounds for finite search space
ASSUME N \in Nat
Processes == 1..N

(* --algorithm LeaderElection
{

    variable
        \* mailbox = (*** TODO: Initialise all processes with an empty mailbox***)
        mailbox = [p \in Processes |-> {}]; \* store the message of a process
        leader = [p \in Processes |-> 0];  \* all have not elected any leader
        round = [p \in Processes |-> 0];   \* all are at round 0
        elected = [p \in Processes |-> FALSE];

    define {
        \* Max(S) == (*** TODO: Pick the highest value in S ***)
        \* Max(S) is a function, and S is a SET
        Max(S) == CHOOSE x \in S: \A y \in S: y <= x
    }
        
    fair process (p \in Processes)
    variable recv={}; \* recv is a SET
    {
    
P:  while (round[self] < STOP) { \* You can get a process's value with self
        \* await \A pid \in Processes: elected[pid] = TRUE;
        recv := Processes; \* recv = 1..N
    
        
Bcast:  while (recv # {}) { 
            with (p \in recv) { \* p = 1,2,3
                (*** TODO: Send 'self' to all processes ***)
                \* each process broadcasts their own id(self)
                mailbox[p] := mailbox[p] \union {self};
                recv := recv \ {p};
            };
            \* recv := {};
        };
        \* A processes signals that it has completed the action by going to the next round
        (*** TODO: Advance to the next round ***)
        round[self] := round[self] + 1; 
        \* elected[self] := FALSE;

Sync:   \* (*** TODO: Wait for processes to be in next round***)
        await \A pid \in Processes: round[pid] >= round[self];
        if (\A pid \in Processes: elected[pid] = TRUE){
            skip;
        }
        else{
            leader[self] := Max(mailbox[self]);
            mailbox[self] := {};
            elected[self] := TRUE;
        }
        \* each process picks the highest id as the leader
        \* leader[self] := (*** TODO: Choose leader ***);
        
        \* mailbox[self] := {};
        
        \* everyProcessHasElectedLeader
        \* await \A pid \in Processes: elected[pid] = TRUE;
        
     }; \* while (round[self] < STOP)
    } \* end process

}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "f6937ce" /\ chksum(tla) = "4c9b71a")
VARIABLES mailbox, leader, round, elected, pc

(* define statement *)
Max(S) == CHOOSE x \in S: \A y \in S: y <= x

VARIABLE recv

vars == << mailbox, leader, round, elected, pc, recv >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ mailbox = [p \in Processes |-> {}]
        /\ leader = [p \in Processes |-> 0]
        /\ round = [p \in Processes |-> 0]
        /\ elected = [p \in Processes |-> FALSE]
        (* Process p *)
        /\ recv = [self \in Processes |-> {}]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF round[self] < STOP
                 THEN /\ recv' = [recv EXCEPT ![self] = Processes]
                      /\ pc' = [pc EXCEPT ![self] = "Bcast"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ recv' = recv
           /\ UNCHANGED << mailbox, leader, round, elected >>

Bcast(self) == /\ pc[self] = "Bcast"
               /\ IF recv[self] # {}
                     THEN /\ \E p \in recv[self]:
                               /\ mailbox' = [mailbox EXCEPT ![p] = mailbox[p] \union {self}]
                               /\ recv' = [recv EXCEPT ![self] = recv[self] \ {p}]
                          /\ pc' = [pc EXCEPT ![self] = "Bcast"]
                          /\ round' = round
                     ELSE /\ round' = [round EXCEPT ![self] = round[self] + 1]
                          /\ pc' = [pc EXCEPT ![self] = "Sync"]
                          /\ UNCHANGED << mailbox, recv >>
               /\ UNCHANGED << leader, elected >>

Sync(self) == /\ pc[self] = "Sync"
              /\ \A pid \in Processes: round[pid] >= round[self]
              /\ IF \A pid \in Processes: elected[pid] = TRUE
                    THEN /\ TRUE
                         /\ UNCHANGED << mailbox, leader, elected >>
                    ELSE /\ leader' = [leader EXCEPT ![self] = Max(mailbox[self])]
                         /\ mailbox' = [mailbox EXCEPT ![self] = {}]
                         /\ elected' = [elected EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "P"]
              /\ UNCHANGED << round, recv >>

p(self) == P(self) \/ Bcast(self) \/ Sync(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Processes: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
\* Agreement: All processes elect the same leader.
Agreement == \A pid1, pid2 \in Processes: (elected[pid1] = TRUE /\ elected[pid2] = TRUE) => leader[pid1] = leader[pid2]
\* Completeness: Eventually, all processes elect some leader.
Completeness == <> (\A pid \in Processes: leader[pid] # 0)
=============================================================================
\* Modification History
\* Last modified Sat May 15 16:36:26 CEST 2021 by wangweiran
\* Created Sat Mar 06 18:53:00 CET 2021 by wangweiran
