------------------------ MODULE LeaderElectionCrash ------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS 
    N, \* Number of processes
    F, \* F: number of faulty processes
    STOP \* Max number of rounds for finite search space
ASSUME N \in Nat /\ F <= N /\ F <= STOP
Processes == 1..N

(* --algorithm LeaderElectionCrash 
{

    variable
        f = F,                            \* number of processes left to be crashed
        alive = [p \in Processes |-> TRUE]; \* all processes are initially alive
        mailbox = [p \in Processes |-> {}];
        leader = [p \in Processes |-> 0];  \* all have not elected any leader
        round = [p \in Processes |-> 0];    \* all are at round 0
        elected = [p \in Processes |-> FALSE];

    define {
        Max(S) == CHOOSE x \in S: \A y \in S: y <= x
    }

    macro MaybeCrash() {
    if (f>0 /\ alive[self] /\ STOP-round[self] > 1) { \* Disallow crashing just before STOP
            either { 
                (*** TODO: process crashes... ***)
                alive[self] := FALSE;
                f := f-1;
            } 
            or skip; }; \* ... or not
    }
    
    fair process (p \in Processes)
    variable recv={};
    {
P:   while (round[self] < STOP) {
        recv := Processes;      
Bcast:  while (alive[self] /\ recv # {}) {
            with (p \in recv) {
                mailbox[p] := mailbox[p] \union {self};
                recv := recv \ {p};
                MaybeCrash();
            };
        };
        round[self] := round[self] + 1;
        elected[self] := FALSE;
        \*elected := [p \in Processes |-> FALSE];
Sync:   if(alive[self]){
            await \A pid \in Processes: alive[pid] => round[pid] >= round[self];
            mailbox[self] := {x \in mailbox[self]: alive[x] = TRUE};
            leader[self] := Max(mailbox[self]);
            elected[self] := TRUE;
            \* await \A pid \in Processes: elected[pid] = TRUE;
        }
        
    };
    } \* end process

}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "339b7ab1" /\ chksum(tla) = "a8b50fd6")
VARIABLES f, alive, mailbox, leader, round, elected, pc

(* define statement *)
Max(S) == CHOOSE x \in S: \A y \in S: y <= x

VARIABLE recv

vars == << f, alive, mailbox, leader, round, elected, pc, recv >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ f = F
        /\ alive = [p \in Processes |-> TRUE]
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
           /\ UNCHANGED << f, alive, mailbox, leader, round, elected >>

Bcast(self) == /\ pc[self] = "Bcast"
               /\ IF alive[self] /\ recv[self] # {}
                     THEN /\ \E p \in recv[self]:
                               /\ mailbox' = [mailbox EXCEPT ![p] = mailbox[p] \union {self}]
                               /\ recv' = [recv EXCEPT ![self] = recv[self] \ {p}]
                               /\ IF f>0 /\ alive[self] /\ STOP-round[self] > 1
                                     THEN /\ \/ /\ alive' = [alive EXCEPT ![self] = FALSE]
                                                /\ f' = f-1
                                             \/ /\ TRUE
                                                /\ UNCHANGED <<f, alive>>
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << f, alive >>
                          /\ pc' = [pc EXCEPT ![self] = "Bcast"]
                          /\ UNCHANGED << round, elected >>
                     ELSE /\ round' = [round EXCEPT ![self] = round[self] + 1]
                          /\ elected' = [elected EXCEPT ![self] = FALSE]
                          /\ pc' = [pc EXCEPT ![self] = "Sync"]
                          /\ UNCHANGED << f, alive, mailbox, recv >>
               /\ UNCHANGED leader

Sync(self) == /\ pc[self] = "Sync"
              /\ IF alive[self]
                    THEN /\ \A pid \in Processes: alive[pid] => round[pid] >= round[self]
                         /\ mailbox' = [mailbox EXCEPT ![self] = {x \in mailbox[self]: alive[x] = TRUE}]
                         /\ leader' = [leader EXCEPT ![self] = Max(mailbox'[self])]
                         /\ elected' = [elected EXCEPT ![self] = TRUE]
                    ELSE /\ TRUE
                         /\ UNCHANGED << mailbox, leader, elected >>
              /\ pc' = [pc EXCEPT ![self] = "P"]
              /\ UNCHANGED << f, alive, round, recv >>

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

\* Agreement: All correct processes elect the same correct leader.
Agreement == (\A pid1, pid2 \in Processes: (alive[pid1] /\ alive[pid2]) /\ (elected[pid1] /\ elected[pid2])=> leader[pid1] = leader[pid2])
\* Agreement == <> (\A x, y \in Processes: (alive[x] /\ alive[y]) /\ (elected[x] /\ elected[y]) => leader[x] = leader[y])


\* Completeness: Eventually, all correct processes elect some correct leader
Completeness == <>(\A pid \in Processes: leader[pid] # 0 /\ alive[pid] => (alive[leader[pid]] = TRUE))

=============================================================================
\* Modification History
\* Last modified Sun May 16 16:23:39 CEST 2021 by wangweiran
\* Created Tue Mar 09 11:36:46 CET 2021 by wangweiran
