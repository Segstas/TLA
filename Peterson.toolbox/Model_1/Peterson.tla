------------------------------ MODULE Peterson ------------------------------

(**
 
  --algorithm Peterson {
   variables flag = [i \in {0, 1} |-> FALSE], other = 0, victim = 0;
   process (thread \in {0,1}) {
     lock1:   flag[self] := TRUE; 
     lock2:   victim := self; 
           other := IF self = 1 THEN 0 ELSE 1;   
     wait: while (flag[other] /\ victim = self) {skip};
     criticalSection: when TRUE; 
     unlock: flag[self] := FALSE;            
     }
  }
  
**)
\* BEGIN TRANSLATION (chksum(pcal) = "63909bd9" /\ chksum(tla) = "a44aea2f")
VARIABLES flag, other, victim, pc

vars == << flag, other, victim, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ other = 0
        /\ victim = 0
        /\ pc = [self \in ProcSet |-> "lock1"]

lock1(self) == /\ pc[self] = "lock1"
               /\ flag' = [flag EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "lock2"]
               /\ UNCHANGED << other, victim >>

lock2(self) == /\ pc[self] = "lock2"
               /\ victim' = self
               /\ other' = (IF self = 1 THEN 0 ELSE 1)
               /\ pc' = [pc EXCEPT ![self] = "wait"]
               /\ flag' = flag

wait(self) == /\ pc[self] = "wait"
              /\ IF flag[other] /\ victim = self
                    THEN /\ TRUE
                         /\ pc' = [pc EXCEPT ![self] = "wait"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "criticalSection"]
              /\ UNCHANGED << flag, other, victim >>

criticalSection(self) == /\ pc[self] = "criticalSection"
                         /\ TRUE
                         /\ pc' = [pc EXCEPT ![self] = "unlock"]
                         /\ UNCHANGED << flag, other, victim >>

unlock(self) == /\ pc[self] = "unlock"
                /\ flag' = [flag EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << other, victim >>

thread(self) == lock1(self) \/ lock2(self) \/ wait(self)
                   \/ criticalSection(self) \/ unlock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {0,1}: thread(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Tue Jan 05 01:26:29 MSK 2021 by a18851548
\* Created Tue Jan 05 00:29:36 MSK 2021 by a18851548
