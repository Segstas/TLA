--------------------------- MODULE DeadLockEmpire ---------------------------
EXTENDS Naturals, TLC

(* --algorithm foo
variables first = 0, second = 0;

process thread0 = 1
variables tempA, tempB
begin
  A1: tempA := first + 1;
  A2: first := tempA;
  
  B1: tempB := second + 1;
  B2: second := tempB;
  
  C:
    if (second = 2 /\ first /= 2) then
              assert FALSE;
    end if;
end process


process thread1 = 2
begin
  A1: tempA := first + 1;
  A2: first := tempA;
  
  B1: tempB := second + 1;
  B2: second := tempB;
end process

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c328528" /\ chksum(tla) = "c036f569")
\* Label A1 of process thread0 at line 10 col 7 changed to A1_
\* Label A2 of process thread0 at line 11 col 7 changed to A2_
\* Label B1 of process thread0 at line 13 col 7 changed to B1_
\* Label B2 of process thread0 at line 14 col 7 changed to B2_
CONSTANT defaultInitValue
VARIABLES first, second, pc, tempA, tempB

vars == << first, second, pc, tempA, tempB >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ first = 0
        /\ second = 0
        (* Process thread0 *)
        /\ tempA = defaultInitValue
        /\ tempB = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "A1_"
                                        [] self = 2 -> "A1"]

A1_ == /\ pc[1] = "A1_"
       /\ tempA' = first + 1
       /\ pc' = [pc EXCEPT ![1] = "A2_"]
       /\ UNCHANGED << first, second, tempB >>

A2_ == /\ pc[1] = "A2_"
       /\ first' = tempA
       /\ pc' = [pc EXCEPT ![1] = "B1_"]
       /\ UNCHANGED << second, tempA, tempB >>

B1_ == /\ pc[1] = "B1_"
       /\ tempB' = second + 1
       /\ pc' = [pc EXCEPT ![1] = "B2_"]
       /\ UNCHANGED << first, second, tempA >>

B2_ == /\ pc[1] = "B2_"
       /\ second' = tempB
       /\ pc' = [pc EXCEPT ![1] = "C"]
       /\ UNCHANGED << first, tempA, tempB >>

C == /\ pc[1] = "C"
     /\ IF (second = 2 /\ first /= 2)
           THEN /\ Assert(FALSE, 
                          "Failure of assertion at line 18, column 15.")
           ELSE /\ TRUE
     /\ pc' = [pc EXCEPT ![1] = "Done"]
     /\ UNCHANGED << first, second, tempA, tempB >>

thread0 == A1_ \/ A2_ \/ B1_ \/ B2_ \/ C

A1 == /\ pc[2] = "A1"
      /\ tempA' = first + 1
      /\ pc' = [pc EXCEPT ![2] = "A2"]
      /\ UNCHANGED << first, second, tempB >>

A2 == /\ pc[2] = "A2"
      /\ first' = tempA
      /\ pc' = [pc EXCEPT ![2] = "B1"]
      /\ UNCHANGED << second, tempA, tempB >>

B1 == /\ pc[2] = "B1"
      /\ tempB' = second + 1
      /\ pc' = [pc EXCEPT ![2] = "B2"]
      /\ UNCHANGED << first, second, tempA >>

B2 == /\ pc[2] = "B2"
      /\ second' = tempB
      /\ pc' = [pc EXCEPT ![2] = "Done"]
      /\ UNCHANGED << first, tempA, tempB >>

thread1 == A1 \/ A2 \/ B1 \/ B2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == thread0 \/ thread1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Tue Jan 05 02:46:36 MSK 2021 by a18851548
\* Created Tue Jan 05 01:33:02 MSK 2021 by a18851548
