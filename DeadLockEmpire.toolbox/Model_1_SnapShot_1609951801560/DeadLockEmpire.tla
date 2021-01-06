--------------------------- MODULE DeadLockEmpire ---------------------------
EXTENDS Naturals, TLC

(* --algorithm foo
variables first = 0, second = 0;

process thread0 = 1
variables tempA, tempB
begin
  T0: skip; \* bubusiness_logic

  T0A1: tempA := first + 1;
  T0A2: first := tempA;
  
  T0B1: tempB := second + 1;
  T0B2: second := tempB;
  
  T0C1:
    if (second = 2 /\ first /= 2) then
  T0C2:           
    assert FALSE;
    end if;
    
end process


process thread1 = 2
begin
  T1: skip; \* bubusiness_logic

  T1A1: tempA := first + 1;
  T1A2: first := tempA;
  
  T1B1: tempB := second + 1;
  T1B2: second := tempB;
end process

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "f5f4b45f" /\ chksum(tla) = "96595c6e")
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
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "T0"
                                        [] self = 2 -> "T1"]

T0 == /\ pc[1] = "T0"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![1] = "T0A1"]
      /\ UNCHANGED << first, second, tempA, tempB >>

T0A1 == /\ pc[1] = "T0A1"
        /\ tempA' = first + 1
        /\ pc' = [pc EXCEPT ![1] = "T0A2"]
        /\ UNCHANGED << first, second, tempB >>

T0A2 == /\ pc[1] = "T0A2"
        /\ first' = tempA
        /\ pc' = [pc EXCEPT ![1] = "T0B1"]
        /\ UNCHANGED << second, tempA, tempB >>

T0B1 == /\ pc[1] = "T0B1"
        /\ tempB' = second + 1
        /\ pc' = [pc EXCEPT ![1] = "T0B2"]
        /\ UNCHANGED << first, second, tempA >>

T0B2 == /\ pc[1] = "T0B2"
        /\ second' = tempB
        /\ pc' = [pc EXCEPT ![1] = "T0C1"]
        /\ UNCHANGED << first, tempA, tempB >>

T0C1 == /\ pc[1] = "T0C1"
        /\ IF (second = 2 /\ first /= 2)
              THEN /\ pc' = [pc EXCEPT ![1] = "T0C2"]
              ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
        /\ UNCHANGED << first, second, tempA, tempB >>

T0C2 == /\ pc[1] = "T0C2"
        /\ Assert(FALSE, "Failure of assertion at line 21, column 5.")
        /\ pc' = [pc EXCEPT ![1] = "Done"]
        /\ UNCHANGED << first, second, tempA, tempB >>

thread0 == T0 \/ T0A1 \/ T0A2 \/ T0B1 \/ T0B2 \/ T0C1 \/ T0C2

T1 == /\ pc[2] = "T1"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![2] = "T1A1"]
      /\ UNCHANGED << first, second, tempA, tempB >>

T1A1 == /\ pc[2] = "T1A1"
        /\ tempA' = first + 1
        /\ pc' = [pc EXCEPT ![2] = "T1A2"]
        /\ UNCHANGED << first, second, tempB >>

T1A2 == /\ pc[2] = "T1A2"
        /\ first' = tempA
        /\ pc' = [pc EXCEPT ![2] = "T1B1"]
        /\ UNCHANGED << second, tempA, tempB >>

T1B1 == /\ pc[2] = "T1B1"
        /\ tempB' = second + 1
        /\ pc' = [pc EXCEPT ![2] = "T1B2"]
        /\ UNCHANGED << first, second, tempA >>

T1B2 == /\ pc[2] = "T1B2"
        /\ second' = tempB
        /\ pc' = [pc EXCEPT ![2] = "Done"]
        /\ UNCHANGED << first, tempA, tempB >>

thread1 == T1 \/ T1A1 \/ T1A2 \/ T1B1 \/ T1B2

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
\* Last modified Wed Jan 06 19:48:21 MSK 2021 by a18851548
\* Created Tue Jan 05 01:33:02 MSK 2021 by a18851548
