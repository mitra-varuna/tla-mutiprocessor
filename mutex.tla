---- MODULE mutex ----
EXTENDS TLC

(* --algorithm hello_world
variable s \in {"Hello", "World!"};
begin
  A:
    print s;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "c66c1fcc" /\ chksum(tla) = "e102bc6a")
VARIABLES s, pc

vars == << s, pc >>

Init == (* Global variables *)
        /\ s \in {"Hello", "World!"}
        /\ pc = "A"

A == /\ pc = "A"
     /\ PrintT(s)
     /\ pc' = "Done"
     /\ s' = s

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
