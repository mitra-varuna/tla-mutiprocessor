---- MODULE locktwo ----
EXTENDS TLC, Integers

(* --algorithm lockone
variables turn = 0;
fair process proc \in {0,1} 
begin
    a1: while(TRUE) do
        skip;
    a2: turn := 1 - self ;  
    a3: await (turn = self);
        cs: skip;
    end while
end process
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "720025f9" /\ chksum(tla) = "c8d068cf")
VARIABLES turn, pc

vars == << turn, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ turn = 0
        /\ pc = [self \in ProcSet |-> "a1"]

a1(self) == /\ pc[self] = "a1"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ turn' = turn

a2(self) == /\ pc[self] = "a2"
            /\ turn' = 1 - self
            /\ pc' = [pc EXCEPT ![self] = "a3"]

a3(self) == /\ pc[self] = "a3"
            /\ (turn = self)
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ turn' = turn

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ turn' = turn

proc(self) == a1(self) \/ a2(self) \/ a3(self) \/ cs(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {0,1}: proc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0,1} : WF_vars(proc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
