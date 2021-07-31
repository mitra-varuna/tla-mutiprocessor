---- MODULE peterson ----
EXTENDS TLC, Integers

(* --algorithm peterson_algorithm
variables flag = [i \in {0, 1} |-> FALSE], turn = 0;
fair process proc \in {0,1} 
begin
    a1: while(TRUE) do
        skip;
    a2: flag[self] := TRUE;
    a3: turn := 1 - self ;  
    a4: await (flag[1-self] =  FALSE) \/ (turn = self);
    cs: skip;
    a5: flag[self] := FALSE;
    end while
end process
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "24a2cb6d" /\ chksum(tla) = "39bf40af")
VARIABLES flag, turn, pc

vars == << flag, turn, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ turn = 0
        /\ pc = [self \in ProcSet |-> "a1"]

a1(self) == /\ pc[self] = "a1"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << flag, turn >>

a2(self) == /\ pc[self] = "a2"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a3"]
            /\ turn' = turn

a3(self) == /\ pc[self] = "a3"
            /\ turn' = 1 - self
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ flag' = flag

a4(self) == /\ pc[self] = "a4"
            /\ (flag[1-self] =  FALSE) \/ (turn = self)
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << flag, turn >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a5"]
            /\ UNCHANGED << flag, turn >>

a5(self) == /\ pc[self] = "a5"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ turn' = turn

proc(self) == a1(self) \/ a2(self) \/ a3(self) \/ a4(self) \/ cs(self)
                 \/ a5(self)

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
