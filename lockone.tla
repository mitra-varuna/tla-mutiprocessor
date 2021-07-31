---- MODULE lockone ----
EXTENDS TLC, Integers

(* --algorithm lockone
variables flag = [i \in {0, 1} |-> FALSE];
fair process proc \in {0,1} 
begin
    a1: while(TRUE) do
        skip;
    a2: flag[self] := TRUE;
    a3: await (flag[1-self] =  FALSE);
        cs: skip;
    a4: flag[self] := FALSE;

    end while
end process
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8f18aff3" /\ chksum(tla) = "63c059ab")
VARIABLES flag, pc

vars == << flag, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ pc = [self \in ProcSet |-> "a1"]

a1(self) == /\ pc[self] = "a1"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ flag' = flag

a2(self) == /\ pc[self] = "a2"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a3"]

a3(self) == /\ pc[self] = "a3"
            /\ (flag[1-self] =  FALSE)
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ flag' = flag

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ flag' = flag

a4(self) == /\ pc[self] = "a4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a1"]

proc(self) == a1(self) \/ a2(self) \/ a3(self) \/ cs(self) \/ a4(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {0,1}: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
