---- MODULE livelock ----
EXTENDS TLC, Integers

(* --algorithm livelock_algorithm
variables flag = [i \in {0, 1} |-> FALSE];
 process proc \in {0,1} 
begin
    a1: while(TRUE) do
        skip;
    a2: flag[self] := TRUE;
        a3: while flag[1 - self] do
            a4: flag[self] := FALSE;
            a5: await (flag[1-self] =  FALSE);
            a6: flag[self] := TRUE;
        end while;
    cs: skip;
    a7: flag[self] := FALSE;
    end while
end process
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7054a924" /\ chksum(tla) = "78f02487")
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
            /\ IF flag[1 - self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "a4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ flag' = flag

a4(self) == /\ pc[self] = "a4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a5"]

a5(self) == /\ pc[self] = "a5"
            /\ (flag[1-self] =  FALSE)
            /\ pc' = [pc EXCEPT ![self] = "a6"]
            /\ flag' = flag

a6(self) == /\ pc[self] = "a6"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a3"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a7"]
            /\ flag' = flag

a7(self) == /\ pc[self] = "a7"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a1"]

proc(self) == a1(self) \/ a2(self) \/ a3(self) \/ a4(self) \/ a5(self)
                 \/ a6(self) \/ cs(self) \/ a7(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {0,1}: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
