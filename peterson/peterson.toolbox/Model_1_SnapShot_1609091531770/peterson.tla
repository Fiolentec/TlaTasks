------------------------------ MODULE peterson ------------------------------
EXTENDS Naturals, TLC
\*CONSTANT N
(*
--algorithm Peterson {
    variables flag = [i \in {0, 1} |-> FALSE],  victim = 0;
         \* Declares the global variables flag and victim and their initial values;
     \* flag is a 2-element array with initially flag[0] = flag[1] = FALSE.
    fair process (proc \in {0,1}) {
            \* Declares two processes with identifier self equal to 0 and 1.
        \* The keyword fair means that no process can stop forever if it can
        \* always take a step.
\*        a1: while (TRUE) {
\*                 skip ;  \* the noncritical section
\*            a2:  flag[self] := TRUE ;
\*            a3:  victim := 1 - self ;   
\*            a4:  await (flag[1-self] = FALSE) \/ (victim = self); \* \/ is written || in C.
\*            cs:  skip ;  \* the critical section
\*            a5:  flag[self] := FALSE               
\*        }
        s1: while (TRUE){
            skip;
        s2: flag[self] := TRUE;
        s3: victim := 1 - self;
        s4: await (flag[1-self] = FALSE) \/ (victim = self);   
        cs: skip;
        s5: flag[self] := FALSE
       }      
    }     
}
        *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-68327f99a9755fcf218aa8c1498fa551
VARIABLES flag, victim, pc

vars == << flag, victim, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ victim = 0
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << flag, victim >>

s2(self) == /\ pc[self] = "s2"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ UNCHANGED victim

s3(self) == /\ pc[self] = "s3"
            /\ victim' = 1 - self
            /\ pc' = [pc EXCEPT ![self] = "s4"]
            /\ flag' = flag

s4(self) == /\ pc[self] = "s4"
            /\ (flag[1-self] = FALSE) \/ (victim = self)
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << flag, victim >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "s5"]
            /\ UNCHANGED << flag, victim >>

s5(self) == /\ pc[self] = "s5"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED victim

proc(self) == s1(self) \/ s2(self) \/ s3(self) \/ s4(self) \/ cs(self)
                 \/ s5(self)

Next == (\E self \in {0,1}: proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0,1} : WF_vars(proc(self))

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a25d5a613cd167a60904e4a5b38343de

=============================================================================
\* Modification History
\* Last modified Sun Dec 27 22:51:29 YEKT 2020 by a18828568
\* Created Sun Dec 27 20:23:45 YEKT 2020 by a18828568
