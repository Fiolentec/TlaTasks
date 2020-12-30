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
            flag[self] := TRUE;
            victim := 1 - self;
            await (flag[1-self] = FALSE) \/ (victim = self);   
        cs: skip;
            flag[self] := FALSE
       }      
    }     
}
        *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-d307f05503a85919fdd39b6cf012449b
VARIABLES flag, victim, pc

vars == << flag, victim, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ victim = 0
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ TRUE
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ victim' = 1 - self
            /\ (flag'[1-self] = FALSE) \/ (victim' = self)
            /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED victim

proc(self) == s1(self) \/ cs(self)

Next == (\E self \in {0,1}: proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0,1} : WF_vars(proc(self))

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-9e736530a4f5f433d0ac56b9073f0d20

=============================================================================
\* Modification History
\* Last modified Sun Dec 27 22:12:57 YEKT 2020 by a18828568
\* Created Sun Dec 27 20:23:45 YEKT 2020 by a18828568
