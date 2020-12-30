------------------------------- MODULE bakery -------------------------------
EXTENDS Naturals, TLC
Numbers == 1..10
CONSTANT N
ASSUME N \in Nat
Threads == 1..N 

             
(*             
--algorithm Bakery 
{ variables num = [i \in Threads |-> 0], flag = [i \in Threads |-> FALSE];
  fair process (p \in Threads)
    variables wanted = {}, max = 0, nexTread = 1 ;
    { noncs:- while (TRUE){ 
              s1:   flag[self] := TRUE;
                             wanted := Threads \ {self} ;
                             max := 0;    
              s2:   while (wanted /= {}){ 
                        with (i \in wanted) 
                          { wanted := wanted \ {i};
                            if (num[i] > max) { max := num[i] }
                          }
                      };
              s3:  with (i \in {j \in Numbers : j > max}) 
                               { num[self] := i };
              s4:  flag[self] := FALSE;
                   wanted := Threads \ {self} ;
                             
              m1:  while (wanted /= {}){     
                        with (i \in wanted) { nexTread := i };
                            await ~ flag[nexTread];
                        m2: await \/ num[nexTread] = 0
                                  \/ (\/ num[self]<num[nexTread]
                                      \/ (num[self]<num[nexTread]) /\ (self<nexTread));
                            wanted := wanted \ {nexTread};
                      } ;
              cs:  skip ; 
              exit:  num[self] := 0; 
            }
    }
}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-8d93b4682ffb69d9a5672d4f97c22352
VARIABLES num, flag, pc, wanted, max, nexTread

vars == << num, flag, pc, wanted, max, nexTread >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ num = [i \in Threads |-> 0]
        /\ flag = [i \in Threads |-> FALSE]
        (* Process p *)
        /\ wanted = [self \in Threads |-> {}]
        /\ max = [self \in Threads |-> 0]
        /\ nexTread = [self \in Threads |-> 1]
        /\ pc = [self \in ProcSet |-> "noncs"]

noncs(self) == /\ pc[self] = "noncs"
               /\ pc' = [pc EXCEPT ![self] = "s1"]
               /\ UNCHANGED << num, flag, wanted, max, nexTread >>

s1(self) == /\ pc[self] = "s1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ wanted' = [wanted EXCEPT ![self] = Threads \ {self}]
            /\ max' = [max EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << num, nexTread >>

s2(self) == /\ pc[self] = "s2"
            /\ IF wanted[self] /= {}
                  THEN /\ \E i \in wanted[self]:
                            /\ wanted' = [wanted EXCEPT ![self] = wanted[self] \ {i}]
                            /\ IF num[i] > max[self]
                                  THEN /\ max' = [max EXCEPT ![self] = num[i]]
                                  ELSE /\ TRUE
                                       /\ max' = max
                       /\ pc' = [pc EXCEPT ![self] = "s2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "s3"]
                       /\ UNCHANGED << wanted, max >>
            /\ UNCHANGED << num, flag, nexTread >>

s3(self) == /\ pc[self] = "s3"
            /\ \E i \in {j \in Numbers : j > max[self]}:
                 num' = [num EXCEPT ![self] = i]
            /\ pc' = [pc EXCEPT ![self] = "s4"]
            /\ UNCHANGED << flag, wanted, max, nexTread >>

s4(self) == /\ pc[self] = "s4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ wanted' = [wanted EXCEPT ![self] = Threads \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "m1"]
            /\ UNCHANGED << num, max, nexTread >>

m1(self) == /\ pc[self] = "m1"
            /\ IF wanted[self] /= {}
                  THEN /\ \E i \in wanted[self]:
                            nexTread' = [nexTread EXCEPT ![self] = i]
                       /\ ~ flag[nexTread'[self]]
                       /\ pc' = [pc EXCEPT ![self] = "m2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED nexTread
            /\ UNCHANGED << num, flag, wanted, max >>

m2(self) == /\ pc[self] = "m2"
            /\ \/ num[nexTread[self]] = 0
               \/ (\/ num[self]<num[nexTread[self]]
                   \/ (num[self]<num[nexTread[self]]) /\ (self<nexTread[self]))
            /\ wanted' = [wanted EXCEPT ![self] = wanted[self] \ {nexTread[self]}]
            /\ pc' = [pc EXCEPT ![self] = "m1"]
            /\ UNCHANGED << num, flag, max, nexTread >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << num, flag, wanted, max, nexTread >>

exit(self) == /\ pc[self] = "exit"
              /\ num' = [num EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "noncs"]
              /\ UNCHANGED << flag, wanted, max, nexTread >>

p(self) == noncs(self) \/ s1(self) \/ s2(self) \/ s3(self) \/ s4(self)
              \/ m1(self) \/ m2(self) \/ cs(self) \/ exit(self)

Next == (\E self \in Threads: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars((pc[self] # "noncs") /\ p(self))

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-5baa0116644512608a0c6203f44f7398


Before(i,j) == /\ num[i] > 0
               /\ \/ pc[j] \in {"noncs", "s1", "exit"}
                  \/ /\ pc[j] = "s2"
                     /\ \/ i \in wanted[j]
                        \/ max[j] >= num[i]
                  \/ /\ pc[j] = "s3"
                     /\ max[j] >= num[i]
                  \/ /\ pc[j] \in {"s4", "m1", "m2"}
                     /\ (\/ num[i]<num[j]
                         \/ num[i]=num[j] /\ i<j )
                     /\ (pc[j] \in {"m1", "m2"}) => (i \in wanted[j])

Inv == \A i \in Threads :     
             /\ (pc[i] \in {"s4", "m1", "m2", "cs"}) => (num[i] # 0)
             /\ (pc[i] \in {"s2", "s3"}) => flag[i]
             /\ (pc[i] = "m2") => (nexTread[i] # i)
             /\  pc[i] \in {"s2", "m1", "m2"} => i \notin wanted[i]  
             /\ (pc[i] \in {"m1", "m2"}) =>
                   \A j \in (Threads \ wanted[i]) \ {i} : Before(i, j)
             /\ /\ (pc[i] = "m2")
                /\ \/ (pc[nexTread[i]] = "s2") /\ (i \notin wanted[nexTread[i]]) 
                   \/ pc[nexTread[i]] = "s3"
                => max[nexTread[i]] >= num[i]
             /\ (pc[i] = "cs") => \A j \in Threads \ {i} : Before(i, j)
=============================================================================
\* Modification History
\* Last modified Wed Dec 30 19:53:14 YEKT 2020 by a18828568
\* Created Wed Dec 30 00:59:27 YEKT 2020 by a18828568
