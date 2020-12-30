---- MODULE MC ----
EXTENDS peterson, TLC

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_160909152972523000 ==
(pc[0] /= "cs") \/ (pc[1] /= "cs")
----
=============================================================================
\* Modification History
\* Created Sun Dec 27 22:52:09 YEKT 2020 by a18828568
