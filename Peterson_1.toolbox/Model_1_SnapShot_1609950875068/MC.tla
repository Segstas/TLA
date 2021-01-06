---- MODULE MC ----
EXTENDS Peterson, TLC

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_160995087206384000 ==
{pc[0],pc[1]} /= {"criticalSection"}
----
=============================================================================
\* Modification History
\* Created Wed Jan 06 19:34:32 MSK 2021 by a18851548
