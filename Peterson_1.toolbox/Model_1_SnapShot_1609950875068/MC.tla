---- MODULE MC ----
EXTENDS Peterson, TLC

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_16099590866432000 ==
{pc[0],pc[1]} /= {"criticalSection"}
----
=============================================================================
\* Modification History
\* Created Wed Jan 06 22:51:26 SAMT 2021 by a18851548
