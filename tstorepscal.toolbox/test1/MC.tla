---- MODULE MC ----
EXTENDS tstorepscal, TLC

\* CONSTANT definitions @modelParameterConstants:0CheckpointAfterSize
const_1628959272719134000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1628959272719135000 ==
history.numWrites < 10
----
=============================================================================
\* Modification History
\* Created Sat Aug 14 09:41:12 PDT 2021 by asnegi
