---- MODULE MC ----
EXTENDS tstorepscal, TLC

\* CONSTANT definitions @modelParameterConstants:0CheckpointAfterSize
const_1629149412658256000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1629149412658257000 ==
history.numWrites < 10
----
=============================================================================
\* Modification History
\* Created Mon Aug 16 14:30:12 PDT 2021 by asnegi
