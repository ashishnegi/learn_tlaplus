------------------------------ MODULE property ------------------------------

EXTENDS Naturals

 

VARIABLES x

 

Spec == x = 0 /\ [][x' \in 1..10]_x

 

P == x = 0

=============================================================================
\* Modification History
\* Last modified Wed Oct 28 20:13:09 PDT 2020 by asnegi
\* Created Wed Oct 28 20:12:54 PDT 2020 by asnegi
