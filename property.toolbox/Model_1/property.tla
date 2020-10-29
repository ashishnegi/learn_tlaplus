------------------------------ MODULE property ------------------------------

EXTENDS Naturals

 

VARIABLES x

 

Spec == x = 11 /\ [][x' \in 1..10]_x

 

P == x = 0

=============================================================================
\* Modification History
\* Last modified Wed Oct 28 20:30:42 PDT 2020 by asnegi
\* Created Wed Oct 28 20:12:54 PDT 2020 by asnegi
