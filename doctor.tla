------------------------------- MODULE doctor -------------------------------

EXTENDS Integers

VARIABLES n

Init ==
    n = 0

NextA ==
    \/ /\ n < 3
       /\ n' = n + 1
    \/ /\ n < 5
       /\ n' = n + 2
    \/ UNCHANGED <<n>>


=============================================================================
\* Modification History
\* Last modified Tue Dec 01 12:14:45 PST 2020 by asnegi
\* Created Tue Nov 10 17:58:12 PST 2020 by asnegi
