------------------------------ MODULE diehard ------------------------------

EXTENDS Integers
VARIABLES small, big

Init == 
    /\ small = 0
    /\ big = 0
    
SmallToBig ==
    /\ small' = 0
    /\ IF (big + small) > 5
        THEN big' = 5
        ELSE big' = big + small

BigToSmall == 
    /\ big' = 0
    /\ IF (big + small) > 3
        THEN small' = 3
        ELSE small' = big + small
        
SmallDrain ==
    /\ small' = 0
    /\ big' = big

BigDrain ==
    /\ small' = small
    /\ big' = 0
    
Next ==
    \/ SmallToBig
    \/ BigToSmall
    \/ SmallDrain
    \/ BigDrain
    
=============================================================================
\* Modification History
\* Last modified Wed Oct 28 00:05:26 PDT 2020 by asnegi
\* Created Tue Oct 27 23:58:27 PDT 2020 by asnegi
