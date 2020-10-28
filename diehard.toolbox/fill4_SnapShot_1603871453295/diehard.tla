------------------------------ MODULE diehard ------------------------------

EXTENDS Integers
VARIABLES small, big

TypeOK ==
    /\ small \in 0..3
    /\ big \in 0..5

Init == 
    /\ small = 0
    /\ big = 0
    
SmallToBig ==
    IF (big + small) > 5
   THEN /\ big' = 5
        /\ small' = small - (5 - big)
   ELSE /\ big' = big + small
        /\ small' = 0

BigToSmall == 
    IF (big + small) > 3
    THEN /\ small' = 3
         /\ big' = big - (3 - small)
    ELSE /\ small' = big + small
         /\ big' = 0

SmallDrain ==
    /\ small' = 0
    /\ big' = big

BigDrain ==
    /\ small' = small
    /\ big' = 0
    
FillSmall ==
    /\ small' = 3
    /\ big' = big

FillBig ==
    /\ small' = small
    /\ big' = 5
    
Next ==
    \/ FillSmall
    \/ FillBig
    \/ SmallToBig
    \/ BigToSmall
    \/ SmallDrain
    \/ BigDrain
    
=============================================================================
\* Modification History
\* Last modified Wed Oct 28 00:49:23 PDT 2020 by asnegi
\* Created Tue Oct 27 23:58:27 PDT 2020 by asnegi
