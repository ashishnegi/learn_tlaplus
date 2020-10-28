------------------------------ MODULE carwheel ------------------------------

EXTENDS Integers
VARIABLES TireA, TireB, TireC, TireD, TireS

TypeOK ==   
    /\ TireA \in 0..20
    /\ TireB \in 0..20
    /\ TireC \in 0..20
    /\ TireD \in 0..20
    /\ TireS \in 0..20

Init == 
    /\ TireA = 20
    /\ TireB = 20
    /\ TireC = 20
    /\ TireD = 20
    /\ TireS = 20

SpareA ==
    /\ TireA' = TireA
    /\ TireB' = TireB - 1
    /\ TireC' = TireC - 1
    /\ TireD' = TireD - 1
    /\ TireS' = TireS - 1

SpareB ==
    /\ TireA' = TireA - 1
    /\ TireB' = TireB
    /\ TireC' = TireC - 1
    /\ TireD' = TireD - 1
    /\ TireS' = TireS - 1

SpareC ==
    /\ TireA' = TireA - 1
    /\ TireB' = TireB - 1
    /\ TireC' = TireC
    /\ TireD' = TireD - 1
    /\ TireS' = TireS - 1

SpareD ==
    /\ TireA' = TireA - 1
    /\ TireB' = TireB - 1
    /\ TireC' = TireC - 1
    /\ TireD' = TireD
    /\ TireS' = TireS - 1

SpareS ==
    /\ TireA' = TireA - 1
    /\ TireB' = TireB - 1
    /\ TireC' = TireC - 1
    /\ TireD' = TireD - 1
    /\ TireS' = TireS
    
Next == 
    \/ SpareA
    \/ SpareB
    \/ SpareC
    \/ SpareD
    \/ SpareS
    
RunCar == 
    \/ (TireA > 0 /\ TireB > 0 /\ TireC > 0)
    
=============================================================================