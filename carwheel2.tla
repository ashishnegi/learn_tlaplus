------------------------------ MODULE carwheel2 ------------------------------

\* We have 5 tires each with 20k miles left. How long a car run with these tires ?

EXTENDS Integers, TLC, FiniteSets
VARIABLES InCarTyres, SpareTyre, NextChangeTyre, TyresMileage, MilesDriven

TypeOK ==
    /\ InCarTyres \subseteq {0, 1, 2, 3, 4}
    /\ Cardinality(InCarTyres) = 4
    /\ SpareTyre \in {0, 1, 2, 3, 4}
    /\ NextChangeTyre \in {0, 1, 2, 3, 4}
    /\ SpareTyre # NextChangeTyre
    /\ TyresMileage \in [ {0,1,2,3,4} -> 0..20 ]
    /\ MilesDriven \in 0..100

Init ==
    /\ InCarTyres = { 0, 1, 2, 3 }
    /\ SpareTyre = 4
    /\ NextChangeTyre = 0
    /\ TyresMileage = [ t \in {0, 1, 2, 3, 4} |-> 20 ]
    /\ MilesDriven = 0
    
RunCar ==
    /\ \A t \in InCarTyres : TyresMileage[t] > 0
    /\ TyresMileage' = [ t \in InCarTyres |-> TyresMileage[t] - 1 ] @@ TyresMileage
    /\ MilesDriven' = MilesDriven + 1
    /\ UNCHANGED << SpareTyre, NextChangeTyre, InCarTyres >>

ChangeTyre ==
    /\ TyresMileage[SpareTyre] > 0
    /\ InCarTyres' = (InCarTyres \union { SpareTyre }) \ { NextChangeTyre }
    /\ SpareTyre' = NextChangeTyre
    \* Choose to replace most driven tyre for next change.
    /\ NextChangeTyre' = CHOOSE v \in InCarTyres' : \A u \in InCarTyres' : TyresMileage[v] <= TyresMileage[u]
    /\ UNCHANGED << TyresMileage, MilesDriven >>

Next == 
    \/ RunCar
    \/ ChangeTyre

MinMilesDriven ==
   MilesDriven < 26 \* For 26, we don't get any result. So, 25 is optimal
 
=============================================================================