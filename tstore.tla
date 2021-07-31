------------------------------- MODULE tstore -------------------------------
EXTENDS Integers, Sequences
CONSTANTS MaxSizeOfDifferntialState
VARIABLES DifferentialState, DeltaDifferentialState, 
          ConsolidatedState, NextId

vars == <<DifferentialState, DeltaDifferentialState, ConsolidatedState, NextId>>

RECURSIVE MaxOf(_,_,_)
MaxOf(seqs, fieldFn(_), value) ==
    IF seqs = <<>>
    THEN value
    ELSE LET fieldValue == fieldFn(Head(seqs))
         IN IF value > fieldValue
            THEN MaxOf(Tail(seqs), fieldFn, value)
            ELSE MaxOf(Tail(seqs), fieldFn, fieldValue)

RECURSIVE SumOf(_,_,_)
SumOf(seqs, fieldFn(_), value) ==
    IF seqs = <<>>
    THEN value
    ELSE SumOf(Tail(seqs), fieldFn, value + fieldFn(Head(seqs)))
         
TypeOK ==
    /\ DifferentialState \in [id: Nat, size: Nat]
    /\ DeltaDifferentialState \in Seq([id: Nat, size: Nat])
    /\ ConsolidatedState \in [id: Nat, size: Nat, exist: BOOLEAN]
    /\ NextId \in Nat

Init ==
    /\ DifferentialState = [id |-> 1, size |-> 0]
    /\ DeltaDifferentialState = <<>>
    /\ ConsolidatedState = [id |-> 0, size |-> 0, exist |-> FALSE]
    /\ NextId = 2

Write ==
    IF DifferentialState.size >= MaxSizeOfDifferntialState
    THEN /\ DifferentialState' = [id |-> NextId, size |-> 1]
         /\ NextId' = NextId + 1
         /\ DeltaDifferentialState' = Append(DeltaDifferentialState, DifferentialState)
         /\ UNCHANGED<<ConsolidatedState>>
    ELSE /\ DifferentialState' = [DifferentialState EXCEPT !.size = DifferentialState.size + 1]
         /\ UNCHANGED<<DeltaDifferentialState, ConsolidatedState, NextId>>

Checkpoint ==
    /\ \/ DeltaDifferentialState # <<>>
       \/ DifferentialState.size > 0
    /\ DifferentialState' = [id |-> NextId, size |-> 0]
    /\ NextId' = NextId + 1
    /\ DeltaDifferentialState' = <<>>
    /\ LET GetId(a) == a.id
           GetSize(a) == a.size
           AllDifferentials == Append(DeltaDifferentialState, DifferentialState)
       IN ConsolidatedState' = [id |-> MaxOf(AllDifferentials, GetId, 0), 
                                exist |-> TRUE, 
                                size |-> SumOf(AllDifferentials, GetSize, 0)] 

Next ==
    \/ Write
    \/ Checkpoint
    
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

AllUniqueStates ==
    /\ \A s \in DOMAIN DeltaDifferentialState : 
            /\ DeltaDifferentialState[s].id < DifferentialState.id
            /\ \/ ConsolidatedState.exist = FALSE
               \/ DeltaDifferentialState[s].id > ConsolidatedState.id

ValidConsolidatedState ==
    \/ ConsolidatedState.exist = FALSE
    \/ ConsolidatedState.size > 0
    
=============================================================================
\* Modification History
\* Last modified Fri Jul 30 18:14:00 PDT 2021 by asnegi
\* Created Fri Jul 30 16:33:44 PDT 2021 by asnegi
