------------------------------- MODULE floyd -------------------------------
(*
1. We have a link list of N nodes
2. Detect cycle in node by having 2 pointers
3. One pointer move fast by 2 steps
4. Another point move slow
5. If fast pointer reaches nullptr.. => no cycle
6. If fast poitner == slow => cycle
*)

\* how to represent a list in TLA+ ?
\* how to represent pointers in list ? => tortoise_node_id, hare_node_id

\* Can we say if we have a cycle then fast pointer == slow pointer eventually
\* if slow_pointer = first_node
\* and fast_pointer = first_node or second_node
\* This means that for all N, with a cycle of N, 
\* if we start with {slow = 0, fast = 0/1}, eventually, slow = fast
\* This is easier to model .. Right ?

EXTENDS Integers, 
        TLC \* for debugging
        
CONSTANTS N

VARIABLES CycleSize, Fast, Slow, Done, Steps

vars == << CycleSize, Fast, Slow, Done, Steps >>

TypeOK ==
    /\ CycleSize \in 1..N
    /\ Fast \in 0..CycleSize-1
    /\ Slow \in 0..CycleSize-1
    /\ Steps \in Nat
    /\ Done \in BOOLEAN

Init == 
    /\ CycleSize \in 1..N
    /\ Fast \in 0..CycleSize-1
    /\ Slow \in 0..CycleSize-1
    /\ Done = FALSE
    /\ Steps = 1
    \* different starting position
    /\ Fast # Slow

MovePointers ==
    /\ Done = FALSE
    /\ Fast' = (Fast + 2) % CycleSize
    /\ Slow' = (Slow + 1) % CycleSize
    /\ Done' = (Fast' = Slow')
    /\ Steps' = Steps + 1
    /\ UNCHANGED << CycleSize >>
    
Next ==
    MovePointers

Spec == 
    /\ Init 
    /\ [][Next]_vars
    /\ WF_vars(Next)
    
Termination ==
    <>[]Done
   
\* If we are done, hare = tortoise
DetectCycle ==
    IF Done = TRUE
    THEN Fast = Slow \* make it # to see cycle detected
    ELSE Fast # Slow

\* Failure of this invariant shows TLC ran it for cycle of size 42
RunsFor42 ==
    IF Done = TRUE
    THEN Fast # 42
    ELSE 1 = 1

\* Failure of this invariant shows TLC ran it for numbers far apart.
LongCycle ==
    IF Done = FALSE
    THEN Fast < Slow + 20
    ELSE 1 = 1

\* stop after levels/step for debugging
StopTLC ==
    IF /\ Steps > 100
       \* /\ Done = FALSE \* Uncomment this to see steps before cycle is not detected
    THEN FALSE
    ELSE TRUE

=============================================================================
\* Modification History
\* Last modified Mon Nov 23 20:34:19 PST 2020 by asnegi
\* Created Mon Nov 16 17:53:19 PST 2020 by asnegi
