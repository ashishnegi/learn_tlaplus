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

VARIABLES Fast, Slow, Done

TypeOK ==
    /\ Fast \in 1..N
    /\ Slow \in 1..N
    /\ Done \in {TRUE, FALSE}

Init == 
    /\ Fast \in 1..N
    /\ Slow \in 1..N
    /\ Done = FALSE
    \* different starting position
    /\ Fast # Slow

MovePointers ==
    /\ Done = FALSE
    /\ Fast' = (Fast + 2) % N
    /\ Slow' = (Slow + 1) % N
    /\ Done' = (Fast' = Slow')              
    /\ UNCHANGED <<N>>
    
Next ==
    /\ MovePointers
    /\ TLCGet("level") < 3
    
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

=============================================================================
\* Modification History
\* Last modified Mon Nov 16 19:20:20 PST 2020 by asnegi
\* Created Mon Nov 16 17:53:19 PST 2020 by asnegi
