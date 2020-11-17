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

EXTENDS Integers

VARIABLES N, Fast, Slow

Init == 
    /\ N = 10
    /\ Fast = 1
    /\ Slow = 0

MovePointers ==
    /\ Fast' = (Fast + 2) % N
    /\ Slow' = (Slow + 1) % N
    /\ UNCHANGED <<N>>
    
Next ==
    MovePointers

\* When DetectCycle invariant fails, we see steps showing that cycle is detected
DetectCycle ==
    Fast # Slow
=============================================================================
\* Modification History
\* Last modified Mon Nov 16 18:42:49 PST 2020 by asnegi
\* Created Mon Nov 16 17:53:19 PST 2020 by asnegi
