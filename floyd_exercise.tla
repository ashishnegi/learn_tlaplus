--------------------------- MODULE floyd_exercise ---------------------------

(***************************************************************************)
(* TLA+ Study Group Exercise: 11/24/2020 *)
(* this is a algorithm of detecting a cycle in a linekd list, using O(1)   *)
(* space.  This algorithm was invented by Robert Floyd and it was called   *)
(* "The Tortoise and the Hare"                                             *)
(* https://dev.to/alisabaj/floyd-s-tortoise-and-hare-algorithm-finding-a-cycle-in-a-linked-list-39af *)
(* The idea behind the algorithm is that, if you have two pointers in a linked list, 
   one moving twice as fast (the hare) than the other (the tortoise), then if they intersect, 
   there is a cycle in the linked list. If they don't intersect, then there is no cycle. *)
(***************************************************************************)

\* Comment for Students:
\* Before reading further, try to attempt the problem yourself.
\* Think about your variables, initial values, different actions and invariants.
\* Write them down in pseudo TLA+.
\* Then complete the exercise in this Spec or complete your own TLA+ spec.

EXTENDS Naturals, TLC

(***************************************************************************)
(* Constant N defines length of linked list                                *)
(***************************************************************************)

\* N : Run model checker for upto size N of lists.
CONSTANTS N

ASSUME N \in Nat

\* Nodes are in set 1..N
Nodes == 1..N

(***************************************************************************)
(* NIL is a termination value of the linekd list                           *)
(*                                                                         *)
(* to be able to work correctly model should have definition               *)
(*                                                                         *)
(* CONSTANT NIL= NIL                                                       *)
(***************************************************************************)
NIL == CHOOSE NIL : NIL \notin Nodes

VARIABLES start, succ, cycle, tortoise, hare, done

\* vars is sequence of all the variables so that we can use it in Property or Spec.
vars == << start, succ, cycle, tortoise, hare, done >>

\* Helper functions for list - begin
getNextNode(node) ==
    IF node \in DOMAIN succ
        THEN succ[node]
        ELSE NIL

getNextNextNode(node) ==
    LET node1 == getNextNode(node) 
    IN getNextNode(node1)
\* Helper functions for list - end

Init == (* Global variables *)
        /\ start \in Nodes
        /\ succ \in [Nodes -> Nodes \union {NIL}]
        /\ hare = getNextNode(start)
        /\ tortoise = getNextNextNode(start)
        /\ cycle = FALSE
        /\ done = FALSE

\* Comment for Students: Implement this Action.
\* goNext Action moves hare and tortoise
goNext == UNCHANGED << start, succ, hare, tortoise, cycle, done >>

\* Comment for Students: Implement this Action.
\* checkState checks if we have found the cycle or if we are done
checkState == UNCHANGED << start, succ, hare, tortoise, cycle, done >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == done = TRUE /\ UNCHANGED vars

Next == goNext \/ checkState \/ Terminating

Spec == /\ Init 
        /\ [][Next]_vars
        /\ WF_vars(Next)

\* Comment for Students:
\* Below part of the Spec gives alternative TLA+ implementation for finding
\* cycles in a link list. This will be used for testing your implementation in goNext and checkState.
\* We test this using Property "PartialCorrectness" below.

\* Transitive closure
\* From https://github.com/tlaplus/Examples/blob/master/specifications/TransitiveClosure/TransitiveClosure.tla
TC(R) ==
  LET Support(X) == {r[1] : r \in X} \cup {r[2] : r \in X}
      S == Support(R)
      RECURSIVE TCR(_)
      TCR(T) == IF T = {} 
                  THEN R
                  ELSE LET r == CHOOSE s \in T : TRUE
                           RR == TCR(T \ {r})
                       IN  RR \cup {<<s, t>> \in S \X S : 
                                      <<s, r>> \in RR /\ <<r, t>> \in RR}
  IN  TCR(S)

HasCycle(node) == LET R == {<<s, t>> \in Nodes \X (Nodes \union {NIL}): succ[s] = t }
                  IN <<node, NIL>> \notin TC(R)

\* Comment for Students:
\* Check this property by adding it in the Model Checker's "Model Overview" => "What to check" => "Properties".
PartialCorrectness == done = TRUE => (cycle <=> HasCycle(start))

=============================================================================
\* Modification History
\* Last modified Mon Nov 23 20:25:00 PST 2020 by asnegi
\* Created Mon Nov 23 20:01:18 PST 2020 by asnegi
