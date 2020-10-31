------------------------------ MODULE tcommit ------------------------------

EXTENDS Integers
VARIABLES Anna, Henry, Minister, Steps

TypeOK ==
    /\ Anna \in { "working", "prepared", "commit", "abort" }
    /\ Henry \in { "working", "prepared", "commit", "abort" }
    /\ Minister \in { "working", "prepared", "commit", "abort" }
    /\ Steps \in 1..10

Init ==
    /\ Minister = "prepared"
    /\ Anna = "working"
    /\ Henry = "working"
    /\ Steps = 1
    
PrepareAnna == 
    /\ Minister = "prepared"
    /\ Anna = "working"
    /\ Anna' = "prepared"
    /\ UNCHANGED << Minister, Henry >>
    /\ Steps' = Steps + 1

PrepareHenry == 
    /\ Minister = "prepared"
    /\ Henry = "working"
    /\ Henry' = "prepared"
    /\ UNCHANGED << Anna, Minister >>
    /\ Steps' = Steps + 1

AbortAnna == 
    /\ \/ Anna = "working"
       \/ Anna = "prepared"
    /\ Anna' = "abort"
    /\ UNCHANGED << Minister, Henry >>
    /\ Steps' = Steps + 1
    
AbortHenry == 
    /\ \/ Henry = "working"
       \/ Henry = "prepared"
    /\ Henry' = "abort"
    /\ UNCHANGED << Anna, Minister >>
    /\ Steps' = Steps + 1
    
CommitAnna == 
    /\ Anna = "prepared"
    /\ Anna' = "commit"
    /\ UNCHANGED << Minister, Henry >>
    /\ Steps' = Steps + 1
    
CommitHenry == 
    /\ Henry = "prepared"
    /\ Henry' = "commit"
    /\ UNCHANGED << Anna, Minister >>
    /\ Steps' = Steps + 1

CommitMinister ==
    /\ Minister = "prepared"
    /\ Anna = "commit"
    /\ Henry = "commit"
    /\ Minister' = "commit"
    /\ Anna' = "commit"
    /\ Henry' = "commit"
    /\ Steps' = Steps + 1
    
AbortMinister ==
    /\ Minister = "prepared"
    /\ \/ Anna = "abort"
       \/ Henry = "abort"
    /\ Minister' = "abort"
    /\ Anna' = "abort"
    /\ Henry' = "abort"
    /\ Steps' = Steps + 1

Next ==
    \/ PrepareAnna \/ AbortAnna \/ CommitAnna
    \/ PrepareHenry \/ AbortHenry \/ CommitHenry
    \/ AbortMinister \/ CommitMinister
    
ValidTermination ==
    \/ Minister = "prepared"
    \/ /\ Anna = "abort"
       /\ Henry = "abort"
    \/ /\ Anna = "commit"
       /\ Henry = "commit"

Visualize == 
    Steps < 6


(*

How to find "what" of a system ?
How to find "how" of a system ? => Write down a simple sequence of events among participants as mentioned in die-hard problem video lecture ?

Is "what" of system :
    * What each individual part is supposed to do ?
And "how" of system :
    * How individual parts communicate with each other ?
    
Will every system have "what" and "how" ?

*)

(*

(***************************************************************************)
(* This specification is explained in "Transaction Commit", Lecture 5 of   *)
(* the TLA+ Video Course.                                                  *)
(***************************************************************************)
CONSTANT RM       \* The set of participating resource managers

VARIABLE rmState  \* rmState[rm] is the state of resource manager rm.
-----------------------------------------------------------------------------
TCTypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
        
TCInit ==   rmState = [r \in RM |-> "working"]
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}
  (*************************************************************************)
  (* True iff all RMs are in the "prepared" or "committed" state.          *)
  (*************************************************************************)

notCommitted == \A r \in RM : rmState[r] # "committed" 
  (*************************************************************************)
  (* True iff no resource manager has decided to commit.                   *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the RMs, and then    *)
(* define the complete next-state action of the specification to be the    *)
(* disjunction of the possible RM actions.                                 *)
(***************************************************************************)
Prepare(r) == /\ rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Decide(r)  == \/ /\ rmState[r] = "prepared"
                 /\ canCommit
                 /\ rmState' = [rmState EXCEPT ![r] = "committed"]
              \/ /\ rmState[r] \in {"working", "prepared"}
                 /\ notCommitted
                 /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM : Prepare(r) \/ Decide(r)
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
-----------------------------------------------------------------------------
TCConsistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.  It is an invariant of the specification.      *)
  (*************************************************************************)
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following part of the spec is not discussed in Video Lecture 5.  It *)
(* will be explained in Video Lecture 8.                                   *)
(***************************************************************************)
TCSpec == TCInit /\ [][TCNext]_rmState
  (*************************************************************************)
  (* The complete specification of the protocol written as a temporal      *)
  (* formula.                                                              *)
  (*************************************************************************)

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
  (*************************************************************************)
  (* This theorem asserts the truth of the temporal formula whose meaning  *)
  (* is that the state predicate TCTypeOK /\ TCInvariant is an invariant   *)
  (* of the specification TCSpec.  Invariance of this conjunction is       *)
  (* equivalent to invariance of both of the formulas TCTypeOK and         *)
  (* TCConsistent.                                                         *)
  (*************************************************************************)

*)
=============================================================================
\* Modification History
\* Last modified Fri Oct 30 20:25:01 PDT 2020 by asnegi
\* Created Thu Oct 29 23:54:32 PDT 2020 by asnegi
