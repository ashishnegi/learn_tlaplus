---------------------------- MODULE tstorepscal ----------------------------
EXTENDS Integers, Sequences, TLC
CONSTANT MaxSizeOfDifferentialState

(*--algorithm tstorepscal

variables differentialState = [id |-> 0, size |-> 0], 
          consolidatedState = <<>>,
          nextId = 1

define
    AllUniqueStates == 
        /\ \A cs \in DOMAIN consolidatedState: consolidatedState[cs].id < differentialState.id
        /\ \A cs1, cs2 \in DOMAIN consolidatedState: 
            \/ cs1 = cs2
            \/ consolidatedState[cs1].id # consolidatedState[cs2].id

    TypeOk ==
        /\ differentialState \in [id: Nat, size: Nat]
        /\ nextId \in Nat
        /\ consolidatedState \in Seq([id: Nat, size: Nat])
end define;

begin
    Write:
        if differentialState.size >= MaxSizeOfDifferentialState then
           consolidatedState := Append(consolidatedState, differentialState);
           differentialState := [id |-> nextId, size |-> 1];
           nextId := nextId + 1;
        else
            differentialState := [differentialState EXCEPT !.size = differentialState.size + 1]; 
        end if;

    PrepareCheckpoint:
        consolidatedState := Append(consolidatedState, differentialState);
        differentialState := [id |-> nextId, size |-> 0];
        nextId := nextId + 1;
end algorithm;*)
        
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ba31dc15f4dfd2c855a56af691a48696
VARIABLES differentialState, consolidatedState, nextId, pc

(* define statement *)
AllUniqueStates ==
    /\ \A cs \in DOMAIN consolidatedState: consolidatedState[cs].id < differentialState.id
    /\ \A cs1, cs2 \in DOMAIN consolidatedState:
        \/ cs1 = cs2
        \/ consolidatedState[cs1].id # consolidatedState[cs2].id

TypeOk ==
    /\ differentialState \in [id: Nat, size: Nat]
    /\ nextId \in Nat
    /\ consolidatedState \in Seq([id: Nat, size: Nat])


vars == << differentialState, consolidatedState, nextId, pc >>

Init == (* Global variables *)
        /\ differentialState = [id |-> 0, size |-> 0]
        /\ consolidatedState = <<>>
        /\ nextId = 1
        /\ pc = "Write"

Write == /\ pc = "Write"
         /\ IF differentialState.size >= MaxSizeOfDifferentialState
               THEN /\ consolidatedState' = Append(consolidatedState, differentialState)
                    /\ differentialState' = [id |-> nextId, size |-> 1]
                    /\ nextId' = nextId + 1
               ELSE /\ differentialState' = [differentialState EXCEPT !.size = differentialState.size + 1]
                    /\ UNCHANGED << consolidatedState, nextId >>
         /\ pc' = "PrepareCheckpoint"

PrepareCheckpoint == /\ pc = "PrepareCheckpoint"
                     /\ consolidatedState' = Append(consolidatedState, differentialState)
                     /\ differentialState' = [id |-> nextId, size |-> 0]
                     /\ nextId' = nextId + 1
                     /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Write \/ PrepareCheckpoint
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ba0adce1479b0526898fc49d3f7b6113
=============================================================================
\* Modification History
\* Last modified Fri Aug 06 00:44:54 PDT 2021 by asnegi
\* Created Fri Jul 30 18:57:13 PDT 2021 by asnegi
