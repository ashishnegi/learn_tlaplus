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

process writer = "writer"
begin Write:
    while TRUE do
        if differentialState.size >= MaxSizeOfDifferentialState then
           consolidatedState := Append(consolidatedState, differentialState);
           differentialState := [id |-> nextId, size |-> 1];
           nextId := nextId + 1;
        else
            differentialState := [differentialState EXCEPT !.size = differentialState.size + 1]; 
        end if;
    end while;
end process;

process checkpoint = "checkpoint"
begin Checkpoint:
    while TRUE do
    PrepareCheckpoint:
        consolidatedState := Append(consolidatedState, differentialState);
        differentialState := [id |-> nextId, size |-> 0];
        nextId := nextId + 1;
    DoCheckpoint:
        skip;
    CompleteCheckpoint:
        skip;
    end while;
end process;
end algorithm;*)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ba31dc15f4dfd2c855a56af691a48696 (chksum(pcal) = "dbce1629" /\ chksum(tla) = "c43bdf97") (chksum(pcal) = "dbce1629" /\ chksum(tla) = "c43bdf97")
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

ProcSet == {"writer"} \cup {"checkpoint"}

Init == (* Global variables *)
        /\ differentialState = [id |-> 0, size |-> 0]
        /\ consolidatedState = <<>>
        /\ nextId = 1
        /\ pc = [self \in ProcSet |-> CASE self = "writer" -> "Write"
                                        [] self = "checkpoint" -> "Checkpoint"]

Write == /\ pc["writer"] = "Write"
         /\ IF differentialState.size >= MaxSizeOfDifferentialState
               THEN /\ consolidatedState' = Append(consolidatedState, differentialState)
                    /\ differentialState' = [id |-> nextId, size |-> 1]
                    /\ nextId' = nextId + 1
               ELSE /\ differentialState' = [differentialState EXCEPT !.size = differentialState.size + 1]
                    /\ UNCHANGED << consolidatedState, nextId >>
         /\ pc' = [pc EXCEPT !["writer"] = "Write"]

writer == Write

Checkpoint == /\ pc["checkpoint"] = "Checkpoint"
              /\ pc' = [pc EXCEPT !["checkpoint"] = "PrepareCheckpoint"]
              /\ UNCHANGED << differentialState, consolidatedState, nextId >>

PrepareCheckpoint == /\ pc["checkpoint"] = "PrepareCheckpoint"
                     /\ consolidatedState' = Append(consolidatedState, differentialState)
                     /\ differentialState' = [id |-> nextId, size |-> 0]
                     /\ nextId' = nextId + 1
                     /\ pc' = [pc EXCEPT !["checkpoint"] = "DoCheckpoint"]

DoCheckpoint == /\ pc["checkpoint"] = "DoCheckpoint"
                /\ TRUE
                /\ pc' = [pc EXCEPT !["checkpoint"] = "CompleteCheckpoint"]
                /\ UNCHANGED << differentialState, consolidatedState, nextId >>

CompleteCheckpoint == /\ pc["checkpoint"] = "CompleteCheckpoint"
                      /\ TRUE
                      /\ pc' = [pc EXCEPT !["checkpoint"] = "Checkpoint"]
                      /\ UNCHANGED << differentialState, consolidatedState, 
                                      nextId >>

checkpoint == Checkpoint \/ PrepareCheckpoint \/ DoCheckpoint
                 \/ CompleteCheckpoint

Next == writer \/ checkpoint

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ba0adce1479b0526898fc49d3f7b6113
=============================================================================
\* Modification History
\* Last modified Tue Aug 10 19:10:21 PDT 2021 by asnegi
\* Created Fri Jul 30 18:57:13 PDT 2021 by asnegi
