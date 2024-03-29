---------------------------- MODULE tstorepscal ----------------------------
EXTENDS Integers, Sequences, TLC
CONSTANT CheckpointAfterSize

RECURSIVE Sum(_,_,_)
Sum(sequ, op(_), acc) ==
    IF sequ = <<>>
    THEN acc
    ELSE Sum(Tail(sequ), op, acc + op(Head(sequ)))

(*--algorithm tstorepscal

variables differentialState = [id |-> 0, size |-> 0],
          consolidatedState = <<>>,
          mergedEnumerable = <<>>,
          history = [numWrites |-> 0],
          nextId = 1

define
    AllUniqueInConsolidated ==
        \/ pc["checkpoint"] \in { "PrepareCheckpoint1", "PrepareCheckpoint2" }
        \/ /\ \A cs \in DOMAIN consolidatedState: consolidatedState[cs].id < differentialState.id
            /\ \A cs1, cs2 \in DOMAIN consolidatedState:
                \/ cs1 = cs2
                \/ consolidatedState[cs1].id # consolidatedState[cs2].id

    AllUniqueInEnumerable ==
        \A m1, m2 \in DOMAIN mergedEnumerable:
            \/ m1 = m2
            \/ mergedEnumerable[m1].id # mergedEnumerable[m2].id

    NoDataLoss ==
        \/ pc["checkpoint"] \in { "PrepareCheckpoint1", "PrepareCheckpoint2" }
        \/ LET GetSize(s) == s.size
           IN /\ history.numWrites = Sum(consolidatedState, GetSize, 0) + differentialState.size
    
    TypeOk ==
        /\ differentialState \in [id: Nat, size: Nat]
        /\ nextId \in Nat
        /\ consolidatedState \in Seq([id: Nat, size: Nat])
        /\ history \in [numWrites: Nat]

end define;

process writer = "writer"
begin Write:
    while TRUE do
        differentialState := [differentialState EXCEPT !.size = differentialState.size + 1];
        history.numWrites := history.numWrites + 1;
    end while;
end process;

process checkpoint = "checkpoint"
begin Checkpoint:
    while TRUE do
        await differentialState.size >= CheckpointAfterSize;

    PrepareCheckpoint1:
        consolidatedState := Append(consolidatedState, differentialState);
    PrepareCheckpoint2:
        differentialState := [id |-> nextId, size |-> 0];
        nextId := nextId + 1;
    PrepareCheckpointDone:
        skip;
    \* Not needed as of now
    (*
    DoCheckpoint:
        skip;
    CompleteCheckpoint:
        skip;
    *)
    end while;
end process;

process enumerable = "enumerable"
variable localEnumerable = <<>>, snapDifferentialState = <<>>;
begin Enumerable:
    while TRUE do
        Enumerable1:
        snapDifferentialState := differentialState;
        Enumerable2:
        localEnumerable := Append(consolidatedState, snapDifferentialState);
        Enumerable3:
        mergedEnumerable := IF \E c \in DOMAIN consolidatedState: consolidatedState[c].id = snapDifferentialState.id
                            THEN consolidatedState
                            ELSE localEnumerable
    end while;
end process;
end algorithm;*)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-ba31dc15f4dfd2c855a56af691a48696 (chksum(pcal) = "dbce1629" /\ chksum(tla) = "c43bdf97") (chksum(pcal) = "dbce1629" /\ chksum(tla) = "c43bdf97") (chksum(pcal) = "f85ee517" /\ chksum(tla) = "a063f0c8") (chksum(pcal) = "ff8211d1" /\ chksum(tla) = "5147be61") (chksum(pcal) = "1fa04d02" /\ chksum(tla) = "c71e981d") (chksum(pcal) = "edb08381" /\ chksum(tla) = "d3317524") (chksum(pcal) = "3016893f" /\ chksum(tla) = "c481ad63") (chksum(pcal) = "34eb4454" /\ chksum(tla) = "90e8a869") (chksum(pcal) = "9de27dc9" /\ chksum(tla) = "5ceea770") (chksum(pcal) = "e46aa204" /\ chksum(tla) = "2db58197") (chksum(pcal) = "e46aa204" /\ chksum(tla) = "2db58197") (chksum(pcal) = "473576d1" /\ chksum(tla) = "b2670709") (chksum(pcal) = "f8c77581" /\ chksum(tla) = "af4ea2f5") (chksum(pcal) = "f8c77581" /\ chksum(tla) = "af4ea2f5") (chksum(pcal) = "e46aa204" /\ chksum(tla) = "2db58197")
VARIABLES differentialState, consolidatedState, mergedEnumerable, history, 
          nextId, pc

(* define statement *)
AllUniqueInConsolidated ==
    \/ pc["checkpoint"] \in { "PrepareCheckpoint1", "PrepareCheckpoint2" }
    \/ /\ \A cs \in DOMAIN consolidatedState: consolidatedState[cs].id < differentialState.id
        /\ \A cs1, cs2 \in DOMAIN consolidatedState:
            \/ cs1 = cs2
            \/ consolidatedState[cs1].id # consolidatedState[cs2].id

AllUniqueInEnumerable ==
    \A m1, m2 \in DOMAIN mergedEnumerable:
        \/ m1 = m2
        \/ mergedEnumerable[m1].id # mergedEnumerable[m2].id

NoDataLoss ==
    \/ pc["checkpoint"] \in { "PrepareCheckpoint1", "PrepareCheckpoint2" }
    \/ LET GetSize(s) == s.size
       IN /\ history.numWrites = Sum(consolidatedState, GetSize, 0) + differentialState.size

TypeOk ==
    /\ differentialState \in [id: Nat, size: Nat]
    /\ nextId \in Nat
    /\ consolidatedState \in Seq([id: Nat, size: Nat])
    /\ history \in [numWrites: Nat]

VARIABLES localEnumerable, snapDifferentialState

vars == << differentialState, consolidatedState, mergedEnumerable, history, 
           nextId, pc, localEnumerable, snapDifferentialState >>

ProcSet == {"writer"} \cup {"checkpoint"} \cup {"enumerable"}

Init == (* Global variables *)
        /\ differentialState = [id |-> 0, size |-> 0]
        /\ consolidatedState = <<>>
        /\ mergedEnumerable = <<>>
        /\ history = [numWrites |-> 0]
        /\ nextId = 1
        (* Process enumerable *)
        /\ localEnumerable = <<>>
        /\ snapDifferentialState = <<>>
        /\ pc = [self \in ProcSet |-> CASE self = "writer" -> "Write"
                                        [] self = "checkpoint" -> "Checkpoint"
                                        [] self = "enumerable" -> "Enumerable"]

Write == /\ pc["writer"] = "Write"
         /\ differentialState' = [differentialState EXCEPT !.size = differentialState.size + 1]
         /\ history' = [history EXCEPT !.numWrites = history.numWrites + 1]
         /\ pc' = [pc EXCEPT !["writer"] = "Write"]
         /\ UNCHANGED << consolidatedState, mergedEnumerable, nextId, 
                         localEnumerable, snapDifferentialState >>

writer == Write

Checkpoint == /\ pc["checkpoint"] = "Checkpoint"
              /\ differentialState.size >= CheckpointAfterSize
              /\ pc' = [pc EXCEPT !["checkpoint"] = "PrepareCheckpoint1"]
              /\ UNCHANGED << differentialState, consolidatedState, 
                              mergedEnumerable, history, nextId, 
                              localEnumerable, snapDifferentialState >>

PrepareCheckpoint1 == /\ pc["checkpoint"] = "PrepareCheckpoint1"
                      /\ consolidatedState' = Append(consolidatedState, differentialState)
                      /\ pc' = [pc EXCEPT !["checkpoint"] = "PrepareCheckpoint2"]
                      /\ UNCHANGED << differentialState, mergedEnumerable, 
                                      history, nextId, localEnumerable, 
                                      snapDifferentialState >>

PrepareCheckpoint2 == /\ pc["checkpoint"] = "PrepareCheckpoint2"
                      /\ differentialState' = [id |-> nextId, size |-> 0]
                      /\ nextId' = nextId + 1
                      /\ pc' = [pc EXCEPT !["checkpoint"] = "PrepareCheckpointDone"]
                      /\ UNCHANGED << consolidatedState, mergedEnumerable, 
                                      history, localEnumerable, 
                                      snapDifferentialState >>

PrepareCheckpointDone == /\ pc["checkpoint"] = "PrepareCheckpointDone"
                         /\ TRUE
                         /\ pc' = [pc EXCEPT !["checkpoint"] = "Checkpoint"]
                         /\ UNCHANGED << differentialState, consolidatedState, 
                                         mergedEnumerable, history, nextId, 
                                         localEnumerable, 
                                         snapDifferentialState >>

checkpoint == Checkpoint \/ PrepareCheckpoint1 \/ PrepareCheckpoint2
                 \/ PrepareCheckpointDone

Enumerable == /\ pc["enumerable"] = "Enumerable"
              /\ pc' = [pc EXCEPT !["enumerable"] = "Enumerable1"]
              /\ UNCHANGED << differentialState, consolidatedState, 
                              mergedEnumerable, history, nextId, 
                              localEnumerable, snapDifferentialState >>

Enumerable1 == /\ pc["enumerable"] = "Enumerable1"
               /\ snapDifferentialState' = differentialState
               /\ pc' = [pc EXCEPT !["enumerable"] = "Enumerable2"]
               /\ UNCHANGED << differentialState, consolidatedState, 
                               mergedEnumerable, history, nextId, 
                               localEnumerable >>

Enumerable2 == /\ pc["enumerable"] = "Enumerable2"
               /\ localEnumerable' = Append(consolidatedState, snapDifferentialState)
               /\ pc' = [pc EXCEPT !["enumerable"] = "Enumerable3"]
               /\ UNCHANGED << differentialState, consolidatedState, 
                               mergedEnumerable, history, nextId, 
                               snapDifferentialState >>

Enumerable3 == /\ pc["enumerable"] = "Enumerable3"
               /\ mergedEnumerable' = (IF \E c \in DOMAIN consolidatedState: consolidatedState[c].id = snapDifferentialState.id
                                       THEN consolidatedState
                                       ELSE localEnumerable)
               /\ pc' = [pc EXCEPT !["enumerable"] = "Enumerable"]
               /\ UNCHANGED << differentialState, consolidatedState, history, 
                               nextId, localEnumerable, snapDifferentialState >>

enumerable == Enumerable \/ Enumerable1 \/ Enumerable2 \/ Enumerable3

Next == writer \/ checkpoint \/ enumerable

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ba0adce1479b0526898fc49d3f7b6113
=============================================================================
\* Modification History
\* Last modified Mon Aug 16 14:30:09 PDT 2021 by asnegi
\* Created Fri Jul 30 18:57:13 PDT 2021 by asnegi
