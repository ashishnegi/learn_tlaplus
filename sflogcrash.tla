----------------------------- MODULE sflogcrash -----------------------------

EXTENDS Integers, Sequences
VARIABLES ReadOnlyExtents, WriteExtent, LSN

TypeOK ==
    /\ ReadOnlyExtents = <<>> \* How to say it is a set of Records with start and end fields ?
    /\ WriteExtent = \A i, j \in Nat : /\ [ start |-> i, end |-> j]
                                       /\ i <= j
    /\ LSN \in 0..10

Init ==
    /\ ReadOnlyExtents = <<>>
    /\ WriteExtent = [start |-> 0, end |-> 0]
    /\ LSN = 0
    
NewWriteExtent ==
    /\ ReadOnlyExtents' = Append(ReadOnlyExtents, WriteExtent)
    /\ WriteExtent' = [start |-> WriteExtent.end + 1, end |-> WriteExtent.end + 1]
    /\ LSN' = LSN + 1

AppendToFile ==
    /\ ReadOnlyExtents' = ReadOnlyExtents
    /\ WriteExtent' = [start |-> WriteExtent.start, end |-> LSN + 1]
    /\ LSN' = LSN + 1
    
Next ==
    \/ AppendToFile
    \/ NewWriteExtent

\* NoDataLoss
\* All read only extents have non missing LSN
\*   ReadOnlyExtents[1].start <= ReadOnlyExtents[1].end == ReadOnlyExtents[2].start + 1 
\*         <= ReadOnlyExtents[2].end == ReadOnlyExtents[3].start + 1 <= ...
\* write extent has latest data
\*   LSN == WriteExtent.end >= WriteExtent.start == ReadOnlyExtents[last].end + 1

NoDataLoss ==
    /\ \A i \in 1..Len(ReadOnlyExtents)-1 : /\ ReadOnlyExtents[i].start <= ReadOnlyExtents[i].end
                                            /\ ReadOnlyExtents[i].end + 1 = ReadOnlyExtents[i+1].start
    /\ IF Len(ReadOnlyExtents) > 0
       THEN ReadOnlyExtents[Len(ReadOnlyExtents)].end + 1 = WriteExtent.start
       ELSE 1 = 1
    /\ WriteExtent.start <= WriteExtent.end
    /\ WriteExtent.end = LSN
    
    
=============================================================================
\* Modification History
\* Last modified Thu Oct 29 05:45:59 PDT 2020 by asnegi
\* Created Wed Oct 28 17:55:29 PDT 2020 by asnegi
