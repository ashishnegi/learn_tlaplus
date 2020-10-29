----------------------------- MODULE sflogcrash -----------------------------

EXTENDS Integers, Sequences

\* Spec for a Logger
\* Logger appends data to a file called write extent which has max capacity of 1 GB.
\* Once write extent is full, we move it to a set of read only files called read extents.
\* Each extent/file is made up of start and end LSN (logical sequence numbers)
\*      extent: [ start, end ] where start <= end.
\*              means that extent contains data from [start, end) // end not included
\*              start == end means no data in file.
VARIABLES ReadOnlyExtents, WriteExtent, LSN, NextState, PrevState

TypeOK ==
    /\ ReadOnlyExtents = <<>> \* How to say it is a Sequence of Records with start and end fields ?
    \* How to add null as state to WriteExtent ? -- when write extent file does not exist on disk.
    /\ WriteExtent = \A i, j \in Nat : /\ [ start |-> i, end |-> j]
                                       /\ i <= j
    /\ LSN \in 0..10
    /\ NextState \in {          "append", "write_extent_full_move_to_readonly", "write_extent_full_new_write_extent", "crash" }
    /\ PrevState \in { "start", "append", "write_extent_full_move_to_readonly", "write_extent_full_new_write_extent", "crash" }


Init ==
    /\ ReadOnlyExtents = <<>>
    /\ WriteExtent = [start |-> 0, end |-> 0]
    /\ LSN = 0
    /\ NextState = "append"
    /\ PrevState = "start"

\* Append keeps appending to WriteExtent increasing end LSN.
\* Prev states: "append" or "write_extent_full_new_write_extent" states.
\* Next states: "append" or "write_extent_full_move_to_readonly" states.  
AppendToFile ==
    /\ \/ PrevState = "start"
       \/ PrevState = "append"
       \/ PrevState = "write_extent_full_new_write_extent"
    /\ ReadOnlyExtents' = ReadOnlyExtents
    /\ WriteExtent' = [start |-> WriteExtent.start, end |-> WriteExtent.end + 1]
    /\ LSN' = LSN + 1
    /\ \/ NextState' = "append"
       \/ NextState' = "write_extent_full_move_to_readonly"
    /\ PrevState' = "append"

\* Append fills up write extent file
\* Make write extent a read only extent
\* Prev states: "append"
\* Next states: "write_extent_full_new_write_extent"
WriteExtentFullMoveToReadOnly ==
    /\ PrevState = "append"
    /\ ReadOnlyExtents' = Append(ReadOnlyExtents, WriteExtent)
    /\ WriteExtent' = WriteExtent \* How to make it null ? i.e. does not exist on disk.
    /\ LSN' = LSN
    /\ NextState' = "write_extent_full_new_write_extent"
    /\ PrevState' = "write_extent_full_move_to_readonly"

\* Create new write extent file and open for new appends
\* Prev states: "write_extent_full_move_to_readonly"
\* Next states: "append"
NewWriteExtentAppend ==
    /\ PrevState = "write_extent_full_move_to_readonly"
    /\ ReadOnlyExtents' = ReadOnlyExtents
    /\ WriteExtent' = [start |-> WriteExtent.end + 1, end |-> WriteExtent.end + 1]
    /\ LSN' = LSN + 1
    /\ NextState' = "append"
    /\ PrevState' = "write_extent_full_new_write_extent"
    
Next ==
    \/ AppendToFile
    \/ WriteExtentFullMoveToReadOnly
    \/ NewWriteExtentAppend

\* Invariants:

\* Invariant 1: NoDataLoss
\* All read only extents have non missing LSN
\*   ReadOnlyExtents[1].start <= ReadOnlyExtents[1].end == ReadOnlyExtents[2].start + 1 
\*         <= ReadOnlyExtents[2].end == ReadOnlyExtents[3].start + 1 <= ...
\* write extent has latest data
\*   LSN == WriteExtent.end >= WriteExtent.start == ReadOnlyExtents[last].end + 1

ValidReadOnlyExtents ==
    /\ \A i \in 1..Len(ReadOnlyExtents)-1 : /\ ReadOnlyExtents[i].start <= ReadOnlyExtents[i].end
                                            /\ ReadOnlyExtents[i].end + 1 = ReadOnlyExtents[i+1].start
    \* In "write_extent_full_move_to_readonly" state, 
    \* WriteExtent does not exist on disk as it is moved to ReadOnlyExtents
    /\ \/ PrevState = "write_extent_full_move_to_readonly" 
       \/ IF Len(ReadOnlyExtents) > 0
          THEN ReadOnlyExtents[Len(ReadOnlyExtents)].end + 1 = WriteExtent.start
          ELSE 1 = 1

ValidWriteExtent ==
    /\ WriteExtent.start <= WriteExtent.end
    /\ WriteExtent.end = LSN

NoDataLoss ==
    /\ ValidReadOnlyExtents
    /\ ValidWriteExtent


=============================================================================
\* Modification History
\* Last modified Thu Oct 29 07:14:15 PDT 2020 by asnegi
\* Created Wed Oct 28 17:55:29 PDT 2020 by asnegi
