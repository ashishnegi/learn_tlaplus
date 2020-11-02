----------------------------- MODULE sflogcrash -----------------------------

EXTENDS Integers, Sequences

\* Spec for a Logger
\* Logger appends data to a file called write extent which has max capacity of 1 GB.
\* Once write extent is full, we move it to a set of read only files called read extents.
\* Each extent/file is made up of start and end LSN (logical sequence numbers)
\*      extent: [ start, end ] where start <= end.
\*              means that extent contains data from [start, end) // end not included
\*              start == end means no data in file.
\* ReadOnlyExtents => sequence of read only files, which moved to read only set, after size limit.
\* WriteExtent => current file to which logger is appending
\* LSN => tracks LSN to which logger has acked write success
\* NextState, PrevState => used for restricting the next state of the logger state machine
\* MaxLSN => used for reducing the search space to finish running the model checker and visualizing the space graph.
VARIABLES ReadOnlyExtents, WriteExtent, LSN, NextState, PrevState, MaxLSN

TypeOK ==
    \* How to tell TLA+ to put upper bound on LSN so that TLC does analysis only under LSN < MaxLSN ?
    \* How to say it is Sequence of Records with start and end fields ?
    \* /\ ReadOnlyExtents \in <<>> 
    \* How to create a set of records with start <= end ?
    \* Todo: How to add null as state to WriteExtent ? -- when write extent file does not exist on disk.
    /\ WriteExtent \in [ { "start", "end" } -> 0..MaxLSN ] 
    /\ LSN \in 0..MaxLSN
    /\ NextState \in {          "append", "WE_full_move_to_RE", "WE_full_new_WE", "crash" }
    /\ PrevState \in { "start", "append", "WE_full_move_to_RE", "WE_full_new_WE", "crash" }
    /\ MaxLSN = 2

Init ==
    /\ ReadOnlyExtents = <<>>
    /\ WriteExtent = [start |-> 0, end |-> 0]
    /\ LSN = 0
    /\ NextState = "append"
    /\ PrevState = "start"
    /\ MaxLSN = 2

\* Append keeps appending to WriteExtent increasing end LSN.
\* Prev states: "append" or "WE_full_new_WE" states.
\* Next states: "append" or "WE_full_move_to_RE" states.  
AppendToFile ==
    /\ \/ PrevState = "start"
       \/ PrevState = "append"
       \/ PrevState = "WE_full_new_WE"
    /\ LSN < MaxLSN
    /\ ReadOnlyExtents' = ReadOnlyExtents
    /\ WriteExtent' = [start |-> WriteExtent.start, end |-> WriteExtent.end + 1]
    /\ LSN' = LSN + 1
    /\ \/ NextState' = "append"
       \/ NextState' = "WE_full_move_to_RE"
    /\ PrevState' = "append"
    /\ UNCHANGED << MaxLSN >>

\* Append fills up write extent file
\* Make write extent a read only extent
\* Prev states: "append"
\* Next states: "WE_full_new_WE"
WriteExtentFullMoveToReadOnly ==
    /\ PrevState = "append"
    /\ ReadOnlyExtents' = Append(ReadOnlyExtents, WriteExtent)
    /\ WriteExtent' = WriteExtent \* How to make it null ? i.e. does not exist on disk.
    /\ LSN' = LSN
    /\ NextState' = "WE_full_new_WE"
    /\ PrevState' = "WE_full_move_to_RE"
    /\ UNCHANGED << MaxLSN >>

\* Create new write extent file and open for new appends
\* Prev states: "WE_full_move_to_RE"
\* Next states: "append"
NewWriteExtentAppend ==
    /\ PrevState = "WE_full_move_to_RE"
    /\ LSN < MaxLSN
    /\ ReadOnlyExtents' = ReadOnlyExtents
    /\ WriteExtent' = [start |-> WriteExtent.end + 1, end |-> WriteExtent.end + 1]
    /\ LSN' = LSN + 1
    /\ NextState' = "append"
    /\ PrevState' = "WE_full_new_WE"
    /\ UNCHANGED << MaxLSN >>
    
Next ==
    \/ AppendToFile
    \/ WriteExtentFullMoveToReadOnly
    \/ NewWriteExtentAppend

\* Invariants:

\* Invariant 1: NoDataLoss
\* All read only extents have non missing LSN
\*   ReadOnlyExtents[1].start < ReadOnlyExtents[1].end + 1 == ReadOnlyExtents[2].start
\*         < ReadOnlyExtents[2].end + 1 == ReadOnlyExtents[3].start < ...
\* write extent has latest data
\*   LSN == WriteExtent.end >= WriteExtent.start == ReadOnlyExtents[last].end + 1

ValidReadOnlyExtents ==
    /\ \A i \in 1..Len(ReadOnlyExtents)-1 : /\ ReadOnlyExtents[i].start < ReadOnlyExtents[i].end
                                            /\ ReadOnlyExtents[i].end + 1 = ReadOnlyExtents[i+1].start
    \* In "WE_full_move_to_RE" state, 
    \* WriteExtent does not exist on disk as it is moved to ReadOnlyExtents
    /\ \/ PrevState = "WE_full_move_to_RE" \* Todo: Handle this case ? by WE as null
       \/ IF Len(ReadOnlyExtents) > 0
          THEN ReadOnlyExtents[Len(ReadOnlyExtents)].end + 1 = WriteExtent.start
          ELSE 1 = 1

ValidWriteExtent ==
    /\ WriteExtent.start <= WriteExtent.end
    /\ WriteExtent.end = LSN

NoDataLoss ==
    /\ ValidReadOnlyExtents
    /\ ValidWriteExtent

\* Change below value to see different steps taken for particular test run.
LSNSteps ==
    LSN < MaxLSN
=============================================================================
\* Modification History
\* Last modified Sun Nov 01 21:11:30 PST 2020 by asnegi
\* Created Wed Oct 28 17:55:29 PDT 2020 by asnegi
