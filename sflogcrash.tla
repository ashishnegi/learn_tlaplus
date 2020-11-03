----------------------------- MODULE sflogcrash -----------------------------

EXTENDS Integers, Sequences

\* Spec for a Logger
\* Logger appends data to a file called write extent which has max capacity of 1 GB.
\* Once write extent is full, we move it to a set of read only files called read extents.
\* Each extent/file is made up of start and end LSN (logical sequence numbers)
\*      extent: [ start, end ] where start <= end.
\*              means that extent contains data from [start, end) // end not included
\*              start == end means no data in file.
\* REs => sequence of read only files, which moved to read only set, after size limit.
\* WE => current file to which logger is appending
\* LSN => tracks LSN to which logger has acked write success
\* PrevState => used for restricting the next state of the logger state machine
\* MaxLSN => used for reducing the search space to finish running the model checker and visualizing the space graph.
VARIABLES REs, WE, WEonDisk, LSN, PrevState, MaxLSN

TypeOK ==
    /\ WE \in [ start : 1..MaxLSN+1, end : 1..MaxLSN+1 ]
    /\ WE.start <= WE.end
    /\ REs \in Seq([ start: 1..MaxLSN+1, end : 1..MaxLSN+1])
    /\ WEonDisk \in { TRUE, FALSE }
    /\ LSN \in 0..MaxLSN
    /\ PrevState \in { "start", "append", "WE_full_move_to_RE", "WE_full_new_WE", "crash", "recovery" }
    /\ MaxLSN = 2

Init ==
    /\ REs = <<>>
    /\ WE = [start |-> 1, end |-> 1]
    /\ WEonDisk = TRUE
    /\ LSN = 0
    /\ PrevState = "start"
    /\ MaxLSN = 2

\* Append keeps appending to WE increasing end LSN.
\* Prev states: "append" or "WE_full_new_WE" states.
\* Next states: "append" or "WE_full_move_to_RE" states.  
AppendToFile ==
    /\ \/ PrevState = "start"
       \/ PrevState = "append"
       \/ PrevState = "WE_full_new_WE"
       \/ PrevState = "recovery"
    /\ LSN < MaxLSN  \* Stop TLC model checker to generate more cases.
    /\ WE' = [start |-> WE.start, end |-> WE.end + 1]
    /\ LSN' = LSN + 1
    /\ PrevState' = "append"
    /\ UNCHANGED << MaxLSN, REs, WEonDisk >>

\* Append fills up write extent file
\* Make write extent a read only extent
\* Prev states: "append"
\* Next states: "WE_full_new_WE"
WriteExtentFullMoveToReadOnly ==
    /\ PrevState = "append"
    /\ REs' = Append(REs, WE)
    /\ WEonDisk' = FALSE
    /\ LSN' = LSN
    /\ PrevState' = "WE_full_move_to_RE"
    /\ UNCHANGED << MaxLSN, WE >>

\* Create new write extent file and open for new appends
\* Prev states: "WE_full_move_to_RE"
\* Next states: "append"
NewWriteExtentAppend ==
    /\ PrevState = "WE_full_move_to_RE"
    /\ LSN < MaxLSN
    /\ WE' = [start |-> WE.end, end |-> WE.end + 1]
    /\ LSN' = LSN + 1
    /\ PrevState' = "WE_full_new_WE"
    /\ UNCHANGED << MaxLSN, REs, WEonDisk >>

\* Crash: torn write : last write ignored
CrashWhileAppend ==
    /\ \/ PrevState = "append"
       \/ PrevState = "WE_full_new_WE"
    /\ PrevState' = "crash"
    /\ LSN' = LSN - 1
    /\ UNCHANGED << MaxLSN, REs, WE, WEonDisk >>
    
CrashNoDataLoss ==
    /\ PrevState' = "crash"
    /\ UNCHANGED << MaxLSN, LSN, REs, WE, WEonDisk >>    

\* Crash:
CrashDataLost ==
    /\ PrevState' = "crash"
    /\ LSN' = IF LSN > (MaxLSN \div 2)
              THEN MaxLSN \div 2
              ELSE IF LSN > 2
                   THEN 2
                   ELSE 0
    /\ UNCHANGED << MaxLSN, WE, WEonDisk >>

\* After crash, we can't look at value of WEonDisk, WE
\* We have a list of files on disk
Recovery ==
    /\ PrevState = "crash"
    /\ PrevState' = "recovery"
    /\ WEonDisk' = TRUE
    /\ LET allFiles == IF Len(REs) = 0
                       THEN <<WE>>
                       ELSE IF REs[Len(REs)] = WE
                            THEN REs
                            ELSE Append(REs, WE)
           goodREs == LET NonCorrupt(re) == (re.start <= LSN)
                      IN SelectSeq(allFiles, NonCorrupt)
       IN /\ REs' = IF Len(goodREs) > 0
                    THEN SubSeq(goodREs, 1, Len(goodREs) - 1)
                    ELSE <<>>
          /\ WE' = IF Len(goodREs) > 0
                   THEN [ goodREs[Len(goodREs)] EXCEPT !["end"] = LSN + 1 ]
                   ELSE [start |-> 1, end |-> LSN + 1]
    /\ UNCHANGED << MaxLSN, LSN >>

Next ==
    \/ AppendToFile
    \/ WriteExtentFullMoveToReadOnly
    \/ NewWriteExtentAppend
    \/ CrashWhileAppend
    \/ CrashNoDataLoss
    \/ Recovery

\* Invariants:

\* Invariant 1: NoDataLoss
\* All read only extents have non missing LSN
\*   REs[1].start < REs[1].end + 1 == REs[2].start
\*         < REs[2].end + 1 == REs[3].start < ...
\* write extent has latest data
\*   LSN == WE.end >= WE.start == REs[last].end + 1

ValidReadOnlyExtents ==
    /\ \A i \in 1..Len(REs)-1 : /\ REs[i].start < REs[i].end
                                /\ REs[i].end = REs[i+1].start
    \* In "WE_full_move_to_RE" state, 
    \* WE does not exist on disk as it is moved to REs
    /\ \/ WEonDisk = FALSE \* Todo: Handle this case ? by WE as null
       \/ IF Len(REs) > 0
          THEN REs[Len(REs)].end = WE.start
          ELSE 1 = 1

ValidWriteExtent ==
    /\ WE.start <= WE.end
    /\ WE.end = LSN + 1

NoDataLoss ==
    \/ PrevState = "crash" \* No valid state during crash
    \/ /\ ValidReadOnlyExtents
       /\ ValidWriteExtent

\* Change below value to see different steps taken for particular test run.
LSNSteps ==
    LSN < MaxLSN - 1
=============================================================================
\* Modification History
\* Last modified Tue Nov 03 14:08:54 PST 2020 by asnegi
\* Created Wed Oct 28 17:55:29 PDT 2020 by asnegi
