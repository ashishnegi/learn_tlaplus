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
\* LowLSN => lowest valid LSN of the logger
\* HighLSN => highest valid LSN of the logger
\*     Data is stored from [LowLSN, HighLSN)
\* PrevState => used for restricting the next state of the logger state machine
\* MaxLSN => used for reducing the search space to finish running the model checker and visualizing the space graph.
VARIABLES REs, WE, WEonDisk, LowLSN, HighLSN, PrevState, MaxLSN

TypeOK ==
    /\ WE \in [ start : 1..MaxLSN, end : 1..MaxLSN ]
    /\ WE.start <= WE.end
    /\ REs \in Seq([ start: 1..MaxLSN, end : 1..MaxLSN])
    /\ WEonDisk \in { TRUE, FALSE }
    /\ LowLSN \in 1..MaxLSN
    /\ HighLSN \in 1..MaxLSN
    /\ PrevState \in { "start", "append", "WE_full_move_to_RE", 
                       "WE_full_new_WE", "crash", "recovery",
                       "truncate_head", "truncate_tail" }
    /\ MaxLSN = 10

Init ==
    /\ REs = <<>>
    /\ WE = [start |-> 1, end |-> 1]
    /\ WEonDisk = TRUE
    /\ LowLSN = 1
    /\ HighLSN = 1
    /\ PrevState = "start"
    /\ MaxLSN = 10

\* Append keeps appending to WE increasing end LSN.
\* Prev states: "append" or "WE_full_new_WE" states.
\* Next states: "append" or "WE_full_move_to_RE" states.  
AppendToFile ==
    \* Append to file is always allowed except crash. 
    \* After crash, we first do recovery.
    /\ PrevState # "crash"
    /\ WEonDisk = TRUE
    /\ HighLSN < MaxLSN - 1 \* Stop TLC model checker to generate more cases.
    /\ WE' = [start |-> WE.start, end |-> WE.end + 1]
    /\ HighLSN' = HighLSN + 1
    /\ PrevState' = "append"
    /\ UNCHANGED << LowLSN, MaxLSN, REs, WEonDisk >>

\* Append fills up write extent file
\* Make write extent a read only extent
\* Prev states: "append"
\* Next states: "WE_full_new_WE"
WriteExtentFullMoveToReadOnly ==
    /\ PrevState = "append"
    /\ REs' = Append(REs, WE)
    /\ WEonDisk' = FALSE
    /\ PrevState' = "WE_full_move_to_RE"
    /\ UNCHANGED << LowLSN, HighLSN, MaxLSN, WE >>

\* Create new write extent file and open for new appends
\* Prev states: "WE_full_move_to_RE"
\* Next states: "append"
NewWriteExtentAppend ==
    /\ PrevState = "WE_full_move_to_RE"
    /\ HighLSN < MaxLSN - 1
    /\ WE' = [start |-> WE.end, end |-> WE.end + 1]
    /\ HighLSN' = HighLSN + 1
    /\ PrevState' = "WE_full_new_WE"
    /\ WEonDisk' = TRUE
    /\ UNCHANGED << LowLSN, MaxLSN, REs >>

\* Crash: torn write : last write ignored
CrashWhileAppend ==
    /\ \/ PrevState = "append"
       \/ PrevState = "WE_full_new_WE"
    /\ PrevState' = "crash"
    /\ HighLSN' = HighLSN - 1
    /\ UNCHANGED << LowLSN, MaxLSN, REs, WE, WEonDisk >>
    
CrashNoDataLoss ==
    /\ PrevState' = "crash"
    /\ UNCHANGED << LowLSN, MaxLSN, HighLSN, REs, WE, WEonDisk >>

\* Crash:
\* we lost all data after some LSN
\* Todo: need to model - data lost in between LowLSN and HighLSN
\*       In that case, we will Fail replica in real world 
\*       and rebuild from another source.
CrashDataLost ==
    /\ PrevState' = "crash"
    /\ HighLSN' = IF HighLSN > (MaxLSN \div 2)
              THEN MaxLSN \div 2
              ELSE IF HighLSN > 2
                   THEN 2
                   ELSE 1
    /\ UNCHANGED << LowLSN, MaxLSN, REs, WE, WEonDisk >>

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
           \* Don't use WE after this, only use allFiles
           goodREs == LET NonCorrupt(re) == (re.start <= HighLSN)
                      IN SelectSeq(allFiles, NonCorrupt)
       IN /\ REs' = IF Len(goodREs) > 0
                    THEN SubSeq(goodREs, 1, Len(goodREs) - 1)
                    ELSE <<>>
          /\ WE' = IF Len(goodREs) > 0
                   THEN [goodREs[Len(goodREs)] EXCEPT !["end"] = HighLSN]
                   ELSE [start |-> 1, end |-> HighLSN]
    /\ UNCHANGED << LowLSN, MaxLSN, HighLSN >>

\* TruncateHead
\* Todo: Remove REs which are lower than LowLSN
TruncateHead ==
    /\ PrevState # "crash"
    /\ PrevState' = "truncate_head"
    /\ LowLSN < HighLSN
    /\ LowLSN' = LowLSN + 1
    /\ UNCHANGED << HighLSN, MaxLSN, WE, REs, WEonDisk >>

\* TruncateTail
TruncateTail ==
    /\ PrevState # "crash"
    /\ PrevState' = "truncate_tail"
    /\ LowLSN < HighLSN
    /\ HighLSN' = HighLSN - 1
    /\ WE' = [start |-> WE.start, end |-> WE.end - 1]
    /\ UNCHANGED << LowLSN, MaxLSN, REs, WEonDisk >>

Next ==
    \/ AppendToFile
    \/ WriteExtentFullMoveToReadOnly
    \/ NewWriteExtentAppend
    \/ CrashWhileAppend
    \/ CrashNoDataLoss
    \/ CrashDataLost
    \/ Recovery
    \*\/ TruncateTail
    \/ TruncateHead

\* Invariants:

\* Invariant 1: NoDataLoss
\* All read only extents have non missing LSN
\*   REs[1].start < REs[1].end == REs[2].start < REs[2].end == REs[3].start < ...
\* write extent has latest data
\*   HighLSN == WE.end >= WE.start == REs[last].end

ValidReadOnlyExtents ==
    /\ \A i \in 1..Len(REs)-1 : /\ REs[i].start < REs[i].end
                                /\ REs[i].end = REs[i+1].start
    \* In "WE_full_move_to_RE" state, 
    \* WE does not exist on disk as it is moved to REs
    /\ \/ WEonDisk = FALSE
       \/ IF Len(REs) > 0
          THEN REs[Len(REs)].end = WE.start
          ELSE 1 = 1

ValidWriteExtent ==
    /\ WE.start <= WE.end
    /\ WE.end = HighLSN

NoDataLoss ==
    \/ PrevState = "crash" \* No valid state during crash
    \/ /\ ValidReadOnlyExtents
       /\ ValidWriteExtent

\* Change below value to see different steps taken for particular test run.
LSNSteps ==
    HighLSN < MaxLSN

=============================================================================
\* Modification History
\* Last modified Wed Nov 04 15:02:46 PST 2020 by asnegi
\* Created Wed Oct 28 17:55:29 PDT 2020 by asnegi
