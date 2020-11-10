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
\* MaxNum => used for reducing the search space to finish running the model checker and visualizing the space graph.
\* MetaDataFile => Stores headLSN, tailLSN, tailVersionNum, fileNames
\*     When a new file is created after last WE fills up, it's entry is added in metadataFile
\*     When Truncation happens, head and tail are updated in metadataFile
\*     Recovery uses metadataFile for knowing list of files in log
\*      
\* Issues:
\* 1) MetaDataFile is single point of failure.
\*        Todo: Create metadataFile.mdlog.tmp file first, 
\*              then delete metadataFile.mdlog and rename .mdlog.tmp to .mdlog

\* TLA+ spec : Look at MetadataFile info to make decision during recovery
VARIABLES REs, WE, WEonDisk, LowLSN, HighLSN, PrevState, MaxNum, MetadataFile, TornWrite

TypeOK ==
    /\ WE \in [ id: 1..MaxNum, start : 1..MaxNum, end : 1..MaxNum, version : 1..MaxNum ]
    /\ WE.start <= WE.end
    /\ REs \in Seq([ id: 1..MaxNum, start: 1..MaxNum, end : 1..MaxNum, version : 1..MaxNum])
    /\ WEonDisk \in { TRUE, FALSE }
    /\ LowLSN \in 1..MaxNum
    /\ HighLSN \in 1..MaxNum
    /\ PrevState \in { "start", "append", "WE_full_move_to_RE", 
                       "WE_full_new_WE", "crash", "recovery",
                       "truncate_head_p1", "truncate_head", 
                       "truncate_tail_p1", "truncate_tail", "close" }
    /\ MetadataFile \in [ headLSN : 1..MaxNum, lastTailLSN : 1..MaxNum, lastTailVersion : 1..MaxNum, 
                          cleanShutdown : { TRUE, FALSE },
                          fileIds : Seq(1..MaxNum) ]
    /\ TornWrite \in { TRUE, FALSE}
    /\ MaxNum = 10

Init ==
    /\ REs = <<>>
    /\ WE = [id |-> 1, start |-> 1, end |-> 1, version |-> 1]
    /\ WEonDisk = TRUE
    /\ LowLSN = 1
    /\ HighLSN = 1
    /\ PrevState = "start"
    /\ MetadataFile = [headLSN |-> 1, lastTailLSN |-> 1, lastTailVersion |-> 1, 
                       cleanShutdown |-> FALSE, fileIds |-> <<1>> ]
    /\ TornWrite = FALSE
    /\ MaxNum = 10

\* Append keeps appending to WE increasing end LSN.
\* Prev states: "append" or "WE_full_new_WE" states.
\* Next states: "append" or "WE_full_move_to_RE" states.  
AppendToFile ==
    \* Append to file is always allowed except crash. 
    \* After crash, we first do recovery.
    /\ PrevState # "crash"
    /\ PrevState # "WE_full_move_to_RE"
    /\ PrevState # "close"
    \* Todo : remove truncate_head_p1 as append can happen after truncate_head acks
    \* Invariant of dangling file fails.
    /\ PrevState # "truncate_head_p1"
    /\ PrevState # "truncate_tail_p1"
    /\ HighLSN < MaxNum - 1 \* Stop TLC model checker to generate more cases.
    /\ WE' = [WE EXCEPT !.end = WE.end + 1]
    /\ HighLSN' = HighLSN + 1
    /\ PrevState' = "append"
    /\ UNCHANGED << LowLSN, MaxNum, REs, WEonDisk, MetadataFile, TornWrite >>

\* Append fills up write extent file
\* Make write extent a read only extent
\* Prev states: "append"
\* Next states: "WE_full_new_WE"
WriteExtentFullMoveToReadOnly ==
    /\ PrevState = "append"
    /\ REs' = Append(REs, WE)
    /\ WEonDisk' = FALSE
    /\ PrevState' = "WE_full_move_to_RE"
    /\ UNCHANGED << LowLSN, HighLSN, MaxNum, WE, MetadataFile, TornWrite >>

\* Create new write extent file and open for new appends
\* Prev states: "WE_full_move_to_RE"
\* Next states: "append"
NewWriteExtentAppend ==
    /\ PrevState = "WE_full_move_to_RE"
    /\ HighLSN < MaxNum - 1
    /\ WE' = [id |-> WE.id + 1, start |-> WE.end, end |-> WE.end + 1, version |-> WE.version]
    /\ HighLSN' = HighLSN + 1
    /\ PrevState' = "WE_full_new_WE"
    /\ WEonDisk' = TRUE
    /\ MetadataFile' = [MetadataFile EXCEPT !.fileIds = Append(MetadataFile.fileIds, WE'.id)]
    /\ UNCHANGED << LowLSN, MaxNum, REs, TornWrite >>

\* Crash: torn write : last write ignored
CrashWhileAppend ==
    /\ \/ PrevState = "append"
       \/ PrevState = "WE_full_new_WE"
    /\ PrevState' = "crash"
    /\ HighLSN' = HighLSN - 1
    /\ TornWrite' = TRUE
    /\ MetadataFile' = [MetadataFile EXCEPT !.cleanShutdown = FALSE]
    /\ UNCHANGED << LowLSN, MaxNum, REs, WE, WEonDisk >>
    
CrashNoDataLoss ==
    /\ PrevState' = "crash"
    /\ MetadataFile' = [MetadataFile EXCEPT !.cleanShutdown = FALSE]
    /\ UNCHANGED << LowLSN, MaxNum, HighLSN, REs, WE, WEonDisk, TornWrite>>

Close ==
    /\ PrevState # "crash"
    /\ PrevState # "WE_full_move_to_RE"
    /\ PrevState # "truncate_head_p1" \* Possibly can be avoided.
    /\ PrevState # "truncate_tail_p1"
    /\ PrevState' = "close"
    /\ MetadataFile' = [MetadataFile EXCEPT !.cleanShutdown = TRUE]
    /\ UNCHANGED << LowLSN, MaxNum, HighLSN, REs, WE, WEonDisk, TornWrite >>
    

MaxOf2(a, b) ==
    IF a < b
    THEN b
    ELSE a

\* Crash:
\* we lost all data after some LSN
\* Todo: need to model - data lost in between LowLSN and HighLSN
\*       In that case, we will Fail replica in real world 
\*       and rebuild from another source.
CrashDataLost ==
    /\ PrevState' = "crash"
    /\ HighLSN' = IF HighLSN > (MaxNum \div 2)
                  THEN MaxOf2(LowLSN, MaxNum \div 2)
                  ELSE IF HighLSN > 3
                  THEN MaxOf2(LowLSN, 3)
                  ELSE MaxOf2(LowLSN, 1)
    /\ MetadataFile' = [MetadataFile EXCEPT !.cleanShutdown = FALSE]
    /\ UNCHANGED << LowLSN, MaxNum, REs, WE, WEonDisk, TornWrite>>

\* After crash, we can't look at value of WEonDisk, WE
\* We have a list of files on disk
Recovery ==
    /\ \/ PrevState = "crash"
       \/ PrevState = "close"
    /\ PrevState' = "recovery"
    /\ WEonDisk' = TRUE
    /\ IF MetadataFile.cleanShutdown
       THEN /\ REs' = REs
            /\ WE' = WE
       ELSE LET allFiles == IF WEonDisk
                            THEN Append(REs, WE)
                            ELSE REs
                            (* TODO: use below: [fId \in MetadataFile.fileIds |-> 
                                LET SameId(r) == r.Id = fId
                                IN SelectSeq(REs \union {WE}, SameId)]*)
                lowLSN == MetadataFile.headLSN
                \* highLSN:
                \*     Last LSN in write file in case of crash during append
                \*     Todo: handle below case.
                \*     LastTailLSN : if version of WE is < metadataFile's version
                \*                   in case of crash during TruncateTail phase1.
                highLSN == LET lastValidWrite == allFiles[MetadataFile.fileIds[Len(MetadataFile.fileIds)]].end
                           IN IF TornWrite 
                              THEN lastValidWrite - 1
                              ELSE lastValidWrite
                goodREs == LET ValidFile(re) == ~ (\/ (re.end < lowLSN) \/ (re.start > highLSN))
                           IN SelectSeq(allFiles, ValidFile)
            IN /\ REs' = IF Len(goodREs) > 0
                         THEN SubSeq(goodREs, 1, Len(goodREs) - 1)
                         ELSE <<>>
               /\ WE' = IF Len(goodREs) > 0
                        \* From last file, remove all data higher than metadataFile.lastTailVersion
                        THEN [goodREs[Len(goodREs)] EXCEPT !.end = highLSN]
                        ELSE [id |-> 1, start |-> 1, end |-> 1, version |-> 1]
    /\ TornWrite' = FALSE
    /\ UNCHANGED << LowLSN, MaxNum, HighLSN, MetadataFile >>

RECURSIVE GetAllIds(_,_)
GetAllIds(files, ids) ==
    IF files = <<>>
    THEN ids
    ELSE GetAllIds(Tail(files), Append(ids, Head(files).id))

\* TruncateHead
\* Phase1 : Update metadata file first.
\* We broke truncate head in 2 phases to simulate a crash in between 2 stages.
TruncateHeadP1 ==
    /\ \/ PrevState = "append"
       \/ PrevState = "WE_full_new_WE"
    /\ LowLSN < HighLSN
    /\ PrevState' = "truncate_head_p1"
    /\ LowLSN' = LowLSN + 1
    /\ LET newREs == LET nonTruncatedRE(re) == re.end > LowLSN'
                     IN SelectSeq(REs, nonTruncatedRE)
       IN MetadataFile' = [MetadataFile EXCEPT !.headLSN = LowLSN', 
                                            !.lastTailLSN = HighLSN,
                                            !.fileIds = GetAllIds(Append(newREs, WE), <<>>)]
    /\ UNCHANGED << HighLSN, MaxNum, REs, WE, WEonDisk, TornWrite >>

TruncateHeadP2 ==
    /\ PrevState = "truncate_head_p1"
    /\ PrevState' = "truncate_head"
    /\ REs' = LET nonTruncatedRE(re) == re.end > LowLSN
              IN SelectSeq(REs, nonTruncatedRE)
    /\ UNCHANGED << LowLSN, HighLSN, MaxNum, WE, WEonDisk, MetadataFile, TornWrite >>    
    
\* TruncateTailP1 :
\* Phase1 : Update metadata file first.
\* We broke truncate tail in 2 phases to simulate a crash in between 2 stages.
\* Update metadata file first:
\* If we crash after updating metadata file, we can truncate tail of WE on recovery.
TruncateTailP1 ==
    /\ \/ PrevState = "append"
       \/ PrevState = "WE_full_new_WE"
    /\ LowLSN < HighLSN
    /\ MetadataFile.lastTailVersion < MaxNum - 1
    /\ PrevState' = "truncate_tail_p1"
    /\ HighLSN' = HighLSN - 1
    /\ MetadataFile' = [MetadataFile EXCEPT !.lastTailLSN = HighLSN',
                                            !.lastTailVersion = MetadataFile.lastTailVersion + 1,
                                            !.fileIds = GetAllIds(Append(REs, WE), <<>>)]
    /\ UNCHANGED << LowLSN, WE, REs, MaxNum, WEonDisk, TornWrite >>

\* Now, zero WE file's head in Phase 2.
TruncateTailP2 ==
    /\ PrevState = "truncate_tail_p1"
    /\ PrevState' = "truncate_tail"
    /\ IF WE.start < WE.end
       THEN /\ WE' = [WE EXCEPT !.end = WE.end - 1]
            /\ REs' = REs
       ELSE /\ WE' = LET lastRE == REs[Len(REs)]
                     IN [ lastRE EXCEPT !.end = lastRE.end - 1 ]
            /\ REs' = SubSeq(REs, 1, Len(REs)-1)
    /\ UNCHANGED << LowLSN, HighLSN, MaxNum, WEonDisk, MetadataFile, TornWrite >>

Next ==
    \/ AppendToFile
    \/ WriteExtentFullMoveToReadOnly
    \/ NewWriteExtentAppend
    \/ CrashWhileAppend
    \/ CrashNoDataLoss
    \/ Close
    \/ Recovery
    \/ TruncateHeadP1
    \/ TruncateHeadP2
    \/ TruncateTailP1
    \/ TruncateTailP2
    \* Not modelling Data Loss. I am not sure, if we should just fail to open if we find we lost data so that
    \* we build from new replica.    
    \* \/ CrashDataLost
    
\* Invariants:

\* Invariant 1: NoDataLoss
\* All read only extents have non missing LSN
\*   REs[1].start < REs[1].end == REs[2].start < REs[2].end == REs[3].start < ...
\* write extent has latest data
\*   HighLSN == WE.end >= WE.start == REs[last].end

NoDanglingFile(re, lowLSN) ==
    \/ re.start >= lowLSN
    \/ re.end > lowLSN

ValidReadOnlyExtents ==
    /\ \A i \in 1..Len(REs)-1 : /\ REs[i].start < REs[i].end
                                /\ REs[i].end = REs[i+1].start
                                /\ REs[i].end < HighLSN
                                /\ NoDanglingFile(REs[i], LowLSN)
    \* In "WE_full_move_to_RE" state, 
    \* WE does not exist on disk as it is moved to REs
    /\ \/ WEonDisk = FALSE
       \/ IF Len(REs) > 0
          THEN LET lastRE == REs[Len(REs)] 
               IN /\ lastRE.end = WE.start
                  /\ lastRE.start < lastRE.end
                  /\ lastRE.end <= HighLSN
                  /\ NoDanglingFile(lastRE, LowLSN)
          ELSE 1 = 1

ValidWriteExtent ==
    /\ WE.start <= WE.end
    /\ WE.end = HighLSN

NoDataLoss ==
    \/ PrevState = "crash" \* No valid state during crash
    \/ PrevState = "truncate_head_p1"
    \/ PrevState = "truncate_tail_p1"
    \/ /\ ValidReadOnlyExtents
       /\ ValidWriteExtent
       /\ LowLSN <= HighLSN

\* Change below value to see different steps taken for particular test run.
LSNSteps ==
    MetadataFile.lastTailVersion < MaxNum

=============================================================================
\* Modification History
\* Last modified Mon Nov 09 23:01:14 PST 2020 by asnegi
\* Created Wed Oct 28 17:55:29 PDT 2020 by asnegi
