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
\* Todo:
\* 1) MetaDataFile corruption is single point of failure.
\*        Todo: Create metadataFile.mdlog.tmp file first, 
\*              then delete metadataFile.mdlog and rename .mdlog.tmp to .mdlog
\*              Handle crash after each step in Recovery.

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
                          cleanShutdown : { TRUE, FALSE }, fileIds : Seq(1..MaxNum) ]
    /\ TornWrite \in { TRUE, FALSE }
    /\ MaxNum = 7

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
    /\ MaxNum = 7

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
    /\ WE' = [WE EXCEPT !.end = WE.end + 1,
             \* Next write after TruncateTail will append to file with new version number.
                        !.version = MetadataFile.lastTailVersion]
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

\* Helper functions
RECURSIVE filterSeq(_,_,_)
filterSeq(seqs, F(_), result) ==
    IF seqs = <<>>
    THEN result
    ELSE filterSeq(Tail(seqs), 
                   F, 
                   IF F(Head(seqs))
                   THEN Append(result, Head(seqs))
                   ELSE result)

RECURSIVE mapSeq(_,_,_)
mapSeq(seqs, M(_), result) ==
    IF seqs = <<>>
    THEN result
    ELSE mapSeq(Tail(seqs), 
                   M, 
                   Append(result, M(Head(seqs))))

GetAllIds(files) ==
    LET getId(r) == r.id
    IN mapSeq(files, getId, <<>>)

\* Helper functions end    

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
                lastWE == LET lastWEId == MetadataFile.fileIds[Len(MetadataFile.fileIds)]
                              SameId(r) == r.id = lastWEId
                          IN Head(filterSeq(allFiles, SameId, <<>>))
                \* highLSN:
                \*     case : Crash during append - TornWrite : Last LSN in write file.
                \*     case : Crash during TruncateTail phase1
                \*                  LastTailLSN : if version of WE is < metadataFile's version
                \*   We can't append while TruncateTail is going on, 
                \*   so we can't have both cases occuring at same time together.
                highLSN == LET lastValidWrite == lastWE.end
                           IN IF TornWrite 
                              THEN lastValidWrite - 1
                              ELSE IF lastWE.version < MetadataFile.lastTailVersion
                              THEN MetadataFile.lastTailLSN
                              ELSE lastValidWrite
                goodREs == LET ValidFile(re) == ~ (\/ (re.end <= lowLSN) \/ (re.start > highLSN))
                           IN SelectSeq(allFiles, ValidFile)
            IN /\ REs' = IF Len(goodREs) > 0
                         THEN SubSeq(goodREs, 1, Len(goodREs) - 1)
                         ELSE <<>>
               /\ WE' = IF Len(goodREs) > 0
                        \* From last file, remove all data higher than metadataFile.lastTailVersion
                        THEN [goodREs[Len(goodREs)] EXCEPT !.end = highLSN,
                                                           !.version = MetadataFile.lastTailVersion]
                        ELSE [id |-> 1, start |-> lowLSN, end |-> highLSN, 
                              version |-> MetadataFile.lastTailVersion]
    /\ TornWrite' = FALSE
    /\ UNCHANGED << LowLSN, MaxNum, HighLSN, MetadataFile >>
        
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
                                            !.fileIds = GetAllIds(Append(newREs, WE))]
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
                                            !.fileIds = GetAllIds(Append(REs, WE))]
    /\ UNCHANGED << LowLSN, WE, REs, MaxNum, WEonDisk, TornWrite >>

\* Now, zero WE file's tail in Phase 2.
TruncateTailP2 ==
    /\ PrevState = "truncate_tail_p1"
    /\ PrevState' = "truncate_tail"
    /\ IF WE.start < WE.end
       THEN /\ WE' = [WE EXCEPT !.end = WE.end - 1]
            /\ REs' = REs
       ELSE /\ WE' = LET lastRE == REs[Len(REs)]
                     IN [ lastRE EXCEPT !.end = lastRE.end - 1]
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

\* [dangling_extent]  [lowLSN, highLSN - valid range]  [dangling_extent]
NotDanglingExtent(ex, lowLSN, highLSN) ==
    ~ ( \/ ex.start >= highLSN
        \/ ex.end <= lowLSN)
        
OrderedExtent(ex1, ex2, highLSN) ==
    /\ ex1.start < ex1.end
    /\ ex1.end = ex2.start
    /\ ex1.end <= highLSN

ValidReadOnlyExtents(CheckDangling) ==
    /\ \A i \in 1..Len(REs)-1 : /\ OrderedExtent(REs[i], REs[i+1], HighLSN)
                                /\ REs[i].end < HighLSN
                                /\ \/ ~ CheckDangling
                                   \/ NotDanglingExtent(REs[i], LowLSN, HighLSN)
    \* In "WE_full_move_to_RE" state, 
    \* WE does not exist on disk as it is moved to REs
    /\ \/ WEonDisk = FALSE
       \/ IF Len(REs) > 0
          THEN LET lastRE == REs[Len(REs)] 
               IN /\ OrderedExtent(lastRE, WE, HighLSN)
                  /\ \/ ~ CheckDangling
                     \/ NotDanglingExtent(lastRE, LowLSN, HighLSN)
          ELSE 1 = 1

ValidWriteExtent ==
    /\ WE.start <= WE.end
    /\ WE.end = HighLSN

NoDataLoss ==
    \/ PrevState = "crash" \* No valid state during crash
    \/ PrevState = "truncate_head_p1"
    \* Todo: Find what is happening ?
    \*   Commenting below line fails the Invariant `NoDataLoss` but does not show the
    \*  steps of failure in TLC Errors window.
    \/ PrevState = "truncate_tail_p1"
    \/ LET checkDangling == ~ (\/ PrevState = "truncate_head_p1"
                               \/ PrevState = "truncate_tail_p1")
       IN /\ ValidReadOnlyExtents(checkDangling)
          /\ ValidWriteExtent
          /\ LowLSN <= HighLSN

\* Change below value to see different steps taken for particular test run.
LSNSteps ==
    HighLSN < MaxNum

\* Crash: Not modelling case of data lost.
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
=============================================================================
\* Modification History
\* Last modified Tue Nov 10 15:03:21 PST 2020 by asnegi
\* Created Wed Oct 28 17:55:29 PDT 2020 by asnegi
