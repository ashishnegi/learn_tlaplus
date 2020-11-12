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
VARIABLES REs, WE, LowLSN, HighLSN, PrevState, MaxNum, MetadataFile, 
          TornWrite, 
          THIP, \* TruncateHeadInProgress
          TTIP, \* TruncateTailInProgress
          NWEIP, \* New WE In Progress - after current WE is full
          New_WE
            
TypeOK ==
    /\ WE \in [ id: 1..MaxNum, start : 1..MaxNum, end : 1..MaxNum, version : 1..MaxNum ]
    /\ WE.start <= WE.end
    /\ New_WE \in [ exist: {TRUE, FALSE}, id: 1..MaxNum, start : 1..MaxNum, end : 1..MaxNum, version : 1..MaxNum ]
    /\ New_WE.start <= New_WE.end
    /\ REs \in Seq([ id: 1..MaxNum, start: 1..MaxNum, end : 1..MaxNum, version : 1..MaxNum])
    /\ LowLSN \in 1..MaxNum
    /\ HighLSN \in 1..MaxNum
    /\ PrevState \in { "start", "append", "WE_full_New_WE", "New_WE_in_MDT", 
                       "crash", "recovery", "close",
                       "truncate_head_p1", "truncate_head", 
                       "truncate_tail_p1", "truncate_tail" }
    /\ MetadataFile \in [ headLSN : 1..MaxNum, lastTailLSN : 1..MaxNum, lastTailVersion : 1..MaxNum, 
                          cleanShutdown : { TRUE, FALSE }, fileIds : Seq(1..MaxNum) ]
                          
    /\ TornWrite \in { TRUE, FALSE }
    /\ THIP \in { TRUE, FALSE }
    /\ TTIP \in { TRUE, FALSE }
    /\ NWEIP \in { TRUE, FALSE }
    /\ MaxNum = 10

Init ==
    /\ REs = <<>>
    /\ WE = [id |-> 1, start |-> 1, end |-> 1, version |-> 1]
    /\ New_WE = [exist |-> FALSE, id |-> 1, start |-> 1, end |-> 1, version |-> 1]
    /\ LowLSN = 1
    /\ HighLSN = 1
    /\ PrevState = "start"
    /\ MetadataFile = [headLSN |-> 1, lastTailLSN |-> 1, lastTailVersion |-> 1, 
                       cleanShutdown |-> FALSE, fileIds |-> <<1>> ]
    /\ TornWrite = FALSE
    /\ THIP = FALSE
    /\ TTIP = FALSE
    /\ NWEIP = FALSE
    /\ MaxNum = 10

\* Append keeps appending to WE increasing end LSN.
AppendToFile ==
    \* Append to file is always allowed except crash. 
    \* After crash, we first do recovery.
    /\ PrevState \notin { "crash", "close" }
    /\ NWEIP = FALSE \* WE is not full
    \* No writes allowed while truncate_tail is in progress.
    /\ TTIP = FALSE
    /\ HighLSN < MaxNum - 1 \* Stop TLC model checker to generate more cases.
    /\ WE' = [WE EXCEPT !.end = WE.end + 1,
             \* Next write after TruncateTail will append to file with new version number.
                        !.version = MetadataFile.lastTailVersion]
    /\ HighLSN' = HighLSN + 1 \* Ack to customer that write succeeded
    /\ PrevState' = "append"
    /\ UNCHANGED << LowLSN, MaxNum, REs, MetadataFile, TornWrite, THIP, TTIP, NWEIP, New_WE >>

\* New steps:
\*  1. Create a new WE file with right data
\*  2. Add to metadata file and move WE to RE in memory and WE' = new_WE
\* Todo: Is "Append" only valid previous state ?
\*       Handle crash after this step
WriteExtentFullNewWE ==
    /\ PrevState = "append"
    /\ NWEIP' = TRUE \* Stop appends to WE
    \* Create new WE
    /\ New_WE' = [exist |-> TRUE, id |-> WE.id + 1, start |-> WE.end, end |-> WE.end + 1, version |-> WE.version]
    /\ PrevState' = "WE_full_New_WE"
    /\ UNCHANGED << LowLSN, HighLSN, MaxNum, REs, WE, MetadataFile, TornWrite, THIP, TTIP >>

\* Add new write extent file to MetadataFile and open for new appends
\* Todo: Handle crash after this step
NewWriteExtentAddToMetadataFile ==
    /\ PrevState = "WE_full_New_WE"
    /\ HighLSN < MaxNum - 1
    \* Change on disk
    /\ MetadataFile' = [MetadataFile EXCEPT !.fileIds = Append(MetadataFile.fileIds, New_WE.id)]
    \* In memory change
    /\ REs' = Append(REs, WE)
    /\ WE' = [ id      |-> New_WE.id,
               start   |-> New_WE.start,
               end     |-> New_WE.end,
               version |-> New_WE.version ]
    /\ New_WE' = [ New_WE EXCEPT !.exist = FALSE ]
    /\ HighLSN' = HighLSN + 1 \* Ack to customer that write succeeded
    /\ PrevState' = "New_WE_in_MDT"
    /\ NWEIP' = FALSE \* allow appends to WE now
    /\ UNCHANGED << LowLSN, MaxNum, TornWrite, THIP, TTIP >>

\* Crash: torn write : last write ignored
CrashWhileAppend ==
    /\ PrevState = "append"
    /\ PrevState' = "crash"
    /\ HighLSN' = HighLSN - 1
    /\ TornWrite' = TRUE
    /\ MetadataFile' = [MetadataFile EXCEPT !.cleanShutdown = FALSE]
    /\ UNCHANGED << LowLSN, MaxNum, REs, WE, THIP, TTIP, NWEIP, New_WE >>
    
CrashNoDataLoss ==
    /\ PrevState' = "crash"
    /\ MetadataFile' = [MetadataFile EXCEPT !.cleanShutdown = FALSE]
    /\ UNCHANGED << LowLSN, MaxNum, HighLSN, REs, WE, TornWrite, THIP, TTIP, NWEIP, New_WE >>

Close ==
    /\ PrevState \notin { "crash", "close" }
    \* Close waits for workflows to finish: 
    \*    New_WE, truncate_head, truncate_tail
    /\ NWEIP = FALSE
    /\ TTIP = FALSE
    /\ THIP = FALSE
    /\ PrevState' = "close"
    /\ MetadataFile' = [MetadataFile EXCEPT !.cleanShutdown = TRUE]
    /\ UNCHANGED << LowLSN, MaxNum, HighLSN, REs, WE, TornWrite, THIP, TTIP, NWEIP, New_WE >>
    

\* Helper functions -- begin
RECURSIVE filterSeq(_,_,_)
filterSeq(seqs, F(_), result) ==
    IF seqs = <<>>
    THEN result
    ELSE filterSeq(Tail(seqs), 
                   F, 
                   IF F(Head(seqs))
                   THEN Append(result, Head(seqs))
                   ELSE result)

GetAllIds(files) ==
    [ i \in 1..Len(files) |-> files[i].id ]

GetMetadataFiles ==
    LET PresentInMetadataFiles(r) == 
            LET SameId(r2Id) == r.id = r2Id
            IN Len(SelectSeq(MetadataFile.fileIds, SameId)) > 0
    IN SelectSeq(Append(REs, WE), PresentInMetadataFiles)

\* Helper functions -- end    

\* After crash, we can't look at value of WEonDisk, WE
\* We have a list of files on disk
\* Recovery happens on Open
Recovery ==
    /\ \/ PrevState = "crash"
       \/ PrevState = "close"
    /\ IF MetadataFile.cleanShutdown
       THEN /\ REs' = REs
            /\ WE' = WE
            /\ MetadataFile' = MetadataFile
       ELSE LET allFiles == GetMetadataFiles
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
                goodExtents == LET ValidFile(f) == ~ (\/ (f.end <= lowLSN) \/ (f.start > highLSN))
                               IN SelectSeq(allFiles, ValidFile)
                cleanState == Len(goodExtents) =  0
            IN IF cleanState
               THEN /\ REs' = <<>>
                    /\ WE' = [id |-> 1, start |-> lowLSN, end |-> highLSN, 
                              version |-> MetadataFile.lastTailVersion]
                    /\ MetadataFile' = [MetadataFile EXCEPT !.fileIds = <<1>>]
               ELSE /\ REs' = SubSeq(goodExtents, 1, Len(goodExtents) - 1)
                    /\ WE' = [goodExtents[Len(goodExtents)] 
                                EXCEPT !.end = highLSN,
                                       !.version = MetadataFile.lastTailVersion]
                    /\ MetadataFile' = MetadataFile
    \* Reset variables correctly so that appends can work.
    /\ PrevState' = "recovery"
    /\ THIP' = FALSE 
    /\ TTIP' = FALSE
    /\ NWEIP' = FALSE
    /\ New_WE' = [ New_WE EXCEPT !.exist = FALSE ]
    /\ TornWrite' = FALSE
    /\ UNCHANGED << LowLSN, MaxNum, HighLSN >>
        
\* TruncateHead
\* Phase1 : Update metadata file first.
\* We broke truncate head in 2 phases to simulate a crash in between 2 stages.
\* Also, other states like appends can happen in between 2 phases.
TruncateHeadP1 ==
    /\ PrevState \notin { "crash", "close" }
    \* truncate_head waits for new_WE workflow to finish.
    \* Todo: This is possibly bad as even starting the TruncateHead is waiting.
    \*       It is not very bad because WE_full_move_to_RE has high priority 
    \*       and should finish fast.
    /\ NWEIP = FALSE
    /\ THIP = FALSE \* Only 1 truncate_head at a time
    /\ LowLSN < HighLSN
    /\ PrevState' = "truncate_head_p1"
    /\ LowLSN' = LowLSN + 1
    /\ LET newREs == LET nonTruncatedRE(re) == re.end > LowLSN'
                     IN SelectSeq(REs, nonTruncatedRE)
       IN MetadataFile' = [MetadataFile EXCEPT !.headLSN = LowLSN', 
                                            !.lastTailLSN = HighLSN,
                                            !.fileIds = GetAllIds(Append(newREs, WE))]
    /\ THIP' = TRUE
    /\ UNCHANGED << HighLSN, MaxNum, REs, WE, TornWrite, TTIP, NWEIP, New_WE >>

TruncateHeadP2 ==
    /\ \/ PrevState = "truncate_head_p1"
       \/ /\ THIP = TRUE
          /\ PrevState # "crash" \* After crash, only recovery runs
    /\ PrevState' = "truncate_head"
    /\ REs' = LET nonTruncatedRE(re) == re.end > LowLSN
              IN SelectSeq(REs, nonTruncatedRE)
    /\ THIP' = FALSE
    /\ UNCHANGED << LowLSN, HighLSN, MaxNum, WE, MetadataFile, TornWrite, TTIP, NWEIP, New_WE >>    
    
\* TruncateTailP1 :
\* Phase1 : Update metadata file first.
\* We broke truncate tail in 2 phases to simulate a crash in between 2 stages.
\* Update metadata file first:
\* If we crash after updating metadata file, we can truncate tail of WE on recovery.
\* Other valid states like appends can't run between 2 phases.
\* Todo: Is "Append" only valid previous state ?
TruncateTailP1 ==
    /\ \/ PrevState = "append"
       \/ PrevState = "New_WE_in_MDT"
    /\ TTIP = FALSE \* Only one truncate tail allowed at a time.
    /\ LowLSN < HighLSN
    /\ MetadataFile.lastTailVersion < MaxNum - 1
    /\ PrevState' = "truncate_tail_p1"
    /\ HighLSN' = HighLSN - 1
    /\ TTIP' = TRUE
    /\ MetadataFile' = [MetadataFile EXCEPT !.lastTailLSN = HighLSN',
                                            !.lastTailVersion = MetadataFile.lastTailVersion + 1,
                                            !.fileIds = GetAllIds(Append(REs, WE))]
    /\ UNCHANGED << LowLSN, WE, REs, MaxNum, TornWrite, THIP, NWEIP, New_WE >>

\* Now, zero WE file's tail in Phase 2.
TruncateTailP2 ==
    /\ PrevState = "truncate_tail_p1"
    /\ PrevState' = "truncate_tail"
    /\ IF WE.start < WE.end \* WE has data
       THEN /\ WE' = [WE EXCEPT !.end = WE.end - 1]
            /\ REs' = REs
       ELSE /\ WE' = LET lastRE == REs[Len(REs)]
                     IN [ lastRE EXCEPT !.end = lastRE.end - 1]
            /\ REs' = SubSeq(REs, 1, Len(REs)-1)
    /\ TTIP' = FALSE
    /\ UNCHANGED << LowLSN, HighLSN, MaxNum, MetadataFile, TornWrite, THIP, NWEIP, New_WE >>

Next ==
    \/ AppendToFile
    \/ WriteExtentFullNewWE
    \/ NewWriteExtentAddToMetadataFile
    \/ CrashWhileAppend
    \/ CrashNoDataLoss
    \/ Close
    \/ Recovery
    (* \/ TruncateHeadP1
    \/ TruncateHeadP2
    \/ TruncateTailP1
    \/ TruncateTailP2 *)
    \* Not modelling Data Loss. 
    \* I am not sure, if we should just fail to open if we find we lost data 
    \*   so that we build from new replica.    
    \* \/ CrashDataLost
    
\* Invariants:

\* Invariant 1: NoDataLoss
\* All read only extents have non missing LSN
\*   REs[1].start < REs[1].end == REs[2].start < REs[2].end == REs[3].start < ...
\* write extent has latest data
\*   HighLSN == WE.end >= WE.start == REs[last].end

\* [dangling_extent]  [lowLSN, highLSN - valid range]  [dangling_extent]
OrderedExtent(ex1, ex2, highLSN) ==
    /\ ex1.start < ex1.end
    /\ ex1.end = ex2.start
    /\ ex1.end <= highLSN

ValidReadOnlyExtents ==
    /\ \A i \in 1..Len(REs)-1 : /\ OrderedExtent(REs[i], REs[i+1], HighLSN)
                                /\ REs[i].end < HighLSN
    /\ IF Len(REs) > 0
       THEN OrderedExtent(REs[Len(REs)], WE, HighLSN)
       ELSE 1 = 1

ValidWriteExtent ==
    /\ WE.start <= WE.end
    /\ WE.end = HighLSN

MetadataExtentsCoverDataRange ==
    LET allFiles == GetMetadataFiles
        firstFile == allFiles[1]
        lastFile == allFiles[Len(allFiles)]
    IN /\ firstFile.start <= LowLSN
       /\ lastFile.end >= HighLSN

NoDataLoss ==
    \* Not valid state during crash or truncate_tail_phase1
    \/ PrevState \in { "crash", "truncate_tail_p1" }
    \/ TTIP = TRUE \* TruncateTail in progress
    \/ /\ ValidReadOnlyExtents
       /\ ValidWriteExtent
       /\ MetadataExtentsCoverDataRange
       /\ LowLSN <= HighLSN

\* Invariant 2: No dangling files on disk
\* No file/extent present on disk which is not required.
NotDanglingExtent(ex, lowLSN, highLSN) ==
    ~ ( \/ ex.start >= highLSN
        \/ ex.end <= lowLSN )

NoDanglingExtents ==
    \/ PrevState \in {"crash", "truncate_head_p1", "truncate_tail_p1" }
    \/ THIP = TRUE \* TruncateHead is in progress - so some files are dangling.
    \* Todo: Why is TruncateTail not failing for dangling REs ?
    \/ /\ \A i \in 1..Len(REs) : NotDanglingExtent(REs[i], LowLSN, HighLSN)
       /\ \/ WE.start = WE.end \* WE is empty
          \/ LowLSN = HighLSN  \* There is no data in log
          \/ TTIP = TRUE \* TruncateTail is in progress - WE might be dangling
          \* If there is some data, WE should be valid
          \/ NotDanglingExtent(WE, LowLSN, HighLSN)

\* Todo: Correctness of MetadataFile:
\*   1. FileIds should be in increasing order
\*   2. HeadLSN should be same as Expected LowLSN
MetadataFileCorrect ==
    /\ \A i \in 1..Len(MetadataFile.fileIds)-1 : 
                MetadataFile.fileIds[i] < MetadataFile.fileIds[i+1]
    /\ MetadataFile.headLSN = LowLSN
    /\ IF MetadataFile.cleanShutdown
       THEN 1 = 1 \* MetadataFile.lastTailLSN = HighLSN
       \* Todo: What should still be correct in clean shutdown case ?
       ELSE 1 = 1

\* Invariants that should fail - Signifies that we have handled these cases.

\* TruncateTail is not called on empty WE for truncating data upto REs
\* Todo: This is not failing - This case is not handled.
\* Using TTIP is not correct as that means that TT has already begin.
TruncateTailCalledOnEmptyWE ==
    ~ ( /\ TTIP = TRUE
        /\ WE.start = WE.end
      )

TruncateHeadCalledOnEmptyWE == 
    ~ ( /\ THIP = TRUE
        /\ WE.start = WE.end
      )

\* Change below value to see different steps taken for particular test run.
LSNSteps ==
    HighLSN < MaxNum

\* Crash: Not modelling case of data lost.
\* we lost all data after some LSN
\* Todo: need to model - data lost in between LowLSN and HighLSN
\*       In that case, we will Fail replica in real world 
\*       and rebuild from another source.
MaxOf2(a, b) ==
    IF a < b
    THEN b
    ELSE a

CrashDataLost ==
    /\ PrevState' = "crash"
    /\ HighLSN' = IF HighLSN > (MaxNum \div 2)
                  THEN MaxOf2(LowLSN, MaxNum \div 2)
                  ELSE IF HighLSN > 3
                  THEN MaxOf2(LowLSN, 3)
                  ELSE MaxOf2(LowLSN, 1)
    /\ MetadataFile' = [MetadataFile EXCEPT !.cleanShutdown = FALSE]
    /\ UNCHANGED << LowLSN, MaxNum, REs, WE, TornWrite>>
=============================================================================
\* Modification History
\* Last modified Wed Nov 11 17:45:51 PST 2020 by asnegi
\* Created Wed Oct 28 17:55:29 PDT 2020 by asnegi
