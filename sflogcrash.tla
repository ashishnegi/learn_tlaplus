----------------------------- MODULE sflogcrash -----------------------------

EXTENDS Integers, Sequences

\* Spec for a Write Ahead Logger (WAL)
\* WAL Logger appends data to a file called write extent (WE) which has max capacity of 1 GB.
\* Once write extent is full, we move it to a set of read files called read extents (RE) and create new WE.
\* Each extent/file has data in range from start to end LSN (logical sequence numbers).
\*      extent: [ start, end ) where start <= end.
\*              means that extent contains data from [start, end) // end not included
\*              start == end means no data in file.
\* Data is appened at the end of log called tail. So, data grows from head towards tail.
\* Other operations performed by logger are truncation of log at head or tail,
\*       Close and recovery of log at Open.
\*
\* State machine valid steps:
\* 1. There is only 1 Append request at a time.
\* 2. After close or crash, only recovery runs.
\* 3. Only 1 TruncateHead request is initiated at a time.
\* 4. Only 1 TruncateTail request is initiated at a time.
\* 5. TruncateHead can be initiated with Append.
\* 6. No other request is served till TruncateTail finishes.

\* Todo:
\* 1) MetaDataFile corruption is single point of failure.
\*        Todo: Create metadataFile.mdlog.tmp file first, 
\*              then delete metadataFile.mdlog and rename .mdlog.tmp to .mdlog
\*              Handle crash after each step in Recovery.

\* Variables are divided into 2 categories:
\* 1. Variables representing on disk data structures
This reads a lot like as if E_ are history variables (https://arxiv.org/pdf/1703.05121.pdf).  It usually makes the spec more reable if you use a single history variable that -for each state- stores a record.  See https://github.com/lemmy/PageQueue/blob/f33ac42ab6402b2f6ec4c0f656ea5367b48b6e78/PageQueue.tla#L137-L154 for an example.
\* 2. Variables representing expected values, prefixed by E_
\* This means that during recovery, we can't use E_* variables.
\* E_* variables are used in Invariants to check that disk state is correct.
VARIABLES 
          Like with Vladimir's spec of Floyd's algorithm, you should see if you really need this variable.
          PrevState, \* For specicying state machine
          WE, \* WE => current file to which logger is appending.
          REs, \* REs => sequence of read only files, which became read only after they were full.
          MetadataFile, \* metadata file storing metadata information of the logger.
          E_LowLSN, \* lowest valid LSN of the logger
          \* Data is stored from [E_LowLSN, E_HighLSN)
          E_HighLSN, \* next valid LSN of the logger. i.e. not including E_HighLSN
          E_THIP, (* TruncateHeadInProgress : Is TruncateHead in progress ?
                     Truncate head means removing old data before offset Head
                  *)
          E_TTIP, (* TruncateTailInProgress : Is TruncateTail in progress ?
                     Truncate tail means removing current data from end of file.
                     This is sometimes needed if we want to reset the file or other false progress cases.
                     Note: New data is appened at tail of the log/file.
                  *)
          E_NWEIP, \* WE is full and Is New WE creation In Progress ?
          New_WE, \* New_WE file while E_NWEIP is TRUE
          TornWrite, \* Did last crash caused torn write ?
          MaxNum \* Variable to restrict TLC Model Checker (MC) to MaxNum steps.
            
TypeOK ==
    /\ WE \in [ id: 1..MaxNum, start : 1..MaxNum, end : 1..MaxNum, version : 1..MaxNum ]
    /\ WE.start <= WE.end
    /\ New_WE \in [ exist: {TRUE, FALSE}, id: 1..MaxNum, start : 1..MaxNum, end : 1..MaxNum, version : 1..MaxNum ]
    /\ New_WE.start <= New_WE.end
    /\ REs \in Seq([ id: 1..MaxNum, start: 1..MaxNum, end : 1..MaxNum, version : 1..MaxNum])
    /\ E_LowLSN \in 1..MaxNum
    /\ E_HighLSN \in 1..MaxNum
    /\ PrevState \in { "start", "append", "WE_full_New_WE", "New_WE_in_MDT", 
                       "crash", "recovery", "close",
                       "truncate_head_p1", "truncate_head", 
                       "truncate_tail_p1", "truncate_tail" }
    \* MetaDataFile => Stores headLSN, tailLSN, tailVersionNum, fileNames
    \*     When a new file is created after last WE fills up, it's entry is added in metadataFile
    \*     When Truncation happens, head and tail are updated in metadataFile
    \*     Recovery uses metadataFile for knowing list of valid files in log
    \*     headLSN corresponds to current E_LowLSN.
    \*     lastTailLSN corresponds to last tail truncation.
    \*     lastTailVersion is needed to know if we crashed during truncating tail or new data has been added
    \*         after last tail truncation.
    \*         This is needed because we don't update metadata file on every write to log WE file.
    /\ MetadataFile \in [ headLSN : 1..MaxNum, lastTailLSN : 1..MaxNum, lastTailVersion : 1..MaxNum, 
                          cleanShutdown : { TRUE, FALSE }, fileIds : Seq(1..MaxNum) ]
                          
    /\ TornWrite \in { TRUE, FALSE }
    /\ E_THIP \in { TRUE, FALSE }
    /\ E_TTIP \in { TRUE, FALSE }
    /\ E_NWEIP \in { TRUE, FALSE }
    This says that MaxNum is always 7
    /\ MaxNum = 7

\* Initial state of the system.
Init ==
    /\ REs = <<>>
    /\ WE = [id |-> 1, start |-> 1, end |-> 1, version |-> 1]
    /\ New_WE = [exist |-> FALSE, id |-> 1, start |-> 1, end |-> 1, version |-> 1]
    /\ E_LowLSN = 1
    /\ E_HighLSN = 1
    /\ PrevState = "start"
    /\ MetadataFile = [headLSN |-> 1, lastTailLSN |-> 1, lastTailVersion |-> 1, 
                       cleanShutdown |-> FALSE, fileIds |-> <<1>> ]
    /\ TornWrite = FALSE
    /\ E_THIP = FALSE
    /\ E_TTIP = FALSE
    /\ E_NWEIP = FALSE
    /\ MaxNum = 7

\* Helper functions -- begin
\* Don't use E_* variables in helper functions.
GetFileIds(files) ==
    [ i \in 1..Len(files) |-> files[i].id ]

GetMetadataFiles ==
    LET PresentInMetadataFiles(r) == 
            LET SameId(r2Id) == r.id = r2Id
            IN Len(SelectSeq(MetadataFile.fileIds, SameId)) > 0
    IN SelectSeq(Append(REs, WE), PresentInMetadataFiles)

GetValidFiles(files, lowLSN, highLSN) ==
    LET ValidFile(f) == /\ f.start < f.end
                        /\ ~ (\/ (f.end <= lowLSN) \/ (f.start > highLSN))
    IN SelectSeq(files, ValidFile)
\* Helper functions -- end

\* Append keeps appending to WE increasing end LSN.
\* No writes allowed while we do Truncate tail.
\* Writes allowed while we do Truncate head.
AppendToFile ==
    \* Append to file is always allowed except close or crash.
    \* After crash/close, we first do recovery.
    /\ PrevState \notin { "crash", "close" }
    /\ E_NWEIP = FALSE \* WE is not full
    \* No writes allowed while truncate_tail is in progress.
    /\ E_TTIP = FALSE
    /\ E_HighLSN < MaxNum - 1 \* Stop TLC model checker to generate more cases.
    /\ WE' = [WE EXCEPT !.end = WE.end + 1,
             \* Every write needs a metadata header with version number
             \* Next write after TruncateTail will append to file with new version number. Thanks TLA+
                        !.version = MetadataFile.lastTailVersion]
    /\ E_HighLSN' = E_HighLSN + 1 \* Ack to customer that write succeeded
    /\ PrevState' = "append"
    /\ UNCHANGED << E_LowLSN, MaxNum, REs, MetadataFile, TornWrite, E_THIP, E_TTIP, E_NWEIP, New_WE >>

\* Action : Write extent is full - Create new Write Extent/file
\*  1. Create a new WE file with right header and append data
\* Next Action: NewWriteExtentAddToMetadataFile :
\*      Add to metadata file and move WE to RE in memory and WE' = new_WE
\* These 2 steps are divided in separate Actions to simulate crash and concurrency with different actions.
\* If we crash before updating Metadata file, we ignore this write and New_WE file is deleted on recovery.
\* Todo: Allow WriteExtentFullNewWE to run after recovery. Add a field in file : full : {TRUE, FALSE}
WriteExtentFullNewWE ==
    /\ \/ PrevState = "append"
       \/ /\ E_THIP = TRUE \* Truncate Head is allowed concurrent with writes.
          /\ PrevState # "crash"
    /\ WE.id < MaxNum - 1 \* Stop MC after these steps
    \* No writes allowed while truncate_tail is in progress.
    /\ E_TTIP = FALSE
    /\ E_NWEIP = FALSE \* Only WE full workflow at a time
    /\ E_NWEIP' = TRUE \* Stop appends to WE
    \* Create new WE
    /\ New_WE' = [ exist |-> TRUE, id |-> WE.id + 1, start |-> WE.end, end |-> WE.end + 1, 
                   \* Next write after TruncateTail will append to file with new version number. Thanks TLA+
                   version |-> MetadataFile.lastTailVersion]

    /\ PrevState' = "WE_full_New_WE"
    /\ UNCHANGED << E_LowLSN, E_HighLSN, MaxNum, REs, WE, MetadataFile, TornWrite, E_THIP, E_TTIP >>

\* Add new write extent file to MetadataFile and open for new appends
NewWriteExtentAddToMetadataFile ==
    /\ E_NWEIP = TRUE
    /\ PrevState # "crash" \* only recovery runs after crash
    /\ E_HighLSN < MaxNum - 1 \* Stop TLC model checker (MC) to generate more cases to finish MC.
    \* No writes allowed while truncate_tail is in progress.
    /\ E_TTIP = FALSE \* How to assert that E_TTIP is false ?
    \* First change MetadataFile on disk:
    \*   It might seem that, We could have easily done !.fileIds = Append(MetadataFile.fileIds, New_WE.id)
    \*   but If you do that , invariant AllMetadataFilesPresentOnDisk will fail.
    \*   i.e. You will see that we can have file entries in MetadataFile which don't exist on disk.
    \*   This can be because of concurrency with TH. Thanks to TLA+.    
    \* Don't use E_LowLSN, E_HighLSN for MetadataFile:
    \*      Idea is not use Low/High LSN for changing disk data structures. They are
    \*      maintained parallely and used for assertion in Invariants.
    /\ LET validFiles == GetValidFiles(Append(REs, WE), MetadataFile.headLSN, WE.end)
       IN /\ MetadataFile' = [MetadataFile EXCEPT !.fileIds = Append(GetFileIds(validFiles), New_WE.id)]
    \* Todo: Split changing RE in separate action to see what concurrency can do.
    \* In-memory data structure change
    \*      Because of concurrency in TH, it is possible to get Truncation till last WE
    \*      while we are adding new WE
          /\ REs' = GetValidFiles(validFiles, E_LowLSN, E_HighLSN)
    /\ WE' = [ id      |-> New_WE.id,
               start   |-> New_WE.start,
               end     |-> New_WE.end,
               version |-> New_WE.version ]
    \* Reset other fields
    /\ New_WE' = [ New_WE EXCEPT !.exist = FALSE ]
    /\ E_HighLSN' = E_HighLSN + 1 \* Ack to customer that write succeeded
    /\ PrevState' = "New_WE_in_MDT"
    /\ E_NWEIP' = FALSE \* allow appends to WE now
    /\ UNCHANGED << E_LowLSN, MaxNum, TornWrite, E_THIP, E_TTIP >>

\* Crash: torn write : last write ignored
\* We can't have torn write in case of New_WE, as only after write is successful, 
\* we update metadata and ack to caller.
CrashWhileAppend ==
    /\ PrevState = "append"
    /\ PrevState' = "crash"
    /\ E_HighLSN' = E_HighLSN - 1 \* Simulate : we crashed before acking to customer
    /\ TornWrite' = TRUE
    \* don't change metadata file as we can't do it during crash
    \* Invariant : CleanShutdownOnlyAfterClose makes sure that we have clean bit set only after close
    \* /\ MetadataFile' = [MetadataFile EXCEPT !.cleanShutdown = FALSE]
    /\ UNCHANGED << E_LowLSN, MaxNum, REs, WE, E_THIP, E_TTIP, E_NWEIP, New_WE, MetadataFile >>

\* Normal crash that does not cause data loss
CrashNoDataLoss ==
    /\ PrevState \notin { "crash", "close" } \* we can't crash after close as we aren't running
    /\ PrevState' = "crash"
    \* don't change metadata file as we can't do it during crash
    \* Invariant : CleanShutdownOnlyAfterClose makes sure that we have clean bit as TRUE only after close
    \* /\ MetadataFile' = [MetadataFile EXCEPT !.cleanShutdown = FALSE]
    /\ UNCHANGED << E_LowLSN, MaxNum, E_HighLSN, REs, WE, TornWrite, E_THIP, E_TTIP, E_NWEIP, New_WE, MetadataFile >>

\* Close the log file.
\* Waits for all operations to finish on log and sets the clean shutdown bit to true.
Close ==
    /\ PrevState \notin { "crash", "close" }
    \* Close waits for workflows to finish: 
    \*    New_WE, truncate_head, truncate_tail
    /\ E_NWEIP = FALSE
    /\ E_TTIP = FALSE
    /\ E_THIP = FALSE
    /\ PrevState' = "close"
    /\ MetadataFile' = [MetadataFile EXCEPT !.cleanShutdown = TRUE,
                                            !.lastTailLSN = WE.end]
    /\ UNCHANGED << E_LowLSN, MaxNum, E_HighLSN, REs, WE, TornWrite, E_THIP, E_TTIP, E_NWEIP, New_WE >>


\* Action: Recovery : It happens on Open
\* After crash, we can't look at value of E_* variables to know the state of the system before close/crash.
\* After recovery, we set cleanshutdown bit in metadatafile to false, which can only be set to TRUE during close.
\* We don't do anything if clean shutdown bit is set in the metadata file - fast open case.
Recovery ==
    /\ \/ PrevState = "crash"
       \/ PrevState = "close"
    /\ IF MetadataFile.cleanShutdown
       THEN /\ REs' = REs
            /\ WE' = WE
            /\ MetadataFile' = [MetadataFile EXCEPT !.cleanShutdown = FALSE ]
       \* Otherwise we crashed.
       \* Read metadata file and check WE/REs file to rebuild the state.
       ELSE LET allFiles == GetMetadataFiles
                lowLSN == MetadataFile.headLSN
                \* last file in metadatafile is supposed to be WE
                \* Todo : add a flag in metadata file for which file is WE.
                lastWE == LET lastWEId == MetadataFile.fileIds[Len(MetadataFile.fileIds)]
                              SameId(r) == r.id = lastWEId
                          IN Head(SelectSeq(allFiles, SameId))
                \* highLSN: Thanks TLA+
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
                goodExtents == GetValidFiles(allFiles, lowLSN, highLSN)
                cleanState == Len(goodExtents) =  0
            IN IF cleanState \* if we don't have any data
               THEN /\ REs' = <<>>
                    /\ WE' = [id |-> 1, start |-> lowLSN, end |-> highLSN, 
                              version |-> MetadataFile.lastTailVersion]
                    \* Not setting clean bit to false, as it is expected to be false because we crashed.
                    /\ MetadataFile' = [MetadataFile EXCEPT !.fileIds = <<1>>]
               ELSE /\ REs' = SubSeq(goodExtents, 1, Len(goodExtents) - 1)
                    /\ WE' = [goodExtents[Len(goodExtents)] 
                                EXCEPT !.end = highLSN,
                                       !.version = MetadataFile.lastTailVersion]
                    /\ MetadataFile' = [ MetadataFile EXCEPT !.fileIds = GetFileIds(goodExtents)]
    \* Reset variables correctly so that appends can work.
    /\ PrevState' = "recovery"
    /\ E_THIP' = FALSE
    /\ E_TTIP' = FALSE
    /\ E_NWEIP' = FALSE
    \* Delete New_WE file if it exists -- crash happened before updating MetadataFile
    /\ New_WE' = [ New_WE EXCEPT !.exist = FALSE ]
    /\ TornWrite' = FALSE
    /\ UNCHANGED << E_LowLSN, MaxNum, E_HighLSN >>
        
\* TruncateHead (TH):
\* Remove old data from the log.
\* ASSUMPTIONS:
\* 1. There is only 1 TH call at a time - but because of 2 phases, there can be multiple TH in phase2.
\* 2. 1 TH and 1 append can happen concurrently.
\* 3. No TT when TH starts.
\* We broke truncate head in 2 phases to simulate a crash in between 2 stages.
\* Other states like appends can happen in between 2 phases.
\* Phase1 : Update metadata file first.
TruncateHeadP1 ==
    /\ PrevState \notin { "crash", "close" }
    \* truncate_head waits for new_WE workflow to finish.
    \* Todo: This is possibly bad as even starting the TruncateHead is waiting.
    \*       It is not very bad because New_WE workflow should finish fast and is also rare.
    /\ E_NWEIP = FALSE
    /\ E_TTIP = FALSE \* No truncate tail in progress.
    /\ E_LowLSN < E_HighLSN
    /\ PrevState' = "truncate_head_p1"
    /\ E_LowLSN' = E_LowLSN + 1
    \* WE is never removed from MetadataFile in case of TH
    \* as we need at least 1 file in logger at all time.
    /\ LET newREs == LET nonTruncatedRE(re) == re.end > E_LowLSN'
                     IN SelectSeq(REs, nonTruncatedRE)
       IN MetadataFile' = [MetadataFile EXCEPT 
                                            !.headLSN = E_LowLSN',
                                            !.lastTailLSN = E_HighLSN,
                                            !.fileIds = GetFileIds(Append(newREs, WE))]
    /\ E_THIP' = TRUE
    /\ UNCHANGED << E_HighLSN, MaxNum, REs, WE, TornWrite, E_TTIP, E_NWEIP, New_WE >>

\* Delete/Zero out RE files in 2nd phase of TruncateHead
TruncateHeadP2 ==
    /\ \/ PrevState = "truncate_head_p1"
       \/ /\ E_THIP = TRUE
          /\ PrevState # "crash" \* After crash, only recovery runs
    /\ PrevState' = "truncate_head"
    /\ REs' = LET nonTruncatedRE(re) == re.end > E_LowLSN
              IN SelectSeq(REs, nonTruncatedRE)
    /\ E_THIP' = FALSE
    /\ UNCHANGED << E_LowLSN, E_HighLSN, MaxNum, WE, MetadataFile, TornWrite, E_TTIP, E_NWEIP, New_WE >>
    
\* TruncateTailP1 :
\* Remove data from tail of the log.
\* ASSUMPTIONS:
\*   1. No TruncateTail (TT) while append is called.
\*   2. No Append/TruncateHead (TH) while TT is going on.
\* Phase1 : Update metadata file first.
\* We broke truncate tail in 2 phases to simulate a crash in between 2 stages.
\* Update metadata file first:
\* If we crash after updating metadata file, we can truncate tail of WE on recovery.
\* Other valid states like appends can't run between 2 phases.
TruncateTailP1 ==
    /\ PrevState \notin { "crash", "close" }
    \* No append, truncate head going on at this time
    /\ E_NWEIP = FALSE
    /\ E_THIP = FALSE
    /\ E_TTIP = FALSE \* Only one truncate tail allowed at a time.
    /\ E_LowLSN < E_HighLSN
    /\ MetadataFile.lastTailVersion < MaxNum - 1 \* Restrict MC to finite states.
    /\ PrevState' = "truncate_tail_p1"
    /\ E_HighLSN' = E_HighLSN - 1
    /\ E_TTIP' = TRUE
    \* In TruncateTail - update tailLsn, version, fileIds in MetadataFile
    /\ LET validExtents == IF WE.start < WE.end \* WE has data
                           THEN Append(REs, [WE EXCEPT !.end = WE.end - 1])
                           ELSE LET lastRE == REs[Len(REs)]
                                IN Append(SubSeq(REs, 1, Len(REs)-1), [ lastRE EXCEPT !.end = lastRE.end - 1])
       IN MetadataFile' = [MetadataFile EXCEPT !.lastTailLSN = E_HighLSN',
                                               !.lastTailVersion = MetadataFile.lastTailVersion + 1,
                                               !.fileIds = GetFileIds(validExtents)]
    /\ UNCHANGED << E_LowLSN, WE, REs, MaxNum, TornWrite, E_THIP, E_NWEIP, New_WE >>

\* Now, actual delete file/zero WE file's tail in Phase 2.
TruncateTailP2 ==
    /\ PrevState = "truncate_tail_p1"
    /\ PrevState' = "truncate_tail"
    /\ IF WE.start < WE.end \* WE has data
       THEN /\ WE' = [WE EXCEPT !.end = WE.end - 1]
            /\ REs' = REs
       ELSE /\ WE' = LET lastRE == REs[Len(REs)]
                     IN [ lastRE EXCEPT !.end = lastRE.end - 1]
            /\ REs' = SubSeq(REs, 1, Len(REs)-1)
    /\ E_TTIP' = FALSE
    /\ UNCHANGED << E_LowLSN, E_HighLSN, MaxNum, MetadataFile, TornWrite, E_THIP, E_NWEIP, New_WE >>

Next ==
    \/ AppendToFile
    \/ WriteExtentFullNewWE
    \/ NewWriteExtentAddToMetadataFile
    \/ CrashWhileAppend
    \/ CrashNoDataLoss
    \/ Close
    \/ Recovery
    \/ TruncateHeadP1
    \/ TruncateHeadP2
    \/ TruncateTailP1
    \/ TruncateTailP2
    \* Not modelling Data Loss. 
    \* I am not sure, if we should just fail to open if we find we lost data 
    \*   so that we build from new replica.    
    \* \/ CrashDataLost
    
\* Invariants:

\* Invariant 1: NoDataLoss
\* All read only extents have non missing LSN
\*   REs[1].start < REs[1].end == REs[2].start < REs[2].end == REs[3].start < ...
\* write extent has latest data
\*   E_HighLSN == WE.end >= WE.start == REs[last].end

\* [dangling_extent]  [lowLSN, highLSN - valid range]  [dangling_extent]
OrderedExtent(ex1, ex2, highLSN) ==
    /\ ex1.start < ex1.end
    /\ ex1.end = ex2.start
    /\ ex1.end <= highLSN

ValidReadOnlyExtents ==
    /\ \A i \in 1..Len(REs)-1 : /\ OrderedExtent(REs[i], REs[i+1], E_HighLSN)
                                /\ REs[i].end < E_HighLSN
    /\ IF Len(REs) > 0
       THEN OrderedExtent(REs[Len(REs)], WE, E_HighLSN)
       ELSE 1 = 1

ValidWriteExtent ==
    /\ WE.start <= WE.end
    /\ WE.end = E_HighLSN

MetadataExtentsCoverDataRange ==
    LET allFiles == GetMetadataFiles
        firstFile == allFiles[1]
        lastFile == allFiles[Len(allFiles)]
    IN /\ firstFile.start <= E_LowLSN
       /\ lastFile.end >= E_HighLSN

NoDataLoss ==
    \* Not valid state during crash or truncate_tail_phase1
    \/ PrevState \in { "crash", "truncate_tail_p1" }
    \/ E_TTIP = TRUE \* TruncateTail in progress
    \/ /\ ValidReadOnlyExtents
       /\ ValidWriteExtent
       /\ MetadataExtentsCoverDataRange
       /\ E_LowLSN <= E_HighLSN

\* Invariant 2: No dangling files on disk
\* No file/extent present on disk which are not required.
NotDanglingExtent(ex, lowLSN, highLSN) ==
    ~ ( \/ ex.start >= highLSN
        \/ ex.end <= lowLSN )

NoDanglingExtents ==
    \/ PrevState = "crash"
    \* TH/TT is in progress - so some files are dangling.
    \/ E_THIP = TRUE
    \/ E_TTIP = TRUE
    \/ /\ \A i \in 1..Len(REs) : NotDanglingExtent(REs[i], E_LowLSN, E_HighLSN)
       /\ \/ WE.start = WE.end \* WE is empty
          \/ E_LowLSN = E_HighLSN  \* There is no data in log
          \* If there is some data, WE should be valid
          \/ NotDanglingExtent(WE, E_LowLSN, E_HighLSN)

\* Invariant 3 : Correctness of MetadataFile:
\*   1. FileIds should be in increasing order
\*   2. HeadLSN should be same as Expected E_LowLSN
IsFileIdPresent(fileIds, id) ==
    LET SameId(fid) == fid = id
    IN Len(SelectSeq(fileIds, SameId)) = 1

AllMetadataFilesPresentOnDisk ==
    LET allFiles == Append(REs, WE)
        allFileIds == [ i \in 1..Len(allFiles) |-> allFiles[i].id ]
    IN /\ \A i \in 1..Len(MetadataFile.fileIds) : 
                IsFileIdPresent(allFileIds, MetadataFile.fileIds[i])
       /\ IF New_WE.exist
          \* if New_WE is present, it should not be in RE, WE and mentioned in MetadataFile
          \* i.e New_WE is transient file
          THEN /\ ~ IsFileIdPresent(allFileIds, New_WE.id)
               /\ ~ IsFileIdPresent(MetadataFile.fileIds, New_WE.id)
          ELSE 1 = 1

MetadataFileCorrect ==
    /\ \* No missing file - files in increasing order
       \A i \in 1..Len(MetadataFile.fileIds)-1 : 
                MetadataFile.fileIds[i] < MetadataFile.fileIds[i+1]
    /\ MetadataFile.headLSN = E_LowLSN
    /\ AllMetadataFilesPresentOnDisk \* even during crash
    /\ IF MetadataFile.cleanShutdown
       THEN MetadataFile.lastTailLSN = E_HighLSN
       \* Todo: What should still be correct in clean shutdown case ?
       ELSE 1 = 1

\* Invariant 4: Valid version number
CorrectVersionNumber ==
    IF MetadataFile.lastTailLSN < E_HighLSN \* some write finished after last TT
    THEN WE.version = MetadataFile.lastTailVersion
    \* Multiple TT can happen one after another increasing version no. Thanks TLA+
    ELSE WE.version <= MetadataFile.lastTailVersion

\* If we have clean shutdown state - except after close, we are in bad state.
CleanShutdownOnlyAfterClose ==
    ~ ( /\ PrevState # "close"
        /\ MetadataFile.cleanShutdown = TRUE
      )

\* Change below value to see different steps taken for particular test run.
LSNSteps ==
    E_HighLSN < MaxNum

\* Spec Ends

\* Todo:
\* Spec after this is WIP and not used.

\* Invariants that should fail - Signifies that we have handled these cases.
\* TruncateTail is not called on empty WE for truncating data upto REs
\* Todo: This is not failing - This case is not handled.
\* Using E_TTIP is not correct as that means that TT has already begin.
TruncateTailCalledOnEmptyWE ==
    ~ ( /\ E_TTIP = TRUE
        /\ WE.start = WE.end
      )

TruncateHeadCalledOnEmptyWE == 
    ~ ( /\ E_THIP = TRUE
        /\ WE.start = WE.end
      )

\* Crash: Not modelling case of data lost.
\* we lost all data after some LSN
\* Todo: need to model - data lost in between E_LowLSN and E_HighLSN
\*       In that case, we will Fail replica in real world 
\*       and rebuild from another source.
MaxOf2(a, b) ==
    IF a < b
    THEN b
    ELSE a

CrashDataLost ==
    /\ PrevState' = "crash"
    /\ E_HighLSN' = IF E_HighLSN > (MaxNum \div 2)
                  THEN MaxOf2(E_LowLSN, MaxNum \div 2)
                  ELSE IF E_HighLSN > 3
                  THEN MaxOf2(E_LowLSN, 3)
                  ELSE MaxOf2(E_LowLSN, 1)
    /\ MetadataFile' = [MetadataFile EXCEPT !.cleanShutdown = FALSE]
    /\ UNCHANGED << E_LowLSN, MaxNum, REs, WE, TornWrite>>
=============================================================================
\* Modification History
\* Last modified Mon Nov 16 16:32:52 PST 2020 by asnegi
\* Created Wed Oct 28 17:55:29 PDT 2020 by asnegi
