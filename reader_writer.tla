--------------------------- MODULE reader_writer ---------------------------

EXTENDS FiniteSets, Integers

CONSTANTS Readers, Writers
VARIABLES BusyActors
vars == BusyActors

TypeOk ==
    /\ BusyActors \subseteq (Readers \union Writers)
    
Init ==
    BusyActors = {}

AcquireReadLock(r) ==
    /\ r \in Readers
    /\ r \notin BusyActors \* Not already taken lock
    /\ Cardinality(BusyActors \intersect Writers) = 0 \* No Writer
    /\ BusyActors' = BusyActors \union {r}

AcquireWriteLock(w) ==
    /\ w \in Writers
    /\ w \notin BusyActors
    /\ BusyActors = {}
    /\ BusyActors' = BusyActors \union {w}

ReleaseLock(rw) ==
    /\ rw \in Writers \/ rw \in Readers
    /\ rw \in BusyActors
    /\ BusyActors' = BusyActors \ {rw}

Next ==
    \/ \E r \in Readers: AcquireReadLock(r)
    \/ \E w \in Writers: AcquireWriteLock(w)
    \/ \E rw \in BusyActors: ReleaseLock(rw)

Only1WriterLockInv ==
    LET busyWriters == BusyActors \intersect Writers
    IN Cardinality(busyWriters) < 2

NoReaderWhileWritingInv ==
    LET busyWriters == BusyActors \intersect Writers
        busyReaders == BusyActors \intersect Readers
    IN IF Cardinality(busyWriters) > 0
       THEN Cardinality(busyReaders) = 0
       ELSE TRUE

NoWriterNonProperty ==
    BusyActors \intersect Writers = {}
NoReaderNonProperty ==
    BusyActors \intersect Readers = {}
AllReadersNonProperty ==
    BusyActors /= Readers

FairRead ==
    \A r \in Readers: WF_vars(AcquireReadLock(r))
FairWrite ==
    \A w \in Writers: WF_vars(AcquireWriteLock(w))
FairRelease ==
    \A rw \in BusyActors: WF_vars(ReleaseLock(rw))

Fairness == FairRead /\ FairWrite /\ FairRelease

Spec == Init /\ [][Next]_vars /\ Fairness

ReaderCanRead ==
    \A r \in Readers: []<>(r \in BusyActors)
WriterCanWrite ==
    \A w \in Writers: []<>(w \in BusyActors)

Liveness == ReaderCanRead /\ WriterCanWrite
=============================================================================
\* Modification History
\* Last modified Sat Feb 27 12:27:23 PST 2021 by asnegi
\* Created Sat Feb 27 11:14:38 PST 2021 by asnegi
