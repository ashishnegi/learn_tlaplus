----------------------------- MODULE sflogcrash -----------------------------

EXTENDS Integers
VARIABLES ReadOnlyExtents, WriteExtent, LSN

TypeOK ==
    /\ ReadOnlyExtents = {} \* How to say it is a set of Tuple of size 2
    /\ WriteExtent = \A i, j \in Nat : /\ <<i, j>>
                                       /\ i <= j
    /\ LSN \in 0..100

Init ==
    /\ ReadOnlyExtents = {}
    /\ WriteExtent = <<0, 0>>
    /\ LSN = 0
    
NewWriteExtent ==
    /\ ReadOnlyExtents' = ReadOnlyExtents \union { WriteExtent }
    /\ WriteExtent' = <<LSN + 1, LSN + 1>>
    /\ LSN' = LSN + 1

AppendToFile ==
    /\ ReadOnlyExtents' = ReadOnlyExtents
    /\ WriteExtent' = <<WriteExtent[1] + 1, LSN + 1>>
    /\ LSN' = LSN + 1
    
Next ==
    \/ AppendToFile
    \/ NewWriteExtent

\* NoDataLoss
\*   ReadOnlyExtents[1][1] <= ReadOnlyExtents[1][2] < ReadOnlyExtents[2][1] <= ReadOnlyExtents[2][2] < ReadOnlyExtents[3][1] <= ...
\*   WriteExtent[2] >= WriteExtent[1] > ReadOnlyExtents[last][2]


=============================================================================
\* Modification History
\* Last modified Wed Oct 28 20:42:46 PDT 2020 by asnegi
\* Created Wed Oct 28 17:55:29 PDT 2020 by asnegi
