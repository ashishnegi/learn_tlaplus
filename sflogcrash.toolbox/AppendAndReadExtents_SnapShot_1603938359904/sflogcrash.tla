----------------------------- MODULE sflogcrash -----------------------------

EXTENDS Integers
VARIABLES ReadExtents, WriteExtent, LSN

\*TypeOK ==
\*    /\ ReadExtents
\*    /\ LSN \in 0..100

Init ==
    /\ ReadExtents = { <<0,0>> }
    /\ WriteExtent = <<0, 0>>
    /\ LSN = 0
    
WriteExtentToReadExtent ==
    /\ ReadExtents' = ReadExtents \union WriteExtent
    /\ WriteExtent' = <<LSN + 1, LSN + 1>>
    /\ LSN' = LSN + 1

Append ==
    /\ ReadExtents' = ReadExtents
    /\ WriteExtent' = <<WriteExtent[1], LSN + 1>>
    /\ LSN' = LSN + 1
    
Next ==
    \/ Append
    \/ WriteExtentToReadExtent

=============================================================================
\* Modification History
\* Last modified Wed Oct 28 19:25:53 PDT 2020 by asnegi
\* Created Wed Oct 28 17:55:29 PDT 2020 by asnegi
