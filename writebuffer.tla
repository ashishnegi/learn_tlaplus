---------------------------- MODULE writebuffer ----------------------------

EXTENDS Integers

VARIABLES Buffer, File

TypeOK ==
    /\ Buffer \in [a : 1]
    

=============================================================================
\* Modification History
\* Last modified Wed Dec 30 14:30:10 PST 2020 by asnegi
\* Created Wed Dec 30 14:26:00 PST 2020 by asnegi
