(*  Title:      Pure/ProofGeneral/pgip.ML
    ID:         $Id$
    Author:     David Aspinall

Prover-side PGIP abstraction.  
Not too closely tied to Isabelle, to help with reuse/porting.
*)

signature PGIP =
sig
    include PGIPTYPES
    include PGIPMARKUP
    include PGIPINPUT
    include PGIPOUTPUT
end

structure Pgip : PGIP = 
struct
   open PgipTypes
   open PgipMarkup
   open PgipInput
   open PgipOutput
end
