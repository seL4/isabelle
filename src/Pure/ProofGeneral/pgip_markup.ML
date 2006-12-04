(*  Title:      Pure/ProofGeneral/pgip_markup.ML
    ID:         $Id$
    Author:     David Aspinall

PGIP abstraction: document markup for proof scripts (in progress).
*)

signature PGIPMARKUP =
sig
  val markup_elements : string list
end

structure PgipMarkup : PGIPMARKUP =
struct
   (* Names of all PGIP document markup elements *)
   val markup_elements =
       [
	"opengoal",
	"proofstep",
	"closegoal",
	"comment",
	"doccomment",
	"whitespace",
	"litcomment",
	"spuriouscmd",
	"badcmd",
	"opentheory",
	"theoryitem",
	"closetheory",
	"metainfo"     (* non-document text *)
	]

end
