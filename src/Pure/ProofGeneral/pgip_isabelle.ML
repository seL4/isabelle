(*  Title:      Pure/ProofGeneral/pgip_isabelle.ML
    ID:         $Id$
    Author:     David Aspinall

Prover-side PGIP abstraction: Isabelle configuration.
*)

signature PGIP_ISABELLE =
sig
    val isabelle_pgml_version_supported : string
    val isabelle_pgip_version_supported : string
    val accepted_inputs : (string * bool * (string list)) list 
end

structure PgipIsabelle : PGIP_ISABELLE =
struct

val isabelle_pgml_version_supported = "1.0";
val isabelle_pgip_version_supported = "2.0"

(** Accepted commands **)

local

    (* These element names are a subset of those in pgip_input.ML.
       They must be handled in proof_general_pgip.ML/process_pgip_element. *)
						    
    val accepted_names =
    (* not implemented: "askconfig", "forget", "restoregoal" *)
    ["askpgip","askpgml","askprefs","getpref","setpref",
     "proverinit","proverexit","startquiet","stopquiet",
     "pgmlsymbolson", "pgmlsymbolsoff",
     "dostep", "undostep", "redostep", "abortgoal", 
     "askids", "showid", "askguise",
     "parsescript",
     "showproofstate", "showctxt", "searchtheorems", "setlinewidth", "viewdoc",
     "doitem", "undoitem", "redoitem", "abortheory",
     "retracttheory", "loadfile", "openfile", "closefile",
     "abortfile", "retractfile", "changecwd", "systemcmd"];

    fun element_async p = 
	false (* single threaded only *)

    fun supported_optional_attrs p = (case p of
					  "undostep" => ["times"]
					(* TODO: we could probably extend these too:
					| "redostep" => ["times"]
					| "undoitem" => ["times"]
					| "redoitem" => ["times"] *)
				        | _ => [])
in
val accepted_inputs = 
    (map (fn p=> (p, element_async p, supported_optional_attrs p))
         accepted_names);
end

end

