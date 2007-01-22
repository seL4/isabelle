(*  Title:      Pure/ProofGeneral/pgip_isabelle.ML
    ID:         $Id$
    Author:     David Aspinall

Prover-side PGIP abstraction: Isabelle configuration and mapping to Isabelle types.
*)

signature PGIP_ISABELLE =
sig
    val isabelle_pgml_version_supported : string
    val isabelle_pgip_version_supported : string
    val accepted_inputs : (string * bool * (string list)) list 

    val location_of_position : Position.T -> PgipTypes.location
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


(* Now we have to parse strings constructed elsewhere in Isabelle, which is silly!
   This is another case where Isabelle should use structured types
   from the ground up to help its interfaces, instead of just plain
   strings.
*)
fun unquote s = case explode s of 
		    "\""::xs => (case (rev xs) of
				    "\""::_ => SOME (String.substring(s,1,(String.size s) - 2))
			         | _ => NONE)
		  | _ => NONE

fun location_of_position pos = 
    let val line = Position.line_of pos
	val (url,descr) = 
	    (case Position.name_of pos of
		 NONE => (NONE,NONE)
	       | SOME possiblyfile => 
		 (case unquote possiblyfile of
		      SOME fname => let val path = (Path.explode fname) in
					case ThyLoad.check_file NONE path of
					    SOME _ => (SOME (PgipTypes.pgipurl_of_path path), NONE)
					  | NONE => (NONE,SOME fname)
				    end
		    | _ => (NONE,SOME possiblyfile)))
    in 
	{ descr=descr, url=url, line=line, column=NONE, char=NONE, length=NONE }
    end 
	
end

