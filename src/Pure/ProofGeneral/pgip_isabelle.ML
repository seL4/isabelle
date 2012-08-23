(*  Title:      Pure/ProofGeneral/pgip_isabelle.ML
    Author:     David Aspinall

Prover-side PGIP abstraction: Isabelle configuration and mapping to Isabelle types.
*)

signature PGIP_ISABELLE =
sig
    val isabelle_pgml_version_supported : string
    val isabelle_pgip_version_supported : string
    val systemid : string
    val accepted_inputs : (string * bool * (string list)) list

    val location_of_position : Position.T -> PgipTypes.location

    (* Additional types of objects in Isar scripts *)

    val ObjTheoryBody : PgipTypes.objtype
    val ObjTheoryDecl : PgipTypes.objtype
    val ObjTheoryBodySubsection : PgipTypes.objtype
    val ObjProofBody : PgipTypes.objtype
    val ObjFormalComment : PgipTypes.objtype
    val ObjClass : PgipTypes.objtype
    val ObjTheoremSet : PgipTypes.objtype
    val ObjOracle : PgipTypes.objtype
    val ObjLocale : PgipTypes.objtype

end

structure PgipIsabelle : PGIP_ISABELLE =
struct

val isabelle_pgml_version_supported = "2.0";
val isabelle_pgip_version_supported = "2.0"
val systemid = "Isabelle"


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


fun location_of_position pos =
    let val line = Position.line_of pos
        val (url,descr) =
            (case Position.file_of pos of
               NONE => (NONE, NONE)
             | SOME fname =>
               let val path = Path.explode fname in
                 if File.exists path
                 then (SOME (PgipTypes.pgipurl_of_path path), NONE)
                 else (NONE, SOME fname)
               end);
    in
        { descr=descr, url=url, line=line, column=NONE, char=NONE, length=NONE }
    end


val [ObjTheoryBody,
     ObjTheoryDecl,
     ObjTheoryBodySubsection,
     ObjProofBody,
     ObjFormalComment,
     ObjClass,
     ObjTheoremSet,
     ObjOracle,
     ObjLocale] =
    map PgipTypes.ObjOther
        ["theory body",
         "theory declaration",
         "theory subsection",
         "proof body",
         "formal comment",
         "class",
         "theorem set declaration",
         "oracle",
         "locale"];

end
