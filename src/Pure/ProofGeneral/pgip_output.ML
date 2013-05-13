(*  Title:      Pure/ProofGeneral/pgip_output.ML
    Author:     David Aspinall

PGIP abstraction: output commands.
*)

signature PGIPOUTPUT =
sig
    datatype pgipoutput =
      Hasprefs            of { prefcategory: string option, 
                               prefs: PgipTypes.preference list }
    | Pgip                of { tag: string option,
                               class: string,
                               seq: int, id: string,
                               destid: string option,
                               refid: string option,
                               refseq: int option,
                               content: XML.tree list }

    val output : pgipoutput -> XML.tree
end

structure PgipOutput : PGIPOUTPUT =
struct

datatype pgipoutput =
         Hasprefs            of { prefcategory: string option, 
                                  prefs: PgipTypes.preference list }
  |      Pgip                of { tag: string option,
                                  class: string,
                                  seq: int, id: string,
                                  destid: string option,
                                  refid: string option,
                                  refseq: int option,
                                  content: XML.tree list }

fun output (Hasprefs vs) =
    let 
        val prefcategory = #prefcategory vs
        val prefs = #prefs vs
    in 
        XML.Elem (("hasprefs", PgipTypes.opt_attr "prefcategory" prefcategory),
          map PgipTypes.haspref prefs)
    end
  | output (Pgip vs) =
    let
        val tag = #tag vs
        val class = #class vs
        val seq = #seq vs
        val id = #id vs
        val destid = #destid vs
        val refid = #refid vs
        val refseq = #refseq vs
        val content = #content vs
    in
        XML.Elem(("pgip",
                 PgipTypes.opt_attr "tag" tag @
                 PgipTypes.attr "id" id @
                 PgipTypes.opt_attr "destid" destid @
                 PgipTypes.attr "class" class @
                 PgipTypes.opt_attr "refid" refid @
                 PgipTypes.opt_attr_map string_of_int "refseq" refseq @
                 PgipTypes.attr "seq" (string_of_int seq)),
                 content)
    end

end

