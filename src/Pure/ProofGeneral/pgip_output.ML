(*  Title:      Pure/ProofGeneral/pgip_output.ML
    Author:     David Aspinall

PGIP abstraction: output commands.
*)

signature PGIPOUTPUT =
sig
    (* These are the PGIP messages which the prover emits. *) 
    datatype pgipoutput = 
      Normalresponse      of { content: XML.tree list }
    | Errorresponse       of { fatality: PgipTypes.fatality, 
                               location: PgipTypes.location option, 
                               content: XML.tree list }
    | Informfileloaded    of { url: PgipTypes.pgipurl, completed: bool }
    | Informfileoutdated  of { url: PgipTypes.pgipurl, completed: bool }
    | Informfileretracted of { url: PgipTypes.pgipurl, completed: bool }
    | Metainforesponse    of { attrs: XML.attributes, 
                               content: XML.tree list }
    | Lexicalstructure    of { content: XML.tree list }
    | Proverinfo          of { name: string, 
                               version: string, 
                               instance: string,
                               descr: string, 
                               url: Url.T, 
                               filenameextns: string }
    | Setids              of { idtables: PgipTypes.idtable list  }
    | Delids              of { idtables: PgipTypes.idtable list }
    | Addids              of { idtables: PgipTypes.idtable list }
    | Hasprefs            of { prefcategory: string option, 
                               prefs: PgipTypes.preference list }
    | Prefval             of { name: string, value: string }
    | Setrefs             of { url: PgipTypes.pgipurl option,
                               thyname: PgipTypes.objname option,
                               objtype: PgipTypes.objtype option,
                               name: PgipTypes.objname option,
                               idtables: PgipTypes.idtable list,
                               fileurls : PgipTypes.pgipurl list }
    | Idvalue             of { thyname: PgipTypes.objname option,
                               objtype: PgipTypes.objtype, 
                               name: PgipTypes.objname, 
                               text: XML.tree list }
    | Informguise         of { file : PgipTypes.pgipurl option,  
                               theory: PgipTypes.objname option, 
                               theorem: PgipTypes.objname option, 
                               proofpos: int option }
    | Parseresult         of { attrs: XML.attributes, doc:PgipMarkup.pgipdocument, 
                               errs: XML.tree list } (* errs to become PGML *)
    | Usespgip            of { version: string, 
                               pgipelems: (string * bool * string list) list }
    | Usespgml            of { version: string }
    | Pgip                of { tag: string option, 
                               class: string, 
                               seq: int, id: string, 
                               destid: string option,
                               refid: string option,
                               refseq: int option,
                               content: XML.tree list }
    | Ready               of { }

    val output : pgipoutput -> XML.tree                                  
end

structure PgipOutput : PGIPOUTPUT =
struct
open PgipTypes

datatype pgipoutput = 
         Normalresponse      of { content: XML.tree list }
       | Errorresponse       of { fatality: fatality, 
                                  location: location option, 
                                  content: XML.tree list }
       | Informfileloaded    of { url: Path.T, completed: bool }
       | Informfileoutdated  of { url: Path.T, completed: bool }
       | Informfileretracted of { url: Path.T, completed: bool }
       | Metainforesponse    of { attrs: XML.attributes, content: XML.tree list }
       | Lexicalstructure    of { content: XML.tree list }
       | Proverinfo          of { name: string, version: string, instance: string,
                                  descr: string, url: Url.T, filenameextns: string }
       | Setids              of { idtables: PgipTypes.idtable list  }
       | Delids              of { idtables: PgipTypes.idtable list }
       | Addids              of { idtables: PgipTypes.idtable list }
       | Hasprefs            of { prefcategory: string option, prefs: preference list }
       | Prefval             of { name: string, value: string }
       | Idvalue             of { thyname: PgipTypes.objname option,
                                  objtype: PgipTypes.objtype, 
                                  name: PgipTypes.objname, 
                                  text: XML.tree list }
       | Setrefs             of { url: PgipTypes.pgipurl option,
                                  thyname: PgipTypes.objname option,
                                  objtype: PgipTypes.objtype option,
                                  name: PgipTypes.objname option,
                                  idtables: PgipTypes.idtable list,
                                  fileurls : PgipTypes.pgipurl list }
       | Informguise         of { file : PgipTypes.pgipurl option,  
                                  theory: PgipTypes.objname option, 
                                  theorem: PgipTypes.objname option, 
                                  proofpos: int option }
       | Parseresult         of { attrs: XML.attributes, doc: PgipMarkup.pgipdocument,
                                  errs: XML.tree list } (* errs to become PGML *)
       | Usespgip            of { version: string, 
                                  pgipelems: (string * bool * string list) list }
       | Usespgml            of { version: string }
       | Pgip                of { tag: string option, 
                                  class: string, 
                                  seq: int, id: string, 
                                  destid: string option,
                                  refid: string option,
                                  refseq: int option,
                                  content: XML.tree list }
       | Ready               of { }


(* Construct output XML messages *)

fun normalresponse (Normalresponse vs) =
    let 
        val content = #content vs
    in
        XML.Elem ("normalresponse", 
                  [],
                  content)
    end

fun errorresponse (Errorresponse vs) =
    let 
        val fatality = #fatality vs
        val location = #location vs
        val content = #content vs
    in
        XML.Elem ("errorresponse",
                 attrs_of_fatality fatality @
                 these (Option.map attrs_of_location location),
                 content)
    end

fun informfileloaded (Informfileloaded vs) =
    let 
        val url = #url vs
        val completed = #completed vs
    in
        XML.Elem ("informfileloaded", 
                  attrs_of_pgipurl url @ 
                  (attr "completed" (PgipTypes.bool_to_pgstring completed)),
                  [])
    end

fun informfileoutdated (Informfileoutdated vs) =
    let 
        val url = #url vs
        val completed = #completed vs
    in
        XML.Elem ("informfileoutdated", 
                  attrs_of_pgipurl url @ 
                  (attr "completed" (PgipTypes.bool_to_pgstring completed)),
                  [])
    end

fun informfileretracted (Informfileretracted vs) =
    let 
        val url = #url vs
        val completed = #completed vs
    in
        XML.Elem ("informfileretracted", 
                  attrs_of_pgipurl url @ 
                  (attr "completed" (PgipTypes.bool_to_pgstring completed)),
                  [])
    end

fun metainforesponse (Metainforesponse vs) =
    let 
        val attrs = #attrs vs
        val content = #content vs
    in
        XML.Elem ("metainforesponse", attrs, content)
    end

fun lexicalstructure (Lexicalstructure vs) =
    let
        val content = #content vs
    in
        XML.Elem ("lexicalstructure", [], content)
    end

fun proverinfo (Proverinfo vs) =
    let
        val name = #name vs
        val version = #version vs
        val instance = #instance vs
        val descr = #descr vs
        val url = #url vs
        val filenameextns = #filenameextns vs
    in 
        XML.Elem ("proverinfo",
                 [("name", name),
                  ("version", version),
                  ("instance", instance), 
                  ("descr", descr),
                  ("url", Url.implode url),
                  ("filenameextns", filenameextns)],
                 [])
    end

fun setids (Setids vs) =
    let
        val idtables = #idtables vs
    in
        XML.Elem ("setids",[],map idtable_to_xml idtables)
    end

fun setrefs (Setrefs vs) =
    let
        val url = #url vs
        val thyname = #thyname vs
        val objtype = #objtype vs
        val name = #name vs
        val idtables = #idtables vs
        val fileurls = #fileurls vs
        fun fileurl_to_xml url = XML.Elem ("fileurl", attrs_of_pgipurl url, [])
    in
        XML.Elem ("setrefs",
                  (the_default [] (Option.map attrs_of_pgipurl url)) @ 
                  (the_default [] (Option.map attrs_of_objtype objtype)) @
                  (opt_attr "thyname" thyname) @
                  (opt_attr "name" name),
                  (map idtable_to_xml idtables) @ 
                  (map fileurl_to_xml fileurls))
    end

fun addids (Addids vs) =
    let
        val idtables = #idtables vs
    in
        XML.Elem ("addids",[],map idtable_to_xml idtables)
    end

fun delids (Delids vs) =
    let
        val idtables = #idtables vs
    in
        XML.Elem ("delids",[],map idtable_to_xml idtables)
    end

fun hasprefs (Hasprefs vs) =
  let 
      val prefcategory = #prefcategory vs
      val prefs = #prefs vs
  in 
      XML.Elem("hasprefs",opt_attr "prefcategory" prefcategory, map haspref prefs)
  end

fun prefval (Prefval vs) =
    let 
        val name = #name vs
        val value = #value vs
    in
        XML.Elem("prefval", attr "name" name, [XML.Text value])
    end 

fun idvalue (Idvalue vs) =
    let 
        val objtype_attrs = attrs_of_objtype (#objtype vs)
        val thyname = #thyname vs
        val name = #name vs
        val text = #text vs
    in
        XML.Elem("idvalue", 
                 objtype_attrs @
                 (opt_attr "thyname" thyname) @
                 (attr "name" name),
                 text)
    end

fun informguise (Informguise vs) =
  let
      val file = #file vs
      val theory = #theory vs
      val theorem = #theorem vs
      val proofpos = #proofpos vs

      fun elto nm attrfn xo = case xo of NONE=>[] | SOME x=>[XML.Elem(nm,attrfn x,[])]

      val guisefile = elto "guisefile" attrs_of_pgipurl file
      val guisetheory = elto "guisetheory" (single o (pair "thyname")) theory
      val guiseproof = elto "guiseproof" 
                            (fn thm=>(attr "thmname" thm) @
                                     (opt_attr "proofpos" (Option.map Int.toString proofpos))) theorem
  in 
      XML.Elem("informguise", [], guisefile @ guisetheory @ guiseproof)
  end

fun parseresult (Parseresult vs) =
    let
        val attrs = #attrs vs
        val doc = #doc vs
        val errs = #errs vs
        val xmldoc = PgipMarkup.output_doc doc
    in 
        XML.Elem("parseresult", attrs, errs @ xmldoc)
    end

fun acceptedpgipelems (Usespgip vs) = 
    let
        val pgipelems = #pgipelems vs
        fun async_attrs b = if b then attr "async" "true" else []
        fun attrs_attrs attrs = if attrs=[] then [] else attr "attributes" (space_implode "," attrs)
        fun singlepgipelem (e,async,attrs) = 
            XML.Elem("pgipelem", ((async_attrs async) @ (attrs_attrs attrs)),[XML.Text e])
                                                      
    in
        XML.Elem ("acceptedpgipelems", [],
                 map singlepgipelem pgipelems)
    end

fun usespgip (Usespgip vs) =
    let
        val version = #version vs
        val acceptedelems = acceptedpgipelems (Usespgip vs)
    in 
        XML.Elem("usespgip", attr "version" version, [acceptedelems])
    end

fun usespgml (Usespgml vs) =
    let
        val version = #version vs
    in 
        XML.Elem("usespgml", attr "version" version, [])
    end

fun pgip (Pgip vs) =
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
        XML.Elem("pgip",
                 opt_attr "tag" tag @
                 attr "id" id @
                 opt_attr "destid" destid @
                 attr "class" class @
                 opt_attr "refid" refid @
                 opt_attr_map string_of_int "refseq" refseq @
                 attr "seq" (string_of_int seq),
                 content)
    end

fun ready (Ready _) = XML.Elem("ready",[],[])


fun output pgipoutput = case pgipoutput of
    Normalresponse _        => normalresponse pgipoutput
  | Errorresponse _         => errorresponse pgipoutput
  | Informfileloaded _      => informfileloaded pgipoutput
  | Informfileoutdated _    => informfileoutdated pgipoutput
  | Informfileretracted _   => informfileretracted pgipoutput
  | Metainforesponse _      => metainforesponse pgipoutput
  | Lexicalstructure _      => lexicalstructure pgipoutput
  | Proverinfo _            => proverinfo pgipoutput
  | Setids _                => setids pgipoutput
  | Setrefs _               => setrefs pgipoutput
  | Addids _                => addids pgipoutput
  | Delids _                => delids pgipoutput
  | Hasprefs _              => hasprefs pgipoutput
  | Prefval _               => prefval pgipoutput
  | Idvalue _               => idvalue pgipoutput
  | Informguise _           => informguise pgipoutput
  | Parseresult _           => parseresult pgipoutput
  | Usespgip _              => usespgip pgipoutput
  | Usespgml _              => usespgml pgipoutput
  | Pgip _                  => pgip pgipoutput
  | Ready _                 => ready pgipoutput

end

