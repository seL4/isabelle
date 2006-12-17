(*  Title:      Pure/ProofGeneral/pgip_output.ML
    ID:         $Id$
    Author:     David Aspinall

PGIP abstraction: output commands
*)

signature PGIPOUTPUT =
sig
    (* These are the PGIP messages which the prover emits. *) 
    datatype pgipoutput = 
      Cleardisplay        of { area: PgipTypes.displayarea }
    | Normalresponse      of { area: PgipTypes.displayarea, 
                               urgent: bool, 
                               messagecategory: PgipTypes.messagecategory, 
                               content: XML.content }
    | Errorresponse       of { fatality: PgipTypes.fatality, 
                               area: PgipTypes.displayarea option, 
                               location: PgipTypes.location option, 
                               content: XML.content }
    | Informfileloaded    of { url: PgipTypes.pgipurl }
    | Informfileretracted of { url: PgipTypes.pgipurl }
    | Proofstate          of { pgml: XML.content }
    | Metainforesponse    of { attrs: XML.attributes, 
                               content: XML.content }
    | Lexicalstructure    of { content: XML.content }
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
    | Idvalue             of { name: PgipTypes.objname, 
			       objtype: PgipTypes.objtype, 
			       text: XML.content }
    | Informguise         of { file : PgipTypes.pgipurl option,  
                               theory: PgipTypes.objname option, 
                               theorem: PgipTypes.objname option, 
                               proofpos: int option }
    | Parseresult         of { attrs: XML.attributes, doc:PgipMarkup.pgipdocument, 
			       errs: XML.content } (* errs to become PGML *)
    | Usespgip            of { version: string, 
                               pgipelems: (string * bool * string list) list }
    | Usespgml            of { version: string }
    | Pgip                of { tag: string option, 
                               class: string, 
                               seq: int, id: string, 
                               destid: string option,
                               refid: string option,
                               refseq: int option,
                               content: XML.content }
    | Ready               of { }

    val output : pgipoutput -> XML.tree                                  
end

structure PgipOutput : PGIPOUTPUT =
struct
open PgipTypes

datatype pgipoutput = 
         Cleardisplay        of { area: displayarea }
       | Normalresponse      of { area: displayarea, urgent: bool, 
                                  messagecategory: messagecategory, content: XML.content }
       | Errorresponse       of { area: displayarea option, fatality: fatality, 
                                  location: location option, content: XML.content }
       | Informfileloaded    of { url: Path.T }
       | Informfileretracted of { url: Path.T }
       | Proofstate          of { pgml: XML.content }
       | Metainforesponse    of { attrs: XML.attributes, content: XML.content }
       | Lexicalstructure    of { content: XML.content }
       | Proverinfo          of { name: string, version: string, instance: string,
                                  descr: string, url: Url.T, filenameextns: string }
       | Setids              of { idtables: PgipTypes.idtable list  }
       | Delids              of { idtables: PgipTypes.idtable list }
       | Addids              of { idtables: PgipTypes.idtable list }
       | Hasprefs            of { prefcategory: string option, prefs: preference list }
       | Prefval             of { name: string, value: string }
       | Idvalue             of { name: PgipTypes.objname, 
				  objtype: PgipTypes.objtype, 
				  text: XML.content }
       | Informguise         of { file : PgipTypes.pgipurl option,  
				  theory: PgipTypes.objname option, 
				  theorem: PgipTypes.objname option, 
				  proofpos: int option }
       | Parseresult         of { attrs: XML.attributes, doc: PgipMarkup.pgipdocument,
				  errs: XML.content } (* errs to become PGML *)
       | Usespgip            of { version: string, 
                                  pgipelems: (string * bool * string list) list }
       | Usespgml            of { version: string }
       | Pgip                of { tag: string option, 
                                  class: string, 
                                  seq: int, id: string, 
                                  destid: string option,
                                  refid: string option,
                                  refseq: int option,
                                  content: XML.content }
       | Ready               of { }


(* Construct output XML messages *)
        
fun cleardisplay vs = 
    let
        val area = #area vs
    in
        XML.Elem ("cleardisplay", (attrs_of_displayarea area), [])
    end

fun normalresponse vs =
    let 
        val area = #area vs
        val urgent = #urgent vs
        val messagecategory = #messagecategory vs
        val content = #content vs
    in
        XML.Elem ("normalresponse", 
                 (attrs_of_displayarea area) @
                 (if urgent then attr "urgent" "true" else []) @
                 (attrs_of_messagecategory messagecategory),
                 content)
    end
                                       
fun errorresponse vs =
    let 
        val area = #area vs
        val fatality = #fatality vs
        val location = #location vs
        val content = #content vs
    in
        XML.Elem ("errorresponse",
                 (the_default [] (Option.map attrs_of_displayarea area)) @
                 (attrs_of_fatality fatality) @
                 (the_default [] (Option.map attrs_of_location location)),
                 content)
    end
                                       

fun informfile lr vs =
    let 
        val url = #url vs
    in
        XML.Elem ("informfile" ^ lr, attrs_of_pgipurl url, [])
    end

val informfileloaded = informfile "loaded"
val informfileretracted = informfile "retracted"

fun proofstate vs =
    let
        val pgml = #pgml vs
    in
        XML.Elem("proofstate", [], pgml)
    end

fun metainforesponse vs =
    let 
        val attrs = #attrs vs
        val content = #content vs
    in
        XML.Elem ("metainforesponse", attrs, content)
    end

fun lexicalstructure vs =
    let
        val content = #content vs
    in
        XML.Elem ("lexicalstructure", [], content)
    end

fun proverinfo vs =
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

fun setids vs =
    let
        val idtables = #idtables vs
    in
        XML.Elem ("setids",[],map idtable_to_xml idtables)
    end

fun addids vs =
    let
        val idtables = #idtables vs
    in
        XML.Elem ("addids",[],map idtable_to_xml idtables)
    end

fun delids vs =
    let
        val idtables = #idtables vs
    in
        XML.Elem ("delids",[],map idtable_to_xml idtables)
    end


fun acceptedpgipelems vs = 
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


fun hasprefs vs =
  let 
      val prefcategory = #prefcategory vs
      val prefs = #prefs vs
  in 
      XML.Elem("hasprefs",opt_attr "prefcategory" prefcategory, map haspref prefs)
  end

fun prefval vs =
    let 
        val name = #name vs
        val value = #value vs
    in
        XML.Elem("prefval", attr "name" name, [XML.Text value])
    end 

fun idvalue vs =
    let 
        val name = #name vs
	val objtype_attrs = attrs_of_objtype (#objtype vs)
        val text = #text vs
    in
        XML.Elem("idvalue", attr "name" name @ objtype_attrs, text)
    end 


fun informguise vs =
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

fun parseresult vs =
    let
        val attrs = #attrs vs
        val doc = #doc vs
        val errs = #errs vs
	val xmldoc = PgipMarkup.output_doc doc
    in 
        XML.Elem("parseresult", attrs, errs@xmldoc)
    end

fun usespgip vs =
    let
        val version = #version vs
        val acceptedelems = acceptedpgipelems vs
    in 
        XML.Elem("usespgip", attr "version" version, [acceptedelems])
    end

fun usespgml vs =
    let
        val version = #version vs
    in 
        XML.Elem("usespgml", attr "version" version, [])
    end

fun pgip vs =
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

fun ready vs = XML.Elem("ready",[],[])


fun output pgipoutput = case pgipoutput of
   Cleardisplay vs         => cleardisplay vs
 | Normalresponse vs       => normalresponse vs
 | Errorresponse vs        => errorresponse vs
 | Informfileloaded vs     => informfileloaded vs
 | Informfileretracted vs  => informfileretracted vs
 | Proofstate vs           => proofstate vs
 | Metainforesponse vs     => metainforesponse vs
 | Lexicalstructure vs     => lexicalstructure vs
 | Proverinfo vs           => proverinfo vs
 | Setids vs               => setids vs
 | Addids vs               => addids vs
 | Delids vs               => delids vs
 | Hasprefs vs             => hasprefs vs
 | Prefval vs              => prefval vs
 | Idvalue vs              => idvalue vs
 | Informguise vs          => informguise vs
 | Parseresult vs          => parseresult vs
 | Usespgip vs             => usespgip vs
 | Usespgml vs             => usespgml vs
 | Pgip vs                 => pgip vs
 | Ready vs                => ready vs

end

