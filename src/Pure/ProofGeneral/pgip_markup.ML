(*  Title:      Pure/ProofGeneral/pgip_markup.ML
    ID:         $Id$
    Author:     David Aspinall

PGIP abstraction: document markup for proof scripts (in progress).
*)

signature PGIPMARKUP =
sig
  (* Generic markup on sequential, non-overlapping pieces of proof text *)
  datatype pgipdoc = 
    Openblock     of { metavarid: string option, name: string option, objtype: string option }
  | Closeblock    of { }
  | Opentheory    of { thyname: string, parentnames: string list , text: string}
  | Theoryitem    of { name: string option, objtype: string option, text: string }
  | Closetheory   of { text: string }
  | Opengoal	  of { thmname: string option, text: string }
  | Proofstep     of { text: string }
  | Closegoal     of { text: string } 
  | Giveupgoal    of { text: string }
  | Postponegoal  of { text: string }
  | Comment       of { text: string }
  | Doccomment    of { text: string }
  | Whitespace    of { text: string }
  | Spuriouscmd   of { text: string }
  | Badcmd        of { text: string }
  | Unparseable	  of { text: string } 
  | Metainfo 	  of { name: string option, text: string }
  (* Last three for PGIP literate markup only: *)
  | Litcomment	  of { format: string option, content: XML.content }
  | Showcode	  of { show: bool }				 
  | Setformat	  of { format: string }

  type pgipdocument = pgipdoc list
  type pgip_parser  = string -> pgipdocument       (* system must provide a parser P *)
  val unparse_doc : pgipdocument -> string list	   (* s.t. unparse (P x) = x         *)
  val output_doc : pgipdocument -> XML.content
  val doc_markup_elements : string list	           (* used in pgip_input *)
  val doc_markup_elements_ignored : string list    (* used in pgip_input *)
end


structure PgipMarkup : PGIPMARKUP =
struct
   open PgipTypes

(* PGIP 3 idea: replace opentheory, opengoal, etc. by just openblock with corresponding objtype? *)
  datatype pgipdoc = 
    Openblock     of { metavarid: string option, name: string option, objtype: string option }
  | Closeblock    of { }
  | Opentheory    of { thyname: string, parentnames: string list, text: string}
  | Theoryitem    of { name: string option, objtype: string option, text: string }
  | Closetheory   of { text: string }
  | Opengoal	  of { thmname: string option, text: string }
  | Proofstep     of { text: string }
  | Closegoal     of { text: string } 
  | Giveupgoal    of { text: string }
  | Postponegoal  of { text: string }
  | Comment       of { text: string }
  | Doccomment    of { text: string }
  | Whitespace    of { text: string }
  | Spuriouscmd   of { text: string }
  | Badcmd        of { text: string }
  | Unparseable	  of { text: string }
  | Metainfo 	  of { name: string option, text: string }
  | Litcomment	  of { format: string option, content: XML.content }
  | Showcode	  of { show: bool }				 
  | Setformat	  of { format: string }

  type pgipdocument = pgipdoc list
  type pgip_parser  = string -> pgipdocument

   fun xml_of docelt = 
       case docelt of

	   Openblock vs  => 
	   XML.Elem("openblock", opt_attr "metavarid" (#metavarid vs), [])
	   
	 | Closeblock vs => 
	   XML.Elem("closeblock", [], [])
	   
	 | Opentheory vs  => 
	   XML.Elem("opentheory", 
		    attr "thyname" (#thyname vs) @
		    opt_attr "parentnames"
			     (case (#parentnames vs) 
			       of [] => NONE
				| ps => SOME (space_implode ";" ps)),
		    [XML.Text (#text vs)])

	 | Theoryitem vs => 
	   XML.Elem("theoryitem", 
		    opt_attr "name" (#name vs) @
		    opt_attr "objtype" (#objtype vs),
		    [XML.Text (#text vs)])
	   
	 | Closetheory vs => 
	   XML.Elem("closetheory", [], [XML.Text (#text vs)])
	   
	 | Opengoal vs => 
	   XML.Elem("opengoal", 
		    opt_attr "thmname" (#thmname vs), 
		    [XML.Text (#text vs)])

	 | Proofstep vs => 
	   XML.Elem("proofstep", [], [XML.Text (#text vs)])

	 | Closegoal vs => 
	   XML.Elem("closegoal", [], [XML.Text (#text vs)])

	 | Giveupgoal vs => 
	   XML.Elem("giveupgoal", [], [XML.Text (#text vs)])

	 | Postponegoal vs => 
	   XML.Elem("postponegoal", [], [XML.Text (#text vs)])

	 | Comment vs => 
	   XML.Elem("comment", [], [XML.Text (#text vs)])

	 | Whitespace vs => 
	   XML.Elem("whitespace", [], [XML.Text (#text vs)])

	 | Doccomment vs => 
	   XML.Elem("doccomment", [], [XML.Text (#text vs)])

	 | Spuriouscmd vs => 
	   XML.Elem("spuriouscmd", [], [XML.Text (#text vs)])

	 | Badcmd vs => 
	   XML.Elem("badcmd", [], [XML.Text (#text vs)])

	 | Unparseable vs => 
	   XML.Elem("unparseable", [], [XML.Text (#text vs)])

	 | Metainfo vs => 
	   XML.Elem("metainfo", opt_attr "name" (#name vs), 
		    [XML.Text (#text vs)])

	 | Litcomment vs =>
	   XML.Elem("litcomment", opt_attr "format" (#format vs), 
		   #content vs)

	 | Showcode vs =>
           XML.Elem("showcode", 
		    attr "show" (PgipTypes.bool_to_pgstring (#show vs)), [])

	 | Setformat vs => 
	   XML.Elem("setformat", attr "format" (#format vs), [])

   val output_doc = map xml_of

   fun unparse_elt docelt = 
   case docelt of
       Openblock vs => ""
     | Closeblock vs => ""
     | Opentheory vs => #text vs
     | Theoryitem vs => #text vs
     | Closetheory vs => #text vs
     | Opengoal vs => #text vs
     | Proofstep vs => #text vs
     | Closegoal vs => #text vs
     | Giveupgoal vs => #text vs
     | Postponegoal vs => #text vs
     | Comment vs => #text vs
     | Doccomment vs => #text vs
     | Whitespace vs => #text vs
     | Spuriouscmd vs => #text vs
     | Badcmd vs => #text vs
     | Unparseable vs => #text vs
     | Metainfo vs => #text vs
     | _ => ""


   val unparse_doc = map unparse_elt


   (* Names of all PGIP document markup elements *)
   val doc_markup_elements =
       ["openblock",
        "closeblock",
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
	"metainfo",
	(* the prover should never receive the next three,
  	   but we include them here so that they are ignored. *)
	"litcomment",
	"showcode",
	"setformat"]

   (* non-document/empty text, must be ignored *)
   val doc_markup_elements_ignored =
       [ "metainfo", "openblock", "closeblock",
	 "litcomment", "showcode", "setformat" ]
end
