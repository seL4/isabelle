(*  Title:      Pure/ProofGeneral/pgml.ML
    Author:     David Aspinall

PGIP abstraction: PGML
*)

signature PGML =
sig
    type pgmlsym = { name: string, content: string }

    datatype pgmlatom = Sym of pgmlsym | Str of string

    datatype pgmlorient = HOVOrient | HOrient | VOrient | HVOrient

    datatype pgmlplace = Subscript | Superscript | Above | Below

    datatype pgmldec = Bold | Italic | Error | Warning | Info | Other of string

    datatype pgmlaction = Toggle | Button | Menu

    datatype pgmlterm =
             Atoms of { kind: string option, content: pgmlatom list }
           | Box of { orient: pgmlorient option, indent: int option, content: pgmlterm list }
           | Break of { mandatory: bool option, indent: int option }
           | Subterm of { kind: string option,
                          param: string option,
                          place: pgmlplace option,
                          name: string option,
                          decoration: pgmldec option,
                          action: pgmlaction option,
                          pos: string option,
                          xref: PgipTypes.pgipurl option,
                          content: pgmlterm list }
           | Alt of { kind: string option, content: pgmlterm list }
           | Embed of XML.tree list
           | Raw of XML.tree

    datatype pgml =
             Pgml of { version: string option, systemid: string option,
                       area: PgipTypes.displayarea option,
                       content: pgmlterm list }

    val atom_to_xml : pgmlatom -> XML.tree
    val pgmlterm_to_xml : pgmlterm -> XML.tree

    val pgml_to_xml : pgml -> XML.tree
end


structure Pgml : PGML =
struct
    open PgipTypes

    type pgmlsym = { name: string, content: string }

    datatype pgmlatom = Sym of pgmlsym | Str of string

    datatype pgmlorient = HOVOrient | HOrient | VOrient | HVOrient

    datatype pgmlplace = Subscript | Superscript | Above | Below

    datatype pgmldec = Bold | Italic | Error | Warning | Info | Other of string

    datatype pgmlaction = Toggle | Button | Menu

    datatype pgmlterm =
             Atoms of { kind: string option, content: pgmlatom list }
           | Box of { orient: pgmlorient option, indent: int option, content: pgmlterm list }
           | Break of { mandatory: bool option, indent: int option }
           | Subterm of { kind: string option,
                          param: string option,
                          place: pgmlplace option,
                          name: string option,
                          decoration: pgmldec option,
                          action: pgmlaction option,
                          pos: string option,
                          xref: PgipTypes.pgipurl option,
                          content: pgmlterm list }
           | Alt of { kind: string option, content: pgmlterm list }
           | Embed of XML.tree list
           | Raw of XML.tree


    datatype pgml =
             Pgml of { version: string option, systemid: string option,
                       area: PgipTypes.displayarea option,
                       content: pgmlterm list }

    fun pgmlorient_to_string HOVOrient = "hov"
      | pgmlorient_to_string HOrient = "h"
      | pgmlorient_to_string VOrient = "v"
      | pgmlorient_to_string HVOrient = "hv"

    fun pgmlplace_to_string Subscript = "sub"
      | pgmlplace_to_string Superscript = "sup"
      | pgmlplace_to_string Above = "above"
      | pgmlplace_to_string Below = "below"

    fun pgmldec_to_string Bold = "bold"
      | pgmldec_to_string Italic = "italic"
      | pgmldec_to_string Error = "error"
      | pgmldec_to_string Warning = "warning"
      | pgmldec_to_string Info = "info"
      | pgmldec_to_string (Other s) = "other"

    fun pgmlaction_to_string Toggle = "toggle"
      | pgmlaction_to_string Button = "button"
      | pgmlaction_to_string Menu = "menu"

    (* NOTE: we assume strings are already XML escaped here, for convenience in Isabelle;
       would be better not to *)  (* FIXME !??? *)
    fun atom_to_xml (Sym {name, content}) = XML.Elem ("sym", attr "name" name, [XML.Text content])
      | atom_to_xml (Str content) = XML.Text content;

    fun pgmlterm_to_xml (Atoms {kind, content}) =
        XML.Elem("atom", opt_attr "kind" kind, map atom_to_xml content)

      | pgmlterm_to_xml (Box {orient, indent, content}) =
        XML.Elem("box",
                 opt_attr_map pgmlorient_to_string "orient" orient @
                 opt_attr_map int_to_pgstring "indent" indent,
                 map pgmlterm_to_xml content)

      | pgmlterm_to_xml (Break {mandatory, indent}) =
        XML.Elem("break",
                 opt_attr_map bool_to_pgstring "mandatory" mandatory @
                 opt_attr_map int_to_pgstring "indent" indent, [])

      | pgmlterm_to_xml (Subterm {kind, param, place, name, decoration, action, pos, xref, content}) =
        XML.Elem("subterm",
                 opt_attr "kind" kind @
                 opt_attr "param" param @
                 opt_attr_map pgmlplace_to_string "place" place @
                 opt_attr "name" name @
                 opt_attr_map pgmldec_to_string "decoration" decoration @
                 opt_attr_map pgmlaction_to_string "action" action @
                 opt_attr "pos" pos @
                 opt_attr_map string_of_pgipurl "xref" xref,
                 map pgmlterm_to_xml content)

      | pgmlterm_to_xml (Alt {kind, content}) =
        XML.Elem("alt", opt_attr "kind" kind, map pgmlterm_to_xml content)

      | pgmlterm_to_xml (Embed xmls) = XML.Elem("embed", [], xmls)

      | pgmlterm_to_xml (Raw xml) = xml


    datatype pgml =
             Pgml of { version: string option, systemid: string option,
                       area: PgipTypes.displayarea option,
                       content: pgmlterm list }

    fun pgml_to_xml (Pgml {version,systemid,area,content}) =
        XML.Elem("pgml",
                 opt_attr "version" version @
                 opt_attr "systemid" systemid @
                 the_default [] (Option.map PgipTypes.attrs_of_displayarea area),
                 map pgmlterm_to_xml content)
end
