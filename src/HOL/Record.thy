(*  Title:      HOL/Record.thy
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen

Extensible records with structural subtyping in HOL.  See
Tools/record_package.ML for the actual implementation.
*)

theory Record = Datatype
files "Tools/record_package.ML":


(* concrete syntax *)

nonterminals
  ident field_type field_types field fields update updates

syntax
  (*field names*)
  ""                    :: "id => ident"                                ("_")
  ""                    :: "longid => ident"                            ("_")

  (*record types*)
  "_field_type"         :: "[ident, type] => field_type"                ("(2_ ::/ _)")
  ""                    :: "field_type => field_types"                  ("_")
  "_field_types"        :: "[field_type, field_types] => field_types"   ("_,/ _")
  "_record_type"        :: "field_types => type"                        ("(3'(| _ |'))")
  "_record_type_scheme" :: "[field_types, type] => type"        ("(3'(| _,/ (2... ::/ _) |'))")

  (*records*)
  "_field"              :: "[ident, 'a] => field"                       ("(2_ =/ _)")
  ""                    :: "field => fields"                            ("_")
  "_fields"             :: "[field, fields] => fields"                  ("_,/ _")
  "_record"             :: "fields => 'a"                               ("(3'(| _ |'))")
  "_record_scheme"      :: "[fields, 'a] => 'a"                 ("(3'(| _,/ (2... =/ _) |'))")

  (*record updates*)
  "_update"             :: "[ident, 'a] => update"                      ("(2_ :=/ _)")
  ""                    :: "update => updates"                          ("_")
  "_updates"            :: "[update, updates] => updates"               ("_,/ _")
  "_record_update"      :: "['a, updates] => 'b"                ("_/(3'(| _ |'))" [900,0] 900)

syntax (input)   (* FIXME (xsymbols) *)
  "_record_type"        :: "field_types => type"                        ("(3\<lparr>_\<rparr>)")
  "_record_type_scheme" :: "[field_types, type] => type"        ("(3\<lparr>_,/ (2\<dots> ::/ _)\<rparr>)")
  "_record"             :: "fields => 'a"                               ("(3\<lparr>_\<rparr>)")
  "_record_scheme"      :: "[fields, 'a] => 'a"                 ("(3\<lparr>_,/ (2\<dots> =/ _)\<rparr>)")
  "_record_update"      :: "['a, updates] => 'b"                ("_/(3\<lparr>_\<rparr>)" [900,0] 900)


(* type class for record extensions *)

axclass more < "term"
instance unit :: more ..


(* initialize the package *)

setup
  RecordPackage.setup


end
