(*  Title:      HOL/Library/Datatype_Records.thy
    Author:     Lars Hupel
*)

section \<open>Records based on BNF/datatype machinery\<close>

theory Datatype_Records
imports Main
keywords "datatype_record" :: thy_decl
begin

text \<open>
  This theory provides an alternative, stripped-down implementation of records based on the
  machinery of the @{command datatype} package.

  It supports:
  \<^item> similar declaration syntax as records
  \<^item> record creation and update syntax (using \<open>\<lparr> ... \<rparr>\<close> brackets)
  \<^item> regular datatype features (e.g. dead type variables etc.)
  \<^item> ``after-the-fact'' registration of single-free-constructor types as records
\<close>

text \<open>
  Caveats:
  \<^item> there is no compatibility layer; importing this theory will disrupt existing syntax
  \<^item> extensible records are not supported
\<close>

no_syntax
  "_constify"           :: "id => ident"                        ("_")
  "_constify"           :: "longid => ident"                    ("_")

  "_field_type"         :: "ident => type => field_type"        ("(2_ ::/ _)")
  ""                    :: "field_type => field_types"          ("_")
  "_field_types"        :: "field_type => field_types => field_types"    ("_,/ _")
  "_record_type"        :: "field_types => type"                ("(3\<lparr>_\<rparr>)")
  "_record_type_scheme" :: "field_types => type => type"        ("(3\<lparr>_,/ (2\<dots> ::/ _)\<rparr>)")

  "_field"              :: "ident => 'a => field"               ("(2_ =/ _)")
  ""                    :: "field => fields"                    ("_")
  "_fields"             :: "field => fields => fields"          ("_,/ _")
  "_record"             :: "fields => 'a"                       ("(3\<lparr>_\<rparr>)")
  "_record_scheme"      :: "fields => 'a => 'a"                 ("(3\<lparr>_,/ (2\<dots> =/ _)\<rparr>)")

  "_field_update"       :: "ident => 'a => field_update"        ("(2_ :=/ _)")
  ""                    :: "field_update => field_updates"      ("_")
  "_field_updates"      :: "field_update => field_updates => field_updates"  ("_,/ _")
  "_record_update"      :: "'a => field_updates => 'b"          ("_/(3\<lparr>_\<rparr>)" [900, 0] 900)

no_syntax (ASCII)
  "_record_type"        :: "field_types => type"                ("(3'(| _ |'))")
  "_record_type_scheme" :: "field_types => type => type"        ("(3'(| _,/ (2... ::/ _) |'))")
  "_record"             :: "fields => 'a"                       ("(3'(| _ |'))")
  "_record_scheme"      :: "fields => 'a => 'a"                 ("(3'(| _,/ (2... =/ _) |'))")
  "_record_update"      :: "'a => field_updates => 'b"          ("_/(3'(| _ |'))" [900, 0] 900)

(* copied and adapted from Record.thy *)

nonterminal
  field and
  fields and
  field_update and
  field_updates

syntax
  "_constify"               :: "id => ident"                        ("_")
  "_constify"               :: "longid => ident"                    ("_")

  "_datatype_field"         :: "ident => 'a => field"               ("(2_ =/ _)")
  ""                        :: "field => fields"                    ("_")
  "_datatype_fields"        :: "field => fields => fields"          ("_,/ _")
  "_datatype_record"        :: "fields => 'a"                       ("(3\<lparr>_\<rparr>)")
  "_datatype_field_update"  :: "ident => 'a => field_update"        ("(2_ :=/ _)")
  ""                        :: "field_update => field_updates"      ("_")
  "_datatype_field_updates" :: "field_update => field_updates => field_updates"  ("_,/ _")
  "_datatype_record_update" :: "'a => field_updates => 'b"          ("_/(3\<lparr>_\<rparr>)" [900, 0] 900)

syntax (ASCII)
  "_datatype_record"        :: "fields => 'a"                       ("(3'(| _ |'))")
  "_datatype_record_scheme" :: "fields => 'a => 'a"                 ("(3'(| _,/ (2... =/ _) |'))")
  "_datatype_record_update" :: "'a => field_updates => 'b"          ("_/(3'(| _ |'))" [900, 0] 900)

named_theorems datatype_record_update

ML_file "datatype_records.ML"
setup \<open>Datatype_Records.setup\<close>

end