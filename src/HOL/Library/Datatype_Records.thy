(*  Title:      HOL/Library/Datatype_Records.thy
    Author:     Lars Hupel
*)

section \<open>Records based on BNF/datatype machinery\<close>

theory Datatype_Records
imports Main
keywords "datatype_record" :: thy_defn
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
  "_constify"           :: "id => ident"                        (\<open>_\<close>)
  "_constify"           :: "longid => ident"                    (\<open>_\<close>)

  "_field_type"         :: "ident => type => field_type"        (\<open>(\<open>indent=2 notation=\<open>infix field type\<close>\<close>_ ::/ _)\<close>)
  ""                    :: "field_type => field_types"          (\<open>_\<close>)
  "_field_types"        :: "field_type => field_types => field_types"    (\<open>_,/ _\<close>)
  "_record_type"        :: "field_types => type"                (\<open>(\<open>indent=3 notation=\<open>mixfix record type\<close>\<close>\<lparr>_\<rparr>)\<close>)
  "_record_type_scheme" :: "field_types => type => type"        (\<open>(\<open>indent=3 notation=\<open>mixfix record type\<close>\<close>\<lparr>_,/ (2\<dots> ::/ _)\<rparr>)\<close>)

  "_field"              :: "ident => 'a => field"               (\<open>(\<open>indent=2 notation=\<open>infix field value\<close>\<close>_ =/ _)\<close>)
  ""                    :: "field => fields"                    (\<open>_\<close>)
  "_fields"             :: "field => fields => fields"          (\<open>_,/ _\<close>)
  "_record"             :: "fields => 'a"                       (\<open>(\<open>indent=3 notation=\<open>mixfix record value\<close>\<close>\<lparr>_\<rparr>)\<close>)
  "_record_scheme"      :: "fields => 'a => 'a"                 (\<open>(\<open>indent=3 notation=\<open>mixfix record value\<close>\<close>\<lparr>_,/ (2\<dots> =/ _)\<rparr>)\<close>)

  "_field_update"       :: "ident => 'a => field_update"        (\<open>(\<open>indent=2 notation=\<open>infix field update\<close>\<close>_ :=/ _)\<close>)
  ""                    :: "field_update => field_updates"      (\<open>_\<close>)
  "_field_updates"      :: "field_update => field_updates => field_updates"  (\<open>_,/ _\<close>)
  "_record_update"      :: "'a => field_updates => 'b"          (\<open>_/(\<open>indent=3 notation=\<open>mixfix record update\<close>\<close>\<lparr>_\<rparr>)\<close> [900, 0] 900)

no_syntax (ASCII)
  "_record_type"        :: "field_types => type"                (\<open>(\<open>indent=3 notation=\<open>mixfix record type\<close>\<close>'(| _ |'))\<close>)
  "_record_type_scheme" :: "field_types => type => type"        (\<open>(\<open>indent=3 notation=\<open>mixfix record type\<close>\<close>'(| _,/ (2... ::/ _) |'))\<close>)
  "_record"             :: "fields => 'a"                       (\<open>(\<open>indent=3 notation=\<open>mixfix record value\<close>\<close>'(| _ |'))\<close>)
  "_record_scheme"      :: "fields => 'a => 'a"                 (\<open>(\<open>indent=3 notation=\<open>mixfix record value\<close>\<close>'(| _,/ (2... =/ _) |'))\<close>)
  "_record_update"      :: "'a => field_updates => 'b"          (\<open>_/(\<open>indent=3 notation=\<open>mixfix record update\<close>\<close>'(| _ |'))\<close> [900, 0] 900)

(* copied and adapted from Record.thy *)

nonterminal
  field and
  fields and
  field_update and
  field_updates

syntax
  "_constify"               :: "id => ident"                        (\<open>_\<close>)
  "_constify"               :: "longid => ident"                    (\<open>_\<close>)

  "_datatype_field"         :: "ident => 'a => field"               (\<open>(2_ =/ _)\<close>)
  ""                        :: "field => fields"                    (\<open>_\<close>)
  "_datatype_fields"        :: "field => fields => fields"          (\<open>_,/ _\<close>)
  "_datatype_record"        :: "fields => 'a"                       (\<open>(3\<lparr>_\<rparr>)\<close>)
  "_datatype_field_update"  :: "ident => 'a => field_update"        (\<open>(2_ :=/ _)\<close>)
  ""                        :: "field_update => field_updates"      (\<open>_\<close>)
  "_datatype_field_updates" :: "field_update => field_updates => field_updates"  (\<open>_,/ _\<close>)
  "_datatype_record_update" :: "'a => field_updates => 'b"          (\<open>_/(3\<lparr>_\<rparr>)\<close> [900, 0] 900)

syntax (ASCII)
  "_datatype_record"        :: "fields => 'a"                       (\<open>(3'(| _ |'))\<close>)
  "_datatype_record_scheme" :: "fields => 'a => 'a"                 (\<open>(3'(| _,/ (2... =/ _) |'))\<close>)
  "_datatype_record_update" :: "'a => field_updates => 'b"          (\<open>_/(3'(| _ |'))\<close> [900, 0] 900)

named_theorems datatype_record_update

ML_file \<open>datatype_records.ML\<close>
setup \<open>Datatype_Records.setup\<close>

end