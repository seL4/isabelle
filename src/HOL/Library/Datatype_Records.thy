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

open_bundle datatype_record_syntax
begin

unbundle no record_syntax

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

end

named_theorems datatype_record_update

ML_file \<open>datatype_records.ML\<close>
setup \<open>Datatype_Records.setup\<close>

end