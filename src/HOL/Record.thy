(*  Title:      HOL/Record.thy
    ID:         $Id$
    Author:     Wolfgang Naraschewski, Norbert Schirmer  and Markus Wenzel, TU Muenchen
*)

theory Record = Product_Type
files ("Tools/record_package.ML"):

ML {*
val [h1, h2] = Goal "PROP Goal (\<And>x. PROP P x) \<Longrightarrow> (PROP P x \<Longrightarrow> PROP Q) \<Longrightarrow> PROP Q";
by (rtac h2 1);
by (rtac (gen_all (h1 RS Drule.rev_triv_goal)) 1);
qed "meta_allE";
*}

lemma prop_subst: "s = t \<Longrightarrow> PROP P t \<Longrightarrow> PROP P s"
  by simp

lemma rec_UNIV_I: "\<And>x. x\<in>UNIV \<equiv> True"
  by simp

lemma rec_True_simp: "(True \<Longrightarrow> PROP P) \<equiv> PROP P"
  by simp


subsection {* Concrete record syntax *}

nonterminals
  ident field_type field_types field fields update updates
syntax
  "_constify"           :: "id => ident"                        ("_")
  "_constify"           :: "longid => ident"                    ("_")

  "_field_type"         :: "[ident, type] => field_type"        ("(2_ ::/ _)")
  ""                    :: "field_type => field_types"          ("_")
  "_field_types"        :: "[field_type, field_types] => field_types"    ("_,/ _")
  "_record_type"        :: "field_types => type"                ("(3'(| _ |'))")
  "_record_type_scheme" :: "[field_types, type] => type"        ("(3'(| _,/ (2... ::/ _) |'))")

  "_field"              :: "[ident, 'a] => field"               ("(2_ =/ _)")
  ""                    :: "field => fields"                    ("_")
  "_fields"             :: "[field, fields] => fields"          ("_,/ _")
  "_record"             :: "fields => 'a"                       ("(3'(| _ |'))")
  "_record_scheme"      :: "[fields, 'a] => 'a"                 ("(3'(| _,/ (2... =/ _) |'))")

  "_update_name"        :: idt
  "_update"             :: "[ident, 'a] => update"              ("(2_ :=/ _)")
  ""                    :: "update => updates"                  ("_")
  "_updates"            :: "[update, updates] => updates"       ("_,/ _")
  "_record_update"      :: "['a, updates] => 'b"                ("_/(3'(| _ |'))" [900,0] 900)

syntax (xsymbols)
  "_record_type"        :: "field_types => type"                ("(3\<lparr>_\<rparr>)")
  "_record_type_scheme" :: "[field_types, type] => type"        ("(3\<lparr>_,/ (2\<dots> ::/ _)\<rparr>)")
  "_record"             :: "fields => 'a"                               ("(3\<lparr>_\<rparr>)")
  "_record_scheme"      :: "[fields, 'a] => 'a"                 ("(3\<lparr>_,/ (2\<dots> =/ _)\<rparr>)")
  "_record_update"      :: "['a, updates] => 'b"                ("_/(3\<lparr>_\<rparr>)" [900,0] 900)

use "Tools/record_package.ML";
setup RecordPackage.setup;

end

