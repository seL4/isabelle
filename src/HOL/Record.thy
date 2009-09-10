(*  Title:      HOL/Record.thy
    ID:         $Id: Record.thy,v 1.33 2007/12/19 15:32:12 schirmer Exp $
    Author:     Wolfgang Naraschewski, Norbert Schirmer and Markus Wenzel, TU Muenchen
*)

header {* Extensible records with structural subtyping *}

theory Record
imports Product_Type IsTuple
uses ("Tools/record.ML")
begin

lemma prop_subst: "s = t \<Longrightarrow> PROP P t \<Longrightarrow> PROP P s"
  by simp

lemma K_record_comp: "(\<lambda>x. c) \<circ> f = (\<lambda>x. c)" 
  by (simp add: comp_def)

lemma meta_iffD2:
  "\<lbrakk> PROP P \<equiv> PROP Q; PROP Q \<rbrakk> \<Longrightarrow> PROP P"
  by simp

lemma o_eq_dest_lhs:
  "a o b = c \<Longrightarrow> a (b v) = c v"
  by clarsimp

lemma id_o_refl:
  "id o f = f o id"
  by simp

lemma o_eq_id_dest:
  "a o b = id o c \<Longrightarrow> a (b v) = c v"
  by clarsimp

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

use "Tools/record.ML"
setup Record.setup

end
