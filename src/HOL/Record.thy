(*  Title:      HOL/Record.thy
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen
*)

header {* Extensible records with structural subtyping *}

theory Record = Datatype
files ("Tools/record_package.ML"):


subsection {* Abstract product types *}

constdefs
  product_type :: "('p => 'a * 'b) => ('a * 'b => 'p) =>
    ('a => 'b => 'p) => (('a => 'b => 'c) => 'p => 'c) => bool"
  "product_type Rep Abs intro elim ==
    type_definition Rep Abs UNIV \<and>
    intro = (\<lambda>a b. Abs (a, b)) \<and>
    elim = (\<lambda>f. prod_case f o Rep)"

lemma product_typeI:
  "type_definition Rep Abs A ==> A == UNIV ==>
    intro == \<lambda>a b. Abs (a, b) ==> elim == \<lambda>f. prod_case f o Rep ==>
    product_type Rep Abs intro elim"
  by (simp add: product_type_def)

lemma product_type_typedef:
    "product_type Rep Abs intro elim ==> type_definition Rep Abs UNIV"
  by (unfold product_type_def) blast

lemma product_type_intro:
    "product_type Rep Abs intro elim ==> intro = (\<lambda>a b. Abs (a, b))"
  by (unfold product_type_def) blast

lemma product_type_elim:
    "product_type Rep Abs intro elim ==> elim = (\<lambda>f. prod_case f o Rep)"
  by (unfold product_type_def) fast  (* FIXME blast fails!? *)

lemma product_type_inject:
  "product_type Rep Abs intro elim ==>
    (intro x y = intro x' y') = (x = x' \<and> y = y')"
proof -
  case rule_context
  show ?thesis
    by (simp add: product_type_intro [OF rule_context]
      Abs_inject [OF product_type_typedef [OF rule_context]])
qed

lemma product_type_surject:
  "product_type Rep Abs intro elim ==>
    elim f (intro x y) = f x y"
proof -
  case rule_context
  show ?thesis
    by (simp add: product_type_intro [OF rule_context]
      product_type_elim [OF rule_context]
      Abs_inverse [OF product_type_typedef [OF rule_context]])
qed

lemma product_type_induct:
  "product_type Rep Abs intro elim ==>
    (!!x y. P (intro x y)) ==> P p"
proof -
  assume hyp: "!!x y. P (intro x y)"
  assume prod_type: "product_type Rep Abs intro elim"
  show "P p"
  proof (rule Abs_induct [OF product_type_typedef [OF prod_type]])
    fix pair show "P (Abs pair)"
    proof (rule prod.induct)
      fix x y from hyp show "P (Abs (x, y))"
	by (simp only: product_type_intro [OF prod_type])
    qed
  qed
qed


text {* \medskip Type class for record extensions. *}

axclass more < "term"
instance unit :: more ..


subsection {* Concrete syntax of records *}

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


subsection {* Package setup *}

use "Tools/record_package.ML"

parse_translation {*
  let
    fun update_name_tr (Free (x, T) :: ts) =
          Term.list_comb (Free (suffix RecordPackage.updateN x, T), ts)
      | update_name_tr (Const (x, T) :: ts) =
          Term.list_comb (Const (suffix RecordPackage.updateN x, T), ts)
      | update_name_tr (((c as Const ("_constrain", _)) $ t $ ty) :: ts) =
          Term.list_comb (c $ update_name_tr [t] $
            (Syntax.const "fun" $ ty $ Syntax.const "dummy"), ts)
      | update_name_tr ts = raise TERM ("update_name_tr", ts);
  in [("_update_name", update_name_tr)] end
*}

setup RecordPackage.setup

end
