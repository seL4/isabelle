(*  Title:      HOL/Record.thy
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen
*)

header {* Extensible records with structural subtyping *}

theory Record = Product_Type
files ("Tools/record_package.ML"):


subsection {* Abstract product types *}

locale product_type =
  fixes Rep and Abs and pair and dest1 and dest2
  assumes "typedef": "type_definition Rep Abs UNIV"
    and pair: "pair == (\<lambda>a b. Abs (a, b))"
    and dest1: "dest1 == (\<lambda>p. fst (Rep p))"
    and dest2: "dest2 == (\<lambda>p. snd (Rep p))"

lemma (in product_type)
    "inject": "(pair x y = pair x' y') = (x = x' \<and> y = y')"
  by (simp add: pair type_definition.Abs_inject [OF "typedef"])

lemma (in product_type) conv1: "dest1 (pair x y) = x"
  by (simp add: pair dest1 type_definition.Abs_inverse [OF "typedef"])

lemma (in product_type) conv2: "dest2 (pair x y) = y"
  by (simp add: pair dest2 type_definition.Abs_inverse [OF "typedef"])

lemma (in product_type) induct [induct type]:
  assumes hyp: "!!x y. P (pair x y)"
  shows "P p"
proof (rule type_definition.Abs_induct [OF "typedef"])
  fix q show "P (Abs q)"
  proof (induct q)
    fix x y have "P (pair x y)" by (rule hyp)
    also have "pair x y = Abs (x, y)" by (simp only: pair)
    finally show "P (Abs (x, y))" .
  qed
qed

lemma (in product_type) cases [cases type]:
    "(!!x y. p = pair x y ==> C) ==> C"
  by (induct p) (auto simp add: "inject")

lemma (in product_type) surjective_pairing:
    "p = pair (dest1 p) (dest2 p)"
  by (induct p) (simp only: conv1 conv2)

lemma (in product_type) split_paired_all:
  "(!!x. PROP P x) == (!!a b. PROP P (pair a b))"
proof
  fix a b
  assume "!!x. PROP P x"
  thus "PROP P (pair a b)" .
next
  fix x
  assume "!!a b. PROP P (pair a b)"
  hence "PROP P (pair (dest1 x) (dest2 x))" .
  thus "PROP P x" by (simp only: surjective_pairing [symmetric])
qed

lemma (in product_type) split_paired_All:
  "(ALL x. P x) = (ALL a b. P (pair a b))"
proof
  fix a b
  assume "ALL x. P x"
  thus "ALL a b. P (pair a b)" by rules
next
  assume P: "ALL a b. P (pair a b)"
  show "ALL x. P x"
  proof
    fix x
    from P have "P (pair (dest1 x) (dest2 x))" by rules
    thus "P x" by (simp only: surjective_pairing [symmetric])
  qed
qed


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


subsection {* Package setup *}

use "Tools/record_package.ML"
setup RecordPackage.setup

end
