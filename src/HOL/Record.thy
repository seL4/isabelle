(*  Title:      HOL/Record.thy
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen
*)

header {* Extensible records with structural subtyping *}

theory Record = Product_Type
files ("Tools/record_package.ML"):


subsection {* Abstract product types *}

constdefs
  product_type :: "('p => 'a * 'b) => ('a * 'b => 'p) =>
    ('a => 'b => 'p) => ('p \<Rightarrow> 'a) => ('p => 'b) => bool"
  "product_type Rep Abs pair dest1 dest2 ==
    type_definition Rep Abs UNIV \<and>
    pair = (\<lambda>a b. Abs (a, b)) \<and>
    dest1 = (\<lambda>p. fst (Rep p)) \<and>
    dest2 = (\<lambda>p. snd (Rep p))"

lemma product_typeI:
  "type_definition Rep Abs UNIV ==>
    pair == \<lambda>a b. Abs (a, b) ==>
    dest1 == (\<lambda>p. fst (Rep p)) \<Longrightarrow>
    dest2 == (\<lambda>p. snd (Rep p)) \<Longrightarrow>
    product_type Rep Abs pair dest1 dest2"
  by (simp add: product_type_def)

lemma product_type_typedef:
    "product_type Rep Abs pair dest1 dest2 ==> type_definition Rep Abs UNIV"
  by (unfold product_type_def) blast

lemma product_type_pair:
    "product_type Rep Abs pair dest1 dest2 ==> pair a b = Abs (a, b)"
  by (unfold product_type_def) blast

lemma product_type_dest1:
    "product_type Rep Abs pair dest1 dest2 ==> dest1 p = fst (Rep p)"
  by (unfold product_type_def) blast

lemma product_type_dest2:
    "product_type Rep Abs pair dest1 dest2 ==> dest2 p = snd (Rep p)"
  by (unfold product_type_def) blast


theorem product_type_inject:
  "product_type Rep Abs pair dest1 dest2 ==>
    (pair x y = pair x' y') = (x = x' \<and> y = y')"
proof -
  case rule_context
  show ?thesis
    by (simp add: product_type_pair [OF rule_context]
      Abs_inject [OF product_type_typedef [OF rule_context]])
qed

theorem product_type_conv1:
  "product_type Rep Abs pair dest1 dest2 ==> dest1 (pair x y) = x"
proof -
  case rule_context
  show ?thesis
    by (simp add: product_type_pair [OF rule_context]
      product_type_dest1 [OF rule_context]
      Abs_inverse [OF product_type_typedef [OF rule_context]])
qed

theorem product_type_conv2:
  "product_type Rep Abs pair dest1 dest2 ==> dest2 (pair x y) = y"
proof -
  case rule_context
  show ?thesis
    by (simp add: product_type_pair [OF rule_context]
      product_type_dest2 [OF rule_context]
      Abs_inverse [OF product_type_typedef [OF rule_context]])
qed

theorem product_type_induct [induct set: product_type]:
  "product_type Rep Abs pair dest1 dest2 ==>
    (!!x y. P (pair x y)) ==> P p"
proof -
  assume hyp: "!!x y. P (pair x y)"
  assume prod_type: "product_type Rep Abs pair dest1 dest2"
  show "P p"
  proof (rule Abs_induct [OF product_type_typedef [OF prod_type]])
    fix pair show "P (Abs pair)"
    proof (rule prod_induct)
      fix x y from hyp show "P (Abs (x, y))"
        by (simp only: product_type_pair [OF prod_type])
    qed
  qed
qed

theorem product_type_cases [cases set: product_type]:
  "product_type Rep Abs pair dest1 dest2 ==>
    (!!x y. p = pair x y \<Longrightarrow> C) ==> C"
proof -
  assume prod_type: "product_type Rep Abs pair dest1 dest2"
  assume "!!x y. p = pair x y \<Longrightarrow> C"
  with prod_type show C
    by (induct p) (simp only: product_type_inject [OF prod_type], blast)
qed

theorem product_type_surjective_pairing:
  "product_type Rep Abs pair dest1 dest2 ==>
    p = pair (dest1 p) (dest2 p)"
proof -
  case rule_context
  thus ?thesis by (induct p)
    (simp add: product_type_conv1 [OF rule_context] product_type_conv2 [OF rule_context])
qed

theorem product_type_split_paired_all:
  "product_type Rep Abs pair dest1 dest2 ==>
  (\<And>x. PROP P x) \<equiv> (\<And>a b. PROP P (pair a b))"
proof
  fix a b
  assume "!!x. PROP P x"
  thus "PROP P (pair a b)" .
next
  case rule_context
  fix x
  assume "!!a b. PROP P (pair a b)"
  hence "PROP P (pair (dest1 x) (dest2 x))" .
  thus "PROP P x" by (simp only: product_type_surjective_pairing [OF rule_context, symmetric])
qed


text {* \medskip Type class for record extensions. *}

axclass more < "term"
instance unit :: more ..


subsection {* Record package setup *}

use "Tools/record_package.ML"
setup RecordPackage.setup


subsection {* Concrete syntax *}

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

end
