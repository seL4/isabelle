(*  Title:      HOL/Predicate.thy
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* Predicates *}

theory Predicate
imports Inductive
begin

subsection {* Converting between predicates and sets *}

definition
  member :: "'a set => 'a => bool" where
  "member == %S x. x : S"

lemma memberI[intro!, Pure.intro!]: "x : S ==> member S x"
  by (simp add: member_def)

lemma memberD[dest!, Pure.dest!]: "member S x ==> x : S"
  by (simp add: member_def)

lemma member_eq[simp]: "member S x = (x : S)"
  by (simp add: member_def)

lemma member_Collect_eq[simp]: "member (Collect P) = P"
  by (simp add: member_def)

lemma Collect_member_eq[simp]: "Collect (member S) = S"
  by (simp add: member_def)

lemma split_set: "(!!S. PROP P S) == (!!S. PROP P (Collect S))"
proof
  fix S
  assume "!!S. PROP P S"
  then show "PROP P (Collect S)" .
next
  fix S
  assume "!!S. PROP P (Collect S)"
  then have "PROP P {x. x : S}" .
  thus "PROP P S" by simp
qed

lemma split_predicate: "(!!S. PROP P S) == (!!S. PROP P (member S))"
proof
  fix S
  assume "!!S. PROP P S"
  then show "PROP P (member S)" .
next
  fix S
  assume "!!S. PROP P (member S)"
  then have "PROP P (member {x. S x})" .
  thus "PROP P S" by simp
qed

lemma member_right_eq: "(x == member y) == (Collect x == y)"
  by (rule equal_intr_rule, simp, drule symmetric, simp)

definition
  member2 :: "('a * 'b) set => 'a => 'b \<Rightarrow> bool" where
  "member2 == %S x y. (x, y) : S"

definition
  Collect2 :: "('a => 'b => bool) => ('a * 'b) set" where
  "Collect2 == %P. {(x, y). P x y}"

lemma member2I[intro!, Pure.intro!]: "(x, y) : S ==> member2 S x y"
  by (simp add: member2_def)

lemma member2D[dest!, Pure.dest!]: "member2 S x y ==> (x, y) : S"
  by (simp add: member2_def)

lemma member2_eq[simp]: "member2 S x y = ((x, y) : S)"
  by (simp add: member2_def)

lemma Collect2I: "P x y ==> (x, y) : Collect2 P"
  by (simp add: Collect2_def)

lemma Collect2D: "(x, y) : Collect2 P ==> P x y"
  by (simp add: Collect2_def)

lemma member2_Collect2_eq[simp]: "member2 (Collect2 P) = P"
  by (simp add: member2_def Collect2_def)

lemma Collect2_member2_eq[simp]: "Collect2 (member2 S) = S"
  by (auto simp add: member2_def Collect2_def)

lemma mem_Collect2_eq[iff]: "((x, y) : Collect2 P) = P x y"
  by (iprover intro: Collect2I dest: Collect2D)

lemma member2_Collect_split_eq [simp]: "member2 (Collect (split P)) = P"
  by (simp add: expand_fun_eq)

lemma split_set2: "(!!S. PROP P S) == (!!S. PROP P (Collect2 S))"
proof
  fix S
  assume "!!S. PROP P S"
  then show "PROP P (Collect2 S)" .
next
  fix S
  assume "!!S. PROP P (Collect2 S)"
  then have "PROP P (Collect2 (member2 S))" .
  thus "PROP P S" by simp
qed

lemma split_predicate2: "(!!S. PROP P S) == (!!S. PROP P (member2 S))"
proof
  fix S
  assume "!!S. PROP P S"
  then show "PROP P (member2 S)" .
next
  fix S
  assume "!!S. PROP P (member2 S)"
  then have "PROP P (member2 (Collect2 S))" .
  thus "PROP P S" by simp
qed

lemma member2_right_eq: "(x == member2 y) == (Collect2 x == y)"
  by (rule equal_intr_rule, simp, drule symmetric, simp)

ML_setup {*
local

fun vars_of b (v as Var _) = if b then [] else [v]
  | vars_of b (t $ u) = vars_of true t union vars_of false u
  | vars_of b (Abs (_, _, t)) = vars_of false t
  | vars_of _ _ = [];

fun rew ths1 ths2 th = Drule.forall_elim_vars 0
  (rewrite_rule ths2 (rewrite_rule ths1 (Drule.forall_intr_list
    (map (cterm_of (theory_of_thm th)) (vars_of false (prop_of th))) th)));

val get_eq = Simpdata.mk_eq o thm;

val split_predicate = get_eq "split_predicate";
val split_predicate2 = get_eq "split_predicate2";
val split_set = get_eq "split_set";
val split_set2 = get_eq "split_set2";
val member_eq = get_eq "member_eq";
val member2_eq = get_eq "member2_eq";
val member_Collect_eq = get_eq "member_Collect_eq";
val member2_Collect2_eq = get_eq "member2_Collect2_eq";
val mem_Collect2_eq = get_eq "mem_Collect2_eq";
val member_right_eq = thm "member_right_eq";
val member2_right_eq = thm "member2_right_eq";

val rew' = Thm.symmetric o rew [split_set2] [split_set,
  member_right_eq, member2_right_eq, member_Collect_eq, member2_Collect2_eq];

val rules1 = [split_predicate, split_predicate2, member_eq, member2_eq];
val rules2 = [split_set, mk_meta_eq mem_Collect_eq, mem_Collect2_eq];

structure PredSetConvData = GenericDataFun
(
  type T = thm list;
  val empty = [];
  val extend = I;
  fun merge _ = Drule.merge_rules;
);

fun mk_attr ths1 ths2 f = Attrib.syntax (Attrib.thms >> (fn ths =>
  Thm.rule_attribute (fn ctxt => rew ths1 (map (f o Simpdata.mk_eq)
    (ths @ PredSetConvData.get ctxt) @ ths2))));

val pred_set_conv_att = Attrib.no_args (Thm.declaration_attribute
  (Drule.add_rule #> PredSetConvData.map));

in

val _ = ML_Context.>> (
  Attrib.add_attributes
    [("pred_set_conv", pred_set_conv_att,
        "declare rules for converting between predicate and set notation"),
     ("to_set", mk_attr [] rules1 I, "convert rule to set notation"),
     ("to_pred", mk_attr [split_set2] rules2 rew',
        "convert rule to predicate notation")])

end;
*}

lemma member_inject [pred_set_conv]: "(member R = member S) = (R = S)"
  by (auto simp add: expand_fun_eq)

lemma member2_inject [pred_set_conv]: "(member2 R = member2 S) = (R = S)"
  by (auto simp add: expand_fun_eq)

lemma member_mono [pred_set_conv]: "(member R <= member S) = (R <= S)"
  by fast

lemma member2_mono [pred_set_conv]: "(member2 R <= member2 S) = (R <= S)"
  by fast

lemma member_empty [pred_set_conv]: "(%x. False) = member {}"
  by (simp add: expand_fun_eq)

lemma member2_empty [pred_set_conv]: "(%x y. False) = member2 {}"
  by (simp add: expand_fun_eq)


subsubsection {* Binary union *}

lemma member_Un [pred_set_conv]: "sup (member R) (member S) = member (R Un S)"
  by (simp add: expand_fun_eq sup_fun_eq sup_bool_eq)

lemma member2_Un [pred_set_conv]: "sup (member2 R) (member2 S) = member2 (R Un S)"
  by (simp add: expand_fun_eq sup_fun_eq sup_bool_eq)

lemma sup1_iff [simp]: "sup A B x \<longleftrightarrow> A x | B x"
  by (simp add: sup_fun_eq sup_bool_eq)

lemma sup2_iff [simp]: "sup A B x y \<longleftrightarrow> A x y | B x y"
  by (simp add: sup_fun_eq sup_bool_eq)

lemma sup1I1 [elim?]: "A x \<Longrightarrow> sup A B x"
  by simp

lemma sup2I1 [elim?]: "A x y \<Longrightarrow> sup A B x y"
  by simp

lemma join1I2 [elim?]: "B x \<Longrightarrow> sup A B x"
  by simp

lemma sup1I2 [elim?]: "B x y \<Longrightarrow> sup A B x y"
  by simp

text {*
  \medskip Classical introduction rule: no commitment to @{text A} vs
  @{text B}.
*}

lemma sup1CI [intro!]: "(~ B x ==> A x) ==> sup A B x"
  by auto

lemma sup2CI [intro!]: "(~ B x y ==> A x y) ==> sup A B x y"
  by auto

lemma sup1E [elim!]: "sup A B x ==> (A x ==> P) ==> (B x ==> P) ==> P"
  by simp iprover

lemma sup2E [elim!]: "sup A B x y ==> (A x y ==> P) ==> (B x y ==> P) ==> P"
  by simp iprover


subsubsection {* Binary intersection *}

lemma member_Int [pred_set_conv]: "inf (member R) (member S) = member (R Int S)"
  by (simp add: expand_fun_eq inf_fun_eq inf_bool_eq)

lemma member2_Int [pred_set_conv]: "inf (member2 R) (member2 S) = member2 (R Int S)"
  by (simp add: expand_fun_eq inf_fun_eq inf_bool_eq)

lemma inf1_iff [simp]: "inf A B x \<longleftrightarrow> A x \<and> B x"
  by (simp add: inf_fun_eq inf_bool_eq)

lemma inf2_iff [simp]: "inf A B x y \<longleftrightarrow> A x y \<and> B x y"
  by (simp add: inf_fun_eq inf_bool_eq)

lemma inf1I [intro!]: "A x ==> B x ==> inf A B x"
  by simp

lemma inf2I [intro!]: "A x y ==> B x y ==> inf A B x y"
  by simp

lemma inf1D1: "inf A B x ==> A x"
  by simp

lemma inf2D1: "inf A B x y ==> A x y"
  by simp

lemma inf1D2: "inf A B x ==> B x"
  by simp

lemma inf2D2: "inf A B x y ==> B x y"
  by simp

lemma inf1E [elim!]: "inf A B x ==> (A x ==> B x ==> P) ==> P"
  by simp

lemma inf2E [elim!]: "inf A B x y ==> (A x y ==> B x y ==> P) ==> P"
  by simp


subsubsection {* Unions of families *}

lemma member_SUP: "(SUP i. member (r i)) = member (UN i. r i)"
  by (simp add: SUPR_def Sup_fun_eq Sup_bool_eq expand_fun_eq) blast

lemma member2_SUP: "(SUP i. member2 (r i)) = member2 (UN i. r i)"
  by (simp add: SUPR_def Sup_fun_eq Sup_bool_eq expand_fun_eq) blast

lemma SUP1_iff [simp]: "(SUP x:A. B x) b = (EX x:A. B x b)"
  by (simp add: SUPR_def Sup_fun_eq Sup_bool_eq) blast

lemma SUP2_iff [simp]: "(SUP x:A. B x) b c = (EX x:A. B x b c)"
  by (simp add: SUPR_def Sup_fun_eq Sup_bool_eq) blast

lemma SUP1_I [intro]: "a : A ==> B a b ==> (SUP x:A. B x) b"
  by auto

lemma SUP2_I [intro]: "a : A ==> B a b c ==> (SUP x:A. B x) b c"
  by auto

lemma SUP1_E [elim!]: "(SUP x:A. B x) b ==> (!!x. x : A ==> B x b ==> R) ==> R"
  by auto

lemma SUP2_E [elim!]: "(SUP x:A. B x) b c ==> (!!x. x : A ==> B x b c ==> R) ==> R"
  by auto


subsubsection {* Intersections of families *}

lemma member_INF: "(INF i. member (r i)) = member (INT i. r i)"
  by (simp add: INFI_def Inf_fun_def Inf_bool_def expand_fun_eq) blast

lemma member2_INF: "(INF i. member2 (r i)) = member2 (INT i. r i)"
  by (simp add: INFI_def Inf_fun_def Inf_bool_def expand_fun_eq) blast

lemma INF1_iff [simp]: "(INF x:A. B x) b = (ALL x:A. B x b)"
  by (simp add: INFI_def Inf_fun_def Inf_bool_def) blast

lemma INF2_iff [simp]: "(INF x:A. B x) b c = (ALL x:A. B x b c)"
  by (simp add: INFI_def Inf_fun_def Inf_bool_def) blast

lemma INF1_I [intro!]: "(!!x. x : A ==> B x b) ==> (INF x:A. B x) b"
  by auto

lemma INF2_I [intro!]: "(!!x. x : A ==> B x b c) ==> (INF x:A. B x) b c"
  by auto

lemma INF1_D [elim]: "(INF x:A. B x) b ==> a : A ==> B a b"
  by auto

lemma INF2_D [elim]: "(INF x:A. B x) b c ==> a : A ==> B a b c"
  by auto

lemma INF1_E [elim]: "(INF x:A. B x) b ==> (B a b ==> R) ==> (a ~: A ==> R) ==> R"
  by auto

lemma INF2_E [elim]: "(INF x:A. B x) b c ==> (B a b c ==> R) ==> (a ~: A ==> R) ==> R"
  by auto


subsection {* Composition of two relations *}

inductive2
  pred_comp  :: "['b => 'c => bool, 'a => 'b => bool] => 'a => 'c => bool"
    (infixr "OO" 75)
  for r :: "'b => 'c => bool" and s :: "'a => 'b => bool"
where
  pred_compI [intro]: "s a b ==> r b c ==> (r OO s) a c"

inductive_cases2 pred_compE [elim!]: "(r OO s) a c"

lemma pred_comp_rel_comp_eq [pred_set_conv]:
  "(member2 r OO member2 s) = member2 (r O s)"
  by (auto simp add: expand_fun_eq elim: pred_compE)


subsection {* Converse *}

inductive2
  conversep :: "('a => 'b => bool) => 'b => 'a => bool"
    ("(_^--1)" [1000] 1000)
  for r :: "'a => 'b => bool"
where
  conversepI: "r a b ==> r^--1 b a"

notation (xsymbols)
  conversep  ("(_\<inverse>\<inverse>)" [1000] 1000)

lemma conversepD:
  assumes ab: "r^--1 a b"
  shows "r b a" using ab
  by cases simp

lemma conversep_iff [iff]: "r^--1 a b = r b a"
  by (iprover intro: conversepI dest: conversepD)

lemma conversep_converse_eq [pred_set_conv]:
  "(member2 r)^--1 = member2 (r^-1)"
  by (auto simp add: expand_fun_eq)

lemma conversep_conversep [simp]: "(r^--1)^--1 = r"
  by (iprover intro: order_antisym conversepI dest: conversepD)

lemma converse_pred_comp: "(r OO s)^--1 = s^--1 OO r^--1"
  by (iprover intro: order_antisym conversepI pred_compI
    elim: pred_compE dest: conversepD)

lemma converse_meet: "(inf r s)^--1 = inf r^--1 s^--1"
  by (simp add: inf_fun_eq inf_bool_eq)
    (iprover intro: conversepI ext dest: conversepD)

lemma converse_join: "(sup r s)^--1 = sup r^--1 s^--1"
  by (simp add: sup_fun_eq sup_bool_eq)
    (iprover intro: conversepI ext dest: conversepD)

lemma conversep_noteq [simp]: "(op ~=)^--1 = op ~="
  by (auto simp add: expand_fun_eq)

lemma conversep_eq [simp]: "(op =)^--1 = op ="
  by (auto simp add: expand_fun_eq)


subsection {* Domain *}

inductive2
  DomainP :: "('a => 'b => bool) => 'a => bool"
  for r :: "'a => 'b => bool"
where
  DomainPI [intro]: "r a b ==> DomainP r a"

inductive_cases2 DomainPE [elim!]: "DomainP r a"

lemma member2_DomainP [pred_set_conv]: "DomainP (member2 r) = member (Domain r)"
  by (blast intro!: Orderings.order_antisym)


subsection {* Range *}

inductive2
  RangeP :: "('a => 'b => bool) => 'b => bool"
  for r :: "'a => 'b => bool"
where
  RangePI [intro]: "r a b ==> RangeP r b"

inductive_cases2 RangePE [elim!]: "RangeP r b"

lemma member2_RangeP [pred_set_conv]: "RangeP (member2 r) = member (Range r)"
  by (blast intro!: Orderings.order_antisym)


subsection {* Inverse image *}

definition
  inv_imagep :: "('b => 'b => bool) => ('a => 'b) => 'a => 'a => bool" where
  "inv_imagep r f == %x y. r (f x) (f y)"

lemma [pred_set_conv]: "inv_imagep (member2 r) f = member2 (inv_image r f)"
  by (simp add: inv_image_def inv_imagep_def)

lemma in_inv_imagep [simp]: "inv_imagep r f x y = r (f x) (f y)"
  by (simp add: inv_imagep_def)


subsection {* Properties of relations - predicate versions *}

abbreviation antisymP :: "('a => 'a => bool) => bool" where
  "antisymP r == antisym (Collect2 r)"

abbreviation transP :: "('a => 'a => bool) => bool" where
  "transP r == trans (Collect2 r)"

abbreviation single_valuedP :: "('a => 'b => bool) => bool" where
  "single_valuedP r == single_valued (Collect2 r)"


subsection {* Bounded quantifiers for predicates *}

text {*
Bounded existential quantifier for predicates (executable).
*}

inductive2 bexp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  for P :: "'a \<Rightarrow> bool" and Q :: "'a \<Rightarrow> bool"
where
  bexpI [intro]: "P x \<Longrightarrow> Q x \<Longrightarrow> bexp P Q"

lemmas bexpE [elim!] = bexp.cases

syntax
  Bexp :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> bool" ("(3\<exists>_\<triangleright>_./ _)" [0, 0, 10] 10)

translations
  "\<exists>x\<triangleright>P. Q" \<rightleftharpoons> "CONST bexp P (\<lambda>x. Q)"

constdefs
  ballp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  "ballp P Q \<equiv> \<forall>x. P x \<longrightarrow> Q x"

syntax
  Ballp :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> bool" ("(3\<forall>_\<triangleright>_./ _)" [0, 0, 10] 10)

translations
  "\<forall>x\<triangleright>P. Q" \<rightleftharpoons> "CONST ballp P (\<lambda>x. Q)"

(* To avoid eta-contraction of body: *)
print_translation {*
let
  fun btr' syn [A,Abs abs] =
    let val (x,t) = atomic_abs_tr' abs
    in Syntax.const syn $ x $ A $ t end
in
[("ballp", btr' "Ballp"),("bexp", btr' "Bexp")]
end
*}

lemma ballpI [intro!]: "(\<And>x. A x \<Longrightarrow> P x) \<Longrightarrow> \<forall>x\<triangleright>A. P x"
  by (simp add: ballp_def)

lemma bspecp [dest?]: "\<forall>x\<triangleright>A. P x \<Longrightarrow> A x \<Longrightarrow> P x"
  by (simp add: ballp_def)

lemma ballpE [elim]: "\<forall>x\<triangleright>A. P x \<Longrightarrow> (P x \<Longrightarrow> Q) \<Longrightarrow> (\<not> A x \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (unfold ballp_def) blast

lemma ballp_not_bexp_eq: "(\<forall>x\<triangleright>P. Q x) = (\<not> (\<exists>x\<triangleright>P. \<not> Q x))"
  by (blast dest: bspecp)

declare ballp_not_bexp_eq [THEN eq_reflection, code unfold]

end
