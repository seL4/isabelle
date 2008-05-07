(*  Title:      HOL/Predicate.thy
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* Predicates *}

theory Predicate
imports Inductive Relation
begin

subsection {* Equality and Subsets *}

lemma pred_equals_eq: "((\<lambda>x. x \<in> R) = (\<lambda>x. x \<in> S)) = (R = S)"
  by (simp add: mem_def)

lemma pred_equals_eq2 [pred_set_conv]: "((\<lambda>x y. (x, y) \<in> R) = (\<lambda>x y. (x, y) \<in> S)) = (R = S)"
  by (simp add: expand_fun_eq mem_def)

lemma pred_subset_eq: "((\<lambda>x. x \<in> R) <= (\<lambda>x. x \<in> S)) = (R <= S)"
  by (simp add: mem_def)

lemma pred_subset_eq2 [pred_set_conv]: "((\<lambda>x y. (x, y) \<in> R) <= (\<lambda>x y. (x, y) \<in> S)) = (R <= S)"
  by fast


subsection {* Top and bottom elements *}

lemma top1I [intro!]: "top x"
  by (simp add: top_fun_eq top_bool_eq)

lemma top2I [intro!]: "top x y"
  by (simp add: top_fun_eq top_bool_eq)

lemma bot1E [elim!]: "bot x \<Longrightarrow> P"
  by (simp add: bot_fun_eq bot_bool_eq)

lemma bot2E [elim!]: "bot x y \<Longrightarrow> P"
  by (simp add: bot_fun_eq bot_bool_eq)


subsection {* The empty set *}

lemma bot_empty_eq: "bot = (\<lambda>x. x \<in> {})"
  by (auto simp add: expand_fun_eq)

lemma bot_empty_eq2: "bot = (\<lambda>x y. (x, y) \<in> {})"
  by (auto simp add: expand_fun_eq)


subsection {* Binary union *}

lemma sup1_iff [simp]: "sup A B x \<longleftrightarrow> A x | B x"
  by (simp add: sup_fun_eq sup_bool_eq)

lemma sup2_iff [simp]: "sup A B x y \<longleftrightarrow> A x y | B x y"
  by (simp add: sup_fun_eq sup_bool_eq)

lemma sup_Un_eq [pred_set_conv]: "sup (\<lambda>x. x \<in> R) (\<lambda>x. x \<in> S) = (\<lambda>x. x \<in> R \<union> S)"
  by (simp add: expand_fun_eq)

lemma sup_Un_eq2 [pred_set_conv]: "sup (\<lambda>x y. (x, y) \<in> R) (\<lambda>x y. (x, y) \<in> S) = (\<lambda>x y. (x, y) \<in> R \<union> S)"
  by (simp add: expand_fun_eq)

lemma sup1I1 [elim?]: "A x \<Longrightarrow> sup A B x"
  by simp

lemma sup2I1 [elim?]: "A x y \<Longrightarrow> sup A B x y"
  by simp

lemma sup1I2 [elim?]: "B x \<Longrightarrow> sup A B x"
  by simp

lemma sup2I2 [elim?]: "B x y \<Longrightarrow> sup A B x y"
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


subsection {* Binary intersection *}

lemma inf1_iff [simp]: "inf A B x \<longleftrightarrow> A x \<and> B x"
  by (simp add: inf_fun_eq inf_bool_eq)

lemma inf2_iff [simp]: "inf A B x y \<longleftrightarrow> A x y \<and> B x y"
  by (simp add: inf_fun_eq inf_bool_eq)

lemma inf_Int_eq [pred_set_conv]: "inf (\<lambda>x. x \<in> R) (\<lambda>x. x \<in> S) = (\<lambda>x. x \<in> R \<inter> S)"
  by (simp add: expand_fun_eq)

lemma inf_Int_eq2 [pred_set_conv]: "inf (\<lambda>x y. (x, y) \<in> R) (\<lambda>x y. (x, y) \<in> S) = (\<lambda>x y. (x, y) \<in> R \<inter> S)"
  by (simp add: expand_fun_eq)

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


subsection {* Unions of families *}

lemma SUP1_iff [simp]: "(SUP x:A. B x) b = (EX x:A. B x b)"
  by (simp add: SUPR_def Sup_fun_def Sup_bool_def) blast

lemma SUP2_iff [simp]: "(SUP x:A. B x) b c = (EX x:A. B x b c)"
  by (simp add: SUPR_def Sup_fun_def Sup_bool_def) blast

lemma SUP1_I [intro]: "a : A ==> B a b ==> (SUP x:A. B x) b"
  by auto

lemma SUP2_I [intro]: "a : A ==> B a b c ==> (SUP x:A. B x) b c"
  by auto

lemma SUP1_E [elim!]: "(SUP x:A. B x) b ==> (!!x. x : A ==> B x b ==> R) ==> R"
  by auto

lemma SUP2_E [elim!]: "(SUP x:A. B x) b c ==> (!!x. x : A ==> B x b c ==> R) ==> R"
  by auto

lemma SUP_UN_eq: "(SUP i. (\<lambda>x. x \<in> r i)) = (\<lambda>x. x \<in> (UN i. r i))"
  by (simp add: expand_fun_eq)

lemma SUP_UN_eq2: "(SUP i. (\<lambda>x y. (x, y) \<in> r i)) = (\<lambda>x y. (x, y) \<in> (UN i. r i))"
  by (simp add: expand_fun_eq)


subsection {* Intersections of families *}

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

lemma INF_INT_eq: "(INF i. (\<lambda>x. x \<in> r i)) = (\<lambda>x. x \<in> (INT i. r i))"
  by (simp add: expand_fun_eq)

lemma INF_INT_eq2: "(INF i. (\<lambda>x y. (x, y) \<in> r i)) = (\<lambda>x y. (x, y) \<in> (INT i. r i))"
  by (simp add: expand_fun_eq)


subsection {* Composition of two relations *}

inductive
  pred_comp  :: "['b => 'c => bool, 'a => 'b => bool] => 'a => 'c => bool"
    (infixr "OO" 75)
  for r :: "'b => 'c => bool" and s :: "'a => 'b => bool"
where
  pred_compI [intro]: "s a b ==> r b c ==> (r OO s) a c"

inductive_cases pred_compE [elim!]: "(r OO s) a c"

lemma pred_comp_rel_comp_eq [pred_set_conv]:
  "((\<lambda>x y. (x, y) \<in> r) OO (\<lambda>x y. (x, y) \<in> s)) = (\<lambda>x y. (x, y) \<in> r O s)"
  by (auto simp add: expand_fun_eq elim: pred_compE)


subsection {* Converse *}

inductive
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
  "(\<lambda>x y. (x, y) \<in> r)^--1 = (\<lambda>x y. (x, y) \<in> r^-1)"
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

inductive
  DomainP :: "('a => 'b => bool) => 'a => bool"
  for r :: "'a => 'b => bool"
where
  DomainPI [intro]: "r a b ==> DomainP r a"

inductive_cases DomainPE [elim!]: "DomainP r a"

lemma DomainP_Domain_eq [pred_set_conv]: "DomainP (\<lambda>x y. (x, y) \<in> r) = (\<lambda>x. x \<in> Domain r)"
  by (blast intro!: Orderings.order_antisym predicate1I)


subsection {* Range *}

inductive
  RangeP :: "('a => 'b => bool) => 'b => bool"
  for r :: "'a => 'b => bool"
where
  RangePI [intro]: "r a b ==> RangeP r b"

inductive_cases RangePE [elim!]: "RangeP r b"

lemma RangeP_Range_eq [pred_set_conv]: "RangeP (\<lambda>x y. (x, y) \<in> r) = (\<lambda>x. x \<in> Range r)"
  by (blast intro!: Orderings.order_antisym predicate1I)


subsection {* Inverse image *}

definition
  inv_imagep :: "('b => 'b => bool) => ('a => 'b) => 'a => 'a => bool" where
  "inv_imagep r f == %x y. r (f x) (f y)"

lemma [pred_set_conv]: "inv_imagep (\<lambda>x y. (x, y) \<in> r) f = (\<lambda>x y. (x, y) \<in> inv_image r f)"
  by (simp add: inv_image_def inv_imagep_def)

lemma in_inv_imagep [simp]: "inv_imagep r f x y = r (f x) (f y)"
  by (simp add: inv_imagep_def)


subsection {* The Powerset operator *}

definition Powp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "Powp A == \<lambda>B. \<forall>x \<in> B. A x"

lemma Powp_Pow_eq [pred_set_conv]: "Powp (\<lambda>x. x \<in> A) = (\<lambda>x. x \<in> Pow A)"
  by (auto simp add: Powp_def expand_fun_eq)

lemmas Powp_mono [mono] = Pow_mono [to_pred pred_subset_eq]


subsection {* Properties of relations - predicate versions *}

abbreviation antisymP :: "('a => 'a => bool) => bool" where
  "antisymP r == antisym {(x, y). r x y}"

abbreviation transP :: "('a => 'a => bool) => bool" where
  "transP r == trans {(x, y). r x y}"

abbreviation single_valuedP :: "('a => 'b => bool) => bool" where
  "single_valuedP r == single_valued {(x, y). r x y}"

end
