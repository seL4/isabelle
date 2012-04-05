(*  Title:      HOL/Relation.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory; Stefan Berghofer, TU Muenchen
*)

header {* Relations – as sets of pairs, and binary predicates *}

theory Relation
imports Datatype Finite_Set
begin

text {* A preliminary: classical rules for reasoning on predicates *}

declare predicate1I [Pure.intro!, intro!]
declare predicate1D [Pure.dest, dest]
declare predicate2I [Pure.intro!, intro!]
declare predicate2D [Pure.dest, dest]
declare bot1E [elim!] 
declare bot2E [elim!]
declare top1I [intro!]
declare top2I [intro!]
declare inf1I [intro!]
declare inf2I [intro!]
declare inf1E [elim!]
declare inf2E [elim!]
declare sup1I1 [intro?]
declare sup2I1 [intro?]
declare sup1I2 [intro?]
declare sup2I2 [intro?]
declare sup1E [elim!]
declare sup2E [elim!]
declare sup1CI [intro!]
declare sup2CI [intro!]
declare INF1_I [intro!]
declare INF2_I [intro!]
declare INF1_D [elim]
declare INF2_D [elim]
declare INF1_E [elim]
declare INF2_E [elim]
declare SUP1_I [intro]
declare SUP2_I [intro]
declare SUP1_E [elim!]
declare SUP2_E [elim!]

subsection {* Fundamental *}

subsubsection {* Relations as sets of pairs *}

type_synonym 'a rel = "('a * 'a) set"

lemma subrelI: -- {* Version of @{thm [source] subsetI} for binary relations *}
  "(\<And>x y. (x, y) \<in> r \<Longrightarrow> (x, y) \<in> s) \<Longrightarrow> r \<subseteq> s"
  by auto

lemma lfp_induct2: -- {* Version of @{thm [source] lfp_induct} for binary relations *}
  "(a, b) \<in> lfp f \<Longrightarrow> mono f \<Longrightarrow>
    (\<And>a b. (a, b) \<in> f (lfp f \<inter> {(x, y). P x y}) \<Longrightarrow> P a b) \<Longrightarrow> P a b"
  using lfp_induct_set [of "(a, b)" f "prod_case P"] by auto


subsubsection {* Conversions between set and predicate relations *}

lemma pred_equals_eq [pred_set_conv]: "(\<lambda>x. x \<in> R) = (\<lambda>x. x \<in> S) \<longleftrightarrow> R = S"
  by (simp add: set_eq_iff fun_eq_iff)

lemma pred_equals_eq2 [pred_set_conv]: "(\<lambda>x y. (x, y) \<in> R) = (\<lambda>x y. (x, y) \<in> S) \<longleftrightarrow> R = S"
  by (simp add: set_eq_iff fun_eq_iff)

lemma pred_subset_eq [pred_set_conv]: "(\<lambda>x. x \<in> R) \<le> (\<lambda>x. x \<in> S) \<longleftrightarrow> R \<subseteq> S"
  by (simp add: subset_iff le_fun_def)

lemma pred_subset_eq2 [pred_set_conv]: "(\<lambda>x y. (x, y) \<in> R) \<le> (\<lambda>x y. (x, y) \<in> S) \<longleftrightarrow> R \<subseteq> S"
  by (simp add: subset_iff le_fun_def)

lemma bot_empty_eq [pred_set_conv]: "\<bottom> = (\<lambda>x. x \<in> {})"
  by (auto simp add: fun_eq_iff)

lemma bot_empty_eq2 [pred_set_conv]: "\<bottom> = (\<lambda>x y. (x, y) \<in> {})"
  by (auto simp add: fun_eq_iff)

lemma top_empty_eq [pred_set_conv]: "\<top> = (\<lambda>x. x \<in> UNIV)"
  by (auto simp add: fun_eq_iff)

lemma top_empty_eq2 [pred_set_conv]: "\<top> = (\<lambda>x y. (x, y) \<in> UNIV)"
  by (auto simp add: fun_eq_iff)

lemma inf_Int_eq [pred_set_conv]: "(\<lambda>x. x \<in> R) \<sqinter> (\<lambda>x. x \<in> S) = (\<lambda>x. x \<in> R \<inter> S)"
  by (simp add: inf_fun_def)

lemma inf_Int_eq2 [pred_set_conv]: "(\<lambda>x y. (x, y) \<in> R) \<sqinter> (\<lambda>x y. (x, y) \<in> S) = (\<lambda>x y. (x, y) \<in> R \<inter> S)"
  by (simp add: inf_fun_def)

lemma sup_Un_eq [pred_set_conv]: "(\<lambda>x. x \<in> R) \<squnion> (\<lambda>x. x \<in> S) = (\<lambda>x. x \<in> R \<union> S)"
  by (simp add: sup_fun_def)

lemma sup_Un_eq2 [pred_set_conv]: "(\<lambda>x y. (x, y) \<in> R) \<squnion> (\<lambda>x y. (x, y) \<in> S) = (\<lambda>x y. (x, y) \<in> R \<union> S)"
  by (simp add: sup_fun_def)

lemma INF_INT_eq [pred_set_conv]: "(\<Sqinter>i\<in>S. (\<lambda>x. x \<in> r i)) = (\<lambda>x. x \<in> (\<Inter>i\<in>S. r i))"
  by (simp add: fun_eq_iff)

lemma INF_INT_eq2 [pred_set_conv]: "(\<Sqinter>i\<in>S. (\<lambda>x y. (x, y) \<in> r i)) = (\<lambda>x y. (x, y) \<in> (\<Inter>i\<in>S. r i))"
  by (simp add: fun_eq_iff)

lemma SUP_UN_eq [pred_set_conv]: "(\<Squnion>i\<in>S. (\<lambda>x. x \<in> r i)) = (\<lambda>x. x \<in> (\<Union>i\<in>S. r i))"
  by (simp add: fun_eq_iff)

lemma SUP_UN_eq2 [pred_set_conv]: "(\<Squnion>i\<in>S. (\<lambda>x y. (x, y) \<in> r i)) = (\<lambda>x y. (x, y) \<in> (\<Union>i\<in>S. r i))"
  by (simp add: fun_eq_iff)

lemma Inf_INT_eq [pred_set_conv]: "\<Sqinter>S = (\<lambda>x. x \<in> INTER S Collect)"
  by (simp add: fun_eq_iff)

lemma INF_Int_eq [pred_set_conv]: "(\<Sqinter>i\<in>S. (\<lambda>x. x \<in> i)) = (\<lambda>x. x \<in> \<Inter>S)"
  by (simp add: fun_eq_iff)

lemma Inf_INT_eq2 [pred_set_conv]: "\<Sqinter>S = (\<lambda>x y. (x, y) \<in> INTER (prod_case ` S) Collect)"
  by (simp add: fun_eq_iff)

lemma INF_Int_eq2 [pred_set_conv]: "(\<Sqinter>i\<in>S. (\<lambda>x y. (x, y) \<in> i)) = (\<lambda>x y. (x, y) \<in> \<Inter>S)"
  by (simp add: fun_eq_iff)

lemma Sup_SUP_eq [pred_set_conv]: "\<Squnion>S = (\<lambda>x. x \<in> UNION S Collect)"
  by (simp add: fun_eq_iff)

lemma SUP_Sup_eq [pred_set_conv]: "(\<Squnion>i\<in>S. (\<lambda>x. x \<in> i)) = (\<lambda>x. x \<in> \<Union>S)"
  by (simp add: fun_eq_iff)

lemma Sup_SUP_eq2 [pred_set_conv]: "\<Squnion>S = (\<lambda>x y. (x, y) \<in> UNION (prod_case ` S) Collect)"
  by (simp add: fun_eq_iff)

lemma SUP_Sup_eq2 [pred_set_conv]: "(\<Squnion>i\<in>S. (\<lambda>x y. (x, y) \<in> i)) = (\<lambda>x y. (x, y) \<in> \<Union>S)"
  by (simp add: fun_eq_iff)


subsection {* Properties of relations *}

subsubsection {* Reflexivity *}

definition refl_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
where
  "refl_on A r \<longleftrightarrow> r \<subseteq> A \<times> A \<and> (\<forall>x\<in>A. (x, x) \<in> r)"

abbreviation refl :: "'a rel \<Rightarrow> bool"
where -- {* reflexivity over a type *}
  "refl \<equiv> refl_on UNIV"

definition reflp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "reflp r \<longleftrightarrow> (\<forall>x. r x x)"

lemma reflp_refl_eq [pred_set_conv]:
  "reflp (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> refl r" 
  by (simp add: refl_on_def reflp_def)

lemma refl_onI: "r \<subseteq> A \<times> A ==> (!!x. x : A ==> (x, x) : r) ==> refl_on A r"
  by (unfold refl_on_def) (iprover intro!: ballI)

lemma refl_onD: "refl_on A r ==> a : A ==> (a, a) : r"
  by (unfold refl_on_def) blast

lemma refl_onD1: "refl_on A r ==> (x, y) : r ==> x : A"
  by (unfold refl_on_def) blast

lemma refl_onD2: "refl_on A r ==> (x, y) : r ==> y : A"
  by (unfold refl_on_def) blast

lemma reflpI:
  "(\<And>x. r x x) \<Longrightarrow> reflp r"
  by (auto intro: refl_onI simp add: reflp_def)

lemma reflpE:
  assumes "reflp r"
  obtains "r x x"
  using assms by (auto dest: refl_onD simp add: reflp_def)

lemma refl_on_Int: "refl_on A r ==> refl_on B s ==> refl_on (A \<inter> B) (r \<inter> s)"
  by (unfold refl_on_def) blast

lemma reflp_inf:
  "reflp r \<Longrightarrow> reflp s \<Longrightarrow> reflp (r \<sqinter> s)"
  by (auto intro: reflpI elim: reflpE)

lemma refl_on_Un: "refl_on A r ==> refl_on B s ==> refl_on (A \<union> B) (r \<union> s)"
  by (unfold refl_on_def) blast

lemma reflp_sup:
  "reflp r \<Longrightarrow> reflp s \<Longrightarrow> reflp (r \<squnion> s)"
  by (auto intro: reflpI elim: reflpE)

lemma refl_on_INTER:
  "ALL x:S. refl_on (A x) (r x) ==> refl_on (INTER S A) (INTER S r)"
  by (unfold refl_on_def) fast

lemma refl_on_UNION:
  "ALL x:S. refl_on (A x) (r x) \<Longrightarrow> refl_on (UNION S A) (UNION S r)"
  by (unfold refl_on_def) blast

lemma refl_on_empty [simp]: "refl_on {} {}"
  by (simp add:refl_on_def)

lemma refl_on_def' [nitpick_unfold, code]:
  "refl_on A r \<longleftrightarrow> (\<forall>(x, y) \<in> r. x \<in> A \<and> y \<in> A) \<and> (\<forall>x \<in> A. (x, x) \<in> r)"
  by (auto intro: refl_onI dest: refl_onD refl_onD1 refl_onD2)


subsubsection {* Irreflexivity *}

definition irrefl :: "'a rel \<Rightarrow> bool"
where
  "irrefl r \<longleftrightarrow> (\<forall>x. (x, x) \<notin> r)"

lemma irrefl_distinct [code]:
  "irrefl r \<longleftrightarrow> (\<forall>(x, y) \<in> r. x \<noteq> y)"
  by (auto simp add: irrefl_def)


subsubsection {* Symmetry *}

definition sym :: "'a rel \<Rightarrow> bool"
where
  "sym r \<longleftrightarrow> (\<forall>x y. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r)"

definition symp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "symp r \<longleftrightarrow> (\<forall>x y. r x y \<longrightarrow> r y x)"

lemma symp_sym_eq [pred_set_conv]:
  "symp (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> sym r" 
  by (simp add: sym_def symp_def)

lemma symI:
  "(\<And>a b. (a, b) \<in> r \<Longrightarrow> (b, a) \<in> r) \<Longrightarrow> sym r"
  by (unfold sym_def) iprover

lemma sympI:
  "(\<And>a b. r a b \<Longrightarrow> r b a) \<Longrightarrow> symp r"
  by (fact symI [to_pred])

lemma symE:
  assumes "sym r" and "(b, a) \<in> r"
  obtains "(a, b) \<in> r"
  using assms by (simp add: sym_def)

lemma sympE:
  assumes "symp r" and "r b a"
  obtains "r a b"
  using assms by (rule symE [to_pred])

lemma symD:
  assumes "sym r" and "(b, a) \<in> r"
  shows "(a, b) \<in> r"
  using assms by (rule symE)

lemma sympD:
  assumes "symp r" and "r b a"
  shows "r a b"
  using assms by (rule symD [to_pred])

lemma sym_Int:
  "sym r \<Longrightarrow> sym s \<Longrightarrow> sym (r \<inter> s)"
  by (fast intro: symI elim: symE)

lemma symp_inf:
  "symp r \<Longrightarrow> symp s \<Longrightarrow> symp (r \<sqinter> s)"
  by (fact sym_Int [to_pred])

lemma sym_Un:
  "sym r \<Longrightarrow> sym s \<Longrightarrow> sym (r \<union> s)"
  by (fast intro: symI elim: symE)

lemma symp_sup:
  "symp r \<Longrightarrow> symp s \<Longrightarrow> symp (r \<squnion> s)"
  by (fact sym_Un [to_pred])

lemma sym_INTER:
  "\<forall>x\<in>S. sym (r x) \<Longrightarrow> sym (INTER S r)"
  by (fast intro: symI elim: symE)

lemma symp_INF:
  "\<forall>x\<in>S. symp (r x) \<Longrightarrow> symp (INFI S r)"
  by (fact sym_INTER [to_pred])

lemma sym_UNION:
  "\<forall>x\<in>S. sym (r x) \<Longrightarrow> sym (UNION S r)"
  by (fast intro: symI elim: symE)

lemma symp_SUP:
  "\<forall>x\<in>S. symp (r x) \<Longrightarrow> symp (SUPR S r)"
  by (fact sym_UNION [to_pred])


subsubsection {* Antisymmetry *}

definition antisym :: "'a rel \<Rightarrow> bool"
where
  "antisym r \<longleftrightarrow> (\<forall>x y. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r \<longrightarrow> x = y)"

abbreviation antisymP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "antisymP r \<equiv> antisym {(x, y). r x y}"

lemma antisymI:
  "(!!x y. (x, y) : r ==> (y, x) : r ==> x=y) ==> antisym r"
  by (unfold antisym_def) iprover

lemma antisymD: "antisym r ==> (a, b) : r ==> (b, a) : r ==> a = b"
  by (unfold antisym_def) iprover

lemma antisym_subset: "r \<subseteq> s ==> antisym s ==> antisym r"
  by (unfold antisym_def) blast

lemma antisym_empty [simp]: "antisym {}"
  by (unfold antisym_def) blast


subsubsection {* Transitivity *}

definition trans :: "'a rel \<Rightarrow> bool"
where
  "trans r \<longleftrightarrow> (\<forall>x y z. (x, y) \<in> r \<longrightarrow> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r)"

definition transp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "transp r \<longleftrightarrow> (\<forall>x y z. r x y \<longrightarrow> r y z \<longrightarrow> r x z)"

lemma transp_trans_eq [pred_set_conv]:
  "transp (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> trans r" 
  by (simp add: trans_def transp_def)

abbreviation transP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where -- {* FIXME drop *}
  "transP r \<equiv> trans {(x, y). r x y}"

lemma transI:
  "(\<And>x y z. (x, y) \<in> r \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> (x, z) \<in> r) \<Longrightarrow> trans r"
  by (unfold trans_def) iprover

lemma transpI:
  "(\<And>x y z. r x y \<Longrightarrow> r y z \<Longrightarrow> r x z) \<Longrightarrow> transp r"
  by (fact transI [to_pred])

lemma transE:
  assumes "trans r" and "(x, y) \<in> r" and "(y, z) \<in> r"
  obtains "(x, z) \<in> r"
  using assms by (unfold trans_def) iprover

lemma transpE:
  assumes "transp r" and "r x y" and "r y z"
  obtains "r x z"
  using assms by (rule transE [to_pred])

lemma transD:
  assumes "trans r" and "(x, y) \<in> r" and "(y, z) \<in> r"
  shows "(x, z) \<in> r"
  using assms by (rule transE)

lemma transpD:
  assumes "transp r" and "r x y" and "r y z"
  shows "r x z"
  using assms by (rule transD [to_pred])

lemma trans_Int:
  "trans r \<Longrightarrow> trans s \<Longrightarrow> trans (r \<inter> s)"
  by (fast intro: transI elim: transE)

lemma transp_inf:
  "transp r \<Longrightarrow> transp s \<Longrightarrow> transp (r \<sqinter> s)"
  by (fact trans_Int [to_pred])

lemma trans_INTER:
  "\<forall>x\<in>S. trans (r x) \<Longrightarrow> trans (INTER S r)"
  by (fast intro: transI elim: transD)

(* FIXME thm trans_INTER [to_pred] *)

lemma trans_join [code]:
  "trans r \<longleftrightarrow> (\<forall>(x, y1) \<in> r. \<forall>(y2, z) \<in> r. y1 = y2 \<longrightarrow> (x, z) \<in> r)"
  by (auto simp add: trans_def)

lemma transp_trans:
  "transp r \<longleftrightarrow> trans {(x, y). r x y}"
  by (simp add: trans_def transp_def)


subsubsection {* Totality *}

definition total_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
where
  "total_on A r \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r)"

abbreviation "total \<equiv> total_on UNIV"

lemma total_on_empty [simp]: "total_on {} r"
  by (simp add: total_on_def)


subsubsection {* Single valued relations *}

definition single_valued :: "('a \<times> 'b) set \<Rightarrow> bool"
where
  "single_valued r \<longleftrightarrow> (\<forall>x y. (x, y) \<in> r \<longrightarrow> (\<forall>z. (x, z) \<in> r \<longrightarrow> y = z))"

abbreviation single_valuedP :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "single_valuedP r \<equiv> single_valued {(x, y). r x y}"

lemma single_valuedI:
  "ALL x y. (x,y):r --> (ALL z. (x,z):r --> y=z) ==> single_valued r"
  by (unfold single_valued_def)

lemma single_valuedD:
  "single_valued r ==> (x, y) : r ==> (x, z) : r ==> y = z"
  by (simp add: single_valued_def)

lemma single_valued_subset:
  "r \<subseteq> s ==> single_valued s ==> single_valued r"
  by (unfold single_valued_def) blast


subsection {* Relation operations *}

subsubsection {* The identity relation *}

definition Id :: "'a rel"
where
  "Id = {p. \<exists>x. p = (x, x)}"

lemma IdI [intro]: "(a, a) : Id"
  by (simp add: Id_def)

lemma IdE [elim!]: "p : Id ==> (!!x. p = (x, x) ==> P) ==> P"
  by (unfold Id_def) (iprover elim: CollectE)

lemma pair_in_Id_conv [iff]: "((a, b) : Id) = (a = b)"
  by (unfold Id_def) blast

lemma refl_Id: "refl Id"
  by (simp add: refl_on_def)

lemma antisym_Id: "antisym Id"
  -- {* A strange result, since @{text Id} is also symmetric. *}
  by (simp add: antisym_def)

lemma sym_Id: "sym Id"
  by (simp add: sym_def)

lemma trans_Id: "trans Id"
  by (simp add: trans_def)

lemma single_valued_Id [simp]: "single_valued Id"
  by (unfold single_valued_def) blast

lemma irrefl_diff_Id [simp]: "irrefl (r - Id)"
  by (simp add:irrefl_def)

lemma trans_diff_Id: "trans r \<Longrightarrow> antisym r \<Longrightarrow> trans (r - Id)"
  unfolding antisym_def trans_def by blast

lemma total_on_diff_Id [simp]: "total_on A (r - Id) = total_on A r"
  by (simp add: total_on_def)


subsubsection {* Diagonal: identity over a set *}

definition Id_on  :: "'a set \<Rightarrow> 'a rel"
where
  "Id_on A = (\<Union>x\<in>A. {(x, x)})"

lemma Id_on_empty [simp]: "Id_on {} = {}"
  by (simp add: Id_on_def) 

lemma Id_on_eqI: "a = b ==> a : A ==> (a, b) : Id_on A"
  by (simp add: Id_on_def)

lemma Id_onI [intro!,no_atp]: "a : A ==> (a, a) : Id_on A"
  by (rule Id_on_eqI) (rule refl)

lemma Id_onE [elim!]:
  "c : Id_on A ==> (!!x. x : A ==> c = (x, x) ==> P) ==> P"
  -- {* The general elimination rule. *}
  by (unfold Id_on_def) (iprover elim!: UN_E singletonE)

lemma Id_on_iff: "((x, y) : Id_on A) = (x = y & x : A)"
  by blast

lemma Id_on_def' [nitpick_unfold]:
  "Id_on {x. A x} = Collect (\<lambda>(x, y). x = y \<and> A x)"
  by auto

lemma Id_on_subset_Times: "Id_on A \<subseteq> A \<times> A"
  by blast

lemma refl_on_Id_on: "refl_on A (Id_on A)"
  by (rule refl_onI [OF Id_on_subset_Times Id_onI])

lemma antisym_Id_on [simp]: "antisym (Id_on A)"
  by (unfold antisym_def) blast

lemma sym_Id_on [simp]: "sym (Id_on A)"
  by (rule symI) clarify

lemma trans_Id_on [simp]: "trans (Id_on A)"
  by (fast intro: transI elim: transD)

lemma single_valued_Id_on [simp]: "single_valued (Id_on A)"
  by (unfold single_valued_def) blast


subsubsection {* Composition *}

inductive_set rel_comp  :: "('a \<times> 'b) set \<Rightarrow> ('b \<times> 'c) set \<Rightarrow> ('a \<times> 'c) set" (infixr "O" 75)
  for r :: "('a \<times> 'b) set" and s :: "('b \<times> 'c) set"
where
  rel_compI [intro]: "(a, b) \<in> r \<Longrightarrow> (b, c) \<in> s \<Longrightarrow> (a, c) \<in> r O s"

abbreviation pred_comp (infixr "OO" 75) where
  "pred_comp \<equiv> rel_compp"

lemmas pred_compI = rel_compp.intros

text {*
  For historic reasons, the elimination rules are not wholly corresponding.
  Feel free to consolidate this.
*}

inductive_cases rel_compEpair: "(a, c) \<in> r O s"
inductive_cases pred_compE [elim!]: "(r OO s) a c"

lemma rel_compE [elim!]: "xz \<in> r O s \<Longrightarrow>
  (\<And>x y z. xz = (x, z) \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, z) \<in> s  \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases xz) (simp, erule rel_compEpair, iprover)

lemmas pred_comp_rel_comp_eq = rel_compp_rel_comp_eq

lemma R_O_Id [simp]:
  "R O Id = R"
  by fast

lemma Id_O_R [simp]:
  "Id O R = R"
  by fast

lemma rel_comp_empty1 [simp]:
  "{} O R = {}"
  by blast

lemma pred_comp_bot1 [simp]:
  "\<bottom> OO R = \<bottom>"
  by (fact rel_comp_empty1 [to_pred])

lemma rel_comp_empty2 [simp]:
  "R O {} = {}"
  by blast

lemma pred_comp_bot2 [simp]:
  "R OO \<bottom> = \<bottom>"
  by (fact rel_comp_empty2 [to_pred])

lemma O_assoc:
  "(R O S) O T = R O (S O T)"
  by blast


lemma pred_comp_assoc:
  "(r OO s) OO t = r OO (s OO t)"
  by (fact O_assoc [to_pred])

lemma trans_O_subset:
  "trans r \<Longrightarrow> r O r \<subseteq> r"
  by (unfold trans_def) blast

lemma transp_pred_comp_less_eq:
  "transp r \<Longrightarrow> r OO r \<le> r "
  by (fact trans_O_subset [to_pred])

lemma rel_comp_mono:
  "r' \<subseteq> r \<Longrightarrow> s' \<subseteq> s \<Longrightarrow> r' O s' \<subseteq> r O s"
  by blast

lemma pred_comp_mono:
  "r' \<le> r \<Longrightarrow> s' \<le> s \<Longrightarrow> r' OO s' \<le> r OO s "
  by (fact rel_comp_mono [to_pred])

lemma rel_comp_subset_Sigma:
  "r \<subseteq> A \<times> B \<Longrightarrow> s \<subseteq> B \<times> C \<Longrightarrow> r O s \<subseteq> A \<times> C"
  by blast

lemma rel_comp_distrib [simp]:
  "R O (S \<union> T) = (R O S) \<union> (R O T)" 
  by auto

lemma pred_comp_distrib [simp]:
  "R OO (S \<squnion> T) = R OO S \<squnion> R OO T"
  by (fact rel_comp_distrib [to_pred])

lemma rel_comp_distrib2 [simp]:
  "(S \<union> T) O R = (S O R) \<union> (T O R)"
  by auto

lemma pred_comp_distrib2 [simp]:
  "(S \<squnion> T) OO R = S OO R \<squnion> T OO R"
  by (fact rel_comp_distrib2 [to_pred])

lemma rel_comp_UNION_distrib:
  "s O UNION I r = (\<Union>i\<in>I. s O r i) "
  by auto

(* FIXME thm rel_comp_UNION_distrib [to_pred] *)

lemma rel_comp_UNION_distrib2:
  "UNION I r O s = (\<Union>i\<in>I. r i O s) "
  by auto

(* FIXME thm rel_comp_UNION_distrib2 [to_pred] *)

lemma single_valued_rel_comp:
  "single_valued r \<Longrightarrow> single_valued s \<Longrightarrow> single_valued (r O s)"
  by (unfold single_valued_def) blast

lemma rel_comp_unfold:
  "r O s = {(x, z). \<exists>y. (x, y) \<in> r \<and> (y, z) \<in> s}"
  by (auto simp add: set_eq_iff)


subsubsection {* Converse *}

inductive_set converse :: "('a \<times> 'b) set \<Rightarrow> ('b \<times> 'a) set" ("(_^-1)" [1000] 999)
  for r :: "('a \<times> 'b) set"
where
  "(a, b) \<in> r \<Longrightarrow> (b, a) \<in> r^-1"

notation (xsymbols)
  converse  ("(_\<inverse>)" [1000] 999)

notation
  conversep ("(_^--1)" [1000] 1000)

notation (xsymbols)
  conversep  ("(_\<inverse>\<inverse>)" [1000] 1000)

lemma converseI [sym]:
  "(a, b) \<in> r \<Longrightarrow> (b, a) \<in> r\<inverse>"
  by (fact converse.intros)

lemma conversepI (* CANDIDATE [sym] *):
  "r a b \<Longrightarrow> r\<inverse>\<inverse> b a"
  by (fact conversep.intros)

lemma converseD [sym]:
  "(a, b) \<in> r\<inverse> \<Longrightarrow> (b, a) \<in> r"
  by (erule converse.cases) iprover

lemma conversepD (* CANDIDATE [sym] *):
  "r\<inverse>\<inverse> b a \<Longrightarrow> r a b"
  by (fact converseD [to_pred])

lemma converseE [elim!]:
  -- {* More general than @{text converseD}, as it ``splits'' the member of the relation. *}
  "yx \<in> r\<inverse> \<Longrightarrow> (\<And>x y. yx = (y, x) \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases yx) (simp, erule converse.cases, iprover)

lemmas conversepE [elim!] = conversep.cases

lemma converse_iff [iff]:
  "(a, b) \<in> r\<inverse> \<longleftrightarrow> (b, a) \<in> r"
  by (auto intro: converseI)

lemma conversep_iff [iff]:
  "r\<inverse>\<inverse> a b = r b a"
  by (fact converse_iff [to_pred])

lemma converse_converse [simp]:
  "(r\<inverse>)\<inverse> = r"
  by (simp add: set_eq_iff)

lemma conversep_conversep [simp]:
  "(r\<inverse>\<inverse>)\<inverse>\<inverse> = r"
  by (fact converse_converse [to_pred])

lemma converse_rel_comp: "(r O s)^-1 = s^-1 O r^-1"
  by blast

lemma converse_pred_comp: "(r OO s)^--1 = s^--1 OO r^--1"
  by (iprover intro: order_antisym conversepI pred_compI
    elim: pred_compE dest: conversepD)

lemma converse_Int: "(r \<inter> s)^-1 = r^-1 \<inter> s^-1"
  by blast

lemma converse_meet: "(r \<sqinter> s)^--1 = r^--1 \<sqinter> s^--1"
  by (simp add: inf_fun_def) (iprover intro: conversepI ext dest: conversepD)

lemma converse_Un: "(r \<union> s)^-1 = r^-1 \<union> s^-1"
  by blast

lemma converse_join: "(r \<squnion> s)^--1 = r^--1 \<squnion> s^--1"
  by (simp add: sup_fun_def) (iprover intro: conversepI ext dest: conversepD)

lemma converse_INTER: "(INTER S r)^-1 = (INT x:S. (r x)^-1)"
  by fast

lemma converse_UNION: "(UNION S r)^-1 = (UN x:S. (r x)^-1)"
  by blast

lemma converse_Id [simp]: "Id^-1 = Id"
  by blast

lemma converse_Id_on [simp]: "(Id_on A)^-1 = Id_on A"
  by blast

lemma refl_on_converse [simp]: "refl_on A (converse r) = refl_on A r"
  by (unfold refl_on_def) auto

lemma sym_converse [simp]: "sym (converse r) = sym r"
  by (unfold sym_def) blast

lemma antisym_converse [simp]: "antisym (converse r) = antisym r"
  by (unfold antisym_def) blast

lemma trans_converse [simp]: "trans (converse r) = trans r"
  by (unfold trans_def) blast

lemma sym_conv_converse_eq: "sym r = (r^-1 = r)"
  by (unfold sym_def) fast

lemma sym_Un_converse: "sym (r \<union> r^-1)"
  by (unfold sym_def) blast

lemma sym_Int_converse: "sym (r \<inter> r^-1)"
  by (unfold sym_def) blast

lemma total_on_converse [simp]: "total_on A (r^-1) = total_on A r"
  by (auto simp: total_on_def)

lemma finite_converse [iff]: "finite (r^-1) = finite r"
  apply (subgoal_tac "r^-1 = (%(x,y). (y,x))`r")
   apply simp
   apply (rule iffI)
    apply (erule finite_imageD [unfolded inj_on_def])
    apply (simp split add: split_split)
   apply (erule finite_imageI)
  apply (simp add: set_eq_iff image_def, auto)
  apply (rule bexI)
   prefer 2 apply assumption
  apply simp
  done

lemma conversep_noteq [simp]: "(op \<noteq>)^--1 = op \<noteq>"
  by (auto simp add: fun_eq_iff)

lemma conversep_eq [simp]: "(op =)^--1 = op ="
  by (auto simp add: fun_eq_iff)

lemma converse_unfold:
  "r\<inverse> = {(y, x). (x, y) \<in> r}"
  by (simp add: set_eq_iff)


subsubsection {* Domain, range and field *}

inductive_set Domain :: "('a \<times> 'b) set \<Rightarrow> 'a set"
  for r :: "('a \<times> 'b) set"
where
  DomainI [intro]: "(a, b) \<in> r \<Longrightarrow> a \<in> Domain r"

abbreviation (input) "DomainP \<equiv> Domainp"

lemmas DomainPI = Domainp.DomainI

inductive_cases DomainE [elim!]: "a \<in> Domain r"
inductive_cases DomainpE [elim!]: "Domainp r a"

inductive_set Range :: "('a \<times> 'b) set \<Rightarrow> 'b set"
  for r :: "('a \<times> 'b) set"
where
  RangeI [intro]: "(a, b) \<in> r \<Longrightarrow> b \<in> Range r"

abbreviation (input) "RangeP \<equiv> Rangep"

lemmas RangePI = Rangep.RangeI

inductive_cases RangeE [elim!]: "b \<in> Range r"
inductive_cases RangepE [elim!]: "Rangep r b"

definition Field :: "'a rel \<Rightarrow> 'a set"
where
  "Field r = Domain r \<union> Range r"

lemma Domain_fst [code]:
  "Domain r = fst ` r"
  by force

lemma Range_snd [code]:
  "Range r = snd ` r"
  by force

lemma fst_eq_Domain: "fst ` R = Domain R"
  by force

lemma snd_eq_Range: "snd ` R = Range R"
  by force

lemma Domain_empty [simp]: "Domain {} = {}"
  by auto

lemma Range_empty [simp]: "Range {} = {}"
  by auto

lemma Field_empty [simp]: "Field {} = {}"
  by (simp add: Field_def)

lemma Domain_empty_iff: "Domain r = {} \<longleftrightarrow> r = {}"
  by auto

lemma Range_empty_iff: "Range r = {} \<longleftrightarrow> r = {}"
  by auto

lemma Domain_insert [simp]: "Domain (insert (a, b) r) = insert a (Domain r)"
  by blast

lemma Range_insert [simp]: "Range (insert (a, b) r) = insert b (Range r)"
  by blast

lemma Field_insert [simp]: "Field (insert (a, b) r) = {a, b} \<union> Field r"
  by (auto simp add: Field_def)

lemma Domain_iff: "a \<in> Domain r \<longleftrightarrow> (\<exists>y. (a, y) \<in> r)"
  by blast

lemma Range_iff: "a \<in> Range r \<longleftrightarrow> (\<exists>y. (y, a) \<in> r)"
  by blast

lemma Domain_Id [simp]: "Domain Id = UNIV"
  by blast

lemma Range_Id [simp]: "Range Id = UNIV"
  by blast

lemma Domain_Id_on [simp]: "Domain (Id_on A) = A"
  by blast

lemma Range_Id_on [simp]: "Range (Id_on A) = A"
  by blast

lemma Domain_Un_eq: "Domain (A \<union> B) = Domain A \<union> Domain B"
  by blast

lemma Range_Un_eq: "Range (A \<union> B) = Range A \<union> Range B"
  by blast

lemma Field_Un [simp]: "Field (r \<union> s) = Field r \<union> Field s"
  by (auto simp: Field_def)

lemma Domain_Int_subset: "Domain (A \<inter> B) \<subseteq> Domain A \<inter> Domain B"
  by blast

lemma Range_Int_subset: "Range (A \<inter> B) \<subseteq> Range A \<inter> Range B"
  by blast

lemma Domain_Diff_subset: "Domain A - Domain B \<subseteq> Domain (A - B)"
  by blast

lemma Range_Diff_subset: "Range A - Range B \<subseteq> Range (A - B)"
  by blast

lemma Domain_Union: "Domain (\<Union>S) = (\<Union>A\<in>S. Domain A)"
  by blast

lemma Range_Union: "Range (\<Union>S) = (\<Union>A\<in>S. Range A)"
  by blast

lemma Field_Union [simp]: "Field (\<Union>R) = \<Union>(Field ` R)"
  by (auto simp: Field_def)

lemma Domain_converse [simp]: "Domain (r\<inverse>) = Range r"
  by auto

lemma Range_converse [simp]: "Range (r\<inverse>) = Domain r"
  by blast

lemma Field_converse [simp]: "Field (r\<inverse>) = Field r"
  by (auto simp: Field_def)

lemma Domain_Collect_split [simp]: "Domain {(x, y). P x y} = {x. EX y. P x y}"
  by auto

lemma Range_Collect_split [simp]: "Range {(x, y). P x y} = {y. EX x. P x y}"
  by auto

lemma finite_Domain: "finite r \<Longrightarrow> finite (Domain r)"
  by (induct set: finite) auto

lemma finite_Range: "finite r \<Longrightarrow> finite (Range r)"
  by (induct set: finite) auto

lemma finite_Field: "finite r \<Longrightarrow> finite (Field r)"
  by (simp add: Field_def finite_Domain finite_Range)

lemma Domain_mono: "r \<subseteq> s \<Longrightarrow> Domain r \<subseteq> Domain s"
  by blast

lemma Range_mono: "r \<subseteq> s \<Longrightarrow> Range r \<subseteq> Range s"
  by blast

lemma mono_Field: "r \<subseteq> s \<Longrightarrow> Field r \<subseteq> Field s"
  by (auto simp: Field_def Domain_def Range_def)

lemma Domain_unfold:
  "Domain r = {x. \<exists>y. (x, y) \<in> r}"
  by blast

lemma Domain_dprod [simp]: "Domain (dprod r s) = uprod (Domain r) (Domain s)"
  by auto

lemma Domain_dsum [simp]: "Domain (dsum r s) = usum (Domain r) (Domain s)"
  by auto


subsubsection {* Image of a set under a relation *}

definition Image :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set" (infixl "``" 90)
where
  "r `` s = {y. \<exists>x\<in>s. (x, y) \<in> r}"

declare Image_def [no_atp]

lemma Image_iff: "(b : r``A) = (EX x:A. (x, b) : r)"
  by (simp add: Image_def)

lemma Image_singleton: "r``{a} = {b. (a, b) : r}"
  by (simp add: Image_def)

lemma Image_singleton_iff [iff]: "(b : r``{a}) = ((a, b) : r)"
  by (rule Image_iff [THEN trans]) simp

lemma ImageI [intro,no_atp]: "(a, b) : r ==> a : A ==> b : r``A"
  by (unfold Image_def) blast

lemma ImageE [elim!]:
  "b : r `` A ==> (!!x. (x, b) : r ==> x : A ==> P) ==> P"
  by (unfold Image_def) (iprover elim!: CollectE bexE)

lemma rev_ImageI: "a : A ==> (a, b) : r ==> b : r `` A"
  -- {* This version's more effective when we already have the required @{text a} *}
  by blast

lemma Image_empty [simp]: "R``{} = {}"
  by blast

lemma Image_Id [simp]: "Id `` A = A"
  by blast

lemma Image_Id_on [simp]: "Id_on A `` B = A \<inter> B"
  by blast

lemma Image_Int_subset: "R `` (A \<inter> B) \<subseteq> R `` A \<inter> R `` B"
  by blast

lemma Image_Int_eq:
  "single_valued (converse R) ==> R `` (A \<inter> B) = R `` A \<inter> R `` B"
  by (simp add: single_valued_def, blast) 

lemma Image_Un: "R `` (A \<union> B) = R `` A \<union> R `` B"
  by blast

lemma Un_Image: "(R \<union> S) `` A = R `` A \<union> S `` A"
  by blast

lemma Image_subset: "r \<subseteq> A \<times> B ==> r``C \<subseteq> B"
  by (iprover intro!: subsetI elim!: ImageE dest!: subsetD SigmaD2)

lemma Image_eq_UN: "r``B = (\<Union>y\<in> B. r``{y})"
  -- {* NOT suitable for rewriting *}
  by blast

lemma Image_mono: "r' \<subseteq> r ==> A' \<subseteq> A ==> (r' `` A') \<subseteq> (r `` A)"
  by blast

lemma Image_UN: "(r `` (UNION A B)) = (\<Union>x\<in>A. r `` (B x))"
  by blast

lemma Image_INT_subset: "(r `` INTER A B) \<subseteq> (\<Inter>x\<in>A. r `` (B x))"
  by blast

text{*Converse inclusion requires some assumptions*}
lemma Image_INT_eq:
     "[|single_valued (r\<inverse>); A\<noteq>{}|] ==> r `` INTER A B = (\<Inter>x\<in>A. r `` B x)"
apply (rule equalityI)
 apply (rule Image_INT_subset) 
apply  (simp add: single_valued_def, blast)
done

lemma Image_subset_eq: "(r``A \<subseteq> B) = (A \<subseteq> - ((r^-1) `` (-B)))"
  by blast

lemma Image_Collect_split [simp]: "{(x, y). P x y} `` A = {y. EX x:A. P x y}"
  by auto


subsubsection {* Inverse image *}

definition inv_image :: "'b rel \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a rel"
where
  "inv_image r f = {(x, y). (f x, f y) \<in> r}"

definition inv_imagep :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "inv_imagep r f = (\<lambda>x y. r (f x) (f y))"

lemma [pred_set_conv]: "inv_imagep (\<lambda>x y. (x, y) \<in> r) f = (\<lambda>x y. (x, y) \<in> inv_image r f)"
  by (simp add: inv_image_def inv_imagep_def)

lemma sym_inv_image: "sym r ==> sym (inv_image r f)"
  by (unfold sym_def inv_image_def) blast

lemma trans_inv_image: "trans r ==> trans (inv_image r f)"
  apply (unfold trans_def inv_image_def)
  apply (simp (no_asm))
  apply blast
  done

lemma in_inv_image[simp]: "((x,y) : inv_image r f) = ((f x, f y) : r)"
  by (auto simp:inv_image_def)

lemma converse_inv_image[simp]: "(inv_image R f)^-1 = inv_image (R^-1) f"
  unfolding inv_image_def converse_unfold by auto

lemma in_inv_imagep [simp]: "inv_imagep r f x y = r (f x) (f y)"
  by (simp add: inv_imagep_def)


subsubsection {* Powerset *}

definition Powp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "Powp A = (\<lambda>B. \<forall>x \<in> B. A x)"

lemma Powp_Pow_eq [pred_set_conv]: "Powp (\<lambda>x. x \<in> A) = (\<lambda>x. x \<in> Pow A)"
  by (auto simp add: Powp_def fun_eq_iff)

lemmas Powp_mono [mono] = Pow_mono [to_pred]

end

