(*  Title:      HOL/Relation.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Stefan Berghofer, TU Muenchen
*)

section \<open>Relations -- as sets of pairs, and binary predicates\<close>

theory Relation
  imports Finite_Set
begin

text \<open>A preliminary: classical rules for reasoning on predicates\<close>

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
declare Inf1_I [intro!]
declare INF1_I [intro!]
declare Inf2_I [intro!]
declare INF2_I [intro!]
declare Inf1_D [elim]
declare INF1_D [elim]
declare Inf2_D [elim]
declare INF2_D [elim]
declare Inf1_E [elim]
declare INF1_E [elim]
declare Inf2_E [elim]
declare INF2_E [elim]
declare Sup1_I [intro]
declare SUP1_I [intro]
declare Sup2_I [intro]
declare SUP2_I [intro]
declare Sup1_E [elim!]
declare SUP1_E [elim!]
declare Sup2_E [elim!]
declare SUP2_E [elim!]


subsection \<open>Fundamental\<close>

subsubsection \<open>Relations as sets of pairs\<close>

type_synonym 'a rel = "('a \<times> 'a) set"

lemma subrelI: "(\<And>x y. (x, y) \<in> r \<Longrightarrow> (x, y) \<in> s) \<Longrightarrow> r \<subseteq> s"
  \<comment> \<open>Version of @{thm [source] subsetI} for binary relations\<close>
  by auto

lemma lfp_induct2:
  "(a, b) \<in> lfp f \<Longrightarrow> mono f \<Longrightarrow>
    (\<And>a b. (a, b) \<in> f (lfp f \<inter> {(x, y). P x y}) \<Longrightarrow> P a b) \<Longrightarrow> P a b"
  \<comment> \<open>Version of @{thm [source] lfp_induct} for binary relations\<close>
  using lfp_induct_set [of "(a, b)" f "case_prod P"] by auto


subsubsection \<open>Conversions between set and predicate relations\<close>

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

lemma Inf_INT_eq [pred_set_conv]: "\<Sqinter>S = (\<lambda>x. x \<in> (\<Inter>(Collect ` S)))"
  by (simp add: fun_eq_iff)

lemma INF_Int_eq [pred_set_conv]: "(\<Sqinter>i\<in>S. (\<lambda>x. x \<in> i)) = (\<lambda>x. x \<in> \<Inter>S)"
  by (simp add: fun_eq_iff)

lemma Inf_INT_eq2 [pred_set_conv]: "\<Sqinter>S = (\<lambda>x y. (x, y) \<in> (\<Inter>(Collect ` case_prod ` S)))"
  by (simp add: fun_eq_iff)

lemma INF_Int_eq2 [pred_set_conv]: "(\<Sqinter>i\<in>S. (\<lambda>x y. (x, y) \<in> i)) = (\<lambda>x y. (x, y) \<in> \<Inter>S)"
  by (simp add: fun_eq_iff)

lemma Sup_SUP_eq [pred_set_conv]: "\<Squnion>S = (\<lambda>x. x \<in> \<Union>(Collect ` S))"
  by (simp add: fun_eq_iff)

lemma SUP_Sup_eq [pred_set_conv]: "(\<Squnion>i\<in>S. (\<lambda>x. x \<in> i)) = (\<lambda>x. x \<in> \<Union>S)"
  by (simp add: fun_eq_iff)

lemma Sup_SUP_eq2 [pred_set_conv]: "\<Squnion>S = (\<lambda>x y. (x, y) \<in> (\<Union>(Collect ` case_prod ` S)))"
  by (simp add: fun_eq_iff)

lemma SUP_Sup_eq2 [pred_set_conv]: "(\<Squnion>i\<in>S. (\<lambda>x y. (x, y) \<in> i)) = (\<lambda>x y. (x, y) \<in> \<Union>S)"
  by (simp add: fun_eq_iff)


subsection \<open>Properties of relations\<close>

subsubsection \<open>Reflexivity\<close>

definition refl_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "refl_on A r \<longleftrightarrow> r \<subseteq> A \<times> A \<and> (\<forall>x\<in>A. (x, x) \<in> r)"

abbreviation refl :: "'a rel \<Rightarrow> bool" \<comment> \<open>reflexivity over a type\<close>
  where "refl \<equiv> refl_on UNIV"

definition reflp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "reflp r \<longleftrightarrow> (\<forall>x. r x x)"

lemma reflp_refl_eq [pred_set_conv]: "reflp (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> refl r"
  by (simp add: refl_on_def reflp_def)

lemma refl_onI [intro?]: "r \<subseteq> A \<times> A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> (x, x) \<in> r) \<Longrightarrow> refl_on A r"
  unfolding refl_on_def by (iprover intro!: ballI)

lemma refl_onD: "refl_on A r \<Longrightarrow> a \<in> A \<Longrightarrow> (a, a) \<in> r"
  unfolding refl_on_def by blast

lemma refl_onD1: "refl_on A r \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> x \<in> A"
  unfolding refl_on_def by blast

lemma refl_onD2: "refl_on A r \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> y \<in> A"
  unfolding refl_on_def by blast

lemma reflpI [intro?]: "(\<And>x. r x x) \<Longrightarrow> reflp r"
  by (auto intro: refl_onI simp add: reflp_def)

lemma reflpE:
  assumes "reflp r"
  obtains "r x x"
  using assms by (auto dest: refl_onD simp add: reflp_def)

lemma reflpD [dest?]:
  assumes "reflp r"
  shows "r x x"
  using assms by (auto elim: reflpE)

lemma refl_on_Int: "refl_on A r \<Longrightarrow> refl_on B s \<Longrightarrow> refl_on (A \<inter> B) (r \<inter> s)"
  unfolding refl_on_def by blast

lemma reflp_inf: "reflp r \<Longrightarrow> reflp s \<Longrightarrow> reflp (r \<sqinter> s)"
  by (auto intro: reflpI elim: reflpE)

lemma refl_on_Un: "refl_on A r \<Longrightarrow> refl_on B s \<Longrightarrow> refl_on (A \<union> B) (r \<union> s)"
  unfolding refl_on_def by blast

lemma reflp_sup: "reflp r \<Longrightarrow> reflp s \<Longrightarrow> reflp (r \<squnion> s)"
  by (auto intro: reflpI elim: reflpE)

lemma refl_on_INTER: "\<forall>x\<in>S. refl_on (A x) (r x) \<Longrightarrow> refl_on (\<Inter>(A ` S)) (\<Inter>(r ` S))"
  unfolding refl_on_def by fast

lemma refl_on_UNION: "\<forall>x\<in>S. refl_on (A x) (r x) \<Longrightarrow> refl_on (\<Union>(A ` S)) (\<Union>(r ` S))"
  unfolding refl_on_def by blast

lemma refl_on_empty [simp]: "refl_on {} {}"
  by (simp add: refl_on_def)

lemma refl_on_singleton [simp]: "refl_on {x} {(x, x)}"
by (blast intro: refl_onI)

lemma refl_on_def' [nitpick_unfold, code]:
  "refl_on A r \<longleftrightarrow> (\<forall>(x, y) \<in> r. x \<in> A \<and> y \<in> A) \<and> (\<forall>x \<in> A. (x, x) \<in> r)"
  by (auto intro: refl_onI dest: refl_onD refl_onD1 refl_onD2)

lemma reflp_equality [simp]: "reflp (=)"
  by (simp add: reflp_def)

lemma reflp_mono: "reflp R \<Longrightarrow> (\<And>x y. R x y \<longrightarrow> Q x y) \<Longrightarrow> reflp Q"
  by (auto intro: reflpI dest: reflpD)


subsubsection \<open>Irreflexivity\<close>

definition irrefl :: "'a rel \<Rightarrow> bool"
  where "irrefl r \<longleftrightarrow> (\<forall>a. (a, a) \<notin> r)"

definition irreflp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "irreflp R \<longleftrightarrow> (\<forall>a. \<not> R a a)"

lemma irreflp_irrefl_eq [pred_set_conv]: "irreflp (\<lambda>a b. (a, b) \<in> R) \<longleftrightarrow> irrefl R"
  by (simp add: irrefl_def irreflp_def)

lemma irreflI [intro?]: "(\<And>a. (a, a) \<notin> R) \<Longrightarrow> irrefl R"
  by (simp add: irrefl_def)

lemma irreflpI [intro?]: "(\<And>a. \<not> R a a) \<Longrightarrow> irreflp R"
  by (fact irreflI [to_pred])

lemma irrefl_distinct [code]: "irrefl r \<longleftrightarrow> (\<forall>(a, b) \<in> r. a \<noteq> b)"
  by (auto simp add: irrefl_def)


subsubsection \<open>Asymmetry\<close>

inductive asym :: "'a rel \<Rightarrow> bool"
  where asymI: "(\<And>a b. (a, b) \<in> R \<Longrightarrow> (b, a) \<notin> R) \<Longrightarrow> asym R"

inductive asymp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where asympI: "(\<And>a b. R a b \<Longrightarrow> \<not> R b a) \<Longrightarrow> asymp R"

lemma asymp_asym_eq [pred_set_conv]: "asymp (\<lambda>a b. (a, b) \<in> R) \<longleftrightarrow> asym R"
  by (auto intro!: asymI asympI elim: asym.cases asymp.cases simp add: irreflp_irrefl_eq)

lemma asymD: "\<lbrakk>asym R; (x,y) \<in> R\<rbrakk> \<Longrightarrow> (y,x) \<notin> R"
  by (simp add: asym.simps)

lemma asym_iff: "asym R \<longleftrightarrow> (\<forall>x y. (x,y) \<in> R \<longrightarrow> (y,x) \<notin> R)"
  by (blast intro: asymI dest: asymD)

subsubsection \<open>Symmetry\<close>

definition sym :: "'a rel \<Rightarrow> bool"
  where "sym r \<longleftrightarrow> (\<forall>x y. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r)"

definition symp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "symp r \<longleftrightarrow> (\<forall>x y. r x y \<longrightarrow> r y x)"

lemma symp_sym_eq [pred_set_conv]: "symp (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> sym r"
  by (simp add: sym_def symp_def)

lemma symI [intro?]: "(\<And>a b. (a, b) \<in> r \<Longrightarrow> (b, a) \<in> r) \<Longrightarrow> sym r"
  by (unfold sym_def) iprover

lemma sympI [intro?]: "(\<And>a b. r a b \<Longrightarrow> r b a) \<Longrightarrow> symp r"
  by (fact symI [to_pred])

lemma symE:
  assumes "sym r" and "(b, a) \<in> r"
  obtains "(a, b) \<in> r"
  using assms by (simp add: sym_def)

lemma sympE:
  assumes "symp r" and "r b a"
  obtains "r a b"
  using assms by (rule symE [to_pred])

lemma symD [dest?]:
  assumes "sym r" and "(b, a) \<in> r"
  shows "(a, b) \<in> r"
  using assms by (rule symE)

lemma sympD [dest?]:
  assumes "symp r" and "r b a"
  shows "r a b"
  using assms by (rule symD [to_pred])

lemma sym_Int: "sym r \<Longrightarrow> sym s \<Longrightarrow> sym (r \<inter> s)"
  by (fast intro: symI elim: symE)

lemma symp_inf: "symp r \<Longrightarrow> symp s \<Longrightarrow> symp (r \<sqinter> s)"
  by (fact sym_Int [to_pred])

lemma sym_Un: "sym r \<Longrightarrow> sym s \<Longrightarrow> sym (r \<union> s)"
  by (fast intro: symI elim: symE)

lemma symp_sup: "symp r \<Longrightarrow> symp s \<Longrightarrow> symp (r \<squnion> s)"
  by (fact sym_Un [to_pred])

lemma sym_INTER: "\<forall>x\<in>S. sym (r x) \<Longrightarrow> sym (\<Inter>(r ` S))"
  by (fast intro: symI elim: symE)

lemma symp_INF: "\<forall>x\<in>S. symp (r x) \<Longrightarrow> symp (\<Sqinter>(r ` S))"
  by (fact sym_INTER [to_pred])

lemma sym_UNION: "\<forall>x\<in>S. sym (r x) \<Longrightarrow> sym (\<Union>(r ` S))"
  by (fast intro: symI elim: symE)

lemma symp_SUP: "\<forall>x\<in>S. symp (r x) \<Longrightarrow> symp (\<Squnion>(r ` S))"
  by (fact sym_UNION [to_pred])


subsubsection \<open>Antisymmetry\<close>

definition antisym :: "'a rel \<Rightarrow> bool"
  where "antisym r \<longleftrightarrow> (\<forall>x y. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r \<longrightarrow> x = y)"

definition antisymp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "antisymp r \<longleftrightarrow> (\<forall>x y. r x y \<longrightarrow> r y x \<longrightarrow> x = y)"

lemma antisymp_antisym_eq [pred_set_conv]: "antisymp (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> antisym r"
  by (simp add: antisym_def antisymp_def)

lemma antisymI [intro?]:
  "(\<And>x y. (x, y) \<in> r \<Longrightarrow> (y, x) \<in> r \<Longrightarrow> x = y) \<Longrightarrow> antisym r"
  unfolding antisym_def by iprover

lemma antisympI [intro?]:
  "(\<And>x y. r x y \<Longrightarrow> r y x \<Longrightarrow> x = y) \<Longrightarrow> antisymp r"
  by (fact antisymI [to_pred])
    
lemma antisymD [dest?]:
  "antisym r \<Longrightarrow> (a, b) \<in> r \<Longrightarrow> (b, a) \<in> r \<Longrightarrow> a = b"
  unfolding antisym_def by iprover

lemma antisympD [dest?]:
  "antisymp r \<Longrightarrow> r a b \<Longrightarrow> r b a \<Longrightarrow> a = b"
  by (fact antisymD [to_pred])

lemma antisym_subset:
  "r \<subseteq> s \<Longrightarrow> antisym s \<Longrightarrow> antisym r"
  unfolding antisym_def by blast

lemma antisymp_less_eq:
  "r \<le> s \<Longrightarrow> antisymp s \<Longrightarrow> antisymp r"
  by (fact antisym_subset [to_pred])
    
lemma antisym_empty [simp]:
  "antisym {}"
  unfolding antisym_def by blast

lemma antisym_bot [simp]:
  "antisymp \<bottom>"
  by (fact antisym_empty [to_pred])
    
lemma antisymp_equality [simp]:
  "antisymp HOL.eq"
  by (auto intro: antisympI)

lemma antisym_singleton [simp]:
  "antisym {x}"
  by (blast intro: antisymI)


subsubsection \<open>Transitivity\<close>

definition trans :: "'a rel \<Rightarrow> bool"
  where "trans r \<longleftrightarrow> (\<forall>x y z. (x, y) \<in> r \<longrightarrow> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r)"

definition transp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "transp r \<longleftrightarrow> (\<forall>x y z. r x y \<longrightarrow> r y z \<longrightarrow> r x z)"

lemma transp_trans_eq [pred_set_conv]: "transp (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> trans r"
  by (simp add: trans_def transp_def)

lemma transI [intro?]: "(\<And>x y z. (x, y) \<in> r \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> (x, z) \<in> r) \<Longrightarrow> trans r"
  by (unfold trans_def) iprover

lemma transpI [intro?]: "(\<And>x y z. r x y \<Longrightarrow> r y z \<Longrightarrow> r x z) \<Longrightarrow> transp r"
  by (fact transI [to_pred])

lemma transE:
  assumes "trans r" and "(x, y) \<in> r" and "(y, z) \<in> r"
  obtains "(x, z) \<in> r"
  using assms by (unfold trans_def) iprover

lemma transpE:
  assumes "transp r" and "r x y" and "r y z"
  obtains "r x z"
  using assms by (rule transE [to_pred])

lemma transD [dest?]:
  assumes "trans r" and "(x, y) \<in> r" and "(y, z) \<in> r"
  shows "(x, z) \<in> r"
  using assms by (rule transE)

lemma transpD [dest?]:
  assumes "transp r" and "r x y" and "r y z"
  shows "r x z"
  using assms by (rule transD [to_pred])

lemma trans_Int: "trans r \<Longrightarrow> trans s \<Longrightarrow> trans (r \<inter> s)"
  by (fast intro: transI elim: transE)

lemma transp_inf: "transp r \<Longrightarrow> transp s \<Longrightarrow> transp (r \<sqinter> s)"
  by (fact trans_Int [to_pred])

lemma trans_INTER: "\<forall>x\<in>S. trans (r x) \<Longrightarrow> trans (\<Inter>(r ` S))"
  by (fast intro: transI elim: transD)

lemma transp_INF: "\<forall>x\<in>S. transp (r x) \<Longrightarrow> transp (\<Sqinter>(r ` S))"
  by (fact trans_INTER [to_pred])
    
lemma trans_join [code]: "trans r \<longleftrightarrow> (\<forall>(x, y1) \<in> r. \<forall>(y2, z) \<in> r. y1 = y2 \<longrightarrow> (x, z) \<in> r)"
  by (auto simp add: trans_def)

lemma transp_trans: "transp r \<longleftrightarrow> trans {(x, y). r x y}"
  by (simp add: trans_def transp_def)

lemma transp_equality [simp]: "transp (=)"
  by (auto intro: transpI)

lemma trans_empty [simp]: "trans {}"
  by (blast intro: transI)

lemma transp_empty [simp]: "transp (\<lambda>x y. False)"
  using trans_empty[to_pred] by (simp add: bot_fun_def)

lemma trans_singleton [simp]: "trans {(a, a)}"
  by (blast intro: transI)

lemma transp_singleton [simp]: "transp (\<lambda>x y. x = a \<and> y = a)"
  by (simp add: transp_def)

context preorder
begin

lemma transp_le[simp]: "transp (\<le>)"
by(auto simp add: transp_def intro: order_trans)

lemma transp_less[simp]: "transp (<)"
by(auto simp add: transp_def intro: less_trans)

lemma transp_ge[simp]: "transp (\<ge>)"
by(auto simp add: transp_def intro: order_trans)

lemma transp_gr[simp]: "transp (>)"
by(auto simp add: transp_def intro: less_trans)

end

subsubsection \<open>Totality\<close>

definition total_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "total_on A r \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r)"

lemma total_onI [intro?]:
  "(\<And>x y. \<lbrakk>x \<in> A; y \<in> A; x \<noteq> y\<rbrakk> \<Longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r) \<Longrightarrow> total_on A r"
  unfolding total_on_def by blast

abbreviation "total \<equiv> total_on UNIV"

lemma total_on_empty [simp]: "total_on {} r"
  by (simp add: total_on_def)

lemma total_on_singleton [simp]: "total_on {x} {(x, x)}"
  unfolding total_on_def by blast


subsubsection \<open>Single valued relations\<close>

definition single_valued :: "('a \<times> 'b) set \<Rightarrow> bool"
  where "single_valued r \<longleftrightarrow> (\<forall>x y. (x, y) \<in> r \<longrightarrow> (\<forall>z. (x, z) \<in> r \<longrightarrow> y = z))"

definition single_valuedp :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "single_valuedp r \<longleftrightarrow> (\<forall>x y. r x y \<longrightarrow> (\<forall>z. r x z \<longrightarrow> y = z))"

lemma single_valuedp_single_valued_eq [pred_set_conv]:
  "single_valuedp (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> single_valued r"
  by (simp add: single_valued_def single_valuedp_def)

lemma single_valuedp_iff_Uniq:
  "single_valuedp r \<longleftrightarrow> (\<forall>x. \<exists>\<^sub>\<le>\<^sub>1y. r x y)"
  unfolding Uniq_def single_valuedp_def by auto

lemma single_valuedI:
  "(\<And>x y. (x, y) \<in> r \<Longrightarrow> (\<And>z. (x, z) \<in> r \<Longrightarrow> y = z)) \<Longrightarrow> single_valued r"
  unfolding single_valued_def by blast

lemma single_valuedpI:
  "(\<And>x y. r x y \<Longrightarrow> (\<And>z. r x z \<Longrightarrow> y = z)) \<Longrightarrow> single_valuedp r"
  by (fact single_valuedI [to_pred])

lemma single_valuedD:
  "single_valued r \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (x, z) \<in> r \<Longrightarrow> y = z"
  by (simp add: single_valued_def)

lemma single_valuedpD:
  "single_valuedp r \<Longrightarrow> r x y \<Longrightarrow> r x z \<Longrightarrow> y = z"
  by (fact single_valuedD [to_pred])

lemma single_valued_empty [simp]:
  "single_valued {}"
  by (simp add: single_valued_def)

lemma single_valuedp_bot [simp]:
  "single_valuedp \<bottom>"
  by (fact single_valued_empty [to_pred])

lemma single_valued_subset:
  "r \<subseteq> s \<Longrightarrow> single_valued s \<Longrightarrow> single_valued r"
  unfolding single_valued_def by blast

lemma single_valuedp_less_eq:
  "r \<le> s \<Longrightarrow> single_valuedp s \<Longrightarrow> single_valuedp r"
  by (fact single_valued_subset [to_pred])


subsection \<open>Relation operations\<close>

subsubsection \<open>The identity relation\<close>

definition Id :: "'a rel"
  where "Id = {p. \<exists>x. p = (x, x)}"

lemma IdI [intro]: "(a, a) \<in> Id"
  by (simp add: Id_def)

lemma IdE [elim!]: "p \<in> Id \<Longrightarrow> (\<And>x. p = (x, x) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding Id_def by (iprover elim: CollectE)

lemma pair_in_Id_conv [iff]: "(a, b) \<in> Id \<longleftrightarrow> a = b"
  unfolding Id_def by blast

lemma refl_Id: "refl Id"
  by (simp add: refl_on_def)

lemma antisym_Id: "antisym Id"
  \<comment> \<open>A strange result, since \<open>Id\<close> is also symmetric.\<close>
  by (simp add: antisym_def)

lemma sym_Id: "sym Id"
  by (simp add: sym_def)

lemma trans_Id: "trans Id"
  by (simp add: trans_def)

lemma single_valued_Id [simp]: "single_valued Id"
  by (unfold single_valued_def) blast

lemma irrefl_diff_Id [simp]: "irrefl (r - Id)"
  by (simp add: irrefl_def)

lemma trans_diff_Id: "trans r \<Longrightarrow> antisym r \<Longrightarrow> trans (r - Id)"
  unfolding antisym_def trans_def by blast

lemma total_on_diff_Id [simp]: "total_on A (r - Id) = total_on A r"
  by (simp add: total_on_def)

lemma Id_fstsnd_eq: "Id = {x. fst x = snd x}"
  by force


subsubsection \<open>Diagonal: identity over a set\<close>

definition Id_on :: "'a set \<Rightarrow> 'a rel"
  where "Id_on A = (\<Union>x\<in>A. {(x, x)})"

lemma Id_on_empty [simp]: "Id_on {} = {}"
  by (simp add: Id_on_def)

lemma Id_on_eqI: "a = b \<Longrightarrow> a \<in> A \<Longrightarrow> (a, b) \<in> Id_on A"
  by (simp add: Id_on_def)

lemma Id_onI [intro!]: "a \<in> A \<Longrightarrow> (a, a) \<in> Id_on A"
  by (rule Id_on_eqI) (rule refl)

lemma Id_onE [elim!]: "c \<in> Id_on A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> c = (x, x) \<Longrightarrow> P) \<Longrightarrow> P"
  \<comment> \<open>The general elimination rule.\<close>
  unfolding Id_on_def by (iprover elim!: UN_E singletonE)

lemma Id_on_iff: "(x, y) \<in> Id_on A \<longleftrightarrow> x = y \<and> x \<in> A"
  by blast

lemma Id_on_def' [nitpick_unfold]: "Id_on {x. A x} = Collect (\<lambda>(x, y). x = y \<and> A x)"
  by auto

lemma Id_on_subset_Times: "Id_on A \<subseteq> A \<times> A"
  by blast

lemma refl_on_Id_on: "refl_on A (Id_on A)"
  by (rule refl_onI [OF Id_on_subset_Times Id_onI])

lemma antisym_Id_on [simp]: "antisym (Id_on A)"
  unfolding antisym_def by blast

lemma sym_Id_on [simp]: "sym (Id_on A)"
  by (rule symI) clarify

lemma trans_Id_on [simp]: "trans (Id_on A)"
  by (fast intro: transI elim: transD)

lemma single_valued_Id_on [simp]: "single_valued (Id_on A)"
  unfolding single_valued_def by blast


subsubsection \<open>Composition\<close>

inductive_set relcomp  :: "('a \<times> 'b) set \<Rightarrow> ('b \<times> 'c) set \<Rightarrow> ('a \<times> 'c) set"  (infixr "O" 75)
  for r :: "('a \<times> 'b) set" and s :: "('b \<times> 'c) set"
  where relcompI [intro]: "(a, b) \<in> r \<Longrightarrow> (b, c) \<in> s \<Longrightarrow> (a, c) \<in> r O s"

notation relcompp (infixr "OO" 75)

lemmas relcomppI = relcompp.intros

text \<open>
  For historic reasons, the elimination rules are not wholly corresponding.
  Feel free to consolidate this.
\<close>

inductive_cases relcompEpair: "(a, c) \<in> r O s"
inductive_cases relcomppE [elim!]: "(r OO s) a c"

lemma relcompE [elim!]: "xz \<in> r O s \<Longrightarrow>
  (\<And>x y z. xz = (x, z) \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, z) \<in> s  \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases xz)
  apply simp
  apply (erule relcompEpair)
  apply iprover
  done

lemma R_O_Id [simp]: "R O Id = R"
  by fast

lemma Id_O_R [simp]: "Id O R = R"
  by fast

lemma relcomp_empty1 [simp]: "{} O R = {}"
  by blast

lemma relcompp_bot1 [simp]: "\<bottom> OO R = \<bottom>"
  by (fact relcomp_empty1 [to_pred])

lemma relcomp_empty2 [simp]: "R O {} = {}"
  by blast

lemma relcompp_bot2 [simp]: "R OO \<bottom> = \<bottom>"
  by (fact relcomp_empty2 [to_pred])

lemma O_assoc: "(R O S) O T = R O (S O T)"
  by blast

lemma relcompp_assoc: "(r OO s) OO t = r OO (s OO t)"
  by (fact O_assoc [to_pred])

lemma trans_O_subset: "trans r \<Longrightarrow> r O r \<subseteq> r"
  by (unfold trans_def) blast

lemma transp_relcompp_less_eq: "transp r \<Longrightarrow> r OO r \<le> r "
  by (fact trans_O_subset [to_pred])

lemma relcomp_mono: "r' \<subseteq> r \<Longrightarrow> s' \<subseteq> s \<Longrightarrow> r' O s' \<subseteq> r O s"
  by blast

lemma relcompp_mono: "r' \<le> r \<Longrightarrow> s' \<le> s \<Longrightarrow> r' OO s' \<le> r OO s "
  by (fact relcomp_mono [to_pred])

lemma relcomp_subset_Sigma: "r \<subseteq> A \<times> B \<Longrightarrow> s \<subseteq> B \<times> C \<Longrightarrow> r O s \<subseteq> A \<times> C"
  by blast

lemma relcomp_distrib [simp]: "R O (S \<union> T) = (R O S) \<union> (R O T)"
  by auto

lemma relcompp_distrib [simp]: "R OO (S \<squnion> T) = R OO S \<squnion> R OO T"
  by (fact relcomp_distrib [to_pred])

lemma relcomp_distrib2 [simp]: "(S \<union> T) O R = (S O R) \<union> (T O R)"
  by auto

lemma relcompp_distrib2 [simp]: "(S \<squnion> T) OO R = S OO R \<squnion> T OO R"
  by (fact relcomp_distrib2 [to_pred])

lemma relcomp_UNION_distrib: "s O \<Union>(r ` I) = (\<Union>i\<in>I. s O r i) "
  by auto

lemma relcompp_SUP_distrib: "s OO \<Squnion>(r ` I) = (\<Squnion>i\<in>I. s OO r i)"
  by (fact relcomp_UNION_distrib [to_pred])
    
lemma relcomp_UNION_distrib2: "\<Union>(r ` I) O s = (\<Union>i\<in>I. r i O s) "
  by auto

lemma relcompp_SUP_distrib2: "\<Squnion>(r ` I) OO s = (\<Squnion>i\<in>I. r i OO s)"
  by (fact relcomp_UNION_distrib2 [to_pred])
    
lemma single_valued_relcomp: "single_valued r \<Longrightarrow> single_valued s \<Longrightarrow> single_valued (r O s)"
  unfolding single_valued_def by blast

lemma relcomp_unfold: "r O s = {(x, z). \<exists>y. (x, y) \<in> r \<and> (y, z) \<in> s}"
  by (auto simp add: set_eq_iff)

lemma relcompp_apply: "(R OO S) a c \<longleftrightarrow> (\<exists>b. R a b \<and> S b c)"
  unfolding relcomp_unfold [to_pred] ..

lemma eq_OO: "(=) OO R = R"
  by blast

lemma OO_eq: "R OO (=) = R"
  by blast


subsubsection \<open>Converse\<close>

inductive_set converse :: "('a \<times> 'b) set \<Rightarrow> ('b \<times> 'a) set"  ("(_\<inverse>)" [1000] 999)
  for r :: "('a \<times> 'b) set"
  where "(a, b) \<in> r \<Longrightarrow> (b, a) \<in> r\<inverse>"

notation conversep  ("(_\<inverse>\<inverse>)" [1000] 1000)

notation (ASCII)
  converse  ("(_^-1)" [1000] 999) and
  conversep ("(_^--1)" [1000] 1000)

lemma converseI [sym]: "(a, b) \<in> r \<Longrightarrow> (b, a) \<in> r\<inverse>"
  by (fact converse.intros)

lemma conversepI (* CANDIDATE [sym] *): "r a b \<Longrightarrow> r\<inverse>\<inverse> b a"
  by (fact conversep.intros)

lemma converseD [sym]: "(a, b) \<in> r\<inverse> \<Longrightarrow> (b, a) \<in> r"
  by (erule converse.cases) iprover

lemma conversepD (* CANDIDATE [sym] *): "r\<inverse>\<inverse> b a \<Longrightarrow> r a b"
  by (fact converseD [to_pred])

lemma converseE [elim!]: "yx \<in> r\<inverse> \<Longrightarrow> (\<And>x y. yx = (y, x) \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> P) \<Longrightarrow> P"
  \<comment> \<open>More general than \<open>converseD\<close>, as it ``splits'' the member of the relation.\<close>
  apply (cases yx)
  apply simp
  apply (erule converse.cases)
  apply iprover
  done

lemmas conversepE [elim!] = conversep.cases

lemma converse_iff [iff]: "(a, b) \<in> r\<inverse> \<longleftrightarrow> (b, a) \<in> r"
  by (auto intro: converseI)

lemma conversep_iff [iff]: "r\<inverse>\<inverse> a b = r b a"
  by (fact converse_iff [to_pred])

lemma converse_converse [simp]: "(r\<inverse>)\<inverse> = r"
  by (simp add: set_eq_iff)

lemma conversep_conversep [simp]: "(r\<inverse>\<inverse>)\<inverse>\<inverse> = r"
  by (fact converse_converse [to_pred])

lemma converse_empty[simp]: "{}\<inverse> = {}"
  by auto

lemma converse_UNIV[simp]: "UNIV\<inverse> = UNIV"
  by auto

lemma converse_relcomp: "(r O s)\<inverse> = s\<inverse> O r\<inverse>"
  by blast

lemma converse_relcompp: "(r OO s)\<inverse>\<inverse> = s\<inverse>\<inverse> OO r\<inverse>\<inverse>"
  by (iprover intro: order_antisym conversepI relcomppI elim: relcomppE dest: conversepD)

lemma converse_Int: "(r \<inter> s)\<inverse> = r\<inverse> \<inter> s\<inverse>"
  by blast

lemma converse_meet: "(r \<sqinter> s)\<inverse>\<inverse> = r\<inverse>\<inverse> \<sqinter> s\<inverse>\<inverse>"
  by (simp add: inf_fun_def) (iprover intro: conversepI ext dest: conversepD)

lemma converse_Un: "(r \<union> s)\<inverse> = r\<inverse> \<union> s\<inverse>"
  by blast

lemma converse_join: "(r \<squnion> s)\<inverse>\<inverse> = r\<inverse>\<inverse> \<squnion> s\<inverse>\<inverse>"
  by (simp add: sup_fun_def) (iprover intro: conversepI ext dest: conversepD)

lemma converse_INTER: "(\<Inter>(r ` S))\<inverse> = (\<Inter>x\<in>S. (r x)\<inverse>)"
  by fast

lemma converse_UNION: "(\<Union>(r ` S))\<inverse> = (\<Union>x\<in>S. (r x)\<inverse>)"
  by blast

lemma converse_mono[simp]: "r\<inverse> \<subseteq> s \<inverse> \<longleftrightarrow> r \<subseteq> s"
  by auto

lemma conversep_mono[simp]: "r\<inverse>\<inverse> \<le> s \<inverse>\<inverse> \<longleftrightarrow> r \<le> s"
  by (fact converse_mono[to_pred])

lemma converse_inject[simp]: "r\<inverse> = s \<inverse> \<longleftrightarrow> r = s"
  by auto

lemma conversep_inject[simp]: "r\<inverse>\<inverse> = s \<inverse>\<inverse> \<longleftrightarrow> r = s"
  by (fact converse_inject[to_pred])

lemma converse_subset_swap: "r \<subseteq> s \<inverse> \<longleftrightarrow> r \<inverse> \<subseteq> s"
  by auto

lemma conversep_le_swap: "r \<le> s \<inverse>\<inverse> \<longleftrightarrow> r \<inverse>\<inverse> \<le> s"
  by (fact converse_subset_swap[to_pred])

lemma converse_Id [simp]: "Id\<inverse> = Id"
  by blast

lemma converse_Id_on [simp]: "(Id_on A)\<inverse> = Id_on A"
  by blast

lemma refl_on_converse [simp]: "refl_on A (converse r) = refl_on A r"
  by (auto simp: refl_on_def)

lemma sym_converse [simp]: "sym (converse r) = sym r"
  unfolding sym_def by blast

lemma antisym_converse [simp]: "antisym (converse r) = antisym r"
  unfolding antisym_def by blast

lemma trans_converse [simp]: "trans (converse r) = trans r"
  unfolding trans_def by blast

lemma sym_conv_converse_eq: "sym r \<longleftrightarrow> r\<inverse> = r"
  unfolding sym_def by fast

lemma sym_Un_converse: "sym (r \<union> r\<inverse>)"
  unfolding sym_def by blast

lemma sym_Int_converse: "sym (r \<inter> r\<inverse>)"
  unfolding sym_def by blast

lemma total_on_converse [simp]: "total_on A (r\<inverse>) = total_on A r"
  by (auto simp: total_on_def)

lemma finite_converse [iff]: "finite (r\<inverse>) = finite r"
unfolding converse_def conversep_iff using [[simproc add: finite_Collect]]
by (auto elim: finite_imageD simp: inj_on_def)

lemma card_inverse[simp]: "card (R\<inverse>) = card R"
proof -
  have *: "\<And>R. prod.swap ` R = R\<inverse>" by auto
  {
    assume "\<not>finite R"
    hence ?thesis
      by auto
  } moreover {
    assume "finite R"
    with card_image_le[of R prod.swap] card_image_le[of "R\<inverse>" prod.swap]
    have ?thesis by (auto simp: *)
  } ultimately show ?thesis by blast
qed  

lemma conversep_noteq [simp]: "(\<noteq>)\<inverse>\<inverse> = (\<noteq>)"
  by (auto simp add: fun_eq_iff)

lemma conversep_eq [simp]: "(=)\<inverse>\<inverse> = (=)"
  by (auto simp add: fun_eq_iff)

lemma converse_unfold [code]: "r\<inverse> = {(y, x). (x, y) \<in> r}"
  by (simp add: set_eq_iff)


subsubsection \<open>Domain, range and field\<close>

inductive_set Domain :: "('a \<times> 'b) set \<Rightarrow> 'a set" for r :: "('a \<times> 'b) set"
  where DomainI [intro]: "(a, b) \<in> r \<Longrightarrow> a \<in> Domain r"

lemmas DomainPI = Domainp.DomainI

inductive_cases DomainE [elim!]: "a \<in> Domain r"
inductive_cases DomainpE [elim!]: "Domainp r a"

inductive_set Range :: "('a \<times> 'b) set \<Rightarrow> 'b set" for r :: "('a \<times> 'b) set"
  where RangeI [intro]: "(a, b) \<in> r \<Longrightarrow> b \<in> Range r"

lemmas RangePI = Rangep.RangeI

inductive_cases RangeE [elim!]: "b \<in> Range r"
inductive_cases RangepE [elim!]: "Rangep r b"

definition Field :: "'a rel \<Rightarrow> 'a set"
  where "Field r = Domain r \<union> Range r"

lemma FieldI1: "(i, j) \<in> R \<Longrightarrow> i \<in> Field R"
  unfolding Field_def by blast

lemma FieldI2: "(i, j) \<in> R \<Longrightarrow> j \<in> Field R"
  unfolding Field_def by auto

lemma Domain_fst [code]: "Domain r = fst ` r"
  by force

lemma Range_snd [code]: "Range r = snd ` r"
  by force

lemma fst_eq_Domain: "fst ` R = Domain R"
  by force

lemma snd_eq_Range: "snd ` R = Range R"
  by force

lemma range_fst [simp]: "range fst = UNIV"
  by (auto simp: fst_eq_Domain)

lemma range_snd [simp]: "range snd = UNIV"
  by (auto simp: snd_eq_Range)

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

lemma Domain_Collect_case_prod [simp]: "Domain {(x, y). P x y} = {x. \<exists>y. P x y}"
  by auto

lemma Range_Collect_case_prod [simp]: "Range {(x, y). P x y} = {y. \<exists>x. P x y}"
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

lemma Domain_unfold: "Domain r = {x. \<exists>y. (x, y) \<in> r}"
  by blast

lemma Field_square [simp]: "Field (x \<times> x) = x"
  unfolding Field_def by blast


subsubsection \<open>Image of a set under a relation\<close>

definition Image :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set"  (infixr "``" 90)
  where "r `` s = {y. \<exists>x\<in>s. (x, y) \<in> r}"

lemma Image_iff: "b \<in> r``A \<longleftrightarrow> (\<exists>x\<in>A. (x, b) \<in> r)"
  by (simp add: Image_def)

lemma Image_singleton: "r``{a} = {b. (a, b) \<in> r}"
  by (simp add: Image_def)

lemma Image_singleton_iff [iff]: "b \<in> r``{a} \<longleftrightarrow> (a, b) \<in> r"
  by (rule Image_iff [THEN trans]) simp

lemma ImageI [intro]: "(a, b) \<in> r \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> r``A"
  unfolding Image_def by blast

lemma ImageE [elim!]: "b \<in> r `` A \<Longrightarrow> (\<And>x. (x, b) \<in> r \<Longrightarrow> x \<in> A \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding Image_def by (iprover elim!: CollectE bexE)

lemma rev_ImageI: "a \<in> A \<Longrightarrow> (a, b) \<in> r \<Longrightarrow> b \<in> r `` A"
  \<comment> \<open>This version's more effective when we already have the required \<open>a\<close>\<close>
  by blast

lemma Image_empty1 [simp]: "{} `` X = {}"
by auto

lemma Image_empty2 [simp]: "R``{} = {}"
by blast

lemma Image_Id [simp]: "Id `` A = A"
  by blast

lemma Image_Id_on [simp]: "Id_on A `` B = A \<inter> B"
  by blast

lemma Image_Int_subset: "R `` (A \<inter> B) \<subseteq> R `` A \<inter> R `` B"
  by blast

lemma Image_Int_eq: "single_valued (converse R) \<Longrightarrow> R `` (A \<inter> B) = R `` A \<inter> R `` B"
  by (auto simp: single_valued_def)

lemma Image_Un: "R `` (A \<union> B) = R `` A \<union> R `` B"
  by blast

lemma Un_Image: "(R \<union> S) `` A = R `` A \<union> S `` A"
  by blast

lemma Image_subset: "r \<subseteq> A \<times> B \<Longrightarrow> r``C \<subseteq> B"
  by (iprover intro!: subsetI elim!: ImageE dest!: subsetD SigmaD2)

lemma Image_eq_UN: "r``B = (\<Union>y\<in> B. r``{y})"
  \<comment> \<open>NOT suitable for rewriting\<close>
  by blast

lemma Image_mono: "r' \<subseteq> r \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> (r' `` A') \<subseteq> (r `` A)"
  by blast

lemma Image_UN: "r `` (\<Union>(B ` A)) = (\<Union>x\<in>A. r `` (B x))"
  by blast

lemma UN_Image: "(\<Union>i\<in>I. X i) `` S = (\<Union>i\<in>I. X i `` S)"
  by auto

lemma Image_INT_subset: "(r `` (\<Inter>(B ` A))) \<subseteq> (\<Inter>x\<in>A. r `` (B x))"
  by blast

text \<open>Converse inclusion requires some assumptions\<close>
lemma Image_INT_eq: "single_valued (r\<inverse>) \<Longrightarrow> A \<noteq> {} \<Longrightarrow> r `` (\<Inter>(B ` A)) = (\<Inter>x\<in>A. r `` B x)"
  apply (rule equalityI)
   apply (rule Image_INT_subset)
  apply (auto simp add: single_valued_def)
  apply blast
  done

lemma Image_subset_eq: "r``A \<subseteq> B \<longleftrightarrow> A \<subseteq> - ((r\<inverse>) `` (- B))"
  by blast

lemma Image_Collect_case_prod [simp]: "{(x, y). P x y} `` A = {y. \<exists>x\<in>A. P x y}"
  by auto

lemma Sigma_Image: "(SIGMA x:A. B x) `` X = (\<Union>x\<in>X \<inter> A. B x)"
  by auto

lemma relcomp_Image: "(X O Y) `` Z = Y `` (X `` Z)"
  by auto

lemma finite_Image[simp]: assumes "finite R" shows "finite (R `` A)"
by(rule finite_subset[OF _ finite_Range[OF assms]]) auto


subsubsection \<open>Inverse image\<close>

definition inv_image :: "'b rel \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a rel"
  where "inv_image r f = {(x, y). (f x, f y) \<in> r}"

definition inv_imagep :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "inv_imagep r f = (\<lambda>x y. r (f x) (f y))"

lemma [pred_set_conv]: "inv_imagep (\<lambda>x y. (x, y) \<in> r) f = (\<lambda>x y. (x, y) \<in> inv_image r f)"
  by (simp add: inv_image_def inv_imagep_def)

lemma sym_inv_image: "sym r \<Longrightarrow> sym (inv_image r f)"
  unfolding sym_def inv_image_def by blast

lemma trans_inv_image: "trans r \<Longrightarrow> trans (inv_image r f)"
  unfolding trans_def inv_image_def
  by (simp (no_asm)) blast

lemma total_inv_image: "\<lbrakk>inj f; total r\<rbrakk> \<Longrightarrow> total (inv_image r f)"
  unfolding inv_image_def total_on_def by (auto simp: inj_eq)

lemma asym_inv_image: "asym R \<Longrightarrow> asym (inv_image R f)"
  by (simp add: inv_image_def asym_iff)

lemma in_inv_image[simp]: "(x, y) \<in> inv_image r f \<longleftrightarrow> (f x, f y) \<in> r"
  by (auto simp: inv_image_def)

lemma converse_inv_image[simp]: "(inv_image R f)\<inverse> = inv_image (R\<inverse>) f"
  unfolding inv_image_def converse_unfold by auto

lemma in_inv_imagep [simp]: "inv_imagep r f x y = r (f x) (f y)"
  by (simp add: inv_imagep_def)


subsubsection \<open>Powerset\<close>

definition Powp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "Powp A = (\<lambda>B. \<forall>x \<in> B. A x)"

lemma Powp_Pow_eq [pred_set_conv]: "Powp (\<lambda>x. x \<in> A) = (\<lambda>x. x \<in> Pow A)"
  by (auto simp add: Powp_def fun_eq_iff)

lemmas Powp_mono [mono] = Pow_mono [to_pred]


subsubsection \<open>Expressing relation operations via \<^const>\<open>Finite_Set.fold\<close>\<close>

lemma Id_on_fold:
  assumes "finite A"
  shows "Id_on A = Finite_Set.fold (\<lambda>x. Set.insert (Pair x x)) {} A"
proof -
  interpret comp_fun_commute "\<lambda>x. Set.insert (Pair x x)"
    by standard auto
  from assms show ?thesis
    unfolding Id_on_def by (induct A) simp_all
qed

lemma comp_fun_commute_Image_fold:
  "comp_fun_commute (\<lambda>(x,y) A. if x \<in> S then Set.insert y A else A)"
proof -
  interpret comp_fun_idem Set.insert
    by (fact comp_fun_idem_insert)
  show ?thesis
    by standard (auto simp: fun_eq_iff comp_fun_commute split: prod.split)
qed

lemma Image_fold:
  assumes "finite R"
  shows "R `` S = Finite_Set.fold (\<lambda>(x,y) A. if x \<in> S then Set.insert y A else A) {} R"
proof -
  interpret comp_fun_commute "(\<lambda>(x,y) A. if x \<in> S then Set.insert y A else A)"
    by (rule comp_fun_commute_Image_fold)
  have *: "\<And>x F. Set.insert x F `` S = (if fst x \<in> S then Set.insert (snd x) (F `` S) else (F `` S))"
    by (force intro: rev_ImageI)
  show ?thesis
    using assms by (induct R) (auto simp: *)
qed

lemma insert_relcomp_union_fold:
  assumes "finite S"
  shows "{x} O S \<union> X = Finite_Set.fold (\<lambda>(w,z) A'. if snd x = w then Set.insert (fst x,z) A' else A') X S"
proof -
  interpret comp_fun_commute "\<lambda>(w,z) A'. if snd x = w then Set.insert (fst x,z) A' else A'"
  proof -
    interpret comp_fun_idem Set.insert
      by (fact comp_fun_idem_insert)
    show "comp_fun_commute (\<lambda>(w,z) A'. if snd x = w then Set.insert (fst x,z) A' else A')"
      by standard (auto simp add: fun_eq_iff split: prod.split)
  qed
  have *: "{x} O S = {(x', z). x' = fst x \<and> (snd x, z) \<in> S}"
    by (auto simp: relcomp_unfold intro!: exI)
  show ?thesis
    unfolding * using \<open>finite S\<close> by (induct S) (auto split: prod.split)
qed

lemma insert_relcomp_fold:
  assumes "finite S"
  shows "Set.insert x R O S =
    Finite_Set.fold (\<lambda>(w,z) A'. if snd x = w then Set.insert (fst x,z) A' else A') (R O S) S"
proof -
  have "Set.insert x R O S = ({x} O S) \<union> (R O S)"
    by auto
  then show ?thesis
    by (auto simp: insert_relcomp_union_fold [OF assms])
qed

lemma comp_fun_commute_relcomp_fold:
  assumes "finite S"
  shows "comp_fun_commute (\<lambda>(x,y) A.
    Finite_Set.fold (\<lambda>(w,z) A'. if y = w then Set.insert (x,z) A' else A') A S)"
proof -
  have *: "\<And>a b A.
    Finite_Set.fold (\<lambda>(w, z) A'. if b = w then Set.insert (a, z) A' else A') A S = {(a,b)} O S \<union> A"
    by (auto simp: insert_relcomp_union_fold[OF assms] cong: if_cong)
  show ?thesis
    by standard (auto simp: *)
qed

lemma relcomp_fold:
  assumes "finite R" "finite S"
  shows "R O S = Finite_Set.fold
    (\<lambda>(x,y) A. Finite_Set.fold (\<lambda>(w,z) A'. if y = w then Set.insert (x,z) A' else A') A S) {} R"
proof -
  interpret commute_relcomp_fold: comp_fun_commute
    "(\<lambda>(x, y) A. Finite_Set.fold (\<lambda>(w, z) A'. if y = w then insert (x, z) A' else A') A S)"
    by (fact comp_fun_commute_relcomp_fold[OF \<open>finite S\<close>])
  from assms show ?thesis
    by (induct R) (auto simp: comp_fun_commute_relcomp_fold insert_relcomp_fold cong: if_cong)
qed

end
