(*  Title:      HOL/Relation.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Martin Desharnais, MPI-INF Saarbruecken
*)

section \<open>Relations -- as sets of pairs, and binary predicates\<close>

theory Relation
  imports Product_Type Sum_Type Fields
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

lemma top_empty_eq: "\<top> = (\<lambda>x. x \<in> UNIV)"
  by (auto simp add: fun_eq_iff)

lemma top_empty_eq2: "\<top> = (\<lambda>x y. (x, y) \<in> UNIV)"
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
  where "refl_on A r \<longleftrightarrow> (\<forall>x\<in>A. (x, x) \<in> r)"

abbreviation refl :: "'a rel \<Rightarrow> bool" \<comment> \<open>reflexivity over a type\<close>
  where "refl \<equiv> refl_on UNIV"

definition reflp_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "reflp_on A R \<longleftrightarrow> (\<forall>x\<in>A. R x x)"

abbreviation reflp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "reflp \<equiv> reflp_on UNIV"

lemma reflp_def[no_atp]: "reflp R \<longleftrightarrow> (\<forall>x. R x x)"
  by (simp add: reflp_on_def)

text \<open>@{thm [source] reflp_def} is for backward compatibility.\<close>

lemma reflp_on_refl_on_eq[pred_set_conv]: "reflp_on A (\<lambda>a b. (a, b) \<in> r) \<longleftrightarrow> refl_on A r"
  by (simp add: refl_on_def reflp_on_def)

lemmas reflp_refl_eq = reflp_on_refl_on_eq[of UNIV]

lemma refl_onI [intro?]: "(\<And>x. x \<in> A \<Longrightarrow> (x, x) \<in> r) \<Longrightarrow> refl_on A r"
  unfolding refl_on_def by (iprover intro!: ballI)

lemma reflI: "(\<And>x. (x, x) \<in> r) \<Longrightarrow> refl r"
  by (auto intro: refl_onI)

lemma reflp_onI:
  "(\<And>x. x \<in> A \<Longrightarrow> R x x) \<Longrightarrow> reflp_on A R"
  by (simp add: reflp_on_def)

lemma reflpI[intro?]: "(\<And>x. R x x) \<Longrightarrow> reflp R"
  by (rule reflp_onI)

lemma refl_onD: "refl_on A r \<Longrightarrow> a \<in> A \<Longrightarrow> (a, a) \<in> r"
  unfolding refl_on_def by blast

lemma reflD: "refl r \<Longrightarrow> (a, a) \<in> r"
  unfolding refl_on_def by blast

lemma reflp_onD:
  "reflp_on A R \<Longrightarrow> x \<in> A \<Longrightarrow> R x x"
  by (simp add: reflp_on_def)

lemma reflpD[dest?]: "reflp R \<Longrightarrow> R x x"
  by (simp add: reflp_onD)

lemma reflpE:
  assumes "reflp r"
  obtains "r x x"
  using assms by (auto dest: refl_onD simp add: reflp_def)

lemma refl_on_top[simp]: "refl_on A \<top>"
  by (simp add: refl_on_def)

lemma reflp_on_top[simp]: "reflp_on A \<top>"
  by (simp add: reflp_on_def)

lemma reflp_on_subset: "reflp_on A R \<Longrightarrow> B \<subseteq> A \<Longrightarrow> reflp_on B R"
  by (auto intro: reflp_onI dest: reflp_onD)

lemma reflp_on_image: "reflp_on (f ` A) R \<longleftrightarrow> reflp_on A (\<lambda>a b. R (f a) (f b))"
  by (simp add: reflp_on_def)

lemma refl_on_Int: "refl_on A r \<Longrightarrow> refl_on B s \<Longrightarrow> refl_on (A \<inter> B) (r \<inter> s)"
  unfolding refl_on_def by blast

lemma reflp_on_inf: "reflp_on A R \<Longrightarrow> reflp_on B S \<Longrightarrow> reflp_on (A \<inter> B) (R \<sqinter> S)"
  by (auto intro: reflp_onI dest: reflp_onD)

lemma reflp_inf: "reflp r \<Longrightarrow> reflp s \<Longrightarrow> reflp (r \<sqinter> s)"
  by (rule reflp_on_inf[of UNIV _ UNIV, unfolded Int_absorb])

lemma refl_on_Un: "refl_on A r \<Longrightarrow> refl_on B s \<Longrightarrow> refl_on (A \<union> B) (r \<union> s)"
  unfolding refl_on_def by blast

lemma reflp_on_sup: "reflp_on A R \<Longrightarrow> reflp_on B S \<Longrightarrow> reflp_on (A \<union> B) (R \<squnion> S)"
  by (auto intro: reflp_onI dest: reflp_onD)

lemma reflp_sup: "reflp r \<Longrightarrow> reflp s \<Longrightarrow> reflp (r \<squnion> s)"
  by (rule reflp_on_sup[of UNIV _ UNIV, unfolded Un_absorb])

lemma refl_on_INTER: "\<forall>x\<in>S. refl_on (A x) (r x) \<Longrightarrow> refl_on (\<Inter>(A ` S)) (\<Inter>(r ` S))"
  unfolding refl_on_def by fast

lemma reflp_on_Inf: "\<forall>x\<in>S. reflp_on (A x) (R x) \<Longrightarrow> reflp_on (\<Inter>(A ` S)) (\<Sqinter>(R ` S))"
  by (auto intro: reflp_onI dest: reflp_onD)

lemma refl_on_UNION: "\<forall>x\<in>S. refl_on (A x) (r x) \<Longrightarrow> refl_on (\<Union>(A ` S)) (\<Union>(r ` S))"
  unfolding refl_on_def by blast

lemma reflp_on_Sup: "\<forall>x\<in>S. reflp_on (A x) (R x) \<Longrightarrow> reflp_on (\<Union>(A ` S)) (\<Squnion>(R ` S))"
  by (auto intro: reflp_onI dest: reflp_onD)

lemma refl_on_empty [simp]: "refl_on {} r"
  by (simp add: refl_on_def)

lemma reflp_on_empty [simp]: "reflp_on {} R"
  by (auto intro: reflp_onI)

lemma refl_on_singleton [simp]: "refl_on {x} {(x, x)}"
by (blast intro: refl_onI)

lemma reflp_on_equality [simp]: "reflp_on A (=)"
  by (simp add: reflp_on_def)

lemma reflp_on_mono_strong:
  "reflp_on B R \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R x y \<Longrightarrow> Q x y) \<Longrightarrow> reflp_on A Q"
  by (rule reflp_onI) (auto dest: reflp_onD)

lemma reflp_on_mono[mono]: "A \<subseteq> B \<Longrightarrow> R \<le> Q \<Longrightarrow> reflp_on B R \<le> reflp_on A Q"
  by (simp add: reflp_on_mono_strong le_fun_def)

lemma (in preorder) reflp_on_le[simp]: "reflp_on A (\<le>)"
  by (simp add: reflp_onI)

lemma (in preorder) reflp_on_ge[simp]: "reflp_on A (\<ge>)"
  by (simp add: reflp_onI)


subsubsection \<open>Irreflexivity\<close>

definition irrefl_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "irrefl_on A r \<longleftrightarrow> (\<forall>a \<in> A. (a, a) \<notin> r)"

abbreviation irrefl :: "'a rel \<Rightarrow> bool" where
  "irrefl \<equiv> irrefl_on UNIV"

definition irreflp_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "irreflp_on A R \<longleftrightarrow> (\<forall>a \<in> A. \<not> R a a)"

abbreviation irreflp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "irreflp \<equiv> irreflp_on UNIV"

lemma irrefl_def[no_atp]: "irrefl r \<longleftrightarrow> (\<forall>a. (a, a) \<notin> r)"
  by (simp add: irrefl_on_def)

lemma irreflp_def[no_atp]: "irreflp R \<longleftrightarrow> (\<forall>a. \<not> R a a)"
  by (simp add: irreflp_on_def)

text \<open>@{thm [source] irrefl_def} and @{thm [source] irreflp_def} are for backward compatibility.\<close>

lemma irreflp_on_irrefl_on_eq [pred_set_conv]: "irreflp_on A (\<lambda>a b. (a, b) \<in> r) \<longleftrightarrow> irrefl_on A r"
  by (simp add: irrefl_on_def irreflp_on_def)

lemmas irreflp_irrefl_eq = irreflp_on_irrefl_on_eq[of UNIV]

lemma irrefl_onI: "(\<And>a. a \<in> A \<Longrightarrow> (a, a) \<notin> r) \<Longrightarrow> irrefl_on A r"
  by (simp add: irrefl_on_def)

lemma irreflI[intro?]: "(\<And>a. (a, a) \<notin> r) \<Longrightarrow> irrefl r"
  by (rule irrefl_onI[of UNIV, simplified])

lemma irreflp_onI: "(\<And>a. a \<in> A \<Longrightarrow> \<not> R a a) \<Longrightarrow> irreflp_on A R"
  by (rule irrefl_onI[to_pred])

lemma irreflpI[intro?]: "(\<And>a. \<not> R a a) \<Longrightarrow> irreflp R"
  by (rule irreflI[to_pred])

lemma irrefl_onD: "irrefl_on A r \<Longrightarrow> a \<in> A \<Longrightarrow> (a, a) \<notin> r"
  by (simp add: irrefl_on_def)

lemma irreflD: "irrefl r \<Longrightarrow> (x, x) \<notin> r"
  by (rule irrefl_onD[of UNIV, simplified])

lemma irreflp_onD: "irreflp_on A R \<Longrightarrow> a \<in> A \<Longrightarrow> \<not> R a a"
  by (rule irrefl_onD[to_pred])

lemma irreflpD: "irreflp R \<Longrightarrow> \<not> R x x"
  by (rule irreflD[to_pred])

lemma irrefl_on_bot[simp]: "irrefl_on A \<bottom>"
  by (simp add: irrefl_on_def)

lemma irreflp_on_bot[simp]: "irreflp_on A \<bottom>"
  using irrefl_on_bot[to_pred] .

lemma irrefl_on_distinct [code]: "irrefl_on A r \<longleftrightarrow> (\<forall>(a, b) \<in> r. a \<in> A \<longrightarrow> b \<in> A \<longrightarrow> a \<noteq> b)"
  by (auto simp add: irrefl_on_def)

lemmas irrefl_distinct = irrefl_on_distinct \<comment> \<open>For backward compatibility\<close>

lemma irrefl_on_subset: "irrefl_on A r \<Longrightarrow> B \<subseteq> A \<Longrightarrow> irrefl_on B r"
  by (auto simp: irrefl_on_def)

lemma irreflp_on_subset: "irreflp_on A R \<Longrightarrow> B \<subseteq> A \<Longrightarrow> irreflp_on B R"
  by (auto simp: irreflp_on_def)

lemma irreflp_on_image: "irreflp_on (f ` A) R \<longleftrightarrow> irreflp_on A (\<lambda>a b. R (f a) (f b))"
  by (simp add: irreflp_on_def)

lemma (in preorder) irreflp_on_less[simp]: "irreflp_on A (<)"
  by (simp add: irreflp_onI)

lemma (in preorder) irreflp_on_greater[simp]: "irreflp_on A (>)"
  by (simp add: irreflp_onI)


subsubsection \<open>Asymmetry\<close>

definition asym_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "asym_on A r \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. (x, y) \<in> r \<longrightarrow> (y, x) \<notin> r)"

abbreviation asym :: "'a rel \<Rightarrow> bool" where
  "asym \<equiv> asym_on UNIV"

definition asymp_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "asymp_on A R \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. R x y \<longrightarrow> \<not> R y x)"

abbreviation asymp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "asymp \<equiv> asymp_on UNIV"

lemma asymp_on_asym_on_eq[pred_set_conv]: "asymp_on A (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> asym_on A r"
  by (simp add: asymp_on_def asym_on_def)

lemmas asymp_asym_eq = asymp_on_asym_on_eq[of UNIV] \<comment> \<open>For backward compatibility\<close>

lemma asym_onI[intro]:
  "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, x) \<notin> r) \<Longrightarrow> asym_on A r"
  by (simp add: asym_on_def)

lemma asymI[intro]: "(\<And>x y. (x, y) \<in> r \<Longrightarrow> (y, x) \<notin> r) \<Longrightarrow> asym r"
  by (simp add: asym_onI)

lemma asymp_onI[intro]:
  "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R x y \<Longrightarrow> \<not> R y x) \<Longrightarrow> asymp_on A R"
  by (rule asym_onI[to_pred])

lemma asympI[intro]: "(\<And>x y. R x y \<Longrightarrow> \<not> R y x) \<Longrightarrow> asymp R"
  by (rule asymI[to_pred])

lemma asym_onD: "asym_on A r \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, x) \<notin> r"
  by (simp add: asym_on_def)

lemma asymD: "asym r \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, x) \<notin> r"
  by (simp add: asym_onD)

lemma asymp_onD: "asymp_on A R \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R x y \<Longrightarrow> \<not> R y x"
  by (rule asym_onD[to_pred])

lemma asympD: "asymp R \<Longrightarrow> R x y \<Longrightarrow> \<not> R y x"
  by (rule asymD[to_pred])

lemma asym_on_bot[simp]: "asym_on A \<bottom>"
  by (simp add: asym_on_def)

lemma asymp_on_bot[simp]: "asymp_on A \<bottom>"
  using asym_on_bot[to_pred] .

lemma asym_iff: "asym r \<longleftrightarrow> (\<forall>x y. (x,y) \<in> r \<longrightarrow> (y,x) \<notin> r)"
  by (blast dest: asymD)

lemma asym_on_subset: "asym_on A r \<Longrightarrow> B \<subseteq> A \<Longrightarrow> asym_on B r"
  by (auto simp: asym_on_def)

lemma asymp_on_subset: "asymp_on A R \<Longrightarrow> B \<subseteq> A \<Longrightarrow> asymp_on B R"
  by (auto simp: asymp_on_def)

lemma asymp_on_image: "asymp_on (f ` A) R \<longleftrightarrow> asymp_on A (\<lambda>a b. R (f a) (f b))"
  by (simp add: asymp_on_def)

lemma irrefl_on_if_asym_on[simp]: "asym_on A r \<Longrightarrow> irrefl_on A r"
  by (auto intro: irrefl_onI dest: asym_onD)

lemma irreflp_on_if_asymp_on[simp]: "asymp_on A r \<Longrightarrow> irreflp_on A r"
  by (rule irrefl_on_if_asym_on[to_pred])

lemma (in preorder) asymp_on_less[simp]: "asymp_on A (<)"
  by (auto intro: dual_order.asym)

lemma (in preorder) asymp_on_greater[simp]: "asymp_on A (>)"
  by (auto intro: dual_order.asym)


subsubsection \<open>Symmetry\<close>

definition sym_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "sym_on A r \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r)"

abbreviation sym :: "'a rel \<Rightarrow> bool" where
  "sym \<equiv> sym_on UNIV"

definition symp_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "symp_on A R \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. R x y \<longrightarrow> R y x)"

abbreviation symp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "symp \<equiv> symp_on UNIV"

lemma sym_def[no_atp]: "sym r \<longleftrightarrow> (\<forall>x y. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r)"
  by (simp add: sym_on_def)

lemma symp_def[no_atp]: "symp R \<longleftrightarrow> (\<forall>x y. R x y \<longrightarrow> R y x)"
  by (simp add: symp_on_def)

text \<open>@{thm [source] sym_def} and @{thm [source] symp_def} are for backward compatibility.\<close>

lemma symp_on_sym_on_eq[pred_set_conv]: "symp_on A (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> sym_on A r"
  by (simp add: sym_on_def symp_on_def)

lemmas symp_sym_eq = symp_on_sym_on_eq[of UNIV] \<comment> \<open>For backward compatibility\<close>

lemma sym_on_bot[simp]: "sym_on A \<bottom>"
  by (simp add: sym_on_def)

lemma symp_on_bot[simp]: "symp_on A \<bottom>"
  using sym_on_bot[to_pred] .

lemma sym_on_top[simp]: "sym_on A \<top>"
  by (simp add: sym_on_def)

lemma symp_on_top[simp]: "symp_on A \<top>"
  by (simp add: symp_on_def)

lemma sym_on_subset: "sym_on A r \<Longrightarrow> B \<subseteq> A \<Longrightarrow> sym_on B r"
  by (auto simp: sym_on_def)

lemma symp_on_subset: "symp_on A R \<Longrightarrow> B \<subseteq> A \<Longrightarrow> symp_on B R"
  by (auto simp: symp_on_def)

lemma symp_on_image: "symp_on (f ` A) R \<longleftrightarrow> symp_on A (\<lambda>a b. R (f a) (f b))"
  by (simp add: symp_on_def)

lemma sym_onI: "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, x) \<in> r) \<Longrightarrow> sym_on A r"
  by (simp add: sym_on_def)

lemma symI [intro?]: "(\<And>x y. (x, y) \<in> r \<Longrightarrow> (y, x) \<in> r) \<Longrightarrow> sym r"
  by (simp add: sym_onI)

lemma symp_onI: "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R x y \<Longrightarrow> R y x) \<Longrightarrow> symp_on A R"
  by (rule sym_onI[to_pred])

lemma sympI [intro?]: "(\<And>x y. R x y \<Longrightarrow> R y x) \<Longrightarrow> symp R"
  by (rule symI[to_pred])

lemma symE:
  assumes "sym r" and "(b, a) \<in> r"
  obtains "(a, b) \<in> r"
  using assms by (simp add: sym_def)

lemma sympE:
  assumes "symp r" and "r b a"
  obtains "r a b"
  using assms by (rule symE [to_pred])

lemma sym_onD: "sym_on A r \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, x) \<in> r"
  by (simp add: sym_on_def)

lemma symD [dest?]: "sym r \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, x) \<in> r"
  by (simp add: sym_onD)

lemma symp_onD: "symp_on A R \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R x y \<Longrightarrow> R y x"
  by (rule sym_onD[to_pred])

lemma sympD [dest?]: "symp R \<Longrightarrow> R x y \<Longrightarrow> R y x"
  by (rule symD[to_pred])

lemma symp_on_equality[simp]: "symp_on A (=)"
  by (simp add: symp_on_def)

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

definition antisym_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "antisym_on A r \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r \<longrightarrow> x = y)"

abbreviation antisym :: "'a rel \<Rightarrow> bool" where
  "antisym \<equiv> antisym_on UNIV"

definition antisymp_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "antisymp_on A R \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. R x y \<longrightarrow> R y x \<longrightarrow> x = y)"

abbreviation antisymp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "antisymp \<equiv> antisymp_on UNIV"

lemma antisym_def[no_atp]: "antisym r \<longleftrightarrow> (\<forall>x y. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r \<longrightarrow> x = y)"
  by (simp add: antisym_on_def)

lemma antisymp_def[no_atp]: "antisymp R \<longleftrightarrow> (\<forall>x y. R x y \<longrightarrow> R y x \<longrightarrow> x = y)"
  by (simp add: antisymp_on_def)

text \<open>@{thm [source] antisym_def} and @{thm [source] antisymp_def} are for backward compatibility.\<close>

lemma antisymp_on_antisym_on_eq[pred_set_conv]:
  "antisymp_on A (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> antisym_on A r"
  by (simp add: antisym_on_def antisymp_on_def)

lemmas antisymp_antisym_eq = antisymp_on_antisym_on_eq[of UNIV] \<comment> \<open>For backward compatibility\<close>

lemma antisym_onI:
  "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, x) \<in> r \<Longrightarrow> x = y) \<Longrightarrow> antisym_on A r"
  unfolding antisym_on_def by simp

lemma antisymI [intro?]:
  "(\<And>x y. (x, y) \<in> r \<Longrightarrow> (y, x) \<in> r \<Longrightarrow> x = y) \<Longrightarrow> antisym r"
  by (simp add: antisym_onI)

lemma antisymp_onI:
  "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R x y \<Longrightarrow> R y x \<Longrightarrow> x = y) \<Longrightarrow> antisymp_on A R"
  by (rule antisym_onI[to_pred])

lemma antisympI [intro?]:
  "(\<And>x y. R x y \<Longrightarrow> R y x \<Longrightarrow> x = y) \<Longrightarrow> antisymp R"
  by (rule antisymI[to_pred])
    
lemma antisym_onD:
  "antisym_on A r \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, x) \<in> r \<Longrightarrow> x = y"
  by (simp add: antisym_on_def)

lemma antisymD [dest?]:
  "antisym r \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, x) \<in> r \<Longrightarrow> x = y"
  by (simp add: antisym_onD)

lemma antisymp_onD:
  "antisymp_on A R \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R x y \<Longrightarrow> R y x \<Longrightarrow> x = y"
  by (rule antisym_onD[to_pred])

lemma antisympD [dest?]:
  "antisymp R \<Longrightarrow> R x y \<Longrightarrow> R y x \<Longrightarrow> x = y"
  by (rule antisymD[to_pred])

lemma antisym_on_bot[simp]: "antisym_on A \<bottom>"
  by (simp add: antisym_on_def)

lemma antisymp_on_bot[simp]: "antisymp_on A \<bottom>"
  using antisym_on_bot[to_pred] .

lemma antisymp_on_mono_stronger:
  fixes
    A :: "'a set" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and
    B :: "'b set" and Q :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and
    f :: "'a \<Rightarrow> 'b"
  assumes "antisymp_on B Q" and "f ` A \<subseteq> B" and
    Q_imp_R: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R x y \<Longrightarrow> Q (f x) (f y)" and
    inj_f: "inj_on f A"
  shows "antisymp_on A R"
proof (rule antisymp_onI)
  fix x y :: 'a
  assume "x \<in> A" and "y \<in> A" and "R x y" and "R y x"
  hence "Q (f x) (f y)" and "Q (f y) (f x)"
    using Q_imp_R by iprover+
  moreover have "f x \<in> B" and "f y \<in> B"
    using \<open>f ` A \<subseteq> B\<close> \<open>x \<in> A\<close> \<open>y \<in> A\<close> by blast+
  ultimately have "f x = f y"
    using \<open>antisymp_on B Q\<close>[THEN antisymp_onD] by iprover
  thus "x = y"
    using inj_f[THEN inj_onD] \<open>x \<in> A\<close> \<open>y \<in> A\<close> by iprover
qed

lemma antisymp_on_mono_strong:
  "antisymp_on B Q \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R x y \<Longrightarrow> Q x y) \<Longrightarrow> antisymp_on A R"
  using antisymp_on_mono_stronger[of B Q "\<lambda>x. x" A R, OF _ _ _ inj_on_id2, unfolded image_ident] .

lemma antisymp_on_mono[mono]: "A \<subseteq> B \<Longrightarrow> R \<le> Q \<Longrightarrow> antisymp_on B Q \<le> antisymp_on A R"
  by (simp add: antisymp_on_mono_strong le_fun_def)

lemma antisym_on_subset: "antisym_on A r \<Longrightarrow> B \<subseteq> A \<Longrightarrow> antisym_on B r"
  by (auto simp: antisym_on_def)

lemma antisymp_on_subset: "antisymp_on A R \<Longrightarrow> B \<subseteq> A \<Longrightarrow> antisymp_on B R"
  using antisymp_on_mono_strong .

lemma antisymp_on_image:
  assumes "inj_on f A"
  shows "antisymp_on (f ` A) R \<longleftrightarrow> antisymp_on A (\<lambda>a b. R (f a) (f b))"
  using assms by (auto simp: antisymp_on_def inj_on_def)

lemma antisym_subset:
  "r \<subseteq> s \<Longrightarrow> antisym s \<Longrightarrow> antisym r"
  unfolding antisym_def by blast

lemma antisymp_less_eq:
  "r \<le> s \<Longrightarrow> antisymp s \<Longrightarrow> antisymp r"
  by (fact antisym_subset [to_pred])
    
lemma antisymp_on_equality[simp]: "antisymp_on A (=)"
  by (auto intro: antisymp_onI)

lemma antisym_singleton [simp]:
  "antisym {x}"
  by (blast intro: antisymI)

lemma antisym_on_if_asym_on: "asym_on A r \<Longrightarrow> antisym_on A r"
  by (auto intro: antisym_onI dest: asym_onD)

lemma antisymp_on_if_asymp_on: "asymp_on A R \<Longrightarrow> antisymp_on A R"
  by (rule antisym_on_if_asym_on[to_pred])

lemma (in preorder) antisymp_on_less[simp]: "antisymp_on A (<)"
  by (rule antisymp_on_if_asymp_on[OF asymp_on_less])

lemma (in preorder) antisymp_on_greater[simp]: "antisymp_on A (>)"
  by (rule antisymp_on_if_asymp_on[OF asymp_on_greater])

lemma (in order) antisymp_on_le[simp]: "antisymp_on A (\<le>)"
  by (simp add: antisymp_onI)

lemma (in order) antisymp_on_ge[simp]: "antisymp_on A (\<ge>)"
  by (simp add: antisymp_onI)


subsubsection \<open>Transitivity\<close>

definition trans_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "trans_on A r \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. (x, y) \<in> r \<longrightarrow> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r)"

abbreviation trans :: "'a rel \<Rightarrow> bool" where
  "trans \<equiv> trans_on UNIV"

definition transp_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "transp_on A R \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. R x y \<longrightarrow> R y z \<longrightarrow> R x z)"

abbreviation transp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "transp \<equiv> transp_on UNIV"

lemma trans_def[no_atp]: "trans r \<longleftrightarrow> (\<forall>x y z. (x, y) \<in> r \<longrightarrow> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r)"
  by (simp add: trans_on_def)

lemma transp_def: "transp R \<longleftrightarrow> (\<forall>x y z. R x y \<longrightarrow> R y z \<longrightarrow> R x z)"
  by (simp add: transp_on_def)

text \<open>@{thm [source] trans_def} and @{thm [source] transp_def} are for backward compatibility.\<close>

lemma transp_on_trans_on_eq[pred_set_conv]: "transp_on A (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> trans_on A r"
  by (simp add: trans_on_def transp_on_def)

lemmas transp_trans_eq = transp_on_trans_on_eq[of UNIV] \<comment> \<open>For backward compatibility\<close>

lemma trans_onI:
  "(\<And>x y z. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> (x, z) \<in> r) \<Longrightarrow>
  trans_on A r"
  unfolding trans_on_def
  by (intro ballI) iprover

lemma transI [intro?]: "(\<And>x y z. (x, y) \<in> r \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> (x, z) \<in> r) \<Longrightarrow> trans r"
  by (rule trans_onI)

lemma transp_onI:
  "(\<And>x y z. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> R x y \<Longrightarrow> R y z \<Longrightarrow> R x z) \<Longrightarrow> transp_on A R"
  by (rule trans_onI[to_pred])

lemma transpI [intro?]: "(\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z) \<Longrightarrow> transp R"
  by (rule transI[to_pred])

lemma transE:
  assumes "trans r" and "(x, y) \<in> r" and "(y, z) \<in> r"
  obtains "(x, z) \<in> r"
  using assms by (unfold trans_def) iprover

lemma transpE:
  assumes "transp r" and "r x y" and "r y z"
  obtains "r x z"
  using assms by (rule transE [to_pred])

lemma trans_onD:
  "trans_on A r \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> (x, z) \<in> r"
  unfolding trans_on_def
  by (elim ballE) iprover+

lemma transD[dest?]: "trans r \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> (x, z) \<in> r"
  by (simp add: trans_onD[of UNIV r x y z])

lemma transp_onD: "transp_on A R \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  by (rule trans_onD[to_pred])

lemma transpD[dest?]: "transp R \<Longrightarrow> R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  by (rule transD[to_pred])

lemma trans_on_subset: "trans_on A r \<Longrightarrow> B \<subseteq> A \<Longrightarrow> trans_on B r"
  by (auto simp: trans_on_def)

lemma transp_on_subset: "transp_on A R \<Longrightarrow> B \<subseteq> A \<Longrightarrow> transp_on B R"
  by (auto simp: transp_on_def)

lemma transp_on_image: "transp_on (f ` A) R \<longleftrightarrow> transp_on A (\<lambda>a b. R (f a) (f b))"
  by (simp add: transp_on_def)

lemma trans_Int: "trans r \<Longrightarrow> trans s \<Longrightarrow> trans (r \<inter> s)"
  by (fast intro: transI elim: transE)

lemma transp_inf: "transp r \<Longrightarrow> transp s \<Longrightarrow> transp (r \<sqinter> s)"
  by (fact trans_Int [to_pred])

lemma trans_INTER: "\<forall>x\<in>S. trans (r x) \<Longrightarrow> trans (\<Inter>(r ` S))"
  by (fast intro: transI elim: transD)

lemma transp_INF: "\<forall>x\<in>S. transp (r x) \<Longrightarrow> transp (\<Sqinter>(r ` S))"
  by (fact trans_INTER [to_pred])

lemma trans_on_join [code]:
  "trans_on A r \<longleftrightarrow> (\<forall>(x, y1) \<in> r. x \<in> A \<longrightarrow> y1 \<in> A \<longrightarrow>
    (\<forall>(y2, z) \<in> r. y1 = y2 \<longrightarrow> z \<in> A \<longrightarrow> (x, z) \<in> r))"
  by (auto simp: trans_on_def)

lemma trans_join: "trans r \<longleftrightarrow> (\<forall>(x, y1) \<in> r. \<forall>(y2, z) \<in> r. y1 = y2 \<longrightarrow> (x, z) \<in> r)"
  by (auto simp add: trans_def)

lemma transp_trans: "transp r \<longleftrightarrow> trans {(x, y). r x y}"
  by (simp add: trans_def transp_def)

lemma transp_on_equality[simp]: "transp_on A (=)"
  by (auto intro: transp_onI)

lemma trans_on_bot[simp]: "trans_on A \<bottom>"
  by (simp add: trans_on_def)

lemma transp_on_bot[simp]: "transp_on A \<bottom>"
  using trans_on_bot[to_pred] .

lemma trans_on_top[simp]: "trans_on A \<top>"
  by (simp add: trans_on_def)

lemma transp_on_top[simp]: "transp_on A \<top>"
  by (simp add: transp_on_def)

lemma transp_empty [simp]: "transp (\<lambda>x y. False)"
  using transp_on_bot unfolding bot_fun_def bot_bool_def .

lemma trans_singleton [simp]: "trans {(a, a)}"
  by (blast intro: transI)

lemma transp_singleton [simp]: "transp (\<lambda>x y. x = a \<and> y = a)"
  by (simp add: transp_def)

lemma asym_on_iff_irrefl_on_if_trans_on: "trans_on A r \<Longrightarrow> asym_on A r \<longleftrightarrow> irrefl_on A r"
  by (auto intro: irrefl_on_if_asym_on dest: trans_onD irrefl_onD)

lemma asymp_on_iff_irreflp_on_if_transp_on: "transp_on A R \<Longrightarrow> asymp_on A R \<longleftrightarrow> irreflp_on A R"
  by (rule asym_on_iff_irrefl_on_if_trans_on[to_pred])

lemma (in preorder) transp_on_le[simp]: "transp_on A (\<le>)"
  by (auto intro: transp_onI order_trans)

lemma (in preorder) transp_on_less[simp]: "transp_on A (<)"
  by (auto intro: transp_onI less_trans)

lemma (in preorder) transp_on_ge[simp]: "transp_on A (\<ge>)"
  by (auto intro: transp_onI order_trans)

lemma (in preorder) transp_on_greater[simp]: "transp_on A (>)"
  by (auto intro: transp_onI less_trans)


subsubsection \<open>Totality\<close>

definition total_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "total_on A r \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r)"

abbreviation total :: "'a rel \<Rightarrow> bool" where
  "total \<equiv> total_on UNIV"

definition totalp_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "totalp_on A R \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. x \<noteq> y \<longrightarrow> R x y \<or> R y x)"

abbreviation totalp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "totalp \<equiv> totalp_on UNIV"

lemma totalp_on_total_on_eq[pred_set_conv]: "totalp_on A (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> total_on A r"
  by (simp add: totalp_on_def total_on_def)

lemma total_onI [intro?]:
  "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r) \<Longrightarrow> total_on A r"
  unfolding total_on_def by blast

lemma totalI: "(\<And>x y. x \<noteq> y \<Longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r) \<Longrightarrow> total r"
  by (rule total_onI)

lemma totalp_onI: "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> R x y \<or> R y x) \<Longrightarrow> totalp_on A R"
  by (rule total_onI[to_pred])

lemma totalpI: "(\<And>x y. x \<noteq> y \<Longrightarrow> R x y \<or> R y x) \<Longrightarrow> totalp R"
  by (rule totalI[to_pred])

lemma totalp_onD:
  "totalp_on A R \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> R x y \<or> R y x"
  by (simp add: totalp_on_def)

lemma totalpD: "totalp R \<Longrightarrow> x \<noteq> y \<Longrightarrow> R x y \<or> R y x"
  by (simp add: totalp_onD)

lemma total_on_top[simp]: "total_on A \<top>"
  by (simp add: total_on_def)

lemma totalp_on_top[simp]: "totalp_on A \<top>"
  by (simp add: totalp_on_def)

lemma totalp_on_mono_stronger:
  fixes
    A :: "'a set" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and
    B :: "'b set" and Q :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and
    f :: "'a \<Rightarrow> 'b"
  assumes "totalp_on B Q" and "f ` A \<subseteq> B" and
    Q_imp_R: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> Q (f x) (f y) \<Longrightarrow> R x y" and
    inj_f: "inj_on f A"
  shows "totalp_on A R"
proof (rule totalp_onI)
  fix x y :: 'a
  assume "x \<in> A" and "y \<in> A" and "x \<noteq> y"
  hence "f x \<in> B" and "f y \<in> B" and "f x \<noteq> f y"
    using \<open>f ` A \<subseteq> B\<close> inj_f by (auto dest: inj_onD)
  hence "Q (f x) (f y) \<or> Q (f y) (f x)"
    using \<open>totalp_on B Q\<close> by (iprover dest: totalp_onD)
  thus "R x y \<or> R y x"
    using Q_imp_R \<open>x \<in> A\<close> \<open>y \<in> A\<close> by iprover
qed

lemma totalp_on_mono_stronger_alt:
  fixes
    A :: "'a set" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and
    B :: "'b set" and Q :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and
    f :: "'b \<Rightarrow> 'a"
  assumes "totalp_on B Q" and "A \<subseteq> f ` B" and
    Q_imp_R: "\<And>x y. x \<in> B \<Longrightarrow> y \<in> B \<Longrightarrow> Q x y \<Longrightarrow> R (f x) (f y)"
  shows "totalp_on A R"
proof (rule totalp_onI)
  fix x y :: 'a
  assume "x \<in> A" and "y \<in> A" and "x \<noteq> y"
  then obtain x' y' where "x' \<in> B" and "x = f x'" and "y' \<in> B" and "y = f y'" and "x' \<noteq> y'"
    using \<open>A \<subseteq> f ` B\<close> by blast
  hence "Q x' y' \<or> Q y' x'"
    using \<open>totalp_on B Q\<close>[THEN totalp_onD] by blast
  hence "R (f x') (f y') \<or> R (f y') (f x')"
    using Q_imp_R \<open>x' \<in> B\<close> \<open>y' \<in> B\<close> by blast
  thus "R x y \<or> R y x"
    using \<open>x = f x'\<close> \<open>y = f y'\<close> by blast
qed

lemma totalp_on_mono_strong:
  "totalp_on B Q \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> Q x y \<Longrightarrow> R x y) \<Longrightarrow> totalp_on A R"
  using totalp_on_mono_stronger[of B Q "\<lambda>x. x" A R, simplified] .

lemma totalp_on_mono[mono]: "A \<subseteq> B \<Longrightarrow> Q \<le> R \<Longrightarrow> totalp_on B Q \<le> totalp_on A R"
  by (auto intro: totalp_on_mono_strong)

lemma total_on_subset: "total_on A r \<Longrightarrow> B \<subseteq> A \<Longrightarrow> total_on B r"
  by (auto simp: total_on_def)

lemma totalp_on_subset: "totalp_on A R \<Longrightarrow> B \<subseteq> A \<Longrightarrow> totalp_on B R"
  using totalp_on_mono_strong .

lemma totalp_on_image:
  assumes "inj_on f A"
  shows "totalp_on (f ` A) R \<longleftrightarrow> totalp_on A (\<lambda>a b. R (f a) (f b))"
  using assms by (auto simp: totalp_on_def inj_on_def)

lemma total_on_empty [simp]: "total_on {} r"
  by (simp add: total_on_def)

lemma totalp_on_empty [simp]: "totalp_on {} R"
  by (simp add: totalp_on_def)

lemma total_on_singleton [simp]: "total_on {x} r"
  by (simp add: total_on_def)

lemma totalp_on_singleton [simp]: "totalp_on {x} R"
  by (simp add: totalp_on_def)

lemma (in linorder) totalp_on_less[simp]: "totalp_on A (<)"
  by (auto intro: totalp_onI)

lemma (in linorder) totalp_on_greater[simp]: "totalp_on A (>)"
  by (auto intro: totalp_onI)

lemma (in linorder) totalp_on_le[simp]: "totalp_on A (\<le>)"
  by (rule totalp_onI, rule linear)

lemma (in linorder) totalp_on_ge[simp]: "totalp_on A (\<ge>)"
  by (rule totalp_onI, rule linear)


subsubsection \<open>Left uniqueness\<close>

definition left_unique :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "left_unique R \<longleftrightarrow> (\<forall>x y z. R x z \<longrightarrow> R y z \<longrightarrow> x = y)"

lemma left_uniqueI: "(\<And>x y z. A x z \<Longrightarrow> A y z \<Longrightarrow> x = y) \<Longrightarrow> left_unique A"
  unfolding left_unique_def by blast

lemma left_uniqueD: "left_unique A \<Longrightarrow> A x z \<Longrightarrow> A y z \<Longrightarrow> x = y"
  unfolding left_unique_def by blast

lemma left_unique_iff_Uniq: "left_unique r \<longleftrightarrow> (\<forall>y. \<exists>\<^sub>\<le>\<^sub>1x. r x y)"
  unfolding Uniq_def left_unique_def by blast

lemma left_unique_bot[simp]: "left_unique \<bottom>"
  by (simp add: left_unique_def)

lemma left_unique_mono_strong:
  "left_unique Q \<Longrightarrow> (\<And>x y. R x y \<Longrightarrow> Q x y) \<Longrightarrow> left_unique R"
  by (rule left_uniqueI) (auto dest: left_uniqueD)

lemma left_unique_mono[mono]: "R \<le> Q \<Longrightarrow> left_unique Q \<le> left_unique R"
  using left_unique_mono_strong[of Q R]
  by (simp add: le_fun_def)


subsubsection \<open>Right uniqueness\<close>

definition single_valued :: "('a \<times> 'b) set \<Rightarrow> bool"
  where "single_valued r \<longleftrightarrow> (\<forall>x y. (x, y) \<in> r \<longrightarrow> (\<forall>z. (x, z) \<in> r \<longrightarrow> y = z))"

definition right_unique :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "right_unique R \<longleftrightarrow> (\<forall>x y z. R x y \<longrightarrow> R x z \<longrightarrow> y = z)"

lemma right_unique_single_valued_eq [pred_set_conv]:
  "right_unique (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> single_valued r"
  by (simp add: single_valued_def right_unique_def)

lemma right_unique_iff_Uniq:
  "right_unique r \<longleftrightarrow> (\<forall>x. \<exists>\<^sub>\<le>\<^sub>1y. r x y)"
  unfolding Uniq_def right_unique_def by auto

lemma single_valuedI:
  "(\<And>x y. (x, y) \<in> r \<Longrightarrow> (\<And>z. (x, z) \<in> r \<Longrightarrow> y = z)) \<Longrightarrow> single_valued r"
  unfolding single_valued_def by blast

lemma right_uniqueI: "(\<And>x y z. R x y \<Longrightarrow> R x z \<Longrightarrow> y = z) \<Longrightarrow> right_unique R"
  unfolding right_unique_def by fast

lemma single_valuedD:
  "single_valued r \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (x, z) \<in> r \<Longrightarrow> y = z"
  by (simp add: single_valued_def)

lemma right_uniqueD: "right_unique R \<Longrightarrow> R x y \<Longrightarrow> R x z \<Longrightarrow> y = z"
  unfolding right_unique_def by fast

lemma single_valued_empty [simp]:
  "single_valued {}"
  by (simp add: single_valued_def)

lemma right_unique_bot[simp]: "right_unique \<bottom>"
  by (fact single_valued_empty[to_pred])

lemma right_unique_mono_strong:
  "right_unique Q \<Longrightarrow> (\<And>x y. R x y \<Longrightarrow> Q x y) \<Longrightarrow> right_unique R"
  by (rule right_uniqueI) (auto dest: right_uniqueD)

lemma right_unique_mono[mono]: "R \<le> Q \<Longrightarrow> right_unique Q \<le> right_unique R"
  using right_unique_mono_strong[of Q R]
  by (simp add: le_fun_def)

lemma single_valued_subset:
  "r \<subseteq> s \<Longrightarrow> single_valued s \<Longrightarrow> single_valued r"
  unfolding single_valued_def by blast

lemma right_unique_less_eq: "r \<le> s \<Longrightarrow> right_unique s \<Longrightarrow> right_unique r"
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

lemma trans_on_diff_Id: "trans_on A r \<Longrightarrow> antisym_on A r \<Longrightarrow> trans_on A (r - Id)"
  by (blast intro: trans_onI dest: trans_onD antisym_onD)

lemma trans_diff_Id[no_atp]: "trans r \<Longrightarrow> antisym r \<Longrightarrow> trans (r - Id)"
  using trans_on_diff_Id .

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
  by (rule refl_onI[OF Id_onI])

lemma antisym_Id_on [simp]: "antisym (Id_on A)"
  unfolding antisym_def by blast

lemma sym_Id_on [simp]: "sym (Id_on A)"
  by (rule symI) clarify

lemma trans_Id_on [simp]: "trans (Id_on A)"
  by (fast intro: transI elim: transD)

lemma single_valued_Id_on [simp]: "single_valued (Id_on A)"
  unfolding single_valued_def by blast


subsubsection \<open>Composition\<close>

inductive_set relcomp  :: "('a \<times> 'b) set \<Rightarrow> ('b \<times> 'c) set \<Rightarrow> ('a \<times> 'c) set"
  for r :: "('a \<times> 'b) set" and s :: "('b \<times> 'c) set"
  where relcompI [intro]: "(a, b) \<in> r \<Longrightarrow> (b, c) \<in> s \<Longrightarrow> (a, c) \<in> relcomp r s"

open_bundle relcomp_syntax
begin
notation relcomp  (infixr \<open>O\<close> 75) and relcompp  (infixr \<open>OO\<close> 75)
end

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

inductive_set converse :: "('a \<times> 'b) set \<Rightarrow> ('b \<times> 'a) set"
  for r :: "('a \<times> 'b) set"
  where "(a, b) \<in> r \<Longrightarrow> (b, a) \<in> converse r"

open_bundle converse_syntax
begin
notation
  converse  (\<open>(\<open>notation=\<open>postfix -1\<close>\<close>_\<inverse>)\<close> [1000] 999) and
  conversep  (\<open>(\<open>notation=\<open>postfix -1-1\<close>\<close>_\<inverse>\<inverse>)\<close> [1000] 1000)
notation (ASCII)
  converse  (\<open>(\<open>notation=\<open>postfix -1\<close>\<close>_^-1)\<close> [1000] 999) and
  conversep (\<open>(\<open>notation=\<open>postfix -1-1\<close>\<close>_^--1)\<close> [1000] 1000)
end

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

lemma refl_on_converse [simp]: "refl_on A (r\<inverse>) = refl_on A r"
  by (auto simp: refl_on_def)

lemma reflp_on_conversp [simp]: "reflp_on A R\<inverse>\<inverse> \<longleftrightarrow> reflp_on A R"
  by (auto simp: reflp_on_def)

lemma irrefl_on_converse [simp]: "irrefl_on A (r\<inverse>) = irrefl_on A r"
  by (simp add: irrefl_on_def)

lemma irreflp_on_converse [simp]: "irreflp_on A (r\<inverse>\<inverse>) = irreflp_on A r"
  by (rule irrefl_on_converse[to_pred])

lemma sym_on_converse [simp]: "sym_on A (r\<inverse>) = sym_on A r"
  by (auto intro: sym_onI dest: sym_onD)

lemma symp_on_conversep [simp]: "symp_on A R\<inverse>\<inverse> = symp_on A R"
  by (rule sym_on_converse[to_pred])

lemma asym_on_converse [simp]: "asym_on A (r\<inverse>) = asym_on A r"
  by (auto dest: asym_onD)

lemma asymp_on_conversep [simp]: "asymp_on A R\<inverse>\<inverse> = asymp_on A R"
  by (rule asym_on_converse[to_pred])

lemma antisym_on_converse [simp]: "antisym_on A (r\<inverse>) = antisym_on A r"
  by (auto intro: antisym_onI dest: antisym_onD)

lemma antisymp_on_conversep [simp]: "antisymp_on A R\<inverse>\<inverse> = antisymp_on A R"
  by (rule antisym_on_converse[to_pred])

lemma trans_on_converse [simp]: "trans_on A (r\<inverse>) = trans_on A r"
  by (auto intro: trans_onI dest: trans_onD)

lemma transp_on_conversep [simp]: "transp_on A R\<inverse>\<inverse> = transp_on A R"
  by (rule trans_on_converse[to_pred])

lemma sym_conv_converse_eq: "sym r \<longleftrightarrow> r\<inverse> = r"
  unfolding sym_def by fast

lemma sym_Un_converse: "sym (r \<union> r\<inverse>)"
  unfolding sym_def by blast

lemma sym_Int_converse: "sym (r \<inter> r\<inverse>)"
  unfolding sym_def by blast

lemma total_on_converse [simp]: "total_on A (r\<inverse>) = total_on A r"
  by (auto simp: total_on_def)

lemma totalp_on_converse [simp]: "totalp_on A R\<inverse>\<inverse> = totalp_on A R"
  by (rule total_on_converse[to_pred])

lemma left_unique_conversep[simp]: "left_unique A\<inverse>\<inverse> \<longleftrightarrow> right_unique A"
  by (auto simp add: left_unique_def right_unique_def)

lemma right_unique_conversep[simp]: "right_unique A\<inverse>\<inverse> \<longleftrightarrow> left_unique A"
  by (auto simp add: left_unique_def right_unique_def)

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

lemma Field_iff: "x \<in> Field r \<longleftrightarrow> (\<exists>y. (x,y) \<in> r \<or> (y,x) \<in> r)"
  by (auto simp: Field_def)

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

definition Image :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set"  (infixr \<open>``\<close> 90)
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
lemma Image_INT_eq:
  assumes "single_valued (r\<inverse>)"
    and "A \<noteq> {}"
  shows "r `` (\<Inter>(B ` A)) = (\<Inter>x\<in>A. r `` B x)"
proof(rule equalityI, rule Image_INT_subset)
  show "(\<Inter>x\<in>A. r `` B x) \<subseteq> r `` \<Inter> (B ` A)"
  proof
    fix x
    assume "x \<in> (\<Inter>x\<in>A. r `` B x)"
    then show "x \<in> r `` \<Inter> (B ` A)"
      using assms unfolding single_valued_def by simp blast
  qed
qed

lemma Image_subset_eq: "r``A \<subseteq> B \<longleftrightarrow> A \<subseteq> - ((r\<inverse>) `` (- B))"
  by blast

lemma Image_Collect_case_prod [simp]: "{(x, y). P x y} `` A = {y. \<exists>x\<in>A. P x y}"
  by auto

lemma Sigma_Image: "(SIGMA x:A. B x) `` X = (\<Union>x\<in>X \<inter> A. B x)"
  by auto

lemma relcomp_Image: "(X O Y) `` Z = Y `` (X `` Z)"
  by auto


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

end
