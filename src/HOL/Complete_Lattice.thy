(*  Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel; Florian Haftmann, TU Muenchen *)

header {* Complete lattices, with special focus on sets *}

theory Complete_Lattice
imports Set
begin

notation
  less_eq (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50) and
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) and
  top ("\<top>") and
  bot ("\<bottom>")


subsection {* Syntactic infimum and supremum operations *}

class Inf =
  fixes Inf :: "'a set \<Rightarrow> 'a" ("\<Sqinter>_" [900] 900)

class Sup =
  fixes Sup :: "'a set \<Rightarrow> 'a" ("\<Squnion>_" [900] 900)

subsection {* Abstract complete lattices *}

class complete_lattice = bounded_lattice + Inf + Sup +
  assumes Inf_lower: "x \<in> A \<Longrightarrow> \<Sqinter>A \<sqsubseteq> x"
     and Inf_greatest: "(\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x) \<Longrightarrow> z \<sqsubseteq> \<Sqinter>A"
  assumes Sup_upper: "x \<in> A \<Longrightarrow> x \<sqsubseteq> \<Squnion>A"
     and Sup_least: "(\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> z) \<Longrightarrow> \<Squnion>A \<sqsubseteq> z"
begin

lemma dual_complete_lattice:
  "class.complete_lattice Sup Inf (op \<ge>) (op >) (op \<squnion>) (op \<sqinter>) \<top> \<bottom>"
  by (auto intro!: class.complete_lattice.intro dual_bounded_lattice)
    (unfold_locales, (fact bot_least top_greatest
        Sup_upper Sup_least Inf_lower Inf_greatest)+)

lemma Inf_Sup: "\<Sqinter>A = \<Squnion>{b. \<forall>a \<in> A. b \<sqsubseteq> a}"
  by (auto intro: antisym Inf_lower Inf_greatest Sup_upper Sup_least)

lemma Sup_Inf:  "\<Squnion>A = \<Sqinter>{b. \<forall>a \<in> A. a \<sqsubseteq> b}"
  by (auto intro: antisym Inf_lower Inf_greatest Sup_upper Sup_least)

lemma Inf_empty [simp]:
  "\<Sqinter>{} = \<top>"
  by (auto intro: antisym Inf_greatest)

lemma Sup_empty [simp]:
  "\<Squnion>{} = \<bottom>"
  by (auto intro: antisym Sup_least)

lemma Inf_UNIV [simp]:
  "\<Sqinter>UNIV = \<bottom>"
  by (simp add: Sup_Inf Sup_empty [symmetric])

lemma Sup_UNIV [simp]:
  "\<Squnion>UNIV = \<top>"
  by (simp add: Inf_Sup Inf_empty [symmetric])

lemma Inf_insert: "\<Sqinter>insert a A = a \<sqinter> \<Sqinter>A"
  by (auto intro: le_infI le_infI1 le_infI2 antisym Inf_greatest Inf_lower)

lemma Sup_insert: "\<Squnion>insert a A = a \<squnion> \<Squnion>A"
  by (auto intro: le_supI le_supI1 le_supI2 antisym Sup_least Sup_upper)

lemma Inf_singleton [simp]:
  "\<Sqinter>{a} = a"
  by (auto intro: antisym Inf_lower Inf_greatest)

lemma Sup_singleton [simp]:
  "\<Squnion>{a} = a"
  by (auto intro: antisym Sup_upper Sup_least)

lemma Inf_binary:
  "\<Sqinter>{a, b} = a \<sqinter> b"
  by (simp add: Inf_empty Inf_insert)

lemma Sup_binary:
  "\<Squnion>{a, b} = a \<squnion> b"
  by (simp add: Sup_empty Sup_insert)

lemma le_Inf_iff: "b \<sqsubseteq> \<Sqinter>A \<longleftrightarrow> (\<forall>a\<in>A. b \<sqsubseteq> a)"
  by (auto intro: Inf_greatest dest: Inf_lower)

lemma Sup_le_iff: "\<Squnion>A \<sqsubseteq> b \<longleftrightarrow> (\<forall>a\<in>A. a \<sqsubseteq> b)"
  by (auto intro: Sup_least dest: Sup_upper)

lemma Inf_mono:
  assumes "\<And>b. b \<in> B \<Longrightarrow> \<exists>a\<in>A. a \<sqsubseteq> b"
  shows "\<Sqinter>A \<sqsubseteq> \<Sqinter>B"
proof (rule Inf_greatest)
  fix b assume "b \<in> B"
  with assms obtain a where "a \<in> A" and "a \<sqsubseteq> b" by blast
  from `a \<in> A` have "\<Sqinter>A \<sqsubseteq> a" by (rule Inf_lower)
  with `a \<sqsubseteq> b` show "\<Sqinter>A \<sqsubseteq> b" by auto
qed

lemma Sup_mono:
  assumes "\<And>a. a \<in> A \<Longrightarrow> \<exists>b\<in>B. a \<sqsubseteq> b"
  shows "\<Squnion>A \<sqsubseteq> \<Squnion>B"
proof (rule Sup_least)
  fix a assume "a \<in> A"
  with assms obtain b where "b \<in> B" and "a \<sqsubseteq> b" by blast
  from `b \<in> B` have "b \<sqsubseteq> \<Squnion>B" by (rule Sup_upper)
  with `a \<sqsubseteq> b` show "a \<sqsubseteq> \<Squnion>B" by auto
qed

lemma top_le:
  "\<top> \<sqsubseteq> x \<Longrightarrow> x = \<top>"
  by (rule antisym) auto

lemma le_bot:
  "x \<sqsubseteq> \<bottom> \<Longrightarrow> x = \<bottom>"
  by (rule antisym) auto

lemma not_less_bot[simp]: "\<not> (x \<sqsubset> \<bottom>)"
  using bot_least[of x] by (auto simp: le_less)

lemma not_top_less[simp]: "\<not> (\<top> \<sqsubset> x)"
  using top_greatest[of x] by (auto simp: le_less)

lemma Sup_upper2: "u \<in> A \<Longrightarrow> v \<sqsubseteq> u \<Longrightarrow> v \<sqsubseteq> \<Squnion>A"
  using Sup_upper[of u A] by auto

lemma Inf_lower2: "u \<in> A \<Longrightarrow> u \<sqsubseteq> v \<Longrightarrow> \<Sqinter>A \<sqsubseteq> v"
  using Inf_lower[of u A] by auto

definition INFI :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "INFI A f = \<Sqinter> (f ` A)"

definition SUPR :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "SUPR A f = \<Squnion> (f ` A)"

end

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3INF _./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3INF _:_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3SUP _./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3SUP _:_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

translations
  "INF x y. B"   == "INF x. INF y. B"
  "INF x. B"     == "CONST INFI CONST UNIV (%x. B)"
  "INF x. B"     == "INF x:CONST UNIV. B"
  "INF x:A. B"   == "CONST INFI A (%x. B)"
  "SUP x y. B"   == "SUP x. SUP y. B"
  "SUP x. B"     == "CONST SUPR CONST UNIV (%x. B)"
  "SUP x. B"     == "SUP x:CONST UNIV. B"
  "SUP x:A. B"   == "CONST SUPR A (%x. B)"

print_translation {*
  [Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax INFI} @{syntax_const "_INF"},
    Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax SUPR} @{syntax_const "_SUP"}]
*} -- {* to avoid eta-contraction of body *}

context complete_lattice
begin

lemma SUP_cong: "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> SUPR A f = SUPR A g"
  by (simp add: SUPR_def cong: image_cong)

lemma INF_cong: "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> INFI A f = INFI A g"
  by (simp add: INFI_def cong: image_cong)

lemma le_SUPI: "i \<in> A \<Longrightarrow> M i \<sqsubseteq> (\<Squnion>i\<in>A. M i)"
  by (auto simp add: SUPR_def intro: Sup_upper)

lemma le_SUPI2: "i \<in> A \<Longrightarrow> u \<sqsubseteq> M i \<Longrightarrow> u \<sqsubseteq> (\<Squnion>i\<in>A. M i)"
  using le_SUPI[of i A M] by auto

lemma SUP_leI: "(\<And>i. i \<in> A \<Longrightarrow> M i \<sqsubseteq> u) \<Longrightarrow> (\<Squnion>i\<in>A. M i) \<sqsubseteq> u"
  by (auto simp add: SUPR_def intro: Sup_least)

lemma INF_leI: "i \<in> A \<Longrightarrow> (\<Sqinter>i\<in>A. M i) \<sqsubseteq> M i"
  by (auto simp add: INFI_def intro: Inf_lower)

lemma INF_leI2: "i \<in> A \<Longrightarrow> M i \<sqsubseteq> u \<Longrightarrow> (\<Sqinter>i\<in>A. M i) \<sqsubseteq> u"
  using INF_leI[of i A M] by auto

lemma le_INFI: "(\<And>i. i \<in> A \<Longrightarrow> u \<sqsubseteq> M i) \<Longrightarrow> u \<sqsubseteq> (\<Sqinter>i\<in>A. M i)"
  by (auto simp add: INFI_def intro: Inf_greatest)

lemma SUP_le_iff: "(\<Squnion>i\<in>A. M i) \<sqsubseteq> u \<longleftrightarrow> (\<forall>i \<in> A. M i \<sqsubseteq> u)"
  unfolding SUPR_def by (auto simp add: Sup_le_iff)

lemma le_INF_iff: "u \<sqsubseteq> (\<Sqinter>i\<in>A. M i) \<longleftrightarrow> (\<forall>i \<in> A. u \<sqsubseteq> M i)"
  unfolding INFI_def by (auto simp add: le_Inf_iff)

lemma INF_const[simp]: "A \<noteq> {} \<Longrightarrow> (\<Sqinter>i\<in>A. M) = M"
  by (auto intro: antisym INF_leI le_INFI)

lemma SUP_const[simp]: "A \<noteq> {} \<Longrightarrow> (\<Squnion>i\<in>A. M) = M"
  by (auto intro: antisym SUP_leI le_SUPI)

lemma INF_mono:
  "(\<And>m. m \<in> B \<Longrightarrow> \<exists>n\<in>A. f n \<sqsubseteq> g m) \<Longrightarrow> (\<Sqinter>n\<in>A. f n) \<sqsubseteq> (\<Sqinter>n\<in>B. g n)"
  by (force intro!: Inf_mono simp: INFI_def)

lemma SUP_mono:
  "(\<And>n. n \<in> A \<Longrightarrow> \<exists>m\<in>B. f n \<sqsubseteq> g m) \<Longrightarrow> (\<Squnion>n\<in>A. f n) \<sqsubseteq> (\<Squnion>n\<in>B. g n)"
  by (force intro!: Sup_mono simp: SUPR_def)

lemma INF_subset:  "A \<subseteq> B \<Longrightarrow> INFI B f \<sqsubseteq> INFI A f"
  by (intro INF_mono) auto

lemma SUP_subset:  "A \<subseteq> B \<Longrightarrow> SUPR A f \<sqsubseteq> SUPR B f"
  by (intro SUP_mono) auto

lemma INF_commute: "(\<Sqinter>i\<in>A. \<Sqinter>j\<in>B. f i j) = (\<Sqinter>j\<in>B. \<Sqinter>i\<in>A. f i j)"
  by (iprover intro: INF_leI le_INFI order_trans antisym)

lemma SUP_commute: "(\<Squnion>i\<in>A. \<Squnion>j\<in>B. f i j) = (\<Squnion>j\<in>B. \<Squnion>i\<in>A. f i j)"
  by (iprover intro: SUP_leI le_SUPI order_trans antisym)

end

lemma Inf_less_iff:
  fixes a :: "'a\<Colon>{complete_lattice,linorder}"
  shows "\<Sqinter>S \<sqsubset> a \<longleftrightarrow> (\<exists>x\<in>S. x \<sqsubset> a)"
  unfolding not_le [symmetric] le_Inf_iff by auto

lemma less_Sup_iff:
  fixes a :: "'a\<Colon>{complete_lattice,linorder}"
  shows "a \<sqsubset> \<Squnion>S \<longleftrightarrow> (\<exists>x\<in>S. a \<sqsubset> x)"
  unfolding not_le [symmetric] Sup_le_iff by auto

lemma INF_less_iff:
  fixes a :: "'a::{complete_lattice,linorder}"
  shows "(\<Sqinter>i\<in>A. f i) \<sqsubset> a \<longleftrightarrow> (\<exists>x\<in>A. f x \<sqsubset> a)"
  unfolding INFI_def Inf_less_iff by auto

lemma less_SUP_iff:
  fixes a :: "'a::{complete_lattice,linorder}"
  shows "a \<sqsubset> (\<Squnion>i\<in>A. f i) \<longleftrightarrow> (\<exists>x\<in>A. a \<sqsubset> f x)"
  unfolding SUPR_def less_Sup_iff by auto

subsection {* @{typ bool} and @{typ "_ \<Rightarrow> _"} as complete lattice *}

instantiation bool :: complete_lattice
begin

definition
  "\<Sqinter>A \<longleftrightarrow> (\<forall>x\<in>A. x)"

definition
  "\<Squnion>A \<longleftrightarrow> (\<exists>x\<in>A. x)"

instance proof
qed (auto simp add: Inf_bool_def Sup_bool_def le_bool_def)

end

lemma INFI_bool_eq [simp]:
  "INFI = Ball"
proof (rule ext)+
  fix A :: "'a set"
  fix P :: "'a \<Rightarrow> bool"
  show "(\<Sqinter>x\<in>A. P x) \<longleftrightarrow> (\<forall>x\<in>A. P x)"
    by (auto simp add: Ball_def INFI_def Inf_bool_def)
qed

lemma SUPR_bool_eq [simp]:
  "SUPR = Bex"
proof (rule ext)+
  fix A :: "'a set"
  fix P :: "'a \<Rightarrow> bool"
  show "(\<Squnion>x\<in>A. P x) \<longleftrightarrow> (\<exists>x\<in>A. P x)"
    by (auto simp add: Bex_def SUPR_def Sup_bool_def)
qed

instantiation "fun" :: (type, complete_lattice) complete_lattice
begin

definition
  "\<Sqinter>A = (\<lambda>x. \<Sqinter>{y. \<exists>f\<in>A. y = f x})"

lemma Inf_apply:
  "(\<Sqinter>A) x = \<Sqinter>{y. \<exists>f\<in>A. y = f x}"
  by (simp add: Inf_fun_def)

definition
  "\<Squnion>A = (\<lambda>x. \<Squnion>{y. \<exists>f\<in>A. y = f x})"

lemma Sup_apply:
  "(\<Squnion>A) x = \<Squnion>{y. \<exists>f\<in>A. y = f x}"
  by (simp add: Sup_fun_def)

instance proof
qed (auto simp add: le_fun_def Inf_apply Sup_apply
  intro: Inf_lower Sup_upper Inf_greatest Sup_least)

end

lemma INFI_apply:
  "(\<Sqinter>y\<in>A. f y) x = (\<Sqinter>y\<in>A. f y x)"
  by (auto intro: arg_cong [of _ _ Inf] simp add: INFI_def Inf_apply)

lemma SUPR_apply:
  "(\<Squnion>y\<in>A. f y) x = (\<Squnion>y\<in>A. f y x)"
  by (auto intro: arg_cong [of _ _ Sup] simp add: SUPR_def Sup_apply)


subsection {* Inter *}

abbreviation Inter :: "'a set set \<Rightarrow> 'a set" where
  "Inter S \<equiv> \<Sqinter>S"
  
notation (xsymbols)
  Inter  ("\<Inter>_" [90] 90)

lemma Inter_eq:
  "\<Inter>A = {x. \<forall>B \<in> A. x \<in> B}"
proof (rule set_eqI)
  fix x
  have "(\<forall>Q\<in>{P. \<exists>B\<in>A. P \<longleftrightarrow> x \<in> B}. Q) \<longleftrightarrow> (\<forall>B\<in>A. x \<in> B)"
    by auto
  then show "x \<in> \<Inter>A \<longleftrightarrow> x \<in> {x. \<forall>B \<in> A. x \<in> B}"
    by (simp add: Inf_fun_def Inf_bool_def) (simp add: mem_def)
qed

lemma Inter_iff [simp,no_atp]: "A \<in> \<Inter>C \<longleftrightarrow> (\<forall>X\<in>C. A \<in> X)"
  by (unfold Inter_eq) blast

lemma InterI [intro!]: "(\<And>X. X \<in> C \<Longrightarrow> A \<in> X) \<Longrightarrow> A \<in> \<Inter>C"
  by (simp add: Inter_eq)

text {*
  \medskip A ``destruct'' rule -- every @{term X} in @{term C}
  contains @{term A} as an element, but @{prop "A \<in> X"} can hold when
  @{prop "X \<in> C"} does not!  This rule is analogous to @{text spec}.
*}

lemma InterD [elim, Pure.elim]: "A \<in> \<Inter>C \<Longrightarrow> X \<in> C \<Longrightarrow> A \<in> X"
  by auto

lemma InterE [elim]: "A \<in> \<Inter>C \<Longrightarrow> (X \<notin> C \<Longrightarrow> R) \<Longrightarrow> (A \<in> X \<Longrightarrow> R) \<Longrightarrow> R"
  -- {* ``Classical'' elimination rule -- does not require proving
    @{prop "X \<in> C"}. *}
  by (unfold Inter_eq) blast

lemma Inter_lower: "B \<in> A \<Longrightarrow> \<Inter>A \<subseteq> B"
  by (fact Inf_lower)

lemma (in complete_lattice) Inf_less_eq:
  assumes "\<And>v. v \<in> A \<Longrightarrow> v \<sqsubseteq> u"
    and "A \<noteq> {}"
  shows "\<Sqinter>A \<sqsubseteq> u"
proof -
  from `A \<noteq> {}` obtain v where "v \<in> A" by blast
  moreover with assms have "v \<sqsubseteq> u" by blast
  ultimately show ?thesis by (rule Inf_lower2)
qed

lemma Inter_subset:
  "(\<And>X. X \<in> A \<Longrightarrow> X \<subseteq> B) \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<Inter>A \<subseteq> B"
  by (fact Inf_less_eq)

lemma Inter_greatest: "(\<And>X. X \<in> A \<Longrightarrow> C \<subseteq> X) \<Longrightarrow> C \<subseteq> Inter A"
  by (fact Inf_greatest)

lemma Int_eq_Inter: "A \<inter> B = \<Inter>{A, B}"
  by (fact Inf_binary [symmetric])

lemma Inter_empty [simp]: "\<Inter>{} = UNIV"
  by (fact Inf_empty)

lemma Inter_UNIV [simp]: "\<Inter>UNIV = {}"
  by (fact Inf_UNIV)

lemma Inter_insert [simp]: "\<Inter>(insert a B) = a \<inter> \<Inter>B"
  by (fact Inf_insert)

lemma (in complete_lattice) Inf_inter_less: "\<Sqinter>A \<squnion> \<Sqinter>B \<sqsubseteq> \<Sqinter>(A \<inter> B)"
  by (auto intro: Inf_greatest Inf_lower)

lemma Inter_Un_subset: "\<Inter>A \<union> \<Inter>B \<subseteq> \<Inter>(A \<inter> B)"
  by (fact Inf_inter_less)

lemma (in complete_lattice) Inf_union_distrib: "\<Sqinter>(A \<union> B) = \<Sqinter>A \<sqinter> \<Sqinter>B"
  by (rule antisym) (auto intro: Inf_greatest Inf_lower le_infI1 le_infI2)

lemma Inter_Un_distrib: "\<Inter>(A \<union> B) = \<Inter>A \<inter> \<Inter>B"
  by (fact Inf_union_distrib)

lemma (in complete_lattice) Inf_top_conv [no_atp]:
  "\<Sqinter>A = \<top> \<longleftrightarrow> (\<forall>x\<in>A. x = \<top>)"
  "\<top> = \<Sqinter>A \<longleftrightarrow> (\<forall>x\<in>A. x = \<top>)"
proof -
  show "\<Sqinter>A = \<top> \<longleftrightarrow> (\<forall>x\<in>A. x = \<top>)"
  proof
    assume "\<forall>x\<in>A. x = \<top>"
    then have "A = {} \<or> A = {\<top>}" by auto
    then show "\<Sqinter>A = \<top>" by auto
  next
    assume "\<Sqinter>A = \<top>"
    show "\<forall>x\<in>A. x = \<top>"
    proof (rule ccontr)
      assume "\<not> (\<forall>x\<in>A. x = \<top>)"
      then obtain x where "x \<in> A" and "x \<noteq> \<top>" by blast
      then obtain B where "A = insert x B" by blast
      with `\<Sqinter>A = \<top>` `x \<noteq> \<top>` show False by (simp add: Inf_insert)
    qed
  qed
  then show "\<top> = \<Sqinter>A \<longleftrightarrow> (\<forall>x\<in>A. x = \<top>)" by auto
qed

lemma Inter_UNIV_conv [simp,no_atp]:
  "\<Inter>A = UNIV \<longleftrightarrow> (\<forall>x\<in>A. x = UNIV)"
  "UNIV = \<Inter>A \<longleftrightarrow> (\<forall>x\<in>A. x = UNIV)"
  by (fact Inf_top_conv)+

lemma (in complete_lattice) Inf_anti_mono: "B \<subseteq> A \<Longrightarrow> \<Sqinter>A \<sqsubseteq> \<Sqinter>B"
  by (auto intro: Inf_greatest Inf_lower)

lemma Inter_anti_mono: "B \<subseteq> A \<Longrightarrow> \<Inter>A \<subseteq> \<Inter>B"
  by (fact Inf_anti_mono)


subsection {* Intersections of families *}

abbreviation INTER :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" where
  "INTER \<equiv> INFI"

syntax
  "_INTER1"     :: "pttrns => 'b set => 'b set"           ("(3INT _./ _)" [0, 10] 10)
  "_INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3INT _:_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_INTER1"     :: "pttrns => 'b set => 'b set"           ("(3\<Inter>_./ _)" [0, 10] 10)
  "_INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Inter>_\<in>_./ _)" [0, 0, 10] 10)

syntax (latex output)
  "_INTER1"     :: "pttrns => 'b set => 'b set"           ("(3\<Inter>(00\<^bsub>_\<^esub>)/ _)" [0, 10] 10)
  "_INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Inter>(00\<^bsub>_\<in>_\<^esub>)/ _)" [0, 0, 10] 10)

translations
  "INT x y. B"  == "INT x. INT y. B"
  "INT x. B"    == "CONST INTER CONST UNIV (%x. B)"
  "INT x. B"    == "INT x:CONST UNIV. B"
  "INT x:A. B"  == "CONST INTER A (%x. B)"

print_translation {*
  [Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax INTER} @{syntax_const "_INTER"}]
*} -- {* to avoid eta-contraction of body *}

lemma INTER_eq_Inter_image:
  "(\<Inter>x\<in>A. B x) = \<Inter>(B`A)"
  by (fact INFI_def)
  
lemma Inter_def:
  "\<Inter>S = (\<Inter>x\<in>S. x)"
  by (simp add: INTER_eq_Inter_image image_def)

lemma INTER_def:
  "(\<Inter>x\<in>A. B x) = {y. \<forall>x\<in>A. y \<in> B x}"
  by (auto simp add: INTER_eq_Inter_image Inter_eq)

lemma Inter_image_eq [simp]:
  "\<Inter>(B`A) = (\<Inter>x\<in>A. B x)"
  by (rule sym) (fact INFI_def)

lemma INT_iff [simp]: "b \<in> (\<Inter>x\<in>A. B x) \<longleftrightarrow> (\<forall>x\<in>A. b \<in> B x)"
  by (unfold INTER_def) blast

lemma INT_I [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> b \<in> B x) \<Longrightarrow> b \<in> (\<Inter>x\<in>A. B x)"
  by (unfold INTER_def) blast

lemma INT_D [elim, Pure.elim]: "b : (\<Inter>x\<in>A. B x) \<Longrightarrow> a:A \<Longrightarrow> b: B a"
  by auto

lemma INT_E [elim]: "b : (\<Inter>x\<in>A. B x) \<Longrightarrow> (b: B a \<Longrightarrow> R) \<Longrightarrow> (a~:A \<Longrightarrow> R) \<Longrightarrow> R"
  -- {* "Classical" elimination -- by the Excluded Middle on @{prop "a:A"}. *}
  by (unfold INTER_def) blast

lemma INT_cong [cong]:
    "A = B \<Longrightarrow> (\<And>x. x:B \<Longrightarrow> C x = D x) \<Longrightarrow> (\<Inter>x\<in>A. C x) = (\<Inter>x\<in>B. D x)"
  by (simp add: INTER_def)

lemma Collect_ball_eq: "{x. \<forall>y\<in>A. P x y} = (\<Inter>y\<in>A. {x. P x y})"
  by blast

lemma Collect_all_eq: "{x. \<forall>y. P x y} = (\<Inter>y. {x. P x y})"
  by blast

lemma INT_lower: "a \<in> A \<Longrightarrow> (\<Inter>x\<in>A. B x) \<subseteq> B a"
  by (fact INF_leI)

lemma INT_greatest: "(\<And>x. x \<in> A \<Longrightarrow> C \<subseteq> B x) \<Longrightarrow> C \<subseteq> (\<Inter>x\<in>A. B x)"
  by (fact le_INFI)

lemma INT_empty [simp]: "(\<Inter>x\<in>{}. B x) = UNIV"
  by blast

lemma INT_absorb: "k \<in> I \<Longrightarrow> A k \<inter> (\<Inter>i\<in>I. A i) = (\<Inter>i\<in>I. A i)"
  by blast

lemma INT_subset_iff: "(B \<subseteq> (\<Inter>i\<in>I. A i)) = (\<forall>i\<in>I. B \<subseteq> A i)"
  by (fact le_INF_iff)

lemma INT_insert [simp]: "(\<Inter>x \<in> insert a A. B x) = B a \<inter> INTER A B"
  by blast

lemma INT_Un: "(\<Inter>i \<in> A \<union> B. M i) = (\<Inter>i \<in> A. M i) \<inter> (\<Inter>i\<in>B. M i)"
  by blast

lemma INT_insert_distrib:
    "u \<in> A \<Longrightarrow> (\<Inter>x\<in>A. insert a (B x)) = insert a (\<Inter>x\<in>A. B x)"
  by blast

lemma INT_constant [simp]: "(\<Inter>y\<in>A. c) = (if A = {} then UNIV else c)"
  by auto

lemma INT_eq: "(\<Inter>x\<in>A. B x) = \<Inter>({Y. \<exists>x\<in>A. Y = B x})"
  -- {* Look: it has an \emph{existential} quantifier *}
  by blast

lemma INTER_UNIV_conv[simp]:
 "(UNIV = (\<Inter>x\<in>A. B x)) = (\<forall>x\<in>A. B x = UNIV)"
 "((\<Inter>x\<in>A. B x) = UNIV) = (\<forall>x\<in>A. B x = UNIV)"
by blast+

lemma INT_bool_eq: "(\<Inter>b. A b) = (A True \<inter> A False)"
  by (auto intro: bool_induct)

lemma Pow_INT_eq: "Pow (\<Inter>x\<in>A. B x) = (\<Inter>x\<in>A. Pow (B x))"
  by blast

lemma INT_anti_mono:
  "B \<subseteq> A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<subseteq> g x) \<Longrightarrow>
    (\<Inter>x\<in>A. f x) \<subseteq> (\<Inter>x\<in>A. g x)"
  -- {* The last inclusion is POSITIVE! *}
  by (blast dest: subsetD)

lemma vimage_INT: "f -` (\<Inter>x\<in>A. B x) = (\<Inter>x\<in>A. f -` B x)"
  by blast


subsection {* Union *}

abbreviation Union :: "'a set set \<Rightarrow> 'a set" where
  "Union S \<equiv> \<Squnion>S"

notation (xsymbols)
  Union  ("\<Union>_" [90] 90)

lemma Union_eq:
  "\<Union>A = {x. \<exists>B \<in> A. x \<in> B}"
proof (rule set_eqI)
  fix x
  have "(\<exists>Q\<in>{P. \<exists>B\<in>A. P \<longleftrightarrow> x \<in> B}. Q) \<longleftrightarrow> (\<exists>B\<in>A. x \<in> B)"
    by auto
  then show "x \<in> \<Union>A \<longleftrightarrow> x \<in> {x. \<exists>B\<in>A. x \<in> B}"
    by (simp add: Sup_fun_def Sup_bool_def) (simp add: mem_def)
qed

lemma Union_iff [simp, no_atp]:
  "A \<in> \<Union>C \<longleftrightarrow> (\<exists>X\<in>C. A\<in>X)"
  by (unfold Union_eq) blast

lemma UnionI [intro]:
  "X \<in> C \<Longrightarrow> A \<in> X \<Longrightarrow> A \<in> \<Union>C"
  -- {* The order of the premises presupposes that @{term C} is rigid;
    @{term A} may be flexible. *}
  by auto

lemma UnionE [elim!]:
  "A \<in> \<Union>C \<Longrightarrow> (\<And>X. A \<in> X \<Longrightarrow> X \<in> C \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

lemma Union_upper: "B \<in> A \<Longrightarrow> B \<subseteq> \<Union>A"
  by (iprover intro: subsetI UnionI)

lemma Union_least: "(\<And>X. X \<in> A \<Longrightarrow> X \<subseteq> C) \<Longrightarrow> \<Union>A \<subseteq> C"
  by (iprover intro: subsetI elim: UnionE dest: subsetD)

lemma Un_eq_Union: "A \<union> B = \<Union>{A, B}"
  by blast

lemma Union_empty [simp]: "\<Union>{} = {}"
  by blast

lemma Union_UNIV [simp]: "\<Union>UNIV = UNIV"
  by blast

lemma Union_insert [simp]: "\<Union>insert a B = a \<union> \<Union>B"
  by blast

lemma Union_Un_distrib [simp]: "\<Union>(A \<union> B) = \<Union>A \<union> \<Union>B"
  by blast

lemma Union_Int_subset: "\<Union>(A \<inter> B) \<subseteq> \<Union>A \<inter> \<Union>B"
  by blast

lemma Union_empty_conv [simp,no_atp]: "(\<Union>A = {}) \<longleftrightarrow> (\<forall>x\<in>A. x = {})"
  by blast

lemma empty_Union_conv [simp,no_atp]: "({} = \<Union>A) \<longleftrightarrow> (\<forall>x\<in>A. x = {})"
  by blast

lemma Union_disjoint: "(\<Union>C \<inter> A = {}) \<longleftrightarrow> (\<forall>B\<in>C. B \<inter> A = {})"
  by blast

lemma subset_Pow_Union: "A \<subseteq> Pow (\<Union>A)"
  by blast

lemma Union_Pow_eq [simp]: "\<Union>(Pow A) = A"
  by blast

lemma Union_mono: "A \<subseteq> B \<Longrightarrow> \<Union>A \<subseteq> \<Union>B"
  by blast


subsection {* Unions of families *}

abbreviation UNION :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" where
  "UNION \<equiv> SUPR"

syntax
  "_UNION1"     :: "pttrns => 'b set => 'b set"           ("(3UN _./ _)" [0, 10] 10)
  "_UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3UN _:_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_UNION1"     :: "pttrns => 'b set => 'b set"           ("(3\<Union>_./ _)" [0, 10] 10)
  "_UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>_\<in>_./ _)" [0, 0, 10] 10)

syntax (latex output)
  "_UNION1"     :: "pttrns => 'b set => 'b set"           ("(3\<Union>(00\<^bsub>_\<^esub>)/ _)" [0, 10] 10)
  "_UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>(00\<^bsub>_\<in>_\<^esub>)/ _)" [0, 0, 10] 10)

translations
  "UN x y. B"   == "UN x. UN y. B"
  "UN x. B"     == "CONST UNION CONST UNIV (%x. B)"
  "UN x. B"     == "UN x:CONST UNIV. B"
  "UN x:A. B"   == "CONST UNION A (%x. B)"

text {*
  Note the difference between ordinary xsymbol syntax of indexed
  unions and intersections (e.g.\ @{text"\<Union>a\<^isub>1\<in>A\<^isub>1. B"})
  and their \LaTeX\ rendition: @{term"\<Union>a\<^isub>1\<in>A\<^isub>1. B"}. The
  former does not make the index expression a subscript of the
  union/intersection symbol because this leads to problems with nested
  subscripts in Proof General.
*}

print_translation {*
  [Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax UNION} @{syntax_const "_UNION"}]
*} -- {* to avoid eta-contraction of body *}

lemma UNION_eq_Union_image:
  "(\<Union>x\<in>A. B x) = \<Union>(B ` A)"
  by (fact SUPR_def)

lemma Union_def:
  "\<Union>S = (\<Union>x\<in>S. x)"
  by (simp add: UNION_eq_Union_image image_def)

lemma UNION_def [no_atp]:
  "(\<Union>x\<in>A. B x) = {y. \<exists>x\<in>A. y \<in> B x}"
  by (auto simp add: UNION_eq_Union_image Union_eq)
  
lemma Union_image_eq [simp]:
  "\<Union>(B ` A) = (\<Union>x\<in>A. B x)"
  by (rule sym) (fact UNION_eq_Union_image)
  
lemma UN_iff [simp]: "(b: (\<Union>x\<in>A. B x)) = (\<exists>x\<in>A. b: B x)"
  by (unfold UNION_def) blast

lemma UN_I [intro]: "a:A \<Longrightarrow> b: B a \<Longrightarrow> b: (\<Union>x\<in>A. B x)"
  -- {* The order of the premises presupposes that @{term A} is rigid;
    @{term b} may be flexible. *}
  by auto

lemma UN_E [elim!]: "b : (\<Union>x\<in>A. B x) \<Longrightarrow> (\<And>x. x:A \<Longrightarrow> b: B x \<Longrightarrow> R) \<Longrightarrow> R"
  by (unfold UNION_def) blast

lemma UN_cong [cong]:
    "A = B \<Longrightarrow> (\<And>x. x:B \<Longrightarrow> C x = D x) \<Longrightarrow> (\<Union>x\<in>A. C x) = (\<Union>x\<in>B. D x)"
  by (simp add: UNION_def)

lemma strong_UN_cong:
    "A = B \<Longrightarrow> (\<And>x. x:B =simp=> C x = D x) \<Longrightarrow> (\<Union>x\<in>A. C x) = (\<Union>x\<in>B. D x)"
  by (simp add: UNION_def simp_implies_def)

lemma image_eq_UN: "f ` A = (\<Union>x\<in>A. {f x})"
  by blast

lemma UN_upper: "a \<in> A \<Longrightarrow> B a \<subseteq> (\<Union>x\<in>A. B x)"
  by (fact le_SUPI)

lemma UN_least: "(\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C) \<Longrightarrow> (\<Union>x\<in>A. B x) \<subseteq> C"
  by (iprover intro: subsetI elim: UN_E dest: subsetD)

lemma Collect_bex_eq [no_atp]: "{x. \<exists>y\<in>A. P x y} = (\<Union>y\<in>A. {x. P x y})"
  by blast

lemma UN_insert_distrib: "u \<in> A \<Longrightarrow> (\<Union>x\<in>A. insert a (B x)) = insert a (\<Union>x\<in>A. B x)"
  by blast

lemma UN_empty [simp,no_atp]: "(\<Union>x\<in>{}. B x) = {}"
  by blast

lemma UN_empty2 [simp]: "(\<Union>x\<in>A. {}) = {}"
  by blast

lemma UN_singleton [simp]: "(\<Union>x\<in>A. {x}) = A"
  by blast

lemma UN_absorb: "k \<in> I \<Longrightarrow> A k \<union> (\<Union>i\<in>I. A i) = (\<Union>i\<in>I. A i)"
  by auto

lemma UN_insert [simp]: "(\<Union>x\<in>insert a A. B x) = B a \<union> UNION A B"
  by blast

lemma UN_Un[simp]: "(\<Union>i \<in> A \<union> B. M i) = (\<Union>i\<in>A. M i) \<union> (\<Union>i\<in>B. M i)"
  by blast

lemma UN_UN_flatten: "(\<Union>x \<in> (\<Union>y\<in>A. B y). C x) = (\<Union>y\<in>A. \<Union>x\<in>B y. C x)"
  by blast

lemma UN_subset_iff: "((\<Union>i\<in>I. A i) \<subseteq> B) = (\<forall>i\<in>I. A i \<subseteq> B)"
  by (fact SUP_le_iff)

lemma image_Union: "f ` \<Union>S = (\<Union>x\<in>S. f ` x)"
  by blast

lemma UN_constant [simp]: "(\<Union>y\<in>A. c) = (if A = {} then {} else c)"
  by auto

lemma UN_eq: "(\<Union>x\<in>A. B x) = \<Union>({Y. \<exists>x\<in>A. Y = B x})"
  by blast

lemma UNION_empty_conv[simp]:
  "{} = (\<Union>x\<in>A. B x) \<longleftrightarrow> (\<forall>x\<in>A. B x = {})"
  "(\<Union>x\<in>A. B x) = {} \<longleftrightarrow> (\<forall>x\<in>A. B x = {})"
by blast+

lemma Collect_ex_eq [no_atp]: "{x. \<exists>y. P x y} = (\<Union>y. {x. P x y})"
  by blast

lemma ball_UN: "(\<forall>z \<in> UNION A B. P z) = (\<forall>x\<in>A. \<forall>z \<in> B x. P z)"
  by blast

lemma bex_UN: "(\<exists>z \<in> UNION A B. P z) = (\<exists>x\<in>A. \<exists>z\<in>B x. P z)"
  by blast

lemma Un_eq_UN: "A \<union> B = (\<Union>b. if b then A else B)"
  by (auto simp add: split_if_mem2)

lemma UN_bool_eq: "(\<Union>b. A b) = (A True \<union> A False)"
  by (auto intro: bool_contrapos)

lemma UN_Pow_subset: "(\<Union>x\<in>A. Pow (B x)) \<subseteq> Pow (\<Union>x\<in>A. B x)"
  by blast

lemma UN_mono:
  "A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<subseteq> g x) \<Longrightarrow>
    (\<Union>x\<in>A. f x) \<subseteq> (\<Union>x\<in>B. g x)"
  by (blast dest: subsetD)

lemma vimage_Union: "f -` (\<Union>A) = (\<Union>X\<in>A. f -` X)"
  by blast

lemma vimage_UN: "f -` (\<Union>x\<in>A. B x) = (\<Union>x\<in>A. f -` B x)"
  by blast

lemma vimage_eq_UN: "f -` B = (\<Union>y\<in>B. f -` {y})"
  -- {* NOT suitable for rewriting *}
  by blast

lemma image_UN: "f ` UNION A B = (\<Union>x\<in>A. f ` B x)"
  by blast


subsection {* Distributive laws *}

lemma Int_Union: "A \<inter> \<Union>B = (\<Union>C\<in>B. A \<inter> C)"
  by blast

lemma Int_Union2: "\<Union>B \<inter> A = (\<Union>C\<in>B. C \<inter> A)"
  by blast

lemma Un_Union_image: "(\<Union>x\<in>C. A x \<union> B x) = \<Union>(A ` C) \<union> \<Union>(B ` C)"
  -- {* Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5: *}
  -- {* Union of a family of unions *}
  by blast

lemma UN_Un_distrib: "(\<Union>i\<in>I. A i \<union> B i) = (\<Union>i\<in>I. A i) \<union> (\<Union>i\<in>I. B i)"
  -- {* Equivalent version *}
  by blast

lemma Un_Inter: "A \<union> \<Inter>B = (\<Inter>C\<in>B. A \<union> C)"
  by blast

lemma Int_Inter_image: "(\<Inter>x\<in>C. A x \<inter> B x) = \<Inter>(A ` C) \<inter> \<Inter>(B ` C)"
  by blast

lemma INT_Int_distrib: "(\<Inter>i\<in>I. A i \<inter> B i) = (\<Inter>i\<in>I. A i) \<inter> (\<Inter>i\<in>I. B i)"
  -- {* Equivalent version *}
  by blast

lemma Int_UN_distrib: "B \<inter> (\<Union>i\<in>I. A i) = (\<Union>i\<in>I. B \<inter> A i)"
  -- {* Halmos, Naive Set Theory, page 35. *}
  by blast

lemma Un_INT_distrib: "B \<union> (\<Inter>i\<in>I. A i) = (\<Inter>i\<in>I. B \<union> A i)"
  by blast

lemma Int_UN_distrib2: "(\<Union>i\<in>I. A i) \<inter> (\<Union>j\<in>J. B j) = (\<Union>i\<in>I. \<Union>j\<in>J. A i \<inter> B j)"
  by blast

lemma Un_INT_distrib2: "(\<Inter>i\<in>I. A i) \<union> (\<Inter>j\<in>J. B j) = (\<Inter>i\<in>I. \<Inter>j\<in>J. A i \<union> B j)"
  by blast


subsection {* Complement *}

lemma Compl_UN [simp]: "- (\<Union>x\<in>A. B x) = (\<Inter>x\<in>A. -B x)"
  by blast

lemma Compl_INT [simp]: "- (\<Inter>x\<in>A. B x) = (\<Union>x\<in>A. -B x)"
  by blast


subsection {* Miniscoping and maxiscoping *}

text {* \medskip Miniscoping: pushing in quantifiers and big Unions
           and Intersections. *}

lemma UN_simps [simp]:
  "\<And>a B C. (\<Union>x\<in>C. insert a (B x)) = (if C={} then {} else insert a (\<Union>x\<in>C. B x))"
  "\<And>A B C. (\<Union>x\<in>C. A x Un B)   = ((if C={} then {} else (\<Union>x\<in>C. A x) Un B))"
  "\<And>A B C. (\<Union>x\<in>C. A Un B x)   = ((if C={} then {} else A Un (\<Union>x\<in>C. B x)))"
  "\<And>A B C. (\<Union>x\<in>C. A x Int B)  = ((\<Union>x\<in>C. A x) Int B)"
  "\<And>A B C. (\<Union>x\<in>C. A Int B x)  = (A Int (\<Union>x\<in>C. B x))"
  "\<And>A B C. (\<Union>x\<in>C. A x - B)    = ((\<Union>x\<in>C. A x) - B)"
  "\<And>A B C. (\<Union>x\<in>C. A - B x)    = (A - (\<Inter>x\<in>C. B x))"
  "\<And>A B. (UN x: \<Union>A. B x) = (UN y:A. UN x:y. B x)"
  "\<And>A B C. (UN z: UNION A B. C z) = (UN  x:A. UN z: B(x). C z)"
  "\<And>A B f. (UN x:f`A. B x)     = (UN a:A. B (f a))"
  by auto

lemma INT_simps [simp]:
  "\<And>A B C. (\<Inter>x\<in>C. A x Int B) = (if C={} then UNIV else (\<Inter>x\<in>C. A x) Int B)"
  "\<And>A B C. (\<Inter>x\<in>C. A Int B x) = (if C={} then UNIV else A Int (\<Inter>x\<in>C. B x))"
  "\<And>A B C. (\<Inter>x\<in>C. A x - B)   = (if C={} then UNIV else (\<Inter>x\<in>C. A x) - B)"
  "\<And>A B C. (\<Inter>x\<in>C. A - B x)   = (if C={} then UNIV else A - (\<Union>x\<in>C. B x))"
  "\<And>a B C. (\<Inter>x\<in>C. insert a (B x)) = insert a (\<Inter>x\<in>C. B x)"
  "\<And>A B C. (\<Inter>x\<in>C. A x Un B)  = ((\<Inter>x\<in>C. A x) Un B)"
  "\<And>A B C. (\<Inter>x\<in>C. A Un B x)  = (A Un (\<Inter>x\<in>C. B x))"
  "\<And>A B. (INT x: \<Union>A. B x) = (\<Inter>y\<in>A. INT x:y. B x)"
  "\<And>A B C. (INT z: UNION A B. C z) = (\<Inter>x\<in>A. INT z: B(x). C z)"
  "\<And>A B f. (INT x:f`A. B x)    = (INT a:A. B (f a))"
  by auto

lemma ball_simps [simp,no_atp]:
  "\<And>A P Q. (\<forall>x\<in>A. P x | Q) = ((\<forall>x\<in>A. P x) | Q)"
  "\<And>A P Q. (\<forall>x\<in>A. P | Q x) = (P | (\<forall>x\<in>A. Q x))"
  "\<And>A P Q. (\<forall>x\<in>A. P --> Q x) = (P --> (\<forall>x\<in>A. Q x))"
  "\<And>A P Q. (\<forall>x\<in>A. P x --> Q) = ((\<exists>x\<in>A. P x) --> Q)"
  "\<And>P. (ALL x:{}. P x) = True"
  "\<And>P. (ALL x:UNIV. P x) = (ALL x. P x)"
  "\<And>a B P. (ALL x:insert a B. P x) = (P a & (ALL x:B. P x))"
  "\<And>A P. (ALL x:\<Union>A. P x) = (ALL y:A. ALL x:y. P x)"
  "\<And>A B P. (ALL x: UNION A B. P x) = (ALL a:A. ALL x: B a. P x)"
  "\<And>P Q. (ALL x:Collect Q. P x) = (ALL x. Q x --> P x)"
  "\<And>A P f. (ALL x:f`A. P x) = (\<forall>x\<in>A. P (f x))"
  "\<And>A P. (~(\<forall>x\<in>A. P x)) = (\<exists>x\<in>A. ~P x)"
  by auto

lemma bex_simps [simp,no_atp]:
  "\<And>A P Q. (\<exists>x\<in>A. P x & Q) = ((\<exists>x\<in>A. P x) & Q)"
  "\<And>A P Q. (\<exists>x\<in>A. P & Q x) = (P & (\<exists>x\<in>A. Q x))"
  "\<And>P. (EX x:{}. P x) = False"
  "\<And>P. (EX x:UNIV. P x) = (EX x. P x)"
  "\<And>a B P. (EX x:insert a B. P x) = (P(a) | (EX x:B. P x))"
  "\<And>A P. (EX x:\<Union>A. P x) = (EX y:A. EX x:y. P x)"
  "\<And>A B P. (EX x: UNION A B. P x) = (EX a:A. EX x:B a. P x)"
  "\<And>P Q. (EX x:Collect Q. P x) = (EX x. Q x & P x)"
  "\<And>A P f. (EX x:f`A. P x) = (\<exists>x\<in>A. P (f x))"
  "\<And>A P. (~(\<exists>x\<in>A. P x)) = (\<forall>x\<in>A. ~P x)"
  by auto

text {* \medskip Maxiscoping: pulling out big Unions and Intersections. *}

lemma UN_extend_simps:
  "\<And>a B C. insert a (\<Union>x\<in>C. B x) = (if C={} then {a} else (\<Union>x\<in>C. insert a (B x)))"
  "\<And>A B C. (\<Union>x\<in>C. A x) Un B    = (if C={} then B else (\<Union>x\<in>C. A x Un B))"
  "\<And>A B C. A Un (\<Union>x\<in>C. B x)   = (if C={} then A else (\<Union>x\<in>C. A Un B x))"
  "\<And>A B C. ((\<Union>x\<in>C. A x) Int B) = (\<Union>x\<in>C. A x Int B)"
  "\<And>A B C. (A Int (\<Union>x\<in>C. B x)) = (\<Union>x\<in>C. A Int B x)"
  "\<And>A B C. ((\<Union>x\<in>C. A x) - B) = (\<Union>x\<in>C. A x - B)"
  "\<And>A B C. (A - (\<Inter>x\<in>C. B x)) = (\<Union>x\<in>C. A - B x)"
  "\<And>A B. (UN y:A. UN x:y. B x) = (UN x: \<Union>A. B x)"
  "\<And>A B C. (UN  x:A. UN z: B(x). C z) = (UN z: UNION A B. C z)"
  "\<And>A B f. (UN a:A. B (f a)) = (UN x:f`A. B x)"
  by auto

lemma INT_extend_simps:
  "\<And>A B C. (\<Inter>x\<in>C. A x) Int B = (if C={} then B else (\<Inter>x\<in>C. A x Int B))"
  "\<And>A B C. A Int (\<Inter>x\<in>C. B x) = (if C={} then A else (\<Inter>x\<in>C. A Int B x))"
  "\<And>A B C. (\<Inter>x\<in>C. A x) - B   = (if C={} then UNIV-B else (\<Inter>x\<in>C. A x - B))"
  "\<And>A B C. A - (\<Union>x\<in>C. B x)   = (if C={} then A else (\<Inter>x\<in>C. A - B x))"
  "\<And>a B C. insert a (\<Inter>x\<in>C. B x) = (\<Inter>x\<in>C. insert a (B x))"
  "\<And>A B C. ((\<Inter>x\<in>C. A x) Un B)  = (\<Inter>x\<in>C. A x Un B)"
  "\<And>A B C. A Un (\<Inter>x\<in>C. B x)  = (\<Inter>x\<in>C. A Un B x)"
  "\<And>A B. (\<Inter>y\<in>A. INT x:y. B x) = (INT x: \<Union>A. B x)"
  "\<And>A B C. (\<Inter>x\<in>A. INT z: B(x). C z) = (INT z: UNION A B. C z)"
  "\<And>A B f. (INT a:A. B (f a))    = (INT x:f`A. B x)"
  by auto


no_notation
  less_eq  (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50) and
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) and
  Inf  ("\<Sqinter>_" [900] 900) and
  Sup  ("\<Squnion>_" [900] 900)

no_syntax (xsymbols)
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

lemmas mem_simps =
  insert_iff empty_iff Un_iff Int_iff Compl_iff Diff_iff
  mem_Collect_eq UN_iff Union_iff INT_iff Inter_iff
  -- {* Each of these has ALREADY been added @{text "[simp]"} above. *}

end
