(*  Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel; Florian Haftmann, TU Muenchen *)

header {* Complete lattices *}

theory Complete_Lattices
imports Fun
begin

notation
  less_eq (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50)


subsection {* Syntactic infimum and supremum operations *}

class Inf =
  fixes Inf :: "'a set \<Rightarrow> 'a" ("\<Sqinter>_" [900] 900)
begin

definition INFIMUM :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where
  INF_def: "INFIMUM A f = \<Sqinter>(f ` A)"

lemma Inf_image_eq [simp]:
  "\<Sqinter>(f ` A) = INFIMUM A f"
  by (simp add: INF_def)

lemma INF_image [simp]:
  "INFIMUM (f ` A) g = INFIMUM A (g \<circ> f)"
  by (simp only: INF_def image_comp)

lemma INF_identity_eq [simp]:
  "INFIMUM A (\<lambda>x. x) = \<Sqinter>A"
  by (simp add: INF_def)

lemma INF_id_eq [simp]:
  "INFIMUM A id = \<Sqinter>A"
  by (simp add: id_def)

lemma INF_cong:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C x = D x) \<Longrightarrow> INFIMUM A C = INFIMUM B D"
  by (simp add: INF_def image_def)

lemma strong_INF_cong [cong]:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B =simp=> C x = D x) \<Longrightarrow> INFIMUM A C = INFIMUM B D"
  unfolding simp_implies_def by (fact INF_cong)

end

class Sup =
  fixes Sup :: "'a set \<Rightarrow> 'a" ("\<Squnion>_" [900] 900)
begin

definition SUPREMUM :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where
  SUP_def: "SUPREMUM A f = \<Squnion>(f ` A)"

lemma Sup_image_eq [simp]:
  "\<Squnion>(f ` A) = SUPREMUM A f"
  by (simp add: SUP_def)

lemma SUP_image [simp]:
  "SUPREMUM (f ` A) g = SUPREMUM A (g \<circ> f)"
  by (simp only: SUP_def image_comp)

lemma SUP_identity_eq [simp]:
  "SUPREMUM A (\<lambda>x. x) = \<Squnion>A"
  by (simp add: SUP_def)

lemma SUP_id_eq [simp]:
  "SUPREMUM A id = \<Squnion>A"
  by (simp add: id_def)

lemma SUP_cong:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C x = D x) \<Longrightarrow> SUPREMUM A C = SUPREMUM B D"
  by (simp add: SUP_def image_def)

lemma strong_SUP_cong [cong]:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B =simp=> C x = D x) \<Longrightarrow> SUPREMUM A C = SUPREMUM B D"
  unfolding simp_implies_def by (fact SUP_cong)

end

text {*
  Note: must use names @{const INFIMUM} and @{const SUPREMUM} here instead of
  @{text INF} and @{text SUP} to allow the following syntax coexist
  with the plain constant names.
*}

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
  "INF x. B"     == "CONST INFIMUM CONST UNIV (%x. B)"
  "INF x. B"     == "INF x:CONST UNIV. B"
  "INF x:A. B"   == "CONST INFIMUM A (%x. B)"
  "SUP x y. B"   == "SUP x. SUP y. B"
  "SUP x. B"     == "CONST SUPREMUM CONST UNIV (%x. B)"
  "SUP x. B"     == "SUP x:CONST UNIV. B"
  "SUP x:A. B"   == "CONST SUPREMUM A (%x. B)"

print_translation {*
  [Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax INFIMUM} @{syntax_const "_INF"},
    Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax SUPREMUM} @{syntax_const "_SUP"}]
*} -- {* to avoid eta-contraction of body *}

subsection {* Abstract complete lattices *}

text {* A complete lattice always has a bottom and a top,
so we include them into the following type class,
along with assumptions that define bottom and top
in terms of infimum and supremum. *}

class complete_lattice = lattice + Inf + Sup + bot + top +
  assumes Inf_lower: "x \<in> A \<Longrightarrow> \<Sqinter>A \<sqsubseteq> x"
     and Inf_greatest: "(\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x) \<Longrightarrow> z \<sqsubseteq> \<Sqinter>A"
  assumes Sup_upper: "x \<in> A \<Longrightarrow> x \<sqsubseteq> \<Squnion>A"
     and Sup_least: "(\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> z) \<Longrightarrow> \<Squnion>A \<sqsubseteq> z"
  assumes Inf_empty [simp]: "\<Sqinter>{} = \<top>"
  assumes Sup_empty [simp]: "\<Squnion>{} = \<bottom>"
begin

subclass bounded_lattice
proof
  fix a
  show "\<bottom> \<le> a" by (auto intro: Sup_least simp only: Sup_empty [symmetric])
  show "a \<le> \<top>" by (auto intro: Inf_greatest simp only: Inf_empty [symmetric])
qed

lemma dual_complete_lattice:
  "class.complete_lattice Sup Inf sup (op \<ge>) (op >) inf \<top> \<bottom>"
  by (auto intro!: class.complete_lattice.intro dual_lattice)
    (unfold_locales, (fact Inf_empty Sup_empty
        Sup_upper Sup_least Inf_lower Inf_greatest)+)

end

context complete_lattice
begin

lemma INF_foundation_dual:
  "Sup.SUPREMUM Inf = INFIMUM"
  by (simp add: fun_eq_iff Sup.SUP_def)

lemma SUP_foundation_dual:
  "Inf.INFIMUM Sup = SUPREMUM"
  by (simp add: fun_eq_iff Inf.INF_def)

lemma Sup_eqI:
  "(\<And>y. y \<in> A \<Longrightarrow> y \<le> x) \<Longrightarrow> (\<And>y. (\<And>z. z \<in> A \<Longrightarrow> z \<le> y) \<Longrightarrow> x \<le> y) \<Longrightarrow> \<Squnion>A = x"
  by (blast intro: antisym Sup_least Sup_upper)

lemma Inf_eqI:
  "(\<And>i. i \<in> A \<Longrightarrow> x \<le> i) \<Longrightarrow> (\<And>y. (\<And>i. i \<in> A \<Longrightarrow> y \<le> i) \<Longrightarrow> y \<le> x) \<Longrightarrow> \<Sqinter>A = x"
  by (blast intro: antisym Inf_greatest Inf_lower)

lemma SUP_eqI:
  "(\<And>i. i \<in> A \<Longrightarrow> f i \<le> x) \<Longrightarrow> (\<And>y. (\<And>i. i \<in> A \<Longrightarrow> f i \<le> y) \<Longrightarrow> x \<le> y) \<Longrightarrow> (\<Squnion>i\<in>A. f i) = x"
  using Sup_eqI [of "f ` A" x] by auto

lemma INF_eqI:
  "(\<And>i. i \<in> A \<Longrightarrow> x \<le> f i) \<Longrightarrow> (\<And>y. (\<And>i. i \<in> A \<Longrightarrow> f i \<ge> y) \<Longrightarrow> x \<ge> y) \<Longrightarrow> (\<Sqinter>i\<in>A. f i) = x"
  using Inf_eqI [of "f ` A" x] by auto

lemma INF_lower: "i \<in> A \<Longrightarrow> (\<Sqinter>i\<in>A. f i) \<sqsubseteq> f i"
  using Inf_lower [of _ "f ` A"] by simp

lemma INF_greatest: "(\<And>i. i \<in> A \<Longrightarrow> u \<sqsubseteq> f i) \<Longrightarrow> u \<sqsubseteq> (\<Sqinter>i\<in>A. f i)"
  using Inf_greatest [of "f ` A"] by auto

lemma SUP_upper: "i \<in> A \<Longrightarrow> f i \<sqsubseteq> (\<Squnion>i\<in>A. f i)"
  using Sup_upper [of _ "f ` A"] by simp

lemma SUP_least: "(\<And>i. i \<in> A \<Longrightarrow> f i \<sqsubseteq> u) \<Longrightarrow> (\<Squnion>i\<in>A. f i) \<sqsubseteq> u"
  using Sup_least [of "f ` A"] by auto

lemma Inf_lower2: "u \<in> A \<Longrightarrow> u \<sqsubseteq> v \<Longrightarrow> \<Sqinter>A \<sqsubseteq> v"
  using Inf_lower [of u A] by auto

lemma INF_lower2: "i \<in> A \<Longrightarrow> f i \<sqsubseteq> u \<Longrightarrow> (\<Sqinter>i\<in>A. f i) \<sqsubseteq> u"
  using INF_lower [of i A f] by auto

lemma Sup_upper2: "u \<in> A \<Longrightarrow> v \<sqsubseteq> u \<Longrightarrow> v \<sqsubseteq> \<Squnion>A"
  using Sup_upper [of u A] by auto

lemma SUP_upper2: "i \<in> A \<Longrightarrow> u \<sqsubseteq> f i \<Longrightarrow> u \<sqsubseteq> (\<Squnion>i\<in>A. f i)"
  using SUP_upper [of i A f] by auto

lemma le_Inf_iff: "b \<sqsubseteq> \<Sqinter>A \<longleftrightarrow> (\<forall>a\<in>A. b \<sqsubseteq> a)"
  by (auto intro: Inf_greatest dest: Inf_lower)

lemma le_INF_iff: "u \<sqsubseteq> (\<Sqinter>i\<in>A. f i) \<longleftrightarrow> (\<forall>i\<in>A. u \<sqsubseteq> f i)"
  using le_Inf_iff [of _ "f ` A"] by simp

lemma Sup_le_iff: "\<Squnion>A \<sqsubseteq> b \<longleftrightarrow> (\<forall>a\<in>A. a \<sqsubseteq> b)"
  by (auto intro: Sup_least dest: Sup_upper)

lemma SUP_le_iff: "(\<Squnion>i\<in>A. f i) \<sqsubseteq> u \<longleftrightarrow> (\<forall>i\<in>A. f i \<sqsubseteq> u)"
  using Sup_le_iff [of "f ` A"] by simp

lemma Inf_insert [simp]: "\<Sqinter>insert a A = a \<sqinter> \<Sqinter>A"
  by (auto intro: le_infI le_infI1 le_infI2 antisym Inf_greatest Inf_lower)

lemma INF_insert [simp]: "(\<Sqinter>x\<in>insert a A. f x) = f a \<sqinter> INFIMUM A f"
  unfolding INF_def Inf_insert by simp

lemma Sup_insert [simp]: "\<Squnion>insert a A = a \<squnion> \<Squnion>A"
  by (auto intro: le_supI le_supI1 le_supI2 antisym Sup_least Sup_upper)

lemma SUP_insert [simp]: "(\<Squnion>x\<in>insert a A. f x) = f a \<squnion> SUPREMUM A f"
  unfolding SUP_def Sup_insert by simp

lemma INF_empty [simp]: "(\<Sqinter>x\<in>{}. f x) = \<top>"
  by (simp add: INF_def)

lemma SUP_empty [simp]: "(\<Squnion>x\<in>{}. f x) = \<bottom>"
  by (simp add: SUP_def)

lemma Inf_UNIV [simp]:
  "\<Sqinter>UNIV = \<bottom>"
  by (auto intro!: antisym Inf_lower)

lemma Sup_UNIV [simp]:
  "\<Squnion>UNIV = \<top>"
  by (auto intro!: antisym Sup_upper)

lemma Inf_Sup: "\<Sqinter>A = \<Squnion>{b. \<forall>a \<in> A. b \<sqsubseteq> a}"
  by (auto intro: antisym Inf_lower Inf_greatest Sup_upper Sup_least)

lemma Sup_Inf:  "\<Squnion>A = \<Sqinter>{b. \<forall>a \<in> A. a \<sqsubseteq> b}"
  by (auto intro: antisym Inf_lower Inf_greatest Sup_upper Sup_least)

lemma Inf_superset_mono: "B \<subseteq> A \<Longrightarrow> \<Sqinter>A \<sqsubseteq> \<Sqinter>B"
  by (auto intro: Inf_greatest Inf_lower)

lemma Sup_subset_mono: "A \<subseteq> B \<Longrightarrow> \<Squnion>A \<sqsubseteq> \<Squnion>B"
  by (auto intro: Sup_least Sup_upper)

lemma Inf_mono:
  assumes "\<And>b. b \<in> B \<Longrightarrow> \<exists>a\<in>A. a \<sqsubseteq> b"
  shows "\<Sqinter>A \<sqsubseteq> \<Sqinter>B"
proof (rule Inf_greatest)
  fix b assume "b \<in> B"
  with assms obtain a where "a \<in> A" and "a \<sqsubseteq> b" by blast
  from `a \<in> A` have "\<Sqinter>A \<sqsubseteq> a" by (rule Inf_lower)
  with `a \<sqsubseteq> b` show "\<Sqinter>A \<sqsubseteq> b" by auto
qed

lemma INF_mono:
  "(\<And>m. m \<in> B \<Longrightarrow> \<exists>n\<in>A. f n \<sqsubseteq> g m) \<Longrightarrow> (\<Sqinter>n\<in>A. f n) \<sqsubseteq> (\<Sqinter>n\<in>B. g n)"
  using Inf_mono [of "g ` B" "f ` A"] by auto

lemma Sup_mono:
  assumes "\<And>a. a \<in> A \<Longrightarrow> \<exists>b\<in>B. a \<sqsubseteq> b"
  shows "\<Squnion>A \<sqsubseteq> \<Squnion>B"
proof (rule Sup_least)
  fix a assume "a \<in> A"
  with assms obtain b where "b \<in> B" and "a \<sqsubseteq> b" by blast
  from `b \<in> B` have "b \<sqsubseteq> \<Squnion>B" by (rule Sup_upper)
  with `a \<sqsubseteq> b` show "a \<sqsubseteq> \<Squnion>B" by auto
qed

lemma SUP_mono:
  "(\<And>n. n \<in> A \<Longrightarrow> \<exists>m\<in>B. f n \<sqsubseteq> g m) \<Longrightarrow> (\<Squnion>n\<in>A. f n) \<sqsubseteq> (\<Squnion>n\<in>B. g n)"
  using Sup_mono [of "f ` A" "g ` B"] by auto

lemma INF_superset_mono:
  "B \<subseteq> A \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> f x \<sqsubseteq> g x) \<Longrightarrow> (\<Sqinter>x\<in>A. f x) \<sqsubseteq> (\<Sqinter>x\<in>B. g x)"
  -- {* The last inclusion is POSITIVE! *}
  by (blast intro: INF_mono dest: subsetD)

lemma SUP_subset_mono:
  "A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<sqsubseteq> g x) \<Longrightarrow> (\<Squnion>x\<in>A. f x) \<sqsubseteq> (\<Squnion>x\<in>B. g x)"
  by (blast intro: SUP_mono dest: subsetD)

lemma Inf_less_eq:
  assumes "\<And>v. v \<in> A \<Longrightarrow> v \<sqsubseteq> u"
    and "A \<noteq> {}"
  shows "\<Sqinter>A \<sqsubseteq> u"
proof -
  from `A \<noteq> {}` obtain v where "v \<in> A" by blast
  moreover from `v \<in> A` assms(1) have "v \<sqsubseteq> u" by blast
  ultimately show ?thesis by (rule Inf_lower2)
qed

lemma less_eq_Sup:
  assumes "\<And>v. v \<in> A \<Longrightarrow> u \<sqsubseteq> v"
    and "A \<noteq> {}"
  shows "u \<sqsubseteq> \<Squnion>A"
proof -
  from `A \<noteq> {}` obtain v where "v \<in> A" by blast
  moreover from `v \<in> A` assms(1) have "u \<sqsubseteq> v" by blast
  ultimately show ?thesis by (rule Sup_upper2)
qed

lemma SUP_eq:
  assumes "\<And>i. i \<in> A \<Longrightarrow> \<exists>j\<in>B. f i \<le> g j"
  assumes "\<And>j. j \<in> B \<Longrightarrow> \<exists>i\<in>A. g j \<le> f i"
  shows "(\<Squnion>i\<in>A. f i) = (\<Squnion>j\<in>B. g j)"
  by (intro antisym SUP_least) (blast intro: SUP_upper2 dest: assms)+

lemma INF_eq:
  assumes "\<And>i. i \<in> A \<Longrightarrow> \<exists>j\<in>B. f i \<ge> g j"
  assumes "\<And>j. j \<in> B \<Longrightarrow> \<exists>i\<in>A. g j \<ge> f i"
  shows "(\<Sqinter>i\<in>A. f i) = (\<Sqinter>j\<in>B. g j)"
  by (intro antisym INF_greatest) (blast intro: INF_lower2 dest: assms)+

lemma less_eq_Inf_inter: "\<Sqinter>A \<squnion> \<Sqinter>B \<sqsubseteq> \<Sqinter>(A \<inter> B)"
  by (auto intro: Inf_greatest Inf_lower)

lemma Sup_inter_less_eq: "\<Squnion>(A \<inter> B) \<sqsubseteq> \<Squnion>A \<sqinter> \<Squnion>B "
  by (auto intro: Sup_least Sup_upper)

lemma Inf_union_distrib: "\<Sqinter>(A \<union> B) = \<Sqinter>A \<sqinter> \<Sqinter>B"
  by (rule antisym) (auto intro: Inf_greatest Inf_lower le_infI1 le_infI2)

lemma INF_union:
  "(\<Sqinter>i \<in> A \<union> B. M i) = (\<Sqinter>i \<in> A. M i) \<sqinter> (\<Sqinter>i\<in>B. M i)"
  by (auto intro!: antisym INF_mono intro: le_infI1 le_infI2 INF_greatest INF_lower)

lemma Sup_union_distrib: "\<Squnion>(A \<union> B) = \<Squnion>A \<squnion> \<Squnion>B"
  by (rule antisym) (auto intro: Sup_least Sup_upper le_supI1 le_supI2)

lemma SUP_union:
  "(\<Squnion>i \<in> A \<union> B. M i) = (\<Squnion>i \<in> A. M i) \<squnion> (\<Squnion>i\<in>B. M i)"
  by (auto intro!: antisym SUP_mono intro: le_supI1 le_supI2 SUP_least SUP_upper)

lemma INF_inf_distrib: "(\<Sqinter>a\<in>A. f a) \<sqinter> (\<Sqinter>a\<in>A. g a) = (\<Sqinter>a\<in>A. f a \<sqinter> g a)"
  by (rule antisym) (rule INF_greatest, auto intro: le_infI1 le_infI2 INF_lower INF_mono)

lemma SUP_sup_distrib: "(\<Squnion>a\<in>A. f a) \<squnion> (\<Squnion>a\<in>A. g a) = (\<Squnion>a\<in>A. f a \<squnion> g a)" (is "?L = ?R")
proof (rule antisym)
  show "?L \<le> ?R" by (auto intro: le_supI1 le_supI2 SUP_upper SUP_mono)
next
  show "?R \<le> ?L" by (rule SUP_least) (auto intro: le_supI1 le_supI2 SUP_upper)
qed

lemma Inf_top_conv [simp]:
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
      with `\<Sqinter>A = \<top>` `x \<noteq> \<top>` show False by simp
    qed
  qed
  then show "\<top> = \<Sqinter>A \<longleftrightarrow> (\<forall>x\<in>A. x = \<top>)" by auto
qed

lemma INF_top_conv [simp]:
  "(\<Sqinter>x\<in>A. B x) = \<top> \<longleftrightarrow> (\<forall>x\<in>A. B x = \<top>)"
  "\<top> = (\<Sqinter>x\<in>A. B x) \<longleftrightarrow> (\<forall>x\<in>A. B x = \<top>)"
  using Inf_top_conv [of "B ` A"] by simp_all

lemma Sup_bot_conv [simp]:
  "\<Squnion>A = \<bottom> \<longleftrightarrow> (\<forall>x\<in>A. x = \<bottom>)" (is ?P)
  "\<bottom> = \<Squnion>A \<longleftrightarrow> (\<forall>x\<in>A. x = \<bottom>)" (is ?Q)
  using dual_complete_lattice
  by (rule complete_lattice.Inf_top_conv)+

lemma SUP_bot_conv [simp]:
 "(\<Squnion>x\<in>A. B x) = \<bottom> \<longleftrightarrow> (\<forall>x\<in>A. B x = \<bottom>)"
 "\<bottom> = (\<Squnion>x\<in>A. B x) \<longleftrightarrow> (\<forall>x\<in>A. B x = \<bottom>)"
  using Sup_bot_conv [of "B ` A"] by simp_all

lemma INF_const [simp]: "A \<noteq> {} \<Longrightarrow> (\<Sqinter>i\<in>A. f) = f"
  by (auto intro: antisym INF_lower INF_greatest)

lemma SUP_const [simp]: "A \<noteq> {} \<Longrightarrow> (\<Squnion>i\<in>A. f) = f"
  by (auto intro: antisym SUP_upper SUP_least)

lemma INF_top [simp]: "(\<Sqinter>x\<in>A. \<top>) = \<top>"
  by (cases "A = {}") simp_all

lemma SUP_bot [simp]: "(\<Squnion>x\<in>A. \<bottom>) = \<bottom>"
  by (cases "A = {}") simp_all

lemma INF_commute: "(\<Sqinter>i\<in>A. \<Sqinter>j\<in>B. f i j) = (\<Sqinter>j\<in>B. \<Sqinter>i\<in>A. f i j)"
  by (iprover intro: INF_lower INF_greatest order_trans antisym)

lemma SUP_commute: "(\<Squnion>i\<in>A. \<Squnion>j\<in>B. f i j) = (\<Squnion>j\<in>B. \<Squnion>i\<in>A. f i j)"
  by (iprover intro: SUP_upper SUP_least order_trans antisym)

lemma INF_absorb:
  assumes "k \<in> I"
  shows "A k \<sqinter> (\<Sqinter>i\<in>I. A i) = (\<Sqinter>i\<in>I. A i)"
proof -
  from assms obtain J where "I = insert k J" by blast
  then show ?thesis by simp
qed

lemma SUP_absorb:
  assumes "k \<in> I"
  shows "A k \<squnion> (\<Squnion>i\<in>I. A i) = (\<Squnion>i\<in>I. A i)"
proof -
  from assms obtain J where "I = insert k J" by blast
  then show ?thesis by simp
qed

lemma INF_constant:
  "(\<Sqinter>y\<in>A. c) = (if A = {} then \<top> else c)"
  by simp

lemma SUP_constant:
  "(\<Squnion>y\<in>A. c) = (if A = {} then \<bottom> else c)"
  by simp

lemma less_INF_D:
  assumes "y < (\<Sqinter>i\<in>A. f i)" "i \<in> A" shows "y < f i"
proof -
  note `y < (\<Sqinter>i\<in>A. f i)`
  also have "(\<Sqinter>i\<in>A. f i) \<le> f i" using `i \<in> A`
    by (rule INF_lower)
  finally show "y < f i" .
qed

lemma SUP_lessD:
  assumes "(\<Squnion>i\<in>A. f i) < y" "i \<in> A" shows "f i < y"
proof -
  have "f i \<le> (\<Squnion>i\<in>A. f i)" using `i \<in> A`
    by (rule SUP_upper)
  also note `(\<Squnion>i\<in>A. f i) < y`
  finally show "f i < y" .
qed

lemma INF_UNIV_bool_expand:
  "(\<Sqinter>b. A b) = A True \<sqinter> A False"
  by (simp add: UNIV_bool inf_commute)

lemma SUP_UNIV_bool_expand:
  "(\<Squnion>b. A b) = A True \<squnion> A False"
  by (simp add: UNIV_bool sup_commute)

lemma Inf_le_Sup: "A \<noteq> {} \<Longrightarrow> Inf A \<le> Sup A"
  by (blast intro: Sup_upper2 Inf_lower ex_in_conv)

lemma INF_le_SUP: "A \<noteq> {} \<Longrightarrow> INFIMUM A f \<le> SUPREMUM A f"
  using Inf_le_Sup [of "f ` A"] by simp

lemma INF_eq_const:
  "I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> f i = x) \<Longrightarrow> INFIMUM I f = x"
  by (auto intro: INF_eqI)

lemma SUP_eq_const:
  "I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> f i = x) \<Longrightarrow> SUPREMUM I f = x"
  by (auto intro: SUP_eqI)

lemma INF_eq_iff:
  "I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> f i \<le> c) \<Longrightarrow> (INFIMUM I f = c) \<longleftrightarrow> (\<forall>i\<in>I. f i = c)"
  using INF_eq_const [of I f c] INF_lower [of _ I f]
  by (auto intro: antisym cong del: strong_INF_cong)

lemma SUP_eq_iff:
  "I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> c \<le> f i) \<Longrightarrow> (SUPREMUM I f = c) \<longleftrightarrow> (\<forall>i\<in>I. f i = c)"
  using SUP_eq_const [of I f c] SUP_upper [of _ I f]
  by (auto intro: antisym cong del: strong_SUP_cong)

end

class complete_distrib_lattice = complete_lattice +
  assumes sup_Inf: "a \<squnion> \<Sqinter>B = (\<Sqinter>b\<in>B. a \<squnion> b)"
  assumes inf_Sup: "a \<sqinter> \<Squnion>B = (\<Squnion>b\<in>B. a \<sqinter> b)"
begin

lemma sup_INF:
  "a \<squnion> (\<Sqinter>b\<in>B. f b) = (\<Sqinter>b\<in>B. a \<squnion> f b)"
  by (simp only: INF_def sup_Inf image_image)

lemma inf_SUP:
  "a \<sqinter> (\<Squnion>b\<in>B. f b) = (\<Squnion>b\<in>B. a \<sqinter> f b)"
  by (simp only: SUP_def inf_Sup image_image)

lemma dual_complete_distrib_lattice:
  "class.complete_distrib_lattice Sup Inf sup (op \<ge>) (op >) inf \<top> \<bottom>"
  apply (rule class.complete_distrib_lattice.intro)
  apply (fact dual_complete_lattice)
  apply (rule class.complete_distrib_lattice_axioms.intro)
  apply (simp_all only: INF_foundation_dual SUP_foundation_dual inf_Sup sup_Inf)
  done

subclass distrib_lattice proof
  fix a b c
  from sup_Inf have "a \<squnion> \<Sqinter>{b, c} = (\<Sqinter>d\<in>{b, c}. a \<squnion> d)" .
  then show "a \<squnion> b \<sqinter> c = (a \<squnion> b) \<sqinter> (a \<squnion> c)" by (simp add: INF_def)
qed

lemma Inf_sup:
  "\<Sqinter>B \<squnion> a = (\<Sqinter>b\<in>B. b \<squnion> a)"
  by (simp add: sup_Inf sup_commute)

lemma Sup_inf:
  "\<Squnion>B \<sqinter> a = (\<Squnion>b\<in>B. b \<sqinter> a)"
  by (simp add: inf_Sup inf_commute)

lemma INF_sup: 
  "(\<Sqinter>b\<in>B. f b) \<squnion> a = (\<Sqinter>b\<in>B. f b \<squnion> a)"
  by (simp add: sup_INF sup_commute)

lemma SUP_inf:
  "(\<Squnion>b\<in>B. f b) \<sqinter> a = (\<Squnion>b\<in>B. f b \<sqinter> a)"
  by (simp add: inf_SUP inf_commute)

lemma Inf_sup_eq_top_iff:
  "(\<Sqinter>B \<squnion> a = \<top>) \<longleftrightarrow> (\<forall>b\<in>B. b \<squnion> a = \<top>)"
  by (simp only: Inf_sup INF_top_conv)

lemma Sup_inf_eq_bot_iff:
  "(\<Squnion>B \<sqinter> a = \<bottom>) \<longleftrightarrow> (\<forall>b\<in>B. b \<sqinter> a = \<bottom>)"
  by (simp only: Sup_inf SUP_bot_conv)

lemma INF_sup_distrib2:
  "(\<Sqinter>a\<in>A. f a) \<squnion> (\<Sqinter>b\<in>B. g b) = (\<Sqinter>a\<in>A. \<Sqinter>b\<in>B. f a \<squnion> g b)"
  by (subst INF_commute) (simp add: sup_INF INF_sup)

lemma SUP_inf_distrib2:
  "(\<Squnion>a\<in>A. f a) \<sqinter> (\<Squnion>b\<in>B. g b) = (\<Squnion>a\<in>A. \<Squnion>b\<in>B. f a \<sqinter> g b)"
  by (subst SUP_commute) (simp add: inf_SUP SUP_inf)

context
  fixes f :: "'a \<Rightarrow> 'b::complete_lattice"
  assumes "mono f"
begin

lemma mono_Inf:
  shows "f (\<Sqinter>A) \<le> (\<Sqinter>x\<in>A. f x)"
  using `mono f` by (auto intro: complete_lattice_class.INF_greatest Inf_lower dest: monoD)

lemma mono_Sup:
  shows "(\<Squnion>x\<in>A. f x) \<le> f (\<Squnion>A)"
  using `mono f` by (auto intro: complete_lattice_class.SUP_least Sup_upper dest: monoD)

end

end

class complete_boolean_algebra = boolean_algebra + complete_distrib_lattice
begin

lemma dual_complete_boolean_algebra:
  "class.complete_boolean_algebra Sup Inf sup (op \<ge>) (op >) inf \<top> \<bottom> (\<lambda>x y. x \<squnion> - y) uminus"
  by (rule class.complete_boolean_algebra.intro, rule dual_complete_distrib_lattice, rule dual_boolean_algebra)

lemma uminus_Inf:
  "- (\<Sqinter>A) = \<Squnion>(uminus ` A)"
proof (rule antisym)
  show "- \<Sqinter>A \<le> \<Squnion>(uminus ` A)"
    by (rule compl_le_swap2, rule Inf_greatest, rule compl_le_swap2, rule Sup_upper) simp
  show "\<Squnion>(uminus ` A) \<le> - \<Sqinter>A"
    by (rule Sup_least, rule compl_le_swap1, rule Inf_lower) auto
qed

lemma uminus_INF: "- (\<Sqinter>x\<in>A. B x) = (\<Squnion>x\<in>A. - B x)"
  by (simp only: INF_def SUP_def uminus_Inf image_image)

lemma uminus_Sup:
  "- (\<Squnion>A) = \<Sqinter>(uminus ` A)"
proof -
  have "\<Squnion>A = - \<Sqinter>(uminus ` A)" by (simp add: image_image uminus_INF)
  then show ?thesis by simp
qed
  
lemma uminus_SUP: "- (\<Squnion>x\<in>A. B x) = (\<Sqinter>x\<in>A. - B x)"
  by (simp only: INF_def SUP_def uminus_Sup image_image)

end

class complete_linorder = linorder + complete_lattice
begin

lemma dual_complete_linorder:
  "class.complete_linorder Sup Inf sup (op \<ge>) (op >) inf \<top> \<bottom>"
  by (rule class.complete_linorder.intro, rule dual_complete_lattice, rule dual_linorder)

lemma complete_linorder_inf_min: "inf = min"
  by (auto intro: antisym simp add: min_def fun_eq_iff)

lemma complete_linorder_sup_max: "sup = max"
  by (auto intro: antisym simp add: max_def fun_eq_iff)

lemma Inf_less_iff:
  "\<Sqinter>S \<sqsubset> a \<longleftrightarrow> (\<exists>x\<in>S. x \<sqsubset> a)"
  unfolding not_le [symmetric] le_Inf_iff by auto

lemma INF_less_iff:
  "(\<Sqinter>i\<in>A. f i) \<sqsubset> a \<longleftrightarrow> (\<exists>x\<in>A. f x \<sqsubset> a)"
  using Inf_less_iff [of "f ` A"] by simp

lemma less_Sup_iff:
  "a \<sqsubset> \<Squnion>S \<longleftrightarrow> (\<exists>x\<in>S. a \<sqsubset> x)"
  unfolding not_le [symmetric] Sup_le_iff by auto

lemma less_SUP_iff:
  "a \<sqsubset> (\<Squnion>i\<in>A. f i) \<longleftrightarrow> (\<exists>x\<in>A. a \<sqsubset> f x)"
  using less_Sup_iff [of _ "f ` A"] by simp

lemma Sup_eq_top_iff [simp]:
  "\<Squnion>A = \<top> \<longleftrightarrow> (\<forall>x<\<top>. \<exists>i\<in>A. x < i)"
proof
  assume *: "\<Squnion>A = \<top>"
  show "(\<forall>x<\<top>. \<exists>i\<in>A. x < i)" unfolding * [symmetric]
  proof (intro allI impI)
    fix x assume "x < \<Squnion>A" then show "\<exists>i\<in>A. x < i"
      unfolding less_Sup_iff by auto
  qed
next
  assume *: "\<forall>x<\<top>. \<exists>i\<in>A. x < i"
  show "\<Squnion>A = \<top>"
  proof (rule ccontr)
    assume "\<Squnion>A \<noteq> \<top>"
    with top_greatest [of "\<Squnion>A"]
    have "\<Squnion>A < \<top>" unfolding le_less by auto
    then have "\<Squnion>A < \<Squnion>A"
      using * unfolding less_Sup_iff by auto
    then show False by auto
  qed
qed

lemma SUP_eq_top_iff [simp]:
  "(\<Squnion>i\<in>A. f i) = \<top> \<longleftrightarrow> (\<forall>x<\<top>. \<exists>i\<in>A. x < f i)"
  using Sup_eq_top_iff [of "f ` A"] by simp

lemma Inf_eq_bot_iff [simp]:
  "\<Sqinter>A = \<bottom> \<longleftrightarrow> (\<forall>x>\<bottom>. \<exists>i\<in>A. i < x)"
  using dual_complete_linorder
  by (rule complete_linorder.Sup_eq_top_iff)

lemma INF_eq_bot_iff [simp]:
  "(\<Sqinter>i\<in>A. f i) = \<bottom> \<longleftrightarrow> (\<forall>x>\<bottom>. \<exists>i\<in>A. f i < x)"
  using Inf_eq_bot_iff [of "f ` A"] by simp

lemma Inf_le_iff: "\<Sqinter>A \<le> x \<longleftrightarrow> (\<forall>y>x. \<exists>a\<in>A. y > a)"
proof safe
  fix y assume "x \<ge> \<Sqinter>A" "y > x"
  then have "y > \<Sqinter>A" by auto
  then show "\<exists>a\<in>A. y > a"
    unfolding Inf_less_iff .
qed (auto elim!: allE[of _ "\<Sqinter>A"] simp add: not_le[symmetric] Inf_lower)

lemma INF_le_iff:
  "INFIMUM A f \<le> x \<longleftrightarrow> (\<forall>y>x. \<exists>i\<in>A. y > f i)"
  using Inf_le_iff [of "f ` A"] by simp

lemma le_Sup_iff: "x \<le> \<Squnion>A \<longleftrightarrow> (\<forall>y<x. \<exists>a\<in>A. y < a)"
proof safe
  fix y assume "x \<le> \<Squnion>A" "y < x"
  then have "y < \<Squnion>A" by auto
  then show "\<exists>a\<in>A. y < a"
    unfolding less_Sup_iff .
qed (auto elim!: allE[of _ "\<Squnion>A"] simp add: not_le[symmetric] Sup_upper)

lemma le_SUP_iff: "x \<le> SUPREMUM A f \<longleftrightarrow> (\<forall>y<x. \<exists>i\<in>A. y < f i)"
  using le_Sup_iff [of _ "f ` A"] by simp

subclass complete_distrib_lattice
proof
  fix a and B
  show "a \<squnion> \<Sqinter>B = (\<Sqinter>b\<in>B. a \<squnion> b)" and "a \<sqinter> \<Squnion>B = (\<Squnion>b\<in>B. a \<sqinter> b)"
    by (safe intro!: INF_eqI [symmetric] sup_mono Inf_lower SUP_eqI [symmetric] inf_mono Sup_upper)
      (auto simp: not_less [symmetric] Inf_less_iff less_Sup_iff
        le_max_iff_disj complete_linorder_sup_max min_le_iff_disj complete_linorder_inf_min)
qed

end


subsection {* Complete lattice on @{typ bool} *}

instantiation bool :: complete_lattice
begin

definition
  [simp, code]: "\<Sqinter>A \<longleftrightarrow> False \<notin> A"

definition
  [simp, code]: "\<Squnion>A \<longleftrightarrow> True \<in> A"

instance proof
qed (auto intro: bool_induct)

end

lemma not_False_in_image_Ball [simp]:
  "False \<notin> P ` A \<longleftrightarrow> Ball A P"
  by auto

lemma True_in_image_Bex [simp]:
  "True \<in> P ` A \<longleftrightarrow> Bex A P"
  by auto

lemma INF_bool_eq [simp]:
  "INFIMUM = Ball"
  by (simp add: fun_eq_iff INF_def)

lemma SUP_bool_eq [simp]:
  "SUPREMUM = Bex"
  by (simp add: fun_eq_iff SUP_def)

instance bool :: complete_boolean_algebra proof
qed (auto intro: bool_induct)


subsection {* Complete lattice on @{typ "_ \<Rightarrow> _"} *}

instantiation "fun" :: (type, complete_lattice) complete_lattice
begin

definition
  "\<Sqinter>A = (\<lambda>x. \<Sqinter>f\<in>A. f x)"

lemma Inf_apply [simp, code]:
  "(\<Sqinter>A) x = (\<Sqinter>f\<in>A. f x)"
  by (simp add: Inf_fun_def)

definition
  "\<Squnion>A = (\<lambda>x. \<Squnion>f\<in>A. f x)"

lemma Sup_apply [simp, code]:
  "(\<Squnion>A) x = (\<Squnion>f\<in>A. f x)"
  by (simp add: Sup_fun_def)

instance proof
qed (auto simp add: le_fun_def intro: INF_lower INF_greatest SUP_upper SUP_least)

end

lemma INF_apply [simp]:
  "(\<Sqinter>y\<in>A. f y) x = (\<Sqinter>y\<in>A. f y x)"
  using Inf_apply [of "f ` A"] by (simp add: comp_def)

lemma SUP_apply [simp]:
  "(\<Squnion>y\<in>A. f y) x = (\<Squnion>y\<in>A. f y x)"
  using Sup_apply [of "f ` A"] by (simp add: comp_def)

instance "fun" :: (type, complete_distrib_lattice) complete_distrib_lattice proof
qed (auto simp add: INF_def SUP_def inf_Sup sup_Inf fun_eq_iff image_image
  simp del: Inf_image_eq Sup_image_eq)

instance "fun" :: (type, complete_boolean_algebra) complete_boolean_algebra ..


subsection {* Complete lattice on unary and binary predicates *}

lemma INF1_I: "(\<And>x. x \<in> A \<Longrightarrow> B x b) \<Longrightarrow> (\<Sqinter>x\<in>A. B x) b"
  by auto

lemma INF2_I: "(\<And>x. x \<in> A \<Longrightarrow> B x b c) \<Longrightarrow> (\<Sqinter>x\<in>A. B x) b c"
  by auto

lemma INF1_D: "(\<Sqinter>x\<in>A. B x) b \<Longrightarrow> a \<in> A \<Longrightarrow> B a b"
  by auto

lemma INF2_D: "(\<Sqinter>x\<in>A. B x) b c \<Longrightarrow> a \<in> A \<Longrightarrow> B a b c"
  by auto

lemma INF1_E: "(\<Sqinter>x\<in>A. B x) b \<Longrightarrow> (B a b \<Longrightarrow> R) \<Longrightarrow> (a \<notin> A \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

lemma INF2_E: "(\<Sqinter>x\<in>A. B x) b c \<Longrightarrow> (B a b c \<Longrightarrow> R) \<Longrightarrow> (a \<notin> A \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

lemma SUP1_I: "a \<in> A \<Longrightarrow> B a b \<Longrightarrow> (\<Squnion>x\<in>A. B x) b"
  by auto

lemma SUP2_I: "a \<in> A \<Longrightarrow> B a b c \<Longrightarrow> (\<Squnion>x\<in>A. B x) b c"
  by auto

lemma SUP1_E: "(\<Squnion>x\<in>A. B x) b \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> B x b \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

lemma SUP2_E: "(\<Squnion>x\<in>A. B x) b c \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> B x b c \<Longrightarrow> R) \<Longrightarrow> R"
  by auto


subsection {* Complete lattice on @{typ "_ set"} *}

instantiation "set" :: (type) complete_lattice
begin

definition
  "\<Sqinter>A = {x. \<Sqinter>((\<lambda>B. x \<in> B) ` A)}"

definition
  "\<Squnion>A = {x. \<Squnion>((\<lambda>B. x \<in> B) ` A)}"

instance proof
qed (auto simp add: less_eq_set_def Inf_set_def Sup_set_def le_fun_def)

end

instance "set" :: (type) complete_boolean_algebra
proof
qed (auto simp add: INF_def SUP_def Inf_set_def Sup_set_def image_def)
  

subsubsection {* Inter *}

abbreviation Inter :: "'a set set \<Rightarrow> 'a set" where
  "Inter S \<equiv> \<Sqinter>S"
  
notation (xsymbols)
  Inter  ("\<Inter>_" [900] 900)

lemma Inter_eq:
  "\<Inter>A = {x. \<forall>B \<in> A. x \<in> B}"
proof (rule set_eqI)
  fix x
  have "(\<forall>Q\<in>{P. \<exists>B\<in>A. P \<longleftrightarrow> x \<in> B}. Q) \<longleftrightarrow> (\<forall>B\<in>A. x \<in> B)"
    by auto
  then show "x \<in> \<Inter>A \<longleftrightarrow> x \<in> {x. \<forall>B \<in> A. x \<in> B}"
    by (simp add: Inf_set_def image_def)
qed

lemma Inter_iff [simp]: "A \<in> \<Inter>C \<longleftrightarrow> (\<forall>X\<in>C. A \<in> X)"
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

lemma Inter_subset:
  "(\<And>X. X \<in> A \<Longrightarrow> X \<subseteq> B) \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<Inter>A \<subseteq> B"
  by (fact Inf_less_eq)

lemma Inter_greatest: "(\<And>X. X \<in> A \<Longrightarrow> C \<subseteq> X) \<Longrightarrow> C \<subseteq> Inter A"
  by (fact Inf_greatest)

lemma Inter_empty: "\<Inter>{} = UNIV"
  by (fact Inf_empty) (* already simp *)

lemma Inter_UNIV: "\<Inter>UNIV = {}"
  by (fact Inf_UNIV) (* already simp *)

lemma Inter_insert: "\<Inter>(insert a B) = a \<inter> \<Inter>B"
  by (fact Inf_insert) (* already simp *)

lemma Inter_Un_subset: "\<Inter>A \<union> \<Inter>B \<subseteq> \<Inter>(A \<inter> B)"
  by (fact less_eq_Inf_inter)

lemma Inter_Un_distrib: "\<Inter>(A \<union> B) = \<Inter>A \<inter> \<Inter>B"
  by (fact Inf_union_distrib)

lemma Inter_UNIV_conv [simp]:
  "\<Inter>A = UNIV \<longleftrightarrow> (\<forall>x\<in>A. x = UNIV)"
  "UNIV = \<Inter>A \<longleftrightarrow> (\<forall>x\<in>A. x = UNIV)"
  by (fact Inf_top_conv)+

lemma Inter_anti_mono: "B \<subseteq> A \<Longrightarrow> \<Inter>A \<subseteq> \<Inter>B"
  by (fact Inf_superset_mono)


subsubsection {* Intersections of families *}

abbreviation INTER :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" where
  "INTER \<equiv> INFIMUM"

text {*
  Note: must use name @{const INTER} here instead of @{text INT}
  to allow the following syntax coexist with the plain constant name.
*}

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

lemma INTER_eq:
  "(\<Inter>x\<in>A. B x) = {y. \<forall>x\<in>A. y \<in> B x}"
  by (auto intro!: INF_eqI)

lemma Inter_image_eq:
  "\<Inter>(B ` A) = (\<Inter>x\<in>A. B x)"
  by (fact Inf_image_eq)

lemma INT_iff [simp]: "b \<in> (\<Inter>x\<in>A. B x) \<longleftrightarrow> (\<forall>x\<in>A. b \<in> B x)"
  using Inter_iff [of _ "B ` A"] by simp

lemma INT_I [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> b \<in> B x) \<Longrightarrow> b \<in> (\<Inter>x\<in>A. B x)"
  by (auto simp add: INF_def image_def)

lemma INT_D [elim, Pure.elim]: "b \<in> (\<Inter>x\<in>A. B x) \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> B a"
  by auto

lemma INT_E [elim]: "b \<in> (\<Inter>x\<in>A. B x) \<Longrightarrow> (b \<in> B a \<Longrightarrow> R) \<Longrightarrow> (a \<notin> A \<Longrightarrow> R) \<Longrightarrow> R"
  -- {* "Classical" elimination -- by the Excluded Middle on @{prop "a\<in>A"}. *}
  by (auto simp add: INF_def image_def)

lemma Collect_ball_eq: "{x. \<forall>y\<in>A. P x y} = (\<Inter>y\<in>A. {x. P x y})"
  by blast

lemma Collect_all_eq: "{x. \<forall>y. P x y} = (\<Inter>y. {x. P x y})"
  by blast

lemma INT_lower: "a \<in> A \<Longrightarrow> (\<Inter>x\<in>A. B x) \<subseteq> B a"
  by (fact INF_lower)

lemma INT_greatest: "(\<And>x. x \<in> A \<Longrightarrow> C \<subseteq> B x) \<Longrightarrow> C \<subseteq> (\<Inter>x\<in>A. B x)"
  by (fact INF_greatest)

lemma INT_empty: "(\<Inter>x\<in>{}. B x) = UNIV"
  by (fact INF_empty)

lemma INT_absorb: "k \<in> I \<Longrightarrow> A k \<inter> (\<Inter>i\<in>I. A i) = (\<Inter>i\<in>I. A i)"
  by (fact INF_absorb)

lemma INT_subset_iff: "B \<subseteq> (\<Inter>i\<in>I. A i) \<longleftrightarrow> (\<forall>i\<in>I. B \<subseteq> A i)"
  by (fact le_INF_iff)

lemma INT_insert [simp]: "(\<Inter>x \<in> insert a A. B x) = B a \<inter> INTER A B"
  by (fact INF_insert)

lemma INT_Un: "(\<Inter>i \<in> A \<union> B. M i) = (\<Inter>i \<in> A. M i) \<inter> (\<Inter>i\<in>B. M i)"
  by (fact INF_union)

lemma INT_insert_distrib:
  "u \<in> A \<Longrightarrow> (\<Inter>x\<in>A. insert a (B x)) = insert a (\<Inter>x\<in>A. B x)"
  by blast

lemma INT_constant [simp]: "(\<Inter>y\<in>A. c) = (if A = {} then UNIV else c)"
  by (fact INF_constant)

lemma INTER_UNIV_conv:
 "(UNIV = (\<Inter>x\<in>A. B x)) = (\<forall>x\<in>A. B x = UNIV)"
 "((\<Inter>x\<in>A. B x) = UNIV) = (\<forall>x\<in>A. B x = UNIV)"
  by (fact INF_top_conv)+ (* already simp *)

lemma INT_bool_eq: "(\<Inter>b. A b) = A True \<inter> A False"
  by (fact INF_UNIV_bool_expand)

lemma INT_anti_mono:
  "A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<subseteq> g x) \<Longrightarrow> (\<Inter>x\<in>B. f x) \<subseteq> (\<Inter>x\<in>A. g x)"
  -- {* The last inclusion is POSITIVE! *}
  by (fact INF_superset_mono)

lemma Pow_INT_eq: "Pow (\<Inter>x\<in>A. B x) = (\<Inter>x\<in>A. Pow (B x))"
  by blast

lemma vimage_INT: "f -` (\<Inter>x\<in>A. B x) = (\<Inter>x\<in>A. f -` B x)"
  by blast


subsubsection {* Union *}

abbreviation Union :: "'a set set \<Rightarrow> 'a set" where
  "Union S \<equiv> \<Squnion>S"

notation (xsymbols)
  Union  ("\<Union>_" [900] 900)

lemma Union_eq:
  "\<Union>A = {x. \<exists>B \<in> A. x \<in> B}"
proof (rule set_eqI)
  fix x
  have "(\<exists>Q\<in>{P. \<exists>B\<in>A. P \<longleftrightarrow> x \<in> B}. Q) \<longleftrightarrow> (\<exists>B\<in>A. x \<in> B)"
    by auto
  then show "x \<in> \<Union>A \<longleftrightarrow> x \<in> {x. \<exists>B\<in>A. x \<in> B}"
    by (simp add: Sup_set_def image_def)
qed

lemma Union_iff [simp]:
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
  by (fact Sup_upper)

lemma Union_least: "(\<And>X. X \<in> A \<Longrightarrow> X \<subseteq> C) \<Longrightarrow> \<Union>A \<subseteq> C"
  by (fact Sup_least)

lemma Union_empty: "\<Union>{} = {}"
  by (fact Sup_empty) (* already simp *)

lemma Union_UNIV: "\<Union>UNIV = UNIV"
  by (fact Sup_UNIV) (* already simp *)

lemma Union_insert: "\<Union>insert a B = a \<union> \<Union>B"
  by (fact Sup_insert) (* already simp *)

lemma Union_Un_distrib [simp]: "\<Union>(A \<union> B) = \<Union>A \<union> \<Union>B"
  by (fact Sup_union_distrib)

lemma Union_Int_subset: "\<Union>(A \<inter> B) \<subseteq> \<Union>A \<inter> \<Union>B"
  by (fact Sup_inter_less_eq)

lemma Union_empty_conv: "(\<Union>A = {}) \<longleftrightarrow> (\<forall>x\<in>A. x = {})"
  by (fact Sup_bot_conv) (* already simp *)

lemma empty_Union_conv: "({} = \<Union>A) \<longleftrightarrow> (\<forall>x\<in>A. x = {})"
  by (fact Sup_bot_conv) (* already simp *)

lemma subset_Pow_Union: "A \<subseteq> Pow (\<Union>A)"
  by blast

lemma Union_Pow_eq [simp]: "\<Union>(Pow A) = A"
  by blast

lemma Union_mono: "A \<subseteq> B \<Longrightarrow> \<Union>A \<subseteq> \<Union>B"
  by (fact Sup_subset_mono)


subsubsection {* Unions of families *}

abbreviation UNION :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" where
  "UNION \<equiv> SUPREMUM"

text {*
  Note: must use name @{const UNION} here instead of @{text UN}
  to allow the following syntax coexist with the plain constant name.
*}

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
  unions and intersections (e.g.\ @{text"\<Union>a\<^sub>1\<in>A\<^sub>1. B"})
  and their \LaTeX\ rendition: @{term"\<Union>a\<^sub>1\<in>A\<^sub>1. B"}. The
  former does not make the index expression a subscript of the
  union/intersection symbol because this leads to problems with nested
  subscripts in Proof General.
*}

print_translation {*
  [Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax UNION} @{syntax_const "_UNION"}]
*} -- {* to avoid eta-contraction of body *}

lemma UNION_eq:
  "(\<Union>x\<in>A. B x) = {y. \<exists>x\<in>A. y \<in> B x}"
  by (auto intro!: SUP_eqI)

lemma bind_UNION [code]:
  "Set.bind A f = UNION A f"
  by (simp add: bind_def UNION_eq)

lemma member_bind [simp]:
  "x \<in> Set.bind P f \<longleftrightarrow> x \<in> UNION P f "
  by (simp add: bind_UNION)

lemma Union_image_eq:
  "\<Union>(B ` A) = (\<Union>x\<in>A. B x)"
  by (fact Sup_image_eq)

lemma UN_iff [simp]: "b \<in> (\<Union>x\<in>A. B x) \<longleftrightarrow> (\<exists>x\<in>A. b \<in> B x)"
  using Union_iff [of _ "B ` A"] by simp

lemma UN_I [intro]: "a \<in> A \<Longrightarrow> b \<in> B a \<Longrightarrow> b \<in> (\<Union>x\<in>A. B x)"
  -- {* The order of the premises presupposes that @{term A} is rigid;
    @{term b} may be flexible. *}
  by auto

lemma UN_E [elim!]: "b \<in> (\<Union>x\<in>A. B x) \<Longrightarrow> (\<And>x. x\<in>A \<Longrightarrow> b \<in> B x \<Longrightarrow> R) \<Longrightarrow> R"
  by (auto simp add: SUP_def image_def)

lemma image_eq_UN: "f ` A = (\<Union>x\<in>A. {f x})"
  by blast

lemma UN_upper: "a \<in> A \<Longrightarrow> B a \<subseteq> (\<Union>x\<in>A. B x)"
  by (fact SUP_upper)

lemma UN_least: "(\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C) \<Longrightarrow> (\<Union>x\<in>A. B x) \<subseteq> C"
  by (fact SUP_least)

lemma Collect_bex_eq: "{x. \<exists>y\<in>A. P x y} = (\<Union>y\<in>A. {x. P x y})"
  by blast

lemma UN_insert_distrib: "u \<in> A \<Longrightarrow> (\<Union>x\<in>A. insert a (B x)) = insert a (\<Union>x\<in>A. B x)"
  by blast

lemma UN_empty: "(\<Union>x\<in>{}. B x) = {}"
  by (fact SUP_empty)

lemma UN_empty2: "(\<Union>x\<in>A. {}) = {}"
  by (fact SUP_bot) (* already simp *)

lemma UN_absorb: "k \<in> I \<Longrightarrow> A k \<union> (\<Union>i\<in>I. A i) = (\<Union>i\<in>I. A i)"
  by (fact SUP_absorb)

lemma UN_insert [simp]: "(\<Union>x\<in>insert a A. B x) = B a \<union> UNION A B"
  by (fact SUP_insert)

lemma UN_Un [simp]: "(\<Union>i \<in> A \<union> B. M i) = (\<Union>i\<in>A. M i) \<union> (\<Union>i\<in>B. M i)"
  by (fact SUP_union)

lemma UN_UN_flatten: "(\<Union>x \<in> (\<Union>y\<in>A. B y). C x) = (\<Union>y\<in>A. \<Union>x\<in>B y. C x)"
  by blast

lemma UN_subset_iff: "((\<Union>i\<in>I. A i) \<subseteq> B) = (\<forall>i\<in>I. A i \<subseteq> B)"
  by (fact SUP_le_iff)

lemma UN_constant [simp]: "(\<Union>y\<in>A. c) = (if A = {} then {} else c)"
  by (fact SUP_constant)

lemma image_Union: "f ` \<Union>S = (\<Union>x\<in>S. f ` x)"
  by blast

lemma UNION_empty_conv:
  "{} = (\<Union>x\<in>A. B x) \<longleftrightarrow> (\<forall>x\<in>A. B x = {})"
  "(\<Union>x\<in>A. B x) = {} \<longleftrightarrow> (\<forall>x\<in>A. B x = {})"
  by (fact SUP_bot_conv)+ (* already simp *)

lemma Collect_ex_eq: "{x. \<exists>y. P x y} = (\<Union>y. {x. P x y})"
  by blast

lemma ball_UN: "(\<forall>z \<in> UNION A B. P z) \<longleftrightarrow> (\<forall>x\<in>A. \<forall>z \<in> B x. P z)"
  by blast

lemma bex_UN: "(\<exists>z \<in> UNION A B. P z) \<longleftrightarrow> (\<exists>x\<in>A. \<exists>z\<in>B x. P z)"
  by blast

lemma Un_eq_UN: "A \<union> B = (\<Union>b. if b then A else B)"
  by (auto simp add: split_if_mem2)

lemma UN_bool_eq: "(\<Union>b. A b) = (A True \<union> A False)"
  by (fact SUP_UNIV_bool_expand)

lemma UN_Pow_subset: "(\<Union>x\<in>A. Pow (B x)) \<subseteq> Pow (\<Union>x\<in>A. B x)"
  by blast

lemma UN_mono:
  "A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<subseteq> g x) \<Longrightarrow>
    (\<Union>x\<in>A. f x) \<subseteq> (\<Union>x\<in>B. g x)"
  by (fact SUP_subset_mono)

lemma vimage_Union: "f -` (\<Union>A) = (\<Union>X\<in>A. f -` X)"
  by blast

lemma vimage_UN: "f -` (\<Union>x\<in>A. B x) = (\<Union>x\<in>A. f -` B x)"
  by blast

lemma vimage_eq_UN: "f -` B = (\<Union>y\<in>B. f -` {y})"
  -- {* NOT suitable for rewriting *}
  by blast

lemma image_UN: "f ` UNION A B = (\<Union>x\<in>A. f ` B x)"
  by blast

lemma UN_singleton [simp]: "(\<Union>x\<in>A. {x}) = A"
  by blast


subsubsection {* Distributive laws *}

lemma Int_Union: "A \<inter> \<Union>B = (\<Union>C\<in>B. A \<inter> C)"
  by (fact inf_Sup)

lemma Un_Inter: "A \<union> \<Inter>B = (\<Inter>C\<in>B. A \<union> C)"
  by (fact sup_Inf)

lemma Int_Union2: "\<Union>B \<inter> A = (\<Union>C\<in>B. C \<inter> A)"
  by (fact Sup_inf)

lemma INT_Int_distrib: "(\<Inter>i\<in>I. A i \<inter> B i) = (\<Inter>i\<in>I. A i) \<inter> (\<Inter>i\<in>I. B i)"
  by (rule sym) (rule INF_inf_distrib)

lemma UN_Un_distrib: "(\<Union>i\<in>I. A i \<union> B i) = (\<Union>i\<in>I. A i) \<union> (\<Union>i\<in>I. B i)"
  by (rule sym) (rule SUP_sup_distrib)

lemma Int_Inter_image: "(\<Inter>x\<in>C. A x \<inter> B x) = \<Inter>(A ` C) \<inter> \<Inter>(B ` C)" -- {* FIXME drop *}
  by (simp add: INT_Int_distrib)

lemma Un_Union_image: "(\<Union>x\<in>C. A x \<union> B x) = \<Union>(A ` C) \<union> \<Union>(B ` C)" -- {* FIXME drop *}
  -- {* Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5: *}
  -- {* Union of a family of unions *}
  by (simp add: UN_Un_distrib)

lemma Un_INT_distrib: "B \<union> (\<Inter>i\<in>I. A i) = (\<Inter>i\<in>I. B \<union> A i)"
  by (fact sup_INF)

lemma Int_UN_distrib: "B \<inter> (\<Union>i\<in>I. A i) = (\<Union>i\<in>I. B \<inter> A i)"
  -- {* Halmos, Naive Set Theory, page 35. *}
  by (fact inf_SUP)

lemma Int_UN_distrib2: "(\<Union>i\<in>I. A i) \<inter> (\<Union>j\<in>J. B j) = (\<Union>i\<in>I. \<Union>j\<in>J. A i \<inter> B j)"
  by (fact SUP_inf_distrib2)

lemma Un_INT_distrib2: "(\<Inter>i\<in>I. A i) \<union> (\<Inter>j\<in>J. B j) = (\<Inter>i\<in>I. \<Inter>j\<in>J. A i \<union> B j)"
  by (fact INF_sup_distrib2)

lemma Union_disjoint: "(\<Union>C \<inter> A = {}) \<longleftrightarrow> (\<forall>B\<in>C. B \<inter> A = {})"
  by (fact Sup_inf_eq_bot_iff)


subsection {* Injections and bijections *}

lemma inj_on_Inter:
  "S \<noteq> {} \<Longrightarrow> (\<And>A. A \<in> S \<Longrightarrow> inj_on f A) \<Longrightarrow> inj_on f (\<Inter>S)"
  unfolding inj_on_def by blast

lemma inj_on_INTER:
  "I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> inj_on f (A i)) \<Longrightarrow> inj_on f (\<Inter>i \<in> I. A i)"
  unfolding inj_on_def by blast

lemma inj_on_UNION_chain:
  assumes CH: "\<And> i j. \<lbrakk>i \<in> I; j \<in> I\<rbrakk> \<Longrightarrow> A i \<le> A j \<or> A j \<le> A i" and
         INJ: "\<And> i. i \<in> I \<Longrightarrow> inj_on f (A i)"
  shows "inj_on f (\<Union> i \<in> I. A i)"
proof -
  {
    fix i j x y
    assume *: "i \<in> I" "j \<in> I" and **: "x \<in> A i" "y \<in> A j"
      and ***: "f x = f y"
    have "x = y"
    proof -
      {
        assume "A i \<le> A j"
        with ** have "x \<in> A j" by auto
        with INJ * ** *** have ?thesis
        by(auto simp add: inj_on_def)
      }
      moreover
      {
        assume "A j \<le> A i"
        with ** have "y \<in> A i" by auto
        with INJ * ** *** have ?thesis
        by(auto simp add: inj_on_def)
      }
      ultimately show ?thesis using CH * by blast
    qed
  }
  then show ?thesis by (unfold inj_on_def UNION_eq) auto
qed

lemma bij_betw_UNION_chain:
  assumes CH: "\<And> i j. \<lbrakk>i \<in> I; j \<in> I\<rbrakk> \<Longrightarrow> A i \<le> A j \<or> A j \<le> A i" and
         BIJ: "\<And> i. i \<in> I \<Longrightarrow> bij_betw f (A i) (A' i)"
  shows "bij_betw f (\<Union> i \<in> I. A i) (\<Union> i \<in> I. A' i)"
proof (unfold bij_betw_def, auto)
  have "\<And> i. i \<in> I \<Longrightarrow> inj_on f (A i)"
  using BIJ bij_betw_def[of f] by auto
  thus "inj_on f (\<Union> i \<in> I. A i)"
  using CH inj_on_UNION_chain[of I A f] by auto
next
  fix i x
  assume *: "i \<in> I" "x \<in> A i"
  hence "f x \<in> A' i" using BIJ bij_betw_def[of f] by auto
  thus "\<exists>j \<in> I. f x \<in> A' j" using * by blast
next
  fix i x'
  assume *: "i \<in> I" "x' \<in> A' i"
  hence "\<exists>x \<in> A i. x' = f x" using BIJ bij_betw_def[of f] by blast
  then have "\<exists>j \<in> I. \<exists>x \<in> A j. x' = f x"
    using * by blast
  then show "x' \<in> f ` (\<Union>x\<in>I. A x)" by blast
qed

(*injectivity's required.  Left-to-right inclusion holds even if A is empty*)
lemma image_INT:
   "[| inj_on f C;  ALL x:A. B x <= C;  j:A |]
    ==> f ` (INTER A B) = (INT x:A. f ` B x)"
apply (simp add: inj_on_def, blast)
done

(*Compare with image_INT: no use of inj_on, and if f is surjective then
  it doesn't matter whether A is empty*)
lemma bij_image_INT: "bij f ==> f ` (INTER A B) = (INT x:A. f ` B x)"
apply (simp add: bij_def)
apply (simp add: inj_on_def surj_def, blast)
done

lemma UNION_fun_upd:
  "UNION J (A(i:=B)) = (UNION (J-{i}) A \<union> (if i\<in>J then B else {}))"
by (auto split: if_splits)


subsubsection {* Complement *}

lemma Compl_INT [simp]: "- (\<Inter>x\<in>A. B x) = (\<Union>x\<in>A. -B x)"
  by (fact uminus_INF)

lemma Compl_UN [simp]: "- (\<Union>x\<in>A. B x) = (\<Inter>x\<in>A. -B x)"
  by (fact uminus_SUP)


subsubsection {* Miniscoping and maxiscoping *}

text {* \medskip Miniscoping: pushing in quantifiers and big Unions
           and Intersections. *}

lemma UN_simps [simp]:
  "\<And>a B C. (\<Union>x\<in>C. insert a (B x)) = (if C={} then {} else insert a (\<Union>x\<in>C. B x))"
  "\<And>A B C. (\<Union>x\<in>C. A x \<union> B) = ((if C={} then {} else (\<Union>x\<in>C. A x) \<union> B))"
  "\<And>A B C. (\<Union>x\<in>C. A \<union> B x) = ((if C={} then {} else A \<union> (\<Union>x\<in>C. B x)))"
  "\<And>A B C. (\<Union>x\<in>C. A x \<inter> B) = ((\<Union>x\<in>C. A x) \<inter> B)"
  "\<And>A B C. (\<Union>x\<in>C. A \<inter> B x) = (A \<inter>(\<Union>x\<in>C. B x))"
  "\<And>A B C. (\<Union>x\<in>C. A x - B) = ((\<Union>x\<in>C. A x) - B)"
  "\<And>A B C. (\<Union>x\<in>C. A - B x) = (A - (\<Inter>x\<in>C. B x))"
  "\<And>A B. (\<Union>x\<in>\<Union>A. B x) = (\<Union>y\<in>A. \<Union>x\<in>y. B x)"
  "\<And>A B C. (\<Union>z\<in>UNION A B. C z) = (\<Union>x\<in>A. \<Union>z\<in>B x. C z)"
  "\<And>A B f. (\<Union>x\<in>f`A. B x) = (\<Union>a\<in>A. B (f a))"
  by auto

lemma INT_simps [simp]:
  "\<And>A B C. (\<Inter>x\<in>C. A x \<inter> B) = (if C={} then UNIV else (\<Inter>x\<in>C. A x) \<inter> B)"
  "\<And>A B C. (\<Inter>x\<in>C. A \<inter> B x) = (if C={} then UNIV else A \<inter>(\<Inter>x\<in>C. B x))"
  "\<And>A B C. (\<Inter>x\<in>C. A x - B) = (if C={} then UNIV else (\<Inter>x\<in>C. A x) - B)"
  "\<And>A B C. (\<Inter>x\<in>C. A - B x) = (if C={} then UNIV else A - (\<Union>x\<in>C. B x))"
  "\<And>a B C. (\<Inter>x\<in>C. insert a (B x)) = insert a (\<Inter>x\<in>C. B x)"
  "\<And>A B C. (\<Inter>x\<in>C. A x \<union> B) = ((\<Inter>x\<in>C. A x) \<union> B)"
  "\<And>A B C. (\<Inter>x\<in>C. A \<union> B x) = (A \<union> (\<Inter>x\<in>C. B x))"
  "\<And>A B. (\<Inter>x\<in>\<Union>A. B x) = (\<Inter>y\<in>A. \<Inter>x\<in>y. B x)"
  "\<And>A B C. (\<Inter>z\<in>UNION A B. C z) = (\<Inter>x\<in>A. \<Inter>z\<in>B x. C z)"
  "\<And>A B f. (\<Inter>x\<in>f`A. B x) = (\<Inter>a\<in>A. B (f a))"
  by auto

lemma UN_ball_bex_simps [simp]:
  "\<And>A P. (\<forall>x\<in>\<Union>A. P x) \<longleftrightarrow> (\<forall>y\<in>A. \<forall>x\<in>y. P x)"
  "\<And>A B P. (\<forall>x\<in>UNION A B. P x) = (\<forall>a\<in>A. \<forall>x\<in> B a. P x)"
  "\<And>A P. (\<exists>x\<in>\<Union>A. P x) \<longleftrightarrow> (\<exists>y\<in>A. \<exists>x\<in>y. P x)"
  "\<And>A B P. (\<exists>x\<in>UNION A B. P x) \<longleftrightarrow> (\<exists>a\<in>A. \<exists>x\<in>B a. P x)"
  by auto


text {* \medskip Maxiscoping: pulling out big Unions and Intersections. *}

lemma UN_extend_simps:
  "\<And>a B C. insert a (\<Union>x\<in>C. B x) = (if C={} then {a} else (\<Union>x\<in>C. insert a (B x)))"
  "\<And>A B C. (\<Union>x\<in>C. A x) \<union> B = (if C={} then B else (\<Union>x\<in>C. A x \<union> B))"
  "\<And>A B C. A \<union> (\<Union>x\<in>C. B x) = (if C={} then A else (\<Union>x\<in>C. A \<union> B x))"
  "\<And>A B C. ((\<Union>x\<in>C. A x) \<inter> B) = (\<Union>x\<in>C. A x \<inter> B)"
  "\<And>A B C. (A \<inter> (\<Union>x\<in>C. B x)) = (\<Union>x\<in>C. A \<inter> B x)"
  "\<And>A B C. ((\<Union>x\<in>C. A x) - B) = (\<Union>x\<in>C. A x - B)"
  "\<And>A B C. (A - (\<Inter>x\<in>C. B x)) = (\<Union>x\<in>C. A - B x)"
  "\<And>A B. (\<Union>y\<in>A. \<Union>x\<in>y. B x) = (\<Union>x\<in>\<Union>A. B x)"
  "\<And>A B C. (\<Union>x\<in>A. \<Union>z\<in>B x. C z) = (\<Union>z\<in>UNION A B. C z)"
  "\<And>A B f. (\<Union>a\<in>A. B (f a)) = (\<Union>x\<in>f`A. B x)"
  by auto

lemma INT_extend_simps:
  "\<And>A B C. (\<Inter>x\<in>C. A x) \<inter> B = (if C={} then B else (\<Inter>x\<in>C. A x \<inter> B))"
  "\<And>A B C. A \<inter> (\<Inter>x\<in>C. B x) = (if C={} then A else (\<Inter>x\<in>C. A \<inter> B x))"
  "\<And>A B C. (\<Inter>x\<in>C. A x) - B = (if C={} then UNIV - B else (\<Inter>x\<in>C. A x - B))"
  "\<And>A B C. A - (\<Union>x\<in>C. B x) = (if C={} then A else (\<Inter>x\<in>C. A - B x))"
  "\<And>a B C. insert a (\<Inter>x\<in>C. B x) = (\<Inter>x\<in>C. insert a (B x))"
  "\<And>A B C. ((\<Inter>x\<in>C. A x) \<union> B) = (\<Inter>x\<in>C. A x \<union> B)"
  "\<And>A B C. A \<union> (\<Inter>x\<in>C. B x) = (\<Inter>x\<in>C. A \<union> B x)"
  "\<And>A B. (\<Inter>y\<in>A. \<Inter>x\<in>y. B x) = (\<Inter>x\<in>\<Union>A. B x)"
  "\<And>A B C. (\<Inter>x\<in>A. \<Inter>z\<in>B x. C z) = (\<Inter>z\<in>UNION A B. C z)"
  "\<And>A B f. (\<Inter>a\<in>A. B (f a)) = (\<Inter>x\<in>f`A. B x)"
  by auto

text {* Finally *}

no_notation
  less_eq (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50)

lemmas mem_simps =
  insert_iff empty_iff Un_iff Int_iff Compl_iff Diff_iff
  mem_Collect_eq UN_iff Union_iff INT_iff Inter_iff
  -- {* Each of these has ALREADY been added @{text "[simp]"} above. *}

end

