(*  Title:      HOL/Library/Countable_Complete_Lattices.thy
    Author:     Johannes Hölzl
*)

section \<open>Countable Complete Lattices\<close>

theory Countable_Complete_Lattices
  imports Main Lattice_Syntax Countable_Set
begin

lemma UNIV_nat_eq: "UNIV = insert 0 (range Suc)"
  by (metis UNIV_eq_I nat.nchotomy insertCI rangeI)

class countable_complete_lattice = lattice + Inf + Sup + bot + top +
  assumes ccInf_lower: "countable A \<Longrightarrow> x \<in> A \<Longrightarrow> \<Sqinter>A \<le> x"
  assumes ccInf_greatest: "countable A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> \<Sqinter>A"
  assumes ccSup_upper: "countable A \<Longrightarrow> x \<in> A \<Longrightarrow> x \<le> \<Squnion>A"
  assumes ccSup_least: "countable A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> \<Squnion>A \<le> z"
  assumes ccInf_empty [simp]: "\<Sqinter>{} = \<top>"
  assumes ccSup_empty [simp]: "\<Squnion>{} = \<bottom>"
begin

subclass bounded_lattice
proof
  fix a
  show "\<bottom> \<le> a" by (auto intro: ccSup_least simp only: ccSup_empty [symmetric])
  show "a \<le> \<top>" by (auto intro: ccInf_greatest simp only: ccInf_empty [symmetric])
qed

lemma ccINF_lower: "countable A \<Longrightarrow> i \<in> A \<Longrightarrow> (\<Sqinter>i\<in>A. f i) \<le> f i"
  using ccInf_lower [of "f ` A"] by simp

lemma ccINF_greatest: "countable A \<Longrightarrow> (\<And>i. i \<in> A \<Longrightarrow> u \<le> f i) \<Longrightarrow> u \<le> (\<Sqinter>i\<in>A. f i)"
  using ccInf_greatest [of "f ` A"] by auto

lemma ccSUP_upper: "countable A \<Longrightarrow> i \<in> A \<Longrightarrow> f i \<le> (\<Squnion>i\<in>A. f i)"
  using ccSup_upper [of "f ` A"] by simp

lemma ccSUP_least: "countable A \<Longrightarrow> (\<And>i. i \<in> A \<Longrightarrow> f i \<le> u) \<Longrightarrow> (\<Squnion>i\<in>A. f i) \<le> u"
  using ccSup_least [of "f ` A"] by auto

lemma ccInf_lower2: "countable A \<Longrightarrow> u \<in> A \<Longrightarrow> u \<le> v \<Longrightarrow> \<Sqinter>A \<le> v"
  using ccInf_lower [of A u] by auto

lemma ccINF_lower2: "countable A \<Longrightarrow> i \<in> A \<Longrightarrow> f i \<le> u \<Longrightarrow> (\<Sqinter>i\<in>A. f i) \<le> u"
  using ccINF_lower [of A i f] by auto

lemma ccSup_upper2: "countable A \<Longrightarrow> u \<in> A \<Longrightarrow> v \<le> u \<Longrightarrow> v \<le> \<Squnion>A"
  using ccSup_upper [of A u] by auto

lemma ccSUP_upper2: "countable A \<Longrightarrow> i \<in> A \<Longrightarrow> u \<le> f i \<Longrightarrow> u \<le> (\<Squnion>i\<in>A. f i)"
  using ccSUP_upper [of A i f] by auto

lemma le_ccInf_iff: "countable A \<Longrightarrow> b \<le> \<Sqinter>A \<longleftrightarrow> (\<forall>a\<in>A. b \<le> a)"
  by (auto intro: ccInf_greatest dest: ccInf_lower)

lemma le_ccINF_iff: "countable A \<Longrightarrow> u \<le> (\<Sqinter>i\<in>A. f i) \<longleftrightarrow> (\<forall>i\<in>A. u \<le> f i)"
  using le_ccInf_iff [of "f ` A"] by simp

lemma ccSup_le_iff: "countable A \<Longrightarrow> \<Squnion>A \<le> b \<longleftrightarrow> (\<forall>a\<in>A. a \<le> b)"
  by (auto intro: ccSup_least dest: ccSup_upper)

lemma ccSUP_le_iff: "countable A \<Longrightarrow> (\<Squnion>i\<in>A. f i) \<le> u \<longleftrightarrow> (\<forall>i\<in>A. f i \<le> u)"
  using ccSup_le_iff [of "f ` A"] by simp

lemma ccInf_insert [simp]: "countable A \<Longrightarrow> \<Sqinter>insert a A = a \<sqinter> \<Sqinter>A"
  by (force intro: le_infI le_infI1 le_infI2 antisym ccInf_greatest ccInf_lower)

lemma ccINF_insert [simp]: "countable A \<Longrightarrow> (\<Sqinter>x\<in>insert a A. f x) = f a \<sqinter> INFIMUM A f"
  unfolding image_insert by simp

lemma ccSup_insert [simp]: "countable A \<Longrightarrow> \<Squnion>insert a A = a \<squnion> \<Squnion>A"
  by (force intro: le_supI le_supI1 le_supI2 antisym ccSup_least ccSup_upper)

lemma ccSUP_insert [simp]: "countable A \<Longrightarrow> (\<Squnion>x\<in>insert a A. f x) = f a \<squnion> SUPREMUM A f"
  unfolding image_insert by simp

lemma ccINF_empty [simp]: "(\<Sqinter>x\<in>{}. f x) = \<top>"
  unfolding image_empty by simp

lemma ccSUP_empty [simp]: "(\<Squnion>x\<in>{}. f x) = \<bottom>"
  unfolding image_empty by simp

lemma ccInf_superset_mono: "countable A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> \<Sqinter>A \<le> \<Sqinter>B"
  by (auto intro: ccInf_greatest ccInf_lower countable_subset)

lemma ccSup_subset_mono: "countable B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> \<Squnion>A \<le> \<Squnion>B"
  by (auto intro: ccSup_least ccSup_upper countable_subset)

lemma ccInf_mono:
  assumes [intro]: "countable B" "countable A"
  assumes "\<And>b. b \<in> B \<Longrightarrow> \<exists>a\<in>A. a \<le> b"
  shows "\<Sqinter>A \<le> \<Sqinter>B"
proof (rule ccInf_greatest)
  fix b assume "b \<in> B"
  with assms obtain a where "a \<in> A" and "a \<le> b" by blast
  from \<open>a \<in> A\<close> have "\<Sqinter>A \<le> a" by (rule ccInf_lower[rotated]) auto
  with \<open>a \<le> b\<close> show "\<Sqinter>A \<le> b" by auto
qed auto

lemma ccINF_mono:
  "countable A \<Longrightarrow> countable B \<Longrightarrow> (\<And>m. m \<in> B \<Longrightarrow> \<exists>n\<in>A. f n \<le> g m) \<Longrightarrow> (\<Sqinter>n\<in>A. f n) \<le> (\<Sqinter>n\<in>B. g n)"
  using ccInf_mono [of "g ` B" "f ` A"] by auto

lemma ccSup_mono:
  assumes [intro]: "countable B" "countable A"
  assumes "\<And>a. a \<in> A \<Longrightarrow> \<exists>b\<in>B. a \<le> b"
  shows "\<Squnion>A \<le> \<Squnion>B"
proof (rule ccSup_least)
  fix a assume "a \<in> A"
  with assms obtain b where "b \<in> B" and "a \<le> b" by blast
  from \<open>b \<in> B\<close> have "b \<le> \<Squnion>B" by (rule ccSup_upper[rotated]) auto
  with \<open>a \<le> b\<close> show "a \<le> \<Squnion>B" by auto
qed auto

lemma ccSUP_mono:
  "countable A \<Longrightarrow> countable B \<Longrightarrow> (\<And>n. n \<in> A \<Longrightarrow> \<exists>m\<in>B. f n \<le> g m) \<Longrightarrow> (\<Squnion>n\<in>A. f n) \<le> (\<Squnion>n\<in>B. g n)"
  using ccSup_mono [of "g ` B" "f ` A"] by auto

lemma ccINF_superset_mono:
  "countable A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> f x \<le> g x) \<Longrightarrow> (\<Sqinter>x\<in>A. f x) \<le> (\<Sqinter>x\<in>B. g x)"
  by (blast intro: ccINF_mono countable_subset dest: subsetD)

lemma ccSUP_subset_mono:
  "countable B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x) \<Longrightarrow> (\<Squnion>x\<in>A. f x) \<le> (\<Squnion>x\<in>B. g x)"
  by (blast intro: ccSUP_mono countable_subset dest: subsetD)


lemma less_eq_ccInf_inter: "countable A \<Longrightarrow> countable B \<Longrightarrow> \<Sqinter>A \<squnion> \<Sqinter>B \<le> \<Sqinter>(A \<inter> B)"
  by (auto intro: ccInf_greatest ccInf_lower)

lemma ccSup_inter_less_eq: "countable A \<Longrightarrow> countable B \<Longrightarrow> \<Squnion>(A \<inter> B) \<le> \<Squnion>A \<sqinter> \<Squnion>B "
  by (auto intro: ccSup_least ccSup_upper)

lemma ccInf_union_distrib: "countable A \<Longrightarrow> countable B \<Longrightarrow> \<Sqinter>(A \<union> B) = \<Sqinter>A \<sqinter> \<Sqinter>B"
  by (rule antisym) (auto intro: ccInf_greatest ccInf_lower le_infI1 le_infI2)

lemma ccINF_union:
  "countable A \<Longrightarrow> countable B \<Longrightarrow> (\<Sqinter>i \<in> A \<union> B. M i) = (\<Sqinter>i \<in> A. M i) \<sqinter> (\<Sqinter>i\<in>B. M i)"
  by (auto intro!: antisym ccINF_mono intro: le_infI1 le_infI2 ccINF_greatest ccINF_lower)

lemma ccSup_union_distrib: "countable A \<Longrightarrow> countable B \<Longrightarrow> \<Squnion>(A \<union> B) = \<Squnion>A \<squnion> \<Squnion>B"
  by (rule antisym) (auto intro: ccSup_least ccSup_upper le_supI1 le_supI2)

lemma ccSUP_union:
  "countable A \<Longrightarrow> countable B \<Longrightarrow> (\<Squnion>i \<in> A \<union> B. M i) = (\<Squnion>i \<in> A. M i) \<squnion> (\<Squnion>i\<in>B. M i)"
  by (auto intro!: antisym ccSUP_mono intro: le_supI1 le_supI2 ccSUP_least ccSUP_upper)

lemma ccINF_inf_distrib: "countable A \<Longrightarrow> (\<Sqinter>a\<in>A. f a) \<sqinter> (\<Sqinter>a\<in>A. g a) = (\<Sqinter>a\<in>A. f a \<sqinter> g a)"
  by (rule antisym) (rule ccINF_greatest, auto intro: le_infI1 le_infI2 ccINF_lower ccINF_mono)

lemma ccSUP_sup_distrib: "countable A \<Longrightarrow> (\<Squnion>a\<in>A. f a) \<squnion> (\<Squnion>a\<in>A. g a) = (\<Squnion>a\<in>A. f a \<squnion> g a)"
  by (rule antisym[rotated]) (rule ccSUP_least, auto intro: le_supI1 le_supI2 ccSUP_upper ccSUP_mono)

lemma ccINF_const [simp]: "A \<noteq> {} \<Longrightarrow> (\<Sqinter>i\<in>A. f) = f"
  unfolding image_constant_conv by auto

lemma ccSUP_const [simp]: "A \<noteq> {} \<Longrightarrow> (\<Squnion>i\<in>A. f) = f"
  unfolding image_constant_conv by auto

lemma ccINF_top [simp]: "(\<Sqinter>x\<in>A. \<top>) = \<top>"
  by (cases "A = {}") simp_all

lemma ccSUP_bot [simp]: "(\<Squnion>x\<in>A. \<bottom>) = \<bottom>"
  by (cases "A = {}") simp_all

lemma ccINF_commute: "countable A \<Longrightarrow> countable B \<Longrightarrow> (\<Sqinter>i\<in>A. \<Sqinter>j\<in>B. f i j) = (\<Sqinter>j\<in>B. \<Sqinter>i\<in>A. f i j)"
  by (iprover intro: ccINF_lower ccINF_greatest order_trans antisym)

lemma ccSUP_commute: "countable A \<Longrightarrow> countable B \<Longrightarrow> (\<Squnion>i\<in>A. \<Squnion>j\<in>B. f i j) = (\<Squnion>j\<in>B. \<Squnion>i\<in>A. f i j)"
  by (iprover intro: ccSUP_upper ccSUP_least order_trans antisym)

end

context
  fixes a :: "'a::{countable_complete_lattice, linorder}"
begin

lemma less_ccSup_iff: "countable S \<Longrightarrow> a < \<Squnion>S \<longleftrightarrow> (\<exists>x\<in>S. a < x)"
  unfolding not_le [symmetric] by (subst ccSup_le_iff) auto

lemma less_ccSUP_iff: "countable A \<Longrightarrow> a < (\<Squnion>i\<in>A. f i) \<longleftrightarrow> (\<exists>x\<in>A. a < f x)"
  using less_ccSup_iff [of "f ` A"] by simp

lemma ccInf_less_iff: "countable S \<Longrightarrow> \<Sqinter>S < a \<longleftrightarrow> (\<exists>x\<in>S. x < a)"
  unfolding not_le [symmetric] by (subst le_ccInf_iff) auto

lemma ccINF_less_iff: "countable A \<Longrightarrow> (\<Sqinter>i\<in>A. f i) < a \<longleftrightarrow> (\<exists>x\<in>A. f x < a)"
  using ccInf_less_iff [of "f ` A"] by simp

end

class countable_complete_distrib_lattice = countable_complete_lattice +
  assumes sup_ccInf: "countable B \<Longrightarrow> a \<squnion> \<Sqinter>B = (\<Sqinter>b\<in>B. a \<squnion> b)"
  assumes inf_ccSup: "countable B \<Longrightarrow> a \<sqinter> \<Squnion>B = (\<Squnion>b\<in>B. a \<sqinter> b)"
begin

lemma sup_ccINF:
  "countable B \<Longrightarrow> a \<squnion> (\<Sqinter>b\<in>B. f b) = (\<Sqinter>b\<in>B. a \<squnion> f b)"
  by (simp only: sup_ccInf image_image countable_image)

lemma inf_ccSUP:
  "countable B \<Longrightarrow> a \<sqinter> (\<Squnion>b\<in>B. f b) = (\<Squnion>b\<in>B. a \<sqinter> f b)"
  by (simp only: inf_ccSup image_image countable_image)

subclass distrib_lattice proof
  fix a b c
  from sup_ccInf[of "{b, c}" a] have "a \<squnion> \<Sqinter>{b, c} = (\<Sqinter>d\<in>{b, c}. a \<squnion> d)"
    by simp
  then show "a \<squnion> b \<sqinter> c = (a \<squnion> b) \<sqinter> (a \<squnion> c)" by simp
qed

lemma ccInf_sup:
  "countable B \<Longrightarrow> \<Sqinter>B \<squnion> a = (\<Sqinter>b\<in>B. b \<squnion> a)"
  by (simp add: sup_ccInf sup_commute)

lemma ccSup_inf:
  "countable B \<Longrightarrow> \<Squnion>B \<sqinter> a = (\<Squnion>b\<in>B. b \<sqinter> a)"
  by (simp add: inf_ccSup inf_commute)

lemma ccINF_sup:
  "countable B \<Longrightarrow> (\<Sqinter>b\<in>B. f b) \<squnion> a = (\<Sqinter>b\<in>B. f b \<squnion> a)"
  by (simp add: sup_ccINF sup_commute)

lemma ccSUP_inf:
  "countable B \<Longrightarrow> (\<Squnion>b\<in>B. f b) \<sqinter> a = (\<Squnion>b\<in>B. f b \<sqinter> a)"
  by (simp add: inf_ccSUP inf_commute)

lemma ccINF_sup_distrib2:
  "countable A \<Longrightarrow> countable B \<Longrightarrow> (\<Sqinter>a\<in>A. f a) \<squnion> (\<Sqinter>b\<in>B. g b) = (\<Sqinter>a\<in>A. \<Sqinter>b\<in>B. f a \<squnion> g b)"
  by (subst ccINF_commute) (simp_all add: sup_ccINF ccINF_sup)

lemma ccSUP_inf_distrib2:
  "countable A \<Longrightarrow> countable B \<Longrightarrow> (\<Squnion>a\<in>A. f a) \<sqinter> (\<Squnion>b\<in>B. g b) = (\<Squnion>a\<in>A. \<Squnion>b\<in>B. f a \<sqinter> g b)"
  by (subst ccSUP_commute) (simp_all add: inf_ccSUP ccSUP_inf)

context
  fixes f :: "'a \<Rightarrow> 'b::countable_complete_lattice"
  assumes "mono f"
begin

lemma mono_ccInf:
  "countable A \<Longrightarrow> f (\<Sqinter>A) \<le> (\<Sqinter>x\<in>A. f x)"
  using \<open>mono f\<close>
  by (auto intro!: countable_complete_lattice_class.ccINF_greatest intro: ccInf_lower dest: monoD)

lemma mono_ccSup:
  "countable A \<Longrightarrow> (\<Squnion>x\<in>A. f x) \<le> f (\<Squnion>A)"
  using \<open>mono f\<close> by (auto intro: countable_complete_lattice_class.ccSUP_least ccSup_upper dest: monoD)

lemma mono_ccINF:
  "countable I \<Longrightarrow> f (INF i : I. A i) \<le> (INF x : I. f (A x))"
  by (intro countable_complete_lattice_class.ccINF_greatest monoD[OF \<open>mono f\<close>] ccINF_lower)

lemma mono_ccSUP:
  "countable I \<Longrightarrow> (SUP x : I. f (A x)) \<le> f (SUP i : I. A i)"
  by (intro countable_complete_lattice_class.ccSUP_least monoD[OF \<open>mono f\<close>] ccSUP_upper)

end

end

subsubsection \<open>Instances of countable complete lattices\<close>

instance "fun" :: (type, countable_complete_lattice) countable_complete_lattice
  by standard
     (auto simp: le_fun_def intro!: ccSUP_upper ccSUP_least ccINF_lower ccINF_greatest)

subclass (in complete_lattice) countable_complete_lattice
  by standard (auto intro: Sup_upper Sup_least Inf_lower Inf_greatest)

subclass (in complete_distrib_lattice) countable_complete_distrib_lattice
  by standard (auto intro: sup_Inf inf_Sup)

end