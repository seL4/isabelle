(*  Title:      HOL/Hull.thy
    Author:     Amine Chaieb, University of Cambridge
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
    Author:     Johannes Hölzl, VU Amsterdam
*)

theory Hull
  imports Main
begin

subsection \<open>A generic notion of the convex, affine, conic hull, or closed "hull".\<close>

definition hull :: "('a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set"  (infixl \<open>hull\<close> 75)
  where "S hull s = \<Inter>{t. S t \<and> s \<subseteq> t}"

lemma hull_same: "S s \<Longrightarrow> S hull s = s"
  unfolding hull_def by auto

lemma hull_in: "(\<And>T. Ball T S \<Longrightarrow> S (\<Inter>T)) \<Longrightarrow> S (S hull s)"
  unfolding hull_def Ball_def by auto

lemma hull_eq: "(\<And>T. Ball T S \<Longrightarrow> S (\<Inter>T)) \<Longrightarrow> (S hull s) = s \<longleftrightarrow> S s"
  using hull_same[of S s] hull_in[of S s] by metis

lemma hull_hull [simp]: "S hull (S hull s) = S hull s"
  unfolding hull_def by blast

lemma hull_subset[intro]: "s \<subseteq> (S hull s)"
  unfolding hull_def by blast

lemma hull_mono: "s \<subseteq> t \<Longrightarrow> (S hull s) \<subseteq> (S hull t)"
  unfolding hull_def by blast

lemma hull_antimono: "\<forall>x. S x \<longrightarrow> T x \<Longrightarrow> (T hull s) \<subseteq> (S hull s)"
  unfolding hull_def by blast

lemma hull_minimal: "s \<subseteq> t \<Longrightarrow> S t \<Longrightarrow> (S hull s) \<subseteq> t"
  unfolding hull_def by blast

lemma subset_hull: "S t \<Longrightarrow> S hull s \<subseteq> t \<longleftrightarrow> s \<subseteq> t"
  unfolding hull_def by blast

lemma hull_UNIV [simp]: "S hull UNIV = UNIV"
  unfolding hull_def by auto

lemma hull_unique: "s \<subseteq> t \<Longrightarrow> S t \<Longrightarrow> (\<And>t'. s \<subseteq> t' \<Longrightarrow> S t' \<Longrightarrow> t \<subseteq> t') \<Longrightarrow> (S hull s = t)"
  unfolding hull_def by auto

lemma hull_induct: "\<lbrakk>a \<in> Q hull S; \<And>x. x\<in> S \<Longrightarrow> P x; Q {x. P x}\<rbrakk> \<Longrightarrow> P a"
  using hull_minimal[of S "{x. P x}" Q]
  by (auto simp add: subset_eq)

lemma hull_inc: "x \<in> S \<Longrightarrow> x \<in> P hull S"
  by (metis hull_subset subset_eq)

lemma hull_Un_subset: "(S hull s) \<union> (S hull t) \<subseteq> (S hull (s \<union> t))"
  unfolding Un_subset_iff by (metis hull_mono Un_upper1 Un_upper2)

lemma hull_Un:
  assumes T: "\<And>T. Ball T S \<Longrightarrow> S (\<Inter>T)"
  shows "S hull (s \<union> t) = S hull (S hull s \<union> S hull t)"
  apply (rule equalityI)
  apply (meson hull_mono hull_subset sup.mono)
  by (metis hull_Un_subset hull_hull hull_mono)

lemma hull_Un_left: "P hull (S \<union> T) = P hull (P hull S \<union> T)"
  apply (rule equalityI)
   apply (simp add: Un_commute hull_mono hull_subset sup.coboundedI2)
  by (metis Un_subset_iff hull_hull hull_mono hull_subset)

lemma hull_Un_right: "P hull (S \<union> T) = P hull (S \<union> P hull T)"
  by (metis hull_Un_left sup.commute)

lemma hull_insert:
   "P hull (insert a S) = P hull (insert a (P hull S))"
  by (metis hull_Un_right insert_is_Un)

lemma hull_redundant_eq: "a \<in> (S hull s) \<longleftrightarrow> S hull (insert a s) = S hull s"
  unfolding hull_def by blast

lemma hull_redundant: "a \<in> (S hull s) \<Longrightarrow> S hull (insert a s) = S hull s"
  by (metis hull_redundant_eq)

end