(*  Title:      HOL/Algebra/Algebraic_Closure.thy
    Author:     Paulo Emílio de Vilhena

With contributions by Martin Baillon.
*)

theory Algebraic_Closure
  imports Indexed_Polynomials Polynomial_Divisibility Finite_Extensions

begin

section \<open>Algebraic Closure\<close>

subsection \<open>Definitions\<close>

inductive iso_incl :: "'a ring \<Rightarrow> 'a ring \<Rightarrow> bool" (infixl "\<lesssim>" 65) for A B
  where iso_inclI [intro]: "id \<in> ring_hom A B \<Longrightarrow> iso_incl A B"

definition law_restrict :: "('a, 'b) ring_scheme \<Rightarrow> 'a ring"
  where "law_restrict R \<equiv> (ring.truncate R)
           \<lparr> mult := (\<lambda>a \<in> carrier R. \<lambda>b \<in> carrier R. a \<otimes>\<^bsub>R\<^esub> b),
              add := (\<lambda>a \<in> carrier R. \<lambda>b \<in> carrier R. a \<oplus>\<^bsub>R\<^esub> b) \<rparr>"

definition (in ring) \<sigma> :: "'a list \<Rightarrow> ((('a list \<times> nat) multiset) \<Rightarrow> 'a) list"
  where "\<sigma> P = map indexed_const P"

definition (in ring) extensions :: "((('a list \<times> nat) multiset) \<Rightarrow> 'a) ring set"
  where "extensions \<equiv> { L \<comment> \<open>such that\<close>.
           \<comment> \<open>i\<close>   (field L) \<and>
           \<comment> \<open>ii\<close>  (indexed_const \<in> ring_hom R L) \<and>
           \<comment> \<open>iii\<close> (\<forall>\<P> \<in> carrier L. carrier_coeff \<P>) \<and>
           \<comment> \<open>iv\<close>  (\<forall>\<P> \<in> carrier L. \<forall>P \<in> carrier (poly_ring R). \<forall>i.
                       \<not> index_free \<P> (P, i) \<longrightarrow>
                         \<X>\<^bsub>(P, i)\<^esub> \<in> carrier L \<and> (ring.eval L) (\<sigma> P) \<X>\<^bsub>(P, i)\<^esub> = \<zero>\<^bsub>L\<^esub>) }"

abbreviation (in ring) restrict_extensions :: "((('a list \<times> nat) multiset) \<Rightarrow> 'a) ring set" ("\<S>")
  where "\<S> \<equiv> law_restrict ` extensions"


subsection \<open>Basic Properties\<close>

(* ========== *)
lemma (in field) is_ring: "ring R"
  using ring_axioms .
(* ========== *)

lemma law_restrict_carrier: "carrier (law_restrict R) = carrier R"
  by (simp add: law_restrict_def ring.defs)

lemma law_restrict_one: "one (law_restrict R) = one R"
  by (simp add: law_restrict_def ring.defs)

lemma law_restrict_zero: "zero (law_restrict R) = zero R"
  by (simp add: law_restrict_def ring.defs)

lemma law_restrict_mult: "monoid.mult (law_restrict R) = (\<lambda>a \<in> carrier R. \<lambda>b \<in> carrier R. a \<otimes>\<^bsub>R\<^esub> b)"
  by (simp add: law_restrict_def ring.defs)

lemma law_restrict_add: "add (law_restrict R) = (\<lambda>a \<in> carrier R. \<lambda>b \<in> carrier R. a \<oplus>\<^bsub>R\<^esub> b)"
  by (simp add: law_restrict_def ring.defs)

lemma (in ring) law_restrict_is_ring: "ring (law_restrict R)"
  by (unfold_locales) (auto simp add: law_restrict_def Units_def ring.defs,
      simp_all add: a_assoc a_comm m_assoc l_distr r_distr a_lcomm)

lemma (in field) law_restrict_is_field: "field (law_restrict R)"
proof -
  have "comm_monoid_axioms (law_restrict R)"
    using m_comm unfolding comm_monoid_axioms_def law_restrict_carrier law_restrict_mult by auto
  then interpret L: cring "law_restrict R"
    using cring.intro law_restrict_is_ring comm_monoid.intro ring.is_monoid by auto
  have "Units R = Units (law_restrict R)"
    unfolding Units_def law_restrict_carrier law_restrict_mult law_restrict_one by auto
  thus ?thesis
    using L.cring_fieldI unfolding field_Units law_restrict_carrier law_restrict_zero by simp
qed

lemma law_restrict_iso_imp_eq:
  assumes "id \<in> ring_iso (law_restrict A) (law_restrict B)" and "ring A" and "ring B"
  shows "law_restrict A = law_restrict B"
proof -
  have "carrier A = carrier B"
    using ring_iso_memE(5)[OF assms(1)] unfolding bij_betw_def law_restrict_def by (simp add: ring.defs)
  hence mult: "a \<otimes>\<^bsub>law_restrict A\<^esub> b = a \<otimes>\<^bsub>law_restrict B\<^esub> b"
    and add:  "a \<oplus>\<^bsub>law_restrict A\<^esub> b = a \<oplus>\<^bsub>law_restrict B\<^esub> b" for a b
    using ring_iso_memE(2-3)[OF assms(1)] unfolding law_restrict_def by (auto simp add: ring.defs)
  have "monoid.mult (law_restrict A) = monoid.mult (law_restrict B)"
    using mult by auto
  moreover have "add (law_restrict A) = add (law_restrict B)"
    using add by auto
  moreover from \<open>carrier A = carrier B\<close> have "carrier (law_restrict A) = carrier (law_restrict B)"
    unfolding law_restrict_def by (simp add: ring.defs)
  moreover have "\<zero>\<^bsub>law_restrict A\<^esub> = \<zero>\<^bsub>law_restrict B\<^esub>"
    using ring_hom_zero[OF _ assms(2-3)[THEN ring.law_restrict_is_ring]] assms(1)
    unfolding ring_iso_def by auto
  moreover have "\<one>\<^bsub>law_restrict A\<^esub> = \<one>\<^bsub>law_restrict B\<^esub>"
    using ring_iso_memE(4)[OF assms(1)] by simp
  ultimately show ?thesis by simp
qed

lemma law_restrict_hom: "h \<in> ring_hom A B \<longleftrightarrow> h \<in> ring_hom (law_restrict A) (law_restrict B)"
proof
  assume "h \<in> ring_hom A B" thus "h \<in> ring_hom (law_restrict A) (law_restrict B)"
    by (auto intro!: ring_hom_memI dest: ring_hom_memE simp: law_restrict_def ring.defs)
next
  assume h: "h \<in> ring_hom (law_restrict A) (law_restrict B)" show "h \<in> ring_hom A B"
    using ring_hom_memE[OF h] by (auto intro!: ring_hom_memI simp: law_restrict_def ring.defs)
qed

lemma iso_incl_hom: "A \<lesssim> B \<longleftrightarrow> (law_restrict A) \<lesssim> (law_restrict B)"
  using law_restrict_hom iso_incl.simps by blast


subsection \<open>Partial Order\<close>

lemma iso_incl_backwards:
  assumes "A \<lesssim> B" shows "id \<in> ring_hom A B"
  using assms by cases

lemma iso_incl_antisym_aux:
  assumes "A \<lesssim> B" and "B \<lesssim> A" shows "id \<in> ring_iso A B"
proof -
  have hom: "id \<in> ring_hom A B" "id \<in> ring_hom B A"
    using assms(1-2)[THEN iso_incl_backwards] by auto
  thus ?thesis
    using hom[THEN ring_hom_memE(1)] by (auto simp add: ring_iso_def bij_betw_def inj_on_def)
qed

lemma iso_incl_refl: "A \<lesssim> A"
  by (rule iso_inclI[OF ring_hom_memI], auto)

lemma iso_incl_trans:
  assumes "A \<lesssim> B" and "B \<lesssim> C" shows "A \<lesssim> C"
  using ring_hom_trans[OF assms[THEN iso_incl_backwards]] by auto

lemma (in ring) iso_incl_antisym:
  assumes "A \<in> \<S>" "B \<in> \<S>" and "A \<lesssim> B" "B \<lesssim> A" shows "A = B"
proof -
  obtain A' B' :: "(('a list \<times> nat) multiset \<Rightarrow> 'a) ring"
    where A: "A = law_restrict A'" "ring A'" and B: "B = law_restrict B'" "ring B'"
    using assms(1-2) field.is_ring by (auto simp add: extensions_def)
  thus ?thesis
    using law_restrict_iso_imp_eq iso_incl_antisym_aux[OF assms(3-4)] by simp
qed

lemma (in ring) iso_incl_partial_order: "partial_order_on \<S> (relation_of (\<lesssim>) \<S>)"
  using iso_incl_refl iso_incl_trans iso_incl_antisym by (rule partial_order_on_relation_ofI)

lemma iso_inclE:
  assumes "ring A" and "ring B" and "A \<lesssim> B" shows "ring_hom_ring A B id"
  using iso_incl_backwards[OF assms(3)] ring_hom_ring.intro[OF assms(1-2)]
  unfolding symmetric[OF ring_hom_ring_axioms_def] by simp

lemma iso_incl_imp_same_eval:
  assumes "ring A" and "ring B" and "A \<lesssim> B" and "a \<in> carrier A" and "set p \<subseteq> carrier A"
  shows "(ring.eval A) p a = (ring.eval B) p a"
  using ring_hom_ring.eval_hom'[OF iso_inclE[OF assms(1-3)] assms(4-5)] by simp


subsection \<open>Extensions Non Empty\<close>

lemma (in ring) indexed_const_is_inj: "inj indexed_const"
  unfolding indexed_const_def by (rule inj_onI, metis)

lemma (in ring) indexed_const_inj_on: "inj_on indexed_const (carrier R)"
  unfolding indexed_const_def by (rule inj_onI, metis)

lemma (in field) extensions_non_empty: "\<S> \<noteq> {}"
proof -
  have "image_ring indexed_const R \<in> extensions"
  proof (auto simp add: extensions_def)
    show "field (image_ring indexed_const R)"
      using inj_imp_image_ring_is_field[OF indexed_const_inj_on] .
  next
    show "indexed_const \<in> ring_hom R (image_ring indexed_const R)"
      using inj_imp_image_ring_iso[OF indexed_const_inj_on] unfolding ring_iso_def by auto
  next
    fix \<P> :: "(('a list \<times> nat) multiset) \<Rightarrow> 'a" and P and i
    assume "\<P> \<in> carrier (image_ring indexed_const R)"
    then obtain k where "k \<in> carrier R" and "\<P> = indexed_const k"
      unfolding image_ring_carrier by blast
    hence "index_free \<P> (P, i)" for P i
      unfolding index_free_def indexed_const_def by auto
    thus "\<not> index_free \<P> (P, i) \<Longrightarrow> \<X>\<^bsub>(P, i)\<^esub> \<in> carrier (image_ring indexed_const R)"
     and "\<not> index_free \<P> (P, i) \<Longrightarrow> ring.eval (image_ring indexed_const R) (\<sigma> P) \<X>\<^bsub>(P, i)\<^esub> = \<zero>\<^bsub>image_ring indexed_const R\<^esub>"
      by auto
    from \<open>k \<in> carrier R\<close> and \<open>\<P> = indexed_const k\<close> show "carrier_coeff \<P>"
      unfolding indexed_const_def carrier_coeff_def by auto
  qed
  thus ?thesis
    by blast
qed


subsection \<open>Chains\<close>

definition union_ring :: "(('a, 'c) ring_scheme) set \<Rightarrow> 'a ring"
  where "union_ring C =
           \<lparr> carrier = (\<Union>(carrier ` C)),
         monoid.mult = (\<lambda>a b. (monoid.mult (SOME R. R \<in> C \<and> a \<in> carrier R \<and> b \<in> carrier R) a b)),
                 one = one (SOME R. R \<in> C),
                zero = zero (SOME R. R \<in> C),
                 add = (\<lambda>a b. (add (SOME R. R \<in> C \<and> a \<in> carrier R \<and> b \<in> carrier R) a b)) \<rparr>"


lemma union_ring_carrier: "carrier (union_ring C) = (\<Union>(carrier ` C))"
  unfolding union_ring_def by simp

context
  fixes C :: "'a ring set"
  assumes field_chain: "\<And>R. R \<in> C \<Longrightarrow> field R" and chain: "\<And>R S. \<lbrakk> R \<in> C; S \<in> C \<rbrakk> \<Longrightarrow> R \<lesssim> S \<or> S \<lesssim> R"
begin

lemma ring_chain: "R \<in> C \<Longrightarrow> ring R"
  using field.is_ring[OF field_chain] by blast

lemma same_one_same_zero:
  assumes "R \<in> C" shows "\<one>\<^bsub>union_ring C\<^esub> = \<one>\<^bsub>R\<^esub>" and "\<zero>\<^bsub>union_ring C\<^esub> = \<zero>\<^bsub>R\<^esub>"
proof -
  have "\<one>\<^bsub>R\<^esub> = \<one>\<^bsub>S\<^esub>" if "R \<in> C" and "S \<in> C" for R S
    using ring_hom_one[of id] chain[OF that] unfolding iso_incl.simps by auto
  moreover have "\<zero>\<^bsub>R\<^esub> = \<zero>\<^bsub>S\<^esub>" if "R \<in> C" and "S \<in> C" for R S
    using chain[OF that] ring_hom_zero[OF _ ring_chain ring_chain] that unfolding iso_incl.simps by auto
  ultimately have "one (SOME R. R \<in> C) = \<one>\<^bsub>R\<^esub>" and "zero (SOME R. R \<in> C) = \<zero>\<^bsub>R\<^esub>"
    using assms by (metis (mono_tags) someI)+
  thus "\<one>\<^bsub>union_ring C\<^esub> = \<one>\<^bsub>R\<^esub>" and "\<zero>\<^bsub>union_ring C\<^esub> = \<zero>\<^bsub>R\<^esub>"
    unfolding union_ring_def by auto
qed

lemma same_laws:
  assumes "R \<in> C" and "a \<in> carrier R" and "b \<in> carrier R"
  shows "a \<otimes>\<^bsub>union_ring C\<^esub> b = a \<otimes>\<^bsub>R\<^esub> b" and "a \<oplus>\<^bsub>union_ring C\<^esub> b = a \<oplus>\<^bsub>R\<^esub> b"
proof -
  have "a \<otimes>\<^bsub>R\<^esub> b = a \<otimes>\<^bsub>S\<^esub> b"
    if "R \<in> C" "a \<in> carrier R" "b \<in> carrier R" and "S \<in> C" "a \<in> carrier S" "b \<in> carrier S" for R S
    using ring_hom_memE(2)[of id R S] ring_hom_memE(2)[of id S R] that chain[OF that(1,4)]
    unfolding iso_incl.simps by auto
  moreover have "a \<oplus>\<^bsub>R\<^esub> b = a \<oplus>\<^bsub>S\<^esub> b"
    if "R \<in> C" "a \<in> carrier R" "b \<in> carrier R" and "S \<in> C" "a \<in> carrier S" "b \<in> carrier S" for R S
    using ring_hom_memE(3)[of id R S] ring_hom_memE(3)[of id S R] that chain[OF that(1,4)]
    unfolding iso_incl.simps by auto
  ultimately
  have "monoid.mult (SOME R. R \<in> C \<and> a \<in> carrier R \<and> b \<in> carrier R) a b = a \<otimes>\<^bsub>R\<^esub> b"
   and         "add (SOME R. R \<in> C \<and> a \<in> carrier R \<and> b \<in> carrier R) a b = a \<oplus>\<^bsub>R\<^esub> b"
    using assms by (metis (mono_tags, lifting) someI)+
  thus "a \<otimes>\<^bsub>union_ring C\<^esub> b = a \<otimes>\<^bsub>R\<^esub> b" and "a \<oplus>\<^bsub>union_ring C\<^esub> b = a \<oplus>\<^bsub>R\<^esub> b"
    unfolding union_ring_def by auto
qed

lemma exists_superset_carrier:
  assumes "finite S" and "S \<noteq> {}" and "S \<subseteq> carrier (union_ring C)"
  shows "\<exists>R \<in> C. S \<subseteq> carrier R"
  using assms
proof (induction, simp)
  case (insert s S)
  obtain R where R: "s \<in> carrier R" "R \<in> C"
    using insert(5) unfolding union_ring_def by auto
  show ?case
  proof (cases)
    assume "S = {}" thus ?thesis
      using R by blast
  next
    assume "S \<noteq> {}"
    then obtain T where T: "S \<subseteq> carrier T" "T \<in> C"
      using insert(3,5) by blast
    have "carrier R \<subseteq> carrier T \<or> carrier T \<subseteq> carrier R"
      using ring_hom_memE(1)[of id R] ring_hom_memE(1)[of id T] chain[OF R(2) T(2)]
      unfolding iso_incl.simps by auto
    thus ?thesis
      using R T by auto
  qed
qed

lemma union_ring_is_monoid:
  assumes "C \<noteq> {}" shows "comm_monoid (union_ring C)"
proof
  fix a b c
  assume "a \<in> carrier (union_ring C)" "b \<in> carrier (union_ring C)" "c \<in> carrier (union_ring C)"
  then obtain R where R: "R \<in> C" "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
    using exists_superset_carrier[of "{ a, b, c }"] by auto
  then interpret field R
    using field_chain by simp

  show "a \<otimes>\<^bsub>union_ring C\<^esub> b \<in> carrier (union_ring C)"
    using R(1-3) unfolding same_laws(1)[OF R(1-3)] unfolding union_ring_def by auto
  show "(a \<otimes>\<^bsub>union_ring C\<^esub> b) \<otimes>\<^bsub>union_ring C\<^esub> c = a \<otimes>\<^bsub>union_ring C\<^esub> (b \<otimes>\<^bsub>union_ring C\<^esub> c)"
   and "a \<otimes>\<^bsub>union_ring C\<^esub> b = b \<otimes>\<^bsub>union_ring C\<^esub> a"
   and "\<one>\<^bsub>union_ring C\<^esub> \<otimes>\<^bsub>union_ring C\<^esub> a = a"
   and "a \<otimes>\<^bsub>union_ring C\<^esub> \<one>\<^bsub>union_ring C\<^esub> = a"
    using same_one_same_zero[OF R(1)] same_laws(1)[OF R(1)] R(2-4) m_assoc m_comm by auto
next
  show "\<one>\<^bsub>union_ring C\<^esub> \<in> carrier (union_ring C)"
    using ring.ring_simprules(6)[OF ring_chain] assms same_one_same_zero(1)
    unfolding union_ring_carrier by auto
qed

lemma union_ring_is_abelian_group:
  assumes "C \<noteq> {}" shows "cring (union_ring C)"
proof (rule cringI[OF abelian_groupI union_ring_is_monoid[OF assms]])
  fix a b c
  assume "a \<in> carrier (union_ring C)" "b \<in> carrier (union_ring C)" "c \<in> carrier (union_ring C)"
  then obtain R where R: "R \<in> C" "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
    using exists_superset_carrier[of "{ a, b, c }"] by auto
  then interpret field R
    using field_chain by simp

  show "a \<oplus>\<^bsub>union_ring C\<^esub> b \<in> carrier (union_ring C)"
    using R(1-3) unfolding same_laws(2)[OF R(1-3)] unfolding union_ring_def by auto
  show "(a \<oplus>\<^bsub>union_ring C\<^esub> b) \<otimes>\<^bsub>union_ring C\<^esub> c = (a \<otimes>\<^bsub>union_ring C\<^esub> c) \<oplus>\<^bsub>union_ring C\<^esub> (b \<otimes>\<^bsub>union_ring C\<^esub> c)"
   and "(a \<oplus>\<^bsub>union_ring C\<^esub> b) \<oplus>\<^bsub>union_ring C\<^esub> c = a \<oplus>\<^bsub>union_ring C\<^esub> (b \<oplus>\<^bsub>union_ring C\<^esub> c)"
   and "a \<oplus>\<^bsub>union_ring C\<^esub> b = b \<oplus>\<^bsub>union_ring C\<^esub> a"
   and "\<zero>\<^bsub>union_ring C\<^esub> \<oplus>\<^bsub>union_ring C\<^esub> a = a"
    using same_one_same_zero[OF R(1)] same_laws[OF R(1)] R(2-4) l_distr a_assoc a_comm by auto
  have "\<exists>a' \<in> carrier R. a' \<oplus>\<^bsub>union_ring C\<^esub> a = \<zero>\<^bsub>union_ring C\<^esub>"
    using same_laws(2)[OF R(1)] R(2) same_one_same_zero[OF R(1)] by simp
  with \<open>R \<in> C\<close> show "\<exists>y \<in> carrier (union_ring C). y \<oplus>\<^bsub>union_ring C\<^esub> a = \<zero>\<^bsub>union_ring C\<^esub>"
    unfolding union_ring_carrier by auto
next
  show "\<zero>\<^bsub>union_ring C\<^esub> \<in> carrier (union_ring C)"
    using ring.ring_simprules(2)[OF ring_chain] assms same_one_same_zero(2)
    unfolding union_ring_carrier by auto
qed

lemma union_ring_is_field :
  assumes "C \<noteq> {}" shows "field (union_ring C)"
proof (rule cring.cring_fieldI[OF union_ring_is_abelian_group[OF assms]])
  have "carrier (union_ring C) - { \<zero>\<^bsub>union_ring C\<^esub> } \<subseteq> Units (union_ring C)"
  proof
    fix a assume "a \<in> carrier (union_ring C) - { \<zero>\<^bsub>union_ring C\<^esub> }"
    hence "a \<in> carrier (union_ring C)" and "a \<noteq> \<zero>\<^bsub>union_ring C\<^esub>"
      by auto
    then obtain R where R: "R \<in> C" "a \<in> carrier R"
      using exists_superset_carrier[of "{ a }"] by auto
    then interpret field R
      using field_chain by simp

    from \<open>a \<in> carrier R\<close> and \<open>a \<noteq> \<zero>\<^bsub>union_ring C\<^esub>\<close> have "a \<in> Units R"
      unfolding same_one_same_zero[OF R(1)] field_Units by auto
    hence "\<exists>a' \<in> carrier R. a' \<otimes>\<^bsub>union_ring C\<^esub> a = \<one>\<^bsub>union_ring C\<^esub> \<and> a \<otimes>\<^bsub>union_ring C\<^esub> a' = \<one>\<^bsub>union_ring C\<^esub>"
      using same_laws[OF R(1)] same_one_same_zero[OF R(1)] R(2) unfolding Units_def by auto
    with \<open>R \<in> C\<close> and \<open>a \<in> carrier (union_ring C)\<close> show "a \<in> Units (union_ring C)"
      unfolding Units_def union_ring_carrier by auto
  qed
  moreover have "\<zero>\<^bsub>union_ring C\<^esub> \<notin> Units (union_ring C)"
  proof (rule ccontr)
    assume "\<not> \<zero>\<^bsub>union_ring C\<^esub> \<notin> Units (union_ring C)"
    then obtain a where a: "a \<in> carrier (union_ring C)" "a \<otimes>\<^bsub>union_ring C\<^esub> \<zero>\<^bsub>union_ring C\<^esub> = \<one>\<^bsub>union_ring C\<^esub>"
      unfolding Units_def by auto
    then obtain R where R: "R \<in> C" "a \<in> carrier R"
      using exists_superset_carrier[of "{ a }"] by auto
    then interpret field R
      using field_chain by simp
    have "\<one>\<^bsub>R\<^esub> = \<zero>\<^bsub>R\<^esub>"
      using a R same_laws(1)[OF R(1)] same_one_same_zero[OF R(1)] by auto
    thus False
      using one_not_zero by simp
  qed
  hence "Units (union_ring C) \<subseteq> carrier (union_ring C) - { \<zero>\<^bsub>union_ring C\<^esub> }"
    unfolding Units_def by auto
  ultimately show "Units (union_ring C) = carrier (union_ring C) - { \<zero>\<^bsub>union_ring C\<^esub> }"
    by simp
qed

lemma union_ring_is_upper_bound:
  assumes "R \<in> C" shows "R \<lesssim> union_ring C"
  using ring_hom_memI[of R id "union_ring C"] same_laws[of R] same_one_same_zero[of R] assms
  unfolding union_ring_carrier by auto

end


subsection \<open>Zorn\<close>

(* ========== *)
lemma Chains_relation_of:
  assumes "C \<in> Chains (relation_of P A)" shows "C \<subseteq> A"
  using assms unfolding Chains_def relation_of_def by auto
(* ========== *)

lemma (in ring) exists_core_chain:
  assumes "C \<in> Chains (relation_of (\<lesssim>) \<S>)" obtains C' where "C' \<subseteq> extensions" and "C = law_restrict ` C'"
  using Chains_relation_of[OF assms] by (meson subset_image_iff)

lemma (in ring) core_chain_is_chain:
  assumes "law_restrict ` C \<in> Chains (relation_of (\<lesssim>) \<S>)" shows "\<And>R S. \<lbrakk> R \<in> C; S \<in> C \<rbrakk> \<Longrightarrow> R \<lesssim> S \<or> S \<lesssim> R"
proof -
  fix R S assume "R \<in> C" and "S \<in> C" thus "R \<lesssim> S \<or> S \<lesssim> R"
    using assms(1) unfolding iso_incl_hom[of R] iso_incl_hom[of S] Chains_def relation_of_def
    by auto
qed

lemma (in field) exists_maximal_extension:
  shows "\<exists>M \<in> \<S>. \<forall>L \<in> \<S>. M \<lesssim> L \<longrightarrow> L = M"
proof (rule predicate_Zorn[OF iso_incl_partial_order])
  fix C assume C: "C \<in> Chains (relation_of (\<lesssim>) \<S>)"
  show "\<exists>L \<in> \<S>. \<forall>R \<in> C. R \<lesssim> L"
  proof (cases)
    assume "C = {}" thus ?thesis
      using extensions_non_empty by auto
  next
    assume "C \<noteq> {}"
    from \<open>C \<in> Chains (relation_of (\<lesssim>) \<S>)\<close>
    obtain C' where C': "C' \<subseteq> extensions" "C = law_restrict ` C'"
      using exists_core_chain by auto
    with \<open>C \<noteq> {}\<close> obtain S where S: "S \<in> C'" and "C' \<noteq> {}"
      by auto

    have core_chain: "\<And>R. R \<in> C' \<Longrightarrow> field R" "\<And>R S. \<lbrakk> R \<in> C'; S \<in> C' \<rbrakk> \<Longrightarrow> R \<lesssim> S \<or> S \<lesssim> R"
      using core_chain_is_chain[of C'] C' C unfolding extensions_def by auto
    from \<open>C' \<noteq> {}\<close> interpret Union: field "union_ring C'"
        using union_ring_is_field[OF core_chain] C'(1) by blast

    have "union_ring C' \<in> extensions"
    proof (auto simp add: extensions_def)
      show "field (union_ring C')"
        using Union.field_axioms .
    next
      from \<open>S \<in> C'\<close> have "indexed_const \<in> ring_hom R S"
        using C'(1) unfolding extensions_def by auto
      thus "indexed_const \<in> ring_hom R (union_ring C')"
        using ring_hom_trans[of _ R S id] union_ring_is_upper_bound[OF core_chain S]
        unfolding iso_incl.simps by auto
    next
      show "a \<in> carrier (union_ring C') \<Longrightarrow> carrier_coeff a" for a
        using C'(1) unfolding union_ring_carrier extensions_def by auto
    next
      fix \<P> P i
      assume "\<P> \<in> carrier (union_ring C')"
        and P: "P \<in> carrier (poly_ring R)"
        and not_index_free: "\<not> index_free \<P> (P, i)"
      from \<open>\<P> \<in> carrier (union_ring C')\<close> obtain T where T: "T \<in> C'" "\<P> \<in> carrier T"
        using exists_superset_carrier[of C' "{ \<P> }"] core_chain by auto
      hence "\<X>\<^bsub>(P, i)\<^esub> \<in> carrier T" and "(ring.eval T) (\<sigma> P) \<X>\<^bsub>(P, i)\<^esub> = \<zero>\<^bsub>T\<^esub>"
        and field: "field T" and hom: "indexed_const \<in> ring_hom R T"
        using P not_index_free C'(1) unfolding extensions_def by auto
      with \<open>T \<in> C'\<close> show "\<X>\<^bsub>(P, i)\<^esub> \<in> carrier (union_ring C')"
        unfolding union_ring_carrier by auto
      have "set P \<subseteq> carrier R"
        using P unfolding sym[OF univ_poly_carrier] polynomial_def by auto
      hence "set (\<sigma> P) \<subseteq> carrier T"
        using ring_hom_memE(1)[OF hom] unfolding \<sigma>_def by (induct P) (auto)
      with \<open>\<X>\<^bsub>(P, i)\<^esub> \<in> carrier T\<close> and \<open>(ring.eval T) (\<sigma> P) \<X>\<^bsub>(P, i)\<^esub> = \<zero>\<^bsub>T\<^esub>\<close>
      show "(ring.eval (union_ring C')) (\<sigma> P) \<X>\<^bsub>(P, i)\<^esub> = \<zero>\<^bsub>union_ring C'\<^esub>"
        using iso_incl_imp_same_eval[OF field.is_ring[OF field] Union.is_ring
              union_ring_is_upper_bound[OF core_chain T(1)]] same_one_same_zero(2)[OF core_chain T(1)]
        by auto
    qed
    moreover have "R \<lesssim> law_restrict (union_ring C')" if "R \<in> C" for R
      using that union_ring_is_upper_bound[OF core_chain] iso_incl_hom unfolding C' by auto
    ultimately show ?thesis
      by blast
  qed
qed


subsection \<open>Existence of roots\<close>

lemma polynomial_hom:
  assumes "h \<in> ring_hom R S" and "field R" and "field S"
  shows "p \<in> carrier (poly_ring R) \<Longrightarrow> (map h p) \<in> carrier (poly_ring S)"
proof -
  assume "p \<in> carrier (poly_ring R)"
  interpret ring_hom_ring R S h
    using ring_hom_ringI2[OF assms(2-3)[THEN field.is_ring] assms(1)] .

  from \<open>p \<in> carrier (poly_ring R)\<close> have "set p \<subseteq> carrier R" and lc: "p \<noteq> [] \<Longrightarrow> lead_coeff p \<noteq> \<zero>\<^bsub>R\<^esub>"
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  hence "set (map h p) \<subseteq> carrier S"
    by (induct p) (auto)
  moreover have "h a = \<zero>\<^bsub>S\<^esub> \<Longrightarrow> a = \<zero>\<^bsub>R\<^esub>" if "a \<in> carrier R" for a
    using non_trivial_field_hom_is_inj[OF assms(1-3)] that unfolding inj_on_def by simp
  with \<open>set p \<subseteq> carrier R\<close> have "lead_coeff (map h p) \<noteq> \<zero>\<^bsub>S\<^esub>" if "p \<noteq> []"
    using lc[OF that] that by (cases p) (auto)
  ultimately show ?thesis
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
qed

lemma (in ring_hom_ring) subfield_polynomial_hom:
  assumes "subfield K R" and "\<one>\<^bsub>S\<^esub> \<noteq> \<zero>\<^bsub>S\<^esub>"
  shows "p \<in> carrier (K[X]\<^bsub>R\<^esub>) \<Longrightarrow> (map h p) \<in> carrier ((h ` K)[X]\<^bsub>S\<^esub>)"
proof -
  assume "p \<in> carrier (K[X]\<^bsub>R\<^esub>)"
  hence "p \<in> carrier (poly_ring (R \<lparr> carrier := K \<rparr>))"
    using R.univ_poly_consistent[OF subfieldE(1)[OF assms(1)]] by simp
  moreover have "h \<in> ring_hom (R \<lparr> carrier := K \<rparr>) (S \<lparr> carrier := h ` K \<rparr>)"
    using hom_mult subfieldE(3)[OF assms(1)] unfolding ring_hom_def subset_iff by auto
  moreover have "field (R \<lparr> carrier := K \<rparr>)" and "field (S \<lparr> carrier := (h ` K) \<rparr>)"
    using R.subfield_iff(2)[OF assms(1)] S.subfield_iff(2)[OF img_is_subfield(2)[OF assms]] by simp+
  ultimately have "(map h p) \<in> carrier (poly_ring (S \<lparr> carrier := h ` K \<rparr>))"
    using polynomial_hom[of h "R \<lparr> carrier := K \<rparr>" "S \<lparr> carrier := h ` K \<rparr>"] by auto
  thus ?thesis
    using S.univ_poly_consistent[OF subfieldE(1)[OF img_is_subfield(2)[OF assms]]] by simp
qed


(* MOVE ========== *)
subsection \<open>Roots and Multiplicity\<close>

definition (in ring) is_root :: "'a list \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_root p x \<longleftrightarrow> (x \<in> carrier R \<and> eval p x = \<zero> \<and> p \<noteq> [])"

definition (in ring) alg_mult :: "'a list \<Rightarrow> 'a \<Rightarrow> nat"
  where "alg_mult p x =
           (if p = [] then 0 else
             (if x \<in> carrier R then Greatest (\<lambda> n. ([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> n) pdivides p) else 0))"

definition (in ring) roots :: "'a list \<Rightarrow> 'a multiset"
  where "roots p = Abs_multiset (alg_mult p)"

definition (in ring) roots_on :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a multiset"
  where "roots_on K p = roots p \<inter># mset_set K"

definition (in ring) splitted :: "'a list \<Rightarrow> bool"
  where "splitted p \<longleftrightarrow> size (roots p) = degree p"

definition (in ring) splitted_on :: "'a set \<Rightarrow> 'a list \<Rightarrow> bool"
  where "splitted_on K p \<longleftrightarrow> size (roots_on K p) = degree p"

lemma (in domain) polynomial_pow_not_zero:
  assumes "p \<in> carrier (poly_ring R)" and "p \<noteq> []"
  shows "p [^]\<^bsub>poly_ring R\<^esub> (n::nat) \<noteq> []"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  from assms UP.integral show ?thesis
    unfolding sym[OF univ_poly_zero[of R "carrier R"]]
    by (induction n, auto)
qed

lemma (in domain) subring_polynomial_pow_not_zero:
  assumes "subring K R" and "p \<in> carrier (K[X])" and "p \<noteq> []"
  shows "p [^]\<^bsub>K[X]\<^esub> (n::nat) \<noteq> []"
  using domain.polynomial_pow_not_zero[OF subring_is_domain, of K p n] assms
  unfolding univ_poly_consistent[OF assms(1)] by simp

lemma (in domain) polynomial_pow_degree:
  assumes "p \<in> carrier (poly_ring R)"
  shows "degree (p [^]\<^bsub>poly_ring R\<^esub> n) = n * degree p"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  show ?thesis
  proof (induction n)
    case 0 thus ?case
      using UP.nat_pow_0 unfolding univ_poly_one by auto
  next
    let ?ppow = "\<lambda>n. p [^]\<^bsub>poly_ring R\<^esub> n"
    case (Suc n) thus ?case
    proof (cases "p = []")
      case True thus ?thesis
        using univ_poly_zero[of R "carrier R"] UP.r_null assms by auto
    next
      case False
      hence "?ppow n \<in> carrier (poly_ring R)" and "?ppow n \<noteq> []" and "p \<noteq> []"
        using polynomial_pow_not_zero[of p n] assms by (auto simp add: univ_poly_one)
      thus ?thesis
        using poly_mult_degree_eq[OF carrier_is_subring, of "?ppow n" p] Suc assms
        unfolding univ_poly_carrier univ_poly_zero
        by (auto simp add: add.commute univ_poly_mult)
    qed
  qed
qed

lemma (in domain) polynomial_pow_division:
  assumes "p \<in> carrier (poly_ring R)" and "(n::nat) \<le> m"
  shows "(p [^]\<^bsub>poly_ring R\<^esub> n) pdivides (p [^]\<^bsub>poly_ring R\<^esub> m)"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  let ?ppow = "\<lambda>n. p [^]\<^bsub>poly_ring R\<^esub> n"

  have "?ppow n \<otimes>\<^bsub>poly_ring R\<^esub> ?ppow k = ?ppow (n + k)" for k
    using assms(1) by (simp add: UP.nat_pow_mult)
  thus ?thesis
    using dividesI[of "?ppow (m - n)" "poly_ring R" "?ppow m" "?ppow n"] assms
    unfolding pdivides_def by auto
qed

lemma (in domain) degree_zero_imp_not_is_root:
  assumes "p \<in> carrier (poly_ring R)" and "degree p = 0" shows "\<not> is_root p x"
proof (cases "p = []", simp add: is_root_def)
  case False with \<open>degree p = 0\<close> have "length p = Suc 0"
    using le_SucE by fastforce
  then obtain a where "p = [ a ]" and "a \<in> carrier R" and "a \<noteq> \<zero>"
    using assms unfolding sym[OF univ_poly_carrier] polynomial_def
    by (metis False length_0_conv length_Suc_conv list.sel(1) list.set_sel(1) subset_code(1))
  thus ?thesis
    unfolding is_root_def by auto
qed

lemma (in domain) is_root_imp_pdivides:
  assumes "p \<in> carrier (poly_ring R)"
  shows "is_root p x \<Longrightarrow> [ \<one>, \<ominus> x ] pdivides p"
proof -
  let ?b = "[ \<one> , \<ominus> x ]"

  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  assume "is_root p x" hence x: "x \<in> carrier R" and is_root: "eval p x = \<zero>"
    unfolding is_root_def by auto
  hence b: "?b \<in> carrier (poly_ring R)"
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  then obtain q r where q: "q \<in> carrier (poly_ring R)" and r: "r \<in> carrier (poly_ring R)"
    and long_divides: "p = (?b \<otimes>\<^bsub>poly_ring R\<^esub> q) \<oplus>\<^bsub>poly_ring R\<^esub> r" "r = [] \<or> degree r < degree ?b"
    using long_division_theorem[OF carrier_is_subring, of p ?b] assms by (auto simp add: univ_poly_carrier)

  show ?thesis
  proof (cases "r = []")
    case True then have "r = \<zero>\<^bsub>poly_ring R\<^esub>"
      unfolding univ_poly_zero[of R "carrier R"] .
    thus ?thesis
      using long_divides(1) q r b dividesI[OF q, of p ?b] by (simp add: pdivides_def)
  next
    case False then have "length r = Suc 0"
      using long_divides(2) le_SucE by fastforce
    then obtain a where "r = [ a ]" and a: "a \<in> carrier R" and "a \<noteq> \<zero>"
      using r unfolding sym[OF univ_poly_carrier] polynomial_def
      by (metis False length_0_conv length_Suc_conv list.sel(1) list.set_sel(1) subset_code(1))

    have "eval p x = ((eval ?b x) \<otimes> (eval q x)) \<oplus> (eval r x)"
      using long_divides(1) ring_hom_memE[OF eval_is_hom[OF carrier_is_subring x]] by (simp add: b q r)
    also have " ... = eval r x"
      using ring_hom_memE[OF eval_is_hom[OF carrier_is_subring x]] x b q r by (auto, algebra)
    finally have "a = \<zero>"
      using a unfolding \<open>r = [ a ]\<close> is_root by simp
    with \<open>a \<noteq> \<zero>\<close> have False .. thus ?thesis ..
  qed
qed

lemma (in domain) pdivides_imp_is_root:
  assumes "p \<noteq> []" and "x \<in> carrier R"
  shows "[ \<one>, \<ominus> x ] pdivides p \<Longrightarrow> is_root p x"
proof -
  assume "[ \<one>, \<ominus> x ] pdivides p"
  then obtain q where q: "q \<in> carrier (poly_ring R)" and pdiv: "p = [ \<one>, \<ominus> x ] \<otimes>\<^bsub>poly_ring R\<^esub> q"
    unfolding pdivides_def by auto
  moreover have "[ \<one>, \<ominus> x ] \<in> carrier (poly_ring R)"
    using assms(2) unfolding sym[OF univ_poly_carrier] polynomial_def by simp
  ultimately have "eval p x = \<zero>"
    using ring_hom_memE[OF eval_is_hom[OF carrier_is_subring, of x]] assms(2) by (auto, algebra)
  with \<open>p \<noteq> []\<close> and \<open>x \<in> carrier R\<close> show "is_root p x"
    unfolding is_root_def by simp
qed

(* MOVE TO Polynomial_Dvisibility.thy ================== *)
lemma (in domain) associated_polynomials_imp_same_length: (* stronger than "imp_same_degree" *)
  assumes "subring K R" and "p \<in> carrier (K[X])" and "q \<in> carrier (K[X])"
  shows "p \<sim>\<^bsub>K[X]\<^esub> q \<Longrightarrow> length p = length q"
proof -
  { fix p q
    assume p: "p \<in> carrier (K[X])" and q: "q \<in> carrier (K[X])" and "p \<sim>\<^bsub>K[X]\<^esub> q"
    have "length p \<le> length q"
    proof (cases "q = []")
      case True with \<open>p \<sim>\<^bsub>K[X]\<^esub> q\<close> have "p = []"
        unfolding associated_def True factor_def univ_poly_def by auto
      thus ?thesis
        using True by simp
    next
      case False
      from \<open>p \<sim>\<^bsub>K[X]\<^esub> q\<close> have "p divides\<^bsub>K [X]\<^esub> q"
        unfolding associated_def by simp
      hence "p divides\<^bsub>poly_ring R\<^esub> q"
        using carrier_polynomial[OF assms(1)]
        unfolding factor_def univ_poly_carrier univ_poly_mult by auto
      with \<open>q \<noteq> []\<close> have "degree p \<le> degree q"
        using pdivides_imp_degree_le[OF assms(1) p q] unfolding pdivides_def by simp
      with \<open>q \<noteq> []\<close> show ?thesis
        by (cases "p = []", auto simp add: Suc_leI le_diff_iff)
    qed
  } note aux_lemma = this

  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] .

  assume "p \<sim>\<^bsub>K[X]\<^esub> q" thus ?thesis
    using aux_lemma[OF assms(2-3)] aux_lemma[OF assms(3,2) UP.associated_sym] by simp
qed
(* ================================================= *)

lemma (in domain) associated_polynomials_imp_same_is_root:
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)" and "p \<sim>\<^bsub>poly_ring R\<^esub> q"
  shows "is_root p x \<longleftrightarrow> is_root q x"
proof (cases "p = []")
  case True with \<open>p \<sim>\<^bsub>poly_ring R\<^esub> q\<close> have "q = []"
    unfolding associated_def True factor_def univ_poly_def by auto
  thus ?thesis
    using True unfolding is_root_def by simp
next
  case False
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  { fix p q
    assume p: "p \<in> carrier (poly_ring R)" and q: "q \<in> carrier (poly_ring R)" and pq: "p \<sim>\<^bsub>poly_ring R\<^esub> q"
    have "is_root p x \<Longrightarrow> is_root q x"
    proof -
      assume is_root: "is_root p x"
      then have "[ \<one>, \<ominus> x ] pdivides p" and "p \<noteq> []" and "x \<in> carrier R"
        using is_root_imp_pdivides[OF p] unfolding is_root_def by auto
      moreover have "[ \<one>, \<ominus> x ] \<in> carrier (poly_ring R)"
        using is_root unfolding is_root_def sym[OF univ_poly_carrier] polynomial_def by simp
      ultimately have "[ \<one>, \<ominus> x ] pdivides q"
        using UP.divides_cong_r[OF _ pq ] unfolding pdivides_def by simp
      with \<open>p \<noteq> []\<close> and \<open>x \<in> carrier R\<close> show ?thesis
        using associated_polynomials_imp_same_length[OF carrier_is_subring p q pq]
              pdivides_imp_is_root[of q x]
        by fastforce
    qed
  }

  then show ?thesis
    using assms UP.associated_sym[OF assms(3)] by blast
qed

lemma (in ring) monic_degree_one_root_condition:
  assumes "a \<in> carrier R" shows "is_root [ \<one>, \<ominus> a ] b \<longleftrightarrow> a = b"
  using assms minus_equality r_neg[OF assms] unfolding is_root_def by (auto, fastforce)

lemma (in field) degree_one_root_condition:
  assumes "p \<in> carrier (poly_ring R)" and "degree p = 1"
  shows "is_root p x \<longleftrightarrow> x = \<ominus> (inv (lead_coeff p) \<otimes> (const_term p))"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  from \<open>degree p = 1\<close> have "length p = Suc (Suc 0)"
    by simp
  then obtain a b where p: "p = [ a, b ]"
    by (metis length_0_conv length_Cons list.exhaust nat.inject)
  hence a: "a \<in> carrier R" "a \<noteq> \<zero>" and b: "b \<in> carrier R"
    using assms(1) unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  hence inv_a: "inv a \<in> carrier R" "(inv a) \<otimes> a = \<one>"
    using subfield_m_inv[OF carrier_is_subfield, of a] by auto
  hence in_carrier: "[ \<one>, (inv a) \<otimes> b ] \<in> carrier (poly_ring R)"
    using b unfolding sym[OF univ_poly_carrier] polynomial_def by auto

  have "p \<sim>\<^bsub>poly_ring R\<^esub> [ \<one>, (inv a) \<otimes> b ]"
  proof (rule UP.associatedI2'[OF _ _ in_carrier, of _ "[ a ]"])
    have "p = [ a ] \<otimes>\<^bsub>poly_ring R\<^esub> [ \<one>, inv a \<otimes> b ]"
      using a inv_a b m_assoc[of a "inv a" b] unfolding p univ_poly_mult by (auto, algebra)
    also have " ... = [ \<one>, inv a \<otimes> b ] \<otimes>\<^bsub>poly_ring R\<^esub> [ a ]"
      using UP.m_comm[OF in_carrier, of "[ a ]"] a
      by (auto simp add: sym[OF univ_poly_carrier] polynomial_def)
    finally show "p = [ \<one>, inv a \<otimes> b ] \<otimes>\<^bsub>poly_ring R\<^esub> [ a ]" .
  next
    from \<open>a \<in> carrier R\<close> and \<open>a \<noteq> \<zero>\<close> show "[ a ] \<in> Units (poly_ring R)"
      unfolding univ_poly_units[OF carrier_is_subfield] by simp
  qed

  moreover have "(inv a) \<otimes> b = \<ominus> (\<ominus> (inv (lead_coeff p) \<otimes> (const_term p)))"
    and "inv (lead_coeff p) \<otimes> (const_term p) \<in> carrier R"
    using inv_a a b unfolding p const_term_def by auto

  ultimately show ?thesis
    using associated_polynomials_imp_same_is_root[OF assms(1) in_carrier]
          monic_degree_one_root_condition
    by (metis add.inv_closed)
qed

lemma (in domain) is_root_imp_is_root_poly_mult:
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)" and "q \<noteq> []"
  shows "is_root p x \<Longrightarrow> is_root (p \<otimes>\<^bsub>poly_ring R\<^esub> q) x"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  assume "is_root p x" then have x: "x \<in> carrier R" and eval: "eval p x = \<zero>" and not_zero: "p \<noteq> []"
    unfolding is_root_def by simp+
  hence "p \<otimes>\<^bsub>poly_ring R\<^esub> q \<noteq> []"
    using assms UP.integral unfolding sym[OF univ_poly_zero[of R "carrier R"]] by blast
  moreover have "eval (p \<otimes>\<^bsub>poly_ring R\<^esub> q) x = \<zero>"
    using assms eval ring_hom_memE[OF eval_is_hom[OF carrier_is_subring x]] by auto
  ultimately show ?thesis
    using x unfolding is_root_def by simp
qed

lemma (in domain) is_root_poly_mult_imp_is_root:
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)"
  shows "is_root (p \<otimes>\<^bsub>poly_ring R\<^esub> q) x \<Longrightarrow> (is_root p x) \<or> (is_root q x)"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  assume is_root: "is_root (p \<otimes>\<^bsub>poly_ring R\<^esub> q) x"
  hence "p \<noteq> []" and "q \<noteq> []"
    unfolding is_root_def sym[OF univ_poly_zero[of R "carrier R"]]
    using UP.l_null[OF assms(2)] UP.r_null[OF assms(1)] by blast+
  moreover have x: "x \<in> carrier R" and "eval (p \<otimes>\<^bsub>poly_ring R\<^esub> q) x = \<zero>"
    using is_root unfolding is_root_def by simp+
  hence "eval p x = \<zero> \<or> eval q x = \<zero>"
    using ring_hom_memE[OF eval_is_hom[OF carrier_is_subring], of x] assms integral by auto
  ultimately show "(is_root p x) \<or> (is_root q x)"
    using x unfolding is_root_def by auto
qed

(*
lemma (in domain)
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "degree p = 1"
  shows "pprime K p"
proof (rule pprimeI[OF assms(1-2)])
  from \<open>degree p = 1\<close> show "p \<noteq> []" and "p \<notin> Units (K [X])"
    unfolding univ_poly_units[OF assms(1)] by auto
next
  fix q r
  assume "q \<in> carrier (K[X])" and "r \<in> carrier (K[X])"
    and pdiv: "p pdivides q \<otimes>\<^bsub>K [X]\<^esub> r"
  hence "q \<in> carrier (poly_ring R)" and "r \<in> carrier (poly_ring R)"
    using carrier_polynomial_shell[OF subfieldE(1)[OF assms(1)]] by auto
  moreover obtain b where b: "b \<in>"
qed
*)

lemma (in domain) finite_number_of_roots:
  assumes "p \<in> carrier (poly_ring R)" shows "finite { x. is_root p x }"
  using assms
proof (induction "degree p" arbitrary: p)
  case 0 thus ?case
    by (simp add: degree_zero_imp_not_is_root)
next
  case (Suc n) show ?case
  proof (cases "{ x. is_root p x } = {}")
    case True thus ?thesis
      by (simp add: True)
  next
    interpret UP: domain "poly_ring R"
      using univ_poly_is_domain[OF carrier_is_subring] .

    case False
    then obtain a where is_root: "is_root p a"
      by blast
    hence a: "a \<in> carrier R" and eval: "eval p a = \<zero>" and p_not_zero: "p \<noteq> []"
      unfolding is_root_def by auto
    hence in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
      unfolding sym[OF univ_poly_carrier] polynomial_def by auto

    obtain q where q: "q \<in> carrier (poly_ring R)" and p: "p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q"
      using is_root_imp_pdivides[OF Suc(3) is_root] unfolding pdivides_def by auto
    with \<open>p \<noteq> []\<close> have q_not_zero: "q \<noteq> []"
      using UP.r_null UP.integral in_carrier unfolding sym[OF univ_poly_zero[of R "carrier R"]]
      by metis
    hence "degree q = n"
      using poly_mult_degree_eq[OF carrier_is_subring, of "[ \<one>, \<ominus> a ]" q]
            in_carrier q p_not_zero p Suc(2)
      unfolding univ_poly_carrier
      by (metis One_nat_def Suc_eq_plus1 diff_Suc_1 list.distinct(1)
                list.size(3-4) plus_1_eq_Suc univ_poly_mult)
    hence "finite { x. is_root q x }"
      using Suc(1)[OF _ q] by simp

    moreover have "{ x. is_root p x } \<subseteq> insert a { x. is_root q x }"
      using is_root_poly_mult_imp_is_root[OF in_carrier q]
            monic_degree_one_root_condition[OF a]
      unfolding p by auto

    ultimately show ?thesis
      using finite_subset by auto
  qed
qed

lemma (in domain) alg_multE:
  assumes "x \<in> carrier R" and "p \<in> carrier (poly_ring R)" and "p \<noteq> []"
  shows "([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult p x)) pdivides p"
    and "\<And>n. ([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> n) pdivides p \<Longrightarrow> n \<le> alg_mult p x"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  let ?ppow = "\<lambda>n :: nat. ([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> n)"

  define S :: "nat set" where "S = { n. ?ppow n pdivides p }"
  have "?ppow 0 = \<one>\<^bsub>poly_ring R\<^esub>"
    using UP.nat_pow_0 by simp
  hence "0 \<in> S"
    using UP.one_divides[OF assms(2)] unfolding S_def pdivides_def by simp
  hence "S \<noteq> {}"
    by auto

  moreover have "n \<le> degree p" if "n \<in> S" for n :: nat
  proof -
    have "[ \<one>, \<ominus> x ] \<in> carrier (poly_ring R)"
      using assms unfolding sym[OF univ_poly_carrier] polynomial_def by auto
    hence "?ppow n \<in> carrier (poly_ring R)"
      using assms unfolding univ_poly_zero by auto
    with \<open>n \<in> S\<close> have "degree (?ppow n) \<le> degree p"
      using pdivides_imp_degree_le[OF carrier_is_subring _ assms(2-3), of "?ppow n"] by (simp add: S_def)
    with \<open>[ \<one>, \<ominus> x ] \<in> carrier (poly_ring R)\<close> show ?thesis
      using polynomial_pow_degree by simp
  qed
  hence "finite S"
    using finite_nat_set_iff_bounded_le by blast

  ultimately have MaxS: "\<And>n. n \<in> S \<Longrightarrow> n \<le> Max S" "Max S \<in> S"
    using Max_ge[of S] Max_in[of S] by auto
  with \<open>x \<in> carrier R\<close> have "alg_mult p x = Max S"
    using Greatest_equality[of "\<lambda>n. ?ppow n pdivides p" "Max S"] assms(3)
    unfolding S_def alg_mult_def by auto
  thus "([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult p x)) pdivides p"
   and "\<And>n. ([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> n) pdivides p \<Longrightarrow> n \<le> alg_mult p x"
    using MaxS unfolding S_def by auto
qed

lemma (in domain) le_alg_mult_imp_pdivides:
  assumes "x \<in> carrier R" and "p \<in> carrier (poly_ring R)"
  shows "n \<le> alg_mult p x \<Longrightarrow> ([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> n) pdivides p"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  assume le_alg_mult: "n \<le> alg_mult p x"
  have in_carrier: "[ \<one>, \<ominus> x ] \<in> carrier (poly_ring R)"
    using assms(1) unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  hence ppow_pdivides:
    "([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> n) pdivides
     ([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult p x))"
    using polynomial_pow_division[OF _ le_alg_mult] by simp

  show ?thesis
  proof (cases "p = []")
    case True thus ?thesis
      using in_carrier pdivides_zero[OF carrier_is_subring] by auto
  next
    case False thus ?thesis
      using ppow_pdivides UP.divides_trans UP.nat_pow_closed alg_multE(1)[OF assms] in_carrier
      unfolding pdivides_def by meson
  qed
qed

lemma (in domain) alg_mult_gt_zero_iff_is_root:
  assumes "p \<in> carrier (poly_ring R)" shows "alg_mult p x > 0 \<longleftrightarrow> is_root p x"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .
  show ?thesis
  proof
    assume is_root: "is_root p x" hence x: "x \<in> carrier R" and not_zero: "p \<noteq> []"
      unfolding is_root_def by auto
    have "[\<one>, \<ominus> x] [^]\<^bsub>poly_ring R\<^esub> (Suc 0) = [\<one>, \<ominus> x]"
      using x unfolding univ_poly_def by auto
    thus "alg_mult p x > 0"
      using is_root_imp_pdivides[OF _ is_root] alg_multE(2)[OF x, of p "Suc 0"] not_zero assms by auto
  next
    assume gt_zero: "alg_mult p x > 0"
    hence x: "x \<in> carrier R" and not_zero: "p \<noteq> []"
      unfolding alg_mult_def by (cases "p = []", auto, cases "x \<in> carrier R", auto)
    hence in_carrier: "[ \<one>, \<ominus> x ] \<in> carrier (poly_ring R)"
      unfolding sym[OF univ_poly_carrier] polynomial_def by auto
    with \<open>x \<in> carrier R\<close> have "[ \<one>, \<ominus> x ] pdivides p" and "eval [ \<one>, \<ominus> x ] x = \<zero>"
      using le_alg_mult_imp_pdivides[of x p "1::nat"] gt_zero assms by (auto, algebra)
    thus "is_root p x"
      using pdivides_imp_root_sharing[OF in_carrier] not_zero x by (simp add: is_root_def)
  qed
qed

lemma (in domain) alg_mult_in_multiset:
  assumes "p \<in> carrier (poly_ring R)" shows "alg_mult p \<in> multiset"
  using assms alg_mult_gt_zero_iff_is_root finite_number_of_roots unfolding multiset_def by auto

lemma (in domain) alg_mult_eq_count_roots:
  assumes "p \<in> carrier (poly_ring R)" shows "alg_mult p = count (roots p)"
  using alg_mult_in_multiset[OF assms] by (simp add: roots_def)

lemma (in domain) roots_mem_iff_is_root:
  assumes "p \<in> carrier (poly_ring R)" shows "x \<in># roots p \<longleftrightarrow> is_root p x"
  using alg_mult_eq_count_roots[OF assms] count_greater_zero_iff
  unfolding roots_def sym[OF alg_mult_gt_zero_iff_is_root[OF assms]] by metis

lemma (in domain) degree_zero_imp_empty_roots:
  assumes "p \<in> carrier (poly_ring R)" and "degree p = 0" shows "roots p = {#}"
proof -
  have "alg_mult p = (\<lambda>x. 0)"
  proof (cases "p = []")
    case True thus ?thesis
      using assms unfolding alg_mult_def by auto
  next
    case False hence "length p = Suc 0"
      using assms(2) by (simp add: le_Suc_eq)
    then obtain a where "a \<in> carrier R" and "a \<noteq> \<zero>" and p: "p = [ a ]"
      using assms(1) unfolding sym[OF univ_poly_carrier] polynomial_def
      by (metis Suc_length_conv hd_in_set length_0_conv list.sel(1) subset_code(1))
    show ?thesis
    proof (rule ccontr)
      assume "alg_mult p \<noteq> (\<lambda>x. 0)"
      then obtain x where "alg_mult p x > 0"
        by auto
      with \<open>p \<noteq> []\<close> have "eval p x = \<zero>"
        using alg_mult_gt_zero_iff_is_root[OF assms(1), of x] unfolding is_root_def by simp
      with \<open>a \<in> carrier R\<close> have "a = \<zero>"
        unfolding p by auto
      with \<open>a \<noteq> \<zero>\<close> show False ..
    qed
  qed
  thus ?thesis
    by (simp add: roots_def zero_multiset.abs_eq)
qed

lemma (in domain) degree_zero_imp_splitted:
  assumes "p \<in> carrier (poly_ring R)" and "degree p = 0" shows "splitted p"
  unfolding splitted_def degree_zero_imp_empty_roots[OF assms] assms(2) by simp

lemma (in domain) roots_inclI':
  assumes "p \<in> carrier (poly_ring R)" and "\<And>a. \<lbrakk> a \<in> carrier R; p \<noteq> [] \<rbrakk> \<Longrightarrow> alg_mult p a \<le> count m a"
  shows "roots p \<subseteq># m"
proof (intro mset_subset_eqI)
  fix a show "count (roots p) a \<le> count m a"
    using assms unfolding sym[OF alg_mult_eq_count_roots[OF assms(1)]] alg_mult_def
    by (cases "p = []", simp, cases "a \<in> carrier R", auto)
qed

lemma (in domain) roots_inclI:
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)" "q \<noteq> []"
    and "\<And>a. \<lbrakk> a \<in> carrier R; p \<noteq> [] \<rbrakk> \<Longrightarrow> ([ \<one>, \<ominus> a ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult p a)) pdivides q"
  shows "roots p \<subseteq># roots q"
  using roots_inclI'[OF assms(1), of "roots q"] assms alg_multE(2)[OF _ assms(2-3)]
  unfolding sym[OF alg_mult_eq_count_roots[OF assms(2)]] by auto

lemma (in domain) pdivides_imp_roots_incl:
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)" "q \<noteq> []"
  shows "p pdivides q \<Longrightarrow> roots p \<subseteq># roots q"
proof (rule roots_inclI[OF assms])
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  fix a assume "p pdivides q" and a: "a \<in> carrier R"
  hence "[ \<one> , \<ominus> a ] \<in> carrier (poly_ring R)"
    unfolding sym[OF univ_poly_carrier] polynomial_def by simp
  with \<open>p pdivides q\<close> show "([\<one>, \<ominus> a] [^]\<^bsub>poly_ring R\<^esub> (alg_mult p a)) pdivides q"
    using UP.divides_trans[of _p q] le_alg_mult_imp_pdivides[OF a assms(1)]
    by (auto simp add: pdivides_def)
qed

lemma (in domain) associated_polynomials_imp_same_roots:
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)" and "p \<sim>\<^bsub>poly_ring R\<^esub> q"
  shows "roots p = roots q"
  using assms pdivides_imp_roots_incl zero_pdivides
  unfolding pdivides_def associated_def
  by (metis subset_mset.eq_iff)

(* MOVE to Polynomial_Divisibility.thy *)
lemma (in comm_monoid_cancel) prime_pow_divides_iff:
  assumes "p \<in> carrier G" "a \<in> carrier G" "b \<in> carrier G" and "prime G p" and "\<not> (p divides a)"
  shows "(p [^] (n :: nat)) divides (a \<otimes> b) \<longleftrightarrow> (p [^] n) divides b"
proof
  assume "(p [^] n) divides b" thus "(p [^] n) divides (a \<otimes> b)"
    using divides_prod_l[of "p [^] n" b a] assms by simp
next
  assume "(p [^] n) divides (a \<otimes> b)" thus "(p [^] n) divides b"
  proof (induction n)
    case 0 with \<open>b \<in> carrier G\<close> show ?case
      by (simp add: unit_divides)
  next
    case (Suc n)
    hence "(p [^] n) divides (a \<otimes> b)" and "(p [^] n) divides b"
      using assms(1) divides_prod_r by auto
    with \<open>(p [^] (Suc n)) divides (a \<otimes> b)\<close> obtain c d
      where c: "c \<in> carrier G" and "b = (p [^] n) \<otimes> c"
        and d: "d \<in> carrier G" and "a \<otimes> b = (p [^] (Suc n)) \<otimes> d"
      using assms by blast
    hence "(p [^] n) \<otimes> (a \<otimes> c) = (p [^] n) \<otimes> (p \<otimes> d)"
      using assms by (simp add: m_assoc m_lcomm)
    hence "a \<otimes> c = p \<otimes> d"
      using c d assms(1) assms(2) l_cancel by blast
    with \<open>\<not> (p divides a)\<close> and \<open>prime G p\<close> have "p divides c"
      by (metis assms(2) c d dividesI' prime_divides)
    with \<open>b = (p [^] n) \<otimes> c\<close> show ?case
      using assms(1) c by simp
  qed
qed

(* MOVE to Polynomial_Divisibility.thy *)
lemma (in domain) pirreducible_pow_pdivides_iff:
  assumes "subfield K R" "p \<in> carrier (K[X])" "q \<in> carrier (K[X])" "r \<in> carrier (K[X])"
    and "pirreducible K p" and "\<not> (p pdivides q)"
  shows "(p [^]\<^bsub>K[X]\<^esub> (n :: nat)) pdivides (q \<otimes>\<^bsub>K[X]\<^esub> r) \<longleftrightarrow> (p [^]\<^bsub>K[X]\<^esub> n) pdivides r"
proof -
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .
  show ?thesis
  proof (cases "r = []")
    case True with \<open>q \<in> carrier (K[X])\<close> have "q \<otimes>\<^bsub>K[X]\<^esub> r = []" and "r = []"
      unfolding  sym[OF univ_poly_zero[of R K]] by auto
    thus ?thesis
      using pdivides_zero[OF subfieldE(1),of K] assms by auto
  next
    case False then have not_zero: "p \<noteq> []" "q \<noteq> []" "r \<noteq> []" "q \<otimes>\<^bsub>K[X]\<^esub> r \<noteq> []"
      using subfieldE(1) pdivides_zero[OF _ assms(2)] assms(1-2,5-6) pirreducibleE(1)
            UP.integral_iff[OF assms(3-4)] univ_poly_zero[of R K] by auto
    from \<open>p \<noteq> []\<close>
    have ppow: "p [^]\<^bsub>K[X]\<^esub> (n :: nat) \<noteq> []" "p [^]\<^bsub>K[X]\<^esub> (n :: nat) \<in> carrier (K[X])"
      using subring_polynomial_pow_not_zero[OF subfieldE(1)] assms(1-2) by auto
    have not_pdiv: "\<not> (p divides\<^bsub>mult_of (K[X])\<^esub> q)"
      using assms(6) pdivides_iff_shell[OF assms(1-3)] unfolding pdivides_def by auto
    have prime: "prime (mult_of (K[X])) p"
      using assms(5) pprime_iff_pirreducible[OF assms(1-2)]
      unfolding sym[OF UP.prime_eq_prime_mult[OF assms(2)]] ring_prime_def by simp
    have "a pdivides b \<longleftrightarrow> a divides\<^bsub>mult_of (K[X])\<^esub> b"
      if "a \<in> carrier (K[X])" "a \<noteq> \<zero>\<^bsub>K[X]\<^esub>" "b \<in> carrier (K[X])" "b \<noteq> \<zero>\<^bsub>K[X]\<^esub>" for a b
      using that UP.divides_imp_divides_mult[of a b] divides_mult_imp_divides[of "K[X]" a b]
      unfolding pdivides_iff_shell[OF assms(1) that(1,3)] by blast
    thus ?thesis
      using UP.mult_of.prime_pow_divides_iff[OF _ _ _ prime not_pdiv, of r] ppow not_zero assms(2-4)
      unfolding nat_pow_mult_of carrier_mult_of mult_mult_of sym[OF univ_poly_zero[of R K]]
      by (metis DiffI UP.m_closed singletonD)
  qed
qed

(* MOVE to Polynomial_Divisibility.thy *)
lemma (in domain) univ_poly_units':
  assumes "subfield K R" shows "p \<in> Units (K[X]) \<longleftrightarrow> p \<in> carrier (K[X]) \<and> p \<noteq> [] \<and> degree p = 0"
  unfolding univ_poly_units[OF assms] sym[OF univ_poly_carrier] polynomial_def
  by (auto, metis hd_in_set le_0_eq le_Suc_eq length_0_conv length_Suc_conv list.sel(1) subsetD)

(* MOVE to Polynomial_Divisibility.thy *)
lemma (in domain) subring_degree_one_imp_pirreducible:
  assumes "subring K R" and "a \<in> Units (R \<lparr> carrier := K \<rparr>)" and "b \<in> K"
  shows "pirreducible K [ a, b ]"
proof (rule pirreducibleI[OF assms(1)])
  have "a \<in> K" and "a \<noteq> \<zero>"
    using assms(2) subringE(1)[OF assms(1)] unfolding Units_def by auto
  thus "[ a, b ] \<in> carrier (K[X])" and "[ a, b ] \<noteq> []" and "[ a, b ] \<notin> Units (K [X])"
    using univ_poly_units_incl[OF assms(1)] assms(2-3)
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
next
  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] .

  { fix q r
    assume q: "q \<in> carrier (K[X])" and r: "r \<in> carrier (K[X])" and "[ a, b ] = q \<otimes>\<^bsub>K[X]\<^esub> r"
    hence not_zero: "q \<noteq> []" "r \<noteq> []"
      by (metis UP.integral_iff list.distinct(1) univ_poly_zero)+
    have "degree (q \<otimes>\<^bsub>K[X]\<^esub> r) = degree q + degree r"
      using not_zero poly_mult_degree_eq[OF assms(1)] q r
      by (simp add: univ_poly_carrier univ_poly_mult)
    with sym[OF \<open>[ a, b ] = q \<otimes>\<^bsub>K[X]\<^esub> r\<close>] have "degree q + degree r = 1" and "q \<noteq> []" "r \<noteq> []"
      using not_zero by auto
  } note aux_lemma1 = this

  { fix q r
    assume q: "q \<in> carrier (K[X])" "q \<noteq> []" and r: "r \<in> carrier (K[X])" "r \<noteq> []"
      and "[ a, b ] = q \<otimes>\<^bsub>K[X]\<^esub> r" and "degree q = 1" and "degree r = 0"
    hence "length q = Suc (Suc 0)" and "length r = Suc 0"
      by (linarith, metis add.right_neutral add_eq_if length_0_conv)
    from \<open>length q = Suc (Suc 0)\<close> obtain c d where q_def: "q = [ c, d ]"
      by (metis length_0_conv length_Cons list.exhaust nat.inject)
    from \<open>length r = Suc 0\<close> obtain e where r_def: "r = [ e ]"
      by (metis length_0_conv length_Suc_conv)
    from \<open>r = [ e ]\<close> and \<open>q = [ c, d ]\<close>
    have c: "c \<in> K" "c \<noteq> \<zero>" and d: "d \<in> K" and e: "e \<in> K" "e \<noteq> \<zero>"
      using r q subringE(1)[OF assms(1)] unfolding sym[OF univ_poly_carrier] polynomial_def by auto
    with sym[OF \<open>[ a, b ] = q \<otimes>\<^bsub>K[X]\<^esub> r\<close>] have "a = c \<otimes> e"
      using poly_mult_lead_coeff[OF assms(1), of q r]
      unfolding polynomial_def sym[OF univ_poly_mult[of R K]] r_def q_def by auto
    obtain inv_a where a: "a \<in> K" and inv_a: "inv_a \<in> K" "a \<otimes> inv_a = \<one>" "inv_a \<otimes> a = \<one>"
      using assms(2) unfolding Units_def by auto
    hence "a \<noteq> \<zero>" and "inv_a \<noteq> \<zero>"
      using subringE(1)[OF assms(1)] integral_iff by auto
    with \<open>c \<in> K\<close> and \<open>c \<noteq> \<zero>\<close> have in_carrier: "[ c \<otimes> inv_a ] \<in> carrier (K[X])"
      using subringE(1,6)[OF assms(1)] inv_a integral
      unfolding sym[OF univ_poly_carrier] polynomial_def
      by (auto, meson subsetD)
    moreover have "[ c \<otimes> inv_a ] \<otimes>\<^bsub>K[X]\<^esub> r = [ \<one> ]"
      using \<open>a = c \<otimes> e\<close> a inv_a c e subsetD[OF subringE(1)[OF assms(1)]]
      unfolding r_def univ_poly_mult by (auto) (simp add: m_assoc m_lcomm integral_iff)+
    ultimately have "r \<in> Units (K[X])"
      using r(1) UP.m_comm[OF in_carrier r(1)] unfolding sym[OF univ_poly_one[of R K]] Units_def by auto
  } note aux_lemma2 = this

  fix q r
  assume q: "q \<in> carrier (K[X])" and r: "r \<in> carrier (K[X])" and qr: "[ a, b ] = q \<otimes>\<^bsub>K[X]\<^esub> r"
  thus "q \<in> Units (K[X]) \<or> r \<in> Units (K[X])"
    using aux_lemma1[OF q r qr] aux_lemma2[of q r] aux_lemma2[of r q] UP.m_comm add_is_1 by auto
qed

(* MOVE to Polynomial_Divisibility.thy *)
lemma (in domain) degree_one_imp_pirreducible:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "degree p = 1"
  shows "pirreducible K p"
proof -
  from \<open>degree p = 1\<close> have "length p = Suc (Suc 0)"
    by simp
  then obtain a b where p: "p = [ a, b ]"
    by (metis length_0_conv length_Suc_conv)
  with \<open>p \<in> carrier (K[X])\<close> show ?thesis
    using subring_degree_one_imp_pirreducible[OF subfieldE(1)[OF assms(1)], of a b]
          subfield.subfield_Units[OF assms(1)]
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
qed

(* MOVE to Polynomial_Divisibility.thy *)
lemma (in ring) degree_oneE[elim]:
  assumes "p \<in> carrier (K[X])" and "degree p = 1"
    and "\<And>a b. \<lbrakk> a \<in> K; a \<noteq> \<zero>; b \<in> K; p = [ a, b ] \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  from \<open>degree p = 1\<close> have "length p = Suc (Suc 0)"
    by simp
  then obtain a b where "p = [ a, b ]"
    by (metis length_0_conv length_Cons nat.inject neq_Nil_conv)
  with \<open>p \<in> carrier (K[X])\<close> have "a \<in> K" and "a \<noteq> \<zero>" and "b \<in> K"
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  with \<open>p = [ a, b ]\<close> show ?thesis
    using assms(3) by simp
qed

(* MOVE to Polynomial_Divisibility.thy *)
lemma (in domain) subring_degree_one_associatedI:
  assumes "subring K R" and "a \<in> K" "a' \<in> K" and "b \<in> K" and "a \<otimes> a' = \<one>"
  shows "[ a , b ] \<sim>\<^bsub>K[X]\<^esub> [ \<one>, a' \<otimes> b ]"
proof -
  from \<open>a \<otimes> a' = \<one>\<close> have not_zero: "a \<noteq> \<zero>" "a' \<noteq> \<zero>"
    using subringE(1)[OF assms(1)] assms(2-3) by auto
  hence "[ a, b ] = [ a ] \<otimes>\<^bsub>K[X]\<^esub> [ \<one>, a' \<otimes> b ]"
    using assms(2-4)[THEN subsetD[OF subringE(1)[OF assms(1)]]] assms(5) m_assoc
    unfolding univ_poly_mult by fastforce
  moreover have "[ a, b ] \<in> carrier (K[X])" and "[ \<one>, a' \<otimes> b ] \<in> carrier (K[X])"
    using subringE(1,3,6)[OF assms(1)] not_zero one_not_zero assms
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  moreover have "[ a ] \<in> Units (K[X])"
  proof -
    from \<open>a \<noteq> \<zero>\<close> and \<open>a' \<noteq> \<zero>\<close> have "[ a ] \<in> carrier (K[X])" and "[ a' ] \<in> carrier (K[X])"
      using assms(2-3) unfolding sym[OF univ_poly_carrier] polynomial_def by auto
    moreover have "a' \<otimes> a = \<one>"
      using subsetD[OF subringE(1)[OF assms(1)]] assms m_comm by simp
    hence "[ a ] \<otimes>\<^bsub>K[X]\<^esub> [ a' ] = [ \<one> ]" and "[ a' ] \<otimes>\<^bsub>K[X]\<^esub> [ a ] = [ \<one> ]"
      using assms unfolding univ_poly_mult by auto
    ultimately show ?thesis
      unfolding sym[OF univ_poly_one[of R K]] Units_def by blast
  qed
  ultimately show ?thesis
    using domain.ring_associated_iff[OF univ_poly_is_domain[OF assms(1)]] by blast
qed

(* MOVE to Polynomial_Divisibility.thy *)
lemma (in domain) degree_one_associatedI:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "degree p = 1"
  shows "p \<sim>\<^bsub>K[X]\<^esub> [ \<one>, inv (lead_coeff p) \<otimes> (const_term p) ]"
proof -
  from \<open>p \<in> carrier (K[X])\<close> and \<open>degree p = 1\<close>
  obtain a b where "p = [ a, b ]" and "a \<in> K" "a \<noteq> \<zero>" and "b \<in> K"
    by auto
  thus ?thesis
    using subring_degree_one_associatedI[OF subfieldE(1)[OF assms(1)]]
          subfield_m_inv[OF assms(1)] subsetD[OF subfieldE(3)[OF assms(1)]]
    unfolding const_term_def
    by auto
qed

lemma (in domain) monic_degree_one_roots:
  assumes "a \<in> carrier R" shows "roots [ \<one> , \<ominus> a ] = {# a #}"
proof -
  let ?p = "[ \<one> , \<ominus> a ]"

  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  from \<open>a \<in> carrier R\<close> have in_carrier: "?p \<in> carrier (poly_ring R)"
    unfolding sym[OF univ_poly_carrier] polynomial_def by simp
  show ?thesis
  proof (rule subset_mset.antisym)
    show "{# a #} \<subseteq># roots ?p"
      using roots_mem_iff_is_root[OF in_carrier]
            monic_degree_one_root_condition[OF assms]
      by simp
  next
    show "roots ?p \<subseteq># {# a #}"
    proof (rule mset_subset_eqI, auto)
      fix b assume "a \<noteq> b" thus "count (roots ?p) b = 0"
        using alg_mult_gt_zero_iff_is_root[OF in_carrier]
              monic_degree_one_root_condition[OF assms]
        unfolding sym[OF alg_mult_eq_count_roots[OF in_carrier]]
        by fastforce
    next
      have "(?p [^]\<^bsub>poly_ring R\<^esub> (alg_mult ?p a)) pdivides ?p"
        using le_alg_mult_imp_pdivides[OF assms in_carrier] by simp
      hence "degree (?p [^]\<^bsub>poly_ring R\<^esub> (alg_mult ?p a)) \<le> degree ?p"
        using pdivides_imp_degree_le[OF carrier_is_subring, of _ ?p] in_carrier by auto
      thus "count (roots ?p) a \<le> Suc 0"
        using polynomial_pow_degree[OF in_carrier]
        unfolding sym[OF alg_mult_eq_count_roots[OF in_carrier]]
        by auto
    qed
  qed
qed

lemma (in domain) degree_one_roots:
  assumes "a \<in> carrier R" "a' \<in> carrier R" and "b \<in> carrier R" and "a \<otimes> a' = \<one>"
  shows "roots [ a , b ] = {# \<ominus> (a' \<otimes> b) #}"
proof -
  have "[ a, b ] \<in> carrier (poly_ring R)" and "[ \<one>, a' \<otimes> b ] \<in> carrier (poly_ring R)"
    using assms unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  thus ?thesis
    using subring_degree_one_associatedI[OF carrier_is_subring assms] assms
          monic_degree_one_roots associated_polynomials_imp_same_roots
    by (metis add.inv_closed local.minus_minus m_closed)
qed

lemma (in field) degree_one_imp_singleton_roots:
  assumes "p \<in> carrier (poly_ring R)" and "degree p = 1"
  shows "roots p = {# \<ominus> (inv (lead_coeff p) \<otimes> (const_term p)) #}"
proof -
  from \<open>p \<in> carrier (poly_ring R)\<close> and \<open>degree p = 1\<close>
  obtain a b where "p = [ a, b ]" and "a \<in> carrier R" "a \<noteq> \<zero>" and "b \<in> carrier R"
    by auto
  thus ?thesis
    using degree_one_roots[of a "inv a" b]
    by (auto simp add: const_term_def field_Units)
qed

lemma (in field) degree_one_imp_splitted:
  assumes "p \<in> carrier (poly_ring R)" and "degree p = 1" shows "splitted p"
  using degree_one_imp_singleton_roots[OF assms] assms(2) unfolding splitted_def by simp

lemma (in field) no_roots_imp_same_roots:
  assumes "p \<in> carrier (poly_ring R)" "p \<noteq> []" and "q \<in> carrier (poly_ring R)"
  shows "roots p = {#} \<Longrightarrow> roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q) = roots q"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  assume no_roots: "roots p = {#}" show "roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q) = roots q"
  proof (intro subset_mset.antisym)
    have pdiv: "q pdivides (p \<otimes>\<^bsub>poly_ring R\<^esub> q)"
      using UP.divides_prod_l assms unfolding pdivides_def by blast
    show "roots q \<subseteq># roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q)"
      using pdivides_imp_roots_incl[OF _ _ _ pdiv] assms
            degree_zero_imp_empty_roots[OF assms(3)]
      by (cases "q = []", auto, metis UP.l_null UP.m_rcancel UP.zero_closed univ_poly_zero)
  next
    show "roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q) \<subseteq># roots q"
    proof (cases "p \<otimes>\<^bsub>poly_ring R\<^esub> q = []")
      case True thus ?thesis
        using degree_zero_imp_empty_roots[OF UP.m_closed[OF assms(1,3)]] by simp
    next
      case False with \<open>p \<noteq> []\<close> have q_not_zero: "q \<noteq> []"
        by (metis UP.r_null assms(1) univ_poly_zero)
      show ?thesis
      proof (rule roots_inclI[OF UP.m_closed[OF assms(1,3)] assms(3) q_not_zero])
        fix a assume a: "a \<in> carrier R"
        hence "\<not> ([ \<one>, \<ominus> a ] pdivides p)"
          using assms(1-2) no_roots pdivides_imp_is_root roots_mem_iff_is_root[of p] by auto
        moreover have in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
          using a unfolding sym[OF univ_poly_carrier] polynomial_def by auto
        hence "pirreducible (carrier R) [ \<one>, \<ominus> a ]"
          using degree_one_imp_pirreducible[OF carrier_is_subfield] by simp
        moreover
        have "([ \<one>, \<ominus> a ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult (p \<otimes>\<^bsub>poly_ring R\<^esub> q) a)) pdivides (p \<otimes>\<^bsub>poly_ring R\<^esub> q)"
          using le_alg_mult_imp_pdivides[OF a UP.m_closed, of p q] assms by simp
        ultimately show "([ \<one>, \<ominus> a ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult (p \<otimes>\<^bsub>poly_ring R\<^esub> q) a)) pdivides q"
          using pirreducible_pow_pdivides_iff[OF carrier_is_subfield in_carrier] assms by auto
      qed
    qed
  qed
qed

lemma (in field) poly_mult_degree_one_monic_imp_same_roots:
  assumes "a \<in> carrier R" and "p \<in> carrier (poly_ring R)" "p \<noteq> []"
  shows "roots ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p) = add_mset a (roots p)"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  from \<open>a \<in> carrier R\<close> have in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
    unfolding sym[OF univ_poly_carrier] polynomial_def by simp

  show ?thesis
  proof (intro subset_mset.antisym[OF roots_inclI' mset_subset_eqI])
    show "([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p) \<in> carrier (poly_ring R)"
      using in_carrier assms(2) by simp
  next
    fix b assume b: "b \<in> carrier R" and "[ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p \<noteq> []"
    hence not_zero: "p \<noteq> []"
      unfolding univ_poly_def by auto
    from \<open>b \<in> carrier R\<close> have in_carrier':  "[ \<one>, \<ominus> b ] \<in> carrier (poly_ring R)"
      unfolding sym[OF univ_poly_carrier] polynomial_def by simp
    show "alg_mult ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p) b \<le> count (add_mset a (roots p)) b"
    proof (cases "a = b")
      case False
      hence "\<not> [ \<one>, \<ominus> b ] pdivides [ \<one>, \<ominus> a ]"
        using assms(1) b monic_degree_one_root_condition pdivides_imp_is_root by blast
      moreover have "pirreducible (carrier R) [ \<one>, \<ominus> b ]"
        using degree_one_imp_pirreducible[OF carrier_is_subfield in_carrier'] by simp
      ultimately
      have "[ \<one>, \<ominus> b ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p) b) pdivides p"
        using le_alg_mult_imp_pdivides[OF b UP.m_closed, of _ p] assms(2) in_carrier
              pirreducible_pow_pdivides_iff[OF carrier_is_subfield in_carrier' in_carrier, of p]
        by auto
      with \<open>a \<noteq> b\<close> show ?thesis
        using alg_mult_eq_count_roots[OF assms(2)] alg_multE(2)[OF b assms(2) not_zero] by auto
    next
      case True
      have "[ \<one>, \<ominus> a ] pdivides ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p)"
        using dividesI[OF assms(2)] unfolding pdivides_def by auto
      with \<open>[ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p \<noteq> []\<close>
      have "alg_mult ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p) a \<ge> Suc 0"
        using alg_multE(2)[of a _ "Suc 0"] in_carrier assms by auto
      then obtain m where m: "alg_mult ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p) a = Suc m"
        using Suc_le_D by blast
      hence "([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> ([ \<one>, \<ominus> a ] [^]\<^bsub>poly_ring R\<^esub> m)) pdivides
             ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p)"
        using le_alg_mult_imp_pdivides[OF _ UP.m_closed, of a _ p]
              in_carrier assms UP.nat_pow_Suc2 by force
      hence "([ \<one>, \<ominus> a ] [^]\<^bsub>poly_ring R\<^esub> m) pdivides p"
        using UP.mult_divides in_carrier assms(2)
        unfolding univ_poly_zero pdivides_def factor_def
        by (simp add: UP.m_assoc UP.m_lcancel univ_poly_zero)
      with \<open>a = b\<close> show ?thesis
        using alg_mult_eq_count_roots assms in_carrier UP.nat_pow_Suc2
              alg_multE(2)[OF assms(1) _ not_zero] m
        by auto
    qed
  next
    fix b
    have not_zero: "[ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p \<noteq> []"
      using assms in_carrier univ_poly_zero[of R] UP.integral by auto

    show "count (add_mset a (roots p)) b \<le> count (roots ([\<one>, \<ominus> a] \<otimes>\<^bsub>poly_ring R\<^esub> p)) b"
    proof (cases "a = b")
      case True
      have "([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> ([ \<one>, \<ominus> a ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult p a))) pdivides
            ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p)"
        using UP.divides_mult[OF _ in_carrier] le_alg_mult_imp_pdivides[OF assms(1,2)] in_carrier assms
        by (auto simp add: pdivides_def)
      with \<open>a = b\<close> show ?thesis
        using alg_mult_eq_count_roots assms in_carrier UP.nat_pow_Suc2
              alg_multE(2)[OF assms(1) _ not_zero]
        by auto
    next
      case False
      have "p pdivides ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p)"
        using dividesI[OF in_carrier] UP.m_comm in_carrier assms unfolding pdivides_def by auto
      thus ?thesis
        using False pdivides_imp_roots_incl assms in_carrier not_zero
        by (simp add: subseteq_mset_def)
    qed
  qed
qed

lemma (in domain) not_empty_rootsE[elim]:
  assumes "p \<in> carrier (poly_ring R)" and "roots p \<noteq> {#}"
    and "\<And>a. \<lbrakk> a \<in> carrier R; a \<in># roots p;
               [ \<one>, \<ominus> a ] \<in> carrier (poly_ring R); [ \<one>, \<ominus> a ] pdivides p \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  from \<open>roots p \<noteq> {#}\<close> obtain a where "a \<in># roots p"
    by blast
  with \<open>p \<in> carrier (poly_ring R)\<close> have "[ \<one>, \<ominus> a ] pdivides p"
    and "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)" and "a \<in> carrier R"
    using is_root_imp_pdivides[of p] roots_mem_iff_is_root[of p] is_root_def[of p a]
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  with \<open>a \<in># roots p\<close> show ?thesis
    using assms(3)[of a] by auto
qed

(* REPLACE th following lemmas on Divisibility.thy ============= *)
(* the only difference is the locale                             *)
lemma (in monoid) mult_cong_r:
  assumes "b \<sim> b'" "a \<in> carrier G"  "b \<in> carrier G"  "b' \<in> carrier G"
  shows "a \<otimes> b \<sim> a \<otimes> b'"
  by (meson assms associated_def divides_mult_lI)

lemma (in comm_monoid) mult_cong_l:
  assumes "a \<sim> a'" "a \<in> carrier G"  "a' \<in> carrier G"  "b \<in> carrier G"
  shows "a \<otimes> b \<sim> a' \<otimes> b"
  using assms m_comm mult_cong_r by auto
(* ============================================================= *)

lemma (in field) associated_polynomials_imp_same_roots:
  assumes "p \<in> carrier (poly_ring R)" "p \<noteq> []" and "q \<in> carrier (poly_ring R)" "q \<noteq> []"
  shows "roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q) = roots p + roots q"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .
  from assms show ?thesis
  proof (induction "degree p" arbitrary: p rule: less_induct)
    case less show ?case
    proof (cases "roots p = {#}")
      case True thus ?thesis
        using no_roots_imp_same_roots[of p q] less by simp
    next
      case False with \<open>p \<in> carrier (poly_ring R)\<close>
      obtain a where a: "a \<in> carrier R" and "a \<in># roots p" and pdiv: "[ \<one>, \<ominus> a ] pdivides p"
          and in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
        by blast
      show ?thesis
      proof (cases "degree p = 1")
        case True with \<open>p \<in> carrier (poly_ring R)\<close>
        obtain b c where p: "p = [ b, c ]" and b: "b \<in> carrier R" "b \<noteq> \<zero>" and c: "c \<in> carrier R"
          by auto
        with \<open>a \<in># roots p\<close> have roots: "roots p = {# a #}" and a: "\<ominus> a = inv b \<otimes> c" "a \<in> carrier R"
          and lead: "lead_coeff p = b" and const: "const_term p = c"
          using degree_one_imp_singleton_roots[of p] less(2) field_Units
          unfolding const_term_def by auto
        hence "(p \<otimes>\<^bsub>poly_ring R\<^esub> q) \<sim>\<^bsub>poly_ring R\<^esub> ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q)"
          using UP.mult_cong_l[OF degree_one_associatedI[OF carrier_is_subfield _ True]] less(2,4)
          by (auto simp add: a lead const)
        hence "roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q) = roots ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q)"
          using associated_polynomials_imp_same_roots in_carrier less(2,4) unfolding a by simp
        thus ?thesis
          unfolding poly_mult_degree_one_monic_imp_same_roots[OF a(2) less(4,5)] roots by simp
      next
        case False
        from \<open>[ \<one>, \<ominus> a ] pdivides p\<close>
        obtain r where p: "p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> r" and r: "r \<in> carrier (poly_ring R)"
          unfolding pdivides_def by auto
        with \<open>p \<noteq> []\<close> have not_zero: "r \<noteq> []"
          using in_carrier univ_poly_zero[of R "carrier R"] UP.integral_iff by auto
        with \<open>p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> r\<close> have deg: "degree p = Suc (degree r)"
          using poly_mult_degree_eq[OF carrier_is_subring, of _ r] in_carrier r
          unfolding univ_poly_carrier sym[OF univ_poly_mult[of R "carrier R"]] by auto
        with \<open>r \<noteq> []\<close> and \<open>q \<noteq> []\<close> have "r \<otimes>\<^bsub>poly_ring R\<^esub> q \<noteq> []"
          using in_carrier univ_poly_zero[of R "carrier R"] UP.integral less(4) r by auto
        hence "roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q) = add_mset a (roots (r \<otimes>\<^bsub>poly_ring R\<^esub> q))"
          using poly_mult_degree_one_monic_imp_same_roots[OF a UP.m_closed[OF r less(4)]]
                UP.m_assoc[OF in_carrier r less(4)] p by auto
        also have " ... = add_mset a (roots r + roots q)"
          using less(1)[OF _ r not_zero less(4-5)] deg by simp
        also have " ... = (add_mset a (roots r)) + roots q"
          by simp
        also have " ... = roots p + roots q"
          using poly_mult_degree_one_monic_imp_same_roots[OF a r not_zero] p by simp
        finally show ?thesis .
      qed
    qed
  qed
qed

lemma (in field) size_roots_le_degree:
  assumes "p \<in> carrier (poly_ring R)" shows "size (roots p) \<le> degree p"
  using assms
proof (induction "degree p" arbitrary: p rule: less_induct)
  case less show ?case
  proof (cases "roots p = {#}", simp)
    interpret UP: domain "poly_ring R"
      using univ_poly_is_domain[OF carrier_is_subring] .

    case False with \<open>p \<in> carrier (poly_ring R)\<close>
    obtain a where a: "a \<in> carrier R" and "a \<in># roots p" and "[ \<one>, \<ominus> a ] pdivides p"
      and in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
      by blast
    then obtain q where p: "p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q" and q: "q \<in> carrier (poly_ring R)"
      unfolding pdivides_def by auto
    with \<open>a \<in># roots p\<close> have "p \<noteq> []"
      using degree_zero_imp_empty_roots[OF less(2)] by auto
    hence not_zero: "q \<noteq> []"
      using in_carrier univ_poly_zero[of R "carrier R"] UP.integral_iff p by auto
    hence "degree p = Suc (degree q)"
      using poly_mult_degree_eq[OF carrier_is_subring, of _ q] in_carrier p q
      unfolding univ_poly_carrier sym[OF univ_poly_mult[of R "carrier R"]] by auto
    with \<open>q \<noteq> []\<close> show ?thesis
      using poly_mult_degree_one_monic_imp_same_roots[OF a q] p less(1)[OF _ q]
      by (metis Suc_le_mono lessI size_add_mset)
  qed
qed

(* MOVE to Divisibility.thy ======== *)
lemma divides_irreducible_condition:
  assumes "irreducible G r" and "a \<in> carrier G"
  shows "a divides\<^bsub>G\<^esub> r \<Longrightarrow> a \<in> Units G \<or> a \<sim>\<^bsub>G\<^esub> r"
  using assms unfolding irreducible_def properfactor_def associated_def
  by (cases "r divides\<^bsub>G\<^esub> a", auto)

(* MOVE to Polynomial_Divisibility.thy ======== *)
lemma (in ring) divides_pirreducible_condition:
  assumes "pirreducible K q" and "p \<in> carrier (K[X])"
  shows "p divides\<^bsub>K[X]\<^esub> q \<Longrightarrow> p \<in> Units (K[X]) \<or> p \<sim>\<^bsub>K[X]\<^esub> q"
  using divides_irreducible_condition[of "K[X]" q p] assms
  unfolding ring_irreducible_def by auto

lemma (in domain) pirreducible_roots:
  assumes "p \<in> carrier (poly_ring R)" and "pirreducible (carrier R) p" and "degree p \<noteq> 1"
  shows "roots p = {#}"
proof (rule ccontr)
  assume "roots p \<noteq> {#}" with \<open>p \<in> carrier (poly_ring R)\<close>
  obtain a where a: "a \<in> carrier R" and "a \<in># roots p" and "[ \<one>, \<ominus> a ] pdivides p"
    and in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
    by blast
  hence "[ \<one>, \<ominus> a ] \<sim>\<^bsub>poly_ring R\<^esub> p"
    using divides_pirreducible_condition[OF assms(2) in_carrier]
          univ_poly_units_incl[OF carrier_is_subring]
    unfolding pdivides_def by auto
  hence "degree p = 1"
    using associated_polynomials_imp_same_length[OF carrier_is_subring in_carrier assms(1)] by auto
  with \<open>degree p \<noteq> 1\<close> show False ..
qed

lemma (in field) pirreducible_imp_not_splitted:
  assumes "p \<in> carrier (poly_ring R)" and "pirreducible (carrier R) p" and "degree p \<noteq> 1"
  shows "\<not> splitted p"
  using pirreducible_roots[of p] pirreducible_degree[OF carrier_is_subfield, of p] assms
  by (simp add: splitted_def)

lemma (in field)
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)"
    and "pirreducible (carrier R) p" and "degree p \<noteq> 1"
  shows "roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q) = roots q"
  using no_roots_imp_same_roots[of p q] pirreducible_roots[of p] assms
  unfolding ring_irreducible_def univ_poly_zero by auto

lemma (in field) trivial_factors_imp_splitted:
  assumes "p \<in> carrier (poly_ring R)"
    and "\<And>q. \<lbrakk> q \<in> carrier (poly_ring R); pirreducible (carrier R) q; q pdivides p \<rbrakk> \<Longrightarrow> degree q \<le> 1"
  shows "splitted p"
  using assms
proof (induction "degree p" arbitrary: p rule: less_induct)
  interpret UP: principal_domain "poly_ring R"
    using univ_poly_is_principal[OF carrier_is_subfield] .
  case less show ?case
  proof (cases "degree p = 0", simp add: degree_zero_imp_splitted[OF less(2)])
    case False show ?thesis
    proof (cases "roots p = {#}")
      case True
      from \<open>degree p \<noteq> 0\<close> have "p \<notin> Units (poly_ring R)" and "p \<in> carrier (poly_ring R) - { [] }"
        using univ_poly_units'[OF carrier_is_subfield, of p] less(2) by auto
      then obtain q where "q \<in> carrier (poly_ring R)" "pirreducible (carrier R) q" and "q pdivides p"
        using UP.exists_irreducible_divisor[of p] unfolding univ_poly_zero pdivides_def by auto
      with \<open>degree p \<noteq> 0\<close> have "roots p \<noteq> {#}"
        using degree_one_imp_singleton_roots[OF _ , of q] less(3)[of q]
              pdivides_imp_roots_incl[OF _ less(2), of q]
              pirreducible_degree[OF carrier_is_subfield, of q]
        by force
      from \<open>roots p = {#}\<close> and \<open>roots p \<noteq> {#}\<close> have False
        by simp
      thus ?thesis ..
    next
      case False with \<open>p \<in> carrier (poly_ring R)\<close>
      obtain a where a: "a \<in> carrier R" and "a \<in># roots p" and "[ \<one>, \<ominus> a ] pdivides p"
        and in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
        by blast
      then obtain q where p: "p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q" and q: "q \<in> carrier (poly_ring R)"
        unfolding pdivides_def by blast
      with \<open>degree p \<noteq> 0\<close> have "p \<noteq> []"
        by auto
      with \<open>p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q\<close> have "q \<noteq> []"
        using in_carrier q unfolding sym[OF univ_poly_zero[of R "carrier R"]] by auto
      with \<open>p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q\<close> and \<open>p \<noteq> []\<close> have "degree p = Suc (degree q)"
        using poly_mult_degree_eq[OF carrier_is_subring] in_carrier q
        unfolding univ_poly_carrier sym[OF univ_poly_mult[of R "carrier R"]] by auto
      moreover have "q pdivides p"
        using p dividesI[OF in_carrier] UP.m_comm[OF in_carrier q] by (auto simp add: pdivides_def)
      hence "degree r = 1" if "r \<in> carrier (poly_ring R)" and "pirreducible (carrier R) r"
        and "r pdivides q" for r
        using less(3)[OF that(1-2)] UP.divides_trans[OF _ _ that(1), of q p] that(3)
              pirreducible_degree[OF carrier_is_subfield that(1-2)]
        by (auto simp add: pdivides_def)
      ultimately have "splitted q"
        using less(1)[OF _ q] by auto
      with \<open>degree p = Suc (degree q)\<close> and \<open>q \<noteq> []\<close> show ?thesis
        using poly_mult_degree_one_monic_imp_same_roots[OF a q]
        unfolding sym[OF p] splitted_def
        by simp
    qed
  qed
qed

lemma (in field) pdivides_imp_splitted:
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)" "q \<noteq> []" and "splitted q"
  shows "p pdivides q \<Longrightarrow> splitted p"
proof (cases "p = []")
  case True thus ?thesis
    using degree_zero_imp_splitted[OF assms(1)] by simp
next
  interpret UP: principal_domain "poly_ring R"
    using univ_poly_is_principal[OF carrier_is_subfield] .

  case False
  assume "p pdivides q"
  then obtain b where b: "b \<in> carrier (poly_ring R)" and q: "q = p \<otimes>\<^bsub>poly_ring R\<^esub> b"
    unfolding pdivides_def by auto
  with \<open>q \<noteq> []\<close> have "p \<noteq> []" and "b \<noteq> []"
    using assms UP.integral_iff[of p b] unfolding sym[OF univ_poly_zero[of R "carrier R"]] by auto
  hence "degree p + degree b = size (roots p) + size (roots b)"
    using associated_polynomials_imp_same_roots[of p b] assms b q splitted_def
          poly_mult_degree_eq[OF carrier_is_subring,of p b]
    unfolding univ_poly_carrier sym[OF univ_poly_mult[of R "carrier R"]]
    by auto
  moreover have "size (roots p) \<le> degree p" and "size (roots b) \<le> degree b"
    using size_roots_le_degree assms(1) b by auto
  ultimately show ?thesis
    unfolding splitted_def by linarith
qed

lemma (in field) splitted_imp_trivial_factors:
  assumes "p \<in> carrier (poly_ring R)" "p \<noteq> []" and "splitted p"
  shows "\<And>q. \<lbrakk> q \<in> carrier (poly_ring R); pirreducible (carrier R) q; q pdivides p \<rbrakk> \<Longrightarrow> degree q = 1"
  using pdivides_imp_splitted[OF _ assms] pirreducible_imp_not_splitted
  by auto

lemma (in field) exists_root:
  assumes "M \<in> extensions" and "\<And>L. \<lbrakk> L \<in> extensions; M \<lesssim> L \<rbrakk> \<Longrightarrow> law_restrict L = law_restrict M"
    and "P \<in> carrier (poly_ring R)"
  shows "(ring.splitted M) (\<sigma> P)"
proof (rule ccontr)
  from \<open>M \<in> extensions\<close> interpret M: field M + Hom: ring_hom_ring R M "indexed_const"
    using ring_hom_ringI2[OF ring_axioms field.is_ring] unfolding extensions_def by auto
  interpret UP: principal_domain "poly_ring M"
    using M.univ_poly_is_principal[OF M.carrier_is_subfield] .

  assume not_splitted: "\<not> (ring.splitted M) (\<sigma> P)"
  have "(\<sigma> P) \<in> carrier (poly_ring M)"
    using polynomial_hom[OF Hom.homh field_axioms M.field_axioms assms(3)] unfolding \<sigma>_def by simp
  then obtain Q
    where Q: "Q \<in> carrier (poly_ring M)" "pirreducible\<^bsub>M\<^esub> (carrier M) Q" "Q pdivides\<^bsub>M\<^esub> (\<sigma> P)"
      and degree_gt: "degree Q > 1"
    using M.trivial_factors_imp_splitted[of "\<sigma> P"] not_splitted by force

  from \<open>(\<sigma> P) \<in> carrier (poly_ring M)\<close> have "(\<sigma> P) \<noteq> []"
    using M.degree_zero_imp_splitted[of "\<sigma> P"] not_splitted unfolding \<sigma>_def by auto

  have "\<exists>i. \<forall>\<P> \<in> carrier M. index_free \<P> (P, i)"
  proof (rule ccontr)
    assume "\<nexists>i. \<forall>\<P> \<in> carrier M. index_free \<P> (P, i)"
    then have "\<X>\<^bsub>(P, i)\<^esub> \<in> carrier M" and "(ring.eval M) (\<sigma> P) \<X>\<^bsub>(P, i)\<^esub> = \<zero>\<^bsub>M\<^esub>" for i
      using assms(1,3) unfolding extensions_def by blast+
    with \<open>(\<sigma> P) \<noteq> []\<close> have "((\<lambda>i :: nat. \<X>\<^bsub>(P, i)\<^esub>) ` UNIV) \<subseteq> { a. (ring.is_root M) (\<sigma> P) a }"
      unfolding M.is_root_def by auto
    moreover have "inj (\<lambda>i :: nat. \<X>\<^bsub>(P, i)\<^esub>)"
      unfolding indexed_var_def indexed_const_def indexed_pmult_def inj_def
      by (metis (no_types, lifting) add_mset_eq_singleton_iff diff_single_eq_union
                                    multi_member_last prod.inject zero_not_one)
    hence "infinite ((\<lambda>i :: nat. \<X>\<^bsub>(P, i)\<^esub>) ` UNIV)"
      unfolding infinite_iff_countable_subset by auto
    ultimately have "infinite { a. (ring.is_root M) (\<sigma> P) a }"
      using finite_subset by auto
    with \<open>(\<sigma> P) \<in> carrier (poly_ring M)\<close> show False
      using M.finite_number_of_roots by simp
  qed
  then obtain i :: nat where "\<forall>\<P> \<in> carrier M. index_free \<P> (P, i)"
    by blast

  then have hyps:
    \<comment> \<open>i\<close>   "field M"
    \<comment> \<open>ii\<close>  "\<And>\<P>. \<P> \<in> carrier M \<Longrightarrow> carrier_coeff \<P>"
    \<comment> \<open>iii\<close> "\<And>\<P>. \<P> \<in> carrier M \<Longrightarrow> index_free \<P> (P, i)"
    \<comment> \<open>iv\<close>  "\<zero>\<^bsub>M\<^esub> = indexed_const \<zero>"
    using assms(1,3) unfolding extensions_def by auto

  define image_poly where "image_poly = image_ring (eval_pmod M (P, i) Q) (poly_ring M)"
  with \<open>degree Q > 1\<close> have "M \<lesssim> image_poly"
    using image_poly_iso_incl[OF hyps Q(1)] by auto
  moreover have is_field: "field image_poly"
    using image_poly_is_field[OF hyps Q(1-2)] unfolding image_poly_def by simp
  moreover have "image_poly \<in> extensions"
  proof (auto simp add: extensions_def is_field)
    fix \<P> assume "\<P> \<in> carrier image_poly"
    then obtain R where \<P>: "\<P> = eval_pmod M (P, i) Q R" and "R \<in> carrier (poly_ring M)"
      unfolding image_poly_def image_ring_carrier by auto
    hence "M.pmod R Q \<in> carrier (poly_ring M)"
      using M.long_division_closed(2)[OF M.carrier_is_subfield _ Q(1)] by simp
    hence "list_all carrier_coeff (M.pmod R Q)"
      using hyps(2) unfolding sym[OF univ_poly_carrier] list_all_iff polynomial_def by auto
    thus "carrier_coeff \<P>"
      using indexed_eval_in_carrier[of "M.pmod R Q"] unfolding \<P> by simp
  next
    from \<open>M \<lesssim> image_poly\<close> show "indexed_const \<in> ring_hom R image_poly"
      using ring_hom_trans[OF Hom.homh, of id] unfolding iso_incl.simps by simp
  next
    from \<open>M \<lesssim> image_poly\<close> interpret Id: ring_hom_ring M image_poly id
      using iso_inclE[OF M.ring_axioms field.is_ring[OF is_field]] by simp

    fix \<P> S j
    assume A: "\<P> \<in> carrier image_poly" "\<not> index_free \<P> (S, j)" "S \<in> carrier (poly_ring R)"
    have "\<X>\<^bsub>(S, j)\<^esub> \<in> carrier image_poly \<and> Id.eval (\<sigma> S) \<X>\<^bsub>(S, j)\<^esub> = \<zero>\<^bsub>image_poly\<^esub>"
    proof (cases)
      assume "(P, i) \<noteq> (S, j)"
      then obtain Q' where "Q' \<in> carrier M" and "\<not> index_free Q' (S, j)"
        using A(1) image_poly_index_free[OF hyps Q(1) _ A(2)] unfolding image_poly_def by auto
      hence "\<X>\<^bsub>(S, j)\<^esub> \<in> carrier M" and "M.eval (\<sigma> S) \<X>\<^bsub>(S, j)\<^esub> = \<zero>\<^bsub>M\<^esub>"
        using assms(1) A(3) unfolding extensions_def by auto
      moreover have "\<sigma> S \<in> carrier (poly_ring M)"
        using polynomial_hom[OF Hom.homh field_axioms M.field_axioms A(3)] unfolding \<sigma>_def .
      ultimately show ?thesis
        using Id.eval_hom[OF M.carrier_is_subring] Id.hom_closed Id.hom_zero by auto
    next
      assume "\<not> (P, i) \<noteq> (S, j)" hence S: "(P, i) = (S, j)"
        by simp
      have poly_hom: "R \<in> carrier (poly_ring image_poly)" if "R \<in> carrier (poly_ring M)" for R
        using polynomial_hom[OF Id.homh M.field_axioms is_field that] by simp
      have "\<X>\<^bsub>(S, j)\<^esub> \<in> carrier image_poly"
        using eval_pmod_var(2)[OF hyps Hom.homh Q(1) degree_gt] unfolding image_poly_def S by simp
      moreover have "Id.eval Q \<X>\<^bsub>(S, j)\<^esub> = \<zero>\<^bsub>image_poly\<^esub>"
        using image_poly_eval_indexed_var[OF hyps Hom.homh Q(1) degree_gt Q(2)] unfolding image_poly_def S by simp
      moreover have "Q pdivides\<^bsub>image_poly\<^esub> (\<sigma> S)"
      proof -
        obtain R where R: "R \<in> carrier (poly_ring M)" "\<sigma> S = Q \<otimes>\<^bsub>poly_ring M\<^esub> R"
          using Q(3) S unfolding pdivides_def by auto
        moreover have "set Q \<subseteq> carrier M" and "set R \<subseteq> carrier M"
          using Q(1) R(1) unfolding sym[OF univ_poly_carrier] polynomial_def by auto
        ultimately have "Id.normalize (\<sigma> S) = Q \<otimes>\<^bsub>poly_ring image_poly\<^esub> R"
          using Id.poly_mult_hom'[of Q R] unfolding univ_poly_mult by simp
        moreover have "\<sigma> S \<in> carrier (poly_ring M)"
          using polynomial_hom[OF Hom.homh field_axioms M.field_axioms A(3)] unfolding \<sigma>_def .
        hence "\<sigma> S \<in> carrier (poly_ring image_poly)"
          using polynomial_hom[OF Id.homh M.field_axioms is_field] by simp
        hence "Id.normalize (\<sigma> S) = \<sigma> S"
          using Id.normalize_polynomial unfolding sym[OF univ_poly_carrier] by simp
        ultimately show ?thesis
          using poly_hom[OF Q(1)] poly_hom[OF R(1)]
          unfolding pdivides_def factor_def univ_poly_mult by auto
      qed
      moreover have "Q \<in> carrier (poly_ring (image_poly))"
        using poly_hom[OF Q(1)] by simp
      ultimately show ?thesis
        using domain.pdivides_imp_root_sharing[OF field.axioms(1)[OF is_field], of Q] by auto
    qed
    thus "\<X>\<^bsub>(S, j)\<^esub> \<in> carrier image_poly" and "Id.eval (\<sigma> S) \<X>\<^bsub>(S, j)\<^esub> = \<zero>\<^bsub>image_poly\<^esub>"
      by auto
  qed
  ultimately have "law_restrict M = law_restrict image_poly"
    using assms(2) by simp
  hence "carrier M = carrier image_poly"
    unfolding law_restrict_def by (simp add:ring.defs)
  moreover have "\<X>\<^bsub>(P, i)\<^esub> \<in> carrier image_poly"
    using eval_pmod_var(2)[OF hyps Hom.homh Q(1) degree_gt] unfolding image_poly_def by simp
  moreover have "\<X>\<^bsub>(P, i)\<^esub> \<notin> carrier M"
    using indexed_var_not_index_free[of "(P, i)"] hyps(3) by blast
  ultimately show False by simp
qed

lemma (in field) exists_extension_with_roots:
  shows "\<exists>L \<in> extensions. \<forall>P \<in> carrier (poly_ring R). (ring.splitted L) (\<sigma> P)"
proof -
  obtain M where "M \<in> extensions" and "\<forall>L \<in> extensions. M \<lesssim> L \<longrightarrow> law_restrict L = law_restrict M"
    using exists_maximal_extension iso_incl_hom by blast
  thus ?thesis
    using exists_root[of M] by auto
qed


subsection \<open>Existence of Algebraic Closure\<close>

locale algebraic_closure = field L + subfield K L for L (structure) and K +
  assumes algebraic_extension: "x \<in> carrier L \<Longrightarrow> (algebraic over K) x"
    and roots_over_subfield: "P \<in> carrier (K[X]) \<Longrightarrow> splitted P"

locale algebraically_closed = field L for L (structure) +
  assumes roots_over_carrier: "P \<in> carrier (poly_ring L) \<Longrightarrow> splitted P"

definition (in field) closure :: "(('a list \<times> nat) multiset \<Rightarrow> 'a) ring" ("\<Omega>")
  where "closure = (SOME L \<comment> \<open>such that\<close>.
           \<comment> \<open>i\<close>  algebraic_closure L (indexed_const ` (carrier R)) \<and>
           \<comment> \<open>ii\<close> indexed_const \<in> ring_hom R L)"

lemma algebraic_hom:
  assumes "h \<in> ring_hom R S" and "field R" and "field S" and "subfield K R" and "x \<in> carrier R"
  shows "((ring.algebraic R) over K) x \<Longrightarrow> ((ring.algebraic S) over (h ` K)) (h x)"
proof -
  interpret Hom: ring_hom_ring R S h
    using ring_hom_ringI2[OF assms(2-3)[THEN field.is_ring] assms(1)] .
  assume "(Hom.R.algebraic over K) x"
  then obtain p where p: "p \<in> carrier (K[X]\<^bsub>R\<^esub>)" and "p \<noteq> []" and eval: "Hom.R.eval p x = \<zero>\<^bsub>R\<^esub>"
    using domain.algebraicE[OF field.axioms(1) subfieldE(1), of R K x] assms(2,4-5) by auto
  hence "(map h p) \<in> carrier ((h ` K)[X]\<^bsub>S\<^esub>)" and "(map h p) \<noteq> []"
    using Hom.subfield_polynomial_hom[OF assms(4) one_not_zero[OF assms(3)]] by auto
  moreover have "Hom.S.eval (map h p) (h x) = \<zero>\<^bsub>S\<^esub>"
    using Hom.eval_hom[OF subfieldE(1)[OF assms(4)] assms(5) p] unfolding eval by simp
  ultimately show ?thesis
    using Hom.S.non_trivial_ker_imp_algebraic[of "h ` K" "h x"] unfolding a_kernel_def' by auto
qed

lemma (in field) exists_closure:
  obtains L :: "((('a list \<times> nat) multiset) \<Rightarrow> 'a) ring"
  where "algebraic_closure L (indexed_const ` (carrier R))" and "indexed_const \<in> ring_hom R L"
proof -
  obtain L where "L \<in> extensions"
    and roots: "\<And>P. P \<in> carrier (poly_ring R) \<Longrightarrow> (ring.splitted L) (\<sigma> P)"
    using exists_extension_with_roots by auto

  let ?K = "indexed_const ` (carrier R)"
  let ?set_of_algs = "{ x \<in> carrier L. ((ring.algebraic L) over ?K) x }"
  let ?M = "L \<lparr> carrier := ?set_of_algs \<rparr>"

  from \<open>L \<in> extensions\<close>
  have L: "field L" and  hom: "ring_hom_ring R L indexed_const"
    using ring_hom_ringI2[OF ring_axioms field.is_ring] unfolding extensions_def by auto
  have "subfield ?K L"
    using ring_hom_ring.img_is_subfield(2)[OF hom carrier_is_subfield
          domain.one_not_zero[OF field.axioms(1)[OF L]]] by auto
  hence set_of_algs: "subfield ?set_of_algs L"
    using field.subfield_of_algebraics[OF L, of ?K] by simp
  have M: "field ?M"
    using ring.subfield_iff(2)[OF field.is_ring[OF L] set_of_algs] by simp

  interpret Id: ring_hom_ring ?M L id
    using ring_hom_ringI[OF field.is_ring[OF M] field.is_ring[OF L]] by auto

  have is_subfield: "subfield ?K ?M"
  proof (intro ring.subfield_iff(1)[OF field.is_ring[OF M]])
    have "L \<lparr> carrier := ?K \<rparr> = ?M \<lparr> carrier := ?K \<rparr>"
      by simp
    moreover from \<open>subfield ?K L\<close> have "field (L \<lparr> carrier := ?K \<rparr>)"
      using ring.subfield_iff(2)[OF field.is_ring[OF L]] by simp
    ultimately show "field (?M \<lparr> carrier := ?K \<rparr>)"
      by simp
  next
    show "?K \<subseteq> carrier ?M"
    proof
      fix x :: "(('a list \<times> nat) multiset) \<Rightarrow> 'a"
      assume "x \<in> ?K"
      hence "x \<in> carrier L"
        using ring_hom_memE(1)[OF ring_hom_ring.homh[OF hom]] by auto
      moreover from \<open>subfield ?K L\<close> and \<open>x \<in> ?K\<close> have "(Id.S.algebraic over ?K) x"
        using domain.algebraic_self[OF field.axioms(1)[OF L] subfieldE(1)] by auto
      ultimately show "x \<in> carrier ?M"
        by auto
    qed
  qed

  have "algebraic_closure ?M ?K"
  proof (intro algebraic_closure.intro[OF M is_subfield])
    have "(Id.R.algebraic over ?K) x" if "x \<in> carrier ?M" for x
      using that Id.S.algebraic_consistent[OF subfieldE(1)[OF set_of_algs]] by simp
    moreover have "Id.R.splitted P" if "P \<in> carrier (?K[X]\<^bsub>?M\<^esub>)" for P
    proof -
      from \<open>P \<in> carrier (?K[X]\<^bsub>?M\<^esub>)\<close> have "P \<in> carrier (poly_ring ?M)"
        using Id.R.carrier_polynomial_shell[OF subfieldE(1)[OF is_subfield]] by simp
      show ?thesis
      proof (cases "degree P = 0")
        case True with \<open>P \<in> carrier (poly_ring ?M)\<close> show ?thesis
          using domain.degree_zero_imp_splitted[OF field.axioms(1)[OF M]]
          by fastforce
      next
        case False then have "degree P > 0"
          by simp
        from \<open>P \<in> carrier (?K[X]\<^bsub>?M\<^esub>)\<close> have "P \<in> carrier (?K[X]\<^bsub>L\<^esub>)"
          unfolding Id.S.univ_poly_consistent[OF subfieldE(1)[OF set_of_algs]] .
        hence "set P \<subseteq> ?K"
          unfolding sym[OF univ_poly_carrier] polynomial_def by auto
        hence "\<exists>Q. set Q \<subseteq> carrier R \<and> P = \<sigma> Q"
        proof (induct P, simp add: \<sigma>_def)
          case (Cons p P)
          then obtain q Q where "q \<in> carrier R" "set Q \<subseteq> carrier R"
            and "\<sigma> Q = P" "indexed_const q = p"
            unfolding \<sigma>_def by auto
          hence "set (q # Q) \<subseteq> carrier R" and "\<sigma> (q # Q) = (p # P)"
            unfolding \<sigma>_def by auto
          thus ?case
            by metis
        qed
        then obtain Q where "set Q \<subseteq> carrier R" and "\<sigma> Q = P"
          by auto
        moreover have "lead_coeff Q \<noteq> \<zero>"
        proof (rule ccontr)
          assume "\<not> lead_coeff Q \<noteq> \<zero>" then have "lead_coeff Q = \<zero>"
            by simp
          with \<open>\<sigma> Q = P\<close> and \<open>degree P > 0\<close> have "lead_coeff P = indexed_const \<zero>"
            unfolding \<sigma>_def by (metis diff_0_eq_0 length_map less_irrefl_nat list.map_sel(1) list.size(3))
          hence "lead_coeff P = \<zero>\<^bsub>L\<^esub>"
            using ring_hom_zero[OF ring_hom_ring.homh ring_hom_ring.axioms(1-2)] hom by auto
          with \<open>degree P > 0\<close> have "\<not> P \<in> carrier (?K[X]\<^bsub>?M\<^esub>)"
            unfolding sym[OF univ_poly_carrier] polynomial_def by auto
          with \<open>P \<in> carrier (?K[X]\<^bsub>?M\<^esub>)\<close> show False
            by simp
        qed
        ultimately have "Q \<in> carrier (poly_ring R)"
          unfolding sym[OF univ_poly_carrier] polynomial_def by auto
        with \<open>\<sigma> Q = P\<close> have "Id.S.splitted P"
          using roots[of Q] by simp

        from \<open>P \<in> carrier (poly_ring ?M)\<close> show ?thesis
        proof (rule field.trivial_factors_imp_splitted[OF M])
          fix R
          assume R: "R \<in> carrier (poly_ring ?M)" "pirreducible\<^bsub>?M\<^esub> (carrier ?M) R" and "R pdivides\<^bsub>?M\<^esub> P"

          from \<open>P \<in> carrier (poly_ring ?M)\<close> and \<open>R \<in> carrier (poly_ring ?M)\<close>
          have "P \<in> carrier ((?set_of_algs)[X]\<^bsub>L\<^esub>)" and "R \<in> carrier ((?set_of_algs)[X]\<^bsub>L\<^esub>)"
            unfolding Id.S.univ_poly_consistent[OF subfieldE(1)[OF set_of_algs]] by auto
          hence in_carrier: "P \<in> carrier (poly_ring L)" "R \<in> carrier (poly_ring L)"
            using Id.S.carrier_polynomial_shell[OF subfieldE(1)[OF set_of_algs]] by auto

          from \<open>R pdivides\<^bsub>?M\<^esub> P\<close> have "R divides\<^bsub>((?set_of_algs)[X]\<^bsub>L\<^esub>)\<^esub> P"
            unfolding pdivides_def Id.S.univ_poly_consistent[OF subfieldE(1)[OF set_of_algs]]
            by simp
          with \<open>P \<in> carrier ((?set_of_algs)[X]\<^bsub>L\<^esub>)\<close> and \<open>R \<in> carrier ((?set_of_algs)[X]\<^bsub>L\<^esub>)\<close>
          have "R pdivides\<^bsub>L\<^esub> P"
            using domain.pdivides_iff_shell[OF field.axioms(1)[OF L] set_of_algs, of R P] by simp
          with \<open>Id.S.splitted P\<close> and \<open>degree P \<noteq> 0\<close> have "Id.S.splitted R"
            using field.pdivides_imp_splitted[OF L in_carrier(2,1)] by fastforce
          show "degree R \<le> 1"
          proof (cases "Id.S.roots R = {#}")
            case True with \<open>Id.S.splitted R\<close> show ?thesis
              unfolding Id.S.splitted_def by simp
          next
            case False with \<open>R \<in> carrier (poly_ring L)\<close>
            obtain a where "a \<in> carrier L" and "a \<in># Id.S.roots R"
              and "[ \<one>\<^bsub>L\<^esub>, \<ominus>\<^bsub>L\<^esub> a ] \<in> carrier (poly_ring L)" and pdiv: "[ \<one>\<^bsub>L\<^esub>, \<ominus>\<^bsub>L\<^esub> a ] pdivides\<^bsub>L\<^esub> R"
              using domain.not_empty_rootsE[OF field.axioms(1)[OF L], of R] by blast

            from \<open>P \<in> carrier (?K[X]\<^bsub>L\<^esub>)\<close>
            have "(Id.S.algebraic over ?K) a"
            proof (rule Id.S.algebraicI)
              from \<open>degree P \<noteq> 0\<close> show "P \<noteq> []"
                by auto
            next
              from \<open>a \<in># Id.S.roots R\<close> and \<open>R \<in> carrier (poly_ring L)\<close>
              have "Id.S.eval R a = \<zero>\<^bsub>L\<^esub>"
                using domain.roots_mem_iff_is_root[OF field.axioms(1)[OF L]]
                unfolding Id.S.is_root_def by auto
              with \<open>R pdivides\<^bsub>L\<^esub> P\<close> and \<open>a \<in> carrier L\<close> show "Id.S.eval P a = \<zero>\<^bsub>L\<^esub>"
                using domain.pdivides_imp_root_sharing[OF field.axioms(1)[OF L] in_carrier(2)] by simp
            qed
            with \<open>a \<in> carrier L\<close> have "a \<in> ?set_of_algs"
              by simp
            hence "[ \<one>\<^bsub>L\<^esub>, \<ominus>\<^bsub>L\<^esub> a ] \<in> carrier ((?set_of_algs)[X]\<^bsub>L\<^esub>)"
              using subringE(3,5)[of ?set_of_algs L] subfieldE(1,6)[OF set_of_algs]
              unfolding sym[OF univ_poly_carrier] polynomial_def by simp
            hence "[ \<one>\<^bsub>L\<^esub>, \<ominus>\<^bsub>L\<^esub> a ] \<in> carrier (poly_ring ?M)"
              unfolding Id.S.univ_poly_consistent[OF subfieldE(1)[OF set_of_algs]] by simp

            from \<open>[ \<one>\<^bsub>L\<^esub>, \<ominus>\<^bsub>L\<^esub> a ] \<in> carrier ((?set_of_algs)[X]\<^bsub>L\<^esub>)\<close>
             and \<open>R \<in> carrier ((?set_of_algs)[X]\<^bsub>L\<^esub>)\<close>
            have "[ \<one>\<^bsub>L\<^esub>, \<ominus>\<^bsub>L\<^esub> a ] divides\<^bsub>(?set_of_algs)[X]\<^bsub>L\<^esub>\<^esub> R"
              using pdiv domain.pdivides_iff_shell[OF field.axioms(1)[OF L] set_of_algs] by simp
            hence "[ \<one>\<^bsub>L\<^esub>, \<ominus>\<^bsub>L\<^esub> a ] divides\<^bsub>poly_ring ?M\<^esub> R"
              unfolding pdivides_def Id.S.univ_poly_consistent[OF subfieldE(1)[OF set_of_algs]]
              by simp

            have "[ \<one>\<^bsub>L\<^esub>, \<ominus>\<^bsub>L\<^esub> a ] \<notin> Units (poly_ring ?M)"
              using Id.R.univ_poly_units[OF field.carrier_is_subfield[OF M]] by force
            with \<open>[ \<one>\<^bsub>L\<^esub>, \<ominus>\<^bsub>L\<^esub> a ] \<in> carrier (poly_ring ?M)\<close> and \<open>R \<in> carrier (poly_ring ?M)\<close>
             and \<open>[ \<one>\<^bsub>L\<^esub>, \<ominus>\<^bsub>L\<^esub> a ] divides\<^bsub>poly_ring ?M\<^esub> R\<close>
            have "[ \<one>\<^bsub>L\<^esub>, \<ominus>\<^bsub>L\<^esub> a ] \<sim>\<^bsub>poly_ring ?M\<^esub> R"
              using Id.R.divides_pirreducible_condition[OF R(2)] by auto
            with \<open>[ \<one>\<^bsub>L\<^esub>, \<ominus>\<^bsub>L\<^esub> a ] \<in> carrier (poly_ring ?M)\<close> and \<open>R \<in> carrier (poly_ring ?M)\<close>
            have "degree R = 1"
              using domain.associated_polynomials_imp_same_length[OF field.axioms(1)[OF M]
                    Id.R.carrier_is_subring, of "[ \<one>\<^bsub>L\<^esub>, \<ominus>\<^bsub>L\<^esub> a ]" R] by force
            thus ?thesis
              by simp
          qed
        qed
      qed
    qed
    ultimately show "algebraic_closure_axioms ?M ?K"
      unfolding algebraic_closure_axioms_def by auto
  qed
  moreover have "indexed_const \<in> ring_hom R ?M"
    using ring_hom_ring.homh[OF hom] subfieldE(3)[OF is_subfield]
    unfolding subset_iff ring_hom_def by auto
  ultimately show thesis
    using that by auto
qed

lemma (in field) closureE:
  shows "algebraic_closure \<Omega> (indexed_const ` (carrier R))" and "indexed_const \<in> ring_hom R \<Omega>"
  using exists_closure unfolding closure_def
  by (metis (mono_tags, lifting) someI2)+

lemma (in field) algebraically_closedI:
  assumes "\<And>p. \<lbrakk> p \<in> carrier (poly_ring R); degree p > 1 \<rbrakk> \<Longrightarrow> \<exists>x \<in> carrier R. eval p x = \<zero>"
  shows "algebraically_closed R"
proof
  fix p assume "p \<in> carrier (poly_ring R)" thus "splitted p"
  proof (induction "degree p" arbitrary: p rule: less_induct)
    case less show ?case
    proof (cases "degree p \<le> 1")
      case True with \<open>p \<in> carrier (poly_ring R)\<close> show ?thesis
        using degree_zero_imp_splitted degree_one_imp_splitted by fastforce
    next
      case False then have "degree p > 1"
        by simp
      with \<open>p \<in> carrier (poly_ring R)\<close> have "roots p \<noteq> {#}"
        using assms[of p] roots_mem_iff_is_root[of p] unfolding is_root_def by force
      then obtain a where a: "a \<in> carrier R" "a \<in># roots p"
        and pdiv: "[ \<one>, \<ominus> a ] pdivides p" and in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
        using less(2) by blast
      then obtain q where q: "q \<in> carrier (poly_ring R)" and p: "p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q"
        unfolding pdivides_def by blast
      with \<open>degree p > 1\<close> have not_zero: "q \<noteq> []" and "p \<noteq> []"
        using domain.integral_iff[OF univ_poly_is_domain[OF carrier_is_subring] in_carrier, of q]
        by (auto simp add: univ_poly_zero[of R "carrier R"])
      hence deg: "degree p = Suc (degree q)"
        using poly_mult_degree_eq[OF carrier_is_subring] in_carrier q p
        unfolding univ_poly_carrier sym[OF univ_poly_mult[of R "carrier R"]] by auto
      hence "splitted q"
        using less(1)[OF _ q] by simp
      moreover have "roots p = add_mset a (roots q)"
        using poly_mult_degree_one_monic_imp_same_roots[OF a(1) q not_zero] p by simp
      ultimately show ?thesis
        unfolding splitted_def deg by simp
    qed
  qed
qed

sublocale algebraic_closure \<subseteq> algebraically_closed
proof (rule algebraically_closedI)
  fix P assume in_carrier: "P \<in> carrier (poly_ring L)" and gt_one: "degree P > 1"
  then have gt_zero: "degree P > 0"
    by simp

  define A where "A = finite_extension K P"

  from \<open>P \<in> carrier (poly_ring L)\<close> have "set P \<subseteq> carrier L"
    by (simp add: polynomial_incl univ_poly_carrier)
  hence A: "subfield A L" and P: "P \<in> carrier (A[X])"
    using finite_extension_mem[OF subfieldE(1)[OF subfield_axioms], of P] in_carrier
          algebraic_extension finite_extension_is_subfield[OF subfield_axioms, of P]
    unfolding sym[OF A_def] sym[OF univ_poly_carrier] polynomial_def by auto
  from \<open>set P \<subseteq> carrier L\<close> have incl: "K \<subseteq> A"
    using finite_extension_incl[OF subfieldE(3)[OF subfield_axioms]] unfolding A_def by simp

  interpret UP_K: domain "K[X]"
    using univ_poly_is_domain[OF subfieldE(1)[OF subfield_axioms]] .
  interpret UP_A: domain "A[X]"
    using univ_poly_is_domain[OF subfieldE(1)[OF A]] .
  interpret Rupt: ring "Rupt A P"
    unfolding rupture_def using ideal.quotient_is_ring[OF UP_A.cgenideal_ideal[OF P]] .
  interpret Hom: ring_hom_ring "L \<lparr> carrier := A \<rparr>" "Rupt A P" "rupture_surj A P \<circ> poly_of_const"
    using ring_hom_ringI2[OF subring_is_ring[OF subfieldE(1)] Rupt.ring_axioms
          rupture_surj_norm_is_hom[OF subfieldE(1) P]] A by simp
  let ?h = "rupture_surj A P \<circ> poly_of_const"

  have h_simp: "rupture_surj A P ` poly_of_const ` E = ?h ` E" for E
    by auto
  hence aux_lemmas:
    "subfield (rupture_surj A P ` poly_of_const ` K) (Rupt A P)"
    "subfield (rupture_surj A P ` poly_of_const ` A) (Rupt A P)"
    using Hom.img_is_subfield(2)[OF _ rupture_one_not_zero[OF A P gt_zero]]
          ring.subfield_iff(1)[OF subring_is_ring[OF subfieldE(1)[OF A]]]
          subfield_iff(2)[OF subfield_axioms] subfield_iff(2)[OF A] incl
    by auto

  have "carrier (K[X]) \<subseteq> carrier (A[X])"
    using subsetI[of "carrier (K[X])" "carrier (A[X])"] incl
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  hence "id \<in> ring_hom (K[X]) (A[X])"
    unfolding ring_hom_def unfolding univ_poly_mult univ_poly_add univ_poly_one by (simp add: subsetD)
  hence "rupture_surj A P \<in> ring_hom (K[X]) (Rupt A P)"
    using ring_hom_trans[OF _ rupture_surj_hom(1)[OF subfieldE(1)[OF A] P], of id] by simp
  then interpret Hom': ring_hom_ring "K[X]" "Rupt A P" "rupture_surj A P"
    using ring_hom_ringI2[OF UP_K.ring_axioms Rupt.ring_axioms] by simp

  from \<open>id \<in> ring_hom (K[X]) (A[X])\<close> have Id: "ring_hom_ring (K[X]) (A[X]) id"
    using ring_hom_ringI2[OF UP_K.ring_axioms UP_A.ring_axioms] by simp
  hence "subalgebra (poly_of_const ` K) (carrier (K[X])) (A[X])"
    using ring_hom_ring.img_is_subalgebra[OF Id _ UP_K.carrier_is_subalgebra[OF subfieldE(3)]]
          univ_poly_subfield_of_consts[OF subfield_axioms] by auto

  moreover from \<open>carrier (K[X]) \<subseteq> carrier (A[X])\<close> have "poly_of_const ` K \<subseteq> carrier (A[X])"
    using subfieldE(3)[OF univ_poly_subfield_of_consts[OF subfield_axioms]] by simp

  ultimately
  have "subalgebra (rupture_surj A P ` poly_of_const ` K) (rupture_surj A P ` carrier (K[X])) (Rupt A P)"
    using ring_hom_ring.img_is_subalgebra[OF rupture_surj_hom(2)[OF subfieldE(1)[OF A] P]] by simp

  moreover have "Rupt.finite_dimension (rupture_surj A P ` poly_of_const ` K) (carrier (Rupt A P))"
  proof (intro Rupt.telescopic_base_dim(1)[where
            ?K = "rupture_surj A P ` poly_of_const ` K" and
            ?F = "rupture_surj A P ` poly_of_const ` A" and
            ?E = "carrier (Rupt A P)", OF aux_lemmas])
    show "Rupt.finite_dimension (rupture_surj A P ` poly_of_const ` A) (carrier (Rupt A P))"
      using Rupt.finite_dimensionI[OF rupture_dimension[OF A P gt_zero]] .
  next
    let ?h = "rupture_surj A P \<circ> poly_of_const"

    from \<open>set P \<subseteq> carrier L\<close> have "finite_dimension K A"
      using finite_extension_finite_dimension(1)[OF subfield_axioms, of P] algebraic_extension
      unfolding A_def by auto
    then obtain Us where Us: "set Us \<subseteq> carrier L" "A = Span K Us"
      using exists_base subfield_axioms by blast
    hence "?h ` A = Rupt.Span (?h ` K) (map ?h Us)"
      using Hom.Span_hom[of K Us] incl Span_base_incl[OF subfield_axioms, of Us]
      unfolding Span_consistent[OF subfieldE(1)[OF A]] by simp
    moreover have "set (map ?h Us) \<subseteq> carrier (Rupt A P)"
      using Span_base_incl[OF subfield_axioms Us(1)] ring_hom_memE(1)[OF Hom.homh]
      unfolding sym[OF Us(2)] by auto
    ultimately
    show "Rupt.finite_dimension (rupture_surj A P ` poly_of_const ` K) (rupture_surj A P ` poly_of_const ` A)"
      using Rupt.Span_finite_dimension[OF aux_lemmas(1)] unfolding h_simp by simp
  qed

  moreover have "rupture_surj A P ` carrier (A[X]) = carrier (Rupt A P)"
    unfolding rupture_def FactRing_def A_RCOSETS_def' by auto
  with \<open>carrier (K[X]) \<subseteq> carrier (A[X])\<close> have "rupture_surj A P ` carrier (K[X]) \<subseteq> carrier (Rupt A P)"
    by auto

  ultimately
  have "Rupt.finite_dimension (rupture_surj A P ` poly_of_const ` K) (rupture_surj A P ` carrier (K[X]))"
    using Rupt.subalbegra_incl_imp_finite_dimension[OF aux_lemmas(1)] by simp

  hence "\<not> inj_on (rupture_surj A P) (carrier (K[X]))"
    using Hom'.infinite_dimension_hom[OF _ rupture_one_not_zero[OF A P gt_zero] _
          UP_K.carrier_is_subalgebra[OF subfieldE(3)] univ_poly_infinite_dimension[OF subfield_axioms]]
          univ_poly_subfield_of_consts[OF subfield_axioms]
    by auto
  then obtain Q where Q: "Q \<in> carrier (K[X])" "Q \<noteq> []" and "rupture_surj A P Q = \<zero>\<^bsub>Rupt A P\<^esub>"
    using Hom'.trivial_ker_imp_inj Hom'.hom_zero unfolding a_kernel_def' univ_poly_zero by blast
  with \<open>carrier (K[X]) \<subseteq> carrier (A[X])\<close> have "Q \<in> PIdl\<^bsub>A[X]\<^esub> P"
    using ideal.rcos_const_imp_mem[OF UP_A.cgenideal_ideal[OF P]]
    unfolding rupture_def FactRing_def by auto
  then obtain R where "R \<in> carrier (A[X])" and "Q = R \<otimes>\<^bsub>A[X]\<^esub> P"
    unfolding cgenideal_def by blast
  with \<open>P \<in> carrier (A[X])\<close> have "P pdivides Q"
    using dividesI[of _ "A[X]"] UP_A.m_comm pdivides_iff_shell[OF A] by simp
  hence "splitted P"
    using pdivides_imp_splitted[OF in_carrier
          carrier_polynomial_shell[OF subfieldE(1)[OF subfield_axioms] Q(1)] Q(2)
          roots_over_subfield[OF Q(1)]] Q by simp
  with \<open>degree P > 1\<close> obtain a where "a \<in># roots P"
    unfolding splitted_def by force
  thus "\<exists>x\<in>carrier L. eval P x = \<zero>"
    unfolding roots_mem_iff_is_root[OF in_carrier] is_root_def by blast
qed

end

