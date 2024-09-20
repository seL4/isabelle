(*  Title:      HOL/Algebra/Algebraic_Closure.thy
    Author:     Paulo Emílio de Vilhena

With contributions by Martin Baillon.
*)

theory Algebraic_Closure
  imports Indexed_Polynomials Polynomial_Divisibility Finite_Extensions

begin

section \<open>Algebraic Closure\<close>

subsection \<open>Definitions\<close>

inductive iso_incl :: "'a ring \<Rightarrow> 'a ring \<Rightarrow> bool" (infixl \<open>\<lesssim>\<close> 65) for A B
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

abbreviation (in ring) restrict_extensions :: "((('a list \<times> nat) multiset) \<Rightarrow> 'a) ring set" (\<open>\<S>\<close>)
  where "\<S> \<equiv> law_restrict ` extensions"


subsection \<open>Basic Properties\<close>

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

definition (in field) alg_closure :: "(('a list \<times> nat) multiset \<Rightarrow> 'a) ring"
  where "alg_closure = (SOME L \<comment> \<open>such that\<close>.
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

lemma (in field) alg_closureE:
  shows "algebraic_closure alg_closure (indexed_const ` (carrier R))"
    and "indexed_const \<in> ring_hom R alg_closure"
  using exists_closure unfolding alg_closure_def
  by (metis (mono_tags, lifting) someI2)+

lemma (in field) algebraically_closedI':
  assumes "\<And>p. \<lbrakk> p \<in> carrier (poly_ring R); degree p > 1 \<rbrakk> \<Longrightarrow> splitted p"
  shows "algebraically_closed R"
proof
  fix p assume "p \<in> carrier (poly_ring R)" show "splitted p"
  proof (cases "degree p \<le> 1")
    case True with \<open>p \<in> carrier (poly_ring R)\<close> show ?thesis
      using degree_zero_imp_splitted degree_one_imp_splitted by fastforce
  next
    case False with \<open>p \<in> carrier (poly_ring R)\<close> show ?thesis
      using assms by fastforce
  qed
qed

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
proof (rule algebraically_closedI')
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
  thus "splitted P"
    using pdivides_imp_splitted[OF in_carrier
          carrier_polynomial_shell[OF subfieldE(1)[OF subfield_axioms] Q(1)] Q(2)
          roots_over_subfield[OF Q(1)]] Q
    by simp
qed

end

