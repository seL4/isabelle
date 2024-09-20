(*  Title:      HOL/Algebra/Ideal_Product.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Ideal_Product
  imports Ideal
begin

section \<open>Product of Ideals\<close>

text \<open>In this section, we study the structure of the set of ideals of a given ring.\<close>

inductive_set
  ideal_prod :: "[ ('a, 'b) ring_scheme, 'a set, 'a set ] \<Rightarrow> 'a set" (infixl \<open>\<cdot>\<index>\<close> 80)
  for R and I and J (* both I and J are supposed ideals *) where
    prod: "\<lbrakk> i \<in> I; j \<in> J \<rbrakk> \<Longrightarrow> i \<otimes>\<^bsub>R\<^esub> j \<in> ideal_prod R I J"
  |  sum: "\<lbrakk> s1 \<in> ideal_prod R I J; s2 \<in> ideal_prod R I J \<rbrakk> \<Longrightarrow> s1 \<oplus>\<^bsub>R\<^esub> s2 \<in> ideal_prod R I J"

definition ideals_set :: "('a, 'b) ring_scheme \<Rightarrow> ('a set) ring"
  where "ideals_set R = \<lparr> carrier = { I. ideal I R },
                             mult = ideal_prod R,
                              one = carrier R,
                             zero = { \<zero>\<^bsub>R\<^esub> },
                              add = set_add R \<rparr>"


subsection \<open>Basic Properties\<close>

lemma (in ring) ideal_prod_in_carrier:
  assumes "ideal I R" "ideal J R"
  shows "I \<cdot> J \<subseteq> carrier R"
proof
  fix s assume "s \<in> I \<cdot> J" thus "s \<in> carrier R"
    by (induct s rule: ideal_prod.induct) (auto, meson assms ideal.I_l_closed ideal.Icarr) 
qed

lemma (in ring) ideal_prod_inter:
  assumes "ideal I R" "ideal J R"
  shows "I \<cdot> J \<subseteq> I \<inter> J"
proof
  fix s assume "s \<in> I \<cdot> J" thus "s \<in> I \<inter> J"
    apply (induct s rule: ideal_prod.induct)
    apply (auto, (meson assms ideal.I_r_closed ideal.I_l_closed ideal.Icarr)+)
    apply (simp_all add: additive_subgroup.a_closed assms ideal.axioms(1))
    done
qed

lemma (in ring) ideal_prod_is_ideal:
  assumes "ideal I R" "ideal J R"
  shows "ideal (I \<cdot> J) R"
proof (rule idealI)
  show "ring R" using ring_axioms .
next
  show "subgroup (I \<cdot> J) (add_monoid R)"
    unfolding subgroup_def
  proof (auto)
    show "\<zero> \<in> I \<cdot> J" using ideal_prod.prod[of \<zero> I \<zero> J R]
      by (simp add: additive_subgroup.zero_closed assms ideal.axioms(1))
  next
    fix s1 s2 assume s1: "s1 \<in> I \<cdot> J" and s2: "s2 \<in> I \<cdot> J"
    have IJcarr: "\<And>a. a \<in> I \<cdot> J \<Longrightarrow> a \<in> carrier R"
      by (meson assms subsetD ideal_prod_in_carrier)
    show "s1 \<in> carrier R" using ideal_prod_in_carrier[OF assms] s1 by blast
    show "s1 \<oplus> s2 \<in> I \<cdot> J" by (simp add: ideal_prod.sum[OF s1 s2])
    show "inv\<^bsub>add_monoid R\<^esub> s1 \<in> I \<cdot> J" using s1
    proof (induct s1 rule: ideal_prod.induct)
      case (prod i j)
      hence "inv\<^bsub>add_monoid R\<^esub> (i \<otimes> j) = (inv\<^bsub>add_monoid R\<^esub> i) \<otimes> j"
        by (metis a_inv_def assms(1) assms(2) ideal.Icarr l_minus)
      thus ?case using ideal_prod.prod[of "inv\<^bsub>add_monoid R\<^esub> i" I j J R] assms
        by (simp add: additive_subgroup.a_subgroup ideal.axioms(1) prod.hyps subgroup.m_inv_closed)
    next
      case (sum s1 s2) thus ?case
        by (metis (no_types) IJcarr a_inv_def add.inv_mult_group ideal_prod.sum sum.hyps)
    qed
  qed
next
  fix s x assume s: "s \<in> I \<cdot> J" and x: "x \<in> carrier R"
  show "x \<otimes> s \<in> I \<cdot> J" using s
  proof (induct s rule: ideal_prod.induct)
    case (prod i j) thus ?case using ideal_prod.prod[of "x \<otimes> i" I j J R] assms
      by (simp add: x ideal.I_l_closed ideal.Icarr m_assoc)
  next
    case (sum s1 s2) thus ?case
    proof -
      have IJ: "I \<cdot> J \<subseteq> carrier R"
        by (metis (no_types) assms(1) assms(2) ideal.axioms(2) ring.ideal_prod_in_carrier)
      then have "s2 \<in> carrier R"
        using sum.hyps(3) by blast
      moreover have "s1 \<in> carrier R"
        using IJ sum.hyps(1) by blast
      ultimately show ?thesis
        by (simp add: ideal_prod.sum r_distr sum.hyps x)
    qed
  qed
  show "s \<otimes> x \<in> I \<cdot> J" using s
  proof (induct s rule: ideal_prod.induct)
    case (prod i j) thus ?case using ideal_prod.prod[of i I "j \<otimes> x" J R] assms x
      by (simp add: x ideal.I_r_closed ideal.Icarr m_assoc)
  next
    case (sum s1 s2) thus ?case 
    proof -
      have "s1 \<in> carrier R" "s2 \<in> carrier R"
        by (meson assms subsetD ideal_prod_in_carrier sum.hyps)+
      then show ?thesis
        by (metis ideal_prod.sum l_distr sum.hyps(2) sum.hyps(4) x)
    qed
  qed
qed

lemma (in ring) ideal_prod_eq_genideal:
  assumes "ideal I R" "ideal J R"
  shows "I \<cdot> J = Idl (I <#> J)"
proof
  have "I <#> J \<subseteq> I \<cdot> J"
  proof
    fix s assume "s \<in> I <#> J"
    then obtain i j where "i \<in> I" "j \<in> J" "s = i \<otimes> j"
      unfolding set_mult_def by blast
    thus "s \<in> I \<cdot> J" using ideal_prod.prod by simp
  qed
  thus "Idl (I <#> J) \<subseteq> I \<cdot> J"
    unfolding genideal_def using ideal_prod_is_ideal[OF assms] by blast
next
  show "I \<cdot> J \<subseteq> Idl (I <#> J)"
  proof
    fix s assume "s \<in> I \<cdot> J" thus "s \<in> Idl (I <#> J)"
    proof (induct s rule: ideal_prod.induct)
      case (prod i j) hence "i \<otimes> j \<in> I <#> J" unfolding set_mult_def by blast
      thus ?case unfolding genideal_def by blast 
    next
      case (sum s1 s2) thus ?case
        by (simp add: additive_subgroup.a_closed additive_subgroup.a_subset
            assms genideal_ideal ideal.axioms(1) set_mult_closed)
    qed
  qed
qed


lemma (in ring) ideal_prod_simp:
  assumes "ideal I R" "ideal J R" (* the second assumption could be suppressed *)
  shows "I = I <+> (I \<cdot> J)"
proof
  show "I \<subseteq> I <+> I \<cdot> J"
  proof
    fix i assume "i \<in> I" hence "i \<oplus> \<zero> \<in> I <+> I \<cdot> J"
      using set_add_def'[of R I "I \<cdot> J"] ideal_prod_is_ideal[OF assms]
            additive_subgroup.zero_closed[OF ideal.axioms(1), of "I \<cdot> J" R] by auto
    thus "i \<in> I <+> I \<cdot> J"
      using \<open>i \<in> I\<close> assms(1) ideal.Icarr by fastforce 
  qed
next
  show "I <+> I \<cdot> J \<subseteq> I"
  proof
    fix s assume "s \<in> I <+> I \<cdot> J"
    then obtain i ij where "i \<in> I" "ij \<in> I \<cdot> J" "s = i \<oplus> ij"
      using set_add_def'[of R I "I \<cdot> J"] by auto
    thus "s \<in> I"
      using ideal_prod_inter[OF assms]
      by (meson additive_subgroup.a_closed assms(1) ideal.axioms(1) inf_sup_ord(1) subsetCE) 
  qed
qed

lemma (in ring) ideal_prod_one:
  assumes "ideal I R"
  shows "I \<cdot> (carrier R) = I"
proof
  show "I \<cdot> (carrier R) \<subseteq> I"
  proof
    fix s assume "s \<in> I \<cdot> (carrier R)" thus "s \<in> I"
      by (induct s rule: ideal_prod.induct)
         (simp_all add: assms ideal.I_r_closed additive_subgroup.a_closed ideal.axioms(1))
  qed
next
  show "I \<subseteq> I \<cdot> (carrier R)"
  proof
    fix i assume "i \<in> I" thus "i \<in>  I \<cdot> (carrier R)"
      by (metis assms ideal.Icarr ideal_prod.simps one_closed r_one)
  qed
qed

lemma (in ring) ideal_prod_zero:
  assumes "ideal I R"
  shows "I \<cdot> { \<zero> } = { \<zero> }"
proof
  show "I \<cdot> { \<zero> } \<subseteq> { \<zero> }"
  proof
    fix s assume "s \<in> I \<cdot> {\<zero>}" thus "s \<in> { \<zero> }"
      using assms ideal.Icarr by (induct s rule: ideal_prod.induct) (fastforce, simp)
  qed
next
  show "{ \<zero> } \<subseteq> I \<cdot> { \<zero> }"
    by (simp add: additive_subgroup.zero_closed assms
                  ideal.axioms(1) ideal_prod_is_ideal zeroideal)
qed

lemma (in ring) ideal_prod_assoc:
  assumes "ideal I R" "ideal J R" "ideal K R"
  shows "(I \<cdot> J) \<cdot> K = I \<cdot> (J \<cdot> K)"
proof
  show "(I \<cdot> J) \<cdot> K \<subseteq> I \<cdot> (J \<cdot> K)"
  proof
    fix s assume "s \<in> (I \<cdot> J) \<cdot> K" thus "s \<in> I \<cdot> (J \<cdot> K)"
    proof (induct s rule: ideal_prod.induct)
      case (sum s1 s2) thus ?case
        by (simp add: ideal_prod.sum)
    next
      case (prod i k) thus ?case
      proof (induct i rule: ideal_prod.induct)
        case (prod i j) thus ?case
          using ideal_prod.prod[OF prod(1) ideal_prod.prod[OF prod(2-3),of R], of R]
          by (metis assms ideal.Icarr m_assoc) 
      next
        case (sum s1 s2) thus ?case
        proof -
          have "s1 \<in> carrier R" "s2 \<in> carrier R"
            by (meson assms subsetD ideal.axioms(2) ring.ideal_prod_in_carrier sum.hyps)+
          moreover have "k \<in> carrier R"
            by (meson additive_subgroup.a_Hcarr assms(3) ideal.axioms(1) sum.prems)
          ultimately show ?thesis
            by (metis ideal_prod.sum l_distr sum.hyps(2) sum.hyps(4) sum.prems)
        qed
      qed
    qed
  qed
next
  show "I \<cdot> (J \<cdot> K) \<subseteq> (I \<cdot> J) \<cdot> K"
  proof
    fix s assume "s \<in> I \<cdot> (J \<cdot> K)" thus "s \<in> (I \<cdot> J) \<cdot> K"
    proof (induct s rule: ideal_prod.induct)
      case (sum s1 s2) thus ?case by (simp add: ideal_prod.sum)
    next
      case (prod i j) show ?case using prod(2) prod(1)
      proof (induct j rule: ideal_prod.induct)
        case (prod j k) thus ?case
          using ideal_prod.prod[OF ideal_prod.prod[OF prod(3) prod(1), of R] prod (2), of R]
          by (metis assms ideal.Icarr m_assoc)
      next
        case (sum s1 s2) thus ?case
        proof -
          have "\<And>a A B. \<lbrakk>a \<in> B \<cdot> A; ideal A R; ideal B R\<rbrakk> \<Longrightarrow> a \<in> carrier R"
            by (meson subsetD ideal_prod_in_carrier)
          moreover have "i \<in> carrier R"
            by (meson additive_subgroup.a_Hcarr assms(1) ideal.axioms(1) sum.prems)
          ultimately show ?thesis
            by (metis (no_types) assms(2) assms(3) ideal_prod.sum r_distr sum)
        qed
      qed
    qed
  qed
qed

lemma (in ring) ideal_prod_r_distr:
  assumes "ideal I R" "ideal J R" "ideal K R"
  shows "I \<cdot> (J <+> K) = (I \<cdot> J) <+>  (I \<cdot> K)"
proof
  show "I \<cdot> (J <+> K) \<subseteq> I \<cdot> J <+> I \<cdot> K"
  proof
    fix s assume "s \<in> I \<cdot> (J <+> K)" thus "s \<in> I \<cdot> J <+> I \<cdot> K"
    proof(induct s rule: ideal_prod.induct)
      case (prod i jk)
      then obtain j k where j: "j \<in> J" and k: "k \<in> K" and jk: "jk = j \<oplus> k"
        using set_add_def'[of R J K] by auto
      hence "i \<otimes> j \<oplus> i \<otimes> k \<in> I \<cdot> J <+> I \<cdot> K"
        using ideal_prod.prod[OF prod(1) j,of R]
              ideal_prod.prod[OF prod(1) k,of R]
              set_add_def'[of R "I \<cdot> J" "I \<cdot> K"] by auto
      thus ?case
        using assms ideal.Icarr r_distr jk j k prod(1) by metis 
    next
      case (sum s1 s2) thus ?case
        by (simp add: add_ideals additive_subgroup.a_closed assms ideal.axioms(1)
                      local.ring_axioms ring.ideal_prod_is_ideal) 
    qed
  qed
next
  { fix s J K assume A: "ideal J R" "ideal K R" "s \<in> I \<cdot> J"
    have "s \<in> I \<cdot> (J <+> K) \<and> s \<in> I \<cdot> (K <+> J)"
    proof -
      from \<open>s \<in> I \<cdot> J\<close> have "s \<in> I \<cdot> (J <+> K)"
      proof (induct s rule: ideal_prod.induct)
        case (prod i j)
        hence "(j \<oplus> \<zero>) \<in> J <+> K"
          using set_add_def'[of R J K]
                additive_subgroup.zero_closed[OF ideal.axioms(1), of K R] A(2) by auto
        thus ?case
          by (metis A(1) additive_subgroup.a_Hcarr ideal.axioms(1) ideal_prod.prod prod r_zero)  
      next
        case (sum s1 s2) thus ?case
          by (simp add: ideal_prod.sum) 
      qed
      thus ?thesis
        by (metis A(1) A(2) ideal_def ring.union_genideal sup_commute) 
    qed } note aux_lemma = this

  show "I \<cdot> J <+> I \<cdot> K \<subseteq> I \<cdot> (J <+> K)"
  proof
    fix s assume "s \<in> I \<cdot> J <+> I \<cdot> K"
    then obtain s1 s2 where s1: "s1 \<in> I \<cdot> J" and s2: "s2 \<in> I \<cdot> K" and  s: "s = s1 \<oplus> s2"
      using set_add_def'[of R "I \<cdot> J" "I \<cdot> K"] by auto
    thus "s \<in> I \<cdot> (J <+> K)"
      using aux_lemma[OF assms(2) assms(3) s1]
            aux_lemma[OF assms(3) assms(2) s2] by (simp add: ideal_prod.sum)
  qed
qed

lemma (in cring) ideal_prod_commute:
  assumes "ideal I R" "ideal J R"
  shows "I \<cdot> J = J \<cdot> I"
proof -
  { fix I J assume A: "ideal I R" "ideal J R"
    have "I \<cdot> J \<subseteq> J \<cdot> I"
    proof
      fix s assume "s \<in> I \<cdot> J" thus "s \<in> J \<cdot> I"
      proof (induct s rule: ideal_prod.induct)
        case (prod i j) thus ?case
          using m_comm[OF ideal.Icarr[OF A(1) prod(1)] ideal.Icarr[OF A(2) prod(2)]]
          by (simp add: ideal_prod.prod)
      next
        case (sum s1 s2) thus ?case by (simp add: ideal_prod.sum) 
      qed
    qed }
  thus ?thesis using assms by blast 
qed

text \<open>The following result would also be true for locale ring\<close>
lemma (in cring) ideal_prod_distr:
  assumes "ideal I R" "ideal J R" "ideal K R"
  shows "I \<cdot> (J <+> K) = (I \<cdot> J) <+>  (I \<cdot> K)"
    and "(J <+> K) \<cdot> I = (J \<cdot> I) <+>  (K \<cdot> I)"
  by (simp_all add: assms ideal_prod_commute local.ring_axioms
                    ring.add_ideals ring.ideal_prod_r_distr)

lemma (in cring) ideal_prod_eq_inter:
  assumes "ideal I R" "ideal J R"
    and "I <+> J = carrier R"
  shows "I \<cdot> J = I \<inter> J"
proof
  show "I \<cdot> J \<subseteq> I \<inter> J"
    using assms ideal_prod_inter by auto
next
  show "I \<inter> J \<subseteq> I \<cdot> J"
  proof
    have "\<one> \<in> I <+> J" using assms(3) one_closed by simp 
    then obtain i j where ij: "i \<in> I" "j \<in> J" "\<one> = i \<oplus> j"
      using set_add_def'[of R I J] by auto

    fix s assume s: "s \<in> I \<inter> J"
    hence "(i \<otimes> s \<in> I \<cdot> J) \<and> (s \<otimes> j \<in> I \<cdot> J)"
      using ij(1-2) by (simp add: ideal_prod.prod)
    moreover have "s = (i \<otimes> s) \<oplus> (s \<otimes> j)"
      using ideal.Icarr[OF assms(1) ij(1)]
            ideal.Icarr[OF assms(2) ij(2)]
            ideal.Icarr[OF assms(1), of s]
      by (metis ij(3) s m_comm[of s i] Int_iff r_distr r_one)
    ultimately show "s \<in>  I \<cdot> J"
      using ideal_prod.sum by fastforce
  qed
qed


subsection \<open>Structure of the Set of Ideals\<close>

text \<open>We focus on commutative rings for convenience.\<close>

lemma (in cring) ideals_set_is_semiring: "semiring (ideals_set R)"
proof -
  have "abelian_monoid (ideals_set R)"
    apply (rule abelian_monoidI) unfolding ideals_set_def
    apply (simp_all add: add_ideals zeroideal)
    apply (simp add: add.set_mult_assoc additive_subgroup.a_subset ideal.axioms(1) set_add_defs(1))
    apply (metis Un_absorb1 additive_subgroup.a_subset additive_subgroup.zero_closed
        cgenideal_minimal cgenideal_self empty_iff genideal_minimal ideal.axioms(1)
        local.ring_axioms order_refl ring.genideal_self subset_antisym subset_singletonD
        union_genideal zero_closed zeroideal)
    by (metis sup_commute union_genideal)

  moreover have "monoid (ideals_set R)"
    apply (rule monoidI) unfolding ideals_set_def
    apply (simp_all add: ideal_prod_is_ideal oneideal
                         ideal_prod_commute ideal_prod_one)
    by (metis ideal_prod_assoc ideal_prod_commute)

  ultimately show ?thesis
    unfolding semiring_def semiring_axioms_def ideals_set_def
    by (simp_all add: ideal_prod_distr ideal_prod_commute ideal_prod_zero zeroideal) 
qed

lemma (in cring) ideals_set_is_comm_monoid: "comm_monoid (ideals_set R)"
proof -
  have "monoid (ideals_set R)"
    apply (rule monoidI) unfolding ideals_set_def
    apply (simp_all add: ideal_prod_is_ideal oneideal
                         ideal_prod_commute ideal_prod_one)
    by (metis ideal_prod_assoc ideal_prod_commute)
  thus ?thesis
    unfolding comm_monoid_def comm_monoid_axioms_def
    by (simp add: ideal_prod_commute ideals_set_def)
qed

lemma (in cring) ideal_prod_eq_Inter_aux:
  assumes "I: {..(Suc n)} \<rightarrow> { J. ideal J R }" 
    and "\<And>i j. \<lbrakk> i \<le> Suc n; j \<le> Suc n \<rbrakk> \<Longrightarrow>
                 i \<noteq> j \<Longrightarrow> (I i) <+> (I j) = carrier R"
  shows "(\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..n}. I k) <+> (I (Suc n)) = carrier R" using assms
proof (induct n arbitrary: I)
  case 0
  hence "(\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..0}. I k) <+> I (Suc 0) = (I 0) <+> (I (Suc 0))"
    using comm_monoid.finprod_0[OF ideals_set_is_comm_monoid, of I]
    by (simp add: atMost_Suc ideals_set_def)
  also have " ... = carrier R"
    using 0(2)[of 0 "Suc 0"] by simp
  finally show ?case .
next
  interpret ISet: comm_monoid "ideals_set R"
    by (simp add: ideals_set_is_comm_monoid)

  case (Suc n)
  let ?I' = "\<lambda>i. I (Suc i)"
  have "?I': {..(Suc n)} \<rightarrow> { J. ideal J R }"
    using Suc.prems(1) by auto
  moreover have "\<And>i j. \<lbrakk> i \<le> Suc n; j \<le> Suc n \<rbrakk> \<Longrightarrow>
                         i \<noteq> j \<Longrightarrow> (?I' i) <+> (?I' j) = carrier R"
    by (simp add: Suc.prems(2))
  ultimately have "(\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..n}. ?I' k) <+> (?I' (Suc n)) = carrier R"
    using Suc.hyps by metis

  moreover have I_carr: "I: {..Suc (Suc n)} \<rightarrow> carrier (ideals_set R)"
    unfolding ideals_set_def using Suc by simp
  hence I'_carr: "I \<in> Suc ` {..n} \<rightarrow> carrier (ideals_set R)" by auto
  ultimately have "(\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {(Suc 0)..Suc n}. I k) <+> (I (Suc (Suc n))) = carrier R"
    using ISet.finprod_reindex[of I "\<lambda>i. Suc i" "{..n}"] by (simp add: atMost_atLeast0) 

  hence "(carrier R) \<cdot> (I 0) = ((\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {Suc 0..Suc n}. I k) <+> I (Suc (Suc n))) \<cdot> (I 0)"
    by auto
  moreover have fprod_cl1: "ideal (\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {Suc 0..Suc n}. I k) R"
    by (metis I'_carr ISet.finprod_closed One_nat_def ideals_set_def image_Suc_atMost
        mem_Collect_eq partial_object.select_convs(1))
  ultimately
  have "I 0 = (\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {Suc 0..Suc n}. I k) \<cdot> (I 0) <+> I (Suc (Suc n)) \<cdot> (I 0)"
    by (metis PiE Suc.prems(1) atLeast0_atMost_Suc atLeast0_atMost_Suc_eq_insert_0
        atMost_atLeast0 ideal_prod_commute ideal_prod_distr(2) ideal_prod_one insertI1
        mem_Collect_eq oneideal)
  also have " ... = (I 0) \<cdot> (\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {Suc 0..Suc n}. I k) <+> I (Suc (Suc n)) \<cdot> (I 0)"
    using fprod_cl1 ideal_prod_commute Suc.prems(1)
    by (simp add: atLeast0_atMost_Suc_eq_insert_0 atMost_atLeast0) 
  also have " ... = (I 0) \<otimes>\<^bsub>(ideals_set R)\<^esub> (\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {Suc 0..Suc n}. I k) <+>
                     I (Suc (Suc n)) \<cdot> (I 0)"
    by (simp add: ideals_set_def)
  finally have I0: "I 0 = (\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..Suc n}. I k) <+> I (Suc (Suc n)) \<cdot> (I 0)"
    using ISet.finprod_insert[of "{Suc 0..Suc n}" 0 I]
          I_carr I'_carr atMost_atLeast0 ISet.finprod_0' atMost_Suc by auto

  have I_SucSuc_I0: "ideal (I (Suc (Suc n))) R \<and> ideal (I 0) R"
    using Suc.prems(1) by auto
  have fprod_cl2: "ideal (\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..Suc n}. I k) R"
    by (metis (no_types) ISet.finprod_closed I_carr Pi_split_insert_domain atMost_Suc ideals_set_def mem_Collect_eq partial_object.select_convs(1))
  have "carrier R = I (Suc (Suc n)) <+> I 0"
    by (simp add: Suc.prems(2))
  also have " ... = I (Suc (Suc n)) <+>
                    ((\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..Suc n}. I k) <+> I (Suc (Suc n)) \<cdot> (I 0))"
    using I0 by auto
  also have " ... = I (Suc (Suc n)) <+>
                    (I (Suc (Suc n)) \<cdot> (I 0) <+> (\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..Suc n}. I k))"
    using fprod_cl2 I_SucSuc_I0 by (metis Un_commute ideal_prod_is_ideal union_genideal)
  also have " ... = (I (Suc (Suc n)) <+> I (Suc (Suc n)) \<cdot> (I 0)) <+>
                    (\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..Suc n}. I k)"
    using fprod_cl2 I_SucSuc_I0 by (metis add.set_mult_assoc ideal_def ideal_prod_in_carrier
                                          oneideal ring.ideal_prod_one set_add_defs(1)) 
  also have " ... = I (Suc (Suc n)) <+> (\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..Suc n}. I k)"
    using ideal_prod_simp[of "I (Suc (Suc n))" "I 0"] I_SucSuc_I0 by simp 
  also have " ... = (\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..Suc n}. I k) <+> I (Suc (Suc n))"
    using fprod_cl2 I_SucSuc_I0 by (metis Un_commute union_genideal)
  finally show ?case by simp
qed

theorem (in cring) ideal_prod_eq_Inter:
  assumes "I: {..n :: nat} \<rightarrow> { J. ideal J R }" 
    and "\<And>i j. \<lbrakk> i \<in> {..n}; j \<in> {..n} \<rbrakk> \<Longrightarrow> i \<noteq> j \<Longrightarrow> (I i) <+> (I j) = carrier R"
  shows "(\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..n}. I k) = (\<Inter> k \<in> {..n}. I k)" using assms
proof (induct n)
  case 0 thus ?case
    using comm_monoid.finprod_0[OF ideals_set_is_comm_monoid] by (simp add: ideals_set_def) 
next
  interpret ISet: comm_monoid "ideals_set R"
    by (simp add: ideals_set_is_comm_monoid)

  case (Suc n)
  hence IH: "(\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..n}. I k) = (\<Inter> k \<in> {..n}. I k)"
    by (simp add: atMost_Suc)
  hence "(\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..Suc n}. I k) = I (Suc n) \<otimes>\<^bsub>(ideals_set R)\<^esub> (\<Inter> k \<in> {..n}. I k)"
    using ISet.finprod_insert[of "{Suc 0..Suc n}" 0 I] atMost_Suc_eq_insert_0[of n]
    by (metis ISet.finprod_Suc Suc.prems(1) ideals_set_def partial_object.select_convs(1))
  hence "(\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..Suc n}. I k) = I (Suc n) \<cdot> (\<Inter> k \<in> {..n}. I k)"
    by (simp add: ideals_set_def)
  moreover have "(\<Inter> k \<in> {..n}. I k) <+> I (Suc n) = carrier R"
    using ideal_prod_eq_Inter_aux[of I n] by (simp add: Suc.prems IH)
  moreover have "ideal (\<Inter> k \<in> {..n}. I k) R"
    using ring.i_Intersect[of R "I ` {..n}"]
    by (metis IH ISet.finprod_closed Pi_split_insert_domain Suc.prems(1) atMost_Suc
              ideals_set_def mem_Collect_eq partial_object.select_convs(1))
  ultimately
  have "(\<Otimes>\<^bsub>(ideals_set R)\<^esub> k \<in> {..Suc n}. I k) = (\<Inter> k \<in> {..n}. I k) \<inter> I (Suc n)"
    using ideal_prod_eq_inter[of "\<Inter> k \<in> {..n}. I k" "I (Suc n)"]
          ideal_prod_commute[of "\<Inter> k \<in> {..n}. I k" "I (Suc n)"]
    by (metis PiE Suc.prems(1) atMost_iff mem_Collect_eq order_refl)
  thus ?case by (simp add: Int_commute atMost_Suc) 
qed

corollary (in cring) inter_plus_ideal_eq_carrier:
  assumes "\<And>i. i \<le> Suc n \<Longrightarrow> ideal (I i) R" 
      and "\<And>i j. \<lbrakk> i \<le> Suc n; j \<le> Suc n; i \<noteq> j \<rbrakk> \<Longrightarrow> I i <+> I j = carrier R"
  shows "(\<Inter> i \<le> n. I i) <+> (I (Suc n)) = carrier R"
  using ideal_prod_eq_Inter[of I n] ideal_prod_eq_Inter_aux[of I n] by (auto simp add: assms)

corollary (in cring) inter_plus_ideal_eq_carrier_arbitrary:
  assumes "\<And>i. i \<le> Suc n \<Longrightarrow> ideal (I i) R" 
      and "\<And>i j. \<lbrakk> i \<le> Suc n; j \<le> Suc n; i \<noteq> j \<rbrakk> \<Longrightarrow> I i <+> I j = carrier R"
      and "j \<le> Suc n"
  shows "(\<Inter> i \<in> ({..(Suc n)} - { j }). I i) <+> (I j) = carrier R"
proof -
  define I' where "I' = (\<lambda>i. if i = Suc n then (I j) else
                             if i = j     then (I (Suc n))
                                          else (I i))"
  have "\<And>i. i \<le> Suc n \<Longrightarrow> ideal (I' i) R"
    using I'_def assms(1) assms(3) by auto
  moreover have "\<And>i j. \<lbrakk> i \<le> Suc n; j \<le> Suc n; i \<noteq> j \<rbrakk> \<Longrightarrow> I' i <+> I' j = carrier R"
    using I'_def assms(2-3) by force
  ultimately have "(\<Inter> i \<le> n. I' i) <+> (I' (Suc n)) = carrier R"
    using inter_plus_ideal_eq_carrier by simp

  moreover have "I' ` {..n} = I ` ({..(Suc n)} - { j })"
  proof
    show "I' ` {..n} \<subseteq> I ` ({..Suc n} - {j})"
    proof
      fix x assume "x \<in> I' ` {..n}"
      then obtain i where i: "i \<in> {..n}" "I' i = x" by blast
      thus "x \<in> I ` ({..Suc n} - {j})"
      proof (cases)
        assume "i = j" thus ?thesis using i I'_def by auto
      next
        assume "i \<noteq> j" thus ?thesis using I'_def i insert_iff by auto
      qed
    qed
  next
    show "I ` ({..Suc n} - {j}) \<subseteq> I' ` {..n}"
    proof
      fix x assume "x \<in> I ` ({..Suc n} - {j})"
      then obtain i where i: "i \<in> {..Suc n}" "i \<noteq> j" "I i = x" by blast
      thus "x \<in> I' ` {..n}"
      proof (cases)
        assume "i = Suc n" thus ?thesis using I'_def assms(3) i(2-3) by auto
      next
        assume "i \<noteq> Suc n" thus ?thesis using I'_def i by auto
      qed
    qed
  qed
  ultimately show ?thesis using I'_def by metis 
qed


subsection \<open>Another Characterization of Prime Ideals\<close>

text \<open>With product of ideals being defined, we can give another definition of a prime ideal\<close>

lemma (in ring) primeideal_divides_ideal_prod:
  assumes "primeideal P R" "ideal I R" "ideal J R"
      and "I \<cdot> J \<subseteq> P"
    shows "I \<subseteq> P \<or> J \<subseteq> P"
proof (cases)
  assume "\<exists> i \<in> I. i \<notin> P"
  then obtain i where i: "i \<in> I" "i \<notin> P" by blast
  have "J \<subseteq> P"
  proof
    fix j assume j: "j \<in> J"
    hence "i \<otimes> j \<in> P"
      using ideal_prod.prod[OF i(1) j, of R] assms(4) by auto
    thus "j \<in> P"
      using primeideal.I_prime[OF assms(1), of i j] i j
      by (meson assms(2-3) ideal.Icarr) 
  qed
  thus ?thesis by blast
next
  assume "\<not> (\<exists> i \<in> I. i \<notin> P)" thus ?thesis by blast
qed

lemma (in cring) divides_ideal_prod_imp_primeideal:
  assumes "ideal P R"
    and "P \<noteq> carrier R"
    and "\<And>I J. \<lbrakk> ideal I R; ideal J R; I \<cdot> J \<subseteq> P \<rbrakk> \<Longrightarrow> I \<subseteq> P \<or> J \<subseteq> P"
  shows "primeideal P R"
proof -
  have "\<And>a b. \<lbrakk> a \<in> carrier R; b \<in> carrier R; a \<otimes> b \<in> P \<rbrakk> \<Longrightarrow> a \<in> P \<or> b \<in> P"
  proof -
    fix a b assume A: "a \<in> carrier R" "b \<in> carrier R" "a \<otimes> b \<in> P"
    have "(PIdl a) \<cdot> (PIdl b) = Idl (PIdl (a \<otimes> b))"
      using ideal_prod_eq_genideal[of "Idl { a }" "Idl { b }"]
            A(1-2) cgenideal_eq_genideal cgenideal_ideal cgenideal_prod by auto
    hence "(PIdl a) \<cdot> (PIdl b) = PIdl (a \<otimes> b)"
      by (simp add: A Idl_subset_ideal cgenideal_ideal cgenideal_minimal
                    genideal_self oneideal subset_antisym)
    hence "(PIdl a) \<cdot> (PIdl b) \<subseteq> P"
      by (simp add: A(3) assms(1) cgenideal_minimal)
    hence "(PIdl a) \<subseteq> P \<or> (PIdl b) \<subseteq> P"
      by (simp add: A assms(3) cgenideal_ideal)
    thus "a \<in> P \<or> b \<in> P"
      using A cgenideal_self by blast
  qed
  thus ?thesis
    using assms is_cring by (simp add: primeidealI)
qed

end
