(* ************************************************************************** *)
(* Title:      Generated_Groups.thy                                           *)
(* Author:     Paulo Emílio de Vilhena                                        *)
(* ************************************************************************** *)

theory Generated_Groups
  imports Group Coset

begin

section\<open>Generated Groups\<close>

inductive_set
  generate :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for G and H where
    one:  "\<one>\<^bsub>G\<^esub> \<in> generate G H"
  | incl: "h \<in> H \<Longrightarrow> h \<in> generate G H"
  | inv:  "h \<in> H \<Longrightarrow> inv\<^bsub>G\<^esub> h \<in> generate G H"
  | eng:  "h1 \<in> generate G H \<Longrightarrow> h2 \<in> generate G H \<Longrightarrow> h1 \<otimes>\<^bsub>G\<^esub> h2 \<in> generate G H"


subsection\<open>Basic Properties of Generated Groups - First Part\<close>

lemma (in group) generate_in_carrier:
  assumes "H \<subseteq> carrier G"
  shows "h \<in> generate G H \<Longrightarrow> h \<in> carrier G"
  apply (induction rule: generate.induct) using assms by blast+

lemma (in group) generate_m_inv_closed:
  assumes "H \<subseteq> carrier G"
  shows "h \<in> generate G H \<Longrightarrow> (inv h) \<in> generate G H"
proof (induction rule: generate.induct)
  case one thus ?case by (simp add: generate.one)
next
  case (incl h) thus ?case using generate.inv[OF incl(1), of G] by simp
next
  case (inv h) thus ?case using assms generate.incl by fastforce
next
  case (eng h1 h2)
  hence "inv (h1 \<otimes> h2) = (inv h2) \<otimes> (inv h1)"
    by (meson assms generate_in_carrier group.inv_mult_group is_group)
  thus ?case using generate.eng[OF eng(4) eng(3)] by simp
qed

lemma (in group) generate_is_subgroup:
  assumes "H \<subseteq> carrier G"
  shows "subgroup (generate G H) G"
proof (intro subgroupI)
  show "generate G H \<subseteq> carrier G" using generate_in_carrier[OF assms] by blast
  show "generate G H \<noteq> {}"        using generate.one by auto
  show "\<And>h. h \<in> generate G H \<Longrightarrow> inv h \<in> generate G H"
    using generate_m_inv_closed[OF assms] by blast
  show "\<And>h1 h2. \<lbrakk> h1 \<in> generate G H; h2 \<in> generate G H \<rbrakk> \<Longrightarrow> h1 \<otimes> h2 \<in> generate G H"
    by (simp add: generate.eng) 
qed


subsection\<open>Characterisations of Generated Groups\<close>

lemma (in group) generate_min_subgroup1:
  assumes "H \<subseteq> carrier G"
    and "subgroup E G" "H \<subseteq> E"
  shows "generate G H \<subseteq> E"
proof
  fix h show "h \<in> generate G H \<Longrightarrow> h \<in> E"
  proof (induct rule: generate.induct)
    case one  thus ?case using subgroup.one_closed[OF assms(2)] by simp 
    case incl thus ?case using assms(3) by blast
    case inv  thus ?case using subgroup.m_inv_closed[OF assms(2)] assms(3) by blast
  next
    case eng thus ?case using subgroup.m_closed[OF assms(2)] by simp 
  qed
qed

lemma (in group) generateI:
  assumes "H \<subseteq> carrier G"
    and "subgroup E G" "H \<subseteq> E"
    and "\<And>K. \<lbrakk> subgroup K G; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
  shows "E = generate G H"
proof
  show "E \<subseteq> generate G H"
    using assms generate_is_subgroup generate.incl by (metis subset_iff)
  show "generate G H \<subseteq> E"
    using generate_min_subgroup1[OF assms(1-3)] by simp
qed

lemma (in group) generateE:
  assumes "H \<subseteq> carrier G" and "E = generate G H"
  shows "subgroup E G" and "H \<subseteq> E" and "\<And>K. \<lbrakk> subgroup K G; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
proof -
  show "subgroup E G" using assms generate_is_subgroup by simp
  show "H \<subseteq> E" using assms(2) by (simp add: generate.incl subsetI)
  show "\<And>K. subgroup K G \<Longrightarrow> H \<subseteq> K \<Longrightarrow> E \<subseteq> K"
    using assms generate_min_subgroup1 by auto
qed

lemma (in group) generate_min_subgroup2:
  assumes "H \<subseteq> carrier G"
  shows "generate G H = \<Inter>{K. subgroup K G \<and> H \<subseteq> K}"
proof
  have "subgroup (generate G H) G \<and> H \<subseteq> generate G H"
    by (simp add: assms generateE(2) generate_is_subgroup)
  thus "\<Inter>{K. subgroup K G \<and> H \<subseteq> K} \<subseteq> generate G H" by blast
next
  have "\<And>K. subgroup K G \<and> H \<subseteq> K \<Longrightarrow> generate G H \<subseteq> K"
    by (simp add: assms generate_min_subgroup1)
  thus "generate G H \<subseteq> \<Inter>{K. subgroup K G \<and> H \<subseteq> K}" by blast
qed


subsection\<open>Representation of Elements from a Generated Group\<close>

text\<open>We define a sort of syntax tree to allow induction arguments with elements of a generated group\<close>

datatype 'a repr =
  One | Inv "'a" | Leaf "'a" | Mult "'a repr" "'a repr"

fun norm :: "('a, 'b) monoid_scheme \<Rightarrow> 'a repr \<Rightarrow> 'a"
  where
    "norm G (One) = \<one>\<^bsub>G\<^esub>"
  | "norm G (Inv h) = (inv\<^bsub>G\<^esub> h)"
  | "norm G (Leaf h) = h" 
  | "norm G (Mult h1 h2) = (norm G h1) \<otimes>\<^bsub>G\<^esub> (norm G h2)"

fun elts :: "'a repr \<Rightarrow> 'a set"
  where
    "elts (One) = {}"
  | "elts (Inv h) = { h }"
  | "elts (Leaf h) = { h }" 
  | "elts (Mult h1 h2) = (elts h1) \<union> (elts h2)"

lemma (in group) generate_repr_iff:
  assumes "H \<subseteq> carrier G"
  shows "(h \<in> generate G H) \<longleftrightarrow> (\<exists>r. (elts r) \<subseteq> H \<and> norm G r = h)"
proof
  show "h \<in> generate G H \<Longrightarrow> \<exists>r. (elts r) \<subseteq> H \<and> norm G r = h"
  proof (induction rule: generate.induct)
    case one thus ?case
      using elts.simps(1) norm.simps(1)[of G] by fastforce 
  next
    case (incl h)
    hence "elts (Leaf h) \<subseteq> H \<and> norm G (Leaf h) = h" by simp
    thus ?case by blast
  next
    case (inv h)
    hence "elts (Inv h) \<subseteq> H \<and> norm G (Inv h) = inv h" by auto
    thus ?case by blast
  next
    case (eng h1 h2)
    then obtain r1 r2 where r1: "elts r1 \<subseteq> H" "norm G r1 = h1"
                        and r2: "elts r2 \<subseteq> H" "norm G r2 = h2" by blast
    hence "elts (Mult r1 r2) \<subseteq> H \<and> norm G (Mult r1 r2) = h1 \<otimes> h2" by simp
    thus ?case by blast 
  qed

  show "\<exists>r. elts r \<subseteq> H \<and> norm G r = h \<Longrightarrow> h \<in> generate G H"
  proof -
    assume "\<exists>r. elts r \<subseteq> H \<and> norm G r = h"
    then obtain r where "elts r \<subseteq> H" "norm G r = h" by blast
    thus "h \<in> generate G H"
    proof (induction arbitrary: h rule: repr.induct)
      case One thus ?case using generate.one by auto
    next
      case Inv thus ?case using generate.simps by force 
    next
      case Leaf thus ?case using generate.simps by force
    next
      case Mult thus ?case using generate.eng by fastforce
    qed
  qed
qed

corollary (in group) generate_repr_set:
  assumes "H \<subseteq> carrier G"
  shows "generate G H = {norm G r | r. (elts r) \<subseteq> H}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix h assume "h \<in> generate G H" thus "h \<in> {norm G r |r. elts r \<subseteq> H}"
      using generate_repr_iff[OF assms] by auto
  qed
next
  show "?B \<subseteq> ?A"
  proof
    fix h assume "h \<in> {norm G r |r. elts r \<subseteq> H}" thus "h \<in> generate G H"
      using generate_repr_iff[OF assms] by auto
  qed
qed

corollary (in group) mono_generate:
  assumes "I \<subseteq> J" and "J \<subseteq> carrier G"
  shows "generate G I \<subseteq> generate G J"
  using assms generate_repr_iff by fastforce

lemma (in group) subgroup_gen_equality:
  assumes "subgroup H G" "K \<subseteq> H"
  shows "generate G K = generate (G \<lparr> carrier := H \<rparr>) K"
proof -
  have "generate G K \<subseteq> H"
    by (meson assms generate_min_subgroup1 order.trans subgroup.subset)
  have mult_eq: "\<And>k1 k2. \<lbrakk> k1 \<in> generate G K; k2 \<in> generate G K \<rbrakk> \<Longrightarrow>
                           k1 \<otimes>\<^bsub>G \<lparr> carrier := H \<rparr>\<^esub> k2 = k1 \<otimes> k2"
    using \<open>generate G K \<subseteq> H\<close> subgroup_mult_equality by simp

  { fix r assume A: "elts r \<subseteq> K"
    hence "norm G r = norm (G \<lparr> carrier := H \<rparr>) r"
    proof (induction r rule: repr.induct)
      case One thus ?case by simp
    next
      case (Inv k) hence "k \<in> K" using A by simp 
      thus ?case using m_inv_consistent[OF assms(1)] assms(2) by auto
    next
      case (Leaf k) hence "k \<in> K" using A by simp 
      thus ?case using m_inv_consistent[OF assms(1)] assms(2) by auto
    next
      case (Mult k1 k2) thus ?case using mult_eq by auto
    qed } note aux_lemma = this

  show ?thesis
  proof
    show "generate G K \<subseteq> generate (G\<lparr>carrier := H\<rparr>) K"
    proof
      fix h assume "h \<in> generate G K" then obtain r where r: "elts r \<subseteq> K" "h = norm G r"
        using generate_repr_iff assms by (metis order.trans subgroup.subset)
      hence "h = norm (G \<lparr> carrier := H \<rparr>) r" using aux_lemma by simp
      thus "h \<in> generate (G\<lparr>carrier := H\<rparr>) K"
        using r assms group.generate_repr_iff [of "G \<lparr> carrier := H \<rparr>" K]
              subgroup.subgroup_is_group[OF assms(1) is_group] by auto
    qed
    show "generate (G\<lparr>carrier := H\<rparr>) K \<subseteq> generate G K"
    proof
      fix h assume "h \<in> generate (G\<lparr>carrier := H\<rparr>) K"
      then obtain r where r: "elts r \<subseteq> K" "h = norm (G\<lparr>carrier := H\<rparr>) r"
        using group.generate_repr_iff [of "G \<lparr> carrier := H \<rparr>" K]
              subgroup.subgroup_is_group[OF assms(1) is_group] assms by auto
      hence "h = norm G r" using aux_lemma by simp
      thus "h \<in> generate G K"
        by (meson assms generate_repr_iff order.trans r(1) subgroup.subset)
    qed
  qed
qed

corollary (in group) gen_equality_betw_subgroups:
  assumes "subgroup I G" "subgroup J G" "K \<subseteq> (I \<inter> J)"
  shows "generate (G \<lparr> carrier := I \<rparr>) K = generate (G \<lparr> carrier := J \<rparr>) K"
  by (metis Int_subset_iff assms subgroup_gen_equality)

lemma (in group) normal_generateI:
  assumes "H \<subseteq> carrier G"
    and "\<And>h g. \<lbrakk> h \<in> H; g \<in> carrier G \<rbrakk> \<Longrightarrow> g \<otimes> h \<otimes> (inv g) \<in> H"
  shows "generate G H \<lhd> G"
proof (rule normal_invI)
  show "subgroup (generate G H) G"
    by (simp add: assms(1) generate_is_subgroup)
next
  have "\<And>r g. \<lbrakk> elts r \<subseteq> H; g \<in> carrier G \<rbrakk> \<Longrightarrow> (g \<otimes> (norm G r) \<otimes> (inv g)) \<in> (generate G H)"
  proof -
    fix r g assume "elts r \<subseteq> H" "g \<in> carrier G"
    thus "(g \<otimes> (norm G r) \<otimes> (inv g)) \<in> (generate G H)"
    proof (induction r rule: repr.induct)
      case One thus ?case
        by (simp add: generate.one) 
    next
      case (Inv h)
      hence "g \<otimes> h \<otimes> (inv g) \<in> H" using assms(2) by simp
      moreover have "norm G (Inv (g \<otimes> h \<otimes> (inv g))) = g \<otimes> (inv h) \<otimes> (inv g)"
        using Inv.prems(1) Inv.prems(2) assms(1) inv_mult_group m_assoc by auto
      ultimately have "\<exists>r. elts r \<subseteq> H \<and> norm G r = g \<otimes> (inv h) \<otimes> (inv g)"
        by (metis elts.simps(2) empty_subsetI insert_subset)
      thus ?case by (simp add: assms(1) generate_repr_iff) 
    next
      case (Leaf h)
      thus ?case using assms(2)[of h g] generate.incl[of "g \<otimes> h \<otimes> inv g" H] by simp
    next
      case (Mult h1 h2)
      hence "elts h1 \<subseteq> H \<and> elts h2 \<subseteq> H" using Mult(3) by simp
      hence in_gen: "norm G h1 \<in> generate G H \<and> norm G h2 \<in> generate G H"
        using assms(1) generate_repr_iff by auto

      have "g \<otimes> norm G (Mult h1 h2) \<otimes> inv g = g \<otimes> (norm G h1 \<otimes> norm G h2) \<otimes> inv g" by simp
      also have " ... = g \<otimes> (norm G h1 \<otimes> (inv g \<otimes> g) \<otimes> norm G h2) \<otimes> inv g"
        using Mult(4) in_gen assms(1) generate_in_carrier by auto
      also have " ... = (g \<otimes> norm G h1 \<otimes> inv g) \<otimes> (g \<otimes> norm G h2 \<otimes> inv g)"
        using Mult.prems(2) assms(1) generate_in_carrier in_gen inv_closed m_assoc m_closed by presburger
      finally have "g \<otimes> norm G (Mult h1 h2) \<otimes> inv g =
                   (g \<otimes> norm G h1 \<otimes> inv g) \<otimes> (g \<otimes> norm G h2 \<otimes> inv g)" .

      thus ?case
        using generate.eng[of "g \<otimes> norm G h1 \<otimes> inv g" G H "g \<otimes> norm G h2 \<otimes> inv g"]
        by (simp add: Mult.IH Mult.prems(2) \<open>elts h1 \<subseteq> H \<and> elts h2 \<subseteq> H\<close>)
    qed
  qed
  thus "\<And>x h. x \<in> carrier G \<Longrightarrow> h \<in> generate G H \<Longrightarrow> x \<otimes> h \<otimes> inv x \<in> generate G H"
    using assms(1) generate_repr_iff by auto
qed


subsection\<open>Basic Properties of Generated Groups - Second Part\<close>

lemma (in group) generate_pow:
  assumes "a \<in> carrier G"
  shows "generate G { a } = { a [^] k | k. k \<in> (UNIV :: int set) }"
proof
  show "generate G { a } \<subseteq> { a [^] k | k. k \<in> (UNIV :: int set) }"
  proof
    fix h  show "h \<in> generate G { a } \<Longrightarrow> h \<in> { a [^] k | k. k \<in> (UNIV :: int set) }"
    proof (induction rule: generate.induct)
      case one thus ?case by (metis (mono_tags, lifting) UNIV_I int_pow_0 mem_Collect_eq) 
    next
      case (incl h) hence "h = a" by auto thus ?case
        by (metis (mono_tags, lifting) CollectI UNIV_I assms group.int_pow_1 is_group) 
    next
      case (inv h) hence "h = a" by auto thus ?case
        by (metis (mono_tags, lifting) mem_Collect_eq UNIV_I assms group.int_pow_1 int_pow_neg is_group)
    next
      case (eng h1 h2) thus ?case
        by (smt assms group.int_pow_mult is_group iso_tuple_UNIV_I mem_Collect_eq) 
    qed
  qed

  show "{ a [^] k | k. k \<in> (UNIV :: int set) } \<subseteq> generate G { a }"
  proof
    { fix k :: "nat" have "a [^] k \<in> generate G { a }"
      proof (induction k)
        case 0 thus ?case by (simp add: generate.one)
      next
        case (Suc k) thus ?case by (simp add: generate.eng generate.incl)
      qed } note aux_lemma = this

    fix h assume "h \<in> { a [^] k | k. k \<in> (UNIV :: int set) }"
    then obtain k :: "nat" where "h = a [^] k \<or> h = inv (a [^] k)"
      by (smt group.int_pow_def2 is_group mem_Collect_eq)
    thus "h \<in> generate G { a }" using aux_lemma
      using assms generate_m_inv_closed by auto
  qed
qed

corollary (in group) generate_one: "generate G { \<one> } = { \<one> }"
  using generate_pow[of "\<one>", OF one_closed] by simp

corollary (in group) generate_empty: "generate G {} = { \<one> }"
  using mono_generate[of "{}" "{ \<one> }"] generate_one generate.one one_closed by blast

corollary (in group)
  assumes "H \<subseteq> carrier G" "h \<in> H"
  shows "h [^] (k :: int) \<in> generate G H"
  using mono_generate[of "{ h }" H] generate_pow[of h] assms by auto


subsection\<open>Derived Subgroup\<close>

abbreviation derived_set :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "derived_set G H \<equiv>
     \<Union>h1 \<in> H. (\<Union>h2 \<in> H. { h1 \<otimes>\<^bsub>G\<^esub> h2 \<otimes>\<^bsub>G\<^esub> (inv\<^bsub>G\<^esub> h1) \<otimes>\<^bsub>G\<^esub> (inv\<^bsub>G\<^esub> h2) })"

definition derived :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "derived G H = generate G (derived_set G H)"

lemma (in group) derived_set_incl:
  assumes "subgroup H G"
  shows "derived_set G H \<subseteq> H"
  by (auto simp add: m_inv_consistent[OF assms] subgroupE[OF assms])

lemma (in group) derived_incl:
  assumes "subgroup H G"
  shows "derived G H \<subseteq> H"
  unfolding derived_def using derived_set_incl[OF assms] assms
  by (meson generate_min_subgroup1 order.trans subgroup.subset)

lemma (in group) subgroup_derived_equality:
  assumes "subgroup H G" "K \<subseteq> H"
  shows "derived (G \<lparr> carrier := H \<rparr>) K = derived G K"
proof -
  have "derived_set G K \<subseteq> H"
  proof
    fix x assume "x \<in> derived_set G K"
    then obtain k1 k2
      where k12: "k1 \<in> K" "k2 \<in> K"
        and  "x = k1 \<otimes> k2 \<otimes> inv k1 \<otimes> inv k2" by blast
    thus "x \<in> H" using k12 assms by (meson subgroup_def subsetCE)
  qed

  moreover have "derived_set (G \<lparr> carrier := H \<rparr>) K = derived_set G K"
  proof
    show "derived_set G K \<subseteq> derived_set (G\<lparr>carrier := H\<rparr>) K"
    proof
      fix x assume "x \<in> derived_set G K"
      then obtain k1 k2 where k12: "k1 \<in> K" "k2 \<in> K"
                          and "x = k1 \<otimes> k2 \<otimes> inv k1 \<otimes> inv k2" by blast
      hence "x = k1 \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> k2 \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> k1 \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> k2"
        using subgroup_mult_equality[OF assms(1)] m_inv_consistent[OF assms(1)] assms(2) k12
        by (simp add: subset_iff)
      thus "x \<in> derived_set (G\<lparr>carrier := H\<rparr>) K" using k12 by blast
    qed
  next
    show "derived_set (G \<lparr> carrier := H \<rparr>) K \<subseteq> derived_set G K"
    proof
      fix x assume "x \<in> derived_set (G \<lparr> carrier := H \<rparr>) K"
      then obtain k1 k2
        where k12: "k1 \<in> K" "k2 \<in> K"
          and "x = k1 \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> k2 \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> k1 \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> k2"
        by blast
      hence "x = k1 \<otimes> k2 \<otimes> inv k1 \<otimes> inv k2"
        using subgroup_mult_equality[OF assms(1)] m_inv_consistent[OF assms(1)] assms(2) k12
        by (simp add: subset_iff)
      thus "x \<in> derived_set G K" using k12 assms by blast
    qed
  qed

  ultimately show ?thesis unfolding derived_def
    using subgroup_gen_equality[OF assms(1), of "derived_set (G\<lparr>carrier := H\<rparr>) K"] by simp
qed

lemma (in comm_group) derived_set:
  assumes "H \<subseteq> carrier G"
  shows "derived G H = { \<one> }"
proof -
  have "derived_set G H = {} \<or> derived_set G H = { \<one> }"
  proof (cases)
    assume "H = {}" thus ?thesis by simp
  next
    assume "H \<noteq> {}" then obtain h' where h': "h' \<in> H" by blast
    have "derived_set G H = { \<one> }"
    proof -
      { fix h assume A: "h \<in> derived_set G H"
        have "h = \<one>"
        proof -
          obtain h1 h2 where h1: "h1 \<in> H" and h2: "h2 \<in> H" and h: "h = h1 \<otimes> h2 \<otimes> inv h1 \<otimes> inv h2"
            using A by blast
          hence "h = (h1 \<otimes> inv h1) \<otimes> (h2 \<otimes> inv h2)" using assms
            by (smt inv_closed inv_mult m_assoc m_closed r_inv set_rev_mp)
          thus ?thesis using h1 h2 assms by (metis contra_subsetD one_closed r_inv r_one)
        qed } note aux_lemma = this
      show ?thesis
      proof
        show "derived_set G H \<subseteq> { \<one> }" using aux_lemma by blast
      next
        show "{ \<one> } \<subseteq> derived_set G H"
        proof -
          have "h' \<otimes> h' \<otimes> inv h' \<otimes> inv h' \<in> derived_set G H" using h' by blast
          thus ?thesis using aux_lemma by auto
        qed
      qed
    qed
    thus ?thesis by simp
  qed
  thus ?thesis unfolding derived_def using generate_empty generate_one by presburger 
qed

lemma (in group) derived_set_in_carrier:
  assumes "H \<subseteq> carrier G"
  shows "derived_set G H \<subseteq> carrier G"
proof
  fix h assume "h \<in> derived_set G H"
  then obtain h1 h2 where "h1 \<in> H" "h2 \<in> H" "h = h1 \<otimes> h2 \<otimes> inv h1 \<otimes> inv h2"
    by blast
  thus "h \<in> carrier G" using assms by blast
qed

lemma (in group) derived_is_normal:
  assumes "H \<lhd> G"
  shows "derived G H \<lhd> G" unfolding derived_def
proof (rule normal_generateI)
  show "(\<Union>h1 \<in> H. \<Union>h2 \<in> H. { h1 \<otimes> h2 \<otimes> inv h1 \<otimes> inv h2 }) \<subseteq> carrier G"
    using subgroup.subset assms normal_invE(1) by blast
next
  show "\<And>h g. \<lbrakk> h \<in> derived_set G H; g \<in> carrier G \<rbrakk> \<Longrightarrow> g \<otimes> h \<otimes> inv g \<in> derived_set G H"
  proof -
    fix h g assume "h \<in> derived_set G H" and g: "g \<in> carrier G"
    then obtain h1 h2 where h1: "h1 \<in> H" "h1 \<in> carrier G"
                        and h2: "h2 \<in> H" "h2 \<in> carrier G"
                        and h:  "h = h1 \<otimes> h2 \<otimes> inv h1 \<otimes> inv h2"
      using subgroup.subset assms normal_invE(1) by blast
    hence "g \<otimes> h \<otimes> inv g =
           g \<otimes> h1 \<otimes> (inv g \<otimes> g) \<otimes> h2 \<otimes> (inv g \<otimes> g) \<otimes> inv h1 \<otimes> (inv g \<otimes> g) \<otimes> inv h2 \<otimes> inv g"
      by (simp add: g m_assoc)
    also
    have " ... =
          (g \<otimes> h1 \<otimes> inv g) \<otimes> (g \<otimes> h2 \<otimes> inv g) \<otimes> (g \<otimes> inv h1 \<otimes> inv g) \<otimes> (g \<otimes> inv h2 \<otimes> inv g)"
      using g h1 h2 m_assoc inv_closed m_closed by presburger
    finally
    have "g \<otimes> h \<otimes> inv g =
         (g \<otimes> h1 \<otimes> inv g) \<otimes> (g \<otimes> h2 \<otimes> inv g) \<otimes> inv (g \<otimes> h1 \<otimes> inv g) \<otimes> inv (g \<otimes> h2 \<otimes> inv g)"
      by (simp add: g h1 h2 inv_mult_group m_assoc)
    moreover have "g \<otimes> h1 \<otimes> inv g \<in> H" by (simp add: assms normal_invE(2) g h1)
    moreover have "g \<otimes> h2 \<otimes> inv g \<in> H" by (simp add: assms normal_invE(2) g h2)
    ultimately show "g \<otimes> h \<otimes> inv g \<in> derived_set G H" by blast
  qed
qed

corollary (in group) derived_self_is_normal: "derived G (carrier G) \<lhd> G"
  by (simp add: group.derived_is_normal group.normal_invI is_group subgroup_self)

corollary (in group) derived_subgroup_is_normal:
  assumes "subgroup H G"
  shows "derived G H \<lhd> G \<lparr> carrier := H \<rparr>"
proof -
  have "H \<lhd> G \<lparr> carrier := H \<rparr>"
    by (metis assms group.coset_join3 group.normalI group.subgroup_self
        partial_object.cases_scheme partial_object.select_convs(1) partial_object.update_convs(1)
        subgroup.rcos_const subgroup_imp_group)
  hence "derived (G \<lparr> carrier := H \<rparr>) H \<lhd> G \<lparr> carrier :=  H \<rparr>"
    using group.derived_is_normal[of "G \<lparr> carrier := H \<rparr>" H] normal_def by blast
  thus ?thesis using subgroup_derived_equality[OF assms] by simp
qed

corollary (in group) derived_quot_is_group: "group (G Mod (derived G (carrier G)))"
  using derived_self_is_normal normal.factorgroup_is_group by auto

lemma (in group) derived_quot_is_comm:
  assumes "H \<in> carrier (G Mod (derived G (carrier G)))"
    and "K \<in> carrier (G Mod (derived G (carrier G)))"
  shows "H <#> K = K <#> H"
proof -
  { fix H K assume A1: "H \<in> carrier (G Mod (derived G (carrier G)))"
               and A2: "K \<in> carrier (G Mod (derived G (carrier G)))"
    have "H <#> K \<subseteq> K <#> H"
    proof -
      obtain h k where hk: "h \<in> carrier G" "k \<in> carrier G"
                   and  H: "H = (derived G (carrier G)) #> h"
                   and  K: "K = (derived G (carrier G)) #> k"
        using A1 A2 unfolding FactGroup_def RCOSETS_def by auto
      have "H <#> K = (h \<otimes> k) <# (derived G (carrier G))"
        using hk H K derived_self_is_normal m_closed normal.coset_eq normal.rcos_sum
        by (metis (no_types, lifting))
      moreover have "K <#> H = (k \<otimes> h) <# (derived G (carrier G))"
        using hk H K derived_self_is_normal m_closed normal.coset_eq normal.rcos_sum
        by (metis (no_types, lifting))
      moreover have "(h \<otimes> k) <# (derived G (carrier G)) \<subseteq> (k \<otimes> h) <# (derived G (carrier G))"
      proof
        fix x assume "x \<in> h \<otimes> k <# derived G (carrier G)"
        then obtain d where d: "d \<in> derived G (carrier G)" "d \<in> carrier G" "x = h \<otimes> k \<otimes> d"
          using generate_is_subgroup[of "derived_set G (carrier G)"]
                subgroup.subset[of "derived G (carrier G)" G]
                derived_set_in_carrier[of "carrier G"]
          unfolding l_coset_def derived_def by auto
        hence "x = (k \<otimes> (h \<otimes> inv h) \<otimes> inv k) \<otimes> h \<otimes> k \<otimes> d"
          using hk by simp
        also have " ... = (k \<otimes> h) \<otimes> (inv h \<otimes> inv k) \<otimes> h \<otimes> k \<otimes> d"
          using d(2) hk m_assoc by (metis subgroup_def subgroup_self)
        also have " ... = (k \<otimes> h) \<otimes> ((inv h \<otimes> inv k \<otimes> h \<otimes> k) \<otimes> d)"
          using d(2) hk m_assoc by simp
        finally have "x = (k \<otimes> h) \<otimes> ((inv h \<otimes> inv k \<otimes> h \<otimes> k) \<otimes> d)" .

        moreover have "inv h \<otimes> inv k \<otimes> inv (inv h) \<otimes> inv (inv k) \<in> derived_set G (carrier G)"
          using inv_closed[OF hk(1)] inv_closed[OF hk(2)] by blast
        hence "inv h \<otimes> inv k \<otimes> h \<otimes> k \<in> derived_set G (carrier G)"
          by (simp add: hk(1) hk(2))
        hence "(inv h \<otimes> inv k \<otimes> h \<otimes> k) \<otimes> d \<in> derived G (carrier G)"
          using d(1) unfolding derived_def by (simp add: generate.eng generate.incl)

        ultimately show "x \<in> (k \<otimes> h) <# (derived G (carrier G))"
          unfolding l_coset_def by blast
      qed
      ultimately show ?thesis by simp
    qed }
  thus ?thesis using assms by auto
qed

theorem (in group) derived_quot_is_comm_group:
  "comm_group (G Mod (derived G (carrier G)))"
  apply (intro group.group_comm_groupI[OF derived_quot_is_group])
  using derived_quot_is_comm by simp

corollary (in group) derived_quot_of_subgroup_is_comm_group:
  assumes "subgroup H G"
  shows "comm_group ((G \<lparr> carrier := H \<rparr>) Mod (derived G H))"
proof -
  have "group (G \<lparr> carrier := H \<rparr>)"
    using assms subgroup_imp_group by auto
  thus ?thesis
    using group.derived_quot_is_comm_group subgroup_derived_equality[OF assms] by fastforce 
qed

lemma (in group) mono_derived:
  assumes "J \<subseteq> carrier G" "I \<subseteq> J"
  shows "(derived G ^^ n) I \<subseteq> (derived G ^^ n) J"
proof -
  { fix I J assume A: "J \<subseteq> carrier G" "I \<subseteq> J" have "derived G I \<subseteq> derived G J"
    proof -
      have "derived_set G I \<subseteq> derived_set G J" using A by blast
      thus ?thesis unfolding derived_def using mono_generate A by (simp add: derived_set_in_carrier)
    qed } note aux_lemma1 = this

  { fix n I assume A: "I \<subseteq> carrier G" have "(derived G ^^ n) I \<subseteq> carrier G"
    proof (induction n)
      case 0 thus ?case using A by simp
    next
      case (Suc n) thus ?case
        using aux_lemma1 derived_self_is_normal funpow_simps_right(2) funpow_swap1
                normal_def o_apply order.trans order_refl subgroup.subset by smt
    qed } note aux_lemma2 = this

  show ?thesis
  proof (induction n)
    case 0 thus ?case using assms by simp
  next
    case (Suc n) thus ?case using aux_lemma1 aux_lemma2 assms(1) by auto
  qed
qed

lemma (in group) exp_of_derived_in_carrier:
  assumes "H \<subseteq> carrier G"
  shows "(derived G ^^ n) H \<subseteq> carrier G" using assms
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  have "(derived G ^^ Suc n) H = (derived G) ((derived G ^^ n) H)" by simp
  also have " ... \<subseteq> (derived G) (carrier G)"
    using mono_derived[of "carrier G" "(derived G ^^ n) H" 1] Suc by simp
  also have " ... \<subseteq> carrier G" unfolding derived_def
    by (simp add: derived_set_incl generate_min_subgroup1 subgroup_self) 
  finally show ?case .  
qed

lemma (in group) exp_of_derived_is_subgroup:
  assumes "subgroup H G"
  shows "subgroup ((derived G ^^ n) H) G" using assms
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  have "(derived G ^^ n) H \<subseteq> carrier G"
    by (simp add: Suc.IH assms subgroup.subset)
  hence "subgroup ((derived G) ((derived G ^^ n) H)) G"
    unfolding derived_def using derived_set_in_carrier generate_is_subgroup by auto 
  thus ?case by simp
qed

end