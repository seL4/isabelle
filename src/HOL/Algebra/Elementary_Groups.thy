section \<open>Elementary Group Constructions\<close>

(*  Title:      HOL/Algebra/Elementary_Groups.thy
    Author:     LC Paulson, ported from HOL Light
*)

theory Elementary_Groups
imports Generated_Groups
begin

subsection\<open>Direct sum/product lemmas\<close>

locale group_disjoint_sum = group G + AG: subgroup A G + BG: subgroup B G for G (structure) and A B
begin

lemma subset_one: "A \<inter> B \<subseteq> {\<one>} \<longleftrightarrow> A \<inter> B = {\<one>}"
  by  auto

lemma sub_id_iff: "A \<inter> B \<subseteq> {\<one>} \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = \<one> \<longrightarrow> x = \<one> \<and> y = \<one>)"
        (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> inv y = \<one> \<longrightarrow> x = \<one> \<and> inv y = \<one>)"
  proof (intro ballI iffI impI)
    fix x y
    assume "A \<inter> B \<subseteq> {\<one>}" "x \<in> A" "y \<in> B" "x \<otimes> inv y = \<one>"
    then have "y = x"
      using group.inv_equality group_l_invI by fastforce
    then show "x = \<one> \<and> inv y = \<one>"
      using \<open>A \<inter> B \<subseteq> {\<one>}\<close> \<open>x \<in> A\<close> \<open>y \<in> B\<close> by fastforce
  next
    assume "\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> inv y = \<one> \<longrightarrow> x = \<one> \<and> inv y = \<one>"
    then show "A \<inter> B \<subseteq> {\<one>}"
      by auto
  qed
  also have "\<dots> = ?rhs"
    by (metis BG.mem_carrier BG.subgroup_axioms inv_inv subgroup_def)
  finally show ?thesis .
qed

lemma cancel: "A \<inter> B \<subseteq> {\<one>} \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. \<forall>x'\<in>A. \<forall>y'\<in>B. x \<otimes> y = x' \<otimes> y' \<longrightarrow> x = x' \<and> y = y')"
        (is "?lhs = ?rhs")
proof -
  have "(\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = \<one> \<longrightarrow> x = \<one> \<and> y = \<one>) = ?rhs"
    (is "?med = _")
  proof (intro ballI iffI impI)
    fix x y x' y'
    assume * [rule_format]: "\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = \<one> \<longrightarrow> x = \<one> \<and> y = \<one>"
      and AB: "x \<in> A" "y \<in> B" "x' \<in> A" "y' \<in> B" and eq: "x \<otimes> y = x' \<otimes> y'"
    then have carr: "x \<in> carrier G" "x' \<in> carrier G" "y \<in> carrier G" "y' \<in> carrier G"
      using AG.subset BG.subset by auto
    then have "inv x' \<otimes> x \<otimes> (y \<otimes> inv y') = inv x' \<otimes> (x \<otimes> y) \<otimes> inv y'"
      by (simp add: m_assoc)
    also have "\<dots> = \<one>"
      using carr  by (simp add: eq) (simp add: m_assoc)
    finally have 1: "inv x' \<otimes> x \<otimes> (y \<otimes> inv y') = \<one>" .
    show "x = x' \<and> y = y'"
      using * [OF _ _ 1] AB by simp (metis carr inv_closed inv_inv local.inv_equality)
  next
    fix x y
    assume * [rule_format]: "\<forall>x\<in>A. \<forall>y\<in>B. \<forall>x'\<in>A. \<forall>y'\<in>B. x \<otimes> y = x' \<otimes> y' \<longrightarrow> x = x' \<and> y = y'"
      and xy: "x \<in> A" "y \<in> B" "x \<otimes> y = \<one>"
    show "x = \<one> \<and> y = \<one>"
      by (rule *) (use xy in auto)
  qed
  then show ?thesis
    by (simp add: sub_id_iff)
qed

lemma commuting_imp_normal1:
  assumes sub: "carrier G \<subseteq> A <#> B"
     and mult: "\<And>x y. \<lbrakk>x \<in> A; y \<in> B\<rbrakk> \<Longrightarrow> x \<otimes> y = y \<otimes> x"
   shows "A \<lhd> G"
proof -
  have AB: "A \<subseteq> carrier G \<and> B \<subseteq> carrier G"
    by (simp add: AG.subset BG.subset)
  have "A #> x = x <# A"
    if x: "x \<in> carrier G" for x
  proof -
    obtain a b where xeq: "x = a \<otimes> b" and "a \<in> A" "b \<in> B" and carr: "a \<in> carrier G" "b \<in> carrier G"
      using x sub AB by (force simp: set_mult_def)
    have Ab: "A <#> {b} = {b} <#> A"
      using AB \<open>a \<in> A\<close> \<open>b \<in> B\<close> mult
      by (force simp: set_mult_def m_assoc subset_iff)
    have "A #> x = A <#> {a \<otimes> b}"
      by (auto simp: l_coset_eq_set_mult r_coset_eq_set_mult xeq)
    also have "\<dots> = A <#> {a} <#> {b}"
      using AB \<open>a \<in> A\<close> \<open>b \<in> B\<close>
      by (auto simp: set_mult_def m_assoc subset_iff)
    also have "\<dots> = {a} <#> A <#> {b}"
      by (metis AG.rcos_const AG.subgroup_axioms \<open>a \<in> A\<close> coset_join3 is_group l_coset_eq_set_mult r_coset_eq_set_mult subgroup.mem_carrier)
    also have "\<dots> = {a} <#> {b} <#> A"
      by (simp add: is_group carr group.set_mult_assoc AB Ab)
    also have "\<dots> = {x} <#> A"
      by (auto simp: set_mult_def xeq)
    finally show "A #> x = x <# A"
      by (simp add: l_coset_eq_set_mult)
  qed
  then show ?thesis
    by (auto simp: normal_def normal_axioms_def AG.subgroup_axioms is_group)
qed

lemma commuting_imp_normal2:
  assumes"carrier G \<subseteq> A <#> B"  "\<And>x y. \<lbrakk>x \<in> A; y \<in> B\<rbrakk> \<Longrightarrow> x \<otimes> y = y \<otimes> x"
  shows "B \<lhd> G"
proof (rule group_disjoint_sum.commuting_imp_normal1)
  show "group_disjoint_sum G B A"
  proof qed
next
  show "carrier G \<subseteq> B <#> A"
    using BG.subgroup_axioms assms commut_normal commuting_imp_normal1 by blast
qed (use assms in auto)


lemma (in group) normal_imp_commuting:
  assumes "A \<lhd> G" "B \<lhd> G" "A \<inter> B \<subseteq> {\<one>}" "x \<in> A" "y \<in> B"
  shows "x \<otimes> y = y \<otimes> x"
proof -
  interpret AG: normal A G
    using assms by auto
  interpret BG: normal B G
    using assms by auto
  interpret group_disjoint_sum G A B
  proof qed
  have * [rule_format]: "(\<forall>x\<in>A. \<forall>y\<in>B. \<forall>x'\<in>A. \<forall>y'\<in>B. x \<otimes> y = x' \<otimes> y' \<longrightarrow> x = x' \<and> y = y')"
    using cancel assms by (auto simp: normal_def)
  have carr: "x \<in> carrier G" "y \<in> carrier G"
    using assms AG.subset BG.subset by auto
  then show ?thesis
    using * [of x _ _ y] AG.coset_eq [rule_format, of y] BG.coset_eq [rule_format, of x]
    by (clarsimp simp: l_coset_def r_coset_def set_eq_iff) (metis \<open>x \<in> A\<close> \<open>y \<in> B\<close>)
qed

lemma normal_eq_commuting:
  assumes "carrier G \<subseteq> A <#> B" "A \<inter> B \<subseteq> {\<one>}"
  shows "A \<lhd> G \<and> B \<lhd> G \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x)"
  by (metis assms commuting_imp_normal1 commuting_imp_normal2 normal_imp_commuting)

lemma (in group) hom_group_mul_rev:
  assumes "(\<lambda>(x,y). x \<otimes> y) \<in> hom (subgroup_generated G A \<times>\<times> subgroup_generated G B) G"
          (is "?h \<in> hom ?P G")
   and "x \<in> carrier G" "y \<in> carrier G" "x \<in> A" "y \<in> B"
 shows "x \<otimes> y = y \<otimes> x"
proof -
  interpret P: group_hom ?P G ?h
    by (simp add: assms DirProd_group group_hom.intro group_hom_axioms.intro is_group)
  have xy: "(x,y) \<in> carrier ?P"
    by (auto simp: assms carrier_subgroup_generated generate.incl)
  have "x \<otimes> (x \<otimes> (y \<otimes> y)) = x \<otimes> (y \<otimes> (x \<otimes> y))"
    using P.hom_mult [OF xy xy] by (simp add: m_assoc assms)
  then have "x \<otimes> (y \<otimes> y) = y \<otimes> (x \<otimes> y)"
    using assms by simp
  then show ?thesis
    by (simp add: assms flip: m_assoc)
qed

lemma hom_group_mul_eq:
   "(\<lambda>(x,y). x \<otimes> y) \<in> hom (subgroup_generated G A \<times>\<times> subgroup_generated G B) G
     \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x)"
         (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    using hom_group_mul_rev AG.subset BG.subset by blast
next
  assume R: ?rhs
  have subG: "generate G (carrier G \<inter> A) \<subseteq> carrier G" for A
    by (simp add: generate_incl)
  have *: "x \<otimes> u \<otimes> (y \<otimes> v) = x \<otimes> y \<otimes> (u \<otimes> v)"
    if eq [rule_format]: "\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x"
      and gen: "x \<in> generate G (carrier G \<inter> A)" "y \<in> generate G (carrier G \<inter> B)"
      "u \<in> generate G (carrier G \<inter> A)" "v \<in> generate G (carrier G \<inter> B)"
    for x y u v
  proof -
    have "u \<otimes> y = y \<otimes> u"
      by (metis AG.carrier_subgroup_generated_subgroup BG.carrier_subgroup_generated_subgroup carrier_subgroup_generated eq that(3) that(4))
    then have "x \<otimes> u \<otimes> y = x \<otimes> y \<otimes> u"
      using gen by (simp add: m_assoc subsetD [OF subG])
    then show ?thesis
      using gen by (simp add: subsetD [OF subG] flip: m_assoc)
  qed
  show ?lhs
    using R by (auto simp: hom_def carrier_subgroup_generated subsetD [OF subG] *)
qed


lemma epi_group_mul_eq:
   "(\<lambda>(x,y). x \<otimes> y) \<in> epi (subgroup_generated G A \<times>\<times> subgroup_generated G B) G
     \<longleftrightarrow> A <#> B = carrier G \<and> (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x)"
proof -
  have subGA: "generate G (carrier G \<inter> A) \<subseteq> A"
    by (simp add: AG.subgroup_axioms generate_subgroup_incl)
  have subGB: "generate G (carrier G \<inter> B) \<subseteq> B"
    by (simp add: BG.subgroup_axioms generate_subgroup_incl)
  have "(((\<lambda>(x, y). x \<otimes> y) ` (generate G (carrier G \<inter> A) \<times> generate G (carrier G \<inter> B)))) = ((A <#> B))"
    by (auto simp: set_mult_def generate.incl pair_imageI dest: subsetD [OF subGA] subsetD [OF subGB])
  then show ?thesis
    by (auto simp: epi_def hom_group_mul_eq carrier_subgroup_generated)
qed

lemma mon_group_mul_eq:
    "(\<lambda>(x,y). x \<otimes> y) \<in> mon (subgroup_generated G A \<times>\<times> subgroup_generated G B) G
     \<longleftrightarrow> A \<inter> B = {\<one>} \<and> (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x)"
proof -
  have subGA: "generate G (carrier G \<inter> A) \<subseteq> A"
    by (simp add: AG.subgroup_axioms generate_subgroup_incl)
  have subGB: "generate G (carrier G \<inter> B) \<subseteq> B"
    by (simp add: BG.subgroup_axioms generate_subgroup_incl)
  show ?thesis
    apply (auto simp: mon_def hom_group_mul_eq simp flip: subset_one)
     apply (simp_all (no_asm_use) add: inj_on_def AG.carrier_subgroup_generated_subgroup BG.carrier_subgroup_generated_subgroup)
    using cancel apply blast+
    done
qed

lemma iso_group_mul_alt:
    "(\<lambda>(x,y). x \<otimes> y) \<in> iso (subgroup_generated G A \<times>\<times> subgroup_generated G B) G
     \<longleftrightarrow> A \<inter> B = {\<one>} \<and> A <#> B = carrier G \<and> (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x)"
  by (auto simp: iso_iff_mon_epi mon_group_mul_eq epi_group_mul_eq)

lemma iso_group_mul_eq:
    "(\<lambda>(x,y). x \<otimes> y) \<in> iso (subgroup_generated G A \<times>\<times> subgroup_generated G B) G
     \<longleftrightarrow> A \<inter> B = {\<one>} \<and> A <#> B = carrier G \<and> A \<lhd> G \<and> B \<lhd> G"
  by (simp add: iso_group_mul_alt normal_eq_commuting cong: conj_cong)


lemma (in group) iso_group_mul_gen:
  assumes "A \<lhd> G" "B \<lhd> G"
  shows "(\<lambda>(x,y). x \<otimes> y) \<in> iso (subgroup_generated G A \<times>\<times> subgroup_generated G B) G
     \<longleftrightarrow> A \<inter> B \<subseteq> {\<one>} \<and> A <#> B = carrier G"
proof -
  interpret group_disjoint_sum G A B
    using assms by (auto simp: group_disjoint_sum_def normal_def)
  show ?thesis
    by (simp add: subset_one iso_group_mul_eq assms)
qed


lemma iso_group_mul:
  assumes "comm_group G"
  shows "((\<lambda>(x,y). x \<otimes> y) \<in> iso (DirProd (subgroup_generated G A) (subgroup_generated G B)) G
     \<longleftrightarrow> A \<inter> B \<subseteq> {\<one>} \<and> A <#> B = carrier G)"
proof (rule iso_group_mul_gen)
  interpret comm_group
    by (rule assms)
  show "A \<lhd> G"
    by (simp add: AG.subgroup_axioms subgroup_imp_normal)
  show "B \<lhd> G"
    by (simp add: BG.subgroup_axioms subgroup_imp_normal)
qed

end


subsection\<open>The one-element group on a given object\<close>

definition singleton_group :: "'a \<Rightarrow> 'a monoid"
  where "singleton_group a = \<lparr>carrier = {a}, monoid.mult = (\<lambda>x y. a), one = a\<rparr>"

lemma singleton_group [simp]: "group (singleton_group a)"
  unfolding singleton_group_def by (auto intro: groupI)

lemma singleton_abelian_group [simp]: "comm_group (singleton_group a)"
  by (metis group.group_comm_groupI monoid.simps(1) singleton_group singleton_group_def)

lemma carrier_singleton_group [simp]: "carrier (singleton_group a) = {a}"
  by (auto simp: singleton_group_def)

lemma (in group) hom_into_singleton_iff [simp]:
  "h \<in> hom G (singleton_group a) \<longleftrightarrow> h \<in> carrier G \<rightarrow> {a}"
  by (auto simp: hom_def singleton_group_def)

declare group.hom_into_singleton_iff [simp]

lemma (in group) id_hom_singleton: "id \<in> hom (singleton_group \<one>) G"
  by (simp add: hom_def singleton_group_def)

subsection\<open>Similarly, trivial groups\<close>

definition trivial_group :: "('a, 'b) monoid_scheme \<Rightarrow> bool"
  where "trivial_group G \<equiv> group G \<and> carrier G = {one G}"

lemma trivial_imp_finite_group:
   "trivial_group G \<Longrightarrow> finite(carrier G)"
  by (simp add: trivial_group_def)

lemma trivial_singleton_group [simp]: "trivial_group(singleton_group a)"
  by (metis monoid.simps(2) partial_object.simps(1) singleton_group singleton_group_def trivial_group_def)

lemma (in group) trivial_group_subset:
   "trivial_group G \<longleftrightarrow> carrier G \<subseteq> {one G}"
  using is_group trivial_group_def by fastforce

lemma (in group) trivial_group: "trivial_group G \<longleftrightarrow> (\<exists>a. carrier G = {a})"
  unfolding trivial_group_def using one_closed is_group by fastforce

lemma (in group) trivial_group_alt:
   "trivial_group G \<longleftrightarrow> (\<exists>a. carrier G \<subseteq> {a})"
  by (auto simp: trivial_group)

lemma (in group) trivial_group_subgroup_generated:
  assumes "S \<subseteq> {one G}"
  shows "trivial_group(subgroup_generated G S)"
proof -
  have "carrier (subgroup_generated G S) \<subseteq> {\<one>}"
    using generate_empty generate_one subset_singletonD assms
    by (fastforce simp add: carrier_subgroup_generated)
  then show ?thesis
    by (simp add: group.trivial_group_subset)
qed

lemma (in group) trivial_group_subgroup_generated_eq:
  "trivial_group(subgroup_generated G s) \<longleftrightarrow> carrier G \<inter> s \<subseteq> {one G}"
  apply (rule iffI)
   apply (force simp: trivial_group_def carrier_subgroup_generated generate.incl)
  by (metis subgroup_generated_restrict trivial_group_subgroup_generated)

lemma isomorphic_group_triviality1:
  assumes "G \<cong> H" "group H" "trivial_group G"
  shows "trivial_group H"
  using assms
  by (auto simp: trivial_group_def is_iso_def iso_def group.is_monoid Group.group_def bij_betw_def hom_one)

lemma isomorphic_group_triviality:
  assumes "G \<cong> H" "group G" "group H"
  shows "trivial_group G \<longleftrightarrow> trivial_group H"
  by (meson assms group.iso_sym isomorphic_group_triviality1)

lemma (in group_hom) kernel_from_trivial_group:
   "trivial_group G \<Longrightarrow> kernel G H h = carrier G"
  by (auto simp: trivial_group_def kernel_def)

lemma (in group_hom) image_from_trivial_group:
   "trivial_group G \<Longrightarrow> h ` carrier G = {one H}"
  by (auto simp: trivial_group_def)

lemma (in group_hom) kernel_to_trivial_group:
   "trivial_group H \<Longrightarrow> kernel G H h = carrier G"
  unfolding kernel_def trivial_group_def
  using hom_closed by blast


subsection\<open>The additive group of integers\<close>

definition integer_group
  where "integer_group = \<lparr>carrier = UNIV, monoid.mult = (+), one = (0::int)\<rparr>"

lemma group_integer_group [simp]: "group integer_group"
  unfolding integer_group_def
proof (rule groupI; simp)
  show "\<And>x::int. \<exists>y. y + x = 0"
  by presburger
qed

lemma carrier_integer_group [simp]: "carrier integer_group = UNIV"
  by (auto simp: integer_group_def)

lemma one_integer_group [simp]: "\<one>\<^bsub>integer_group\<^esub> = 0"
  by (auto simp: integer_group_def)

lemma mult_integer_group [simp]: "x \<otimes>\<^bsub>integer_group\<^esub> y = x + y"
  by (auto simp: integer_group_def)

lemma inv_integer_group [simp]: "inv\<^bsub>integer_group\<^esub> x = -x"
  by (rule group.inv_equality [OF group_integer_group]) (auto simp: integer_group_def)

lemma abelian_integer_group: "comm_group integer_group"
  by (rule group.group_comm_groupI [OF group_integer_group]) (auto simp: integer_group_def)

lemma group_nat_pow_integer_group [simp]:
  fixes n::nat and x::int
  shows "pow integer_group x n = int n * x"
  by (induction n) (auto simp: integer_group_def algebra_simps)

lemma group_int_pow_integer_group [simp]:
  fixes n::int and x::int
  shows "pow integer_group x n = n * x"
  by (simp add: int_pow_def2)

lemma (in group) hom_integer_group_pow:
   "x \<in> carrier G \<Longrightarrow> pow G x \<in> hom integer_group G"
  by (rule homI) (auto simp: int_pow_mult)

end
