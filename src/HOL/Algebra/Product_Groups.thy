(*  Title:      HOL/Algebra/Product_Groups.thy
    Author:     LC Paulson (ported from HOL Light)
*)

section \<open>Product and Sum Groups\<close>

theory Product_Groups
  imports Elementary_Groups "HOL-Library.Equipollence" 
  
begin

subsection \<open>Product of a Family of Groups\<close>

definition product_group:: "'a set \<Rightarrow> ('a \<Rightarrow> ('b, 'c) monoid_scheme) \<Rightarrow> ('a \<Rightarrow> 'b) monoid"
  where "product_group I G \<equiv> \<lparr>carrier = (\<Pi>\<^sub>E i\<in>I. carrier (G i)),
                              monoid.mult = (\<lambda>x y. (\<lambda>i\<in>I. x i \<otimes>\<^bsub>G i\<^esub> y i)),
                              one = (\<lambda>i\<in>I. \<one>\<^bsub>G i\<^esub>)\<rparr>"

lemma carrier_product_group [simp]: "carrier(product_group I G) = (\<Pi>\<^sub>E i\<in>I. carrier (G i))"
  by (simp add: product_group_def)

lemma one_product_group [simp]: "one(product_group I G) = (\<lambda>i\<in>I. one (G i))"
  by (simp add: product_group_def)

lemma mult_product_group [simp]: "(\<otimes>\<^bsub>product_group I G\<^esub>) = (\<lambda>x y. \<lambda>i\<in>I. x i \<otimes>\<^bsub>G i\<^esub> y i)"
  by (simp add: product_group_def)

lemma product_group [simp]:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)" shows "group (product_group I G)"
proof (rule groupI; simp)
  show "(\<lambda>i. x i \<otimes>\<^bsub>G i\<^esub> y i) \<in> (\<Pi> i\<in>I. carrier (G i))"
    if "x \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))" "y \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))" for x y
    using that assms group.subgroup_self subgroup.m_closed by fastforce
  show "(\<lambda>i. \<one>\<^bsub>G i\<^esub>) \<in> (\<Pi> i\<in>I. carrier (G i))"
    by (simp add: assms group.is_monoid)
  show "(\<lambda>i\<in>I. (if i \<in> I then x i \<otimes>\<^bsub>G i\<^esub> y i else undefined) \<otimes>\<^bsub>G i\<^esub> z i) =
        (\<lambda>i\<in>I. x i \<otimes>\<^bsub>G i\<^esub> (if i \<in> I then y i \<otimes>\<^bsub>G i\<^esub> z i else undefined))"
    if "x \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))" "y \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))" "z \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))" for x y z
    using that  by (auto simp: PiE_iff assms group.is_monoid monoid.m_assoc intro: restrict_ext)
  show "(\<lambda>i\<in>I. (if i \<in> I then \<one>\<^bsub>G i\<^esub> else undefined) \<otimes>\<^bsub>G i\<^esub> x i) = x"
    if "x \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))" for x
    using assms that by (fastforce simp: Group.group_def PiE_iff)
  show "\<exists>y\<in>\<Pi>\<^sub>E i\<in>I. carrier (G i). (\<lambda>i\<in>I. y i \<otimes>\<^bsub>G i\<^esub> x i) = (\<lambda>i\<in>I. \<one>\<^bsub>G i\<^esub>)"
    if "x \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))" for x
    by (rule_tac x="\<lambda>i\<in>I. inv\<^bsub>G i\<^esub> x i" in bexI) (use assms that in \<open>auto simp: PiE_iff group.l_inv\<close>)
qed

lemma inv_product_group [simp]:
  assumes "f \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))" "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows "inv\<^bsub>product_group I G\<^esub> f = (\<lambda>i\<in>I. inv\<^bsub>G i\<^esub> f i)"
proof (rule group.inv_equality)
  show "Group.group (product_group I G)"
    by (simp add: assms)
  show "(\<lambda>i\<in>I. inv\<^bsub>G i\<^esub> f i) \<otimes>\<^bsub>product_group I G\<^esub> f = \<one>\<^bsub>product_group I G\<^esub>"
    using assms by (auto simp: PiE_iff group.l_inv)
  show "f \<in> carrier (product_group I G)"
    using assms by simp
  show "(\<lambda>i\<in>I. inv\<^bsub>G i\<^esub> f i) \<in> carrier (product_group I G)"
    using PiE_mem assms by fastforce
qed


lemma trivial_product_group: "trivial_group(product_group I G) \<longleftrightarrow> (\<forall>i \<in> I. trivial_group(G i))"
 (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then have "inv\<^bsub>product_group I G\<^esub> (\<lambda>a\<in>I. \<one>\<^bsub>G a\<^esub>) = \<one>\<^bsub>product_group I G\<^esub>"
    by (metis group.is_monoid monoid.inv_one one_product_group trivial_group_def)
  have [simp]: "\<one>\<^bsub>G i\<^esub> \<otimes>\<^bsub>G i\<^esub> \<one>\<^bsub>G i\<^esub> = \<one>\<^bsub>G i\<^esub>" if "i \<in> I" for i
    unfolding trivial_group_def
  proof -
    have 1: "(\<lambda>a\<in>I. \<one>\<^bsub>G a\<^esub>) i = \<one>\<^bsub>G i\<^esub>"
      by (simp add: that)
    have "(\<lambda>a\<in>I. \<one>\<^bsub>G a\<^esub>) = (\<lambda>a\<in>I. \<one>\<^bsub>G a\<^esub>) \<otimes>\<^bsub>product_group I G\<^esub> (\<lambda>a\<in>I. \<one>\<^bsub>G a\<^esub>)"
      by (metis (no_types) L group.is_monoid monoid.l_one one_product_group singletonI trivial_group_def)
    then show ?thesis
      using 1 by (simp add: that)
  qed
  show ?rhs
    using L
    by (auto simp: trivial_group_def product_group_def PiE_eq_singleton intro: groupI)
next
  assume ?rhs
  then show ?lhs
    by (simp add: PiE_eq_singleton trivial_group_def)
qed


lemma PiE_subgroup_product_group:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows "subgroup (PiE I H) (product_group I G) \<longleftrightarrow> (\<forall>i \<in> I. subgroup (H i) (G i))"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then have [simp]: "PiE I H \<noteq> {}"
    using subgroup_nonempty by force
  show ?rhs
  proof (clarify; unfold_locales)
    show sub: "H i \<subseteq> carrier (G i)" if "i \<in> I" for i
      using that L by (simp add: subgroup_def) (metis (no_types, lifting) L subgroup_nonempty subset_PiE)
    show "x \<otimes>\<^bsub>G i\<^esub> y \<in> H i" if "i \<in> I" "x \<in> H i" "y \<in> H i" for i x y
    proof -
      have *: "\<And>x. x \<in> Pi\<^sub>E I H \<Longrightarrow> (\<forall>y \<in> Pi\<^sub>E I H. \<forall>i\<in>I. x i \<otimes>\<^bsub>G i\<^esub> y i \<in> H i)"
        using L by (auto simp: subgroup_def Pi_iff)
      have "\<forall>y\<in>H i. f i \<otimes>\<^bsub>G i\<^esub> y \<in> H i" if f: "f \<in> Pi\<^sub>E I H" and "i \<in> I" for i f
        using * [OF f] \<open>i \<in> I\<close>
        by (subst(asm) all_PiE_elements) auto
      then have "\<forall>f \<in> Pi\<^sub>E I H. \<forall>i \<in> I. \<forall>y\<in>H i. f i \<otimes>\<^bsub>G i\<^esub> y \<in> H i"
        by blast
      with that show ?thesis
        by (subst(asm) all_PiE_elements) auto
    qed
    show "\<one>\<^bsub>G i\<^esub> \<in> H i" if "i \<in> I" for i
      using L subgroup.one_closed that by fastforce
    show "inv\<^bsub>G i\<^esub> x \<in> H i" if "i \<in> I" and x: "x \<in> H i" for i x
    proof -
      have *: "\<forall>y \<in> Pi\<^sub>E I H. \<forall>i\<in>I. inv\<^bsub>G i\<^esub> y i \<in> H i"
      proof
        fix y
        assume y: "y \<in> Pi\<^sub>E I H"
        then have yc: "y \<in> carrier (product_group I G)"
          by (metis (no_types) L subgroup_def subsetCE)
        have "inv\<^bsub>product_group I G\<^esub> y \<in> Pi\<^sub>E I H"
          by (simp add: y L subgroup.m_inv_closed)
        moreover have "inv\<^bsub>product_group I G\<^esub> y = (\<lambda>i\<in>I. inv\<^bsub>G i\<^esub> y i)"
          using yc by (simp add: assms)
        ultimately show "\<forall>i\<in>I. inv\<^bsub>G i\<^esub> y i \<in> H i"
          by auto
      qed
      then have "\<forall>i\<in>I. \<forall>x\<in>H i. inv\<^bsub>G i\<^esub> x \<in> H i"
        by (subst(asm) all_PiE_elements) auto
      then show ?thesis
        using that(1) x by blast
    qed
  qed
next
  assume R: ?rhs
  show ?lhs
  proof
    show "Pi\<^sub>E I H \<subseteq> carrier (product_group I G)"
      using R by (force simp: subgroup_def)
    show "x \<otimes>\<^bsub>product_group I G\<^esub> y \<in> Pi\<^sub>E I H" if "x \<in> Pi\<^sub>E I H" "y \<in> Pi\<^sub>E I H" for x y
      using R that by (auto simp: PiE_iff subgroup_def)
    show "\<one>\<^bsub>product_group I G\<^esub> \<in> Pi\<^sub>E I H"
      using R by (force simp: subgroup_def)
    show "inv\<^bsub>product_group I G\<^esub> x \<in> Pi\<^sub>E I H" if "x \<in> Pi\<^sub>E I H" for x
    proof -
      have x: "x \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))"
        using R that by (force simp:  subgroup_def)
      show ?thesis
        using assms R that by (fastforce simp: x assms subgroup_def)
    qed
  qed
qed

lemma product_group_subgroup_generated:
  assumes "\<And>i. i \<in> I \<Longrightarrow> subgroup (H i) (G i)" and gp: "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows "product_group I (\<lambda>i. subgroup_generated (G i) (H i))
       = subgroup_generated (product_group I G) (PiE I H)"
proof (rule monoid.equality)
  have [simp]: "\<And>i. i \<in> I \<Longrightarrow> carrier (G i) \<inter> H i = H i" "(\<Pi>\<^sub>E i\<in>I. carrier (G i)) \<inter> Pi\<^sub>E I H = Pi\<^sub>E I H"
    using assms by (force simp: subgroup_def)+
  have "(\<Pi>\<^sub>E i\<in>I. generate (G i) (H i)) = generate (product_group I G) (Pi\<^sub>E I H)"
  proof (rule group.generateI)
    show "Group.group (product_group I G)"
      using assms by simp
    show "subgroup (\<Pi>\<^sub>E i\<in>I. generate (G i) (H i)) (product_group I G)"
      using assms by (simp add: PiE_subgroup_product_group group.generate_is_subgroup subgroup.subset)
    show "Pi\<^sub>E I H \<subseteq> (\<Pi>\<^sub>E i\<in>I. generate (G i) (H i))"
      using assms by (auto simp: PiE_iff generate.incl)
    show "(\<Pi>\<^sub>E i\<in>I. generate (G i) (H i)) \<subseteq> K"
      if "subgroup K (product_group I G)" "Pi\<^sub>E I H \<subseteq> K" for K
      using assms that group.generate_subgroup_incl by fastforce
  qed
  with assms
  show "carrier (product_group I (\<lambda>i. subgroup_generated (G i) (H i))) =
        carrier (subgroup_generated (product_group I G) (Pi\<^sub>E I H))"
    by (simp add: carrier_subgroup_generated cong: PiE_cong)
qed auto

lemma finite_product_group:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows
   "finite (carrier (product_group I G)) \<longleftrightarrow>
    finite {i. i \<in> I \<and> ~ trivial_group(G i)} \<and> (\<forall>i \<in> I. finite(carrier(G i)))"
proof -
  have [simp]: "\<And>i. i \<in> I \<Longrightarrow> carrier (G i) \<noteq> {}"
    using assms group.is_monoid by blast
  show ?thesis
    by (auto simp: finite_PiE_iff PiE_eq_empty_iff group.trivial_group_alt [OF assms] cong: Collect_cong conj_cong)
qed

subsection \<open>Sum of a Family of Groups\<close>

definition sum_group :: "'a set \<Rightarrow> ('a \<Rightarrow> ('b, 'c) monoid_scheme) \<Rightarrow> ('a \<Rightarrow> 'b) monoid"
  where "sum_group I G \<equiv>
        subgroup_generated
         (product_group I G)
         {x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}}"

lemma subgroup_sum_group:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows "subgroup {x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}}
                  (product_group I G)"
proof unfold_locales
  fix x y
  have *: "{i. (i \<in> I \<longrightarrow> x i \<otimes>\<^bsub>G i\<^esub> y i \<noteq> \<one>\<^bsub>G i\<^esub>) \<and> i \<in> I}
        \<subseteq> {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>} \<union> {i \<in> I. y i \<noteq> \<one>\<^bsub>G i\<^esub>}"
    by (auto simp: Group.group_def dest: assms)
  assume
    "x \<in> {x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}}"
    "y \<in> {x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}}"
  then
  show "x \<otimes>\<^bsub>product_group I G\<^esub> y \<in> {x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}}"
    using assms
    apply (auto simp: Group.group_def monoid.m_closed PiE_iff)
    apply (rule finite_subset [OF *])
    by blast
next
  fix x
  assume "x \<in> {x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}}"
  then show "inv\<^bsub>product_group I G\<^esub> x \<in> {x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}}"
    using assms
    by (auto simp: PiE_iff assms group.inv_eq_1_iff [OF assms] conj_commute cong: rev_conj_cong)
qed (use assms [unfolded Group.group_def] in auto)

lemma carrier_sum_group:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows "carrier(sum_group I G) = {x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}}"
proof -
  interpret SG: subgroup "{x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}}" "(product_group I G)"
    by (simp add: assms subgroup_sum_group)
  show ?thesis
    by (simp add: sum_group_def subgroup_sum_group carrier_subgroup_generated_alt)
qed

lemma one_sum_group [simp]: "\<one>\<^bsub>sum_group I G\<^esub> = (\<lambda>i\<in>I. \<one>\<^bsub>G i\<^esub>)"
  by (simp add: sum_group_def)

lemma mult_sum_group [simp]: "(\<otimes>\<^bsub>sum_group I G\<^esub>) = (\<lambda>x y. (\<lambda>i\<in>I. x i \<otimes>\<^bsub>G i\<^esub> y i))"
  by (auto simp: sum_group_def)

lemma sum_group [simp]:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)" shows "group (sum_group I G)"
proof (rule groupI)
  note group.is_monoid [OF assms, simp]
  show "x \<otimes>\<^bsub>sum_group I G\<^esub> y \<in> carrier (sum_group I G)"
    if "x \<in> carrier (sum_group I G)" and
      "y \<in> carrier (sum_group I G)" for x y
  proof -
    have *: "{i \<in> I. x i \<otimes>\<^bsub>G i\<^esub> y i \<noteq> \<one>\<^bsub>G i\<^esub>} \<subseteq> {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>} \<union> {i \<in> I. y i \<noteq> \<one>\<^bsub>G i\<^esub>}"
      by auto
    show ?thesis
      using that
      apply (simp add: assms carrier_sum_group PiE_iff monoid.m_closed conj_commute cong: rev_conj_cong)
      apply (blast intro: finite_subset [OF *])
      done
  qed
  show "\<one>\<^bsub>sum_group I G\<^esub> \<otimes>\<^bsub>sum_group I G\<^esub> x = x"
    if "x \<in> carrier (sum_group I G)" for x
    using that by (auto simp: assms carrier_sum_group PiE_iff extensional_def)
  show "\<exists>y\<in>carrier (sum_group I G). y \<otimes>\<^bsub>sum_group I G\<^esub> x = \<one>\<^bsub>sum_group I G\<^esub>"
    if "x \<in> carrier (sum_group I G)" for x
  proof
    let ?y = "\<lambda>i\<in>I. m_inv (G i) (x i)"
    show "?y \<otimes>\<^bsub>sum_group I G\<^esub> x = \<one>\<^bsub>sum_group I G\<^esub>"
      using that assms
      by (auto simp: carrier_sum_group PiE_iff group.l_inv)
    show "?y \<in> carrier (sum_group I G)"
      using that assms
      by (auto simp: carrier_sum_group PiE_iff group.inv_eq_1_iff group.l_inv cong: conj_cong)
  qed
qed (auto simp: assms carrier_sum_group PiE_iff group.is_monoid monoid.m_assoc)

lemma inv_sum_group [simp]:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)" and x: "x \<in> carrier (sum_group I G)"
  shows "m_inv (sum_group I G) x = (\<lambda>i\<in>I. m_inv (G i) (x i))"
proof (rule group.inv_equality)
  show "(\<lambda>i\<in>I. inv\<^bsub>G i\<^esub> x i) \<otimes>\<^bsub>sum_group I G\<^esub> x = \<one>\<^bsub>sum_group I G\<^esub>"
    using x by (auto simp: carrier_sum_group PiE_iff group.l_inv assms intro: restrict_ext)
  show "(\<lambda>i\<in>I. inv\<^bsub>G i\<^esub> x i) \<in> carrier (sum_group I G)"
    using x by (simp add: carrier_sum_group PiE_iff group.inv_eq_1_iff assms conj_commute cong: rev_conj_cong)
qed (auto simp: assms)


thm group.subgroups_Inter (*REPLACE*)
theorem subgroup_Inter:
  assumes subgr: "(\<And>H. H \<in> A \<Longrightarrow> subgroup H G)"
    and not_empty: "A \<noteq> {}"
  shows "subgroup (\<Inter>A) G"
proof
  show "\<Inter> A \<subseteq> carrier G"
    by (simp add: Inf_less_eq not_empty subgr subgroup.subset)
qed (auto simp: subgr subgroup.m_closed subgroup.one_closed subgroup.m_inv_closed)

thm group.subgroups_Inter_pair (*REPLACE*)
lemma subgroup_Int:
  assumes "subgroup I G" "subgroup J G"
  shows "subgroup (I \<inter> J) G" using subgroup_Inter[ where ?A = "{I,J}"] assms by auto


lemma sum_group_subgroup_generated:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)" and sg: "\<And>i. i \<in> I \<Longrightarrow> subgroup (H i) (G i)"
  shows "sum_group I (\<lambda>i. subgroup_generated (G i) (H i)) = subgroup_generated (sum_group I G) (PiE I H)"
proof (rule monoid.equality)
  have "subgroup (carrier (sum_group I G) \<inter> Pi\<^sub>E I H) (product_group I G)"
    by (rule subgroup_Int) (auto simp: assms carrier_sum_group subgroup_sum_group PiE_subgroup_product_group)
  moreover have "carrier (sum_group I G) \<inter> Pi\<^sub>E I H
              \<subseteq> carrier (subgroup_generated (product_group I G)
                    {x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}})"
    by (simp add: assms subgroup_sum_group subgroup.carrier_subgroup_generated_subgroup carrier_sum_group)
  ultimately
  have "subgroup (carrier (sum_group I G) \<inter> Pi\<^sub>E I H) (sum_group I G)"
    by (simp add: assms sum_group_def group.subgroup_subgroup_generated_iff)
  then have *: "{f \<in> \<Pi>\<^sub>E i\<in>I. carrier (subgroup_generated (G i) (H i)). finite {i \<in> I. f i \<noteq> \<one>\<^bsub>G i\<^esub>}}
      = carrier (subgroup_generated (sum_group I G) (carrier (sum_group I G) \<inter> Pi\<^sub>E I H))"
    apply (simp only: subgroup.carrier_subgroup_generated_subgroup)
    using subgroup.subset [OF sg]
    apply (auto simp: set_eq_iff PiE_def Pi_def assms carrier_sum_group subgroup.carrier_subgroup_generated_subgroup)
    done
  then show "carrier (sum_group I (\<lambda>i. subgroup_generated (G i) (H i))) =
        carrier (subgroup_generated (sum_group I G) (Pi\<^sub>E I H))"
    by simp (simp add: assms group.subgroupE(1) group.group_subgroup_generated carrier_sum_group)
qed (auto simp: sum_group_def subgroup_generated_def)


lemma iso_product_groupI:
  assumes iso: "\<And>i. i \<in> I \<Longrightarrow> G i \<cong> H i"
    and G: "\<And>i. i \<in> I \<Longrightarrow> group (G i)" and H: "\<And>i. i \<in> I \<Longrightarrow> group (H i)"
  shows "product_group I G \<cong> product_group I H" (is "?IG \<cong> ?IH")
proof -
  have "\<And>i. i \<in> I \<Longrightarrow> \<exists>h. h \<in> iso (G i) (H i)"
    using iso by (auto simp: is_iso_def)
  then obtain f where f: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> iso (G i) (H i)"
    by metis
  define h where "h \<equiv> \<lambda>x. (\<lambda>i\<in>I. f i (x i))"
  have hom: "h \<in> iso ?IG ?IH"
  proof (rule isoI)
    show hom: "h \<in> hom ?IG ?IH"
    proof (rule homI)
      fix x
      assume "x \<in> carrier ?IG"
      with f show "h x \<in> carrier ?IH"
        using PiE by (fastforce simp add: h_def PiE_def iso_def hom_def)
    next
      fix x y
      assume "x \<in> carrier ?IG" "y \<in> carrier ?IG"
      with f show "h (x \<otimes>\<^bsub>?IG\<^esub> y) = h x \<otimes>\<^bsub>?IH\<^esub> h y"
        apply (simp add: h_def PiE_def iso_def hom_def)
        using PiE by (fastforce simp add: h_def PiE_def iso_def hom_def intro: restrict_ext)
    qed
    with G H interpret GH : group_hom "?IG" "?IH" h
      by (simp add: group_hom_def group_hom_axioms_def)
    show "bij_betw h (carrier ?IG) (carrier ?IH)"
      unfolding bij_betw_def
    proof (intro conjI subset_antisym)
      have "\<gamma> i = \<one>\<^bsub>G i\<^esub>"
        if \<gamma>: "\<gamma> \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))" and eq: "(\<lambda>i\<in>I. f i (\<gamma> i)) = (\<lambda>i\<in>I. \<one>\<^bsub>H i\<^esub>)" and "i \<in> I"
        for \<gamma> i
      proof -
        have "inj_on (f i) (carrier (G i))" "f i \<in> hom (G i) (H i)"
          using \<open>i \<in> I\<close> f by (auto simp: iso_def bij_betw_def)
        then have *: "\<And>x. \<lbrakk>f i x = \<one>\<^bsub>H i\<^esub>; x \<in> carrier (G i)\<rbrakk> \<Longrightarrow> x = \<one>\<^bsub>G i\<^esub>"
          by (metis G Group.group_def H hom_one inj_onD monoid.one_closed \<open>i \<in> I\<close>)
        show ?thesis
          using eq \<open>i \<in> I\<close> * \<gamma> by (simp add: fun_eq_iff) (meson PiE_iff)
      qed
      then show "inj_on h (carrier ?IG)"
        apply (simp add: iso_def bij_betw_def GH.inj_on_one_iff flip: carrier_product_group)
        apply (force simp: h_def)
        done
    next
      show "h ` carrier ?IG \<subseteq> carrier ?IH"
        unfolding h_def using f
        by (force simp: PiE_def Pi_def Group.iso_def dest!: bij_betwE)
    next
      show "carrier ?IH \<subseteq> h ` carrier ?IG"
        unfolding h_def
      proof (clarsimp simp: iso_def bij_betw_def)
        fix x
        assume "x \<in> (\<Pi>\<^sub>E i\<in>I. carrier (H i))"
        with f have x: "x \<in> (\<Pi>\<^sub>E i\<in>I. f i ` carrier (G i))"
          unfolding h_def by (auto simp: iso_def bij_betw_def)
        have "\<And>i. i \<in> I \<Longrightarrow> inj_on (f i) (carrier (G i))"
          using f by (auto simp: iso_def bij_betw_def)
        let ?g = "\<lambda>i\<in>I. inv_into (carrier (G i)) (f i) (x i)"
        show "x \<in> (\<lambda>g. \<lambda>i\<in>I. f i (g i)) ` (\<Pi>\<^sub>E i\<in>I. carrier (G i))"
        proof
          show "x = (\<lambda>i\<in>I. f i (?g i))"
            using x by (auto simp: PiE_iff fun_eq_iff extensional_def f_inv_into_f)
          show "?g \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))"
            using x by (auto simp: PiE_iff inv_into_into)
        qed
      qed
    qed
  qed
  then show ?thesis
    using is_iso_def by auto
qed

lemma iso_sum_groupI:
  assumes iso: "\<And>i. i \<in> I \<Longrightarrow> G i \<cong> H i"
    and G: "\<And>i. i \<in> I \<Longrightarrow> group (G i)" and H: "\<And>i. i \<in> I \<Longrightarrow> group (H i)"
  shows "sum_group I G \<cong> sum_group I H" (is "?IG \<cong> ?IH")
proof -
  have "\<And>i. i \<in> I \<Longrightarrow> \<exists>h. h \<in> iso (G i) (H i)"
    using iso by (auto simp: is_iso_def)
  then obtain f where f: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> iso (G i) (H i)"
    by metis
  then have injf: "inj_on (f i) (carrier (G i))"
    and homf: "f i \<in> hom (G i) (H i)" if "i \<in> I" for i
    using \<open>i \<in> I\<close> f by (auto simp: iso_def bij_betw_def)
  then have one: "\<And>x. \<lbrakk>f i x = \<one>\<^bsub>H i\<^esub>; x \<in> carrier (G i)\<rbrakk> \<Longrightarrow> x = \<one>\<^bsub>G i\<^esub>" if "i \<in> I" for i
    by (metis G H group.subgroup_self hom_one inj_on_eq_iff subgroup.one_closed that)
  have fin1: "finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>} \<Longrightarrow> finite {i \<in> I. f i (x i) \<noteq> \<one>\<^bsub>H i\<^esub>}" for x
    using homf by (auto simp: G H hom_one elim!: rev_finite_subset)
  define h where "h \<equiv> \<lambda>x. (\<lambda>i\<in>I. f i (x i))"
  have hom: "h \<in> iso ?IG ?IH"
  proof (rule isoI)
    show hom: "h \<in> hom ?IG ?IH"
    proof (rule homI)
      fix x
      assume "x \<in> carrier ?IG"
      with f fin1 show "h x \<in> carrier ?IH"
        by (force simp: h_def PiE_def iso_def hom_def carrier_sum_group assms conj_commute cong: conj_cong)
    next
      fix x y
      assume "x \<in> carrier ?IG" "y \<in> carrier ?IG"
      with homf show "h (x \<otimes>\<^bsub>?IG\<^esub> y) = h x \<otimes>\<^bsub>?IH\<^esub> h y"
        by (fastforce simp add: h_def PiE_def hom_def carrier_sum_group assms intro: restrict_ext)
    qed
    with G H interpret GH : group_hom "?IG" "?IH" h
      by (simp add: group_hom_def group_hom_axioms_def)
    show "bij_betw h (carrier ?IG) (carrier ?IH)"
      unfolding bij_betw_def
    proof (intro conjI subset_antisym)
      have \<gamma>: "\<gamma> i = \<one>\<^bsub>G i\<^esub>"
        if "\<gamma> \<in> (\<Pi>\<^sub>E i\<in>I. carrier (G i))" and eq: "(\<lambda>i\<in>I. f i (\<gamma> i)) = (\<lambda>i\<in>I. \<one>\<^bsub>H i\<^esub>)" and "i \<in> I"
        for \<gamma> i
        using \<open>i \<in> I\<close> one that by (simp add: fun_eq_iff) (meson PiE_iff)
      show "inj_on h (carrier ?IG)"
        apply (simp add: iso_def bij_betw_def GH.inj_on_one_iff assms one flip: carrier_sum_group)
        apply (auto simp: h_def fun_eq_iff carrier_sum_group assms PiE_def Pi_def extensional_def one)
        done
    next
      show "h ` carrier ?IG \<subseteq> carrier ?IH"
        using homf GH.hom_closed
        by (fastforce simp: h_def PiE_def Pi_def dest!: bij_betwE)
    next
      show "carrier ?IH \<subseteq> h ` carrier ?IG"
        unfolding h_def
      proof (clarsimp simp: iso_def bij_betw_def carrier_sum_group assms)
        fix x
        assume x: "x \<in> (\<Pi>\<^sub>E i\<in>I. carrier (H i))" and fin: "finite {i \<in> I. x i \<noteq> \<one>\<^bsub>H i\<^esub>}"
        with f have xf: "x \<in> (\<Pi>\<^sub>E i\<in>I. f i ` carrier (G i))"
          unfolding h_def
          by (auto simp: iso_def bij_betw_def)
        have "\<And>i. i \<in> I \<Longrightarrow> inj_on (f i) (carrier (G i))"
          using f by (auto simp: iso_def bij_betw_def)
        let ?g = "\<lambda>i\<in>I. inv_into (carrier (G i)) (f i) (x i)"
        show "x \<in> (\<lambda>g. \<lambda>i\<in>I. f i (g i))
                 ` {x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}}"
        proof
          show xeq: "x = (\<lambda>i\<in>I. f i (?g i))"
            using x by (clarsimp simp: PiE_iff fun_eq_iff extensional_def) (metis iso_iff f_inv_into_f f)
          have "finite {i \<in> I. inv_into (carrier (G i)) (f i) (x i) \<noteq> \<one>\<^bsub>G i\<^esub>}"
            apply (rule finite_subset [OF _ fin])
            using G H group.subgroup_self hom_one homf injf inv_into_f_eq subgroup.one_closed by fastforce
          with x show "?g \<in> {x \<in> \<Pi>\<^sub>E i\<in>I. carrier (G i). finite {i \<in> I. x i \<noteq> \<one>\<^bsub>G i\<^esub>}}"
            apply (auto simp: PiE_iff inv_into_into conj_commute cong: conj_cong)
            by (metis (no_types, opaque_lifting) iso_iff f inv_into_into)
        qed
      qed
    qed
  qed
  then show ?thesis
    using is_iso_def by auto
qed

end
