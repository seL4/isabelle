(*  Title:      HOL/Algebra/Solvable_Groups.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Solvable_Groups
  imports Generated_Groups
    
begin

section \<open>Solvable Groups\<close>

subsection \<open>Definitions\<close>

inductive solvable_seq :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> bool"
  for G where
    unity: "solvable_seq G { \<one>\<^bsub>G\<^esub> }"
  | extension: "\<lbrakk> solvable_seq G K; K \<lhd> (G \<lparr> carrier := H \<rparr>); subgroup H G;
                  comm_group ((G \<lparr> carrier := H \<rparr>) Mod K) \<rbrakk> \<Longrightarrow> solvable_seq G H"

definition solvable :: "('a, 'b) monoid_scheme \<Rightarrow> bool"
  where "solvable G \<longleftrightarrow> solvable_seq G (carrier G)"


subsection \<open>Solvable Groups and Derived Subgroups\<close>

text \<open>We show that a group G is solvable iff the subgroup (derived G ^^ n) (carrier G)
      is trivial for a sufficiently large n. \<close>

lemma (in group) solvable_imp_subgroup:
  assumes "solvable_seq G H" shows "subgroup H G"
  using assms normal.axioms(1)[OF one_is_normal] by (induction) (auto)

lemma (in group) augment_solvable_seq:
  assumes "subgroup H G" and "solvable_seq G (derived G H)" shows "solvable_seq G H"
  using extension[OF _ derived_subgroup_is_normal _ derived_quot_of_subgroup_is_comm_group] assms by simp

theorem (in group) trivial_derived_seq_imp_solvable:
  assumes "subgroup H G" and "((derived G) ^^ n) H = { \<one> }" shows "solvable_seq G H"
  using assms
proof (induct n arbitrary: H, simp add: unity[of G])
  case (Suc n) thus ?case
    using augment_solvable_seq derived_is_subgroup[OF subgroup.subset] by (simp add: funpow_swap1)
qed

theorem (in group) solvable_imp_trivial_derived_seq:
  assumes "solvable_seq G H" shows "\<exists>n. (derived G ^^ n) H = { \<one> }"
  using assms
proof (induction)
  case unity
  have "(derived G ^^ 0) { \<one> } = { \<one> }"
    by simp
  thus ?case by blast
next
  case (extension K H)
  obtain n where "(derived G ^^ n) K = { \<one> }"
    using solvable_imp_subgroup extension(1,5) by auto
  hence "(derived G ^^ (Suc n)) H \<subseteq> { \<one> }"
    using mono_exp_of_derived[OF derived_of_subgroup_minimal[OF extension(2-4)], of n] by (simp add: funpow_swap1)
  moreover have "{ \<one> } \<subseteq> (derived G ^^ (Suc n)) H"
    using subgroup.one_closed[OF exp_of_derived_is_subgroup[OF extension(3)], of "Suc n"] by auto
  ultimately show ?case
    by blast
qed

theorem (in group) solvable_iff_trivial_derived_seq:
  "solvable G \<longleftrightarrow> (\<exists>n. (derived G ^^ n) (carrier G) = { \<one> })"
  using solvable_imp_trivial_derived_seq subgroup_self trivial_derived_seq_imp_solvable
  by (auto simp add: solvable_def)

corollary (in group) solvable_subgroup:
  assumes "subgroup H G" and "solvable G" shows "solvable_seq G H"
proof -
  obtain n where n: "(derived G ^^ n) (carrier G) = { \<one> }"
    using assms(2) solvable_imp_trivial_derived_seq by (auto simp add: solvable_def)
  show ?thesis
  proof (rule trivial_derived_seq_imp_solvable[OF assms(1), of n])
    show "(derived G ^^ n) H = { \<one> }"
      using subgroup.one_closed[OF exp_of_derived_is_subgroup[OF assms(1)], of n]
            mono_exp_of_derived[OF subgroup.subset[OF assms(1)], of n] n
      by auto
  qed
qed


subsection \<open>Short Exact Sequences\<close>

text \<open>Even if we don't talk about short exact sequences explicitly, we show that given an
      injective homomorphism from a group H to a group G, if H isn't solvable the group G
      isn't neither. \<close>

theorem (in group_hom) solvable_img_imp_solvable:
  assumes "subgroup K G" and "inj_on h K" and "solvable_seq H (h ` K)" shows "solvable_seq G K"
proof -
  obtain n where "(derived H ^^ n) (h ` K) = { \<one>\<^bsub>H\<^esub> }"
    using solvable_imp_trivial_derived_seq assms(1,3) by auto
  hence "h ` ((derived G ^^ n) K) = { \<one>\<^bsub>H\<^esub> }"
    unfolding exp_of_derived_img[OF subgroup.subset[OF assms(1)]] .
  moreover have "(derived G ^^ n) K \<subseteq> K"
    using G.mono_derived[of _ K] G.derived_incl[OF _ assms(1)] by (induct n) (auto)
  hence "inj_on h ((derived G ^^ n) K)"
    using inj_on_subset[OF assms(2)] by blast
  moreover have "{ \<one> } \<subseteq> (derived G ^^ n) K"
    using subgroup.one_closed[OF G.exp_of_derived_is_subgroup[OF assms(1)]] by blast
  ultimately show ?thesis
    using G.trivial_derived_seq_imp_solvable[OF assms(1), of n]
    by (metis (no_types, lifting) hom_one image_empty image_insert inj_on_image_eq_iff order_refl)
qed

corollary (in group_hom) inj_hom_imp_solvable:
  assumes "inj_on h (carrier G)" and "solvable H" shows "solvable G"
  using solvable_img_imp_solvable[OF _ assms(1)] G.subgroup_self
        solvable_subgroup[OF subgroup_img_is_subgroup assms(2)]
  unfolding solvable_def
  by simp

theorem (in group_hom) solvable_imp_solvable_img:
  assumes "solvable_seq G K" shows "solvable_seq H (h ` K)"
proof -
  obtain n where "(derived G ^^ n) K = { \<one> }"
    using G.solvable_imp_trivial_derived_seq[OF assms] by blast
  thus ?thesis
    using trivial_derived_seq_imp_solvable[OF subgroup_img_is_subgroup, of _ n]
          exp_of_derived_img[OF subgroup.subset, of _ n] G.solvable_imp_subgroup[OF assms]
    by auto
qed

corollary (in group_hom) surj_hom_imp_solvable:
  assumes "h ` carrier G = carrier H" and "solvable G" shows "solvable H"
  using assms solvable_imp_solvable_img[of "carrier G"] unfolding solvable_def by simp

lemma solvable_seq_condition:
  assumes "group_hom G H f" "group_hom H K g" and "f ` I \<subseteq> J" and "kernel H K g \<subseteq> f ` I"
    and "subgroup J H" and "solvable_seq G I" "solvable_seq K (g ` J)"
  shows "solvable_seq H J"
proof -
  interpret G: group G + H: group H + K: group K + J: subgroup J H + I: subgroup I G
    using assms(1-2,5) group.solvable_imp_subgroup[OF _ assms(6)] unfolding group_hom_def by auto

  obtain n m
    where n: "(derived G ^^ n) I = { \<one>\<^bsub>G\<^esub> }" and m: "(derived K ^^ m) (g ` J) = { \<one>\<^bsub>K\<^esub> }"
    using G.solvable_imp_trivial_derived_seq[OF assms(6)]
          K.solvable_imp_trivial_derived_seq[OF assms(7)]
    by auto
  have "(derived H ^^ m) J \<subseteq> f ` I"
    using m H.exp_of_derived_in_carrier[OF J.subset, of m] assms(4)
    by (auto simp add: group_hom.exp_of_derived_img[OF assms(2) J.subset] kernel_def)
  hence "(derived H ^^ n) ((derived H ^^ m) J) \<subseteq> f ` ((derived G ^^ n) I)"
    using n H.mono_exp_of_derived unfolding sym[OF group_hom.exp_of_derived_img[OF assms(1) I.subset, of n]] by simp
  hence "(derived H ^^ (n + m)) J \<subseteq> { \<one>\<^bsub>H\<^esub> }"
    using group_hom.hom_one[OF assms(1)] unfolding n by (simp add: funpow_add)
  moreover have "{ \<one>\<^bsub>H\<^esub> } \<subseteq> (derived H ^^ (n + m)) J"
    using subgroup.one_closed[OF H.exp_of_derived_is_subgroup[OF assms(5), of "n + m"]] by blast
  ultimately show ?thesis
    using H.trivial_derived_seq_imp_solvable[OF assms(5)] by simp
qed

lemma solvable_condition:
  assumes "group_hom G H f" "group_hom H K g"
    and "g ` (carrier H) = carrier K" and "kernel H K g \<subseteq> f ` (carrier G)"
    and "solvable G" "solvable K" shows "solvable H"
  using solvable_seq_condition[OF assms(1-2) _ assms(4) group.subgroup_self] assms(3,5-6)
        subgroup.subset[OF group_hom.img_is_subgroup[OF assms(1)]] group_hom.axioms(2)[OF assms(1)]
  by (simp add: solvable_def)

end