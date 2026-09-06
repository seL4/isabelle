section \<open>A normal solvable tower has a solvable Galois group\<close>

theory Galois_Solvable_Tower
  imports Complex_Field_Extension Galois_Action Galois_Restriction_Core
begin

text \<open>Given a fixed complex splitting field @{term K} and a chain
  of intermediate fields \<open>F = F\<^sub>0 \<subseteq> F\<^sub>1 \<subseteq> \<dots> \<subseteq> F\<^sub>n = K\<close> in which each \<open>F\<^sub>i\<close> is \<^emph>\<open>stable\<close> under
  @{term "field_auto K F"} and each step's relative Galois group \<open>field_auto F\<^sub>i\<^sub>+\<^sub>1 F\<^sub>i\<close> is
  solvable, the whole Galois group @{term "field_auto K F"} is solvable.  This chains the inductive
  step @{thm [source] galois_solvable_tower_step} down the tower, the base case being the trivial
  group @{term "field_auto K K"}.\<close>

subsection \<open>The trivial Galois group\<close>

text \<open>An automorphism of @{term K} fixing all of @{term K} is the identity, so @{term "field_auto K K"}
  is trivial.\<close>
lemma field_auto_self_trivial:
  fixes K :: "complex set"
  assumes K: "Subfield K"
  shows "field_auto K K = {identity K}"
proof -
  have cK: "complex_subfield K" using K by (simp add: complex_subfield_iff_subfield)
  have "\<sigma> \<in> {identity K}" if "\<sigma> \<in> field_auto K K" for \<sigma>
    by (metis that PiE_restrict field_auto_mem_iff insertI1 restrict_ext)
  then show ?thesis
    using cK identity_field_auto by auto
qed

lemma solvable_field_auto_self:
  fixes K :: "complex set"
  assumes K: "Subfield K"
  shows "Group.solvable (field_auto K K) (compose K) (identity K)"
proof -
  have cK: "complex_subfield K" using K by (simp add: complex_subfield_iff_subfield)
  interpret G: Group "field_auto K K" "compose K" "identity K"
    by (rule Galois_group_Group[OF cK subset_refl])
  show ?thesis unfolding G.solvable_def
    using G.derivedSeries.simps(1) assms field_auto_self_trivial by blast
qed

subsection \<open>Normal solvable towers\<close>

text \<open>@{term "solvable_tower K F Fs"}: the chain starting at @{term F} and following @{term Fs}, with
  fixed top @{term K}, in which every field is a subfield of @{term K}, every intermediate field is
  stable under @{term "field_auto K F"}, and every step has a solvable relative Galois group.  (The
  empty tower requires @{term "F = K"}.)\<close>
fun solvable_tower :: "complex set \<Rightarrow> complex set \<Rightarrow> complex set list \<Rightarrow> bool" where
  "solvable_tower K F [] \<longleftrightarrow> F = K"
| "solvable_tower K F (G # Gs) \<longleftrightarrow>
     Subfield F \<and> Subfield G \<and> F \<subseteq> G \<and> G \<subseteq> K \<and>
     (\<forall>\<sigma> \<in> field_auto K F. \<sigma> ` G = G) \<and>
     Group.solvable (field_auto G F) (compose G) (identity G) \<and>
     solvable_tower K G Gs"

subsection \<open>The assembly\<close>

text \<open>\<^emph>\<open>A normal solvable tower has a solvable Galois group.\<close>  By induction down the tower: the top
  @{term K} has the trivial (hence solvable) group @{term "field_auto K K"}; each step combines the
  solvable relative group @{term "field_auto G F"} with the solvable @{term "field_auto K G"} (from
  the induction hypothesis) via @{thm [source] galois_solvable_tower_step}, using stability of
  @{term G} under @{term "field_auto K F"}.\<close>
theorem solvable_tower_imp_solvable:
  assumes K: "Subfield K"
  shows "solvable_tower K F Fs \<Longrightarrow> Subfield F
           \<Longrightarrow> Group.solvable (field_auto K F) (compose K) (identity K)"
proof (induction Fs arbitrary: F)
  case Nil then show ?case
    by (metis solvable_field_auto_self solvable_tower.simps(1))
next
  case Cons
  then show ?case
    by (metis assms galois_solvable_tower_step solvable_tower.simps(2))
qed

end
