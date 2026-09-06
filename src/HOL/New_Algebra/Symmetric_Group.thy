section \<open>The Symmetric and Alternating Groups\<close>

theory Symmetric_Group
  imports Derived_Series "HOL-Combinatorics.Permutations" "HOL-Combinatorics.Cycles"
begin

text \<open>
  We realise the concrete symmetric group @{text "S\<^sub>n"} as the group of permutations of
  @{term "{0..<n}"} under function composition, reusing the permutation and sign
  machinery of @{theory "HOL-Combinatorics.Permutations"}.

  Design note: the development's own @{term "transformations.Sym"} consists of
  \<^emph>\<open>extensional\<close> maps (undefined outside the carrier), which does not interoperate
  directly with the library predicate @{term "p permutes S"} (identity outside the
  carrier).  Building @{text "S\<^sub>n"} natively on @{term "{p. p permutes S}"} avoids that
  impedance mismatch and lets us inherit @{const sign} and its homomorphism property
  for free.
\<close>

subsection \<open>The symmetric group as a @{locale Group}\<close>

definition Sn :: "nat \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "Sn n = {p. p permutes {0..<n}}"

lemma Sn_iff: "p \<in> Sn n \<longleftrightarrow> p permutes {0..<n}"
  by (simp add: Sn_def)

lemma Sn_permutation: "p \<in> Sn n \<Longrightarrow> permutation p"
  by (auto simp: Sn_def permutation_permutes)

text \<open>@{term "Sn n"} is a group under composition.\<close>
theorem Group_Sn: "Group (Sn n) (\<circ>) id"
proof (rule GroupI)
  fix u assume "u \<in> Sn n"
  then have perm: "u permutes {0..<n}" by (simp add: Sn_def)
  have "inv u \<in> Sn n" "u \<circ> inv u = id" "inv u \<circ> u = id"
    using perm by (simp_all add: Sn_def permutes_inv permutes_inv_o)
  then show "\<exists>v \<in> Sn n. u \<circ> v = id \<and> v \<circ> u = id" by blast
qed (auto simp: Sn_def permutes_compose permutes_id o_assoc)


subsection \<open>Relation to the development's abstract symmetric group\<close>

text \<open>
  The development's own symmetric group @{term "transformations.Sym S"} consists of the
  \<^emph>\<open>extensional\<close> bijections of @{term S} under @{term "compose S"}/@{term "identity S"}.  
  Our @{term "Sn n"} uses library @{const permutes} maps (identity outside).  The two are 
  reconciled by @{const restrict}: restricting a permutation to @{term S} yields an element
  of @{term "transformations.Sym S"}, and this correspondence is bijective.  This makes
  the concrete @{term "Sn n"} available to the development's @{locale Group_Action} machinery.
\<close>

lemma restrict_permutes_in_Sym:
  assumes "p permutes S"
  shows "restrict p S \<in> transformations.Sym S"
  using permutes_imp_bij [OF assms]
    by (simp add: bij_betw_imp_funcset transformations.Units_bij_betwD)

text \<open>Conversely, an element of @{term "transformations.Sym S"} permutes @{term S} once it
  is extended by the identity outside @{term S}.\<close>
lemma Sym_extend_permutes:
  assumes "\<alpha> \<in> transformations.Sym S"
  shows "(\<lambda>x. if x \<in> S then \<alpha> x else x) permutes S"
proof (rule bij_imp_permutes)
  have "bij_betw \<alpha> S S" using assms by (simp add: transformations.Units_bijective)
  then show "bij_betw (\<lambda>x. if x \<in> S then \<alpha> x else x) S S"
    by (smt (verit, best) bij_betw_cong)
qed simp


subsection \<open>The sign homomorphism and the alternating group\<close>

text \<open>The two-element group of signs.\<close>
lemma Group_signs: "Group {1, -1::int} (*) 1"
proof (rule GroupI)
  fix u :: int assume "u \<in> {1, -1}"
  then show "\<exists>v \<in> {1, -1::int}. u * v = 1 \<and> v * u = 1" by force
qed auto

lemma sign_range: "p \<in> Sn n \<Longrightarrow> sign p \<in> {1, -1::int}"
  by (auto simp: sign_def)

text \<open>@{const sign} is a group homomorphism @{text "S\<^sub>n \<rightarrow> {1, -1}"}.  The multiplicativity
  is inherited directly from @{thm [source] sign_compose}.\<close>
lemma sign_hom: "group_homomorphism (restrict sign (Sn n)) (Sn n) (\<circ>) id {1,-1::int} (*) 1"
proof -
  interpret S: Group "Sn n" "(\<circ>)" id by (rule Group_Sn)
  interpret T: Group "{1,-1::int}" "(*)" 1 by (rule Group_signs)
  show ?thesis
  proof qed (use sign_range in \<open>auto simp: Sn_permutation sign_compose\<close>)
qed

text \<open>The alternating group is the kernel of the sign homomorphism.\<close>
definition An :: "nat \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "An n = group_homomorphism.Ker (restrict sign (Sn n)) (Sn n) (1::int)"

context
  fixes n::nat
begin

interpretation H: group_homomorphism "restrict sign (Sn n)" "Sn n" "(\<circ>)" id "{1,-1::int}" "(*)" 1
  by (rule sign_hom)

lemma An_normal: "normal_subgroup (An n) (Sn n) (\<circ>) id"
  using An_def H.kernel.normal_subgroup_axioms by presburger

lemma An_iff: "p \<in> An n \<longleftrightarrow> p \<in> Sn n \<and> sign p = 1"
  by (metis An_def H.Ker_image H.Ker_memI H.kernel.sub restrict_apply)

end

lemma An_subset_Sn: "An n \<subseteq> Sn n"
  by (auto simp: An_iff)


subsection \<open>Three-cycles\<close>

text \<open>A three-cycle on distinct points of @{term "{0..<n}"} is a permutation, and it is
  even, hence lies in the alternating group.\<close>

lemma three_cycle_permutes:
  assumes "distinct [a,b,c]" "a < n" "b < n" "c < n"
  shows "cycle_of_list [a,b,c] permutes {0..<(n::nat)}"
  using assms cycle_permutes [of "[a,b,c]"] permutes_subset assms by fastforce

lemma three_cycle_in_Sn:
  assumes "distinct [a,b,c]" "a < n" "b < n" "c < n"
  shows "cycle_of_list [a,b,c] \<in> Sn n"
  using assms three_cycle_permutes by (simp add: Sn_def)

lemma three_cycle_sign:
  assumes "distinct [a,b,c]"
  shows "sign (cycle_of_list [a,b,c]) = 1"
proof -
  have "sign (cycle_of_list [a,b,c])
      = sign (Transposition.transpose a b) * sign (Transposition.transpose b c)"
    by (simp add: permutation_swap_id sign_compose)
  also have "\<dots> = 1" using assms by (simp add: sign_swap_id)
  finally show ?thesis .
qed

lemma three_cycle_in_An:
  assumes "distinct [a,b,c]" "a < n" "b < n" "c < n"
  shows "cycle_of_list [a,b,c] \<in> An n"
  by (meson An_iff assms three_cycle_in_Sn three_cycle_sign)

end
