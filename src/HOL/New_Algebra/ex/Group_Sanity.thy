theory Group_Sanity
  imports "HOL-New_Algebra.Schreier_Refinement"
    "HOL-New_Algebra.Composition_Factors_Solvable"
    "HOL-New_Algebra.Sym_Not_Solvable"
    "HOL-New_Algebra.Symmetric_Generation"
begin

section \<open>Cross-checks on the Zassenhaus lemma\<close>

text \<open>The four wings @{term left_top}, @{term left_bottom}, @{term right_top}, @{term right_bottom} are
  where a plausible-looking but wrong Zassenhaus would come from --- transposing an @{term H} for a
  @{term K}, or an @{term H1} for a @{term K1}, still yields sets and still admits a proof of
  \<^emph>\<open>some\<close> isomorphism.  The checks pin the wings down by their behaviour in cases where their values
  are forced.

  Note on method: these proofs go through the intro/elim API that \<open>Zassenhaus\<close> already exports
  (\<open>left_top_memE\<close>, \<open>left_bottom_memI\<close>, \<open>left_bottom_memE\<close>)
  rather than unfolding the @{const image} definitions.  Unfolding and finishing with @{method force}
  does not terminate here.\<close>

context zassenhaus
begin

subsection \<open>With \<open>H\<^sub>1\<close> trivial the left wing collapses\<close>

text \<open>This is the case in which Zassenhaus specialises to the second isomorphism theorem: the left
  quotient becomes @{text "(H \<inter> K) / (H \<inter> K\<^sub>1)"}.  Getting it right is what makes the general
  statement credible, so it is the sharpest single check available without building a concrete group.

  Only the \<^emph>\<open>elimination\<close> direction is checked for the top wing, since \<open>Zassenhaus\<close> exports no
  @{text left_top_memI}; that is enough to catch a wing that is too large.\<close>

lemma left_top_trivial_H1_subset:
  assumes H1: "H1 = {\<one>}" and x: "x \<in> left_top"
  shows "x \<in> H \<inter> K"
proof -
  from x obtain b n where b: "b \<in> H \<inter> K" and n: "n \<in> H1" and xeq: "x = b \<cdot> n"
    by (rule left_top_memE)
  have "n = \<one>" using n H1 by simp
  moreover have "b \<in> G" using b H.sub by blast
  ultimately show ?thesis using b xeq by simp
qed

text \<open>For the bottom wing both directions are available, so the collapse is an equality.\<close>

lemma left_bottom_trivial_H1:
  assumes H1: "H1 = {\<one>}"
  shows "left_bottom = H \<inter> K1"
proof
  show "left_bottom \<subseteq> H \<inter> K1"
  proof
    fix x assume "x \<in> left_bottom"
    then obtain c n where c: "c \<in> H \<inter> K1" and n: "n \<in> H1" and xeq: "x = c \<cdot> n"
      by (rule left_bottom_memE)
    have "n = \<one>" using n H1 by simp
    moreover have "c \<in> G" using c H.sub by blast
    ultimately show "x \<in> H \<inter> K1" using c xeq by simp
  qed
  show "H \<inter> K1 \<subseteq> left_bottom"
  proof
    fix x assume x: "x \<in> H \<inter> K1"
    have xG: "x \<in> G" using x H.sub by blast
    have "\<one> \<in> H1" using H1 by simp
    then have "x \<cdot> \<one> \<in> left_bottom" using x by (rule left_bottom_memI[rotated])
    then show "x \<in> left_bottom" using xG by simp
  qed
qed


subsection \<open>The symmetric case is genuinely symmetric\<close>

text \<open>When the two flags coincide the two wings are literally the same set, so the isomorphism is
  between a quotient and itself.  A wing definition that had transposed an @{term H} for a @{term K}
  would fail this, and unlike the collapse above it is a statement about all four wings at once.\<close>

lemma left_top_eq_right_top_when_flags_agree:
  assumes "H = K" and "H1 = K1"
  shows "left_top = right_top"
  unfolding left_top_def right_top_def using assms by simp

lemma left_bottom_eq_right_bottom_when_flags_agree:
  assumes "H = K" and "H1 = K1"
  shows "left_bottom = right_bottom"
  unfolding left_bottom_def right_bottom_def using assms by simp


subsection \<open>The butterfly inclusions hold in the required orientation\<close>

text \<open>Collected from \<open>Zassenhaus\<close>: each bottom wing sits inside its own top wing, and the middle
  group @{term "H \<inter> K"} sits inside both tops.  Recording them together checks that the diagram is
  oriented as the lemma's statement needs --- a transposed wing would break one of the four.\<close>

lemmas butterfly_inclusions =
  left_bottom_subset_top right_bottom_subset_top
  middle_subset_left_top middle_subset_right_top

end

section \<open>Cross-checking the Schreier refinement indices\<close>

text \<open>
  These checks specialise one side of the Schreier construction to the
  canonical one-step series.  Both flattened refinement matrices must then be
  exactly the factor sequence of the other series, not merely a permutation of
  it.  This pins down the row bounds, endpoint orientation, factor packaging,
  and row-major flattening independently of the final multiset argument.
\<close>

context normal_series
begin

interpretation one_step: normal_series_pair
    G "(\<cdot>)" \<one> "one_step_normal_series_term G \<one>" 1 H n
proof (rule normal_series_pair.intro)
  show "normal_series G (\<cdot>) \<one> (one_step_normal_series_term G \<one>) 1"
    by (rule G.one_step_normal_series)
  show "normal_series G (\<cdot>) \<one> H n"
    by (rule normal_series_axioms)
qed

theorem one_step_schreier_factor_classes:
  "one_step.left_refinement_factor_classes = series_factor_classes \<and>
    one_step.right_refinement_factor_classes = series_factor_classes"
proof -
  have right_factor:
      "one_step.right_refinement_factor_class j 0 = series_factor_class j"
    if j: "j < n" for j
  proof -
    have start: "one_step.right_refinement_term j 0 = H j"
      by (rule one_step.right_refinement_start[OF j])
    have finish: "one_step.right_refinement_term j 1 = H (Suc j)"
      by (rule one_step.right_refinement_end[OF j])
    show ?thesis
      unfolding one_step.right_refinement_factor_class_def
      using start finish series_factor_class_eq_normal_factor_class
      by simp
  qed
  have left_factor:
      "one_step.left_refinement_factor_class 0 j = series_factor_class j"
    if j: "j < n" for j
  proof -
    have transpose:
        "one_step.left_refinement_factor_class 0 j =
          one_step.right_refinement_factor_class j 0"
      by (rule one_step.refinement_factor_class_eq) (use j in simp_all)
    show ?thesis using transpose right_factor[OF j] by simp
  qed
  show ?thesis
  proof
    show "one_step.left_refinement_factor_classes = series_factor_classes"
      unfolding one_step.left_refinement_factor_classes_def series_factor_classes_def
      by (simp add: left_factor)
    show "one_step.right_refinement_factor_classes = series_factor_classes"
      unfolding one_step.right_refinement_factor_classes_def series_factor_classes_def
      by (simp add: right_factor)
  qed
qed

end

section \<open>Composition factors of the symmetric and alternating groups\<close>

text \<open>These are \<^emph>\<open>consistency\<close> checks, not new mathematics.  The composition-series material of
  We test \<open>Composition_Factors_Solvable\<close> against results proved independently elsewhere in this
  development, on the principle that a vacuous or too-weak definition would let a false statement
  through.

  The sharpest available cross-check is @{thm [source] Sn_not_solvable}: this development already
  proves, by an argument that knows nothing of composition series, that \<open>S\<^sub>n\<close> is not solvable for
  \<open>n \<ge> 5\<close>.  The new criterion says solvability is equivalent to all composition factors being
  abelian.  The two must agree, and forcing them to agree pins down real content: if
  @{const composition_series.abelian_factors} were vacuously true --- say because
  @{text series_factor} returned something degenerate --- then \<open>S\<^sub>5\<close> would come out solvable and
  contradict a theorem already in the library.\<close>

subsection \<open>A finite group has a composition series, and \<open>S\<^sub>5\<close> in particular\<close>

text \<open>First that the existence theorem applies at all to a concrete group of interest.\<close>
lemma Sn_has_composition_series:
  "\<exists>H m. composition_series (Sn n) (\<circ>) id H m"
proof (rule finite_group_has_composition_series_ex)
  show "Group (Sn n) (\<circ>) id" by (rule Group_Sn)
  show "finite (Sn n)" by (rule finite_Sn)
qed

subsection \<open>The criterion is consistent with \<open>S\<^sub>n\<close> being unsolvable\<close>

text \<open>\<^bold>\<open>The main cross-check.\<close>  Every composition series of \<open>S\<^sub>n\<close> (\<open>n \<ge> 5\<close>) has a factor that is
  \<^emph>\<open>not\<close> abelian.  This is not proved by exhibiting one --- it is forced, by combining the new
  criterion with the independently proved unsolvability of \<open>S\<^sub>n\<close>.  It therefore fails if the new
  criterion is too weak in either direction.\<close>
theorem Sn_composition_factors_not_all_abelian:
  assumes n5: "5 \<le> n" and series: "composition_series (Sn n) (\<circ>) id H m"
  shows "\<not> composition_series.abelian_factors (\<circ>) id H m"
proof
  interpret S: composition_series "Sn n" "(\<circ>)" id H m by (rule series)
  assume "S.abelian_factors"
  \<comment> \<open>The criterion would make \<open>S\<^sub>n\<close> solvable...\<close>
  then have "Group.solvable (Sn n) (\<circ>) id" using S.solvable_iff_abelian_factors by blast
  \<comment> \<open>...contradicting @{thm [source] Sn_not_solvable}, proved independently of all this.\<close>
  with Sn_not_solvable[OF n5] show False by simp
qed

text \<open>The same for the alternating groups, via @{thm [source] An_not_solvable}.\<close>
theorem An_composition_factors_not_all_abelian:
  assumes n5: "5 \<le> n" and series: "composition_series (An n) (\<circ>) id H m"
  shows "\<not> composition_series.abelian_factors (\<circ>) id H m"
proof
  interpret A: composition_series "An n" "(\<circ>)" id H m by (rule series)
  assume "A.abelian_factors"
  then have "Group.solvable (An n) (\<circ>) id" using A.solvable_iff_abelian_factors by blast
  with An_not_solvable[OF n5] show False by simp
qed

text \<open>And the existence and criterion theorems combine: some composition series of \<open>S\<^sub>5\<close> exists, and
  every one of them has a non-abelian factor.  If @{const composition_series} were unsatisfiable
  these two would not sit together --- the first would be vacuous.\<close>
corollary S5_has_series_with_a_nonabelian_factor:
  "\<exists>H m. composition_series (Sn 5) (\<circ>) id H m
         \<and> \<not> composition_series.abelian_factors (\<circ>) id H m"
proof -
  obtain H m where series: "composition_series (Sn 5) (\<circ>) id H m"
    using Sn_has_composition_series[of 5] by blast
  then have "\<not> composition_series.abelian_factors (\<circ>) id H m"
    by (rule Sn_composition_factors_not_all_abelian[OF order_refl])
  with series show ?thesis by blast
qed

end
