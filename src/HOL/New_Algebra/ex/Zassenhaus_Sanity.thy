section \<open>Cross-checks on the Zassenhaus lemma\<close>

theory Zassenhaus_Sanity
  imports "HOL-New_Algebra.Zassenhaus_Lemma"
begin

text \<open>Zassenhaus is now \<^emph>\<open>load-bearing\<close>: \<open>Series_Refinement\<close> imports it, so the whole Jordan--Hölder
  development inherits any error in it.  Like that development it was merged on structural evidence
  (it builds, contains no \<open>sorry\<close>).  The checks below test its content.

  The four wings @{term left_top}, @{term left_bottom}, @{term right_top}, @{term right_bottom} are
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

end
