section \<open>Composition factors of the symmetric and alternating groups\<close>

theory Sn_Composition_Factors
  imports Composition_Factors_Solvable Sym_Not_Solvable Symmetric_Generation
begin

text \<open>These are \<^emph>\<open>consistency\<close> checks, not new mathematics.  The composition-series material of
  \<open>Composition_Factors_Solvable\<close> was contributed as a large block and merged on
  structural evidence (it builds, contains no \<open>sorry\<close>, and cites the existing solvability lemmas).
  The checks below test its \<^emph>\<open>content\<close> against results proved independently elsewhere in this
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
