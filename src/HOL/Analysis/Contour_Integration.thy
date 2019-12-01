section \<open>Contour Integration\<close>

theory Contour_Integration
  imports Henstock_Kurzweil_Integration Path_Connected Complex_Transcendental
begin

subsection\<^marker>\<open>tag unimportant\<close> \<open>Piecewise differentiable functions\<close>

definition piecewise_differentiable_on
           (infixr "piecewise'_differentiable'_on" 50)
  where "f piecewise_differentiable_on i  \<equiv>
           continuous_on i f \<and>
           (\<exists>S. finite S \<and> (\<forall>x \<in> i - S. f differentiable (at x within i)))"

lemma piecewise_differentiable_on_imp_continuous_on:
    "f piecewise_differentiable_on S \<Longrightarrow> continuous_on S f"
by (simp add: piecewise_differentiable_on_def)

lemma piecewise_differentiable_on_subset:
    "f piecewise_differentiable_on S \<Longrightarrow> T \<le> S \<Longrightarrow> f piecewise_differentiable_on T"
  using continuous_on_subset
  unfolding piecewise_differentiable_on_def
  apply safe
  apply (blast elim: continuous_on_subset)
  by (meson Diff_iff differentiable_within_subset subsetCE)

lemma differentiable_on_imp_piecewise_differentiable:
  fixes a:: "'a::{linorder_topology,real_normed_vector}"
  shows "f differentiable_on {a..b} \<Longrightarrow> f piecewise_differentiable_on {a..b}"
  apply (simp add: piecewise_differentiable_on_def differentiable_imp_continuous_on)
  apply (rule_tac x="{a,b}" in exI, simp add: differentiable_on_def)
  done

lemma differentiable_imp_piecewise_differentiable:
    "(\<And>x. x \<in> S \<Longrightarrow> f differentiable (at x within S))
         \<Longrightarrow> f piecewise_differentiable_on S"
by (auto simp: piecewise_differentiable_on_def differentiable_imp_continuous_on differentiable_on_def
         intro: differentiable_within_subset)

lemma piecewise_differentiable_const [iff]: "(\<lambda>x. z) piecewise_differentiable_on S"
  by (simp add: differentiable_imp_piecewise_differentiable)

lemma piecewise_differentiable_compose:
    "\<lbrakk>f piecewise_differentiable_on S; g piecewise_differentiable_on (f ` S);
      \<And>x. finite (S \<inter> f-`{x})\<rbrakk>
      \<Longrightarrow> (g \<circ> f) piecewise_differentiable_on S"
  apply (simp add: piecewise_differentiable_on_def, safe)
  apply (blast intro: continuous_on_compose2)
  apply (rename_tac A B)
  apply (rule_tac x="A \<union> (\<Union>x\<in>B. S \<inter> f-`{x})" in exI)
  apply (blast intro!: differentiable_chain_within)
  done

lemma piecewise_differentiable_affine:
  fixes m::real
  assumes "f piecewise_differentiable_on ((\<lambda>x. m *\<^sub>R x + c) ` S)"
  shows "(f \<circ> (\<lambda>x. m *\<^sub>R x + c)) piecewise_differentiable_on S"
proof (cases "m = 0")
  case True
  then show ?thesis
    unfolding o_def
    by (force intro: differentiable_imp_piecewise_differentiable differentiable_const)
next
  case False
  show ?thesis
    apply (rule piecewise_differentiable_compose [OF differentiable_imp_piecewise_differentiable])
    apply (rule assms derivative_intros | simp add: False vimage_def real_vector_affinity_eq)+
    done
qed

lemma piecewise_differentiable_cases:
  fixes c::real
  assumes "f piecewise_differentiable_on {a..c}"
          "g piecewise_differentiable_on {c..b}"
           "a \<le> c" "c \<le> b" "f c = g c"
  shows "(\<lambda>x. if x \<le> c then f x else g x) piecewise_differentiable_on {a..b}"
proof -
  obtain S T where st: "finite S" "finite T"
               and fd: "\<And>x. x \<in> {a..c} - S \<Longrightarrow> f differentiable at x within {a..c}"
               and gd: "\<And>x. x \<in> {c..b} - T \<Longrightarrow> g differentiable at x within {c..b}"
    using assms
    by (auto simp: piecewise_differentiable_on_def)
  have finabc: "finite ({a,b,c} \<union> (S \<union> T))"
    by (metis \<open>finite S\<close> \<open>finite T\<close> finite_Un finite_insert finite.emptyI)
  have "continuous_on {a..c} f" "continuous_on {c..b} g"
    using assms piecewise_differentiable_on_def by auto
  then have "continuous_on {a..b} (\<lambda>x. if x \<le> c then f x else g x)"
    using continuous_on_cases [OF closed_real_atLeastAtMost [of a c],
                               OF closed_real_atLeastAtMost [of c b],
                               of f g "\<lambda>x. x\<le>c"]  assms
    by (force simp: ivl_disj_un_two_touch)
  moreover
  { fix x
    assume x: "x \<in> {a..b} - ({a,b,c} \<union> (S \<union> T))"
    have "(\<lambda>x. if x \<le> c then f x else g x) differentiable at x within {a..b}" (is "?diff_fg")
    proof (cases x c rule: le_cases)
      case le show ?diff_fg
      proof (rule differentiable_transform_within [where d = "dist x c"])
        have "f differentiable at x"
          using x le fd [of x] at_within_interior [of x "{a..c}"] by simp
        then show "f differentiable at x within {a..b}"
          by (simp add: differentiable_at_withinI)
      qed (use x le st dist_real_def in auto)
    next
      case ge show ?diff_fg
      proof (rule differentiable_transform_within [where d = "dist x c"])
        have "g differentiable at x"
          using x ge gd [of x] at_within_interior [of x "{c..b}"] by simp
        then show "g differentiable at x within {a..b}"
          by (simp add: differentiable_at_withinI)
      qed (use x ge st dist_real_def in auto)
    qed
  }
  then have "\<exists>S. finite S \<and>
                 (\<forall>x\<in>{a..b} - S. (\<lambda>x. if x \<le> c then f x else g x) differentiable at x within {a..b})"
    by (meson finabc)
  ultimately show ?thesis
    by (simp add: piecewise_differentiable_on_def)
qed

lemma piecewise_differentiable_neg:
    "f piecewise_differentiable_on S \<Longrightarrow> (\<lambda>x. -(f x)) piecewise_differentiable_on S"
  by (auto simp: piecewise_differentiable_on_def continuous_on_minus)

lemma piecewise_differentiable_add:
  assumes "f piecewise_differentiable_on i"
          "g piecewise_differentiable_on i"
    shows "(\<lambda>x. f x + g x) piecewise_differentiable_on i"
proof -
  obtain S T where st: "finite S" "finite T"
                       "\<forall>x\<in>i - S. f differentiable at x within i"
                       "\<forall>x\<in>i - T. g differentiable at x within i"
    using assms by (auto simp: piecewise_differentiable_on_def)
  then have "finite (S \<union> T) \<and> (\<forall>x\<in>i - (S \<union> T). (\<lambda>x. f x + g x) differentiable at x within i)"
    by auto
  moreover have "continuous_on i f" "continuous_on i g"
    using assms piecewise_differentiable_on_def by auto
  ultimately show ?thesis
    by (auto simp: piecewise_differentiable_on_def continuous_on_add)
qed

lemma piecewise_differentiable_diff:
    "\<lbrakk>f piecewise_differentiable_on S;  g piecewise_differentiable_on S\<rbrakk>
     \<Longrightarrow> (\<lambda>x. f x - g x) piecewise_differentiable_on S"
  unfolding diff_conv_add_uminus
  by (metis piecewise_differentiable_add piecewise_differentiable_neg)

lemma continuous_on_joinpaths_D1:
    "continuous_on {0..1} (g1 +++ g2) \<Longrightarrow> continuous_on {0..1} g1"
  apply (rule continuous_on_eq [of _ "(g1 +++ g2) \<circ> ((*)(inverse 2))"])
  apply (rule continuous_intros | simp)+
  apply (auto elim!: continuous_on_subset simp: joinpaths_def)
  done

lemma continuous_on_joinpaths_D2:
    "\<lbrakk>continuous_on {0..1} (g1 +++ g2); pathfinish g1 = pathstart g2\<rbrakk> \<Longrightarrow> continuous_on {0..1} g2"
  apply (rule continuous_on_eq [of _ "(g1 +++ g2) \<circ> (\<lambda>x. inverse 2*x + 1/2)"])
  apply (rule continuous_intros | simp)+
  apply (auto elim!: continuous_on_subset simp add: joinpaths_def pathfinish_def pathstart_def Ball_def)
  done

lemma piecewise_differentiable_D1:
  assumes "(g1 +++ g2) piecewise_differentiable_on {0..1}"
  shows "g1 piecewise_differentiable_on {0..1}"
proof -
  obtain S where cont: "continuous_on {0..1} g1" and "finite S"
    and S: "\<And>x. x \<in> {0..1} - S \<Longrightarrow> g1 +++ g2 differentiable at x within {0..1}"
    using assms unfolding piecewise_differentiable_on_def
    by (blast dest!: continuous_on_joinpaths_D1)
  show ?thesis
    unfolding piecewise_differentiable_on_def
  proof (intro exI conjI ballI cont)
    show "finite (insert 1 (((*)2) ` S))"
      by (simp add: \<open>finite S\<close>)
    show "g1 differentiable at x within {0..1}" if "x \<in> {0..1} - insert 1 ((*) 2 ` S)" for x
    proof (rule_tac d="dist (x/2) (1/2)" in differentiable_transform_within)
      have "g1 +++ g2 differentiable at (x / 2) within {0..1/2}"
        by (rule differentiable_subset [OF S [of "x/2"]] | use that in force)+
      then show "g1 +++ g2 \<circ> (*) (inverse 2) differentiable at x within {0..1}"
        using image_affinity_atLeastAtMost_div [of 2 0 "0::real" 1]
        by (auto intro: differentiable_chain_within)
    qed (use that in \<open>auto simp: joinpaths_def\<close>)
  qed
qed

lemma piecewise_differentiable_D2:
  assumes "(g1 +++ g2) piecewise_differentiable_on {0..1}" and eq: "pathfinish g1 = pathstart g2"
  shows "g2 piecewise_differentiable_on {0..1}"
proof -
  have [simp]: "g1 1 = g2 0"
    using eq by (simp add: pathfinish_def pathstart_def)
  obtain S where cont: "continuous_on {0..1} g2" and "finite S"
    and S: "\<And>x. x \<in> {0..1} - S \<Longrightarrow> g1 +++ g2 differentiable at x within {0..1}"
    using assms unfolding piecewise_differentiable_on_def
    by (blast dest!: continuous_on_joinpaths_D2)
  show ?thesis
    unfolding piecewise_differentiable_on_def
  proof (intro exI conjI ballI cont)
    show "finite (insert 0 ((\<lambda>x. 2*x-1)`S))"
      by (simp add: \<open>finite S\<close>)
    show "g2 differentiable at x within {0..1}" if "x \<in> {0..1} - insert 0 ((\<lambda>x. 2*x-1)`S)" for x
    proof (rule_tac d="dist ((x+1)/2) (1/2)" in differentiable_transform_within)
      have x2: "(x + 1) / 2 \<notin> S"
        using that
        apply (clarsimp simp: image_iff)
        by (metis add.commute add_diff_cancel_left' mult_2 field_sum_of_halves)
      have "g1 +++ g2 \<circ> (\<lambda>x. (x+1) / 2) differentiable at x within {0..1}"
        by (rule differentiable_chain_within differentiable_subset [OF S [of "(x+1)/2"]] | use x2 that in force)+
      then show "g1 +++ g2 \<circ> (\<lambda>x. (x+1) / 2) differentiable at x within {0..1}"
        by (auto intro: differentiable_chain_within)
      show "(g1 +++ g2 \<circ> (\<lambda>x. (x + 1) / 2)) x' = g2 x'" if "x' \<in> {0..1}" "dist x' x < dist ((x + 1) / 2) (1/2)" for x'
      proof -
        have [simp]: "(2*x'+2)/2 = x'+1"
          by (simp add: field_split_simps)
        show ?thesis
          using that by (auto simp: joinpaths_def)
      qed
    qed (use that in \<open>auto simp: joinpaths_def\<close>)
  qed
qed


subsection\<open>The concept of continuously differentiable\<close>

text \<open>
John Harrison writes as follows:

``The usual assumption in complex analysis texts is that a path \<open>\<gamma>\<close> should be piecewise
continuously differentiable, which ensures that the path integral exists at least for any continuous
f, since all piecewise continuous functions are integrable. However, our notion of validity is
weaker, just piecewise differentiability\ldots{} [namely] continuity plus differentiability except on a
finite set\ldots{} [Our] underlying theory of integration is the Kurzweil-Henstock theory. In contrast to
the Riemann or Lebesgue theory (but in common with a simple notion based on antiderivatives), this
can integrate all derivatives.''

"Formalizing basic complex analysis." From Insight to Proof: Festschrift in Honour of Andrzej Trybulec.
Studies in Logic, Grammar and Rhetoric 10.23 (2007): 151-165.

And indeed he does not assume that his derivatives are continuous, but the penalty is unreasonably
difficult proofs concerning winding numbers. We need a self-contained and straightforward theorem
asserting that all derivatives can be integrated before we can adopt Harrison's choice.\<close>

definition\<^marker>\<open>tag important\<close> C1_differentiable_on :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> real set \<Rightarrow> bool"
           (infix "C1'_differentiable'_on" 50)
  where
  "f C1_differentiable_on S \<longleftrightarrow>
   (\<exists>D. (\<forall>x \<in> S. (f has_vector_derivative (D x)) (at x)) \<and> continuous_on S D)"

lemma C1_differentiable_on_eq:
    "f C1_differentiable_on S \<longleftrightarrow>
     (\<forall>x \<in> S. f differentiable at x) \<and> continuous_on S (\<lambda>x. vector_derivative f (at x))"
     (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding C1_differentiable_on_def
    by (metis (no_types, lifting) continuous_on_eq  differentiableI_vector vector_derivative_at)
next
  assume ?rhs
  then show ?lhs
    using C1_differentiable_on_def vector_derivative_works by fastforce
qed

lemma C1_differentiable_on_subset:
  "f C1_differentiable_on T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> f C1_differentiable_on S"
  unfolding C1_differentiable_on_def  continuous_on_eq_continuous_within
  by (blast intro:  continuous_within_subset)

lemma C1_differentiable_compose:
  assumes fg: "f C1_differentiable_on S" "g C1_differentiable_on (f ` S)" and fin: "\<And>x. finite (S \<inter> f-`{x})"
  shows "(g \<circ> f) C1_differentiable_on S"
proof -
  have "\<And>x. x \<in> S \<Longrightarrow> g \<circ> f differentiable at x"
    by (meson C1_differentiable_on_eq assms differentiable_chain_at imageI)
  moreover have "continuous_on S (\<lambda>x. vector_derivative (g \<circ> f) (at x))"
  proof (rule continuous_on_eq [of _ "\<lambda>x. vector_derivative f (at x) *\<^sub>R vector_derivative g (at (f x))"])
    show "continuous_on S (\<lambda>x. vector_derivative f (at x) *\<^sub>R vector_derivative g (at (f x)))"
      using fg
      apply (clarsimp simp add: C1_differentiable_on_eq)
      apply (rule Limits.continuous_on_scaleR, assumption)
      by (metis (mono_tags, lifting) continuous_at_imp_continuous_on continuous_on_compose continuous_on_cong differentiable_imp_continuous_within o_def)
    show "\<And>x. x \<in> S \<Longrightarrow> vector_derivative f (at x) *\<^sub>R vector_derivative g (at (f x)) = vector_derivative (g \<circ> f) (at x)"
      by (metis (mono_tags, hide_lams) C1_differentiable_on_eq fg imageI vector_derivative_chain_at)
  qed
  ultimately show ?thesis
    by (simp add: C1_differentiable_on_eq)
qed

lemma C1_diff_imp_diff: "f C1_differentiable_on S \<Longrightarrow> f differentiable_on S"
  by (simp add: C1_differentiable_on_eq differentiable_at_imp_differentiable_on)

lemma C1_differentiable_on_ident [simp, derivative_intros]: "(\<lambda>x. x) C1_differentiable_on S"
  by (auto simp: C1_differentiable_on_eq)

lemma C1_differentiable_on_const [simp, derivative_intros]: "(\<lambda>z. a) C1_differentiable_on S"
  by (auto simp: C1_differentiable_on_eq)

lemma C1_differentiable_on_add [simp, derivative_intros]:
  "f C1_differentiable_on S \<Longrightarrow> g C1_differentiable_on S \<Longrightarrow> (\<lambda>x. f x + g x) C1_differentiable_on S"
  unfolding C1_differentiable_on_eq  by (auto intro: continuous_intros)

lemma C1_differentiable_on_minus [simp, derivative_intros]:
  "f C1_differentiable_on S \<Longrightarrow> (\<lambda>x. - f x) C1_differentiable_on S"
  unfolding C1_differentiable_on_eq  by (auto intro: continuous_intros)

lemma C1_differentiable_on_diff [simp, derivative_intros]:
  "f C1_differentiable_on S \<Longrightarrow> g C1_differentiable_on S \<Longrightarrow> (\<lambda>x. f x - g x) C1_differentiable_on S"
  unfolding C1_differentiable_on_eq  by (auto intro: continuous_intros)

lemma C1_differentiable_on_mult [simp, derivative_intros]:
  fixes f g :: "real \<Rightarrow> 'a :: real_normed_algebra"
  shows "f C1_differentiable_on S \<Longrightarrow> g C1_differentiable_on S \<Longrightarrow> (\<lambda>x. f x * g x) C1_differentiable_on S"
  unfolding C1_differentiable_on_eq
  by (auto simp: continuous_on_add continuous_on_mult continuous_at_imp_continuous_on differentiable_imp_continuous_within)

lemma C1_differentiable_on_scaleR [simp, derivative_intros]:
  "f C1_differentiable_on S \<Longrightarrow> g C1_differentiable_on S \<Longrightarrow> (\<lambda>x. f x *\<^sub>R g x) C1_differentiable_on S"
  unfolding C1_differentiable_on_eq
  by (rule continuous_intros | simp add: continuous_at_imp_continuous_on differentiable_imp_continuous_within)+


definition\<^marker>\<open>tag important\<close> piecewise_C1_differentiable_on
           (infixr "piecewise'_C1'_differentiable'_on" 50)
  where "f piecewise_C1_differentiable_on i  \<equiv>
           continuous_on i f \<and>
           (\<exists>S. finite S \<and> (f C1_differentiable_on (i - S)))"

lemma C1_differentiable_imp_piecewise:
    "f C1_differentiable_on S \<Longrightarrow> f piecewise_C1_differentiable_on S"
  by (auto simp: piecewise_C1_differentiable_on_def C1_differentiable_on_eq continuous_at_imp_continuous_on differentiable_imp_continuous_within)

lemma piecewise_C1_imp_differentiable:
    "f piecewise_C1_differentiable_on i \<Longrightarrow> f piecewise_differentiable_on i"
  by (auto simp: piecewise_C1_differentiable_on_def piecewise_differentiable_on_def
           C1_differentiable_on_def differentiable_def has_vector_derivative_def
           intro: has_derivative_at_withinI)

lemma piecewise_C1_differentiable_compose:
  assumes fg: "f piecewise_C1_differentiable_on S" "g piecewise_C1_differentiable_on (f ` S)" and fin: "\<And>x. finite (S \<inter> f-`{x})"
  shows "(g \<circ> f) piecewise_C1_differentiable_on S"
proof -
  have "continuous_on S (\<lambda>x. g (f x))"
    by (metis continuous_on_compose2 fg order_refl piecewise_C1_differentiable_on_def)
  moreover have "\<exists>T. finite T \<and> g \<circ> f C1_differentiable_on S - T"
  proof -
    obtain F where "finite F" and F: "f C1_differentiable_on S - F" and f: "f piecewise_C1_differentiable_on S"
      using fg by (auto simp: piecewise_C1_differentiable_on_def)
    obtain G where "finite G" and G: "g C1_differentiable_on f ` S - G" and g: "g piecewise_C1_differentiable_on f ` S"
      using fg by (auto simp: piecewise_C1_differentiable_on_def)
    show ?thesis
    proof (intro exI conjI)
      show "finite (F \<union> (\<Union>x\<in>G. S \<inter> f-`{x}))"
        using fin by (auto simp only: Int_Union \<open>finite F\<close> \<open>finite G\<close> finite_UN finite_imageI)
      show "g \<circ> f C1_differentiable_on S - (F \<union> (\<Union>x\<in>G. S \<inter> f -` {x}))"
        apply (rule C1_differentiable_compose)
          apply (blast intro: C1_differentiable_on_subset [OF F])
          apply (blast intro: C1_differentiable_on_subset [OF G])
        by (simp add:  C1_differentiable_on_subset G Diff_Int_distrib2 fin)
    qed
  qed
  ultimately show ?thesis
    by (simp add: piecewise_C1_differentiable_on_def)
qed

lemma piecewise_C1_differentiable_on_subset:
    "f piecewise_C1_differentiable_on S \<Longrightarrow> T \<le> S \<Longrightarrow> f piecewise_C1_differentiable_on T"
  by (auto simp: piecewise_C1_differentiable_on_def elim!: continuous_on_subset C1_differentiable_on_subset)

lemma C1_differentiable_imp_continuous_on:
  "f C1_differentiable_on S \<Longrightarrow> continuous_on S f"
  unfolding C1_differentiable_on_eq continuous_on_eq_continuous_within
  using differentiable_at_withinI differentiable_imp_continuous_within by blast

lemma C1_differentiable_on_empty [iff]: "f C1_differentiable_on {}"
  unfolding C1_differentiable_on_def
  by auto

lemma piecewise_C1_differentiable_affine:
  fixes m::real
  assumes "f piecewise_C1_differentiable_on ((\<lambda>x. m * x + c) ` S)"
  shows "(f \<circ> (\<lambda>x. m *\<^sub>R x + c)) piecewise_C1_differentiable_on S"
proof (cases "m = 0")
  case True
  then show ?thesis
    unfolding o_def by (auto simp: piecewise_C1_differentiable_on_def)
next
  case False
  have *: "\<And>x. finite (S \<inter> {y. m * y + c = x})"
    using False not_finite_existsD by fastforce
  show ?thesis
    apply (rule piecewise_C1_differentiable_compose [OF C1_differentiable_imp_piecewise])
    apply (rule * assms derivative_intros | simp add: False vimage_def)+
    done
qed

lemma piecewise_C1_differentiable_cases:
  fixes c::real
  assumes "f piecewise_C1_differentiable_on {a..c}"
          "g piecewise_C1_differentiable_on {c..b}"
           "a \<le> c" "c \<le> b" "f c = g c"
  shows "(\<lambda>x. if x \<le> c then f x else g x) piecewise_C1_differentiable_on {a..b}"
proof -
  obtain S T where st: "f C1_differentiable_on ({a..c} - S)"
                       "g C1_differentiable_on ({c..b} - T)"
                       "finite S" "finite T"
    using assms
    by (force simp: piecewise_C1_differentiable_on_def)
  then have f_diff: "f differentiable_on {a..<c} - S"
        and g_diff: "g differentiable_on {c<..b} - T"
    by (simp_all add: C1_differentiable_on_eq differentiable_at_withinI differentiable_on_def)
  have "continuous_on {a..c} f" "continuous_on {c..b} g"
    using assms piecewise_C1_differentiable_on_def by auto
  then have cab: "continuous_on {a..b} (\<lambda>x. if x \<le> c then f x else g x)"
    using continuous_on_cases [OF closed_real_atLeastAtMost [of a c],
                               OF closed_real_atLeastAtMost [of c b],
                               of f g "\<lambda>x. x\<le>c"]  assms
    by (force simp: ivl_disj_un_two_touch)
  { fix x
    assume x: "x \<in> {a..b} - insert c (S \<union> T)"
    have "(\<lambda>x. if x \<le> c then f x else g x) differentiable at x" (is "?diff_fg")
    proof (cases x c rule: le_cases)
      case le show ?diff_fg
        apply (rule differentiable_transform_within [where f=f and d = "dist x c"])
        using x dist_real_def le st by (auto simp: C1_differentiable_on_eq)
    next
      case ge show ?diff_fg
        apply (rule differentiable_transform_within [where f=g and d = "dist x c"])
        using dist_nz x dist_real_def ge st x by (auto simp: C1_differentiable_on_eq)
    qed
  }
  then have "(\<forall>x \<in> {a..b} - insert c (S \<union> T). (\<lambda>x. if x \<le> c then f x else g x) differentiable at x)"
    by auto
  moreover
  { assume fcon: "continuous_on ({a<..<c} - S) (\<lambda>x. vector_derivative f (at x))"
       and gcon: "continuous_on ({c<..<b} - T) (\<lambda>x. vector_derivative g (at x))"
    have "open ({a<..<c} - S)"  "open ({c<..<b} - T)"
      using st by (simp_all add: open_Diff finite_imp_closed)
    moreover have "continuous_on ({a<..<c} - S) (\<lambda>x. vector_derivative (\<lambda>x. if x \<le> c then f x else g x) (at x))"
    proof -
      have "((\<lambda>x. if x \<le> c then f x else g x) has_vector_derivative vector_derivative f (at x))            (at x)"
        if "a < x" "x < c" "x \<notin> S" for x
      proof -
        have f: "f differentiable at x"
          by (meson C1_differentiable_on_eq Diff_iff atLeastAtMost_iff less_eq_real_def st(1) that)
        show ?thesis
          using that
          apply (rule_tac f=f and d="dist x c" in has_vector_derivative_transform_within)
             apply (auto simp: dist_norm vector_derivative_works [symmetric] f)
          done
      qed
      then show ?thesis
        by (metis (no_types, lifting) continuous_on_eq [OF fcon] DiffE greaterThanLessThan_iff vector_derivative_at)
    qed
    moreover have "continuous_on ({c<..<b} - T) (\<lambda>x. vector_derivative (\<lambda>x. if x \<le> c then f x else g x) (at x))"
    proof -
      have "((\<lambda>x. if x \<le> c then f x else g x) has_vector_derivative vector_derivative g (at x))            (at x)"
        if "c < x" "x < b" "x \<notin> T" for x
      proof -
        have g: "g differentiable at x"
          by (metis C1_differentiable_on_eq DiffD1 DiffI atLeastAtMost_diff_ends greaterThanLessThan_iff st(2) that)
        show ?thesis
          using that
          apply (rule_tac f=g and d="dist x c" in has_vector_derivative_transform_within)
             apply (auto simp: dist_norm vector_derivative_works [symmetric] g)
          done
      qed
      then show ?thesis
        by (metis (no_types, lifting) continuous_on_eq [OF gcon] DiffE greaterThanLessThan_iff vector_derivative_at)
    qed
    ultimately have "continuous_on ({a<..<b} - insert c (S \<union> T))
        (\<lambda>x. vector_derivative (\<lambda>x. if x \<le> c then f x else g x) (at x))"
      by (rule continuous_on_subset [OF continuous_on_open_Un], auto)
  } note * = this
  have "continuous_on ({a<..<b} - insert c (S \<union> T)) (\<lambda>x. vector_derivative (\<lambda>x. if x \<le> c then f x else g x) (at x))"
    using st
    by (auto simp: C1_differentiable_on_eq elim!: continuous_on_subset intro: *)
  ultimately have "\<exists>S. finite S \<and> ((\<lambda>x. if x \<le> c then f x else g x) C1_differentiable_on {a..b} - S)"
    apply (rule_tac x="{a,b,c} \<union> S \<union> T" in exI)
    using st  by (auto simp: C1_differentiable_on_eq elim!: continuous_on_subset)
  with cab show ?thesis
    by (simp add: piecewise_C1_differentiable_on_def)
qed

lemma piecewise_C1_differentiable_neg:
    "f piecewise_C1_differentiable_on S \<Longrightarrow> (\<lambda>x. -(f x)) piecewise_C1_differentiable_on S"
  unfolding piecewise_C1_differentiable_on_def
  by (auto intro!: continuous_on_minus C1_differentiable_on_minus)

lemma piecewise_C1_differentiable_add:
  assumes "f piecewise_C1_differentiable_on i"
          "g piecewise_C1_differentiable_on i"
    shows "(\<lambda>x. f x + g x) piecewise_C1_differentiable_on i"
proof -
  obtain S t where st: "finite S" "finite t"
                       "f C1_differentiable_on (i-S)"
                       "g C1_differentiable_on (i-t)"
    using assms by (auto simp: piecewise_C1_differentiable_on_def)
  then have "finite (S \<union> t) \<and> (\<lambda>x. f x + g x) C1_differentiable_on i - (S \<union> t)"
    by (auto intro: C1_differentiable_on_add elim!: C1_differentiable_on_subset)
  moreover have "continuous_on i f" "continuous_on i g"
    using assms piecewise_C1_differentiable_on_def by auto
  ultimately show ?thesis
    by (auto simp: piecewise_C1_differentiable_on_def continuous_on_add)
qed

lemma piecewise_C1_differentiable_diff:
    "\<lbrakk>f piecewise_C1_differentiable_on S;  g piecewise_C1_differentiable_on S\<rbrakk>
     \<Longrightarrow> (\<lambda>x. f x - g x) piecewise_C1_differentiable_on S"
  unfolding diff_conv_add_uminus
  by (metis piecewise_C1_differentiable_add piecewise_C1_differentiable_neg)

lemma piecewise_C1_differentiable_D1:
  fixes g1 :: "real \<Rightarrow> 'a::real_normed_field"
  assumes "(g1 +++ g2) piecewise_C1_differentiable_on {0..1}"
    shows "g1 piecewise_C1_differentiable_on {0..1}"
proof -
  obtain S where "finite S"
             and co12: "continuous_on ({0..1} - S) (\<lambda>x. vector_derivative (g1 +++ g2) (at x))"
             and g12D: "\<forall>x\<in>{0..1} - S. g1 +++ g2 differentiable at x"
    using assms  by (auto simp: piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have g1D: "g1 differentiable at x" if "x \<in> {0..1} - insert 1 ((*) 2 ` S)" for x
  proof (rule differentiable_transform_within)
    show "g1 +++ g2 \<circ> (*) (inverse 2) differentiable at x"
      using that g12D
      apply (simp only: joinpaths_def)
      by (rule differentiable_chain_at derivative_intros | force)+
    show "\<And>x'. \<lbrakk>dist x' x < dist (x/2) (1/2)\<rbrakk>
          \<Longrightarrow> (g1 +++ g2 \<circ> (*) (inverse 2)) x' = g1 x'"
      using that by (auto simp: dist_real_def joinpaths_def)
  qed (use that in \<open>auto simp: dist_real_def\<close>)
  have [simp]: "vector_derivative (g1 \<circ> (*) 2) (at (x/2)) = 2 *\<^sub>R vector_derivative g1 (at x)"
               if "x \<in> {0..1} - insert 1 ((*) 2 ` S)" for x
    apply (subst vector_derivative_chain_at)
    using that
    apply (rule derivative_eq_intros g1D | simp)+
    done
  have "continuous_on ({0..1/2} - insert (1/2) S) (\<lambda>x. vector_derivative (g1 +++ g2) (at x))"
    using co12 by (rule continuous_on_subset) force
  then have coDhalf: "continuous_on ({0..1/2} - insert (1/2) S) (\<lambda>x. vector_derivative (g1 \<circ> (*)2) (at x))"
  proof (rule continuous_on_eq [OF _ vector_derivative_at])
    show "(g1 +++ g2 has_vector_derivative vector_derivative (g1 \<circ> (*) 2) (at x)) (at x)"
      if "x \<in> {0..1/2} - insert (1/2) S" for x
    proof (rule has_vector_derivative_transform_within)
      show "(g1 \<circ> (*) 2 has_vector_derivative vector_derivative (g1 \<circ> (*) 2) (at x)) (at x)"
        using that
        by (force intro: g1D differentiable_chain_at simp: vector_derivative_works [symmetric])
      show "\<And>x'. \<lbrakk>dist x' x < dist x (1/2)\<rbrakk> \<Longrightarrow> (g1 \<circ> (*) 2) x' = (g1 +++ g2) x'"
        using that by (auto simp: dist_norm joinpaths_def)
    qed (use that in \<open>auto simp: dist_norm\<close>)
  qed
  have "continuous_on ({0..1} - insert 1 ((*) 2 ` S))
                      ((\<lambda>x. 1/2 * vector_derivative (g1 \<circ> (*)2) (at x)) \<circ> (*)(1/2))"
    apply (rule continuous_intros)+
    using coDhalf
    apply (simp add: scaleR_conv_of_real image_set_diff image_image)
    done
  then have con_g1: "continuous_on ({0..1} - insert 1 ((*) 2 ` S)) (\<lambda>x. vector_derivative g1 (at x))"
    by (rule continuous_on_eq) (simp add: scaleR_conv_of_real)
  have "continuous_on {0..1} g1"
    using continuous_on_joinpaths_D1 assms piecewise_C1_differentiable_on_def by blast
  with \<open>finite S\<close> show ?thesis
    apply (clarsimp simp add: piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
    apply (rule_tac x="insert 1 (((*)2)`S)" in exI)
    apply (simp add: g1D con_g1)
  done
qed

lemma piecewise_C1_differentiable_D2:
  fixes g2 :: "real \<Rightarrow> 'a::real_normed_field"
  assumes "(g1 +++ g2) piecewise_C1_differentiable_on {0..1}" "pathfinish g1 = pathstart g2"
    shows "g2 piecewise_C1_differentiable_on {0..1}"
proof -
  obtain S where "finite S"
             and co12: "continuous_on ({0..1} - S) (\<lambda>x. vector_derivative (g1 +++ g2) (at x))"
             and g12D: "\<forall>x\<in>{0..1} - S. g1 +++ g2 differentiable at x"
    using assms  by (auto simp: piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have g2D: "g2 differentiable at x" if "x \<in> {0..1} - insert 0 ((\<lambda>x. 2*x-1) ` S)" for x
  proof (rule differentiable_transform_within)
    show "g1 +++ g2 \<circ> (\<lambda>x. (x + 1) / 2) differentiable at x"
      using g12D that
      apply (simp only: joinpaths_def)
      apply (drule_tac x= "(x+1) / 2" in bspec, force simp: field_split_simps)
      apply (rule differentiable_chain_at derivative_intros | force)+
      done
    show "\<And>x'. dist x' x < dist ((x + 1) / 2) (1/2) \<Longrightarrow> (g1 +++ g2 \<circ> (\<lambda>x. (x + 1) / 2)) x' = g2 x'"
      using that by (auto simp: dist_real_def joinpaths_def field_simps)
    qed (use that in \<open>auto simp: dist_norm\<close>)
  have [simp]: "vector_derivative (g2 \<circ> (\<lambda>x. 2*x-1)) (at ((x+1)/2)) = 2 *\<^sub>R vector_derivative g2 (at x)"
               if "x \<in> {0..1} - insert 0 ((\<lambda>x. 2*x-1) ` S)" for x
    using that  by (auto simp: vector_derivative_chain_at field_split_simps g2D)
  have "continuous_on ({1/2..1} - insert (1/2) S) (\<lambda>x. vector_derivative (g1 +++ g2) (at x))"
    using co12 by (rule continuous_on_subset) force
  then have coDhalf: "continuous_on ({1/2..1} - insert (1/2) S) (\<lambda>x. vector_derivative (g2 \<circ> (\<lambda>x. 2*x-1)) (at x))"
  proof (rule continuous_on_eq [OF _ vector_derivative_at])
    show "(g1 +++ g2 has_vector_derivative vector_derivative (g2 \<circ> (\<lambda>x. 2 * x - 1)) (at x))
          (at x)"
      if "x \<in> {1 / 2..1} - insert (1 / 2) S" for x
    proof (rule_tac f="g2 \<circ> (\<lambda>x. 2*x-1)" and d="dist (3/4) ((x+1)/2)" in has_vector_derivative_transform_within)
      show "(g2 \<circ> (\<lambda>x. 2 * x - 1) has_vector_derivative vector_derivative (g2 \<circ> (\<lambda>x. 2 * x - 1)) (at x))
            (at x)"
        using that by (force intro: g2D differentiable_chain_at simp: vector_derivative_works [symmetric])
      show "\<And>x'. \<lbrakk>dist x' x < dist (3 / 4) ((x + 1) / 2)\<rbrakk> \<Longrightarrow> (g2 \<circ> (\<lambda>x. 2 * x - 1)) x' = (g1 +++ g2) x'"
        using that by (auto simp: dist_norm joinpaths_def add_divide_distrib)
    qed (use that in \<open>auto simp: dist_norm\<close>)
  qed
  have [simp]: "((\<lambda>x. (x+1) / 2) ` ({0..1} - insert 0 ((\<lambda>x. 2 * x - 1) ` S))) = ({1/2..1} - insert (1/2) S)"
    apply (simp add: image_set_diff inj_on_def image_image)
    apply (auto simp: image_affinity_atLeastAtMost_div add_divide_distrib)
    done
  have "continuous_on ({0..1} - insert 0 ((\<lambda>x. 2*x-1) ` S))
                      ((\<lambda>x. 1/2 * vector_derivative (g2 \<circ> (\<lambda>x. 2*x-1)) (at x)) \<circ> (\<lambda>x. (x+1)/2))"
    by (rule continuous_intros | simp add:  coDhalf)+
  then have con_g2: "continuous_on ({0..1} - insert 0 ((\<lambda>x. 2*x-1) ` S)) (\<lambda>x. vector_derivative g2 (at x))"
    by (rule continuous_on_eq) (simp add: scaleR_conv_of_real)
  have "continuous_on {0..1} g2"
    using continuous_on_joinpaths_D2 assms piecewise_C1_differentiable_on_def by blast
  with \<open>finite S\<close> show ?thesis
    apply (clarsimp simp add: piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
    apply (rule_tac x="insert 0 ((\<lambda>x. 2 * x - 1) ` S)" in exI)
    apply (simp add: g2D con_g2)
  done
qed

subsection \<open>Valid paths, and their start and finish\<close>

definition\<^marker>\<open>tag important\<close> valid_path :: "(real \<Rightarrow> 'a :: real_normed_vector) \<Rightarrow> bool"
  where "valid_path f \<equiv> f piecewise_C1_differentiable_on {0..1::real}"

definition closed_path :: "(real \<Rightarrow> 'a :: real_normed_vector) \<Rightarrow> bool"
  where "closed_path g \<equiv> g 0 = g 1"

text\<open>In particular, all results for paths apply\<close>

lemma valid_path_imp_path: "valid_path g \<Longrightarrow> path g"
  by (simp add: path_def piecewise_C1_differentiable_on_def valid_path_def)

lemma connected_valid_path_image: "valid_path g \<Longrightarrow> connected(path_image g)"
  by (metis connected_path_image valid_path_imp_path)

lemma compact_valid_path_image: "valid_path g \<Longrightarrow> compact(path_image g)"
  by (metis compact_path_image valid_path_imp_path)

lemma bounded_valid_path_image: "valid_path g \<Longrightarrow> bounded(path_image g)"
  by (metis bounded_path_image valid_path_imp_path)

lemma closed_valid_path_image: "valid_path g \<Longrightarrow> closed(path_image g)"
  by (metis closed_path_image valid_path_imp_path)

lemma valid_path_compose:
  assumes "valid_path g"
      and der: "\<And>x. x \<in> path_image g \<Longrightarrow> f field_differentiable (at x)"
      and con: "continuous_on (path_image g) (deriv f)"
    shows "valid_path (f \<circ> g)"
proof -
  obtain S where "finite S" and g_diff: "g C1_differentiable_on {0..1} - S"
    using \<open>valid_path g\<close> unfolding valid_path_def piecewise_C1_differentiable_on_def by auto
  have "f \<circ> g differentiable at t" when "t\<in>{0..1} - S" for t
    proof (rule differentiable_chain_at)
      show "g differentiable at t" using \<open>valid_path g\<close>
        by (meson C1_differentiable_on_eq \<open>g C1_differentiable_on {0..1} - S\<close> that)
    next
      have "g t\<in>path_image g" using that DiffD1 image_eqI path_image_def by metis
      then show "f differentiable at (g t)"
        using der[THEN field_differentiable_imp_differentiable] by auto
    qed
  moreover have "continuous_on ({0..1} - S) (\<lambda>x. vector_derivative (f \<circ> g) (at x))"
    proof (rule continuous_on_eq [where f = "\<lambda>x. vector_derivative g (at x) * deriv f (g x)"],
        rule continuous_intros)
      show "continuous_on ({0..1} - S) (\<lambda>x. vector_derivative g (at x))"
        using g_diff C1_differentiable_on_eq by auto
    next
      have "continuous_on {0..1} (\<lambda>x. deriv f (g x))"
        using continuous_on_compose[OF _ con[unfolded path_image_def],unfolded comp_def]
          \<open>valid_path g\<close> piecewise_C1_differentiable_on_def valid_path_def
        by blast
      then show "continuous_on ({0..1} - S) (\<lambda>x. deriv f (g x))"
        using continuous_on_subset by blast
    next
      show "vector_derivative g (at t) * deriv f (g t) = vector_derivative (f \<circ> g) (at t)"
          when "t \<in> {0..1} - S" for t
        proof (rule vector_derivative_chain_at_general[symmetric])
          show "g differentiable at t" by (meson C1_differentiable_on_eq g_diff that)
        next
          have "g t\<in>path_image g" using that DiffD1 image_eqI path_image_def by metis
          then show "f field_differentiable at (g t)" using der by auto
        qed
    qed
  ultimately have "f \<circ> g C1_differentiable_on {0..1} - S"
    using C1_differentiable_on_eq by blast
  moreover have "path (f \<circ> g)"
    apply (rule path_continuous_image[OF valid_path_imp_path[OF \<open>valid_path g\<close>]])
    using der
    by (simp add: continuous_at_imp_continuous_on field_differentiable_imp_continuous_at)
  ultimately show ?thesis unfolding valid_path_def piecewise_C1_differentiable_on_def path_def
    using \<open>finite S\<close> by auto
qed
  
lemma valid_path_uminus_comp[simp]:
  fixes g::"real \<Rightarrow> 'a ::real_normed_field"
  shows "valid_path (uminus \<circ> g) \<longleftrightarrow> valid_path g"
proof 
  show "valid_path g \<Longrightarrow> valid_path (uminus \<circ> g)" for g::"real \<Rightarrow> 'a"
    by (auto intro!: valid_path_compose derivative_intros simp add: deriv_linear[of "-1",simplified])  
  then show "valid_path g" when "valid_path (uminus \<circ> g)"
    by (metis fun.map_comp group_add_class.minus_comp_minus id_comp that)
qed

lemma valid_path_offset[simp]:
  shows "valid_path (\<lambda>t. g t - z) \<longleftrightarrow> valid_path g"  
proof 
  show *: "valid_path (g::real\<Rightarrow>'a) \<Longrightarrow> valid_path (\<lambda>t. g t - z)" for g z
    unfolding valid_path_def
    by (fastforce intro:derivative_intros C1_differentiable_imp_piecewise piecewise_C1_differentiable_diff)
  show "valid_path (\<lambda>t. g t - z) \<Longrightarrow> valid_path g"
    using *[of "\<lambda>t. g t - z" "-z",simplified] .
qed
  

subsection\<open>Contour Integrals along a path\<close>

text\<open>This definition is for complex numbers only, and does not generalise to line integrals in a vector field\<close>

text\<open>piecewise differentiable function on [0,1]\<close>

definition\<^marker>\<open>tag important\<close> has_contour_integral :: "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> bool"
           (infixr "has'_contour'_integral" 50)
  where "(f has_contour_integral i) g \<equiv>
           ((\<lambda>x. f(g x) * vector_derivative g (at x within {0..1}))
            has_integral i) {0..1}"

definition\<^marker>\<open>tag important\<close> contour_integrable_on
           (infixr "contour'_integrable'_on" 50)
  where "f contour_integrable_on g \<equiv> \<exists>i. (f has_contour_integral i) g"

definition\<^marker>\<open>tag important\<close> contour_integral
  where "contour_integral g f \<equiv> SOME i. (f has_contour_integral i) g \<or> \<not> f contour_integrable_on g \<and> i=0"

lemma not_integrable_contour_integral: "\<not> f contour_integrable_on g \<Longrightarrow> contour_integral g f = 0"
  unfolding contour_integrable_on_def contour_integral_def by blast

lemma contour_integral_unique: "(f has_contour_integral i) g \<Longrightarrow> contour_integral g f = i"
  apply (simp add: contour_integral_def has_contour_integral_def contour_integrable_on_def)
  using has_integral_unique by blast

lemma has_contour_integral_eqpath:
     "\<lbrakk>(f has_contour_integral y) p; f contour_integrable_on \<gamma>;
       contour_integral p f = contour_integral \<gamma> f\<rbrakk>
      \<Longrightarrow> (f has_contour_integral y) \<gamma>"
using contour_integrable_on_def contour_integral_unique by auto

lemma has_contour_integral_integral:
    "f contour_integrable_on i \<Longrightarrow> (f has_contour_integral (contour_integral i f)) i"
  by (metis contour_integral_unique contour_integrable_on_def)

lemma has_contour_integral_unique:
    "(f has_contour_integral i) g \<Longrightarrow> (f has_contour_integral j) g \<Longrightarrow> i = j"
  using has_integral_unique
  by (auto simp: has_contour_integral_def)

lemma has_contour_integral_integrable: "(f has_contour_integral i) g \<Longrightarrow> f contour_integrable_on g"
  using contour_integrable_on_def by blast

text\<open>Show that we can forget about the localized derivative.\<close>

lemma has_integral_localized_vector_derivative:
    "((\<lambda>x. f (g x) * vector_derivative g (at x within {a..b})) has_integral i) {a..b} \<longleftrightarrow>
     ((\<lambda>x. f (g x) * vector_derivative g (at x)) has_integral i) {a..b}"
proof -
  have *: "{a..b} - {a,b} = interior {a..b}"
    by (simp add: atLeastAtMost_diff_ends)
  show ?thesis
    apply (rule has_integral_spike_eq [of "{a,b}"])
    apply (auto simp: at_within_interior [of _ "{a..b}"])
    done
qed

lemma integrable_on_localized_vector_derivative:
    "(\<lambda>x. f (g x) * vector_derivative g (at x within {a..b})) integrable_on {a..b} \<longleftrightarrow>
     (\<lambda>x. f (g x) * vector_derivative g (at x)) integrable_on {a..b}"
  by (simp add: integrable_on_def has_integral_localized_vector_derivative)

lemma has_contour_integral:
     "(f has_contour_integral i) g \<longleftrightarrow>
      ((\<lambda>x. f (g x) * vector_derivative g (at x)) has_integral i) {0..1}"
  by (simp add: has_integral_localized_vector_derivative has_contour_integral_def)

lemma contour_integrable_on:
     "f contour_integrable_on g \<longleftrightarrow>
      (\<lambda>t. f(g t) * vector_derivative g (at t)) integrable_on {0..1}"
  by (simp add: has_contour_integral integrable_on_def contour_integrable_on_def)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Reversing a path\<close>

lemma valid_path_imp_reverse:
  assumes "valid_path g"
    shows "valid_path(reversepath g)"
proof -
  obtain S where "finite S" and S: "g C1_differentiable_on ({0..1} - S)"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def)
  then have "finite ((-) 1 ` S)"
    by auto
  moreover have "(reversepath g C1_differentiable_on ({0..1} - (-) 1 ` S))"
    unfolding reversepath_def
    apply (rule C1_differentiable_compose [of "\<lambda>x::real. 1-x" _ g, unfolded o_def])
    using S
    by (force simp: finite_vimageI inj_on_def C1_differentiable_on_eq elim!: continuous_on_subset)+
  ultimately show ?thesis using assms
    by (auto simp: valid_path_def piecewise_C1_differentiable_on_def path_def [symmetric])
qed

lemma valid_path_reversepath [simp]: "valid_path(reversepath g) \<longleftrightarrow> valid_path g"
  using valid_path_imp_reverse by force

lemma has_contour_integral_reversepath:
  assumes "valid_path g" and f: "(f has_contour_integral i) g"
    shows "(f has_contour_integral (-i)) (reversepath g)"
proof -
  { fix S x
    assume xs: "g C1_differentiable_on ({0..1} - S)" "x \<notin> (-) 1 ` S" "0 \<le> x" "x \<le> 1"
    have "vector_derivative (\<lambda>x. g (1 - x)) (at x within {0..1}) =
            - vector_derivative g (at (1 - x) within {0..1})"
    proof -
      obtain f' where f': "(g has_vector_derivative f') (at (1 - x))"
        using xs
        by (force simp: has_vector_derivative_def C1_differentiable_on_def)
      have "(g \<circ> (\<lambda>x. 1 - x) has_vector_derivative -1 *\<^sub>R f') (at x)"
        by (intro vector_diff_chain_within has_vector_derivative_at_within [OF f'] derivative_eq_intros | simp)+
      then have mf': "((\<lambda>x. g (1 - x)) has_vector_derivative -f') (at x)"
        by (simp add: o_def)
      show ?thesis
        using xs
        by (auto simp: vector_derivative_at_within_ivl [OF mf'] vector_derivative_at_within_ivl [OF f'])
    qed
  } note * = this
  obtain S where S: "continuous_on {0..1} g" "finite S" "g C1_differentiable_on {0..1} - S"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def)
  have "((\<lambda>x. - (f (g (1 - x)) * vector_derivative g (at (1 - x) within {0..1}))) has_integral -i)
       {0..1}"
    using has_integral_affinity01 [where m= "-1" and c=1, OF f [unfolded has_contour_integral_def]]
    by (simp add: has_integral_neg)
  then show ?thesis
    using S
    apply (clarsimp simp: reversepath_def has_contour_integral_def)
    apply (rule_tac S = "(\<lambda>x. 1 - x) ` S" in has_integral_spike_finite)
      apply (auto simp: *)
    done
qed

lemma contour_integrable_reversepath:
    "valid_path g \<Longrightarrow> f contour_integrable_on g \<Longrightarrow> f contour_integrable_on (reversepath g)"
  using has_contour_integral_reversepath contour_integrable_on_def by blast

lemma contour_integrable_reversepath_eq:
    "valid_path g \<Longrightarrow> (f contour_integrable_on (reversepath g) \<longleftrightarrow> f contour_integrable_on g)"
  using contour_integrable_reversepath valid_path_reversepath by fastforce

lemma contour_integral_reversepath:
  assumes "valid_path g"
    shows "contour_integral (reversepath g) f = - (contour_integral g f)"
proof (cases "f contour_integrable_on g")
  case True then show ?thesis
    by (simp add: assms contour_integral_unique has_contour_integral_integral has_contour_integral_reversepath)
next
  case False then have "\<not> f contour_integrable_on (reversepath g)"
    by (simp add: assms contour_integrable_reversepath_eq)
  with False show ?thesis by (simp add: not_integrable_contour_integral)
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>Joining two paths together\<close>

lemma valid_path_join:
  assumes "valid_path g1" "valid_path g2" "pathfinish g1 = pathstart g2"
    shows "valid_path(g1 +++ g2)"
proof -
  have "g1 1 = g2 0"
    using assms by (auto simp: pathfinish_def pathstart_def)
  moreover have "(g1 \<circ> (\<lambda>x. 2*x)) piecewise_C1_differentiable_on {0..1/2}"
    apply (rule piecewise_C1_differentiable_compose)
    using assms
    apply (auto simp: valid_path_def piecewise_C1_differentiable_on_def continuous_on_joinpaths)
    apply (force intro: finite_vimageI [where h = "(*)2"] inj_onI)
    done
  moreover have "(g2 \<circ> (\<lambda>x. 2*x-1)) piecewise_C1_differentiable_on {1/2..1}"
    apply (rule piecewise_C1_differentiable_compose)
    using assms unfolding valid_path_def piecewise_C1_differentiable_on_def
    by (auto intro!: continuous_intros finite_vimageI [where h = "(\<lambda>x. 2*x - 1)"] inj_onI
             simp: image_affinity_atLeastAtMost_diff continuous_on_joinpaths)
  ultimately show ?thesis
    apply (simp only: valid_path_def continuous_on_joinpaths joinpaths_def)
    apply (rule piecewise_C1_differentiable_cases)
    apply (auto simp: o_def)
    done
qed

lemma valid_path_join_D1:
  fixes g1 :: "real \<Rightarrow> 'a::real_normed_field"
  shows "valid_path (g1 +++ g2) \<Longrightarrow> valid_path g1"
  unfolding valid_path_def
  by (rule piecewise_C1_differentiable_D1)

lemma valid_path_join_D2:
  fixes g2 :: "real \<Rightarrow> 'a::real_normed_field"
  shows "\<lbrakk>valid_path (g1 +++ g2); pathfinish g1 = pathstart g2\<rbrakk> \<Longrightarrow> valid_path g2"
  unfolding valid_path_def
  by (rule piecewise_C1_differentiable_D2)

lemma valid_path_join_eq [simp]:
  fixes g2 :: "real \<Rightarrow> 'a::real_normed_field"
  shows "pathfinish g1 = pathstart g2 \<Longrightarrow> (valid_path(g1 +++ g2) \<longleftrightarrow> valid_path g1 \<and> valid_path g2)"
  using valid_path_join_D1 valid_path_join_D2 valid_path_join by blast

lemma has_contour_integral_join:
  assumes "(f has_contour_integral i1) g1" "(f has_contour_integral i2) g2"
          "valid_path g1" "valid_path g2"
    shows "(f has_contour_integral (i1 + i2)) (g1 +++ g2)"
proof -
  obtain s1 s2
    where s1: "finite s1" "\<forall>x\<in>{0..1} - s1. g1 differentiable at x"
      and s2: "finite s2" "\<forall>x\<in>{0..1} - s2. g2 differentiable at x"
    using assms
    by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have 1: "((\<lambda>x. f (g1 x) * vector_derivative g1 (at x)) has_integral i1) {0..1}"
   and 2: "((\<lambda>x. f (g2 x) * vector_derivative g2 (at x)) has_integral i2) {0..1}"
    using assms
    by (auto simp: has_contour_integral)
  have i1: "((\<lambda>x. (2*f (g1 (2*x))) * vector_derivative g1 (at (2*x))) has_integral i1) {0..1/2}"
   and i2: "((\<lambda>x. (2*f (g2 (2*x - 1))) * vector_derivative g2 (at (2*x - 1))) has_integral i2) {1/2..1}"
    using has_integral_affinity01 [OF 1, where m= 2 and c=0, THEN has_integral_cmul [where c=2]]
          has_integral_affinity01 [OF 2, where m= 2 and c="-1", THEN has_integral_cmul [where c=2]]
    by (simp_all only: image_affinity_atLeastAtMost_div_diff, simp_all add: scaleR_conv_of_real mult_ac)
  have g1: "\<lbrakk>0 \<le> z; z*2 < 1; z*2 \<notin> s1\<rbrakk> \<Longrightarrow>
            vector_derivative (\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) (at z) =
            2 *\<^sub>R vector_derivative g1 (at (z*2))" for z
    apply (rule vector_derivative_at [OF has_vector_derivative_transform_within [where f = "(\<lambda>x. g1(2*x))" and d = "\<bar>z - 1/2\<bar>"]])
    apply (simp_all add: dist_real_def abs_if split: if_split_asm)
    apply (rule vector_diff_chain_at [of "\<lambda>x. 2*x" 2 _ g1, simplified o_def])
    apply (simp add: has_vector_derivative_def has_derivative_def bounded_linear_mult_left)
    using s1
    apply (auto simp: algebra_simps vector_derivative_works)
    done
  have g2: "\<lbrakk>1 < z*2; z \<le> 1; z*2 - 1 \<notin> s2\<rbrakk> \<Longrightarrow>
            vector_derivative (\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) (at z) =
            2 *\<^sub>R vector_derivative g2 (at (z*2 - 1))" for z
    apply (rule vector_derivative_at [OF has_vector_derivative_transform_within [where f = "(\<lambda>x. g2 (2*x - 1))" and d = "\<bar>z - 1/2\<bar>"]])
    apply (simp_all add: dist_real_def abs_if split: if_split_asm)
    apply (rule vector_diff_chain_at [of "\<lambda>x. 2*x - 1" 2 _ g2, simplified o_def])
    apply (simp add: has_vector_derivative_def has_derivative_def bounded_linear_mult_left)
    using s2
    apply (auto simp: algebra_simps vector_derivative_works)
    done
  have "((\<lambda>x. f ((g1 +++ g2) x) * vector_derivative (g1 +++ g2) (at x)) has_integral i1) {0..1/2}"
    apply (rule has_integral_spike_finite [OF _ _ i1, of "insert (1/2) ((*)2 -` s1)"])
    using s1
    apply (force intro: finite_vimageI [where h = "(*)2"] inj_onI)
    apply (clarsimp simp add: joinpaths_def scaleR_conv_of_real mult_ac g1)
    done
  moreover have "((\<lambda>x. f ((g1 +++ g2) x) * vector_derivative (g1 +++ g2) (at x)) has_integral i2) {1/2..1}"
    apply (rule has_integral_spike_finite [OF _ _ i2, of "insert (1/2) ((\<lambda>x. 2*x-1) -` s2)"])
    using s2
    apply (force intro: finite_vimageI [where h = "\<lambda>x. 2*x-1"] inj_onI)
    apply (clarsimp simp add: joinpaths_def scaleR_conv_of_real mult_ac g2)
    done
  ultimately
  show ?thesis
    apply (simp add: has_contour_integral)
    apply (rule has_integral_combine [where c = "1/2"], auto)
    done
qed

lemma contour_integrable_joinI:
  assumes "f contour_integrable_on g1" "f contour_integrable_on g2"
          "valid_path g1" "valid_path g2"
    shows "f contour_integrable_on (g1 +++ g2)"
  using assms
  by (meson has_contour_integral_join contour_integrable_on_def)

lemma contour_integrable_joinD1:
  assumes "f contour_integrable_on (g1 +++ g2)" "valid_path g1"
    shows "f contour_integrable_on g1"
proof -
  obtain s1
    where s1: "finite s1" "\<forall>x\<in>{0..1} - s1. g1 differentiable at x"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have "(\<lambda>x. f ((g1 +++ g2) (x/2)) * vector_derivative (g1 +++ g2) (at (x/2))) integrable_on {0..1}"
    using assms
    apply (auto simp: contour_integrable_on)
    apply (drule integrable_on_subcbox [where a=0 and b="1/2"])
    apply (auto intro: integrable_affinity [of _ 0 "1/2::real" "1/2" 0, simplified])
    done
  then have *: "(\<lambda>x. (f ((g1 +++ g2) (x/2))/2) * vector_derivative (g1 +++ g2) (at (x/2))) integrable_on {0..1}"
    by (auto dest: integrable_cmul [where c="1/2"] simp: scaleR_conv_of_real)
  have g1: "\<lbrakk>0 < z; z < 1; z \<notin> s1\<rbrakk> \<Longrightarrow>
            vector_derivative (\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) (at (z/2)) =
            2 *\<^sub>R vector_derivative g1 (at z)"  for z
    apply (rule vector_derivative_at [OF has_vector_derivative_transform_within [where f = "(\<lambda>x. g1(2*x))" and d = "\<bar>(z-1)/2\<bar>"]])
    apply (simp_all add: field_simps dist_real_def abs_if split: if_split_asm)
    apply (rule vector_diff_chain_at [of "\<lambda>x. x*2" 2 _ g1, simplified o_def])
    using s1
    apply (auto simp: vector_derivative_works has_vector_derivative_def has_derivative_def bounded_linear_mult_left)
    done
  show ?thesis
    using s1
    apply (auto simp: contour_integrable_on)
    apply (rule integrable_spike_finite [of "{0,1} \<union> s1", OF _ _ *])
    apply (auto simp: joinpaths_def scaleR_conv_of_real g1)
    done
qed

lemma contour_integrable_joinD2:
  assumes "f contour_integrable_on (g1 +++ g2)" "valid_path g2"
    shows "f contour_integrable_on g2"
proof -
  obtain s2
    where s2: "finite s2" "\<forall>x\<in>{0..1} - s2. g2 differentiable at x"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have "(\<lambda>x. f ((g1 +++ g2) (x/2 + 1/2)) * vector_derivative (g1 +++ g2) (at (x/2 + 1/2))) integrable_on {0..1}"
    using assms
    apply (auto simp: contour_integrable_on)
    apply (drule integrable_on_subcbox [where a="1/2" and b=1], auto)
    apply (drule integrable_affinity [of _ "1/2::real" 1 "1/2" "1/2", simplified])
    apply (simp add: image_affinity_atLeastAtMost_diff)
    done
  then have *: "(\<lambda>x. (f ((g1 +++ g2) (x/2 + 1/2))/2) * vector_derivative (g1 +++ g2) (at (x/2 + 1/2)))
                integrable_on {0..1}"
    by (auto dest: integrable_cmul [where c="1/2"] simp: scaleR_conv_of_real)
  have g2: "\<lbrakk>0 < z; z < 1; z \<notin> s2\<rbrakk> \<Longrightarrow>
            vector_derivative (\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) (at (z/2+1/2)) =
            2 *\<^sub>R vector_derivative g2 (at z)" for z
    apply (rule vector_derivative_at [OF has_vector_derivative_transform_within [where f = "(\<lambda>x. g2(2*x-1))" and d = "\<bar>z/2\<bar>"]])
    apply (simp_all add: field_simps dist_real_def abs_if split: if_split_asm)
    apply (rule vector_diff_chain_at [of "\<lambda>x. x*2-1" 2 _ g2, simplified o_def])
    using s2
    apply (auto simp: has_vector_derivative_def has_derivative_def bounded_linear_mult_left
                      vector_derivative_works add_divide_distrib)
    done
  show ?thesis
    using s2
    apply (auto simp: contour_integrable_on)
    apply (rule integrable_spike_finite [of "{0,1} \<union> s2", OF _ _ *])
    apply (auto simp: joinpaths_def scaleR_conv_of_real g2)
    done
qed

lemma contour_integrable_join [simp]:
  shows
    "\<lbrakk>valid_path g1; valid_path g2\<rbrakk>
     \<Longrightarrow> f contour_integrable_on (g1 +++ g2) \<longleftrightarrow> f contour_integrable_on g1 \<and> f contour_integrable_on g2"
using contour_integrable_joinD1 contour_integrable_joinD2 contour_integrable_joinI by blast

lemma contour_integral_join [simp]:
  shows
    "\<lbrakk>f contour_integrable_on g1; f contour_integrable_on g2; valid_path g1; valid_path g2\<rbrakk>
        \<Longrightarrow> contour_integral (g1 +++ g2) f = contour_integral g1 f + contour_integral g2 f"
  by (simp add: has_contour_integral_integral has_contour_integral_join contour_integral_unique)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Shifting the starting point of a (closed) path\<close>

lemma shiftpath_alt_def: "shiftpath a f = (\<lambda>x. if x \<le> 1-a then f (a + x) else f (a + x - 1))"
  by (auto simp: shiftpath_def)

lemma valid_path_shiftpath [intro]:
  assumes "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "valid_path(shiftpath a g)"
  using assms
  apply (auto simp: valid_path_def shiftpath_alt_def)
  apply (rule piecewise_C1_differentiable_cases)
  apply (auto simp: algebra_simps)
  apply (rule piecewise_C1_differentiable_affine [of g 1 a, simplified o_def scaleR_one])
  apply (auto simp: pathfinish_def pathstart_def elim: piecewise_C1_differentiable_on_subset)
  apply (rule piecewise_C1_differentiable_affine [of g 1 "a-1", simplified o_def scaleR_one algebra_simps])
  apply (auto simp: pathfinish_def pathstart_def elim: piecewise_C1_differentiable_on_subset)
  done

lemma has_contour_integral_shiftpath:
  assumes f: "(f has_contour_integral i) g" "valid_path g"
      and a: "a \<in> {0..1}"
    shows "(f has_contour_integral i) (shiftpath a g)"
proof -
  obtain s
    where s: "finite s" and g: "\<forall>x\<in>{0..1} - s. g differentiable at x"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have *: "((\<lambda>x. f (g x) * vector_derivative g (at x)) has_integral i) {0..1}"
    using assms by (auto simp: has_contour_integral)
  then have i: "i = integral {a..1} (\<lambda>x. f (g x) * vector_derivative g (at x)) +
                    integral {0..a} (\<lambda>x. f (g x) * vector_derivative g (at x))"
    apply (rule has_integral_unique)
    apply (subst add.commute)
    apply (subst integral_combine)
    using assms * integral_unique by auto
  { fix x
    have "0 \<le> x \<Longrightarrow> x + a < 1 \<Longrightarrow> x \<notin> (\<lambda>x. x - a) ` s \<Longrightarrow>
         vector_derivative (shiftpath a g) (at x) = vector_derivative g (at (x + a))"
      unfolding shiftpath_def
      apply (rule vector_derivative_at [OF has_vector_derivative_transform_within [where f = "(\<lambda>x. g(a+x))" and d = "dist(1-a) x"]])
        apply (auto simp: field_simps dist_real_def abs_if split: if_split_asm)
      apply (rule vector_diff_chain_at [of "\<lambda>x. x+a" 1 _ g, simplified o_def scaleR_one])
       apply (intro derivative_eq_intros | simp)+
      using g
       apply (drule_tac x="x+a" in bspec)
      using a apply (auto simp: has_vector_derivative_def vector_derivative_works image_def add.commute)
      done
  } note vd1 = this
  { fix x
    have "1 < x + a \<Longrightarrow> x \<le> 1 \<Longrightarrow> x \<notin> (\<lambda>x. x - a + 1) ` s \<Longrightarrow>
          vector_derivative (shiftpath a g) (at x) = vector_derivative g (at (x + a - 1))"
      unfolding shiftpath_def
      apply (rule vector_derivative_at [OF has_vector_derivative_transform_within [where f = "(\<lambda>x. g(a+x-1))" and d = "dist (1-a) x"]])
        apply (auto simp: field_simps dist_real_def abs_if split: if_split_asm)
      apply (rule vector_diff_chain_at [of "\<lambda>x. x+a-1" 1 _ g, simplified o_def scaleR_one])
       apply (intro derivative_eq_intros | simp)+
      using g
      apply (drule_tac x="x+a-1" in bspec)
      using a apply (auto simp: has_vector_derivative_def vector_derivative_works image_def add.commute)
      done
  } note vd2 = this
  have va1: "(\<lambda>x. f (g x) * vector_derivative g (at x)) integrable_on ({a..1})"
    using * a   by (fastforce intro: integrable_subinterval_real)
  have v0a: "(\<lambda>x. f (g x) * vector_derivative g (at x)) integrable_on ({0..a})"
    apply (rule integrable_subinterval_real)
    using * a by auto
  have "((\<lambda>x. f (shiftpath a g x) * vector_derivative (shiftpath a g) (at x))
        has_integral  integral {a..1} (\<lambda>x. f (g x) * vector_derivative g (at x)))  {0..1 - a}"
    apply (rule has_integral_spike_finite
             [where S = "{1-a} \<union> (\<lambda>x. x-a) ` s" and f = "\<lambda>x. f(g(a+x)) * vector_derivative g (at(a+x))"])
      using s apply blast
     using a apply (auto simp: algebra_simps vd1)
     apply (force simp: shiftpath_def add.commute)
    using has_integral_affinity [where m=1 and c=a, simplified, OF integrable_integral [OF va1]]
    apply (simp add: image_affinity_atLeastAtMost_diff [where m=1 and c=a, simplified] add.commute)
    done
  moreover
  have "((\<lambda>x. f (shiftpath a g x) * vector_derivative (shiftpath a g) (at x))
        has_integral  integral {0..a} (\<lambda>x. f (g x) * vector_derivative g (at x)))  {1 - a..1}"
    apply (rule has_integral_spike_finite
             [where S = "{1-a} \<union> (\<lambda>x. x-a+1) ` s" and f = "\<lambda>x. f(g(a+x-1)) * vector_derivative g (at(a+x-1))"])
      using s apply blast
     using a apply (auto simp: algebra_simps vd2)
     apply (force simp: shiftpath_def add.commute)
    using has_integral_affinity [where m=1 and c="a-1", simplified, OF integrable_integral [OF v0a]]
    apply (simp add: image_affinity_atLeastAtMost [where m=1 and c="1-a", simplified])
    apply (simp add: algebra_simps)
    done
  ultimately show ?thesis
    using a
    by (auto simp: i has_contour_integral intro: has_integral_combine [where c = "1-a"])
qed

lemma has_contour_integral_shiftpath_D:
  assumes "(f has_contour_integral i) (shiftpath a g)"
          "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "(f has_contour_integral i) g"
proof -
  obtain s
    where s: "finite s" and g: "\<forall>x\<in>{0..1} - s. g differentiable at x"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  { fix x
    assume x: "0 < x" "x < 1" "x \<notin> s"
    then have gx: "g differentiable at x"
      using g by auto
    have "vector_derivative g (at x within {0..1}) =
          vector_derivative (shiftpath (1 - a) (shiftpath a g)) (at x within {0..1})"
      apply (rule vector_derivative_at_within_ivl
                  [OF has_vector_derivative_transform_within_open
                      [where f = "(shiftpath (1 - a) (shiftpath a g))" and S = "{0<..<1}-s"]])
      using s g assms x
      apply (auto simp: finite_imp_closed open_Diff shiftpath_shiftpath
                        at_within_interior [of _ "{0..1}"] vector_derivative_works [symmetric])
      apply (rule differentiable_transform_within [OF gx, of "min x (1-x)"])
      apply (auto simp: dist_real_def shiftpath_shiftpath abs_if split: if_split_asm)
      done
  } note vd = this
  have fi: "(f has_contour_integral i) (shiftpath (1 - a) (shiftpath a g))"
    using assms  by (auto intro!: has_contour_integral_shiftpath)
  show ?thesis
    apply (simp add: has_contour_integral_def)
    apply (rule has_integral_spike_finite [of "{0,1} \<union> s", OF _ _  fi [unfolded has_contour_integral_def]])
    using s assms vd
    apply (auto simp: Path_Connected.shiftpath_shiftpath)
    done
qed

lemma has_contour_integral_shiftpath_eq:
  assumes "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "(f has_contour_integral i) (shiftpath a g) \<longleftrightarrow> (f has_contour_integral i) g"
  using assms has_contour_integral_shiftpath has_contour_integral_shiftpath_D by blast

lemma contour_integrable_on_shiftpath_eq:
  assumes "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "f contour_integrable_on (shiftpath a g) \<longleftrightarrow> f contour_integrable_on g"
using assms contour_integrable_on_def has_contour_integral_shiftpath_eq by auto

lemma contour_integral_shiftpath:
  assumes "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "contour_integral (shiftpath a g) f = contour_integral g f"
   using assms
   by (simp add: contour_integral_def contour_integrable_on_def has_contour_integral_shiftpath_eq)


subsection\<^marker>\<open>tag unimportant\<close> \<open>More about straight-line paths\<close>

lemma has_vector_derivative_linepath_within:
    "(linepath a b has_vector_derivative (b - a)) (at x within s)"
apply (simp add: linepath_def has_vector_derivative_def algebra_simps)
apply (rule derivative_eq_intros | simp)+
done

lemma vector_derivative_linepath_within:
    "x \<in> {0..1} \<Longrightarrow> vector_derivative (linepath a b) (at x within {0..1}) = b - a"
  apply (rule vector_derivative_within_cbox [of 0 "1::real", simplified])
  apply (auto simp: has_vector_derivative_linepath_within)
  done

lemma vector_derivative_linepath_at [simp]: "vector_derivative (linepath a b) (at x) = b - a"
  by (simp add: has_vector_derivative_linepath_within vector_derivative_at)

lemma valid_path_linepath [iff]: "valid_path (linepath a b)"
  apply (simp add: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq continuous_on_linepath)
  apply (rule_tac x="{}" in exI)
  apply (simp add: differentiable_on_def differentiable_def)
  using has_vector_derivative_def has_vector_derivative_linepath_within
  apply (fastforce simp add: continuous_on_eq_continuous_within)
  done

lemma has_contour_integral_linepath:
  shows "(f has_contour_integral i) (linepath a b) \<longleftrightarrow>
         ((\<lambda>x. f(linepath a b x) * (b - a)) has_integral i) {0..1}"
  by (simp add: has_contour_integral)

lemma linepath_in_path:
  shows "x \<in> {0..1} \<Longrightarrow> linepath a b x \<in> closed_segment a b"
  by (auto simp: segment linepath_def)

lemma linepath_image_01: "linepath a b ` {0..1} = closed_segment a b"
  by (auto simp: segment linepath_def)

lemma linepath_in_convex_hull:
    fixes x::real
    assumes a: "a \<in> convex hull s"
        and b: "b \<in> convex hull s"
        and x: "0\<le>x" "x\<le>1"
       shows "linepath a b x \<in> convex hull s"
  apply (rule closed_segment_subset_convex_hull [OF a b, THEN subsetD])
  using x
  apply (auto simp: linepath_image_01 [symmetric])
  done

lemma Re_linepath: "Re(linepath (of_real a) (of_real b) x) = (1 - x)*a + x*b"
  by (simp add: linepath_def)

lemma Im_linepath: "Im(linepath (of_real a) (of_real b) x) = 0"
  by (simp add: linepath_def)

lemma has_contour_integral_trivial [iff]: "(f has_contour_integral 0) (linepath a a)"
  by (simp add: has_contour_integral_linepath)

lemma has_contour_integral_trivial_iff [simp]: "(f has_contour_integral i) (linepath a a) \<longleftrightarrow> i=0"
  using has_contour_integral_unique by blast

lemma contour_integral_trivial [simp]: "contour_integral (linepath a a) f = 0"
  using has_contour_integral_trivial contour_integral_unique by blast

lemma differentiable_linepath [intro]: "linepath a b differentiable at x within A"
  by (auto simp: linepath_def)

lemma bounded_linear_linepath:
  assumes "bounded_linear f"
  shows   "f (linepath a b x) = linepath (f a) (f b) x"
proof -
  interpret f: bounded_linear f by fact
  show ?thesis by (simp add: linepath_def f.add f.scale)
qed

lemma bounded_linear_linepath':
  assumes "bounded_linear f"
  shows   "f \<circ> linepath a b = linepath (f a) (f b)"
  using bounded_linear_linepath[OF assms] by (simp add: fun_eq_iff)

lemma cnj_linepath: "cnj (linepath a b x) = linepath (cnj a) (cnj b) x"
  by (simp add: linepath_def)

lemma cnj_linepath': "cnj \<circ> linepath a b = linepath (cnj a) (cnj b)"
  by (simp add: linepath_def fun_eq_iff)

subsection\<open>Relation to subpath construction\<close>

lemma valid_path_subpath:
  fixes g :: "real \<Rightarrow> 'a :: real_normed_vector"
  assumes "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}"
    shows "valid_path(subpath u v g)"
proof (cases "v=u")
  case True
  then show ?thesis
    unfolding valid_path_def subpath_def
    by (force intro: C1_differentiable_on_const C1_differentiable_imp_piecewise)
next
  case False
  have "(g \<circ> (\<lambda>x. ((v-u) * x + u))) piecewise_C1_differentiable_on {0..1}"
    apply (rule piecewise_C1_differentiable_compose)
    apply (simp add: C1_differentiable_imp_piecewise)
     apply (simp add: image_affinity_atLeastAtMost)
    using assms False
    apply (auto simp: algebra_simps valid_path_def piecewise_C1_differentiable_on_subset)
    apply (subst Int_commute)
    apply (auto simp: inj_on_def algebra_simps crossproduct_eq finite_vimage_IntI)
    done
  then show ?thesis
    by (auto simp: o_def valid_path_def subpath_def)
qed

lemma has_contour_integral_subpath_refl [iff]: "(f has_contour_integral 0) (subpath u u g)"
  by (simp add: has_contour_integral subpath_def)

lemma contour_integrable_subpath_refl [iff]: "f contour_integrable_on (subpath u u g)"
  using has_contour_integral_subpath_refl contour_integrable_on_def by blast

lemma contour_integral_subpath_refl [simp]: "contour_integral (subpath u u g) f = 0"
  by (simp add: contour_integral_unique)

lemma has_contour_integral_subpath:
  assumes f: "f contour_integrable_on g" and g: "valid_path g"
      and uv: "u \<in> {0..1}" "v \<in> {0..1}" "u \<le> v"
    shows "(f has_contour_integral  integral {u..v} (\<lambda>x. f(g x) * vector_derivative g (at x)))
           (subpath u v g)"
proof (cases "v=u")
  case True
  then show ?thesis
    using f   by (simp add: contour_integrable_on_def subpath_def has_contour_integral)
next
  case False
  obtain s where s: "\<And>x. x \<in> {0..1} - s \<Longrightarrow> g differentiable at x" and fs: "finite s"
    using g unfolding piecewise_C1_differentiable_on_def C1_differentiable_on_eq valid_path_def by blast
  have *: "((\<lambda>x. f (g ((v - u) * x + u)) * vector_derivative g (at ((v - u) * x + u)))
            has_integral (1 / (v - u)) * integral {u..v} (\<lambda>t. f (g t) * vector_derivative g (at t)))
           {0..1}"
    using f uv
    apply (simp add: contour_integrable_on subpath_def has_contour_integral)
    apply (drule integrable_on_subcbox [where a=u and b=v, simplified])
    apply (simp_all add: has_integral_integral)
    apply (drule has_integral_affinity [where m="v-u" and c=u, simplified])
    apply (simp_all add: False image_affinity_atLeastAtMost_div_diff scaleR_conv_of_real)
    apply (simp add: divide_simps False)
    done
  { fix x
    have "x \<in> {0..1} \<Longrightarrow>
           x \<notin> (\<lambda>t. (v-u) *\<^sub>R t + u) -` s \<Longrightarrow>
           vector_derivative (\<lambda>x. g ((v-u) * x + u)) (at x) = (v-u) *\<^sub>R vector_derivative g (at ((v-u) * x + u))"
      apply (rule vector_derivative_at [OF vector_diff_chain_at [simplified o_def]])
      apply (intro derivative_eq_intros | simp)+
      apply (cut_tac s [of "(v - u) * x + u"])
      using uv mult_left_le [of x "v-u"]
      apply (auto simp:  vector_derivative_works)
      done
  } note vd = this
  show ?thesis
    apply (cut_tac has_integral_cmul [OF *, where c = "v-u"])
    using fs assms
    apply (simp add: False subpath_def has_contour_integral)
    apply (rule_tac S = "(\<lambda>t. ((v-u) *\<^sub>R t + u)) -` s" in has_integral_spike_finite)
    apply (auto simp: inj_on_def False finite_vimageI vd scaleR_conv_of_real)
    done
qed

lemma contour_integrable_subpath:
  assumes "f contour_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}"
    shows "f contour_integrable_on (subpath u v g)"
  apply (cases u v rule: linorder_class.le_cases)
   apply (metis contour_integrable_on_def has_contour_integral_subpath [OF assms])
  apply (subst reversepath_subpath [symmetric])
  apply (rule contour_integrable_reversepath)
   using assms apply (blast intro: valid_path_subpath)
  apply (simp add: contour_integrable_on_def)
  using assms apply (blast intro: has_contour_integral_subpath)
  done

lemma has_integral_contour_integral_subpath:
  assumes "f contour_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}" "u \<le> v"
    shows "(((\<lambda>x. f(g x) * vector_derivative g (at x)))
            has_integral  contour_integral (subpath u v g) f) {u..v}"
  using assms
  apply (auto simp: has_integral_integrable_integral)
  apply (rule integrable_on_subcbox [where a=u and b=v and S = "{0..1}", simplified])
  apply (auto simp: contour_integral_unique [OF has_contour_integral_subpath] contour_integrable_on)
  done

lemma contour_integral_subcontour_integral:
  assumes "f contour_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}" "u \<le> v"
    shows "contour_integral (subpath u v g) f =
           integral {u..v} (\<lambda>x. f(g x) * vector_derivative g (at x))"
  using assms has_contour_integral_subpath contour_integral_unique by blast

lemma contour_integral_subpath_combine_less:
  assumes "f contour_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}" "w \<in> {0..1}"
          "u<v" "v<w"
    shows "contour_integral (subpath u v g) f + contour_integral (subpath v w g) f =
           contour_integral (subpath u w g) f"
  using assms apply (auto simp: contour_integral_subcontour_integral)
  apply (rule integral_combine, auto)
  apply (rule integrable_on_subcbox [where a=u and b=w and S = "{0..1}", simplified])
  apply (auto simp: contour_integrable_on)
  done

lemma contour_integral_subpath_combine:
  assumes "f contour_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}" "w \<in> {0..1}"
    shows "contour_integral (subpath u v g) f + contour_integral (subpath v w g) f =
           contour_integral (subpath u w g) f"
proof (cases "u\<noteq>v \<and> v\<noteq>w \<and> u\<noteq>w")
  case True
    have *: "subpath v u g = reversepath(subpath u v g) \<and>
             subpath w u g = reversepath(subpath u w g) \<and>
             subpath w v g = reversepath(subpath v w g)"
      by (auto simp: reversepath_subpath)
    have "u < v \<and> v < w \<or>
          u < w \<and> w < v \<or>
          v < u \<and> u < w \<or>
          v < w \<and> w < u \<or>
          w < u \<and> u < v \<or>
          w < v \<and> v < u"
      using True assms by linarith
    with assms show ?thesis
      using contour_integral_subpath_combine_less [of f g u v w]
            contour_integral_subpath_combine_less [of f g u w v]
            contour_integral_subpath_combine_less [of f g v u w]
            contour_integral_subpath_combine_less [of f g v w u]
            contour_integral_subpath_combine_less [of f g w u v]
            contour_integral_subpath_combine_less [of f g w v u]
      apply simp
      apply (elim disjE)
      apply (auto simp: * contour_integral_reversepath contour_integrable_subpath
               valid_path_subpath algebra_simps)
      done
next
  case False
  then show ?thesis
    apply (auto)
    using assms
    by (metis eq_neg_iff_add_eq_0 contour_integral_reversepath reversepath_subpath valid_path_subpath)
qed

lemma contour_integral_integral:
     "contour_integral g f = integral {0..1} (\<lambda>x. f (g x) * vector_derivative g (at x))"
  by (simp add: contour_integral_def integral_def has_contour_integral contour_integrable_on)

lemma contour_integral_cong:
  assumes "g = g'" "\<And>x. x \<in> path_image g \<Longrightarrow> f x = f' x"
  shows   "contour_integral g f = contour_integral g' f'"
  unfolding contour_integral_integral using assms
  by (intro integral_cong) (auto simp: path_image_def)


text \<open>Contour integral along a segment on the real axis\<close>

lemma has_contour_integral_linepath_Reals_iff:
  fixes a b :: complex and f :: "complex \<Rightarrow> complex"
  assumes "a \<in> Reals" "b \<in> Reals" "Re a < Re b"
  shows   "(f has_contour_integral I) (linepath a b) \<longleftrightarrow>
             ((\<lambda>x. f (of_real x)) has_integral I) {Re a..Re b}"
proof -
  from assms have [simp]: "of_real (Re a) = a" "of_real (Re b) = b"
    by (simp_all add: complex_eq_iff)
  from assms have "a \<noteq> b" by auto
  have "((\<lambda>x. f (of_real x)) has_integral I) (cbox (Re a) (Re b)) \<longleftrightarrow>
          ((\<lambda>x. f (a + b * of_real x - a * of_real x)) has_integral I /\<^sub>R (Re b - Re a)) {0..1}"
    by (subst has_integral_affinity_iff [of "Re b - Re a" _ "Re a", symmetric])
       (insert assms, simp_all add: field_simps scaleR_conv_of_real)
  also have "(\<lambda>x. f (a + b * of_real x - a * of_real x)) =
               (\<lambda>x. (f (a + b * of_real x - a * of_real x) * (b - a)) /\<^sub>R (Re b - Re a))"
    using \<open>a \<noteq> b\<close> by (auto simp: field_simps fun_eq_iff scaleR_conv_of_real)
  also have "(\<dots> has_integral I /\<^sub>R (Re b - Re a)) {0..1} \<longleftrightarrow> 
               ((\<lambda>x. f (linepath a b x) * (b - a)) has_integral I) {0..1}" using assms
    by (subst has_integral_cmul_iff) (auto simp: linepath_def scaleR_conv_of_real algebra_simps)
  also have "\<dots> \<longleftrightarrow> (f has_contour_integral I) (linepath a b)" unfolding has_contour_integral_def
    by (intro has_integral_cong) (simp add: vector_derivative_linepath_within)
  finally show ?thesis by simp
qed

lemma contour_integrable_linepath_Reals_iff:
  fixes a b :: complex and f :: "complex \<Rightarrow> complex"
  assumes "a \<in> Reals" "b \<in> Reals" "Re a < Re b"
  shows   "(f contour_integrable_on linepath a b) \<longleftrightarrow>
             (\<lambda>x. f (of_real x)) integrable_on {Re a..Re b}"
  using has_contour_integral_linepath_Reals_iff[OF assms, of f]
  by (auto simp: contour_integrable_on_def integrable_on_def)

lemma contour_integral_linepath_Reals_eq:
  fixes a b :: complex and f :: "complex \<Rightarrow> complex"
  assumes "a \<in> Reals" "b \<in> Reals" "Re a < Re b"
  shows   "contour_integral (linepath a b) f = integral {Re a..Re b} (\<lambda>x. f (of_real x))"
proof (cases "f contour_integrable_on linepath a b")
  case True
  thus ?thesis using has_contour_integral_linepath_Reals_iff[OF assms, of f]
    using has_contour_integral_integral has_contour_integral_unique by blast
next
  case False
  thus ?thesis using contour_integrable_linepath_Reals_iff[OF assms, of f]
    by (simp add: not_integrable_contour_integral not_integrable_integral)
qed



text\<open>Cauchy's theorem where there's a primitive\<close>

lemma contour_integral_primitive_lemma:
  fixes f :: "complex \<Rightarrow> complex" and g :: "real \<Rightarrow> complex"
  assumes "a \<le> b"
      and "\<And>x. x \<in> s \<Longrightarrow> (f has_field_derivative f' x) (at x within s)"
      and "g piecewise_differentiable_on {a..b}"  "\<And>x. x \<in> {a..b} \<Longrightarrow> g x \<in> s"
    shows "((\<lambda>x. f'(g x) * vector_derivative g (at x within {a..b}))
             has_integral (f(g b) - f(g a))) {a..b}"
proof -
  obtain k where k: "finite k" "\<forall>x\<in>{a..b} - k. g differentiable (at x within {a..b})" and cg: "continuous_on {a..b} g"
    using assms by (auto simp: piecewise_differentiable_on_def)
  have cfg: "continuous_on {a..b} (\<lambda>x. f (g x))"
    apply (rule continuous_on_compose [OF cg, unfolded o_def])
    using assms
    apply (metis field_differentiable_def field_differentiable_imp_continuous_at continuous_on_eq_continuous_within continuous_on_subset image_subset_iff)
    done
  { fix x::real
    assume a: "a < x" and b: "x < b" and xk: "x \<notin> k"
    then have "g differentiable at x within {a..b}"
      using k by (simp add: differentiable_at_withinI)
    then have "(g has_vector_derivative vector_derivative g (at x within {a..b})) (at x within {a..b})"
      by (simp add: vector_derivative_works has_field_derivative_def scaleR_conv_of_real)
    then have gdiff: "(g has_derivative (\<lambda>u. u * vector_derivative g (at x within {a..b}))) (at x within {a..b})"
      by (simp add: has_vector_derivative_def scaleR_conv_of_real)
    have "(f has_field_derivative (f' (g x))) (at (g x) within g ` {a..b})"
      using assms by (metis a atLeastAtMost_iff b DERIV_subset image_subset_iff less_eq_real_def)
    then have fdiff: "(f has_derivative (*) (f' (g x))) (at (g x) within g ` {a..b})"
      by (simp add: has_field_derivative_def)
    have "((\<lambda>x. f (g x)) has_vector_derivative f' (g x) * vector_derivative g (at x within {a..b})) (at x within {a..b})"
      using diff_chain_within [OF gdiff fdiff]
      by (simp add: has_vector_derivative_def scaleR_conv_of_real o_def mult_ac)
  } note * = this
  show ?thesis
    apply (rule fundamental_theorem_of_calculus_interior_strong)
    using k assms cfg *
    apply (auto simp: at_within_Icc_at)
    done
qed

lemma contour_integral_primitive:
  assumes "\<And>x. x \<in> s \<Longrightarrow> (f has_field_derivative f' x) (at x within s)"
      and "valid_path g" "path_image g \<subseteq> s"
    shows "(f' has_contour_integral (f(pathfinish g) - f(pathstart g))) g"
  using assms
  apply (simp add: valid_path_def path_image_def pathfinish_def pathstart_def has_contour_integral_def)
  apply (auto intro!: piecewise_C1_imp_differentiable contour_integral_primitive_lemma [of 0 1 s])
  done

corollary Cauchy_theorem_primitive:
  assumes "\<And>x. x \<in> s \<Longrightarrow> (f has_field_derivative f' x) (at x within s)"
      and "valid_path g"  "path_image g \<subseteq> s" "pathfinish g = pathstart g"
    shows "(f' has_contour_integral 0) g"
  using assms
  by (metis diff_self contour_integral_primitive)

text\<open>Existence of path integral for continuous function\<close>
lemma contour_integrable_continuous_linepath:
  assumes "continuous_on (closed_segment a b) f"
  shows "f contour_integrable_on (linepath a b)"
proof -
  have "continuous_on {0..1} ((\<lambda>x. f x * (b - a)) \<circ> linepath a b)"
    apply (rule continuous_on_compose [OF continuous_on_linepath], simp add: linepath_image_01)
    apply (rule continuous_intros | simp add: assms)+
    done
  then show ?thesis
    apply (simp add: contour_integrable_on_def has_contour_integral_def integrable_on_def [symmetric])
    apply (rule integrable_continuous [of 0 "1::real", simplified])
    apply (rule continuous_on_eq [where f = "\<lambda>x. f(linepath a b x)*(b - a)"])
    apply (auto simp: vector_derivative_linepath_within)
    done
qed

lemma has_field_der_id: "((\<lambda>x. x\<^sup>2 / 2) has_field_derivative x) (at x)"
  by (rule has_derivative_imp_has_field_derivative)
     (rule derivative_intros | simp)+

lemma contour_integral_id [simp]: "contour_integral (linepath a b) (\<lambda>y. y) = (b^2 - a^2)/2"
  apply (rule contour_integral_unique)
  using contour_integral_primitive [of UNIV "\<lambda>x. x^2/2" "\<lambda>x. x" "linepath a b"]
  apply (auto simp: field_simps has_field_der_id)
  done

lemma contour_integrable_on_const [iff]: "(\<lambda>x. c) contour_integrable_on (linepath a b)"
  by (simp add: contour_integrable_continuous_linepath)

lemma contour_integrable_on_id [iff]: "(\<lambda>x. x) contour_integrable_on (linepath a b)"
  by (simp add: contour_integrable_continuous_linepath)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Arithmetical combining theorems\<close>

lemma has_contour_integral_neg:
    "(f has_contour_integral i) g \<Longrightarrow> ((\<lambda>x. -(f x)) has_contour_integral (-i)) g"
  by (simp add: has_integral_neg has_contour_integral_def)

lemma has_contour_integral_add:
    "\<lbrakk>(f1 has_contour_integral i1) g; (f2 has_contour_integral i2) g\<rbrakk>
     \<Longrightarrow> ((\<lambda>x. f1 x + f2 x) has_contour_integral (i1 + i2)) g"
  by (simp add: has_integral_add has_contour_integral_def algebra_simps)

lemma has_contour_integral_diff:
  "\<lbrakk>(f1 has_contour_integral i1) g; (f2 has_contour_integral i2) g\<rbrakk>
         \<Longrightarrow> ((\<lambda>x. f1 x - f2 x) has_contour_integral (i1 - i2)) g"
  by (simp add: has_integral_diff has_contour_integral_def algebra_simps)

lemma has_contour_integral_lmul:
  "(f has_contour_integral i) g \<Longrightarrow> ((\<lambda>x. c * (f x)) has_contour_integral (c*i)) g"
apply (simp add: has_contour_integral_def)
apply (drule has_integral_mult_right)
apply (simp add: algebra_simps)
done

lemma has_contour_integral_rmul:
  "(f has_contour_integral i) g \<Longrightarrow> ((\<lambda>x. (f x) * c) has_contour_integral (i*c)) g"
apply (drule has_contour_integral_lmul)
apply (simp add: mult.commute)
done

lemma has_contour_integral_div:
  "(f has_contour_integral i) g \<Longrightarrow> ((\<lambda>x. f x/c) has_contour_integral (i/c)) g"
  by (simp add: field_class.field_divide_inverse) (metis has_contour_integral_rmul)

lemma has_contour_integral_eq:
    "\<lbrakk>(f has_contour_integral y) p; \<And>x. x \<in> path_image p \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> (g has_contour_integral y) p"
apply (simp add: path_image_def has_contour_integral_def)
by (metis (no_types, lifting) image_eqI has_integral_eq)

lemma has_contour_integral_bound_linepath:
  assumes "(f has_contour_integral i) (linepath a b)"
          "0 \<le> B" "\<And>x. x \<in> closed_segment a b \<Longrightarrow> norm(f x) \<le> B"
    shows "norm i \<le> B * norm(b - a)"
proof -
  { fix x::real
    assume x: "0 \<le> x" "x \<le> 1"
  have "norm (f (linepath a b x)) *
        norm (vector_derivative (linepath a b) (at x within {0..1})) \<le> B * norm (b - a)"
    by (auto intro: mult_mono simp: assms linepath_in_path of_real_linepath vector_derivative_linepath_within x)
  } note * = this
  have "norm i \<le> (B * norm (b - a)) * content (cbox 0 (1::real))"
    apply (rule has_integral_bound
       [of _ "\<lambda>x. f (linepath a b x) * vector_derivative (linepath a b) (at x within {0..1})"])
    using assms * unfolding has_contour_integral_def
    apply (auto simp: norm_mult)
    done
  then show ?thesis
    by (auto simp: content_real)
qed

(*UNUSED
lemma has_contour_integral_bound_linepath_strong:
  fixes a :: real and f :: "complex \<Rightarrow> real"
  assumes "(f has_contour_integral i) (linepath a b)"
          "finite k"
          "0 \<le> B" "\<And>x::real. x \<in> closed_segment a b - k \<Longrightarrow> norm(f x) \<le> B"
    shows "norm i \<le> B*norm(b - a)"
*)

lemma has_contour_integral_const_linepath: "((\<lambda>x. c) has_contour_integral c*(b - a))(linepath a b)"
  unfolding has_contour_integral_linepath
  by (metis content_real diff_0_right has_integral_const_real lambda_one of_real_1 scaleR_conv_of_real zero_le_one)

lemma has_contour_integral_0: "((\<lambda>x. 0) has_contour_integral 0) g"
  by (simp add: has_contour_integral_def)

lemma has_contour_integral_is_0:
    "(\<And>z. z \<in> path_image g \<Longrightarrow> f z = 0) \<Longrightarrow> (f has_contour_integral 0) g"
  by (rule has_contour_integral_eq [OF has_contour_integral_0]) auto

lemma has_contour_integral_sum:
    "\<lbrakk>finite s; \<And>a. a \<in> s \<Longrightarrow> (f a has_contour_integral i a) p\<rbrakk>
     \<Longrightarrow> ((\<lambda>x. sum (\<lambda>a. f a x) s) has_contour_integral sum i s) p"
  by (induction s rule: finite_induct) (auto simp: has_contour_integral_0 has_contour_integral_add)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Operations on path integrals\<close>

lemma contour_integral_const_linepath [simp]: "contour_integral (linepath a b) (\<lambda>x. c) = c*(b - a)"
  by (rule contour_integral_unique [OF has_contour_integral_const_linepath])

lemma contour_integral_neg:
    "f contour_integrable_on g \<Longrightarrow> contour_integral g (\<lambda>x. -(f x)) = -(contour_integral g f)"
  by (simp add: contour_integral_unique has_contour_integral_integral has_contour_integral_neg)

lemma contour_integral_add:
    "f1 contour_integrable_on g \<Longrightarrow> f2 contour_integrable_on g \<Longrightarrow> contour_integral g (\<lambda>x. f1 x + f2 x) =
                contour_integral g f1 + contour_integral g f2"
  by (simp add: contour_integral_unique has_contour_integral_integral has_contour_integral_add)

lemma contour_integral_diff:
    "f1 contour_integrable_on g \<Longrightarrow> f2 contour_integrable_on g \<Longrightarrow> contour_integral g (\<lambda>x. f1 x - f2 x) =
                contour_integral g f1 - contour_integral g f2"
  by (simp add: contour_integral_unique has_contour_integral_integral has_contour_integral_diff)

lemma contour_integral_lmul:
  shows "f contour_integrable_on g
           \<Longrightarrow> contour_integral g (\<lambda>x. c * f x) = c*contour_integral g f"
  by (simp add: contour_integral_unique has_contour_integral_integral has_contour_integral_lmul)

lemma contour_integral_rmul:
  shows "f contour_integrable_on g
        \<Longrightarrow> contour_integral g (\<lambda>x. f x * c) = contour_integral g f * c"
  by (simp add: contour_integral_unique has_contour_integral_integral has_contour_integral_rmul)

lemma contour_integral_div:
  shows "f contour_integrable_on g
        \<Longrightarrow> contour_integral g (\<lambda>x. f x / c) = contour_integral g f / c"
  by (simp add: contour_integral_unique has_contour_integral_integral has_contour_integral_div)

lemma contour_integral_eq:
    "(\<And>x. x \<in> path_image p \<Longrightarrow> f x = g x) \<Longrightarrow> contour_integral p f = contour_integral p g"
  apply (simp add: contour_integral_def)
  using has_contour_integral_eq
  by (metis contour_integral_unique has_contour_integral_integrable has_contour_integral_integral)

lemma contour_integral_eq_0:
    "(\<And>z. z \<in> path_image g \<Longrightarrow> f z = 0) \<Longrightarrow> contour_integral g f = 0"
  by (simp add: has_contour_integral_is_0 contour_integral_unique)

lemma contour_integral_bound_linepath:
  shows
    "\<lbrakk>f contour_integrable_on (linepath a b);
      0 \<le> B; \<And>x. x \<in> closed_segment a b \<Longrightarrow> norm(f x) \<le> B\<rbrakk>
     \<Longrightarrow> norm(contour_integral (linepath a b) f) \<le> B*norm(b - a)"
  apply (rule has_contour_integral_bound_linepath [of f])
  apply (auto simp: has_contour_integral_integral)
  done

lemma contour_integral_0 [simp]: "contour_integral g (\<lambda>x. 0) = 0"
  by (simp add: contour_integral_unique has_contour_integral_0)

lemma contour_integral_sum:
    "\<lbrakk>finite s; \<And>a. a \<in> s \<Longrightarrow> (f a) contour_integrable_on p\<rbrakk>
     \<Longrightarrow> contour_integral p (\<lambda>x. sum (\<lambda>a. f a x) s) = sum (\<lambda>a. contour_integral p (f a)) s"
  by (auto simp: contour_integral_unique has_contour_integral_sum has_contour_integral_integral)

lemma contour_integrable_eq:
    "\<lbrakk>f contour_integrable_on p; \<And>x. x \<in> path_image p \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> g contour_integrable_on p"
  unfolding contour_integrable_on_def
  by (metis has_contour_integral_eq)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Arithmetic theorems for path integrability\<close>

lemma contour_integrable_neg:
    "f contour_integrable_on g \<Longrightarrow> (\<lambda>x. -(f x)) contour_integrable_on g"
  using has_contour_integral_neg contour_integrable_on_def by blast

lemma contour_integrable_add:
    "\<lbrakk>f1 contour_integrable_on g; f2 contour_integrable_on g\<rbrakk> \<Longrightarrow> (\<lambda>x. f1 x + f2 x) contour_integrable_on g"
  using has_contour_integral_add contour_integrable_on_def
  by fastforce

lemma contour_integrable_diff:
    "\<lbrakk>f1 contour_integrable_on g; f2 contour_integrable_on g\<rbrakk> \<Longrightarrow> (\<lambda>x. f1 x - f2 x) contour_integrable_on g"
  using has_contour_integral_diff contour_integrable_on_def
  by fastforce

lemma contour_integrable_lmul:
    "f contour_integrable_on g \<Longrightarrow> (\<lambda>x. c * f x) contour_integrable_on g"
  using has_contour_integral_lmul contour_integrable_on_def
  by fastforce

lemma contour_integrable_rmul:
    "f contour_integrable_on g \<Longrightarrow> (\<lambda>x. f x * c) contour_integrable_on g"
  using has_contour_integral_rmul contour_integrable_on_def
  by fastforce

lemma contour_integrable_div:
    "f contour_integrable_on g \<Longrightarrow> (\<lambda>x. f x / c) contour_integrable_on g"
  using has_contour_integral_div contour_integrable_on_def
  by fastforce

lemma contour_integrable_sum:
    "\<lbrakk>finite s; \<And>a. a \<in> s \<Longrightarrow> (f a) contour_integrable_on p\<rbrakk>
     \<Longrightarrow> (\<lambda>x. sum (\<lambda>a. f a x) s) contour_integrable_on p"
   unfolding contour_integrable_on_def
   by (metis has_contour_integral_sum)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Reversing a path integral\<close>

lemma has_contour_integral_reverse_linepath:
    "(f has_contour_integral i) (linepath a b)
     \<Longrightarrow> (f has_contour_integral (-i)) (linepath b a)"
  using has_contour_integral_reversepath valid_path_linepath by fastforce

lemma contour_integral_reverse_linepath:
    "continuous_on (closed_segment a b) f
     \<Longrightarrow> contour_integral (linepath a b) f = - (contour_integral(linepath b a) f)"
apply (rule contour_integral_unique)
apply (rule has_contour_integral_reverse_linepath)
by (simp add: closed_segment_commute contour_integrable_continuous_linepath has_contour_integral_integral)


(* Splitting a path integral in a flat way.*)

lemma has_contour_integral_split:
  assumes f: "(f has_contour_integral i) (linepath a c)" "(f has_contour_integral j) (linepath c b)"
      and k: "0 \<le> k" "k \<le> 1"
      and c: "c - a = k *\<^sub>R (b - a)"
    shows "(f has_contour_integral (i + j)) (linepath a b)"
proof (cases "k = 0 \<or> k = 1")
  case True
  then show ?thesis
    using assms by auto
next
  case False
  then have k: "0 < k" "k < 1" "complex_of_real k \<noteq> 1"
    using assms by auto
  have c': "c = k *\<^sub>R (b - a) + a"
    by (metis diff_add_cancel c)
  have bc: "(b - c) = (1 - k) *\<^sub>R (b - a)"
    by (simp add: algebra_simps c')
  { assume *: "((\<lambda>x. f ((1 - x) *\<^sub>R a + x *\<^sub>R c) * (c - a)) has_integral i) {0..1}"
    have **: "\<And>x. ((k - x) / k) *\<^sub>R a + (x / k) *\<^sub>R c = (1 - x) *\<^sub>R a + x *\<^sub>R b"
      using False apply (simp add: c' algebra_simps)
      apply (simp add: real_vector.scale_left_distrib [symmetric] field_split_simps)
      done
    have "((\<lambda>x. f ((1 - x) *\<^sub>R a + x *\<^sub>R b) * (b - a)) has_integral i) {0..k}"
      using k has_integral_affinity01 [OF *, of "inverse k" "0"]
      apply (simp add: divide_simps mult.commute [of _ "k"] image_affinity_atLeastAtMost ** c)
      apply (auto dest: has_integral_cmul [where c = "inverse k"])
      done
  } note fi = this
  { assume *: "((\<lambda>x. f ((1 - x) *\<^sub>R c + x *\<^sub>R b) * (b - c)) has_integral j) {0..1}"
    have **: "\<And>x. (((1 - x) / (1 - k)) *\<^sub>R c + ((x - k) / (1 - k)) *\<^sub>R b) = ((1 - x) *\<^sub>R a + x *\<^sub>R b)"
      using k
      apply (simp add: c' field_simps)
      apply (simp add: scaleR_conv_of_real divide_simps)
      apply (simp add: field_simps)
      done
    have "((\<lambda>x. f ((1 - x) *\<^sub>R a + x *\<^sub>R b) * (b - a)) has_integral j) {k..1}"
      using k has_integral_affinity01 [OF *, of "inverse(1 - k)" "-(k/(1 - k))"]
      apply (simp add: divide_simps mult.commute [of _ "1-k"] image_affinity_atLeastAtMost ** bc)
      apply (auto dest: has_integral_cmul [where k = "(1 - k) *\<^sub>R j" and c = "inverse (1 - k)"])
      done
  } note fj = this
  show ?thesis
    using f k
    apply (simp add: has_contour_integral_linepath)
    apply (simp add: linepath_def)
    apply (rule has_integral_combine [OF _ _ fi fj], simp_all)
    done
qed

lemma continuous_on_closed_segment_transform:
  assumes f: "continuous_on (closed_segment a b) f"
      and k: "0 \<le> k" "k \<le> 1"
      and c: "c - a = k *\<^sub>R (b - a)"
    shows "continuous_on (closed_segment a c) f"
proof -
  have c': "c = (1 - k) *\<^sub>R a + k *\<^sub>R b"
    using c by (simp add: algebra_simps)
  have "closed_segment a c \<subseteq> closed_segment a b"
    by (metis c' ends_in_segment(1) in_segment(1) k subset_closed_segment)
  then show "continuous_on (closed_segment a c) f"
    by (rule continuous_on_subset [OF f])
qed

lemma contour_integral_split:
  assumes f: "continuous_on (closed_segment a b) f"
      and k: "0 \<le> k" "k \<le> 1"
      and c: "c - a = k *\<^sub>R (b - a)"
    shows "contour_integral(linepath a b) f = contour_integral(linepath a c) f + contour_integral(linepath c b) f"
proof -
  have c': "c = (1 - k) *\<^sub>R a + k *\<^sub>R b"
    using c by (simp add: algebra_simps)
  have "closed_segment a c \<subseteq> closed_segment a b"
    by (metis c' ends_in_segment(1) in_segment(1) k subset_closed_segment)
  moreover have "closed_segment c b \<subseteq> closed_segment a b"
    by (metis c' ends_in_segment(2) in_segment(1) k subset_closed_segment)
  ultimately
  have *: "continuous_on (closed_segment a c) f" "continuous_on (closed_segment c b) f"
    by (auto intro: continuous_on_subset [OF f])
  show ?thesis
    by (rule contour_integral_unique) (meson "*" c contour_integrable_continuous_linepath has_contour_integral_integral has_contour_integral_split k)
qed

lemma contour_integral_split_linepath:
  assumes f: "continuous_on (closed_segment a b) f"
      and c: "c \<in> closed_segment a b"
    shows "contour_integral(linepath a b) f = contour_integral(linepath a c) f + contour_integral(linepath c b) f"
  using c by (auto simp: closed_segment_def algebra_simps intro!: contour_integral_split [OF f])

subsection\<open>Partial circle path\<close>

definition\<^marker>\<open>tag important\<close> part_circlepath :: "[complex, real, real, real, real] \<Rightarrow> complex"
  where "part_circlepath z r s t \<equiv> \<lambda>x. z + of_real r * exp (\<i> * of_real (linepath s t x))"

lemma pathstart_part_circlepath [simp]:
     "pathstart(part_circlepath z r s t) = z + r*exp(\<i> * s)"
by (metis part_circlepath_def pathstart_def pathstart_linepath)

lemma pathfinish_part_circlepath [simp]:
     "pathfinish(part_circlepath z r s t) = z + r*exp(\<i>*t)"
by (metis part_circlepath_def pathfinish_def pathfinish_linepath)

lemma reversepath_part_circlepath[simp]:
    "reversepath (part_circlepath z r s t) = part_circlepath z r t s"
  unfolding part_circlepath_def reversepath_def linepath_def 
  by (auto simp:algebra_simps)
    
lemma has_vector_derivative_part_circlepath [derivative_intros]:
    "((part_circlepath z r s t) has_vector_derivative
      (\<i> * r * (of_real t - of_real s) * exp(\<i> * linepath s t x)))
     (at x within X)"
  apply (simp add: part_circlepath_def linepath_def scaleR_conv_of_real)
  apply (rule has_vector_derivative_real_field)
  apply (rule derivative_eq_intros | simp)+
  done

lemma differentiable_part_circlepath:
  "part_circlepath c r a b differentiable at x within A"
  using has_vector_derivative_part_circlepath[of c r a b x A] differentiableI_vector by blast

lemma vector_derivative_part_circlepath:
    "vector_derivative (part_circlepath z r s t) (at x) =
       \<i> * r * (of_real t - of_real s) * exp(\<i> * linepath s t x)"
  using has_vector_derivative_part_circlepath vector_derivative_at by blast

lemma vector_derivative_part_circlepath01:
    "\<lbrakk>0 \<le> x; x \<le> 1\<rbrakk>
     \<Longrightarrow> vector_derivative (part_circlepath z r s t) (at x within {0..1}) =
          \<i> * r * (of_real t - of_real s) * exp(\<i> * linepath s t x)"
  using has_vector_derivative_part_circlepath
  by (auto simp: vector_derivative_at_within_ivl)

lemma valid_path_part_circlepath [simp]: "valid_path (part_circlepath z r s t)"
  apply (simp add: valid_path_def)
  apply (rule C1_differentiable_imp_piecewise)
  apply (auto simp: C1_differentiable_on_eq vector_derivative_works vector_derivative_part_circlepath has_vector_derivative_part_circlepath
              intro!: continuous_intros)
  done

lemma path_part_circlepath [simp]: "path (part_circlepath z r s t)"
  by (simp add: valid_path_imp_path)

proposition path_image_part_circlepath:
  assumes "s \<le> t"
    shows "path_image (part_circlepath z r s t) = {z + r * exp(\<i> * of_real x) | x. s \<le> x \<and> x \<le> t}"
proof -
  { fix z::real
    assume "0 \<le> z" "z \<le> 1"
    with \<open>s \<le> t\<close> have "\<exists>x. (exp (\<i> * linepath s t z) = exp (\<i> * of_real x)) \<and> s \<le> x \<and> x \<le> t"
      apply (rule_tac x="(1 - z) * s + z * t" in exI)
      apply (simp add: linepath_def scaleR_conv_of_real algebra_simps)
      apply (rule conjI)
      using mult_right_mono apply blast
      using affine_ineq  by (metis "mult.commute")
  }
  moreover
  { fix z
    assume "s \<le> z" "z \<le> t"
    then have "z + of_real r * exp (\<i> * of_real z) \<in> (\<lambda>x. z + of_real r * exp (\<i> * linepath s t x)) ` {0..1}"
      apply (rule_tac x="(z - s)/(t - s)" in image_eqI)
      apply (simp add: linepath_def scaleR_conv_of_real divide_simps exp_eq)
      apply (auto simp: field_split_simps)
      done
  }
  ultimately show ?thesis
    by (fastforce simp add: path_image_def part_circlepath_def)
qed

lemma path_image_part_circlepath':
  "path_image (part_circlepath z r s t) = (\<lambda>x. z + r * cis x) ` closed_segment s t"
proof -
  have "path_image (part_circlepath z r s t) = 
          (\<lambda>x. z + r * exp(\<i> * of_real x)) ` linepath s t ` {0..1}"
    by (simp add: image_image path_image_def part_circlepath_def)
  also have "linepath s t ` {0..1} = closed_segment s t"
    by (rule linepath_image_01)
  finally show ?thesis by (simp add: cis_conv_exp)
qed

lemma path_image_part_circlepath_subset:
    "\<lbrakk>s \<le> t; 0 \<le> r\<rbrakk> \<Longrightarrow> path_image(part_circlepath z r s t) \<subseteq> sphere z r"
by (auto simp: path_image_part_circlepath sphere_def dist_norm algebra_simps norm_mult)

lemma in_path_image_part_circlepath:
  assumes "w \<in> path_image(part_circlepath z r s t)" "s \<le> t" "0 \<le> r"
    shows "norm(w - z) = r"
proof -
  have "w \<in> {c. dist z c = r}"
    by (metis (no_types) path_image_part_circlepath_subset sphere_def subset_eq assms)
  thus ?thesis
    by (simp add: dist_norm norm_minus_commute)
qed

lemma path_image_part_circlepath_subset':
  assumes "r \<ge> 0"
  shows   "path_image (part_circlepath z r s t) \<subseteq> sphere z r"
proof (cases "s \<le> t")
  case True
  thus ?thesis using path_image_part_circlepath_subset[of s t r z] assms by simp
next
  case False
  thus ?thesis using path_image_part_circlepath_subset[of t s r z] assms
    by (subst reversepath_part_circlepath [symmetric], subst path_image_reversepath) simp_all
qed

lemma part_circlepath_cnj: "cnj (part_circlepath c r a b x) = part_circlepath (cnj c) r (-a) (-b) x"
  by (simp add: part_circlepath_def exp_cnj linepath_def algebra_simps)

lemma contour_integral_bound_part_circlepath:
  assumes "f contour_integrable_on part_circlepath c r a b"
  assumes "B \<ge> 0" "r \<ge> 0" "\<And>x. x \<in> path_image (part_circlepath c r a b) \<Longrightarrow> norm (f x) \<le> B"
  shows   "norm (contour_integral (part_circlepath c r a b) f) \<le> B * r * \<bar>b - a\<bar>"
proof -
  let ?I = "integral {0..1} (\<lambda>x. f (part_circlepath c r a b x) * \<i> * of_real (r * (b - a)) *
              exp (\<i> * linepath a b x))"
  have "norm ?I \<le> integral {0..1} (\<lambda>x::real. B * 1 * (r * \<bar>b - a\<bar>) * 1)"
  proof (rule integral_norm_bound_integral, goal_cases)
    case 1
    with assms(1) show ?case
      by (simp add: contour_integrable_on vector_derivative_part_circlepath mult_ac)
  next
    case (3 x)
    with assms(2-) show ?case unfolding norm_mult norm_of_real abs_mult
      by (intro mult_mono) (auto simp: path_image_def)
  qed auto
  also have "?I = contour_integral (part_circlepath c r a b) f"
    by (simp add: contour_integral_integral vector_derivative_part_circlepath mult_ac)
  finally show ?thesis by simp
qed

lemma has_contour_integral_part_circlepath_iff:
  assumes "a < b"
  shows "(f has_contour_integral I) (part_circlepath c r a b) \<longleftrightarrow>
           ((\<lambda>t. f (c + r * cis t) * r * \<i> * cis t) has_integral I) {a..b}"
proof -
  have "(f has_contour_integral I) (part_circlepath c r a b) \<longleftrightarrow>
          ((\<lambda>x. f (part_circlepath c r a b x) * vector_derivative (part_circlepath c r a b)
           (at x within {0..1})) has_integral I) {0..1}"
    unfolding has_contour_integral_def ..
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. f (part_circlepath c r a b x) * r * (b - a) * \<i> *
                            cis (linepath a b x)) has_integral I) {0..1}"
    by (intro has_integral_cong, subst vector_derivative_part_circlepath01)
       (simp_all add: cis_conv_exp)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. f (c + r * exp (\<i> * linepath (of_real a) (of_real b) x)) *
                       r * \<i> * exp (\<i> * linepath (of_real a) (of_real b) x) *
                       vector_derivative (linepath (of_real a) (of_real b)) 
                         (at x within {0..1})) has_integral I) {0..1}"
    by (intro has_integral_cong, subst vector_derivative_linepath_within)
       (auto simp: part_circlepath_def cis_conv_exp of_real_linepath [symmetric])
  also have "\<dots> \<longleftrightarrow> ((\<lambda>z. f (c + r * exp (\<i> * z)) * r * \<i> * exp (\<i> * z)) has_contour_integral I)
                      (linepath (of_real a) (of_real b))"
    by (simp add: has_contour_integral_def)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>t. f (c + r * cis t) * r * \<i> * cis t) has_integral I) {a..b}" using assms
    by (subst has_contour_integral_linepath_Reals_iff) (simp_all add: cis_conv_exp)
  finally show ?thesis .
qed

lemma contour_integrable_part_circlepath_iff:
  assumes "a < b"
  shows "f contour_integrable_on (part_circlepath c r a b) \<longleftrightarrow>
           (\<lambda>t. f (c + r * cis t) * r * \<i> * cis t) integrable_on {a..b}"
  using assms by (auto simp: contour_integrable_on_def integrable_on_def 
                             has_contour_integral_part_circlepath_iff)

lemma contour_integral_part_circlepath_eq:
  assumes "a < b"
  shows "contour_integral (part_circlepath c r a b) f =
           integral {a..b} (\<lambda>t. f (c + r * cis t) * r * \<i> * cis t)"
proof (cases "f contour_integrable_on part_circlepath c r a b")
  case True
  hence "(\<lambda>t. f (c + r * cis t) * r * \<i> * cis t) integrable_on {a..b}" 
    using assms by (simp add: contour_integrable_part_circlepath_iff)
  with True show ?thesis
    using has_contour_integral_part_circlepath_iff[OF assms]
          contour_integral_unique has_integral_integrable_integral by blast
next
  case False
  hence "\<not>(\<lambda>t. f (c + r * cis t) * r * \<i> * cis t) integrable_on {a..b}" 
    using assms by (simp add: contour_integrable_part_circlepath_iff)
  with False show ?thesis
    by (simp add: not_integrable_contour_integral not_integrable_integral)
qed

lemma contour_integral_part_circlepath_reverse:
  "contour_integral (part_circlepath c r a b) f = -contour_integral (part_circlepath c r b a) f"
  by (subst reversepath_part_circlepath [symmetric], subst contour_integral_reversepath) simp_all

lemma contour_integral_part_circlepath_reverse':
  "b < a \<Longrightarrow> contour_integral (part_circlepath c r a b) f = 
               -contour_integral (part_circlepath c r b a) f"
  by (rule contour_integral_part_circlepath_reverse)

lemma finite_bounded_log: "finite {z::complex. norm z \<le> b \<and> exp z = w}"
proof (cases "w = 0")
  case True then show ?thesis by auto
next
  case False
  have *: "finite {x. cmod (complex_of_real (2 * real_of_int x * pi) * \<i>) \<le> b + cmod (Ln w)}"
    apply (simp add: norm_mult finite_int_iff_bounded_le)
    apply (rule_tac x="\<lfloor>(b + cmod (Ln w)) / (2*pi)\<rfloor>" in exI)
    apply (auto simp: field_split_simps le_floor_iff)
    done
  have [simp]: "\<And>P f. {z. P z \<and> (\<exists>n. z = f n)} = f ` {n. P (f n)}"
    by blast
  show ?thesis
    apply (subst exp_Ln [OF False, symmetric])
    apply (simp add: exp_eq)
    using norm_add_leD apply (fastforce intro: finite_subset [OF _ *])
    done
qed

lemma finite_bounded_log2:
  fixes a::complex
    assumes "a \<noteq> 0"
    shows "finite {z. norm z \<le> b \<and> exp(a*z) = w}"
proof -
  have *: "finite ((\<lambda>z. z / a) ` {z. cmod z \<le> b * cmod a \<and> exp z = w})"
    by (rule finite_imageI [OF finite_bounded_log])
  show ?thesis
    by (rule finite_subset [OF _ *]) (force simp: assms norm_mult)
qed

lemma has_contour_integral_bound_part_circlepath_strong:
  assumes fi: "(f has_contour_integral i) (part_circlepath z r s t)"
      and "finite k" and le: "0 \<le> B" "0 < r" "s \<le> t"
      and B: "\<And>x. x \<in> path_image(part_circlepath z r s t) - k \<Longrightarrow> norm(f x) \<le> B"
    shows "cmod i \<le> B * r * (t - s)"
proof -
  consider "s = t" | "s < t" using \<open>s \<le> t\<close> by linarith
  then show ?thesis
  proof cases
    case 1 with fi [unfolded has_contour_integral]
    have "i = 0"  by (simp add: vector_derivative_part_circlepath)
    with assms show ?thesis by simp
  next
    case 2
    have [simp]: "\<bar>r\<bar> = r" using \<open>r > 0\<close> by linarith
    have [simp]: "cmod (complex_of_real t - complex_of_real s) = t-s"
      by (metis "2" abs_of_pos diff_gt_0_iff_gt norm_of_real of_real_diff)
    have "finite (part_circlepath z r s t -` {y} \<inter> {0..1})" if "y \<in> k" for y
    proof -
      define w where "w = (y - z)/of_real r / exp(\<i> * of_real s)"
      have fin: "finite (of_real -` {z. cmod z \<le> 1 \<and> exp (\<i> * complex_of_real (t - s) * z) = w})"
        apply (rule finite_vimageI [OF finite_bounded_log2])
        using \<open>s < t\<close> apply (auto simp: inj_of_real)
        done
      show ?thesis
        apply (simp add: part_circlepath_def linepath_def vimage_def)
        apply (rule finite_subset [OF _ fin])
        using le
        apply (auto simp: w_def algebra_simps scaleR_conv_of_real exp_add exp_diff)
        done
    qed
    then have fin01: "finite ((part_circlepath z r s t) -` k \<inter> {0..1})"
      by (rule finite_finite_vimage_IntI [OF \<open>finite k\<close>])
    have **: "((\<lambda>x. if (part_circlepath z r s t x) \<in> k then 0
                    else f(part_circlepath z r s t x) *
                       vector_derivative (part_circlepath z r s t) (at x)) has_integral i)  {0..1}"
      by (rule has_integral_spike [OF negligible_finite [OF fin01]])  (use fi has_contour_integral in auto)
    have *: "\<And>x. \<lbrakk>0 \<le> x; x \<le> 1; part_circlepath z r s t x \<notin> k\<rbrakk> \<Longrightarrow> cmod (f (part_circlepath z r s t x)) \<le> B"
      by (auto intro!: B [unfolded path_image_def image_def, simplified])
    show ?thesis
      apply (rule has_integral_bound [where 'a=real, simplified, OF _ **, simplified])
      using assms apply force
      apply (simp add: norm_mult vector_derivative_part_circlepath)
      using le * "2" \<open>r > 0\<close> by auto
  qed
qed

lemma has_contour_integral_bound_part_circlepath:
      "\<lbrakk>(f has_contour_integral i) (part_circlepath z r s t);
        0 \<le> B; 0 < r; s \<le> t;
        \<And>x. x \<in> path_image(part_circlepath z r s t) \<Longrightarrow> norm(f x) \<le> B\<rbrakk>
       \<Longrightarrow> norm i \<le> B*r*(t - s)"
  by (auto intro: has_contour_integral_bound_part_circlepath_strong)

lemma contour_integrable_continuous_part_circlepath:
     "continuous_on (path_image (part_circlepath z r s t)) f
      \<Longrightarrow> f contour_integrable_on (part_circlepath z r s t)"
  apply (simp add: contour_integrable_on has_contour_integral_def vector_derivative_part_circlepath path_image_def)
  apply (rule integrable_continuous_real)
  apply (fast intro: path_part_circlepath [unfolded path_def] continuous_intros continuous_on_compose2 [where g=f, OF _ _ order_refl])
  done

lemma simple_path_part_circlepath:
    "simple_path(part_circlepath z r s t) \<longleftrightarrow> (r \<noteq> 0 \<and> s \<noteq> t \<and> \<bar>s - t\<bar> \<le> 2*pi)"
proof (cases "r = 0 \<or> s = t")
  case True
  then show ?thesis
    unfolding part_circlepath_def simple_path_def
    by (rule disjE) (force intro: bexI [where x = "1/4"] bexI [where x = "1/3"])+
next
  case False then have "r \<noteq> 0" "s \<noteq> t" by auto
  have *: "\<And>x y z s t. \<i>*((1 - x) * s + x * t) = \<i>*(((1 - y) * s + y * t)) + z  \<longleftrightarrow> \<i>*(x - y) * (t - s) = z"
    by (simp add: algebra_simps)
  have abs01: "\<And>x y::real. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1
                      \<Longrightarrow> (x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0 \<longleftrightarrow> \<bar>x - y\<bar> \<in> {0,1})"
    by auto
  have **: "\<And>x y. (\<exists>n. (complex_of_real x - of_real y) * (of_real t - of_real s) = 2 * (of_int n * of_real pi)) \<longleftrightarrow>
                  (\<exists>n. \<bar>x - y\<bar> * (t - s) = 2 * (of_int n * pi))"
    by (force simp: algebra_simps abs_if dest: arg_cong [where f=Re] arg_cong [where f=complex_of_real]
                    intro: exI [where x = "-n" for n])
  have 1: "\<bar>s - t\<bar> \<le> 2 * pi"
    if "\<And>x. 0 \<le> x \<and> x \<le> 1 \<Longrightarrow> (\<exists>n. x * (t - s) = 2 * (real_of_int n * pi)) \<longrightarrow> x = 0 \<or> x = 1"
  proof (rule ccontr)
    assume "\<not> \<bar>s - t\<bar> \<le> 2 * pi"
    then have *: "\<And>n. t - s \<noteq> of_int n * \<bar>s - t\<bar>"
      using False that [of "2*pi / \<bar>t - s\<bar>"]
      by (simp add: abs_minus_commute divide_simps)
    show False
      using * [of 1] * [of "-1"] by auto
  qed
  have 2: "\<bar>s - t\<bar> = \<bar>2 * (real_of_int n * pi) / x\<bar>" if "x \<noteq> 0" "x * (t - s) = 2 * (real_of_int n * pi)" for x n
  proof -
    have "t-s = 2 * (real_of_int n * pi)/x"
      using that by (simp add: field_simps)
    then show ?thesis by (metis abs_minus_commute)
  qed
  have abs_away: "\<And>P. (\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. P \<bar>x - y\<bar>) \<longleftrightarrow> (\<forall>x::real. 0 \<le> x \<and> x \<le> 1 \<longrightarrow> P x)"
    by force
  show ?thesis using False
    apply (simp add: simple_path_def)
    apply (simp add: part_circlepath_def linepath_def exp_eq  * ** abs01  del: Set.insert_iff)
    apply (subst abs_away)
    apply (auto simp: 1)
    apply (rule ccontr)
    apply (auto simp: 2 field_split_simps abs_mult dest: of_int_leD)
    done
qed

lemma arc_part_circlepath:
  assumes "r \<noteq> 0" "s \<noteq> t" "\<bar>s - t\<bar> < 2*pi"
    shows "arc (part_circlepath z r s t)"
proof -
  have *: "x = y" if eq: "\<i> * (linepath s t x) = \<i> * (linepath s t y) + 2 * of_int n * complex_of_real pi * \<i>"
    and x: "x \<in> {0..1}" and y: "y \<in> {0..1}" for x y n
  proof (rule ccontr)
    assume "x \<noteq> y"
    have "(linepath s t x) = (linepath s t y) + 2 * of_int n * complex_of_real pi"
      by (metis add_divide_eq_iff complex_i_not_zero mult.commute nonzero_mult_div_cancel_left eq)
    then have "s*y + t*x = s*x + (t*y + of_int n * (pi * 2))"
      by (force simp: algebra_simps linepath_def dest: arg_cong [where f=Re])
    with \<open>x \<noteq> y\<close> have st: "s-t = (of_int n * (pi * 2) / (y-x))"
      by (force simp: field_simps)
    have "\<bar>real_of_int n\<bar> < \<bar>y - x\<bar>"
      using assms \<open>x \<noteq> y\<close> by (simp add: st abs_mult field_simps)
    then show False
      using assms x y st by (auto dest: of_int_lessD)
  qed
  show ?thesis
    using assms
    apply (simp add: arc_def)
    apply (simp add: part_circlepath_def inj_on_def exp_eq)
    apply (blast intro: *)
    done
qed

subsection\<open>Special case of one complete circle\<close>

definition\<^marker>\<open>tag important\<close> circlepath :: "[complex, real, real] \<Rightarrow> complex"
  where "circlepath z r \<equiv> part_circlepath z r 0 (2*pi)"

lemma circlepath: "circlepath z r = (\<lambda>x. z + r * exp(2 * of_real pi * \<i> * of_real x))"
  by (simp add: circlepath_def part_circlepath_def linepath_def algebra_simps)

lemma pathstart_circlepath [simp]: "pathstart (circlepath z r) = z + r"
  by (simp add: circlepath_def)

lemma pathfinish_circlepath [simp]: "pathfinish (circlepath z r) = z + r"
  by (simp add: circlepath_def) (metis exp_two_pi_i mult.commute)

lemma circlepath_minus: "circlepath z (-r) x = circlepath z r (x + 1/2)"
proof -
  have "z + of_real r * exp (2 * pi * \<i> * (x + 1/2)) =
        z + of_real r * exp (2 * pi * \<i> * x + pi * \<i>)"
    by (simp add: divide_simps) (simp add: algebra_simps)
  also have "\<dots> = z - r * exp (2 * pi * \<i> * x)"
    by (simp add: exp_add)
  finally show ?thesis
    by (simp add: circlepath path_image_def sphere_def dist_norm)
qed

lemma circlepath_add1: "circlepath z r (x+1) = circlepath z r x"
  using circlepath_minus [of z r "x+1/2"] circlepath_minus [of z "-r" x]
  by (simp add: add.commute)

lemma circlepath_add_half: "circlepath z r (x + 1/2) = circlepath z r (x - 1/2)"
  using circlepath_add1 [of z r "x-1/2"]
  by (simp add: add.commute)

lemma path_image_circlepath_minus_subset:
     "path_image (circlepath z (-r)) \<subseteq> path_image (circlepath z r)"
  apply (simp add: path_image_def image_def circlepath_minus, clarify)
  apply (case_tac "xa \<le> 1/2", force)
  apply (force simp: circlepath_add_half)+
  done

lemma path_image_circlepath_minus: "path_image (circlepath z (-r)) = path_image (circlepath z r)"
  using path_image_circlepath_minus_subset by fastforce

lemma has_vector_derivative_circlepath [derivative_intros]:
 "((circlepath z r) has_vector_derivative (2 * pi * \<i> * r * exp (2 * of_real pi * \<i> * of_real x)))
   (at x within X)"
  apply (simp add: circlepath_def scaleR_conv_of_real)
  apply (rule derivative_eq_intros)
  apply (simp add: algebra_simps)
  done

lemma vector_derivative_circlepath:
   "vector_derivative (circlepath z r) (at x) =
    2 * pi * \<i> * r * exp(2 * of_real pi * \<i> * x)"
using has_vector_derivative_circlepath vector_derivative_at by blast

lemma vector_derivative_circlepath01:
    "\<lbrakk>0 \<le> x; x \<le> 1\<rbrakk>
     \<Longrightarrow> vector_derivative (circlepath z r) (at x within {0..1}) =
          2 * pi * \<i> * r * exp(2 * of_real pi * \<i> * x)"
  using has_vector_derivative_circlepath
  by (auto simp: vector_derivative_at_within_ivl)

lemma valid_path_circlepath [simp]: "valid_path (circlepath z r)"
  by (simp add: circlepath_def)

lemma path_circlepath [simp]: "path (circlepath z r)"
  by (simp add: valid_path_imp_path)

lemma path_image_circlepath_nonneg:
  assumes "0 \<le> r" shows "path_image (circlepath z r) = sphere z r"
proof -
  have *: "x \<in> (\<lambda>u. z + (cmod (x - z)) * exp (\<i> * (of_real u * (of_real pi * 2)))) ` {0..1}" for x
  proof (cases "x = z")
    case True then show ?thesis by force
  next
    case False
    define w where "w = x - z"
    then have "w \<noteq> 0" by (simp add: False)
    have **: "\<And>t. \<lbrakk>Re w = cos t * cmod w; Im w = sin t * cmod w\<rbrakk> \<Longrightarrow> w = of_real (cmod w) * exp (\<i> * t)"
      using cis_conv_exp complex_eq_iff by auto
    show ?thesis
      apply (rule sincos_total_2pi [of "Re(w/of_real(norm w))" "Im(w/of_real(norm w))"])
      apply (simp add: divide_simps \<open>w \<noteq> 0\<close> cmod_power2 [symmetric])
      apply (rule_tac x="t / (2*pi)" in image_eqI)
      apply (simp add: field_simps \<open>w \<noteq> 0\<close>)
      using False **
      apply (auto simp: w_def)
      done
  qed
  show ?thesis
    unfolding circlepath path_image_def sphere_def dist_norm
    by (force simp: assms algebra_simps norm_mult norm_minus_commute intro: *)
qed

lemma path_image_circlepath [simp]:
    "path_image (circlepath z r) = sphere z \<bar>r\<bar>"
  using path_image_circlepath_minus
  by (force simp: path_image_circlepath_nonneg abs_if)

lemma has_contour_integral_bound_circlepath_strong:
      "\<lbrakk>(f has_contour_integral i) (circlepath z r);
        finite k; 0 \<le> B; 0 < r;
        \<And>x. \<lbrakk>norm(x - z) = r; x \<notin> k\<rbrakk> \<Longrightarrow> norm(f x) \<le> B\<rbrakk>
        \<Longrightarrow> norm i \<le> B*(2*pi*r)"
  unfolding circlepath_def
  by (auto simp: algebra_simps in_path_image_part_circlepath dest!: has_contour_integral_bound_part_circlepath_strong)

lemma has_contour_integral_bound_circlepath:
      "\<lbrakk>(f has_contour_integral i) (circlepath z r);
        0 \<le> B; 0 < r; \<And>x. norm(x - z) = r \<Longrightarrow> norm(f x) \<le> B\<rbrakk>
        \<Longrightarrow> norm i \<le> B*(2*pi*r)"
  by (auto intro: has_contour_integral_bound_circlepath_strong)

lemma contour_integrable_continuous_circlepath:
    "continuous_on (path_image (circlepath z r)) f
     \<Longrightarrow> f contour_integrable_on (circlepath z r)"
  by (simp add: circlepath_def contour_integrable_continuous_part_circlepath)

lemma simple_path_circlepath: "simple_path(circlepath z r) \<longleftrightarrow> (r \<noteq> 0)"
  by (simp add: circlepath_def simple_path_part_circlepath)

lemma notin_path_image_circlepath [simp]: "cmod (w - z) < r \<Longrightarrow> w \<notin> path_image (circlepath z r)"
  by (simp add: sphere_def dist_norm norm_minus_commute)

lemma contour_integral_circlepath:
  assumes "r > 0"
  shows "contour_integral (circlepath z r) (\<lambda>w. 1 / (w - z)) = 2 * complex_of_real pi * \<i>"
proof (rule contour_integral_unique)
  show "((\<lambda>w. 1 / (w - z)) has_contour_integral 2 * complex_of_real pi * \<i>) (circlepath z r)"
    unfolding has_contour_integral_def using assms
    apply (subst has_integral_cong)
     apply (simp add: vector_derivative_circlepath01)
    using has_integral_const_real [of _ 0 1] apply (force simp: circlepath)
    done
qed


subsection\<open> Uniform convergence of path integral\<close>

text\<open>Uniform convergence when the derivative of the path is bounded, and in particular for the special case of a circle.\<close>

proposition contour_integral_uniform_limit:
  assumes ev_fint: "eventually (\<lambda>n::'a. (f n) contour_integrable_on \<gamma>) F"
      and ul_f: "uniform_limit (path_image \<gamma>) f l F"
      and noleB: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (vector_derivative \<gamma> (at t)) \<le> B"
      and \<gamma>: "valid_path \<gamma>"
      and [simp]: "\<not> trivial_limit F"
  shows "l contour_integrable_on \<gamma>" "((\<lambda>n. contour_integral \<gamma> (f n)) \<longlongrightarrow> contour_integral \<gamma> l) F"
proof -
  have "0 \<le> B" by (meson noleB [of 0] atLeastAtMost_iff norm_ge_zero order_refl order_trans zero_le_one)
  { fix e::real
    assume "0 < e"
    then have "0 < e / (\<bar>B\<bar> + 1)" by simp
    then have "\<forall>\<^sub>F n in F. \<forall>x\<in>path_image \<gamma>. cmod (f n x - l x) < e / (\<bar>B\<bar> + 1)"
      using ul_f [unfolded uniform_limit_iff dist_norm] by auto
    with ev_fint
    obtain a where fga: "\<And>x. x \<in> {0..1} \<Longrightarrow> cmod (f a (\<gamma> x) - l (\<gamma> x)) < e / (\<bar>B\<bar> + 1)"
               and inta: "(\<lambda>t. f a (\<gamma> t) * vector_derivative \<gamma> (at t)) integrable_on {0..1}"
      using eventually_happens [OF eventually_conj]
      by (fastforce simp: contour_integrable_on path_image_def)
    have Ble: "B * e / (\<bar>B\<bar> + 1) \<le> e"
      using \<open>0 \<le> B\<close>  \<open>0 < e\<close> by (simp add: field_split_simps)
    have "\<exists>h. (\<forall>x\<in>{0..1}. cmod (l (\<gamma> x) * vector_derivative \<gamma> (at x) - h x) \<le> e) \<and> h integrable_on {0..1}"
    proof (intro exI conjI ballI)
      show "cmod (l (\<gamma> x) * vector_derivative \<gamma> (at x) - f a (\<gamma> x) * vector_derivative \<gamma> (at x)) \<le> e"
        if "x \<in> {0..1}" for x
        apply (rule order_trans [OF _ Ble])
        using noleB [OF that] fga [OF that] \<open>0 \<le> B\<close> \<open>0 < e\<close>
        apply (simp add: norm_mult left_diff_distrib [symmetric] norm_minus_commute divide_simps)
        apply (fastforce simp: mult_ac dest: mult_mono [OF less_imp_le])
        done
    qed (rule inta)
  }
  then show lintg: "l contour_integrable_on \<gamma>"
    unfolding contour_integrable_on by (metis (mono_tags, lifting)integrable_uniform_limit_real)
  { fix e::real
    define B' where "B' = B + 1"
    have B': "B' > 0" "B' > B" using  \<open>0 \<le> B\<close> by (auto simp: B'_def)
    assume "0 < e"
    then have ev_no': "\<forall>\<^sub>F n in F. \<forall>x\<in>path_image \<gamma>. 2 * cmod (f n x - l x) < e / B'"
      using ul_f [unfolded uniform_limit_iff dist_norm, rule_format, of "e / B' / 2"] B'
        by (simp add: field_simps)
    have ie: "integral {0..1::real} (\<lambda>x. e / 2) < e" using \<open>0 < e\<close> by simp
    have *: "cmod (f x (\<gamma> t) * vector_derivative \<gamma> (at t) - l (\<gamma> t) * vector_derivative \<gamma> (at t)) \<le> e / 2"
             if t: "t\<in>{0..1}" and leB': "2 * cmod (f x (\<gamma> t) - l (\<gamma> t)) < e / B'" for x t
    proof -
      have "2 * cmod (f x (\<gamma> t) - l (\<gamma> t)) * cmod (vector_derivative \<gamma> (at t)) \<le> e * (B/ B')"
        using mult_mono [OF less_imp_le [OF leB'] noleB] B' \<open>0 < e\<close> t by auto
      also have "\<dots> < e"
        by (simp add: B' \<open>0 < e\<close> mult_imp_div_pos_less)
      finally have "2 * cmod (f x (\<gamma> t) - l (\<gamma> t)) * cmod (vector_derivative \<gamma> (at t)) < e" .
      then show ?thesis
        by (simp add: left_diff_distrib [symmetric] norm_mult)
    qed
    have le_e: "\<And>x. \<lbrakk>\<forall>xa\<in>{0..1}. 2 * cmod (f x (\<gamma> xa) - l (\<gamma> xa)) < e / B'; f x contour_integrable_on \<gamma>\<rbrakk>
         \<Longrightarrow> cmod (integral {0..1}
                    (\<lambda>u. f x (\<gamma> u) * vector_derivative \<gamma> (at u) - l (\<gamma> u) * vector_derivative \<gamma> (at u))) < e"
      apply (rule le_less_trans [OF integral_norm_bound_integral ie])
        apply (simp add: lintg integrable_diff contour_integrable_on [symmetric])
       apply (blast intro: *)+
      done
    have "\<forall>\<^sub>F x in F. dist (contour_integral \<gamma> (f x)) (contour_integral \<gamma> l) < e"
      apply (rule eventually_mono [OF eventually_conj [OF ev_no' ev_fint]])
      apply (simp add: dist_norm contour_integrable_on path_image_def contour_integral_integral)
      apply (simp add: lintg integral_diff [symmetric] contour_integrable_on [symmetric] le_e)
      done
  }
  then show "((\<lambda>n. contour_integral \<gamma> (f n)) \<longlongrightarrow> contour_integral \<gamma> l) F"
    by (rule tendstoI)
qed

corollary\<^marker>\<open>tag unimportant\<close> contour_integral_uniform_limit_circlepath:
  assumes "\<forall>\<^sub>F n::'a in F. (f n) contour_integrable_on (circlepath z r)"
      and "uniform_limit (sphere z r) f l F"
      and "\<not> trivial_limit F" "0 < r"
    shows "l contour_integrable_on (circlepath z r)"
          "((\<lambda>n. contour_integral (circlepath z r) (f n)) \<longlongrightarrow> contour_integral (circlepath z r) l) F"
  using assms by (auto simp: vector_derivative_circlepath norm_mult intro!: contour_integral_uniform_limit)


subsection\<^marker>\<open>tag unimportant\<close> \<open>General stepping result for derivative formulas\<close>

lemma Cauchy_next_derivative:
  assumes "continuous_on (path_image \<gamma>) f'"
      and leB: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (vector_derivative \<gamma> (at t)) \<le> B"
      and int: "\<And>w. w \<in> s - path_image \<gamma> \<Longrightarrow> ((\<lambda>u. f' u / (u - w)^k) has_contour_integral f w) \<gamma>"
      and k: "k \<noteq> 0"
      and "open s"
      and \<gamma>: "valid_path \<gamma>"
      and w: "w \<in> s - path_image \<gamma>"
    shows "(\<lambda>u. f' u / (u - w)^(Suc k)) contour_integrable_on \<gamma>"
      and "(f has_field_derivative (k * contour_integral \<gamma> (\<lambda>u. f' u/(u - w)^(Suc k))))
           (at w)"  (is "?thes2")
proof -
  have "open (s - path_image \<gamma>)" using \<open>open s\<close> closed_valid_path_image \<gamma> by blast
  then obtain d where "d>0" and d: "ball w d \<subseteq> s - path_image \<gamma>" using w
    using open_contains_ball by blast
  have [simp]: "\<And>n. cmod (1 + of_nat n) = 1 + of_nat n"
    by (metis norm_of_nat of_nat_Suc)
  have cint: "\<And>x. \<lbrakk>x \<noteq> w; cmod (x - w) < d\<rbrakk>
         \<Longrightarrow> (\<lambda>z. (f' z / (z - x) ^ k - f' z / (z - w) ^ k) / (x * k - w * k)) contour_integrable_on \<gamma>"
    apply (rule contour_integrable_div [OF contour_integrable_diff])
    using int w d
    by (force simp: dist_norm norm_minus_commute intro!: has_contour_integral_integrable)+
  have 1: "\<forall>\<^sub>F n in at w. (\<lambda>x. f' x * (inverse (x - n) ^ k - inverse (x - w) ^ k) / (n - w) / of_nat k)
                         contour_integrable_on \<gamma>"
    unfolding eventually_at
    apply (rule_tac x=d in exI)
    apply (simp add: \<open>d > 0\<close> dist_norm field_simps cint)
    done
  have bim_g: "bounded (image f' (path_image \<gamma>))"
    by (simp add: compact_imp_bounded compact_continuous_image compact_valid_path_image assms)
  then obtain C where "C > 0" and C: "\<And>x. \<lbrakk>0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> cmod (f' (\<gamma> x)) \<le> C"
    by (force simp: bounded_pos path_image_def)
  have twom: "\<forall>\<^sub>F n in at w.
               \<forall>x\<in>path_image \<gamma>.
                cmod ((inverse (x - n) ^ k - inverse (x - w) ^ k) / (n - w) / k - inverse (x - w) ^ Suc k) < e"
         if "0 < e" for e
  proof -
    have *: "cmod ((inverse (x - u) ^ k - inverse (x - w) ^ k) / ((u - w) * k) - inverse (x - w) ^ Suc k)   < e"
            if x: "x \<in> path_image \<gamma>" and "u \<noteq> w" and uwd: "cmod (u - w) < d/2"
                and uw_less: "cmod (u - w) < e * (d/2) ^ (k+2) / (1 + real k)"
            for u x
    proof -
      define ff where [abs_def]:
        "ff n w =
          (if n = 0 then inverse(x - w)^k
           else if n = 1 then k / (x - w)^(Suc k)
           else (k * of_real(Suc k)) / (x - w)^(k + 2))" for n :: nat and w
      have km1: "\<And>z::complex. z \<noteq> 0 \<Longrightarrow> z ^ (k - Suc 0) = z ^ k / z"
        by (simp add: field_simps) (metis Suc_pred \<open>k \<noteq> 0\<close> neq0_conv power_Suc)
      have ff1: "(ff i has_field_derivative ff (Suc i) z) (at z within ball w (d/2))"
              if "z \<in> ball w (d/2)" "i \<le> 1" for i z
      proof -
        have "z \<notin> path_image \<gamma>"
          using \<open>x \<in> path_image \<gamma>\<close> d that ball_divide_subset_numeral by blast
        then have xz[simp]: "x \<noteq> z" using \<open>x \<in> path_image \<gamma>\<close> by blast
        then have neq: "x * x + z * z \<noteq> x * (z * 2)"
          by (blast intro: dest!: sum_sqs_eq)
        with xz have "\<And>v. v \<noteq> 0 \<Longrightarrow> (x * x + z * z) * v \<noteq> (x * (z * 2) * v)" by auto
        then have neqq: "\<And>v. v \<noteq> 0 \<Longrightarrow> x * (x * v) + z * (z * v) \<noteq> x * (z * (2 * v))"
          by (simp add: algebra_simps)
        show ?thesis using \<open>i \<le> 1\<close>
          apply (simp add: ff_def dist_norm Nat.le_Suc_eq km1, safe)
          apply (rule derivative_eq_intros | simp add: km1 | simp add: field_simps neq neqq)+
          done
      qed
      { fix a::real and b::real assume ab: "a > 0" "b > 0"
        then have "k * (1 + real k) * (1 / a) \<le> k * (1 + real k) * (4 / b) \<longleftrightarrow> b \<le> 4 * a"
          by (subst mult_le_cancel_left_pos)
            (use \<open>k \<noteq> 0\<close> in \<open>auto simp: divide_simps\<close>)
        with ab have "real k * (1 + real k) / a \<le> (real k * 4 + real k * real k * 4) / b \<longleftrightarrow> b \<le> 4 * a"
          by (simp add: field_simps)
      } note canc = this
      have ff2: "cmod (ff (Suc 1) v) \<le> real (k * (k + 1)) / (d/2) ^ (k + 2)"
                if "v \<in> ball w (d/2)" for v
      proof -
        have lessd: "\<And>z. cmod (\<gamma> z - v) < d/2 \<Longrightarrow> cmod (w - \<gamma> z) < d"
          by (metis that norm_minus_commute norm_triangle_half_r dist_norm mem_ball)
        have "d/2 \<le> cmod (x - v)" using d x that
          using lessd d x
          by (auto simp add: dist_norm path_image_def ball_def not_less [symmetric] del: divide_const_simps)
        then have "d \<le> cmod (x - v) * 2"
          by (simp add: field_split_simps)
        then have dpow_le: "d ^ (k+2) \<le> (cmod (x - v) * 2) ^ (k+2)"
          using \<open>0 < d\<close> order_less_imp_le power_mono by blast
        have "x \<noteq> v" using that
          using \<open>x \<in> path_image \<gamma>\<close> ball_divide_subset_numeral d by fastforce
        then show ?thesis
        using \<open>d > 0\<close> apply (simp add: ff_def norm_mult norm_divide norm_power dist_norm canc)
        using dpow_le apply (simp add: field_split_simps)
        done
      qed
      have ub: "u \<in> ball w (d/2)"
        using uwd by (simp add: dist_commute dist_norm)
      have "cmod (inverse (x - u) ^ k - (inverse (x - w) ^ k + of_nat k * (u - w) / ((x - w) * (x - w) ^ k)))
                  \<le> (real k * 4 + real k * real k * 4) * (cmod (u - w) * cmod (u - w)) / (d * (d * (d/2) ^ k))"
        using complex_Taylor [OF _ ff1 ff2 _ ub, of w, simplified]
        by (simp add: ff_def \<open>0 < d\<close>)
      then have "cmod (inverse (x - u) ^ k - (inverse (x - w) ^ k + of_nat k * (u - w) / ((x - w) * (x - w) ^ k)))
                  \<le> (cmod (u - w) * real k) * (1 + real k) * cmod (u - w) / (d/2) ^ (k+2)"
        by (simp add: field_simps)
      then have "cmod (inverse (x - u) ^ k - (inverse (x - w) ^ k + of_nat k * (u - w) / ((x - w) * (x - w) ^ k)))
                 / (cmod (u - w) * real k)
                  \<le> (1 + real k) * cmod (u - w) / (d/2) ^ (k+2)"
        using \<open>k \<noteq> 0\<close> \<open>u \<noteq> w\<close> by (simp add: mult_ac zero_less_mult_iff pos_divide_le_eq)
      also have "\<dots> < e"
        using uw_less \<open>0 < d\<close> by (simp add: mult_ac divide_simps)
      finally have e: "cmod (inverse (x-u)^k - (inverse (x-w)^k + of_nat k * (u-w) / ((x-w) * (x-w)^k)))
                        / cmod ((u - w) * real k)   <   e"
        by (simp add: norm_mult)
      have "x \<noteq> u"
        using uwd \<open>0 < d\<close> x d by (force simp: dist_norm ball_def norm_minus_commute)
      show ?thesis
        apply (rule le_less_trans [OF _ e])
        using \<open>k \<noteq> 0\<close> \<open>x \<noteq> u\<close> \<open>u \<noteq> w\<close>
        apply (simp add: field_simps norm_divide [symmetric])
        done
    qed
    show ?thesis
      unfolding eventually_at
      apply (rule_tac x = "min (d/2) ((e*(d/2)^(k + 2))/(Suc k))" in exI)
      apply (force simp: \<open>d > 0\<close> dist_norm that simp del: power_Suc intro: *)
      done
  qed
  have 2: "uniform_limit (path_image \<gamma>) (\<lambda>n x. f' x * (inverse (x - n) ^ k - inverse (x - w) ^ k) / (n - w) / of_nat k) (\<lambda>x. f' x / (x - w) ^ Suc k) (at w)"
    unfolding uniform_limit_iff dist_norm
  proof clarify
    fix e::real
    assume "0 < e"
    have *: "cmod (f' (\<gamma> x) * (inverse (\<gamma> x - u) ^ k - inverse (\<gamma> x - w) ^ k) / ((u - w) * k) -
                        f' (\<gamma> x) / ((\<gamma> x - w) * (\<gamma> x - w) ^ k)) < e"
              if ec: "cmod ((inverse (\<gamma> x - u) ^ k - inverse (\<gamma> x - w) ^ k) / ((u - w) * k) -
                      inverse (\<gamma> x - w) * inverse (\<gamma> x - w) ^ k) < e / C"
                 and x: "0 \<le> x" "x \<le> 1"
              for u x
    proof (cases "(f' (\<gamma> x)) = 0")
      case True then show ?thesis by (simp add: \<open>0 < e\<close>)
    next
      case False
      have "cmod (f' (\<gamma> x) * (inverse (\<gamma> x - u) ^ k - inverse (\<gamma> x - w) ^ k) / ((u - w) * k) -
                        f' (\<gamma> x) / ((\<gamma> x - w) * (\<gamma> x - w) ^ k)) =
            cmod (f' (\<gamma> x) * ((inverse (\<gamma> x - u) ^ k - inverse (\<gamma> x - w) ^ k) / ((u - w) * k) -
                             inverse (\<gamma> x - w) * inverse (\<gamma> x - w) ^ k))"
        by (simp add: field_simps)
      also have "\<dots> = cmod (f' (\<gamma> x)) *
                       cmod ((inverse (\<gamma> x - u) ^ k - inverse (\<gamma> x - w) ^ k) / ((u - w) * k) -
                             inverse (\<gamma> x - w) * inverse (\<gamma> x - w) ^ k)"
        by (simp add: norm_mult)
      also have "\<dots> < cmod (f' (\<gamma> x)) * (e/C)"
        using False mult_strict_left_mono [OF ec] by force
      also have "\<dots> \<le> e" using C
        by (metis False \<open>0 < e\<close> frac_le less_eq_real_def mult.commute pos_le_divide_eq x zero_less_norm_iff)
      finally show ?thesis .
    qed
    show "\<forall>\<^sub>F n in at w.
              \<forall>x\<in>path_image \<gamma>.
               cmod (f' x * (inverse (x - n) ^ k - inverse (x - w) ^ k) / (n - w) / of_nat k - f' x / (x - w) ^ Suc k) < e"
      using twom [OF divide_pos_pos [OF \<open>0 < e\<close> \<open>C > 0\<close>]]   unfolding path_image_def
      by (force intro: * elim: eventually_mono)
  qed
  show "(\<lambda>u. f' u / (u - w) ^ (Suc k)) contour_integrable_on \<gamma>"
    by (rule contour_integral_uniform_limit [OF 1 2 leB \<gamma>]) auto
  have *: "(\<lambda>n. contour_integral \<gamma> (\<lambda>x. f' x * (inverse (x - n) ^ k - inverse (x - w) ^ k) / (n - w) / k))
           \<midarrow>w\<rightarrow> contour_integral \<gamma> (\<lambda>u. f' u / (u - w) ^ (Suc k))"
    by (rule contour_integral_uniform_limit [OF 1 2 leB \<gamma>]) auto
  have **: "contour_integral \<gamma> (\<lambda>x. f' x * (inverse (x - u) ^ k - inverse (x - w) ^ k) / ((u - w) * k)) =
              (f u - f w) / (u - w) / k"
    if "dist u w < d" for u
  proof -
    have u: "u \<in> s - path_image \<gamma>"
      by (metis subsetD d dist_commute mem_ball that)
    show ?thesis
      apply (rule contour_integral_unique)
      apply (simp add: diff_divide_distrib algebra_simps)
      apply (intro has_contour_integral_diff has_contour_integral_div)
      using u w apply (simp_all add: field_simps int)
      done
  qed
  show ?thes2
    apply (simp add: has_field_derivative_iff del: power_Suc)
    apply (rule Lim_transform_within [OF tendsto_mult_left [OF *] \<open>0 < d\<close> ])
    apply (simp add: \<open>k \<noteq> 0\<close> **)
    done
qed

lemma Cauchy_next_derivative_circlepath:
  assumes contf: "continuous_on (path_image (circlepath z r)) f"
      and int: "\<And>w. w \<in> ball z r \<Longrightarrow> ((\<lambda>u. f u / (u - w)^k) has_contour_integral g w) (circlepath z r)"
      and k: "k \<noteq> 0"
      and w: "w \<in> ball z r"
    shows "(\<lambda>u. f u / (u - w)^(Suc k)) contour_integrable_on (circlepath z r)"
           (is "?thes1")
      and "(g has_field_derivative (k * contour_integral (circlepath z r) (\<lambda>u. f u/(u - w)^(Suc k)))) (at w)"
           (is "?thes2")
proof -
  have "r > 0" using w
    using ball_eq_empty by fastforce
  have wim: "w \<in> ball z r - path_image (circlepath z r)"
    using w by (auto simp: dist_norm)
  show ?thes1 ?thes2
    by (rule Cauchy_next_derivative [OF contf _ int k open_ball valid_path_circlepath wim, where B = "2 * pi * \<bar>r\<bar>"];
        auto simp: vector_derivative_circlepath norm_mult)+
qed



end