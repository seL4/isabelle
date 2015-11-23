section \<open>Complex path integrals and Cauchy's integral theorem\<close>

text\<open>By John Harrison et al.  Ported from HOL Light by L C Paulson (2015)\<close>

theory Cauchy_Integral_Thm
imports Complex_Transcendental Weierstrass Ordered_Euclidean_Space
begin

subsection \<open>Piecewise differentiable functions\<close>

definition piecewise_differentiable_on
           (infixr "piecewise'_differentiable'_on" 50)
  where "f piecewise_differentiable_on i  \<equiv>
           continuous_on i f \<and>
           (\<exists>s. finite s \<and> (\<forall>x \<in> i - s. f differentiable (at x within i)))"

lemma piecewise_differentiable_on_imp_continuous_on:
    "f piecewise_differentiable_on s \<Longrightarrow> continuous_on s f"
by (simp add: piecewise_differentiable_on_def)

lemma piecewise_differentiable_on_subset:
    "f piecewise_differentiable_on s \<Longrightarrow> t \<le> s \<Longrightarrow> f piecewise_differentiable_on t"
  using continuous_on_subset
  unfolding piecewise_differentiable_on_def
  apply safe
  apply (blast intro: elim: continuous_on_subset)
  by (meson Diff_iff differentiable_within_subset subsetCE)

lemma differentiable_on_imp_piecewise_differentiable:
  fixes a:: "'a::{linorder_topology,real_normed_vector}"
  shows "f differentiable_on {a..b} \<Longrightarrow> f piecewise_differentiable_on {a..b}"
  apply (simp add: piecewise_differentiable_on_def differentiable_imp_continuous_on)
  apply (rule_tac x="{a,b}" in exI, simp add: differentiable_on_def)
  done

lemma differentiable_imp_piecewise_differentiable:
    "(\<And>x. x \<in> s \<Longrightarrow> f differentiable (at x within s))
         \<Longrightarrow> f piecewise_differentiable_on s"
by (auto simp: piecewise_differentiable_on_def differentiable_imp_continuous_on differentiable_on_def
         intro: differentiable_within_subset)

lemma piecewise_differentiable_const [iff]: "(\<lambda>x. z) piecewise_differentiable_on s"
  by (simp add: differentiable_imp_piecewise_differentiable)

lemma piecewise_differentiable_compose:
    "\<lbrakk>f piecewise_differentiable_on s; g piecewise_differentiable_on (f ` s);
      \<And>x. finite (s \<inter> f-`{x})\<rbrakk>
      \<Longrightarrow> (g o f) piecewise_differentiable_on s"
  apply (simp add: piecewise_differentiable_on_def, safe)
  apply (blast intro: continuous_on_compose2)
  apply (rename_tac A B)
  apply (rule_tac x="A \<union> (\<Union>x\<in>B. s \<inter> f-`{x})" in exI)
  apply (blast intro: differentiable_chain_within)
  done

lemma piecewise_differentiable_affine:
  fixes m::real
  assumes "f piecewise_differentiable_on ((\<lambda>x. m *\<^sub>R x + c) ` s)"
  shows "(f o (\<lambda>x. m *\<^sub>R x + c)) piecewise_differentiable_on s"
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
  obtain s t where st: "finite s" "finite t"
                       "\<forall>x\<in>{a..c} - s. f differentiable at x within {a..c}"
                       "\<forall>x\<in>{c..b} - t. g differentiable at x within {c..b}"
    using assms
    by (auto simp: piecewise_differentiable_on_def)
  have finabc: "finite ({a,b,c} \<union> (s \<union> t))"
    by (metis \<open>finite s\<close> \<open>finite t\<close> finite_Un finite_insert finite.emptyI)
  have "continuous_on {a..c} f" "continuous_on {c..b} g"
    using assms piecewise_differentiable_on_def by auto
  then have "continuous_on {a..b} (\<lambda>x. if x \<le> c then f x else g x)"
    using continuous_on_cases [OF closed_real_atLeastAtMost [of a c],
                               OF closed_real_atLeastAtMost [of c b],
                               of f g "\<lambda>x. x\<le>c"]  assms
    by (force simp: ivl_disj_un_two_touch)
  moreover
  { fix x
    assume x: "x \<in> {a..b} - ({a,b,c} \<union> (s \<union> t))"
    have "(\<lambda>x. if x \<le> c then f x else g x) differentiable at x within {a..b}" (is "?diff_fg")
    proof (cases x c rule: le_cases)
      case le show ?diff_fg
        apply (rule differentiable_transform_within [where d = "dist x c" and f = f])
        using x le st
        apply (simp_all add: dist_real_def dist_nz [symmetric])
        apply (rule differentiable_at_withinI)
        apply (rule differentiable_within_open [where s = "{a<..<c} - s", THEN iffD1], simp_all)
        apply (blast intro: open_greaterThanLessThan finite_imp_closed)
        apply (force elim!: differentiable_subset)
        done
    next
      case ge show ?diff_fg
        apply (rule differentiable_transform_within [where d = "dist x c" and f = g])
        using x ge st
        apply (simp_all add: dist_real_def dist_nz [symmetric])
        apply (rule differentiable_at_withinI)
        apply (rule differentiable_within_open [where s = "{c<..<b} - t", THEN iffD1], simp_all)
        apply (blast intro: open_greaterThanLessThan finite_imp_closed)
        apply (force elim!: differentiable_subset)
        done
    qed
  }
  then have "\<exists>s. finite s \<and>
                 (\<forall>x\<in>{a..b} - s. (\<lambda>x. if x \<le> c then f x else g x) differentiable at x within {a..b})"
    by (meson finabc)
  ultimately show ?thesis
    by (simp add: piecewise_differentiable_on_def)
qed

lemma piecewise_differentiable_neg:
    "f piecewise_differentiable_on s \<Longrightarrow> (\<lambda>x. -(f x)) piecewise_differentiable_on s"
  by (auto simp: piecewise_differentiable_on_def continuous_on_minus)

lemma piecewise_differentiable_add:
  assumes "f piecewise_differentiable_on i"
          "g piecewise_differentiable_on i"
    shows "(\<lambda>x. f x + g x) piecewise_differentiable_on i"
proof -
  obtain s t where st: "finite s" "finite t"
                       "\<forall>x\<in>i - s. f differentiable at x within i"
                       "\<forall>x\<in>i - t. g differentiable at x within i"
    using assms by (auto simp: piecewise_differentiable_on_def)
  then have "finite (s \<union> t) \<and> (\<forall>x\<in>i - (s \<union> t). (\<lambda>x. f x + g x) differentiable at x within i)"
    by auto
  moreover have "continuous_on i f" "continuous_on i g"
    using assms piecewise_differentiable_on_def by auto
  ultimately show ?thesis
    by (auto simp: piecewise_differentiable_on_def continuous_on_add)
qed

lemma piecewise_differentiable_diff:
    "\<lbrakk>f piecewise_differentiable_on s;  g piecewise_differentiable_on s\<rbrakk>
     \<Longrightarrow> (\<lambda>x. f x - g x) piecewise_differentiable_on s"
  unfolding diff_conv_add_uminus
  by (metis piecewise_differentiable_add piecewise_differentiable_neg)

lemma continuous_on_joinpaths_D1:
    "continuous_on {0..1} (g1 +++ g2) \<Longrightarrow> continuous_on {0..1} g1"
  apply (rule continuous_on_eq [of _ "(g1 +++ g2) o (op*(inverse 2))"])
  apply (rule continuous_intros | simp)+
  apply (auto elim!: continuous_on_subset simp: joinpaths_def)
  done

lemma continuous_on_joinpaths_D2:
    "\<lbrakk>continuous_on {0..1} (g1 +++ g2); pathfinish g1 = pathstart g2\<rbrakk> \<Longrightarrow> continuous_on {0..1} g2"
  apply (rule continuous_on_eq [of _ "(g1 +++ g2) o (\<lambda>x. inverse 2*x + 1/2)"])
  apply (rule continuous_intros | simp)+
  apply (auto elim!: continuous_on_subset simp add: joinpaths_def pathfinish_def pathstart_def Ball_def)
  done

lemma piecewise_differentiable_D1:
    "(g1 +++ g2) piecewise_differentiable_on {0..1} \<Longrightarrow> g1 piecewise_differentiable_on {0..1}"
  apply (clarsimp simp add: piecewise_differentiable_on_def dest!: continuous_on_joinpaths_D1)
  apply (rule_tac x="insert 1 ((op*2)`s)" in exI)
  apply simp
  apply (intro ballI)
  apply (rule_tac d="dist (x/2) (1/2)" and f = "(g1 +++ g2) o (op*(inverse 2))"
       in differentiable_transform_within)
  apply (auto simp: dist_real_def joinpaths_def)
  apply (rule differentiable_chain_within derivative_intros | simp)+
  apply (rule differentiable_subset)
  apply (force simp:)+
  done

lemma piecewise_differentiable_D2:
    "\<lbrakk>(g1 +++ g2) piecewise_differentiable_on {0..1}; pathfinish g1 = pathstart g2\<rbrakk>
    \<Longrightarrow> g2 piecewise_differentiable_on {0..1}"
  apply (clarsimp simp add: piecewise_differentiable_on_def dest!: continuous_on_joinpaths_D2)
  apply (rule_tac x="insert 0 ((\<lambda>x. 2*x-1)`s)" in exI)
  apply simp
  apply (intro ballI)
  apply (rule_tac d="dist ((x+1)/2) (1/2)" and f = "(g1 +++ g2) o (\<lambda>x. (x+1)/2)"
          in differentiable_transform_within)
  apply (auto simp: dist_real_def joinpaths_def abs_if field_simps split: split_if_asm)
  apply (rule differentiable_chain_within derivative_intros | simp)+
  apply (rule differentiable_subset)
  apply (force simp: divide_simps)+
  done


subsubsection\<open>The concept of continuously differentiable\<close>

definition C1_differentiable_on :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> real set \<Rightarrow> bool"
           (infix "C1'_differentiable'_on" 50)
  where
  "f C1_differentiable_on s \<longleftrightarrow>
   (\<exists>D. (\<forall>x \<in> s. (f has_vector_derivative (D x)) (at x)) \<and> continuous_on s D)"

lemma C1_differentiable_on_eq:
    "f C1_differentiable_on s \<longleftrightarrow>
     (\<forall>x \<in> s. f differentiable at x) \<and> continuous_on s (\<lambda>x. vector_derivative f (at x))"
  unfolding C1_differentiable_on_def
  apply safe
  using differentiable_def has_vector_derivative_def apply blast
  apply (erule continuous_on_eq)
  using vector_derivative_at apply fastforce
  using vector_derivative_works apply fastforce
  done

lemma C1_differentiable_on_subset:
  "f C1_differentiable_on t \<Longrightarrow> s \<subseteq> t \<Longrightarrow> f C1_differentiable_on s"
  unfolding C1_differentiable_on_def  continuous_on_eq_continuous_within
  by (blast intro:  continuous_within_subset)

lemma C1_differentiable_compose:
    "\<lbrakk>f C1_differentiable_on s; g C1_differentiable_on (f ` s);
      \<And>x. finite (s \<inter> f-`{x})\<rbrakk>
      \<Longrightarrow> (g o f) C1_differentiable_on s"
  apply (simp add: C1_differentiable_on_eq, safe)
   using differentiable_chain_at apply blast
  apply (rule continuous_on_eq [of _ "\<lambda>x. vector_derivative f (at x) *\<^sub>R vector_derivative g (at (f x))"])
   apply (rule Limits.continuous_on_scaleR, assumption)
   apply (metis (mono_tags, lifting) continuous_on_eq continuous_at_imp_continuous_on continuous_on_compose differentiable_imp_continuous_within o_def)
  by (simp add: vector_derivative_chain_at)

lemma C1_diff_imp_diff: "f C1_differentiable_on s \<Longrightarrow> f differentiable_on s"
  by (simp add: C1_differentiable_on_eq differentiable_at_imp_differentiable_on)

lemma C1_differentiable_on_ident [simp, derivative_intros]: "(\<lambda>x. x) C1_differentiable_on s"
  by (auto simp: C1_differentiable_on_eq continuous_on_const)

lemma C1_differentiable_on_const [simp, derivative_intros]: "(\<lambda>z. a) C1_differentiable_on s"
  by (auto simp: C1_differentiable_on_eq continuous_on_const)

lemma C1_differentiable_on_add [simp, derivative_intros]:
  "f C1_differentiable_on s \<Longrightarrow> g C1_differentiable_on s \<Longrightarrow> (\<lambda>x. f x + g x) C1_differentiable_on s"
  unfolding C1_differentiable_on_eq  by (auto intro: continuous_intros)

lemma C1_differentiable_on_minus [simp, derivative_intros]:
  "f C1_differentiable_on s \<Longrightarrow> (\<lambda>x. - f x) C1_differentiable_on s"
  unfolding C1_differentiable_on_eq  by (auto intro: continuous_intros)

lemma C1_differentiable_on_diff [simp, derivative_intros]:
  "f C1_differentiable_on s \<Longrightarrow> g C1_differentiable_on s \<Longrightarrow> (\<lambda>x. f x - g x) C1_differentiable_on s"
  unfolding C1_differentiable_on_eq  by (auto intro: continuous_intros)

lemma C1_differentiable_on_mult [simp, derivative_intros]:
  fixes f g :: "real \<Rightarrow> 'a :: real_normed_algebra"
  shows "f C1_differentiable_on s \<Longrightarrow> g C1_differentiable_on s \<Longrightarrow> (\<lambda>x. f x * g x) C1_differentiable_on s"
  unfolding C1_differentiable_on_eq
  by (auto simp: continuous_on_add continuous_on_mult continuous_at_imp_continuous_on differentiable_imp_continuous_within)

lemma C1_differentiable_on_scaleR [simp, derivative_intros]:
  "f C1_differentiable_on s \<Longrightarrow> g C1_differentiable_on s \<Longrightarrow> (\<lambda>x. f x *\<^sub>R g x) C1_differentiable_on s"
  unfolding C1_differentiable_on_eq
  by (rule continuous_intros | simp add: continuous_at_imp_continuous_on differentiable_imp_continuous_within)+


definition piecewise_C1_differentiable_on
           (infixr "piecewise'_C1'_differentiable'_on" 50)
  where "f piecewise_C1_differentiable_on i  \<equiv>
           continuous_on i f \<and>
           (\<exists>s. finite s \<and> (f C1_differentiable_on (i - s)))"

lemma C1_differentiable_imp_piecewise:
    "f C1_differentiable_on s \<Longrightarrow> f piecewise_C1_differentiable_on s"
  by (auto simp: piecewise_C1_differentiable_on_def C1_differentiable_on_eq continuous_at_imp_continuous_on differentiable_imp_continuous_within)

lemma piecewise_C1_imp_differentiable:
    "f piecewise_C1_differentiable_on i \<Longrightarrow> f piecewise_differentiable_on i"
  by (auto simp: piecewise_C1_differentiable_on_def piecewise_differentiable_on_def
           C1_differentiable_on_def differentiable_def has_vector_derivative_def
           intro: has_derivative_at_within)

lemma piecewise_C1_differentiable_compose:
    "\<lbrakk>f piecewise_C1_differentiable_on s; g piecewise_C1_differentiable_on (f ` s);
      \<And>x. finite (s \<inter> f-`{x})\<rbrakk>
      \<Longrightarrow> (g o f) piecewise_C1_differentiable_on s"
  apply (simp add: piecewise_C1_differentiable_on_def, safe)
  apply (blast intro: continuous_on_compose2)
  apply (rename_tac A B)
  apply (rule_tac x="A \<union> (\<Union>x\<in>B. s \<inter> f-`{x})" in exI)
  apply (rule conjI, blast)
  apply (rule C1_differentiable_compose)
  apply (blast intro: C1_differentiable_on_subset)
  apply (blast intro: C1_differentiable_on_subset)
  by (simp add: Diff_Int_distrib2)

lemma piecewise_C1_differentiable_on_subset:
    "f piecewise_C1_differentiable_on s \<Longrightarrow> t \<le> s \<Longrightarrow> f piecewise_C1_differentiable_on t"
  by (auto simp: piecewise_C1_differentiable_on_def elim!: continuous_on_subset C1_differentiable_on_subset)

lemma C1_differentiable_imp_continuous_on:
  "f C1_differentiable_on s \<Longrightarrow> continuous_on s f"
  unfolding C1_differentiable_on_eq continuous_on_eq_continuous_within
  using differentiable_at_withinI differentiable_imp_continuous_within by blast

lemma C1_differentiable_on_empty [iff]: "f C1_differentiable_on {}"
  unfolding C1_differentiable_on_def
  by auto

lemma piecewise_C1_differentiable_affine:
  fixes m::real
  assumes "f piecewise_C1_differentiable_on ((\<lambda>x. m * x + c) ` s)"
  shows "(f o (\<lambda>x. m *\<^sub>R x + c)) piecewise_C1_differentiable_on s"
proof (cases "m = 0")
  case True
  then show ?thesis
    unfolding o_def by (auto simp: piecewise_C1_differentiable_on_def continuous_on_const)
next
  case False
  show ?thesis
    apply (rule piecewise_C1_differentiable_compose [OF C1_differentiable_imp_piecewise])
    apply (rule assms derivative_intros | simp add: False vimage_def)+
    using real_vector_affinity_eq [OF False, where c=c, unfolded scaleR_conv_of_real]
    apply simp
    done
qed

lemma piecewise_C1_differentiable_cases:
  fixes c::real
  assumes "f piecewise_C1_differentiable_on {a..c}"
          "g piecewise_C1_differentiable_on {c..b}"
           "a \<le> c" "c \<le> b" "f c = g c"
  shows "(\<lambda>x. if x \<le> c then f x else g x) piecewise_C1_differentiable_on {a..b}"
proof -
  obtain s t where st: "f C1_differentiable_on ({a..c} - s)"
                       "g C1_differentiable_on ({c..b} - t)"
                       "finite s" "finite t"
    using assms
    by (force simp: piecewise_C1_differentiable_on_def)
  then have f_diff: "f differentiable_on {a..<c} - s"
        and g_diff: "g differentiable_on {c<..b} - t"
    by (simp_all add: C1_differentiable_on_eq differentiable_at_withinI differentiable_on_def)
  have "continuous_on {a..c} f" "continuous_on {c..b} g"
    using assms piecewise_C1_differentiable_on_def by auto
  then have cab: "continuous_on {a..b} (\<lambda>x. if x \<le> c then f x else g x)"
    using continuous_on_cases [OF closed_real_atLeastAtMost [of a c],
                               OF closed_real_atLeastAtMost [of c b],
                               of f g "\<lambda>x. x\<le>c"]  assms
    by (force simp: ivl_disj_un_two_touch)
  { fix x
    assume x: "x \<in> {a..b} - insert c (s \<union> t)"
    have "(\<lambda>x. if x \<le> c then f x else g x) differentiable at x" (is "?diff_fg")
    proof (cases x c rule: le_cases)
      case le show ?diff_fg
        apply (rule differentiable_transform_at [of "dist x c" _ f])
        using x dist_real_def le st by (auto simp: C1_differentiable_on_eq)
    next
      case ge show ?diff_fg
        apply (rule differentiable_transform_at [of "dist x c" _ g])
        using dist_nz x dist_real_def ge st x by (auto simp: C1_differentiable_on_eq)
    qed
  }
  then have "(\<forall>x \<in> {a..b} - insert c (s \<union> t). (\<lambda>x. if x \<le> c then f x else g x) differentiable at x)"
    by auto
  moreover
  { assume fcon: "continuous_on ({a<..<c} - s) (\<lambda>x. vector_derivative f (at x))"
       and gcon: "continuous_on ({c<..<b} - t) (\<lambda>x. vector_derivative g (at x))"
    have "open ({a<..<c} - s)"  "open ({c<..<b} - t)"
      using st by (simp_all add: open_Diff finite_imp_closed)
    moreover have "continuous_on ({a<..<c} - s) (\<lambda>x. vector_derivative (\<lambda>x. if x \<le> c then f x else g x) (at x))"
      apply (rule continuous_on_eq [OF fcon])
      apply (simp add:)
      apply (rule vector_derivative_at [symmetric])
      apply (rule_tac f=f and d="dist x c" in has_vector_derivative_transform_at)
      apply (simp_all add: dist_norm vector_derivative_works [symmetric])
      using f_diff
      by (meson C1_differentiable_on_eq Diff_iff atLeastAtMost_iff less_imp_le st(1))
    moreover have "continuous_on ({c<..<b} - t) (\<lambda>x. vector_derivative (\<lambda>x. if x \<le> c then f x else g x) (at x))"
      apply (rule continuous_on_eq [OF gcon])
      apply (simp add:)
      apply (rule vector_derivative_at [symmetric])
      apply (rule_tac f=g and d="dist x c" in has_vector_derivative_transform_at)
      apply (simp_all add: dist_norm vector_derivative_works [symmetric])
      using g_diff
      by (meson C1_differentiable_on_eq Diff_iff atLeastAtMost_iff less_imp_le st(2))
    ultimately have "continuous_on ({a<..<b} - insert c (s \<union> t))
        (\<lambda>x. vector_derivative (\<lambda>x. if x \<le> c then f x else g x) (at x))"
      apply (rule continuous_on_subset [OF continuous_on_open_Un], auto)
      done
  } note * = this
  have "continuous_on ({a<..<b} - insert c (s \<union> t)) (\<lambda>x. vector_derivative (\<lambda>x. if x \<le> c then f x else g x) (at x))"
    using st
    by (auto simp: C1_differentiable_on_eq elim!: continuous_on_subset intro: *)
  ultimately have "\<exists>s. finite s \<and> ((\<lambda>x. if x \<le> c then f x else g x) C1_differentiable_on {a..b} - s)"
    apply (rule_tac x="{a,b,c} \<union> s \<union> t" in exI)
    using st  by (auto simp: C1_differentiable_on_eq elim!: continuous_on_subset)
  with cab show ?thesis
    by (simp add: piecewise_C1_differentiable_on_def)
qed

lemma piecewise_C1_differentiable_neg:
    "f piecewise_C1_differentiable_on s \<Longrightarrow> (\<lambda>x. -(f x)) piecewise_C1_differentiable_on s"
  unfolding piecewise_C1_differentiable_on_def
  by (auto intro!: continuous_on_minus C1_differentiable_on_minus)

lemma piecewise_C1_differentiable_add:
  assumes "f piecewise_C1_differentiable_on i"
          "g piecewise_C1_differentiable_on i"
    shows "(\<lambda>x. f x + g x) piecewise_C1_differentiable_on i"
proof -
  obtain s t where st: "finite s" "finite t"
                       "f C1_differentiable_on (i-s)"
                       "g C1_differentiable_on (i-t)"
    using assms by (auto simp: piecewise_C1_differentiable_on_def)
  then have "finite (s \<union> t) \<and> (\<lambda>x. f x + g x) C1_differentiable_on i - (s \<union> t)"
    by (auto intro: C1_differentiable_on_add elim!: C1_differentiable_on_subset)
  moreover have "continuous_on i f" "continuous_on i g"
    using assms piecewise_C1_differentiable_on_def by auto
  ultimately show ?thesis
    by (auto simp: piecewise_C1_differentiable_on_def continuous_on_add)
qed

lemma piecewise_C1_differentiable_diff:
    "\<lbrakk>f piecewise_C1_differentiable_on s;  g piecewise_C1_differentiable_on s\<rbrakk>
     \<Longrightarrow> (\<lambda>x. f x - g x) piecewise_C1_differentiable_on s"
  unfolding diff_conv_add_uminus
  by (metis piecewise_C1_differentiable_add piecewise_C1_differentiable_neg)

lemma piecewise_C1_differentiable_D1:
  fixes g1 :: "real \<Rightarrow> 'a::real_normed_field"
  assumes "(g1 +++ g2) piecewise_C1_differentiable_on {0..1}"
    shows "g1 piecewise_C1_differentiable_on {0..1}"
proof -
  obtain s where "finite s"
             and co12: "continuous_on ({0..1} - s) (\<lambda>x. vector_derivative (g1 +++ g2) (at x))"
             and g12D: "\<forall>x\<in>{0..1} - s. g1 +++ g2 differentiable at x"
    using assms  by (auto simp: piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  then have g1D: "g1 differentiable at x" if "x \<in> {0..1} - insert 1 (op * 2 ` s)" for x
    apply (rule_tac d="dist (x/2) (1/2)" and f = "(g1 +++ g2) o (op*(inverse 2))" in differentiable_transform_at)
    using that
    apply (simp_all add: dist_real_def joinpaths_def)
    apply (rule differentiable_chain_at derivative_intros | force)+
    done
  have [simp]: "vector_derivative (g1 \<circ> op * 2) (at (x/2)) = 2 *\<^sub>R vector_derivative g1 (at x)"
               if "x \<in> {0..1} - insert 1 (op * 2 ` s)" for x
    apply (subst vector_derivative_chain_at)
    using that
    apply (rule derivative_eq_intros g1D | simp)+
    done
  have "continuous_on ({0..1/2} - insert (1/2) s) (\<lambda>x. vector_derivative (g1 +++ g2) (at x))"
    using co12 by (rule continuous_on_subset) force
  then have coDhalf: "continuous_on ({0..1/2} - insert (1/2) s) (\<lambda>x. vector_derivative (g1 o op*2) (at x))"
    apply (rule continuous_on_eq [OF _ vector_derivative_at])
    apply (rule_tac f="g1 o op*2" and d="dist x (1/2)" in has_vector_derivative_transform_at)
    apply (simp_all add: dist_norm joinpaths_def vector_derivative_works [symmetric])
    apply (force intro: g1D differentiable_chain_at)
    done
  have "continuous_on ({0..1} - insert 1 (op * 2 ` s))
                      ((\<lambda>x. 1/2 * vector_derivative (g1 o op*2) (at x)) o op*(1/2))"
    apply (rule continuous_intros)+
    using coDhalf
    apply (simp add: scaleR_conv_of_real image_set_diff image_image)
    done
  then have con_g1: "continuous_on ({0..1} - insert 1 (op * 2 ` s)) (\<lambda>x. vector_derivative g1 (at x))"
    by (rule continuous_on_eq) (simp add: scaleR_conv_of_real)
  have "continuous_on {0..1} g1"
    using continuous_on_joinpaths_D1 assms piecewise_C1_differentiable_on_def by blast
  with \<open>finite s\<close> show ?thesis
    apply (clarsimp simp add: piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
    apply (rule_tac x="insert 1 ((op*2)`s)" in exI)
    apply (simp add: g1D con_g1)
  done
qed

lemma piecewise_C1_differentiable_D2:
  fixes g2 :: "real \<Rightarrow> 'a::real_normed_field"
  assumes "(g1 +++ g2) piecewise_C1_differentiable_on {0..1}" "pathfinish g1 = pathstart g2"
    shows "g2 piecewise_C1_differentiable_on {0..1}"
proof -
  obtain s where "finite s"
             and co12: "continuous_on ({0..1} - s) (\<lambda>x. vector_derivative (g1 +++ g2) (at x))"
             and g12D: "\<forall>x\<in>{0..1} - s. g1 +++ g2 differentiable at x"
    using assms  by (auto simp: piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  then have g2D: "g2 differentiable at x" if "x \<in> {0..1} - insert 0 ((\<lambda>x. 2*x-1) ` s)" for x
    apply (rule_tac d="dist ((x+1)/2) (1/2)" and f = "(g1 +++ g2) o (\<lambda>x. (x+1)/2)" in differentiable_transform_at)
    using that
    apply (simp_all add: dist_real_def joinpaths_def)
    apply (auto simp: dist_real_def joinpaths_def field_simps)
    apply (rule differentiable_chain_at derivative_intros | force)+
    apply (drule_tac x= "(x + 1) / 2" in bspec, force simp: divide_simps)
    apply assumption
    done
  have [simp]: "vector_derivative (g2 \<circ> (\<lambda>x. 2*x-1)) (at ((x+1)/2)) = 2 *\<^sub>R vector_derivative g2 (at x)"
               if "x \<in> {0..1} - insert 0 ((\<lambda>x. 2*x-1) ` s)" for x
    using that  by (auto simp: vector_derivative_chain_at divide_simps g2D)
  have "continuous_on ({1/2..1} - insert (1/2) s) (\<lambda>x. vector_derivative (g1 +++ g2) (at x))"
    using co12 by (rule continuous_on_subset) force
  then have coDhalf: "continuous_on ({1/2..1} - insert (1/2) s) (\<lambda>x. vector_derivative (g2 o (\<lambda>x. 2*x-1)) (at x))"
    apply (rule continuous_on_eq [OF _ vector_derivative_at])
    apply (rule_tac f="g2 o (\<lambda>x. 2*x-1)" and d="dist (3/4) ((x+1)/2)" in has_vector_derivative_transform_at)
    apply (auto simp: dist_real_def field_simps joinpaths_def vector_derivative_works [symmetric]
                intro!: g2D differentiable_chain_at)
    done
  have [simp]: "((\<lambda>x. (x + 1) / 2) ` ({0..1} - insert 0 ((\<lambda>x. 2 * x - 1) ` s))) = ({1/2..1} - insert (1/2) s)"
    apply (simp add: image_set_diff inj_on_def image_image)
    apply (auto simp: image_affinity_atLeastAtMost_div add_divide_distrib)
    done
  have "continuous_on ({0..1} - insert 0 ((\<lambda>x. 2*x-1) ` s))
                      ((\<lambda>x. 1/2 * vector_derivative (g2 \<circ> (\<lambda>x. 2*x-1)) (at x)) o (\<lambda>x. (x+1)/2))"
    by (rule continuous_intros | simp add:  coDhalf)+
  then have con_g2: "continuous_on ({0..1} - insert 0 ((\<lambda>x. 2*x-1) ` s)) (\<lambda>x. vector_derivative g2 (at x))"
    by (rule continuous_on_eq) (simp add: scaleR_conv_of_real)
  have "continuous_on {0..1} g2"
    using continuous_on_joinpaths_D2 assms piecewise_C1_differentiable_on_def by blast
  with \<open>finite s\<close> show ?thesis
    apply (clarsimp simp add: piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
    apply (rule_tac x="insert 0 ((\<lambda>x. 2 * x - 1) ` s)" in exI)
    apply (simp add: g2D con_g2)
  done
qed

subsection \<open>Valid paths, and their start and finish\<close>

lemma Diff_Un_eq: "A - (B \<union> C) = A - B - C"
  by blast

definition valid_path :: "(real \<Rightarrow> 'a :: real_normed_vector) \<Rightarrow> bool"
  where "valid_path f \<equiv> f piecewise_C1_differentiable_on {0..1::real}"

definition closed_path :: "(real \<Rightarrow> 'a :: real_normed_vector) \<Rightarrow> bool"
  where "closed_path g \<equiv> g 0 = g 1"

subsubsection\<open>In particular, all results for paths apply\<close>

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


subsection\<open>Contour Integrals along a path\<close>

text\<open>This definition is for complex numbers only, and does not generalise to line integrals in a vector field\<close>

text\<open>piecewise differentiable function on [0,1]\<close>

definition has_contour_integral :: "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> bool"
           (infixr "has'_contour'_integral" 50)
  where "(f has_contour_integral i) g \<equiv>
           ((\<lambda>x. f(g x) * vector_derivative g (at x within {0..1}))
            has_integral i) {0..1}"

definition contour_integrable_on
           (infixr "contour'_integrable'_on" 50)
  where "f contour_integrable_on g \<equiv> \<exists>i. (f has_contour_integral i) g"

definition contour_integral
  where "contour_integral g f \<equiv> @i. (f has_contour_integral i) g"

lemma contour_integral_unique: "(f has_contour_integral i)  g \<Longrightarrow> contour_integral g f = i"
  by (auto simp: contour_integral_def has_contour_integral_def integral_def [symmetric])

lemma has_contour_integral_integral:
    "f contour_integrable_on i \<Longrightarrow> (f has_contour_integral (contour_integral i f)) i"
  by (metis contour_integral_unique contour_integrable_on_def)

lemma has_contour_integral_unique:
    "(f has_contour_integral i) g \<Longrightarrow> (f has_contour_integral j) g \<Longrightarrow> i = j"
  using has_integral_unique
  by (auto simp: has_contour_integral_def)

lemma has_contour_integral_integrable: "(f has_contour_integral i) g \<Longrightarrow> f contour_integrable_on g"
  using contour_integrable_on_def by blast

(* Show that we can forget about the localized derivative.*)

lemma vector_derivative_within_interior:
     "\<lbrakk>x \<in> interior s; NO_MATCH UNIV s\<rbrakk>
      \<Longrightarrow> vector_derivative f (at x within s) = vector_derivative f (at x)"
  apply (simp add: vector_derivative_def has_vector_derivative_def has_derivative_def netlimit_within_interior)
  apply (subst lim_within_interior, auto)
  done

lemma has_integral_localized_vector_derivative:
    "((\<lambda>x. f (g x) * vector_derivative g (at x within {a..b})) has_integral i) {a..b} \<longleftrightarrow>
     ((\<lambda>x. f (g x) * vector_derivative g (at x)) has_integral i) {a..b}"
proof -
  have "{a..b} - {a,b} = interior {a..b}"
    by (simp add: atLeastAtMost_diff_ends)
  show ?thesis
    apply (rule has_integral_spike_eq [of "{a,b}"])
    apply (auto simp: vector_derivative_within_interior)
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

subsection\<open>Reversing a path\<close>

lemma valid_path_imp_reverse:
  assumes "valid_path g"
    shows "valid_path(reversepath g)"
proof -
  obtain s where "finite s" "g C1_differentiable_on ({0..1} - s)"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def)
  then have "finite (op - 1 ` s)" "(reversepath g C1_differentiable_on ({0..1} - op - 1 ` s))"
    apply (auto simp: reversepath_def)
    apply (rule C1_differentiable_compose [of "\<lambda>x::real. 1-x" _ g, unfolded o_def])
    apply (auto simp: C1_differentiable_on_eq)
    apply (rule continuous_intros, force)
    apply (force elim!: continuous_on_subset)
    apply (simp add: finite_vimageI inj_on_def)
    done
  then show ?thesis using assms
    by (auto simp: valid_path_def piecewise_C1_differentiable_on_def path_def [symmetric])
qed

lemma valid_path_reversepath: "valid_path(reversepath g) \<longleftrightarrow> valid_path g"
  using valid_path_imp_reverse by force

lemma has_contour_integral_reversepath:
  assumes "valid_path g" "(f has_contour_integral i) g"
    shows "(f has_contour_integral (-i)) (reversepath g)"
proof -
  { fix s x
    assume xs: "g C1_differentiable_on ({0..1} - s)" "x \<notin> op - 1 ` s" "0 \<le> x" "x \<le> 1"
      have "vector_derivative (\<lambda>x. g (1 - x)) (at x within {0..1}) =
            - vector_derivative g (at (1 - x) within {0..1})"
      proof -
        obtain f' where f': "(g has_vector_derivative f') (at (1 - x))"
          using xs
          by (force simp: has_vector_derivative_def C1_differentiable_on_def)
        have "(g o (\<lambda>x. 1 - x) has_vector_derivative -1 *\<^sub>R f') (at x)"
          apply (rule vector_diff_chain_within)
          apply (intro vector_diff_chain_within derivative_eq_intros | simp)+
          apply (rule has_vector_derivative_at_within [OF f'])
          done
        then have mf': "((\<lambda>x. g (1 - x)) has_vector_derivative -f') (at x)"
          by (simp add: o_def)
        show ?thesis
          using xs
          by (auto simp: vector_derivative_at_within_ivl [OF mf'] vector_derivative_at_within_ivl [OF f'])
      qed
  } note * = this
  have 01: "{0..1::real} = cbox 0 1"
    by simp
  show ?thesis using assms
    apply (auto simp: has_contour_integral_def)
    apply (drule has_integral_affinity01 [where m= "-1" and c=1])
    apply (auto simp: reversepath_def valid_path_def piecewise_C1_differentiable_on_def)
    apply (drule has_integral_neg)
    apply (rule_tac s = "(\<lambda>x. 1 - x) ` s" in has_integral_spike_finite)
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
    "\<lbrakk>valid_path g; f contour_integrable_on g\<rbrakk> \<Longrightarrow> contour_integral (reversepath g) f = -(contour_integral g f)"
  using has_contour_integral_reversepath contour_integrable_on_def contour_integral_unique by blast


subsection\<open>Joining two paths together\<close>

lemma valid_path_join:
  assumes "valid_path g1" "valid_path g2" "pathfinish g1 = pathstart g2"
    shows "valid_path(g1 +++ g2)"
proof -
  have "g1 1 = g2 0"
    using assms by (auto simp: pathfinish_def pathstart_def)
  moreover have "(g1 o (\<lambda>x. 2*x)) piecewise_C1_differentiable_on {0..1/2}"
    apply (rule piecewise_C1_differentiable_compose)
    using assms
    apply (auto simp: valid_path_def piecewise_C1_differentiable_on_def continuous_on_joinpaths)
    apply (rule continuous_intros | simp)+
    apply (force intro: finite_vimageI [where h = "op*2"] inj_onI)
    done
  moreover have "(g2 o (\<lambda>x. 2*x-1)) piecewise_C1_differentiable_on {1/2..1}"
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
    apply (rule vector_derivative_at [OF has_vector_derivative_transform_at [of "\<bar>z - 1/2\<bar>" _ "(\<lambda>x. g1(2*x))"]])
    apply (simp_all add: dist_real_def abs_if split: split_if_asm)
    apply (rule vector_diff_chain_at [of "\<lambda>x. 2*x" 2 _ g1, simplified o_def])
    apply (simp add: has_vector_derivative_def has_derivative_def bounded_linear_mult_left)
    using s1
    apply (auto simp: algebra_simps vector_derivative_works)
    done
  have g2: "\<lbrakk>1 < z*2; z \<le> 1; z*2 - 1 \<notin> s2\<rbrakk> \<Longrightarrow>
            vector_derivative (\<lambda>x. if x*2 \<le> 1 then g1 (2*x) else g2 (2*x - 1)) (at z) =
            2 *\<^sub>R vector_derivative g2 (at (z*2 - 1))" for z
    apply (rule vector_derivative_at [OF has_vector_derivative_transform_at [of "\<bar>z - 1/2\<bar>" _ "(\<lambda>x. g2 (2*x - 1))"]])
    apply (simp_all add: dist_real_def abs_if split: split_if_asm)
    apply (rule vector_diff_chain_at [of "\<lambda>x. 2*x - 1" 2 _ g2, simplified o_def])
    apply (simp add: has_vector_derivative_def has_derivative_def bounded_linear_mult_left)
    using s2
    apply (auto simp: algebra_simps vector_derivative_works)
    done
  have "((\<lambda>x. f ((g1 +++ g2) x) * vector_derivative (g1 +++ g2) (at x)) has_integral i1) {0..1/2}"
    apply (rule has_integral_spike_finite [OF _ _ i1, of "insert (1/2) (op*2 -` s1)"])
    using s1
    apply (force intro: finite_vimageI [where h = "op*2"] inj_onI)
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
    apply (rule vector_derivative_at [OF has_vector_derivative_transform_at [of "\<bar>(z-1)/2\<bar>" _ "(\<lambda>x. g1(2*x))"]])
    apply (simp_all add: field_simps dist_real_def abs_if split: split_if_asm)
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
    apply (rule vector_derivative_at [OF has_vector_derivative_transform_at [of "\<bar>z/2\<bar>" _ "(\<lambda>x. g2(2*x-1))"]])
    apply (simp_all add: field_simps dist_real_def abs_if split: split_if_asm)
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


subsection\<open>Shifting the starting point of a (closed) path\<close>

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
    apply (subst Integration.integral_combine)
    using assms * integral_unique by auto
  { fix x
    have "0 \<le> x \<Longrightarrow> x + a < 1 \<Longrightarrow> x \<notin> (\<lambda>x. x - a) ` s \<Longrightarrow>
         vector_derivative (shiftpath a g) (at x) = vector_derivative g (at (x + a))"
      unfolding shiftpath_def
      apply (rule vector_derivative_at [OF has_vector_derivative_transform_at [of "dist(1-a) x" _ "(\<lambda>x. g(a+x))"]])
        apply (auto simp: field_simps dist_real_def abs_if split: split_if_asm)
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
      apply (rule vector_derivative_at [OF has_vector_derivative_transform_at [of "dist (1-a) x" _ "(\<lambda>x. g(a+x-1))"]])
        apply (auto simp: field_simps dist_real_def abs_if split: split_if_asm)
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
             [where s = "{1-a} \<union> (\<lambda>x. x-a) ` s" and f = "\<lambda>x. f(g(a+x)) * vector_derivative g (at(a+x))"])
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
             [where s = "{1-a} \<union> (\<lambda>x. x-a+1) ` s" and f = "\<lambda>x. f(g(a+x-1)) * vector_derivative g (at(a+x-1))"])
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
                      [of "{0<..<1}-s" _ "(shiftpath (1 - a) (shiftpath a g))"]])
      using s g assms x
      apply (auto simp: finite_imp_closed open_Diff shiftpath_shiftpath
                        vector_derivative_within_interior vector_derivative_works [symmetric])
      apply (rule Derivative.differentiable_transform_at [of "min x (1-x)", OF _ _ gx])
      apply (auto simp: dist_real_def shiftpath_shiftpath abs_if)
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

lemma contour_integral_shiftpath:
  assumes "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "contour_integral (shiftpath a g) f = contour_integral g f"
   using assms by (simp add: contour_integral_def has_contour_integral_shiftpath_eq)


subsection\<open>More about straight-line paths\<close>

lemma has_vector_derivative_linepath_within:
    "(linepath a b has_vector_derivative (b - a)) (at x within s)"
apply (simp add: linepath_def has_vector_derivative_def algebra_simps)
apply (rule derivative_eq_intros | simp)+
done

lemma vector_derivative_linepath_within:
    "x \<in> {0..1} \<Longrightarrow> vector_derivative (linepath a b) (at x within {0..1}) = b - a"
  apply (rule vector_derivative_within_closed_interval [of 0 "1::real", simplified])
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
  by (simp add: has_contour_integral vector_derivative_linepath_at)

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

lemma linepath_of_real: "(linepath (of_real a) (of_real b) x) = of_real ((1 - x)*a + x*b)"
  by (simp add: scaleR_conv_of_real linepath_def)

lemma of_real_linepath: "of_real (linepath a b x) = linepath (of_real a) (of_real b) x"
  by (metis linepath_of_real mult.right_neutral of_real_def real_scaleR_def)

lemma has_contour_integral_trivial [iff]: "(f has_contour_integral 0) (linepath a a)"
  by (simp add: has_contour_integral_linepath)

lemma contour_integral_trivial [simp]: "contour_integral (linepath a a) f = 0"
  using has_contour_integral_trivial contour_integral_unique by blast


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
  have "(g o (\<lambda>x. ((v-u) * x + u))) piecewise_C1_differentiable_on {0..1}"
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
  by (simp add: has_contour_integral_subpath_refl contour_integral_unique)

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
    apply (rule_tac s = "(\<lambda>t. ((v-u) *\<^sub>R t + u)) -` s" in has_integral_spike_finite)
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

lemma has_integral_integrable_integral: "(f has_integral i) s \<longleftrightarrow> f integrable_on s \<and> integral s f = i"
  by blast

lemma has_integral_contour_integral_subpath:
  assumes "f contour_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}" "u \<le> v"
    shows "(((\<lambda>x. f(g x) * vector_derivative g (at x)))
            has_integral  contour_integral (subpath u v g) f) {u..v}"
  using assms
  apply (auto simp: has_integral_integrable_integral)
  apply (rule integrable_on_subcbox [where a=u and b=v and s = "{0..1}", simplified])
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
  apply (rule integrable_on_subcbox [where a=u and b=w and s = "{0..1}", simplified])
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
                   valid_path_reversepath valid_path_subpath algebra_simps)
      done
next
  case False
  then show ?thesis
    apply (auto simp: contour_integral_subpath_refl)
    using assms
    by (metis eq_neg_iff_add_eq_0 contour_integrable_subpath contour_integral_reversepath reversepath_subpath valid_path_subpath)
qed

lemma contour_integral_integral:
  shows "contour_integral g f = integral {0..1} (\<lambda>x. f (g x) * vector_derivative g (at x))"
  by (simp add: contour_integral_def integral_def has_contour_integral)


subsection\<open>Segments via convex hulls\<close>

lemma segments_subset_convex_hull:
    "closed_segment a b \<subseteq> (convex hull {a,b,c})"
    "closed_segment a c \<subseteq> (convex hull {a,b,c})"
    "closed_segment b c \<subseteq> (convex hull {a,b,c})"
    "closed_segment b a \<subseteq> (convex hull {a,b,c})"
    "closed_segment c a \<subseteq> (convex hull {a,b,c})"
    "closed_segment c b \<subseteq> (convex hull {a,b,c})"
by (auto simp: segment_convex_hull linepath_of_real  elim!: rev_subsetD [OF _ hull_mono])

lemma midpoints_in_convex_hull:
  assumes "x \<in> convex hull s" "y \<in> convex hull s"
    shows "midpoint x y \<in> convex hull s"
proof -
  have "(1 - inverse(2)) *\<^sub>R x + inverse(2) *\<^sub>R y \<in> convex hull s"
    apply (rule convexD_alt)
    using assms
    apply (auto simp: convex_convex_hull)
    done
  then show ?thesis
    by (simp add: midpoint_def algebra_simps)
qed

lemma convex_hull_subset:
    "s \<subseteq> convex hull t \<Longrightarrow> convex hull s \<subseteq> convex hull t"
  by (simp add: convex_convex_hull subset_hull)

lemma not_in_interior_convex_hull_3:
  fixes a :: "complex"
  shows "a \<notin> interior(convex hull {a,b,c})"
        "b \<notin> interior(convex hull {a,b,c})"
        "c \<notin> interior(convex hull {a,b,c})"
  by (auto simp: card_insert_le_m1 not_in_interior_convex_hull)


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
    apply (metis complex_differentiable_def complex_differentiable_imp_continuous_at continuous_on_eq_continuous_within continuous_on_subset image_subset_iff)
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
    then have fdiff: "(f has_derivative op * (f' (g x))) (at (g x) within g ` {a..b})"
      by (simp add: has_field_derivative_def)
    have "((\<lambda>x. f (g x)) has_vector_derivative f' (g x) * vector_derivative g (at x within {a..b})) (at x within {a..b})"
      using diff_chain_within [OF gdiff fdiff]
      by (simp add: has_vector_derivative_def scaleR_conv_of_real o_def mult_ac)
  } note * = this
  show ?thesis
    apply (rule fundamental_theorem_of_calculus_interior_strong)
    using k assms cfg *
    apply (auto simp: at_within_closed_interval)
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
  have "continuous_on {0..1} ((\<lambda>x. f x * (b - a)) o linepath a b)"
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
  by (simp add: continuous_on_const contour_integrable_continuous_linepath)

lemma contour_integrable_on_id [iff]: "(\<lambda>x. x) contour_integrable_on (linepath a b)"
  by (simp add: continuous_on_id contour_integrable_continuous_linepath)


subsection\<open>Arithmetical combining theorems\<close>

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
  by (simp add: has_integral_sub has_contour_integral_def algebra_simps)

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

lemma has_contour_integral_setsum:
    "\<lbrakk>finite s; \<And>a. a \<in> s \<Longrightarrow> (f a has_contour_integral i a) p\<rbrakk>
     \<Longrightarrow> ((\<lambda>x. setsum (\<lambda>a. f a x) s) has_contour_integral setsum i s) p"
  by (induction s rule: finite_induct) (auto simp: has_contour_integral_0 has_contour_integral_add)


subsection \<open>Operations on path integrals\<close>

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
  by (simp add: contour_integral_def) (metis has_contour_integral_eq)

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

lemma contour_integral_0: "contour_integral g (\<lambda>x. 0) = 0"
  by (simp add: contour_integral_unique has_contour_integral_0)

lemma contour_integral_setsum:
    "\<lbrakk>finite s; \<And>a. a \<in> s \<Longrightarrow> (f a) contour_integrable_on p\<rbrakk>
     \<Longrightarrow> contour_integral p (\<lambda>x. setsum (\<lambda>a. f a x) s) = setsum (\<lambda>a. contour_integral p (f a)) s"
  by (auto simp: contour_integral_unique has_contour_integral_setsum has_contour_integral_integral)

lemma contour_integrable_eq:
    "\<lbrakk>f contour_integrable_on p; \<And>x. x \<in> path_image p \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> g contour_integrable_on p"
  unfolding contour_integrable_on_def
  by (metis has_contour_integral_eq)


subsection \<open>Arithmetic theorems for path integrability\<close>

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

lemma contour_integrable_setsum:
    "\<lbrakk>finite s; \<And>a. a \<in> s \<Longrightarrow> (f a) contour_integrable_on p\<rbrakk>
     \<Longrightarrow> (\<lambda>x. setsum (\<lambda>a. f a x) s) contour_integrable_on p"
   unfolding contour_integrable_on_def
   by (metis has_contour_integral_setsum)


subsection\<open>Reversing a path integral\<close>

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
    using assms
    apply auto
    apply (metis add.left_neutral has_contour_integral_trivial has_contour_integral_unique)
    apply (metis add.right_neutral has_contour_integral_trivial has_contour_integral_unique)
    done
next
  case False
  then have k: "0 < k" "k < 1" "complex_of_real k \<noteq> 1"
    using assms apply auto
    using of_real_eq_iff by fastforce
  have c': "c = k *\<^sub>R (b - a) + a"
    by (metis diff_add_cancel c)
  have bc: "(b - c) = (1 - k) *\<^sub>R (b - a)"
    by (simp add: algebra_simps c')
  { assume *: "((\<lambda>x. f ((1 - x) *\<^sub>R a + x *\<^sub>R c) * (c - a)) has_integral i) {0..1}"
    have **: "\<And>x. ((k - x) / k) *\<^sub>R a + (x / k) *\<^sub>R c = (1 - x) *\<^sub>R a + x *\<^sub>R b"
      using False
      apply (simp add: c' algebra_simps)
      apply (simp add: real_vector.scale_left_distrib [symmetric] divide_simps)
      done
    have "((\<lambda>x. f ((1 - x) *\<^sub>R a + x *\<^sub>R b) * (b - a)) has_integral i) {0..k}"
      using * k
      apply -
      apply (drule has_integral_affinity [of _ _ 0 "1::real" "inverse k" "0", simplified])
      apply (simp_all add: divide_simps mult.commute [of _ "k"] image_affinity_atLeastAtMost ** c)
      apply (drule Integration.has_integral_cmul [where c = "inverse k"])
      apply (simp add: Integration.has_integral_cmul)
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
      using * k
      apply -
      apply (drule has_integral_affinity [of _ _ 0 "1::real" "inverse(1 - k)" "-(k/(1 - k))", simplified])
      apply (simp_all add: divide_simps mult.commute [of _ "1-k"] image_affinity_atLeastAtMost ** bc)
      apply (drule Integration.has_integral_cmul [where k = "(1 - k) *\<^sub>R j" and c = "inverse (1 - k)"])
      apply (simp add: Integration.has_integral_cmul)
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
  show "continuous_on (closed_segment a c) f"
    apply (rule continuous_on_subset [OF f])
    apply (simp add: segment_convex_hull)
    apply (rule convex_hull_subset)
    using assms
    apply (auto simp: hull_inc c' Convex.convexD_alt)
    done
qed

lemma contour_integral_split:
  assumes f: "continuous_on (closed_segment a b) f"
      and k: "0 \<le> k" "k \<le> 1"
      and c: "c - a = k *\<^sub>R (b - a)"
    shows "contour_integral(linepath a b) f = contour_integral(linepath a c) f + contour_integral(linepath c b) f"
proof -
  have c': "c = (1 - k) *\<^sub>R a + k *\<^sub>R b"
    using c by (simp add: algebra_simps)
  have *: "continuous_on (closed_segment a c) f" "continuous_on (closed_segment c b) f"
    apply (rule_tac [!] continuous_on_subset [OF f])
    apply (simp_all add: segment_convex_hull)
    apply (rule_tac [!] convex_hull_subset)
    using assms
    apply (auto simp: hull_inc c' Convex.convexD_alt)
    done
  show ?thesis
    apply (rule contour_integral_unique)
    apply (rule has_contour_integral_split [OF has_contour_integral_integral has_contour_integral_integral k c])
    apply (rule contour_integrable_continuous_linepath *)+
    done
qed

lemma contour_integral_split_linepath:
  assumes f: "continuous_on (closed_segment a b) f"
      and c: "c \<in> closed_segment a b"
    shows "contour_integral(linepath a b) f = contour_integral(linepath a c) f + contour_integral(linepath c b) f"
  using c
  by (auto simp: closed_segment_def algebra_simps intro!: contour_integral_split [OF f])

(* The special case of midpoints used in the main quadrisection.*)

lemma has_contour_integral_midpoint:
  assumes "(f has_contour_integral i) (linepath a (midpoint a b))"
          "(f has_contour_integral j) (linepath (midpoint a b) b)"
    shows "(f has_contour_integral (i + j)) (linepath a b)"
  apply (rule has_contour_integral_split [where c = "midpoint a b" and k = "1/2"])
  using assms
  apply (auto simp: midpoint_def algebra_simps scaleR_conv_of_real)
  done

lemma contour_integral_midpoint:
   "continuous_on (closed_segment a b) f
    \<Longrightarrow> contour_integral (linepath a b) f =
        contour_integral (linepath a (midpoint a b)) f + contour_integral (linepath (midpoint a b) b) f"
  apply (rule contour_integral_split [where c = "midpoint a b" and k = "1/2"])
  using assms
  apply (auto simp: midpoint_def algebra_simps scaleR_conv_of_real)
  done


text\<open>A couple of special case lemmas that are useful below\<close>

lemma triangle_linear_has_chain_integral:
    "((\<lambda>x. m*x + d) has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
  apply (rule Cauchy_theorem_primitive [of UNIV "\<lambda>x. m/2 * x^2 + d*x"])
  apply (auto intro!: derivative_eq_intros)
  done

lemma has_chain_integral_chain_integral3:
     "(f has_contour_integral i) (linepath a b +++ linepath b c +++ linepath c d)
      \<Longrightarrow> contour_integral (linepath a b) f + contour_integral (linepath b c) f + contour_integral (linepath c d) f = i"
  apply (subst contour_integral_unique [symmetric], assumption)
  apply (drule has_contour_integral_integrable)
  apply (simp add: valid_path_join)
  done

subsection\<open>Reversing the order in a double path integral\<close>

text\<open>The condition is stronger than needed but it's often true in typical situations\<close>

lemma fst_im_cbox [simp]: "cbox c d \<noteq> {} \<Longrightarrow> (fst ` cbox (a,c) (b,d)) = cbox a b"
  by (auto simp: cbox_Pair_eq)

lemma snd_im_cbox [simp]: "cbox a b \<noteq> {} \<Longrightarrow> (snd ` cbox (a,c) (b,d)) = cbox c d"
  by (auto simp: cbox_Pair_eq)

lemma contour_integral_swap:
  assumes fcon:  "continuous_on (path_image g \<times> path_image h) (\<lambda>(y1,y2). f y1 y2)"
      and vp:    "valid_path g" "valid_path h"
      and gvcon: "continuous_on {0..1} (\<lambda>t. vector_derivative g (at t))"
      and hvcon: "continuous_on {0..1} (\<lambda>t. vector_derivative h (at t))"
  shows "contour_integral g (\<lambda>w. contour_integral h (f w)) =
         contour_integral h (\<lambda>z. contour_integral g (\<lambda>w. f w z))"
proof -
  have gcon: "continuous_on {0..1} g" and hcon: "continuous_on {0..1} h"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def)
  have fgh1: "\<And>x. (\<lambda>t. f (g x) (h t)) = (\<lambda>(y1,y2). f y1 y2) o (\<lambda>t. (g x, h t))"
    by (rule ext) simp
  have fgh2: "\<And>x. (\<lambda>t. f (g t) (h x)) = (\<lambda>(y1,y2). f y1 y2) o (\<lambda>t. (g t, h x))"
    by (rule ext) simp
  have fcon_im1: "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> continuous_on ((\<lambda>t. (g x, h t)) ` {0..1}) (\<lambda>(x, y). f x y)"
    by (rule continuous_on_subset [OF fcon]) (auto simp: path_image_def)
  have fcon_im2: "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> continuous_on ((\<lambda>t. (g t, h x)) ` {0..1}) (\<lambda>(x, y). f x y)"
    by (rule continuous_on_subset [OF fcon]) (auto simp: path_image_def)
  have vdg: "\<And>y. y \<in> {0..1} \<Longrightarrow> (\<lambda>x. f (g x) (h y) * vector_derivative g (at x)) integrable_on {0..1}"
    apply (rule integrable_continuous_real)
    apply (rule continuous_on_mult [OF _ gvcon])
    apply (subst fgh2)
    apply (rule fcon_im2 gcon continuous_intros | simp)+
    done
  have "(\<lambda>z. vector_derivative g (at (fst z))) = (\<lambda>x. vector_derivative g (at x)) o fst"
    by auto
  then have gvcon': "continuous_on (cbox (0, 0) (1, 1::real)) (\<lambda>x. vector_derivative g (at (fst x)))"
    apply (rule ssubst)
    apply (rule continuous_intros | simp add: gvcon)+
    done
  have "(\<lambda>z. vector_derivative h (at (snd z))) = (\<lambda>x. vector_derivative h (at x)) o snd"
    by auto
  then have hvcon': "continuous_on (cbox (0, 0) (1::real, 1)) (\<lambda>x. vector_derivative h (at (snd x)))"
    apply (rule ssubst)
    apply (rule continuous_intros | simp add: hvcon)+
    done
  have "(\<lambda>x. f (g (fst x)) (h (snd x))) = (\<lambda>(y1,y2). f y1 y2) o (\<lambda>w. ((g o fst) w, (h o snd) w))"
    by auto
  then have fgh: "continuous_on (cbox (0, 0) (1, 1)) (\<lambda>x. f (g (fst x)) (h (snd x)))"
    apply (rule ssubst)
    apply (rule gcon hcon continuous_intros | simp)+
    apply (auto simp: path_image_def intro: continuous_on_subset [OF fcon])
    done
  have "integral {0..1} (\<lambda>x. contour_integral h (f (g x)) * vector_derivative g (at x)) =
        integral {0..1} (\<lambda>x. contour_integral h (\<lambda>y. f (g x) y * vector_derivative g (at x)))"
    apply (rule integral_cong [OF contour_integral_rmul [symmetric]])
    apply (clarsimp simp: contour_integrable_on)
    apply (rule integrable_continuous_real)
    apply (rule continuous_on_mult [OF _ hvcon])
    apply (subst fgh1)
    apply (rule fcon_im1 hcon continuous_intros | simp)+
    done
  also have "... = integral {0..1}
                     (\<lambda>y. contour_integral g (\<lambda>x. f x (h y) * vector_derivative h (at y)))"
    apply (simp add: contour_integral_integral)
    apply (subst integral_swap_continuous [where 'a = real and 'b = real, of 0 0 1 1, simplified])
    apply (rule fgh gvcon' hvcon' continuous_intros | simp add: split_def)+
    apply (simp add: algebra_simps)
    done
  also have "... = contour_integral h (\<lambda>z. contour_integral g (\<lambda>w. f w z))"
    apply (simp add: contour_integral_integral)
    apply (rule integral_cong)
    apply (subst integral_mult_left [symmetric])
    apply (blast intro: vdg)
    apply (simp add: algebra_simps)
    done
  finally show ?thesis
    by (simp add: contour_integral_integral)
qed


subsection\<open>The key quadrisection step\<close>

lemma norm_sum_half:
  assumes "norm(a + b) >= e"
    shows "norm a >= e/2 \<or> norm b >= e/2"
proof -
  have "e \<le> norm (- a - b)"
    by (simp add: add.commute assms norm_minus_commute)
  thus ?thesis
    using norm_triangle_ineq4 order_trans by fastforce
qed

lemma norm_sum_lemma:
  assumes "e \<le> norm (a + b + c + d)"
    shows "e / 4 \<le> norm a \<or> e / 4 \<le> norm b \<or> e / 4 \<le> norm c \<or> e / 4 \<le> norm d"
proof -
  have "e \<le> norm ((a + b) + (c + d))" using assms
    by (simp add: algebra_simps)
  then show ?thesis
    by (auto dest!: norm_sum_half)
qed

lemma Cauchy_theorem_quadrisection:
  assumes f: "continuous_on (convex hull {a,b,c}) f"
      and dist: "dist a b \<le> K" "dist b c \<le> K" "dist c a \<le> K"
      and e: "e * K^2 \<le>
              norm (contour_integral(linepath a b) f + contour_integral(linepath b c) f + contour_integral(linepath c a) f)"
  shows "\<exists>a' b' c'.
           a' \<in> convex hull {a,b,c} \<and> b' \<in> convex hull {a,b,c} \<and> c' \<in> convex hull {a,b,c} \<and>
           dist a' b' \<le> K/2  \<and>  dist b' c' \<le> K/2  \<and>  dist c' a' \<le> K/2  \<and>
           e * (K/2)^2 \<le> norm(contour_integral(linepath a' b') f + contour_integral(linepath b' c') f + contour_integral(linepath c' a') f)"
proof -
  note divide_le_eq_numeral1 [simp del]
  def a' \<equiv> "midpoint b c"
  def b' \<equiv> "midpoint c a"
  def c' \<equiv> "midpoint a b"
  have fabc: "continuous_on (closed_segment a b) f" "continuous_on (closed_segment b c) f" "continuous_on (closed_segment c a) f"
    using f continuous_on_subset segments_subset_convex_hull by metis+
  have fcont': "continuous_on (closed_segment c' b') f"
               "continuous_on (closed_segment a' c') f"
               "continuous_on (closed_segment b' a') f"
    unfolding a'_def b'_def c'_def
    apply (rule continuous_on_subset [OF f],
           metis midpoints_in_convex_hull convex_hull_subset hull_subset insert_subset segment_convex_hull)+
    done
  let ?pathint = "\<lambda>x y. contour_integral(linepath x y) f"
  have *: "?pathint a b + ?pathint b c + ?pathint c a =
          (?pathint a c' + ?pathint c' b' + ?pathint b' a) +
          (?pathint a' c' + ?pathint c' b + ?pathint b a') +
          (?pathint a' c + ?pathint c b' + ?pathint b' a') +
          (?pathint a' b' + ?pathint b' c' + ?pathint c' a')"
    apply (simp add: fcont' contour_integral_reverse_linepath)
    apply (simp add: a'_def b'_def c'_def contour_integral_midpoint fabc)
    done
  have [simp]: "\<And>x y. cmod (x * 2 - y * 2) = cmod (x - y) * 2"
    by (metis left_diff_distrib mult.commute norm_mult_numeral1)
  have [simp]: "\<And>x y. cmod (x - y) = cmod (y - x)"
    by (simp add: norm_minus_commute)
  consider "e * K\<^sup>2 / 4 \<le> cmod (?pathint a c' + ?pathint c' b' + ?pathint b' a)" |
           "e * K\<^sup>2 / 4 \<le> cmod (?pathint a' c' + ?pathint c' b + ?pathint b a')" |
           "e * K\<^sup>2 / 4 \<le> cmod (?pathint a' c + ?pathint c b' + ?pathint b' a')" |
           "e * K\<^sup>2 / 4 \<le> cmod (?pathint a' b' + ?pathint b' c' + ?pathint c' a')"
    using assms
    apply (simp only: *)
    apply (blast intro: that dest!: norm_sum_lemma)
    done
  then show ?thesis
  proof cases
    case 1 then show ?thesis
      apply (rule_tac x=a in exI)
      apply (rule exI [where x=c'])
      apply (rule exI [where x=b'])
      using assms
      apply (auto simp: a'_def c'_def b'_def midpoints_in_convex_hull hull_subset [THEN subsetD])
      apply (auto simp: midpoint_def dist_norm scaleR_conv_of_real divide_simps)
      done
  next
    case 2 then show ?thesis
      apply (rule_tac x=a' in exI)
      apply (rule exI [where x=c'])
      apply (rule exI [where x=b])
      using assms
      apply (auto simp: a'_def c'_def b'_def midpoints_in_convex_hull hull_subset [THEN subsetD])
      apply (auto simp: midpoint_def dist_norm scaleR_conv_of_real divide_simps)
      done
  next
    case 3 then show ?thesis
      apply (rule_tac x=a' in exI)
      apply (rule exI [where x=c])
      apply (rule exI [where x=b'])
      using assms
      apply (auto simp: a'_def c'_def b'_def midpoints_in_convex_hull hull_subset [THEN subsetD])
      apply (auto simp: midpoint_def dist_norm scaleR_conv_of_real divide_simps)
      done
  next
    case 4 then show ?thesis
      apply (rule_tac x=a' in exI)
      apply (rule exI [where x=b'])
      apply (rule exI [where x=c'])
      using assms
      apply (auto simp: a'_def c'_def b'_def midpoints_in_convex_hull hull_subset [THEN subsetD])
      apply (auto simp: midpoint_def dist_norm scaleR_conv_of_real divide_simps)
      done
  qed
qed

subsection\<open>Cauchy's theorem for triangles\<close>

lemma triangle_points_closer:
  fixes a::complex
  shows "\<lbrakk>x \<in> convex hull {a,b,c};  y \<in> convex hull {a,b,c}\<rbrakk>
         \<Longrightarrow> norm(x - y) \<le> norm(a - b) \<or>
             norm(x - y) \<le> norm(b - c) \<or>
             norm(x - y) \<le> norm(c - a)"
  using simplex_extremal_le [of "{a,b,c}"]
  by (auto simp: norm_minus_commute)

lemma holomorphic_point_small_triangle:
  assumes x: "x \<in> s"
      and f: "continuous_on s f"
      and cd: "f complex_differentiable (at x within s)"
      and e: "0 < e"
    shows "\<exists>k>0. \<forall>a b c. dist a b \<le> k \<and> dist b c \<le> k \<and> dist c a \<le> k \<and>
              x \<in> convex hull {a,b,c} \<and> convex hull {a,b,c} \<subseteq> s
              \<longrightarrow> norm(contour_integral(linepath a b) f + contour_integral(linepath b c) f +
                       contour_integral(linepath c a) f)
                  \<le> e*(dist a b + dist b c + dist c a)^2"
           (is "\<exists>k>0. \<forall>a b c. _ \<longrightarrow> ?normle a b c")
proof -
  have le_of_3: "\<And>a x y z. \<lbrakk>0 \<le> x*y; 0 \<le> x*z; 0 \<le> y*z; a \<le> (e*(x + y + z))*x + (e*(x + y + z))*y + (e*(x + y + z))*z\<rbrakk>
                     \<Longrightarrow> a \<le> e*(x + y + z)^2"
    by (simp add: algebra_simps power2_eq_square)
  have disj_le: "\<lbrakk>x \<le> a \<or> x \<le> b \<or> x \<le> c; 0 \<le> a; 0 \<le> b; 0 \<le> c\<rbrakk> \<Longrightarrow> x \<le> a + b + c"
             for x::real and a b c
    by linarith
  have fabc: "f contour_integrable_on linepath a b" "f contour_integrable_on linepath b c" "f contour_integrable_on linepath c a"
              if "convex hull {a, b, c} \<subseteq> s" for a b c
    using segments_subset_convex_hull that
    by (metis continuous_on_subset f contour_integrable_continuous_linepath)+
  note path_bound = has_contour_integral_bound_linepath [simplified norm_minus_commute, OF has_contour_integral_integral]
  { fix f' a b c d
    assume d: "0 < d"
       and f': "\<And>y. \<lbrakk>cmod (y - x) \<le> d; y \<in> s\<rbrakk> \<Longrightarrow> cmod (f y - f x - f' * (y - x)) \<le> e * cmod (y - x)"
       and le: "cmod (a - b) \<le> d" "cmod (b - c) \<le> d" "cmod (c - a) \<le> d"
       and xc: "x \<in> convex hull {a, b, c}"
       and s: "convex hull {a, b, c} \<subseteq> s"
    have pa: "contour_integral (linepath a b) f + contour_integral (linepath b c) f + contour_integral (linepath c a) f =
              contour_integral (linepath a b) (\<lambda>y. f y - f x - f'*(y - x)) +
              contour_integral (linepath b c) (\<lambda>y. f y - f x - f'*(y - x)) +
              contour_integral (linepath c a) (\<lambda>y. f y - f x - f'*(y - x))"
      apply (simp add: contour_integral_diff contour_integral_lmul contour_integrable_lmul contour_integrable_diff fabc [OF s])
      apply (simp add: field_simps)
      done
    { fix y
      assume yc: "y \<in> convex hull {a,b,c}"
      have "cmod (f y - f x - f' * (y - x)) \<le> e*norm(y - x)"
        apply (rule f')
        apply (metis triangle_points_closer [OF xc yc] le norm_minus_commute order_trans)
        using s yc by blast
      also have "... \<le> e * (cmod (a - b) + cmod (b - c) + cmod (c - a))"
        by (simp add: yc e xc disj_le [OF triangle_points_closer])
      finally have "cmod (f y - f x - f' * (y - x)) \<le> e * (cmod (a - b) + cmod (b - c) + cmod (c - a))" .
    } note cm_le = this
    have "?normle a b c"
      apply (simp add: dist_norm pa)
      apply (rule le_of_3)
      using f' xc s e
      apply simp_all
      apply (intro norm_triangle_le add_mono path_bound)
      apply (simp_all add: contour_integral_diff contour_integral_lmul contour_integrable_lmul contour_integrable_diff fabc)
      apply (blast intro: cm_le elim: dest: segments_subset_convex_hull [THEN subsetD])+
      done
  } note * = this
  show ?thesis
    using cd e
    apply (simp add: complex_differentiable_def has_field_derivative_def has_derivative_within_alt approachable_lt_le2 Ball_def)
    apply (clarify dest!: spec mp)
    using *
    apply (simp add: dist_norm, blast)
    done
qed


(* Hence the most basic theorem for a triangle.*)
locale Chain =
  fixes x0 At Follows
  assumes At0: "At x0 0"
      and AtSuc: "\<And>x n. At x n \<Longrightarrow> \<exists>x'. At x' (Suc n) \<and> Follows x' x"
begin
  primrec f where
    "f 0 = x0"
  | "f (Suc n) = (SOME x. At x (Suc n) \<and> Follows x (f n))"

  lemma At: "At (f n) n"
  proof (induct n)
    case 0 show ?case
      by (simp add: At0)
  next
    case (Suc n) show ?case
      by (metis (no_types, lifting) AtSuc [OF Suc] f.simps(2) someI_ex)
  qed

  lemma Follows: "Follows (f(Suc n)) (f n)"
    by (metis (no_types, lifting) AtSuc [OF At [of n]] f.simps(2) someI_ex)

  declare f.simps(2) [simp del]
end

lemma Chain3:
  assumes At0: "At x0 y0 z0 0"
      and AtSuc: "\<And>x y z n. At x y z n \<Longrightarrow> \<exists>x' y' z'. At x' y' z' (Suc n) \<and> Follows x' y' z' x y z"
  obtains f g h where
    "f 0 = x0" "g 0 = y0" "h 0 = z0"
                      "\<And>n. At (f n) (g n) (h n) n"
                       "\<And>n. Follows (f(Suc n)) (g(Suc n)) (h(Suc n)) (f n) (g n) (h n)"
proof -
  interpret three: Chain "(x0,y0,z0)" "\<lambda>(x,y,z). At x y z" "\<lambda>(x',y',z'). \<lambda>(x,y,z). Follows x' y' z' x y z"
    apply unfold_locales
    using At0 AtSuc by auto
  show ?thesis
  apply (rule that [of "\<lambda>n. fst (three.f n)"  "\<lambda>n. fst (snd (three.f n))" "\<lambda>n. snd (snd (three.f n))"])
  apply simp_all
  using three.At three.Follows
  apply (simp_all add: split_beta')
  done
qed

lemma Cauchy_theorem_triangle:
  assumes "f holomorphic_on (convex hull {a,b,c})"
    shows "(f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
proof -
  have contf: "continuous_on (convex hull {a,b,c}) f"
    by (metis assms holomorphic_on_imp_continuous_on)
  let ?pathint = "\<lambda>x y. contour_integral(linepath x y) f"
  { fix y::complex
    assume fy: "(f has_contour_integral y) (linepath a b +++ linepath b c +++ linepath c a)"
       and ynz: "y \<noteq> 0"
    def K \<equiv> "1 + max (dist a b) (max (dist b c) (dist c a))"
    def e \<equiv> "norm y / K^2"
    have K1: "K \<ge> 1"  by (simp add: K_def max.coboundedI1)
    then have K: "K > 0" by linarith
    have [iff]: "dist a b \<le> K" "dist b c \<le> K" "dist c a \<le> K"
      by (simp_all add: K_def)
    have e: "e > 0"
      unfolding e_def using ynz K1 by simp
    def At \<equiv> "\<lambda>x y z n. convex hull {x,y,z} \<subseteq> convex hull {a,b,c} \<and>
                         dist x y \<le> K/2^n \<and> dist y z \<le> K/2^n \<and> dist z x \<le> K/2^n \<and>
                         norm(?pathint x y + ?pathint y z + ?pathint z x) \<ge> e*(K/2^n)^2"
    have At0: "At a b c 0"
      using fy
      by (simp add: At_def e_def has_chain_integral_chain_integral3)
    { fix x y z n
      assume At: "At x y z n"
      then have contf': "continuous_on (convex hull {x,y,z}) f"
        using contf At_def continuous_on_subset by blast
      have "\<exists>x' y' z'. At x' y' z' (Suc n) \<and> convex hull {x',y',z'} \<subseteq> convex hull {x,y,z}"
        using At
        apply (simp add: At_def)
        using  Cauchy_theorem_quadrisection [OF contf', of "K/2^n" e]
        apply clarsimp
        apply (rule_tac x="a'" in exI)
        apply (rule_tac x="b'" in exI)
        apply (rule_tac x="c'" in exI)
        apply (simp add: algebra_simps)
        apply (meson convex_hull_subset empty_subsetI insert_subset subsetCE)
        done
    } note AtSuc = this
    obtain fa fb fc
      where f0 [simp]: "fa 0 = a" "fb 0 = b" "fc 0 = c"
        and cosb: "\<And>n. convex hull {fa n, fb n, fc n} \<subseteq> convex hull {a,b,c}"
        and dist: "\<And>n. dist (fa n) (fb n) \<le> K/2^n"
                  "\<And>n. dist (fb n) (fc n) \<le> K/2^n"
                  "\<And>n. dist (fc n) (fa n) \<le> K/2^n"
        and no: "\<And>n. norm(?pathint (fa n) (fb n) +
                           ?pathint (fb n) (fc n) +
                           ?pathint (fc n) (fa n)) \<ge> e * (K/2^n)^2"
        and conv_le: "\<And>n. convex hull {fa(Suc n), fb(Suc n), fc(Suc n)} \<subseteq> convex hull {fa n, fb n, fc n}"
      apply (rule Chain3 [of At, OF At0 AtSuc])
      apply (auto simp: At_def)
      done
    have "\<exists>x. \<forall>n. x \<in> convex hull {fa n, fb n, fc n}"
      apply (rule bounded_closed_nest)
      apply (simp_all add: compact_imp_closed finite_imp_compact_convex_hull finite_imp_bounded_convex_hull)
      apply (rule allI)
      apply (rule transitive_stepwise_le)
      apply (auto simp: conv_le)
      done
    then obtain x where x: "\<And>n. x \<in> convex hull {fa n, fb n, fc n}" by auto
    then have xin: "x \<in> convex hull {a,b,c}"
      using assms f0 by blast
    then have fx: "f complex_differentiable at x within (convex hull {a,b,c})"
      using assms holomorphic_on_def by blast
    { fix k n
      assume k: "0 < k"
         and le:
            "\<And>x' y' z'.
               \<lbrakk>dist x' y' \<le> k; dist y' z' \<le> k; dist z' x' \<le> k;
                x \<in> convex hull {x',y',z'};
                convex hull {x',y',z'} \<subseteq> convex hull {a,b,c}\<rbrakk>
               \<Longrightarrow>
               cmod (?pathint x' y' + ?pathint y' z' + ?pathint z' x') * 10
                     \<le> e * (dist x' y' + dist y' z' + dist z' x')\<^sup>2"
         and Kk: "K / k < 2 ^ n"
      have "K / 2 ^ n < k" using Kk k
        by (auto simp: field_simps)
      then have DD: "dist (fa n) (fb n) \<le> k" "dist (fb n) (fc n) \<le> k" "dist (fc n) (fa n) \<le> k"
        using dist [of n]  k
        by linarith+
      have dle: "(dist (fa n) (fb n) + dist (fb n) (fc n) + dist (fc n) (fa n))\<^sup>2
               \<le> (3 * K / 2 ^ n)\<^sup>2"
        using dist [of n] e K
        by (simp add: abs_le_square_iff [symmetric])
      have less10: "\<And>x y::real. 0 < x \<Longrightarrow> y \<le> 9*x \<Longrightarrow> y < x*10"
        by linarith
      have "e * (dist (fa n) (fb n) + dist (fb n) (fc n) + dist (fc n) (fa n))\<^sup>2 \<le> e * (3 * K / 2 ^ n)\<^sup>2"
        using ynz dle e mult_le_cancel_left_pos by blast
      also have "... <
          cmod (?pathint (fa n) (fb n) + ?pathint (fb n) (fc n) + ?pathint (fc n) (fa n)) * 10"
        using no [of n] e K
        apply (simp add: e_def field_simps)
        apply (simp only: zero_less_norm_iff [symmetric])
        done
      finally have False
        using le [OF DD x cosb] by auto
    } then
    have ?thesis
      using holomorphic_point_small_triangle [OF xin contf fx, of "e/10"] e
      apply clarsimp
      apply (rule_tac x1="K/k" in exE [OF real_arch_pow2], blast)
      done
  }
  moreover have "f contour_integrable_on (linepath a b +++ linepath b c +++ linepath c a)"
    by simp (meson contf continuous_on_subset contour_integrable_continuous_linepath segments_subset_convex_hull(1)
                   segments_subset_convex_hull(3) segments_subset_convex_hull(5))
  ultimately show ?thesis
    using has_contour_integral_integral by fastforce
qed


subsection\<open>Version needing function holomorphic in interior only\<close>

lemma Cauchy_theorem_flat_lemma:
  assumes f: "continuous_on (convex hull {a,b,c}) f"
      and c: "c - a = k *\<^sub>R (b - a)"
      and k: "0 \<le> k"
    shows "contour_integral (linepath a b) f + contour_integral (linepath b c) f +
          contour_integral (linepath c a) f = 0"
proof -
  have fabc: "continuous_on (closed_segment a b) f" "continuous_on (closed_segment b c) f" "continuous_on (closed_segment c a) f"
    using f continuous_on_subset segments_subset_convex_hull by metis+
  show ?thesis
  proof (cases "k \<le> 1")
    case True show ?thesis
      by (simp add: contour_integral_split [OF fabc(1) k True c] contour_integral_reverse_linepath fabc)
  next
    case False then show ?thesis
      using fabc c
      apply (subst contour_integral_split [of a c f "1/k" b, symmetric])
      apply (metis closed_segment_commute fabc(3))
      apply (auto simp: k contour_integral_reverse_linepath)
      done
  qed
qed

lemma Cauchy_theorem_flat:
  assumes f: "continuous_on (convex hull {a,b,c}) f"
      and c: "c - a = k *\<^sub>R (b - a)"
    shows "contour_integral (linepath a b) f +
           contour_integral (linepath b c) f +
           contour_integral (linepath c a) f = 0"
proof (cases "0 \<le> k")
  case True with assms show ?thesis
    by (blast intro: Cauchy_theorem_flat_lemma)
next
  case False
  have "continuous_on (closed_segment a b) f" "continuous_on (closed_segment b c) f" "continuous_on (closed_segment c a) f"
    using f continuous_on_subset segments_subset_convex_hull by metis+
  moreover have "contour_integral (linepath b a) f + contour_integral (linepath a c) f +
        contour_integral (linepath c b) f = 0"
    apply (rule Cauchy_theorem_flat_lemma [of b a c f "1-k"])
    using False c
    apply (auto simp: f insert_commute scaleR_conv_of_real algebra_simps)
    done
  ultimately show ?thesis
    apply (auto simp: contour_integral_reverse_linepath)
    using add_eq_0_iff by force
qed


lemma Cauchy_theorem_triangle_interior:
  assumes contf: "continuous_on (convex hull {a,b,c}) f"
      and holf:  "f holomorphic_on interior (convex hull {a,b,c})"
     shows "(f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
proof -
  have fabc: "continuous_on (closed_segment a b) f" "continuous_on (closed_segment b c) f" "continuous_on (closed_segment c a) f"
    using contf continuous_on_subset segments_subset_convex_hull by metis+
  have "bounded (f ` (convex hull {a,b,c}))"
    by (simp add: compact_continuous_image compact_convex_hull compact_imp_bounded contf)
  then obtain B where "0 < B" and Bnf: "\<And>x. x \<in> convex hull {a,b,c} \<Longrightarrow> norm (f x) \<le> B"
     by (auto simp: dest!: bounded_pos [THEN iffD1])
  have "bounded (convex hull {a,b,c})"
    by (simp add: bounded_convex_hull)
  then obtain C where C: "0 < C" and Cno: "\<And>y. y \<in> convex hull {a,b,c} \<Longrightarrow> norm y < C"
    using bounded_pos_less by blast
  then have diff_2C: "norm(x - y) \<le> 2*C"
           if x: "x \<in> convex hull {a, b, c}" and y: "y \<in> convex hull {a, b, c}" for x y
  proof -
    have "cmod x \<le> C"
      using x by (meson Cno not_le not_less_iff_gr_or_eq)
    hence "cmod (x - y) \<le> C + C"
      using y by (meson Cno add_mono_thms_linordered_field(4) less_eq_real_def norm_triangle_ineq4 order_trans)
    thus "cmod (x - y) \<le> 2 * C"
      by (metis mult_2)
  qed
  have contf': "continuous_on (convex hull {b,a,c}) f"
    using contf by (simp add: insert_commute)
  { fix y::complex
    assume fy: "(f has_contour_integral y) (linepath a b +++ linepath b c +++ linepath c a)"
       and ynz: "y \<noteq> 0"
    have pi_eq_y: "contour_integral (linepath a b) f + contour_integral (linepath b c) f + contour_integral (linepath c a) f = y"
      by (rule has_chain_integral_chain_integral3 [OF fy])
    have ?thesis
    proof (cases "c=a \<or> a=b \<or> b=c")
      case True then show ?thesis
        using Cauchy_theorem_flat [OF contf, of 0]
        using has_chain_integral_chain_integral3 [OF fy] ynz
        by (force simp: fabc contour_integral_reverse_linepath)
    next
      case False
      then have car3: "card {a, b, c} = Suc (DIM(complex))"
        by auto
      { assume "interior(convex hull {a,b,c}) = {}"
        then have "collinear{a,b,c}"
          using interior_convex_hull_eq_empty [OF car3]
          by (simp add: collinear_3_eq_affine_dependent)
        then have "False"
          using False
          apply (clarsimp simp add: collinear_3 collinear_lemma)
          apply (drule Cauchy_theorem_flat [OF contf'])
          using pi_eq_y ynz
          apply (simp add: fabc add_eq_0_iff contour_integral_reverse_linepath)
          done
      }
      then obtain d where d: "d \<in> interior (convex hull {a, b, c})"
        by blast
      { fix d1
        assume d1_pos: "0 < d1"
           and d1: "\<And>x x'. \<lbrakk>x\<in>convex hull {a, b, c}; x'\<in>convex hull {a, b, c}; cmod (x' - x) < d1\<rbrakk>
                           \<Longrightarrow> cmod (f x' - f x) < cmod y / (24 * C)"
        def e      \<equiv> "min 1 (min (d1/(4*C)) ((norm y / 24 / C) / B))"
        def shrink \<equiv> "\<lambda>x. x - e *\<^sub>R (x - d)"
        let ?pathint = "\<lambda>x y. contour_integral(linepath x y) f"
        have e: "0 < e" "e \<le> 1" "e \<le> d1 / (4 * C)" "e \<le> cmod y / 24 / C / B"
          using d1_pos \<open>C>0\<close> \<open>B>0\<close> ynz by (simp_all add: e_def)
        then have eCB: "24 * e * C * B \<le> cmod y"
          using \<open>C>0\<close> \<open>B>0\<close>  by (simp add: field_simps)
        have e_le_d1: "e * (4 * C) \<le> d1"
          using e \<open>C>0\<close> by (simp add: field_simps)
        have "shrink a \<in> interior(convex hull {a,b,c})"
             "shrink b \<in> interior(convex hull {a,b,c})"
             "shrink c \<in> interior(convex hull {a,b,c})"
          using d e by (auto simp: hull_inc mem_interior_convex_shrink shrink_def)
        then have fhp0: "(f has_contour_integral 0)
                (linepath (shrink a) (shrink b) +++ linepath (shrink b) (shrink c) +++ linepath (shrink c) (shrink a))"
          by (simp add: Cauchy_theorem_triangle holomorphic_on_subset [OF holf] hull_minimal convex_interior)
        then have f_0_shrink: "?pathint (shrink a) (shrink b) + ?pathint (shrink b) (shrink c) + ?pathint (shrink c) (shrink a) = 0"
          by (simp add: has_chain_integral_chain_integral3)
        have fpi_abc: "f contour_integrable_on linepath (shrink a) (shrink b)"
                      "f contour_integrable_on linepath (shrink b) (shrink c)"
                      "f contour_integrable_on linepath (shrink c) (shrink a)"
          using fhp0  by (auto simp: valid_path_join dest: has_contour_integral_integrable)
        have cmod_shr: "\<And>x y. cmod (shrink y - shrink x - (y - x)) = e * cmod (x - y)"
          using e by (simp add: shrink_def real_vector.scale_right_diff_distrib [symmetric])
        have sh_eq: "\<And>a b d::complex. (b - e *\<^sub>R (b - d)) - (a - e *\<^sub>R (a - d)) - (b - a) = e *\<^sub>R (a - b)"
          by (simp add: algebra_simps)
        have "cmod y / (24 * C) \<le> cmod y / cmod (b - a) / 12"
          using False \<open>C>0\<close> diff_2C [of b a] ynz
          by (auto simp: divide_simps hull_inc)
        have less_C: "\<lbrakk>u \<in> convex hull {a, b, c}; 0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> x * cmod u < C" for x u
          apply (cases "x=0", simp add: \<open>0<C\<close>)
          using Cno [of u] mult_left_le_one_le [of "cmod u" x] le_less_trans norm_ge_zero by blast
        { fix u v
          assume uv: "u \<in> convex hull {a, b, c}" "v \<in> convex hull {a, b, c}" "u\<noteq>v"
             and fpi_uv: "f contour_integrable_on linepath (shrink u) (shrink v)"
          have shr_uv: "shrink u \<in> interior(convex hull {a,b,c})"
                       "shrink v \<in> interior(convex hull {a,b,c})"
            using d e uv
            by (auto simp: hull_inc mem_interior_convex_shrink shrink_def)
          have cmod_fuv: "\<And>x. 0\<le>x \<Longrightarrow> x\<le>1 \<Longrightarrow> cmod (f (linepath (shrink u) (shrink v) x)) \<le> B"
            using shr_uv by (blast intro: Bnf linepath_in_convex_hull interior_subset [THEN subsetD])
          have By_uv: "B * (12 * (e * cmod (u - v))) \<le> cmod y"
            apply (rule order_trans [OF _ eCB])
            using e \<open>B>0\<close> diff_2C [of u v] uv
            by (auto simp: field_simps)
          { fix x::real   assume x: "0\<le>x" "x\<le>1"
            have cmod_less_4C: "cmod ((1 - x) *\<^sub>R u - (1 - x) *\<^sub>R d) + cmod (x *\<^sub>R v - x *\<^sub>R d) < (C+C) + (C+C)"
              apply (rule add_strict_mono; rule norm_triangle_half_l [of _ 0])
              using uv x d interior_subset
              apply (auto simp: hull_inc intro!: less_C)
              done
            have ll: "linepath (shrink u) (shrink v) x - linepath u v x = -e * ((1 - x) *\<^sub>R (u - d) + x *\<^sub>R (v - d))"
              by (simp add: linepath_def shrink_def algebra_simps scaleR_conv_of_real)
            have cmod_less_dt: "cmod (linepath (shrink u) (shrink v) x - linepath u v x) < d1"
              using \<open>e>0\<close>
              apply (simp add: ll norm_mult scaleR_diff_right)
              apply (rule less_le_trans [OF _ e_le_d1])
              using cmod_less_4C
              apply (force intro: norm_triangle_lt)
              done
            have "cmod (f (linepath (shrink u) (shrink v) x) - f (linepath u v x)) < cmod y / (24 * C)"
              using x uv shr_uv cmod_less_dt
              by (auto simp: hull_inc intro: d1 interior_subset [THEN subsetD] linepath_in_convex_hull)
            also have "... \<le> cmod y / cmod (v - u) / 12"
              using False uv \<open>C>0\<close> diff_2C [of v u] ynz
              by (auto simp: divide_simps hull_inc)
            finally have "cmod (f (linepath (shrink u) (shrink v) x) - f (linepath u v x)) \<le> cmod y / cmod (v - u) / 12"
              by simp
            then have cmod_12_le: "cmod (v - u) * cmod (f (linepath (shrink u) (shrink v) x) - f (linepath u v x)) * 12 \<le> cmod y"
              using uv False by (auto simp: field_simps)
            have "cmod (f (linepath (shrink u) (shrink v) x)) * cmod (shrink v - shrink u - (v - u)) +
                  cmod (v - u) * cmod (f (linepath (shrink u) (shrink v) x) - f (linepath u v x))
                  \<le> cmod y / 6"
              apply (rule order_trans [of _ "B*((norm y / 24 / C / B)*2*C) + (2*C)*(norm y /24 / C)"])
              apply (rule add_mono [OF mult_mono])
              using By_uv e \<open>0 < B\<close> \<open>0 < C\<close> x ynz
              apply (simp_all add: cmod_fuv cmod_shr cmod_12_le hull_inc)
              apply (simp add: field_simps)
              done
          } note cmod_diff_le = this
          have f_uv: "continuous_on (closed_segment u v) f"
            by (blast intro: uv continuous_on_subset [OF contf closed_segment_subset_convex_hull])
          have **: "\<And>f' x' f x::complex. f'*x' - f*x = f'*(x' - x) + x*(f' - f)"
            by (simp add: algebra_simps)
          have "norm (?pathint (shrink u) (shrink v) - ?pathint u v) \<le> norm y / 6"
            apply (rule order_trans)
            apply (rule has_integral_bound
                    [of "B*(norm y /24/C/B)*2*C + (2*C)*(norm y/24/C)"
                        "\<lambda>x. f(linepath (shrink u) (shrink v) x) * (shrink v - shrink u) - f(linepath u v x)*(v - u)"
                        _ 0 1 ])
            using ynz \<open>0 < B\<close> \<open>0 < C\<close>
            apply (simp_all del: le_divide_eq_numeral1)
            apply (simp add: has_integral_sub has_contour_integral_linepath [symmetric] has_contour_integral_integral
                             fpi_uv f_uv contour_integrable_continuous_linepath, clarify)
            apply (simp only: **)
            apply (simp add: norm_triangle_le norm_mult cmod_diff_le del: le_divide_eq_numeral1)
            done
          } note * = this
          have "norm (?pathint (shrink a) (shrink b) - ?pathint a b) \<le> norm y / 6"
            using False fpi_abc by (rule_tac *) (auto simp: hull_inc)
          moreover
          have "norm (?pathint (shrink b) (shrink c) - ?pathint b c) \<le> norm y / 6"
            using False fpi_abc by (rule_tac *) (auto simp: hull_inc)
          moreover
          have "norm (?pathint (shrink c) (shrink a) - ?pathint c a) \<le> norm y / 6"
            using False fpi_abc by (rule_tac *) (auto simp: hull_inc)
          ultimately
          have "norm((?pathint (shrink a) (shrink b) - ?pathint a b) +
                     (?pathint (shrink b) (shrink c) - ?pathint b c) + (?pathint (shrink c) (shrink a) - ?pathint c a))
                \<le> norm y / 6 + norm y / 6 + norm y / 6"
            by (metis norm_triangle_le add_mono)
          also have "... = norm y / 2"
            by simp
          finally have "norm((?pathint (shrink a) (shrink b) + ?pathint (shrink b) (shrink c) + ?pathint (shrink c) (shrink a)) -
                          (?pathint a b + ?pathint b c + ?pathint c a))
                \<le> norm y / 2"
            by (simp add: algebra_simps)
          then
          have "norm(?pathint a b + ?pathint b c + ?pathint c a) \<le> norm y / 2"
            by (simp add: f_0_shrink) (metis (mono_tags) add.commute minus_add_distrib norm_minus_cancel uminus_add_conv_diff)
          then have "False"
            using pi_eq_y ynz by auto
        }
        moreover have "uniformly_continuous_on (convex hull {a,b,c}) f"
          by (simp add: contf compact_convex_hull compact_uniformly_continuous)
        ultimately have "False"
          unfolding uniformly_continuous_on_def
          by (force simp: ynz \<open>0 < C\<close> dist_norm)
        then show ?thesis ..
      qed
  }
  moreover have "f contour_integrable_on (linepath a b +++ linepath b c +++ linepath c a)"
    using fabc contour_integrable_continuous_linepath by auto
  ultimately show ?thesis
    using has_contour_integral_integral by fastforce
qed


subsection\<open>Version allowing finite number of exceptional points\<close>

lemma Cauchy_theorem_triangle_cofinite:
  assumes "continuous_on (convex hull {a,b,c}) f"
      and "finite s"
      and "(\<And>x. x \<in> interior(convex hull {a,b,c}) - s \<Longrightarrow> f complex_differentiable (at x))"
     shows "(f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
using assms
proof (induction "card s" arbitrary: a b c s rule: less_induct)
  case (less s a b c)
  show ?case
  proof (cases "s={}")
    case True with less show ?thesis
      by (fastforce simp: holomorphic_on_def complex_differentiable_at_within
                    Cauchy_theorem_triangle_interior)
  next
    case False
    then obtain d s' where d: "s = insert d s'" "d \<notin> s'"
      by (meson Set.set_insert all_not_in_conv)
    then show ?thesis
    proof (cases "d \<in> convex hull {a,b,c}")
      case False
      show "(f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
        apply (rule less.hyps [of "s'"])
        using False d \<open>finite s\<close> interior_subset
        apply (auto intro!: less.prems)
        done
    next
      case True
      have *: "convex hull {a, b, d} \<subseteq> convex hull {a, b, c}"
        by (meson True hull_subset insert_subset convex_hull_subset)
      have abd: "(f has_contour_integral 0) (linepath a b +++ linepath b d +++ linepath d a)"
        apply (rule less.hyps [of "s'"])
        using True d  \<open>finite s\<close> not_in_interior_convex_hull_3
        apply (auto intro!: less.prems continuous_on_subset [OF  _ *])
        apply (metis * insert_absorb insert_subset interior_mono)
        done
      have *: "convex hull {b, c, d} \<subseteq> convex hull {a, b, c}"
        by (meson True hull_subset insert_subset convex_hull_subset)
      have bcd: "(f has_contour_integral 0) (linepath b c +++ linepath c d +++ linepath d b)"
        apply (rule less.hyps [of "s'"])
        using True d  \<open>finite s\<close> not_in_interior_convex_hull_3
        apply (auto intro!: less.prems continuous_on_subset [OF _ *])
        apply (metis * insert_absorb insert_subset interior_mono)
        done
      have *: "convex hull {c, a, d} \<subseteq> convex hull {a, b, c}"
        by (meson True hull_subset insert_subset convex_hull_subset)
      have cad: "(f has_contour_integral 0) (linepath c a +++ linepath a d +++ linepath d c)"
        apply (rule less.hyps [of "s'"])
        using True d  \<open>finite s\<close> not_in_interior_convex_hull_3
        apply (auto intro!: less.prems continuous_on_subset [OF _ *])
        apply (metis * insert_absorb insert_subset interior_mono)
        done
      have "f contour_integrable_on linepath a b"
        using less.prems
        by (metis continuous_on_subset insert_commute contour_integrable_continuous_linepath segments_subset_convex_hull(3))
      moreover have "f contour_integrable_on linepath b c"
        using less.prems
        by (metis continuous_on_subset contour_integrable_continuous_linepath segments_subset_convex_hull(3))
      moreover have "f contour_integrable_on linepath c a"
        using less.prems
        by (metis continuous_on_subset insert_commute contour_integrable_continuous_linepath segments_subset_convex_hull(3))
      ultimately have fpi: "f contour_integrable_on (linepath a b +++ linepath b c +++ linepath c a)"
        by auto
      { fix y::complex
        assume fy: "(f has_contour_integral y) (linepath a b +++ linepath b c +++ linepath c a)"
           and ynz: "y \<noteq> 0"
        have cont_ad: "continuous_on (closed_segment a d) f"
          by (meson "*" continuous_on_subset less.prems(1) segments_subset_convex_hull(3))
        have cont_bd: "continuous_on (closed_segment b d) f"
          by (meson True closed_segment_subset_convex_hull continuous_on_subset hull_subset insert_subset less.prems(1))
        have cont_cd: "continuous_on (closed_segment c d) f"
          by (meson "*" continuous_on_subset less.prems(1) segments_subset_convex_hull(2))
        have "contour_integral  (linepath a b) f = - (contour_integral (linepath b d) f + (contour_integral (linepath d a) f))"
                "contour_integral  (linepath b c) f = - (contour_integral (linepath c d) f + (contour_integral (linepath d b) f))"
                "contour_integral  (linepath c a) f = - (contour_integral (linepath a d) f + contour_integral (linepath d c) f)"
            using has_chain_integral_chain_integral3 [OF abd]
                  has_chain_integral_chain_integral3 [OF bcd]
                  has_chain_integral_chain_integral3 [OF cad]
            by (simp_all add: algebra_simps add_eq_0_iff)
        then have ?thesis
          using cont_ad cont_bd cont_cd fy has_chain_integral_chain_integral3 contour_integral_reverse_linepath by fastforce
      }
      then show ?thesis
        using fpi contour_integrable_on_def by blast
    qed
  qed
qed


subsection\<open>Cauchy's theorem for an open starlike set\<close>

lemma starlike_convex_subset:
  assumes s: "a \<in> s" "closed_segment b c \<subseteq> s" and subs: "\<And>x. x \<in> s \<Longrightarrow> closed_segment a x \<subseteq> s"
    shows "convex hull {a,b,c} \<subseteq> s"
      using s
      apply (clarsimp simp add: convex_hull_insert [of "{b,c}" a] segment_convex_hull)
      apply (meson subs convexD convex_closed_segment ends_in_segment(1) ends_in_segment(2) subsetCE)
      done

lemma triangle_contour_integrals_starlike_primitive:
  assumes contf: "continuous_on s f"
      and s: "a \<in> s" "open s"
      and x: "x \<in> s"
      and subs: "\<And>y. y \<in> s \<Longrightarrow> closed_segment a y \<subseteq> s"
      and zer: "\<And>b c. closed_segment b c \<subseteq> s
                   \<Longrightarrow> contour_integral (linepath a b) f + contour_integral (linepath b c) f +
                       contour_integral (linepath c a) f = 0"
    shows "((\<lambda>x. contour_integral(linepath a x) f) has_field_derivative f x) (at x)"
proof -
  let ?pathint = "\<lambda>x y. contour_integral(linepath x y) f"
  { fix e y
    assume e: "0 < e" and bxe: "ball x e \<subseteq> s" and close: "cmod (y - x) < e"
    have y: "y \<in> s"
      using bxe close  by (force simp: dist_norm norm_minus_commute)
    have cont_ayf: "continuous_on (closed_segment a y) f"
      using contf continuous_on_subset subs y by blast
    have xys: "closed_segment x y \<subseteq> s"
      apply (rule order_trans [OF _ bxe])
      using close
      by (auto simp: dist_norm ball_def norm_minus_commute dest: segment_bound)
    have "?pathint a y - ?pathint a x = ?pathint x y"
      using zer [OF xys]  contour_integral_reverse_linepath [OF cont_ayf]  add_eq_0_iff by force
  } note [simp] = this
  { fix e::real
    assume e: "0 < e"
    have cont_atx: "continuous (at x) f"
      using x s contf continuous_on_eq_continuous_at by blast
    then obtain d1 where d1: "d1>0" and d1_less: "\<And>y. cmod (y - x) < d1 \<Longrightarrow> cmod (f y - f x) < e/2"
      unfolding continuous_at Lim_at dist_norm  using e
      by (drule_tac x="e/2" in spec) force
    obtain d2 where d2: "d2>0" "ball x d2 \<subseteq> s" using  \<open>open s\<close> x
      by (auto simp: open_contains_ball)
    have dpos: "min d1 d2 > 0" using d1 d2 by simp
    { fix y
      assume yx: "y \<noteq> x" and close: "cmod (y - x) < min d1 d2"
      have y: "y \<in> s"
        using d2 close  by (force simp: dist_norm norm_minus_commute)
      have fxy: "f contour_integrable_on linepath x y"
        apply (rule contour_integrable_continuous_linepath)
        apply (rule continuous_on_subset [OF contf])
        using close d2
        apply (auto simp: dist_norm norm_minus_commute dest!: segment_bound(1))
        done
      then obtain i where i: "(f has_contour_integral i) (linepath x y)"
        by (auto simp: contour_integrable_on_def)
      then have "((\<lambda>w. f w - f x) has_contour_integral (i - f x * (y - x))) (linepath x y)"
        by (rule has_contour_integral_diff [OF _ has_contour_integral_const_linepath])
      then have "cmod (i - f x * (y - x)) \<le> e / 2 * cmod (y - x)"
        apply (rule has_contour_integral_bound_linepath [where B = "e/2"])
        using e apply simp
        apply (rule d1_less [THEN less_imp_le])
        using close segment_bound
        apply force
        done
      also have "... < e * cmod (y - x)"
        by (simp add: e yx)
      finally have "cmod (?pathint x y - f x * (y-x)) / cmod (y-x) < e"
        using i yx  by (simp add: contour_integral_unique divide_less_eq)
    }
    then have "\<exists>d>0. \<forall>y. y \<noteq> x \<and> cmod (y-x) < d \<longrightarrow> cmod (?pathint x y - f x * (y-x)) / cmod (y-x) < e"
      using dpos by blast
  }
  then have *: "(\<lambda>y. (?pathint x y - f x * (y - x)) /\<^sub>R cmod (y - x)) -- x --> 0"
    by (simp add: Lim_at dist_norm inverse_eq_divide)
  show ?thesis
    apply (simp add: has_field_derivative_def has_derivative_at bounded_linear_mult_right)
    apply (rule Lim_transform [OF * Lim_eventually])
    apply (simp add: inverse_eq_divide [symmetric] eventually_at)
    using \<open>open s\<close> x
    apply (force simp: dist_norm open_contains_ball)
    done
qed

(** Existence of a primitive.*)

lemma holomorphic_starlike_primitive:
  assumes contf: "continuous_on s f"
      and s: "starlike s" and os: "open s"
      and k: "finite k"
      and fcd: "\<And>x. x \<in> s - k \<Longrightarrow> f complex_differentiable at x"
    shows "\<exists>g. \<forall>x \<in> s. (g has_field_derivative f x) (at x)"
proof -
  obtain a where a: "a\<in>s" and a_cs: "\<And>x. x\<in>s \<Longrightarrow> closed_segment a x \<subseteq> s"
    using s by (auto simp: starlike_def)
  { fix x b c
    assume "x \<in> s" "closed_segment b c \<subseteq> s"
    then have abcs: "convex hull {a, b, c} \<subseteq> s"
      by (simp add: a a_cs starlike_convex_subset)
    then have *: "continuous_on (convex hull {a, b, c}) f"
      by (simp add: continuous_on_subset [OF contf])
    have "(f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
      apply (rule Cauchy_theorem_triangle_cofinite [OF _ k])
      using abcs apply (simp add: continuous_on_subset [OF contf])
      using * abcs interior_subset apply (auto intro: fcd)
      done
  } note 0 = this
  show ?thesis
    apply (intro exI ballI)
    apply (rule triangle_contour_integrals_starlike_primitive [OF contf a os], assumption)
    apply (metis a_cs)
    apply (metis has_chain_integral_chain_integral3 0)
    done
qed

lemma Cauchy_theorem_starlike:
 "\<lbrakk>open s; starlike s; finite k; continuous_on s f;
   \<And>x. x \<in> s - k \<Longrightarrow> f complex_differentiable at x;
   valid_path g; path_image g \<subseteq> s; pathfinish g = pathstart g\<rbrakk>
   \<Longrightarrow> (f has_contour_integral 0)  g"
  by (metis holomorphic_starlike_primitive Cauchy_theorem_primitive at_within_open)

lemma Cauchy_theorem_starlike_simple:
  "\<lbrakk>open s; starlike s; f holomorphic_on s; valid_path g; path_image g \<subseteq> s; pathfinish g = pathstart g\<rbrakk>
   \<Longrightarrow> (f has_contour_integral 0) g"
apply (rule Cauchy_theorem_starlike [OF _ _ finite.emptyI])
apply (simp_all add: holomorphic_on_imp_continuous_on)
apply (metis at_within_open holomorphic_on_def)
done


subsection\<open>Cauchy's theorem for a convex set\<close>

text\<open>For a convex set we can avoid assuming openness and boundary analyticity\<close>

lemma triangle_contour_integrals_convex_primitive:
  assumes contf: "continuous_on s f"
      and s: "a \<in> s" "convex s"
      and x: "x \<in> s"
      and zer: "\<And>b c. \<lbrakk>b \<in> s; c \<in> s\<rbrakk>
                   \<Longrightarrow> contour_integral (linepath a b) f + contour_integral (linepath b c) f +
                       contour_integral (linepath c a) f = 0"
    shows "((\<lambda>x. contour_integral(linepath a x) f) has_field_derivative f x) (at x within s)"
proof -
  let ?pathint = "\<lambda>x y. contour_integral(linepath x y) f"
  { fix y
    assume y: "y \<in> s"
    have cont_ayf: "continuous_on (closed_segment a y) f"
      using s y  by (meson contf continuous_on_subset convex_contains_segment)
    have xys: "closed_segment x y \<subseteq> s"  (*?*)
      using convex_contains_segment s x y by auto
    have "?pathint a y - ?pathint a x = ?pathint x y"
      using zer [OF x y]  contour_integral_reverse_linepath [OF cont_ayf]  add_eq_0_iff by force
  } note [simp] = this
  { fix e::real
    assume e: "0 < e"
    have cont_atx: "continuous (at x within s) f"
      using x s contf  by (simp add: continuous_on_eq_continuous_within)
    then obtain d1 where d1: "d1>0" and d1_less: "\<And>y. \<lbrakk>y \<in> s; cmod (y - x) < d1\<rbrakk> \<Longrightarrow> cmod (f y - f x) < e/2"
      unfolding continuous_within Lim_within dist_norm using e
      by (drule_tac x="e/2" in spec) force
    { fix y
      assume yx: "y \<noteq> x" and close: "cmod (y - x) < d1" and y: "y \<in> s"
      have fxy: "f contour_integrable_on linepath x y"
        using convex_contains_segment s x y
        by (blast intro!: contour_integrable_continuous_linepath continuous_on_subset [OF contf])
      then obtain i where i: "(f has_contour_integral i) (linepath x y)"
        by (auto simp: contour_integrable_on_def)
      then have "((\<lambda>w. f w - f x) has_contour_integral (i - f x * (y - x))) (linepath x y)"
        by (rule has_contour_integral_diff [OF _ has_contour_integral_const_linepath])
      then have "cmod (i - f x * (y - x)) \<le> e / 2 * cmod (y - x)"
        apply (rule has_contour_integral_bound_linepath [where B = "e/2"])
        using e apply simp
        apply (rule d1_less [THEN less_imp_le])
        using convex_contains_segment s(2) x y apply blast
        using close segment_bound(1) apply fastforce
        done
      also have "... < e * cmod (y - x)"
        by (simp add: e yx)
      finally have "cmod (?pathint x y - f x * (y-x)) / cmod (y-x) < e"
        using i yx  by (simp add: contour_integral_unique divide_less_eq)
    }
    then have "\<exists>d>0. \<forall>y\<in>s. y \<noteq> x \<and> cmod (y-x) < d \<longrightarrow> cmod (?pathint x y - f x * (y-x)) / cmod (y-x) < e"
      using d1 by blast
  }
  then have *: "((\<lambda>y. (contour_integral (linepath x y) f - f x * (y - x)) /\<^sub>R cmod (y - x)) ---> 0) (at x within s)"
    by (simp add: Lim_within dist_norm inverse_eq_divide)
  show ?thesis
    apply (simp add: has_field_derivative_def has_derivative_within bounded_linear_mult_right)
    apply (rule Lim_transform [OF * Lim_eventually])
    using linordered_field_no_ub
    apply (force simp: inverse_eq_divide [symmetric] eventually_at)
    done
qed

lemma pathintegral_convex_primitive:
  "\<lbrakk>convex s; continuous_on s f;
    \<And>a b c. \<lbrakk>a \<in> s; b \<in> s; c \<in> s\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)\<rbrakk>
         \<Longrightarrow> \<exists>g. \<forall>x \<in> s. (g has_field_derivative f x) (at x within s)"
  apply (cases "s={}")
  apply (simp_all add: ex_in_conv [symmetric])
  apply (blast intro: triangle_contour_integrals_convex_primitive has_chain_integral_chain_integral3)
  done

lemma holomorphic_convex_primitive:
  "\<lbrakk>convex s; finite k; continuous_on s f;
    \<And>x. x \<in> interior s - k \<Longrightarrow> f complex_differentiable at x\<rbrakk>
   \<Longrightarrow> \<exists>g. \<forall>x \<in> s. (g has_field_derivative f x) (at x within s)"
apply (rule pathintegral_convex_primitive [OF _ _ Cauchy_theorem_triangle_cofinite])
prefer 3
apply (erule continuous_on_subset)
apply (simp add: subset_hull continuous_on_subset, assumption+)
by (metis Diff_iff convex_contains_segment insert_absorb insert_subset interior_mono segment_convex_hull subset_hull)

lemma Cauchy_theorem_convex:
    "\<lbrakk>continuous_on s f; convex s; finite k;
      \<And>x. x \<in> interior s - k \<Longrightarrow> f complex_differentiable at x;
     valid_path g; path_image g \<subseteq> s;
     pathfinish g = pathstart g\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) g"
  by (metis holomorphic_convex_primitive Cauchy_theorem_primitive)

lemma Cauchy_theorem_convex_simple:
    "\<lbrakk>f holomorphic_on s; convex s;
     valid_path g; path_image g \<subseteq> s;
     pathfinish g = pathstart g\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) g"
  apply (rule Cauchy_theorem_convex)
  apply (simp_all add: holomorphic_on_imp_continuous_on)
  apply (rule finite.emptyI)
  using at_within_interior holomorphic_on_def interior_subset by fastforce


text\<open>In particular for a disc\<close>
lemma Cauchy_theorem_disc:
    "\<lbrakk>finite k; continuous_on (cball a e) f;
      \<And>x. x \<in> ball a e - k \<Longrightarrow> f complex_differentiable at x;
     valid_path g; path_image g \<subseteq> cball a e;
     pathfinish g = pathstart g\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) g"
  apply (rule Cauchy_theorem_convex)
  apply (auto simp: convex_cball interior_cball)
  done

lemma Cauchy_theorem_disc_simple:
    "\<lbrakk>f holomorphic_on (ball a e); valid_path g; path_image g \<subseteq> ball a e;
     pathfinish g = pathstart g\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) g"
by (simp add: Cauchy_theorem_convex_simple)


subsection\<open>Generalize integrability to local primitives\<close>

lemma contour_integral_local_primitive_lemma:
  fixes f :: "complex\<Rightarrow>complex"
  shows
    "\<lbrakk>g piecewise_differentiable_on {a..b};
      \<And>x. x \<in> s \<Longrightarrow> (f has_field_derivative f' x) (at x within s);
      \<And>x. x \<in> {a..b} \<Longrightarrow> g x \<in> s\<rbrakk>
     \<Longrightarrow> (\<lambda>x. f' (g x) * vector_derivative g (at x within {a..b}))
            integrable_on {a..b}"
  apply (cases "cbox a b = {}", force)
  apply (simp add: integrable_on_def)
  apply (rule exI)
  apply (rule contour_integral_primitive_lemma, assumption+)
  using atLeastAtMost_iff by blast

lemma contour_integral_local_primitive_any:
  fixes f :: "complex \<Rightarrow> complex"
  assumes gpd: "g piecewise_differentiable_on {a..b}"
      and dh: "\<And>x. x \<in> s
               \<Longrightarrow> \<exists>d h. 0 < d \<and>
                         (\<forall>y. norm(y - x) < d \<longrightarrow> (h has_field_derivative f y) (at y within s))"
      and gs: "\<And>x. x \<in> {a..b} \<Longrightarrow> g x \<in> s"
  shows "(\<lambda>x. f(g x) * vector_derivative g (at x)) integrable_on {a..b}"
proof -
  { fix x
    assume x: "a \<le> x" "x \<le> b"
    obtain d h where d: "0 < d"
               and h: "(\<And>y. norm(y - g x) < d \<Longrightarrow> (h has_field_derivative f y) (at y within s))"
      using x gs dh by (metis atLeastAtMost_iff)
    have "continuous_on {a..b} g" using gpd piecewise_differentiable_on_def by blast
    then obtain e where e: "e>0" and lessd: "\<And>x'. x' \<in> {a..b} \<Longrightarrow> \<bar>x' - x\<bar> < e \<Longrightarrow> cmod (g x' - g x) < d"
      using x d
      apply (auto simp: dist_norm continuous_on_iff)
      apply (drule_tac x=x in bspec)
      using x apply simp
      apply (drule_tac x=d in spec, auto)
      done
    have "\<exists>d>0. \<forall>u v. u \<le> x \<and> x \<le> v \<and> {u..v} \<subseteq> ball x d \<and> (u \<le> v \<longrightarrow> a \<le> u \<and> v \<le> b) \<longrightarrow>
                          (\<lambda>x. f (g x) * vector_derivative g (at x)) integrable_on {u..v}"
      apply (rule_tac x=e in exI)
      using e
      apply (simp add: integrable_on_localized_vector_derivative [symmetric], clarify)
      apply (rule_tac f = h and s = "g ` {u..v}" in contour_integral_local_primitive_lemma)
        apply (meson atLeastatMost_subset_iff gpd piecewise_differentiable_on_subset)
       apply (force simp: ball_def dist_norm intro: lessd gs DERIV_subset [OF h], force)
      done
  } then
  show ?thesis
    by (force simp: intro!: integrable_on_little_subintervals [of a b, simplified])
qed

lemma contour_integral_local_primitive:
  fixes f :: "complex \<Rightarrow> complex"
  assumes g: "valid_path g" "path_image g \<subseteq> s"
      and dh: "\<And>x. x \<in> s
               \<Longrightarrow> \<exists>d h. 0 < d \<and>
                         (\<forall>y. norm(y - x) < d \<longrightarrow> (h has_field_derivative f y) (at y within s))"
  shows "f contour_integrable_on g"
  using g
  apply (simp add: valid_path_def path_image_def contour_integrable_on_def has_contour_integral_def
            has_integral_localized_vector_derivative integrable_on_def [symmetric])
  using contour_integral_local_primitive_any [OF _ dh]
  by (meson image_subset_iff piecewise_C1_imp_differentiable)


text\<open>In particular if a function is holomorphic\<close>

lemma contour_integrable_holomorphic:
  assumes contf: "continuous_on s f"
      and os: "open s"
      and k: "finite k"
      and g: "valid_path g" "path_image g \<subseteq> s"
      and fcd: "\<And>x. x \<in> s - k \<Longrightarrow> f complex_differentiable at x"
    shows "f contour_integrable_on g"
proof -
  { fix z
    assume z: "z \<in> s"
    obtain d where d: "d>0" "ball z d \<subseteq> s" using  \<open>open s\<close> z
      by (auto simp: open_contains_ball)
    then have contfb: "continuous_on (ball z d) f"
      using contf continuous_on_subset by blast
    obtain h where "\<forall>y\<in>ball z d. (h has_field_derivative f y) (at y within ball z d)"
      using holomorphic_convex_primitive [OF convex_ball k contfb fcd] d
            interior_subset by force
    then have "\<forall>y\<in>ball z d. (h has_field_derivative f y) (at y within s)"
      by (metis Topology_Euclidean_Space.open_ball at_within_open d(2) os subsetCE)
    then have "\<exists>h. (\<forall>y. cmod (y - z) < d \<longrightarrow> (h has_field_derivative f y) (at y within s))"
      by (force simp: dist_norm norm_minus_commute)
    then have "\<exists>d h. 0 < d \<and> (\<forall>y. cmod (y - z) < d \<longrightarrow> (h has_field_derivative f y) (at y within s))"
      using d by blast
  }
  then show ?thesis
    by (rule contour_integral_local_primitive [OF g])
qed

lemma contour_integrable_holomorphic_simple:
  assumes contf: "continuous_on s f"
      and os: "open s"
      and g: "valid_path g" "path_image g \<subseteq> s"
      and fh: "f holomorphic_on s"
    shows "f contour_integrable_on g"
  apply (rule contour_integrable_holomorphic [OF contf os Finite_Set.finite.emptyI g])
  using fh  by (simp add: complex_differentiable_def holomorphic_on_open os)

lemma continuous_on_inversediff:
  fixes z:: "'a::real_normed_field" shows "z \<notin> s \<Longrightarrow> continuous_on s (\<lambda>w. 1 / (w - z))"
  by (rule continuous_intros | force)+

corollary contour_integrable_inversediff:
    "\<lbrakk>valid_path g; z \<notin> path_image g\<rbrakk> \<Longrightarrow> (\<lambda>w. 1 / (w-z)) contour_integrable_on g"
apply (rule contour_integrable_holomorphic_simple [of "UNIV-{z}", OF continuous_on_inversediff])
apply (auto simp: holomorphic_on_open open_delete intro!: derivative_eq_intros)
done

text\<open>Key fact that path integral is the same for a "nearby" path. This is the
 main lemma for the homotopy form of Cauchy's theorem and is also useful
 if we want "without loss of generality" to assume some nice properties of a
 path (e.g. smoothness). It can also be used to define the integrals of
 analytic functions over arbitrary continuous paths. This is just done for
 winding numbers now.
\<close>

text\<open>A technical definition to avoid duplication of similar proofs,
     for paths joined at the ends versus looping paths\<close>
definition linked_paths :: "bool \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a::topological_space) \<Rightarrow> bool"
  where "linked_paths atends g h ==
        (if atends then pathstart h = pathstart g \<and> pathfinish h = pathfinish g
                   else pathfinish g = pathstart g \<and> pathfinish h = pathstart h)"

text\<open>This formulation covers two cases: @{term g} and @{term h} share their
      start and end points; @{term g} and @{term h} both loop upon themselves.\<close>
lemma contour_integral_nearby:
  assumes os: "open s" and p: "path p" "path_image p \<subseteq> s"
    shows
       "\<exists>d. 0 < d \<and>
            (\<forall>g h. valid_path g \<and> valid_path h \<and>
                  (\<forall>t \<in> {0..1}. norm(g t - p t) < d \<and> norm(h t - p t) < d) \<and>
                  linked_paths atends g h
                  \<longrightarrow> path_image g \<subseteq> s \<and> path_image h \<subseteq> s \<and>
                      (\<forall>f. f holomorphic_on s \<longrightarrow> contour_integral h f = contour_integral g f))"
proof -
  have "\<forall>z. \<exists>e. z \<in> path_image p \<longrightarrow> 0 < e \<and> ball z e \<subseteq> s"
    using open_contains_ball os p(2) by blast
  then obtain ee where ee: "\<And>z. z \<in> path_image p \<Longrightarrow> 0 < ee z \<and> ball z (ee z) \<subseteq> s"
    by metis
  def cover \<equiv> "(\<lambda>z. ball z (ee z/3)) ` (path_image p)"
  have "compact (path_image p)"
    by (metis p(1) compact_path_image)
  moreover have "path_image p \<subseteq> (\<Union>c\<in>path_image p. ball c (ee c / 3))"
    using ee by auto
  ultimately have "\<exists>D \<subseteq> cover. finite D \<and> path_image p \<subseteq> \<Union>D"
    by (simp add: compact_eq_heine_borel cover_def)
  then obtain D where D: "D \<subseteq> cover" "finite D" "path_image p \<subseteq> \<Union>D"
    by blast
  then obtain k where k: "k \<subseteq> {0..1}" "finite k" and D_eq: "D = ((\<lambda>z. ball z (ee z / 3)) \<circ> p) ` k"
    apply (simp add: cover_def path_image_def image_comp)
    apply (blast dest!: finite_subset_image [OF \<open>finite D\<close>])
    done
  then have kne: "k \<noteq> {}"
    using D by auto
  have pi: "\<And>i. i \<in> k \<Longrightarrow> p i \<in> path_image p"
    using k  by (auto simp: path_image_def)
  then have eepi: "\<And>i. i \<in> k \<Longrightarrow> 0 < ee((p i))"
    by (metis ee)
  def e \<equiv> "Min((ee o p) ` k)"
  have fin_eep: "finite ((ee o p) ` k)"
    using k  by blast
  have enz: "0 < e"
    using ee k  by (simp add: kne e_def Min_gr_iff [OF fin_eep] eepi)
  have "uniformly_continuous_on {0..1} p"
    using p  by (simp add: path_def compact_uniformly_continuous)
  then obtain d::real where d: "d>0"
          and de: "\<And>x x'. \<bar>x' - x\<bar> < d \<Longrightarrow> x\<in>{0..1} \<Longrightarrow> x'\<in>{0..1} \<Longrightarrow> cmod (p x' - p x) < e/3"
    unfolding uniformly_continuous_on_def dist_norm real_norm_def
    by (metis divide_pos_pos enz zero_less_numeral)
  then obtain N::nat where N: "N>0" "inverse N < d"
    using real_arch_inv [of d]   by auto
  { fix g h
    assume g: "valid_path g" and gp: "\<forall>t\<in>{0..1}. cmod (g t - p t) < e / 3"
       and h: "valid_path h" and hp: "\<forall>t\<in>{0..1}. cmod (h t - p t) < e / 3"
       and joins: "linked_paths atends g h"
    { fix t::real
      assume t: "0 \<le> t" "t \<le> 1"
      then obtain u where u: "u \<in> k" and ptu: "p t \<in> ball(p u) (ee(p u) / 3)"
        using \<open>path_image p \<subseteq> \<Union>D\<close> D_eq by (force simp: path_image_def)
      then have ele: "e \<le> ee (p u)" using fin_eep
        by (simp add: e_def)
      have "cmod (g t - p t) < e / 3" "cmod (h t - p t) < e / 3"
        using gp hp t by auto
      with ele have "cmod (g t - p t) < ee (p u) / 3"
                    "cmod (h t - p t) < ee (p u) / 3"
        by linarith+
      then have "g t \<in> ball(p u) (ee(p u))"  "h t \<in> ball(p u) (ee(p u))"
        using norm_diff_triangle_ineq [of "g t" "p t" "p t" "p u"]
              norm_diff_triangle_ineq [of "h t" "p t" "p t" "p u"] ptu eepi u
        by (force simp: dist_norm ball_def norm_minus_commute)+
      then have "g t \<in> s" "h t \<in> s" using ee u k
        by (auto simp: path_image_def ball_def)
    }
    then have ghs: "path_image g \<subseteq> s" "path_image h \<subseteq> s"
      by (auto simp: path_image_def)
    moreover
    { fix f
      assume fhols: "f holomorphic_on s"
      then have fpa: "f contour_integrable_on g"  "f contour_integrable_on h"
        using g ghs h holomorphic_on_imp_continuous_on os contour_integrable_holomorphic_simple
        by blast+
      have contf: "continuous_on s f"
        by (simp add: fhols holomorphic_on_imp_continuous_on)
      { fix z
        assume z: "z \<in> path_image p"
        have "f holomorphic_on ball z (ee z)"
          using fhols ee z holomorphic_on_subset by blast
        then have "\<exists>ff. (\<forall>w \<in> ball z (ee z). (ff has_field_derivative f w) (at w))"
          using holomorphic_convex_primitive [of "ball z (ee z)" "{}" f, simplified]
          by (metis open_ball at_within_open holomorphic_on_def holomorphic_on_imp_continuous_on mem_ball)
      }
      then obtain ff where ff:
            "\<And>z w. \<lbrakk>z \<in> path_image p; w \<in> ball z (ee z)\<rbrakk> \<Longrightarrow> (ff z has_field_derivative f w) (at w)"
        by metis
      { fix n
        assume n: "n \<le> N"
        then have "contour_integral(subpath 0 (n/N) h) f - contour_integral(subpath 0 (n/N) g) f =
                   contour_integral(linepath (g(n/N)) (h(n/N))) f - contour_integral(linepath (g 0) (h 0)) f"
        proof (induct n)
          case 0 show ?case by simp
        next
          case (Suc n)
          obtain t where t: "t \<in> k" and "p (n/N) \<in> ball(p t) (ee(p t) / 3)"
            using \<open>path_image p \<subseteq> \<Union>D\<close> [THEN subsetD, where c="p (n/N)"] D_eq N Suc.prems
            by (force simp: path_image_def)
          then have ptu: "cmod (p t - p (n/N)) < ee (p t) / 3"
            by (simp add: dist_norm)
          have e3le: "e/3 \<le> ee (p t) / 3"  using fin_eep t
            by (simp add: e_def)
          { fix x
            assume x: "n/N \<le> x" "x \<le> (1 + n)/N"
            then have nN01: "0 \<le> n/N" "(1 + n)/N \<le> 1"
              using Suc.prems by auto
            then have x01: "0 \<le> x" "x \<le> 1"
              using x by linarith+
            have "cmod (p t - p x)  < ee (p t) / 3 + e/3"
              apply (rule norm_diff_triangle_less [OF ptu de])
              using x N x01 Suc.prems
              apply (auto simp: field_simps)
              done
            then have ptx: "cmod (p t - p x) < 2*ee (p t)/3"
              using e3le eepi [OF t] by simp
            have "cmod (p t - g x) < 2*ee (p t)/3 + e/3 "
              apply (rule norm_diff_triangle_less [OF ptx])
              using gp x01 by (simp add: norm_minus_commute)
            also have "... \<le> ee (p t)"
              using e3le eepi [OF t] by simp
            finally have gg: "cmod (p t - g x) < ee (p t)" .
            have "cmod (p t - h x) < 2*ee (p t)/3 + e/3 "
              apply (rule norm_diff_triangle_less [OF ptx])
              using hp x01 by (simp add: norm_minus_commute)
            also have "... \<le> ee (p t)"
              using e3le eepi [OF t] by simp
            finally have "cmod (p t - g x) < ee (p t)"
                         "cmod (p t - h x) < ee (p t)"
              using gg by auto
          } note ptgh_ee = this
          have pi_hgn: "path_image (linepath (h (n/N)) (g (n/N))) \<subseteq> ball (p t) (ee (p t))"
            using ptgh_ee [of "n/N"] Suc.prems
            by (auto simp: field_simps dist_norm dest: segment_furthest_le [where y="p t"])
          then have gh_ns: "closed_segment (g (n/N)) (h (n/N)) \<subseteq> s"
            using \<open>N>0\<close> Suc.prems
            apply (simp add: path_image_join field_simps closed_segment_commute)
            apply (erule order_trans)
            apply (simp add: ee pi t)
            done
          have pi_ghn': "path_image (linepath (g ((1 + n) / N)) (h ((1 + n) / N)))
                  \<subseteq> ball (p t) (ee (p t))"
            using ptgh_ee [of "(1+n)/N"] Suc.prems
            by (auto simp: field_simps dist_norm dest: segment_furthest_le [where y="p t"])
          then have gh_n's: "closed_segment (g ((1 + n) / N)) (h ((1 + n) / N)) \<subseteq> s"
            using \<open>N>0\<close> Suc.prems ee pi t
            by (auto simp: Path_Connected.path_image_join field_simps)
          have pi_subset_ball:
                "path_image (subpath (n/N) ((1+n) / N) g +++ linepath (g ((1+n) / N)) (h ((1+n) / N)) +++
                             subpath ((1+n) / N) (n/N) h +++ linepath (h (n/N)) (g (n/N)))
                 \<subseteq> ball (p t) (ee (p t))"
            apply (intro subset_path_image_join pi_hgn pi_ghn')
            using \<open>N>0\<close> Suc.prems
            apply (auto simp: dist_norm field_simps closed_segment_eq_real_ivl ptgh_ee)
            done
          have pi0: "(f has_contour_integral 0)
                       (subpath (n/ N) ((Suc n)/N) g +++ linepath(g ((Suc n) / N)) (h((Suc n) / N)) +++
                        subpath ((Suc n) / N) (n/N) h +++ linepath(h (n/N)) (g (n/N)))"
            apply (rule Cauchy_theorem_primitive [of "ball(p t) (ee(p t))" "ff (p t)" "f"])
            apply (metis ff open_ball at_within_open pi t)
            apply (intro valid_path_join)
            using Suc.prems pi_subset_ball apply (simp_all add: valid_path_subpath g h)
            done
          have fpa1: "f contour_integrable_on subpath (real n / real N) (real (Suc n) / real N) g"
            using Suc.prems by (simp add: contour_integrable_subpath g fpa)
          have fpa2: "f contour_integrable_on linepath (g (real (Suc n) / real N)) (h (real (Suc n) / real N))"
            using gh_n's
            by (auto intro!: contour_integrable_continuous_linepath continuous_on_subset [OF contf])
          have fpa3: "f contour_integrable_on linepath (h (real n / real N)) (g (real n / real N))"
            using gh_ns
            by (auto simp: closed_segment_commute intro!: contour_integrable_continuous_linepath continuous_on_subset [OF contf])
          have eq0: "contour_integral (subpath (n/N) ((Suc n) / real N) g) f +
                     contour_integral (linepath (g ((Suc n) / N)) (h ((Suc n) / N))) f +
                     contour_integral (subpath ((Suc n) / N) (n/N) h) f +
                     contour_integral (linepath (h (n/N)) (g (n/N))) f = 0"
            using contour_integral_unique [OF pi0] Suc.prems
            by (simp add: g h fpa valid_path_subpath contour_integrable_subpath
                          fpa1 fpa2 fpa3 algebra_simps del: of_nat_Suc)
          have *: "\<And>hn he hn' gn gd gn' hgn ghn gh0 ghn'.
                    \<lbrakk>hn - gn = ghn - gh0;
                     gd + ghn' + he + hgn = (0::complex);
                     hn - he = hn'; gn + gd = gn'; hgn = -ghn\<rbrakk> \<Longrightarrow> hn' - gn' = ghn' - gh0"
            by (auto simp: algebra_simps)
          have "contour_integral (subpath 0 (n/N) h) f - contour_integral (subpath ((Suc n) / N) (n/N) h) f =
                contour_integral (subpath 0 (n/N) h) f + contour_integral (subpath (n/N) ((Suc n) / N) h) f"
            unfolding reversepath_subpath [symmetric, of "((Suc n) / N)"]
            using Suc.prems by (simp add: h fpa contour_integral_reversepath valid_path_subpath contour_integrable_subpath)
          also have "... = contour_integral (subpath 0 ((Suc n) / N) h) f"
            using Suc.prems by (simp add: contour_integral_subpath_combine h fpa)
          finally have pi0_eq:
               "contour_integral (subpath 0 (n/N) h) f - contour_integral (subpath ((Suc n) / N) (n/N) h) f =
                contour_integral (subpath 0 ((Suc n) / N) h) f" .
          show ?case
            apply (rule * [OF Suc.hyps eq0 pi0_eq])
            using Suc.prems
            apply (simp_all add: g h fpa contour_integral_subpath_combine
                     contour_integral_reversepath [symmetric] contour_integrable_continuous_linepath
                     continuous_on_subset [OF contf gh_ns])
            done
      qed
      } note ind = this
      have "contour_integral h f = contour_integral g f"
        using ind [OF order_refl] N joins
        by (simp add: linked_paths_def pathstart_def pathfinish_def split: split_if_asm)
    }
    ultimately
    have "path_image g \<subseteq> s \<and> path_image h \<subseteq> s \<and> (\<forall>f. f holomorphic_on s \<longrightarrow> contour_integral h f = contour_integral g f)"
      by metis
  } note * = this
  show ?thesis
    apply (rule_tac x="e/3" in exI)
    apply (rule conjI)
    using enz apply simp
    apply (clarsimp simp only: ball_conj_distrib)
    apply (rule *; assumption)
    done
qed


lemma
  assumes "open s" "path p" "path_image p \<subseteq> s"
    shows contour_integral_nearby_ends:
      "\<exists>d. 0 < d \<and>
              (\<forall>g h. valid_path g \<and> valid_path h \<and>
                    (\<forall>t \<in> {0..1}. norm(g t - p t) < d \<and> norm(h t - p t) < d) \<and>
                    pathstart h = pathstart g \<and> pathfinish h = pathfinish g
                    \<longrightarrow> path_image g \<subseteq> s \<and>
                        path_image h \<subseteq> s \<and>
                        (\<forall>f. f holomorphic_on s
                            \<longrightarrow> contour_integral h f = contour_integral g f))"
    and contour_integral_nearby_loops:
      "\<exists>d. 0 < d \<and>
              (\<forall>g h. valid_path g \<and> valid_path h \<and>
                    (\<forall>t \<in> {0..1}. norm(g t - p t) < d \<and> norm(h t - p t) < d) \<and>
                    pathfinish g = pathstart g \<and> pathfinish h = pathstart h
                    \<longrightarrow> path_image g \<subseteq> s \<and>
                        path_image h \<subseteq> s \<and>
                        (\<forall>f. f holomorphic_on s
                            \<longrightarrow> contour_integral h f = contour_integral g f))"
  using contour_integral_nearby [OF assms, where atends=True]
  using contour_integral_nearby [OF assms, where atends=False]
  unfolding linked_paths_def by simp_all

corollary differentiable_polynomial_function:
  fixes p :: "real \<Rightarrow> 'a::euclidean_space"
  shows "polynomial_function p \<Longrightarrow> p differentiable_on s"
by (meson has_vector_derivative_polynomial_function differentiable_at_imp_differentiable_on differentiable_def has_vector_derivative_def)

lemma C1_differentiable_polynomial_function:
  fixes p :: "real \<Rightarrow> 'a::euclidean_space"
  shows "polynomial_function p \<Longrightarrow> p C1_differentiable_on s"
  by (metis continuous_on_polymonial_function C1_differentiable_on_def  has_vector_derivative_polynomial_function)

lemma valid_path_polynomial_function:
  fixes p :: "real \<Rightarrow> 'a::euclidean_space"
  shows "polynomial_function p \<Longrightarrow> valid_path p"
by (force simp: valid_path_def piecewise_C1_differentiable_on_def continuous_on_polymonial_function C1_differentiable_polynomial_function)

lemma valid_path_subpath_trivial [simp]:
    fixes g :: "real \<Rightarrow> 'a::euclidean_space"
    shows "z \<noteq> g x \<Longrightarrow> valid_path (subpath x x g)"
  by (simp add: subpath_def valid_path_polynomial_function)

lemma contour_integral_bound_exists:
assumes s: "open s"
    and g: "valid_path g"
    and pag: "path_image g \<subseteq> s"
  shows "\<exists>L. 0 < L \<and>
       (\<forall>f B. f holomorphic_on s \<and> (\<forall>z \<in> s. norm(f z) \<le> B)
         \<longrightarrow> norm(contour_integral g f) \<le> L*B)"
proof -
have "path g" using g
  by (simp add: valid_path_imp_path)
then obtain d::real and p
  where d: "0 < d"
    and p: "polynomial_function p" "path_image p \<subseteq> s"
    and pi: "\<And>f. f holomorphic_on s \<Longrightarrow> contour_integral g f = contour_integral p f"
  using contour_integral_nearby_ends [OF s \<open>path g\<close> pag]
  apply clarify
  apply (drule_tac x=g in spec)
  apply (simp only: assms)
  apply (force simp: valid_path_polynomial_function dest: path_approx_polynomial_function)
  done
then obtain p' where p': "polynomial_function p'"
         "\<And>x. (p has_vector_derivative (p' x)) (at x)"
  using has_vector_derivative_polynomial_function by force
then have "bounded(p' ` {0..1})"
  using continuous_on_polymonial_function
  by (force simp: intro!: compact_imp_bounded compact_continuous_image)
then obtain L where L: "L>0" and nop': "\<And>x. x \<in> {0..1} \<Longrightarrow> norm (p' x) \<le> L"
  by (force simp: bounded_pos)
{ fix f B
  assume f: "f holomorphic_on s"
     and B: "\<And>z. z\<in>s \<Longrightarrow> cmod (f z) \<le> B"
  then have "f contour_integrable_on p \<and> valid_path p"
    using p s
    by (blast intro: valid_path_polynomial_function contour_integrable_holomorphic_simple holomorphic_on_imp_continuous_on)
  moreover have "\<And>x. x \<in> {0..1} \<Longrightarrow> cmod (vector_derivative p (at x)) * cmod (f (p x)) \<le> L * B"
    apply (rule mult_mono)
    apply (subst Derivative.vector_derivative_at; force intro: p' nop')
    using L B p
    apply (auto simp: path_image_def image_subset_iff)
    done
  ultimately have "cmod (contour_integral g f) \<le> L * B"
    apply (simp add: pi [OF f])
    apply (simp add: contour_integral_integral)
    apply (rule order_trans [OF integral_norm_bound_integral])
    apply (auto simp: mult.commute integral_norm_bound_integral contour_integrable_on [symmetric] norm_mult)
    done
} then
show ?thesis
  by (force simp: L contour_integral_integral)
qed

subsection\<open>Constancy of a function from a connected set into a finite, disconnected or discrete set\<close>

text\<open>Still missing: versions for a set that is smaller than R, or countable.\<close>

lemma continuous_disconnected_range_constant:
  assumes s: "connected s"
      and conf: "continuous_on s f"
      and fim: "f ` s \<subseteq> t"
      and cct: "\<And>y. y \<in> t \<Longrightarrow> connected_component_set t y = {y}"
    shows "\<exists>a. \<forall>x \<in> s. f x = a"
proof (cases "s = {}")
  case True then show ?thesis by force
next
  case False
  { fix x assume "x \<in> s"
    then have "f ` s \<subseteq> {f x}"
    by (metis connected_continuous_image conf connected_component_maximal fim image_subset_iff rev_image_eqI s cct)
  }
  with False show ?thesis
    by blast
qed

lemma discrete_subset_disconnected:
  fixes s :: "'a::topological_space set"
  fixes t :: "'b::real_normed_vector set"
  assumes conf: "continuous_on s f"
      and no: "\<And>x. x \<in> s \<Longrightarrow> \<exists>e>0. \<forall>y. y \<in> s \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x)"
   shows "f ` s \<subseteq> {y. connected_component_set (f ` s) y = {y}}"
proof -
  { fix x assume x: "x \<in> s"
    then obtain e where "e>0" and ele: "\<And>y. \<lbrakk>y \<in> s; f y \<noteq> f x\<rbrakk> \<Longrightarrow> e \<le> norm (f y - f x)"
      using conf no [OF x] by auto
    then have e2: "0 \<le> e / 2"
      by simp
    have "f y = f x" if "y \<in> s" and ccs: "f y \<in> connected_component_set (f ` s) (f x)" for y
      apply (rule ccontr)
      using connected_closed [of "connected_component_set (f ` s) (f x)"] `e>0`
      apply (simp add: del: ex_simps)
      apply (drule spec [where x="cball (f x) (e / 2)"])
      apply (drule spec [where x="- ball(f x) e"])
      apply (auto simp: dist_norm open_closed [symmetric] simp del: le_divide_eq_numeral1 dest!: connected_component_in)
        apply (metis diff_self e2 ele norm_minus_commute norm_zero not_less)
       using centre_in_cball connected_component_refl_eq e2 x apply blast
      using ccs
      apply (force simp: cball_def dist_norm norm_minus_commute dest: ele [OF `y \<in> s`])
      done
    moreover have "connected_component_set (f ` s) (f x) \<subseteq> f ` s"
      by (auto simp: connected_component_in)
    ultimately have "connected_component_set (f ` s) (f x) = {f x}"
      by (auto simp: x)
  }
  with assms show ?thesis
    by blast
qed

lemma finite_implies_discrete:
  fixes s :: "'a::topological_space set"
  assumes "finite (f ` s)"
  shows "(\<forall>x \<in> s. \<exists>e>0. \<forall>y. y \<in> s \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x))"
proof -
  have "\<exists>e>0. \<forall>y. y \<in> s \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x)" if "x \<in> s" for x
  proof (cases "f ` s - {f x} = {}")
    case True
    with zero_less_numeral show ?thesis
      by (fastforce simp add: Set.image_subset_iff cong: conj_cong)
  next
    case False
    then obtain z where z: "z \<in> s" "f z \<noteq> f x"
      by blast
    have finn: "finite {norm (z - f x) |z. z \<in> f ` s - {f x}}"
      using assms by simp
    then have *: "0 < Inf{norm(z - f x) | z. z \<in> f ` s - {f x}}"
      apply (rule finite_imp_less_Inf)
      using z apply force+
      done
    show ?thesis
      by (force intro!: * cInf_le_finite [OF finn])
  qed
  with assms show ?thesis
    by blast
qed

text\<open>This proof requires the existence of two separate values of the range type.\<close>
lemma finite_range_constant_imp_connected:
  assumes "\<And>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
              \<lbrakk>continuous_on s f; finite(f ` s)\<rbrakk> \<Longrightarrow> \<exists>a. \<forall>x \<in> s. f x = a"
    shows "connected s"
proof -
  { fix t u
    assume clt: "closedin (subtopology euclidean s) t"
       and clu: "closedin (subtopology euclidean s) u"
       and tue: "t \<inter> u = {}" and tus: "t \<union> u = s"
    have conif: "continuous_on s (\<lambda>x. if x \<in> t then 0 else 1)"
      apply (subst tus [symmetric])
      apply (rule continuous_on_cases_local)
      using clt clu tue
      apply (auto simp: tus continuous_on_const)
      done
    have fi: "finite ((\<lambda>x. if x \<in> t then 0 else 1) ` s)"
      by (rule finite_subset [of _ "{0,1}"]) auto
    have "t = {} \<or> u = {}"
      using assms [OF conif fi] tus [symmetric]
      by (auto simp: Ball_def) (metis IntI empty_iff one_neq_zero tue)
  }
  then show ?thesis
    by (simp add: connected_closed_in_eq)
qed

lemma continuous_disconnected_range_constant_eq:
      "(connected s \<longleftrightarrow>
           (\<forall>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
            \<forall>t. continuous_on s f \<and> f ` s \<subseteq> t \<and> (\<forall>y \<in> t. connected_component_set t y = {y})
            \<longrightarrow> (\<exists>a::'b. \<forall>x \<in> s. f x = a)))" (is ?thesis1)
  and continuous_discrete_range_constant_eq:
      "(connected s \<longleftrightarrow>
         (\<forall>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
          continuous_on s f \<and>
          (\<forall>x \<in> s. \<exists>e. 0 < e \<and> (\<forall>y. y \<in> s \<and> (f y \<noteq> f x) \<longrightarrow> e \<le> norm(f y - f x)))
          \<longrightarrow> (\<exists>a::'b. \<forall>x \<in> s. f x = a)))" (is ?thesis2)
  and continuous_finite_range_constant_eq:
      "(connected s \<longleftrightarrow>
         (\<forall>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
          continuous_on s f \<and> finite (f ` s)
          \<longrightarrow> (\<exists>a::'b. \<forall>x \<in> s. f x = a)))" (is ?thesis3)
proof -
  have *: "\<And>s t u v. \<lbrakk>s \<Longrightarrow> t; t \<Longrightarrow> u; u \<Longrightarrow> v; v \<Longrightarrow> s\<rbrakk>
    \<Longrightarrow> (s \<longleftrightarrow> t) \<and> (s \<longleftrightarrow> u) \<and> (s \<longleftrightarrow> v)"
    by blast
  have "?thesis1 \<and> ?thesis2 \<and> ?thesis3"
    apply (rule *)
    using continuous_disconnected_range_constant apply metis
    apply clarify
    apply (frule discrete_subset_disconnected; blast)
    apply (blast dest: finite_implies_discrete)
    apply (blast intro!: finite_range_constant_imp_connected)
    done
  then show ?thesis1 ?thesis2 ?thesis3
    by blast+
qed

lemma continuous_discrete_range_constant:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1"
  assumes s: "connected s"
      and "continuous_on s f"
      and "\<And>x. x \<in> s \<Longrightarrow> \<exists>e>0. \<forall>y. y \<in> s \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x)"
    shows "\<exists>a. \<forall>x \<in> s. f x = a"
  using continuous_discrete_range_constant_eq [THEN iffD1, OF s] assms
  by blast

lemma continuous_finite_range_constant:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1"
  assumes "connected s"
      and "continuous_on s f"
      and "finite (f ` s)"
    shows "\<exists>a. \<forall>x \<in> s. f x = a"
  using assms continuous_finite_range_constant_eq
  by blast


text\<open>We can treat even non-rectifiable paths as having a "length" for bounds on analytic functions in open sets.\<close>

subsection\<open>Winding Numbers\<close>

text\<open>The result is an integer, but it doesn't have type @{typ int}!\<close>
definition winding_number:: "[real \<Rightarrow> complex, complex] \<Rightarrow> complex" where
  "winding_number \<gamma> z \<equiv>
    @n. \<forall>e > 0. \<exists>p. valid_path p \<and> z \<notin> path_image p \<and>
                    pathstart p = pathstart \<gamma> \<and>
                    pathfinish p = pathfinish \<gamma> \<and>
                    (\<forall>t \<in> {0..1}. norm(\<gamma> t - p t) < e) \<and>
                    contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * ii * n"

lemma winding_number:
  assumes "path \<gamma>" "z \<notin> path_image \<gamma>" "0 < e"
    shows "\<exists>p. valid_path p \<and> z \<notin> path_image p \<and>
               pathstart p = pathstart \<gamma> \<and>
               pathfinish p = pathfinish \<gamma> \<and>
               (\<forall>t \<in> {0..1}. norm (\<gamma> t - p t) < e) \<and>
               contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * ii * winding_number \<gamma> z"
proof -
  have "path_image \<gamma> \<subseteq> UNIV - {z}"
    using assms by blast
  then obtain d
    where d: "d>0"
      and pi_eq: "\<And>h1 h2. valid_path h1 \<and> valid_path h2 \<and>
                    (\<forall>t\<in>{0..1}. cmod (h1 t - \<gamma> t) < d \<and> cmod (h2 t - \<gamma> t) < d) \<and>
                    pathstart h2 = pathstart h1 \<and> pathfinish h2 = pathfinish h1 \<longrightarrow>
                      path_image h1 \<subseteq> UNIV - {z} \<and> path_image h2 \<subseteq> UNIV - {z} \<and>
                      (\<forall>f. f holomorphic_on UNIV - {z} \<longrightarrow> contour_integral h2 f = contour_integral h1 f)"
    using contour_integral_nearby_ends [of "UNIV - {z}" \<gamma>] assms by (auto simp: open_delete)
  then obtain h where h: "polynomial_function h \<and> pathstart h = pathstart \<gamma> \<and> pathfinish h = pathfinish \<gamma> \<and>
                          (\<forall>t \<in> {0..1}. norm(h t - \<gamma> t) < d/2)"
    using path_approx_polynomial_function [OF `path \<gamma>`, of "d/2"] d by auto
  def nn \<equiv> "1/(2* pi*ii) * contour_integral h (\<lambda>w. 1/(w - z))"
  have "\<exists>n. \<forall>e > 0. \<exists>p. valid_path p \<and> z \<notin> path_image p \<and>
                        pathstart p = pathstart \<gamma> \<and>  pathfinish p = pathfinish \<gamma> \<and>
                        (\<forall>t \<in> {0..1}. norm(\<gamma> t - p t) < e) \<and>
                        contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * ii * n"
                    (is "\<exists>n. \<forall>e > 0. ?PP e n")
    proof (rule_tac x=nn in exI, clarify)
      fix e::real
      assume e: "e>0"
      obtain p where p: "polynomial_function p \<and>
            pathstart p = pathstart \<gamma> \<and> pathfinish p = pathfinish \<gamma> \<and> (\<forall>t\<in>{0..1}. cmod (p t - \<gamma> t) < min e (d / 2))"
        using path_approx_polynomial_function [OF `path \<gamma>`, of "min e (d/2)"] d `0<e` by auto
      have "(\<lambda>w. 1 / (w - z)) holomorphic_on UNIV - {z}"
        by (auto simp: intro!: holomorphic_intros)
      then show "?PP e nn"
        apply (rule_tac x=p in exI)
        using pi_eq [of h p] h p d
        apply (auto simp: valid_path_polynomial_function norm_minus_commute nn_def)
        done
    qed
  then show ?thesis
    unfolding winding_number_def
    apply (rule someI2_ex)
    apply (blast intro: `0<e`)
    done
qed

lemma winding_number_unique:
  assumes \<gamma>: "path \<gamma>" "z \<notin> path_image \<gamma>"
      and pi:
        "\<And>e. e>0 \<Longrightarrow> \<exists>p. valid_path p \<and> z \<notin> path_image p \<and>
                          pathstart p = pathstart \<gamma> \<and> pathfinish p = pathfinish \<gamma> \<and>
                          (\<forall>t \<in> {0..1}. norm (\<gamma> t - p t) < e) \<and>
                          contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * ii * n"
   shows "winding_number \<gamma> z = n"
proof -
  have "path_image \<gamma> \<subseteq> UNIV - {z}"
    using assms by blast
  then obtain e
    where e: "e>0"
      and pi_eq: "\<And>h1 h2 f. \<lbrakk>valid_path h1; valid_path h2;
                    (\<forall>t\<in>{0..1}. cmod (h1 t - \<gamma> t) < e \<and> cmod (h2 t - \<gamma> t) < e);
                    pathstart h2 = pathstart h1; pathfinish h2 = pathfinish h1; f holomorphic_on UNIV - {z}\<rbrakk> \<Longrightarrow>
                    contour_integral h2 f = contour_integral h1 f"
    using contour_integral_nearby_ends [of "UNIV - {z}" \<gamma>] assms  by (auto simp: open_delete)
  obtain p where p:
     "valid_path p \<and> z \<notin> path_image p \<and>
      pathstart p = pathstart \<gamma> \<and> pathfinish p = pathfinish \<gamma> \<and>
      (\<forall>t \<in> {0..1}. norm (\<gamma> t - p t) < e) \<and>
      contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * ii * n"
    using pi [OF e] by blast
  obtain q where q:
     "valid_path q \<and> z \<notin> path_image q \<and>
      pathstart q = pathstart \<gamma> \<and> pathfinish q = pathfinish \<gamma> \<and>
      (\<forall>t\<in>{0..1}. cmod (\<gamma> t - q t) < e) \<and> contour_integral q (\<lambda>w. 1 / (w - z)) = complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z"
    using winding_number [OF \<gamma> e] by blast
  have "2 * complex_of_real pi * \<i> * n = contour_integral p (\<lambda>w. 1 / (w - z))"
    using p by auto
  also have "... = contour_integral q (\<lambda>w. 1 / (w - z))"
    apply (rule pi_eq)
    using p q
    by (auto simp: valid_path_polynomial_function norm_minus_commute intro!: holomorphic_intros)
  also have "... = 2 * complex_of_real pi * \<i> * winding_number \<gamma> z"
    using q by auto
  finally have "2 * complex_of_real pi * \<i> * n = 2 * complex_of_real pi * \<i> * winding_number \<gamma> z" .
  then show ?thesis
    by simp
qed

lemma winding_number_unique_loop:
  assumes \<gamma>: "path \<gamma>" "z \<notin> path_image \<gamma>"
      and loop: "pathfinish \<gamma> = pathstart \<gamma>"
      and pi:
        "\<And>e. e>0 \<Longrightarrow> \<exists>p. valid_path p \<and> z \<notin> path_image p \<and>
                           pathfinish p = pathstart p \<and>
                           (\<forall>t \<in> {0..1}. norm (\<gamma> t - p t) < e) \<and>
                           contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * ii * n"
   shows "winding_number \<gamma> z = n"
proof -
  have "path_image \<gamma> \<subseteq> UNIV - {z}"
    using assms by blast
  then obtain e
    where e: "e>0"
      and pi_eq: "\<And>h1 h2 f. \<lbrakk>valid_path h1; valid_path h2;
                    (\<forall>t\<in>{0..1}. cmod (h1 t - \<gamma> t) < e \<and> cmod (h2 t - \<gamma> t) < e);
                    pathfinish h1 = pathstart h1; pathfinish h2 = pathstart h2; f holomorphic_on UNIV - {z}\<rbrakk> \<Longrightarrow>
                    contour_integral h2 f = contour_integral h1 f"
    using contour_integral_nearby_loops [of "UNIV - {z}" \<gamma>] assms  by (auto simp: open_delete)
  obtain p where p:
     "valid_path p \<and> z \<notin> path_image p \<and>
      pathfinish p = pathstart p \<and>
      (\<forall>t \<in> {0..1}. norm (\<gamma> t - p t) < e) \<and>
      contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * ii * n"
    using pi [OF e] by blast
  obtain q where q:
     "valid_path q \<and> z \<notin> path_image q \<and>
      pathstart q = pathstart \<gamma> \<and> pathfinish q = pathfinish \<gamma> \<and>
      (\<forall>t\<in>{0..1}. cmod (\<gamma> t - q t) < e) \<and> contour_integral q (\<lambda>w. 1 / (w - z)) = complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z"
    using winding_number [OF \<gamma> e] by blast
  have "2 * complex_of_real pi * \<i> * n = contour_integral p (\<lambda>w. 1 / (w - z))"
    using p by auto
  also have "... = contour_integral q (\<lambda>w. 1 / (w - z))"
    apply (rule pi_eq)
    using p q loop
    by (auto simp: valid_path_polynomial_function norm_minus_commute intro!: holomorphic_intros)
  also have "... = 2 * complex_of_real pi * \<i> * winding_number \<gamma> z"
    using q by auto
  finally have "2 * complex_of_real pi * \<i> * n = 2 * complex_of_real pi * \<i> * winding_number \<gamma> z" .
  then show ?thesis
    by simp
qed

lemma winding_number_valid_path:
  assumes "valid_path \<gamma>" "z \<notin> path_image \<gamma>"
    shows "winding_number \<gamma> z = 1/(2*pi*ii) * contour_integral \<gamma> (\<lambda>w. 1/(w - z))"
  using assms by (auto simp: valid_path_imp_path intro!: winding_number_unique)

lemma has_contour_integral_winding_number:
  assumes \<gamma>: "valid_path \<gamma>" "z \<notin> path_image \<gamma>"
    shows "((\<lambda>w. 1/(w - z)) has_contour_integral (2*pi*ii*winding_number \<gamma> z)) \<gamma>"
by (simp add: winding_number_valid_path has_contour_integral_integral contour_integrable_inversediff assms)

lemma winding_number_trivial [simp]: "z \<noteq> a \<Longrightarrow> winding_number(linepath a a) z = 0"
  by (simp add: winding_number_valid_path)

lemma winding_number_subpath_trivial [simp]: "z \<noteq> g x \<Longrightarrow> winding_number (subpath x x g) z = 0"
  by (simp add: winding_number_valid_path)

lemma winding_number_join:
  assumes g1: "path g1" "z \<notin> path_image g1"
      and g2: "path g2" "z \<notin> path_image g2"
      and "pathfinish g1 = pathstart g2"
    shows "winding_number(g1 +++ g2) z = winding_number g1 z + winding_number g2 z"
  apply (rule winding_number_unique)
  using assms apply (simp_all add: not_in_path_image_join)
  apply (frule winding_number [OF g2])
  apply (frule winding_number [OF g1], clarify)
  apply (rename_tac p2 p1)
  apply (rule_tac x="p1+++p2" in exI)
  apply (simp add: not_in_path_image_join contour_integrable_inversediff algebra_simps)
  apply (auto simp: joinpaths_def)
  done

lemma winding_number_reversepath:
  assumes "path \<gamma>" "z \<notin> path_image \<gamma>"
    shows "winding_number(reversepath \<gamma>) z = - (winding_number \<gamma> z)"
  apply (rule winding_number_unique)
  using assms
  apply simp_all
  apply (frule winding_number [OF assms], clarify)
  apply (rule_tac x="reversepath p" in exI)
  apply (simp add: contour_integral_reversepath contour_integrable_inversediff valid_path_imp_reverse)
  apply (auto simp: reversepath_def)
  done

lemma winding_number_shiftpath:
  assumes \<gamma>: "path \<gamma>" "z \<notin> path_image \<gamma>"
      and "pathfinish \<gamma> = pathstart \<gamma>" "a \<in> {0..1}"
    shows "winding_number(shiftpath a \<gamma>) z = winding_number \<gamma> z"
  apply (rule winding_number_unique_loop)
  using assms
  apply (simp_all add: path_shiftpath path_image_shiftpath pathfinish_shiftpath pathstart_shiftpath)
  apply (frule winding_number [OF \<gamma>], clarify)
  apply (rule_tac x="shiftpath a p" in exI)
  apply (simp add: contour_integral_shiftpath path_image_shiftpath pathfinish_shiftpath pathstart_shiftpath valid_path_shiftpath)
  apply (auto simp: shiftpath_def)
  done

lemma winding_number_split_linepath:
  assumes "c \<in> closed_segment a b" "z \<notin> closed_segment a b"
    shows "winding_number(linepath a b) z = winding_number(linepath a c) z + winding_number(linepath c b) z"
proof -
  have "z \<notin> closed_segment a c" "z \<notin> closed_segment c b"
    using assms  apply (meson convex_contains_segment convex_segment ends_in_segment(1) subsetCE)
    using assms  by (meson convex_contains_segment convex_segment ends_in_segment(2) subsetCE)
  then show ?thesis
    using assms
    by (simp add: winding_number_valid_path contour_integral_split_linepath [symmetric] continuous_on_inversediff field_simps)
qed

lemma winding_number_cong:
   "(\<And>t. \<lbrakk>0 \<le> t; t \<le> 1\<rbrakk> \<Longrightarrow> p t = q t) \<Longrightarrow> winding_number p z = winding_number q z"
  by (simp add: winding_number_def pathstart_def pathfinish_def)

lemma winding_number_offset: "winding_number p z = winding_number (\<lambda>w. p w - z) 0"
  apply (simp add: winding_number_def contour_integral_integral path_image_def valid_path_def pathstart_def pathfinish_def)
  apply (intro ext arg_cong [where f = Eps] arg_cong [where f = All] imp_cong refl, safe)
  apply (rename_tac g)
  apply (rule_tac x="\<lambda>t. g t - z" in exI)
  apply (force simp: vector_derivative_def has_vector_derivative_diff_const piecewise_C1_differentiable_diff C1_differentiable_imp_piecewise)
  apply (rename_tac g)
  apply (rule_tac x="\<lambda>t. g t + z" in exI)
  apply (simp add: piecewise_C1_differentiable_add vector_derivative_def has_vector_derivative_add_const C1_differentiable_imp_piecewise)
  apply (force simp: algebra_simps)
  done

(* A combined theorem deducing several things piecewise.*)
lemma winding_number_join_pos_combined:
     "\<lbrakk>valid_path \<gamma>1; z \<notin> path_image \<gamma>1; 0 < Re(winding_number \<gamma>1 z);
       valid_path \<gamma>2; z \<notin> path_image \<gamma>2; 0 < Re(winding_number \<gamma>2 z); pathfinish \<gamma>1 = pathstart \<gamma>2\<rbrakk>
      \<Longrightarrow> valid_path(\<gamma>1 +++ \<gamma>2) \<and> z \<notin> path_image(\<gamma>1 +++ \<gamma>2) \<and> 0 < Re(winding_number(\<gamma>1 +++ \<gamma>2) z)"
  by (simp add: valid_path_join path_image_join winding_number_join valid_path_imp_path)


(* Useful sufficient conditions for the winding number to be positive etc.*)

lemma Re_winding_number:
    "\<lbrakk>valid_path \<gamma>; z \<notin> path_image \<gamma>\<rbrakk>
     \<Longrightarrow> Re(winding_number \<gamma> z) = Im(contour_integral \<gamma> (\<lambda>w. 1/(w - z))) / (2*pi)"
by (simp add: winding_number_valid_path field_simps Re_divide power2_eq_square)

lemma winding_number_pos_le:
  assumes \<gamma>: "valid_path \<gamma>" "z \<notin> path_image \<gamma>"
      and ge: "\<And>x. \<lbrakk>0 < x; x < 1\<rbrakk> \<Longrightarrow> 0 \<le> Im (vector_derivative \<gamma> (at x) * cnj(\<gamma> x - z))"
    shows "0 \<le> Re(winding_number \<gamma> z)"
proof -
  have *: "0 \<le> Im (vector_derivative \<gamma> (at x) / (\<gamma> x - z))" if x: "0 < x" "x < 1" for x
    using ge by (simp add: Complex.Im_divide algebra_simps x)
  show ?thesis
    apply (simp add: Re_winding_number [OF \<gamma>] field_simps)
    apply (rule has_integral_component_nonneg
             [of ii "\<lambda>x. if x \<in> {0<..<1}
                         then 1/(\<gamma> x - z) * vector_derivative \<gamma> (at x) else 0", simplified])
      prefer 3 apply (force simp: *)
     apply (simp add: Basis_complex_def)
    apply (rule has_integral_spike_interior [of 0 1 _ "\<lambda>x. 1/(\<gamma> x - z) * vector_derivative \<gamma> (at x)"])
    apply simp
    apply (simp only: box_real)
    apply (subst has_contour_integral [symmetric])
    using \<gamma>
    apply (simp add: contour_integrable_inversediff has_contour_integral_integral)
    done
qed

lemma winding_number_pos_lt_lemma:
  assumes \<gamma>: "valid_path \<gamma>" "z \<notin> path_image \<gamma>"
      and e: "0 < e"
      and ge: "\<And>x. \<lbrakk>0 < x; x < 1\<rbrakk> \<Longrightarrow> e \<le> Im (vector_derivative \<gamma> (at x) / (\<gamma> x - z))"
    shows "0 < Re(winding_number \<gamma> z)"
proof -
  have "e \<le> Im (contour_integral \<gamma> (\<lambda>w. 1 / (w - z)))"
    apply (rule has_integral_component_le
             [of ii "\<lambda>x. ii*e" "ii*e" "{0..1}"
                    "\<lambda>x. if x \<in> {0<..<1} then 1/(\<gamma> x - z) * vector_derivative \<gamma> (at x) else ii*e"
                    "contour_integral \<gamma> (\<lambda>w. 1/(w - z))", simplified])
    using e
    apply (simp_all add: Basis_complex_def)
    using has_integral_const_real [of _ 0 1] apply force
    apply (rule has_integral_spike_interior [of 0 1 _ "\<lambda>x. 1/(\<gamma> x - z) * vector_derivative \<gamma> (at x)", simplified box_real])
    apply simp
    apply (subst has_contour_integral [symmetric])
    using \<gamma>
    apply (simp_all add: contour_integrable_inversediff has_contour_integral_integral ge)
    done
  with e show ?thesis
    by (simp add: Re_winding_number [OF \<gamma>] field_simps)
qed

lemma winding_number_pos_lt:
  assumes \<gamma>: "valid_path \<gamma>" "z \<notin> path_image \<gamma>"
      and e: "0 < e"
      and ge: "\<And>x. \<lbrakk>0 < x; x < 1\<rbrakk> \<Longrightarrow> e \<le> Im (vector_derivative \<gamma> (at x) * cnj(\<gamma> x - z))"
    shows "0 < Re (winding_number \<gamma> z)"
proof -
  have bm: "bounded ((\<lambda>w. w - z) ` (path_image \<gamma>))"
    using bounded_translation [of _ "-z"] \<gamma> by (simp add: bounded_valid_path_image)
  then obtain B where B: "B > 0" and Bno: "\<And>x. x \<in> (\<lambda>w. w - z) ` (path_image \<gamma>) \<Longrightarrow> norm x \<le> B"
    using bounded_pos [THEN iffD1, OF bm] by blast
  { fix x::real  assume x: "0 < x" "x < 1"
    then have B2: "cmod (\<gamma> x - z)^2 \<le> B^2" using Bno [of "\<gamma> x - z"]
      by (simp add: path_image_def power2_eq_square mult_mono')
    with x have "\<gamma> x \<noteq> z" using \<gamma>
      using path_image_def by fastforce
    then have "e / B\<^sup>2 \<le> Im (vector_derivative \<gamma> (at x) * cnj (\<gamma> x - z)) / (cmod (\<gamma> x - z))\<^sup>2"
      using B ge [OF x] B2 e
      apply (rule_tac y="e / (cmod (\<gamma> x - z))\<^sup>2" in order_trans)
      apply (auto simp: divide_left_mono divide_right_mono)
      done
    then have "e / B\<^sup>2 \<le> Im (vector_derivative \<gamma> (at x) / (\<gamma> x - z))"
      by (simp add: Im_divide_Reals complex_div_cnj [of _ "\<gamma> x - z" for x] del: complex_cnj_diff times_complex.sel)
  } note * = this
  show ?thesis
    using e B by (simp add: * winding_number_pos_lt_lemma [OF \<gamma>, of "e/B^2"])
qed

subsection\<open>The winding number is an integer\<close>

text\<open>Proof from the book Complex Analysis by Lars V. Ahlfors, Chapter 4, section 2.1,
     Also on page 134 of Serge Lang's book with the name title, etc.\<close>

lemma exp_fg:
  fixes z::complex
  assumes g: "(g has_vector_derivative g') (at x within s)"
      and f: "(f has_vector_derivative (g' / (g x - z))) (at x within s)"
      and z: "g x \<noteq> z"
    shows "((\<lambda>x. exp(-f x) * (g x - z)) has_vector_derivative 0) (at x within s)"
proof -
  have *: "(exp o (\<lambda>x. (- f x)) has_vector_derivative - (g' / (g x - z)) * exp (- f x)) (at x within s)"
    using assms unfolding has_vector_derivative_def scaleR_conv_of_real
    by (auto intro!: derivative_eq_intros)
  show ?thesis
    apply (rule has_vector_derivative_eq_rhs)
    apply (rule bounded_bilinear.has_vector_derivative [OF bounded_bilinear_mult])
    using z
    apply (auto simp: intro!: derivative_eq_intros * [unfolded o_def] g)
    done
qed

lemma winding_number_exp_integral:
  fixes z::complex
  assumes \<gamma>: "\<gamma> piecewise_C1_differentiable_on {a..b}"
      and ab: "a \<le> b"
      and z: "z \<notin> \<gamma> ` {a..b}"
    shows "(\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z)) integrable_on {a..b}"
          (is "?thesis1")
          "exp (- (integral {a..b} (\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z)))) * (\<gamma> b - z) = \<gamma> a - z"
          (is "?thesis2")
proof -
  let ?D\<gamma> = "\<lambda>x. vector_derivative \<gamma> (at x)"
  have [simp]: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> \<gamma> x \<noteq> z"
    using z by force
  have cong: "continuous_on {a..b} \<gamma>"
    using \<gamma> by (simp add: piecewise_C1_differentiable_on_def)
  obtain k where fink: "finite k" and g_C1_diff: "\<gamma> C1_differentiable_on ({a..b} - k)"
    using \<gamma> by (force simp: piecewise_C1_differentiable_on_def)
  have o: "open ({a<..<b} - k)"
    using `finite k` by (simp add: finite_imp_closed open_Diff)
  moreover have "{a<..<b} - k \<subseteq> {a..b} - k"
    by force
  ultimately have g_diff_at: "\<And>x. \<lbrakk>x \<notin> k; x \<in> {a<..<b}\<rbrakk> \<Longrightarrow> \<gamma> differentiable at x"
    by (metis Diff_iff differentiable_on_subset C1_diff_imp_diff [OF g_C1_diff] differentiable_on_def differentiable_within_open)
  { fix w
    assume "w \<noteq> z"
    have "continuous_on (ball w (cmod (w - z))) (\<lambda>w. 1 / (w - z))"
      by (auto simp: dist_norm intro!: continuous_intros)
    moreover have "\<And>x. cmod (w - x) < cmod (w - z) \<Longrightarrow> \<exists>f'. ((\<lambda>w. 1 / (w - z)) has_field_derivative f') (at x)"
      by (auto simp: intro!: derivative_eq_intros)
    ultimately have "\<exists>h. \<forall>y. norm(y - w) < norm(w - z) \<longrightarrow> (h has_field_derivative 1/(y - z)) (at y)"
      using holomorphic_convex_primitive [of "ball w (norm(w - z))" "{}" "\<lambda>w. 1/(w - z)"]
      by (simp add: complex_differentiable_def Ball_def dist_norm at_within_open_NO_MATCH norm_minus_commute)
  }
  then obtain h where h: "\<And>w y. w \<noteq> z \<Longrightarrow> norm(y - w) < norm(w - z) \<Longrightarrow> (h w has_field_derivative 1/(y - z)) (at y)"
    by meson
  have exy: "\<exists>y. ((\<lambda>x. inverse (\<gamma> x - z) * ?D\<gamma> x) has_integral y) {a..b}"
    unfolding integrable_on_def [symmetric]
    apply (rule contour_integral_local_primitive_any [OF piecewise_C1_imp_differentiable [OF \<gamma>], of "-{z}"])
    apply (rename_tac w)
    apply (rule_tac x="norm(w - z)" in exI)
    apply (simp_all add: inverse_eq_divide)
    apply (metis has_field_derivative_at_within h)
    done
  have vg_int: "(\<lambda>x. ?D\<gamma> x / (\<gamma> x - z)) integrable_on {a..b}"
    unfolding box_real [symmetric] divide_inverse_commute
    by (auto intro!: exy integrable_subinterval simp add: integrable_on_def ab)
  with ab show ?thesis1
    by (simp add: divide_inverse_commute integral_def integrable_on_def)
  { fix t
    assume t: "t \<in> {a..b}"
    have cball: "continuous_on (ball (\<gamma> t) (dist (\<gamma> t) z)) (\<lambda>x. inverse (x - z))"
        using z by (auto intro!: continuous_intros simp: dist_norm)
    have icd: "\<And>x. cmod (\<gamma> t - x) < cmod (\<gamma> t - z) \<Longrightarrow> (\<lambda>w. inverse (w - z)) complex_differentiable at x"
      unfolding complex_differentiable_def by (force simp: intro!: derivative_eq_intros)
    obtain h where h: "\<And>x. cmod (\<gamma> t - x) < cmod (\<gamma> t - z) \<Longrightarrow>
                       (h has_field_derivative inverse (x - z)) (at x within {y. cmod (\<gamma> t - y) < cmod (\<gamma> t - z)})"
      using holomorphic_convex_primitive [where f = "\<lambda>w. inverse(w - z)", OF convex_ball finite.emptyI cball icd]
      by simp (auto simp: ball_def dist_norm that)
    { fix x D
      assume x: "x \<notin> k" "a < x" "x < b"
      then have "x \<in> interior ({a..b} - k)"
        using open_subset_interior [OF o] by fastforce
      then have con: "isCont (\<lambda>x. ?D\<gamma> x) x"
        using g_C1_diff x by (auto simp: C1_differentiable_on_eq intro: continuous_on_interior)
      then have con_vd: "continuous (at x within {a..b}) (\<lambda>x. ?D\<gamma> x)"
        by (rule continuous_at_imp_continuous_within)
      have gdx: "\<gamma> differentiable at x"
        using x by (simp add: g_diff_at)
      have "((\<lambda>c. Exp (- integral {a..c} (\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z))) * (\<gamma> c - z)) has_derivative (\<lambda>h. 0))
          (at x within {a..b})"
        using x gdx t
        apply (clarsimp simp add: differentiable_iff_scaleR)
        apply (rule exp_fg [unfolded has_vector_derivative_def, simplified], blast intro: has_derivative_at_within)
        apply (simp_all add: has_vector_derivative_def [symmetric])
        apply (rule has_vector_derivative_eq_rhs [OF integral_has_vector_derivative_continuous_at])
        apply (rule con_vd continuous_intros cong vg_int | simp add: continuous_at_imp_continuous_within has_vector_derivative_continuous vector_derivative_at)+
        done
      } note * = this
    have "exp (- (integral {a..t} (\<lambda>x. ?D\<gamma> x / (\<gamma> x - z)))) * (\<gamma> t - z) =\<gamma> a - z"
      apply (rule has_derivative_zero_unique_strong_interval [of "{a,b} \<union> k" a b])
      using t
      apply (auto intro!: * continuous_intros fink cong indefinite_integral_continuous [OF vg_int]  simp add: ab)+
      done
   }
  with ab show ?thesis2
    by (simp add: divide_inverse_commute integral_def)
qed

corollary winding_number_exp_2pi:
    "\<lbrakk>path p; z \<notin> path_image p\<rbrakk>
     \<Longrightarrow> pathfinish p - z = exp (2 * pi * ii * winding_number p z) * (pathstart p - z)"
using winding_number [of p z 1] unfolding valid_path_def path_image_def pathstart_def pathfinish_def
  by (force dest: winding_number_exp_integral(2) [of _ 0 1 z] simp: field_simps contour_integral_integral exp_minus)


subsection\<open>The version with complex integers and equality\<close>

lemma integer_winding_number_eq:
  assumes \<gamma>: "path \<gamma>" and z: "z \<notin> path_image \<gamma>"
  shows "winding_number \<gamma> z \<in> \<int> \<longleftrightarrow> pathfinish \<gamma> = pathstart \<gamma>"
proof -
  have *: "\<And>i::complex. \<And>g0 g1. \<lbrakk>i \<noteq> 0; g0 \<noteq> z; (g1 - z) / i = g0 - z\<rbrakk> \<Longrightarrow> (i = 1 \<longleftrightarrow> g1 = g0)"
      by (simp add: field_simps) algebra
  obtain p where p: "valid_path p" "z \<notin> path_image p"
                    "pathstart p = pathstart \<gamma>" "pathfinish p = pathfinish \<gamma>"
                    "contour_integral p (\<lambda>w. 1 / (w - z)) = complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z"
    using winding_number [OF assms, of 1] by auto
  have [simp]: "(winding_number \<gamma> z \<in> \<int>) = (Exp (contour_integral p (\<lambda>w. 1 / (w - z))) = 1)"
      using p by (simp add: exp_eq_1 complex_is_Int_iff)
  have "winding_number p z \<in> \<int> \<longleftrightarrow> pathfinish p = pathstart p"
    using p z
    apply (simp add: winding_number_valid_path valid_path_def path_image_def pathstart_def pathfinish_def)
    using winding_number_exp_integral(2) [of p 0 1 z]
    apply (simp add: field_simps contour_integral_integral exp_minus)
    apply (rule *)
    apply (auto simp: path_image_def field_simps)
    done
  then show ?thesis using p
    by (auto simp: winding_number_valid_path)
qed

theorem integer_winding_number:
  "\<lbrakk>path \<gamma>; pathfinish \<gamma> = pathstart \<gamma>; z \<notin> path_image \<gamma>\<rbrakk> \<Longrightarrow> winding_number \<gamma> z \<in> \<int>"
by (metis integer_winding_number_eq)


text\<open>If the winding number's magnitude is at least one, then the path must contain points in every direction.*)
   We can thus bound the winding number of a path that doesn't intersect a given ray. \<close>

lemma winding_number_pos_meets:
  fixes z::complex
  assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and 1: "Re (winding_number \<gamma> z) \<ge> 1"
      and w: "w \<noteq> z"
  shows "\<exists>a::real. 0 < a \<and> z + a*(w - z) \<in> path_image \<gamma>"
proof -
  have [simp]: "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> \<gamma> x \<noteq> z"
    using z by (auto simp: path_image_def)
  have [simp]: "z \<notin> \<gamma> ` {0..1}"
    using path_image_def z by auto
  have gpd: "\<gamma> piecewise_C1_differentiable_on {0..1}"
    using \<gamma> valid_path_def by blast
  def r \<equiv> "(w - z) / (\<gamma> 0 - z)"
  have [simp]: "r \<noteq> 0"
    using w z by (auto simp: r_def)
  have "Arg r \<le> 2*pi"
    by (simp add: Arg less_eq_real_def)
  also have "... \<le> Im (integral {0..1} (\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z)))"
    using 1
    apply (simp add: winding_number_valid_path [OF \<gamma> z] Cauchy_Integral_Thm.contour_integral_integral)
    apply (simp add: Complex.Re_divide field_simps power2_eq_square)
    done
  finally have "Arg r \<le> Im (integral {0..1} (\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z)))" .
  then have "\<exists>t. t \<in> {0..1} \<and> Im(integral {0..t} (\<lambda>x. vector_derivative \<gamma> (at x)/(\<gamma> x - z))) = Arg r"
    apply (simp add:)
    apply (rule Topological_Spaces.IVT')
    apply (simp_all add: Complex_Transcendental.Arg_ge_0)
    apply (intro continuous_intros indefinite_integral_continuous winding_number_exp_integral [OF gpd]; simp)
    done
  then obtain t where t:     "t \<in> {0..1}"
                  and eqArg: "Im (integral {0..t} (\<lambda>x. vector_derivative \<gamma> (at x)/(\<gamma> x - z))) = Arg r"
    by blast
  def i \<equiv> "integral {0..t} (\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z))"
  have iArg: "Arg r = Im i"
    using eqArg by (simp add: i_def)
  have gpdt: "\<gamma> piecewise_C1_differentiable_on {0..t}"
    by (metis atLeastAtMost_iff atLeastatMost_subset_iff order_refl piecewise_C1_differentiable_on_subset gpd t)
  have "Exp (- i) * (\<gamma> t - z) = \<gamma> 0 - z"
    unfolding i_def
    apply (rule winding_number_exp_integral [OF gpdt])
    using t z unfolding path_image_def
    apply force+
    done
  then have *: "\<gamma> t - z = exp i * (\<gamma> 0 - z)"
    by (simp add: exp_minus field_simps)
  then have "(w - z) = r * (\<gamma> 0 - z)"
    by (simp add: r_def)
  then have "z + complex_of_real (exp (Re i)) * (w - z) / complex_of_real (cmod r) = \<gamma> t"
    apply (simp add:)
    apply (subst Complex_Transcendental.Arg_eq [of r])
    apply (simp add: iArg)
    using *
    apply (simp add: Exp_eq_polar field_simps)
    done
  with t show ?thesis
    by (rule_tac x="exp(Re i) / norm r" in exI) (auto simp: path_image_def)
qed

lemma winding_number_big_meets:
  fixes z::complex
  assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and "abs (Re (winding_number \<gamma> z)) \<ge> 1"
      and w: "w \<noteq> z"
  shows "\<exists>a::real. 0 < a \<and> z + a*(w - z) \<in> path_image \<gamma>"
proof -
  { assume "Re (winding_number \<gamma> z) \<le> - 1"
    then have "Re (winding_number (reversepath \<gamma>) z) \<ge> 1"
      by (simp add: \<gamma> valid_path_imp_path winding_number_reversepath z)
    moreover have "valid_path (reversepath \<gamma>)"
      using \<gamma> valid_path_imp_reverse by auto
    moreover have "z \<notin> path_image (reversepath \<gamma>)"
      by (simp add: z)
    ultimately have "\<exists>a::real. 0 < a \<and> z + a*(w - z) \<in> path_image (reversepath \<gamma>)"
      using winding_number_pos_meets w by blast
    then have ?thesis
      by simp
  }
  then show ?thesis
    using assms
    by (simp add: Groups.abs_if_class.abs_if winding_number_pos_meets split: split_if_asm)
qed

lemma winding_number_less_1:
  fixes z::complex
  shows
  "\<lbrakk>valid_path \<gamma>; z \<notin> path_image \<gamma>; w \<noteq> z;
    \<And>a::real. 0 < a \<Longrightarrow> z + a*(w - z) \<notin> path_image \<gamma>\<rbrakk>
   \<Longrightarrow> abs (Re(winding_number \<gamma> z)) < 1"
   by (auto simp: not_less dest: winding_number_big_meets)

text\<open>One way of proving that WN=1 for a loop.\<close>
lemma winding_number_eq_1:
  fixes z::complex
  assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
      and 0: "0 < Re(winding_number \<gamma> z)" and 2: "Re(winding_number \<gamma> z) < 2"
  shows "winding_number \<gamma> z = 1"
proof -
  have "winding_number \<gamma> z \<in> Ints"
    by (simp add: \<gamma> integer_winding_number loop valid_path_imp_path z)
  then show ?thesis
    using 0 2 by (auto simp: Ints_def)
qed


subsection\<open>Continuity of winding number and invariance on connected sets.\<close>

lemma continuous_at_winding_number:
  fixes z::complex
  assumes \<gamma>: "path \<gamma>" and z: "z \<notin> path_image \<gamma>"
  shows "continuous (at z) (winding_number \<gamma>)"
proof -
  obtain e where "e>0" and cbg: "cball z e \<subseteq> - path_image \<gamma>"
    using open_contains_cball [of "- path_image \<gamma>"]  z
    by (force simp: closed_def [symmetric] closed_path_image [OF \<gamma>])
  then have ppag: "path_image \<gamma> \<subseteq> - cball z (e/2)"
    by (force simp: cball_def dist_norm)
  have oc: "open (- cball z (e / 2))"
    by (simp add: closed_def [symmetric])
  obtain d where "d>0" and pi_eq:
    "\<And>h1 h2. \<lbrakk>valid_path h1; valid_path h2;
              (\<forall>t\<in>{0..1}. cmod (h1 t - \<gamma> t) < d \<and> cmod (h2 t - \<gamma> t) < d);
              pathstart h2 = pathstart h1; pathfinish h2 = pathfinish h1\<rbrakk>
             \<Longrightarrow>
               path_image h1 \<subseteq> - cball z (e / 2) \<and>
               path_image h2 \<subseteq> - cball z (e / 2) \<and>
               (\<forall>f. f holomorphic_on - cball z (e / 2) \<longrightarrow> contour_integral h2 f = contour_integral h1 f)"
    using contour_integral_nearby_ends [OF oc \<gamma> ppag] by metis
  obtain p where p: "valid_path p" "z \<notin> path_image p"
                    "pathstart p = pathstart \<gamma> \<and> pathfinish p = pathfinish \<gamma>"
              and pg: "\<And>t. t\<in>{0..1} \<Longrightarrow> cmod (\<gamma> t - p t) < min d e / 2"
              and pi: "contour_integral p (\<lambda>x. 1 / (x - z)) = complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z"
    using winding_number [OF \<gamma> z, of "min d e / 2"] `d>0` `e>0` by auto
  { fix w
    assume d2: "cmod (w - z) < d/2" and e2: "cmod (w - z) < e/2"
    then have wnotp: "w \<notin> path_image p"
      using cbg `d>0` `e>0`
      apply (simp add: path_image_def cball_def dist_norm, clarify)
      apply (frule pg)
      apply (drule_tac c="\<gamma> x" in subsetD)
      apply (auto simp: less_eq_real_def norm_minus_commute norm_triangle_half_l)
      done
    have wnotg: "w \<notin> path_image \<gamma>"
      using cbg e2 `e>0` by (force simp: dist_norm norm_minus_commute)
    { fix k::real
      assume k: "k>0"
      then obtain q where q: "valid_path q" "w \<notin> path_image q"
                             "pathstart q = pathstart \<gamma> \<and> pathfinish q = pathfinish \<gamma>"
                    and qg: "\<And>t. t \<in> {0..1} \<Longrightarrow> cmod (\<gamma> t - q t) < min k (min d e) / 2"
                    and qi: "contour_integral q (\<lambda>u. 1 / (u - w)) = complex_of_real (2 * pi) * \<i> * winding_number \<gamma> w"
        using winding_number [OF \<gamma> wnotg, of "min k (min d e) / 2"] `d>0` `e>0` k
        by (force simp: min_divide_distrib_right)
      have "contour_integral p (\<lambda>u. 1 / (u - w)) = contour_integral q (\<lambda>u. 1 / (u - w))"
        apply (rule pi_eq [OF `valid_path q` `valid_path p`, THEN conjunct2, THEN conjunct2, rule_format])
        apply (frule pg)
        apply (frule qg)
        using p q `d>0` e2
        apply (auto simp: dist_norm norm_minus_commute intro!: holomorphic_intros)
        done
      then have "contour_integral p (\<lambda>x. 1 / (x - w)) = complex_of_real (2 * pi) * \<i> * winding_number \<gamma> w"
        by (simp add: pi qi)
    } note pip = this
    have "path p"
      using p by (simp add: valid_path_imp_path)
    then have "winding_number p w = winding_number \<gamma> w"
      apply (rule winding_number_unique [OF _ wnotp])
      apply (rule_tac x=p in exI)
      apply (simp add: p wnotp min_divide_distrib_right pip)
      done
  } note wnwn = this
  obtain pe where "pe>0" and cbp: "cball z (3 / 4 * pe) \<subseteq> - path_image p"
    using p open_contains_cball [of "- path_image p"]
    by (force simp: closed_def [symmetric] closed_path_image [OF valid_path_imp_path])
  obtain L
    where "L>0"
      and L: "\<And>f B. \<lbrakk>f holomorphic_on - cball z (3 / 4 * pe);
                      \<forall>z \<in> - cball z (3 / 4 * pe). cmod (f z) \<le> B\<rbrakk> \<Longrightarrow>
                      cmod (contour_integral p f) \<le> L * B"
    using contour_integral_bound_exists [of "- cball z (3/4*pe)" p] cbp `valid_path p` by force
  { fix e::real and w::complex
    assume e: "0 < e" and w: "cmod (w - z) < pe/4" "cmod (w - z) < e * pe\<^sup>2 / (8 * L)"
    then have [simp]: "w \<notin> path_image p"
      using cbp p(2) `0 < pe`
      by (force simp: dist_norm norm_minus_commute path_image_def cball_def)
    have [simp]: "contour_integral p (\<lambda>x. 1/(x - w)) - contour_integral p (\<lambda>x. 1/(x - z)) =
                  contour_integral p (\<lambda>x. 1/(x - w) - 1/(x - z))"
      by (simp add: p contour_integrable_inversediff contour_integral_diff)
    { fix x
      assume pe: "3/4 * pe < cmod (z - x)"
      have "cmod (w - x) < pe/4 + cmod (z - x)"
        by (meson add_less_cancel_right norm_diff_triangle_le order_refl order_trans_rules(21) w(1))
      then have wx: "cmod (w - x) < 4/3 * cmod (z - x)" using pe by simp
      have "cmod (z - x) \<le> cmod (z - w) + cmod (w - x)"
        using norm_diff_triangle_le by blast
      also have "... < pe/4 + cmod (w - x)"
        using w by (simp add: norm_minus_commute)
      finally have "pe/2 < cmod (w - x)"
        using pe by auto
      then have "(pe/2)^2 < cmod (w - x) ^ 2"
        apply (rule power_strict_mono)
        using `pe>0` by auto
      then have pe2: "pe^2 < 4 * cmod (w - x) ^ 2"
        by (simp add: power_divide)
      have "8 * L * cmod (w - z) < e * pe\<^sup>2"
        using w `L>0` by (simp add: field_simps)
      also have "... < e * 4 * cmod (w - x) * cmod (w - x)"
        using pe2 `e>0` by (simp add: power2_eq_square)
      also have "... < e * 4 * cmod (w - x) * (4/3 * cmod (z - x))"
        using wx
        apply (rule mult_strict_left_mono)
        using pe2 e not_less_iff_gr_or_eq by fastforce
      finally have "L * cmod (w - z) < 2/3 * e * cmod (w - x) * cmod (z - x)"
        by simp
      also have "... \<le> e * cmod (w - x) * cmod (z - x)"
         using e by simp
      finally have Lwz: "L * cmod (w - z) < e * cmod (w - x) * cmod (z - x)" .
      have "L * cmod (1 / (x - w) - 1 / (x - z)) \<le> e"
        apply (cases "x=z \<or> x=w")
        using pe `pe>0` w `L>0`
        apply (force simp: norm_minus_commute)
        using wx w(2) `L>0` pe pe2 Lwz
        apply (auto simp: divide_simps mult_less_0_iff norm_minus_commute norm_divide norm_mult power2_eq_square)
        done
    } note L_cmod_le = this
    have *: "cmod (contour_integral p (\<lambda>x. 1 / (x - w) - 1 / (x - z))) \<le> L * (e * pe\<^sup>2 / L / 4 * (inverse (pe / 2))\<^sup>2)"
      apply (rule L)
      using `pe>0` w
      apply (force simp: dist_norm norm_minus_commute intro!: holomorphic_intros)
      using `pe>0` w `L>0`
      apply (auto simp: cball_def dist_norm field_simps L_cmod_le  simp del: less_divide_eq_numeral1 le_divide_eq_numeral1)
      done
    have "cmod (contour_integral p (\<lambda>x. 1 / (x - w)) - contour_integral p (\<lambda>x. 1 / (x - z))) < 2*e"
      apply (simp add:)
      apply (rule le_less_trans [OF *])
      using `L>0` e
      apply (force simp: field_simps)
      done
    then have "cmod (winding_number p w - winding_number p z) < e"
      using pi_ge_two e
      by (force simp: winding_number_valid_path p field_simps norm_divide norm_mult intro: less_le_trans)
  } note cmod_wn_diff = this
  show ?thesis
    apply (rule continuous_transform_at [of "min d e / 2" _ "winding_number p"])
    apply (auto simp: `d>0` `e>0` dist_norm wnwn simp del: less_divide_eq_numeral1)
    apply (simp add: continuous_at_eps_delta, clarify)
    apply (rule_tac x="min (pe/4) (e/2*pe^2/L/4)" in exI)
    using `pe>0` `L>0`
    apply (simp add: dist_norm cmod_wn_diff)
    done
qed

corollary continuous_on_winding_number:
    "path \<gamma> \<Longrightarrow> continuous_on (- path_image \<gamma>) (\<lambda>w. winding_number \<gamma> w)"
  by (simp add: continuous_at_imp_continuous_on continuous_at_winding_number)


subsection{*The winding number is constant on a connected region*}

lemma winding_number_constant:
  assumes \<gamma>: "path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>" and cs: "connected s" and sg: "s \<inter> path_image \<gamma> = {}"
    shows "\<exists>k. \<forall>z \<in> s. winding_number \<gamma> z = k"
proof -
  { fix y z
    assume ne: "winding_number \<gamma> y \<noteq> winding_number \<gamma> z"
    assume "y \<in> s" "z \<in> s"
    then have "winding_number \<gamma> y \<in> \<int>"  "winding_number \<gamma> z \<in>  \<int>"
      using integer_winding_number [OF \<gamma> loop] sg `y \<in> s` by auto
    with ne have "1 \<le> cmod (winding_number \<gamma> y - winding_number \<gamma> z)"
      by (auto simp: Ints_def of_int_diff [symmetric] simp del: of_int_diff)
  } note * = this
  show ?thesis
    apply (rule continuous_discrete_range_constant [OF cs])
    using continuous_on_winding_number [OF \<gamma>] sg
    apply (metis Diff_Compl Diff_eq_empty_iff continuous_on_subset)
    apply (rule_tac x=1 in exI)
    apply (auto simp: *)
    done
qed

lemma winding_number_eq:
     "\<lbrakk>path \<gamma>; pathfinish \<gamma> = pathstart \<gamma>; w \<in> s; z \<in> s; connected s; s \<inter> path_image \<gamma> = {}\<rbrakk>
      \<Longrightarrow> winding_number \<gamma> w = winding_number \<gamma> z"
using winding_number_constant by fastforce

lemma open_winding_number_levelsets:
  assumes \<gamma>: "path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
    shows "open {z. z \<notin> path_image \<gamma> \<and> winding_number \<gamma> z = k}"
proof -
  have op: "open (- path_image \<gamma>)"
    by (simp add: closed_path_image \<gamma> open_Compl)
  { fix z assume z: "z \<notin> path_image \<gamma>" and k: "k = winding_number \<gamma> z"
    obtain e where e: "e>0" "ball z e \<subseteq> - path_image \<gamma>"
      using open_contains_ball [of "- path_image \<gamma>"] op z
      by blast
    have "\<exists>e>0. \<forall>y. dist y z < e \<longrightarrow> y \<notin> path_image \<gamma> \<and> winding_number \<gamma> y = winding_number \<gamma> z"
      apply (rule_tac x=e in exI)
      using e apply (simp add: dist_norm ball_def norm_minus_commute)
      apply (auto simp: dist_norm norm_minus_commute intro!: winding_number_eq [OF assms, where s = "ball z e"])
      done
  } then
  show ?thesis
    by (auto simp: Complex.open_complex_def)
qed

subsection\<open>Winding number is zero "outside" a curve, in various senses\<close>

lemma winding_number_zero_in_outside:
  assumes \<gamma>: "path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>" and z: "z \<in> outside (path_image \<gamma>)"
    shows "winding_number \<gamma> z = 0"
proof -
  obtain B::real where "0 < B" and B: "path_image \<gamma> \<subseteq> ball 0 B"
    using bounded_subset_ballD [OF bounded_path_image [OF \<gamma>]] by auto
  obtain w::complex where w: "w \<notin> ball 0 (B + 1)"
    by (metis abs_of_nonneg le_less less_irrefl mem_ball_0 norm_of_real)
  have "- ball 0 (B + 1) \<subseteq> outside (path_image \<gamma>)"
    apply (rule outside_subset_convex)
    using B subset_ball by auto
  then have wout: "w \<in> outside (path_image \<gamma>)"
    using w by blast
  moreover obtain k where "\<And>z. z \<in> outside (path_image \<gamma>) \<Longrightarrow> winding_number \<gamma> z = k"
    using winding_number_constant [OF \<gamma> loop, of "outside(path_image \<gamma>)"] connected_outside
    by (metis DIM_complex bounded_path_image dual_order.refl \<gamma> outside_no_overlap)
  ultimately have "winding_number \<gamma> z = winding_number \<gamma> w"
    using z by blast
  also have "... = 0"
  proof -
    have wnot: "w \<notin> path_image \<gamma>"  using wout by (simp add: outside_def)
    { fix e::real assume "0<e"
      obtain p where p: "polynomial_function p" "pathstart p = pathstart \<gamma>" "pathfinish p = pathfinish \<gamma>"
                 and pg1: "(\<And>t. \<lbrakk>0 \<le> t; t \<le> 1\<rbrakk> \<Longrightarrow> cmod (p t - \<gamma> t) < 1)"
                 and pge: "(\<And>t. \<lbrakk>0 \<le> t; t \<le> 1\<rbrakk> \<Longrightarrow> cmod (p t - \<gamma> t) < e)"
        using path_approx_polynomial_function [OF \<gamma>, of "min 1 e"] `e>0` by force
      have pip: "path_image p \<subseteq> ball 0 (B + 1)"
        using B
        apply (clarsimp simp add: path_image_def dist_norm ball_def)
        apply (frule (1) pg1)
        apply (fastforce dest: norm_add_less)
        done
      then have "w \<notin> path_image p"  using w by blast
      then have "\<exists>p. valid_path p \<and> w \<notin> path_image p \<and>
                     pathstart p = pathstart \<gamma> \<and> pathfinish p = pathfinish \<gamma> \<and>
                     (\<forall>t\<in>{0..1}. cmod (\<gamma> t - p t) < e) \<and> contour_integral p (\<lambda>wa. 1 / (wa - w)) = 0"
        apply (rule_tac x=p in exI)
        apply (simp add: p valid_path_polynomial_function)
        apply (intro conjI)
        using pge apply (simp add: norm_minus_commute)
        apply (rule contour_integral_unique [OF Cauchy_theorem_convex_simple [OF _ convex_ball [of 0 "B+1"]]])
        apply (rule holomorphic_intros | simp add: dist_norm)+
        using mem_ball_0 w apply blast
        using p apply (simp_all add: valid_path_polynomial_function loop pip)
        done
    }
    then show ?thesis
      by (auto intro: winding_number_unique [OF \<gamma>] simp add: wnot)
  qed
  finally show ?thesis .
qed

lemma winding_number_zero_outside:
    "\<lbrakk>path \<gamma>; convex s; pathfinish \<gamma> = pathstart \<gamma>; z \<notin> s; path_image \<gamma> \<subseteq> s\<rbrakk> \<Longrightarrow> winding_number \<gamma> z = 0"
  by (meson convex_in_outside outside_mono subsetCE winding_number_zero_in_outside)

lemma winding_number_zero_at_infinity:
  assumes \<gamma>: "path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
    shows "\<exists>B. \<forall>z. B \<le> norm z \<longrightarrow> winding_number \<gamma> z = 0"
proof -
  obtain B::real where "0 < B" and B: "path_image \<gamma> \<subseteq> ball 0 B"
    using bounded_subset_ballD [OF bounded_path_image [OF \<gamma>]] by auto
  then show ?thesis
    apply (rule_tac x="B+1" in exI, clarify)
    apply (rule winding_number_zero_outside [OF \<gamma> convex_cball [of 0 B] loop])
    apply (meson less_add_one mem_cball_0 not_le order_trans)
    using ball_subset_cball by blast
qed

lemma winding_number_zero_point:
    "\<lbrakk>path \<gamma>; convex s; pathfinish \<gamma> = pathstart \<gamma>; open s; path_image \<gamma> \<subseteq> s\<rbrakk>
     \<Longrightarrow> \<exists>z. z \<in> s \<and> winding_number \<gamma> z = 0"
  using outside_compact_in_open [of "path_image \<gamma>" s] path_image_nonempty winding_number_zero_in_outside
  by (fastforce simp add: compact_path_image)


text\<open>If a path winds round a set, it winds rounds its inside.\<close>
lemma winding_number_around_inside:
  assumes \<gamma>: "path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
      and cls: "closed s" and cos: "connected s" and s_disj: "s \<inter> path_image \<gamma> = {}"
      and z: "z \<in> s" and wn_nz: "winding_number \<gamma> z \<noteq> 0" and w: "w \<in> s \<union> inside s"
    shows "winding_number \<gamma> w = winding_number \<gamma> z"
proof -
  have ssb: "s \<subseteq> inside(path_image \<gamma>)"
  proof
    fix x :: complex
    assume "x \<in> s"
    hence "x \<notin> path_image \<gamma>"
      by (meson disjoint_iff_not_equal s_disj)
    thus "x \<in> inside (path_image \<gamma>)"
      using `x \<in> s` by (metis (no_types) ComplI UnE cos \<gamma> loop s_disj union_with_outside winding_number_eq winding_number_zero_in_outside wn_nz z)
qed
  show ?thesis
    apply (rule winding_number_eq [OF \<gamma> loop w])
    using z apply blast
    apply (simp add: cls connected_with_inside cos)
    apply (simp add: Int_Un_distrib2 s_disj, safe)
    by (meson ssb inside_inside_compact_connected [OF cls, of "path_image \<gamma>"] compact_path_image connected_path_image contra_subsetD disjoint_iff_not_equal \<gamma> inside_no_overlap)
 qed


text\<open>Bounding a WN by 1/2 for a path and point in opposite halfspaces.\<close>
lemma winding_number_subpath_continuous:
  assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>"
    shows "continuous_on {0..1} (\<lambda>x. winding_number(subpath 0 x \<gamma>) z)"
proof -
  have *: "integral {0..x} (\<lambda>t. vector_derivative \<gamma> (at t) / (\<gamma> t - z)) / (2 * of_real pi * \<i>) =
         winding_number (subpath 0 x \<gamma>) z"
         if x: "0 \<le> x" "x \<le> 1" for x
  proof -
    have "integral {0..x} (\<lambda>t. vector_derivative \<gamma> (at t) / (\<gamma> t - z)) / (2 * of_real pi * \<i>) =
          1 / (2*pi*ii) * contour_integral (subpath 0 x \<gamma>) (\<lambda>w. 1/(w - z))"
      using assms x
      apply (simp add: contour_integral_subcontour_integral [OF contour_integrable_inversediff])
      done
    also have "... = winding_number (subpath 0 x \<gamma>) z"
      apply (subst winding_number_valid_path)
      using assms x
      apply (simp_all add: valid_path_subpath)
      by (force simp: closed_segment_eq_real_ivl path_image_def)
    finally show ?thesis .
  qed
  show ?thesis
    apply (rule continuous_on_eq
                 [where f = "\<lambda>x. 1 / (2*pi*ii) *
                                 integral {0..x} (\<lambda>t. 1/(\<gamma> t - z) * vector_derivative \<gamma> (at t))"])
    apply (rule continuous_intros)+
    apply (rule indefinite_integral_continuous)
    apply (rule contour_integrable_inversediff [OF assms, unfolded contour_integrable_on])
      using assms
    apply (simp add: *)
    done
qed

lemma winding_number_ivt_pos:
    assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and "0 \<le> w" "w \<le> Re(winding_number \<gamma> z)"
      shows "\<exists>t \<in> {0..1}. Re(winding_number(subpath 0 t \<gamma>) z) = w"
  apply (rule ivt_increasing_component_on_1 [of 0 1, where ?k = "1::complex", simplified complex_inner_1_right])
  apply (simp add:)
  apply (rule winding_number_subpath_continuous [OF \<gamma> z])
  using assms
  apply (auto simp: path_image_def image_def)
  done

lemma winding_number_ivt_neg:
    assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and "Re(winding_number \<gamma> z) \<le> w" "w \<le> 0"
      shows "\<exists>t \<in> {0..1}. Re(winding_number(subpath 0 t \<gamma>) z) = w"
  apply (rule ivt_decreasing_component_on_1 [of 0 1, where ?k = "1::complex", simplified complex_inner_1_right])
  apply (simp add:)
  apply (rule winding_number_subpath_continuous [OF \<gamma> z])
  using assms
  apply (auto simp: path_image_def image_def)
  done

lemma winding_number_ivt_abs:
    assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and "0 \<le> w" "w \<le> \<bar>Re(winding_number \<gamma> z)\<bar>"
      shows "\<exists>t \<in> {0..1}. \<bar>Re (winding_number (subpath 0 t \<gamma>) z)\<bar> = w"
  using assms winding_number_ivt_pos [of \<gamma> z w] winding_number_ivt_neg [of \<gamma> z "-w"]
  by force

lemma winding_number_lt_half_lemma:
  assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and az: "a \<bullet> z \<le> b" and pag: "path_image \<gamma> \<subseteq> {w. a \<bullet> w > b}"
    shows "Re(winding_number \<gamma> z) < 1/2"
proof -
  { assume "Re(winding_number \<gamma> z) \<ge> 1/2"
    then obtain t::real where t: "0 \<le> t" "t \<le> 1" and sub12: "Re (winding_number (subpath 0 t \<gamma>) z) = 1/2"
      using winding_number_ivt_pos [OF \<gamma> z, of "1/2"] by auto
    have gt: "\<gamma> t - z = - (of_real (exp (- (2 * pi * Im (winding_number (subpath 0 t \<gamma>) z)))) * (\<gamma> 0 - z))"
      using winding_number_exp_2pi [of "subpath 0 t \<gamma>" z]
      apply (simp add: t \<gamma> valid_path_imp_path)
      using closed_segment_eq_real_ivl path_image_def t z by (fastforce simp add: Euler sub12)
    have "b < a \<bullet> \<gamma> 0"
    proof -
      have "\<gamma> 0 \<in> {c. b < a \<bullet> c}"
        by (metis (no_types) pag atLeastAtMost_iff image_subset_iff order_refl path_image_def zero_le_one)
      thus ?thesis
        by blast
    qed
    moreover have "b < a \<bullet> \<gamma> t"
    proof -
      have "\<gamma> t \<in> {c. b < a \<bullet> c}"
        by (metis (no_types) pag atLeastAtMost_iff image_subset_iff path_image_def t)
      thus ?thesis
        by blast
    qed
    ultimately have "0 < a \<bullet> (\<gamma> 0 - z)" "0 < a \<bullet> (\<gamma> t - z)" using az
      by (simp add: inner_diff_right)+
    then have False
      by (simp add: gt inner_mult_right mult_less_0_iff)
  }
  then show ?thesis by force
qed

lemma winding_number_lt_half:
  assumes "valid_path \<gamma>" "a \<bullet> z \<le> b" "path_image \<gamma> \<subseteq> {w. a \<bullet> w > b}"
    shows "\<bar>Re (winding_number \<gamma> z)\<bar> < 1/2"
proof -
  have "z \<notin> path_image \<gamma>" using assms by auto
  with assms show ?thesis
    apply (simp add: winding_number_lt_half_lemma abs_if del: less_divide_eq_numeral1)
    apply (metis complex_inner_1_right winding_number_lt_half_lemma [OF valid_path_imp_reverse, of \<gamma> z a b]
                 winding_number_reversepath valid_path_imp_path inner_minus_left path_image_reversepath)
    done
qed

lemma winding_number_le_half:
  assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>"
      and anz: "a \<noteq> 0" and azb: "a \<bullet> z \<le> b" and pag: "path_image \<gamma> \<subseteq> {w. a \<bullet> w \<ge> b}"
    shows "\<bar>Re (winding_number \<gamma> z)\<bar> \<le> 1/2"
proof -
  { assume wnz_12: "\<bar>Re (winding_number \<gamma> z)\<bar> > 1/2"
    have "isCont (winding_number \<gamma>) z"
      by (metis continuous_at_winding_number valid_path_imp_path \<gamma> z)
    then obtain d where "d>0" and d: "\<And>x'. dist x' z < d \<Longrightarrow> dist (winding_number \<gamma> x') (winding_number \<gamma> z) < abs(Re(winding_number \<gamma> z)) - 1/2"
      using continuous_at_eps_delta wnz_12 diff_less_iff(1) by blast
    def z' \<equiv> "z - (d / (2 * cmod a)) *\<^sub>R a"
    have *: "a \<bullet> z' \<le> b - d / 3 * cmod a"
      unfolding z'_def inner_mult_right' divide_inverse
      apply (simp add: divide_simps algebra_simps dot_square_norm power2_eq_square anz)
      apply (metis `0 < d` add_increasing azb less_eq_real_def mult_nonneg_nonneg mult_right_mono norm_ge_zero norm_numeral)
      done
    have "cmod (winding_number \<gamma> z' - winding_number \<gamma> z) < \<bar>Re (winding_number \<gamma> z)\<bar> - 1/2"
      using d [of z'] anz `d>0` by (simp add: dist_norm z'_def)
    then have "1/2 < \<bar>Re (winding_number \<gamma> z)\<bar> - cmod (winding_number \<gamma> z' - winding_number \<gamma> z)"
      by simp
    then have "1/2 < \<bar>Re (winding_number \<gamma> z)\<bar> - \<bar>Re (winding_number \<gamma> z') - Re (winding_number \<gamma> z)\<bar>"
      using abs_Re_le_cmod [of "winding_number \<gamma> z' - winding_number \<gamma> z"] by simp
    then have wnz_12': "\<bar>Re (winding_number \<gamma> z')\<bar> > 1/2"
      by linarith
    moreover have "\<bar>Re (winding_number \<gamma> z')\<bar> < 1/2"
      apply (rule winding_number_lt_half [OF \<gamma> *])
      using azb `d>0` pag
      apply (auto simp: add_strict_increasing anz divide_simps algebra_simps dest!: subsetD)
      done
    ultimately have False
      by simp
  }
  then show ?thesis by force
qed

lemma winding_number_lt_half_linepath: "z \<notin> closed_segment a b \<Longrightarrow> \<bar>Re (winding_number (linepath a b) z)\<bar> < 1/2"
  using separating_hyperplane_closed_point [of "closed_segment a b" z]
  apply auto
  apply (simp add: closed_segment_def)
  apply (drule less_imp_le)
  apply (frule winding_number_lt_half [OF valid_path_linepath [of a b]])
  apply (auto simp: segment)
  done


text\<open> Positivity of WN for a linepath.\<close>
lemma winding_number_linepath_pos_lt:
    assumes "0 < Im ((b - a) * cnj (b - z))"
      shows "0 < Re(winding_number(linepath a b) z)"
proof -
  have z: "z \<notin> path_image (linepath a b)"
    using assms
    by (simp add: closed_segment_def) (force simp: algebra_simps)
  show ?thesis
    apply (rule winding_number_pos_lt [OF valid_path_linepath z assms])
    apply (simp add: linepath_def algebra_simps)
    done
qed


subsection{* Cauchy's integral formula, again for a convex enclosing set.*}

lemma Cauchy_integral_formula_weak:
    assumes s: "convex s" and "finite k" and conf: "continuous_on s f"
        and fcd: "(\<And>x. x \<in> interior s - k \<Longrightarrow> f complex_differentiable at x)"
        and z: "z \<in> interior s - k" and vpg: "valid_path \<gamma>"
        and pasz: "path_image \<gamma> \<subseteq> s - {z}" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
      shows "((\<lambda>w. f w / (w - z)) has_contour_integral (2*pi * ii * winding_number \<gamma> z * f z)) \<gamma>"
proof -
  obtain f' where f': "(f has_field_derivative f') (at z)"
    using fcd [OF z] by (auto simp: complex_differentiable_def)
  have pas: "path_image \<gamma> \<subseteq> s" and znotin: "z \<notin> path_image \<gamma>" using pasz by blast+
  have c: "continuous (at x within s) (\<lambda>w. if w = z then f' else (f w - f z) / (w - z))" if "x \<in> s" for x
  proof (cases "x = z")
    case True then show ?thesis
      apply (simp add: continuous_within)
      apply (rule Lim_transform_away_within [of _ "z+1" _ "\<lambda>w::complex. (f w - f z)/(w - z)"])
      using has_field_derivative_at_within DERIV_within_iff f'
      apply (fastforce simp add:)+
      done
  next
    case False
    then have dxz: "dist x z > 0" using dist_nz by blast
    have cf: "continuous (at x within s) f"
      using conf continuous_on_eq_continuous_within that by blast
    show ?thesis
      apply (rule continuous_transform_within [OF dxz that, of "\<lambda>w::complex. (f w - f z)/(w - z)"])
      apply (force simp: dist_commute)
      apply (rule cf continuous_intros)+
      using False by auto
  qed
  have fink': "finite (insert z k)" using \<open>finite k\<close> by blast
  have *: "((\<lambda>w. if w = z then f' else (f w - f z) / (w - z)) has_contour_integral 0) \<gamma>"
    apply (rule Cauchy_theorem_convex [OF _ s fink' _ vpg pas loop])
    using c apply (force simp: continuous_on_eq_continuous_within)
    apply (rename_tac w)
    apply (rule_tac d="dist w z" and f = "\<lambda>w. (f w - f z)/(w - z)" in complex_differentiable_transform_within)
    apply (simp_all add: dist_pos_lt dist_commute)
    apply (metis less_irrefl)
    apply (rule derivative_intros fcd | simp)+
    done
  show ?thesis
    apply (rule has_contour_integral_eq)
    using znotin has_contour_integral_add [OF has_contour_integral_lmul [OF has_contour_integral_winding_number [OF vpg znotin], of "f z"] *]
    apply (auto simp: mult_ac divide_simps)
    done
qed

theorem Cauchy_integral_formula_convex_simple:
    "\<lbrakk>convex s; f holomorphic_on s; z \<in> interior s; valid_path \<gamma>; path_image \<gamma> \<subseteq> s - {z};
      pathfinish \<gamma> = pathstart \<gamma>\<rbrakk>
     \<Longrightarrow> ((\<lambda>w. f w / (w - z)) has_contour_integral (2*pi * ii * winding_number \<gamma> z * f z)) \<gamma>"
  apply (rule Cauchy_integral_formula_weak [where k = "{}"])
  using holomorphic_on_imp_continuous_on
  by auto (metis at_within_interior holomorphic_on_def interiorE subsetCE)


subsection\<open>Homotopy forms of Cauchy's theorem\<close>

proposition Cauchy_theorem_homotopic:
    assumes hom: "if atends then homotopic_paths s g h else homotopic_loops s g h"
        and "open s" and f: "f holomorphic_on s"
        and vpg: "valid_path g" and vph: "valid_path h"
    shows "contour_integral g f = contour_integral h f"
proof -
  have pathsf: "linked_paths atends g h"
    using hom  by (auto simp: linked_paths_def homotopic_paths_imp_pathstart homotopic_paths_imp_pathfinish homotopic_loops_imp_loop)
  obtain k :: "real \<times> real \<Rightarrow> complex"
    where contk: "continuous_on ({0..1} \<times> {0..1}) k"
      and ks: "k ` ({0..1} \<times> {0..1}) \<subseteq> s"
      and k [simp]: "\<forall>x. k (0, x) = g x" "\<forall>x. k (1, x) = h x"
      and ksf: "\<forall>t\<in>{0..1}. linked_paths atends g (\<lambda>x. k (t, x))"
      using hom pathsf by (auto simp: linked_paths_def homotopic_paths_def homotopic_loops_def homotopic_with_def split: split_if_asm)
  have ucontk: "uniformly_continuous_on ({0..1} \<times> {0..1}) k"
    by (blast intro: compact_Times compact_uniformly_continuous [OF contk])
  { fix t::real assume t: "t \<in> {0..1}"
    have pak: "path (k o (\<lambda>u. (t, u)))"
      unfolding path_def
      apply (rule continuous_intros continuous_on_subset [OF contk])+
      using t by force
    have pik: "path_image (k \<circ> Pair t) \<subseteq> s"
      using ks t by (auto simp: path_image_def)
    obtain e where "e>0" and e:
         "\<And>g h. \<lbrakk>valid_path g; valid_path h;
                  \<forall>u\<in>{0..1}. cmod (g u - (k \<circ> Pair t) u) < e \<and> cmod (h u - (k \<circ> Pair t) u) < e;
                  linked_paths atends g h\<rbrakk>
                 \<Longrightarrow> contour_integral h f = contour_integral g f"
      using contour_integral_nearby [OF \<open>open s\<close> pak pik, of atends] f by metis
    obtain d where "d>0" and d:
        "\<And>x x'. \<lbrakk>x \<in> {0..1} \<times> {0..1}; x' \<in> {0..1} \<times> {0..1}; norm (x'-x) < d\<rbrakk> \<Longrightarrow> norm (k x' - k x) < e/4"
      by (rule uniformly_continuous_onE [OF ucontk, of "e/4"]) (auto simp: dist_norm `e>0`)
    { fix t1 t2
      assume t1: "0 \<le> t1" "t1 \<le> 1" and t2: "0 \<le> t2" "t2 \<le> 1" and ltd: "\<bar>t1 - t\<bar> < d" "\<bar>t2 - t\<bar> < d"
      have no2: "\<And>g1 k1 kt. \<lbrakk>norm(g1 - k1) < e/4; norm(k1 - kt) < e/4\<rbrakk> \<Longrightarrow> norm(g1 - kt) < e"
        using \<open>e > 0\<close>
        apply (rule_tac y = k1 in norm_triangle_half_l)
        apply (auto simp: norm_minus_commute intro: order_less_trans)
        done
      have "\<exists>d>0. \<forall>g1 g2. valid_path g1 \<and> valid_path g2 \<and>
                          (\<forall>u\<in>{0..1}. cmod (g1 u - k (t1, u)) < d \<and> cmod (g2 u - k (t2, u)) < d) \<and>
                          linked_paths atends g1 g2 \<longrightarrow>
                          contour_integral g2 f = contour_integral g1 f"
        apply (rule_tac x="e/4" in exI)
        using t t1 t2 ltd \<open>e > 0\<close>
        apply (auto intro!: e simp: d no2 simp del: less_divide_eq_numeral1)
        done
    }
    then have "\<exists>e. 0 < e \<and>
              (\<forall>t1 t2. t1 \<in> {0..1} \<and> t2 \<in> {0..1} \<and> abs(t1 - t) < e \<and> abs(t2 - t) < e
                \<longrightarrow> (\<exists>d. 0 < d \<and>
                     (\<forall>g1 g2. valid_path g1 \<and> valid_path g2 \<and>
                       (\<forall>u \<in> {0..1}.
                          norm(g1 u - k((t1,u))) < d \<and> norm(g2 u - k((t2,u))) < d) \<and>
                          linked_paths atends g1 g2
                          \<longrightarrow> contour_integral g2 f = contour_integral g1 f)))"
      by (rule_tac x=d in exI) (simp add: \<open>d > 0\<close>)
  }
  then obtain ee where ee:
       "\<And>t. t \<in> {0..1} \<Longrightarrow> ee t > 0 \<and>
          (\<forall>t1 t2. t1 \<in> {0..1} \<longrightarrow> t2 \<in> {0..1} \<longrightarrow> abs(t1 - t) < ee t \<longrightarrow> abs(t2 - t) < ee t
            \<longrightarrow> (\<exists>d. 0 < d \<and>
                 (\<forall>g1 g2. valid_path g1 \<and> valid_path g2 \<and>
                   (\<forall>u \<in> {0..1}.
                      norm(g1 u - k((t1,u))) < d \<and> norm(g2 u - k((t2,u))) < d) \<and>
                      linked_paths atends g1 g2
                      \<longrightarrow> contour_integral g2 f = contour_integral g1 f)))"
    by metis
  note ee_rule = ee [THEN conjunct2, rule_format]
  def C \<equiv> "(\<lambda>t. ball t (ee t / 3)) ` {0..1}"
  have "\<forall>t \<in> C. open t" by (simp add: C_def)
  moreover have "{0..1} \<subseteq> \<Union>C"
    using ee [THEN conjunct1] by (auto simp: C_def dist_norm)
  ultimately obtain C' where C': "C' \<subseteq> C" "finite C'" and C'01: "{0..1} \<subseteq> \<Union>C'"
    by (rule compactE [OF compact_interval])
  def kk \<equiv> "{t \<in> {0..1}. ball t (ee t / 3) \<in> C'}"
  have kk01: "kk \<subseteq> {0..1}" by (auto simp: kk_def)
  def e \<equiv> "Min (ee ` kk)"
  have C'_eq: "C' = (\<lambda>t. ball t (ee t / 3)) ` kk"
    using C' by (auto simp: kk_def C_def)
  have ee_pos[simp]: "\<And>t. t \<in> {0..1} \<Longrightarrow> ee t > 0"
    by (simp add: kk_def ee)
  moreover have "finite kk"
    using \<open>finite C'\<close> kk01 by (force simp: C'_eq inj_on_def ball_eq_ball_iff dest: ee_pos finite_imageD)
  moreover have "kk \<noteq> {}" using \<open>{0..1} \<subseteq> \<Union>C'\<close> C'_eq by force
  ultimately have "e > 0"
    using finite_less_Inf_iff [of "ee ` kk" 0] kk01 by (force simp: e_def)
  then obtain N::nat where "N > 0" and N: "1/N < e/3"
    by (meson divide_pos_pos nat_approx_posE zero_less_Suc zero_less_numeral)
  have e_le_ee: "\<And>i. i \<in> kk \<Longrightarrow> e \<le> ee i"
    using \<open>finite kk\<close> by (simp add: e_def Min_le_iff [of "ee ` kk"])
  have plus: "\<exists>t \<in> kk. x \<in> ball t (ee t / 3)" if "x \<in> {0..1}" for x
    using C' subsetD [OF C'01 that]  unfolding C'_eq by blast
  have [OF order_refl]:
      "\<exists>d. 0 < d \<and> (\<forall>j. valid_path j \<and> (\<forall>u \<in> {0..1}. norm(j u - k (n/N, u)) < d) \<and> linked_paths atends g j
                        \<longrightarrow> contour_integral j f = contour_integral g f)"
       if "n \<le> N" for n
  using that
  proof (induct n)
    case 0 show ?case using ee_rule [of 0 0 0]
      apply clarsimp
      apply (rule_tac x=d in exI, safe)
      by (metis diff_self vpg norm_zero)
  next
    case (Suc n)
    then have N01: "n/N \<in> {0..1}" "(Suc n)/N \<in> {0..1}"  by auto
    then obtain t where t: "t \<in> kk" "n/N \<in> ball t (ee t / 3)"
      using plus [of "n/N"] by blast
    then have nN_less: "\<bar>n/N - t\<bar> < ee t"
      by (simp add: dist_norm del: less_divide_eq_numeral1)
    have n'N_less: "\<bar>real (Suc n) / real N - t\<bar> < ee t"
      using t N \<open>N > 0\<close> e_le_ee [of t]
      by (simp add: dist_norm add_divide_distrib abs_diff_less_iff del: less_divide_eq_numeral1) (simp add: field_simps)
    have t01: "t \<in> {0..1}" using `kk \<subseteq> {0..1}` `t \<in> kk` by blast
    obtain d1 where "d1 > 0" and d1:
        "\<And>g1 g2. \<lbrakk>valid_path g1; valid_path g2;
                   \<forall>u\<in>{0..1}. cmod (g1 u - k (n/N, u)) < d1 \<and> cmod (g2 u - k ((Suc n) / N, u)) < d1;
                   linked_paths atends g1 g2\<rbrakk>
                   \<Longrightarrow> contour_integral g2 f = contour_integral g1 f"
      using ee [THEN conjunct2, rule_format, OF t01 N01 nN_less n'N_less] by fastforce
    have "n \<le> N" using Suc.prems by auto
    with Suc.hyps
    obtain d2 where "d2 > 0"
      and d2: "\<And>j. \<lbrakk>valid_path j; \<forall>u\<in>{0..1}. cmod (j u - k (n/N, u)) < d2; linked_paths atends g j\<rbrakk>
                     \<Longrightarrow> contour_integral j f = contour_integral g f"
        by auto
    have "continuous_on {0..1} (k o (\<lambda>u. (n/N, u)))"
      apply (rule continuous_intros continuous_on_subset [OF contk])+
      using N01 by auto
    then have pkn: "path (\<lambda>u. k (n/N, u))"
      by (simp add: path_def)
    have min12: "min d1 d2 > 0" by (simp add: `0 < d1` `0 < d2`)
    obtain p where "polynomial_function p"
        and psf: "pathstart p = pathstart (\<lambda>u. k (n/N, u))"
                 "pathfinish p = pathfinish (\<lambda>u. k (n/N, u))"
        and pk_le:  "\<And>t. t\<in>{0..1} \<Longrightarrow> cmod (p t - k (n/N, t)) < min d1 d2"
      using path_approx_polynomial_function [OF pkn min12] by blast
    then have vpp: "valid_path p" using valid_path_polynomial_function by blast
    have lpa: "linked_paths atends g p"
      by (metis (mono_tags, lifting) N01(1) ksf linked_paths_def pathfinish_def pathstart_def psf)
    show ?case
      apply (rule_tac x="min d1 d2" in exI)
      apply (simp add: `0 < d1` `0 < d2`, clarify)
      apply (rule_tac s="contour_integral p f" in trans)
      using pk_le N01(1) ksf pathfinish_def pathstart_def
      apply (force intro!: vpp d1 simp add: linked_paths_def psf ksf)
      using pk_le N01 apply (force intro!: vpp d2 lpa simp add: linked_paths_def psf ksf)
      done
  qed
  then obtain d where "0 < d"
                       "\<And>j. valid_path j \<and> (\<forall>u \<in> {0..1}. norm(j u - k (1,u)) < d) \<and>
                            linked_paths atends g j
                            \<Longrightarrow> contour_integral j f = contour_integral g f"
    using \<open>N>0\<close> by auto
  then have "linked_paths atends g h \<Longrightarrow> contour_integral h f = contour_integral g f"
    using \<open>N>0\<close> vph by fastforce
  then show ?thesis
    by (simp add: pathsf)
qed

proposition Cauchy_theorem_homotopic_paths:
    assumes hom: "homotopic_paths s g h"
        and "open s" and f: "f holomorphic_on s"
        and vpg: "valid_path g" and vph: "valid_path h"
    shows "contour_integral g f = contour_integral h f"
  using Cauchy_theorem_homotopic [of True s g h] assms by simp

proposition Cauchy_theorem_homotopic_loops:
    assumes hom: "homotopic_loops s g h"
        and "open s" and f: "f holomorphic_on s"
        and vpg: "valid_path g" and vph: "valid_path h"
    shows "contour_integral g f = contour_integral h f"
  using Cauchy_theorem_homotopic [of False s g h] assms by simp

lemma has_contour_integral_newpath:
    "\<lbrakk>(f has_contour_integral y) h; f contour_integrable_on g; contour_integral g f = contour_integral h f\<rbrakk>
     \<Longrightarrow> (f has_contour_integral y) g"
  using has_contour_integral_integral contour_integral_unique by auto

lemma Cauchy_theorem_null_homotopic:
     "\<lbrakk>f holomorphic_on s; open s; valid_path g; homotopic_loops s g (linepath a a)\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) g"
  apply (rule has_contour_integral_newpath [where h = "linepath a a"], simp)
  using contour_integrable_holomorphic_simple
    apply (blast dest: holomorphic_on_imp_continuous_on homotopic_loops_imp_subset)
  by (simp add: Cauchy_theorem_homotopic_loops)



subsection\<open>More winding number properties\<close>

text\<open>including the fact that it's +-1 inside a simple closed curve.\<close>

lemma winding_number_homotopic_paths:
    assumes "homotopic_paths (-{z}) g h"
      shows "winding_number g z = winding_number h z"
proof -
  have "path g" "path h" using homotopic_paths_imp_path [OF assms] by auto
  moreover have pag: "z \<notin> path_image g" and pah: "z \<notin> path_image h"
    using homotopic_paths_imp_subset [OF assms] by auto
  ultimately obtain d e where "d > 0" "e > 0"
      and d: "\<And>p. \<lbrakk>path p; pathstart p = pathstart g; pathfinish p = pathfinish g; \<forall>t\<in>{0..1}. norm (p t - g t) < d\<rbrakk>
            \<Longrightarrow> homotopic_paths (-{z}) g p"
      and e: "\<And>q. \<lbrakk>path q; pathstart q = pathstart h; pathfinish q = pathfinish h; \<forall>t\<in>{0..1}. norm (q t - h t) < e\<rbrakk>
            \<Longrightarrow> homotopic_paths (-{z}) h q"
    using homotopic_nearby_paths [of g "-{z}"] homotopic_nearby_paths [of h "-{z}"] by force
  obtain p where p:
       "valid_path p" "z \<notin> path_image p"
       "pathstart p = pathstart g" "pathfinish p = pathfinish g"
       and gp_less:"\<forall>t\<in>{0..1}. cmod (g t - p t) < d"
       and pap: "contour_integral p (\<lambda>w. 1 / (w - z)) = complex_of_real (2 * pi) * \<i> * winding_number g z"
    using winding_number [OF \<open>path g\<close> pag \<open>0 < d\<close>] by blast
  obtain q where q:
       "valid_path q" "z \<notin> path_image q"
       "pathstart q = pathstart h" "pathfinish q = pathfinish h"
       and hq_less: "\<forall>t\<in>{0..1}. cmod (h t - q t) < e"
       and paq:  "contour_integral q (\<lambda>w. 1 / (w - z)) = complex_of_real (2 * pi) * \<i> * winding_number h z"
    using winding_number [OF \<open>path h\<close> pah \<open>0 < e\<close>] by blast
  have gp: "homotopic_paths (- {z}) g p"
    by (simp add: d p valid_path_imp_path norm_minus_commute gp_less)
  have hq: "homotopic_paths (- {z}) h q"
    by (simp add: e q valid_path_imp_path norm_minus_commute hq_less)
  have "contour_integral p (\<lambda>w. 1/(w - z)) = contour_integral q (\<lambda>w. 1/(w - z))"
    apply (rule Cauchy_theorem_homotopic_paths [of "-{z}"])
    apply (blast intro: homotopic_paths_trans homotopic_paths_sym gp hq assms)
    apply (auto intro!: holomorphic_intros simp: p q)
    done
  then show ?thesis
    by (simp add: pap paq)
qed

lemma winding_number_homotopic_loops:
    assumes "homotopic_loops (-{z}) g h"
      shows "winding_number g z = winding_number h z"
proof -
  have "path g" "path h" using homotopic_loops_imp_path [OF assms] by auto
  moreover have pag: "z \<notin> path_image g" and pah: "z \<notin> path_image h"
    using homotopic_loops_imp_subset [OF assms] by auto
  moreover have gloop: "pathfinish g = pathstart g" and hloop: "pathfinish h = pathstart h"
    using homotopic_loops_imp_loop [OF assms] by auto
  ultimately obtain d e where "d > 0" "e > 0"
      and d: "\<And>p. \<lbrakk>path p; pathfinish p = pathstart p; \<forall>t\<in>{0..1}. norm (p t - g t) < d\<rbrakk>
            \<Longrightarrow> homotopic_loops (-{z}) g p"
      and e: "\<And>q. \<lbrakk>path q; pathfinish q = pathstart q; \<forall>t\<in>{0..1}. norm (q t - h t) < e\<rbrakk>
            \<Longrightarrow> homotopic_loops (-{z}) h q"
    using homotopic_nearby_loops [of g "-{z}"] homotopic_nearby_loops [of h "-{z}"] by force
  obtain p where p:
       "valid_path p" "z \<notin> path_image p"
       "pathstart p = pathstart g" "pathfinish p = pathfinish g"
       and gp_less:"\<forall>t\<in>{0..1}. cmod (g t - p t) < d"
       and pap: "contour_integral p (\<lambda>w. 1 / (w - z)) = complex_of_real (2 * pi) * \<i> * winding_number g z"
    using winding_number [OF \<open>path g\<close> pag \<open>0 < d\<close>] by blast
  obtain q where q:
       "valid_path q" "z \<notin> path_image q"
       "pathstart q = pathstart h" "pathfinish q = pathfinish h"
       and hq_less: "\<forall>t\<in>{0..1}. cmod (h t - q t) < e"
       and paq:  "contour_integral q (\<lambda>w. 1 / (w - z)) = complex_of_real (2 * pi) * \<i> * winding_number h z"
    using winding_number [OF \<open>path h\<close> pah \<open>0 < e\<close>] by blast
  have gp: "homotopic_loops (- {z}) g p"
    by (simp add: gloop d gp_less norm_minus_commute p valid_path_imp_path)
  have hq: "homotopic_loops (- {z}) h q"
    by (simp add: e hloop hq_less norm_minus_commute q valid_path_imp_path)
  have "contour_integral p (\<lambda>w. 1/(w - z)) = contour_integral q (\<lambda>w. 1/(w - z))"
    apply (rule Cauchy_theorem_homotopic_loops [of "-{z}"])
    apply (blast intro: homotopic_loops_trans homotopic_loops_sym gp hq assms)
    apply (auto intro!: holomorphic_intros simp: p q)
    done
  then show ?thesis
    by (simp add: pap paq)
qed

lemma winding_number_paths_linear_eq:
  "\<lbrakk>path g; path h; pathstart h = pathstart g; pathfinish h = pathfinish g;
    \<And>t. t \<in> {0..1} \<Longrightarrow> z \<notin> closed_segment (g t) (h t)\<rbrakk>
        \<Longrightarrow> winding_number h z = winding_number g z"
  by (blast intro: sym homotopic_paths_linear winding_number_homotopic_paths elim: )

lemma winding_number_loops_linear_eq:
  "\<lbrakk>path g; path h; pathfinish g = pathstart g; pathfinish h = pathstart h;
    \<And>t. t \<in> {0..1} \<Longrightarrow> z \<notin> closed_segment (g t) (h t)\<rbrakk>
        \<Longrightarrow> winding_number h z = winding_number g z"
  by (blast intro: sym homotopic_loops_linear winding_number_homotopic_loops elim: )

lemma winding_number_nearby_paths_eq:
     "\<lbrakk>path g; path h;
      pathstart h = pathstart g; pathfinish h = pathfinish g;
      \<And>t. t \<in> {0..1} \<Longrightarrow> norm(h t - g t) < norm(g t - z)\<rbrakk>
      \<Longrightarrow> winding_number h z = winding_number g z"
  by (metis segment_bound(2) norm_minus_commute not_le winding_number_paths_linear_eq)

lemma winding_number_nearby_loops_eq:
     "\<lbrakk>path g; path h;
      pathfinish g = pathstart g;
        pathfinish h = pathstart h;
      \<And>t. t \<in> {0..1} \<Longrightarrow> norm(h t - g t) < norm(g t - z)\<rbrakk>
      \<Longrightarrow> winding_number h z = winding_number g z"
  by (metis segment_bound(2) norm_minus_commute not_le winding_number_loops_linear_eq)

end
