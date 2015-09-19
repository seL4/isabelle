section \<open>Complex path integrals and Cauchy's integral theorem\<close>

theory Cauchy_Integral_Thm
imports Complex_Transcendental Weierstrass
begin

(*FIXME migrate into libraries*)

lemma inj_mult_left [simp]: "inj (op* x) \<longleftrightarrow> x \<noteq> (0::'a::idom)"
  by (metis injI mult_cancel_left the_inv_f_f zero_neq_one)

lemma continuous_on_strong_cong:
  "s = t \<Longrightarrow> (\<And>x. x \<in> t =simp=> f x = g x) \<Longrightarrow> continuous_on s f \<longleftrightarrow> continuous_on t g"
  by (simp add: simp_implies_def)

thm image_affinity_atLeastAtMost_div_diff
lemma image_affinity_atLeastAtMost_div:
  fixes c :: "'a::linordered_field"
  shows "((\<lambda>x. x/m + c) ` {a..b}) = (if {a..b}={} then {}
            else if 0 \<le> m then {a/m + c .. b/m + c}
            else {b/m + c .. a/m + c})"
  using image_affinity_atLeastAtMost [of "inverse m" c a b]
  by (simp add: field_class.field_divide_inverse algebra_simps)

thm continuous_on_closed_Un
lemma continuous_on_open_Un:
  "open s \<Longrightarrow> open t \<Longrightarrow> continuous_on s f \<Longrightarrow> continuous_on t f \<Longrightarrow> continuous_on (s \<union> t) f"
  using continuous_on_open_Union [of "{s,t}"] by auto

thm continuous_on_eq (*REPLACE*)
lemma continuous_on_eq:
  "\<lbrakk>continuous_on s f; \<And>x. x \<in> s \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> continuous_on s g"
  unfolding continuous_on_def tendsto_def eventually_at_topological
  by simp

thm vector_derivative_add_at
lemma vector_derivative_mult_at [simp]:
  fixes f g :: "real \<Rightarrow> 'a :: real_normed_algebra"
  shows  "\<lbrakk>f differentiable at a; g differentiable at a\<rbrakk>
   \<Longrightarrow> vector_derivative (\<lambda>x. f x * g x) (at a) = f a * vector_derivative g (at a) + vector_derivative f (at a) * g a"
  by (simp add: vector_derivative_at has_vector_derivative_mult vector_derivative_works [symmetric])

lemma vector_derivative_scaleR_at [simp]:
    "\<lbrakk>f differentiable at a; g differentiable at a\<rbrakk>
   \<Longrightarrow> vector_derivative (\<lambda>x. f x *\<^sub>R g x) (at a) = f a *\<^sub>R vector_derivative g (at a) + vector_derivative f (at a) *\<^sub>R g a"
apply (rule vector_derivative_at)
apply (rule has_vector_derivative_scaleR)
apply (auto simp: vector_derivative_works has_vector_derivative_def has_field_derivative_def mult_commute_abs)
done

thm Derivative.vector_diff_chain_at
lemma vector_derivative_chain_at:
  assumes "f differentiable at x" "(g differentiable at (f x))"
  shows "vector_derivative (g \<circ> f) (at x) =
         vector_derivative f (at x) *\<^sub>R vector_derivative g (at (f x))"
by (metis Derivative.vector_diff_chain_at vector_derivative_at vector_derivative_works assms)


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
    by (metis `finite s` `finite t` finite_Un finite_insert finite.emptyI)
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

lemma piecewise_C1_differentiable_C1_diff:
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
  with `finite s` show ?thesis
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
  with `finite s` show ?thesis
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

definition has_path_integral :: "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> bool"
           (infixr "has'_path'_integral" 50)
  where "(f has_path_integral i) g \<equiv>
           ((\<lambda>x. f(g x) * vector_derivative g (at x within {0..1}))
            has_integral i) {0..1}"

definition path_integrable_on
           (infixr "path'_integrable'_on" 50)
  where "f path_integrable_on g \<equiv> \<exists>i. (f has_path_integral i) g"

definition path_integral
  where "path_integral g f \<equiv> @i. (f has_path_integral i) g"

lemma path_integral_unique: "(f has_path_integral i)  g \<Longrightarrow> path_integral g f = i"
  by (auto simp: path_integral_def has_path_integral_def integral_def [symmetric])

lemma has_path_integral_integral:
    "f path_integrable_on i \<Longrightarrow> (f has_path_integral (path_integral i f)) i"
  by (metis path_integral_unique path_integrable_on_def)

lemma has_path_integral_unique:
    "(f has_path_integral i) g \<Longrightarrow> (f has_path_integral j) g \<Longrightarrow> i = j"
  using has_integral_unique
  by (auto simp: has_path_integral_def)

lemma has_path_integral_integrable: "(f has_path_integral i) g \<Longrightarrow> f path_integrable_on g"
  using path_integrable_on_def by blast

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

lemma has_path_integral:
     "(f has_path_integral i) g \<longleftrightarrow>
      ((\<lambda>x. f (g x) * vector_derivative g (at x)) has_integral i) {0..1}"
  by (simp add: has_integral_localized_vector_derivative has_path_integral_def)

lemma path_integrable_on:
     "f path_integrable_on g \<longleftrightarrow>
      (\<lambda>t. f(g t) * vector_derivative g (at t)) integrable_on {0..1}"
  by (simp add: has_path_integral integrable_on_def path_integrable_on_def)

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

lemma has_path_integral_reversepath:
  assumes "valid_path g" "(f has_path_integral i) g"
    shows "(f has_path_integral (-i)) (reversepath g)"
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
    apply (auto simp: has_path_integral_def)
    apply (drule has_integral_affinity01 [where m= "-1" and c=1])
    apply (auto simp: reversepath_def valid_path_def piecewise_C1_differentiable_on_def)
    apply (drule has_integral_neg)
    apply (rule_tac s = "(\<lambda>x. 1 - x) ` s" in has_integral_spike_finite)
    apply (auto simp: *)
    done
qed

lemma path_integrable_reversepath:
    "valid_path g \<Longrightarrow> f path_integrable_on g \<Longrightarrow> f path_integrable_on (reversepath g)"
  using has_path_integral_reversepath path_integrable_on_def by blast

lemma path_integrable_reversepath_eq:
    "valid_path g \<Longrightarrow> (f path_integrable_on (reversepath g) \<longleftrightarrow> f path_integrable_on g)"
  using path_integrable_reversepath valid_path_reversepath by fastforce

lemma path_integral_reversepath:
    "\<lbrakk>valid_path g; f path_integrable_on g\<rbrakk> \<Longrightarrow> path_integral (reversepath g) f = -(path_integral g f)"
  using has_path_integral_reversepath path_integrable_on_def path_integral_unique by blast


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

lemma has_path_integral_join:
  assumes "(f has_path_integral i1) g1" "(f has_path_integral i2) g2"
          "valid_path g1" "valid_path g2"
    shows "(f has_path_integral (i1 + i2)) (g1 +++ g2)"
proof -
  obtain s1 s2
    where s1: "finite s1" "\<forall>x\<in>{0..1} - s1. g1 differentiable at x"
      and s2: "finite s2" "\<forall>x\<in>{0..1} - s2. g2 differentiable at x"
    using assms
    by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have 1: "((\<lambda>x. f (g1 x) * vector_derivative g1 (at x)) has_integral i1) {0..1}"
   and 2: "((\<lambda>x. f (g2 x) * vector_derivative g2 (at x)) has_integral i2) {0..1}"
    using assms
    by (auto simp: has_path_integral)
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
    apply (simp add: has_path_integral)
    apply (rule has_integral_combine [where c = "1/2"], auto)
    done
qed

lemma path_integrable_joinI:
  assumes "f path_integrable_on g1" "f path_integrable_on g2"
          "valid_path g1" "valid_path g2"
    shows "f path_integrable_on (g1 +++ g2)"
  using assms
  by (meson has_path_integral_join path_integrable_on_def)

lemma path_integrable_joinD1:
  assumes "f path_integrable_on (g1 +++ g2)" "valid_path g1"
    shows "f path_integrable_on g1"
proof -
  obtain s1
    where s1: "finite s1" "\<forall>x\<in>{0..1} - s1. g1 differentiable at x"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have "(\<lambda>x. f ((g1 +++ g2) (x/2)) * vector_derivative (g1 +++ g2) (at (x/2))) integrable_on {0..1}"
    using assms
    apply (auto simp: path_integrable_on)
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
    apply (auto simp: path_integrable_on)
    apply (rule integrable_spike_finite [of "{0,1} \<union> s1", OF _ _ *])
    apply (auto simp: joinpaths_def scaleR_conv_of_real g1)
    done
qed

lemma path_integrable_joinD2:
  assumes "f path_integrable_on (g1 +++ g2)" "valid_path g2"
    shows "f path_integrable_on g2"
proof -
  obtain s2
    where s2: "finite s2" "\<forall>x\<in>{0..1} - s2. g2 differentiable at x"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have "(\<lambda>x. f ((g1 +++ g2) (x/2 + 1/2)) * vector_derivative (g1 +++ g2) (at (x/2 + 1/2))) integrable_on {0..1}"
    using assms
    apply (auto simp: path_integrable_on)
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
    apply (auto simp: path_integrable_on)
    apply (rule integrable_spike_finite [of "{0,1} \<union> s2", OF _ _ *])
    apply (auto simp: joinpaths_def scaleR_conv_of_real g2)
    done
qed

lemma path_integrable_join [simp]:
  shows
    "\<lbrakk>valid_path g1; valid_path g2\<rbrakk>
     \<Longrightarrow> f path_integrable_on (g1 +++ g2) \<longleftrightarrow> f path_integrable_on g1 \<and> f path_integrable_on g2"
using path_integrable_joinD1 path_integrable_joinD2 path_integrable_joinI by blast

lemma path_integral_join [simp]:
  shows
    "\<lbrakk>f path_integrable_on g1; f path_integrable_on g2; valid_path g1; valid_path g2\<rbrakk>
        \<Longrightarrow> path_integral (g1 +++ g2) f = path_integral g1 f + path_integral g2 f"
  by (simp add: has_path_integral_integral has_path_integral_join path_integral_unique)


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

lemma has_path_integral_shiftpath:
  assumes f: "(f has_path_integral i) g" "valid_path g"
      and a: "a \<in> {0..1}"
    shows "(f has_path_integral i) (shiftpath a g)"
proof -
  obtain s
    where s: "finite s" and g: "\<forall>x\<in>{0..1} - s. g differentiable at x"
    using assms by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have *: "((\<lambda>x. f (g x) * vector_derivative g (at x)) has_integral i) {0..1}"
    using assms by (auto simp: has_path_integral)
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
    by (auto simp: i has_path_integral intro: has_integral_combine [where c = "1-a"])
qed

lemma has_path_integral_shiftpath_D:
  assumes "(f has_path_integral i) (shiftpath a g)"
          "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "(f has_path_integral i) g"
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
  have fi: "(f has_path_integral i) (shiftpath (1 - a) (shiftpath a g))"
    using assms  by (auto intro!: has_path_integral_shiftpath)
  show ?thesis
    apply (simp add: has_path_integral_def)
    apply (rule has_integral_spike_finite [of "{0,1} \<union> s", OF _ _  fi [unfolded has_path_integral_def]])
    using s assms vd
    apply (auto simp: Path_Connected.shiftpath_shiftpath)
    done
qed

lemma has_path_integral_shiftpath_eq:
  assumes "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "(f has_path_integral i) (shiftpath a g) \<longleftrightarrow> (f has_path_integral i) g"
  using assms has_path_integral_shiftpath has_path_integral_shiftpath_D by blast

lemma path_integral_shiftpath:
  assumes "valid_path g" "pathfinish g = pathstart g" "a \<in> {0..1}"
    shows "path_integral (shiftpath a g) f = path_integral g f"
   using assms by (simp add: path_integral_def has_path_integral_shiftpath_eq)


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

lemma has_path_integral_linepath:
  shows "(f has_path_integral i) (linepath a b) \<longleftrightarrow>
         ((\<lambda>x. f(linepath a b x) * (b - a)) has_integral i) {0..1}"
  by (simp add: has_path_integral vector_derivative_linepath_at)

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

lemma has_path_integral_trivial [iff]: "(f has_path_integral 0) (linepath a a)"
  by (simp add: has_path_integral_linepath)

lemma path_integral_trivial [simp]: "path_integral (linepath a a) f = 0"
  using has_path_integral_trivial path_integral_unique by blast


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

lemma has_path_integral_subpath_refl [iff]: "(f has_path_integral 0) (subpath u u g)"
  by (simp add: has_path_integral subpath_def)

lemma path_integrable_subpath_refl [iff]: "f path_integrable_on (subpath u u g)"
  using has_path_integral_subpath_refl path_integrable_on_def by blast

lemma path_integral_subpath_refl [simp]: "path_integral (subpath u u g) f = 0"
  by (simp add: has_path_integral_subpath_refl path_integral_unique)

lemma has_path_integral_subpath:
  assumes f: "f path_integrable_on g" and g: "valid_path g"
      and uv: "u \<in> {0..1}" "v \<in> {0..1}" "u \<le> v"
    shows "(f has_path_integral  integral {u..v} (\<lambda>x. f(g x) * vector_derivative g (at x)))
           (subpath u v g)"
proof (cases "v=u")
  case True
  then show ?thesis
    using f   by (simp add: path_integrable_on_def subpath_def has_path_integral)
next
  case False
  obtain s where s: "\<And>x. x \<in> {0..1} - s \<Longrightarrow> g differentiable at x" and fs: "finite s"
    using g unfolding piecewise_C1_differentiable_on_def C1_differentiable_on_eq valid_path_def by blast
  have *: "((\<lambda>x. f (g ((v - u) * x + u)) * vector_derivative g (at ((v - u) * x + u)))
            has_integral (1 / (v - u)) * integral {u..v} (\<lambda>t. f (g t) * vector_derivative g (at t)))
           {0..1}"
    using f uv
    apply (simp add: path_integrable_on subpath_def has_path_integral)
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
    apply (simp add: False subpath_def has_path_integral)
    apply (rule_tac s = "(\<lambda>t. ((v-u) *\<^sub>R t + u)) -` s" in has_integral_spike_finite)
    apply (auto simp: inj_on_def False finite_vimageI vd scaleR_conv_of_real)
    done
qed

lemma path_integrable_subpath:
  assumes "f path_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}"
    shows "f path_integrable_on (subpath u v g)"
  apply (cases u v rule: linorder_class.le_cases)
   apply (metis path_integrable_on_def has_path_integral_subpath [OF assms])
  apply (subst reversepath_subpath [symmetric])
  apply (rule path_integrable_reversepath)
   using assms apply (blast intro: valid_path_subpath)
  apply (simp add: path_integrable_on_def)
  using assms apply (blast intro: has_path_integral_subpath)
  done

lemma has_integral_integrable_integral: "(f has_integral i) s \<longleftrightarrow> f integrable_on s \<and> integral s f = i"
  by blast

lemma has_integral_path_integral_subpath:
  assumes "f path_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}" "u \<le> v"
    shows "(((\<lambda>x. f(g x) * vector_derivative g (at x)))
            has_integral  path_integral (subpath u v g) f) {u..v}"
  using assms
  apply (auto simp: has_integral_integrable_integral)
  apply (rule integrable_on_subcbox [where a=u and b=v and s = "{0..1}", simplified])
  apply (auto simp: path_integral_unique [OF has_path_integral_subpath] path_integrable_on)
  done

lemma path_integral_subpath_integral:
  assumes "f path_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}" "u \<le> v"
    shows "path_integral (subpath u v g) f =
           integral {u..v} (\<lambda>x. f(g x) * vector_derivative g (at x))"
  using assms has_path_integral_subpath path_integral_unique by blast

lemma path_integral_subpath_combine_less:
  assumes "f path_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}" "w \<in> {0..1}"
          "u<v" "v<w"
    shows "path_integral (subpath u v g) f + path_integral (subpath v w g) f =
           path_integral (subpath u w g) f"
  using assms apply (auto simp: path_integral_subpath_integral)
  apply (rule integral_combine, auto)
  apply (rule integrable_on_subcbox [where a=u and b=w and s = "{0..1}", simplified])
  apply (auto simp: path_integrable_on)
  done

lemma path_integral_subpath_combine:
  assumes "f path_integrable_on g" "valid_path g" "u \<in> {0..1}" "v \<in> {0..1}" "w \<in> {0..1}"
    shows "path_integral (subpath u v g) f + path_integral (subpath v w g) f =
           path_integral (subpath u w g) f"
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
      using path_integral_subpath_combine_less [of f g u v w]
            path_integral_subpath_combine_less [of f g u w v]
            path_integral_subpath_combine_less [of f g v u w]
            path_integral_subpath_combine_less [of f g v w u]
            path_integral_subpath_combine_less [of f g w u v]
            path_integral_subpath_combine_less [of f g w v u]
      apply simp
      apply (elim disjE)
      apply (auto simp: * path_integral_reversepath path_integrable_subpath
                   valid_path_reversepath valid_path_subpath algebra_simps)
      done
next
  case False
  then show ?thesis
    apply (auto simp: path_integral_subpath_refl)
    using assms
    by (metis eq_neg_iff_add_eq_0 path_integrable_subpath path_integral_reversepath reversepath_subpath valid_path_subpath)
qed

lemma path_integral_integral:
  shows "path_integral g f = integral {0..1} (\<lambda>x. f (g x) * vector_derivative g (at x))"
  by (simp add: path_integral_def integral_def has_path_integral)


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
    apply (rule mem_convex)
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

lemma path_integral_primitive_lemma:
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

lemma path_integral_primitive:
  assumes "\<And>x. x \<in> s \<Longrightarrow> (f has_field_derivative f' x) (at x within s)"
      and "valid_path g" "path_image g \<subseteq> s"
    shows "(f' has_path_integral (f(pathfinish g) - f(pathstart g))) g"
  using assms
  apply (simp add: valid_path_def path_image_def pathfinish_def pathstart_def has_path_integral_def)
  apply (auto intro!: piecewise_C1_imp_differentiable path_integral_primitive_lemma [of 0 1 s])
  done

corollary Cauchy_theorem_primitive:
  assumes "\<And>x. x \<in> s \<Longrightarrow> (f has_field_derivative f' x) (at x within s)"
      and "valid_path g"  "path_image g \<subseteq> s" "pathfinish g = pathstart g"
    shows "(f' has_path_integral 0) g"
  using assms
  by (metis diff_self path_integral_primitive)


text\<open>Existence of path integral for continuous function\<close>
lemma path_integrable_continuous_linepath:
  assumes "continuous_on (closed_segment a b) f"
  shows "f path_integrable_on (linepath a b)"
proof -
  have "continuous_on {0..1} ((\<lambda>x. f x * (b - a)) o linepath a b)"
    apply (rule continuous_on_compose [OF continuous_on_linepath], simp add: linepath_image_01)
    apply (rule continuous_intros | simp add: assms)+
    done
  then show ?thesis
    apply (simp add: path_integrable_on_def has_path_integral_def integrable_on_def [symmetric])
    apply (rule integrable_continuous [of 0 "1::real", simplified])
    apply (rule continuous_on_eq [where f = "\<lambda>x. f(linepath a b x)*(b - a)"])
    apply (auto simp: vector_derivative_linepath_within)
    done
qed

lemma has_field_der_id: "((\<lambda>x. x\<^sup>2 / 2) has_field_derivative x) (at x)"
  by (rule has_derivative_imp_has_field_derivative)
     (rule derivative_intros | simp)+

lemma path_integral_id [simp]: "path_integral (linepath a b) (\<lambda>y. y) = (b^2 - a^2)/2"
  apply (rule path_integral_unique)
  using path_integral_primitive [of UNIV "\<lambda>x. x^2/2" "\<lambda>x. x" "linepath a b"]
  apply (auto simp: field_simps has_field_der_id)
  done

lemma path_integrable_on_const [iff]: "(\<lambda>x. c) path_integrable_on (linepath a b)"
  by (simp add: continuous_on_const path_integrable_continuous_linepath)

lemma path_integrable_on_id [iff]: "(\<lambda>x. x) path_integrable_on (linepath a b)"
  by (simp add: continuous_on_id path_integrable_continuous_linepath)


subsection\<open>Arithmetical combining theorems\<close>

lemma has_path_integral_neg:
    "(f has_path_integral i) g \<Longrightarrow> ((\<lambda>x. -(f x)) has_path_integral (-i)) g"
  by (simp add: has_integral_neg has_path_integral_def)

lemma has_path_integral_add:
    "\<lbrakk>(f1 has_path_integral i1) g; (f2 has_path_integral i2) g\<rbrakk>
     \<Longrightarrow> ((\<lambda>x. f1 x + f2 x) has_path_integral (i1 + i2)) g"
  by (simp add: has_integral_add has_path_integral_def algebra_simps)

lemma has_path_integral_diff:
  "\<lbrakk>(f1 has_path_integral i1) g; (f2 has_path_integral i2) g\<rbrakk>
         \<Longrightarrow> ((\<lambda>x. f1 x - f2 x) has_path_integral (i1 - i2)) g"
  by (simp add: has_integral_sub has_path_integral_def algebra_simps)

lemma has_path_integral_lmul:
  "(f has_path_integral i) g \<Longrightarrow> ((\<lambda>x. c * (f x)) has_path_integral (c*i)) g"
apply (simp add: has_path_integral_def)
apply (drule has_integral_mult_right)
apply (simp add: algebra_simps)
done

lemma has_path_integral_rmul:
  "(f has_path_integral i) g \<Longrightarrow> ((\<lambda>x. (f x) * c) has_path_integral (i*c)) g"
apply (drule has_path_integral_lmul)
apply (simp add: mult.commute)
done

lemma has_path_integral_div:
  "(f has_path_integral i) g \<Longrightarrow> ((\<lambda>x. f x/c) has_path_integral (i/c)) g"
  by (simp add: field_class.field_divide_inverse) (metis has_path_integral_rmul)

lemma has_path_integral_eq:
    "\<lbrakk>(f has_path_integral y) p; \<And>x. x \<in> path_image p \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> (g has_path_integral y) p"
apply (simp add: path_image_def has_path_integral_def)
by (metis (no_types, lifting) image_eqI has_integral_eq)

lemma has_path_integral_bound_linepath:
  assumes "(f has_path_integral i) (linepath a b)"
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
    using assms * unfolding has_path_integral_def
    apply (auto simp: norm_mult)
    done
  then show ?thesis
    by (auto simp: content_real)
qed

(*UNUSED
lemma has_path_integral_bound_linepath_strong:
  fixes a :: real and f :: "complex \<Rightarrow> real"
  assumes "(f has_path_integral i) (linepath a b)"
          "finite k"
          "0 \<le> B" "\<And>x::real. x \<in> closed_segment a b - k \<Longrightarrow> norm(f x) \<le> B"
    shows "norm i \<le> B*norm(b - a)"
*)

lemma has_path_integral_const_linepath: "((\<lambda>x. c) has_path_integral c*(b - a))(linepath a b)"
  unfolding has_path_integral_linepath
  by (metis content_real diff_0_right has_integral_const_real lambda_one of_real_1 scaleR_conv_of_real zero_le_one)

lemma has_path_integral_0: "((\<lambda>x. 0) has_path_integral 0) g"
  by (simp add: has_path_integral_def)

lemma has_path_integral_is_0:
    "(\<And>z. z \<in> path_image g \<Longrightarrow> f z = 0) \<Longrightarrow> (f has_path_integral 0) g"
  by (rule has_path_integral_eq [OF has_path_integral_0]) auto

lemma has_path_integral_setsum:
    "\<lbrakk>finite s; \<And>a. a \<in> s \<Longrightarrow> (f a has_path_integral i a) p\<rbrakk>
     \<Longrightarrow> ((\<lambda>x. setsum (\<lambda>a. f a x) s) has_path_integral setsum i s) p"
  by (induction s rule: finite_induct) (auto simp: has_path_integral_0 has_path_integral_add)


subsection \<open>Operations on path integrals\<close>

lemma path_integral_const_linepath [simp]: "path_integral (linepath a b) (\<lambda>x. c) = c*(b - a)"
  by (rule path_integral_unique [OF has_path_integral_const_linepath])

lemma path_integral_neg:
    "f path_integrable_on g \<Longrightarrow> path_integral g (\<lambda>x. -(f x)) = -(path_integral g f)"
  by (simp add: path_integral_unique has_path_integral_integral has_path_integral_neg)

lemma path_integral_add:
    "f1 path_integrable_on g \<Longrightarrow> f2 path_integrable_on g \<Longrightarrow> path_integral g (\<lambda>x. f1 x + f2 x) =
                path_integral g f1 + path_integral g f2"
  by (simp add: path_integral_unique has_path_integral_integral has_path_integral_add)

lemma path_integral_diff:
    "f1 path_integrable_on g \<Longrightarrow> f2 path_integrable_on g \<Longrightarrow> path_integral g (\<lambda>x. f1 x - f2 x) =
                path_integral g f1 - path_integral g f2"
  by (simp add: path_integral_unique has_path_integral_integral has_path_integral_diff)

lemma path_integral_lmul:
  shows "f path_integrable_on g
           \<Longrightarrow> path_integral g (\<lambda>x. c * f x) = c*path_integral g f"
  by (simp add: path_integral_unique has_path_integral_integral has_path_integral_lmul)

lemma path_integral_rmul:
  shows "f path_integrable_on g
        \<Longrightarrow> path_integral g (\<lambda>x. f x * c) = path_integral g f * c"
  by (simp add: path_integral_unique has_path_integral_integral has_path_integral_rmul)

lemma path_integral_div:
  shows "f path_integrable_on g
        \<Longrightarrow> path_integral g (\<lambda>x. f x / c) = path_integral g f / c"
  by (simp add: path_integral_unique has_path_integral_integral has_path_integral_div)

lemma path_integral_eq:
    "(\<And>x. x \<in> path_image p \<Longrightarrow> f x = g x) \<Longrightarrow> path_integral p f = path_integral p g"
  by (simp add: path_integral_def) (metis has_path_integral_eq)

lemma path_integral_eq_0:
    "(\<And>z. z \<in> path_image g \<Longrightarrow> f z = 0) \<Longrightarrow> path_integral g f = 0"
  by (simp add: has_path_integral_is_0 path_integral_unique)

lemma path_integral_bound_linepath:
  shows
    "\<lbrakk>f path_integrable_on (linepath a b);
      0 \<le> B; \<And>x. x \<in> closed_segment a b \<Longrightarrow> norm(f x) \<le> B\<rbrakk>
     \<Longrightarrow> norm(path_integral (linepath a b) f) \<le> B*norm(b - a)"
  apply (rule has_path_integral_bound_linepath [of f])
  apply (auto simp: has_path_integral_integral)
  done

lemma path_integral_0: "path_integral g (\<lambda>x. 0) = 0"
  by (simp add: path_integral_unique has_path_integral_0)

lemma path_integral_setsum:
    "\<lbrakk>finite s; \<And>a. a \<in> s \<Longrightarrow> (f a) path_integrable_on p\<rbrakk>
     \<Longrightarrow> path_integral p (\<lambda>x. setsum (\<lambda>a. f a x) s) = setsum (\<lambda>a. path_integral p (f a)) s"
  by (auto simp: path_integral_unique has_path_integral_setsum has_path_integral_integral)

lemma path_integrable_eq:
    "\<lbrakk>f path_integrable_on p; \<And>x. x \<in> path_image p \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> g path_integrable_on p"
  unfolding path_integrable_on_def
  by (metis has_path_integral_eq)


subsection \<open>Arithmetic theorems for path integrability\<close>

lemma path_integrable_neg:
    "f path_integrable_on g \<Longrightarrow> (\<lambda>x. -(f x)) path_integrable_on g"
  using has_path_integral_neg path_integrable_on_def by blast

lemma path_integrable_add:
    "\<lbrakk>f1 path_integrable_on g; f2 path_integrable_on g\<rbrakk> \<Longrightarrow> (\<lambda>x. f1 x + f2 x) path_integrable_on g"
  using has_path_integral_add path_integrable_on_def
  by fastforce

lemma path_integrable_diff:
    "\<lbrakk>f1 path_integrable_on g; f2 path_integrable_on g\<rbrakk> \<Longrightarrow> (\<lambda>x. f1 x - f2 x) path_integrable_on g"
  using has_path_integral_diff path_integrable_on_def
  by fastforce

lemma path_integrable_lmul:
    "f path_integrable_on g \<Longrightarrow> (\<lambda>x. c * f x) path_integrable_on g"
  using has_path_integral_lmul path_integrable_on_def
  by fastforce

lemma path_integrable_rmul:
    "f path_integrable_on g \<Longrightarrow> (\<lambda>x. f x * c) path_integrable_on g"
  using has_path_integral_rmul path_integrable_on_def
  by fastforce

lemma path_integrable_div:
    "f path_integrable_on g \<Longrightarrow> (\<lambda>x. f x / c) path_integrable_on g"
  using has_path_integral_div path_integrable_on_def
  by fastforce

lemma path_integrable_setsum:
    "\<lbrakk>finite s; \<And>a. a \<in> s \<Longrightarrow> (f a) path_integrable_on p\<rbrakk>
     \<Longrightarrow> (\<lambda>x. setsum (\<lambda>a. f a x) s) path_integrable_on p"
   unfolding path_integrable_on_def
   by (metis has_path_integral_setsum)


subsection\<open>Reversing a path integral\<close>

lemma has_path_integral_reverse_linepath:
    "(f has_path_integral i) (linepath a b)
     \<Longrightarrow> (f has_path_integral (-i)) (linepath b a)"
  using has_path_integral_reversepath valid_path_linepath by fastforce

lemma path_integral_reverse_linepath:
    "continuous_on (closed_segment a b) f
     \<Longrightarrow> path_integral (linepath a b) f = - (path_integral(linepath b a) f)"
apply (rule path_integral_unique)
apply (rule has_path_integral_reverse_linepath)
by (simp add: closed_segment_commute path_integrable_continuous_linepath has_path_integral_integral)


(* Splitting a path integral in a flat way.*)

lemma has_path_integral_split:
  assumes f: "(f has_path_integral i) (linepath a c)" "(f has_path_integral j) (linepath c b)"
      and k: "0 \<le> k" "k \<le> 1"
      and c: "c - a = k *\<^sub>R (b - a)"
    shows "(f has_path_integral (i + j)) (linepath a b)"
proof (cases "k = 0 \<or> k = 1")
  case True
  then show ?thesis
    using assms
    apply auto
    apply (metis add.left_neutral has_path_integral_trivial has_path_integral_unique)
    apply (metis add.right_neutral has_path_integral_trivial has_path_integral_unique)
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
    apply (simp add: has_path_integral_linepath)
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
    apply (auto simp: hull_inc c' Convex.mem_convex)
    done
qed

lemma path_integral_split:
  assumes f: "continuous_on (closed_segment a b) f"
      and k: "0 \<le> k" "k \<le> 1"
      and c: "c - a = k *\<^sub>R (b - a)"
    shows "path_integral(linepath a b) f = path_integral(linepath a c) f + path_integral(linepath c b) f"
proof -
  have c': "c = (1 - k) *\<^sub>R a + k *\<^sub>R b"
    using c by (simp add: algebra_simps)
  have *: "continuous_on (closed_segment a c) f" "continuous_on (closed_segment c b) f"
    apply (rule_tac [!] continuous_on_subset [OF f])
    apply (simp_all add: segment_convex_hull)
    apply (rule_tac [!] convex_hull_subset)
    using assms
    apply (auto simp: hull_inc c' Convex.mem_convex)
    done
  show ?thesis
    apply (rule path_integral_unique)
    apply (rule has_path_integral_split [OF has_path_integral_integral has_path_integral_integral k c])
    apply (rule path_integrable_continuous_linepath *)+
    done
qed

lemma path_integral_split_linepath:
  assumes f: "continuous_on (closed_segment a b) f"
      and c: "c \<in> closed_segment a b"
    shows "path_integral(linepath a b) f = path_integral(linepath a c) f + path_integral(linepath c b) f"
  using c
  by (auto simp: closed_segment_def algebra_simps intro!: path_integral_split [OF f])

(* The special case of midpoints used in the main quadrisection.*)

lemma has_path_integral_midpoint:
  assumes "(f has_path_integral i) (linepath a (midpoint a b))"
          "(f has_path_integral j) (linepath (midpoint a b) b)"
    shows "(f has_path_integral (i + j)) (linepath a b)"
  apply (rule has_path_integral_split [where c = "midpoint a b" and k = "1/2"])
  using assms
  apply (auto simp: midpoint_def algebra_simps scaleR_conv_of_real)
  done

lemma path_integral_midpoint:
   "continuous_on (closed_segment a b) f
    \<Longrightarrow> path_integral (linepath a b) f =
        path_integral (linepath a (midpoint a b)) f + path_integral (linepath (midpoint a b) b) f"
  apply (rule path_integral_split [where c = "midpoint a b" and k = "1/2"])
  using assms
  apply (auto simp: midpoint_def algebra_simps scaleR_conv_of_real)
  done


text\<open>A couple of special case lemmas that are useful below\<close>

lemma triangle_linear_has_chain_integral:
    "((\<lambda>x. m*x + d) has_path_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
  apply (rule Cauchy_theorem_primitive [of UNIV "\<lambda>x. m/2 * x^2 + d*x"])
  apply (auto intro!: derivative_eq_intros)
  done

lemma has_chain_integral_chain_integral3:
     "(f has_path_integral i) (linepath a b +++ linepath b c +++ linepath c d)
      \<Longrightarrow> path_integral (linepath a b) f + path_integral (linepath b c) f + path_integral (linepath c d) f = i"
  apply (subst path_integral_unique [symmetric], assumption)
  apply (drule has_path_integral_integrable)
  apply (simp add: valid_path_join)
  done

subsection\<open>Reversing the order in a double path integral\<close>

text\<open>The condition is stronger than needed but it's often true in typical situations\<close>

lemma fst_im_cbox [simp]: "cbox c d \<noteq> {} \<Longrightarrow> (fst ` cbox (a,c) (b,d)) = cbox a b"
  by (auto simp: cbox_Pair_eq)

lemma snd_im_cbox [simp]: "cbox a b \<noteq> {} \<Longrightarrow> (snd ` cbox (a,c) (b,d)) = cbox c d"
  by (auto simp: cbox_Pair_eq)

lemma path_integral_swap:
  assumes fcon:  "continuous_on (path_image g \<times> path_image h) (\<lambda>(y1,y2). f y1 y2)"
      and vp:    "valid_path g" "valid_path h"
      and gvcon: "continuous_on {0..1} (\<lambda>t. vector_derivative g (at t))"
      and hvcon: "continuous_on {0..1} (\<lambda>t. vector_derivative h (at t))"
  shows "path_integral g (\<lambda>w. path_integral h (f w)) =
         path_integral h (\<lambda>z. path_integral g (\<lambda>w. f w z))"
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
  have "integral {0..1} (\<lambda>x. path_integral h (f (g x)) * vector_derivative g (at x)) =
        integral {0..1} (\<lambda>x. path_integral h (\<lambda>y. f (g x) y * vector_derivative g (at x)))"
    apply (rule integral_cong [OF path_integral_rmul [symmetric]])
    apply (clarsimp simp: path_integrable_on)
    apply (rule integrable_continuous_real)
    apply (rule continuous_on_mult [OF _ hvcon])
    apply (subst fgh1)
    apply (rule fcon_im1 hcon continuous_intros | simp)+
    done
  also have "... = integral {0..1}
                     (\<lambda>y. path_integral g (\<lambda>x. f x (h y) * vector_derivative h (at y)))"
    apply (simp add: path_integral_integral)
    apply (subst integral_swap_continuous [where 'a = real and 'b = real, of 0 0 1 1, simplified])
    apply (rule fgh gvcon' hvcon' continuous_intros | simp add: split_def)+
    apply (simp add: algebra_simps)
    done
  also have "... = path_integral h (\<lambda>z. path_integral g (\<lambda>w. f w z))"
    apply (simp add: path_integral_integral)
    apply (rule integral_cong)
    apply (subst integral_mult_left [symmetric])
    apply (blast intro: vdg)
    apply (simp add: algebra_simps)
    done
  finally show ?thesis
    by (simp add: path_integral_integral)
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
              norm (path_integral(linepath a b) f + path_integral(linepath b c) f + path_integral(linepath c a) f)"
  shows "\<exists>a' b' c'.
           a' \<in> convex hull {a,b,c} \<and> b' \<in> convex hull {a,b,c} \<and> c' \<in> convex hull {a,b,c} \<and>
           dist a' b' \<le> K/2  \<and>  dist b' c' \<le> K/2  \<and>  dist c' a' \<le> K/2  \<and>
           e * (K/2)^2 \<le> norm(path_integral(linepath a' b') f + path_integral(linepath b' c') f + path_integral(linepath c' a') f)"
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
  let ?pathint = "\<lambda>x y. path_integral(linepath x y) f"
  have *: "?pathint a b + ?pathint b c + ?pathint c a =
          (?pathint a c' + ?pathint c' b' + ?pathint b' a) +
          (?pathint a' c' + ?pathint c' b + ?pathint b a') +
          (?pathint a' c + ?pathint c b' + ?pathint b' a') +
          (?pathint a' b' + ?pathint b' c' + ?pathint c' a')"
    apply (simp add: fcont' path_integral_reverse_linepath)
    apply (simp add: a'_def b'_def c'_def path_integral_midpoint fabc)
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
              \<longrightarrow> norm(path_integral(linepath a b) f + path_integral(linepath b c) f +
                       path_integral(linepath c a) f)
                  \<le> e*(dist a b + dist b c + dist c a)^2"
           (is "\<exists>k>0. \<forall>a b c. _ \<longrightarrow> ?normle a b c")
proof -
  have le_of_3: "\<And>a x y z. \<lbrakk>0 \<le> x*y; 0 \<le> x*z; 0 \<le> y*z; a \<le> (e*(x + y + z))*x + (e*(x + y + z))*y + (e*(x + y + z))*z\<rbrakk>
                     \<Longrightarrow> a \<le> e*(x + y + z)^2"
    by (simp add: algebra_simps power2_eq_square)
  have disj_le: "\<lbrakk>x \<le> a \<or> x \<le> b \<or> x \<le> c; 0 \<le> a; 0 \<le> b; 0 \<le> c\<rbrakk> \<Longrightarrow> x \<le> a + b + c"
             for x::real and a b c
    by linarith
  have fabc: "f path_integrable_on linepath a b" "f path_integrable_on linepath b c" "f path_integrable_on linepath c a"
              if "convex hull {a, b, c} \<subseteq> s" for a b c
    using segments_subset_convex_hull that
    by (metis continuous_on_subset f path_integrable_continuous_linepath)+
  note path_bound = has_path_integral_bound_linepath [simplified norm_minus_commute, OF has_path_integral_integral]
  { fix f' a b c d
    assume d: "0 < d"
       and f': "\<And>y. \<lbrakk>cmod (y - x) \<le> d; y \<in> s\<rbrakk> \<Longrightarrow> cmod (f y - f x - f' * (y - x)) \<le> e * cmod (y - x)"
       and le: "cmod (a - b) \<le> d" "cmod (b - c) \<le> d" "cmod (c - a) \<le> d"
       and xc: "x \<in> convex hull {a, b, c}"
       and s: "convex hull {a, b, c} \<subseteq> s"
    have pa: "path_integral (linepath a b) f + path_integral (linepath b c) f + path_integral (linepath c a) f =
              path_integral (linepath a b) (\<lambda>y. f y - f x - f'*(y - x)) +
              path_integral (linepath b c) (\<lambda>y. f y - f x - f'*(y - x)) +
              path_integral (linepath c a) (\<lambda>y. f y - f x - f'*(y - x))"
      apply (simp add: path_integral_diff path_integral_lmul path_integrable_lmul path_integrable_diff fabc [OF s])
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
      apply (simp_all add: path_integral_diff path_integral_lmul path_integrable_lmul path_integrable_diff fabc)
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
    shows "(f has_path_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
proof -
  have contf: "continuous_on (convex hull {a,b,c}) f"
    by (metis assms holomorphic_on_imp_continuous_on)
  let ?pathint = "\<lambda>x y. path_integral(linepath x y) f"
  { fix y::complex
    assume fy: "(f has_path_integral y) (linepath a b +++ linepath b c +++ linepath c a)"
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
  moreover have "f path_integrable_on (linepath a b +++ linepath b c +++ linepath c a)"
    by simp (meson contf continuous_on_subset path_integrable_continuous_linepath segments_subset_convex_hull(1)
                   segments_subset_convex_hull(3) segments_subset_convex_hull(5))
  ultimately show ?thesis
    using has_path_integral_integral by fastforce
qed


subsection\<open>Version needing function holomorphic in interior only\<close>

lemma Cauchy_theorem_flat_lemma:
  assumes f: "continuous_on (convex hull {a,b,c}) f"
      and c: "c - a = k *\<^sub>R (b - a)"
      and k: "0 \<le> k"
    shows "path_integral (linepath a b) f + path_integral (linepath b c) f +
          path_integral (linepath c a) f = 0"
proof -
  have fabc: "continuous_on (closed_segment a b) f" "continuous_on (closed_segment b c) f" "continuous_on (closed_segment c a) f"
    using f continuous_on_subset segments_subset_convex_hull by metis+
  show ?thesis
  proof (cases "k \<le> 1")
    case True show ?thesis
      by (simp add: path_integral_split [OF fabc(1) k True c] path_integral_reverse_linepath fabc)
  next
    case False then show ?thesis
      using fabc c
      apply (subst path_integral_split [of a c f "1/k" b, symmetric])
      apply (metis closed_segment_commute fabc(3))
      apply (auto simp: k path_integral_reverse_linepath)
      done
  qed
qed

lemma Cauchy_theorem_flat:
  assumes f: "continuous_on (convex hull {a,b,c}) f"
      and c: "c - a = k *\<^sub>R (b - a)"
    shows "path_integral (linepath a b) f +
           path_integral (linepath b c) f +
           path_integral (linepath c a) f = 0"
proof (cases "0 \<le> k")
  case True with assms show ?thesis
    by (blast intro: Cauchy_theorem_flat_lemma)
next
  case False
  have "continuous_on (closed_segment a b) f" "continuous_on (closed_segment b c) f" "continuous_on (closed_segment c a) f"
    using f continuous_on_subset segments_subset_convex_hull by metis+
  moreover have "path_integral (linepath b a) f + path_integral (linepath a c) f +
        path_integral (linepath c b) f = 0"
    apply (rule Cauchy_theorem_flat_lemma [of b a c f "1-k"])
    using False c
    apply (auto simp: f insert_commute scaleR_conv_of_real algebra_simps)
    done
  ultimately show ?thesis
    apply (auto simp: path_integral_reverse_linepath)
    using add_eq_0_iff by force
qed


lemma Cauchy_theorem_triangle_interior:
  assumes contf: "continuous_on (convex hull {a,b,c}) f"
      and holf:  "f holomorphic_on interior (convex hull {a,b,c})"
     shows "(f has_path_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
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
    assume fy: "(f has_path_integral y) (linepath a b +++ linepath b c +++ linepath c a)"
       and ynz: "y \<noteq> 0"
    have pi_eq_y: "path_integral (linepath a b) f + path_integral (linepath b c) f + path_integral (linepath c a) f = y"
      by (rule has_chain_integral_chain_integral3 [OF fy])
    have ?thesis
    proof (cases "c=a \<or> a=b \<or> b=c")
      case True then show ?thesis
        using Cauchy_theorem_flat [OF contf, of 0]
        using has_chain_integral_chain_integral3 [OF fy] ynz
        by (force simp: fabc path_integral_reverse_linepath)
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
          apply (simp add: fabc add_eq_0_iff path_integral_reverse_linepath)
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
        let ?pathint = "\<lambda>x y. path_integral(linepath x y) f"
        have e: "0 < e" "e \<le> 1" "e \<le> d1 / (4 * C)" "e \<le> cmod y / 24 / C / B"
          using d1_pos `C>0` `B>0` ynz by (simp_all add: e_def)
        then have eCB: "24 * e * C * B \<le> cmod y"
          using `C>0` `B>0`  by (simp add: field_simps)
        have e_le_d1: "e * (4 * C) \<le> d1"
          using e `C>0` by (simp add: field_simps)
        have "shrink a \<in> interior(convex hull {a,b,c})"
             "shrink b \<in> interior(convex hull {a,b,c})"
             "shrink c \<in> interior(convex hull {a,b,c})"
          using d e by (auto simp: hull_inc mem_interior_convex_shrink shrink_def)
        then have fhp0: "(f has_path_integral 0)
                (linepath (shrink a) (shrink b) +++ linepath (shrink b) (shrink c) +++ linepath (shrink c) (shrink a))"
          by (simp add: Cauchy_theorem_triangle holomorphic_on_subset [OF holf] hull_minimal convex_interior)
        then have f_0_shrink: "?pathint (shrink a) (shrink b) + ?pathint (shrink b) (shrink c) + ?pathint (shrink c) (shrink a) = 0"
          by (simp add: has_chain_integral_chain_integral3)
        have fpi_abc: "f path_integrable_on linepath (shrink a) (shrink b)"
                      "f path_integrable_on linepath (shrink b) (shrink c)"
                      "f path_integrable_on linepath (shrink c) (shrink a)"
          using fhp0  by (auto simp: valid_path_join dest: has_path_integral_integrable)
        have cmod_shr: "\<And>x y. cmod (shrink y - shrink x - (y - x)) = e * cmod (x - y)"
          using e by (simp add: shrink_def real_vector.scale_right_diff_distrib [symmetric])
        have sh_eq: "\<And>a b d::complex. (b - e *\<^sub>R (b - d)) - (a - e *\<^sub>R (a - d)) - (b - a) = e *\<^sub>R (a - b)"
          by (simp add: algebra_simps)
        have "cmod y / (24 * C) \<le> cmod y / cmod (b - a) / 12"
          using False `C>0` diff_2C [of b a] ynz
          by (auto simp: divide_simps hull_inc)
        have less_C: "\<lbrakk>u \<in> convex hull {a, b, c}; 0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> x * cmod u < C" for x u
          apply (cases "x=0", simp add: `0<C`)
          using Cno [of u] mult_left_le_one_le [of "cmod u" x] le_less_trans norm_ge_zero by blast
        { fix u v
          assume uv: "u \<in> convex hull {a, b, c}" "v \<in> convex hull {a, b, c}" "u\<noteq>v"
             and fpi_uv: "f path_integrable_on linepath (shrink u) (shrink v)"
          have shr_uv: "shrink u \<in> interior(convex hull {a,b,c})"
                       "shrink v \<in> interior(convex hull {a,b,c})"
            using d e uv
            by (auto simp: hull_inc mem_interior_convex_shrink shrink_def)
          have cmod_fuv: "\<And>x. 0\<le>x \<Longrightarrow> x\<le>1 \<Longrightarrow> cmod (f (linepath (shrink u) (shrink v) x)) \<le> B"
            using shr_uv by (blast intro: Bnf linepath_in_convex_hull interior_subset [THEN subsetD])
          have By_uv: "B * (12 * (e * cmod (u - v))) \<le> cmod y"
            apply (rule order_trans [OF _ eCB])
            using e `B>0` diff_2C [of u v] uv
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
              using `e>0`
              apply (simp add: ll norm_mult scaleR_diff_right)
              apply (rule less_le_trans [OF _ e_le_d1])
              using cmod_less_4C
              apply (force intro: norm_triangle_lt)
              done
            have "cmod (f (linepath (shrink u) (shrink v) x) - f (linepath u v x)) < cmod y / (24 * C)"
              using x uv shr_uv cmod_less_dt
              by (auto simp: hull_inc intro: d1 interior_subset [THEN subsetD] linepath_in_convex_hull)
            also have "... \<le> cmod y / cmod (v - u) / 12"
              using False uv `C>0` diff_2C [of v u] ynz
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
              using By_uv e `0 < B` `0 < C` x ynz
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
            using ynz `0 < B` `0 < C`
            apply (simp_all del: le_divide_eq_numeral1)
            apply (simp add: has_integral_sub has_path_integral_linepath [symmetric] has_path_integral_integral
                             fpi_uv f_uv path_integrable_continuous_linepath, clarify)
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
          by (force simp: ynz `0 < C` dist_norm)
        then show ?thesis ..
      qed
  }
  moreover have "f path_integrable_on (linepath a b +++ linepath b c +++ linepath c a)"
    using fabc path_integrable_continuous_linepath by auto
  ultimately show ?thesis
    using has_path_integral_integral by fastforce
qed


subsection\<open>Version allowing finite number of exceptional points\<close>

lemma Cauchy_theorem_triangle_cofinite:
  assumes "continuous_on (convex hull {a,b,c}) f"
      and "finite s"
      and "(\<And>x. x \<in> interior(convex hull {a,b,c}) - s \<Longrightarrow> f complex_differentiable (at x))"
     shows "(f has_path_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
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
      show "(f has_path_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
        apply (rule less.hyps [of "s'"])
        using False d `finite s` interior_subset
        apply (auto intro!: less.prems)
        done
    next
      case True
      have *: "convex hull {a, b, d} \<subseteq> convex hull {a, b, c}"
        by (meson True hull_subset insert_subset convex_hull_subset)
      have abd: "(f has_path_integral 0) (linepath a b +++ linepath b d +++ linepath d a)"
        apply (rule less.hyps [of "s'"])
        using True d  `finite s` not_in_interior_convex_hull_3
        apply (auto intro!: less.prems continuous_on_subset [OF  _ *])
        apply (metis * insert_absorb insert_subset interior_mono)
        done
      have *: "convex hull {b, c, d} \<subseteq> convex hull {a, b, c}"
        by (meson True hull_subset insert_subset convex_hull_subset)
      have bcd: "(f has_path_integral 0) (linepath b c +++ linepath c d +++ linepath d b)"
        apply (rule less.hyps [of "s'"])
        using True d  `finite s` not_in_interior_convex_hull_3
        apply (auto intro!: less.prems continuous_on_subset [OF _ *])
        apply (metis * insert_absorb insert_subset interior_mono)
        done
      have *: "convex hull {c, a, d} \<subseteq> convex hull {a, b, c}"
        by (meson True hull_subset insert_subset convex_hull_subset)
      have cad: "(f has_path_integral 0) (linepath c a +++ linepath a d +++ linepath d c)"
        apply (rule less.hyps [of "s'"])
        using True d  `finite s` not_in_interior_convex_hull_3
        apply (auto intro!: less.prems continuous_on_subset [OF _ *])
        apply (metis * insert_absorb insert_subset interior_mono)
        done
      have "f path_integrable_on linepath a b"
        using less.prems
        by (metis continuous_on_subset insert_commute path_integrable_continuous_linepath segments_subset_convex_hull(3))
      moreover have "f path_integrable_on linepath b c"
        using less.prems
        by (metis continuous_on_subset path_integrable_continuous_linepath segments_subset_convex_hull(3))
      moreover have "f path_integrable_on linepath c a"
        using less.prems
        by (metis continuous_on_subset insert_commute path_integrable_continuous_linepath segments_subset_convex_hull(3))
      ultimately have fpi: "f path_integrable_on (linepath a b +++ linepath b c +++ linepath c a)"
        by auto
      { fix y::complex
        assume fy: "(f has_path_integral y) (linepath a b +++ linepath b c +++ linepath c a)"
           and ynz: "y \<noteq> 0"
        have cont_ad: "continuous_on (closed_segment a d) f"
          by (meson "*" continuous_on_subset less.prems(1) segments_subset_convex_hull(3))
        have cont_bd: "continuous_on (closed_segment b d) f"
          by (meson True closed_segment_subset_convex_hull continuous_on_subset hull_subset insert_subset less.prems(1))
        have cont_cd: "continuous_on (closed_segment c d) f"
          by (meson "*" continuous_on_subset less.prems(1) segments_subset_convex_hull(2))
        have "path_integral  (linepath a b) f = - (path_integral (linepath b d) f + (path_integral (linepath d a) f))"
                "path_integral  (linepath b c) f = - (path_integral (linepath c d) f + (path_integral (linepath d b) f))"
                "path_integral  (linepath c a) f = - (path_integral (linepath a d) f + path_integral (linepath d c) f)"
            using has_chain_integral_chain_integral3 [OF abd]
                  has_chain_integral_chain_integral3 [OF bcd]
                  has_chain_integral_chain_integral3 [OF cad]
            by (simp_all add: algebra_simps add_eq_0_iff)
        then have ?thesis
          using cont_ad cont_bd cont_cd fy has_chain_integral_chain_integral3 path_integral_reverse_linepath by fastforce
      }
      then show ?thesis
        using fpi path_integrable_on_def by blast
    qed
  qed
qed


subsection\<open>Cauchy's theorem for an open starlike set\<close>

lemma starlike_convex_subset:
  assumes s: "a \<in> s" "closed_segment b c \<subseteq> s" and subs: "\<And>x. x \<in> s \<Longrightarrow> closed_segment a x \<subseteq> s"
    shows "convex hull {a,b,c} \<subseteq> s"
      using s
      apply (clarsimp simp add: convex_hull_insert [of "{b,c}" a] segment_convex_hull)
      apply (meson subs convexD convex_segment ends_in_segment(1) ends_in_segment(2) subsetCE)
      done

lemma triangle_path_integrals_starlike_primitive:
  assumes contf: "continuous_on s f"
      and s: "a \<in> s" "open s"
      and x: "x \<in> s"
      and subs: "\<And>y. y \<in> s \<Longrightarrow> closed_segment a y \<subseteq> s"
      and zer: "\<And>b c. closed_segment b c \<subseteq> s
                   \<Longrightarrow> path_integral (linepath a b) f + path_integral (linepath b c) f +
                       path_integral (linepath c a) f = 0"
    shows "((\<lambda>x. path_integral(linepath a x) f) has_field_derivative f x) (at x)"
proof -
  let ?pathint = "\<lambda>x y. path_integral(linepath x y) f"
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
      using zer [OF xys]  path_integral_reverse_linepath [OF cont_ayf]  add_eq_0_iff by force
  } note [simp] = this
  { fix e::real
    assume e: "0 < e"
    have cont_atx: "continuous (at x) f"
      using x s contf continuous_on_eq_continuous_at by blast
    then obtain d1 where d1: "d1>0" and d1_less: "\<And>y. cmod (y - x) < d1 \<Longrightarrow> cmod (f y - f x) < e/2"
      unfolding continuous_at Lim_at dist_norm  using e
      by (drule_tac x="e/2" in spec) force
    obtain d2 where d2: "d2>0" "ball x d2 \<subseteq> s" using  `open s` x
      by (auto simp: open_contains_ball)
    have dpos: "min d1 d2 > 0" using d1 d2 by simp
    { fix y
      assume yx: "y \<noteq> x" and close: "cmod (y - x) < min d1 d2"
      have y: "y \<in> s"
        using d2 close  by (force simp: dist_norm norm_minus_commute)
      have fxy: "f path_integrable_on linepath x y"
        apply (rule path_integrable_continuous_linepath)
        apply (rule continuous_on_subset [OF contf])
        using close d2
        apply (auto simp: dist_norm norm_minus_commute dest!: segment_bound(1))
        done
      then obtain i where i: "(f has_path_integral i) (linepath x y)"
        by (auto simp: path_integrable_on_def)
      then have "((\<lambda>w. f w - f x) has_path_integral (i - f x * (y - x))) (linepath x y)"
        by (rule has_path_integral_diff [OF _ has_path_integral_const_linepath])
      then have "cmod (i - f x * (y - x)) \<le> e / 2 * cmod (y - x)"
        apply (rule has_path_integral_bound_linepath [where B = "e/2"])
        using e apply simp
        apply (rule d1_less [THEN less_imp_le])
        using close segment_bound
        apply force
        done
      also have "... < e * cmod (y - x)"
        by (simp add: e yx)
      finally have "cmod (?pathint x y - f x * (y-x)) / cmod (y-x) < e"
        using i yx  by (simp add: path_integral_unique divide_less_eq)
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
    using `open s` x
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
    have "(f has_path_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
      apply (rule Cauchy_theorem_triangle_cofinite [OF _ k])
      using abcs apply (simp add: continuous_on_subset [OF contf])
      using * abcs interior_subset apply (auto intro: fcd)
      done
  } note 0 = this
  show ?thesis
    apply (intro exI ballI)
    apply (rule triangle_path_integrals_starlike_primitive [OF contf a os], assumption)
    apply (metis a_cs)
    apply (metis has_chain_integral_chain_integral3 0)
    done
qed

lemma Cauchy_theorem_starlike:
 "\<lbrakk>open s; starlike s; finite k; continuous_on s f;
   \<And>x. x \<in> s - k \<Longrightarrow> f complex_differentiable at x;
   valid_path g; path_image g \<subseteq> s; pathfinish g = pathstart g\<rbrakk>
   \<Longrightarrow> (f has_path_integral 0)  g"
  by (metis holomorphic_starlike_primitive Cauchy_theorem_primitive at_within_open)

lemma Cauchy_theorem_starlike_simple:
  "\<lbrakk>open s; starlike s; f holomorphic_on s; valid_path g; path_image g \<subseteq> s; pathfinish g = pathstart g\<rbrakk>
   \<Longrightarrow> (f has_path_integral 0) g"
apply (rule Cauchy_theorem_starlike [OF _ _ finite.emptyI])
apply (simp_all add: holomorphic_on_imp_continuous_on)
apply (metis at_within_open holomorphic_on_def)
done


subsection\<open>Cauchy's theorem for a convex set\<close>

text\<open>For a convex set we can avoid assuming openness and boundary analyticity\<close>

lemma triangle_path_integrals_convex_primitive:
  assumes contf: "continuous_on s f"
      and s: "a \<in> s" "convex s"
      and x: "x \<in> s"
      and zer: "\<And>b c. \<lbrakk>b \<in> s; c \<in> s\<rbrakk>
                   \<Longrightarrow> path_integral (linepath a b) f + path_integral (linepath b c) f +
                       path_integral (linepath c a) f = 0"
    shows "((\<lambda>x. path_integral(linepath a x) f) has_field_derivative f x) (at x within s)"
proof -
  let ?pathint = "\<lambda>x y. path_integral(linepath x y) f"
  { fix y
    assume y: "y \<in> s"
    have cont_ayf: "continuous_on (closed_segment a y) f"
      using s y  by (meson contf continuous_on_subset convex_contains_segment)
    have xys: "closed_segment x y \<subseteq> s"  (*?*)
      using convex_contains_segment s x y by auto
    have "?pathint a y - ?pathint a x = ?pathint x y"
      using zer [OF x y]  path_integral_reverse_linepath [OF cont_ayf]  add_eq_0_iff by force
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
      have fxy: "f path_integrable_on linepath x y"
        using convex_contains_segment s x y
        by (blast intro!: path_integrable_continuous_linepath continuous_on_subset [OF contf])
      then obtain i where i: "(f has_path_integral i) (linepath x y)"
        by (auto simp: path_integrable_on_def)
      then have "((\<lambda>w. f w - f x) has_path_integral (i - f x * (y - x))) (linepath x y)"
        by (rule has_path_integral_diff [OF _ has_path_integral_const_linepath])
      then have "cmod (i - f x * (y - x)) \<le> e / 2 * cmod (y - x)"
        apply (rule has_path_integral_bound_linepath [where B = "e/2"])
        using e apply simp
        apply (rule d1_less [THEN less_imp_le])
        using convex_contains_segment s(2) x y apply blast
        using close segment_bound(1) apply fastforce
        done
      also have "... < e * cmod (y - x)"
        by (simp add: e yx)
      finally have "cmod (?pathint x y - f x * (y-x)) / cmod (y-x) < e"
        using i yx  by (simp add: path_integral_unique divide_less_eq)
    }
    then have "\<exists>d>0. \<forall>y\<in>s. y \<noteq> x \<and> cmod (y-x) < d \<longrightarrow> cmod (?pathint x y - f x * (y-x)) / cmod (y-x) < e"
      using d1 by blast
  }
  then have *: "((\<lambda>y. (path_integral (linepath x y) f - f x * (y - x)) /\<^sub>R cmod (y - x)) ---> 0) (at x within s)"
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
    \<And>a b c. \<lbrakk>a \<in> s; b \<in> s; c \<in> s\<rbrakk> \<Longrightarrow> (f has_path_integral 0) (linepath a b +++ linepath b c +++ linepath c a)\<rbrakk>
         \<Longrightarrow> \<exists>g. \<forall>x \<in> s. (g has_field_derivative f x) (at x within s)"
  apply (cases "s={}")
  apply (simp_all add: ex_in_conv [symmetric])
  apply (blast intro: triangle_path_integrals_convex_primitive has_chain_integral_chain_integral3)
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
    "\<lbrakk>continuous_on s f;convex s; finite k;
      \<And>x. x \<in> interior s - k \<Longrightarrow> f complex_differentiable at x;
     valid_path g; path_image g \<subseteq> s;
     pathfinish g = pathstart g\<rbrakk> \<Longrightarrow> (f has_path_integral 0) g"
  by (metis holomorphic_convex_primitive Cauchy_theorem_primitive)

lemma Cauchy_theorem_convex_simple:
    "\<lbrakk>f holomorphic_on s; convex s;
     valid_path g; path_image g \<subseteq> s;
     pathfinish g = pathstart g\<rbrakk> \<Longrightarrow> (f has_path_integral 0) g"
  apply (rule Cauchy_theorem_convex)
  apply (simp_all add: holomorphic_on_imp_continuous_on)
  apply (rule finite.emptyI)
  using at_within_interior holomorphic_on_def interior_subset by fastforce


text\<open>In particular for a disc\<close>
lemma Cauchy_theorem_disc:
    "\<lbrakk>finite k; continuous_on (cball a e) f;
      \<And>x. x \<in> ball a e - k \<Longrightarrow> f complex_differentiable at x;
     valid_path g; path_image g \<subseteq> cball a e;
     pathfinish g = pathstart g\<rbrakk> \<Longrightarrow> (f has_path_integral 0) g"
  apply (rule Cauchy_theorem_convex)
  apply (auto simp: convex_cball interior_cball)
  done

lemma Cauchy_theorem_disc_simple:
    "\<lbrakk>f holomorphic_on (ball a e); valid_path g; path_image g \<subseteq> ball a e;
     pathfinish g = pathstart g\<rbrakk> \<Longrightarrow> (f has_path_integral 0) g"
by (simp add: Cauchy_theorem_convex_simple)


subsection\<open>Generalize integrability to local primitives\<close>

lemma path_integral_local_primitive_lemma:
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
  apply (rule path_integral_primitive_lemma, assumption+)
  using atLeastAtMost_iff by blast

lemma path_integral_local_primitive_any:
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
      apply (rule_tac f = h and s = "g ` {u..v}" in path_integral_local_primitive_lemma)
        apply (meson atLeastatMost_subset_iff gpd piecewise_differentiable_on_subset)
       apply (force simp: ball_def dist_norm intro: lessd gs DERIV_subset [OF h], force)
      done
  } then
  show ?thesis
    by (force simp: intro!: integrable_on_little_subintervals [of a b, simplified])
qed

lemma path_integral_local_primitive:
  fixes f :: "complex \<Rightarrow> complex"
  assumes g: "valid_path g" "path_image g \<subseteq> s"
      and dh: "\<And>x. x \<in> s
               \<Longrightarrow> \<exists>d h. 0 < d \<and>
                         (\<forall>y. norm(y - x) < d \<longrightarrow> (h has_field_derivative f y) (at y within s))"
  shows "f path_integrable_on g"
  using g
  apply (simp add: valid_path_def path_image_def path_integrable_on_def has_path_integral_def
            has_integral_localized_vector_derivative integrable_on_def [symmetric])
  using path_integral_local_primitive_any [OF _ dh]
  by (meson image_subset_iff piecewise_C1_imp_differentiable)


text\<open>In particular if a function is holomorphic\<close>

lemma path_integrable_holomorphic:
  assumes contf: "continuous_on s f"
      and os: "open s"
      and k: "finite k"
      and g: "valid_path g" "path_image g \<subseteq> s"
      and fcd: "\<And>x. x \<in> s - k \<Longrightarrow> f complex_differentiable at x"
    shows "f path_integrable_on g"
proof -
  { fix z
    assume z: "z \<in> s"
    obtain d where d: "d>0" "ball z d \<subseteq> s" using  `open s` z
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
    by (rule path_integral_local_primitive [OF g])
qed

lemma path_integrable_holomorphic_simple:
  assumes contf: "continuous_on s f"
      and os: "open s"
      and g: "valid_path g" "path_image g \<subseteq> s"
      and fh: "f holomorphic_on s"
    shows "f path_integrable_on g"
  apply (rule path_integrable_holomorphic [OF contf os Finite_Set.finite.emptyI g])
  using fh  by (simp add: complex_differentiable_def holomorphic_on_open os)

lemma continuous_on_inversediff:
  fixes z:: "'a::real_normed_field" shows "z \<notin> s \<Longrightarrow> continuous_on s (\<lambda>w. 1 / (w - z))"
  by (rule continuous_intros | force)+

corollary path_integrable_inversediff:
    "\<lbrakk>valid_path g; z \<notin> path_image g\<rbrakk> \<Longrightarrow> (\<lambda>w. 1 / (w-z)) path_integrable_on g"
apply (rule path_integrable_holomorphic_simple [of "UNIV-{z}", OF continuous_on_inversediff])
apply (auto simp: holomorphic_on_open open_delete intro!: derivative_eq_intros)
done

text{*Key fact that path integral is the same for a "nearby" path. This is the
 main lemma for the homotopy form of Cauchy's theorem and is also useful
 if we want "without loss of generality" to assume some nice properties of a
 path (e.g. smoothness). It can also be used to define the integrals of
 analytic functions over arbitrary continuous paths. This is just done for
 winding numbers now.
*}

text{*This formulation covers two cases: @{term g} and @{term h} share their
      start and end points; @{term g} and @{term h} both loop upon themselves. *}
lemma path_integral_nearby:
  assumes os: "open s"
      and p: "path p" "path_image p \<subseteq> s"
    shows
       "\<exists>d. 0 < d \<and>
            (\<forall>g h. valid_path g \<and> valid_path h \<and>
                  (\<forall>t \<in> {0..1}. norm(g t - p t) < d \<and> norm(h t - p t) < d) \<and>
                  (if Ends then pathstart h = pathstart g \<and> pathfinish h = pathfinish g
                   else pathfinish g = pathstart g \<and> pathfinish h = pathstart h)
                  \<longrightarrow> path_image g \<subseteq> s \<and> path_image h \<subseteq> s \<and>
                      (\<forall>f. f holomorphic_on s \<longrightarrow> path_integral h f = path_integral g f))"
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
    apply (blast dest!: finite_subset_image [OF `finite D`])
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
       and joins: "if Ends then pathstart h = pathstart g \<and> pathfinish h = pathfinish g
                   else pathfinish g = pathstart g \<and> pathfinish h = pathstart h"
    { fix t::real
      assume t: "0 \<le> t" "t \<le> 1"
      then obtain u where u: "u \<in> k" and ptu: "p t \<in> ball(p u) (ee(p u) / 3)"
        using `path_image p \<subseteq> \<Union>D` D_eq by (force simp: path_image_def)
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
      then have fpa: "f path_integrable_on g"  "f path_integrable_on h"
        using g ghs h holomorphic_on_imp_continuous_on os path_integrable_holomorphic_simple
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
        then have "path_integral(subpath 0 (n/N) h) f - path_integral(subpath 0 (n/N) g) f =
                   path_integral(linepath (g(n/N)) (h(n/N))) f - path_integral(linepath (g 0) (h 0)) f"
        proof (induct n)
          case 0 show ?case by simp
        next
          case (Suc n)
          obtain t where t: "t \<in> k" and "p (n/N) \<in> ball(p t) (ee(p t) / 3)"
            using `path_image p \<subseteq> \<Union>D` [THEN subsetD, where c="p (n/N)"] D_eq N Suc.prems
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
            by (auto simp: field_simps real_of_nat_def dist_norm dest: segment_furthest_le [where y="p t"])
          then have gh_ns: "closed_segment (g (n/N)) (h (n/N)) \<subseteq> s"
            using `N>0` Suc.prems
            apply (simp add: real_of_nat_def path_image_join field_simps closed_segment_commute)
            apply (erule order_trans)
            apply (simp add: ee pi t)
            done
          have pi_ghn': "path_image (linepath (g ((1 + n) / N)) (h ((1 + n) / N)))
                  \<subseteq> ball (p t) (ee (p t))"
            using ptgh_ee [of "(1+n)/N"] Suc.prems
            by (auto simp: field_simps real_of_nat_def dist_norm dest: segment_furthest_le [where y="p t"])
          then have gh_n's: "closed_segment (g ((1 + n) / N)) (h ((1 + n) / N)) \<subseteq> s"
            using `N>0` Suc.prems ee pi t
            by (auto simp: Path_Connected.path_image_join field_simps)
          have pi_subset_ball:
                "path_image (subpath (n/N) ((1+n) / N) g +++ linepath (g ((1+n) / N)) (h ((1+n) / N)) +++
                             subpath ((1+n) / N) (n/N) h +++ linepath (h (n/N)) (g (n/N)))
                 \<subseteq> ball (p t) (ee (p t))"
            apply (intro subset_path_image_join pi_hgn pi_ghn')
            using `N>0` Suc.prems
            apply (auto simp: dist_norm field_simps closed_segment_eq_real_ivl ptgh_ee)
            done
          have pi0: "(f has_path_integral 0)
                       (subpath (n/ N) ((Suc n)/N) g +++ linepath(g ((Suc n) / N)) (h((Suc n) / N)) +++
                        subpath ((Suc n) / N) (n/N) h +++ linepath(h (n/N)) (g (n/N)))"
            apply (rule Cauchy_theorem_primitive [of "ball(p t) (ee(p t))" "ff (p t)" "f"])
            apply (metis ff open_ball at_within_open pi t)
            apply (intro valid_path_join)
            using Suc.prems pi_subset_ball apply (simp_all add: valid_path_subpath g h)
            done
          have fpa1: "f path_integrable_on subpath (real n / real N) (real (Suc n) / real N) g"
            using Suc.prems by (simp add: path_integrable_subpath g fpa)
          have fpa2: "f path_integrable_on linepath (g (real (Suc n) / real N)) (h (real (Suc n) / real N))"
            using gh_n's
            by (auto intro!: path_integrable_continuous_linepath continuous_on_subset [OF contf])
          have fpa3: "f path_integrable_on linepath (h (real n / real N)) (g (real n / real N))"
            using gh_ns
            by (auto simp: closed_segment_commute intro!: path_integrable_continuous_linepath continuous_on_subset [OF contf])
          have eq0: "path_integral (subpath (n/N) ((Suc n) / real N) g) f +
                     path_integral (linepath (g ((Suc n) / N)) (h ((Suc n) / N))) f +
                     path_integral (subpath ((Suc n) / N) (n/N) h) f +
                     path_integral (linepath (h (n/N)) (g (n/N))) f = 0"
            using path_integral_unique [OF pi0] Suc.prems
            by (simp add: g h fpa valid_path_subpath path_integrable_subpath
                          fpa1 fpa2 fpa3 algebra_simps)
          have *: "\<And>hn he hn' gn gd gn' hgn ghn gh0 ghn'.
                    \<lbrakk>hn - gn = ghn - gh0;
                     gd + ghn' + he + hgn = (0::complex);
                     hn - he = hn'; gn + gd = gn'; hgn = -ghn\<rbrakk> \<Longrightarrow> hn' - gn' = ghn' - gh0"
            by (auto simp: algebra_simps)
          have "path_integral (subpath 0 (n/N) h) f - path_integral (subpath ((Suc n) / N) (n/N) h) f =
                path_integral (subpath 0 (n/N) h) f + path_integral (subpath (n/N) ((Suc n) / N) h) f"
            unfolding reversepath_subpath [symmetric, of "((Suc n) / N)"]
            using Suc.prems by (simp add: h fpa path_integral_reversepath valid_path_subpath path_integrable_subpath)
          also have "... = path_integral (subpath 0 ((Suc n) / N) h) f"
            using Suc.prems by (simp add: path_integral_subpath_combine h fpa)
          finally have pi0_eq:
               "path_integral (subpath 0 (n/N) h) f - path_integral (subpath ((Suc n) / N) (n/N) h) f =
                path_integral (subpath 0 ((Suc n) / N) h) f" .
          show ?case
            apply (rule * [OF Suc.hyps eq0 pi0_eq])
            using Suc.prems
            apply (simp_all add: g h fpa path_integral_subpath_combine
                     path_integral_reversepath [symmetric] path_integrable_continuous_linepath
                     continuous_on_subset [OF contf gh_ns])
            done
      qed
      } note ind = this
      have "path_integral h f = path_integral g f"
        using ind [OF order_refl] N joins
        by (simp add: pathstart_def pathfinish_def split: split_if_asm)
    }
    ultimately
    have "path_image g \<subseteq> s \<and> path_image h \<subseteq> s \<and> (\<forall>f. f holomorphic_on s \<longrightarrow> path_integral h f = path_integral g f)"
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
    shows path_integral_nearby_ends:
      "\<exists>d. 0 < d \<and>
              (\<forall>g h. valid_path g \<and> valid_path h \<and>
                    (\<forall>t \<in> {0..1}. norm(g t - p t) < d \<and> norm(h t - p t) < d) \<and>
                    pathstart h = pathstart g \<and> pathfinish h = pathfinish g
                    \<longrightarrow> path_image g \<subseteq> s \<and>
                        path_image h \<subseteq> s \<and>
                        (\<forall>f. f holomorphic_on s
                            \<longrightarrow> path_integral h f = path_integral g f))"
    and path_integral_nearby_loop:
      "\<exists>d. 0 < d \<and>
              (\<forall>g h. valid_path g \<and> valid_path h \<and>
                    (\<forall>t \<in> {0..1}. norm(g t - p t) < d \<and> norm(h t - p t) < d) \<and>
                    pathfinish g = pathstart g \<and> pathfinish h = pathstart h
                    \<longrightarrow> path_image g \<subseteq> s \<and>
                        path_image h \<subseteq> s \<and>
                        (\<forall>f. f holomorphic_on s
                            \<longrightarrow> path_integral h f = path_integral g f))"
  using path_integral_nearby [OF assms, where Ends=True]
  using path_integral_nearby [OF assms, where Ends=False]
  by simp_all

  thm has_vector_derivative_polynomial_function
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

lemma path_integral_bound_exists:
assumes s: "open s"
    and g: "valid_path g"
    and pag: "path_image g \<subseteq> s"
  shows "\<exists>L. 0 < L \<and>
       (\<forall>f B. f holomorphic_on s \<and> (\<forall>z \<in> s. norm(f z) \<le> B)
         \<longrightarrow> norm(path_integral g f) \<le> L*B)"
proof -
have "path g" using g
  by (simp add: valid_path_imp_path)
then obtain d::real and p
  where d: "0 < d"
    and p: "polynomial_function p" "path_image p \<subseteq> s"
    and pi: "\<And>f. f holomorphic_on s \<Longrightarrow> path_integral g f = path_integral p f"
  using path_integral_nearby_ends [OF s `path g` pag]
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
  then have "f path_integrable_on p \<and> valid_path p"
    using p s
    by (blast intro: valid_path_polynomial_function path_integrable_holomorphic_simple holomorphic_on_imp_continuous_on)
  moreover have "\<And>x. x \<in> {0..1} \<Longrightarrow> cmod (vector_derivative p (at x)) * cmod (f (p x)) \<le> L * B"
    apply (rule mult_mono)
    apply (subst Derivative.vector_derivative_at; force intro: p' nop')
    using L B p
    apply (auto simp: path_image_def image_subset_iff)
    done
  ultimately have "cmod (path_integral g f) \<le> L * B"
    apply (simp add: pi [OF f])
    apply (simp add: path_integral_integral)
    apply (rule order_trans [OF integral_norm_bound_integral])
    apply (auto simp: mult.commute integral_norm_bound_integral path_integrable_on [symmetric] norm_mult)
    done
} then
show ?thesis
  by (force simp: L path_integral_integral)
qed

end
