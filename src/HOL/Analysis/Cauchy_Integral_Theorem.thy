section \<open>Complex path integrals and Cauchy's integral theorem\<close>

text\<open>By John Harrison et al.  Ported from HOL Light by L C Paulson (2015)\<close>

theory Cauchy_Integral_Theorem
imports Complex_Transcendental Weierstrass_Theorems Ordered_Euclidean_Space
begin

subsection\<open>Homeomorphisms of arc images\<close>

lemma homeomorphism_arc:
  fixes g :: "real \<Rightarrow> 'a::t2_space"
  assumes "arc g"
  obtains h where "homeomorphism {0..1} (path_image g) g h"
using assms by (force simp add: arc_def homeomorphism_compact path_def path_image_def)

lemma homeomorphic_arc_image_interval:
  fixes g :: "real \<Rightarrow> 'a::t2_space" and a::real
  assumes "arc g" "a < b"
  shows "(path_image g) homeomorphic {a..b}"
proof -
  have "(path_image g) homeomorphic {0..1::real}"
    by (meson assms(1) homeomorphic_def homeomorphic_sym homeomorphism_arc)
  also have "... homeomorphic {a..b}"
    using assms by (force intro: homeomorphic_closed_intervals_real)
  finally show ?thesis .
qed

lemma homeomorphic_arc_images:
  fixes g :: "real \<Rightarrow> 'a::t2_space" and h :: "real \<Rightarrow> 'b::t2_space"
  assumes "arc g" "arc h"
  shows "(path_image g) homeomorphic (path_image h)"
proof -
  have "(path_image g) homeomorphic {0..1::real}"
    by (meson assms homeomorphic_def homeomorphic_sym homeomorphism_arc)
  also have "... homeomorphic (path_image h)"
    by (meson assms homeomorphic_def homeomorphism_arc)
  finally show ?thesis .
qed

lemma path_connected_arc_complement:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "arc \<gamma>" "2 \<le> DIM('a)"
  shows "path_connected(- path_image \<gamma>)"
proof -
  have "path_image \<gamma> homeomorphic {0..1::real}"
    by (simp add: assms homeomorphic_arc_image_interval)
  then
  show ?thesis
    apply (rule path_connected_complement_homeomorphic_convex_compact)
      apply (auto simp: assms)
    done
qed

lemma connected_arc_complement:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "arc \<gamma>" "2 \<le> DIM('a)"
  shows "connected(- path_image \<gamma>)"
  by (simp add: assms path_connected_arc_complement path_connected_imp_connected)

lemma inside_arc_empty:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "arc \<gamma>"
    shows "inside(path_image \<gamma>) = {}"
proof (cases "DIM('a) = 1")
  case True
  then show ?thesis
    using assms connected_arc_image connected_convex_1_gen inside_convex by blast
next
  case False
  show ?thesis
  proof (rule inside_bounded_complement_connected_empty)
    show "connected (- path_image \<gamma>)"
      apply (rule connected_arc_complement [OF assms])
      using False
      by (metis DIM_ge_Suc0 One_nat_def Suc_1 not_less_eq_eq order_class.order.antisym)
    show "bounded (path_image \<gamma>)"
      by (simp add: assms bounded_arc_image)
  qed
qed

lemma inside_simple_curve_imp_closed:
  fixes \<gamma> :: "real \<Rightarrow> 'a::euclidean_space"
    shows "\<lbrakk>simple_path \<gamma>; x \<in> inside(path_image \<gamma>)\<rbrakk> \<Longrightarrow> pathfinish \<gamma> = pathstart \<gamma>"
  using arc_simple_path  inside_arc_empty by blast

    
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
  apply (blast intro!: differentiable_chain_within)
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
      proof (rule differentiable_transform_within [where d = "dist x c" and f = f])
        have "f differentiable at x within ({a<..<c} - s)"
          apply (rule differentiable_at_withinI)
          using x le st
          by (metis (no_types, lifting) DiffD1 DiffD2 DiffI UnCI atLeastAtMost_diff_ends atLeastAtMost_iff at_within_interior insert_iff interior_atLeastAtMost_real le st(3) x)
        moreover have "open ({a<..<c} - s)"
          by (blast intro: open_greaterThanLessThan \<open>finite s\<close> finite_imp_closed)
        ultimately show "f differentiable at x within {a..b}"
          using x le by (auto simp add: at_within_open_NO_MATCH differentiable_at_withinI)
      qed (use x le st dist_real_def in auto)
    next
      case ge show ?diff_fg
      proof (rule differentiable_transform_within [where d = "dist x c" and f = g])
        have "g differentiable at x within ({c<..<b} - t)"
          apply (rule differentiable_at_withinI)
          using x ge st
          by (metis DiffD1 DiffD2 DiffI UnCI atLeastAtMost_diff_ends atLeastAtMost_iff at_within_interior insert_iff interior_atLeastAtMost_real)
        moreover have "open ({c<..<b} - t)"
          by (blast intro: open_greaterThanLessThan \<open>finite t\<close> finite_imp_closed)
        ultimately show "g differentiable at x within {a..b}"
          using x ge by (auto simp add: at_within_open_NO_MATCH differentiable_at_withinI)
      qed (use x ge st dist_real_def in auto)
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
  apply (auto simp: dist_real_def joinpaths_def abs_if field_simps split: if_split_asm)
  apply (rule differentiable_chain_within derivative_intros | simp)+
  apply (rule differentiable_subset)
  apply (force simp: divide_simps)+
  done


subsubsection\<open>The concept of continuously differentiable\<close>

text \<open>
John Harrison writes as follows:

``The usual assumption in complex analysis texts is that a path \<open>\<gamma>\<close> should be piecewise
continuously differentiable, which ensures that the path integral exists at least for any continuous
f, since all piecewise continuous functions are integrable. However, our notion of validity is
weaker, just piecewise differentiability... [namely] continuity plus differentiability except on a
ﬁnite set ... [Our] underlying theory of integration is the Kurzweil-Henstock theory. In contrast to
the Riemann or Lebesgue theory (but in common with a simple notion based on antiderivatives), this
can integrate all derivatives.''

"Formalizing basic complex analysis." From Insight to Proof: Festschrift in Honour of Andrzej Trybulec.
Studies in Logic, Grammar and Rhetoric 10.23 (2007): 151-165.

And indeed he does not assume that his derivatives are continuous, but the penalty is unreasonably
difficult proofs concerning winding numbers. We need a self-contained and straightforward theorem
asserting that all derivatives can be integrated before we can adopt Harrison's choice.\<close>

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
        apply (rule differentiable_transform_within [where f=f and d = "dist x c"])
        using x dist_real_def le st by (auto simp: C1_differentiable_on_eq)
    next
      case ge show ?diff_fg
        apply (rule differentiable_transform_within [where f=g and d = "dist x c"])
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
      apply (rule_tac f=f and d="dist x c" in has_vector_derivative_transform_within)
      apply (simp_all add: dist_norm vector_derivative_works [symmetric])
      apply (metis (full_types) C1_differentiable_on_eq Diff_iff Groups.add_ac(2) add_mono_thms_linordered_field(5) atLeastAtMost_iff linorder_not_le order_less_irrefl st(1))
      apply auto
      done
    moreover have "continuous_on ({c<..<b} - t) (\<lambda>x. vector_derivative (\<lambda>x. if x \<le> c then f x else g x) (at x))"
      apply (rule continuous_on_eq [OF gcon])
      apply (simp add:)
      apply (rule vector_derivative_at [symmetric])
      apply (rule_tac f=g and d="dist x c" in has_vector_derivative_transform_within)
      apply (simp_all add: dist_norm vector_derivative_works [symmetric])
      apply (metis (full_types) C1_differentiable_on_eq Diff_iff Groups.add_ac(2) add_mono_thms_linordered_field(5) atLeastAtMost_iff less_irrefl not_le st(2))
      apply auto
      done
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
    apply (rule_tac d="dist (x/2) (1/2)" and f = "(g1 +++ g2) o (op*(inverse 2))" in differentiable_transform_within)
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
    apply (rule_tac f="g1 o op*2" and d="dist x (1/2)" in has_vector_derivative_transform_within)
    apply (simp_all add: dist_norm joinpaths_def vector_derivative_works [symmetric])
    apply (force intro: g1D differentiable_chain_at)
    apply auto
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
    apply (rule_tac d="dist ((x+1)/2) (1/2)" and f = "(g1 +++ g2) o (\<lambda>x. (x+1)/2)" in differentiable_transform_within)
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
    apply (rule_tac f="g2 o (\<lambda>x. 2*x-1)" and d="dist (3/4) ((x+1)/2)" in has_vector_derivative_transform_within)
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

proposition valid_path_compose:
  assumes "valid_path g"
      and der: "\<And>x. x \<in> path_image g \<Longrightarrow> f field_differentiable (at x)"
      and con: "continuous_on (path_image g) (deriv f)"
    shows "valid_path (f o g)"
proof -
  obtain s where "finite s" and g_diff: "g C1_differentiable_on {0..1} - s"
    using \<open>valid_path g\<close> unfolding valid_path_def piecewise_C1_differentiable_on_def by auto
  have "f \<circ> g differentiable at t" when "t\<in>{0..1} - s" for t
    proof (rule differentiable_chain_at)
      show "g differentiable at t" using \<open>valid_path g\<close>
        by (meson C1_differentiable_on_eq \<open>g C1_differentiable_on {0..1} - s\<close> that)
    next
      have "g t\<in>path_image g" using that DiffD1 image_eqI path_image_def by metis
      then show "f differentiable at (g t)" 
        using der[THEN field_differentiable_imp_differentiable] by auto
    qed
  moreover have "continuous_on ({0..1} - s) (\<lambda>x. vector_derivative (f \<circ> g) (at x))"
    proof (rule continuous_on_eq [where f = "\<lambda>x. vector_derivative g (at x) * deriv f (g x)"],
        rule continuous_intros)
      show "continuous_on ({0..1} - s) (\<lambda>x. vector_derivative g (at x))"
        using g_diff C1_differentiable_on_eq by auto
    next
      have "continuous_on {0..1} (\<lambda>x. deriv f (g x))"
        using continuous_on_compose[OF _ con[unfolded path_image_def],unfolded comp_def]
          \<open>valid_path g\<close> piecewise_C1_differentiable_on_def valid_path_def
        by blast
      then show "continuous_on ({0..1} - s) (\<lambda>x. deriv f (g x))"
        using continuous_on_subset by blast
    next
      show "vector_derivative g (at t) * deriv f (g t) = vector_derivative (f \<circ> g) (at t)"
          when "t \<in> {0..1} - s" for t
        proof (rule vector_derivative_chain_at_general[symmetric])
          show "g differentiable at t" by (meson C1_differentiable_on_eq g_diff that)
        next
          have "g t\<in>path_image g" using that DiffD1 image_eqI path_image_def by metis
          then show "f field_differentiable at (g t)" using der by auto
        qed
    qed
  ultimately have "f o g C1_differentiable_on {0..1} - s"
    using C1_differentiable_on_eq by blast
  moreover have "path (f \<circ> g)" 
    apply (rule path_continuous_image[OF valid_path_imp_path[OF \<open>valid_path g\<close>]])
    using der
    by (simp add: continuous_at_imp_continuous_on field_differentiable_imp_continuous_at)
  ultimately show ?thesis unfolding valid_path_def piecewise_C1_differentiable_on_def path_def
    using \<open>finite s\<close> by auto
qed


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
  where "contour_integral g f \<equiv> @i. (f has_contour_integral i) g \<or> ~ f contour_integrable_on g \<and> i=0"

lemma not_integrable_contour_integral: "~ f contour_integrable_on g \<Longrightarrow> contour_integral g f = 0"
  unfolding contour_integrable_on_def contour_integral_def by blast

lemma contour_integral_unique: "(f has_contour_integral i) g \<Longrightarrow> contour_integral g f = i"
  apply (simp add: contour_integral_def has_contour_integral_def contour_integrable_on_def)
  using has_integral_unique by blast

corollary has_contour_integral_eqpath:
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

lemma valid_path_reversepath [simp]: "valid_path(reversepath g) \<longleftrightarrow> valid_path g"
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
    apply (rule_tac S = "(\<lambda>x. 1 - x) ` s" in has_integral_spike_finite)
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
  case False then have "~ f contour_integrable_on (reversepath g)"
    by (simp add: assms contour_integrable_reversepath_eq)
  with False show ?thesis by (simp add: not_integrable_contour_integral)
qed


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
                      [where f = "(shiftpath (1 - a) (shiftpath a g))" and s = "{0<..<1}-s"]])
      using s g assms x
      apply (auto simp: finite_imp_closed open_Diff shiftpath_shiftpath
                        vector_derivative_within_interior vector_derivative_works [symmetric])
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
     "contour_integral g f = integral {0..1} (\<lambda>x. f (g x) * vector_derivative g (at x))"
  by (simp add: contour_integral_def integral_def has_contour_integral contour_integrable_on)


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
    then have fdiff: "(f has_derivative op * (f' (g x))) (at (g x) within g ` {a..b})"
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

lemma contour_integrable_sum:
    "\<lbrakk>finite s; \<And>a. a \<in> s \<Longrightarrow> (f a) contour_integrable_on p\<rbrakk>
     \<Longrightarrow> (\<lambda>x. sum (\<lambda>a. f a x) s) contour_integrable_on p"
   unfolding contour_integrable_on_def
   by (metis has_contour_integral_sum)


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
    using assms by auto
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
      apply (drule has_integral_cmul [where c = "inverse k"])
      apply (simp add: has_integral_cmul)
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
      apply (drule has_integral_cmul [where k = "(1 - k) *\<^sub>R j" and c = "inverse (1 - k)"])
      apply (simp add: has_integral_cmul)
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
    apply (auto simp: hull_inc c' convexD_alt)
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
    apply (auto simp: hull_inc c' convexD_alt)
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

lemma has_chain_integral_chain_integral4:
     "(f has_contour_integral i) (linepath a b +++ linepath b c +++ linepath c d +++ linepath d e)
      \<Longrightarrow> contour_integral (linepath a b) f + contour_integral (linepath b c) f + contour_integral (linepath c d) f + contour_integral (linepath d e) f = i"
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
    apply (simp only: contour_integral_integral)
    apply (subst integral_swap_continuous [where 'a = real and 'b = real, of 0 0 1 1, simplified])
     apply (rule fgh gvcon' hvcon' continuous_intros | simp add: split_def)+
    unfolding integral_mult_left [symmetric]
    apply (simp only: mult_ac)
    done
  also have "... = contour_integral h (\<lambda>z. contour_integral g (\<lambda>w. f w z))"
    apply (simp add: contour_integral_integral)
    apply (rule integral_cong)
    unfolding integral_mult_left [symmetric]
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
  define a' where "a' = midpoint b c"
  define b' where "b' = midpoint c a"
  define c' where "c' = midpoint a b"
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
      and cd: "f field_differentiable (at x within s)"
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
    apply (simp add: field_differentiable_def has_field_derivative_def has_derivative_within_alt approachable_lt_le2 Ball_def)
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
    define K where "K = 1 + max (dist a b) (max (dist b c) (dist c a))"
    define e where "e = norm y / K^2"
    have K1: "K \<ge> 1"  by (simp add: K_def max.coboundedI1)
    then have K: "K > 0" by linarith
    have [iff]: "dist a b \<le> K" "dist b c \<le> K" "dist c a \<le> K"
      by (simp_all add: K_def)
    have e: "e > 0"
      unfolding e_def using ynz K1 by simp
    define At where "At x y z n \<longleftrightarrow>
        convex hull {x,y,z} \<subseteq> convex hull {a,b,c} \<and>
        dist x y \<le> K/2^n \<and> dist y z \<le> K/2^n \<and> dist z x \<le> K/2^n \<and>
        norm(?pathint x y + ?pathint y z + ?pathint z x) \<ge> e*(K/2^n)^2"
      for x y z n
    have At0: "At a b c 0"
      using fy
      by (simp add: At_def e_def has_chain_integral_chain_integral3)
    { fix x y z n
      assume At: "At x y z n"
      then have contf': "continuous_on (convex hull {x,y,z}) f"
        using contf At_def continuous_on_subset by metis
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
      apply (intro allI impI)
      apply (erule transitive_stepwise_le)
      apply (auto simp: conv_le)
      done
    then obtain x where x: "\<And>n. x \<in> convex hull {fa n, fb n, fc n}" by auto
    then have xin: "x \<in> convex hull {a,b,c}"
      using assms f0 by blast
    then have fx: "f field_differentiable at x within (convex hull {a,b,c})"
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
      apply (rule_tac y1="K/k" in exE [OF real_arch_pow[of 2]])
      apply force+
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
        define e where "e = min 1 (min (d1/(4*C)) ((norm y / 24 / C) / B))"
        define shrink where "shrink x = x - e *\<^sub>R (x - d)" for x
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
            apply (simp add: has_integral_diff has_contour_integral_linepath [symmetric] has_contour_integral_integral
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
      and "(\<And>x. x \<in> interior(convex hull {a,b,c}) - s \<Longrightarrow> f field_differentiable (at x))"
     shows "(f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)"
using assms
proof (induction "card s" arbitrary: a b c s rule: less_induct)
  case (less s a b c)
  show ?case
  proof (cases "s={}")
    case True with less show ?thesis
      by (fastforce simp: holomorphic_on_def field_differentiable_at_within
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
  then have *: "(\<lambda>y. (?pathint x y - f x * (y - x)) /\<^sub>R cmod (y - x)) \<midarrow>x\<rightarrow> 0"
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
  fixes f :: "complex \<Rightarrow> complex"
  assumes contf: "continuous_on s f"
      and s: "starlike s" and os: "open s"
      and k: "finite k"
      and fcd: "\<And>x. x \<in> s - k \<Longrightarrow> f field_differentiable at x"
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
   \<And>x. x \<in> s - k \<Longrightarrow> f field_differentiable at x;
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
  then have *: "((\<lambda>y. (contour_integral (linepath x y) f - f x * (y - x)) /\<^sub>R cmod (y - x)) \<longlongrightarrow> 0) (at x within s)"
    by (simp add: Lim_within dist_norm inverse_eq_divide)
  show ?thesis
    apply (simp add: has_field_derivative_def has_derivative_within bounded_linear_mult_right)
    apply (rule Lim_transform [OF * Lim_eventually])
    using linordered_field_no_ub
    apply (force simp: inverse_eq_divide [symmetric] eventually_at)
    done
qed

lemma contour_integral_convex_primitive:
  "\<lbrakk>convex s; continuous_on s f;
    \<And>a b c. \<lbrakk>a \<in> s; b \<in> s; c \<in> s\<rbrakk> \<Longrightarrow> (f has_contour_integral 0) (linepath a b +++ linepath b c +++ linepath c a)\<rbrakk>
         \<Longrightarrow> \<exists>g. \<forall>x \<in> s. (g has_field_derivative f x) (at x within s)"
  apply (cases "s={}")
  apply (simp_all add: ex_in_conv [symmetric])
  apply (blast intro: triangle_contour_integrals_convex_primitive has_chain_integral_chain_integral3)
  done

lemma holomorphic_convex_primitive:
  fixes f :: "complex \<Rightarrow> complex"
  shows
  "\<lbrakk>convex s; finite k; continuous_on s f;
    \<And>x. x \<in> interior s - k \<Longrightarrow> f field_differentiable at x\<rbrakk>
   \<Longrightarrow> \<exists>g. \<forall>x \<in> s. (g has_field_derivative f x) (at x within s)"
apply (rule contour_integral_convex_primitive [OF _ _ Cauchy_theorem_triangle_cofinite])
prefer 3
apply (erule continuous_on_subset)
apply (simp add: subset_hull continuous_on_subset, assumption+)
by (metis Diff_iff convex_contains_segment insert_absorb insert_subset interior_mono segment_convex_hull subset_hull)

lemma holomorphic_convex_primitive':
  fixes f :: "complex \<Rightarrow> complex"
  assumes "convex s" and "open s" and "f holomorphic_on s"
  shows   "\<exists>g. \<forall>x \<in> s. (g has_field_derivative f x) (at x within s)"
proof (rule holomorphic_convex_primitive)
  fix x assume "x \<in> interior s - {}"
  with assms show "f field_differentiable at x"
    by (auto intro!: holomorphic_on_imp_differentiable_at simp: interior_open)
qed (insert assms, auto intro: holomorphic_on_imp_continuous_on)

lemma Cauchy_theorem_convex:
    "\<lbrakk>continuous_on s f; convex s; finite k;
      \<And>x. x \<in> interior s - k \<Longrightarrow> f field_differentiable at x;
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
      \<And>x. x \<in> ball a e - k \<Longrightarrow> f field_differentiable at x;
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
      and fcd: "\<And>x. x \<in> s - k \<Longrightarrow> f field_differentiable at x"
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
      by (metis open_ball at_within_open d(2) os subsetCE)
    then have "\<exists>h. (\<forall>y. cmod (y - z) < d \<longrightarrow> (h has_field_derivative f y) (at y within s))"
      by (force simp: dist_norm norm_minus_commute)
    then have "\<exists>d h. 0 < d \<and> (\<forall>y. cmod (y - z) < d \<longrightarrow> (h has_field_derivative f y) (at y within s))"
      using d by blast
  }
  then show ?thesis
    by (rule contour_integral_local_primitive [OF g])
qed

lemma contour_integrable_holomorphic_simple:
  assumes fh: "f holomorphic_on s"
      and os: "open s"
      and g: "valid_path g" "path_image g \<subseteq> s"
    shows "f contour_integrable_on g"
  apply (rule contour_integrable_holomorphic [OF _ os Finite_Set.finite.emptyI g])
  apply (simp add: fh holomorphic_on_imp_continuous_on)
  using fh  by (simp add: field_differentiable_def holomorphic_on_open os)

lemma continuous_on_inversediff:
  fixes z:: "'a::real_normed_field" shows "z \<notin> s \<Longrightarrow> continuous_on s (\<lambda>w. 1 / (w - z))"
  by (rule continuous_intros | force)+

corollary contour_integrable_inversediff:
    "\<lbrakk>valid_path g; z \<notin> path_image g\<rbrakk> \<Longrightarrow> (\<lambda>w. 1 / (w-z)) contour_integrable_on g"
apply (rule contour_integrable_holomorphic_simple [of _ "UNIV-{z}"])
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
  define cover where "cover = (\<lambda>z. ball z (ee z/3)) ` (path_image p)"
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
  define e where "e = Min((ee o p) ` k)"
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
    using real_arch_inverse [of d]   by auto
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
            apply (auto simp: path_image_subpath dist_norm field_simps closed_segment_eq_real_ivl ptgh_ee)
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
        by (simp add: linked_paths_def pathstart_def pathfinish_def split: if_split_asm)
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
  by (blast intro: has_vector_derivative_polynomial_function that elim: )
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

text\<open>We can treat even non-rectifiable paths as having a "length" for bounds on analytic functions in open sets.\<close>

subsection\<open>Winding Numbers\<close>

definition winding_number:: "[real \<Rightarrow> complex, complex] \<Rightarrow> complex" where
  "winding_number \<gamma> z \<equiv>
    @n. \<forall>e > 0. \<exists>p. valid_path p \<and> z \<notin> path_image p \<and>
                    pathstart p = pathstart \<gamma> \<and>
                    pathfinish p = pathfinish \<gamma> \<and>
                    (\<forall>t \<in> {0..1}. norm(\<gamma> t - p t) < e) \<and>
                    contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * \<i> * n"

lemma winding_number:
  assumes "path \<gamma>" "z \<notin> path_image \<gamma>" "0 < e"
    shows "\<exists>p. valid_path p \<and> z \<notin> path_image p \<and>
               pathstart p = pathstart \<gamma> \<and>
               pathfinish p = pathfinish \<gamma> \<and>
               (\<forall>t \<in> {0..1}. norm (\<gamma> t - p t) < e) \<and>
               contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * \<i> * winding_number \<gamma> z"
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
    using path_approx_polynomial_function [OF \<open>path \<gamma>\<close>, of "d/2"] d by auto
  define nn where "nn = 1/(2* pi*\<i>) * contour_integral h (\<lambda>w. 1/(w - z))"
  have "\<exists>n. \<forall>e > 0. \<exists>p. valid_path p \<and> z \<notin> path_image p \<and>
                        pathstart p = pathstart \<gamma> \<and>  pathfinish p = pathfinish \<gamma> \<and>
                        (\<forall>t \<in> {0..1}. norm(\<gamma> t - p t) < e) \<and>
                        contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * \<i> * n"
                    (is "\<exists>n. \<forall>e > 0. ?PP e n")
    proof (rule_tac x=nn in exI, clarify)
      fix e::real
      assume e: "e>0"
      obtain p where p: "polynomial_function p \<and>
            pathstart p = pathstart \<gamma> \<and> pathfinish p = pathfinish \<gamma> \<and> (\<forall>t\<in>{0..1}. cmod (p t - \<gamma> t) < min e (d / 2))"
        using path_approx_polynomial_function [OF \<open>path \<gamma>\<close>, of "min e (d/2)"] d \<open>0<e\<close> by auto
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
    apply (blast intro: \<open>0<e\<close>)
    done
qed

lemma winding_number_unique:
  assumes \<gamma>: "path \<gamma>" "z \<notin> path_image \<gamma>"
      and pi:
        "\<And>e. e>0 \<Longrightarrow> \<exists>p. valid_path p \<and> z \<notin> path_image p \<and>
                          pathstart p = pathstart \<gamma> \<and> pathfinish p = pathfinish \<gamma> \<and>
                          (\<forall>t \<in> {0..1}. norm (\<gamma> t - p t) < e) \<and>
                          contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * \<i> * n"
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
      contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * \<i> * n"
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
                           contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * \<i> * n"
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
      contour_integral p (\<lambda>w. 1/(w - z)) = 2 * pi * \<i> * n"
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
    shows "winding_number \<gamma> z = 1/(2*pi*\<i>) * contour_integral \<gamma> (\<lambda>w. 1/(w - z))"
  using assms by (auto simp: valid_path_imp_path intro!: winding_number_unique)

lemma has_contour_integral_winding_number:
  assumes \<gamma>: "valid_path \<gamma>" "z \<notin> path_image \<gamma>"
    shows "((\<lambda>w. 1/(w - z)) has_contour_integral (2*pi*\<i>*winding_number \<gamma> z)) \<gamma>"
by (simp add: winding_number_valid_path has_contour_integral_integral contour_integrable_inversediff assms)

lemma winding_number_trivial [simp]: "z \<noteq> a \<Longrightarrow> winding_number(linepath a a) z = 0"
  by (simp add: winding_number_valid_path)

lemma winding_number_subpath_trivial [simp]: "z \<noteq> g x \<Longrightarrow> winding_number (subpath x x g) z = 0"
  by (simp add: path_image_subpath winding_number_valid_path)

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

subsubsection\<open>Some lemmas about negating a path.\<close>

lemma valid_path_negatepath: "valid_path \<gamma> \<Longrightarrow> valid_path (uminus \<circ> \<gamma>)"
   unfolding o_def using piecewise_C1_differentiable_neg valid_path_def by blast

lemma has_contour_integral_negatepath:
  assumes \<gamma>: "valid_path \<gamma>" and cint: "((\<lambda>z. f (- z)) has_contour_integral - i) \<gamma>"
  shows "(f has_contour_integral i) (uminus \<circ> \<gamma>)"
proof -
  obtain S where cont: "continuous_on {0..1} \<gamma>" and "finite S" and diff: "\<gamma> C1_differentiable_on {0..1} - S"
    using \<gamma> by (auto simp: valid_path_def piecewise_C1_differentiable_on_def)
  have "((\<lambda>x. - (f (- \<gamma> x) * vector_derivative \<gamma> (at x within {0..1}))) has_integral i) {0..1}"
    using cint by (auto simp: has_contour_integral_def dest: has_integral_neg)
  then
  have "((\<lambda>x. f (- \<gamma> x) * vector_derivative (uminus \<circ> \<gamma>) (at x within {0..1})) has_integral i) {0..1}"
  proof (rule rev_iffD1 [OF _ has_integral_spike_eq])
    show "negligible S"
      by (simp add: \<open>finite S\<close> negligible_finite)
    show "f (- \<gamma> x) * vector_derivative (uminus \<circ> \<gamma>) (at x within {0..1}) =
         - (f (- \<gamma> x) * vector_derivative \<gamma> (at x within {0..1}))"
      if "x \<in> {0..1} - S" for x
    proof -
      have "vector_derivative (uminus \<circ> \<gamma>) (at x within cbox 0 1) = - vector_derivative \<gamma> (at x within cbox 0 1)"
        apply (rule vector_derivative_within_closed_interval)
        using that
          apply (auto simp: o_def)
        apply (rule has_vector_derivative_minus)
        by (metis C1_differentiable_on_def diff has_vector_derivative_at_within that vector_derivative_at_within_ivl zero_less_one)
      then show ?thesis
        by simp
    qed
  qed
  then show ?thesis by (simp add: has_contour_integral_def)
qed

lemma winding_number_negatepath:
  assumes \<gamma>: "valid_path \<gamma>" and 0: "0 \<notin> path_image \<gamma>"
  shows "winding_number(uminus \<circ> \<gamma>) 0 = winding_number \<gamma> 0"
proof -
  have "op / 1 contour_integrable_on \<gamma>"
    using "0" \<gamma> contour_integrable_inversediff by fastforce
  then have "((\<lambda>z. 1/z) has_contour_integral contour_integral \<gamma> (op / 1)) \<gamma>"
    by (rule has_contour_integral_integral)
  then have "((\<lambda>z. 1 / - z) has_contour_integral - contour_integral \<gamma> (op / 1)) \<gamma>"
    using has_contour_integral_neg by auto
  then show ?thesis
    using assms
    apply (simp add: winding_number_valid_path valid_path_negatepath image_def path_defs)
    apply (simp add: contour_integral_unique has_contour_integral_negatepath)
    done
qed

lemma contour_integrable_negatepath:
  assumes \<gamma>: "valid_path \<gamma>" and pi: "(\<lambda>z. f (- z)) contour_integrable_on \<gamma>"
  shows "f contour_integrable_on (uminus \<circ> \<gamma>)"
  by (metis \<gamma> add.inverse_inverse contour_integrable_on_def has_contour_integral_negatepath pi)

(* A combined theorem deducing several things piecewise.*)
lemma winding_number_join_pos_combined:
     "\<lbrakk>valid_path \<gamma>1; z \<notin> path_image \<gamma>1; 0 < Re(winding_number \<gamma>1 z);
       valid_path \<gamma>2; z \<notin> path_image \<gamma>2; 0 < Re(winding_number \<gamma>2 z); pathfinish \<gamma>1 = pathstart \<gamma>2\<rbrakk>
      \<Longrightarrow> valid_path(\<gamma>1 +++ \<gamma>2) \<and> z \<notin> path_image(\<gamma>1 +++ \<gamma>2) \<and> 0 < Re(winding_number(\<gamma>1 +++ \<gamma>2) z)"
  by (simp add: valid_path_join path_image_join winding_number_join valid_path_imp_path)


subsubsection\<open>Useful sufficient conditions for the winding number to be positive\<close>

lemma Re_winding_number:
    "\<lbrakk>valid_path \<gamma>; z \<notin> path_image \<gamma>\<rbrakk>
     \<Longrightarrow> Re(winding_number \<gamma> z) = Im(contour_integral \<gamma> (\<lambda>w. 1/(w - z))) / (2*pi)"
by (simp add: winding_number_valid_path field_simps Re_divide power2_eq_square)

lemma winding_number_pos_le:
  assumes \<gamma>: "valid_path \<gamma>" "z \<notin> path_image \<gamma>"
      and ge: "\<And>x. \<lbrakk>0 < x; x < 1\<rbrakk> \<Longrightarrow> 0 \<le> Im (vector_derivative \<gamma> (at x) * cnj(\<gamma> x - z))"
    shows "0 \<le> Re(winding_number \<gamma> z)"
proof -
  have ge0: "0 \<le> Im (vector_derivative \<gamma> (at x) / (\<gamma> x - z))" if x: "0 < x" "x < 1" for x
    using ge by (simp add: Complex.Im_divide algebra_simps x)
  have hi: "((\<lambda>x. 1 / (\<gamma> x - z) * vector_derivative \<gamma> (at x)) has_integral contour_integral \<gamma> (\<lambda>w. 1 / (w - z)))
            (cbox 0 1)"
    unfolding box_real
    apply (subst has_contour_integral [symmetric])
    using \<gamma> by (simp add: contour_integrable_inversediff has_contour_integral_integral)
  have "0 \<le> Im (contour_integral \<gamma> (\<lambda>w. 1 / (w - z)))"
    apply (rule has_integral_component_nonneg
             [of \<i> "\<lambda>x. if x \<in> {0<..<1}
                         then 1/(\<gamma> x - z) * vector_derivative \<gamma> (at x) else 0", simplified])
      prefer 3 apply (force simp: ge0)
     apply (simp add: Basis_complex_def)
    apply (rule has_integral_spike_interior [OF hi])
    apply simp
    done
  then show ?thesis
    by (simp add: Re_winding_number [OF \<gamma>] field_simps)
qed

lemma winding_number_pos_lt_lemma:
  assumes \<gamma>: "valid_path \<gamma>" "z \<notin> path_image \<gamma>"
      and e: "0 < e"
      and ge: "\<And>x. \<lbrakk>0 < x; x < 1\<rbrakk> \<Longrightarrow> e \<le> Im (vector_derivative \<gamma> (at x) / (\<gamma> x - z))"
    shows "0 < Re(winding_number \<gamma> z)"
proof -
  have hi: "((\<lambda>x. 1 / (\<gamma> x - z) * vector_derivative \<gamma> (at x)) has_integral contour_integral \<gamma> (\<lambda>w. 1 / (w - z)))
            (cbox 0 1)"
    unfolding box_real
    apply (subst has_contour_integral [symmetric])
    using \<gamma> by (simp add: contour_integrable_inversediff has_contour_integral_integral)
  have "e \<le> Im (contour_integral \<gamma> (\<lambda>w. 1 / (w - z)))"
    apply (rule has_integral_component_le
             [of \<i> "\<lambda>x. \<i>*e" "\<i>*e" "{0..1}"
                    "\<lambda>x. if x \<in> {0<..<1} then 1/(\<gamma> x - z) * vector_derivative \<gamma> (at x) else \<i>*e"
                    "contour_integral \<gamma> (\<lambda>w. 1/(w - z))", simplified])
    using e apply (simp_all add: Basis_complex_def)
    using has_integral_const_real [of _ 0 1] apply force
     apply (rule has_integral_spike_interior [OF hi, simplified box_real])
    apply (simp_all add: ge)
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
    using \<open>finite k\<close> by (simp add: finite_imp_closed open_Diff)
  moreover have "{a<..<b} - k \<subseteq> {a..b} - k"
    by force
  ultimately have g_diff_at: "\<And>x. \<lbrakk>x \<notin> k; x \<in> {a<..<b}\<rbrakk> \<Longrightarrow> \<gamma> differentiable at x"
    by (metis Diff_iff differentiable_on_subset C1_diff_imp_diff [OF g_C1_diff] differentiable_on_def at_within_open)
  { fix w
    assume "w \<noteq> z"
    have "continuous_on (ball w (cmod (w - z))) (\<lambda>w. 1 / (w - z))"
      by (auto simp: dist_norm intro!: continuous_intros)
    moreover have "\<And>x. cmod (w - x) < cmod (w - z) \<Longrightarrow> \<exists>f'. ((\<lambda>w. 1 / (w - z)) has_field_derivative f') (at x)"
      by (auto simp: intro!: derivative_eq_intros)
    ultimately have "\<exists>h. \<forall>y. norm(y - w) < norm(w - z) \<longrightarrow> (h has_field_derivative 1/(y - z)) (at y)"
      using holomorphic_convex_primitive [of "ball w (norm(w - z))" "{}" "\<lambda>w. 1/(w - z)"]
      by (simp add: field_differentiable_def Ball_def dist_norm at_within_open_NO_MATCH norm_minus_commute)
  }
  then obtain h where h: "\<And>w y. w \<noteq> z \<Longrightarrow> norm(y - w) < norm(w - z) \<Longrightarrow> (h w has_field_derivative 1/(y - z)) (at y)"
    by meson
  have exy: "\<exists>y. ((\<lambda>x. inverse (\<gamma> x - z) * ?D\<gamma> x) has_integral y) {a..b}"
    unfolding integrable_on_def [symmetric]
  proof (rule contour_integral_local_primitive_any [OF piecewise_C1_imp_differentiable [OF \<gamma>]])
    show "\<exists>d h. 0 < d \<and>
               (\<forall>y. cmod (y - w) < d \<longrightarrow> (h has_field_derivative inverse (y - z))(at y within - {z}))" 
          if "w \<in> - {z}" for w
      apply (rule_tac x="norm(w - z)" in exI)
      using that inverse_eq_divide has_field_derivative_at_within h
      by (metis Compl_insert DiffD2 insertCI right_minus_eq zero_less_norm_iff)
  qed simp
  have vg_int: "(\<lambda>x. ?D\<gamma> x / (\<gamma> x - z)) integrable_on {a..b}"
    unfolding box_real [symmetric] divide_inverse_commute
    by (auto intro!: exy integrable_subinterval simp add: integrable_on_def ab)
  with ab show ?thesis1
    by (simp add: divide_inverse_commute integral_def integrable_on_def)
  { fix t
    assume t: "t \<in> {a..b}"
    have cball: "continuous_on (ball (\<gamma> t) (dist (\<gamma> t) z)) (\<lambda>x. inverse (x - z))"
        using z by (auto intro!: continuous_intros simp: dist_norm)
    have icd: "\<And>x. cmod (\<gamma> t - x) < cmod (\<gamma> t - z) \<Longrightarrow> (\<lambda>w. inverse (w - z)) field_differentiable at x"
      unfolding field_differentiable_def by (force simp: intro!: derivative_eq_intros)
    obtain h where h: "\<And>x. cmod (\<gamma> t - x) < cmod (\<gamma> t - z) \<Longrightarrow>
                       (h has_field_derivative inverse (x - z)) (at x within {y. cmod (\<gamma> t - y) < cmod (\<gamma> t - z)})"
      using holomorphic_convex_primitive [where f = "\<lambda>w. inverse(w - z)", OF convex_ball finite.emptyI cball icd]
      by simp (auto simp: ball_def dist_norm that)
    { fix x D
      assume x: "x \<notin> k" "a < x" "x < b"
      then have "x \<in> interior ({a..b} - k)"
        using open_subset_interior [OF o] by fastforce
      then have con: "isCont ?D\<gamma> x"
        using g_C1_diff x by (auto simp: C1_differentiable_on_eq intro: continuous_on_interior)
      then have con_vd: "continuous (at x within {a..b}) (\<lambda>x. ?D\<gamma> x)"
        by (rule continuous_at_imp_continuous_within)
      have gdx: "\<gamma> differentiable at x"
        using x by (simp add: g_diff_at)
      have "\<And>d. \<lbrakk>x \<notin> k; a < x; x < b;
          (\<gamma> has_vector_derivative d) (at x); a \<le> t; t \<le> b\<rbrakk>
         \<Longrightarrow> ((\<lambda>x. integral {a..x}
                     (\<lambda>x. ?D\<gamma> x /
                           (\<gamma> x - z))) has_vector_derivative
              d / (\<gamma> x - z))
              (at x within {a..b})"
        apply (rule has_vector_derivative_eq_rhs)
         apply (rule integral_has_vector_derivative_continuous_at [where S = "{}", simplified])
        apply (rule con_vd continuous_intros cong vg_int | simp add: continuous_at_imp_continuous_within has_vector_derivative_continuous vector_derivative_at)+
        done
      then have "((\<lambda>c. exp (- integral {a..c} (\<lambda>x. ?D\<gamma> x / (\<gamma> x - z))) * (\<gamma> c - z)) has_derivative (\<lambda>h. 0))
          (at x within {a..b})"
        using x gdx t
        apply (clarsimp simp add: differentiable_iff_scaleR)
        apply (rule exp_fg [unfolded has_vector_derivative_def, simplified], blast intro: has_derivative_at_within)
        apply (simp_all add: has_vector_derivative_def [symmetric])
        done
      } note * = this
    have "exp (- (integral {a..t} (\<lambda>x. ?D\<gamma> x / (\<gamma> x - z)))) * (\<gamma> t - z) =\<gamma> a - z"
      apply (rule has_derivative_zero_unique_strong_interval [of "{a,b} \<union> k" a b])
      using t
      apply (auto intro!: * continuous_intros fink cong indefinite_integral_continuous_1 [OF vg_int]  simp add: ab)+
      done
   }
  with ab show ?thesis2
    by (simp add: divide_inverse_commute integral_def)
qed

corollary winding_number_exp_2pi:
    "\<lbrakk>path p; z \<notin> path_image p\<rbrakk>
     \<Longrightarrow> pathfinish p - z = exp (2 * pi * \<i> * winding_number p z) * (pathstart p - z)"
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
  have [simp]: "(winding_number \<gamma> z \<in> \<int>) = (exp (contour_integral p (\<lambda>w. 1 / (w - z))) = 1)"
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
  define r where "r = (w - z) / (\<gamma> 0 - z)"
  have [simp]: "r \<noteq> 0"
    using w z by (auto simp: r_def)
  have "Arg r \<le> 2*pi"
    by (simp add: Arg less_eq_real_def)
  also have "... \<le> Im (integral {0..1} (\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z)))"
    using 1
    apply (simp add: winding_number_valid_path [OF \<gamma> z] contour_integral_integral)
    apply (simp add: Complex.Re_divide field_simps power2_eq_square)
    done
  finally have "Arg r \<le> Im (integral {0..1} (\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z)))" .
  then have "\<exists>t. t \<in> {0..1} \<and> Im(integral {0..t} (\<lambda>x. vector_derivative \<gamma> (at x)/(\<gamma> x - z))) = Arg r"
    apply (simp add:)
    apply (rule IVT')
    apply (simp_all add: Arg_ge_0)
    apply (intro continuous_intros indefinite_integral_continuous_1 winding_number_exp_integral [OF gpd]; simp)
    done
  then obtain t where t:     "t \<in> {0..1}"
                  and eqArg: "Im (integral {0..t} (\<lambda>x. vector_derivative \<gamma> (at x)/(\<gamma> x - z))) = Arg r"
    by blast
  define i where "i = integral {0..t} (\<lambda>x. vector_derivative \<gamma> (at x) / (\<gamma> x - z))"
  have iArg: "Arg r = Im i"
    using eqArg by (simp add: i_def)
  have gpdt: "\<gamma> piecewise_C1_differentiable_on {0..t}"
    by (metis atLeastAtMost_iff atLeastatMost_subset_iff order_refl piecewise_C1_differentiable_on_subset gpd t)
  have "exp (- i) * (\<gamma> t - z) = \<gamma> 0 - z"
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
    apply (simp add: exp_eq_polar field_simps)
    done
  with t show ?thesis
    by (rule_tac x="exp(Re i) / norm r" in exI) (auto simp: path_image_def)
qed

lemma winding_number_big_meets:
  fixes z::complex
  assumes \<gamma>: "valid_path \<gamma>" and z: "z \<notin> path_image \<gamma>" and "\<bar>Re (winding_number \<gamma> z)\<bar> \<ge> 1"
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
    by (simp add: abs_if winding_number_pos_meets split: if_split_asm)
qed

lemma winding_number_less_1:
  fixes z::complex
  shows
  "\<lbrakk>valid_path \<gamma>; z \<notin> path_image \<gamma>; w \<noteq> z;
    \<And>a::real. 0 < a \<Longrightarrow> z + a*(w - z) \<notin> path_image \<gamma>\<rbrakk>
   \<Longrightarrow> Re(winding_number \<gamma> z) < 1"
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
    using winding_number [OF \<gamma> z, of "min d e / 2"] \<open>d>0\<close> \<open>e>0\<close> by auto
  { fix w
    assume d2: "cmod (w - z) < d/2" and e2: "cmod (w - z) < e/2"
    then have wnotp: "w \<notin> path_image p"
      using cbg \<open>d>0\<close> \<open>e>0\<close>
      apply (simp add: path_image_def cball_def dist_norm, clarify)
      apply (frule pg)
      apply (drule_tac c="\<gamma> x" in subsetD)
      apply (auto simp: less_eq_real_def norm_minus_commute norm_triangle_half_l)
      done
    have wnotg: "w \<notin> path_image \<gamma>"
      using cbg e2 \<open>e>0\<close> by (force simp: dist_norm norm_minus_commute)
    { fix k::real
      assume k: "k>0"
      then obtain q where q: "valid_path q" "w \<notin> path_image q"
                             "pathstart q = pathstart \<gamma> \<and> pathfinish q = pathfinish \<gamma>"
                    and qg: "\<And>t. t \<in> {0..1} \<Longrightarrow> cmod (\<gamma> t - q t) < min k (min d e) / 2"
                    and qi: "contour_integral q (\<lambda>u. 1 / (u - w)) = complex_of_real (2 * pi) * \<i> * winding_number \<gamma> w"
        using winding_number [OF \<gamma> wnotg, of "min k (min d e) / 2"] \<open>d>0\<close> \<open>e>0\<close> k
        by (force simp: min_divide_distrib_right)
      have "contour_integral p (\<lambda>u. 1 / (u - w)) = contour_integral q (\<lambda>u. 1 / (u - w))"
        apply (rule pi_eq [OF \<open>valid_path q\<close> \<open>valid_path p\<close>, THEN conjunct2, THEN conjunct2, rule_format])
        apply (frule pg)
        apply (frule qg)
        using p q \<open>d>0\<close> e2
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
    using contour_integral_bound_exists [of "- cball z (3/4*pe)" p] cbp \<open>valid_path p\<close> by force
  { fix e::real and w::complex
    assume e: "0 < e" and w: "cmod (w - z) < pe/4" "cmod (w - z) < e * pe\<^sup>2 / (8 * L)"
    then have [simp]: "w \<notin> path_image p"
      using cbp p(2) \<open>0 < pe\<close>
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
        using \<open>pe>0\<close> by auto
      then have pe2: "pe^2 < 4 * cmod (w - x) ^ 2"
        by (simp add: power_divide)
      have "8 * L * cmod (w - z) < e * pe\<^sup>2"
        using w \<open>L>0\<close> by (simp add: field_simps)
      also have "... < e * 4 * cmod (w - x) * cmod (w - x)"
        using pe2 \<open>e>0\<close> by (simp add: power2_eq_square)
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
        using pe \<open>pe>0\<close> w \<open>L>0\<close>
        apply (force simp: norm_minus_commute)
        using wx w(2) \<open>L>0\<close> pe pe2 Lwz
        apply (auto simp: divide_simps mult_less_0_iff norm_minus_commute norm_divide norm_mult power2_eq_square)
        done
    } note L_cmod_le = this
    have *: "cmod (contour_integral p (\<lambda>x. 1 / (x - w) - 1 / (x - z))) \<le> L * (e * pe\<^sup>2 / L / 4 * (inverse (pe / 2))\<^sup>2)"
      apply (rule L)
      using \<open>pe>0\<close> w
      apply (force simp: dist_norm norm_minus_commute intro!: holomorphic_intros)
      using \<open>pe>0\<close> w \<open>L>0\<close>
      apply (auto simp: cball_def dist_norm field_simps L_cmod_le  simp del: less_divide_eq_numeral1 le_divide_eq_numeral1)
      done
    have "cmod (contour_integral p (\<lambda>x. 1 / (x - w)) - contour_integral p (\<lambda>x. 1 / (x - z))) < 2*e"
      apply (simp add:)
      apply (rule le_less_trans [OF *])
      using \<open>L>0\<close> e
      apply (force simp: field_simps)
      done
    then have "cmod (winding_number p w - winding_number p z) < e"
      using pi_ge_two e
      by (force simp: winding_number_valid_path p field_simps norm_divide norm_mult intro: less_le_trans)
  } note cmod_wn_diff = this
  then have "isCont (winding_number p) z"
    apply (simp add: continuous_at_eps_delta, clarify)
    apply (rule_tac x="min (pe/4) (e/2*pe^2/L/4)" in exI)
    using \<open>pe>0\<close> \<open>L>0\<close>
    apply (simp add: dist_norm cmod_wn_diff)
    done
  then show ?thesis
    apply (rule continuous_transform_within [where d = "min d e / 2"])
    apply (auto simp: \<open>d>0\<close> \<open>e>0\<close> dist_norm wnwn)
    done
qed

corollary continuous_on_winding_number:
    "path \<gamma> \<Longrightarrow> continuous_on (- path_image \<gamma>) (\<lambda>w. winding_number \<gamma> w)"
  by (simp add: continuous_at_imp_continuous_on continuous_at_winding_number)


subsection\<open>The winding number is constant on a connected region\<close>

lemma winding_number_constant:
  assumes \<gamma>: "path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>" and cs: "connected S" and sg: "S \<inter> path_image \<gamma> = {}"
  shows "winding_number \<gamma> constant_on S"
proof -
  have *: "1 \<le> cmod (winding_number \<gamma> y - winding_number \<gamma> z)"
      if ne: "winding_number \<gamma> y \<noteq> winding_number \<gamma> z" and "y \<in> S" "z \<in> S" for y z
  proof -
    have "winding_number \<gamma> y \<in> \<int>"  "winding_number \<gamma> z \<in>  \<int>"
      using that integer_winding_number [OF \<gamma> loop] sg \<open>y \<in> S\<close> by auto
    with ne show ?thesis
      by (auto simp: Ints_def of_int_diff [symmetric] simp del: of_int_diff)
  qed
  have cont: "continuous_on S (\<lambda>w. winding_number \<gamma> w)"
    using continuous_on_winding_number [OF \<gamma>] sg
    by (meson continuous_on_subset disjoint_eq_subset_Compl)
  show ?thesis
    using "*" zero_less_one
    by (blast intro: continuous_discrete_range_constant [OF cs cont])
qed

lemma winding_number_eq:
     "\<lbrakk>path \<gamma>; pathfinish \<gamma> = pathstart \<gamma>; w \<in> S; z \<in> S; connected S; S \<inter> path_image \<gamma> = {}\<rbrakk>
      \<Longrightarrow> winding_number \<gamma> w = winding_number \<gamma> z"
  using winding_number_constant by (metis constant_on_def) 

lemma open_winding_number_levelsets:
  assumes \<gamma>: "path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
    shows "open {z. z \<notin> path_image \<gamma> \<and> winding_number \<gamma> z = k}"
proof -
  have opn: "open (- path_image \<gamma>)"
    by (simp add: closed_path_image \<gamma> open_Compl)
  { fix z assume z: "z \<notin> path_image \<gamma>" and k: "k = winding_number \<gamma> z"
    obtain e where e: "e>0" "ball z e \<subseteq> - path_image \<gamma>"
      using open_contains_ball [of "- path_image \<gamma>"] opn z
      by blast
    have "\<exists>e>0. \<forall>y. dist y z < e \<longrightarrow> y \<notin> path_image \<gamma> \<and> winding_number \<gamma> y = winding_number \<gamma> z"
      apply (rule_tac x=e in exI)
      using e apply (simp add: dist_norm ball_def norm_minus_commute)
      apply (auto simp: dist_norm norm_minus_commute intro!: winding_number_eq [OF assms, where S = "ball z e"])
      done
  } then
  show ?thesis
    by (auto simp: open_dist)
qed

subsection\<open>Winding number is zero "outside" a curve, in various senses\<close>

proposition winding_number_zero_in_outside:
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
  moreover have "winding_number \<gamma> constant_on outside (path_image \<gamma>)"
    using winding_number_constant [OF \<gamma> loop, of "outside(path_image \<gamma>)"] connected_outside
    by (metis DIM_complex bounded_path_image dual_order.refl \<gamma> outside_no_overlap)
  ultimately have "winding_number \<gamma> z = winding_number \<gamma> w"
    by (metis (no_types, hide_lams) constant_on_def z)
  also have "... = 0"
  proof -
    have wnot: "w \<notin> path_image \<gamma>"  using wout by (simp add: outside_def)
    { fix e::real assume "0<e"
      obtain p where p: "polynomial_function p" "pathstart p = pathstart \<gamma>" "pathfinish p = pathfinish \<gamma>"
                 and pg1: "(\<And>t. \<lbrakk>0 \<le> t; t \<le> 1\<rbrakk> \<Longrightarrow> cmod (p t - \<gamma> t) < 1)"
                 and pge: "(\<And>t. \<lbrakk>0 \<le> t; t \<le> 1\<rbrakk> \<Longrightarrow> cmod (p t - \<gamma> t) < e)"
        using path_approx_polynomial_function [OF \<gamma>, of "min 1 e"] \<open>e>0\<close> by force
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

corollary winding_number_zero_const: "a \<noteq> z \<Longrightarrow> winding_number (\<lambda>t. a) z = 0"
  by (rule winding_number_zero_in_outside)
     (auto simp: pathfinish_def pathstart_def path_polynomial_function)

corollary winding_number_zero_outside:
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
      using \<open>x \<in> s\<close> by (metis (no_types) ComplI UnE cos \<gamma> loop s_disj union_with_outside winding_number_eq winding_number_zero_in_outside wn_nz z)
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
          1 / (2*pi*\<i>) * contour_integral (subpath 0 x \<gamma>) (\<lambda>w. 1/(w - z))"
      using assms x
      apply (simp add: contour_integral_subcontour_integral [OF contour_integrable_inversediff])
      done
    also have "... = winding_number (subpath 0 x \<gamma>) z"
      apply (subst winding_number_valid_path)
      using assms x
      apply (simp_all add: path_image_subpath valid_path_subpath)
      by (force simp: path_image_def)
    finally show ?thesis .
  qed
  show ?thesis
    apply (rule continuous_on_eq
                 [where f = "\<lambda>x. 1 / (2*pi*\<i>) *
                                 integral {0..x} (\<lambda>t. 1/(\<gamma> t - z) * vector_derivative \<gamma> (at t))"])
    apply (rule continuous_intros)+
    apply (rule indefinite_integral_continuous_1)
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
      using closed_segment_eq_real_ivl path_image_def t z by (fastforce simp: path_image_subpath Euler sub12)
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
    then obtain d where "d>0" and d: "\<And>x'. dist x' z < d \<Longrightarrow> dist (winding_number \<gamma> x') (winding_number \<gamma> z) < \<bar>Re(winding_number \<gamma> z)\<bar> - 1/2"
      using continuous_at_eps_delta wnz_12 diff_gt_0_iff_gt by blast
    define z' where "z' = z - (d / (2 * cmod a)) *\<^sub>R a"
    have *: "a \<bullet> z' \<le> b - d / 3 * cmod a"
      unfolding z'_def inner_mult_right' divide_inverse
      apply (simp add: divide_simps algebra_simps dot_square_norm power2_eq_square anz)
      apply (metis \<open>0 < d\<close> add_increasing azb less_eq_real_def mult_nonneg_nonneg mult_right_mono norm_ge_zero norm_numeral)
      done
    have "cmod (winding_number \<gamma> z' - winding_number \<gamma> z) < \<bar>Re (winding_number \<gamma> z)\<bar> - 1/2"
      using d [of z'] anz \<open>d>0\<close> by (simp add: dist_norm z'_def)
    then have "1/2 < \<bar>Re (winding_number \<gamma> z)\<bar> - cmod (winding_number \<gamma> z' - winding_number \<gamma> z)"
      by simp
    then have "1/2 < \<bar>Re (winding_number \<gamma> z)\<bar> - \<bar>Re (winding_number \<gamma> z') - Re (winding_number \<gamma> z)\<bar>"
      using abs_Re_le_cmod [of "winding_number \<gamma> z' - winding_number \<gamma> z"] by simp
    then have wnz_12': "\<bar>Re (winding_number \<gamma> z')\<bar> > 1/2"
      by linarith
    moreover have "\<bar>Re (winding_number \<gamma> z')\<bar> < 1/2"
      apply (rule winding_number_lt_half [OF \<gamma> *])
      using azb \<open>d>0\<close> pag
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


subsection\<open>Cauchy's integral formula, again for a convex enclosing set.\<close>

lemma Cauchy_integral_formula_weak:
    assumes s: "convex s" and "finite k" and conf: "continuous_on s f"
        and fcd: "(\<And>x. x \<in> interior s - k \<Longrightarrow> f field_differentiable at x)"
        and z: "z \<in> interior s - k" and vpg: "valid_path \<gamma>"
        and pasz: "path_image \<gamma> \<subseteq> s - {z}" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
      shows "((\<lambda>w. f w / (w - z)) has_contour_integral (2*pi * \<i> * winding_number \<gamma> z * f z)) \<gamma>"
proof -
  obtain f' where f': "(f has_field_derivative f') (at z)"
    using fcd [OF z] by (auto simp: field_differentiable_def)
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
    then have dxz: "dist x z > 0" by auto
    have cf: "continuous (at x within s) f"
      using conf continuous_on_eq_continuous_within that by blast
    have "continuous (at x within s) (\<lambda>w. (f w - f z) / (w - z))"
      by (rule cf continuous_intros | simp add: False)+
    then show ?thesis
      apply (rule continuous_transform_within [OF _ dxz that, of "\<lambda>w::complex. (f w - f z)/(w - z)"])
      apply (force simp: dist_commute)
      done
  qed
  have fink': "finite (insert z k)" using \<open>finite k\<close> by blast
  have *: "((\<lambda>w. if w = z then f' else (f w - f z) / (w - z)) has_contour_integral 0) \<gamma>"
    apply (rule Cauchy_theorem_convex [OF _ s fink' _ vpg pas loop])
    using c apply (force simp: continuous_on_eq_continuous_within)
    apply (rename_tac w)
    apply (rule_tac d="dist w z" and f = "\<lambda>w. (f w - f z)/(w - z)" in field_differentiable_transform_within)
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
     \<Longrightarrow> ((\<lambda>w. f w / (w - z)) has_contour_integral (2*pi * \<i> * winding_number \<gamma> z * f z)) \<gamma>"
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
      using hom pathsf by (auto simp: linked_paths_def homotopic_paths_def homotopic_loops_def homotopic_with_def split: if_split_asm)
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
      by (rule uniformly_continuous_onE [OF ucontk, of "e/4"]) (auto simp: dist_norm \<open>e>0\<close>)
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
              (\<forall>t1 t2. t1 \<in> {0..1} \<and> t2 \<in> {0..1} \<and> \<bar>t1 - t\<bar> < e \<and> \<bar>t2 - t\<bar> < e
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
          (\<forall>t1 t2. t1 \<in> {0..1} \<longrightarrow> t2 \<in> {0..1} \<longrightarrow> \<bar>t1 - t\<bar> < ee t \<longrightarrow> \<bar>t2 - t\<bar> < ee t
            \<longrightarrow> (\<exists>d. 0 < d \<and>
                 (\<forall>g1 g2. valid_path g1 \<and> valid_path g2 \<and>
                   (\<forall>u \<in> {0..1}.
                      norm(g1 u - k((t1,u))) < d \<and> norm(g2 u - k((t2,u))) < d) \<and>
                      linked_paths atends g1 g2
                      \<longrightarrow> contour_integral g2 f = contour_integral g1 f)))"
    by metis
  note ee_rule = ee [THEN conjunct2, rule_format]
  define C where "C = (\<lambda>t. ball t (ee t / 3)) ` {0..1}"
  obtain C' where C': "C' \<subseteq> C" "finite C'" and C'01: "{0..1} \<subseteq> \<Union>C'"
  proof (rule compactE [OF compact_interval])
    show "{0..1} \<subseteq> \<Union>C"
      using ee [THEN conjunct1] by (auto simp: C_def dist_norm)
  qed (use C_def in auto)
  define kk where "kk = {t \<in> {0..1}. ball t (ee t / 3) \<in> C'}"
  have kk01: "kk \<subseteq> {0..1}" by (auto simp: kk_def)
  define e where "e = Min (ee ` kk)"
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
    have t01: "t \<in> {0..1}" using \<open>kk \<subseteq> {0..1}\<close> \<open>t \<in> kk\<close> by blast
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
    have min12: "min d1 d2 > 0" by (simp add: \<open>0 < d1\<close> \<open>0 < d2\<close>)
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
      apply (simp add: \<open>0 < d1\<close> \<open>0 < d2\<close>, clarify)
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


proposition winding_number_subpath_combine:
    "\<lbrakk>path g; z \<notin> path_image g;
      u \<in> {0..1}; v \<in> {0..1}; w \<in> {0..1}\<rbrakk>
      \<Longrightarrow> winding_number (subpath u v g) z + winding_number (subpath v w g) z =
          winding_number (subpath u w g) z"
apply (rule trans [OF winding_number_join [THEN sym]
                      winding_number_homotopic_paths [OF homotopic_join_subpaths]])
apply (auto dest: path_image_subpath_subset)
done


subsection\<open>Partial circle path\<close>

definition part_circlepath :: "[complex, real, real, real, real] \<Rightarrow> complex"
  where "part_circlepath z r s t \<equiv> \<lambda>x. z + of_real r * exp (\<i> * of_real (linepath s t x))"

lemma pathstart_part_circlepath [simp]:
     "pathstart(part_circlepath z r s t) = z + r*exp(\<i> * s)"
by (metis part_circlepath_def pathstart_def pathstart_linepath)

lemma pathfinish_part_circlepath [simp]:
     "pathfinish(part_circlepath z r s t) = z + r*exp(\<i>*t)"
by (metis part_circlepath_def pathfinish_def pathfinish_linepath)

proposition has_vector_derivative_part_circlepath [derivative_intros]:
    "((part_circlepath z r s t) has_vector_derivative
      (\<i> * r * (of_real t - of_real s) * exp(\<i> * linepath s t x)))
     (at x within X)"
  apply (simp add: part_circlepath_def linepath_def scaleR_conv_of_real)
  apply (rule has_vector_derivative_real_complex)
  apply (rule derivative_eq_intros | simp)+
  done

corollary vector_derivative_part_circlepath:
    "vector_derivative (part_circlepath z r s t) (at x) =
       \<i> * r * (of_real t - of_real s) * exp(\<i> * linepath s t x)"
  using has_vector_derivative_part_circlepath vector_derivative_at by blast

corollary vector_derivative_part_circlepath01:
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
      apply (auto simp: algebra_simps divide_simps)
      done
  }
  ultimately show ?thesis
    by (fastforce simp add: path_image_def part_circlepath_def)
qed

corollary path_image_part_circlepath_subset:
    "\<lbrakk>s \<le> t; 0 \<le> r\<rbrakk> \<Longrightarrow> path_image(part_circlepath z r s t) \<subseteq> sphere z r"
by (auto simp: path_image_part_circlepath sphere_def dist_norm algebra_simps norm_mult)

proposition in_path_image_part_circlepath:
  assumes "w \<in> path_image(part_circlepath z r s t)" "s \<le> t" "0 \<le> r"
    shows "norm(w - z) = r"
proof -
  have "w \<in> {c. dist z c = r}"
    by (metis (no_types) path_image_part_circlepath_subset sphere_def subset_eq assms)
  thus ?thesis
    by (simp add: dist_norm norm_minus_commute)
qed

proposition finite_bounded_log: "finite {z::complex. norm z \<le> b \<and> exp z = w}"
proof (cases "w = 0")
  case True then show ?thesis by auto
next
  case False
  have *: "finite {x. cmod (complex_of_real (2 * real_of_int x * pi) * \<i>) \<le> b + cmod (Ln w)}"
    apply (simp add: norm_mult finite_int_iff_bounded_le)
    apply (rule_tac x="\<lfloor>(b + cmod (Ln w)) / (2*pi)\<rfloor>" in exI)
    apply (auto simp: divide_simps le_floor_iff)
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

proposition has_contour_integral_bound_part_circlepath_strong:
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
      apply (rule has_integral_spike
              [where f = "\<lambda>x. f(part_circlepath z r s t x) * vector_derivative (part_circlepath z r s t) (at x)"])
      apply (rule negligible_finite [OF fin01])
      using fi has_contour_integral
      apply auto
      done
    have *: "\<And>x. \<lbrakk>0 \<le> x; x \<le> 1; part_circlepath z r s t x \<notin> k\<rbrakk> \<Longrightarrow> cmod (f (part_circlepath z r s t x)) \<le> B"
      by (auto intro!: B [unfolded path_image_def image_def, simplified])
    show ?thesis
      apply (rule has_integral_bound [where 'a=real, simplified, OF _ **, simplified])
      using assms apply force
      apply (simp add: norm_mult vector_derivative_part_circlepath)
      using le * "2" \<open>r > 0\<close> by auto
  qed
qed

corollary has_contour_integral_bound_part_circlepath:
      "\<lbrakk>(f has_contour_integral i) (part_circlepath z r s t);
        0 \<le> B; 0 < r; s \<le> t;
        \<And>x. x \<in> path_image(part_circlepath z r s t) \<Longrightarrow> norm(f x) \<le> B\<rbrakk>
       \<Longrightarrow> norm i \<le> B*r*(t - s)"
  by (auto intro: has_contour_integral_bound_part_circlepath_strong)

proposition contour_integrable_continuous_part_circlepath:
     "continuous_on (path_image (part_circlepath z r s t)) f
      \<Longrightarrow> f contour_integrable_on (part_circlepath z r s t)"
  apply (simp add: contour_integrable_on has_contour_integral_def vector_derivative_part_circlepath path_image_def)
  apply (rule integrable_continuous_real)
  apply (fast intro: path_part_circlepath [unfolded path_def] continuous_intros continuous_on_compose2 [where g=f, OF _ _ order_refl])
  done

proposition winding_number_part_circlepath_pos_less:
  assumes "s < t" and no: "norm(w - z) < r"
    shows "0 < Re (winding_number(part_circlepath z r s t) w)"
proof -
  have "0 < r" by (meson no norm_not_less_zero not_le order.strict_trans2)
  note valid_path_part_circlepath
  moreover have " w \<notin> path_image (part_circlepath z r s t)"
    using assms by (auto simp: path_image_def image_def part_circlepath_def norm_mult linepath_def)
  moreover have "0 < r * (t - s) * (r - cmod (w - z))"
    using assms by (metis \<open>0 < r\<close> diff_gt_0_iff_gt mult_pos_pos)
  ultimately show ?thesis
    apply (rule winding_number_pos_lt [where e = "r*(t - s)*(r - norm(w - z))"])
    apply (simp add: vector_derivative_part_circlepath right_diff_distrib [symmetric] mult_ac)
    apply (rule mult_left_mono)+
    using Re_Im_le_cmod [of "w-z" "linepath s t x" for x]
    apply (simp add: exp_Euler cos_of_real sin_of_real part_circlepath_def algebra_simps cos_squared_eq [unfolded power2_eq_square])
    using assms \<open>0 < r\<close> by auto
qed

proposition simple_path_part_circlepath:
    "simple_path(part_circlepath z r s t) \<longleftrightarrow> (r \<noteq> 0 \<and> s \<noteq> t \<and> \<bar>s - t\<bar> \<le> 2*pi)"
proof (cases "r = 0 \<or> s = t")
  case True
  then show ?thesis
    apply (rule disjE)
    apply (force simp: part_circlepath_def simple_path_def intro: bexI [where x = "1/4"] bexI [where x = "1/3"])+
    done
next
  case False then have "r \<noteq> 0" "s \<noteq> t" by auto
  have *: "\<And>x y z s t. \<i>*((1 - x) * s + x * t) = \<i>*(((1 - y) * s + y * t)) + z  \<longleftrightarrow> \<i>*(x - y) * (t - s) = z"
    by (simp add: algebra_simps)
  have abs01: "\<And>x y::real. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1
                      \<Longrightarrow> (x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0 \<longleftrightarrow> \<bar>x - y\<bar> \<in> {0,1})"
    by auto
  have abs_away: "\<And>P. (\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. P \<bar>x - y\<bar>) \<longleftrightarrow> (\<forall>x::real. 0 \<le> x \<and> x \<le> 1 \<longrightarrow> P x)"
    by force
  have **: "\<And>x y. (\<exists>n. (complex_of_real x - of_real y) * (of_real t - of_real s) = 2 * (of_int n * of_real pi)) \<longleftrightarrow>
                  (\<exists>n. \<bar>x - y\<bar> * (t - s) = 2 * (of_int n * pi))"
    by (force simp: algebra_simps abs_if dest: arg_cong [where f=Re] arg_cong [where f=complex_of_real]
                    intro: exI [where x = "-n" for n])
  have 1: "\<forall>x. 0 \<le> x \<and> x \<le> 1 \<longrightarrow> (\<exists>n. x * (t - s) = 2 * (real_of_int n * pi)) \<longrightarrow> x = 0 \<or> x = 1 \<Longrightarrow> \<bar>s - t\<bar> \<le> 2 * pi"
    apply (rule ccontr)
    apply (drule_tac x="2*pi / \<bar>t - s\<bar>" in spec)
    using False
    apply (simp add: abs_minus_commute divide_simps)
    apply (frule_tac x=1 in spec)
    apply (drule_tac x="-1" in spec)
    apply (simp add:)
    done
  have 2: "\<bar>s - t\<bar> = \<bar>2 * (real_of_int n * pi) / x\<bar>" if "x \<noteq> 0" "x * (t - s) = 2 * (real_of_int n * pi)" for x n
  proof -
    have "t-s = 2 * (real_of_int n * pi)/x"
      using that by (simp add: field_simps)
    then show ?thesis by (metis abs_minus_commute)
  qed
  show ?thesis using False
    apply (simp add: simple_path_def path_part_circlepath)
    apply (simp add: part_circlepath_def linepath_def exp_eq  * ** abs01  del: Set.insert_iff)
    apply (subst abs_away)
    apply (auto simp: 1)
    apply (rule ccontr)
    apply (auto simp: 2 divide_simps abs_mult dest: of_int_leD)
    done
qed

proposition arc_part_circlepath:
  assumes "r \<noteq> 0" "s \<noteq> t" "\<bar>s - t\<bar> < 2*pi"
    shows "arc (part_circlepath z r s t)"
proof -
  have *: "x = y" if eq: "\<i> * (linepath s t x) = \<i> * (linepath s t y) + 2 * of_int n * complex_of_real pi * \<i>"
                  and x: "x \<in> {0..1}" and y: "y \<in> {0..1}" for x y n
    proof -
      have "(linepath s t x) = (linepath s t y) + 2 * of_int n * complex_of_real pi"
        by (metis add_divide_eq_iff complex_i_not_zero mult.commute nonzero_mult_div_cancel_left eq)
      then have "s*y + t*x = s*x + (t*y + of_int n * (pi * 2))"
        by (force simp: algebra_simps linepath_def dest: arg_cong [where f=Re])
      then have st: "x \<noteq> y \<Longrightarrow> (s-t) = (of_int n * (pi * 2) / (y-x))"
        by (force simp: field_simps)
      show ?thesis
        apply (rule ccontr)
        using assms x y
        apply (simp add: st abs_mult field_simps)
        using st
        apply (auto simp: dest: of_int_lessD)
        done
    qed
  show ?thesis
    using assms
    apply (simp add: arc_def)
    apply (simp add: part_circlepath_def inj_on_def exp_eq)
    apply (blast intro: *)
    done
qed


subsection\<open>Special case of one complete circle\<close>

definition circlepath :: "[complex, real, real] \<Rightarrow> complex"
  where "circlepath z r \<equiv> part_circlepath z r 0 (2*pi)"

lemma circlepath: "circlepath z r = (\<lambda>x. z + r * exp(2 * of_real pi * \<i> * of_real x))"
  by (simp add: circlepath_def part_circlepath_def linepath_def algebra_simps)

lemma pathstart_circlepath [simp]: "pathstart (circlepath z r) = z + r"
  by (simp add: circlepath_def)

lemma pathfinish_circlepath [simp]: "pathfinish (circlepath z r) = z + r"
  by (simp add: circlepath_def) (metis exp_two_pi_i mult.commute)

lemma circlepath_minus: "circlepath z (-r) x = circlepath z r (x + 1/2)"
proof -
  have "z + of_real r * exp (2 * pi * \<i> * (x + 1 / 2)) =
        z + of_real r * exp (2 * pi * \<i> * x + pi * \<i>)"
    by (simp add: divide_simps) (simp add: algebra_simps)
  also have "... = z - r * exp (2 * pi * \<i> * x)"
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
  apply (force simp add: circlepath_add_half)+
  done

lemma path_image_circlepath_minus: "path_image (circlepath z (-r)) = path_image (circlepath z r)"
  using path_image_circlepath_minus_subset by fastforce

proposition has_vector_derivative_circlepath [derivative_intros]:
 "((circlepath z r) has_vector_derivative (2 * pi * \<i> * r * exp (2 * of_real pi * \<i> * of_real x)))
   (at x within X)"
  apply (simp add: circlepath_def scaleR_conv_of_real)
  apply (rule derivative_eq_intros)
  apply (simp add: algebra_simps)
  done

corollary vector_derivative_circlepath:
   "vector_derivative (circlepath z r) (at x) =
    2 * pi * \<i> * r * exp(2 * of_real pi * \<i> * x)"
using has_vector_derivative_circlepath vector_derivative_at by blast

corollary vector_derivative_circlepath01:
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
      apply (simp add: divide_simps \<open>w \<noteq> 0\<close>)
      using False **
      apply (auto simp: w_def)
      done
  qed
  show ?thesis
    unfolding circlepath path_image_def sphere_def dist_norm
    by (force simp: assms algebra_simps norm_mult norm_minus_commute intro: *)
qed

proposition path_image_circlepath [simp]:
    "path_image (circlepath z r) = sphere z \<bar>r\<bar>"
  using path_image_circlepath_minus
  by (force simp add: path_image_circlepath_nonneg abs_if)

lemma has_contour_integral_bound_circlepath_strong:
      "\<lbrakk>(f has_contour_integral i) (circlepath z r);
        finite k; 0 \<le> B; 0 < r;
        \<And>x. \<lbrakk>norm(x - z) = r; x \<notin> k\<rbrakk> \<Longrightarrow> norm(f x) \<le> B\<rbrakk>
        \<Longrightarrow> norm i \<le> B*(2*pi*r)"
  unfolding circlepath_def
  by (auto simp: algebra_simps in_path_image_part_circlepath dest!: has_contour_integral_bound_part_circlepath_strong)

corollary has_contour_integral_bound_circlepath:
      "\<lbrakk>(f has_contour_integral i) (circlepath z r);
        0 \<le> B; 0 < r; \<And>x. norm(x - z) = r \<Longrightarrow> norm(f x) \<le> B\<rbrakk>
        \<Longrightarrow> norm i \<le> B*(2*pi*r)"
  by (auto intro: has_contour_integral_bound_circlepath_strong)

proposition contour_integrable_continuous_circlepath:
    "continuous_on (path_image (circlepath z r)) f
     \<Longrightarrow> f contour_integrable_on (circlepath z r)"
  by (simp add: circlepath_def contour_integrable_continuous_part_circlepath)

lemma simple_path_circlepath: "simple_path(circlepath z r) \<longleftrightarrow> (r \<noteq> 0)"
  by (simp add: circlepath_def simple_path_part_circlepath)

lemma notin_path_image_circlepath [simp]: "cmod (w - z) < r \<Longrightarrow> w \<notin> path_image (circlepath z r)"
  by (simp add: sphere_def dist_norm norm_minus_commute)

proposition contour_integral_circlepath:
     "0 < r \<Longrightarrow> contour_integral (circlepath z r) (\<lambda>w. 1 / (w - z)) = 2 * complex_of_real pi * \<i>"
  apply (rule contour_integral_unique)
  apply (simp add: has_contour_integral_def)
  apply (subst has_integral_cong)
  apply (simp add: vector_derivative_circlepath01)
  using has_integral_const_real [of _ 0 1]
  apply (force simp: circlepath)
  done

lemma winding_number_circlepath_centre: "0 < r \<Longrightarrow> winding_number (circlepath z r) z = 1"
  apply (rule winding_number_unique_loop)
  apply (simp_all add: sphere_def valid_path_imp_path)
  apply (rule_tac x="circlepath z r" in exI)
  apply (simp add: sphere_def contour_integral_circlepath)
  done

proposition winding_number_circlepath:
  assumes "norm(w - z) < r" shows "winding_number(circlepath z r) w = 1"
proof (cases "w = z")
  case True then show ?thesis
    using assms winding_number_circlepath_centre by auto
next
  case False
  have [simp]: "r > 0"
    using assms le_less_trans norm_ge_zero by blast
  define r' where "r' = norm(w - z)"
  have "r' < r"
    by (simp add: assms r'_def)
  have disjo: "cball z r' \<inter> sphere z r = {}"
    using \<open>r' < r\<close> by (force simp: cball_def sphere_def)
  have "winding_number(circlepath z r) w = winding_number(circlepath z r) z"
    apply (rule winding_number_around_inside [where s = "cball z r'"])
    apply (simp_all add: disjo order.strict_implies_order winding_number_circlepath_centre)
    apply (simp_all add: False r'_def dist_norm norm_minus_commute)
    done
  also have "... = 1"
    by (simp add: winding_number_circlepath_centre)
  finally show ?thesis .
qed


text\<open> Hence the Cauchy formula for points inside a circle.\<close>

theorem Cauchy_integral_circlepath:
  assumes "continuous_on (cball z r) f" "f holomorphic_on (ball z r)" "norm(w - z) < r"
  shows "((\<lambda>u. f u/(u - w)) has_contour_integral (2 * of_real pi * \<i> * f w))
         (circlepath z r)"
proof -
  have "r > 0"
    using assms le_less_trans norm_ge_zero by blast
  have "((\<lambda>u. f u / (u - w)) has_contour_integral (2 * pi) * \<i> * winding_number (circlepath z r) w * f w)
        (circlepath z r)"
    apply (rule Cauchy_integral_formula_weak [where s = "cball z r" and k = "{}"])
    using assms  \<open>r > 0\<close>
    apply (simp_all add: dist_norm norm_minus_commute)
    apply (metis at_within_interior dist_norm holomorphic_on_def interior_ball mem_ball norm_minus_commute)
    apply (simp add: cball_def sphere_def dist_norm, clarify)
    apply (simp add:)
    by (metis dist_commute dist_norm less_irrefl)
  then show ?thesis
    by (simp add: winding_number_circlepath assms)
qed

corollary Cauchy_integral_circlepath_simple:
  assumes "f holomorphic_on cball z r" "norm(w - z) < r"
  shows "((\<lambda>u. f u/(u - w)) has_contour_integral (2 * of_real pi * \<i> * f w))
         (circlepath z r)"
using assms by (force simp: holomorphic_on_imp_continuous_on holomorphic_on_subset Cauchy_integral_circlepath)


lemma no_bounded_connected_component_imp_winding_number_zero:
  assumes g: "path g" "path_image g \<subseteq> s" "pathfinish g = pathstart g" "z \<notin> s"
      and nb: "\<And>z. bounded (connected_component_set (- s) z) \<longrightarrow> z \<in> s"
  shows "winding_number g z = 0"
apply (rule winding_number_zero_in_outside)
apply (simp_all add: assms)
by (metis nb [of z] \<open>path_image g \<subseteq> s\<close> \<open>z \<notin> s\<close> contra_subsetD mem_Collect_eq outside outside_mono)

lemma no_bounded_path_component_imp_winding_number_zero:
  assumes g: "path g" "path_image g \<subseteq> s" "pathfinish g = pathstart g" "z \<notin> s"
      and nb: "\<And>z. bounded (path_component_set (- s) z) \<longrightarrow> z \<in> s"
  shows "winding_number g z = 0"
apply (rule no_bounded_connected_component_imp_winding_number_zero [OF g])
by (simp add: bounded_subset nb path_component_subset_connected_component)


subsection\<open> Uniform convergence of path integral\<close>

text\<open>Uniform convergence when the derivative of the path is bounded, and in particular for the special case of a circle.\<close>

proposition contour_integral_uniform_limit:
  assumes ev_fint: "eventually (\<lambda>n::'a. (f n) contour_integrable_on \<gamma>) F"
      and ul_f: "uniform_limit (path_image \<gamma>) f l F"
      and noleB: "\<And>t. t \<in> {0..1} \<Longrightarrow> norm (vector_derivative \<gamma> (at t)) \<le> B"
      and \<gamma>: "valid_path \<gamma>"
      and [simp]: "~ (trivial_limit F)"
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
      using \<open>0 \<le> B\<close>  \<open>0 < e\<close> by (simp add: divide_simps)
    have "\<exists>h. (\<forall>x\<in>{0..1}. cmod (l (\<gamma> x) * vector_derivative \<gamma> (at x) - h x) \<le> e) \<and> h integrable_on {0..1}"
      apply (rule_tac x="\<lambda>x. f (a::'a) (\<gamma> x) * vector_derivative \<gamma> (at x)" in exI)
      apply (intro inta conjI ballI)
      apply (rule order_trans [OF _ Ble])
      apply (frule noleB)
      apply (frule fga)
      using \<open>0 \<le> B\<close>  \<open>0 < e\<close>
      apply (simp add: norm_mult left_diff_distrib [symmetric] norm_minus_commute divide_simps)
      apply (drule (1) mult_mono [OF less_imp_le])
      apply (simp_all add: mult_ac)
      done
  }
  then show lintg: "l contour_integrable_on \<gamma>"
    apply (simp add: contour_integrable_on)
    by (metis (mono_tags, lifting)integrable_uniform_limit_real) 
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
      also have "... < e"
        by (simp add: B' \<open>0 < e\<close> mult_imp_div_pos_less)
      finally have "2 * cmod (f x (\<gamma> t) - l (\<gamma> t)) * cmod (vector_derivative \<gamma> (at t)) < e" .
      then show ?thesis
        by (simp add: left_diff_distrib [symmetric] norm_mult)
    qed
    have "\<forall>\<^sub>F x in F. dist (contour_integral \<gamma> (f x)) (contour_integral \<gamma> l) < e"
      apply (rule eventually_mono [OF eventually_conj [OF ev_no' ev_fint]])
      apply (simp add: dist_norm contour_integrable_on path_image_def contour_integral_integral)
      apply (simp add: lintg integral_diff [symmetric] contour_integrable_on [symmetric], clarify)
      apply (rule le_less_trans [OF integral_norm_bound_integral ie])
      apply (simp add: lintg integrable_diff contour_integrable_on [symmetric])
      apply (blast intro: *)+
      done
  }
  then show "((\<lambda>n. contour_integral \<gamma> (f n)) \<longlongrightarrow> contour_integral \<gamma> l) F"
    by (rule tendstoI)
qed

corollary contour_integral_uniform_limit_circlepath:
  assumes "\<forall>\<^sub>F n::'a in F. (f n) contour_integrable_on (circlepath z r)"
      and "uniform_limit (sphere z r) f l F"
      and "~ (trivial_limit F)" "0 < r"
    shows "l contour_integrable_on (circlepath z r)"
          "((\<lambda>n. contour_integral (circlepath z r) (f n)) \<longlongrightarrow> contour_integral (circlepath z r) l) F"
  using assms by (auto simp: vector_derivative_circlepath norm_mult intro!: contour_integral_uniform_limit)


subsection\<open> General stepping result for derivative formulas.\<close>

proposition Cauchy_next_derivative:
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
  have 1: "\<forall>\<^sub>F n in at w. (\<lambda>x. f' x * (inverse (x - n) ^ k - inverse (x - w) ^ k) / (n - w) / of_nat k)
                         contour_integrable_on \<gamma>"
    apply (simp add: eventually_at)
    apply (rule_tac x=d in exI)
    apply (simp add: \<open>d > 0\<close> dist_norm field_simps, clarify)
    apply (rule contour_integrable_div [OF contour_integrable_diff])
    using int w d
    apply (force simp:  dist_norm norm_minus_commute intro!: has_contour_integral_integrable)+
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
                and uw_less: "cmod (u - w) < e * (d / 2) ^ (k+2) / (1 + real k)"
            for u x
    proof -
      define ff where [abs_def]:
        "ff n w =
          (if n = 0 then inverse(x - w)^k
           else if n = 1 then k / (x - w)^(Suc k)
           else (k * of_real(Suc k)) / (x - w)^(k + 2))" for n :: nat and w
      have km1: "\<And>z::complex. z \<noteq> 0 \<Longrightarrow> z ^ (k - Suc 0) = z ^ k / z"
        by (simp add: field_simps) (metis Suc_pred \<open>k \<noteq> 0\<close> neq0_conv power_Suc)
      have ff1: "(ff i has_field_derivative ff (Suc i) z) (at z within ball w (d / 2))"
              if "z \<in> ball w (d / 2)" "i \<le> 1" for i z
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
          apply (subst mult_le_cancel_left_pos)
          using \<open>k \<noteq> 0\<close>
          apply (auto simp: divide_simps)
          done
        with ab have "real k * (1 + real k) / a \<le> (real k * 4 + real k * real k * 4) / b \<longleftrightarrow> b \<le> 4 * a"
          by (simp add: field_simps)
      } note canc = this
      have ff2: "cmod (ff (Suc 1) v) \<le> real (k * (k + 1)) / (d / 2) ^ (k + 2)"
                if "v \<in> ball w (d / 2)" for v
      proof -
        have "d/2 \<le> cmod (x - v)" using d x that
          apply (simp add: dist_norm path_image_def ball_def not_less [symmetric] del: divide_const_simps, clarify)
          apply (drule subsetD)
           prefer 2 apply blast
          apply (metis norm_minus_commute norm_triangle_half_r CollectI)
          done
        then have "d \<le> cmod (x - v) * 2"
          by (simp add: divide_simps)
        then have dpow_le: "d ^ (k+2) \<le> (cmod (x - v) * 2) ^ (k+2)"
          using \<open>0 < d\<close> order_less_imp_le power_mono by blast
        have "x \<noteq> v" using that
          using \<open>x \<in> path_image \<gamma>\<close> ball_divide_subset_numeral d by fastforce
        then show ?thesis
        using \<open>d > 0\<close>
        apply (simp add: ff_def norm_mult norm_divide norm_power dist_norm canc)
        using dpow_le
        apply (simp add: algebra_simps divide_simps mult_less_0_iff)
        done
      qed
      have ub: "u \<in> ball w (d / 2)"
        using uwd by (simp add: dist_commute dist_norm)
      have "cmod (inverse (x - u) ^ k - (inverse (x - w) ^ k + of_nat k * (u - w) / ((x - w) * (x - w) ^ k)))
                  \<le> (real k * 4 + real k * real k * 4) * (cmod (u - w) * cmod (u - w)) / (d * (d * (d / 2) ^ k))"
        using complex_taylor [OF _ ff1 ff2 _ ub, of w, simplified]
        by (simp add: ff_def \<open>0 < d\<close>)
      then have "cmod (inverse (x - u) ^ k - (inverse (x - w) ^ k + of_nat k * (u - w) / ((x - w) * (x - w) ^ k)))
                  \<le> (cmod (u - w) * real k) * (1 + real k) * cmod (u - w) / (d / 2) ^ (k+2)"
        by (simp add: field_simps)
      then have "cmod (inverse (x - u) ^ k - (inverse (x - w) ^ k + of_nat k * (u - w) / ((x - w) * (x - w) ^ k)))
                 / (cmod (u - w) * real k)
                  \<le> (1 + real k) * cmod (u - w) / (d / 2) ^ (k+2)"
        using \<open>k \<noteq> 0\<close> \<open>u \<noteq> w\<close> by (simp add: mult_ac zero_less_mult_iff pos_divide_le_eq)
      also have "... < e"
        using uw_less \<open>0 < d\<close> by (simp add: mult_ac divide_simps)
      finally have e: "cmod (inverse (x-u)^k - (inverse (x-w)^k + of_nat k * (u-w) / ((x-w) * (x-w)^k)))
                        / cmod ((u - w) * real k)   <   e"
        by (simp add: norm_mult)
      have "x \<noteq> u"
        using uwd \<open>0 < d\<close> x d by (force simp: dist_norm ball_def norm_minus_commute)
      show ?thesis
        apply (rule le_less_trans [OF _ e])
        using \<open>k \<noteq> 0\<close> \<open>x \<noteq> u\<close>  \<open>u \<noteq> w\<close>
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
      also have "... = cmod (f' (\<gamma> x)) *
                       cmod ((inverse (\<gamma> x - u) ^ k - inverse (\<gamma> x - w) ^ k) / ((u - w) * k) -
                             inverse (\<gamma> x - w) * inverse (\<gamma> x - w) ^ k)"
        by (simp add: norm_mult)
      also have "... < cmod (f' (\<gamma> x)) * (e/C)"
        apply (rule mult_strict_left_mono [OF ec])
        using False by simp
      also have "... \<le> e" using C
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
    apply (rule contour_integral_unique)
    apply (simp add: diff_divide_distrib algebra_simps)
    apply (rule has_contour_integral_diff; rule has_contour_integral_div; simp add: field_simps; rule int)
    apply (metis contra_subsetD d dist_commute mem_ball that)
    apply (rule w)
    done
  show ?thes2
    apply (simp add: DERIV_within_iff del: power_Suc)
    apply (rule Lim_transform_within [OF tendsto_mult_left [OF *] \<open>0 < d\<close> ])
    apply (simp add: \<open>k \<noteq> 0\<close> **)
    done
qed

corollary Cauchy_next_derivative_circlepath:
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


text\<open> In particular, the first derivative formula.\<close>

proposition Cauchy_derivative_integral_circlepath:
  assumes contf: "continuous_on (cball z r) f"
      and holf: "f holomorphic_on ball z r"
      and w: "w \<in> ball z r"
    shows "(\<lambda>u. f u/(u - w)^2) contour_integrable_on (circlepath z r)"
           (is "?thes1")
      and "(f has_field_derivative (1 / (2 * of_real pi * \<i>) * contour_integral(circlepath z r) (\<lambda>u. f u / (u - w)^2))) (at w)"
           (is "?thes2")
proof -
  have [simp]: "r \<ge> 0" using w
    using ball_eq_empty by fastforce
  have f: "continuous_on (path_image (circlepath z r)) f"
    by (rule continuous_on_subset [OF contf]) (force simp add: cball_def sphere_def)
  have int: "\<And>w. dist z w < r \<Longrightarrow>
                 ((\<lambda>u. f u / (u - w)) has_contour_integral (\<lambda>x. 2 * of_real pi * \<i> * f x) w) (circlepath z r)"
    by (rule Cauchy_integral_circlepath [OF contf holf]) (simp add: dist_norm norm_minus_commute)
  show ?thes1
    apply (simp add: power2_eq_square)
    apply (rule Cauchy_next_derivative_circlepath [OF f _ _ w, where k=1, simplified])
    apply (blast intro: int)
    done
  have "((\<lambda>x. 2 * of_real pi * \<i> * f x) has_field_derivative contour_integral (circlepath z r) (\<lambda>u. f u / (u - w)^2)) (at w)"
    apply (simp add: power2_eq_square)
    apply (rule Cauchy_next_derivative_circlepath [OF f _ _ w, where k=1 and g = "\<lambda>x. 2 * of_real pi * \<i> * f x", simplified])
    apply (blast intro: int)
    done
  then have fder: "(f has_field_derivative contour_integral (circlepath z r) (\<lambda>u. f u / (u - w)^2) / (2 * of_real pi * \<i>)) (at w)"
    by (rule DERIV_cdivide [where f = "\<lambda>x. 2 * of_real pi * \<i> * f x" and c = "2 * of_real pi * \<i>", simplified])
  show ?thes2
    by simp (rule fder)
qed

subsection\<open> Existence of all higher derivatives.\<close>

proposition derivative_is_holomorphic:
  assumes "open s"
      and fder: "\<And>z. z \<in> s \<Longrightarrow> (f has_field_derivative f' z) (at z)"
    shows "f' holomorphic_on s"
proof -
  have *: "\<exists>h. (f' has_field_derivative h) (at z)" if "z \<in> s" for z
  proof -
    obtain r where "r > 0" and r: "cball z r \<subseteq> s"
      using open_contains_cball \<open>z \<in> s\<close> \<open>open s\<close> by blast
    then have holf_cball: "f holomorphic_on cball z r"
      apply (simp add: holomorphic_on_def)
      using field_differentiable_at_within field_differentiable_def fder by blast
    then have "continuous_on (path_image (circlepath z r)) f"
      using \<open>r > 0\<close> by (force elim: holomorphic_on_subset [THEN holomorphic_on_imp_continuous_on])
    then have contfpi: "continuous_on (path_image (circlepath z r)) (\<lambda>x. 1/(2 * of_real pi*\<i>) * f x)"
      by (auto intro: continuous_intros)+
    have contf_cball: "continuous_on (cball z r) f" using holf_cball
      by (simp add: holomorphic_on_imp_continuous_on holomorphic_on_subset)
    have holf_ball: "f holomorphic_on ball z r" using holf_cball
      using ball_subset_cball holomorphic_on_subset by blast
    { fix w  assume w: "w \<in> ball z r"
      have intf: "(\<lambda>u. f u / (u - w)\<^sup>2) contour_integrable_on circlepath z r"
        by (blast intro: w Cauchy_derivative_integral_circlepath [OF contf_cball holf_ball])
      have fder': "(f has_field_derivative 1 / (2 * of_real pi * \<i>) * contour_integral (circlepath z r) (\<lambda>u. f u / (u - w)\<^sup>2))
                  (at w)"
        by (blast intro: w Cauchy_derivative_integral_circlepath [OF contf_cball holf_ball])
      have f'_eq: "f' w = contour_integral (circlepath z r) (\<lambda>u. f u / (u - w)\<^sup>2) / (2 * of_real pi * \<i>)"
        using fder' ball_subset_cball r w by (force intro: DERIV_unique [OF fder])
      have "((\<lambda>u. f u / (u - w)\<^sup>2 / (2 * of_real pi * \<i>)) has_contour_integral
                contour_integral (circlepath z r) (\<lambda>u. f u / (u - w)\<^sup>2) / (2 * of_real pi * \<i>))
                (circlepath z r)"
        by (rule has_contour_integral_div [OF has_contour_integral_integral [OF intf]])
      then have "((\<lambda>u. f u / (2 * of_real pi * \<i> * (u - w)\<^sup>2)) has_contour_integral
                contour_integral (circlepath z r) (\<lambda>u. f u / (u - w)\<^sup>2) / (2 * of_real pi * \<i>))
                (circlepath z r)"
        by (simp add: algebra_simps)
      then have "((\<lambda>u. f u / (2 * of_real pi * \<i> * (u - w)\<^sup>2)) has_contour_integral f' w) (circlepath z r)"
        by (simp add: f'_eq)
    } note * = this
    show ?thesis
      apply (rule exI)
      apply (rule Cauchy_next_derivative_circlepath [OF contfpi, of 2 f', simplified])
      apply (simp_all add: \<open>0 < r\<close> * dist_norm)
      done
  qed
  show ?thesis
    by (simp add: holomorphic_on_open [OF \<open>open s\<close>] *)
qed

lemma holomorphic_deriv [holomorphic_intros]:
    "\<lbrakk>f holomorphic_on s; open s\<rbrakk> \<Longrightarrow> (deriv f) holomorphic_on s"
by (metis DERIV_deriv_iff_field_differentiable at_within_open derivative_is_holomorphic holomorphic_on_def)

lemma analytic_deriv [analytic_intros]: "f analytic_on s \<Longrightarrow> (deriv f) analytic_on s"
  using analytic_on_holomorphic holomorphic_deriv by auto

lemma holomorphic_higher_deriv [holomorphic_intros]: "\<lbrakk>f holomorphic_on s; open s\<rbrakk> \<Longrightarrow> (deriv ^^ n) f holomorphic_on s"
  by (induction n) (auto simp: holomorphic_deriv)

lemma analytic_higher_deriv [analytic_intros]: "f analytic_on s \<Longrightarrow> (deriv ^^ n) f analytic_on s"
  unfolding analytic_on_def using holomorphic_higher_deriv by blast

lemma has_field_derivative_higher_deriv:
     "\<lbrakk>f holomorphic_on s; open s; x \<in> s\<rbrakk>
      \<Longrightarrow> ((deriv ^^ n) f has_field_derivative (deriv ^^ (Suc n)) f x) (at x)"
by (metis (no_types, hide_lams) DERIV_deriv_iff_field_differentiable at_within_open comp_apply
         funpow.simps(2) holomorphic_higher_deriv holomorphic_on_def)

lemma valid_path_compose_holomorphic:
  assumes "valid_path g" and holo:"f holomorphic_on s" and "open s" "path_image g \<subseteq> s"
  shows "valid_path (f o g)"
proof (rule valid_path_compose[OF \<open>valid_path g\<close>])
  fix x assume "x \<in> path_image g"
  then show "f field_differentiable at x"
    using analytic_on_imp_differentiable_at analytic_on_open assms holo by blast
next
  have "deriv f holomorphic_on s"
    using holomorphic_deriv holo \<open>open s\<close> by auto
  then show "continuous_on (path_image g) (deriv f)"
    using assms(4) holomorphic_on_imp_continuous_on holomorphic_on_subset by auto
qed


subsection\<open> Morera's theorem.\<close>

lemma Morera_local_triangle_ball:
  assumes "\<And>z. z \<in> s
          \<Longrightarrow> \<exists>e a. 0 < e \<and> z \<in> ball a e \<and> continuous_on (ball a e) f \<and>
                    (\<forall>b c. closed_segment b c \<subseteq> ball a e
                           \<longrightarrow> contour_integral (linepath a b) f +
                               contour_integral (linepath b c) f +
                               contour_integral (linepath c a) f = 0)"
  shows "f analytic_on s"
proof -
  { fix z  assume "z \<in> s"
    with assms obtain e a where
            "0 < e" and z: "z \<in> ball a e" and contf: "continuous_on (ball a e) f"
        and 0: "\<And>b c. closed_segment b c \<subseteq> ball a e
                      \<Longrightarrow> contour_integral (linepath a b) f +
                          contour_integral (linepath b c) f +
                          contour_integral (linepath c a) f = 0"
      by fastforce
    have az: "dist a z < e" using mem_ball z by blast
    have sb_ball: "ball z (e - dist a z) \<subseteq> ball a e"
      by (simp add: dist_commute ball_subset_ball_iff)
    have "\<exists>e>0. f holomorphic_on ball z e"
      apply (rule_tac x="e - dist a z" in exI)
      apply (simp add: az)
      apply (rule holomorphic_on_subset [OF _ sb_ball])
      apply (rule derivative_is_holomorphic[OF open_ball])
      apply (rule triangle_contour_integrals_starlike_primitive [OF contf _ open_ball, of a])
         apply (simp_all add: 0 \<open>0 < e\<close>)
      apply (meson \<open>0 < e\<close> centre_in_ball convex_ball convex_contains_segment mem_ball)
      done
  }
  then show ?thesis
    by (simp add: analytic_on_def)
qed

lemma Morera_local_triangle:
  assumes "\<And>z. z \<in> s
          \<Longrightarrow> \<exists>t. open t \<and> z \<in> t \<and> continuous_on t f \<and>
                  (\<forall>a b c. convex hull {a,b,c} \<subseteq> t
                              \<longrightarrow> contour_integral (linepath a b) f +
                                  contour_integral (linepath b c) f +
                                  contour_integral (linepath c a) f = 0)"
  shows "f analytic_on s"
proof -
  { fix z  assume "z \<in> s"
    with assms obtain t where
            "open t" and z: "z \<in> t" and contf: "continuous_on t f"
        and 0: "\<And>a b c. convex hull {a,b,c} \<subseteq> t
                      \<Longrightarrow> contour_integral (linepath a b) f +
                          contour_integral (linepath b c) f +
                          contour_integral (linepath c a) f = 0"
      by force
    then obtain e where "e>0" and e: "ball z e \<subseteq> t"
      using open_contains_ball by blast
    have [simp]: "continuous_on (ball z e) f" using contf
      using continuous_on_subset e by blast
    have "\<exists>e a. 0 < e \<and>
               z \<in> ball a e \<and>
               continuous_on (ball a e) f \<and>
               (\<forall>b c. closed_segment b c \<subseteq> ball a e \<longrightarrow>
                      contour_integral (linepath a b) f + contour_integral (linepath b c) f + contour_integral (linepath c a) f = 0)"
      apply (rule_tac x=e in exI)
      apply (rule_tac x=z in exI)
      apply (simp add: \<open>e > 0\<close>, clarify)
      apply (rule 0)
      apply (meson z \<open>0 < e\<close> centre_in_ball closed_segment_subset convex_ball dual_order.trans e starlike_convex_subset)
      done
  }
  then show ?thesis
    by (simp add: Morera_local_triangle_ball)
qed

proposition Morera_triangle:
    "\<lbrakk>continuous_on s f; open s;
      \<And>a b c. convex hull {a,b,c} \<subseteq> s
              \<longrightarrow> contour_integral (linepath a b) f +
                  contour_integral (linepath b c) f +
                  contour_integral (linepath c a) f = 0\<rbrakk>
     \<Longrightarrow> f analytic_on s"
  using Morera_local_triangle by blast



subsection\<open> Combining theorems for higher derivatives including Leibniz rule.\<close>

lemma higher_deriv_linear [simp]:
    "(deriv ^^ n) (\<lambda>w. c*w) = (\<lambda>z. if n = 0 then c*z else if n = 1 then c else 0)"
  by (induction n) (auto simp: deriv_const deriv_linear)

lemma higher_deriv_const [simp]: "(deriv ^^ n) (\<lambda>w. c) = (\<lambda>w. if n=0 then c else 0)"
  by (induction n) (auto simp: deriv_const)

lemma higher_deriv_ident [simp]:
     "(deriv ^^ n) (\<lambda>w. w) z = (if n = 0 then z else if n = 1 then 1 else 0)"
  apply (induction n, simp)
  apply (metis higher_deriv_linear lambda_one)
  done

corollary higher_deriv_id [simp]:
     "(deriv ^^ n) id z = (if n = 0 then z else if n = 1 then 1 else 0)"
  by (simp add: id_def)

lemma has_complex_derivative_funpow_1:
     "\<lbrakk>(f has_field_derivative 1) (at z); f z = z\<rbrakk> \<Longrightarrow> (f^^n has_field_derivative 1) (at z)"
  apply (induction n)
  apply auto
  apply (metis DERIV_ident DERIV_transform_at id_apply zero_less_one)
  by (metis DERIV_chain comp_funpow comp_id funpow_swap1 mult.right_neutral)

proposition higher_deriv_uminus:
  assumes "f holomorphic_on s" "open s" and z: "z \<in> s"
    shows "(deriv ^^ n) (\<lambda>w. -(f w)) z = - ((deriv ^^ n) f z)"
using z
proof (induction n arbitrary: z)
  case 0 then show ?case by simp
next
  case (Suc n z)
  have *: "((deriv ^^ n) f has_field_derivative deriv ((deriv ^^ n) f) z) (at z)"
    using Suc.prems assms has_field_derivative_higher_deriv by auto
  show ?case
    apply simp
    apply (rule DERIV_imp_deriv)
    apply (rule DERIV_transform_within_open [of "\<lambda>w. -((deriv ^^ n) f w)"])
    apply (rule derivative_eq_intros | rule * refl assms Suc)+
    apply (simp add: Suc)
    done
qed

proposition higher_deriv_add:
  fixes z::complex
  assumes "f holomorphic_on s" "g holomorphic_on s" "open s" and z: "z \<in> s"
    shows "(deriv ^^ n) (\<lambda>w. f w + g w) z = (deriv ^^ n) f z + (deriv ^^ n) g z"
using z
proof (induction n arbitrary: z)
  case 0 then show ?case by simp
next
  case (Suc n z)
  have *: "((deriv ^^ n) f has_field_derivative deriv ((deriv ^^ n) f) z) (at z)"
          "((deriv ^^ n) g has_field_derivative deriv ((deriv ^^ n) g) z) (at z)"
    using Suc.prems assms has_field_derivative_higher_deriv by auto
  show ?case
    apply simp
    apply (rule DERIV_imp_deriv)
    apply (rule DERIV_transform_within_open [of "\<lambda>w. (deriv ^^ n) f w + (deriv ^^ n) g w"])
    apply (rule derivative_eq_intros | rule * refl assms Suc)+
    apply (simp add: Suc)
    done
qed

corollary higher_deriv_diff:
  fixes z::complex
  assumes "f holomorphic_on s" "g holomorphic_on s" "open s" and z: "z \<in> s"
    shows "(deriv ^^ n) (\<lambda>w. f w - g w) z = (deriv ^^ n) f z - (deriv ^^ n) g z"
  apply (simp only: Groups.group_add_class.diff_conv_add_uminus higher_deriv_add)
  apply (subst higher_deriv_add)
  using assms holomorphic_on_minus apply (auto simp: higher_deriv_uminus)
  done


lemma bb: "Suc n choose k = (n choose k) + (if k = 0 then 0 else (n choose (k - 1)))"
  by (cases k) simp_all

proposition higher_deriv_mult:
  fixes z::complex
  assumes "f holomorphic_on s" "g holomorphic_on s" "open s" and z: "z \<in> s"
    shows "(deriv ^^ n) (\<lambda>w. f w * g w) z =
           (\<Sum>i = 0..n. of_nat (n choose i) * (deriv ^^ i) f z * (deriv ^^ (n - i)) g z)"
using z
proof (induction n arbitrary: z)
  case 0 then show ?case by simp
next
  case (Suc n z)
  have *: "\<And>n. ((deriv ^^ n) f has_field_derivative deriv ((deriv ^^ n) f) z) (at z)"
          "\<And>n. ((deriv ^^ n) g has_field_derivative deriv ((deriv ^^ n) g) z) (at z)"
    using Suc.prems assms has_field_derivative_higher_deriv by auto
  have sumeq: "(\<Sum>i = 0..n.
               of_nat (n choose i) * (deriv ((deriv ^^ i) f) z * (deriv ^^ (n - i)) g z + deriv ((deriv ^^ (n - i)) g) z * (deriv ^^ i) f z)) =
            g z * deriv ((deriv ^^ n) f) z + (\<Sum>i = 0..n. (deriv ^^ i) f z * (of_nat (Suc n choose i) * (deriv ^^ (Suc n - i)) g z))"
    apply (simp add: bb algebra_simps sum.distrib)
    apply (subst (4) sum_Suc_reindex)
    apply (auto simp: algebra_simps Suc_diff_le intro: sum.cong)
    done
  show ?case
    apply (simp only: funpow.simps o_apply)
    apply (rule DERIV_imp_deriv)
    apply (rule DERIV_transform_within_open
             [of "\<lambda>w. (\<Sum>i = 0..n. of_nat (n choose i) * (deriv ^^ i) f w * (deriv ^^ (n - i)) g w)"])
    apply (simp add: algebra_simps)
    apply (rule DERIV_cong [OF DERIV_sum])
    apply (rule DERIV_cmult)
    apply (auto simp: intro: DERIV_mult * sumeq \<open>open s\<close> Suc.prems Suc.IH [symmetric])
    done
qed


proposition higher_deriv_transform_within_open:
  fixes z::complex
  assumes "f holomorphic_on s" "g holomorphic_on s" "open s" and z: "z \<in> s"
      and fg: "\<And>w. w \<in> s \<Longrightarrow> f w = g w"
    shows "(deriv ^^ i) f z = (deriv ^^ i) g z"
using z
by (induction i arbitrary: z)
   (auto simp: fg intro: complex_derivative_transform_within_open holomorphic_higher_deriv assms)

proposition higher_deriv_compose_linear:
  fixes z::complex
  assumes f: "f holomorphic_on t" and s: "open s" and t: "open t" and z: "z \<in> s"
      and fg: "\<And>w. w \<in> s \<Longrightarrow> u * w \<in> t"
    shows "(deriv ^^ n) (\<lambda>w. f (u * w)) z = u^n * (deriv ^^ n) f (u * z)"
using z
proof (induction n arbitrary: z)
  case 0 then show ?case by simp
next
  case (Suc n z)
  have holo0: "f holomorphic_on op * u ` s"
    by (meson fg f holomorphic_on_subset image_subset_iff)
  have holo1: "(\<lambda>w. f (u * w)) holomorphic_on s"
    apply (rule holomorphic_on_compose [where g=f, unfolded o_def])
    apply (rule holo0 holomorphic_intros)+
    done
  have holo2: "(\<lambda>z. u ^ n * (deriv ^^ n) f (u * z)) holomorphic_on s"
    apply (rule holomorphic_intros)+
    apply (rule holomorphic_on_compose [where g="(deriv ^^ n) f", unfolded o_def])
    apply (rule holomorphic_intros)
    apply (rule holomorphic_on_subset [where s=t])
    apply (rule holomorphic_intros assms)+
    apply (blast intro: fg)
    done
  have "deriv ((deriv ^^ n) (\<lambda>w. f (u * w))) z = deriv (\<lambda>z. u^n * (deriv ^^ n) f (u*z)) z"
    apply (rule complex_derivative_transform_within_open [OF _ holo2 s Suc.prems])
    apply (rule holomorphic_higher_deriv [OF holo1 s])
    apply (simp add: Suc.IH)
    done
  also have "... = u^n * deriv (\<lambda>z. (deriv ^^ n) f (u * z)) z"
    apply (rule deriv_cmult)
    apply (rule analytic_on_imp_differentiable_at [OF _ Suc.prems])
    apply (rule analytic_on_compose_gen [where g="(deriv ^^ n) f" and t=t, unfolded o_def])
    apply (simp add: analytic_on_linear)
    apply (simp add: analytic_on_open f holomorphic_higher_deriv t)
    apply (blast intro: fg)
    done
  also have "... = u * u ^ n * deriv ((deriv ^^ n) f) (u * z)"
      apply (subst complex_derivative_chain [where g = "(deriv ^^ n) f" and f = "op* u", unfolded o_def])
      apply (rule derivative_intros)
      using Suc.prems field_differentiable_def f fg has_field_derivative_higher_deriv t apply blast
      apply (simp add: deriv_linear)
      done
  finally show ?case
    by simp
qed

lemma higher_deriv_add_at:
  assumes "f analytic_on {z}" "g analytic_on {z}"
    shows "(deriv ^^ n) (\<lambda>w. f w + g w) z = (deriv ^^ n) f z + (deriv ^^ n) g z"
proof -
  have "f analytic_on {z} \<and> g analytic_on {z}"
    using assms by blast
  with higher_deriv_add show ?thesis
    by (auto simp: analytic_at_two)
qed

lemma higher_deriv_diff_at:
  assumes "f analytic_on {z}" "g analytic_on {z}"
    shows "(deriv ^^ n) (\<lambda>w. f w - g w) z = (deriv ^^ n) f z - (deriv ^^ n) g z"
proof -
  have "f analytic_on {z} \<and> g analytic_on {z}"
    using assms by blast
  with higher_deriv_diff show ?thesis
    by (auto simp: analytic_at_two)
qed

lemma higher_deriv_uminus_at:
   "f analytic_on {z}  \<Longrightarrow> (deriv ^^ n) (\<lambda>w. -(f w)) z = - ((deriv ^^ n) f z)"
  using higher_deriv_uminus
    by (auto simp: analytic_at)

lemma higher_deriv_mult_at:
  assumes "f analytic_on {z}" "g analytic_on {z}"
    shows "(deriv ^^ n) (\<lambda>w. f w * g w) z =
           (\<Sum>i = 0..n. of_nat (n choose i) * (deriv ^^ i) f z * (deriv ^^ (n - i)) g z)"
proof -
  have "f analytic_on {z} \<and> g analytic_on {z}"
    using assms by blast
  with higher_deriv_mult show ?thesis
    by (auto simp: analytic_at_two)
qed


text\<open> Nonexistence of isolated singularities and a stronger integral formula.\<close>

proposition no_isolated_singularity:
  fixes z::complex
  assumes f: "continuous_on s f" and holf: "f holomorphic_on (s - k)" and s: "open s" and k: "finite k"
    shows "f holomorphic_on s"
proof -
  { fix z
    assume "z \<in> s" and cdf: "\<And>x. x\<in>s - k \<Longrightarrow> f field_differentiable at x"
    have "f field_differentiable at z"
    proof (cases "z \<in> k")
      case False then show ?thesis by (blast intro: cdf \<open>z \<in> s\<close>)
    next
      case True
      with finite_set_avoid [OF k, of z]
      obtain d where "d>0" and d: "\<And>x. \<lbrakk>x\<in>k; x \<noteq> z\<rbrakk> \<Longrightarrow> d \<le> dist z x"
        by blast
      obtain e where "e>0" and e: "ball z e \<subseteq> s"
        using  s \<open>z \<in> s\<close> by (force simp add: open_contains_ball)
      have fde: "continuous_on (ball z (min d e)) f"
        by (metis Int_iff ball_min_Int continuous_on_subset e f subsetI)
      have "\<exists>g. \<forall>w \<in> ball z (min d e). (g has_field_derivative f w) (at w within ball z (min d e))"
        apply (rule contour_integral_convex_primitive [OF convex_ball fde])
        apply (rule Cauchy_theorem_triangle_cofinite [OF _ k])
         apply (metis continuous_on_subset [OF fde] closed_segment_subset convex_ball starlike_convex_subset)
        apply (rule cdf)
        apply (metis Diff_iff Int_iff ball_min_Int bot_least contra_subsetD convex_ball e insert_subset
               interior_mono interior_subset subset_hull)
        done
      then have "f holomorphic_on ball z (min d e)"
        by (metis open_ball at_within_open derivative_is_holomorphic)
      then show ?thesis
        unfolding holomorphic_on_def
        by (metis open_ball \<open>0 < d\<close> \<open>0 < e\<close> at_within_open centre_in_ball min_less_iff_conj)
    qed
  }
  with holf s k show ?thesis
    by (simp add: holomorphic_on_open open_Diff finite_imp_closed field_differentiable_def [symmetric])
qed

lemma no_isolated_singularity':
  fixes z::complex
  assumes f: "\<And>z. z \<in> k \<Longrightarrow> (f \<longlongrightarrow> f z) (at z within s)" 
      and holf: "f holomorphic_on (s - k)" and s: "open s" and k: "finite k"
    shows "f holomorphic_on s"
proof (rule no_isolated_singularity[OF _ assms(2-)])
  show "continuous_on s f" unfolding continuous_on_def
  proof
    fix z assume z: "z \<in> s"
    show "(f \<longlongrightarrow> f z) (at z within s)"
    proof (cases "z \<in> k")
      case False
      from holf have "continuous_on (s - k) f" 
        by (rule holomorphic_on_imp_continuous_on)
      with z False have "(f \<longlongrightarrow> f z) (at z within (s - k))" 
        by (simp add: continuous_on_def)
      also from z k s False have "at z within (s - k) = at z within s"
        by (subst (1 2) at_within_open) (auto intro: finite_imp_closed)
      finally show "(f \<longlongrightarrow> f z) (at z within s)" .
    qed (insert assms z, simp_all)
  qed
qed

proposition Cauchy_integral_formula_convex:
    assumes s: "convex s" and k: "finite k" and contf: "continuous_on s f"
        and fcd: "(\<And>x. x \<in> interior s - k \<Longrightarrow> f field_differentiable at x)"
        and z: "z \<in> interior s" and vpg: "valid_path \<gamma>"
        and pasz: "path_image \<gamma> \<subseteq> s - {z}" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
      shows "((\<lambda>w. f w / (w - z)) has_contour_integral (2*pi * \<i> * winding_number \<gamma> z * f z)) \<gamma>"
  apply (rule Cauchy_integral_formula_weak [OF s finite.emptyI contf])
  apply (simp add: holomorphic_on_open [symmetric] field_differentiable_def)
  using no_isolated_singularity [where s = "interior s"]
  apply (metis k contf fcd holomorphic_on_open field_differentiable_def continuous_on_subset
               has_field_derivative_at_within holomorphic_on_def interior_subset open_interior)
  using assms
  apply auto
  done


text\<open> Formula for higher derivatives.\<close>

proposition Cauchy_has_contour_integral_higher_derivative_circlepath:
  assumes contf: "continuous_on (cball z r) f"
      and holf: "f holomorphic_on ball z r"
      and w: "w \<in> ball z r"
    shows "((\<lambda>u. f u / (u - w) ^ (Suc k)) has_contour_integral ((2 * pi * \<i>) / (fact k) * (deriv ^^ k) f w))
           (circlepath z r)"
using w
proof (induction k arbitrary: w)
  case 0 then show ?case
    using assms by (auto simp: Cauchy_integral_circlepath dist_commute dist_norm)
next
  case (Suc k)
  have [simp]: "r > 0" using w
    using ball_eq_empty by fastforce
  have f: "continuous_on (path_image (circlepath z r)) f"
    by (rule continuous_on_subset [OF contf]) (force simp add: cball_def sphere_def less_imp_le)
  obtain X where X: "((\<lambda>u. f u / (u - w) ^ Suc (Suc k)) has_contour_integral X) (circlepath z r)"
    using Cauchy_next_derivative_circlepath(1) [OF f Suc.IH _ Suc.prems]
    by (auto simp: contour_integrable_on_def)
  then have con: "contour_integral (circlepath z r) ((\<lambda>u. f u / (u - w) ^ Suc (Suc k))) = X"
    by (rule contour_integral_unique)
  have "\<And>n. ((deriv ^^ n) f has_field_derivative deriv ((deriv ^^ n) f) w) (at w)"
    using Suc.prems assms has_field_derivative_higher_deriv by auto
  then have dnf_diff: "\<And>n. (deriv ^^ n) f field_differentiable (at w)"
    by (force simp add: field_differentiable_def)
  have "deriv (\<lambda>w. complex_of_real (2 * pi) * \<i> / (fact k) * (deriv ^^ k) f w) w =
          of_nat (Suc k) * contour_integral (circlepath z r) (\<lambda>u. f u / (u - w) ^ Suc (Suc k))"
    by (force intro!: DERIV_imp_deriv Cauchy_next_derivative_circlepath [OF f Suc.IH _ Suc.prems])
  also have "... = of_nat (Suc k) * X"
    by (simp only: con)
  finally have "deriv (\<lambda>w. ((2 * pi) * \<i> / (fact k)) * (deriv ^^ k) f w) w = of_nat (Suc k) * X" .
  then have "((2 * pi) * \<i> / (fact k)) * deriv (\<lambda>w. (deriv ^^ k) f w) w = of_nat (Suc k) * X"
    by (metis deriv_cmult dnf_diff)
  then have "deriv (\<lambda>w. (deriv ^^ k) f w) w = of_nat (Suc k) * X / ((2 * pi) * \<i> / (fact k))"
    by (simp add: field_simps)
  then show ?case
  using of_nat_eq_0_iff X by fastforce
qed

proposition Cauchy_higher_derivative_integral_circlepath:
  assumes contf: "continuous_on (cball z r) f"
      and holf: "f holomorphic_on ball z r"
      and w: "w \<in> ball z r"
    shows "(\<lambda>u. f u / (u - w)^(Suc k)) contour_integrable_on (circlepath z r)"
           (is "?thes1")
      and "(deriv ^^ k) f w = (fact k) / (2 * pi * \<i>) * contour_integral(circlepath z r) (\<lambda>u. f u/(u - w)^(Suc k))"
           (is "?thes2")
proof -
  have *: "((\<lambda>u. f u / (u - w) ^ Suc k) has_contour_integral (2 * pi) * \<i> / (fact k) * (deriv ^^ k) f w)
           (circlepath z r)"
    using Cauchy_has_contour_integral_higher_derivative_circlepath [OF assms]
    by simp
  show ?thes1 using *
    using contour_integrable_on_def by blast
  show ?thes2
    unfolding contour_integral_unique [OF *] by (simp add: divide_simps)
qed

corollary Cauchy_contour_integral_circlepath:
  assumes "continuous_on (cball z r) f" "f holomorphic_on ball z r" "w \<in> ball z r"
    shows "contour_integral(circlepath z r) (\<lambda>u. f u/(u - w)^(Suc k)) = (2 * pi * \<i>) * (deriv ^^ k) f w / (fact k)"
by (simp add: Cauchy_higher_derivative_integral_circlepath [OF assms])

corollary Cauchy_contour_integral_circlepath_2:
  assumes "continuous_on (cball z r) f" "f holomorphic_on ball z r" "w \<in> ball z r"
    shows "contour_integral(circlepath z r) (\<lambda>u. f u/(u - w)^2) = (2 * pi * \<i>) * deriv f w"
  using Cauchy_contour_integral_circlepath [OF assms, of 1]
  by (simp add: power2_eq_square)


subsection\<open>A holomorphic function is analytic, i.e. has local power series.\<close>

theorem holomorphic_power_series:
  assumes holf: "f holomorphic_on ball z r"
      and w: "w \<in> ball z r"
    shows "((\<lambda>n. (deriv ^^ n) f z / (fact n) * (w - z)^n) sums f w)"
proof -
  have fh': "f holomorphic_on cball z ((r + dist w z) / 2)"
     apply (rule holomorphic_on_subset [OF holf])
     apply (clarsimp simp del: divide_const_simps)
     apply (metis add.commute dist_commute le_less_trans mem_ball real_gt_half_sum w)
     done
  \<comment>\<open>Replacing @{term r} and the original (weak) premises\<close>
  obtain r where "0 < r" and holfc: "f holomorphic_on cball z r" and w: "w \<in> ball z r"
    apply (rule that [of "(r + dist w z) / 2"])
      apply (simp_all add: fh')
     apply (metis add_0_iff ball_eq_empty dist_nz dist_self empty_iff not_less pos_add_strict w)
    apply (metis add_less_cancel_right dist_commute mem_ball mult_2_right w)
    done
  then have holf: "f holomorphic_on ball z r" and contf: "continuous_on (cball z r) f"
    using ball_subset_cball holomorphic_on_subset apply blast
    by (simp add: holfc holomorphic_on_imp_continuous_on)
  have cint: "\<And>k. (\<lambda>u. f u / (u - z) ^ Suc k) contour_integrable_on circlepath z r"
    apply (rule Cauchy_higher_derivative_integral_circlepath [OF contf holf])
    apply (simp add: \<open>0 < r\<close>)
    done
  obtain B where "0 < B" and B: "\<And>u. u \<in> cball z r \<Longrightarrow> norm(f u) \<le> B"
    by (metis (no_types) bounded_pos compact_cball compact_continuous_image compact_imp_bounded contf image_eqI)
  obtain k where k: "0 < k" "k \<le> r" and wz_eq: "norm(w - z) = r - k"
             and kle: "\<And>u. norm(u - z) = r \<Longrightarrow> k \<le> norm(u - w)"
    apply (rule_tac k = "r - dist z w" in that)
    using w
    apply (auto simp: dist_norm norm_minus_commute)
    by (metis add_diff_eq diff_add_cancel norm_diff_ineq norm_minus_commute)
  have ul: "uniform_limit (sphere z r) (\<lambda>n x. (\<Sum>k<n. (w - z) ^ k * (f x / (x - z) ^ Suc k))) (\<lambda>x. f x / (x - w)) sequentially"
    unfolding uniform_limit_iff dist_norm 
  proof clarify
    fix e::real
    assume "0 < e"
    have rr: "0 \<le> (r - k) / r" "(r - k) / r < 1" using  k by auto
    obtain n where n: "((r - k) / r) ^ n < e / B * k"
      using real_arch_pow_inv [of "e/B*k" "(r - k)/r"] \<open>0 < e\<close> \<open>0 < B\<close> k by force
    have "norm ((\<Sum>k<N. (w - z) ^ k * f u / (u - z) ^ Suc k) - f u / (u - w)) < e"
         if "n \<le> N" and r: "r = dist z u"  for N u
    proof -
      have N: "((r - k) / r) ^ N < e / B * k"
        apply (rule le_less_trans [OF power_decreasing n])
        using  \<open>n \<le> N\<close> k by auto
      have u [simp]: "(u \<noteq> z) \<and> (u \<noteq> w)"
        using \<open>0 < r\<close> r w by auto
      have wzu_not1: "(w - z) / (u - z) \<noteq> 1"
        by (metis (no_types) dist_norm divide_eq_1_iff less_irrefl mem_ball norm_minus_commute r w)
      have "norm ((\<Sum>k<N. (w - z) ^ k * f u / (u - z) ^ Suc k) * (u - w) - f u)
            = norm ((\<Sum>k<N. (((w - z) / (u - z)) ^ k)) * f u * (u - w) / (u - z) - f u)"
        unfolding sum_distrib_right sum_divide_distrib power_divide by (simp add: algebra_simps)
      also have "... = norm ((((w - z) / (u - z)) ^ N - 1) * (u - w) / (((w - z) / (u - z) - 1) * (u - z)) - 1) * norm (f u)"
        using \<open>0 < B\<close>
        apply (auto simp: geometric_sum [OF wzu_not1])
        apply (simp add: field_simps norm_mult [symmetric])
        done
      also have "... = norm ((u-z) ^ N * (w - u) - ((w - z) ^ N - (u-z) ^ N) * (u-w)) / (r ^ N * norm (u-w)) * norm (f u)"
        using \<open>0 < r\<close> r by (simp add: divide_simps norm_mult norm_divide norm_power dist_norm norm_minus_commute)
      also have "... = norm ((w - z) ^ N * (w - u)) / (r ^ N * norm (u - w)) * norm (f u)"
        by (simp add: algebra_simps)
      also have "... = norm (w - z) ^ N * norm (f u) / r ^ N"
        by (simp add: norm_mult norm_power norm_minus_commute)
      also have "... \<le> (((r - k)/r)^N) * B"
        using \<open>0 < r\<close> w k
        apply (simp add: divide_simps)
        apply (rule mult_mono [OF power_mono])
        apply (auto simp: norm_divide wz_eq norm_power dist_norm norm_minus_commute B r)
        done
      also have "... < e * k"
        using \<open>0 < B\<close> N by (simp add: divide_simps)
      also have "... \<le> e * norm (u - w)"
        using r kle \<open>0 < e\<close> by (simp add: dist_commute dist_norm)
      finally show ?thesis
        by (simp add: divide_simps norm_divide del: power_Suc)
    qed
    with \<open>0 < r\<close> show "\<forall>\<^sub>F n in sequentially. \<forall>x\<in>sphere z r.
                norm ((\<Sum>k<n. (w - z) ^ k * (f x / (x - z) ^ Suc k)) - f x / (x - w)) < e"
      by (auto simp: mult_ac less_imp_le eventually_sequentially Ball_def)
  qed
  have eq: "\<forall>\<^sub>F x in sequentially.
             contour_integral (circlepath z r) (\<lambda>u. \<Sum>k<x. (w - z) ^ k * (f u / (u - z) ^ Suc k)) =
             (\<Sum>k<x. contour_integral (circlepath z r) (\<lambda>u. f u / (u - z) ^ Suc k) * (w - z) ^ k)"
    apply (rule eventuallyI)
    apply (subst contour_integral_sum, simp)
    using contour_integrable_lmul [OF cint, of "(w - z) ^ a" for a] apply (simp add: field_simps)
    apply (simp only: contour_integral_lmul cint algebra_simps)
    done
  have "(\<lambda>k. contour_integral (circlepath z r) (\<lambda>u. f u/(u - z)^(Suc k)) * (w - z)^k)
        sums contour_integral (circlepath z r) (\<lambda>u. f u/(u - w))"
    unfolding sums_def
    apply (rule Lim_transform_eventually [OF eq])
    apply (rule contour_integral_uniform_limit_circlepath [OF eventuallyI ul])
    apply (rule contour_integrable_sum, simp)
    apply (rule contour_integrable_lmul)
    apply (rule Cauchy_higher_derivative_integral_circlepath [OF contf holf])
    using \<open>0 < r\<close>
    apply auto
    done
  then have "(\<lambda>k. contour_integral (circlepath z r) (\<lambda>u. f u/(u - z)^(Suc k)) * (w - z)^k)
             sums (2 * of_real pi * \<i> * f w)"
    using w by (auto simp: dist_commute dist_norm contour_integral_unique [OF Cauchy_integral_circlepath_simple [OF holfc]])
  then have "(\<lambda>k. contour_integral (circlepath z r) (\<lambda>u. f u / (u - z) ^ Suc k) * (w - z)^k / (\<i> * (of_real pi * 2)))
            sums ((2 * of_real pi * \<i> * f w) / (\<i> * (complex_of_real pi * 2)))"
    by (rule sums_divide)
  then have "(\<lambda>n. (w - z) ^ n * contour_integral (circlepath z r) (\<lambda>u. f u / (u - z) ^ Suc n) / (\<i> * (of_real pi * 2)))
            sums f w"
    by (simp add: field_simps)
  then show ?thesis
    by (simp add: field_simps \<open>0 < r\<close> Cauchy_higher_derivative_integral_circlepath [OF contf holf])
qed


subsection\<open>The Liouville theorem and the Fundamental Theorem of Algebra.\<close>

text\<open> These weak Liouville versions don't even need the derivative formula.\<close>

lemma Liouville_weak_0:
  assumes holf: "f holomorphic_on UNIV" and inf: "(f \<longlongrightarrow> 0) at_infinity"
    shows "f z = 0"
proof (rule ccontr)
  assume fz: "f z \<noteq> 0"
  with inf [unfolded Lim_at_infinity, rule_format, of "norm(f z)/2"]
  obtain B where B: "\<And>x. B \<le> cmod x \<Longrightarrow> norm (f x) * 2 < cmod (f z)"
    by (auto simp: dist_norm)
  define R where "R = 1 + \<bar>B\<bar> + norm z"
  have "R > 0" unfolding R_def
  proof -
    have "0 \<le> cmod z + \<bar>B\<bar>"
      by (metis (full_types) add_nonneg_nonneg norm_ge_zero real_norm_def)
    then show "0 < 1 + \<bar>B\<bar> + cmod z"
      by linarith
  qed
  have *: "((\<lambda>u. f u / (u - z)) has_contour_integral 2 * complex_of_real pi * \<i> * f z) (circlepath z R)"
    apply (rule Cauchy_integral_circlepath)
    using \<open>R > 0\<close> apply (auto intro: holomorphic_on_subset [OF holf] holomorphic_on_imp_continuous_on)+
    done
  have "cmod (x - z) = R \<Longrightarrow> cmod (f x) * 2 \<le> cmod (f z)" for x
    apply (simp add: R_def)
    apply (rule less_imp_le)
    apply (rule B)
    using norm_triangle_ineq4 [of x z]
    apply (auto simp:)
    done
  with  \<open>R > 0\<close> fz show False
    using has_contour_integral_bound_circlepath [OF *, of "norm(f z)/2/R"]
    by (auto simp: norm_mult norm_divide divide_simps)
qed

proposition Liouville_weak:
  assumes "f holomorphic_on UNIV" and "(f \<longlongrightarrow> l) at_infinity"
    shows "f z = l"
  using Liouville_weak_0 [of "\<lambda>z. f z - l"]
  by (simp add: assms holomorphic_on_const holomorphic_on_diff LIM_zero)


proposition Liouville_weak_inverse:
  assumes "f holomorphic_on UNIV" and unbounded: "\<And>B. eventually (\<lambda>x. norm (f x) \<ge> B) at_infinity"
    obtains z where "f z = 0"
proof -
  { assume f: "\<And>z. f z \<noteq> 0"
    have 1: "(\<lambda>x. 1 / f x) holomorphic_on UNIV"
      by (simp add: holomorphic_on_divide holomorphic_on_const assms f)
    have 2: "((\<lambda>x. 1 / f x) \<longlongrightarrow> 0) at_infinity"
      apply (rule tendstoI [OF eventually_mono])
      apply (rule_tac B="2/e" in unbounded)
      apply (simp add: dist_norm norm_divide divide_simps mult_ac)
      done
    have False
      using Liouville_weak_0 [OF 1 2] f by simp
  }
  then show ?thesis
    using that by blast
qed


text\<open> In particular we get the Fundamental Theorem of Algebra.\<close>

theorem fundamental_theorem_of_algebra:
    fixes a :: "nat \<Rightarrow> complex"
  assumes "a 0 = 0 \<or> (\<exists>i \<in> {1..n}. a i \<noteq> 0)"
  obtains z where "(\<Sum>i\<le>n. a i * z^i) = 0"
using assms
proof (elim disjE bexE)
  assume "a 0 = 0" then show ?thesis
    by (auto simp: that [of 0])
next
  fix i
  assume i: "i \<in> {1..n}" and nz: "a i \<noteq> 0"
  have 1: "(\<lambda>z. \<Sum>i\<le>n. a i * z^i) holomorphic_on UNIV"
    by (rule holomorphic_intros)+
  show ?thesis
    apply (rule Liouville_weak_inverse [OF 1])
    apply (rule polyfun_extremal)
    apply (rule nz)
    using i that
    apply (auto simp:)
    done
qed


subsection\<open> Weierstrass convergence theorem.\<close>

proposition holomorphic_uniform_limit:
  assumes cont: "eventually (\<lambda>n. continuous_on (cball z r) (f n) \<and> (f n) holomorphic_on ball z r) F"
      and ulim: "uniform_limit (cball z r) f g F"
      and F:  "~ trivial_limit F"
  obtains "continuous_on (cball z r) g" "g holomorphic_on ball z r"
proof (cases r "0::real" rule: linorder_cases)
  case less then show ?thesis by (force simp add: ball_empty less_imp_le continuous_on_def holomorphic_on_def intro: that)
next
  case equal then show ?thesis
    by (force simp add: holomorphic_on_def continuous_on_sing intro: that)
next
  case greater
  have contg: "continuous_on (cball z r) g"
    using cont uniform_limit_theorem [OF eventually_mono ulim F]  by blast
  have 1: "continuous_on (path_image (circlepath z r)) (\<lambda>x. 1 / (2 * complex_of_real pi * \<i>) * g x)"
    apply (rule continuous_intros continuous_on_subset [OF contg])+
    using \<open>0 < r\<close> by auto
  have 2: "((\<lambda>u. 1 / (2 * of_real pi * \<i>) * g u / (u - w) ^ 1) has_contour_integral g w) (circlepath z r)"
       if w: "w \<in> ball z r" for w
  proof -
    define d where "d = (r - norm(w - z))"
    have "0 < d"  "d \<le> r" using w by (auto simp: norm_minus_commute d_def dist_norm)
    have dle: "\<And>u. cmod (z - u) = r \<Longrightarrow> d \<le> cmod (u - w)"
      unfolding d_def by (metis add_diff_eq diff_add_cancel norm_diff_ineq norm_minus_commute)
    have ev_int: "\<forall>\<^sub>F n in F. (\<lambda>u. f n u / (u - w)) contour_integrable_on circlepath z r"
      apply (rule eventually_mono [OF cont])
      using w
      apply (auto intro: Cauchy_higher_derivative_integral_circlepath [where k=0, simplified])
      done
    have ul_less: "uniform_limit (sphere z r) (\<lambda>n x. f n x / (x - w)) (\<lambda>x. g x / (x - w)) F"
      using greater \<open>0 < d\<close> 
      apply (clarsimp simp add: uniform_limit_iff dist_norm norm_divide diff_divide_distrib [symmetric] divide_simps)
      apply (rule_tac e1="e * d" in eventually_mono [OF uniform_limitD [OF ulim]])
       apply (force simp: dist_norm intro: dle mult_left_mono less_le_trans)+
      done
    have g_cint: "(\<lambda>u. g u/(u - w)) contour_integrable_on circlepath z r"
      by (rule contour_integral_uniform_limit_circlepath [OF ev_int ul_less F \<open>0 < r\<close>])
    have cif_tends_cig: "((\<lambda>n. contour_integral(circlepath z r) (\<lambda>u. f n u / (u - w))) \<longlongrightarrow> contour_integral(circlepath z r) (\<lambda>u. g u/(u - w))) F"
      by (rule contour_integral_uniform_limit_circlepath [OF ev_int ul_less F \<open>0 < r\<close>])
    have f_tends_cig: "((\<lambda>n. 2 * of_real pi * \<i> * f n w) \<longlongrightarrow> contour_integral (circlepath z r) (\<lambda>u. g u / (u - w))) F"
      apply (rule Lim_transform_eventually [where f = "\<lambda>n. contour_integral (circlepath z r) (\<lambda>u. f n u/(u - w))"])
      apply (rule eventually_mono [OF cont])
      apply (rule contour_integral_unique [OF Cauchy_integral_circlepath])
      using w
      apply (auto simp: norm_minus_commute dist_norm cif_tends_cig)
      done
    have "((\<lambda>n. 2 * of_real pi * \<i> * f n w) \<longlongrightarrow> 2 * of_real pi * \<i> * g w) F"
      apply (rule tendsto_mult_left [OF tendstoI])
      apply (rule eventually_mono [OF uniform_limitD [OF ulim]], assumption)
      using w
      apply (force simp add: dist_norm)
      done
    then have "((\<lambda>u. g u / (u - w)) has_contour_integral 2 * of_real pi * \<i> * g w) (circlepath z r)"
      using has_contour_integral_integral [OF g_cint] tendsto_unique [OF F f_tends_cig] w
      by (force simp add: dist_norm)
    then have "((\<lambda>u. g u / (2 * of_real pi * \<i> * (u - w))) has_contour_integral g w) (circlepath z r)"
      using has_contour_integral_div [where c = "2 * of_real pi * \<i>"]
      by (force simp add: field_simps)
    then show ?thesis
      by (simp add: dist_norm)
  qed
  show ?thesis
    using Cauchy_next_derivative_circlepath(2) [OF 1 2, simplified]
    by (fastforce simp add: holomorphic_on_open contg intro: that)
qed


text\<open> Version showing that the limit is the limit of the derivatives.\<close>

proposition has_complex_derivative_uniform_limit:
  fixes z::complex
  assumes cont: "eventually (\<lambda>n. continuous_on (cball z r) (f n) \<and>
                               (\<forall>w \<in> ball z r. ((f n) has_field_derivative (f' n w)) (at w))) F"
      and ulim: "uniform_limit (cball z r) f g F"
      and F:  "~ trivial_limit F" and "0 < r"
  obtains g' where
      "continuous_on (cball z r) g"
      "\<And>w. w \<in> ball z r \<Longrightarrow> (g has_field_derivative (g' w)) (at w) \<and> ((\<lambda>n. f' n w) \<longlongrightarrow> g' w) F"
proof -
  let ?conint = "contour_integral (circlepath z r)"
  have g: "continuous_on (cball z r) g" "g holomorphic_on ball z r"
    by (rule holomorphic_uniform_limit [OF eventually_mono [OF cont] ulim F];
             auto simp: holomorphic_on_open field_differentiable_def)+
  then obtain g' where g': "\<And>x. x \<in> ball z r \<Longrightarrow> (g has_field_derivative g' x) (at x)"
    using DERIV_deriv_iff_has_field_derivative
    by (fastforce simp add: holomorphic_on_open)
  then have derg: "\<And>x. x \<in> ball z r \<Longrightarrow> deriv g x = g' x"
    by (simp add: DERIV_imp_deriv)
  have tends_f'n_g': "((\<lambda>n. f' n w) \<longlongrightarrow> g' w) F" if w: "w \<in> ball z r" for w
  proof -
    have eq_f': "?conint (\<lambda>x. f n x / (x - w)\<^sup>2) - ?conint (\<lambda>x. g x / (x - w)\<^sup>2) = (f' n w - g' w) * (2 * of_real pi * \<i>)"
             if cont_fn: "continuous_on (cball z r) (f n)"
             and fnd: "\<And>w. w \<in> ball z r \<Longrightarrow> (f n has_field_derivative f' n w) (at w)" for n
    proof -
      have hol_fn: "f n holomorphic_on ball z r"
        using fnd by (force simp add: holomorphic_on_open)
      have "(f n has_field_derivative 1 / (2 * of_real pi * \<i>) * ?conint (\<lambda>u. f n u / (u - w)\<^sup>2)) (at w)"
        by (rule Cauchy_derivative_integral_circlepath [OF cont_fn hol_fn w])
      then have f': "f' n w = 1 / (2 * of_real pi * \<i>) * ?conint (\<lambda>u. f n u / (u - w)\<^sup>2)"
        using DERIV_unique [OF fnd] w by blast
      show ?thesis
        by (simp add: f' Cauchy_contour_integral_circlepath_2 [OF g w] derg [OF w] divide_simps)
    qed
    define d where "d = (r - norm(w - z))^2"
    have "d > 0"
      using w by (simp add: dist_commute dist_norm d_def)
    have dle: "\<And>y. r = cmod (z - y) \<Longrightarrow> d \<le> cmod ((y - w)\<^sup>2)"
      apply (simp add: d_def norm_power)
      apply (rule power_mono)
      apply (metis add_diff_eq diff_add_cancel norm_diff_ineq norm_minus_commute)
      apply (metis diff_ge_0_iff_ge dist_commute dist_norm less_eq_real_def mem_ball w)
      done
    have 1: "\<forall>\<^sub>F n in F. (\<lambda>x. f n x / (x - w)\<^sup>2) contour_integrable_on circlepath z r"
      by (force simp add: holomorphic_on_open intro: w Cauchy_derivative_integral_circlepath eventually_mono [OF cont])
    have 2: "uniform_limit (sphere z r) (\<lambda>n x. f n x / (x - w)\<^sup>2) (\<lambda>x. g x / (x - w)\<^sup>2) F"
      unfolding uniform_limit_iff
    proof clarify
      fix e::real
      assume "0 < e"
      with  \<open>r > 0\<close>
      show "\<forall>\<^sub>F n in F. \<forall>x\<in>sphere z r. dist (f n x / (x - w)\<^sup>2) (g x / (x - w)\<^sup>2) < e"
        apply (simp add: diff_divide_distrib [symmetric] norm_divide divide_simps sphere_def dist_norm)
        apply (rule eventually_mono [OF uniform_limitD [OF ulim], of "e*d"])
         apply (simp add: \<open>0 < d\<close>)
        apply (force simp add: dist_norm dle intro: less_le_trans)
        done
    qed
    have "((\<lambda>n. contour_integral (circlepath z r) (\<lambda>x. f n x / (x - w)\<^sup>2))
             \<longlongrightarrow> contour_integral (circlepath z r) ((\<lambda>x. g x / (x - w)\<^sup>2))) F"
      by (rule contour_integral_uniform_limit_circlepath [OF 1 2 F \<open>0 < r\<close>])
    then have tendsto_0: "((\<lambda>n. 1 / (2 * of_real pi * \<i>) * (?conint (\<lambda>x. f n x / (x - w)\<^sup>2) - ?conint (\<lambda>x. g x / (x - w)\<^sup>2))) \<longlongrightarrow> 0) F"
      using Lim_null by (force intro!: tendsto_mult_right_zero)
    have "((\<lambda>n. f' n w - g' w) \<longlongrightarrow> 0) F"
      apply (rule Lim_transform_eventually [OF _ tendsto_0])
      apply (force simp add: divide_simps intro: eq_f' eventually_mono [OF cont])
      done
    then show ?thesis using Lim_null by blast
  qed
  obtain g' where "\<And>w. w \<in> ball z r \<Longrightarrow> (g has_field_derivative (g' w)) (at w) \<and> ((\<lambda>n. f' n w) \<longlongrightarrow> g' w) F"
      by (blast intro: tends_f'n_g' g' )
  then show ?thesis using g
    using that by blast
qed


subsection\<open>Some more simple/convenient versions for applications.\<close>

lemma holomorphic_uniform_sequence:
  assumes S: "open S"
      and hol_fn: "\<And>n. (f n) holomorphic_on S"
      and ulim_g: "\<And>x. x \<in> S \<Longrightarrow> \<exists>d. 0 < d \<and> cball x d \<subseteq> S \<and> uniform_limit (cball x d) f g sequentially"
  shows "g holomorphic_on S"
proof -
  have "\<exists>f'. (g has_field_derivative f') (at z)" if "z \<in> S" for z
  proof -
    obtain r where "0 < r" and r: "cball z r \<subseteq> S"
               and ul: "uniform_limit (cball z r) f g sequentially"
      using ulim_g [OF \<open>z \<in> S\<close>] by blast 
    have *: "\<forall>\<^sub>F n in sequentially. continuous_on (cball z r) (f n) \<and> f n holomorphic_on ball z r"
      apply (intro eventuallyI conjI)
      using hol_fn holomorphic_on_imp_continuous_on holomorphic_on_subset r apply blast
      apply (metis hol_fn holomorphic_on_subset interior_cball interior_subset r)
      done
    show ?thesis
      apply (rule holomorphic_uniform_limit [OF *])
      using \<open>0 < r\<close> centre_in_ball ul
      apply (auto simp: holomorphic_on_open)
      done
  qed
  with S show ?thesis
    by (simp add: holomorphic_on_open)
qed

lemma has_complex_derivative_uniform_sequence:
  fixes S :: "complex set"
  assumes S: "open S"
      and hfd: "\<And>n x. x \<in> S \<Longrightarrow> ((f n) has_field_derivative f' n x) (at x)"
      and ulim_g: "\<And>x. x \<in> S
             \<Longrightarrow> \<exists>d. 0 < d \<and> cball x d \<subseteq> S \<and> uniform_limit (cball x d) f g sequentially"
  shows "\<exists>g'. \<forall>x \<in> S. (g has_field_derivative g' x) (at x) \<and> ((\<lambda>n. f' n x) \<longlongrightarrow> g' x) sequentially"
proof -
  have y: "\<exists>y. (g has_field_derivative y) (at z) \<and> (\<lambda>n. f' n z) \<longlonglongrightarrow> y" if "z \<in> S" for z
  proof -
    obtain r where "0 < r" and r: "cball z r \<subseteq> S"
               and ul: "uniform_limit (cball z r) f g sequentially"
      using ulim_g [OF \<open>z \<in> S\<close>] by blast 
    have *: "\<forall>\<^sub>F n in sequentially. continuous_on (cball z r) (f n) \<and>
                                   (\<forall>w \<in> ball z r. ((f n) has_field_derivative (f' n w)) (at w))"
      apply (intro eventuallyI conjI)
      apply (meson hfd holomorphic_on_imp_continuous_on holomorphic_on_open holomorphic_on_subset r S)
      using ball_subset_cball hfd r apply blast
      done
    show ?thesis
      apply (rule has_complex_derivative_uniform_limit [OF *, of g])
      using \<open>0 < r\<close> centre_in_ball ul
      apply force+
      done
  qed
  show ?thesis
    by (rule bchoice) (blast intro: y)
qed


subsection\<open>On analytic functions defined by a series.\<close>
 
lemma series_and_derivative_comparison:
  fixes S :: "complex set"
  assumes S: "open S"
      and h: "summable h"
      and hfd: "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
      and to_g: "\<forall>\<^sub>F n in sequentially. \<forall>x\<in>S. norm (f n x) \<le> h n"
  obtains g g' where "\<forall>x \<in> S. ((\<lambda>n. f n x) sums g x) \<and> ((\<lambda>n. f' n x) sums g' x) \<and> (g has_field_derivative g' x) (at x)"
proof -
  obtain g where g: "uniform_limit S (\<lambda>n x. \<Sum>i<n. f i x) g sequentially"
    using weierstrass_m_test_ev [OF to_g h]  by force
  have *: "\<exists>d>0. cball x d \<subseteq> S \<and> uniform_limit (cball x d) (\<lambda>n x. \<Sum>i<n. f i x) g sequentially"
         if "x \<in> S" for x
  proof -
    obtain d where "d>0" and d: "cball x d \<subseteq> S"
      using open_contains_cball [of "S"] \<open>x \<in> S\<close> S by blast
    then show ?thesis
      apply (rule_tac x=d in exI)
        using g uniform_limit_on_subset
        apply (force simp: dist_norm eventually_sequentially)
          done
  qed
  have "\<And>x. x \<in> S \<Longrightarrow> (\<lambda>n. \<Sum>i<n. f i x) \<longlonglongrightarrow> g x"
    by (metis tendsto_uniform_limitI [OF g])
  moreover have "\<exists>g'. \<forall>x\<in>S. (g has_field_derivative g' x) (at x) \<and> (\<lambda>n. \<Sum>i<n. f' i x) \<longlonglongrightarrow> g' x"
    by (rule has_complex_derivative_uniform_sequence [OF S]) (auto intro: * hfd DERIV_sum)+
  ultimately show ?thesis
    by (metis sums_def that)
qed

text\<open>A version where we only have local uniform/comparative convergence.\<close>

lemma series_and_derivative_comparison_local:
  fixes S :: "complex set"
  assumes S: "open S"
      and hfd: "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
      and to_g: "\<And>x. x \<in> S \<Longrightarrow> \<exists>d h. 0 < d \<and> summable h \<and> (\<forall>\<^sub>F n in sequentially. \<forall>y\<in>ball x d \<inter> S. norm (f n y) \<le> h n)"
  shows "\<exists>g g'. \<forall>x \<in> S. ((\<lambda>n. f n x) sums g x) \<and> ((\<lambda>n. f' n x) sums g' x) \<and> (g has_field_derivative g' x) (at x)"
proof -
  have "\<exists>y. (\<lambda>n. f n z) sums (\<Sum>n. f n z) \<and> (\<lambda>n. f' n z) sums y \<and> ((\<lambda>x. \<Sum>n. f n x) has_field_derivative y) (at z)"
       if "z \<in> S" for z
  proof -
    obtain d h where "0 < d" "summable h" and le_h: "\<forall>\<^sub>F n in sequentially. \<forall>y\<in>ball z d \<inter> S. norm (f n y) \<le> h n"
      using to_g \<open>z \<in> S\<close> by meson
    then obtain r where "r>0" and r: "ball z r \<subseteq> ball z d \<inter> S" using \<open>z \<in> S\<close> S
      by (metis Int_iff open_ball centre_in_ball open_Int open_contains_ball_eq)
    have 1: "open (ball z d \<inter> S)"
      by (simp add: open_Int S)
    have 2: "\<And>n x. x \<in> ball z d \<inter> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
      by (auto simp: hfd)
    obtain g g' where gg': "\<forall>x \<in> ball z d \<inter> S. ((\<lambda>n. f n x) sums g x) \<and>
                                    ((\<lambda>n. f' n x) sums g' x) \<and> (g has_field_derivative g' x) (at x)"
      by (auto intro: le_h series_and_derivative_comparison [OF 1 \<open>summable h\<close> hfd])
    then have "(\<lambda>n. f' n z) sums g' z"
      by (meson \<open>0 < r\<close> centre_in_ball contra_subsetD r)
    moreover have "(\<lambda>n. f n z) sums (\<Sum>n. f n z)"
      using  summable_sums centre_in_ball \<open>0 < d\<close> \<open>summable h\<close> le_h
      by (metis (full_types) Int_iff gg' summable_def that)
    moreover have "((\<lambda>x. \<Sum>n. f n x) has_field_derivative g' z) (at z)"
      apply (rule_tac f=g in DERIV_transform_at [OF _ \<open>0 < r\<close>])
      apply (simp add: gg' \<open>z \<in> S\<close> \<open>0 < d\<close>)
      apply (metis (full_types) contra_subsetD dist_commute gg' mem_ball r sums_unique)
      done
    ultimately show ?thesis by auto
  qed
  then show ?thesis
    by (rule_tac x="\<lambda>x. suminf  (\<lambda>n. f n x)" in exI) meson
qed


text\<open>Sometimes convenient to compare with a complex series of positive reals. (?)\<close>

lemma series_and_derivative_comparison_complex:
  fixes S :: "complex set"
  assumes S: "open S"
      and hfd: "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative f' n x) (at x)"
      and to_g: "\<And>x. x \<in> S \<Longrightarrow> \<exists>d h. 0 < d \<and> summable h \<and> range h \<subseteq> \<real>\<^sub>\<ge>\<^sub>0 \<and> (\<forall>\<^sub>F n in sequentially. \<forall>y\<in>ball x d \<inter> S. cmod(f n y) \<le> cmod (h n))"
  shows "\<exists>g g'. \<forall>x \<in> S. ((\<lambda>n. f n x) sums g x) \<and> ((\<lambda>n. f' n x) sums g' x) \<and> (g has_field_derivative g' x) (at x)"
apply (rule series_and_derivative_comparison_local [OF S hfd], assumption)
apply (rule ex_forward [OF to_g], assumption)
apply (erule exE)
apply (rule_tac x="Re o h" in exI)
apply (force simp add: summable_Re o_def nonneg_Reals_cmod_eq_Re image_subset_iff)
done

text\<open>Sometimes convenient to compare with a complex series of positive reals. (?)\<close>
lemma series_differentiable_comparison_complex:
  fixes S :: "complex set"
  assumes S: "open S"
    and hfd: "\<And>n x. x \<in> S \<Longrightarrow> f n field_differentiable (at x)"
    and to_g: "\<And>x. x \<in> S \<Longrightarrow> \<exists>d h. 0 < d \<and> summable h \<and> range h \<subseteq> \<real>\<^sub>\<ge>\<^sub>0 \<and> (\<forall>\<^sub>F n in sequentially. \<forall>y\<in>ball x d \<inter> S. cmod(f n y) \<le> cmod (h n))"
  obtains g where "\<forall>x \<in> S. ((\<lambda>n. f n x) sums g x) \<and> g field_differentiable (at x)"
proof -
  have hfd': "\<And>n x. x \<in> S \<Longrightarrow> (f n has_field_derivative deriv (f n) x) (at x)"
    using hfd field_differentiable_derivI by blast
  have "\<exists>g g'. \<forall>x \<in> S. ((\<lambda>n. f n x) sums g x) \<and> ((\<lambda>n. deriv (f n) x) sums g' x) \<and> (g has_field_derivative g' x) (at x)"
    by (metis series_and_derivative_comparison_complex [OF S hfd' to_g])
  then show ?thesis
    using field_differentiable_def that by blast
qed

text\<open>In particular, a power series is analytic inside circle of convergence.\<close>

lemma power_series_and_derivative_0:
  fixes a :: "nat \<Rightarrow> complex" and r::real
  assumes "summable (\<lambda>n. a n * r^n)"
    shows "\<exists>g g'. \<forall>z. cmod z < r \<longrightarrow>
             ((\<lambda>n. a n * z^n) sums g z) \<and> ((\<lambda>n. of_nat n * a n * z^(n - 1)) sums g' z) \<and> (g has_field_derivative g' z) (at z)"
proof (cases "0 < r")
  case True
    have der: "\<And>n z. ((\<lambda>x. a n * x ^ n) has_field_derivative of_nat n * a n * z ^ (n - 1)) (at z)"
      by (rule derivative_eq_intros | simp)+
    have y_le: "\<lbrakk>cmod (z - y) * 2 < r - cmod z\<rbrakk> \<Longrightarrow> cmod y \<le> cmod (of_real r + of_real (cmod z)) / 2" for z y
      using \<open>r > 0\<close>
      apply (auto simp: algebra_simps norm_mult norm_divide norm_power of_real_add [symmetric] simp del: of_real_add)
      using norm_triangle_ineq2 [of y z]
      apply (simp only: diff_le_eq norm_minus_commute mult_2)
      done
    have "summable (\<lambda>n. a n * complex_of_real r ^ n)"
      using assms \<open>r > 0\<close> by simp
    moreover have "\<And>z. cmod z < r \<Longrightarrow> cmod ((of_real r + of_real (cmod z)) / 2) < cmod (of_real r)"
      using \<open>r > 0\<close>
      by (simp add: of_real_add [symmetric] del: of_real_add)
    ultimately have sum: "\<And>z. cmod z < r \<Longrightarrow> summable (\<lambda>n. of_real (cmod (a n)) * ((of_real r + complex_of_real (cmod z)) / 2) ^ n)"
      by (rule power_series_conv_imp_absconv_weak)
    have "\<exists>g g'. \<forall>z \<in> ball 0 r. (\<lambda>n.  (a n) * z ^ n) sums g z \<and>
               (\<lambda>n. of_nat n * (a n) * z ^ (n - 1)) sums g' z \<and> (g has_field_derivative g' z) (at z)"
      apply (rule series_and_derivative_comparison_complex [OF open_ball der])
      apply (rule_tac x="(r - norm z)/2" in exI)
      apply (simp add: dist_norm)
      apply (rule_tac x="\<lambda>n. of_real(norm(a n)*((r + norm z)/2)^n)" in exI)
      using \<open>r > 0\<close>
      apply (auto simp: sum eventually_sequentially norm_mult norm_divide norm_power)
      apply (rule_tac x=0 in exI)
      apply (force simp: dist_norm intro!: mult_left_mono power_mono y_le)
      done
  then show ?thesis
    by (simp add: ball_def)
next
  case False then show ?thesis
    apply (simp add: not_less)
    using less_le_trans norm_not_less_zero by blast
qed

proposition power_series_and_derivative:
  fixes a :: "nat \<Rightarrow> complex" and r::real
  assumes "summable (\<lambda>n. a n * r^n)"
    obtains g g' where "\<forall>z \<in> ball w r.
             ((\<lambda>n. a n * (z - w) ^ n) sums g z) \<and> ((\<lambda>n. of_nat n * a n * (z - w) ^ (n - 1)) sums g' z) \<and>
              (g has_field_derivative g' z) (at z)"
  using power_series_and_derivative_0 [OF assms]
  apply clarify
  apply (rule_tac g="(\<lambda>z. g(z - w))" in that)
  using DERIV_shift [where z="-w"]
  apply (auto simp: norm_minus_commute Ball_def dist_norm)
  done

proposition power_series_holomorphic:
  assumes "\<And>w. w \<in> ball z r \<Longrightarrow> ((\<lambda>n. a n*(w - z)^n) sums f w)"
    shows "f holomorphic_on ball z r"
proof -
  have "\<exists>f'. (f has_field_derivative f') (at w)" if w: "dist z w < r" for w
  proof -
    have inb: "z + complex_of_real ((dist z w + r) / 2) \<in> ball z r"
    proof -
      have wz: "cmod (w - z) < r" using w
        by (auto simp: divide_simps dist_norm norm_minus_commute)
      then have "0 \<le> r"
        by (meson less_eq_real_def norm_ge_zero order_trans)
      show ?thesis
        using w by (simp add: dist_norm \<open>0\<le>r\<close> of_real_add [symmetric] del: of_real_add)
    qed
    have sum: "summable (\<lambda>n. a n * of_real (((cmod (z - w) + r) / 2) ^ n))"
      using assms [OF inb] by (force simp add: summable_def dist_norm)
    obtain g g' where gg': "\<And>u. u \<in> ball z ((cmod (z - w) + r) / 2) \<Longrightarrow>
                               (\<lambda>n. a n * (u - z) ^ n) sums g u \<and>
                               (\<lambda>n. of_nat n * a n * (u - z) ^ (n - 1)) sums g' u \<and> (g has_field_derivative g' u) (at u)"
      by (rule power_series_and_derivative [OF sum, of z]) fastforce
    have [simp]: "g u = f u" if "cmod (u - w) < (r - cmod (z - w)) / 2" for u
    proof -
      have less: "cmod (z - u) * 2 < cmod (z - w) + r"
        using that dist_triangle2 [of z u w]
        by (simp add: dist_norm [symmetric] algebra_simps)
      show ?thesis
        apply (rule sums_unique2 [of "\<lambda>n. a n*(u - z)^n"])
        using gg' [of u] less w
        apply (auto simp: assms dist_norm)
        done
    qed
    show ?thesis
      apply (rule_tac x="g' w" in exI)
      apply (rule DERIV_transform_at [where f=g and d="(r - norm(z - w))/2"])
      using w gg' [of w]
      apply (auto simp: dist_norm)
      done
  qed
  then show ?thesis by (simp add: holomorphic_on_open)
qed

corollary holomorphic_iff_power_series:
     "f holomorphic_on ball z r \<longleftrightarrow>
      (\<forall>w \<in> ball z r. (\<lambda>n. (deriv ^^ n) f z / (fact n) * (w - z)^n) sums f w)"
  apply (intro iffI ballI)
   using holomorphic_power_series  apply force
  apply (rule power_series_holomorphic [where a = "\<lambda>n. (deriv ^^ n) f z / (fact n)"])
  apply force
  done

corollary power_series_analytic:
     "(\<And>w. w \<in> ball z r \<Longrightarrow> (\<lambda>n. a n*(w - z)^n) sums f w) \<Longrightarrow> f analytic_on ball z r"
  by (force simp add: analytic_on_open intro!: power_series_holomorphic)

corollary analytic_iff_power_series:
     "f analytic_on ball z r \<longleftrightarrow>
      (\<forall>w \<in> ball z r. (\<lambda>n. (deriv ^^ n) f z / (fact n) * (w - z)^n) sums f w)"
  by (simp add: analytic_on_open holomorphic_iff_power_series)


subsection\<open>Equality between holomorphic functions, on open ball then connected set.\<close>

lemma holomorphic_fun_eq_on_ball:
   "\<lbrakk>f holomorphic_on ball z r; g holomorphic_on ball z r;
     w \<in> ball z r;
     \<And>n. (deriv ^^ n) f z = (deriv ^^ n) g z\<rbrakk>
     \<Longrightarrow> f w = g w"
  apply (rule sums_unique2 [of "\<lambda>n. (deriv ^^ n) f z / (fact n) * (w - z)^n"])
  apply (auto simp: holomorphic_iff_power_series)
  done

lemma holomorphic_fun_eq_0_on_ball:
   "\<lbrakk>f holomorphic_on ball z r;  w \<in> ball z r;
     \<And>n. (deriv ^^ n) f z = 0\<rbrakk>
     \<Longrightarrow> f w = 0"
  apply (rule sums_unique2 [of "\<lambda>n. (deriv ^^ n) f z / (fact n) * (w - z)^n"])
  apply (auto simp: holomorphic_iff_power_series)
  done

lemma holomorphic_fun_eq_0_on_connected:
  assumes holf: "f holomorphic_on s" and "open s"
      and cons: "connected s"
      and der: "\<And>n. (deriv ^^ n) f z = 0"
      and "z \<in> s" "w \<in> s"
    shows "f w = 0"
proof -
  have *: "\<And>x e. \<lbrakk> \<forall>xa. (deriv ^^ xa) f x = 0;  ball x e \<subseteq> s\<rbrakk>
           \<Longrightarrow> ball x e \<subseteq> (\<Inter>n. {w \<in> s. (deriv ^^ n) f w = 0})"
    apply auto
    apply (rule holomorphic_fun_eq_0_on_ball [OF holomorphic_higher_deriv])
    apply (rule holomorphic_on_subset [OF holf], simp_all)
    by (metis funpow_add o_apply)
  have 1: "openin (subtopology euclidean s) (\<Inter>n. {w \<in> s. (deriv ^^ n) f w = 0})"
    apply (rule open_subset, force)
    using \<open>open s\<close>
    apply (simp add: open_contains_ball Ball_def)
    apply (erule all_forward)
    using "*" by auto blast+
  have 2: "closedin (subtopology euclidean s) (\<Inter>n. {w \<in> s. (deriv ^^ n) f w = 0})"
    using assms
    by (auto intro: continuous_closedin_preimage_constant holomorphic_on_imp_continuous_on holomorphic_higher_deriv)
  obtain e where "e>0" and e: "ball w e \<subseteq> s" using openE [OF \<open>open s\<close> \<open>w \<in> s\<close>] .
  then have holfb: "f holomorphic_on ball w e"
    using holf holomorphic_on_subset by blast
  have 3: "(\<Inter>n. {w \<in> s. (deriv ^^ n) f w = 0}) = s \<Longrightarrow> f w = 0"
    using \<open>e>0\<close> e by (force intro: holomorphic_fun_eq_0_on_ball [OF holfb])
  show ?thesis
    using cons der \<open>z \<in> s\<close>
    apply (simp add: connected_clopen)
    apply (drule_tac x="\<Inter>n. {w \<in> s. (deriv ^^ n) f w = 0}" in spec)
    apply (auto simp: 1 2 3)
    done
qed

lemma holomorphic_fun_eq_on_connected:
  assumes "f holomorphic_on s" "g holomorphic_on s" and "open s"  "connected s"
      and "\<And>n. (deriv ^^ n) f z = (deriv ^^ n) g z"
      and "z \<in> s" "w \<in> s"
    shows "f w = g w"
  apply (rule holomorphic_fun_eq_0_on_connected [of "\<lambda>x. f x - g x" s z, simplified])
  apply (intro assms holomorphic_intros)
  using assms apply simp_all
  apply (subst higher_deriv_diff, auto)
  done

lemma holomorphic_fun_eq_const_on_connected:
  assumes holf: "f holomorphic_on s" and "open s"
      and cons: "connected s"
      and der: "\<And>n. 0 < n \<Longrightarrow> (deriv ^^ n) f z = 0"
      and "z \<in> s" "w \<in> s"
    shows "f w = f z"
  apply (rule holomorphic_fun_eq_0_on_connected [of "\<lambda>w. f w - f z" s z, simplified])
  apply (intro assms holomorphic_intros)
  using assms apply simp_all
  apply (subst higher_deriv_diff)
  apply (intro holomorphic_intros | simp)+
  done


subsection\<open>Some basic lemmas about poles/singularities.\<close>

lemma pole_lemma:
  assumes holf: "f holomorphic_on s" and a: "a \<in> interior s"
    shows "(\<lambda>z. if z = a then deriv f a
                 else (f z - f a) / (z - a)) holomorphic_on s" (is "?F holomorphic_on s")
proof -
  have F1: "?F field_differentiable (at u within s)" if "u \<in> s" "u \<noteq> a" for u
  proof -
    have fcd: "f field_differentiable at u within s"
      using holf holomorphic_on_def by (simp add: \<open>u \<in> s\<close>)
    have cd: "(\<lambda>z. (f z - f a) / (z - a)) field_differentiable at u within s"
      by (rule fcd derivative_intros | simp add: that)+
    have "0 < dist a u" using that dist_nz by blast
    then show ?thesis
      by (rule field_differentiable_transform_within [OF _ _ _ cd]) (auto simp: \<open>u \<in> s\<close>)
  qed
  have F2: "?F field_differentiable at a" if "0 < e" "ball a e \<subseteq> s" for e
  proof -
    have holfb: "f holomorphic_on ball a e"
      by (rule holomorphic_on_subset [OF holf \<open>ball a e \<subseteq> s\<close>])
    have 2: "?F holomorphic_on ball a e - {a}"
      apply (rule holomorphic_on_subset [where s = "s - {a}"])
      apply (simp add: holomorphic_on_def field_differentiable_def [symmetric])
      using mem_ball that
      apply (auto intro: F1 field_differentiable_within_subset)
      done
    have "isCont (\<lambda>z. if z = a then deriv f a else (f z - f a) / (z - a)) x"
            if "dist a x < e" for x
    proof (cases "x=a")
      case True then show ?thesis
      using holfb \<open>0 < e\<close>
      apply (simp add: holomorphic_on_open field_differentiable_def [symmetric])
      apply (drule_tac x=a in bspec)
      apply (auto simp: DERIV_deriv_iff_field_differentiable [symmetric] continuous_at DERIV_iff2
                elim: rev_iffD1 [OF _ LIM_equal])
      done
    next
      case False with 2 that show ?thesis
        by (force simp: holomorphic_on_open open_Diff field_differentiable_def [symmetric] field_differentiable_imp_continuous_at)
    qed
    then have 1: "continuous_on (ball a e) ?F"
      by (clarsimp simp:  continuous_on_eq_continuous_at)
    have "?F holomorphic_on ball a e"
      by (auto intro: no_isolated_singularity [OF 1 2])
    with that show ?thesis
      by (simp add: holomorphic_on_open field_differentiable_def [symmetric]
                    field_differentiable_at_within)
  qed
  show ?thesis
  proof
    fix x assume "x \<in> s" show "?F field_differentiable at x within s"
    proof (cases "x=a")
      case True then show ?thesis
      using a by (auto simp: mem_interior intro: field_differentiable_at_within F2)
    next
      case False with F1 \<open>x \<in> s\<close>
      show ?thesis by blast
    qed
  qed
qed

proposition pole_theorem:
  assumes holg: "g holomorphic_on s" and a: "a \<in> interior s"
      and eq: "\<And>z. z \<in> s - {a} \<Longrightarrow> g z = (z - a) * f z"
    shows "(\<lambda>z. if z = a then deriv g a
                 else f z - g a/(z - a)) holomorphic_on s"
  using pole_lemma [OF holg a]
  by (rule holomorphic_transform) (simp add: eq divide_simps)

lemma pole_lemma_open:
  assumes "f holomorphic_on s" "open s"
    shows "(\<lambda>z. if z = a then deriv f a else (f z - f a)/(z - a)) holomorphic_on s"
proof (cases "a \<in> s")
  case True with assms interior_eq pole_lemma
    show ?thesis by fastforce
next
  case False with assms show ?thesis
    apply (simp add: holomorphic_on_def field_differentiable_def [symmetric], clarify)
    apply (rule field_differentiable_transform_within [where f = "\<lambda>z. (f z - f a)/(z - a)" and d = 1])
    apply (rule derivative_intros | force)+
    done
qed

proposition pole_theorem_open:
  assumes holg: "g holomorphic_on s" and s: "open s"
      and eq: "\<And>z. z \<in> s - {a} \<Longrightarrow> g z = (z - a) * f z"
    shows "(\<lambda>z. if z = a then deriv g a
                 else f z - g a/(z - a)) holomorphic_on s"
  using pole_lemma_open [OF holg s]
  by (rule holomorphic_transform) (auto simp: eq divide_simps)

proposition pole_theorem_0:
  assumes holg: "g holomorphic_on s" and a: "a \<in> interior s"
      and eq: "\<And>z. z \<in> s - {a} \<Longrightarrow> g z = (z - a) * f z"
      and [simp]: "f a = deriv g a" "g a = 0"
    shows "f holomorphic_on s"
  using pole_theorem [OF holg a eq]
  by (rule holomorphic_transform) (auto simp: eq divide_simps)

proposition pole_theorem_open_0:
  assumes holg: "g holomorphic_on s" and s: "open s"
      and eq: "\<And>z. z \<in> s - {a} \<Longrightarrow> g z = (z - a) * f z"
      and [simp]: "f a = deriv g a" "g a = 0"
    shows "f holomorphic_on s"
  using pole_theorem_open [OF holg s eq]
  by (rule holomorphic_transform) (auto simp: eq divide_simps)

lemma pole_theorem_analytic:
  assumes g: "g analytic_on s"
      and eq: "\<And>z. z \<in> s
             \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>w \<in> ball z d - {a}. g w = (w - a) * f w)"
    shows "(\<lambda>z. if z = a then deriv g a
                 else f z - g a/(z - a)) analytic_on s"
using g
apply (simp add: analytic_on_def Ball_def)
apply (safe elim!: all_forward dest!: eq)
apply (rule_tac x="min d e" in exI, simp)
apply (rule pole_theorem_open)
apply (auto simp: holomorphic_on_subset subset_ball)
done

lemma pole_theorem_analytic_0:
  assumes g: "g analytic_on s"
      and eq: "\<And>z. z \<in> s \<Longrightarrow> \<exists>d. 0 < d \<and> (\<forall>w \<in> ball z d - {a}. g w = (w - a) * f w)"
      and [simp]: "f a = deriv g a" "g a = 0"
    shows "f analytic_on s"
proof -
  have [simp]: "(\<lambda>z. if z = a then deriv g a else f z - g a / (z - a)) = f"
    by auto
  show ?thesis
    using pole_theorem_analytic [OF g eq] by simp
qed

lemma pole_theorem_analytic_open_superset:
  assumes g: "g analytic_on s" and "s \<subseteq> t" "open t"
      and eq: "\<And>z. z \<in> t - {a} \<Longrightarrow> g z = (z - a) * f z"
    shows "(\<lambda>z. if z = a then deriv g a
                 else f z - g a/(z - a)) analytic_on s"
  apply (rule pole_theorem_analytic [OF g])
  apply (rule openE [OF \<open>open t\<close>])
  using assms eq by auto

lemma pole_theorem_analytic_open_superset_0:
  assumes g: "g analytic_on s" "s \<subseteq> t" "open t" "\<And>z. z \<in> t - {a} \<Longrightarrow> g z = (z - a) * f z"
      and [simp]: "f a = deriv g a" "g a = 0"
    shows "f analytic_on s"
proof -
  have [simp]: "(\<lambda>z. if z = a then deriv g a else f z - g a / (z - a)) = f"
    by auto
  have "(\<lambda>z. if z = a then deriv g a else f z - g a/(z - a)) analytic_on s"
    by (rule pole_theorem_analytic_open_superset [OF g])
  then show ?thesis by simp
qed


subsection\<open>General, homology form of Cauchy's theorem.\<close>

text\<open>Proof is based on Dixon's, as presented in Lang's "Complex Analysis" book (page 147).\<close>

lemma contour_integral_continuous_on_linepath_2D:
  assumes "open u" and cont_dw: "\<And>w. w \<in> u \<Longrightarrow> F w contour_integrable_on (linepath a b)"
      and cond_uu: "continuous_on (u \<times> u) (\<lambda>(x,y). F x y)"
      and abu: "closed_segment a b \<subseteq> u"
    shows "continuous_on u (\<lambda>w. contour_integral (linepath a b) (F w))"
proof -
  have *: "\<exists>d>0. \<forall>x'\<in>u. dist x' w < d \<longrightarrow>
                         dist (contour_integral (linepath a b) (F x'))
                              (contour_integral (linepath a b) (F w)) \<le> \<epsilon>"
          if "w \<in> u" "0 < \<epsilon>" "a \<noteq> b" for w \<epsilon>
  proof -
    obtain \<delta> where "\<delta>>0" and \<delta>: "cball w \<delta> \<subseteq> u" using open_contains_cball \<open>open u\<close> \<open>w \<in> u\<close> by force
    let ?TZ = "{(t,z) |t z. t \<in> cball w \<delta> \<and> z \<in> closed_segment a b}"
    have "uniformly_continuous_on ?TZ (\<lambda>(x,y). F x y)"
      apply (rule compact_uniformly_continuous)
      apply (rule continuous_on_subset[OF cond_uu])
      using abu \<delta>
      apply (auto simp: compact_Times simp del: mem_cball)
      done
    then obtain \<eta> where "\<eta>>0"
        and \<eta>: "\<And>x x'. \<lbrakk>x\<in>?TZ; x'\<in>?TZ; dist x' x < \<eta>\<rbrakk> \<Longrightarrow>
                         dist ((\<lambda>(x,y). F x y) x') ((\<lambda>(x,y). F x y) x) < \<epsilon>/norm(b - a)"
      apply (rule uniformly_continuous_onE [where e = "\<epsilon>/norm(b - a)"])
      using \<open>0 < \<epsilon>\<close> \<open>a \<noteq> b\<close> by auto
    have \<eta>: "\<lbrakk>norm (w - x1) \<le> \<delta>;   x2 \<in> closed_segment a b;
              norm (w - x1') \<le> \<delta>;  x2' \<in> closed_segment a b; norm ((x1', x2') - (x1, x2)) < \<eta>\<rbrakk>
              \<Longrightarrow> norm (F x1' x2' - F x1 x2) \<le> \<epsilon> / cmod (b - a)"
             for x1 x2 x1' x2'
      using \<eta> [of "(x1,x2)" "(x1',x2')"] by (force simp add: dist_norm)
    have le_ee: "cmod (contour_integral (linepath a b) (\<lambda>x. F x' x - F w x)) \<le> \<epsilon>"
                if "x' \<in> u" "cmod (x' - w) < \<delta>" "cmod (x' - w) < \<eta>"  for x'
    proof -
      have "cmod (contour_integral (linepath a b) (\<lambda>x. F x' x - F w x)) \<le> \<epsilon>/norm(b - a) * norm(b - a)"
        apply (rule has_contour_integral_bound_linepath [OF has_contour_integral_integral _ \<eta>])
        apply (rule contour_integrable_diff [OF cont_dw cont_dw])
        using \<open>0 < \<epsilon>\<close> \<open>a \<noteq> b\<close> \<open>0 < \<delta>\<close> \<open>w \<in> u\<close> that
        apply (auto simp: norm_minus_commute)
        done
      also have "... = \<epsilon>" using \<open>a \<noteq> b\<close> by simp
      finally show ?thesis .
    qed
    show ?thesis
      apply (rule_tac x="min \<delta> \<eta>" in exI)
      using \<open>0 < \<delta>\<close> \<open>0 < \<eta>\<close>
      apply (auto simp: dist_norm contour_integral_diff [OF cont_dw cont_dw, symmetric] \<open>w \<in> u\<close> intro: le_ee)
      done
  qed
  show ?thesis
    apply (rule continuous_onI)
    apply (cases "a=b")
    apply (auto intro: *)
    done
qed

text\<open>This version has @{term"polynomial_function \<gamma>"} as an additional assumption.\<close>
lemma Cauchy_integral_formula_global_weak:
    assumes u: "open u" and holf: "f holomorphic_on u"
        and z: "z \<in> u" and \<gamma>: "polynomial_function \<gamma>"
        and pasz: "path_image \<gamma> \<subseteq> u - {z}" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
        and zero: "\<And>w. w \<notin> u \<Longrightarrow> winding_number \<gamma> w = 0"
      shows "((\<lambda>w. f w / (w - z)) has_contour_integral (2*pi * \<i> * winding_number \<gamma> z * f z)) \<gamma>"
proof -
  obtain \<gamma>' where pf\<gamma>': "polynomial_function \<gamma>'" and \<gamma>': "\<And>x. (\<gamma> has_vector_derivative (\<gamma>' x)) (at x)"
    using has_vector_derivative_polynomial_function [OF \<gamma>] by blast
  then have "bounded(path_image \<gamma>')"
    by (simp add: path_image_def compact_imp_bounded compact_continuous_image continuous_on_polymonial_function)
  then obtain B where "B>0" and B: "\<And>x. x \<in> path_image \<gamma>' \<Longrightarrow> norm x \<le> B"
    using bounded_pos by force
  define d where [abs_def]: "d z w = (if w = z then deriv f z else (f w - f z)/(w - z))" for z w
  define v where "v = {w. w \<notin> path_image \<gamma> \<and> winding_number \<gamma> w = 0}"
  have "path \<gamma>" "valid_path \<gamma>" using \<gamma>
    by (auto simp: path_polynomial_function valid_path_polynomial_function)
  then have ov: "open v"
    by (simp add: v_def open_winding_number_levelsets loop)
  have uv_Un: "u \<union> v = UNIV"
    using pasz zero by (auto simp: v_def)
  have conf: "continuous_on u f"
    by (metis holf holomorphic_on_imp_continuous_on)
  have hol_d: "(d y) holomorphic_on u" if "y \<in> u" for y
  proof -
    have *: "(\<lambda>c. if c = y then deriv f y else (f c - f y) / (c - y)) holomorphic_on u"
      by (simp add: holf pole_lemma_open u)
    then have "isCont (\<lambda>x. if x = y then deriv f y else (f x - f y) / (x - y)) y"
      using at_within_open field_differentiable_imp_continuous_at holomorphic_on_def that u by fastforce
    then have "continuous_on u (d y)"
      apply (simp add: d_def continuous_on_eq_continuous_at u, clarify)
      using * holomorphic_on_def
      by (meson field_differentiable_within_open field_differentiable_imp_continuous_at u)
    moreover have "d y holomorphic_on u - {y}"
      apply (simp add: d_def holomorphic_on_open u open_delete field_differentiable_def [symmetric])
      apply (intro ballI)
      apply (rename_tac w)
      apply (rule_tac d="dist w y" and f = "\<lambda>w. (f w - f y)/(w - y)" in field_differentiable_transform_within)
      apply (auto simp: dist_pos_lt dist_commute intro!: derivative_intros)
      using analytic_on_imp_differentiable_at analytic_on_open holf u apply blast
      done
    ultimately show ?thesis
      by (rule no_isolated_singularity) (auto simp: u)
  qed
  have cint_fxy: "(\<lambda>x. (f x - f y) / (x - y)) contour_integrable_on \<gamma>" if "y \<notin> path_image \<gamma>" for y
    apply (rule contour_integrable_holomorphic_simple [where s = "u-{y}"])
    using \<open>valid_path \<gamma>\<close> pasz
    apply (auto simp: u open_delete)
    apply (rule continuous_intros holomorphic_intros continuous_on_subset [OF conf] holomorphic_on_subset [OF holf] |
                force simp add: that)+
    done
  define h where
    "h z = (if z \<in> u then contour_integral \<gamma> (d z) else contour_integral \<gamma> (\<lambda>w. f w/(w - z)))" for z
  have U: "\<And>z. z \<in> u \<Longrightarrow> ((d z) has_contour_integral h z) \<gamma>"
    apply (simp add: h_def)
    apply (rule has_contour_integral_integral [OF contour_integrable_holomorphic_simple [where s=u]])
    using u pasz \<open>valid_path \<gamma>\<close>
    apply (auto intro: holomorphic_on_imp_continuous_on hol_d)
    done
  have V: "((\<lambda>w. f w / (w - z)) has_contour_integral h z) \<gamma>" if z: "z \<in> v" for z
  proof -
    have 0: "0 = (f z) * 2 * of_real (2 * pi) * \<i> * winding_number \<gamma> z"
      using v_def z by auto
    then have "((\<lambda>x. 1 / (x - z)) has_contour_integral 0) \<gamma>"
     using z v_def  has_contour_integral_winding_number [OF \<open>valid_path \<gamma>\<close>] by fastforce
    then have "((\<lambda>x. f z * (1 / (x - z))) has_contour_integral 0) \<gamma>"
      using has_contour_integral_lmul by fastforce
    then have "((\<lambda>x. f z / (x - z)) has_contour_integral 0) \<gamma>"
      by (simp add: divide_simps)
    moreover have "((\<lambda>x. (f x - f z) / (x - z)) has_contour_integral contour_integral \<gamma> (d z)) \<gamma>"
      using z
      apply (auto simp: v_def)
      apply (metis (no_types, lifting) contour_integrable_eq d_def has_contour_integral_eq has_contour_integral_integral cint_fxy)
      done
    ultimately have *: "((\<lambda>x. f z / (x - z) + (f x - f z) / (x - z)) has_contour_integral (0 + contour_integral \<gamma> (d z))) \<gamma>"
      by (rule has_contour_integral_add)
    have "((\<lambda>w. f w / (w - z)) has_contour_integral contour_integral \<gamma> (d z)) \<gamma>"
            if  "z \<in> u"
      using * by (auto simp: divide_simps has_contour_integral_eq)
    moreover have "((\<lambda>w. f w / (w - z)) has_contour_integral contour_integral \<gamma> (\<lambda>w. f w / (w - z))) \<gamma>"
            if "z \<notin> u"
      apply (rule has_contour_integral_integral [OF contour_integrable_holomorphic_simple [where s=u]])
      using u pasz \<open>valid_path \<gamma>\<close> that
      apply (auto intro: holomorphic_on_imp_continuous_on hol_d)
      apply (rule continuous_intros conf holomorphic_intros holf | force)+
      done
    ultimately show ?thesis
      using z by (simp add: h_def)
  qed
  have znot: "z \<notin> path_image \<gamma>"
    using pasz by blast
  obtain d0 where "d0>0" and d0: "\<And>x y. x \<in> path_image \<gamma> \<Longrightarrow> y \<in> - u \<Longrightarrow> d0 \<le> dist x y"
    using separate_compact_closed [of "path_image \<gamma>" "-u"] pasz u
    by (fastforce simp add: \<open>path \<gamma>\<close> compact_path_image)
  obtain dd where "0 < dd" and dd: "{y + k | y k. y \<in> path_image \<gamma> \<and> k \<in> ball 0 dd} \<subseteq> u"
    apply (rule that [of "d0/2"])
    using \<open>0 < d0\<close>
    apply (auto simp: dist_norm dest: d0)
    done
  have "\<And>x x'. \<lbrakk>x \<in> path_image \<gamma>; dist x x' * 2 < dd\<rbrakk> \<Longrightarrow> \<exists>y k. x' = y + k \<and> y \<in> path_image \<gamma> \<and> dist 0 k * 2 \<le> dd"
    apply (rule_tac x=x in exI)
    apply (rule_tac x="x'-x" in exI)
    apply (force simp add: dist_norm)
    done
  then have 1: "path_image \<gamma> \<subseteq> interior {y + k |y k. y \<in> path_image \<gamma> \<and> k \<in> cball 0 (dd / 2)}"
    apply (clarsimp simp add: mem_interior)
    using \<open>0 < dd\<close>
    apply (rule_tac x="dd/2" in exI, auto)
    done
  obtain t where "compact t" and subt: "path_image \<gamma> \<subseteq> interior t" and t: "t \<subseteq> u"
    apply (rule that [OF _ 1])
    apply (fastforce simp add: \<open>valid_path \<gamma>\<close> compact_valid_path_image intro!: compact_sums)
    apply (rule order_trans [OF _ dd])
    using \<open>0 < dd\<close> by fastforce
  obtain L where "L>0"
           and L: "\<And>f B. \<lbrakk>f holomorphic_on interior t; \<And>z. z\<in>interior t \<Longrightarrow> cmod (f z) \<le> B\<rbrakk> \<Longrightarrow>
                         cmod (contour_integral \<gamma> f) \<le> L * B"
      using contour_integral_bound_exists [OF open_interior \<open>valid_path \<gamma>\<close> subt]
      by blast
  have "bounded(f ` t)"
    by (meson \<open>compact t\<close> compact_continuous_image compact_imp_bounded conf continuous_on_subset t)
  then obtain D where "D>0" and D: "\<And>x. x \<in> t \<Longrightarrow> norm (f x) \<le> D"
    by (auto simp: bounded_pos)
  obtain C where "C>0" and C: "\<And>x. x \<in> t \<Longrightarrow> norm x \<le> C"
    using \<open>compact t\<close> bounded_pos compact_imp_bounded by force
  have "dist (h y) 0 \<le> e" if "0 < e" and le: "D * L / e + C \<le> cmod y" for e y
  proof -
    have "D * L / e > 0"  using \<open>D>0\<close> \<open>L>0\<close> \<open>e>0\<close> by simp
    with le have ybig: "norm y > C" by force
    with C have "y \<notin> t"  by force
    then have ynot: "y \<notin> path_image \<gamma>"
      using subt interior_subset by blast
    have [simp]: "winding_number \<gamma> y = 0"
      apply (rule winding_number_zero_outside [of _ "cball 0 C"])
      using ybig interior_subset subt
      apply (force simp add: loop \<open>path \<gamma>\<close> dist_norm intro!: C)+
      done
    have [simp]: "h y = contour_integral \<gamma> (\<lambda>w. f w/(w - y))"
      by (rule contour_integral_unique [symmetric]) (simp add: v_def ynot V)
    have holint: "(\<lambda>w. f w / (w - y)) holomorphic_on interior t"
      apply (rule holomorphic_on_divide)
      using holf holomorphic_on_subset interior_subset t apply blast
      apply (rule holomorphic_intros)+
      using \<open>y \<notin> t\<close> interior_subset by auto
    have leD: "cmod (f z / (z - y)) \<le> D * (e / L / D)" if z: "z \<in> interior t" for z
    proof -
      have "D * L / e + cmod z \<le> cmod y"
        using le C [of z] z using interior_subset by force
      then have DL2: "D * L / e \<le> cmod (z - y)"
        using norm_triangle_ineq2 [of y z] by (simp add: norm_minus_commute)
      have "cmod (f z / (z - y)) = cmod (f z) * inverse (cmod (z - y))"
        by (simp add: norm_mult norm_inverse Fields.field_class.field_divide_inverse)
      also have "... \<le> D * (e / L / D)"
        apply (rule mult_mono)
        using that D interior_subset apply blast
        using \<open>L>0\<close> \<open>e>0\<close> \<open>D>0\<close> DL2
        apply (auto simp: norm_divide divide_simps algebra_simps)
        done
      finally show ?thesis .
    qed
    have "dist (h y) 0 = cmod (contour_integral \<gamma> (\<lambda>w. f w / (w - y)))"
      by (simp add: dist_norm)
    also have "... \<le> L * (D * (e / L / D))"
      by (rule L [OF holint leD])
    also have "... = e"
      using  \<open>L>0\<close> \<open>0 < D\<close> by auto
    finally show ?thesis .
  qed
  then have "(h \<longlongrightarrow> 0) at_infinity"
    by (meson Lim_at_infinityI)
  moreover have "h holomorphic_on UNIV"
  proof -
    have con_ff: "continuous (at (x,z)) (\<lambda>(x,y). (f y - f x) / (y - x))"
                 if "x \<in> u" "z \<in> u" "x \<noteq> z" for x z
      using that conf
      apply (simp add: split_def continuous_on_eq_continuous_at u)
      apply (simp | rule continuous_intros continuous_within_compose2 [where g=f])+
      done
    have con_fstsnd: "continuous_on UNIV (\<lambda>x. (fst x - snd x) ::complex)"
      by (rule continuous_intros)+
    have open_uu_Id: "open (u \<times> u - Id)"
      apply (rule open_Diff)
      apply (simp add: open_Times u)
      using continuous_closed_preimage_constant [OF con_fstsnd closed_UNIV, of 0]
      apply (auto simp: Id_fstsnd_eq algebra_simps)
      done
    have con_derf: "continuous (at z) (deriv f)" if "z \<in> u" for z
      apply (rule continuous_on_interior [of u])
      apply (simp add: holf holomorphic_deriv holomorphic_on_imp_continuous_on u)
      by (simp add: interior_open that u)
    have tendsto_f': "((\<lambda>(x,y). if y = x then deriv f (x)
                                else (f (y) - f (x)) / (y - x)) \<longlongrightarrow> deriv f x)
                      (at (x, x) within u \<times> u)" if "x \<in> u" for x
    proof (rule Lim_withinI)
      fix e::real assume "0 < e"
      obtain k1 where "k1>0" and k1: "\<And>x'. norm (x' - x) \<le> k1 \<Longrightarrow> norm (deriv f x' - deriv f x) < e"
        using \<open>0 < e\<close> continuous_within_E [OF con_derf [OF \<open>x \<in> u\<close>]]
        by (metis UNIV_I dist_norm)
      obtain k2 where "k2>0" and k2: "ball x k2 \<subseteq> u" by (blast intro: openE [OF u] \<open>x \<in> u\<close>)
      have neq: "norm ((f z' - f x') / (z' - x') - deriv f x) \<le> e"
                    if "z' \<noteq> x'" and less_k1: "norm (x'-x, z'-x) < k1" and less_k2: "norm (x'-x, z'-x) < k2"
                 for x' z'
      proof -
        have cs_less: "w \<in> closed_segment x' z' \<Longrightarrow> cmod (w - x) \<le> norm (x'-x, z'-x)" for w
          apply (drule segment_furthest_le [where y=x])
          by (metis (no_types) dist_commute dist_norm norm_fst_le norm_snd_le order_trans)
        have derf_le: "w \<in> closed_segment x' z' \<Longrightarrow> z' \<noteq> x' \<Longrightarrow> cmod (deriv f w - deriv f x) \<le> e" for w
          by (blast intro: cs_less less_k1 k1 [unfolded divide_const_simps dist_norm] less_imp_le le_less_trans)
        have f_has_der: "\<And>x. x \<in> u \<Longrightarrow> (f has_field_derivative deriv f x) (at x within u)"
          by (metis DERIV_deriv_iff_field_differentiable at_within_open holf holomorphic_on_def u)
        have "closed_segment x' z' \<subseteq> u"
          by (rule order_trans [OF _ k2]) (simp add: cs_less  le_less_trans [OF _ less_k2] dist_complex_def norm_minus_commute subset_iff)
        then have cint_derf: "(deriv f has_contour_integral f z' - f x') (linepath x' z')"
          using contour_integral_primitive [OF f_has_der valid_path_linepath] pasz  by simp
        then have *: "((\<lambda>x. deriv f x / (z' - x')) has_contour_integral (f z' - f x') / (z' - x')) (linepath x' z')"
          by (rule has_contour_integral_div)
        have "norm ((f z' - f x') / (z' - x') - deriv f x) \<le> e/norm(z' - x') * norm(z' - x')"
          apply (rule has_contour_integral_bound_linepath [OF has_contour_integral_diff [OF *]])
          using has_contour_integral_div [where c = "z' - x'", OF has_contour_integral_const_linepath [of "deriv f x" z' x']]
                 \<open>e > 0\<close>  \<open>z' \<noteq> x'\<close>
          apply (auto simp: norm_divide divide_simps derf_le)
          done
        also have "... \<le> e" using \<open>0 < e\<close> by simp
        finally show ?thesis .
      qed
      show "\<exists>d>0. \<forall>xa\<in>u \<times> u.
                  0 < dist xa (x, x) \<and> dist xa (x, x) < d \<longrightarrow>
                  dist (case xa of (x, y) \<Rightarrow> if y = x then deriv f x else (f y - f x) / (y - x)) (deriv f x) \<le> e"
        apply (rule_tac x="min k1 k2" in exI)
        using \<open>k1>0\<close> \<open>k2>0\<close> \<open>e>0\<close>
        apply (force simp: dist_norm neq intro: dual_order.strict_trans2 k1 less_imp_le norm_fst_le)
        done
    qed
    have con_pa_f: "continuous_on (path_image \<gamma>) f"
      by (meson holf holomorphic_on_imp_continuous_on holomorphic_on_subset interior_subset subt t)
    have le_B: "\<And>t. t \<in> {0..1} \<Longrightarrow> cmod (vector_derivative \<gamma> (at t)) \<le> B"
      apply (rule B)
      using \<gamma>' using path_image_def vector_derivative_at by fastforce
    have f_has_cint: "\<And>w. w \<in> v - path_image \<gamma> \<Longrightarrow> ((\<lambda>u. f u / (u - w) ^ 1) has_contour_integral h w) \<gamma>"
      by (simp add: V)
    have cond_uu: "continuous_on (u \<times> u) (\<lambda>(x,y). d x y)"
      apply (simp add: continuous_on_eq_continuous_within d_def continuous_within tendsto_f')
      apply (simp add: tendsto_within_open_NO_MATCH open_Times u, clarify)
      apply (rule Lim_transform_within_open [OF _ open_uu_Id, where f = "(\<lambda>(x,y). (f y - f x) / (y - x))"])
      using con_ff
      apply (auto simp: continuous_within)
      done
    have hol_dw: "(\<lambda>z. d z w) holomorphic_on u" if "w \<in> u" for w
    proof -
      have "continuous_on u ((\<lambda>(x,y). d x y) o (\<lambda>z. (w,z)))"
        by (rule continuous_on_compose continuous_intros continuous_on_subset [OF cond_uu] | force intro: that)+
      then have *: "continuous_on u (\<lambda>z. if w = z then deriv f z else (f w - f z) / (w - z))"
        by (rule rev_iffD1 [OF _ continuous_on_cong [OF refl]]) (simp add: d_def field_simps)
      have **: "\<And>x. \<lbrakk>x \<in> u; x \<noteq> w\<rbrakk> \<Longrightarrow> (\<lambda>z. if w = z then deriv f z else (f w - f z) / (w - z)) field_differentiable at x"
        apply (rule_tac f = "\<lambda>x. (f w - f x)/(w - x)" and d = "dist x w" in field_differentiable_transform_within)
        apply (rule u derivative_intros holomorphic_on_imp_differentiable_at [OF holf] | force simp add: dist_commute)+
        done
      show ?thesis
        unfolding d_def
        apply (rule no_isolated_singularity [OF * _ u, where k = "{w}"])
        apply (auto simp: field_differentiable_def [symmetric] holomorphic_on_open open_Diff u **)
        done
    qed
    { fix a b
      assume abu: "closed_segment a b \<subseteq> u"
      then have "\<And>w. w \<in> u \<Longrightarrow> (\<lambda>z. d z w) contour_integrable_on (linepath a b)"
        by (metis hol_dw continuous_on_subset contour_integrable_continuous_linepath holomorphic_on_imp_continuous_on)
      then have cont_cint_d: "continuous_on u (\<lambda>w. contour_integral (linepath a b) (\<lambda>z. d z w))"
        apply (rule contour_integral_continuous_on_linepath_2D [OF \<open>open u\<close> _ _ abu])
        apply (auto simp: intro: continuous_on_swap_args cond_uu)
        done
      have cont_cint_d\<gamma>: "continuous_on {0..1} ((\<lambda>w. contour_integral (linepath a b) (\<lambda>z. d z w)) o \<gamma>)"
        apply (rule continuous_on_compose)
        using \<open>path \<gamma>\<close> path_def pasz
        apply (auto intro!: continuous_on_subset [OF cont_cint_d])
        apply (force simp add: path_image_def)
        done
      have cint_cint: "(\<lambda>w. contour_integral (linepath a b) (\<lambda>z. d z w)) contour_integrable_on \<gamma>"
        apply (simp add: contour_integrable_on)
        apply (rule integrable_continuous_real)
        apply (rule continuous_on_mult [OF cont_cint_d\<gamma> [unfolded o_def]])
        using pf\<gamma>'
        by (simp add: continuous_on_polymonial_function vector_derivative_at [OF \<gamma>'])
      have "contour_integral (linepath a b) h = contour_integral (linepath a b) (\<lambda>z. contour_integral \<gamma> (d z))"
        using abu  by (force simp add: h_def intro: contour_integral_eq)
      also have "... =  contour_integral \<gamma> (\<lambda>w. contour_integral (linepath a b) (\<lambda>z. d z w))"
        apply (rule contour_integral_swap)
        apply (rule continuous_on_subset [OF cond_uu])
        using abu pasz \<open>valid_path \<gamma>\<close>
        apply (auto intro!: continuous_intros)
        by (metis \<gamma>' continuous_on_eq path_def path_polynomial_function pf\<gamma>' vector_derivative_at)
      finally have cint_h_eq:
          "contour_integral (linepath a b) h =
                    contour_integral \<gamma> (\<lambda>w. contour_integral (linepath a b) (\<lambda>z. d z w))" .
      note cint_cint cint_h_eq
    } note cint_h = this
    have conthu: "continuous_on u h"
    proof (simp add: continuous_on_sequentially, clarify)
      fix a x
      assume x: "x \<in> u" and au: "\<forall>n. a n \<in> u" and ax: "a \<longlonglongrightarrow> x"
      then have A1: "\<forall>\<^sub>F n in sequentially. d (a n) contour_integrable_on \<gamma>"
        by (meson U contour_integrable_on_def eventuallyI)
      obtain dd where "dd>0" and dd: "cball x dd \<subseteq> u" using open_contains_cball u x by force
      have A2: "uniform_limit (path_image \<gamma>) (\<lambda>n. d (a n)) (d x) sequentially"
        unfolding uniform_limit_iff dist_norm
      proof clarify
        fix ee::real
        assume "0 < ee"
        show "\<forall>\<^sub>F n in sequentially. \<forall>\<xi>\<in>path_image \<gamma>. cmod (d (a n) \<xi> - d x \<xi>) < ee"
        proof -
          let ?ddpa = "{(w,z) |w z. w \<in> cball x dd \<and> z \<in> path_image \<gamma>}"
          have "uniformly_continuous_on ?ddpa (\<lambda>(x,y). d x y)"
            apply (rule compact_uniformly_continuous [OF continuous_on_subset[OF cond_uu]])
            using dd pasz \<open>valid_path \<gamma>\<close>
             apply (auto simp: compact_Times compact_valid_path_image simp del: mem_cball)
            done
          then obtain kk where "kk>0"
            and kk: "\<And>x x'. \<lbrakk>x\<in>?ddpa; x'\<in>?ddpa; dist x' x < kk\<rbrakk> \<Longrightarrow>
                             dist ((\<lambda>(x,y). d x y) x') ((\<lambda>(x,y). d x y) x) < ee"
            apply (rule uniformly_continuous_onE [where e = ee])
            using \<open>0 < ee\<close> by auto
          have kk: "\<lbrakk>norm (w - x) \<le> dd; z \<in> path_image \<gamma>; norm ((w, z) - (x, z)) < kk\<rbrakk> \<Longrightarrow> norm (d w z - d x z) < ee"
            for  w z
            using \<open>dd>0\<close> kk [of "(x,z)" "(w,z)"] by (force simp add: norm_minus_commute dist_norm)
          show ?thesis
            using ax unfolding lim_sequentially eventually_sequentially
            apply (drule_tac x="min dd kk" in spec)
            using \<open>dd > 0\<close> \<open>kk > 0\<close>
            apply (fastforce simp: kk dist_norm)
            done
        qed
      qed
      have tendsto_hx: "(\<lambda>n. contour_integral \<gamma> (d (a n))) \<longlonglongrightarrow> h x"
        apply (simp add: contour_integral_unique [OF U, symmetric] x)
        apply (rule contour_integral_uniform_limit [OF A1 A2 le_B])
        apply (auto simp: \<open>valid_path \<gamma>\<close>)
        done
      then show "(h \<circ> a) \<longlonglongrightarrow> h x"
        by (simp add: h_def x au o_def)
    qed
    show ?thesis
    proof (simp add: holomorphic_on_open field_differentiable_def [symmetric], clarify)
      fix z0
      consider "z0 \<in> v" | "z0 \<in> u" using uv_Un by blast
      then show "h field_differentiable at z0"
      proof cases
        assume "z0 \<in> v" then show ?thesis
          using Cauchy_next_derivative [OF con_pa_f le_B f_has_cint _ ov] V f_has_cint \<open>valid_path \<gamma>\<close>
          by (auto simp: field_differentiable_def v_def)
      next
        assume "z0 \<in> u" then
        obtain e where "e>0" and e: "ball z0 e \<subseteq> u" by (blast intro: openE [OF u])
        have *: "contour_integral (linepath a b) h + contour_integral (linepath b c) h + contour_integral (linepath c a) h = 0"
                if abc_subset: "convex hull {a, b, c} \<subseteq> ball z0 e"  for a b c
        proof -
          have *: "\<And>x1 x2 z. z \<in> u \<Longrightarrow> closed_segment x1 x2 \<subseteq> u \<Longrightarrow> (\<lambda>w. d w z) contour_integrable_on linepath x1 x2"
            using  hol_dw holomorphic_on_imp_continuous_on u
            by (auto intro!: contour_integrable_holomorphic_simple)
          have abc: "closed_segment a b \<subseteq> u"  "closed_segment b c \<subseteq> u"  "closed_segment c a \<subseteq> u"
            using that e segments_subset_convex_hull by fastforce+
          have eq0: "\<And>w. w \<in> u \<Longrightarrow> contour_integral (linepath a b +++ linepath b c +++ linepath c a) (\<lambda>z. d z w) = 0"
            apply (rule contour_integral_unique [OF Cauchy_theorem_triangle])
            apply (rule holomorphic_on_subset [OF hol_dw])
            using e abc_subset by auto
          have "contour_integral \<gamma>
                   (\<lambda>x. contour_integral (linepath a b) (\<lambda>z. d z x) +
                        (contour_integral (linepath b c) (\<lambda>z. d z x) +
                         contour_integral (linepath c a) (\<lambda>z. d z x)))  =  0"
            apply (rule contour_integral_eq_0)
            using abc pasz u
            apply (subst contour_integral_join [symmetric], auto intro: eq0 *)+
            done
          then show ?thesis
            by (simp add: cint_h abc contour_integrable_add contour_integral_add [symmetric] add_ac)
        qed
        show ?thesis
          using e \<open>e > 0\<close>
          by (auto intro!: holomorphic_on_imp_differentiable_at [OF _ open_ball] analytic_imp_holomorphic
                           Morera_triangle continuous_on_subset [OF conthu] *)
      qed
    qed
  qed
  ultimately have [simp]: "h z = 0" for z
    by (meson Liouville_weak)
  have "((\<lambda>w. 1 / (w - z)) has_contour_integral complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z) \<gamma>"
    by (rule has_contour_integral_winding_number [OF \<open>valid_path \<gamma>\<close> znot])
  then have "((\<lambda>w. f z * (1 / (w - z))) has_contour_integral complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z * f z) \<gamma>"
    by (metis mult.commute has_contour_integral_lmul)
  then have 1: "((\<lambda>w. f z / (w - z)) has_contour_integral complex_of_real (2 * pi) * \<i> * winding_number \<gamma> z * f z) \<gamma>"
    by (simp add: divide_simps)
  moreover have 2: "((\<lambda>w. (f w - f z) / (w - z)) has_contour_integral 0) \<gamma>"
    using U [OF z] pasz d_def by (force elim: has_contour_integral_eq [where g = "\<lambda>w. (f w - f z)/(w - z)"])
  show ?thesis
    using has_contour_integral_add [OF 1 2]  by (simp add: diff_divide_distrib)
qed


theorem Cauchy_integral_formula_global:
    assumes S: "open S" and holf: "f holomorphic_on S"
        and z: "z \<in> S" and vpg: "valid_path \<gamma>"
        and pasz: "path_image \<gamma> \<subseteq> S - {z}" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
        and zero: "\<And>w. w \<notin> S \<Longrightarrow> winding_number \<gamma> w = 0"
      shows "((\<lambda>w. f w / (w - z)) has_contour_integral (2*pi * \<i> * winding_number \<gamma> z * f z)) \<gamma>"
proof -
  have "path \<gamma>" using vpg by (blast intro: valid_path_imp_path)
  have hols: "(\<lambda>w. f w / (w - z)) holomorphic_on S - {z}" "(\<lambda>w. 1 / (w - z)) holomorphic_on S - {z}"
    by (rule holomorphic_intros holomorphic_on_subset [OF holf] | force)+
  then have cint_fw: "(\<lambda>w. f w / (w - z)) contour_integrable_on \<gamma>"
    by (meson contour_integrable_holomorphic_simple holomorphic_on_imp_continuous_on open_delete S vpg pasz)
  obtain d where "d>0"
      and d: "\<And>g h. \<lbrakk>valid_path g; valid_path h; \<forall>t\<in>{0..1}. cmod (g t - \<gamma> t) < d \<and> cmod (h t - \<gamma> t) < d;
                     pathstart h = pathstart g \<and> pathfinish h = pathfinish g\<rbrakk>
                     \<Longrightarrow> path_image h \<subseteq> S - {z} \<and> (\<forall>f. f holomorphic_on S - {z} \<longrightarrow> contour_integral h f = contour_integral g f)"
    using contour_integral_nearby_ends [OF _ \<open>path \<gamma>\<close> pasz] S by (simp add: open_Diff) metis
  obtain p where polyp: "polynomial_function p"
             and ps: "pathstart p = pathstart \<gamma>" and pf: "pathfinish p = pathfinish \<gamma>" and led: "\<forall>t\<in>{0..1}. cmod (p t - \<gamma> t) < d"
    using path_approx_polynomial_function [OF \<open>path \<gamma>\<close> \<open>d > 0\<close>] by blast
  then have ploop: "pathfinish p = pathstart p" using loop by auto
  have vpp: "valid_path p"  using polyp valid_path_polynomial_function by blast
  have [simp]: "z \<notin> path_image \<gamma>" using pasz by blast
  have paps: "path_image p \<subseteq> S - {z}" and cint_eq: "(\<And>f. f holomorphic_on S - {z} \<Longrightarrow> contour_integral p f = contour_integral \<gamma> f)"
    using pf ps led d [OF vpg vpp] \<open>d > 0\<close> by auto
  have wn_eq: "winding_number p z = winding_number \<gamma> z"
    using vpp paps
    by (simp add: subset_Diff_insert vpg valid_path_polynomial_function winding_number_valid_path cint_eq hols)
  have "winding_number p w = winding_number \<gamma> w" if "w \<notin> S" for w
  proof -
    have hol: "(\<lambda>v. 1 / (v - w)) holomorphic_on S - {z}"
      using that by (force intro: holomorphic_intros holomorphic_on_subset [OF holf])
   have "w \<notin> path_image p" "w \<notin> path_image \<gamma>" using paps pasz that by auto
   then show ?thesis
    using vpp vpg by (simp add: subset_Diff_insert valid_path_polynomial_function winding_number_valid_path cint_eq [OF hol])
  qed
  then have wn0: "\<And>w. w \<notin> S \<Longrightarrow> winding_number p w = 0"
    by (simp add: zero)
  show ?thesis
    using Cauchy_integral_formula_global_weak [OF S holf z polyp paps ploop wn0] hols
    by (metis wn_eq cint_eq has_contour_integral_eqpath cint_fw cint_eq)
qed

theorem Cauchy_theorem_global:
    assumes S: "open S" and holf: "f holomorphic_on S"
        and vpg: "valid_path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
        and pas: "path_image \<gamma> \<subseteq> S"
        and zero: "\<And>w. w \<notin> S \<Longrightarrow> winding_number \<gamma> w = 0"
      shows "(f has_contour_integral 0) \<gamma>"
proof -
  obtain z where "z \<in> S" and znot: "z \<notin> path_image \<gamma>"
  proof -
    have "compact (path_image \<gamma>)"
      using compact_valid_path_image vpg by blast
    then have "path_image \<gamma> \<noteq> S"
      by (metis (no_types) compact_open path_image_nonempty S)
    with pas show ?thesis by (blast intro: that)
  qed
  then have pasz: "path_image \<gamma> \<subseteq> S - {z}" using pas by blast
  have hol: "(\<lambda>w. (w - z) * f w) holomorphic_on S"
    by (rule holomorphic_intros holf)+
  show ?thesis
    using Cauchy_integral_formula_global [OF S hol \<open>z \<in> S\<close> vpg pasz loop zero]
    by (auto simp: znot elim!: has_contour_integral_eq)
qed

corollary Cauchy_theorem_global_outside:
    assumes "open S" "f holomorphic_on S" "valid_path \<gamma>"  "pathfinish \<gamma> = pathstart \<gamma>" "path_image \<gamma> \<subseteq> S"
            "\<And>w. w \<notin> S \<Longrightarrow> w \<in> outside(path_image \<gamma>)"
      shows "(f has_contour_integral 0) \<gamma>"
by (metis Cauchy_theorem_global assms winding_number_zero_in_outside valid_path_imp_path)


lemma simply_connected_imp_winding_number_zero:
  assumes "simply_connected S" "path g"
           "path_image g \<subseteq> S" "pathfinish g = pathstart g" "z \<notin> S"
    shows "winding_number g z = 0"
proof -
  have "winding_number g z = winding_number(linepath (pathstart g) (pathstart g)) z"
    apply (rule winding_number_homotopic_paths)
    apply (rule homotopic_loops_imp_homotopic_paths_null [where a = "pathstart g"])
    apply (rule homotopic_loops_subset [of S])
    using assms
    apply (auto simp: homotopic_paths_imp_homotopic_loops path_defs simply_connected_eq_contractible_path)
    done
  also have "... = 0"
    using assms by (force intro: winding_number_trivial)
  finally show ?thesis .
qed

lemma Cauchy_theorem_simply_connected:
  assumes "open S" "simply_connected S" "f holomorphic_on S" "valid_path g"
           "path_image g \<subseteq> S" "pathfinish g = pathstart g"
    shows "(f has_contour_integral 0) g"
using assms
apply (simp add: simply_connected_eq_contractible_path)
apply (auto intro!: Cauchy_theorem_null_homotopic [where a = "pathstart g"]
                         homotopic_paths_imp_homotopic_loops)
using valid_path_imp_path by blast

lemma holomorphic_logarithm_exists:
  assumes A: "convex A" "open A" 
      and f: "f holomorphic_on A" "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
      and z0: "z0 \<in> A"
    obtains g where "g holomorphic_on A" and "\<And>x. x \<in> A \<Longrightarrow> exp (g x) = f x"
proof -
  note f' = holomorphic_derivI [OF f(1) A(2)]
  from A have "\<exists>g. \<forall>x\<in>A. (g has_field_derivative (deriv f x / f x)) (at x within A)"
    by (intro holomorphic_convex_primitive' holomorphic_intros f) auto
  then obtain g where g: "\<And>x. x \<in> A \<Longrightarrow> (g has_field_derivative deriv f x / f x) (at x)"
    using A by (auto simp: at_within_open[of _ A])

  define h where "h = (\<lambda>x. -g z0 + ln (f z0) + g x)"
  from g and A have g_holo: "g holomorphic_on A"
    by (auto simp: holomorphic_on_def at_within_open[of _ A] field_differentiable_def)
  hence h_holo: "h holomorphic_on A"
    by (auto simp: h_def intro!: holomorphic_intros)
  have "\<exists>c. \<forall>x\<in>A. f x / exp (h x) - 1 = c"
  proof (rule DERIV_zero_constant, goal_cases)
    case (2 x)
    note [simp] = at_within_open[OF _ \<open>open A\<close>]
    from 2 and z0 and f show ?case
      by (auto simp: h_def exp_diff field_simps intro!: derivative_eq_intros g f')
  qed fact+

  then obtain c where c: "\<And>x. x \<in> A \<Longrightarrow> f x / exp (h x) - 1 = c"
    by blast
  from c[OF z0] and z0 and f have "c = 0"
    by (simp add: h_def)
  with c have "\<And>x. x \<in> A \<Longrightarrow> exp (h x) = f x" by simp
  from that[OF h_holo this] show ?thesis .
qed

end
