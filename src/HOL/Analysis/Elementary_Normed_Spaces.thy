(*  Author:     L C Paulson, University of Cambridge
    Author:     Amine Chaieb, University of Cambridge
    Author:     Robert Himmelmann, TU Muenchen
    Author:     Brian Huffman, Portland State University
*)

section \<open>Elementary Normed Vector Spaces\<close>

theory Elementary_Normed_Spaces
  imports
  "HOL-Library.FuncSet"
  Elementary_Metric_Spaces
begin

subsection%unimportant \<open>Various Lemmas Combining Imports\<close>

lemma countable_PiE:
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> countable (F i)) \<Longrightarrow> countable (Pi\<^sub>E I F)"
  by (induct I arbitrary: F rule: finite_induct) (auto simp: PiE_insert_eq)


lemma open_sums:
  fixes T :: "('b::real_normed_vector) set"
  assumes "open S \<or> open T"
  shows "open (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
  using assms
proof
  assume S: "open S"
  show ?thesis
  proof (clarsimp simp: open_dist)
    fix x y
    assume "x \<in> S" "y \<in> T"
    with S obtain e where "e > 0" and e: "\<And>x'. dist x' x < e \<Longrightarrow> x' \<in> S"
      by (auto simp: open_dist)
    then have "\<And>z. dist z (x + y) < e \<Longrightarrow> \<exists>x\<in>S. \<exists>y\<in>T. z = x + y"
      by (metis \<open>y \<in> T\<close> diff_add_cancel dist_add_cancel2)
    then show "\<exists>e>0. \<forall>z. dist z (x + y) < e \<longrightarrow> (\<exists>x\<in>S. \<exists>y\<in>T. z = x + y)"
      using \<open>0 < e\<close> \<open>x \<in> S\<close> by blast
  qed
next
  assume T: "open T"
  show ?thesis
  proof (clarsimp simp: open_dist)
    fix x y
    assume "x \<in> S" "y \<in> T"
    with T obtain e where "e > 0" and e: "\<And>x'. dist x' y < e \<Longrightarrow> x' \<in> T"
      by (auto simp: open_dist)
    then have "\<And>z. dist z (x + y) < e \<Longrightarrow> \<exists>x\<in>S. \<exists>y\<in>T. z = x + y"
      by (metis \<open>x \<in> S\<close> add_diff_cancel_left' add_diff_eq diff_diff_add dist_norm)
    then show "\<exists>e>0. \<forall>z. dist z (x + y) < e \<longrightarrow> (\<exists>x\<in>S. \<exists>y\<in>T. z = x + y)"
      using \<open>0 < e\<close> \<open>y \<in> T\<close> by blast
  qed
qed


subsection \<open>Support\<close>

definition (in monoid_add) support_on :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b set"
  where "support_on s f = {x\<in>s. f x \<noteq> 0}"

lemma in_support_on: "x \<in> support_on s f \<longleftrightarrow> x \<in> s \<and> f x \<noteq> 0"
  by (simp add: support_on_def)

lemma support_on_simps[simp]:
  "support_on {} f = {}"
  "support_on (insert x s) f =
    (if f x = 0 then support_on s f else insert x (support_on s f))"
  "support_on (s \<union> t) f = support_on s f \<union> support_on t f"
  "support_on (s \<inter> t) f = support_on s f \<inter> support_on t f"
  "support_on (s - t) f = support_on s f - support_on t f"
  "support_on (f ` s) g = f ` (support_on s (g \<circ> f))"
  unfolding support_on_def by auto

lemma support_on_cong:
  "(\<And>x. x \<in> s \<Longrightarrow> f x = 0 \<longleftrightarrow> g x = 0) \<Longrightarrow> support_on s f = support_on s g"
  by (auto simp: support_on_def)

lemma support_on_if: "a \<noteq> 0 \<Longrightarrow> support_on A (\<lambda>x. if P x then a else 0) = {x\<in>A. P x}"
  by (auto simp: support_on_def)

lemma support_on_if_subset: "support_on A (\<lambda>x. if P x then a else 0) \<subseteq> {x \<in> A. P x}"
  by (auto simp: support_on_def)

lemma finite_support[intro]: "finite S \<Longrightarrow> finite (support_on S f)"
  unfolding support_on_def by auto

(* TODO: is supp_sum really needed? TODO: Generalize to Finite_Set.fold *)
definition (in comm_monoid_add) supp_sum :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'a"
  where "supp_sum f S = (\<Sum>x\<in>support_on S f. f x)"

lemma supp_sum_empty[simp]: "supp_sum f {} = 0"
  unfolding supp_sum_def by auto

lemma supp_sum_insert[simp]:
  "finite (support_on S f) \<Longrightarrow>
    supp_sum f (insert x S) = (if x \<in> S then supp_sum f S else f x + supp_sum f S)"
  by (simp add: supp_sum_def in_support_on insert_absorb)

lemma supp_sum_divide_distrib: "supp_sum f A / (r::'a::field) = supp_sum (\<lambda>n. f n / r) A"
  by (cases "r = 0")
     (auto simp: supp_sum_def sum_divide_distrib intro!: sum.cong support_on_cong)


subsection \<open>Intervals\<close>

lemma image_affinity_interval:
  fixes c :: "'a::ordered_real_vector"
  shows "((\<lambda>x. m *\<^sub>R x + c) ` {a..b}) = 
           (if {a..b}={} then {}
            else if 0 \<le> m then {m *\<^sub>R a + c .. m  *\<^sub>R b + c}
            else {m *\<^sub>R b + c .. m *\<^sub>R a + c})"
         (is "?lhs = ?rhs")
proof (cases "m=0")
  case True
  then show ?thesis
    by force
next
  case False
  show ?thesis
  proof
    show "?lhs \<subseteq> ?rhs"
      by (auto simp: scaleR_left_mono scaleR_left_mono_neg)
    show "?rhs \<subseteq> ?lhs"
    proof (clarsimp, intro conjI impI subsetI)
      show "\<lbrakk>0 \<le> m; a \<le> b; x \<in> {m *\<^sub>R a + c..m *\<^sub>R b + c}\<rbrakk>
            \<Longrightarrow> x \<in> (\<lambda>x. m *\<^sub>R x + c) ` {a..b}" for x
        apply (rule_tac x="inverse m *\<^sub>R (x-c)" in rev_image_eqI)
        using False apply (auto simp: le_diff_eq pos_le_divideRI)
        using diff_le_eq pos_le_divideR_eq by force
      show "\<lbrakk>\<not> 0 \<le> m; a \<le> b;  x \<in> {m *\<^sub>R b + c..m *\<^sub>R a + c}\<rbrakk>
            \<Longrightarrow> x \<in> (\<lambda>x. m *\<^sub>R x + c) ` {a..b}" for x
        apply (rule_tac x="inverse m *\<^sub>R (x-c)" in rev_image_eqI)
        apply (auto simp: diff_le_eq neg_le_divideR_eq)
        using diff_eq_diff_less_eq linordered_field_class.sign_simps(11) minus_diff_eq not_less scaleR_le_cancel_left_neg by fastforce
    qed
  qed
qed


subsection%unimportant \<open>Various Lemmas on Normed Algebras\<close>


lemma closed_of_nat_image: "closed (of_nat ` A :: 'a::real_normed_algebra_1 set)"
  by (rule discrete_imp_closed[of 1]) (auto simp: dist_of_nat)

lemma closed_of_int_image: "closed (of_int ` A :: 'a::real_normed_algebra_1 set)"
  by (rule discrete_imp_closed[of 1]) (auto simp: dist_of_int)

lemma closed_Nats [simp]: "closed (\<nat> :: 'a :: real_normed_algebra_1 set)"
  unfolding Nats_def by (rule closed_of_nat_image)

lemma closed_Ints [simp]: "closed (\<int> :: 'a :: real_normed_algebra_1 set)"
  unfolding Ints_def by (rule closed_of_int_image)

lemma closed_subset_Ints:
  fixes A :: "'a :: real_normed_algebra_1 set"
  assumes "A \<subseteq> \<int>"
  shows   "closed A"
proof (intro discrete_imp_closed[OF zero_less_one] ballI impI, goal_cases)
  case (1 x y)
  with assms have "x \<in> \<int>" and "y \<in> \<int>" by auto
  with \<open>dist y x < 1\<close> show "y = x"
    by (auto elim!: Ints_cases simp: dist_of_int)
qed

subsection \<open>Filters\<close>

definition indirection :: "'a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> 'a filter"  (infixr "indirection" 70)
  where "a indirection v = at a within {b. \<exists>c\<ge>0. b - a = scaleR c v}"


subsection \<open>Trivial Limits\<close>

lemma trivial_limit_at_infinity:
  "\<not> trivial_limit (at_infinity :: ('a::{real_normed_vector,perfect_space}) filter)"
  unfolding trivial_limit_def eventually_at_infinity
  apply clarsimp
  apply (subgoal_tac "\<exists>x::'a. x \<noteq> 0", clarify)
   apply (rule_tac x="scaleR (b / norm x) x" in exI, simp)
  apply (cut_tac islimpt_UNIV [of "0::'a", unfolded islimpt_def])
  apply (drule_tac x=UNIV in spec, simp)
  done

subsection \<open>Limits\<close>

proposition Lim_at_infinity: "(f \<longlongrightarrow> l) at_infinity \<longleftrightarrow> (\<forall>e>0. \<exists>b. \<forall>x. norm x \<ge> b \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at_infinity)

corollary Lim_at_infinityI [intro?]:
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>B. \<forall>x. norm x \<ge> B \<longrightarrow> dist (f x) l \<le> e"
  shows "(f \<longlongrightarrow> l) at_infinity"
  apply (simp add: Lim_at_infinity, clarify)
  apply (rule ex_forward [OF assms [OF half_gt_zero]], auto)
  done

lemma Lim_transform_within_set_eq:
  fixes a l :: "'a::real_normed_vector"
  shows "eventually (\<lambda>x. x \<in> s \<longleftrightarrow> x \<in> t) (at a)
         \<Longrightarrow> ((f \<longlongrightarrow> l) (at a within s) \<longleftrightarrow> (f \<longlongrightarrow> l) (at a within t))"
  by (force intro: Lim_transform_within_set elim: eventually_mono)

lemma Lim_null:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "(f \<longlongrightarrow> l) net \<longleftrightarrow> ((\<lambda>x. f(x) - l) \<longlongrightarrow> 0) net"
  by (simp add: Lim dist_norm)

lemma Lim_null_comparison:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "eventually (\<lambda>x. norm (f x) \<le> g x) net" "(g \<longlongrightarrow> 0) net"
  shows "(f \<longlongrightarrow> 0) net"
  using assms(2)
proof (rule metric_tendsto_imp_tendsto)
  show "eventually (\<lambda>x. dist (f x) 0 \<le> dist (g x) 0) net"
    using assms(1) by (rule eventually_mono) (simp add: dist_norm)
qed

lemma Lim_transform_bound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
    and g :: "'a \<Rightarrow> 'c::real_normed_vector"
  assumes "eventually (\<lambda>n. norm (f n) \<le> norm (g n)) net"
    and "(g \<longlongrightarrow> 0) net"
  shows "(f \<longlongrightarrow> 0) net"
  using assms(1) tendsto_norm_zero [OF assms(2)]
  by (rule Lim_null_comparison)

lemma lim_null_mult_right_bounded:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_div_algebra"
  assumes f: "(f \<longlongrightarrow> 0) F" and g: "eventually (\<lambda>x. norm(g x) \<le> B) F"
    shows "((\<lambda>z. f z * g z) \<longlongrightarrow> 0) F"
proof -
  have *: "((\<lambda>x. norm (f x) * B) \<longlongrightarrow> 0) F"
    by (simp add: f tendsto_mult_left_zero tendsto_norm_zero)
  have "((\<lambda>x. norm (f x) * norm (g x)) \<longlongrightarrow> 0) F"
    apply (rule Lim_null_comparison [OF _ *])
    apply (simp add: eventually_mono [OF g] mult_left_mono)
    done
  then show ?thesis
    by (subst tendsto_norm_zero_iff [symmetric]) (simp add: norm_mult)
qed

lemma lim_null_mult_left_bounded:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_div_algebra"
  assumes g: "eventually (\<lambda>x. norm(g x) \<le> B) F" and f: "(f \<longlongrightarrow> 0) F"
    shows "((\<lambda>z. g z * f z) \<longlongrightarrow> 0) F"
proof -
  have *: "((\<lambda>x. B * norm (f x)) \<longlongrightarrow> 0) F"
    by (simp add: f tendsto_mult_right_zero tendsto_norm_zero)
  have "((\<lambda>x. norm (g x) * norm (f x)) \<longlongrightarrow> 0) F"
    apply (rule Lim_null_comparison [OF _ *])
    apply (simp add: eventually_mono [OF g] mult_right_mono)
    done
  then show ?thesis
    by (subst tendsto_norm_zero_iff [symmetric]) (simp add: norm_mult)
qed

lemma lim_null_scaleR_bounded:
  assumes f: "(f \<longlongrightarrow> 0) net" and gB: "eventually (\<lambda>a. f a = 0 \<or> norm(g a) \<le> B) net"
    shows "((\<lambda>n. f n *\<^sub>R g n) \<longlongrightarrow> 0) net"
proof
  fix \<epsilon>::real
  assume "0 < \<epsilon>"
  then have B: "0 < \<epsilon> / (abs B + 1)" by simp
  have *: "\<bar>f x\<bar> * norm (g x) < \<epsilon>" if f: "\<bar>f x\<bar> * (\<bar>B\<bar> + 1) < \<epsilon>" and g: "norm (g x) \<le> B" for x
  proof -
    have "\<bar>f x\<bar> * norm (g x) \<le> \<bar>f x\<bar> * B"
      by (simp add: mult_left_mono g)
    also have "\<dots> \<le> \<bar>f x\<bar> * (\<bar>B\<bar> + 1)"
      by (simp add: mult_left_mono)
    also have "\<dots> < \<epsilon>"
      by (rule f)
    finally show ?thesis .
  qed
  show "\<forall>\<^sub>F x in net. dist (f x *\<^sub>R g x) 0 < \<epsilon>"
    apply (rule eventually_mono [OF eventually_conj [OF tendstoD [OF f B] gB] ])
    apply (auto simp: \<open>0 < \<epsilon>\<close> divide_simps * split: if_split_asm)
    done
qed

lemma Lim_norm_ubound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "\<not>(trivial_limit net)" "(f \<longlongrightarrow> l) net" "eventually (\<lambda>x. norm(f x) \<le> e) net"
  shows "norm(l) \<le> e"
  using assms by (fast intro: tendsto_le tendsto_intros)

lemma Lim_norm_lbound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "\<not> trivial_limit net"
    and "(f \<longlongrightarrow> l) net"
    and "eventually (\<lambda>x. e \<le> norm (f x)) net"
  shows "e \<le> norm l"
  using assms by (fast intro: tendsto_le tendsto_intros)

text\<open>Limit under bilinear function\<close>

lemma Lim_bilinear:
  assumes "(f \<longlongrightarrow> l) net"
    and "(g \<longlongrightarrow> m) net"
    and "bounded_bilinear h"
  shows "((\<lambda>x. h (f x) (g x)) \<longlongrightarrow> (h l m)) net"
  using \<open>bounded_bilinear h\<close> \<open>(f \<longlongrightarrow> l) net\<close> \<open>(g \<longlongrightarrow> m) net\<close>
  by (rule bounded_bilinear.tendsto)

lemma Lim_at_zero:
  fixes a :: "'a::real_normed_vector"
    and l :: "'b::topological_space"
  shows "(f \<longlongrightarrow> l) (at a) \<longleftrightarrow> ((\<lambda>x. f(a + x)) \<longlongrightarrow> l) (at 0)"
  using LIM_offset_zero LIM_offset_zero_cancel ..


subsection%unimportant \<open>Limit Point of Filter\<close>

lemma netlimit_at_vector:
  fixes a :: "'a::real_normed_vector"
  shows "netlimit (at a) = a"
proof (cases "\<exists>x. x \<noteq> a")
  case True then obtain x where x: "x \<noteq> a" ..
  have "\<not> trivial_limit (at a)"
    unfolding trivial_limit_def eventually_at dist_norm
    apply clarsimp
    apply (rule_tac x="a + scaleR (d / 2) (sgn (x - a))" in exI)
    apply (simp add: norm_sgn sgn_zero_iff x)
    done
  then show ?thesis
    by (rule netlimit_within [of a UNIV])
qed simp

subsection \<open>Boundedness\<close>

lemma bounded_pos: "bounded S \<longleftrightarrow> (\<exists>b>0. \<forall>x\<in> S. norm x \<le> b)"
  apply (simp add: bounded_iff)
  apply (subgoal_tac "\<And>x (y::real). 0 < 1 + \<bar>y\<bar> \<and> (x \<le> y \<longrightarrow> x \<le> 1 + \<bar>y\<bar>)")
  apply metis
  apply arith
  done

lemma bounded_pos_less: "bounded S \<longleftrightarrow> (\<exists>b>0. \<forall>x\<in> S. norm x < b)"
  apply (simp add: bounded_pos)
  apply (safe; rule_tac x="b+1" in exI; force)
  done

lemma Bseq_eq_bounded:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "Bseq f \<longleftrightarrow> bounded (range f)"
  unfolding Bseq_def bounded_pos by auto

lemma bounded_linear_image:
  assumes "bounded S"
    and "bounded_linear f"
  shows "bounded (f ` S)"
proof -
  from assms(1) obtain b where "b > 0" and b: "\<forall>x\<in>S. norm x \<le> b"
    unfolding bounded_pos by auto
  from assms(2) obtain B where B: "B > 0" "\<forall>x. norm (f x) \<le> B * norm x"
    using bounded_linear.pos_bounded by (auto simp: ac_simps)
  show ?thesis
    unfolding bounded_pos
  proof (intro exI, safe)
    show "norm (f x) \<le> B * b" if "x \<in> S" for x
      by (meson B b less_imp_le mult_left_mono order_trans that)
  qed (use \<open>b > 0\<close> \<open>B > 0\<close> in auto)
qed

lemma bounded_scaling:
  fixes S :: "'a::real_normed_vector set"
  shows "bounded S \<Longrightarrow> bounded ((\<lambda>x. c *\<^sub>R x) ` S)"
  apply (rule bounded_linear_image, assumption)
  apply (rule bounded_linear_scaleR_right)
  done

lemma bounded_scaleR_comp:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "bounded (f ` S)"
  shows "bounded ((\<lambda>x. r *\<^sub>R f x) ` S)"
  using bounded_scaling[of "f ` S" r] assms
  by (auto simp: image_image)

lemma bounded_translation:
  fixes S :: "'a::real_normed_vector set"
  assumes "bounded S"
  shows "bounded ((\<lambda>x. a + x) ` S)"
proof -
  from assms obtain b where b: "b > 0" "\<forall>x\<in>S. norm x \<le> b"
    unfolding bounded_pos by auto
  {
    fix x
    assume "x \<in> S"
    then have "norm (a + x) \<le> b + norm a"
      using norm_triangle_ineq[of a x] b by auto
  }
  then show ?thesis
    unfolding bounded_pos
    using norm_ge_zero[of a] b(1) and add_strict_increasing[of b 0 "norm a"]
    by (auto intro!: exI[of _ "b + norm a"])
qed

lemma bounded_translation_minus:
  fixes S :: "'a::real_normed_vector set"
  shows "bounded S \<Longrightarrow> bounded ((\<lambda>x. x - a) ` S)"
using bounded_translation [of S "-a"] by simp

lemma bounded_uminus [simp]:
  fixes X :: "'a::real_normed_vector set"
  shows "bounded (uminus ` X) \<longleftrightarrow> bounded X"
by (auto simp: bounded_def dist_norm; rule_tac x="-x" in exI; force simp: add.commute norm_minus_commute)

lemma uminus_bounded_comp [simp]:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "bounded ((\<lambda>x. - f x) ` S) \<longleftrightarrow> bounded (f ` S)"
  using bounded_uminus[of "f ` S"]
  by (auto simp: image_image)

lemma bounded_plus_comp:
  fixes f g::"'a \<Rightarrow> 'b::real_normed_vector"
  assumes "bounded (f ` S)"
  assumes "bounded (g ` S)"
  shows "bounded ((\<lambda>x. f x + g x) ` S)"
proof -
  {
    fix B C
    assume "\<And>x. x\<in>S \<Longrightarrow> norm (f x) \<le> B" "\<And>x. x\<in>S \<Longrightarrow> norm (g x) \<le> C"
    then have "\<And>x. x \<in> S \<Longrightarrow> norm (f x + g x) \<le> B + C"
      by (auto intro!: norm_triangle_le add_mono)
  } then show ?thesis
    using assms by (fastforce simp: bounded_iff)
qed

lemma bounded_plus:
  fixes S ::"'a::real_normed_vector set"
  assumes "bounded S" "bounded T"
  shows "bounded ((\<lambda>(x,y). x + y) ` (S \<times> T))"
  using bounded_plus_comp [of fst "S \<times> T" snd] assms
  by (auto simp: split_def split: if_split_asm)

lemma bounded_minus_comp:
  "bounded (f ` S) \<Longrightarrow> bounded (g ` S) \<Longrightarrow> bounded ((\<lambda>x. f x - g x) ` S)"
  for f g::"'a \<Rightarrow> 'b::real_normed_vector"
  using bounded_plus_comp[of "f" S "\<lambda>x. - g x"]
  by auto

lemma bounded_minus:
  fixes S ::"'a::real_normed_vector set"
  assumes "bounded S" "bounded T"
  shows "bounded ((\<lambda>(x,y). x - y) ` (S \<times> T))"
  using bounded_minus_comp [of fst "S \<times> T" snd] assms
  by (auto simp: split_def split: if_split_asm)

lemma not_bounded_UNIV[simp]:
  "\<not> bounded (UNIV :: 'a::{real_normed_vector, perfect_space} set)"
proof (auto simp: bounded_pos not_le)
  obtain x :: 'a where "x \<noteq> 0"
    using perfect_choose_dist [OF zero_less_one] by fast
  fix b :: real
  assume b: "b >0"
  have b1: "b +1 \<ge> 0"
    using b by simp
  with \<open>x \<noteq> 0\<close> have "b < norm (scaleR (b + 1) (sgn x))"
    by (simp add: norm_sgn)
  then show "\<exists>x::'a. b < norm x" ..
qed

corollary cobounded_imp_unbounded:
    fixes S :: "'a::{real_normed_vector, perfect_space} set"
    shows "bounded (- S) \<Longrightarrow> \<not> bounded S"
  using bounded_Un [of S "-S"]  by (simp add: sup_compl_top)


subsection \<open>Normed spaces with the Heine-Borel property\<close>

lemma not_compact_UNIV[simp]:
  fixes s :: "'a::{real_normed_vector,perfect_space,heine_borel} set"
  shows "\<not> compact (UNIV::'a set)"
    by (simp add: compact_eq_bounded_closed)

text\<open>Representing sets as the union of a chain of compact sets.\<close>
lemma closed_Union_compact_subsets:
  fixes S :: "'a::{heine_borel,real_normed_vector} set"
  assumes "closed S"
  obtains F where "\<And>n. compact(F n)" "\<And>n. F n \<subseteq> S" "\<And>n. F n \<subseteq> F(Suc n)"
                  "(\<Union>n. F n) = S" "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> \<exists>N. \<forall>n \<ge> N. K \<subseteq> F n"
proof
  show "compact (S \<inter> cball 0 (of_nat n))" for n
    using assms compact_eq_bounded_closed by auto
next
  show "(\<Union>n. S \<inter> cball 0 (real n)) = S"
    by (auto simp: real_arch_simple)
next
  fix K :: "'a set"
  assume "compact K" "K \<subseteq> S"
  then obtain N where "K \<subseteq> cball 0 N"
    by (meson bounded_pos mem_cball_0 compact_imp_bounded subsetI)
  then show "\<exists>N. \<forall>n\<ge>N. K \<subseteq> S \<inter> cball 0 (real n)"
    by (metis of_nat_le_iff Int_subset_iff \<open>K \<subseteq> S\<close> real_arch_simple subset_cball subset_trans)
qed auto


subsection \<open>Continuity\<close>

subsubsection%unimportant \<open>Structural rules for uniform continuity\<close>

lemma uniformly_continuous_on_dist[continuous_intros]:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "uniformly_continuous_on s f"
    and "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. dist (f x) (g x))"
proof -
  {
    fix a b c d :: 'b
    have "\<bar>dist a b - dist c d\<bar> \<le> dist a c + dist b d"
      using dist_triangle2 [of a b c] dist_triangle2 [of b c d]
      using dist_triangle3 [of c d a] dist_triangle [of a d b]
      by arith
  } note le = this
  {
    fix x y
    assume f: "(\<lambda>n. dist (f (x n)) (f (y n))) \<longlonglongrightarrow> 0"
    assume g: "(\<lambda>n. dist (g (x n)) (g (y n))) \<longlonglongrightarrow> 0"
    have "(\<lambda>n. \<bar>dist (f (x n)) (g (x n)) - dist (f (y n)) (g (y n))\<bar>) \<longlonglongrightarrow> 0"
      by (rule Lim_transform_bound [OF _ tendsto_add_zero [OF f g]],
        simp add: le)
  }
  then show ?thesis
    using assms unfolding uniformly_continuous_on_sequentially
    unfolding dist_real_def by simp
qed

lemma uniformly_continuous_on_norm[continuous_intros]:
  fixes f :: "'a :: metric_space \<Rightarrow> 'b :: real_normed_vector"
  assumes "uniformly_continuous_on s f"
  shows "uniformly_continuous_on s (\<lambda>x. norm (f x))"
  unfolding norm_conv_dist using assms
  by (intro uniformly_continuous_on_dist uniformly_continuous_on_const)

lemma uniformly_continuous_on_cmul[continuous_intros]:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "uniformly_continuous_on s f"
  shows "uniformly_continuous_on s (\<lambda>x. c *\<^sub>R f(x))"
  using bounded_linear_scaleR_right assms
  by (rule bounded_linear.uniformly_continuous_on)

lemma dist_minus:
  fixes x y :: "'a::real_normed_vector"
  shows "dist (- x) (- y) = dist x y"
  unfolding dist_norm minus_diff_minus norm_minus_cancel ..

lemma uniformly_continuous_on_minus[continuous_intros]:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "uniformly_continuous_on s f \<Longrightarrow> uniformly_continuous_on s (\<lambda>x. - f x)"
  unfolding uniformly_continuous_on_def dist_minus .

lemma uniformly_continuous_on_add[continuous_intros]:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "uniformly_continuous_on s f"
    and "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. f x + g x)"
  using assms
  unfolding uniformly_continuous_on_sequentially
  unfolding dist_norm tendsto_norm_zero_iff add_diff_add
  by (auto intro: tendsto_add_zero)

lemma uniformly_continuous_on_diff[continuous_intros]:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "uniformly_continuous_on s f"
    and "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. f x - g x)"
  using assms uniformly_continuous_on_add [of s f "- g"]
    by (simp add: fun_Compl_def uniformly_continuous_on_minus)


subsection%unimportant \<open>Topological properties of linear functions\<close>

lemma linear_lim_0:
  assumes "bounded_linear f"
  shows "(f \<longlongrightarrow> 0) (at (0))"
proof -
  interpret f: bounded_linear f by fact
  have "(f \<longlongrightarrow> f 0) (at 0)"
    using tendsto_ident_at by (rule f.tendsto)
  then show ?thesis unfolding f.zero .
qed

lemma linear_continuous_at:
  assumes "bounded_linear f"
  shows "continuous (at a) f"
  unfolding continuous_at using assms
  apply (rule bounded_linear.tendsto)
  apply (rule tendsto_ident_at)
  done

lemma linear_continuous_within:
  "bounded_linear f \<Longrightarrow> continuous (at x within s) f"
  using continuous_at_imp_continuous_within[of x f s] using linear_continuous_at[of f] by auto

lemma linear_continuous_on:
  "bounded_linear f \<Longrightarrow> continuous_on s f"
  using continuous_at_imp_continuous_on[of s f] using linear_continuous_at[of f] by auto

end