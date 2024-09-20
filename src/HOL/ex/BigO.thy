(*  Title:      HOL/ex/BigO.thy
    Authors:    Jeremy Avigad and Kevin Donnelly; proofs tidied by LCP
*)

section \<open>Big O notation\<close>

theory BigO
  imports
    Complex_Main
    "HOL-Library.Function_Algebras"
    "HOL-Library.Set_Algebras"
begin

text \<open>
  This library is designed to support asymptotic ``big O'' calculations,
  i.e.~reasoning with expressions of the form \<open>f = O(g)\<close> and \<open>f = g + O(h)\<close>.
  An earlier version of this library is described in detail in \<^cite>\<open>"Avigad-Donnelly"\<close>.

  The main changes in this version are as follows:

    \<^item> We have eliminated the \<open>O\<close> operator on sets. (Most uses of this seem
      to be inessential.)
    \<^item> We no longer use \<open>+\<close> as output syntax for \<open>+o\<close>
    \<^item> Lemmas involving \<open>sumr\<close> have been replaced by more general lemmas
      involving `\<open>sum\<close>.
    \<^item> The library has been expanded, with e.g.~support for expressions of
      the form \<open>f < g + O(h)\<close>.

  Note also since the Big O library includes rules that demonstrate set
  inclusion, to use the automated reasoners effectively with the library one
  should redeclare the theorem \<open>subsetI\<close> as an intro rule, rather than as an
  \<open>intro!\<close> rule, for example, using \<^theory_text>\<open>declare subsetI [del, intro]\<close>.
\<close>


subsection \<open>Definitions\<close>

definition bigo :: "('a \<Rightarrow> 'b::linordered_idom) \<Rightarrow> ('a \<Rightarrow> 'b) set"  (\<open>(1O'(_'))\<close>)
  where "O(f:: 'a \<Rightarrow> 'b) = {h. \<exists>c. \<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>}"

lemma bigo_pos_const:
  "(\<exists>c::'a::linordered_idom. \<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>) \<longleftrightarrow>
    (\<exists>c. 0 < c \<and> (\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>))"
  by (metis (no_types, opaque_lifting) abs_ge_zero abs_not_less_zero abs_of_nonneg dual_order.trans
        mult_1 zero_less_abs_iff zero_less_mult_iff zero_less_one)

lemma bigo_alt_def: "O(f) = {h. \<exists>c. 0 < c \<and> (\<forall>x. \<bar>h x\<bar> \<le> c * \<bar>f x\<bar>)}"
  by (auto simp add: bigo_def bigo_pos_const)

lemma bigo_elt_subset [intro]: "f \<in> O(g) \<Longrightarrow> O(f) \<le> O(g)"
  apply (auto simp add: bigo_alt_def)
  by (metis (no_types, opaque_lifting) mult.assoc mult_le_cancel_left_pos order.trans
      zero_less_mult_iff)

lemma bigo_refl [intro]: "f \<in> O(f)"
  using bigo_def comm_monoid_mult_class.mult_1 dual_order.eq_iff by blast

lemma bigo_zero: "0 \<in> O(g)"
  using bigo_def mult_le_cancel_left1 by fastforce

lemma bigo_zero2: "O(\<lambda>x. 0) = {\<lambda>x. 0}"
  by (auto simp add: bigo_def)

lemma bigo_plus_self_subset [intro]: "O(f) + O(f) \<subseteq> O(f)"
  apply (auto simp add: bigo_alt_def set_plus_def)
  apply (rule_tac x = "c + ca" in exI)
  by (smt (verit, best) abs_triangle_ineq add_mono add_pos_pos comm_semiring_class.distrib dual_order.trans)

lemma bigo_plus_idemp [simp]: "O(f) + O(f) = O(f)"
  by (simp add: antisym bigo_plus_self_subset bigo_zero set_zero_plus2)

lemma bigo_plus_subset [intro]: "O(f + g) \<subseteq> O(f) + O(g)"
  apply (rule subsetI)
  apply (auto simp add: bigo_def bigo_pos_const func_plus set_plus_def)
  apply (subst bigo_pos_const [symmetric])+
  apply (rule_tac x = "\<lambda>n. if \<bar>g n\<bar> \<le> \<bar>f n\<bar> then x n else 0" in exI)
  apply (rule conjI)
   apply (rule_tac x = "c + c" in exI)
   apply (clarsimp)
  apply (smt (verit, ccfv_threshold) mult.commute abs_triangle_ineq add_le_cancel_left dual_order.trans mult.left_commute mult_2 mult_le_cancel_left_pos)
  apply (simp add: order_less_le)
  apply (rule_tac x = "\<lambda>n. if \<bar>f n\<bar> < \<bar>g n\<bar> then x n else 0" in exI)
  apply (rule conjI)
   apply (rule_tac x = "c + c" in exI)
   apply auto
  apply (subgoal_tac "c * \<bar>f xa + g xa\<bar> \<le> (c + c) * \<bar>g xa\<bar>")
   apply (metis mult_2 order.trans)
  apply simp
  done

lemma bigo_plus_subset2 [intro]: "A \<subseteq> O(f) \<Longrightarrow> B \<subseteq> O(f) \<Longrightarrow> A + B \<subseteq> O(f)"
  using bigo_plus_idemp set_plus_mono2 by blast

lemma bigo_plus_eq: "\<forall>x. 0 \<le> f x \<Longrightarrow> \<forall>x. 0 \<le> g x \<Longrightarrow> O(f + g) = O(f) + O(g)"
  apply (rule equalityI)
   apply (rule bigo_plus_subset)
  apply (simp add: bigo_alt_def set_plus_def func_plus)
  apply clarify
  apply (rule_tac x = "max c ca" in exI)
  by (smt (verit, del_insts) add.commute abs_triangle_ineq add_mono_thms_linordered_field(3) distrib_left less_max_iff_disj linorder_not_less max.orderE max_mult_distrib_right order_le_less)

lemma bigo_bounded_alt: "\<forall>x. 0 \<le> f x \<Longrightarrow> \<forall>x. f x \<le> c * g x \<Longrightarrow> f \<in> O(g)"
  by (simp add: bigo_def) (metis abs_mult abs_of_nonneg order_trans)

lemma bigo_bounded: "\<forall>x. 0 \<le> f x \<Longrightarrow> \<forall>x. f x \<le> g x \<Longrightarrow> f \<in> O(g)"
  by (metis bigo_bounded_alt mult_1)

lemma bigo_bounded2: "\<forall>x. lb x \<le> f x \<Longrightarrow> \<forall>x. f x \<le> lb x + g x \<Longrightarrow> f \<in> lb +o O(g)"
  by (simp add: add.commute bigo_bounded diff_le_eq set_minus_imp_plus)

lemma bigo_abs: "(\<lambda>x. \<bar>f x\<bar>) =o O(f)"
  by (smt (verit, del_insts) abs_abs bigo_def bigo_refl mem_Collect_eq)

lemma bigo_abs2: "f =o O(\<lambda>x. \<bar>f x\<bar>)"
  by (smt (verit, del_insts) abs_abs bigo_def bigo_refl mem_Collect_eq)

lemma bigo_abs3: "O(f) = O(\<lambda>x. \<bar>f x\<bar>)"
  using bigo_abs bigo_abs2 bigo_elt_subset by blast

lemma bigo_abs4: assumes "f =o g +o O(h)" shows "(\<lambda>x. \<bar>f x\<bar>) =o (\<lambda>x. \<bar>g x\<bar>) +o O(h)"
proof -
  { assume *: "f - g \<in> O(h)"
    have "(\<lambda>x. \<bar>f x\<bar> - \<bar>g x\<bar>) =o O(\<lambda>x. \<bar>\<bar>f x\<bar> - \<bar>g x\<bar>\<bar>)"
      by (rule bigo_abs2)
    also have "\<dots> \<subseteq> O(\<lambda>x. \<bar>f x - g x\<bar>)"
      by (simp add: abs_triangle_ineq3 bigo_bounded bigo_elt_subset)
    also have "\<dots> \<subseteq> O(f - g)"
      using bigo_abs3 by fastforce
    also from * have "\<dots> \<subseteq> O(h)"
      by (rule bigo_elt_subset)
    finally have "(\<lambda>x. \<bar>f x\<bar> - \<bar>g x\<bar>) \<in> O(h)" . }
  then show ?thesis
    by (smt (verit) assms bigo_alt_def fun_diff_def mem_Collect_eq set_minus_imp_plus set_plus_imp_minus)
qed

lemma bigo_abs5: "f =o O(g) \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) =o O(g)"
  by (auto simp: bigo_def)

lemma bigo_elt_subset2 [intro]:
  assumes *: "f \<in> g +o O(h)"
  shows "O(f) \<subseteq> O(g) + O(h)"
proof -
  note *
  also have "g +o O(h) \<subseteq> O(g) + O(h)"
    by (auto del: subsetI)
  also have "\<dots> = O(\<lambda>x. \<bar>g x\<bar>) + O(\<lambda>x. \<bar>h x\<bar>)"
    by (subst bigo_abs3 [symmetric])+ (rule refl)
  also have "\<dots> = O((\<lambda>x. \<bar>g x\<bar>) + (\<lambda>x. \<bar>h x\<bar>))"
    by (rule bigo_plus_eq [symmetric]) auto
  finally have "f \<in> \<dots>" .
  then have "O(f) \<subseteq> \<dots>"
    by (elim bigo_elt_subset)
  also have "\<dots> = O(\<lambda>x. \<bar>g x\<bar>) + O(\<lambda>x. \<bar>h x\<bar>)"
    by (rule bigo_plus_eq, auto)
  finally show ?thesis
    by (simp flip: bigo_abs3)
qed

lemma bigo_mult [intro]: "O(f)*O(g) \<subseteq> O(f * g)"
  apply (rule subsetI)
  apply (subst bigo_def)
  apply (clarsimp simp add: bigo_alt_def set_times_def func_times)
  apply (rule_tac x = "c * ca" in exI)
  by (smt (verit, ccfv_threshold) mult.commute mult.assoc abs_ge_zero abs_mult dual_order.trans mult_mono)

lemma bigo_mult2 [intro]: "f *o O(g) \<subseteq> O(f * g)"
  by (metis bigo_mult bigo_refl dual_order.trans mult.commute set_times_mono4)

lemma bigo_mult3: "f \<in> O(h) \<Longrightarrow> g \<in> O(j) \<Longrightarrow> f * g \<in> O(h * j)"
  using bigo_mult mult.commute mult.commute set_times_intro subsetD by blast

lemma bigo_mult4 [intro]: "f \<in> k +o O(h) \<Longrightarrow> g * f \<in> (g * k) +o O(g * h)"
  by (metis bigo_mult3 bigo_refl left_diff_distrib' mult.commute set_minus_imp_plus set_plus_imp_minus)

lemma bigo_mult5:
  fixes f :: "'a \<Rightarrow> 'b::linordered_field"
  assumes "\<forall>x. f x \<noteq> 0"
  shows "O(f * g) \<subseteq> f *o O(g)"
proof
  fix h
  assume "h \<in> O(f * g)"
  then have "(\<lambda>x. 1 / (f x)) * h \<in> (\<lambda>x. 1 / f x) *o O(f * g)"
    by auto
  also have "\<dots> \<subseteq> O((\<lambda>x. 1 / f x) * (f * g))"
    by (rule bigo_mult2)
  also have "(\<lambda>x. 1 / f x) * (f * g) = g"
    using assms by auto
  finally have "(\<lambda>x. (1::'b) / f x) * h \<in> O(g)" .
  then have "f * ((\<lambda>x. (1::'b) / f x) * h) \<in> f *o O(g)"
    by auto
  also have "f * ((\<lambda>x. (1::'b) / f x) * h) = h"
  by (simp add: assms times_fun_def)
  finally show "h \<in> f *o O(g)" .
qed

lemma bigo_mult6: "\<forall>x. f x \<noteq> 0 \<Longrightarrow> O(f * g) = f *o O(g)"
  for f :: "'a \<Rightarrow> 'b::linordered_field"
  by (simp add: bigo_mult2 bigo_mult5 subset_antisym)

lemma bigo_mult7: "\<forall>x. f x \<noteq> 0 \<Longrightarrow> O(f * g) \<subseteq> O(f) * O(g)"
  for f :: "'a \<Rightarrow> 'b::linordered_field"
  by (metis bigo_mult6 bigo_refl mult.commute set_times_mono4)

lemma bigo_mult8: "\<forall>x. f x \<noteq> 0 \<Longrightarrow> O(f * g) = O(f) * O(g)"
  for f :: "'a \<Rightarrow> 'b::linordered_field"
  by (simp add: bigo_mult bigo_mult7 subset_antisym)

lemma bigo_minus [intro]: "f \<in> O(g) \<Longrightarrow> - f \<in> O(g)"
  by (auto simp add: bigo_def fun_Compl_def)

lemma bigo_minus2:
  assumes "f \<in> g +o O(h)" shows "- f \<in> -g +o O(h)"
proof -
   have "- f + g \<in> O(h)"
    by (metis assms bigo_minus minus_diff_eq set_plus_imp_minus uminus_add_conv_diff)
  then show ?thesis
    by (simp add: set_minus_imp_plus)
qed

lemma bigo_minus3: "O(- f) = O(f)"
  by (auto simp add: bigo_def fun_Compl_def)

lemma bigo_plus_absorb_lemma1:
  assumes *: "f \<in> O(g)"
  shows "f +o O(g) \<subseteq> O(g)"
  using assms bigo_plus_idemp set_plus_mono4 by blast

lemma bigo_plus_absorb_lemma2:
  assumes *: "f \<in> O(g)"
  shows "O(g) \<subseteq> f +o O(g)"
proof -
  from * have "- f \<in> O(g)"
    by auto
  then have "- f +o O(g) \<subseteq> O(g)"
    by (elim bigo_plus_absorb_lemma1)
  then have "f +o (- f +o O(g)) \<subseteq> f +o O(g)"
    by auto
  also have "f +o (- f +o O(g)) = O(g)"
    by (simp add: set_plus_rearranges)
  finally show ?thesis .
qed

lemma bigo_plus_absorb [simp]: "f \<in> O(g) \<Longrightarrow> f +o O(g) = O(g)"
  by (simp add: bigo_plus_absorb_lemma1 bigo_plus_absorb_lemma2 subset_antisym)

lemma bigo_plus_absorb2 [intro]: "f \<in> O(g) \<Longrightarrow> A \<subseteq> O(g) \<Longrightarrow> f +o A \<subseteq> O(g)"
  using bigo_plus_absorb set_plus_mono by blast

lemma bigo_add_commute_imp: "f \<in> g +o O(h) \<Longrightarrow> g \<in> f +o O(h)"
  by (metis bigo_minus minus_diff_eq set_minus_imp_plus set_plus_imp_minus)

lemma bigo_add_commute: "f \<in> g +o O(h) \<longleftrightarrow> g \<in> f +o O(h)"
  using bigo_add_commute_imp by blast

lemma bigo_const1: "(\<lambda>x. c) \<in> O(\<lambda>x. 1)"
  by (auto simp add: bigo_def ac_simps)

lemma bigo_const2 [intro]: "O(\<lambda>x. c) \<subseteq> O(\<lambda>x. 1)"
  by (metis bigo_elt_subset bigo_const1)

lemma bigo_const3: "c \<noteq> 0 \<Longrightarrow> (\<lambda>x. 1) \<in> O(\<lambda>x. c)"
  for c :: "'a::linordered_field"
  by (metis bigo_bounded_alt le_numeral_extra(4) nonzero_divide_eq_eq zero_less_one_class.zero_le_one)

lemma bigo_const4: "c \<noteq> 0 \<Longrightarrow> O(\<lambda>x. 1) \<subseteq> O(\<lambda>x. c)"
  for c :: "'a::linordered_field"
  by (metis bigo_elt_subset bigo_const3)

lemma bigo_const [simp]: "c \<noteq> 0 \<Longrightarrow> O(\<lambda>x. c) = O(\<lambda>x. 1)"
  for c :: "'a::linordered_field"
  by (metis equalityI bigo_const2 bigo_const4)

lemma bigo_const_mult1: "(\<lambda>x. c * f x) \<in> O(f)"
  by (simp add: bigo_def) (metis abs_mult dual_order.refl)

lemma bigo_const_mult2: "O(\<lambda>x. c * f x) \<subseteq> O(f)"
  by (metis bigo_elt_subset bigo_const_mult1)

lemma bigo_const_mult3: "c \<noteq> 0 \<Longrightarrow> f \<in> O(\<lambda>x. c * f x)"
  for c :: "'a::linordered_field"
  by (simp add: bigo_def) (metis abs_mult field_class.field_divide_inverse mult.commute nonzero_divide_eq_eq order_refl)

lemma bigo_const_mult4: "c \<noteq> 0 \<Longrightarrow> O(f) \<subseteq> O(\<lambda>x. c * f x)"
  for c :: "'a::linordered_field"
  by (simp add: bigo_const_mult3 bigo_elt_subset)

lemma bigo_const_mult [simp]: "c \<noteq> 0 \<Longrightarrow> O(\<lambda>x. c * f x) = O(f)"
  for c :: "'a::linordered_field"
  by (simp add: bigo_const_mult2 bigo_const_mult4 subset_antisym)

lemma bigo_const_mult5 [simp]: "(\<lambda>x. c) *o O(f) = O(f)" if "c \<noteq> 0"
  for c :: "'a::linordered_field"
proof
  show "O(f) \<subseteq> (\<lambda>x. c) *o O(f)"
    using that
    apply (clarsimp simp add: bigo_def elt_set_times_def func_times)
    apply (rule_tac x = "\<lambda>y. inverse c * x y" in exI)
    apply (simp add: mult.assoc [symmetric] abs_mult)
    apply (rule_tac x = "\<bar>inverse c\<bar> * ca" in exI)
    apply auto
    done
  have "O(\<lambda>x. c * f x) \<subseteq> O(f)"
    by (simp add: bigo_const_mult2)
  then show "(\<lambda>x. c) *o O(f) \<subseteq> O(f)"
    using order_trans[OF bigo_mult2] by (force simp add: times_fun_def)
qed


lemma bigo_const_mult6 [intro]: "(\<lambda>x. c) *o O(f) \<subseteq> O(f)"
  apply (auto intro!: simp add: bigo_def elt_set_times_def func_times)
  apply (rule_tac x = "ca * \<bar>c\<bar>" in exI)
  by (smt (verit, ccfv_SIG) ab_semigroup_mult_class.mult_ac(1) abs_abs abs_le_self_iff abs_mult le_cases3 mult.commute mult_left_mono)

lemma bigo_const_mult7 [intro]:
  assumes *: "f =o O(g)"
  shows "(\<lambda>x. c * f x) =o O(g)"
proof -
  from * have "(\<lambda>x. c) * f =o (\<lambda>x. c) *o O(g)"
    by auto
  also have "(\<lambda>x. c) * f = (\<lambda>x. c * f x)"
    by (simp add: func_times)
  also have "(\<lambda>x. c) *o O(g) \<subseteq> O(g)"
    by (auto del: subsetI)
  finally show ?thesis .
qed

lemma bigo_compose1: "f =o O(g) \<Longrightarrow> (\<lambda>x. f (k x)) =o O(\<lambda>x. g (k x))"
  by (auto simp: bigo_def)

lemma bigo_compose2: "f =o g +o O(h) \<Longrightarrow> (\<lambda>x. f (k x)) =o (\<lambda>x. g (k x)) +o O(\<lambda>x. h(k x))"
  by (smt (verit, best) set_minus_plus bigo_def fun_diff_def mem_Collect_eq)


subsection \<open>Sum\<close>

lemma bigo_sum_main:
  assumes "\<forall>x. \<forall>y \<in> A x. 0 \<le> h x y" and "\<forall>x. \<forall>y \<in> A x. \<bar>f x y\<bar> \<le> c * h x y"
  shows "(\<lambda>x. \<Sum>y \<in> A x. f x y) =o O(\<lambda>x. \<Sum>y \<in> A x. h x y)"
proof -
  have "(\<Sum>i\<in>A x. \<bar>f x i\<bar>) \<le> \<bar>c\<bar> * sum (h x) (A x)" for x
    by (smt (verit, ccfv_threshold) assms abs_mult_pos abs_of_nonneg abs_of_nonpos dual_order.trans le_cases3 neg_0_le_iff_le sum_distrib_left sum_mono)
  then show ?thesis
    using assms by (fastforce simp add: bigo_def sum_nonneg intro: order_trans [OF sum_abs])
qed

lemma bigo_sum1: "\<forall>x y. 0 \<le> h x y \<Longrightarrow>
    \<exists>c. \<forall>x y. \<bar>f x y\<bar> \<le> c * h x y \<Longrightarrow>
      (\<lambda>x. \<Sum>y \<in> A x. f x y) =o O(\<lambda>x. \<Sum>y \<in> A x. h x y)"
  by (metis (no_types) bigo_sum_main)

lemma bigo_sum2: "\<forall>y. 0 \<le> h y \<Longrightarrow>
    \<exists>c. \<forall>y. \<bar>f y\<bar> \<le> c * (h y) \<Longrightarrow>
      (\<lambda>x. \<Sum>y \<in> A x. f y) =o O(\<lambda>x. \<Sum>y \<in> A x. h y)"
  by (rule bigo_sum1) auto

lemma bigo_sum3: "f =o O(h) \<Longrightarrow>
    (\<lambda>x. \<Sum>y \<in> A x. l x y * f (k x y)) =o O(\<lambda>x. \<Sum>y \<in> A x. \<bar>l x y * h (k x y)\<bar>)"
  apply (rule bigo_sum1)
  using abs_ge_zero apply blast
  apply (clarsimp simp: bigo_def)
  by (smt (verit, ccfv_threshold) abs_mult abs_not_less_zero mult.left_commute mult_le_cancel_left)

lemma bigo_sum4: "f =o g +o O(h) \<Longrightarrow>
    (\<lambda>x. \<Sum>y \<in> A x. l x y * f (k x y)) =o
      (\<lambda>x. \<Sum>y \<in> A x. l x y * g (k x y)) +o
        O(\<lambda>x. \<Sum>y \<in> A x. \<bar>l x y * h (k x y)\<bar>)"
  using bigo_sum3 [of "f-g" h l k A]
  apply (simp add: algebra_simps sum_subtractf)
  by (smt (verit) bigo_alt_def minus_apply set_minus_imp_plus set_plus_imp_minus mem_Collect_eq)

lemma bigo_sum5: "f =o O(h) \<Longrightarrow> \<forall>x y. 0 \<le> l x y \<Longrightarrow>
    \<forall>x. 0 \<le> h x \<Longrightarrow>
      (\<lambda>x. \<Sum>y \<in> A x. l x y * f (k x y)) =o
        O(\<lambda>x. \<Sum>y \<in> A x. l x y * h (k x y))"
  using bigo_sum3 [of f h l k A] by simp

lemma bigo_sum6: "f =o g +o O(h) \<Longrightarrow> \<forall>x y. 0 \<le> l x y \<Longrightarrow>
    \<forall>x. 0 \<le> h x \<Longrightarrow>
      (\<lambda>x. \<Sum>y \<in> A x. l x y * f (k x y)) =o
        (\<lambda>x. \<Sum>y \<in> A x. l x y * g (k x y)) +o
          O(\<lambda>x. \<Sum>y \<in> A x. l x y * h (k x y))"
  using bigo_sum5 [of "f-g" h l k A]
  apply (simp add: algebra_simps sum_subtractf)
  by (smt (verit, del_insts) bigo_alt_def set_minus_imp_plus minus_apply set_plus_imp_minus mem_Collect_eq)


subsection \<open>Misc useful stuff\<close>

lemma bigo_useful_add: "f =o O(h) \<Longrightarrow> g =o O(h) \<Longrightarrow> f + g =o O(h)"
  using bigo_plus_idemp set_plus_intro by blast

lemma bigo_useful_const_mult: "c \<noteq> 0 \<Longrightarrow> (\<lambda>x. c) * f =o O(h) \<Longrightarrow> f =o O(h)"
  for c :: "'a::linordered_field"
  using bigo_elt_subset bigo_mult6 by fastforce

lemma bigo_fix: "(\<lambda>x::nat. f (x + 1)) =o O(\<lambda>x. h (x + 1)) \<Longrightarrow> f 0 = 0 \<Longrightarrow> f =o O(h)"
  by (simp add: bigo_alt_def) (metis abs_eq_0_iff abs_ge_zero abs_mult abs_of_pos not0_implies_Suc)

lemma bigo_fix2:
  "(\<lambda>x. f ((x::nat) + 1)) =o (\<lambda>x. g(x + 1)) +o O(\<lambda>x. h(x + 1)) \<Longrightarrow>
       f 0 = g 0 \<Longrightarrow> f =o g +o O(h)"
  apply (rule set_minus_imp_plus [OF bigo_fix])
   apply (smt (verit, del_insts) bigo_alt_def fun_diff_def set_plus_imp_minus mem_Collect_eq)
  apply simp
  done


subsection \<open>Less than or equal to\<close>

definition lesso :: "('a \<Rightarrow> 'b::linordered_idom) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"  (infixl \<open><o\<close> 70)
  where "f <o g = (\<lambda>x. max (f x - g x) 0)"

lemma bigo_lesseq1: "f =o O(h) \<Longrightarrow> \<forall>x. \<bar>g x\<bar> \<le> \<bar>f x\<bar> \<Longrightarrow> g =o O(h)"
  by (smt (verit, del_insts) bigo_def mem_Collect_eq order_trans)

lemma bigo_lesseq2: "f =o O(h) \<Longrightarrow> \<forall>x. \<bar>g x\<bar> \<le> f x \<Longrightarrow> g =o O(h)"
  by (metis (mono_tags, lifting) abs_ge_zero abs_of_nonneg bigo_lesseq1 dual_order.trans)

lemma bigo_lesseq3: "f =o O(h) \<Longrightarrow> \<forall>x. 0 \<le> g x \<Longrightarrow> \<forall>x. g x \<le> f x \<Longrightarrow> g =o O(h)"
  by (meson bigo_bounded bigo_elt_subset subsetD)

lemma bigo_lesseq4: "f =o O(h) \<Longrightarrow> \<forall>x. 0 \<le> g x \<Longrightarrow> \<forall>x. g x \<le> \<bar>f x\<bar> \<Longrightarrow> g =o O(h)"
  by (metis abs_of_nonneg bigo_lesseq1)

lemma bigo_lesso1: "\<forall>x. f x \<le> g x \<Longrightarrow> f <o g =o O(h)"
  by (smt (verit, del_insts) abs_ge_zero add_0 bigo_abs3 bigo_bounded diff_le_eq lesso_def max_def order_refl)

lemma bigo_lesso2: "f =o g +o O(h) \<Longrightarrow> \<forall>x. 0 \<le> k x \<Longrightarrow> \<forall>x. k x \<le> f x \<Longrightarrow> k <o g =o O(h)"
  unfolding lesso_def
  apply (rule bigo_lesseq4 [of "f-g"])
    apply (erule set_plus_imp_minus)
  using max.cobounded2 apply blast
  by (smt (verit) abs_ge_zero abs_of_nonneg diff_ge_0_iff_ge diff_mono diff_self fun_diff_def order_refl max.coboundedI2 max_def)

lemma bigo_lesso3: "f =o g +o O(h) \<Longrightarrow> \<forall>x. 0 \<le> k x \<Longrightarrow> \<forall>x. g x \<le> k x \<Longrightarrow> f <o k =o O(h)"
  unfolding lesso_def
  apply (rule bigo_lesseq4 [of "f-g"])
    apply (erule set_plus_imp_minus)
  using max.cobounded2 apply blast
  by (smt (verit) abs_eq_iff abs_ge_zero abs_if abs_minus_le_zero diff_left_mono fun_diff_def le_max_iff_disj order.trans order_eq_refl)

lemma bigo_lesso4:
  fixes k :: "'a \<Rightarrow> 'b::linordered_field"
  assumes f: "f <o g =o O(k)" and g: "g =o h +o O(k)"
  shows "f <o h =o O(k)"
proof -
  have "g - h \<in> O(k)"
    by (simp add: g set_plus_imp_minus)
  then have "(\<lambda>x. \<bar>g x - h x\<bar>) \<in> O(k)"
    using bigo_abs5 by force
  then have \<section>: "(\<lambda>x. max (f x - g x) 0) + (\<lambda>x. \<bar>g x - h x\<bar>) \<in> O(k)"
    by (metis (mono_tags, lifting) bigo_lesseq1 bigo_useful_add dual_order.eq_iff f lesso_def)
  have "\<bar>max (f x - h x) 0\<bar> \<le> ((\<lambda>x. max (f x - g x) 0) + (\<lambda>x. \<bar>g x - h x\<bar>)) x" for x
    by (auto simp add: func_plus fun_diff_def algebra_simps split: split_max abs_split)
  then show ?thesis
    by (smt (verit, ccfv_SIG) \<section> bigo_lesseq2 lesso_def)
qed


lemma bigo_lesso5:
  assumes "f <o g =o O(h)" shows "\<exists>C. \<forall>x. f x \<le> g x + C * \<bar>h x\<bar>"
proof -
  obtain c where "0 < c" and c: "\<And>x. f x - g x \<le> c * \<bar>h x\<bar>"
    using assms by (auto simp: lesso_def bigo_alt_def)
  have "\<bar>max (f x - g x) 0\<bar> = max (f x - g x) 0" for x
    by (auto simp add: algebra_simps)
  then show ?thesis
    by (metis c add.commute diff_le_eq)
qed

lemma lesso_add: "f <o g =o O(h) \<Longrightarrow> k <o l =o O(h) \<Longrightarrow> (f + k) <o (g + l) =o O(h)"
  unfolding lesso_def
  using bigo_useful_add by (fastforce split: split_max intro: bigo_lesseq3)

lemma bigo_LIMSEQ1: "f \<longlonglongrightarrow> 0" if f: "f =o O(g)" and g: "g \<longlonglongrightarrow> 0"
  for f g :: "nat \<Rightarrow> real"
proof -
  { fix r::real
    assume "0 < r"
    obtain c::real where "0 < c"  and rc: "\<And>x. \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>"
      using f by (auto simp: LIMSEQ_iff bigo_alt_def)
    with g \<open>0 < r\<close> obtain no where "\<forall>n\<ge>no. \<bar>g n\<bar> < r/c"
      by (fastforce simp: LIMSEQ_iff)
    then have "\<exists>no. \<forall>n\<ge>no. \<bar>f n\<bar> < r"
      by (metis \<open>0 < c\<close> mult.commute order_le_less_trans pos_less_divide_eq rc) }
  then show ?thesis
    by (auto simp: LIMSEQ_iff)
qed

lemma bigo_LIMSEQ2:
  fixes f g :: "nat \<Rightarrow> real"
  assumes "f =o g +o O(h)" "h \<longlonglongrightarrow> 0" and f: "f \<longlonglongrightarrow> a"
  shows  "g \<longlonglongrightarrow> a"
proof -
  have "f - g \<longlonglongrightarrow> 0"
    using assms bigo_LIMSEQ1 set_plus_imp_minus by blast
  then have "(\<lambda>n. f n - g n) \<longlonglongrightarrow> 0"
    by (simp add: fun_diff_def)
  then show ?thesis
    using Lim_transform_eq f by blast
qed

end
