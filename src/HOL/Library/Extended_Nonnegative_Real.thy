(*  Title:      HOL/Library/Extended_Nonnegative_Real.thy
    Author:     Johannes Hölzl
*)

subsection \<open>The type of non-negative extended real numbers\<close>

theory Extended_Nonnegative_Real
  imports Extended_Real Indicator_Function
begin

lemma ereal_ineq_diff_add:
  assumes "b \<noteq> (-\<infinity>::ereal)" "a \<ge> b"
  shows "a = b + (a-b)"
by (metis add.commute assms ereal_eq_minus_iff ereal_minus_le_iff ereal_plus_eq_PInfty)

lemma Limsup_const_add:
  fixes c :: "'a::{complete_linorder, linorder_topology, topological_monoid_add, ordered_ab_semigroup_add}"
  shows "F \<noteq> bot \<Longrightarrow> Limsup F (\<lambda>x. c + f x) = c + Limsup F f"
  by (rule Limsup_compose_continuous_mono)
     (auto intro!: monoI add_mono continuous_on_add continuous_on_id continuous_on_const)

lemma Liminf_const_add:
  fixes c :: "'a::{complete_linorder, linorder_topology, topological_monoid_add, ordered_ab_semigroup_add}"
  shows "F \<noteq> bot \<Longrightarrow> Liminf F (\<lambda>x. c + f x) = c + Liminf F f"
  by (rule Liminf_compose_continuous_mono)
     (auto intro!: monoI add_mono continuous_on_add continuous_on_id continuous_on_const)

lemma Liminf_add_const:
  fixes c :: "'a::{complete_linorder, linorder_topology, topological_monoid_add, ordered_ab_semigroup_add}"
  shows "F \<noteq> bot \<Longrightarrow> Liminf F (\<lambda>x. f x + c) = Liminf F f + c"
  by (rule Liminf_compose_continuous_mono)
     (auto intro!: monoI add_mono continuous_on_add continuous_on_id continuous_on_const)

lemma sums_offset:
  fixes f g :: "nat \<Rightarrow> 'a :: {t2_space, topological_comm_monoid_add}"
  assumes "(\<lambda>n. f (n + i)) sums l" shows "f sums (l + (\<Sum>j<i. f j))"
proof  -
  have "(\<lambda>k. (\<Sum>n<k. f (n + i)) + (\<Sum>j<i. f j)) \<longlonglongrightarrow> l + (\<Sum>j<i. f j)"
    using assms by (auto intro!: tendsto_add simp: sums_def)
  moreover
  { fix k :: nat
    have "(\<Sum>j<k + i. f j) = (\<Sum>j=i..<k + i. f j) + (\<Sum>j=0..<i. f j)"
      by (subst sum.union_disjoint[symmetric]) (auto intro!: sum.cong)
    also have "(\<Sum>j=i..<k + i. f j) = (\<Sum>j\<in>(\<lambda>n. n + i)`{0..<k}. f j)"
      unfolding image_add_atLeastLessThan by simp
    finally have "(\<Sum>j<k + i. f j) = (\<Sum>n<k. f (n + i)) + (\<Sum>j<i. f j)"
      by (auto simp: inj_on_def atLeast0LessThan sum.reindex) }
  ultimately have "(\<lambda>k. (\<Sum>n<k + i. f n)) \<longlonglongrightarrow> l + (\<Sum>j<i. f j)"
    by simp
  then show ?thesis
    unfolding sums_def by (rule LIMSEQ_offset)
qed

lemma suminf_offset:
  fixes f g :: "nat \<Rightarrow> 'a :: {t2_space, topological_comm_monoid_add}"
  shows "summable (\<lambda>j. f (j + i)) \<Longrightarrow> suminf f = (\<Sum>j. f (j + i)) + (\<Sum>j<i. f j)"
  by (intro sums_unique[symmetric] sums_offset summable_sums)

lemma eventually_at_left_1: "(\<And>z::real. 0 < z \<Longrightarrow> z < 1 \<Longrightarrow> P z) \<Longrightarrow> eventually P (at_left 1)"
  by (subst eventually_at_left[of 0]) (auto intro: exI[of _ 0])

lemma mult_eq_1:
  fixes a b :: "'a :: {ordered_semiring, comm_monoid_mult}"
  shows "0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> b \<le> 1 \<Longrightarrow> a * b = 1 \<longleftrightarrow> (a = 1 \<and> b = 1)"
  by (metis mult.left_neutral eq_iff mult.commute mult_right_mono)

lemma ereal_add_diff_cancel:
  fixes a b :: ereal
  shows "\<bar>b\<bar> \<noteq> \<infinity> \<Longrightarrow> (a + b) - b = a"
  by (cases a b rule: ereal2_cases) auto

lemma add_top:
  fixes x :: "'a::{order_top, ordered_comm_monoid_add}"
  shows "0 \<le> x \<Longrightarrow> x + top = top"
  by (intro top_le add_increasing order_refl)

lemma top_add:
  fixes x :: "'a::{order_top, ordered_comm_monoid_add}"
  shows "0 \<le> x \<Longrightarrow> top + x = top"
  by (intro top_le add_increasing2 order_refl)

lemma le_lfp: "mono f \<Longrightarrow> x \<le> lfp f \<Longrightarrow> f x \<le> lfp f"
  by (subst lfp_unfold) (auto dest: monoD)

lemma lfp_transfer:
  assumes \<alpha>: "sup_continuous \<alpha>" and f: "sup_continuous f" and mg: "mono g"
  assumes bot: "\<alpha> bot \<le> lfp g" and eq: "\<And>x. x \<le> lfp f \<Longrightarrow> \<alpha> (f x) = g (\<alpha> x)"
  shows "\<alpha> (lfp f) = lfp g"
proof (rule antisym)
  note mf = sup_continuous_mono[OF f]
  have f_le_lfp: "(f ^^ i) bot \<le> lfp f" for i
    by (induction i) (auto intro: le_lfp mf)

  have "\<alpha> ((f ^^ i) bot) \<le> lfp g" for i
    by (induction i) (auto simp: bot eq f_le_lfp intro!: le_lfp mg)
  then show "\<alpha> (lfp f) \<le> lfp g"
    unfolding sup_continuous_lfp[OF f]
    by (subst \<alpha>[THEN sup_continuousD])
       (auto intro!: mono_funpow sup_continuous_mono[OF f] SUP_least)

  show "lfp g \<le> \<alpha> (lfp f)"
    by (rule lfp_lowerbound) (simp add: eq[symmetric] lfp_fixpoint[OF mf])
qed

lemma sup_continuous_applyD: "sup_continuous f \<Longrightarrow> sup_continuous (\<lambda>x. f x h)"
  using sup_continuous_apply[THEN sup_continuous_compose] .

lemma sup_continuous_SUP[order_continuous_intros]:
  fixes M :: "_ \<Rightarrow> _ \<Rightarrow> 'a::complete_lattice"
  assumes M: "\<And>i. i \<in> I \<Longrightarrow> sup_continuous (M i)"
  shows  "sup_continuous (SUP i\<in>I. M i)"
  unfolding sup_continuous_def by (auto simp add: sup_continuousD [OF M] image_comp intro: SUP_commute)

lemma sup_continuous_apply_SUP[order_continuous_intros]:
  fixes M :: "_ \<Rightarrow> _ \<Rightarrow> 'a::complete_lattice"
  shows "(\<And>i. i \<in> I \<Longrightarrow> sup_continuous (M i)) \<Longrightarrow> sup_continuous (\<lambda>x. SUP i\<in>I. M i x)"
  unfolding SUP_apply[symmetric] by (rule sup_continuous_SUP)

lemma sup_continuous_lfp'[order_continuous_intros]:
  assumes 1: "sup_continuous f"
  assumes 2: "\<And>g. sup_continuous g \<Longrightarrow> sup_continuous (f g)"
  shows "sup_continuous (lfp f)"
proof -
  have "sup_continuous ((f ^^ i) bot)" for i
  proof (induction i)
    case (Suc i) then show ?case
      by (auto intro!: 2)
  qed (simp add: bot_fun_def sup_continuous_const)
  then show ?thesis
    unfolding sup_continuous_lfp[OF 1] by (intro order_continuous_intros)
qed

lemma sup_continuous_lfp''[order_continuous_intros]:
  assumes 1: "\<And>s. sup_continuous (f s)"
  assumes 2: "\<And>g. sup_continuous g \<Longrightarrow> sup_continuous (\<lambda>s. f s (g s))"
  shows "sup_continuous (\<lambda>x. lfp (f x))"
proof -
  have "sup_continuous (\<lambda>x. (f x ^^ i) bot)" for i
  proof (induction i)
    case (Suc i) then show ?case
      by (auto intro!: 2)
  qed (simp add: bot_fun_def sup_continuous_const)
  then show ?thesis
    unfolding sup_continuous_lfp[OF 1] by (intro order_continuous_intros)
qed

lemma mono_INF_fun:
    "(\<And>x y. mono (F x y)) \<Longrightarrow> mono (\<lambda>z x. INF y \<in> X x. F x y z :: 'a :: complete_lattice)"
  by (auto intro!: INF_mono[OF bexI] simp: le_fun_def mono_def)

lemma continuous_on_cmult_ereal:
  "\<bar>c::ereal\<bar> \<noteq> \<infinity> \<Longrightarrow> continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>x. c * f x)"
  using tendsto_cmult_ereal[of c f "f x" "at x within A" for x]
  by (auto simp: continuous_on_def simp del: tendsto_cmult_ereal)

lemma real_of_nat_Sup:
  assumes "A \<noteq> {}" "bdd_above A"
  shows "of_nat (Sup A) = (SUP a\<in>A. of_nat a :: real)"
proof (intro antisym)
  show "(SUP a\<in>A. of_nat a::real) \<le> of_nat (Sup A)"
    using assms by (intro cSUP_least of_nat_mono) (auto intro: cSup_upper)
  have "Sup A \<in> A"
    using assms by (auto simp: Sup_nat_def bdd_above_nat)
  then show "of_nat (Sup A) \<le> (SUP a\<in>A. of_nat a::real)"
    by (intro cSUP_upper bdd_above_image_mono assms) (auto simp: mono_def)
qed

lemma (in complete_lattice) SUP_sup_const1:
  "I \<noteq> {} \<Longrightarrow> (SUP i\<in>I. sup c (f i)) = sup c (SUP i\<in>I. f i)"
  using SUP_sup_distrib[of "\<lambda>_. c" I f] by simp

lemma (in complete_lattice) SUP_sup_const2:
  "I \<noteq> {} \<Longrightarrow> (SUP i\<in>I. sup (f i) c) = sup (SUP i\<in>I. f i) c"
  using SUP_sup_distrib[of f I "\<lambda>_. c"] by simp

lemma one_less_of_natD:
  assumes "(1::'a::linordered_semidom) < of_nat n" shows "1 < n"
  by (cases n) (use assms in auto)

subsection \<open>Defining the extended non-negative reals\<close>

text \<open>Basic definitions and type class setup\<close>

typedef ennreal = "{x :: ereal. 0 \<le> x}"
  morphisms enn2ereal e2ennreal'
  by auto

definition "e2ennreal x = e2ennreal' (max 0 x)"

lemma enn2ereal_range: "e2ennreal ` {0..} = UNIV"
proof -
  have "\<exists>y\<ge>0. x = e2ennreal y" for x
    by (cases x) (auto simp: e2ennreal_def max_absorb2)
  then show ?thesis
    by (auto simp: image_iff Bex_def)
qed

lemma type_definition_ennreal': "type_definition enn2ereal e2ennreal {x. 0 \<le> x}"
  using type_definition_ennreal
  by (auto simp: type_definition_def e2ennreal_def max_absorb2)

setup_lifting type_definition_ennreal'

declare [[coercion e2ennreal]]

instantiation ennreal :: complete_linorder
begin

lift_definition top_ennreal :: ennreal is top by (rule top_greatest)
lift_definition bot_ennreal :: ennreal is 0 by (rule order_refl)
lift_definition sup_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> ennreal" is sup by (rule le_supI1)
lift_definition inf_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> ennreal" is inf by (rule le_infI)

lift_definition Inf_ennreal :: "ennreal set \<Rightarrow> ennreal" is "Inf"
  by (rule Inf_greatest)

lift_definition Sup_ennreal :: "ennreal set \<Rightarrow> ennreal" is "sup 0 \<circ> Sup"
  by auto

lift_definition less_eq_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> bool" is "(<)" .

instance
  by standard
     (transfer ; auto simp: Inf_lower Inf_greatest Sup_upper Sup_least le_max_iff_disj max.absorb1)+

end

lemma pcr_ennreal_enn2ereal[simp]: "pcr_ennreal (enn2ereal x) x"
  by (simp add: ennreal.pcr_cr_eq cr_ennreal_def)

lemma rel_fun_eq_pcr_ennreal: "rel_fun (=) pcr_ennreal f g \<longleftrightarrow> f = enn2ereal \<circ> g"
  by (auto simp: rel_fun_def ennreal.pcr_cr_eq cr_ennreal_def)

instantiation ennreal :: infinity
begin

definition infinity_ennreal :: ennreal
where
  [simp]: "\<infinity> = (top::ennreal)"

instance ..

end

instantiation ennreal :: "{semiring_1_no_zero_divisors, comm_semiring_1}"
begin

lift_definition one_ennreal :: ennreal is 1 by simp
lift_definition zero_ennreal :: ennreal is 0 by simp
lift_definition plus_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> ennreal" is "(+)" by simp
lift_definition times_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> ennreal" is "(*)" by simp

instance
  by standard (transfer; auto simp: field_simps ereal_right_distrib)+

end

instantiation ennreal :: minus
begin

lift_definition minus_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> ennreal" is "\<lambda>a b. max 0 (a - b)"
  by simp

instance ..

end

instance ennreal :: numeral ..

instantiation ennreal :: inverse
begin

lift_definition inverse_ennreal :: "ennreal \<Rightarrow> ennreal" is inverse
  by (rule inverse_ereal_ge0I)

definition divide_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> ennreal"
  where "x div y = x * inverse (y :: ennreal)"

instance ..

end

lemma ennreal_zero_less_one: "0 < (1::ennreal)" \<comment> \<open>TODO: remove\<close>
  by transfer auto

instance ennreal :: dioid
proof (standard; transfer)
  fix a b :: ereal assume "0 \<le> a" "0 \<le> b" then show "(a \<le> b) = (\<exists>c\<in>Collect ((\<le>) 0). b = a + c)"
    unfolding ereal_ex_split Bex_def
    by (cases a b rule: ereal2_cases) (auto intro!: exI[of _ "real_of_ereal (b - a)"])
qed

instance ennreal :: ordered_comm_semiring
  by standard
     (transfer ; auto intro: add_mono mult_mono mult_ac ereal_left_distrib ereal_mult_left_mono)+

instance ennreal :: linordered_nonzero_semiring
proof
  fix a b::ennreal
  show "a < b \<Longrightarrow> a + 1 < b + 1"
    by transfer (simp add: add_right_mono ereal_add_cancel_right less_le)
qed (transfer; simp)

instance ennreal :: strict_ordered_ab_semigroup_add
proof
  fix a b c d :: ennreal show "a < b \<Longrightarrow> c < d \<Longrightarrow> a + c < b + d"
    by transfer (auto intro!: ereal_add_strict_mono)
qed

declare [[coercion "of_nat :: nat \<Rightarrow> ennreal"]]

lemma e2ennreal_neg: "x \<le> 0 \<Longrightarrow> e2ennreal x = 0"
  unfolding zero_ennreal_def e2ennreal_def by (simp add: max_absorb1)

lemma e2ennreal_mono: "x \<le> y \<Longrightarrow> e2ennreal x \<le> e2ennreal y"
  by (cases "0 \<le> x" "0 \<le> y" rule: bool.exhaust[case_product bool.exhaust])
     (auto simp: e2ennreal_neg less_eq_ennreal.abs_eq eq_onp_def)

lemma enn2ereal_nonneg[simp]: "0 \<le> enn2ereal x"
  using ennreal.enn2ereal[of x] by simp

lemma ereal_ennreal_cases:
  obtains b where "0 \<le> a" "a = enn2ereal b" | "a < 0"
  using e2ennreal'_inverse[of a, symmetric] by (cases "0 \<le> a") (auto intro: enn2ereal_nonneg)

lemma rel_fun_liminf[transfer_rule]: "rel_fun (rel_fun (=) pcr_ennreal) pcr_ennreal liminf liminf"
proof -
  have "rel_fun (rel_fun (=) pcr_ennreal) pcr_ennreal (\<lambda>x. sup 0 (liminf x)) liminf"
    unfolding liminf_SUP_INF[abs_def] by (transfer_prover_start, transfer_step+; simp)
  then show ?thesis
    apply (subst (asm) (2) rel_fun_def)
    apply (subst (2) rel_fun_def)
    apply (auto simp: comp_def max.absorb2 Liminf_bounded rel_fun_eq_pcr_ennreal)
    done
qed

lemma rel_fun_limsup[transfer_rule]: "rel_fun (rel_fun (=) pcr_ennreal) pcr_ennreal limsup limsup"
proof -
  have "rel_fun (rel_fun (=) pcr_ennreal) pcr_ennreal (\<lambda>x. INF n. sup 0 (SUP i\<in>{n..}. x i)) limsup"
    unfolding limsup_INF_SUP[abs_def] by (transfer_prover_start, transfer_step+; simp)
  then show ?thesis
    unfolding limsup_INF_SUP[abs_def]
    apply (subst (asm) (2) rel_fun_def)
    apply (subst (2) rel_fun_def)
    apply (auto simp: comp_def max.absorb2 Sup_upper2 rel_fun_eq_pcr_ennreal)
    apply (subst (asm) max.absorb2)
    apply (auto intro: SUP_upper2)
    done
qed

lemma sum_enn2ereal[simp]: "(\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> (\<Sum>i\<in>I. enn2ereal (f i)) = enn2ereal (sum f I)"
  by (induction I rule: infinite_finite_induct) (auto simp: sum_nonneg zero_ennreal.rep_eq plus_ennreal.rep_eq)

lemma transfer_e2ennreal_sum [transfer_rule]:
  "rel_fun (rel_fun (=) pcr_ennreal) (rel_fun (=) pcr_ennreal) sum sum"
  by (auto intro!: rel_funI simp: rel_fun_eq_pcr_ennreal comp_def)

lemma enn2ereal_of_nat[simp]: "enn2ereal (of_nat n) = ereal n"
  by (induction n) (auto simp: zero_ennreal.rep_eq one_ennreal.rep_eq plus_ennreal.rep_eq)

lemma enn2ereal_numeral[simp]: "enn2ereal (numeral a) = numeral a"
  by (metis enn2ereal_of_nat numeral_eq_ereal of_nat_numeral)

lemma transfer_numeral[transfer_rule]: "pcr_ennreal (numeral a) (numeral a)"
  unfolding cr_ennreal_def pcr_ennreal_def by auto

subsection \<open>Cancellation simprocs\<close>

lemma ennreal_add_left_cancel: "a + b = a + c \<longleftrightarrow> a = (\<infinity>::ennreal) \<or> b = c"
  unfolding infinity_ennreal_def by transfer (simp add: top_ereal_def ereal_add_cancel_left)

lemma ennreal_add_left_cancel_le: "a + b \<le> a + c \<longleftrightarrow> a = (\<infinity>::ennreal) \<or> b \<le> c"
  unfolding infinity_ennreal_def by transfer (simp add: ereal_add_le_add_iff top_ereal_def disj_commute)

lemma ereal_add_left_cancel_less:
  fixes a b c :: ereal
  shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a + b < a + c \<longleftrightarrow> a \<noteq> \<infinity> \<and> b < c"
  by (cases a b c rule: ereal3_cases) auto

lemma ennreal_add_left_cancel_less: "a + b < a + c \<longleftrightarrow> a \<noteq> (\<infinity>::ennreal) \<and> b < c"
  unfolding infinity_ennreal_def
  by transfer (simp add: top_ereal_def ereal_add_left_cancel_less)

ML \<open>
structure Cancel_Ennreal_Common =
struct
  (* copied from src/HOL/Tools/nat_numeral_simprocs.ML *)
  fun find_first_t _    _ []         = raise TERM("find_first_t", [])
    | find_first_t past u (t::terms) =
          if u aconv t then (rev past @ terms)
          else find_first_t (t::past) u terms

  fun dest_summing (Const (\<^const_name>\<open>Groups.plus\<close>, _) $ t $ u, ts) =
        dest_summing (t, dest_summing (u, ts))
    | dest_summing (t, ts) = t :: ts

  val mk_sum = Arith_Data.long_mk_sum
  fun dest_sum t = dest_summing (t, [])
  val find_first = find_first_t []
  val trans_tac = Numeral_Simprocs.trans_tac
  val norm_ss =
    simpset_of (put_simpset HOL_basic_ss \<^context>
      addsimps @{thms ac_simps add_0_left add_0_right})
  fun norm_tac ctxt = ALLGOALS (simp_tac (put_simpset norm_ss ctxt))
  fun simplify_meta_eq ctxt cancel_th th =
    Arith_Data.simplify_meta_eq [] ctxt
      ([th, cancel_th] MRS trans)
  fun mk_eq (a, b) = HOLogic.mk_Trueprop (HOLogic.mk_eq (a, b))
end

structure Eq_Ennreal_Cancel = ExtractCommonTermFun
(open Cancel_Ennreal_Common
  val mk_bal = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>HOL.eq\<close> \<^typ>\<open>ennreal\<close>
  fun simp_conv _ _ = SOME @{thm ennreal_add_left_cancel}
)

structure Le_Ennreal_Cancel = ExtractCommonTermFun
(open Cancel_Ennreal_Common
  val mk_bal = HOLogic.mk_binrel \<^const_name>\<open>Orderings.less_eq\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Orderings.less_eq\<close> \<^typ>\<open>ennreal\<close>
  fun simp_conv _ _ = SOME @{thm ennreal_add_left_cancel_le}
)

structure Less_Ennreal_Cancel = ExtractCommonTermFun
(open Cancel_Ennreal_Common
  val mk_bal = HOLogic.mk_binrel \<^const_name>\<open>Orderings.less\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Orderings.less\<close> \<^typ>\<open>ennreal\<close>
  fun simp_conv _ _ = SOME @{thm ennreal_add_left_cancel_less}
)
\<close>

simproc_setup ennreal_eq_cancel
  ("(l::ennreal) + m = n" | "(l::ennreal) = m + n") =
  \<open>fn phi => fn ctxt => fn ct => Eq_Ennreal_Cancel.proc ctxt (Thm.term_of ct)\<close>

simproc_setup ennreal_le_cancel
  ("(l::ennreal) + m \<le> n" | "(l::ennreal) \<le> m + n") =
  \<open>fn phi => fn ctxt => fn ct => Le_Ennreal_Cancel.proc ctxt (Thm.term_of ct)\<close>

simproc_setup ennreal_less_cancel
  ("(l::ennreal) + m < n" | "(l::ennreal) < m + n") =
  \<open>fn phi => fn ctxt => fn ct => Less_Ennreal_Cancel.proc ctxt (Thm.term_of ct)\<close>


subsection \<open>Order with top\<close>

lemma ennreal_zero_less_top[simp]: "0 < (top::ennreal)"
  by transfer (simp add: top_ereal_def)

lemma ennreal_one_less_top[simp]: "1 < (top::ennreal)"
  by transfer (simp add: top_ereal_def)

lemma ennreal_zero_neq_top[simp]: "0 \<noteq> (top::ennreal)"
  by transfer (simp add: top_ereal_def)

lemma ennreal_top_neq_zero[simp]: "(top::ennreal) \<noteq> 0"
  by transfer (simp add: top_ereal_def)

lemma ennreal_top_neq_one[simp]: "top \<noteq> (1::ennreal)"
  by transfer (simp add: top_ereal_def one_ereal_def flip: ereal_max)

lemma ennreal_one_neq_top[simp]: "1 \<noteq> (top::ennreal)"
  by transfer (simp add: top_ereal_def one_ereal_def flip: ereal_max)

lemma ennreal_add_less_top[simp]:
  fixes a b :: ennreal
  shows "a + b < top \<longleftrightarrow> a < top \<and> b < top"
  by transfer (auto simp: top_ereal_def)

lemma ennreal_add_eq_top[simp]:
  fixes a b :: ennreal
  shows "a + b = top \<longleftrightarrow> a = top \<or> b = top"
  by transfer (auto simp: top_ereal_def)

lemma ennreal_sum_less_top[simp]:
  fixes f :: "'a \<Rightarrow> ennreal"
  shows "finite I \<Longrightarrow> (\<Sum>i\<in>I. f i) < top \<longleftrightarrow> (\<forall>i\<in>I. f i < top)"
  by (induction I rule: finite_induct) auto

lemma ennreal_sum_eq_top[simp]:
  fixes f :: "'a \<Rightarrow> ennreal"
  shows "finite I \<Longrightarrow> (\<Sum>i\<in>I. f i) = top \<longleftrightarrow> (\<exists>i\<in>I. f i = top)"
  by (induction I rule: finite_induct) auto

lemma ennreal_mult_eq_top_iff:
  fixes a b :: ennreal
  shows "a * b = top \<longleftrightarrow> (a = top \<and> b \<noteq> 0) \<or> (b = top \<and> a \<noteq> 0)"
  by transfer (auto simp: top_ereal_def)

lemma ennreal_top_eq_mult_iff:
  fixes a b :: ennreal
  shows "top = a * b \<longleftrightarrow> (a = top \<and> b \<noteq> 0) \<or> (b = top \<and> a \<noteq> 0)"
  using ennreal_mult_eq_top_iff[of a b] by auto

lemma ennreal_mult_less_top:
  fixes a b :: ennreal
  shows "a * b < top \<longleftrightarrow> (a = 0 \<or> b = 0 \<or> (a < top \<and> b < top))"
  by transfer (auto simp add: top_ereal_def)

lemma top_power_ennreal: "top ^ n = (if n = 0 then 1 else top :: ennreal)"
  by (induction n) (simp_all add: ennreal_mult_eq_top_iff)

lemma ennreal_prod_eq_0[simp]:
  fixes f :: "'a \<Rightarrow> ennreal"
  shows "(prod f A = 0) = (finite A \<and> (\<exists>i\<in>A. f i = 0))"
  by (induction A rule: infinite_finite_induct) auto

lemma ennreal_prod_eq_top:
  fixes f :: "'a \<Rightarrow> ennreal"
  shows "(\<Prod>i\<in>I. f i) = top \<longleftrightarrow> (finite I \<and> ((\<forall>i\<in>I. f i \<noteq> 0) \<and> (\<exists>i\<in>I. f i = top)))"
  by (induction I rule: infinite_finite_induct) (auto simp: ennreal_mult_eq_top_iff)

lemma ennreal_top_mult: "top * a = (if a = 0 then 0 else top :: ennreal)"
  by (simp add: ennreal_mult_eq_top_iff)

lemma ennreal_mult_top: "a * top = (if a = 0 then 0 else top :: ennreal)"
  by (simp add: ennreal_mult_eq_top_iff)

lemma enn2ereal_eq_top_iff[simp]: "enn2ereal x = \<infinity> \<longleftrightarrow> x = top"
  by transfer (simp add: top_ereal_def)

lemma enn2ereal_top[simp]: "enn2ereal top = \<infinity>"
  by transfer (simp add: top_ereal_def)

lemma e2ennreal_infty[simp]: "e2ennreal \<infinity> = top"
  by (simp add: top_ennreal.abs_eq top_ereal_def)

lemma ennreal_top_minus[simp]: "top - x = (top::ennreal)"
  by transfer (auto simp: top_ereal_def max_def)

lemma minus_top_ennreal: "x - top = (if x = top then top else 0:: ennreal)"
  by transfer (use ereal_eq_minus_iff top_ereal_def in force)

lemma bot_ennreal: "bot = (0::ennreal)"
  by transfer rule

lemma ennreal_of_nat_neq_top[simp]: "of_nat i \<noteq> (top::ennreal)"
  by (induction i) auto

lemma numeral_eq_of_nat: "(numeral a::ennreal) = of_nat (numeral a)"
  by simp

lemma of_nat_less_top: "of_nat i < (top::ennreal)"
  using less_le_trans[of "of_nat i" "of_nat (Suc i)" "top::ennreal"]
  by simp

lemma top_neq_numeral[simp]: "top \<noteq> (numeral i::ennreal)"
  using of_nat_less_top[of "numeral i"] by simp

lemma ennreal_numeral_less_top[simp]: "numeral i < (top::ennreal)"
  using of_nat_less_top[of "numeral i"] by simp

lemma ennreal_add_bot[simp]: "bot + x = (x::ennreal)"
  by transfer simp

lemma add_top_right_ennreal [simp]: "x + top = (top :: ennreal)"
  by (cases x) auto

lemma add_top_left_ennreal [simp]: "top + x = (top :: ennreal)"
  by (cases x) auto

lemma ennreal_top_mult_left [simp]: "x \<noteq> 0 \<Longrightarrow> x * top = (top :: ennreal)"
  by (subst ennreal_mult_eq_top_iff) auto

lemma ennreal_top_mult_right [simp]: "x \<noteq> 0 \<Longrightarrow> top * x = (top :: ennreal)"
  by (subst ennreal_mult_eq_top_iff) auto


lemma power_top_ennreal [simp]: "n > 0 \<Longrightarrow> top ^ n = (top :: ennreal)"
  by (induction n) auto

lemma power_eq_top_ennreal_iff: "x ^ n = top \<longleftrightarrow> x = (top :: ennreal) \<and> n > 0"
  by (induction n) (auto simp: ennreal_mult_eq_top_iff)

lemma ennreal_mult_le_mult_iff: "c \<noteq> 0 \<Longrightarrow> c \<noteq> top \<Longrightarrow> c * a \<le> c * b \<longleftrightarrow> a \<le> (b :: ennreal)"
  including ennreal.lifting
  by (transfer, subst ereal_mult_le_mult_iff) (auto simp: top_ereal_def)

lemma power_mono_ennreal: "x \<le> y \<Longrightarrow> x ^ n \<le> (y ^ n :: ennreal)"
  by (induction n) (auto intro!: mult_mono)

instance ennreal :: semiring_char_0
proof (standard, safe intro!: linorder_injI)
  have *: "1 + of_nat k \<noteq> (0::ennreal)" for k
    using add_pos_nonneg[OF zero_less_one, of "of_nat k :: ennreal"] by auto
  fix x y :: nat assume "x < y" "of_nat x = (of_nat y::ennreal)" then show False
    by (auto simp add: less_iff_Suc_add *)
qed

subsection \<open>Arithmetic\<close>

lemma ennreal_minus_zero[simp]: "a - (0::ennreal) = a"
  by transfer (auto simp: max_def)

lemma ennreal_add_diff_cancel_right[simp]:
  fixes x y z :: ennreal shows "y \<noteq> top \<Longrightarrow> (x + y) - y = x"
  by transfer (metis ereal_eq_minus_iff max_absorb2 not_MInfty_nonneg top_ereal_def)

lemma ennreal_add_diff_cancel_left[simp]:
  fixes x y z :: ennreal shows "y \<noteq> top \<Longrightarrow> (y + x) - y = x"
  by (simp add: add.commute)

lemma
  fixes a b :: ennreal
  shows "a - b = 0 \<Longrightarrow> a \<le> b"
  by transfer (metis ereal_diff_gr0 le_cases max.absorb2 not_less)

lemma ennreal_minus_cancel:
  fixes a b c :: ennreal
  shows "c \<noteq> top \<Longrightarrow> a \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> c - a = c - b \<Longrightarrow> a = b"
  apply transfer
  subgoal for a b c
    by (cases a b c rule: ereal3_cases)
       (auto simp: top_ereal_def max_def split: if_splits)
  done

lemma sup_const_add_ennreal:
  fixes a b c :: "ennreal"
  shows "sup (c + a) (c + b) = c + sup a b"
  by transfer (metis add_left_mono le_cases sup.absorb2 sup.orderE)

lemma ennreal_diff_add_assoc:
  fixes a b c :: ennreal
  shows "a \<le> b \<Longrightarrow> c + b - a = c + (b - a)"
  apply transfer
  subgoal for a b c
    by (cases a b c rule: ereal3_cases) (auto simp: field_simps max_absorb2)
  done

lemma mult_divide_eq_ennreal:
  fixes a b :: ennreal
  shows "b \<noteq> 0 \<Longrightarrow> b \<noteq> top \<Longrightarrow> (a * b) / b = a"
  unfolding divide_ennreal_def
  apply transfer
  apply (subst mult.assoc)
  apply (simp add: top_ereal_def flip: divide_ereal_def)
  done

lemma divide_mult_eq: "a \<noteq> 0 \<Longrightarrow> a \<noteq> \<infinity> \<Longrightarrow> x * a / (b * a) = x / (b::ennreal)"
  unfolding divide_ennreal_def infinity_ennreal_def
  apply transfer
  subgoal for a b c
    apply (cases a b c rule: ereal3_cases)
    apply (auto simp: top_ereal_def)
    done
  done

lemma ennreal_mult_divide_eq:
  fixes a b :: ennreal
  shows "b \<noteq> 0 \<Longrightarrow> b \<noteq> top \<Longrightarrow> (a * b) / b = a"
  unfolding divide_ennreal_def
  apply transfer
  apply (subst mult.assoc)
  apply (simp add: top_ereal_def flip: divide_ereal_def)
  done

lemma ennreal_add_diff_cancel:
  fixes a b :: ennreal
  shows "b \<noteq> \<infinity> \<Longrightarrow> (a + b) - b = a"
  unfolding infinity_ennreal_def
  by transfer (simp add: max_absorb2 top_ereal_def ereal_add_diff_cancel)

lemma ennreal_minus_eq_0:
  "a - b = 0 \<Longrightarrow> a \<le> (b::ennreal)"
  by transfer (metis ereal_diff_gr0 le_cases max.absorb2 not_less)

lemma ennreal_mono_minus_cancel:
  fixes a b c :: ennreal
  shows "a - b \<le> a - c \<Longrightarrow> a < top \<Longrightarrow> b \<le> a \<Longrightarrow> c \<le> a \<Longrightarrow> c \<le> b"
  by transfer
     (auto simp add: max.absorb2 ereal_diff_positive top_ereal_def dest: ereal_mono_minus_cancel)

lemma ennreal_mono_minus:
  fixes a b c :: ennreal
  shows "c \<le> b \<Longrightarrow> a - b \<le> a - c"
  by transfer (meson ereal_minus_mono max.mono order_refl)

lemma ennreal_minus_pos_iff:
  fixes a b :: ennreal
  shows "a < top \<or> b < top \<Longrightarrow> 0 < a - b \<Longrightarrow> b < a"
  by transfer (use add.left_neutral ereal_minus_le_iff less_irrefl not_less in fastforce)

lemma ennreal_inverse_top[simp]: "inverse top = (0::ennreal)"
  by transfer (simp add: top_ereal_def ereal_inverse_eq_0)

lemma ennreal_inverse_zero[simp]: "inverse 0 = (top::ennreal)"
  by transfer (simp add: top_ereal_def ereal_inverse_eq_0)

lemma ennreal_top_divide: "top / (x::ennreal) = (if x = top then 0 else top)"
  unfolding divide_ennreal_def
  by transfer (simp add: top_ereal_def ereal_inverse_eq_0 ereal_0_gt_inverse)

lemma ennreal_zero_divide[simp]: "0 / (x::ennreal) = 0"
  by (simp add: divide_ennreal_def)

lemma ennreal_divide_zero[simp]: "x / (0::ennreal) = (if x = 0 then 0 else top)"
  by (simp add: divide_ennreal_def ennreal_mult_top)

lemma ennreal_divide_top[simp]: "x / (top::ennreal) = 0"
  by (simp add: divide_ennreal_def ennreal_top_mult)

lemma ennreal_times_divide: "a * (b / c) = a * b / (c::ennreal)"
  unfolding divide_ennreal_def
  by transfer (simp add: divide_ereal_def[symmetric] ereal_times_divide_eq)

lemma ennreal_zero_less_divide: "0 < a / b \<longleftrightarrow> (0 < a \<and> b < (top::ennreal))"
  unfolding divide_ennreal_def
  by transfer (auto simp: ereal_zero_less_0_iff top_ereal_def ereal_0_gt_inverse)

lemma add_divide_distrib_ennreal: "(a + b) / c = a / c + b / (c :: ennreal)"
  by (simp add: divide_ennreal_def ring_distribs)

lemma divide_right_mono_ennreal:
  fixes a b c :: ennreal
  shows "a \<le> b \<Longrightarrow> a / c \<le> b / c"
  unfolding divide_ennreal_def by (intro mult_mono) auto

lemma ennreal_mult_strict_right_mono: "(a::ennreal) < c \<Longrightarrow> 0 < b \<Longrightarrow> b < top \<Longrightarrow> a * b < c * b"
  by transfer (auto intro!: ereal_mult_strict_right_mono)

lemma ennreal_indicator_less[simp]:
  "indicator A x \<le> (indicator B x::ennreal) \<longleftrightarrow> (x \<in> A \<longrightarrow> x \<in> B)"
  by (simp add: indicator_def not_le)

lemma ennreal_inverse_positive: "0 < inverse x \<longleftrightarrow> (x::ennreal) \<noteq> top"
  by transfer (simp add: ereal_0_gt_inverse top_ereal_def)

lemma ennreal_inverse_mult': "((0 < b \<or> a < top) \<and> (0 < a \<or> b < top)) \<Longrightarrow> inverse (a * b::ennreal) = inverse a * inverse b"
  apply transfer
  subgoal for a b
    by (cases a b rule: ereal2_cases) (auto simp: top_ereal_def)
  done

lemma ennreal_inverse_mult: "a < top \<Longrightarrow> b < top \<Longrightarrow> inverse (a * b::ennreal) = inverse a * inverse b"
  apply transfer
  subgoal for a b
    by (cases a b rule: ereal2_cases) (auto simp: top_ereal_def)
  done

lemma ennreal_inverse_1[simp]: "inverse (1::ennreal) = 1"
  by transfer simp

lemma ennreal_inverse_eq_0_iff[simp]: "inverse (a::ennreal) = 0 \<longleftrightarrow> a = top"
  by transfer (simp add: ereal_inverse_eq_0 top_ereal_def)

lemma ennreal_inverse_eq_top_iff[simp]: "inverse (a::ennreal) = top \<longleftrightarrow> a = 0"
  by transfer (simp add: top_ereal_def)

lemma ennreal_divide_eq_0_iff[simp]: "(a::ennreal) / b = 0 \<longleftrightarrow> (a = 0 \<or> b = top)"
  by (simp add: divide_ennreal_def)

lemma ennreal_divide_eq_top_iff: "(a::ennreal) / b = top \<longleftrightarrow> ((a \<noteq> 0 \<and> b = 0) \<or> (a = top \<and> b \<noteq> top))"
  by (auto simp add: divide_ennreal_def ennreal_mult_eq_top_iff)

lemma one_divide_one_divide_ennreal[simp]: "1 / (1 / c) = (c::ennreal)"
  including ennreal.lifting
  unfolding divide_ennreal_def
  by transfer auto

lemma ennreal_mult_left_cong:
  "((a::ennreal) \<noteq> 0 \<Longrightarrow> b = c) \<Longrightarrow> a * b = a * c"
  by (cases "a = 0") simp_all

lemma ennreal_mult_right_cong:
  "((a::ennreal) \<noteq> 0 \<Longrightarrow> b = c) \<Longrightarrow> b * a = c * a"
  by (cases "a = 0") simp_all

lemma ennreal_zero_less_mult_iff: "0 < a * b \<longleftrightarrow> 0 < a \<and> 0 < (b::ennreal)"
  by transfer (auto simp add: ereal_zero_less_0_iff le_less)

lemma less_diff_eq_ennreal:
  fixes a b c :: ennreal
  shows "b < top \<or> c < top \<Longrightarrow> a < b - c \<longleftrightarrow> a + c < b"
  apply transfer
  subgoal for a b c
    by (cases a b c rule: ereal3_cases) (auto split: split_max)
  done

lemma diff_add_cancel_ennreal:
  fixes a b :: ennreal shows "a \<le> b \<Longrightarrow> b - a + a = b"
  unfolding infinity_ennreal_def
  by transfer (metis (no_types) add.commute ereal_diff_positive ereal_ineq_diff_add max_def not_MInfty_nonneg)

lemma ennreal_diff_self[simp]: "a \<noteq> top \<Longrightarrow> a - a = (0::ennreal)"
  by transfer (simp add: top_ereal_def)

lemma ennreal_minus_mono:
  fixes a b c :: ennreal
  shows "a \<le> c \<Longrightarrow> d \<le> b \<Longrightarrow> a - b \<le> c - d"
  by transfer (meson ereal_minus_mono max.mono order_refl)

lemma ennreal_minus_eq_top[simp]: "a - (b::ennreal) = top \<longleftrightarrow> a = top"
  by transfer (auto simp: top_ereal_def max.absorb2 ereal_minus_eq_PInfty_iff split: split_max)

lemma ennreal_divide_self[simp]: "a \<noteq> 0 \<Longrightarrow> a < top \<Longrightarrow> a / a = (1::ennreal)"
  unfolding divide_ennreal_def
  apply transfer
  subgoal for a
    by (cases a) (auto simp: top_ereal_def)
  done

subsection \<open>Coercion from \<^typ>\<open>real\<close> to \<^typ>\<open>ennreal\<close>\<close>

lift_definition ennreal :: "real \<Rightarrow> ennreal" is "sup 0 \<circ> ereal"
  by simp

declare [[coercion ennreal]]

lemma ennreal_cong: "x = y \<Longrightarrow> ennreal x = ennreal y" by simp

lemma ennreal_cases[cases type: ennreal]:
  fixes x :: ennreal
  obtains (real) r :: real where "0 \<le> r" "x = ennreal r" | (top) "x = top"
  apply transfer
  subgoal for x thesis
    by (cases x) (auto simp: max.absorb2 top_ereal_def)
  done

lemmas ennreal2_cases = ennreal_cases[case_product ennreal_cases]
lemmas ennreal3_cases = ennreal_cases[case_product ennreal2_cases]

lemma ennreal_neq_top[simp]: "ennreal r \<noteq> top"
  by transfer (simp add: top_ereal_def zero_ereal_def flip: ereal_max)

lemma top_neq_ennreal[simp]: "top \<noteq> ennreal r"
  using ennreal_neq_top[of r] by (auto simp del: ennreal_neq_top)

lemma ennreal_less_top[simp]: "ennreal x < top"
  by transfer (simp add: top_ereal_def max_def)

lemma ennreal_neg: "x \<le> 0 \<Longrightarrow> ennreal x = 0"
  by transfer (simp add: max.absorb1)

lemma ennreal_inj[simp]:
  "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> ennreal a = ennreal b \<longleftrightarrow> a = b"
  by (transfer fixing: a b) (auto simp: max_absorb2)

lemma ennreal_le_iff[simp]: "0 \<le> y \<Longrightarrow> ennreal x \<le> ennreal y \<longleftrightarrow> x \<le> y"
  by (auto simp: ennreal_def zero_ereal_def less_eq_ennreal.abs_eq eq_onp_def split: split_max)

lemma le_ennreal_iff: "0 \<le> r \<Longrightarrow> x \<le> ennreal r \<longleftrightarrow> (\<exists>q\<ge>0. x = ennreal q \<and> q \<le> r)"
  by (cases x) (auto simp: top_unique)

lemma ennreal_less_iff: "0 \<le> r \<Longrightarrow> ennreal r < ennreal q \<longleftrightarrow> r < q"
  unfolding not_le[symmetric] by auto

lemma ennreal_eq_zero_iff[simp]: "0 \<le> x \<Longrightarrow> ennreal x = 0 \<longleftrightarrow> x = 0"
  by transfer (auto simp: max_absorb2)

lemma ennreal_less_zero_iff[simp]: "0 < ennreal x \<longleftrightarrow> 0 < x"
  by transfer (auto simp: max_def)

lemma ennreal_lessI: "0 < q \<Longrightarrow> r < q \<Longrightarrow> ennreal r < ennreal q"
  by (cases "0 \<le> r") (auto simp: ennreal_less_iff ennreal_neg)

lemma ennreal_leI: "x \<le> y \<Longrightarrow> ennreal x \<le> ennreal y"
  by (cases "0 \<le> y") (auto simp: ennreal_neg)

lemma enn2ereal_ennreal[simp]: "0 \<le> x \<Longrightarrow> enn2ereal (ennreal x) = x"
  by transfer (simp add: max_absorb2)

lemma e2ennreal_enn2ereal[simp]: "e2ennreal (enn2ereal x) = x"
  by (simp add: e2ennreal_def max_absorb2 ennreal.enn2ereal_inverse)

lemma enn2ereal_e2ennreal: "x \<ge> 0 \<Longrightarrow> enn2ereal (e2ennreal x) = x"
by (metis e2ennreal_enn2ereal ereal_ennreal_cases not_le)

lemma e2ennreal_ereal [simp]: "e2ennreal (ereal x) = ennreal x"
by (metis e2ennreal_def enn2ereal_inverse ennreal.rep_eq sup_ereal_def)

lemma ennreal_0[simp]: "ennreal 0 = 0"
  by (simp add: ennreal_def max.absorb1 zero_ennreal.abs_eq)

lemma ennreal_1[simp]: "ennreal 1 = 1"
  by transfer (simp add: max_absorb2)

lemma ennreal_eq_0_iff: "ennreal x = 0 \<longleftrightarrow> x \<le> 0"
  by (cases "0 \<le> x") (auto simp: ennreal_neg)

lemma ennreal_le_iff2: "ennreal x \<le> ennreal y \<longleftrightarrow> ((0 \<le> y \<and> x \<le> y) \<or> (x \<le> 0 \<and> y \<le> 0))"
  by (cases "0 \<le> y") (auto simp: ennreal_eq_0_iff ennreal_neg)

lemma ennreal_eq_1[simp]: "ennreal x = 1 \<longleftrightarrow> x = 1"
  by (cases "0 \<le> x") (auto simp: ennreal_neg simp flip: ennreal_1)

lemma ennreal_le_1[simp]: "ennreal x \<le> 1 \<longleftrightarrow> x \<le> 1"
  by (cases "0 \<le> x") (auto simp: ennreal_neg simp flip: ennreal_1)

lemma ennreal_ge_1[simp]: "ennreal x \<ge> 1 \<longleftrightarrow> x \<ge> 1"
  by (cases "0 \<le> x") (auto simp: ennreal_neg simp flip: ennreal_1)

lemma one_less_ennreal[simp]: "1 < ennreal x \<longleftrightarrow> 1 < x"
  by transfer (auto simp: max.absorb2 less_max_iff_disj)

lemma ennreal_plus[simp]:
  "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> ennreal (a + b) = ennreal a + ennreal b"
  by (transfer fixing: a b) (auto simp: max_absorb2)

lemma add_mono_ennreal: "x < ennreal y \<Longrightarrow> x' < ennreal y' \<Longrightarrow> x + x' < ennreal (y + y')"
  by (metis (full_types) add_strict_mono ennreal_less_zero_iff ennreal_plus less_le not_less zero_le)

lemma sum_ennreal[simp]: "(\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> (\<Sum>i\<in>I. ennreal (f i)) = ennreal (sum f I)"
  by (induction I rule: infinite_finite_induct) (auto simp: sum_nonneg)

lemma sum_list_ennreal[simp]:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x \<ge> 0"
  shows   "sum_list (map (\<lambda>x. ennreal (f x)) xs) = ennreal (sum_list (map f xs))"
using assms
proof (induction xs)
  case (Cons x xs)
  from Cons have "(\<Sum>x\<leftarrow>x # xs. ennreal (f x)) = ennreal (f x) + ennreal (sum_list (map f xs))"
    by simp
  also from Cons.prems have "\<dots> = ennreal (f x + sum_list (map f xs))"
    by (intro ennreal_plus [symmetric] sum_list_nonneg) auto
  finally show ?case by simp
qed simp_all

lemma ennreal_of_nat_eq_real_of_nat: "of_nat i = ennreal (of_nat i)"
  by (induction i) simp_all

lemma of_nat_le_ennreal_iff[simp]: "0 \<le> r \<Longrightarrow> of_nat i \<le> ennreal r \<longleftrightarrow> of_nat i \<le> r"
  by (simp add: ennreal_of_nat_eq_real_of_nat)

lemma ennreal_le_of_nat_iff[simp]: "ennreal r \<le> of_nat i \<longleftrightarrow> r \<le> of_nat i"
  by (simp add: ennreal_of_nat_eq_real_of_nat)

lemma ennreal_indicator: "ennreal (indicator A x) = indicator A x"
  by (auto split: split_indicator)

lemma ennreal_numeral[simp]: "ennreal (numeral n) = numeral n"
  using ennreal_of_nat_eq_real_of_nat[of "numeral n"] by simp

lemma ennreal_less_numeral_iff [simp]: "ennreal n < numeral w \<longleftrightarrow> n < numeral w"
  by (metis ennreal_less_iff ennreal_numeral less_le not_less zero_less_numeral)

lemma numeral_less_ennreal_iff [simp]: "numeral w < ennreal n \<longleftrightarrow> numeral w < n"
  using ennreal_less_iff zero_le_numeral by fastforce

lemma numeral_le_ennreal_iff [simp]: "numeral n \<le> ennreal m \<longleftrightarrow> numeral n \<le> m"
  by (metis not_le ennreal_less_numeral_iff)

lemma min_ennreal: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> min (ennreal x) (ennreal y) = ennreal (min x y)"
  by (auto split: split_min)

lemma ennreal_half[simp]: "ennreal (1/2) = inverse 2"
  by transfer (simp add: max.absorb2)

lemma ennreal_minus: "0 \<le> q \<Longrightarrow> ennreal r - ennreal q = ennreal (r - q)"
  by transfer
     (simp add: max.absorb2 zero_ereal_def flip: ereal_max)

lemma ennreal_minus_top[simp]: "ennreal a - top = 0"
  by (simp add: minus_top_ennreal)

lemma e2eenreal_enn2ereal_diff [simp]:
  "e2ennreal(enn2ereal x - enn2ereal y) = x - y" for x y
by (cases x, cases y, auto simp add: ennreal_minus e2ennreal_neg)

lemma ennreal_mult: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> ennreal (a * b) = ennreal a * ennreal b"
  by transfer (simp add: max_absorb2)

lemma ennreal_mult': "0 \<le> a \<Longrightarrow> ennreal (a * b) = ennreal a * ennreal b"
  by (cases "0 \<le> b") (auto simp: ennreal_mult ennreal_neg mult_nonneg_nonpos)

lemma indicator_mult_ennreal: "indicator A x * ennreal r = ennreal (indicator A x * r)"
  by (simp split: split_indicator)

lemma ennreal_mult'': "0 \<le> b \<Longrightarrow> ennreal (a * b) = ennreal a * ennreal b"
  by (cases "0 \<le> a") (auto simp: ennreal_mult ennreal_neg mult_nonpos_nonneg)

lemma numeral_mult_ennreal: "0 \<le> x \<Longrightarrow> numeral b * ennreal x = ennreal (numeral b * x)"
  by (simp add: ennreal_mult)

lemma ennreal_power: "0 \<le> r \<Longrightarrow> ennreal r ^ n = ennreal (r ^ n)"
  by (induction n) (auto simp: ennreal_mult)

lemma power_eq_top_ennreal: "x ^ n = top \<longleftrightarrow> (n \<noteq> 0 \<and> (x::ennreal) = top)"
  by (cases x rule: ennreal_cases)
     (auto simp: ennreal_power top_power_ennreal)

lemma inverse_ennreal: "0 < r \<Longrightarrow> inverse (ennreal r) = ennreal (inverse r)"
  by transfer (simp add: max.absorb2)

lemma divide_ennreal: "0 \<le> r \<Longrightarrow> 0 < q \<Longrightarrow> ennreal r / ennreal q = ennreal (r / q)"
  by (simp add: divide_ennreal_def inverse_ennreal ennreal_mult[symmetric] inverse_eq_divide)

lemma ennreal_inverse_power: "inverse (x ^ n :: ennreal) = inverse x ^ n"
proof (cases x rule: ennreal_cases)
  case top with power_eq_top_ennreal[of x n] show ?thesis
    by (cases "n = 0") auto
next
  case (real r) then show ?thesis
  proof cases
    assume "x = 0" then show ?thesis
      using power_eq_top_ennreal[of top "n - 1"]
      by (cases n) (auto simp: ennreal_top_mult)
  next
    assume "x \<noteq> 0"
    with real have "0 < r" by auto
    with real show ?thesis
      by (induction n)
         (auto simp add: ennreal_power ennreal_mult[symmetric] inverse_ennreal)
  qed
qed

lemma power_divide_distrib_ennreal [algebra_simps]:
  "(x / y) ^ n = x ^ n / (y ^ n :: ennreal)"
  by (simp add: divide_ennreal_def algebra_simps ennreal_inverse_power)

lemma ennreal_divide_numeral: "0 \<le> x \<Longrightarrow> ennreal x / numeral b = ennreal (x / numeral b)"
  by (subst divide_ennreal[symmetric]) auto

lemma prod_ennreal: "(\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> (\<Prod>i\<in>A. ennreal (f i)) = ennreal (prod f A)"
  by (induction A rule: infinite_finite_induct)
     (auto simp: ennreal_mult prod_nonneg)

lemma prod_mono_ennreal:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<le> (g x :: ennreal)"
  shows   "prod f A \<le> prod g A"
  using assms by (induction A rule: infinite_finite_induct) (auto intro!: mult_mono)

lemma mult_right_ennreal_cancel: "a * ennreal c = b * ennreal c \<longleftrightarrow> (a = b \<or> c \<le> 0)"
proof (cases "0 \<le> c")
  case True
  then show ?thesis
    by (metis ennreal_eq_0_iff ennreal_mult_right_cong ennreal_neq_top mult_divide_eq_ennreal)
qed (use ennreal_neg in auto)

lemma ennreal_le_epsilon:
  "(\<And>e::real. y < top \<Longrightarrow> 0 < e \<Longrightarrow> x \<le> y + ennreal e) \<Longrightarrow> x \<le> y"
  apply (cases y rule: ennreal_cases)
  apply (cases x rule: ennreal_cases)
  apply (auto simp flip: ennreal_plus simp add: top_unique intro: zero_less_one field_le_epsilon)
  done

lemma ennreal_rat_dense:
  fixes x y :: ennreal
  shows "x < y \<Longrightarrow> \<exists>r::rat. x < real_of_rat r \<and> real_of_rat r < y"
proof transfer
  fix x y :: ereal assume xy: "0 \<le> x" "0 \<le> y" "x < y"
  moreover
  from ereal_dense3[OF \<open>x < y\<close>]
  obtain r where r: "x < ereal (real_of_rat r)" "ereal (real_of_rat r) < y"
    by auto
  then have "0 \<le> r"
    using le_less_trans[OF \<open>0 \<le> x\<close> \<open>x < ereal (real_of_rat r)\<close>] by auto
  with r show "\<exists>r. x < (sup 0 \<circ> ereal) (real_of_rat r) \<and> (sup 0 \<circ> ereal) (real_of_rat r) < y"
    by (intro exI[of _ r]) (auto simp: max_absorb2)
qed

lemma ennreal_Ex_less_of_nat: "(x::ennreal) < top \<Longrightarrow> \<exists>n. x < of_nat n"
  by (cases x rule: ennreal_cases)
     (auto simp: ennreal_of_nat_eq_real_of_nat ennreal_less_iff reals_Archimedean2)

subsection \<open>Coercion from \<^typ>\<open>ennreal\<close> to \<^typ>\<open>real\<close>\<close>

definition "enn2real x = real_of_ereal (enn2ereal x)"

lemma enn2real_nonneg[simp]: "0 \<le> enn2real x"
  by (auto simp: enn2real_def intro!: real_of_ereal_pos enn2ereal_nonneg)

lemma enn2real_mono: "a \<le> b \<Longrightarrow> b < top \<Longrightarrow> enn2real a \<le> enn2real b"
  by (auto simp add: enn2real_def less_eq_ennreal.rep_eq intro!: real_of_ereal_positive_mono enn2ereal_nonneg)

lemma enn2real_of_nat[simp]: "enn2real (of_nat n) = n"
  by (auto simp: enn2real_def)

lemma enn2real_ennreal[simp]: "0 \<le> r \<Longrightarrow> enn2real (ennreal r) = r"
  by (simp add: enn2real_def)

lemma ennreal_enn2real[simp]: "r < top \<Longrightarrow> ennreal (enn2real r) = r"
  by (cases r rule: ennreal_cases) auto

lemma real_of_ereal_enn2ereal[simp]: "real_of_ereal (enn2ereal x) = enn2real x"
  by (simp add: enn2real_def)

lemma enn2real_top[simp]: "enn2real top = 0"
  unfolding enn2real_def top_ennreal.rep_eq top_ereal_def by simp

lemma enn2real_0[simp]: "enn2real 0 = 0"
  unfolding enn2real_def zero_ennreal.rep_eq by simp

lemma enn2real_1[simp]: "enn2real 1 = 1"
  unfolding enn2real_def one_ennreal.rep_eq by simp

lemma enn2real_numeral[simp]: "enn2real (numeral n) = (numeral n)"
  unfolding enn2real_def by simp

lemma enn2real_mult: "enn2real (a * b) = enn2real a * enn2real b"
  unfolding enn2real_def
  by (simp del: real_of_ereal_enn2ereal add: times_ennreal.rep_eq)

lemma enn2real_leI: "0 \<le> B \<Longrightarrow> x \<le> ennreal B \<Longrightarrow> enn2real x \<le> B"
  by (cases x rule: ennreal_cases) (auto simp: top_unique)

lemma enn2real_positive_iff: "0 < enn2real x \<longleftrightarrow> (0 < x \<and> x < top)"
  by (cases x rule: ennreal_cases) auto

lemma enn2real_eq_posreal_iff[simp]: "c > 0 \<Longrightarrow> enn2real x = c \<longleftrightarrow> x = c"
  by (cases x) auto

lemma ennreal_enn2real_if: "ennreal (enn2real r) = (if r = top then 0 else r)"
  by(auto intro!: ennreal_enn2real simp add: less_top)

subsection \<open>Coercion from \<^typ>\<open>enat\<close> to \<^typ>\<open>ennreal\<close>\<close>


definition ennreal_of_enat :: "enat \<Rightarrow> ennreal"
where
  "ennreal_of_enat n = (case n of \<infinity> \<Rightarrow> top | enat n \<Rightarrow> of_nat n)"

declare [[coercion ennreal_of_enat]]
declare [[coercion "of_nat :: nat \<Rightarrow> ennreal"]]

lemma ennreal_of_enat_infty[simp]: "ennreal_of_enat \<infinity> = \<infinity>"
  by (simp add: ennreal_of_enat_def)

lemma ennreal_of_enat_enat[simp]: "ennreal_of_enat (enat n) = of_nat n"
  by (simp add: ennreal_of_enat_def)

lemma ennreal_of_enat_0[simp]: "ennreal_of_enat 0 = 0"
  using ennreal_of_enat_enat[of 0] unfolding enat_0 by simp

lemma ennreal_of_enat_1[simp]: "ennreal_of_enat 1 = 1"
  using ennreal_of_enat_enat[of 1] unfolding enat_1 by simp

lemma ennreal_top_neq_of_nat[simp]: "(top::ennreal) \<noteq> of_nat i"
  using ennreal_of_nat_neq_top[of i] by metis

lemma ennreal_of_enat_inj[simp]: "ennreal_of_enat i = ennreal_of_enat j \<longleftrightarrow> i = j"
  by (cases i j rule: enat.exhaust[case_product enat.exhaust]) auto

lemma ennreal_of_enat_le_iff[simp]: "ennreal_of_enat m \<le> ennreal_of_enat n \<longleftrightarrow> m \<le> n"
  by (auto simp: ennreal_of_enat_def top_unique split: enat.split)

lemma of_nat_less_ennreal_of_nat[simp]: "of_nat n \<le> ennreal_of_enat x \<longleftrightarrow> of_nat n \<le> x"
  by (cases x) (auto simp: of_nat_eq_enat)

lemma ennreal_of_enat_Sup: "ennreal_of_enat (Sup X) = (SUP x\<in>X. ennreal_of_enat x)"
proof -
  have "ennreal_of_enat (Sup X) \<le> (SUP x \<in> X. ennreal_of_enat x)"
    unfolding Sup_enat_def
  proof (clarsimp, intro conjI impI)
    fix x assume "finite X" "X \<noteq> {}"
    then show "ennreal_of_enat (Max X) \<le> (SUP x \<in> X. ennreal_of_enat x)"
      by (intro SUP_upper Max_in)
  next
    assume "infinite X" "X \<noteq> {}"
    have "\<exists>y\<in>X. r < ennreal_of_enat y" if r: "r < top" for r
    proof -
      from ennreal_Ex_less_of_nat[OF r] guess n .. note n = this
      have "\<not> (X \<subseteq> enat ` {.. n})"
        using \<open>infinite X\<close> by (auto dest: finite_subset)
      then obtain x where x: "x \<in> X" "x \<notin> enat ` {..n}"
        by blast
      then have "of_nat n \<le> x"
        by (cases x) (auto simp: of_nat_eq_enat)
      with x show ?thesis
        by (auto intro!: bexI[of _ x] less_le_trans[OF n])
    qed
    then have "(SUP x \<in> X. ennreal_of_enat x) = top"
      by simp
    then show "top \<le> (SUP x \<in> X. ennreal_of_enat x)"
      unfolding top_unique by simp
  qed
  then show ?thesis
    by (auto intro!: antisym Sup_least intro: Sup_upper)
qed

lemma ennreal_of_enat_eSuc[simp]: "ennreal_of_enat (eSuc x) = 1 + ennreal_of_enat x"
  by (cases x) (auto simp: eSuc_enat)

subsection \<open>Topology on \<^typ>\<open>ennreal\<close>\<close>

lemma enn2ereal_Iio: "enn2ereal -` {..<a} = (if 0 \<le> a then {..< e2ennreal a} else {})"
  using enn2ereal_nonneg
  by (cases a rule: ereal_ennreal_cases)
     (auto simp add: vimage_def set_eq_iff ennreal.enn2ereal_inverse less_ennreal.rep_eq e2ennreal_def max_absorb2
           simp del: enn2ereal_nonneg
           intro: le_less_trans less_imp_le)

lemma enn2ereal_Ioi: "enn2ereal -` {a <..} = (if 0 \<le> a then {e2ennreal a <..} else UNIV)"
  by (cases a rule: ereal_ennreal_cases)
     (auto simp add: vimage_def set_eq_iff ennreal.enn2ereal_inverse less_ennreal.rep_eq e2ennreal_def max_absorb2
           intro: less_le_trans)

instantiation ennreal :: linear_continuum_topology
begin

definition open_ennreal :: "ennreal set \<Rightarrow> bool"
  where "(open :: ennreal set \<Rightarrow> bool) = generate_topology (range lessThan \<union> range greaterThan)"

instance
proof
  show "\<exists>a b::ennreal. a \<noteq> b"
    using zero_neq_one by (intro exI)
  show "\<And>x y::ennreal. x < y \<Longrightarrow> \<exists>z>x. z < y"
  proof transfer
    fix x y :: ereal assume "0 \<le> x" and *: "x < y"
    moreover from dense[OF *] guess z ..
    ultimately show "\<exists>z\<in>Collect ((\<le>) 0). x < z \<and> z < y"
      by (intro bexI[of _ z]) auto
  qed
qed (rule open_ennreal_def)

end

lemma continuous_on_e2ennreal: "continuous_on A e2ennreal"
proof (rule continuous_on_subset)
  show "continuous_on ({0..} \<union> {..0}) e2ennreal"
  proof (rule continuous_on_closed_Un)
    show "continuous_on {0 ..} e2ennreal"
      by (rule continuous_onI_mono)
         (auto simp add: less_eq_ennreal.abs_eq eq_onp_def enn2ereal_range)
    show "continuous_on {.. 0} e2ennreal"
      by (subst continuous_on_cong[OF refl, of _ _ "\<lambda>_. 0"])
         (auto simp add: e2ennreal_neg continuous_on_const)
  qed auto
  show "A \<subseteq> {0..} \<union> {..0::ereal}"
    by auto
qed

lemma continuous_at_e2ennreal: "continuous (at x within A) e2ennreal"
  by (rule continuous_on_imp_continuous_within[OF continuous_on_e2ennreal, of _ UNIV]) auto

lemma continuous_on_enn2ereal: "continuous_on UNIV enn2ereal"
  by (rule continuous_on_generate_topology[OF open_generated_order])
     (auto simp add: enn2ereal_Iio enn2ereal_Ioi)

lemma continuous_at_enn2ereal: "continuous (at x within A) enn2ereal"
  by (rule continuous_on_imp_continuous_within[OF continuous_on_enn2ereal]) auto

lemma sup_continuous_e2ennreal[order_continuous_intros]:
  assumes f: "sup_continuous f" shows "sup_continuous (\<lambda>x. e2ennreal (f x))"
proof (rule sup_continuous_compose[OF _ f])
  show "sup_continuous e2ennreal"
    by (simp add: continuous_at_e2ennreal continuous_at_left_imp_sup_continuous e2ennreal_mono mono_def)
qed

lemma sup_continuous_enn2ereal[order_continuous_intros]:
  assumes f: "sup_continuous f" shows "sup_continuous (\<lambda>x. enn2ereal (f x))"
proof (rule sup_continuous_compose[OF _ f])
  show "sup_continuous enn2ereal"
  by (simp add: continuous_at_enn2ereal continuous_at_left_imp_sup_continuous less_eq_ennreal.rep_eq mono_def)
qed

lemma sup_continuous_mult_left_ennreal':
  fixes c :: "ennreal"
  shows "sup_continuous (\<lambda>x. c * x)"
  unfolding sup_continuous_def
  by transfer (auto simp: SUP_ereal_mult_left max.absorb2 SUP_upper2)

lemma sup_continuous_mult_left_ennreal[order_continuous_intros]:
  "sup_continuous f \<Longrightarrow> sup_continuous (\<lambda>x. c * f x :: ennreal)"
  by (rule sup_continuous_compose[OF sup_continuous_mult_left_ennreal'])

lemma sup_continuous_mult_right_ennreal[order_continuous_intros]:
  "sup_continuous f \<Longrightarrow> sup_continuous (\<lambda>x. f x * c :: ennreal)"
  using sup_continuous_mult_left_ennreal[of f c] by (simp add: mult.commute)

lemma sup_continuous_divide_ennreal[order_continuous_intros]:
  fixes f g :: "'a::complete_lattice \<Rightarrow> ennreal"
  shows "sup_continuous f \<Longrightarrow> sup_continuous (\<lambda>x. f x / c)"
  unfolding divide_ennreal_def by (rule sup_continuous_mult_right_ennreal)

lemma transfer_enn2ereal_continuous_on [transfer_rule]:
  "rel_fun (=) (rel_fun (rel_fun (=) pcr_ennreal) (=)) continuous_on continuous_on"
proof -
  have "continuous_on A f" if "continuous_on A (\<lambda>x. enn2ereal (f x))" for A and f :: "'a \<Rightarrow> ennreal"
    using continuous_on_compose2[OF continuous_on_e2ennreal[of "{0..}"] that]
    by (auto simp: ennreal.enn2ereal_inverse subset_eq e2ennreal_def max_absorb2)
  moreover
  have "continuous_on A (\<lambda>x. enn2ereal (f x))" if "continuous_on A f" for A and f :: "'a \<Rightarrow> ennreal"
    using continuous_on_compose2[OF continuous_on_enn2ereal that] by auto
  ultimately
  show ?thesis
    by (auto simp add: rel_fun_def ennreal.pcr_cr_eq cr_ennreal_def)
qed

lemma transfer_sup_continuous[transfer_rule]:
  "(rel_fun (rel_fun (=) pcr_ennreal) (=)) sup_continuous sup_continuous"
proof (safe intro!: rel_funI dest!: rel_fun_eq_pcr_ennreal[THEN iffD1])
  show "sup_continuous (enn2ereal \<circ> f) \<Longrightarrow> sup_continuous f" for f :: "'a \<Rightarrow> _"
    using sup_continuous_e2ennreal[of "enn2ereal \<circ> f"] by simp
  show "sup_continuous f \<Longrightarrow> sup_continuous (enn2ereal \<circ> f)" for f :: "'a \<Rightarrow> _"
    using sup_continuous_enn2ereal[of f] by (simp add: comp_def)
qed

lemma continuous_on_ennreal[tendsto_intros]:
  "continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>x. ennreal (f x))"
  by transfer (auto intro!: continuous_on_max continuous_on_const continuous_on_ereal)

lemma tendsto_ennrealD:
  assumes lim: "((\<lambda>x. ennreal (f x)) \<longlongrightarrow> ennreal x) F"
  assumes *: "\<forall>\<^sub>F x in F. 0 \<le> f x" and x: "0 \<le> x"
  shows "(f \<longlongrightarrow> x) F"
proof -
  have "((\<lambda>x. enn2ereal (ennreal (f x))) \<longlongrightarrow> enn2ereal (ennreal x)) F 
    \<longleftrightarrow> (f \<longlongrightarrow> enn2ereal (ennreal x)) F"
    using "*" eventually_mono
    by (intro tendsto_cong) fastforce
  then show ?thesis
    using assms(1) continuous_at_enn2ereal isCont_tendsto_compose x by fastforce
qed

lemma tendsto_ennreal_iff[simp]:
  "\<forall>\<^sub>F x in F. 0 \<le> f x \<Longrightarrow> 0 \<le> x \<Longrightarrow> ((\<lambda>x. ennreal (f x)) \<longlongrightarrow> ennreal x) F \<longleftrightarrow> (f \<longlongrightarrow> x) F"
  by (auto dest: tendsto_ennrealD)
     (auto simp: ennreal_def
           intro!: continuous_on_tendsto_compose[OF continuous_on_e2ennreal[of UNIV]] tendsto_max)

lemma tendsto_enn2ereal_iff[simp]: "((\<lambda>i. enn2ereal (f i)) \<longlongrightarrow> enn2ereal x) F \<longleftrightarrow> (f \<longlongrightarrow> x) F"
  using continuous_on_enn2ereal[THEN continuous_on_tendsto_compose, of f x F]
    continuous_on_e2ennreal[THEN continuous_on_tendsto_compose, of "\<lambda>x. enn2ereal (f x)" "enn2ereal x" F UNIV]
  by auto

lemma ennreal_tendsto_0_iff: "(\<And>n. f n \<ge> 0) \<Longrightarrow> ((\<lambda>n. ennreal (f n)) \<longlonglongrightarrow> 0) \<longleftrightarrow> (f \<longlonglongrightarrow> 0)"
  by (metis (mono_tags) ennreal_0 eventuallyI order_refl tendsto_ennreal_iff)
    
lemma continuous_on_add_ennreal:
  fixes f g :: "'a::topological_space \<Rightarrow> ennreal"
  shows "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. f x + g x)"
  by (transfer fixing: A) (auto intro!: tendsto_add_ereal_nonneg simp: continuous_on_def)

lemma continuous_on_inverse_ennreal[continuous_intros]:
  fixes f :: "'a::topological_space \<Rightarrow> ennreal"
  shows "continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>x. inverse (f x))"
proof (transfer fixing: A)
  show "pred_fun top  ((\<le>) 0) f \<Longrightarrow> continuous_on A (\<lambda>x. inverse (f x))" if "continuous_on A f"
    for f :: "'a \<Rightarrow> ereal"
    using continuous_on_compose2[OF continuous_on_inverse_ereal that] by (auto simp: subset_eq)
qed

instance ennreal :: topological_comm_monoid_add
proof
  show "((\<lambda>x. fst x + snd x) \<longlongrightarrow> a + b) (nhds a \<times>\<^sub>F nhds b)" for a b :: ennreal
    using continuous_on_add_ennreal[of UNIV fst snd]
    using tendsto_at_iff_tendsto_nhds[symmetric, of "\<lambda>x::(ennreal \<times> ennreal). fst x + snd x"]
    by (auto simp: continuous_on_eq_continuous_at)
       (simp add: isCont_def nhds_prod[symmetric])
qed

lemma sup_continuous_add_ennreal[order_continuous_intros]:
  fixes f g :: "'a::complete_lattice \<Rightarrow> ennreal"
  shows "sup_continuous f \<Longrightarrow> sup_continuous g \<Longrightarrow> sup_continuous (\<lambda>x. f x + g x)"
  by transfer (auto intro!: sup_continuous_add)

lemma ennreal_suminf_lessD: "(\<Sum>i. f i :: ennreal) < x \<Longrightarrow> f i < x"
  using le_less_trans[OF sum_le_suminf[OF summableI, of "{i}" f]] by simp

lemma sums_ennreal[simp]: "(\<And>i. 0 \<le> f i) \<Longrightarrow> 0 \<le> x \<Longrightarrow> (\<lambda>i. ennreal (f i)) sums ennreal x \<longleftrightarrow> f sums x"
  unfolding sums_def by (simp add: always_eventually sum_nonneg)

lemma summable_suminf_not_top: "(\<And>i. 0 \<le> f i) \<Longrightarrow> (\<Sum>i. ennreal (f i)) \<noteq> top \<Longrightarrow> summable f"
  using summable_sums[OF summableI, of "\<lambda>i. ennreal (f i)"]
  by (cases "\<Sum>i. ennreal (f i)" rule: ennreal_cases)
     (auto simp: summable_def)

lemma suminf_ennreal[simp]:
  "(\<And>i. 0 \<le> f i) \<Longrightarrow> (\<Sum>i. ennreal (f i)) \<noteq> top \<Longrightarrow> (\<Sum>i. ennreal (f i)) = ennreal (\<Sum>i. f i)"
  by (rule sums_unique[symmetric]) (simp add: summable_suminf_not_top suminf_nonneg summable_sums)

lemma sums_enn2ereal[simp]: "(\<lambda>i. enn2ereal (f i)) sums enn2ereal x \<longleftrightarrow> f sums x"
  unfolding sums_def by (simp add: always_eventually sum_nonneg)

lemma suminf_enn2ereal[simp]: "(\<Sum>i. enn2ereal (f i)) = enn2ereal (suminf f)"
  by (rule sums_unique[symmetric]) (simp add: summable_sums)

lemma transfer_e2ennreal_suminf [transfer_rule]: "rel_fun (rel_fun (=) pcr_ennreal) pcr_ennreal suminf suminf"
  by (auto simp: rel_funI rel_fun_eq_pcr_ennreal comp_def)

lemma ennreal_suminf_cmult[simp]: "(\<Sum>i. r * f i) = r * (\<Sum>i. f i::ennreal)"
  by transfer (auto intro!: suminf_cmult_ereal)

lemma ennreal_suminf_multc[simp]: "(\<Sum>i. f i * r) = (\<Sum>i. f i::ennreal) * r"
  using ennreal_suminf_cmult[of r f] by (simp add: ac_simps)

lemma ennreal_suminf_divide[simp]: "(\<Sum>i. f i / r) = (\<Sum>i. f i::ennreal) / r"
  by (simp add: divide_ennreal_def)

lemma ennreal_suminf_neq_top: "summable f \<Longrightarrow> (\<And>i. 0 \<le> f i) \<Longrightarrow> (\<Sum>i. ennreal (f i)) \<noteq> top"
  using sums_ennreal[of f "suminf f"]
  by (simp add: suminf_nonneg flip: sums_unique summable_sums_iff del: sums_ennreal)

lemma suminf_ennreal_eq:
  "(\<And>i. 0 \<le> f i) \<Longrightarrow> f sums x \<Longrightarrow> (\<Sum>i. ennreal (f i)) = ennreal x"
  using suminf_nonneg[of f] sums_unique[of f x]
  by (intro sums_unique[symmetric]) (auto simp: summable_sums_iff)

lemma ennreal_suminf_bound_add:
  fixes f :: "nat \<Rightarrow> ennreal"
  shows "(\<And>N. (\<Sum>n<N. f n) + y \<le> x) \<Longrightarrow> suminf f + y \<le> x"
  by transfer (auto intro!: suminf_bound_add)

lemma ennreal_suminf_SUP_eq_directed:
  fixes f :: "'a \<Rightarrow> nat \<Rightarrow> ennreal"
  assumes *: "\<And>N i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> finite N \<Longrightarrow> \<exists>k\<in>I. \<forall>n\<in>N. f i n \<le> f k n \<and> f j n \<le> f k n"
  shows "(\<Sum>n. SUP i\<in>I. f i n) = (SUP i\<in>I. \<Sum>n. f i n)"
proof cases
  assume "I \<noteq> {}"
  then obtain i where "i \<in> I" by auto
  from * show ?thesis
    by (transfer fixing: I)
       (auto simp: max_absorb2 SUP_upper2[OF \<open>i \<in> I\<close>] suminf_nonneg summable_ereal_pos \<open>I \<noteq> {}\<close>
             intro!: suminf_SUP_eq_directed)
qed (simp add: bot_ennreal)

lemma INF_ennreal_add_const:
  fixes f g :: "nat \<Rightarrow> ennreal"
  shows "(INF i. f i + c) = (INF i. f i) + c"
  using continuous_at_Inf_mono[of "\<lambda>x. x + c" "f`UNIV"]
  using continuous_add[of "at_right (Inf (range f))", of "\<lambda>x. x" "\<lambda>x. c"]
  by (auto simp: mono_def image_comp)

lemma INF_ennreal_const_add:
  fixes f g :: "nat \<Rightarrow> ennreal"
  shows "(INF i. c + f i) = c + (INF i. f i)"
  using INF_ennreal_add_const[of f c] by (simp add: ac_simps)

lemma SUP_mult_left_ennreal: "c * (SUP i\<in>I. f i) = (SUP i\<in>I. c * f i ::ennreal)"
proof cases
  assume "I \<noteq> {}" then show ?thesis
    by transfer (auto simp add: SUP_ereal_mult_left max_absorb2 SUP_upper2)
qed (simp add: bot_ennreal)

lemma SUP_mult_right_ennreal: "(SUP i\<in>I. f i) * c = (SUP i\<in>I. f i * c ::ennreal)"
  using SUP_mult_left_ennreal by (simp add: mult.commute)

lemma SUP_divide_ennreal: "(SUP i\<in>I. f i) / c = (SUP i\<in>I. f i / c ::ennreal)"
  using SUP_mult_right_ennreal by (simp add: divide_ennreal_def)

lemma ennreal_SUP_of_nat_eq_top: "(SUP x. of_nat x :: ennreal) = top"
proof (intro antisym top_greatest le_SUP_iff[THEN iffD2] allI impI)
  fix y :: ennreal assume "y < top"
  then obtain r where "y = ennreal r"
    by (cases y rule: ennreal_cases) auto
  then show "\<exists>i\<in>UNIV. y < of_nat i"
    using reals_Archimedean2[of "max 1 r"] zero_less_one
    by (simp add: ennreal_Ex_less_of_nat)
qed

lemma ennreal_SUP_eq_top:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes "\<And>n. \<exists>i\<in>I. of_nat n \<le> f i"
  shows "(SUP i \<in> I. f i) = top"
proof -
  have "(SUP x. of_nat x :: ennreal) \<le> (SUP i \<in> I. f i)"
    using assms by (auto intro!: SUP_least intro: SUP_upper2)
  then show ?thesis
    by (auto simp: ennreal_SUP_of_nat_eq_top top_unique)
qed

lemma ennreal_INF_const_minus:
  fixes f :: "'a \<Rightarrow> ennreal"
  shows "I \<noteq> {} \<Longrightarrow> (SUP x\<in>I. c - f x) = c - (INF x\<in>I. f x)"
  by (transfer fixing: I)
     (simp add: sup_max[symmetric] SUP_sup_const1 SUP_ereal_minus_right del: sup_ereal_def)

lemma of_nat_Sup_ennreal:
  assumes "A \<noteq> {}" "bdd_above A"
  shows "of_nat (Sup A) = (SUP a\<in>A. of_nat a :: ennreal)"
proof (intro antisym)
  show "(SUP a\<in>A. of_nat a::ennreal) \<le> of_nat (Sup A)"
    by (intro SUP_least of_nat_mono) (auto intro: cSup_upper assms)
  have "Sup A \<in> A"
    using assms by (auto simp: Sup_nat_def bdd_above_nat)
  then show "of_nat (Sup A) \<le> (SUP a\<in>A. of_nat a::ennreal)"
    by (intro SUP_upper)
qed

lemma ennreal_tendsto_const_minus:
  fixes g :: "'a \<Rightarrow> ennreal"
  assumes ae: "\<forall>\<^sub>F x in F. g x \<le> c"
  assumes g: "((\<lambda>x. c - g x) \<longlongrightarrow> 0) F"
  shows "(g \<longlongrightarrow> c) F"
proof (cases c rule: ennreal_cases)
  case top with tendsto_unique[OF _ g, of "top"] show ?thesis
    by (cases "F = bot") auto
next
  case (real r)
  then have "\<forall>x. \<exists>q\<ge>0. g x \<le> c \<longrightarrow> (g x = ennreal q \<and> q \<le> r)"
    by (auto simp: le_ennreal_iff)
  then obtain f where *: "0 \<le> f x" "g x = ennreal (f x)" "f x \<le> r" if "g x \<le> c" for x
    by metis
  from ae have ae2: "\<forall>\<^sub>F x in F. c - g x = ennreal (r - f x) \<and> f x \<le> r \<and> g x = ennreal (f x) \<and> 0 \<le> f x"
  proof eventually_elim
    fix x assume "g x \<le> c" with *[of x] \<open>0 \<le> r\<close> show "c - g x = ennreal (r - f x) \<and> f x \<le> r \<and> g x = ennreal (f x) \<and> 0 \<le> f x"
      by (auto simp: real ennreal_minus)
  qed
  with g have "((\<lambda>x. ennreal (r - f x)) \<longlongrightarrow> ennreal 0) F"
    by (auto simp add: tendsto_cong eventually_conj_iff)
  with ae2 have "((\<lambda>x. r - f x) \<longlongrightarrow> 0) F"
    by (subst (asm) tendsto_ennreal_iff) (auto elim: eventually_mono)
  then have "(f \<longlongrightarrow> r) F"
    by (rule Lim_transform2[OF tendsto_const])
  with ae2 have "((\<lambda>x. ennreal (f x)) \<longlongrightarrow> ennreal r) F"
    by (subst tendsto_ennreal_iff) (auto elim: eventually_mono simp: real)
  with ae2 show ?thesis
    by (auto simp: real tendsto_cong eventually_conj_iff)
qed

lemma ennreal_SUP_add:
  fixes f g :: "nat \<Rightarrow> ennreal"
  shows "incseq f \<Longrightarrow> incseq g \<Longrightarrow> (SUP i. f i + g i) = Sup (f ` UNIV) + Sup (g ` UNIV)"
  unfolding incseq_def le_fun_def
  by transfer
     (simp add: SUP_ereal_add incseq_def le_fun_def max_absorb2 SUP_upper2)

lemma ennreal_SUP_sum:
  fixes f :: "'a \<Rightarrow> nat \<Rightarrow> ennreal"
  shows "(\<And>i. i \<in> I \<Longrightarrow> incseq (f i)) \<Longrightarrow> (SUP n. \<Sum>i\<in>I. f i n) = (\<Sum>i\<in>I. SUP n. f i n)"
  unfolding incseq_def
  by transfer
     (simp add: SUP_ereal_sum incseq_def SUP_upper2 max_absorb2 sum_nonneg)

lemma ennreal_liminf_minus:
  fixes f :: "nat \<Rightarrow> ennreal"
  shows "(\<And>n. f n \<le> c) \<Longrightarrow> liminf (\<lambda>n. c - f n) = c - limsup f"
  apply transfer
  apply (simp add: ereal_diff_positive max.absorb2 liminf_ereal_cminus)
  apply (subst max.absorb2)
  apply (rule ereal_diff_positive)
  apply (rule Limsup_bounded)
  apply auto
  done

lemma ennreal_continuous_on_cmult:
  "(c::ennreal) < top \<Longrightarrow> continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>x. c * f x)"
  by (transfer fixing: A) (auto intro: continuous_on_cmult_ereal)

lemma ennreal_tendsto_cmult:
  "(c::ennreal) < top \<Longrightarrow> (f \<longlongrightarrow> x) F \<Longrightarrow> ((\<lambda>x. c * f x) \<longlongrightarrow> c * x) F"
  by (rule continuous_on_tendsto_compose[where g=f, OF ennreal_continuous_on_cmult, where s=UNIV])
     (auto simp: continuous_on_id)

lemma tendsto_ennrealI[intro, simp, tendsto_intros]:
  "(f \<longlongrightarrow> x) F \<Longrightarrow> ((\<lambda>x. ennreal (f x)) \<longlongrightarrow> ennreal x) F"
  by (auto simp: ennreal_def
           intro!: continuous_on_tendsto_compose[OF continuous_on_e2ennreal[of UNIV]] tendsto_max)

lemma tendsto_enn2erealI [tendsto_intros]:
  assumes "(f \<longlongrightarrow> l) F"
  shows "((\<lambda>i. enn2ereal(f i)) \<longlongrightarrow> enn2ereal l) F"
using tendsto_enn2ereal_iff assms by auto

lemma tendsto_e2ennrealI [tendsto_intros]:
  assumes "(f \<longlongrightarrow> l) F"
  shows "((\<lambda>i. e2ennreal(f i)) \<longlongrightarrow> e2ennreal l) F"
proof -
  have *: "e2ennreal (max x 0) = e2ennreal x" for x
    by (simp add: e2ennreal_def max.commute)
  have "((\<lambda>i. max (f i) 0) \<longlongrightarrow> max l 0) F"
    apply (intro tendsto_intros) using assms by auto
  then have "((\<lambda>i. enn2ereal(e2ennreal (max (f i) 0))) \<longlongrightarrow> enn2ereal (e2ennreal (max l 0))) F"
    by (subst enn2ereal_e2ennreal, auto)+
  then have "((\<lambda>i. e2ennreal (max (f i) 0)) \<longlongrightarrow> e2ennreal (max l 0)) F"
    using tendsto_enn2ereal_iff by auto
  then show ?thesis
    unfolding * by auto
qed

lemma ennreal_suminf_minus:
  fixes f g :: "nat \<Rightarrow> ennreal"
  shows "(\<And>i. g i \<le> f i) \<Longrightarrow> suminf f \<noteq> top \<Longrightarrow> suminf g \<noteq> top \<Longrightarrow> (\<Sum>i. f i - g i) = suminf f - suminf g"
  by transfer
     (auto simp add: max.absorb2 ereal_diff_positive suminf_le_pos top_ereal_def intro!: suminf_ereal_minus)

lemma ennreal_Sup_countable_SUP:
  "A \<noteq> {} \<Longrightarrow> \<exists>f::nat \<Rightarrow> ennreal. incseq f \<and> range f \<subseteq> A \<and> Sup A = (SUP i. f i)"
  unfolding incseq_def
  apply transfer
  subgoal for A
    using Sup_countable_SUP[of A]
    by (force simp add: incseq_def[symmetric] SUP_upper2 max.absorb2 image_subset_iff Sup_upper2 cong: conj_cong)
  done

lemma ennreal_Inf_countable_INF:
  "A \<noteq> {} \<Longrightarrow> \<exists>f::nat \<Rightarrow> ennreal. decseq f \<and> range f \<subseteq> A \<and> Inf A = (INF i. f i)"
  including ennreal.lifting
  unfolding decseq_def
  apply transfer
  subgoal for A
    using Inf_countable_INF[of A]
    apply (clarsimp simp flip: decseq_def)
    subgoal for f
      by (intro exI[of _ f]) auto
    done
  done

lemma ennreal_SUP_countable_SUP:
  "A \<noteq> {} \<Longrightarrow> \<exists>f::nat \<Rightarrow> ennreal. range f \<subseteq> g`A \<and> Sup (g ` A) = Sup (f ` UNIV)"
  using ennreal_Sup_countable_SUP [of "g`A"] by auto

lemma of_nat_tendsto_top_ennreal: "(\<lambda>n::nat. of_nat n :: ennreal) \<longlonglongrightarrow> top"
  using LIMSEQ_SUP[of "of_nat :: nat \<Rightarrow> ennreal"]
  by (simp add: ennreal_SUP_of_nat_eq_top incseq_def)

lemma SUP_sup_continuous_ennreal:
  fixes f :: "ennreal \<Rightarrow> 'a::complete_lattice"
  assumes f: "sup_continuous f" and "I \<noteq> {}"
  shows "(SUP i\<in>I. f (g i)) = f (SUP i\<in>I. g i)"
proof (rule antisym)
  show "(SUP i\<in>I. f (g i)) \<le> f (SUP i\<in>I. g i)"
    by (rule mono_SUP[OF sup_continuous_mono[OF f]])
  from ennreal_Sup_countable_SUP[of "g`I"] \<open>I \<noteq> {}\<close>
  obtain M :: "nat \<Rightarrow> ennreal" where "incseq M" and M: "range M \<subseteq> g ` I" and eq: "(SUP i \<in> I. g i) = (SUP i. M i)"
    by auto
  have "f (SUP i \<in> I. g i) = (SUP i \<in> range M. f i)"
    unfolding eq sup_continuousD[OF f \<open>mono M\<close>] by (simp add: image_comp)
  also have "\<dots> \<le> (SUP i \<in> I. f (g i))"
    by (insert M, drule SUP_subset_mono) (auto simp add: image_comp)
  finally show "f (SUP i \<in> I. g i) \<le> (SUP i \<in> I. f (g i))" .
qed

lemma ennreal_suminf_SUP_eq:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> ennreal"
  shows "(\<And>i. incseq (\<lambda>n. f n i)) \<Longrightarrow> (\<Sum>i. SUP n. f n i) = (SUP n. \<Sum>i. f n i)"
  apply (rule ennreal_suminf_SUP_eq_directed)
  subgoal for N n j
    by (auto simp: incseq_def intro!:exI[of _ "max n j"])
  done

lemma ennreal_SUP_add_left:
  fixes c :: ennreal
  shows "I \<noteq> {} \<Longrightarrow> (SUP i\<in>I. f i + c) = (SUP i\<in>I. f i) + c"
  apply transfer
  apply (simp add: SUP_ereal_add_left)
  apply (subst (1 2) max.absorb2)
  apply (auto intro: SUP_upper2 add_nonneg_nonneg)
  done

lemma ennreal_SUP_const_minus:
  fixes f :: "'a \<Rightarrow> ennreal"
  shows "I \<noteq> {} \<Longrightarrow> c < top \<Longrightarrow> (INF x\<in>I. c - f x) = c - (SUP x\<in>I. f x)"
  apply (transfer fixing: I)
  unfolding ex_in_conv[symmetric]
  apply (auto simp add: SUP_upper2 sup_absorb2 simp flip: sup_ereal_def)
  apply (subst INF_ereal_minus_right[symmetric])
  apply (auto simp del: sup_ereal_def simp add: sup_INF)
  done

subsection \<open>Approximation lemmas\<close>

lemma INF_approx_ennreal:
  fixes x::ennreal and e::real
  assumes "e > 0"
  assumes INF: "x = (INF i \<in> A. f i)"
  assumes "x \<noteq> \<infinity>"
  shows "\<exists>i \<in> A. f i < x + e"
proof -
  have "(INF i \<in> A. f i) < x + e"
    unfolding INF[symmetric] using \<open>0<e\<close> \<open>x \<noteq> \<infinity>\<close> by (cases x) auto
  then show ?thesis
    unfolding INF_less_iff .
qed

lemma SUP_approx_ennreal:
  fixes x::ennreal and e::real
  assumes "e > 0" "A \<noteq> {}"
  assumes SUP: "x = (SUP i \<in> A. f i)"
  assumes "x \<noteq> \<infinity>"
  shows "\<exists>i \<in> A. x < f i + e"
proof -
  have "x < x + e"
    using \<open>0<e\<close> \<open>x \<noteq> \<infinity>\<close> by (cases x) auto
  also have "x + e = (SUP i \<in> A. f i + e)"
    unfolding SUP ennreal_SUP_add_left[OF \<open>A \<noteq> {}\<close>] ..
  finally show ?thesis
    unfolding less_SUP_iff .
qed

lemma ennreal_approx_SUP:
  fixes x::ennreal
  assumes f_bound: "\<And>i. i \<in> A \<Longrightarrow> f i \<le> x"
  assumes approx: "\<And>e. (e::real) > 0 \<Longrightarrow> \<exists>i \<in> A. x \<le> f i + e"
  shows "x = (SUP i \<in> A. f i)"
proof (rule antisym)
  show "x \<le> (SUP i\<in>A. f i)"
  proof (rule ennreal_le_epsilon)
    fix e :: real assume "0 < e"
    from approx[OF this] guess i ..
    then have "x \<le> f i + e"
      by simp
    also have "\<dots> \<le> (SUP i\<in>A. f i) + e"
      by (intro add_mono \<open>i \<in> A\<close> SUP_upper order_refl)
    finally show "x \<le> (SUP i\<in>A. f i) + e" .
  qed
qed (intro SUP_least f_bound)

lemma ennreal_approx_INF:
  fixes x::ennreal
  assumes f_bound: "\<And>i. i \<in> A \<Longrightarrow> x \<le> f i"
  assumes approx: "\<And>e. (e::real) > 0 \<Longrightarrow> \<exists>i \<in> A. f i \<le> x + e"
  shows "x = (INF i \<in> A. f i)"
proof (rule antisym)
  show "(INF i\<in>A. f i) \<le> x"
  proof (rule ennreal_le_epsilon)
    fix e :: real assume "0 < e"
    from approx[OF this] guess i .. note i = this
    then have "(INF i\<in>A. f i) \<le> f i"
      by (intro INF_lower)
    also have "\<dots> \<le> x + e"
      by fact
    finally show "(INF i\<in>A. f i) \<le> x + e" .
  qed
qed (intro INF_greatest f_bound)

lemma ennreal_approx_unit:
  "(\<And>a::ennreal. 0 < a \<Longrightarrow> a < 1 \<Longrightarrow> a * z \<le> y) \<Longrightarrow> z \<le> y"
  apply (subst SUP_mult_right_ennreal[of "\<lambda>x. x" "{0 <..< 1}" z, simplified])
  apply (auto intro: SUP_least)
  done

lemma suminf_ennreal2:
  "(\<And>i. 0 \<le> f i) \<Longrightarrow> summable f \<Longrightarrow> (\<Sum>i. ennreal (f i)) = ennreal (\<Sum>i. f i)"
  using suminf_ennreal_eq by blast

lemma less_top_ennreal: "x < top \<longleftrightarrow> (\<exists>r\<ge>0. x = ennreal r)"
  by (cases x) auto

lemma enn2real_less_iff[simp]: "x < top \<Longrightarrow> enn2real x < c \<longleftrightarrow> x < c"
  using ennreal_less_iff less_top_ennreal by auto

lemma enn2real_le_iff[simp]: "\<lbrakk>x < top; c > 0\<rbrakk> \<Longrightarrow> enn2real x \<le> c \<longleftrightarrow> x \<le> c"
  by (cases x) auto

lemma enn2real_less:
  assumes "enn2real e < r" "e \<noteq> top" shows "e < ennreal r"
  using enn2real_less_iff assms top.not_eq_extremum by blast

lemma enn2real_le:
  assumes "enn2real e \<le> r" "e \<noteq> top" shows "e \<le> ennreal r"
  by (metis assms enn2real_less ennreal_enn2real_if eq_iff less_le)

lemma tendsto_top_iff_ennreal:
  fixes f :: "'a \<Rightarrow> ennreal"
  shows "(f \<longlongrightarrow> top) F \<longleftrightarrow> (\<forall>l\<ge>0. eventually (\<lambda>x. ennreal l < f x) F)"
  by (auto simp: less_top_ennreal order_tendsto_iff )

lemma ennreal_tendsto_top_eq_at_top:
  "((\<lambda>z. ennreal (f z)) \<longlongrightarrow> top) F \<longleftrightarrow> (LIM z F. f z :> at_top)"
  unfolding filterlim_at_top_dense tendsto_top_iff_ennreal
  apply (auto simp: ennreal_less_iff)
  subgoal for y
    by (auto elim!: eventually_mono allE[of _ "max 0 y"])
  done

lemma tendsto_0_if_Limsup_eq_0_ennreal:
  fixes f :: "_ \<Rightarrow> ennreal"
  shows "Limsup F f = 0 \<Longrightarrow> (f \<longlongrightarrow> 0) F"
  using Liminf_le_Limsup[of F f] tendsto_iff_Liminf_eq_Limsup[of F f 0]
  by (cases "F = bot") auto

lemma diff_le_self_ennreal[simp]: "a - b \<le> (a::ennreal)"
  by (cases a b rule: ennreal2_cases) (auto simp: ennreal_minus)

lemma ennreal_ineq_diff_add: "b \<le> a \<Longrightarrow> a = b + (a - b::ennreal)"
  by transfer (auto simp: ereal_diff_positive max.absorb2 ereal_ineq_diff_add)

lemma ennreal_mult_strict_left_mono: "(a::ennreal) < c \<Longrightarrow> 0 < b \<Longrightarrow> b < top \<Longrightarrow> b * a < b * c"
  by transfer (auto intro!: ereal_mult_strict_left_mono)

lemma ennreal_between: "0 < e \<Longrightarrow> 0 < x \<Longrightarrow> x < top \<Longrightarrow> x - e < (x::ennreal)"
  by transfer (auto intro!: ereal_between)

lemma minus_less_iff_ennreal: "b < top \<Longrightarrow> b \<le> a \<Longrightarrow> a - b < c \<longleftrightarrow> a < c + (b::ennreal)"
  by transfer
     (auto simp: top_ereal_def ereal_minus_less le_less)

lemma tendsto_zero_ennreal:
  assumes ev: "\<And>r. 0 < r \<Longrightarrow> \<forall>\<^sub>F x in F. f x < ennreal r"
  shows "(f \<longlongrightarrow> 0) F"
proof (rule order_tendstoI)
  fix e::ennreal assume "e > 0"
  obtain e'::real where "e' > 0" "ennreal e' < e"
    using \<open>0 < e\<close> dense[of 0 "if e = top then 1 else (enn2real e)"]
    by (cases e) (auto simp: ennreal_less_iff)
  from ev[OF \<open>e' > 0\<close>] show "\<forall>\<^sub>F x in F. f x < e"
    by eventually_elim (insert \<open>ennreal e' < e\<close>, auto)
qed simp

lifting_update ennreal.lifting
lifting_forget ennreal.lifting


subsection \<open>\<^typ>\<open>ennreal\<close> theorems\<close>

lemma neq_top_trans: fixes x y :: ennreal shows "\<lbrakk> y \<noteq> top; x \<le> y \<rbrakk> \<Longrightarrow> x \<noteq> top"
  by (auto simp: top_unique)

lemma diff_diff_ennreal: fixes a b :: ennreal shows "a \<le> b \<Longrightarrow> b \<noteq> \<infinity> \<Longrightarrow> b - (b - a) = a"
  by (cases a b rule: ennreal2_cases) (auto simp: ennreal_minus top_unique)

lemma ennreal_less_one_iff[simp]: "ennreal x < 1 \<longleftrightarrow> x < 1"
  by (cases "0 \<le> x") (auto simp: ennreal_neg ennreal_less_iff simp flip: ennreal_1)

lemma SUP_const_minus_ennreal:
  fixes f :: "'a \<Rightarrow> ennreal" shows "I \<noteq> {} \<Longrightarrow> (SUP x\<in>I. c - f x) = c - (INF x\<in>I. f x)"
  including ennreal.lifting
  by (transfer fixing: I)
     (simp add: SUP_sup_distrib[symmetric] SUP_ereal_minus_right
           flip: sup_ereal_def)

lemma zero_minus_ennreal[simp]: "0 - (a::ennreal) = 0"
  including ennreal.lifting
  by transfer (simp split: split_max)

lemma diff_diff_commute_ennreal:
  fixes a b c :: ennreal shows "a - b - c = a - c - b"
  by (cases a b c rule: ennreal3_cases) (simp_all add: ennreal_minus field_simps)

lemma diff_gr0_ennreal: "b < (a::ennreal) \<Longrightarrow> 0 < a - b"
  including ennreal.lifting by transfer (auto simp: ereal_diff_gr0 ereal_diff_positive split: split_max)

lemma divide_le_posI_ennreal:
  fixes x y z :: ennreal
  shows "x > 0 \<Longrightarrow> z \<le> x * y \<Longrightarrow> z / x \<le> y"
  by (cases x y z rule: ennreal3_cases)
     (auto simp: divide_ennreal ennreal_mult[symmetric] field_simps top_unique)

lemma add_diff_eq_ennreal:
  fixes x y z :: ennreal
  shows "z \<le> y \<Longrightarrow> x + (y - z) = x + y - z"
  including ennreal.lifting
  by transfer
     (insert add_mono[of "0::ereal"], auto simp add: ereal_diff_positive max.absorb2 add_diff_eq_ereal)

lemma add_diff_inverse_ennreal:
  fixes x y :: ennreal shows "x \<le> y \<Longrightarrow> x + (y - x) = y"
  by (cases x) (simp_all add: top_unique add_diff_eq_ennreal)

lemma add_diff_eq_iff_ennreal[simp]:
  fixes x y :: ennreal shows "x + (y - x) = y \<longleftrightarrow> x \<le> y"
proof
  assume *: "x + (y - x) = y" show "x \<le> y"
    by (subst *[symmetric]) simp
qed (simp add: add_diff_inverse_ennreal)

lemma add_diff_le_ennreal: "a + b - c \<le> a + (b - c::ennreal)"
  apply (cases a b c rule: ennreal3_cases)
  subgoal for a' b' c'
    by (cases "0 \<le> b' - c'") (simp_all add: ennreal_minus top_add ennreal_neg flip: ennreal_plus)
  apply (simp_all add: top_add flip: ennreal_plus)
  done

lemma diff_eq_0_ennreal: "a < top \<Longrightarrow> a \<le> b \<Longrightarrow> a - b = (0::ennreal)"
  using ennreal_minus_pos_iff gr_zeroI not_less by blast

lemma diff_diff_ennreal': fixes x y z :: ennreal shows "z \<le> y \<Longrightarrow> y - z \<le> x \<Longrightarrow> x - (y - z) = x + z - y"
  by (cases x; cases y; cases z)
     (auto simp add: top_add add_top minus_top_ennreal ennreal_minus top_unique
           simp flip: ennreal_plus)

lemma diff_diff_ennreal'': fixes x y z :: ennreal
  shows "z \<le> y \<Longrightarrow> x - (y - z) = (if y - z \<le> x then x + z - y else 0)"
  by (cases x; cases y; cases z)
     (auto simp add: top_add add_top minus_top_ennreal ennreal_minus top_unique ennreal_neg
           simp flip: ennreal_plus)

lemma power_less_top_ennreal: fixes x :: ennreal shows "x ^ n < top \<longleftrightarrow> x < top \<or> n = 0"
  using power_eq_top_ennreal[of x n] by (auto simp: less_top)

lemma ennreal_divide_times: "(a / b) * c = a * (c / b :: ennreal)"
  by (simp add: mult.commute ennreal_times_divide)

lemma diff_less_top_ennreal: "a - b < top \<longleftrightarrow>  a < (top :: ennreal)"
  by (cases a; cases b) (auto simp: ennreal_minus)

lemma divide_less_ennreal: "b \<noteq> 0 \<Longrightarrow> b < top \<Longrightarrow> a / b < c \<longleftrightarrow> a < (c * b :: ennreal)"
  by (cases a; cases b; cases c)
     (auto simp: divide_ennreal ennreal_mult[symmetric] ennreal_less_iff field_simps ennreal_top_mult ennreal_top_divide)

lemma one_less_numeral[simp]: "1 < (numeral n::ennreal) \<longleftrightarrow> (num.One < n)"
  by (simp flip: ennreal_1 ennreal_numeral add: ennreal_less_iff)

lemma divide_eq_1_ennreal: "a / b = (1::ennreal) \<longleftrightarrow> (b \<noteq> top \<and> b \<noteq> 0 \<and> b = a)"
  by (cases a ; cases b; cases "b = 0") (auto simp: ennreal_top_divide divide_ennreal split: if_split_asm)

lemma ennreal_mult_cancel_left: "(a * b = a * c) = (a = top \<and> b \<noteq> 0 \<and> c \<noteq> 0 \<or> a = 0 \<or> b = (c::ennreal))"
  by (cases a; cases b; cases c) (auto simp: ennreal_mult[symmetric] ennreal_mult_top ennreal_top_mult)

lemma ennreal_minus_if: "ennreal a - ennreal b = ennreal (if 0 \<le> b then (if b \<le> a then a - b else 0) else a)"
  by (auto simp: ennreal_minus ennreal_neg)

lemma ennreal_plus_if: "ennreal a + ennreal b = ennreal (if 0 \<le> a then (if 0 \<le> b then a + b else a) else b)"
  by (auto simp: ennreal_neg)

lemma power_le_one_iff: "0 \<le> (a::real) \<Longrightarrow> a ^ n \<le> 1 \<longleftrightarrow> (n = 0 \<or> a \<le> 1)"
  by (metis (mono_tags, opaque_lifting) le_less neq0_conv not_le one_le_power power_0 power_eq_imp_eq_base power_le_one zero_le_one)

lemma ennreal_diff_le_mono_left: "a \<le> b \<Longrightarrow> a - c \<le> (b::ennreal)"
  using ennreal_mono_minus[of 0 c a, THEN order_trans, of b] by simp

lemma ennreal_minus_le_iff: "a - b \<le> c \<longleftrightarrow> (a \<le> b + (c::ennreal) \<and> (a = top \<and> b = top \<longrightarrow> c = top))"
  by (cases a; cases b; cases c)
     (auto simp: top_unique top_add add_top ennreal_minus simp flip: ennreal_plus)

lemma ennreal_le_minus_iff: "a \<le> b - c \<longleftrightarrow> (a + c \<le> (b::ennreal) \<or> (a = 0 \<and> b \<le> c))"
  by (cases a; cases b; cases c)
     (auto simp: top_unique top_add add_top ennreal_minus ennreal_le_iff2
           simp flip: ennreal_plus)

lemma diff_add_eq_diff_diff_swap_ennreal: "x - (y + z :: ennreal) = x - y - z"
  by (cases x; cases y; cases z)
     (auto simp: ennreal_minus_if add_top top_add simp flip: ennreal_plus)

lemma diff_add_assoc2_ennreal: "b \<le> a \<Longrightarrow> (a - b + c::ennreal) = a + c - b"
  by (cases a; cases b; cases c)
     (auto simp add: ennreal_minus_if ennreal_plus_if add_top top_add top_unique simp del: ennreal_plus)

lemma diff_gt_0_iff_gt_ennreal: "0 < a - b \<longleftrightarrow> (a = top \<and> b = top \<or> b < (a::ennreal))"
  by (cases a; cases b) (auto simp: ennreal_minus_if ennreal_less_iff)

lemma diff_eq_0_iff_ennreal: "(a - b::ennreal) = 0 \<longleftrightarrow> (a < top \<and> a \<le> b)"
  by (cases a) (auto simp: ennreal_minus_eq_0 diff_eq_0_ennreal)

lemma add_diff_self_ennreal: "a + (b - a::ennreal) = (if a \<le> b then b else a)"
  by (auto simp: diff_eq_0_iff_ennreal less_top)

lemma diff_add_self_ennreal: "(b - a + a::ennreal) = (if a \<le> b then b else a)"
  by (auto simp: diff_add_cancel_ennreal diff_eq_0_iff_ennreal less_top)

lemma ennreal_minus_cancel_iff:
  fixes a b c :: ennreal
  shows "a - b = a - c \<longleftrightarrow> (b = c \<or> (a \<le> b \<and> a \<le> c) \<or> a = top)"
  by (cases a; cases b; cases c) (auto simp: ennreal_minus_if)

text \<open>The next lemma is wrong for $a = top$, for $b = c = 1$ for instance.\<close>

lemma ennreal_right_diff_distrib:
  fixes a b c :: ennreal
  assumes "a \<noteq> top"
  shows "a * (b - c) = a * b - a * c"
  apply (cases a; cases b; cases c)
         apply (use assms in \<open>auto simp add: ennreal_mult_top ennreal_minus ennreal_mult' [symmetric]\<close>)
  apply (simp add: algebra_simps)
  done

lemma SUP_diff_ennreal:
  "c < top \<Longrightarrow> (SUP i\<in>I. f i - c :: ennreal) = (SUP i\<in>I. f i) - c"
  by (auto intro!: SUP_eqI ennreal_minus_mono SUP_least intro: SUP_upper
           simp: ennreal_minus_cancel_iff ennreal_minus_le_iff less_top[symmetric])

lemma ennreal_SUP_add_right:
  fixes c :: ennreal shows "I \<noteq> {} \<Longrightarrow> c + (SUP i\<in>I. f i) = (SUP i\<in>I. c + f i)"
  using ennreal_SUP_add_left[of I f c] by (simp add: add.commute)

lemma SUP_add_directed_ennreal:
  fixes f g :: "_ \<Rightarrow> ennreal"
  assumes directed: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> \<exists>k\<in>I. f i + g j \<le> f k + g k"
  shows "(SUP i\<in>I. f i + g i) = (SUP i\<in>I. f i) + (SUP i\<in>I. g i)"
proof cases
  assume "I = {}" then show ?thesis
    by (simp add: bot_ereal_def)
next
  assume "I \<noteq> {}"
  show ?thesis
  proof (rule antisym)
    show "(SUP i\<in>I. f i + g i) \<le> (SUP i\<in>I. f i) + (SUP i\<in>I. g i)"
      by (rule SUP_least; intro add_mono SUP_upper)
  next
    have "(SUP i\<in>I. f i) + (SUP i\<in>I. g i) = (SUP i\<in>I. f i + (SUP i\<in>I. g i))"
      by (intro ennreal_SUP_add_left[symmetric] \<open>I \<noteq> {}\<close>)
    also have "\<dots> = (SUP i\<in>I. (SUP j\<in>I. f i + g j))"
      using \<open>I \<noteq> {}\<close> by (simp add: ennreal_SUP_add_right)
    also have "\<dots> \<le> (SUP i\<in>I. f i + g i)"
      using directed by (intro SUP_least) (blast intro: SUP_upper2)
    finally show "(SUP i\<in>I. f i) + (SUP i\<in>I. g i) \<le> (SUP i\<in>I. f i + g i)" .
  qed
qed

lemma enn2real_eq_0_iff: "enn2real x = 0 \<longleftrightarrow> x = 0 \<or> x = top"
  by (cases x) auto

lemma continuous_on_diff_ennreal:
  "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> top) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> g x \<noteq> top) \<Longrightarrow> continuous_on A (\<lambda>z. f z - g z::ennreal)"
  including ennreal.lifting
proof (transfer fixing: A, simp add: top_ereal_def)
  fix f g :: "'a \<Rightarrow> ereal" assume "\<forall>x. 0 \<le> f x" "\<forall>x. 0 \<le> g x" "continuous_on A f" "continuous_on A g"
  moreover assume "f x \<noteq> \<infinity>" "g x \<noteq> \<infinity>" if "x \<in> A" for x
  ultimately show "continuous_on A (\<lambda>z. max 0 (f z - g z))"
    by (intro continuous_on_max continuous_on_const continuous_on_diff_ereal) auto
qed

lemma tendsto_diff_ennreal:
  "(f \<longlongrightarrow> x) F \<Longrightarrow> (g \<longlongrightarrow> y) F \<Longrightarrow> x \<noteq> top \<Longrightarrow> y \<noteq> top \<Longrightarrow> ((\<lambda>z. f z - g z::ennreal) \<longlongrightarrow> x - y) F"
  using continuous_on_tendsto_compose[where f="\<lambda>x. fst x - snd x::ennreal" and s="{(x, y). x \<noteq> top \<and> y \<noteq> top}" and g="\<lambda>x. (f x, g x)" and l="(x, y)" and F="F",
    OF continuous_on_diff_ennreal]
  by (auto simp: tendsto_Pair eventually_conj_iff less_top order_tendstoD continuous_on_fst continuous_on_snd continuous_on_id)

declare lim_real_of_ereal [tendsto_intros]

lemma tendsto_enn2real [tendsto_intros]:
  assumes "(u \<longlongrightarrow> ennreal l) F" "l \<ge> 0"
  shows "((\<lambda>n. enn2real (u n)) \<longlongrightarrow> l) F"
  unfolding enn2real_def
  by (metis assms enn2ereal_ennreal lim_real_of_ereal tendsto_enn2erealI)

end
