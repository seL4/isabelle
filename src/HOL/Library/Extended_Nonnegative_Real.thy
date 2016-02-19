(*  Title:      HOL/Library/Extended_Nonnegative_Real.thy
    Author:     Johannes Hölzl
*)

subsection \<open>The type of non-negative extended real numbers\<close>

theory Extended_Nonnegative_Real
  imports Extended_Real
begin

context linordered_nonzero_semiring
begin

lemma of_nat_nonneg [simp]: "0 \<le> of_nat n"
  by (induct n) simp_all

lemma of_nat_mono[simp]: "i \<le> j \<Longrightarrow> of_nat i \<le> of_nat j"
  by (auto simp add: le_iff_add intro!: add_increasing2)

end

lemma of_nat_less[simp]:
  "i < j \<Longrightarrow> of_nat i < (of_nat j::'a::{linordered_nonzero_semiring, semiring_char_0})"
  by (auto simp: less_le)

lemma of_nat_le_iff[simp]:
  "of_nat i \<le> (of_nat j::'a::{linordered_nonzero_semiring, semiring_char_0}) \<longleftrightarrow> i \<le> j"
proof (safe intro!: of_nat_mono)
  assume "of_nat i \<le> (of_nat j::'a)" then show "i \<le> j"
  proof (intro leI notI)
    assume "j < i" from less_le_trans[OF of_nat_less[OF this] \<open>of_nat i \<le> of_nat j\<close>] show False
      by blast
  qed
qed

lemma (in complete_lattice) SUP_sup_const1:
  "I \<noteq> {} \<Longrightarrow> (SUP i:I. sup c (f i)) = sup c (SUP i:I. f i)"
  using SUP_sup_distrib[of "\<lambda>_. c" I f] by simp

lemma (in complete_lattice) SUP_sup_const2:
  "I \<noteq> {} \<Longrightarrow> (SUP i:I. sup (f i) c) = sup (SUP i:I. f i) c"
  using SUP_sup_distrib[of f I "\<lambda>_. c"] by simp

lemma one_less_of_natD:
  "(1::'a::linordered_semidom) < of_nat n \<Longrightarrow> 1 < n"
  using zero_le_one[where 'a='a]
  apply (cases n)
  apply simp
  subgoal for n'
    apply (cases n')
    apply simp
    apply simp
    done
  done

lemma setsum_le_suminf:
  fixes f :: "nat \<Rightarrow> 'a::{ordered_comm_monoid_add, linorder_topology}"
  shows "summable f \<Longrightarrow> finite I \<Longrightarrow> \<forall>m\<in>- I. 0 \<le> f m \<Longrightarrow> setsum f I \<le> suminf f"
  by (rule sums_le[OF _ sums_If_finite_set summable_sums]) auto

typedef ennreal = "{x :: ereal. 0 \<le> x}"
  morphisms enn2ereal e2ennreal'
  by auto

definition "e2ennreal x = e2ennreal' (max 0 x)"

lemma type_definition_ennreal': "type_definition enn2ereal e2ennreal {x. 0 \<le> x}"
  using type_definition_ennreal
  by (auto simp: type_definition_def e2ennreal_def max_absorb2)

setup_lifting type_definition_ennreal'

lift_definition ennreal :: "real \<Rightarrow> ennreal" is "sup 0 \<circ> ereal"
  by simp

declare [[coercion ennreal]]
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

lift_definition less_eq_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> bool" is "op \<le>" .
lift_definition less_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> bool" is "op <" .

instance
  by standard
     (transfer ; auto simp: Inf_lower Inf_greatest Sup_upper Sup_least le_max_iff_disj max.absorb1)+

end

lemma ennreal_cases:
  fixes x :: ennreal
  obtains (real) r :: real where "0 \<le> r" "x = ennreal r" | (top) "x = top"
  apply transfer
  subgoal for x thesis
    by (cases x) (auto simp: max.absorb2 top_ereal_def)
  done

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
lift_definition plus_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> ennreal" is "op +" by simp
lift_definition times_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> ennreal" is "op *" by simp

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

lemma ennreal_zero_less_one: "0 < (1::ennreal)"
  by transfer auto

instance ennreal :: dioid
proof (standard; transfer)
  fix a b :: ereal assume "0 \<le> a" "0 \<le> b" then show "(a \<le> b) = (\<exists>c\<in>Collect (op \<le> 0). b = a + c)"
    unfolding ereal_ex_split Bex_def
    by (cases a b rule: ereal2_cases) (auto intro!: exI[of _ "real_of_ereal (b - a)"])
qed

instance ennreal :: ordered_comm_semiring
  by standard
     (transfer ; auto intro: add_mono mult_mono mult_ac ereal_left_distrib ereal_mult_left_mono)+

instance ennreal :: linordered_nonzero_semiring
  proof qed (transfer; simp)

declare [[coercion "of_nat :: nat \<Rightarrow> ennreal"]]

lemma e2ennreal_neg: "x \<le> 0 \<Longrightarrow> e2ennreal x = 0"
  unfolding zero_ennreal_def e2ennreal_def by (simp add: max_absorb1)

lemma e2ennreal_mono: "x \<le> y \<Longrightarrow> e2ennreal x \<le> e2ennreal y"
  by (cases "0 \<le> x" "0 \<le> y" rule: bool.exhaust[case_product bool.exhaust])
     (auto simp: e2ennreal_neg less_eq_ennreal.abs_eq eq_onp_def)

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

  fun dest_summing (Const (@{const_name Groups.plus}, _) $ t $ u, ts) =
        dest_summing (t, dest_summing (u, ts))
    | dest_summing (t, ts) = t :: ts

  val mk_sum = Arith_Data.long_mk_sum
  fun dest_sum t = dest_summing (t, [])
  val find_first = find_first_t []
  val trans_tac = Numeral_Simprocs.trans_tac
  val norm_ss =
    simpset_of (put_simpset HOL_basic_ss @{context}
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
  val dest_bal = HOLogic.dest_bin @{const_name HOL.eq} @{typ ennreal}
  fun simp_conv _ _ = SOME @{thm ennreal_add_left_cancel}
)

structure Le_Ennreal_Cancel = ExtractCommonTermFun
(open Cancel_Ennreal_Common
  val mk_bal = HOLogic.mk_binrel @{const_name Orderings.less_eq}
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less_eq} @{typ ennreal}
  fun simp_conv _ _ = SOME @{thm ennreal_add_left_cancel_le}
)

structure Less_Ennreal_Cancel = ExtractCommonTermFun
(open Cancel_Ennreal_Common
  val mk_bal = HOLogic.mk_binrel @{const_name Orderings.less}
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less} @{typ ennreal}
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
    fix x y :: ereal assume "0 \<le> x" "x < y"
    moreover from dense[OF this(2)] guess z ..
    ultimately show "\<exists>z\<in>Collect (op \<le> 0). x < z \<and> z < y"
      by (intro bexI[of _ z]) auto
  qed
qed (rule open_ennreal_def)

end

lemma ennreal_rat_dense:
  fixes x y :: ennreal
  shows "x < y \<Longrightarrow> \<exists>r::rat. x < real_of_rat r \<and> real_of_rat r < y"
proof transfer
  fix x y :: ereal assume xy: "0 \<le> x" "0 \<le> y" "x < y"
  moreover
  from ereal_dense3[OF \<open>x < y\<close>]
  obtain r where "x < ereal (real_of_rat r)" "ereal (real_of_rat r) < y"
    by auto
  moreover then have "0 \<le> r"
    using le_less_trans[OF \<open>0 \<le> x\<close> \<open>x < ereal (real_of_rat r)\<close>] by auto
  ultimately show "\<exists>r. x < (sup 0 \<circ> ereal) (real_of_rat r) \<and> (sup 0 \<circ> ereal) (real_of_rat r) < y"
    by (intro exI[of _ r]) (auto simp: max_absorb2)
qed

lemma enn2ereal_range: "e2ennreal ` {0..} = UNIV"
proof -
  have "\<exists>y\<ge>0. x = e2ennreal y" for x
    by (cases x) (auto simp: e2ennreal_def max_absorb2)
  then show ?thesis
    by (auto simp: image_iff Bex_def)
qed

lemma enn2ereal_nonneg: "0 \<le> enn2ereal x"
  using ennreal.enn2ereal[of x] by simp

lemma ereal_ennreal_cases:
  obtains b where "0 \<le> a" "a = enn2ereal b" | "a < 0"
  using e2ennreal'_inverse[of a, symmetric] by (cases "0 \<le> a") (auto intro: enn2ereal_nonneg)

lemma enn2ereal_Iio: "enn2ereal -` {..<a} = (if 0 \<le> a then {..< e2ennreal a} else {})"
  using enn2ereal_nonneg
  by (cases a rule: ereal_ennreal_cases)
     (auto simp add: vimage_def set_eq_iff ennreal.enn2ereal_inverse less_ennreal.rep_eq e2ennreal_def max_absorb2
           intro: le_less_trans less_imp_le)

lemma enn2ereal_Ioi: "enn2ereal -` {a <..} = (if 0 \<le> a then {e2ennreal a <..} else UNIV)"
  using enn2ereal_nonneg
  by (cases a rule: ereal_ennreal_cases)
     (auto simp add: vimage_def set_eq_iff ennreal.enn2ereal_inverse less_ennreal.rep_eq e2ennreal_def max_absorb2
           intro: less_le_trans)

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

lemma transfer_enn2ereal_continuous_on [transfer_rule]:
  "rel_fun (op =) (rel_fun (rel_fun op = pcr_ennreal) op =) continuous_on continuous_on"
proof -
  have "continuous_on A f" if "continuous_on A (\<lambda>x. enn2ereal (f x))" for A and f :: "'a \<Rightarrow> ennreal"
    using continuous_on_compose2[OF continuous_on_e2ennreal[of "{0..}"] that]
    by (auto simp: ennreal.enn2ereal_inverse subset_eq enn2ereal_nonneg e2ennreal_def max_absorb2)
  moreover
  have "continuous_on A (\<lambda>x. enn2ereal (f x))" if "continuous_on A f" for A and f :: "'a \<Rightarrow> ennreal"
    using continuous_on_compose2[OF continuous_on_enn2ereal that] by auto
  ultimately
  show ?thesis
    by (auto simp add: rel_fun_def ennreal.pcr_cr_eq cr_ennreal_def)
qed

lemma continuous_on_add_ennreal[continuous_intros]:
  fixes f g :: "'a::topological_space \<Rightarrow> ennreal"
  shows "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. f x + g x)"
  by (transfer fixing: A) (auto intro!: tendsto_add_ereal_nonneg simp: continuous_on_def)

lemma continuous_on_inverse_ennreal[continuous_intros]:
  fixes f :: "'a::topological_space \<Rightarrow> ennreal"
  shows "continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>x. inverse (f x))"
proof (transfer fixing: A)
  show "pred_fun (\<lambda>_. True)  (op \<le> 0) f \<Longrightarrow> continuous_on A (\<lambda>x. inverse (f x))" if "continuous_on A f"
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

lemma ennreal_zero_less_top[simp]: "0 < (top::ennreal)"
  by transfer (simp add: top_ereal_def)

lemma ennreal_one_less_top[simp]: "1 < (top::ennreal)"
  by transfer (simp add: top_ereal_def)

lemma ennreal_zero_neq_top[simp]: "0 \<noteq> (top::ennreal)"
  by transfer (simp add: top_ereal_def)

lemma ennreal_top_neq_zero[simp]: "(top::ennreal) \<noteq> 0"
  by transfer (simp add: top_ereal_def)

lemma ennreal_top_neq_one[simp]: "top \<noteq> (1::ennreal)"
  by transfer (simp add: top_ereal_def one_ereal_def ereal_max[symmetric] del: ereal_max)

lemma ennreal_one_neq_top[simp]: "1 \<noteq> (top::ennreal)"
  by transfer (simp add: top_ereal_def one_ereal_def ereal_max[symmetric] del: ereal_max)

lemma ennreal_add_less_top[simp]:
  fixes a b :: ennreal
  shows "a + b < top \<longleftrightarrow> a < top \<and> b < top"
  by transfer (auto simp: top_ereal_def)

lemma ennreal_add_eq_top[simp]:
  fixes a b :: ennreal
  shows "a + b = top \<longleftrightarrow> a = top \<or> b = top"
  by transfer (auto simp: top_ereal_def)

lemma ennreal_setsum_less_top[simp]:
  fixes f :: "'a \<Rightarrow> ennreal"
  shows "finite I \<Longrightarrow> (\<Sum>i\<in>I. f i) < top \<longleftrightarrow> (\<forall>i\<in>I. f i < top)"
  by (induction I rule: finite_induct) auto

lemma ennreal_setsum_eq_top[simp]:
  fixes f :: "'a \<Rightarrow> ennreal"
  shows "finite I \<Longrightarrow> (\<Sum>i\<in>I. f i) = top \<longleftrightarrow> (\<exists>i\<in>I. f i = top)"
  by (induction I rule: finite_induct) auto

lemma enn2ereal_eq_top_iff[simp]: "enn2ereal x = \<infinity> \<longleftrightarrow> x = top"
  by transfer (simp add: top_ereal_def)

lemma ennreal_top_top: "top - top = (top::ennreal)"
  by transfer (auto simp: top_ereal_def max_def)

lemma ennreal_minus_zero[simp]: "a - (0::ennreal) = a"
  by transfer (auto simp: max_def)

lemma ennreal_add_diff_cancel_right[simp]:
  fixes x y z :: ennreal shows "y \<noteq> top \<Longrightarrow> (x + y) - y = x"
  apply transfer
  subgoal for x y
    apply (cases x y rule: ereal2_cases)
    apply (auto split: split_max simp: top_ereal_def)
    done
  done

lemma ennreal_add_diff_cancel_left[simp]:
  fixes x y z :: ennreal shows "y \<noteq> top \<Longrightarrow> (y + x) - y = x"
  by (simp add: add.commute)

lemma
  fixes a b :: ennreal
  shows "a - b = 0 \<Longrightarrow> a \<le> b"
  apply transfer
  subgoal for a b
    apply (cases a b rule: ereal2_cases)
    apply (auto simp: not_le max_def split: if_splits)
    done
  done

lemma ennreal_minus_cancel:
  fixes a b c :: ennreal
  shows "c \<noteq> top \<Longrightarrow> a \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> c - a = c - b \<Longrightarrow> a = b"
  apply transfer
  subgoal for a b c
    by (cases a b c rule: ereal3_cases)
       (auto simp: top_ereal_def max_def split: if_splits)
  done

lemma enn2ereal_ennreal[simp]: "0 \<le> x \<Longrightarrow> enn2ereal (ennreal x) = x"
  by transfer (simp add: max_absorb2)

lemma tendsto_ennrealD:
  assumes lim: "((\<lambda>x. ennreal (f x)) \<longlongrightarrow> ennreal x) F"
  assumes *: "\<forall>\<^sub>F x in F. 0 \<le> f x" and x: "0 \<le> x"
  shows "(f \<longlongrightarrow> x) F"
  using continuous_on_tendsto_compose[OF continuous_on_enn2ereal lim]
  apply simp
  apply (subst (asm) tendsto_cong)
  using *
  apply eventually_elim
  apply (auto simp: max_absorb2 \<open>0 \<le> x\<close>)
  done

lemma tendsto_ennreal_iff[simp]:
  "\<forall>\<^sub>F x in F. 0 \<le> f x \<Longrightarrow> 0 \<le> x \<Longrightarrow> ((\<lambda>x. ennreal (f x)) \<longlongrightarrow> ennreal x) F \<longleftrightarrow> (f \<longlongrightarrow> x) F"
  by (auto dest: tendsto_ennrealD)
     (auto simp: ennreal_def
           intro!: continuous_on_tendsto_compose[OF continuous_on_e2ennreal[of UNIV]] tendsto_max)

lemma ennreal_zero[simp]: "ennreal 0 = 0"
  by (simp add: ennreal_def max.absorb1 zero_ennreal.abs_eq)

lemma ennreal_plus[simp]:
  "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> ennreal (a + b) = ennreal a + ennreal b"
  by (transfer fixing: a b) (auto simp: max_absorb2)

lemma ennreal_inj[simp]:
  "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> ennreal a = ennreal b \<longleftrightarrow> a = b"
  by (transfer fixing: a b) (auto simp: max_absorb2)

lemma ennreal_le_iff[simp]: "0 \<le> y \<Longrightarrow> ennreal x \<le> ennreal y \<longleftrightarrow> x \<le> y"
  by (auto simp: ennreal_def zero_ereal_def less_eq_ennreal.abs_eq eq_onp_def split: split_max)

lemma setsum_ennreal[simp]: "(\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> (\<Sum>i\<in>I. ennreal (f i)) = ennreal (setsum f I)"
  by (induction I rule: infinite_finite_induct) (auto simp: setsum_nonneg)

lemma sums_ennreal[simp]: "(\<And>i. 0 \<le> f i) \<Longrightarrow> 0 \<le> x \<Longrightarrow> (\<lambda>i. ennreal (f i)) sums ennreal x \<longleftrightarrow> f sums x"
  unfolding sums_def by (simp add: always_eventually setsum_nonneg)

lemma summable_suminf_not_top: "(\<And>i. 0 \<le> f i) \<Longrightarrow> (\<Sum>i. ennreal (f i)) \<noteq> top \<Longrightarrow> summable f"
  using summable_sums[OF summableI, of "\<lambda>i. ennreal (f i)"]
  by (cases "\<Sum>i. ennreal (f i)" rule: ennreal_cases)
     (auto simp: summable_def)

lemma suminf_ennreal[simp]:
  "(\<And>i. 0 \<le> f i) \<Longrightarrow> (\<Sum>i. ennreal (f i)) \<noteq> top \<Longrightarrow> (\<Sum>i. ennreal (f i)) = ennreal (\<Sum>i. f i)"
  by (rule sums_unique[symmetric]) (simp add: summable_suminf_not_top suminf_nonneg summable_sums)

lemma suminf_less_top: "(\<Sum>i. f i :: ennreal) < top \<Longrightarrow> f i < top"
  using le_less_trans[OF setsum_le_suminf[OF summableI, of "{i}" f]] by simp

lemma add_top:
  fixes x :: "'a::{order_top, ordered_comm_monoid_add}"
  shows "0 \<le> x \<Longrightarrow> x + top = top"
  by (intro top_le add_increasing order_refl)

lemma top_add:
  fixes x :: "'a::{order_top, ordered_comm_monoid_add}"
  shows "0 \<le> x \<Longrightarrow> top + x = top"
  by (intro top_le add_increasing2 order_refl)

lemma enn2ereal_top: "enn2ereal top = \<infinity>"
  by transfer (simp add: top_ereal_def)

lemma e2ennreal_infty: "e2ennreal \<infinity> = top"
  by (simp add: top_ennreal.abs_eq top_ereal_def)

lemma sup_const_add_ennreal:
  fixes a b c :: "ennreal"
  shows "sup (c + a) (c + b) = c + sup a b"
  apply transfer
  subgoal for a b c
    apply (cases a b c rule: ereal3_cases)
    apply (auto simp: ereal_max[symmetric] simp del: ereal_max)
    apply (auto simp: top_ereal_def[symmetric] sup_ereal_def[symmetric]
                simp del: sup_ereal_def)
    apply (auto simp add: top_ereal_def)
    done
  done

lemma bot_ennreal: "bot = (0::ennreal)"
  by transfer rule

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
    by (rule lfp_lowerbound) (simp add: eq[symmetric] lfp_unfold[OF mf, symmetric])
qed

lemma sup_continuous_applyD: "sup_continuous f \<Longrightarrow> sup_continuous (\<lambda>x. f x h)"
  using sup_continuous_apply[THEN sup_continuous_compose] .

lemma INF_ennreal_add_const:
  fixes f g :: "nat \<Rightarrow> ennreal"
  shows "(INF i. f i + c) = (INF i. f i) + c"
  using continuous_at_Inf_mono[of "\<lambda>x. x + c" "f`UNIV"]
  using continuous_add[of "at_right (Inf (range f))", of "\<lambda>x. x" "\<lambda>x. c"]
  by (auto simp: mono_def)

lemma INF_ennreal_const_add:
  fixes f g :: "nat \<Rightarrow> ennreal"
  shows "(INF i. c + f i) = c + (INF i. f i)"
  using INF_ennreal_add_const[of f c] by (simp add: ac_simps)

lemma sup_continuous_e2ennreal[order_continuous_intros]:
  assumes f: "sup_continuous f" shows "sup_continuous (\<lambda>x. e2ennreal (f x))"
  apply (rule sup_continuous_compose[OF _ f])
  apply (rule continuous_at_left_imp_sup_continuous)
  apply (auto simp: mono_def e2ennreal_mono continuous_at_e2ennreal)
  done

lemma sup_continuous_enn2ereal[order_continuous_intros]:
  assumes f: "sup_continuous f" shows "sup_continuous (\<lambda>x. enn2ereal (f x))"
  apply (rule sup_continuous_compose[OF _ f])
  apply (rule continuous_at_left_imp_sup_continuous)
  apply (simp_all add: mono_def less_eq_ennreal.rep_eq continuous_at_enn2ereal)
  done

lemma ennreal_1[simp]: "ennreal 1 = 1"
  by transfer (simp add: max_absorb2)

lemma ennreal_of_nat_eq_real_of_nat: "of_nat i = ennreal (of_nat i)"
  by (induction i) simp_all

lemma ennreal_SUP_of_nat_eq_top: "(SUP x. of_nat x :: ennreal) = top"
proof (intro antisym top_greatest le_SUP_iff[THEN iffD2] allI impI)
  fix y :: ennreal assume "y < top"
  then obtain r where "y = ennreal r"
    by (cases y rule: ennreal_cases) auto
  then show "\<exists>i\<in>UNIV. y < of_nat i"
    using ex_less_of_nat[of "max 1 r"] zero_less_one
    by (auto simp: ennreal_of_nat_eq_real_of_nat ennreal_def less_ennreal.abs_eq eq_onp_def max.absorb2
             dest!: one_less_of_natD intro: less_trans)
qed

lemma ennreal_SUP_eq_top:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes "\<And>n. \<exists>i\<in>I. of_nat n \<le> f i"
  shows "(SUP i : I. f i) = top"
proof -
  have "(SUP x. of_nat x :: ennreal) \<le> (SUP i : I. f i)"
    using assms by (auto intro!: SUP_least intro: SUP_upper2)
  then show ?thesis
    by (auto simp: ennreal_SUP_of_nat_eq_top top_unique)
qed

lemma sup_continuous_SUP[order_continuous_intros]:
  fixes M :: "_ \<Rightarrow> _ \<Rightarrow> 'a::complete_lattice"
  assumes M: "\<And>i. i \<in> I \<Longrightarrow> sup_continuous (M i)"
  shows  "sup_continuous (SUP i:I. M i)"
  unfolding sup_continuous_def by (auto simp add: sup_continuousD[OF M] intro: SUP_commute)

lemma sup_continuous_apply_SUP[order_continuous_intros]:
  fixes M :: "_ \<Rightarrow> _ \<Rightarrow> 'a::complete_lattice"
  shows "(\<And>i. i \<in> I \<Longrightarrow> sup_continuous (M i)) \<Longrightarrow> sup_continuous (\<lambda>x. SUP i:I. M i x)"
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

lemma ennreal_INF_const_minus:
  fixes f :: "'a \<Rightarrow> ennreal"
  shows "I \<noteq> {} \<Longrightarrow> (SUP x:I. c - f x) = c - (INF x:I. f x)"
  by (transfer fixing: I)
     (simp add: sup_max[symmetric] SUP_sup_const1 SUP_ereal_minus_right del: sup_ereal_def)

lemma ennreal_diff_add_assoc:
  fixes a b c :: ennreal
  shows "a \<le> b \<Longrightarrow> c + b - a = c + (b - a)"
  apply transfer
  subgoal for a b c
    apply (cases a b c rule: ereal3_cases)
    apply (auto simp: field_simps max_absorb2)
    done
  done

lemma ennreal_top_minus[simp]:
  fixes c :: ennreal
  shows "top - c = top"
  by transfer (auto simp: top_ereal_def max_absorb2)

lemma le_ennreal_iff:
  "0 \<le> r \<Longrightarrow> x \<le> ennreal r \<longleftrightarrow> (\<exists>q\<ge>0. x = ennreal q \<and> q \<le> r)"
  apply (transfer fixing: r)
  subgoal for x
    by (cases x) (auto simp: max_absorb2 cong: conj_cong)
  done

lemma ennreal_minus: "0 \<le> q \<Longrightarrow> q \<le> r \<Longrightarrow> ennreal r - ennreal q = ennreal (r - q)"
  by transfer (simp add: max_absorb2)

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
  then obtain f where *: "\<And>x. g x \<le> c \<Longrightarrow> 0 \<le> f x" "\<And>x. g x \<le> c \<Longrightarrow> g x = ennreal (f x)" "\<And>x. g x \<le> c \<Longrightarrow> f x \<le> r"
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

lemma ereal_add_diff_cancel:
  fixes a b :: ereal
  shows "\<bar>b\<bar> \<noteq> \<infinity> \<Longrightarrow> (a + b) - b = a"
  by (cases a b rule: ereal2_cases) auto

lemma ennreal_add_diff_cancel:
  fixes a b :: ennreal
  shows "b \<noteq> \<infinity> \<Longrightarrow> (a + b) - b = a"
  unfolding infinity_ennreal_def
  by transfer (simp add: max_absorb2 top_ereal_def ereal_add_diff_cancel)

lemma ennreal_mult_eq_top_iff:
  fixes a b :: ennreal
  shows "a * b = top \<longleftrightarrow> (a = top \<and> b \<noteq> 0) \<or> (b = top \<and> a \<noteq> 0)"
  by transfer (auto simp: top_ereal_def)

lemma ennreal_top_eq_mult_iff:
  fixes a b :: ennreal
  shows "top = a * b \<longleftrightarrow> (a = top \<and> b \<noteq> 0) \<or> (b = top \<and> a \<noteq> 0)"
  using ennreal_mult_eq_top_iff[of a b] by auto

lemma ennreal_mult: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> ennreal (a * b) = ennreal a * ennreal b"
  by transfer (simp add: max_absorb2)

lemma setsum_enn2ereal[simp]: "(\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> (\<Sum>i\<in>I. enn2ereal (f i)) = enn2ereal (setsum f I)"
  by (induction I rule: infinite_finite_induct) (auto simp: setsum_nonneg zero_ennreal.rep_eq plus_ennreal.rep_eq)

lemma e2ennreal_enn2ereal[simp]: "e2ennreal (enn2ereal x) = x"
  by (simp add: e2ennreal_def max_absorb2 enn2ereal_nonneg ennreal.enn2ereal_inverse)

lemma tendsto_enn2ereal_iff[simp]: "((\<lambda>i. enn2ereal (f i)) \<longlongrightarrow> enn2ereal x) F \<longleftrightarrow> (f \<longlongrightarrow> x) F"
  using continuous_on_enn2ereal[THEN continuous_on_tendsto_compose, of f x F]
    continuous_on_e2ennreal[THEN continuous_on_tendsto_compose, of "\<lambda>x. enn2ereal (f x)" "enn2ereal x" F UNIV]
  by auto

lemma sums_enn2ereal[simp]: "(\<lambda>i. enn2ereal (f i)) sums enn2ereal x \<longleftrightarrow> f sums x"
  unfolding sums_def by (simp add: always_eventually setsum_nonneg setsum_enn2ereal)

lemma suminf_enn2real[simp]: "(\<Sum>i. enn2ereal (f i)) = enn2ereal (suminf f)"
  by (rule sums_unique[symmetric]) (simp add: summable_sums)

lemma pcr_ennreal_enn2ereal[simp]: "pcr_ennreal (enn2ereal x) x"
  by (simp add: ennreal.pcr_cr_eq cr_ennreal_def)

lemma rel_fun_eq_pcr_ennreal: "rel_fun op = pcr_ennreal f g \<longleftrightarrow> f = enn2ereal \<circ> g"
  by (auto simp: rel_fun_def ennreal.pcr_cr_eq cr_ennreal_def)

lemma transfer_e2ennreal_suminf [transfer_rule]: "rel_fun (rel_fun op = pcr_ennreal) pcr_ennreal suminf suminf"
  by (auto simp: rel_funI rel_fun_eq_pcr_ennreal comp_def)

lemma ennreal_suminf_cmult[simp]: "(\<Sum>i. r * f i) = r * (\<Sum>i. f i::ennreal)"
  by transfer (auto intro!: suminf_cmult_ereal)

lemma ennreal_suminf_SUP_eq_directed:
  fixes f :: "'a \<Rightarrow> nat \<Rightarrow> ennreal"
  assumes *: "\<And>N i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> finite N \<Longrightarrow> \<exists>k\<in>I. \<forall>n\<in>N. f i n \<le> f k n \<and> f j n \<le> f k n"
  shows "(\<Sum>n. SUP i:I. f i n) = (SUP i:I. \<Sum>n. f i n)"
proof cases
  assume "I \<noteq> {}"
  then obtain i where "i \<in> I" by auto
  from * show ?thesis
    by (transfer fixing: I)
       (auto simp: max_absorb2 SUP_upper2[OF \<open>i \<in> I\<close>] suminf_nonneg summable_ereal_pos \<open>I \<noteq> {}\<close>
             intro!: suminf_SUP_eq_directed)
qed (simp add: bot_ennreal)

lemma ennreal_eq_zero_iff[simp]: "0 \<le> x \<Longrightarrow> ennreal x = 0 \<longleftrightarrow> x = 0"
  by transfer (auto simp: max_absorb2)

lemma ennreal_neq_top[simp]: "ennreal r \<noteq> top"
  by transfer (simp add: top_ereal_def zero_ereal_def ereal_max[symmetric] del: ereal_max)

lemma ennreal_of_nat_neq_top[simp]: "of_nat i \<noteq> (top::ennreal)"
  by (induction i) auto

lemma ennreal_suminf_neq_top: "summable f \<Longrightarrow> (\<And>i. 0 \<le> f i) \<Longrightarrow> (\<Sum>i. ennreal (f i)) \<noteq> top"
  using sums_ennreal[of f "suminf f"]
  by (simp add: suminf_nonneg sums_unique[symmetric] summable_sums_iff[symmetric] del: sums_ennreal)

instance ennreal :: semiring_char_0
proof (standard, safe intro!: linorder_injI)
  have *: "1 + of_nat k \<noteq> (0::ennreal)" for k
    using add_pos_nonneg[OF zero_less_one, of "of_nat k :: ennreal"] by auto
  fix x y :: nat assume "x < y" "of_nat x = (of_nat y::ennreal)" then show False
    by (auto simp add: less_iff_Suc_add *)
qed

lemma ennreal_suminf_lessD: "(\<Sum>i. f i :: ennreal) < x \<Longrightarrow> f i < x"
  using le_less_trans[OF setsum_le_suminf[OF summableI, of "{i}" f]] by simp

lemma ennreal_less_top[simp]: "ennreal x < top"
  by transfer (simp add: top_ereal_def max_def)

lemma ennreal_le_epsilon:
  "(\<And>e::real. y < top \<Longrightarrow> 0 < e \<Longrightarrow> x \<le> y + ennreal e) \<Longrightarrow> x \<le> y"
  apply (cases y rule: ennreal_cases)
  apply (cases x rule: ennreal_cases)
  apply (auto simp del: ennreal_plus simp add: top_unique ennreal_plus[symmetric]
    intro: zero_less_one field_le_epsilon)
  done

lemma ennreal_less_zero_iff[simp]: "0 < ennreal x \<longleftrightarrow> 0 < x"
  by transfer (auto simp: max_def)

lemma suminf_ennreal_eq:
  "(\<And>i. 0 \<le> f i) \<Longrightarrow> f sums x \<Longrightarrow> (\<Sum>i. ennreal (f i)) = ennreal x"
  using suminf_nonneg[of f] sums_unique[of f x]
  by (intro sums_unique[symmetric]) (auto simp: summable_sums_iff)

lemma transfer_e2ennreal_sumset [transfer_rule]:
  "rel_fun (rel_fun op = pcr_ennreal) (rel_fun op = pcr_ennreal) setsum setsum"
  by (auto intro!: rel_funI simp: rel_fun_eq_pcr_ennreal comp_def)

lemma ennreal_suminf_bound_add:
  fixes f :: "nat \<Rightarrow> ennreal"
  shows "(\<And>N. (\<Sum>n<N. f n) + y \<le> x) \<Longrightarrow> suminf f + y \<le> x"
  by transfer (auto intro!: suminf_bound_add)

end
