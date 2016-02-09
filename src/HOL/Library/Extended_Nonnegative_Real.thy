(*  Title:      HOL/Library/Extended_Nonnegative_Real.thy
    Author:     Johannes Hölzl
*)

subsection \<open>The type of non-negative extended real numbers\<close>

theory Extended_Nonnegative_Real
  imports Extended_Real
begin

typedef ennreal = "{x :: ereal. 0 \<le> x}"
  morphisms enn2ereal e2ennreal
  by auto

setup_lifting type_definition_ennreal


lift_definition ennreal :: "real \<Rightarrow> ennreal" is "max 0 \<circ> ereal"
  by simp

declare [[coercion ennreal]]
declare [[coercion e2ennreal]]

instantiation ennreal :: semiring_1_no_zero_divisors
begin

lift_definition one_ennreal :: ennreal is 1 by simp
lift_definition zero_ennreal :: ennreal is 0 by simp
lift_definition plus_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> ennreal" is "op +" by simp
lift_definition times_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> ennreal" is "op *" by simp

instance
  by standard (transfer; auto simp: field_simps ereal_right_distrib)+

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


instantiation ennreal :: complete_linorder
begin

lift_definition top_ennreal :: ennreal is top by simp
lift_definition bot_ennreal :: ennreal is 0 by simp
lift_definition sup_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> ennreal" is sup by (simp add: max.coboundedI1)
lift_definition inf_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> ennreal" is inf by (simp add: min.boundedI)

lift_definition Inf_ennreal :: "ennreal set \<Rightarrow> ennreal" is "Inf"
  by (auto intro: Inf_greatest)

lift_definition Sup_ennreal :: "ennreal set \<Rightarrow> ennreal" is "sup 0 \<circ> Sup"
  by auto

lift_definition less_eq_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> bool" is "op \<le>" .
lift_definition less_ennreal :: "ennreal \<Rightarrow> ennreal \<Rightarrow> bool" is "op <" .

instance
  by standard
     (transfer ; auto simp: Inf_lower Inf_greatest Sup_upper Sup_least le_max_iff_disj max.absorb1)+

end



lemma ennreal_zero_less_one: "0 < (1::ennreal)"
  by transfer auto

instance ennreal :: ordered_comm_semiring
  by standard
     (transfer ; auto intro: add_mono mult_mono mult_ac ereal_left_distrib ereal_mult_left_mono)+

instantiation ennreal :: linear_continuum_topology
begin

definition open_ennreal :: "ennreal set \<Rightarrow> bool"
  where "(open :: ennreal set \<Rightarrow> bool) = generate_topology (range lessThan \<union> range greaterThan)"

instance
proof
  show "\<exists>a b::ennreal. a \<noteq> b"
    using ennreal_zero_less_one by (auto dest: order.strict_implies_not_eq)
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
  ultimately show "\<exists>r. x < (max 0 \<circ> ereal) (real_of_rat r) \<and> (max 0 \<circ> ereal) (real_of_rat r) < y"
    by (intro exI[of _ r]) (auto simp: max_absorb2)
qed

lemma enn2ereal_range: "e2ennreal ` {0..} = UNIV"
proof -
  have "\<exists>y\<ge>0. x = e2ennreal y" for x
    by (cases x) auto
  then show ?thesis
    by (auto simp: image_iff Bex_def)
qed

lemma enn2ereal_nonneg: "0 \<le> enn2ereal x"
  using ennreal.enn2ereal[of x] by simp

lemma ereal_ennreal_cases:
  obtains b where "0 \<le> a" "a = enn2ereal b" | "a < 0"
  using e2ennreal_inverse[of a, symmetric] by (cases "0 \<le> a") (auto intro: enn2ereal_nonneg)

lemma enn2ereal_Iio: "enn2ereal -` {..<a} = (if 0 \<le> a then {..< e2ennreal a} else {})"
  using enn2ereal_nonneg
  by (cases a rule: ereal_ennreal_cases)
     (auto simp add: vimage_def set_eq_iff ennreal.enn2ereal_inverse less_ennreal.rep_eq
           intro: le_less_trans less_imp_le)

lemma enn2ereal_Ioi: "enn2ereal -` {a <..} = (if 0 \<le> a then {e2ennreal a <..} else UNIV)"
  using enn2ereal_nonneg
  by (cases a rule: ereal_ennreal_cases)
     (auto simp add: vimage_def set_eq_iff ennreal.enn2ereal_inverse less_ennreal.rep_eq
           intro: less_le_trans)

lemma continuous_e2ennreal: "continuous_on {0 ..} e2ennreal"
  by (rule continuous_onI_mono)
     (auto simp add: less_eq_ennreal.abs_eq eq_onp_def enn2ereal_range)

lemma continuous_enn2ereal: "continuous_on UNIV enn2ereal"
  by (rule continuous_on_generate_topology[OF open_generated_order])
     (auto simp add: enn2ereal_Iio enn2ereal_Ioi)

lemma transfer_enn2ereal_continuous_on [transfer_rule]:
  "rel_fun (op =) (rel_fun (rel_fun op = pcr_ennreal) op =) continuous_on continuous_on"
proof -
  have "continuous_on A f" if "continuous_on A (\<lambda>x. enn2ereal (f x))" for A and f :: "'a \<Rightarrow> ennreal"
    using continuous_on_compose2[OF continuous_e2ennreal that]
    by (auto simp: ennreal.enn2ereal_inverse subset_eq enn2ereal_nonneg)
  moreover
  have "continuous_on A (\<lambda>x. enn2ereal (f x))" if "continuous_on A f" for A and f :: "'a \<Rightarrow> ennreal"
    using continuous_on_compose2[OF continuous_enn2ereal that] by auto
  ultimately
  show ?thesis
    by (auto simp add: rel_fun_def ennreal.pcr_cr_eq cr_ennreal_def)
qed

lemma continuous_on_add_ennreal[continuous_intros]:
  fixes f g :: "'a::topological_space \<Rightarrow> ennreal"
  shows "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. f x + g x)"
  by (transfer fixing: A) (auto intro!: tendsto_add_ereal_nonneg simp: continuous_on_def)

lemma continuous_on_inverse_ennreal[continuous_intros]:
  fixes f :: "_ \<Rightarrow> ennreal"
  shows "continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>x. inverse (f x))"
proof (transfer fixing: A)
  show "pred_fun (op \<le> 0) f \<Longrightarrow> continuous_on A (\<lambda>x. inverse (f x))" if "continuous_on A f"
    for f :: "_ \<Rightarrow> ereal"
    using continuous_on_compose2[OF continuous_on_inverse_ereal that] by (auto simp: subset_eq)
qed

end
