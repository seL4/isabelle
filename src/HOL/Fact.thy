(*  Title       : Fact.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
    The integer version of factorial and other additions by Jeremy Avigad.
*)

header{*Factorial Function*}

theory Fact
imports Main
begin

class fact =
  fixes fact :: "'a \<Rightarrow> 'a"

instantiation nat :: fact
begin 

fun
  fact_nat :: "nat \<Rightarrow> nat"
where
  fact_0_nat: "fact_nat 0 = Suc 0"
| fact_Suc: "fact_nat (Suc x) = Suc x * fact x"

instance ..

end

(* definitions for the integers *)

instantiation int :: fact

begin 

definition
  fact_int :: "int \<Rightarrow> int"
where  
  "fact_int x = (if x >= 0 then int (fact (nat x)) else 0)"

instance proof qed

end


subsection {* Set up Transfer *}

lemma transfer_nat_int_factorial:
  "(x::int) >= 0 \<Longrightarrow> fact (nat x) = nat (fact x)"
  unfolding fact_int_def
  by auto


lemma transfer_nat_int_factorial_closure:
  "x >= (0::int) \<Longrightarrow> fact x >= 0"
  by (auto simp add: fact_int_def)

declare transfer_morphism_nat_int[transfer add return: 
    transfer_nat_int_factorial transfer_nat_int_factorial_closure]

lemma transfer_int_nat_factorial:
  "fact (int x) = int (fact x)"
  unfolding fact_int_def by auto

lemma transfer_int_nat_factorial_closure:
  "is_nat x \<Longrightarrow> fact x >= 0"
  by (auto simp add: fact_int_def)

declare transfer_morphism_int_nat[transfer add return: 
    transfer_int_nat_factorial transfer_int_nat_factorial_closure]


subsection {* Factorial *}

lemma fact_0_int [simp]: "fact (0::int) = 1"
  by (simp add: fact_int_def)

lemma fact_1_nat [simp]: "fact (1::nat) = 1"
  by simp

lemma fact_Suc_0_nat [simp]: "fact (Suc 0) = Suc 0"
  by simp

lemma fact_1_int [simp]: "fact (1::int) = 1"
  by (simp add: fact_int_def)

lemma fact_plus_one_nat: "fact ((n::nat) + 1) = (n + 1) * fact n"
  by simp

lemma fact_plus_one_int: 
  assumes "n >= 0"
  shows "fact ((n::int) + 1) = (n + 1) * fact n"
  using assms unfolding fact_int_def 
  by (simp add: nat_add_distrib algebra_simps int_mult)

lemma fact_reduce_nat: "(n::nat) > 0 \<Longrightarrow> fact n = n * fact (n - 1)"
  apply (subgoal_tac "n = Suc (n - 1)")
  apply (erule ssubst)
  apply (subst fact_Suc)
  apply simp_all
  done

lemma fact_reduce_int: "(n::int) > 0 \<Longrightarrow> fact n = n * fact (n - 1)"
  apply (subgoal_tac "n = (n - 1) + 1")
  apply (erule ssubst)
  apply (subst fact_plus_one_int)
  apply simp_all
  done

lemma fact_nonzero_nat [simp]: "fact (n::nat) \<noteq> 0"
  apply (induct n)
  apply (auto simp add: fact_plus_one_nat)
  done

lemma fact_nonzero_int [simp]: "n >= 0 \<Longrightarrow> fact (n::int) ~= 0"
  by (simp add: fact_int_def)

lemma fact_gt_zero_nat [simp]: "fact (n :: nat) > 0"
  by (insert fact_nonzero_nat [of n], arith)

lemma fact_gt_zero_int [simp]: "n >= 0 \<Longrightarrow> fact (n :: int) > 0"
  by (auto simp add: fact_int_def)

lemma fact_ge_one_nat [simp]: "fact (n :: nat) >= 1"
  by (insert fact_nonzero_nat [of n], arith)

lemma fact_ge_Suc_0_nat [simp]: "fact (n :: nat) >= Suc 0"
  by (insert fact_nonzero_nat [of n], arith)

lemma fact_ge_one_int [simp]: "n >= 0 \<Longrightarrow> fact (n :: int) >= 1"
  apply (auto simp add: fact_int_def)
  apply (subgoal_tac "1 = int 1")
  apply (erule ssubst)
  apply (subst zle_int)
  apply auto
  done

lemma dvd_fact_nat [rule_format]: "1 <= m \<longrightarrow> m <= n \<longrightarrow> m dvd fact (n::nat)"
  apply (induct n)
  apply force
  apply (auto simp only: fact_Suc)
  apply (subgoal_tac "m = Suc n")
  apply (erule ssubst)
  apply (rule dvd_triv_left)
  apply auto
  done

lemma dvd_fact_int [rule_format]: "1 <= m \<longrightarrow> m <= n \<longrightarrow> m dvd fact (n::int)"
  apply (case_tac "1 <= n")
  apply (induct n rule: int_ge_induct)
  apply (auto simp add: fact_plus_one_int)
  apply (subgoal_tac "m = i + 1")
  apply auto
  done

lemma interval_plus_one_nat: "(i::nat) <= j + 1 \<Longrightarrow> 
  {i..j+1} = {i..j} Un {j+1}"
  by auto

lemma interval_Suc: "i <= Suc j \<Longrightarrow> {i..Suc j} = {i..j} Un {Suc j}"
  by auto

lemma interval_plus_one_int: "(i::int) <= j + 1 \<Longrightarrow> {i..j+1} = {i..j} Un {j+1}"
  by auto

lemma fact_altdef_nat: "fact (n::nat) = (PROD i:{1..n}. i)"
  apply (induct n)
  apply force
  apply (subst fact_Suc)
  apply (subst interval_Suc)
  apply auto
done

lemma fact_altdef_int: "n >= 0 \<Longrightarrow> fact (n::int) = (PROD i:{1..n}. i)"
  apply (induct n rule: int_ge_induct)
  apply force
  apply (subst fact_plus_one_int, assumption)
  apply (subst interval_plus_one_int)
  apply auto
done

lemma fact_dvd: "n \<le> m \<Longrightarrow> fact n dvd fact (m::nat)"
  by (auto simp add: fact_altdef_nat intro!: setprod_dvd_setprod_subset)

lemma fact_mod: "m \<le> (n::nat) \<Longrightarrow> fact n mod fact m = 0"
  by (auto simp add: dvd_imp_mod_0 fact_dvd)

lemma fact_div_fact:
  assumes "m \<ge> (n :: nat)"
  shows "(fact m) div (fact n) = \<Prod>{n + 1..m}"
proof -
  obtain d where "d = m - n" by auto
  from assms this have "m = n + d" by auto
  have "fact (n + d) div (fact n) = \<Prod>{n + 1..n + d}"
  proof (induct d)
    case 0
    show ?case by simp
  next
    case (Suc d')
    have "fact (n + Suc d') div fact n = Suc (n + d') * fact (n + d') div fact n"
      by simp
    also from Suc.hyps have "... = Suc (n + d') * \<Prod>{n + 1..n + d'}" 
      unfolding div_mult1_eq[of _ "fact (n + d')"] by (simp add: fact_mod)
    also have "... = \<Prod>{n + 1..n + Suc d'}"
      by (simp add: atLeastAtMostSuc_conv setprod_insert)
    finally show ?case .
  qed
  from this `m = n + d` show ?thesis by simp
qed

lemma fact_mono_nat: "(m::nat) \<le> n \<Longrightarrow> fact m \<le> fact n"
apply (drule le_imp_less_or_eq)
apply (auto dest!: less_imp_Suc_add)
apply (induct_tac k, auto)
done

lemma fact_neg_int [simp]: "m < (0::int) \<Longrightarrow> fact m = 0"
  unfolding fact_int_def by auto

lemma fact_ge_zero_int [simp]: "fact m >= (0::int)"
  apply (case_tac "m >= 0")
  apply auto
  apply (frule fact_gt_zero_int)
  apply arith
done

lemma fact_mono_int_aux [rule_format]: "k >= (0::int) \<Longrightarrow> 
    fact (m + k) >= fact m"
  apply (case_tac "m < 0")
  apply auto
  apply (induct k rule: int_ge_induct)
  apply auto
  apply (subst add_assoc [symmetric])
  apply (subst fact_plus_one_int)
  apply auto
  apply (erule order_trans)
  apply (subst mult_le_cancel_right1)
  apply (subgoal_tac "fact (m + i) >= 0")
  apply arith
  apply auto
done

lemma fact_mono_int: "(m::int) <= n \<Longrightarrow> fact m <= fact n"
  apply (insert fact_mono_int_aux [of "n - m" "m"])
  apply auto
done

text{*Note that @{term "fact 0 = fact 1"}*}
lemma fact_less_mono_nat: "[| (0::nat) < m; m < n |] ==> fact m < fact n"
apply (drule_tac m = m in less_imp_Suc_add, auto)
apply (induct_tac k, auto)
done

lemma fact_less_mono_int_aux: "k >= 0 \<Longrightarrow> (0::int) < m \<Longrightarrow>
    fact m < fact ((m + 1) + k)"
  apply (induct k rule: int_ge_induct)
  apply (simp add: fact_plus_one_int)
  apply (subst mult_less_cancel_right1)
  apply (insert fact_gt_zero_int [of m], arith)
  apply (subst (2) fact_reduce_int)
  apply (auto simp add: add_ac)
  apply (erule order_less_le_trans)
  apply (subst mult_le_cancel_right1)
  apply auto
  apply (subgoal_tac "fact (i + (1 + m)) >= 0")
  apply force
  apply (rule fact_ge_zero_int)
done

lemma fact_less_mono_int: "(0::int) < m \<Longrightarrow> m < n \<Longrightarrow> fact m < fact n"
  apply (insert fact_less_mono_int_aux [of "n - (m + 1)" "m"])
  apply auto
done

lemma fact_num_eq_if_nat: "fact (m::nat) = 
  (if m=0 then 1 else m * fact (m - 1))"
by (cases m) auto

lemma fact_add_num_eq_if_nat:
  "fact ((m::nat) + n) = (if m + n = 0 then 1 else (m + n) * fact (m + n - 1))"
by (cases "m + n") auto

lemma fact_add_num_eq_if2_nat:
  "fact ((m::nat) + n) = 
    (if m = 0 then fact n else (m + n) * fact ((m - 1) + n))"
by (cases m) auto

lemma fact_le_power: "fact n \<le> n^n"
proof (induct n)
  case (Suc n)
  then have "fact n \<le> Suc n ^ n" by (rule le_trans) (simp add: power_mono)
  then show ?case by (simp add: add_le_mono)
qed simp

subsection {* @{term fact} and @{term of_nat} *}

lemma of_nat_fact_not_zero [simp]: "of_nat (fact n) \<noteq> (0::'a::semiring_char_0)"
by auto

lemma of_nat_fact_gt_zero [simp]: "(0::'a::{linordered_semidom}) < of_nat(fact n)" by auto

lemma of_nat_fact_ge_zero [simp]: "(0::'a::linordered_semidom) \<le> of_nat(fact n)"
by simp

lemma inv_of_nat_fact_gt_zero [simp]: "(0::'a::linordered_field) < inverse (of_nat (fact n))"
by (auto simp add: positive_imp_inverse_positive)

lemma inv_of_nat_fact_ge_zero [simp]: "(0::'a::linordered_field) \<le> inverse (of_nat (fact n))"
by (auto intro: order_less_imp_le)

end
