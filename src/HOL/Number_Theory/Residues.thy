(*  Title:      HOL/Number_Theory/Residues.thy
    Author:     Jeremy Avigad

An algebraic treatment of residue rings, and resulting proofs of
Euler's theorem and Wilson's theorem.
*)

section {* Residue rings *}

theory Residues
imports UniqueFactorization MiscAlgebra
begin

(*

  A locale for residue rings

*)

definition residue_ring :: "int => int ring" where
  "residue_ring m == (|
    carrier =       {0..m - 1},
    mult =          (%x y. (x * y) mod m),
    one =           1,
    zero =          0,
    add =           (%x y. (x + y) mod m) |)"

locale residues =
  fixes m :: int and R (structure)
  assumes m_gt_one: "m > 1"
  defines "R == residue_ring m"

context residues
begin

lemma abelian_group: "abelian_group R"
  apply (insert m_gt_one)
  apply (rule abelian_groupI)
  apply (unfold R_def residue_ring_def)
  apply (auto simp add: mod_add_right_eq [symmetric] ac_simps)
  apply (case_tac "x = 0")
  apply force
  apply (subgoal_tac "(x + (m - x)) mod m = 0")
  apply (erule bexI)
  apply auto
  done

lemma comm_monoid: "comm_monoid R"
  apply (insert m_gt_one)
  apply (unfold R_def residue_ring_def)
  apply (rule comm_monoidI)
  apply auto
  apply (subgoal_tac "x * y mod m * z mod m = z * (x * y mod m) mod m")
  apply (erule ssubst)
  apply (subst mod_mult_right_eq [symmetric])+
  apply (simp_all only: ac_simps)
  done

lemma cring: "cring R"
  apply (rule cringI)
  apply (rule abelian_group)
  apply (rule comm_monoid)
  apply (unfold R_def residue_ring_def, auto)
  apply (subst mod_add_eq [symmetric])
  apply (subst mult.commute)
  apply (subst mod_mult_right_eq [symmetric])
  apply (simp add: field_simps)
  done

end

sublocale residues < cring
  by (rule cring)


context residues
begin

(* These lemmas translate back and forth between internal and
   external concepts *)

lemma res_carrier_eq: "carrier R = {0..m - 1}"
  unfolding R_def residue_ring_def by auto

lemma res_add_eq: "x \<oplus> y = (x + y) mod m"
  unfolding R_def residue_ring_def by auto

lemma res_mult_eq: "x \<otimes> y = (x * y) mod m"
  unfolding R_def residue_ring_def by auto

lemma res_zero_eq: "\<zero> = 0"
  unfolding R_def residue_ring_def by auto

lemma res_one_eq: "\<one> = 1"
  unfolding R_def residue_ring_def units_of_def by auto

lemma res_units_eq: "Units R = { x. 0 < x & x < m & coprime x m}"
  apply (insert m_gt_one)
  apply (unfold Units_def R_def residue_ring_def)
  apply auto
  apply (subgoal_tac "x ~= 0")
  apply auto
  apply (metis invertible_coprime_int)
  apply (subst (asm) coprime_iff_invertible'_int)
  apply (auto simp add: cong_int_def mult.commute)
  done

lemma res_neg_eq: "\<ominus> x = (- x) mod m"
  apply (insert m_gt_one)
  apply (unfold R_def a_inv_def m_inv_def residue_ring_def)
  apply auto
  apply (rule the_equality)
  apply auto
  apply (subst mod_add_right_eq [symmetric])
  apply auto
  apply (subst mod_add_left_eq [symmetric])
  apply auto
  apply (subgoal_tac "y mod m = - x mod m")
  apply simp
  apply (metis minus_add_cancel mod_mult_self1 mult.commute)
  done

lemma finite [iff]: "finite (carrier R)"
  by (subst res_carrier_eq, auto)

lemma finite_Units [iff]: "finite (Units R)"
  by (subst res_units_eq) auto

(* The function a -> a mod m maps the integers to the
   residue classes. The following lemmas show that this mapping
   respects addition and multiplication on the integers. *)

lemma mod_in_carrier [iff]: "a mod m : carrier R"
  apply (unfold res_carrier_eq)
  apply (insert m_gt_one, auto)
  done

lemma add_cong: "(x mod m) \<oplus> (y mod m) = (x + y) mod m"
  unfolding R_def residue_ring_def
  apply auto
  apply presburger
  done

lemma mult_cong: "(x mod m) \<otimes> (y mod m) = (x * y) mod m"
  unfolding R_def residue_ring_def
  by auto (metis mod_mult_eq)

lemma zero_cong: "\<zero> = 0"
  unfolding R_def residue_ring_def by auto

lemma one_cong: "\<one> = 1 mod m"
  using m_gt_one unfolding R_def residue_ring_def by auto

(* revise algebra library to use 1? *)
lemma pow_cong: "(x mod m) (^) n = x^n mod m"
  apply (insert m_gt_one)
  apply (induct n)
  apply (auto simp add: nat_pow_def one_cong)
  apply (metis mult.commute mult_cong)
  done

lemma neg_cong: "\<ominus> (x mod m) = (- x) mod m"
  by (metis mod_minus_eq res_neg_eq)

lemma (in residues) prod_cong:
    "finite A \<Longrightarrow> (\<Otimes> i:A. (f i) mod m) = (PROD i:A. f i) mod m"
  by (induct set: finite) (auto simp: one_cong mult_cong)

lemma (in residues) sum_cong:
    "finite A \<Longrightarrow> (\<Oplus> i:A. (f i) mod m) = (SUM i: A. f i) mod m"
  by (induct set: finite) (auto simp: zero_cong add_cong)

lemma mod_in_res_units [simp]: "1 < m \<Longrightarrow> coprime a m \<Longrightarrow>
    a mod m : Units R"
  apply (subst res_units_eq, auto)
  apply (insert pos_mod_sign [of m a])
  apply (subgoal_tac "a mod m ~= 0")
  apply arith
  apply auto
  apply (metis gcd_int.commute gcd_red_int)
  done

lemma res_eq_to_cong: "((a mod m) = (b mod m)) = [a = b] (mod (m::int))"
  unfolding cong_int_def by auto

(* Simplifying with these will translate a ring equation in R to a
   congruence. *)

lemmas res_to_cong_simps = add_cong mult_cong pow_cong one_cong
    prod_cong sum_cong neg_cong res_eq_to_cong

(* Other useful facts about the residue ring *)

lemma one_eq_neg_one: "\<one> = \<ominus> \<one> \<Longrightarrow> m = 2"
  apply (simp add: res_one_eq res_neg_eq)
  apply (metis add.commute add_diff_cancel mod_mod_trivial one_add_one uminus_add_conv_diff
            zero_neq_one zmod_zminus1_eq_if)
  done

end


(* prime residues *)

locale residues_prime =
  fixes p and R (structure)
  assumes p_prime [intro]: "prime p"
  defines "R == residue_ring p"

sublocale residues_prime < residues p
  apply (unfold R_def residues_def)
  using p_prime apply auto
  apply (metis (full_types) int_1 of_nat_less_iff prime_gt_1_nat)
  done

context residues_prime
begin

lemma is_field: "field R"
  apply (rule cring.field_intro2)
  apply (rule cring)
  apply (auto simp add: res_carrier_eq res_one_eq res_zero_eq res_units_eq)
  apply (rule classical)
  apply (erule notE)
  apply (subst gcd_commute_int)
  apply (rule prime_imp_coprime_int)
  apply (rule p_prime)
  apply (rule notI)
  apply (frule zdvd_imp_le)
  apply auto
  done

lemma res_prime_units_eq: "Units R = {1..p - 1}"
  apply (subst res_units_eq)
  apply auto
  apply (subst gcd_commute_int)
  apply (auto simp add: p_prime prime_imp_coprime_int zdvd_not_zless)
  done

end

sublocale residues_prime < field
  by (rule is_field)


(*
  Test cases: Euler's theorem and Wilson's theorem.
*)


subsection{* Euler's theorem *}

(* the definition of the phi function *)

definition phi :: "int => nat"
  where "phi m = card({ x. 0 < x & x < m & gcd x m = 1})"

lemma phi_def_nat: "phi m = card({ x. 0 < x & x < nat m & gcd x (nat m) = 1})"
  apply (simp add: phi_def)
  apply (rule bij_betw_same_card [of nat])
  apply (auto simp add: inj_on_def bij_betw_def image_def)
  apply (metis dual_order.irrefl dual_order.strict_trans leI nat_1 transfer_nat_int_gcd(1))
  apply (metis One_nat_def int_0 int_1 int_less_0_conv int_nat_eq nat_int transfer_int_nat_gcd(1) zless_int)
  done

lemma prime_phi:
  assumes  "2 \<le> p" "phi p = p - 1" shows "prime p"
proof -
  have "{x. 0 < x \<and> x < p \<and> coprime x p} = {1..p - 1}"
    using assms unfolding phi_def_nat
    by (intro card_seteq) fastforce+
  then have cop: "\<And>x. x \<in> {1::nat..p - 1} \<Longrightarrow> coprime x p"
    by blast
  { fix x::nat assume *: "1 < x" "x < p" and "x dvd p"
    have "coprime x p"
      apply (rule cop)
      using * apply auto
      done
    with `x dvd p` `1 < x` have "False" by auto }
  then show ?thesis
    using `2 \<le> p`
    by (simp add: prime_def)
       (metis One_nat_def dvd_pos_nat nat_dvd_not_less nat_neq_iff not_gr0
              not_numeral_le_zero one_dvd)
qed

lemma phi_zero [simp]: "phi 0 = 0"
  apply (subst phi_def)
(* Auto hangs here. Once again, where is the simplification rule
   1 == Suc 0 coming from? *)
  apply (auto simp add: card_eq_0_iff)
(* Add card_eq_0_iff as a simp rule? delete card_empty_imp? *)
  done

lemma phi_one [simp]: "phi 1 = 0"
  by (auto simp add: phi_def card_eq_0_iff)

lemma (in residues) phi_eq: "phi m = card(Units R)"
  by (simp add: phi_def res_units_eq)

lemma (in residues) euler_theorem1:
  assumes a: "gcd a m = 1"
  shows "[a^phi m = 1] (mod m)"
proof -
  from a m_gt_one have [simp]: "a mod m : Units R"
    by (intro mod_in_res_units)
  from phi_eq have "(a mod m) (^) (phi m) = (a mod m) (^) (card (Units R))"
    by simp
  also have "\<dots> = \<one>"
    by (intro units_power_order_eq_one, auto)
  finally show ?thesis
    by (simp add: res_to_cong_simps)
qed

(* In fact, there is a two line proof!

lemma (in residues) euler_theorem1:
  assumes a: "gcd a m = 1"
  shows "[a^phi m = 1] (mod m)"
proof -
  have "(a mod m) (^) (phi m) = \<one>"
    by (simp add: phi_eq units_power_order_eq_one a m_gt_one)
  then show ?thesis
    by (simp add: res_to_cong_simps)
qed

*)

(* outside the locale, we can relax the restriction m > 1 *)

lemma euler_theorem:
  assumes "m >= 0" and "gcd a m = 1"
  shows "[a^phi m = 1] (mod m)"
proof (cases)
  assume "m = 0 | m = 1"
  then show ?thesis by auto
next
  assume "~(m = 0 | m = 1)"
  with assms show ?thesis
    by (intro residues.euler_theorem1, unfold residues_def, auto)
qed

lemma (in residues_prime) phi_prime: "phi p = (nat p - 1)"
  apply (subst phi_eq)
  apply (subst res_prime_units_eq)
  apply auto
  done

lemma phi_prime: "prime p \<Longrightarrow> phi p = (nat p - 1)"
  apply (rule residues_prime.phi_prime)
  apply (erule residues_prime.intro)
  done

lemma fermat_theorem:
  fixes a::int
  assumes "prime p" and "~ (p dvd a)"
  shows "[a^(p - 1) = 1] (mod p)"
proof -
  from assms have "[a^phi p = 1] (mod p)"
    apply (intro euler_theorem)
    apply (metis of_nat_0_le_iff)
    apply (metis gcd_int.commute prime_imp_coprime_int)
    done
  also have "phi p = nat p - 1"
    by (rule phi_prime, rule assms)
  finally show ?thesis
    by (metis nat_int)
qed

lemma fermat_theorem_nat:
  assumes "prime p" and "~ (p dvd a)"
  shows "[a^(p - 1) = 1] (mod p)"
using fermat_theorem [of p a] assms
by (metis int_1 of_nat_power transfer_int_nat_cong zdvd_int)


subsection {* Wilson's theorem *}

lemma (in field) inv_pair_lemma: "x : Units R \<Longrightarrow> y : Units R \<Longrightarrow>
    {x, inv x} ~= {y, inv y} \<Longrightarrow> {x, inv x} Int {y, inv y} = {}"
  apply auto
  apply (metis Units_inv_inv)+
  done

lemma (in residues_prime) wilson_theorem1:
  assumes a: "p > 2"
  shows "[fact (p - 1) = (-1::int)] (mod p)"
proof -
  let ?InversePairs = "{ {x, inv x} | x. x : Units R - {\<one>, \<ominus> \<one>}}"
  have UR: "Units R = {\<one>, \<ominus> \<one>} Un (Union ?InversePairs)"
    by auto
  have "(\<Otimes>i: Units R. i) =
    (\<Otimes>i: {\<one>, \<ominus> \<one>}. i) \<otimes> (\<Otimes>i: Union ?InversePairs. i)"
    apply (subst UR)
    apply (subst finprod_Un_disjoint)
    apply (auto intro: funcsetI)
    apply (metis Units_inv_inv inv_one inv_neg_one)+
    done
  also have "(\<Otimes>i: {\<one>, \<ominus> \<one>}. i) = \<ominus> \<one>"
    apply (subst finprod_insert)
    apply auto
    apply (frule one_eq_neg_one)
    apply (insert a, force)
    done
  also have "(\<Otimes>i:(Union ?InversePairs). i) =
      (\<Otimes>A: ?InversePairs. (\<Otimes>y:A. y))"
    apply (subst finprod_Union_disjoint, auto)
    apply (metis Units_inv_inv)+
    done
  also have "\<dots> = \<one>"
    apply (rule finprod_one, auto)
    apply (subst finprod_insert, auto)
    apply (metis inv_eq_self)
    done
  finally have "(\<Otimes>i: Units R. i) = \<ominus> \<one>"
    by simp
  also have "(\<Otimes>i: Units R. i) = (\<Otimes>i: Units R. i mod p)"
    apply (rule finprod_cong')
    apply (auto)
    apply (subst (asm) res_prime_units_eq)
    apply auto
    done
  also have "\<dots> = (PROD i: Units R. i) mod p"
    apply (rule prod_cong)
    apply auto
    done
  also have "\<dots> = fact (p - 1) mod p"
    apply (subst fact_altdef_nat)
    apply (insert assms)
    apply (subst res_prime_units_eq)
    apply (simp add: int_setprod zmod_int setprod_int_eq)
    done
  finally have "fact (p - 1) mod p = (\<ominus> \<one> :: int)".
  then show ?thesis  
    by (metis of_nat_fact Divides.transfer_int_nat_functions(2) cong_int_def res_neg_eq res_one_eq)
qed

lemma wilson_theorem:
  assumes "prime p" shows "[fact (p - 1) = - 1] (mod p)"
proof (cases "p = 2")
  case True
  then show ?thesis
    by (simp add: cong_int_def fact_altdef_nat)
next
  case False
  then show ?thesis
    using assms prime_ge_2_nat
    by (metis residues_prime.wilson_theorem1 residues_prime.intro le_eq_less_or_eq)
qed

end
