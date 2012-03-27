(*  Title:      HOL/Number_Theory/Residues.thy
    Author:     Jeremy Avigad

An algebraic treatment of residue rings, and resulting proofs of
Euler's theorem and Wilson's theorem.
*)

header {* Residue rings *}

theory Residues
imports
  UniqueFactorization
  Binomial
  MiscAlgebra
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
  apply (auto simp add: mod_add_right_eq [symmetric] add_ac)
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
  apply (simp_all only: mult_ac)
  done

lemma cring: "cring R"
  apply (rule cringI)
  apply (rule abelian_group)
  apply (rule comm_monoid)
  apply (unfold R_def residue_ring_def, auto)
  apply (subst mod_add_eq [symmetric])
  apply (subst mult_commute)
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
  apply (rule invertible_coprime_int)
  apply (subgoal_tac "x ~= 0")
  apply auto
  apply (subst (asm) coprime_iff_invertible'_int)
  apply (rule m_gt_one)
  apply (auto simp add: cong_int_def mult_commute)
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
  apply (subst zmod_eq_dvd_iff)
  apply auto
  done

lemma finite [iff]: "finite (carrier R)"
  by (subst res_carrier_eq, auto)

lemma finite_Units [iff]: "finite (Units R)"
  by (subst res_units_eq, auto)

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
  apply (unfold R_def residue_ring_def, auto)
  apply (subst mod_mult_right_eq [symmetric])
  apply (subst mult_commute)
  apply (subst mod_mult_right_eq [symmetric])
  apply (subst mult_commute)
  apply auto
  done

lemma zero_cong: "\<zero> = 0"
  unfolding R_def residue_ring_def by auto

lemma one_cong: "\<one> = 1 mod m"
  using m_gt_one unfolding R_def residue_ring_def by auto

(* revise algebra library to use 1? *)
lemma pow_cong: "(x mod m) (^) n = x^n mod m"
  apply (insert m_gt_one)
  apply (induct n)
  apply (auto simp add: nat_pow_def one_cong)
  apply (subst mult_commute)
  apply (rule mult_cong)
  done

lemma neg_cong: "\<ominus> (x mod m) = (- x) mod m"
  apply (rule sym)
  apply (rule sum_zero_eq_neg)
  apply auto
  apply (subst add_cong)
  apply (subst zero_cong)
  apply auto
  done

lemma (in residues) prod_cong:
    "finite A \<Longrightarrow> (\<Otimes> i:A. (f i) mod m) = (PROD i:A. f i) mod m"
  apply (induct set: finite)
  apply (auto simp: one_cong mult_cong)
  done

lemma (in residues) sum_cong:
    "finite A \<Longrightarrow> (\<Oplus> i:A. (f i) mod m) = (SUM i: A. f i) mod m"
  apply (induct set: finite)
  apply (auto simp: zero_cong add_cong)
  done

lemma mod_in_res_units [simp]: "1 < m \<Longrightarrow> coprime a m \<Longrightarrow>
    a mod m : Units R"
  apply (subst res_units_eq, auto)
  apply (insert pos_mod_sign [of m a])
  apply (subgoal_tac "a mod m ~= 0")
  apply arith
  apply auto
  apply (subst (asm) gcd_red_int)
  apply (subst gcd_commute_int, assumption)
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
  apply (insert m_gt_one)
  apply (subgoal_tac "~(m > 2)")
  apply arith
  apply (rule notI)
  apply (subgoal_tac "-1 mod m = m - 1")
  apply force
  apply (subst mod_add_self2 [symmetric])
  apply (subst mod_pos_pos_trivial)
  apply auto
  done

end


(* prime residues *)

locale residues_prime =
  fixes p :: int and R (structure)
  assumes p_prime [intro]: "prime p"
  defines "R == residue_ring p"

sublocale residues_prime < residues p
  apply (unfold R_def residues_def)
  using p_prime apply auto
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
  apply (rule prime_imp_coprime_int)
  apply (rule p_prime)
  apply (rule zdvd_not_zless)
  apply auto
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
  assumes "prime p" and "~ (p dvd a)"
  shows "[a^(nat p - 1) = 1] (mod p)"
proof -
  from assms have "[a^phi p = 1] (mod p)"
    apply (intro euler_theorem)
    (* auto should get this next part. matching across
       substitutions is needed. *)
    apply (frule prime_gt_1_int, arith)
    apply (subst gcd_commute_int, erule prime_imp_coprime_int, assumption)
    done
  also have "phi p = nat p - 1"
    by (rule phi_prime, rule assms)
  finally show ?thesis .
qed


subsection {* Wilson's theorem *}

lemma (in field) inv_pair_lemma: "x : Units R \<Longrightarrow> y : Units R \<Longrightarrow>
    {x, inv x} ~= {y, inv y} \<Longrightarrow> {x, inv x} Int {y, inv y} = {}"
  apply auto
  apply (erule notE)
  apply (erule inv_eq_imp_eq)
  apply auto
  apply (erule notE)
  apply (erule inv_eq_imp_eq)
  apply auto
  done

lemma (in residues_prime) wilson_theorem1:
  assumes a: "p > 2"
  shows "[fact (p - 1) = - 1] (mod p)"
proof -
  let ?InversePairs = "{ {x, inv x} | x. x : Units R - {\<one>, \<ominus> \<one>}}"
  have UR: "Units R = {\<one>, \<ominus> \<one>} Un (Union ?InversePairs)"
    by auto
  have "(\<Otimes>i: Units R. i) =
    (\<Otimes>i: {\<one>, \<ominus> \<one>}. i) \<otimes> (\<Otimes>i: Union ?InversePairs. i)"
    apply (subst UR)
    apply (subst finprod_Un_disjoint)
    apply (auto intro:funcsetI)
    apply (drule sym, subst (asm) inv_eq_one_eq)
    apply auto
    apply (drule sym, subst (asm) inv_eq_neg_one_eq)
    apply auto
    done
  also have "(\<Otimes>i: {\<one>, \<ominus> \<one>}. i) = \<ominus> \<one>"
    apply (subst finprod_insert)
    apply auto
    apply (frule one_eq_neg_one)
    apply (insert a, force)
    done
  also have "(\<Otimes>i:(Union ?InversePairs). i) =
      (\<Otimes>A: ?InversePairs. (\<Otimes>y:A. y))"
    apply (subst finprod_Union_disjoint)
    apply force
    apply force
    apply clarify
    apply (rule inv_pair_lemma)
    apply auto
    done
  also have "\<dots> = \<one>"
    apply (rule finprod_one)
    apply auto
    apply (subst finprod_insert)
    apply auto
    apply (frule inv_eq_self)
    apply (auto)
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
    apply (subst fact_altdef_int)
    apply (insert assms, force)
    apply (subst res_prime_units_eq, rule refl)
    done
  finally have "fact (p - 1) mod p = \<ominus> \<one>".
  then show ?thesis by (simp add: res_to_cong_simps)
qed

lemma wilson_theorem: "prime (p::int) \<Longrightarrow> [fact (p - 1) = - 1] (mod p)"
  apply (frule prime_gt_1_int)
  apply (case_tac "p = 2")
  apply (subst fact_altdef_int, simp)
  apply (subst cong_int_def)
  apply simp
  apply (rule residues_prime.wilson_theorem1)
  apply (rule residues_prime.intro)
  apply auto
  done

end
