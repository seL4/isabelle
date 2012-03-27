(*  Title:      HOL/Number_Theory/Cong.thy
    Authors:    Christophe Tabacznyj, Lawrence C. Paulson, Amine Chaieb,
                Thomas M. Rasmussen, Jeremy Avigad

Defines congruence (notation: [x = y] (mod z)) for natural numbers and
integers.

This file combines and revises a number of prior developments.

The original theories "GCD" and "Primes" were by Christophe Tabacznyj
and Lawrence C. Paulson, based on \cite{davenport92}. They introduced
gcd, lcm, and prime for the natural numbers.

The original theory "IntPrimes" was by Thomas M. Rasmussen, and
extended gcd, lcm, primes to the integers. Amine Chaieb provided
another extension of the notions to the integers, and added a number
of results to "Primes" and "GCD".

The original theory, "IntPrimes", by Thomas M. Rasmussen, defined and
developed the congruence relations on the integers. The notion was
extended to the natural numbers by Chaieb. Jeremy Avigad combined
these, revised and tidied them, made the development uniform for the
natural numbers and the integers, and added a number of new theorems.
*)

header {* Congruence *}

theory Cong
imports Primes
begin

subsection {* Turn off @{text One_nat_def} *}

lemma induct'_nat [case_names zero plus1, induct type: nat]:
    "P (0::nat) \<Longrightarrow> (\<And>n. P n \<Longrightarrow> P (n + 1)) \<Longrightarrow> P n"
  by (induct n) (simp_all add: One_nat_def)

lemma cases_nat [case_names zero plus1, cases type: nat]:
    "P (0::nat) \<Longrightarrow> (\<And>n. P (n + 1)) \<Longrightarrow> P n"
  by (rule induct'_nat)

lemma power_plus_one [simp]: "(x::'a::power)^(n + 1) = x * x^n"
  by (simp add: One_nat_def)

lemma power_eq_one_eq_nat [simp]: "((x::nat)^m = 1) = (m = 0 | x = 1)"
  by (induct m) auto

lemma card_insert_if' [simp]: "finite A \<Longrightarrow>
    card (insert x A) = (if x \<in> A then (card A) else (card A) + 1)"
  by (auto simp add: insert_absorb)

lemma nat_1' [simp]: "nat 1 = 1"
  by simp

(* For those annoying moments where Suc reappears, use Suc_eq_plus1 *)

declare nat_1 [simp del]
declare add_2_eq_Suc [simp del]
declare add_2_eq_Suc' [simp del]


declare mod_pos_pos_trivial [simp]


subsection {* Main definitions *}

class cong =
  fixes cong :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("(1[_ = _] '(mod _'))")
begin

abbreviation notcong :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  ("(1[_ \<noteq> _] '(mod _'))")
  where "notcong x y m \<equiv> \<not> cong x y m"

end

(* definitions for the natural numbers *)

instantiation nat :: cong
begin

definition cong_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "cong_nat x y m = ((x mod m) = (y mod m))"

instance ..

end


(* definitions for the integers *)

instantiation int :: cong
begin

definition cong_int :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
  where "cong_int x y m = ((x mod m) = (y mod m))"

instance ..

end


subsection {* Set up Transfer *}


lemma transfer_nat_int_cong:
  "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> m >= 0 \<Longrightarrow>
    ([(nat x) = (nat y)] (mod (nat m))) = ([x = y] (mod m))"
  unfolding cong_int_def cong_nat_def
  apply (auto simp add: nat_mod_distrib [symmetric])
  apply (subst (asm) eq_nat_nat_iff)
  apply (cases "m = 0", force, rule pos_mod_sign, force)+
  apply assumption
  done

declare transfer_morphism_nat_int[transfer add return:
    transfer_nat_int_cong]

lemma transfer_int_nat_cong:
  "[(int x) = (int y)] (mod (int m)) = [x = y] (mod m)"
  apply (auto simp add: cong_int_def cong_nat_def)
  apply (auto simp add: zmod_int [symmetric])
  done

declare transfer_morphism_int_nat[transfer add return:
    transfer_int_nat_cong]


subsection {* Congruence *}

(* was zcong_0, etc. *)
lemma cong_0_nat [simp, presburger]: "([(a::nat) = b] (mod 0)) = (a = b)"
  unfolding cong_nat_def by auto

lemma cong_0_int [simp, presburger]: "([(a::int) = b] (mod 0)) = (a = b)"
  unfolding cong_int_def by auto

lemma cong_1_nat [simp, presburger]: "[(a::nat) = b] (mod 1)"
  unfolding cong_nat_def by auto

lemma cong_Suc_0_nat [simp, presburger]: "[(a::nat) = b] (mod Suc 0)"
  unfolding cong_nat_def by (auto simp add: One_nat_def)

lemma cong_1_int [simp, presburger]: "[(a::int) = b] (mod 1)"
  unfolding cong_int_def by auto

lemma cong_refl_nat [simp]: "[(k::nat) = k] (mod m)"
  unfolding cong_nat_def by auto

lemma cong_refl_int [simp]: "[(k::int) = k] (mod m)"
  unfolding cong_int_def by auto

lemma cong_sym_nat: "[(a::nat) = b] (mod m) \<Longrightarrow> [b = a] (mod m)"
  unfolding cong_nat_def by auto

lemma cong_sym_int: "[(a::int) = b] (mod m) \<Longrightarrow> [b = a] (mod m)"
  unfolding cong_int_def by auto

lemma cong_sym_eq_nat: "[(a::nat) = b] (mod m) = [b = a] (mod m)"
  unfolding cong_nat_def by auto

lemma cong_sym_eq_int: "[(a::int) = b] (mod m) = [b = a] (mod m)"
  unfolding cong_int_def by auto

lemma cong_trans_nat [trans]:
    "[(a::nat) = b] (mod m) \<Longrightarrow> [b = c] (mod m) \<Longrightarrow> [a = c] (mod m)"
  unfolding cong_nat_def by auto

lemma cong_trans_int [trans]:
    "[(a::int) = b] (mod m) \<Longrightarrow> [b = c] (mod m) \<Longrightarrow> [a = c] (mod m)"
  unfolding cong_int_def by auto

lemma cong_add_nat:
    "[(a::nat) = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a + c = b + d] (mod m)"
  apply (unfold cong_nat_def)
  apply (subst (1 2) mod_add_eq)
  apply simp
  done

lemma cong_add_int:
    "[(a::int) = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a + c = b + d] (mod m)"
  apply (unfold cong_int_def)
  apply (subst (1 2) mod_add_left_eq)
  apply (subst (1 2) mod_add_right_eq)
  apply simp
  done

lemma cong_diff_int:
    "[(a::int) = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a - c = b - d] (mod m)"
  apply (unfold cong_int_def)
  apply (subst (1 2) mod_diff_eq)
  apply simp
  done

lemma cong_diff_aux_int:
  "(a::int) >= c \<Longrightarrow> b >= d \<Longrightarrow> [(a::int) = b] (mod m) \<Longrightarrow>
      [c = d] (mod m) \<Longrightarrow> [tsub a c = tsub b d] (mod m)"
  apply (subst (1 2) tsub_eq)
  apply (auto intro: cong_diff_int)
  done

lemma cong_diff_nat:
  assumes "(a::nat) >= c" and "b >= d" and "[a = b] (mod m)" and
    "[c = d] (mod m)"
  shows "[a - c = b - d] (mod m)"
  using assms by (rule cong_diff_aux_int [transferred]);

lemma cong_mult_nat:
    "[(a::nat) = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a * c = b * d] (mod m)"
  apply (unfold cong_nat_def)
  apply (subst (1 2) mod_mult_eq)
  apply simp
  done

lemma cong_mult_int:
    "[(a::int) = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a * c = b * d] (mod m)"
  apply (unfold cong_int_def)
  apply (subst (1 2) mod_mult_right_eq)
  apply (subst (1 2) mult_commute)
  apply (subst (1 2) mod_mult_right_eq)
  apply simp
  done

lemma cong_exp_nat: "[(x::nat) = y] (mod n) \<Longrightarrow> [x^k = y^k] (mod n)"
  by (induct k) (auto simp add: cong_mult_nat)

lemma cong_exp_int: "[(x::int) = y] (mod n) \<Longrightarrow> [x^k = y^k] (mod n)"
  by (induct k) (auto simp add: cong_mult_int)

lemma cong_setsum_nat [rule_format]:
    "(ALL x: A. [((f x)::nat) = g x] (mod m)) \<longrightarrow>
      [(SUM x:A. f x) = (SUM x:A. g x)] (mod m)"
  apply (cases "finite A")
  apply (induct set: finite)
  apply (auto intro: cong_add_nat)
  done

lemma cong_setsum_int [rule_format]:
    "(ALL x: A. [((f x)::int) = g x] (mod m)) \<longrightarrow>
      [(SUM x:A. f x) = (SUM x:A. g x)] (mod m)"
  apply (cases "finite A")
  apply (induct set: finite)
  apply (auto intro: cong_add_int)
  done

lemma cong_setprod_nat [rule_format]:
    "(ALL x: A. [((f x)::nat) = g x] (mod m)) \<longrightarrow>
      [(PROD x:A. f x) = (PROD x:A. g x)] (mod m)"
  apply (cases "finite A")
  apply (induct set: finite)
  apply (auto intro: cong_mult_nat)
  done

lemma cong_setprod_int [rule_format]:
    "(ALL x: A. [((f x)::int) = g x] (mod m)) \<longrightarrow>
      [(PROD x:A. f x) = (PROD x:A. g x)] (mod m)"
  apply (cases "finite A")
  apply (induct set: finite)
  apply (auto intro: cong_mult_int)
  done

lemma cong_scalar_nat: "[(a::nat)= b] (mod m) \<Longrightarrow> [a * k = b * k] (mod m)"
  by (rule cong_mult_nat) simp_all

lemma cong_scalar_int: "[(a::int)= b] (mod m) \<Longrightarrow> [a * k = b * k] (mod m)"
  by (rule cong_mult_int) simp_all

lemma cong_scalar2_nat: "[(a::nat)= b] (mod m) \<Longrightarrow> [k * a = k * b] (mod m)"
  by (rule cong_mult_nat) simp_all

lemma cong_scalar2_int: "[(a::int)= b] (mod m) \<Longrightarrow> [k * a = k * b] (mod m)"
  by (rule cong_mult_int) simp_all

lemma cong_mult_self_nat: "[(a::nat) * m = 0] (mod m)"
  unfolding cong_nat_def by auto

lemma cong_mult_self_int: "[(a::int) * m = 0] (mod m)"
  unfolding cong_int_def by auto

lemma cong_eq_diff_cong_0_int: "[(a::int) = b] (mod m) = [a - b = 0] (mod m)"
  apply (rule iffI)
  apply (erule cong_diff_int [of a b m b b, simplified])
  apply (erule cong_add_int [of "a - b" 0 m b b, simplified])
  done

lemma cong_eq_diff_cong_0_aux_int: "a >= b \<Longrightarrow>
    [(a::int) = b] (mod m) = [tsub a b = 0] (mod m)"
  by (subst tsub_eq, assumption, rule cong_eq_diff_cong_0_int)

lemma cong_eq_diff_cong_0_nat:
  assumes "(a::nat) >= b"
  shows "[a = b] (mod m) = [a - b = 0] (mod m)"
  using assms by (rule cong_eq_diff_cong_0_aux_int [transferred])

lemma cong_diff_cong_0'_nat:
  "[(x::nat) = y] (mod n) \<longleftrightarrow>
    (if x <= y then [y - x = 0] (mod n) else [x - y = 0] (mod n))"
  apply (cases "y <= x")
  apply (frule cong_eq_diff_cong_0_nat [where m = n])
  apply auto [1]
  apply (subgoal_tac "x <= y")
  apply (frule cong_eq_diff_cong_0_nat [where m = n])
  apply (subst cong_sym_eq_nat)
  apply auto
  done

lemma cong_altdef_nat: "(a::nat) >= b \<Longrightarrow> [a = b] (mod m) = (m dvd (a - b))"
  apply (subst cong_eq_diff_cong_0_nat, assumption)
  apply (unfold cong_nat_def)
  apply (simp add: dvd_eq_mod_eq_0 [symmetric])
  done

lemma cong_altdef_int: "[(a::int) = b] (mod m) = (m dvd (a - b))"
  apply (subst cong_eq_diff_cong_0_int)
  apply (unfold cong_int_def)
  apply (simp add: dvd_eq_mod_eq_0 [symmetric])
  done

lemma cong_abs_int: "[(x::int) = y] (mod abs m) = [x = y] (mod m)"
  by (simp add: cong_altdef_int)

lemma cong_square_int:
   "\<lbrakk> prime (p::int); 0 < a; [a * a = 1] (mod p) \<rbrakk>
    \<Longrightarrow> [a = 1] (mod p) \<or> [a = - 1] (mod p)"
  apply (simp only: cong_altdef_int)
  apply (subst prime_dvd_mult_eq_int [symmetric], assumption)
  (* any way around this? *)
  apply (subgoal_tac "a * a - 1 = (a - 1) * (a - -1)")
  apply (auto simp add: field_simps)
  done

lemma cong_mult_rcancel_int:
    "coprime k (m::int) \<Longrightarrow> [a * k = b * k] (mod m) = [a = b] (mod m)"
  apply (subst (1 2) cong_altdef_int)
  apply (subst left_diff_distrib [symmetric])
  apply (rule coprime_dvd_mult_iff_int)
  apply (subst gcd_commute_int, assumption)
  done

lemma cong_mult_rcancel_nat:
  assumes  "coprime k (m::nat)"
  shows "[a * k = b * k] (mod m) = [a = b] (mod m)"
  apply (rule cong_mult_rcancel_int [transferred])
  using assms apply auto
  done

lemma cong_mult_lcancel_nat:
    "coprime k (m::nat) \<Longrightarrow> [k * a = k * b ] (mod m) = [a = b] (mod m)"
  by (simp add: mult_commute cong_mult_rcancel_nat)

lemma cong_mult_lcancel_int:
    "coprime k (m::int) \<Longrightarrow> [k * a = k * b] (mod m) = [a = b] (mod m)"
  by (simp add: mult_commute cong_mult_rcancel_int)

(* was zcong_zgcd_zmult_zmod *)
lemma coprime_cong_mult_int:
  "[(a::int) = b] (mod m) \<Longrightarrow> [a = b] (mod n) \<Longrightarrow> coprime m n
    \<Longrightarrow> [a = b] (mod m * n)"
  apply (simp only: cong_altdef_int)
  apply (erule (2) divides_mult_int)
  done

lemma coprime_cong_mult_nat:
  assumes "[(a::nat) = b] (mod m)" and "[a = b] (mod n)" and "coprime m n"
  shows "[a = b] (mod m * n)"
  apply (rule coprime_cong_mult_int [transferred])
  using assms apply auto
  done

lemma cong_less_imp_eq_nat: "0 \<le> (a::nat) \<Longrightarrow>
    a < m \<Longrightarrow> 0 \<le> b \<Longrightarrow> b < m \<Longrightarrow> [a = b] (mod m) \<Longrightarrow> a = b"
  by (auto simp add: cong_nat_def)

lemma cong_less_imp_eq_int: "0 \<le> (a::int) \<Longrightarrow>
    a < m \<Longrightarrow> 0 \<le> b \<Longrightarrow> b < m \<Longrightarrow> [a = b] (mod m) \<Longrightarrow> a = b"
  by (auto simp add: cong_int_def)

lemma cong_less_unique_nat:
    "0 < (m::nat) \<Longrightarrow> (\<exists>!b. 0 \<le> b \<and> b < m \<and> [a = b] (mod m))"
  apply auto
  apply (rule_tac x = "a mod m" in exI)
  apply (unfold cong_nat_def, auto)
  done

lemma cong_less_unique_int:
    "0 < (m::int) \<Longrightarrow> (\<exists>!b. 0 \<le> b \<and> b < m \<and> [a = b] (mod m))"
  apply auto
  apply (rule_tac x = "a mod m" in exI)
  apply (unfold cong_int_def, auto)
  done

lemma cong_iff_lin_int: "([(a::int) = b] (mod m)) = (\<exists>k. b = a + m * k)"
  apply (auto simp add: cong_altdef_int dvd_def field_simps)
  apply (rule_tac [!] x = "-k" in exI, auto)
  done

lemma cong_iff_lin_nat: "([(a::nat) = b] (mod m)) =
    (\<exists>k1 k2. b + k1 * m = a + k2 * m)"
  apply (rule iffI)
  apply (cases "b <= a")
  apply (subst (asm) cong_altdef_nat, assumption)
  apply (unfold dvd_def, auto)
  apply (rule_tac x = k in exI)
  apply (rule_tac x = 0 in exI)
  apply (auto simp add: field_simps)
  apply (subst (asm) cong_sym_eq_nat)
  apply (subst (asm) cong_altdef_nat)
  apply force
  apply (unfold dvd_def, auto)
  apply (rule_tac x = 0 in exI)
  apply (rule_tac x = k in exI)
  apply (auto simp add: field_simps)
  apply (unfold cong_nat_def)
  apply (subgoal_tac "a mod m = (a + k2 * m) mod m")
  apply (erule ssubst)back
  apply (erule subst)
  apply auto
  done

lemma cong_gcd_eq_int: "[(a::int) = b] (mod m) \<Longrightarrow> gcd a m = gcd b m"
  apply (subst (asm) cong_iff_lin_int, auto)
  apply (subst add_commute)
  apply (subst (2) gcd_commute_int)
  apply (subst mult_commute)
  apply (subst gcd_add_mult_int)
  apply (rule gcd_commute_int)
  done

lemma cong_gcd_eq_nat:
  assumes "[(a::nat) = b] (mod m)"
  shows "gcd a m = gcd b m"
  apply (rule cong_gcd_eq_int [transferred])
  using assms apply auto
  done

lemma cong_imp_coprime_nat: "[(a::nat) = b] (mod m) \<Longrightarrow> coprime a m \<Longrightarrow> coprime b m"
  by (auto simp add: cong_gcd_eq_nat)

lemma cong_imp_coprime_int: "[(a::int) = b] (mod m) \<Longrightarrow> coprime a m \<Longrightarrow> coprime b m"
  by (auto simp add: cong_gcd_eq_int)

lemma cong_cong_mod_nat: "[(a::nat) = b] (mod m) = [a mod m = b mod m] (mod m)"
  by (auto simp add: cong_nat_def)

lemma cong_cong_mod_int: "[(a::int) = b] (mod m) = [a mod m = b mod m] (mod m)"
  by (auto simp add: cong_int_def)

lemma cong_minus_int [iff]: "[(a::int) = b] (mod -m) = [a = b] (mod m)"
  apply (subst (1 2) cong_altdef_int)
  apply auto
  done

lemma cong_zero_nat: "[(a::nat) = b] (mod 0) = (a = b)"
  by auto

lemma cong_zero_int: "[(a::int) = b] (mod 0) = (a = b)"
  by auto

(*
lemma mod_dvd_mod_int:
    "0 < (m::int) \<Longrightarrow> m dvd b \<Longrightarrow> (a mod b mod m) = (a mod m)"
  apply (unfold dvd_def, auto)
  apply (rule mod_mod_cancel)
  apply auto
  done

lemma mod_dvd_mod:
  assumes "0 < (m::nat)" and "m dvd b"
  shows "(a mod b mod m) = (a mod m)"

  apply (rule mod_dvd_mod_int [transferred])
  using assms apply auto
  done
*)

lemma cong_add_lcancel_nat:
    "[(a::nat) + x = a + y] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  by (simp add: cong_iff_lin_nat)

lemma cong_add_lcancel_int:
    "[(a::int) + x = a + y] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  by (simp add: cong_iff_lin_int)

lemma cong_add_rcancel_nat: "[(x::nat) + a = y + a] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  by (simp add: cong_iff_lin_nat)

lemma cong_add_rcancel_int: "[(x::int) + a = y + a] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  by (simp add: cong_iff_lin_int)

lemma cong_add_lcancel_0_nat: "[(a::nat) + x = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)"
  by (simp add: cong_iff_lin_nat)

lemma cong_add_lcancel_0_int: "[(a::int) + x = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)"
  by (simp add: cong_iff_lin_int)

lemma cong_add_rcancel_0_nat: "[x + (a::nat) = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)"
  by (simp add: cong_iff_lin_nat)

lemma cong_add_rcancel_0_int: "[x + (a::int) = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)"
  by (simp add: cong_iff_lin_int)

lemma cong_dvd_modulus_nat: "[(x::nat) = y] (mod m) \<Longrightarrow> n dvd m \<Longrightarrow>
    [x = y] (mod n)"
  apply (auto simp add: cong_iff_lin_nat dvd_def)
  apply (rule_tac x="k1 * k" in exI)
  apply (rule_tac x="k2 * k" in exI)
  apply (simp add: field_simps)
  done

lemma cong_dvd_modulus_int: "[(x::int) = y] (mod m) \<Longrightarrow> n dvd m \<Longrightarrow> [x = y] (mod n)"
  by (auto simp add: cong_altdef_int dvd_def)

lemma cong_dvd_eq_nat: "[(x::nat) = y] (mod n) \<Longrightarrow> n dvd x \<longleftrightarrow> n dvd y"
  unfolding cong_nat_def by (auto simp add: dvd_eq_mod_eq_0)

lemma cong_dvd_eq_int: "[(x::int) = y] (mod n) \<Longrightarrow> n dvd x \<longleftrightarrow> n dvd y"
  unfolding cong_int_def by (auto simp add: dvd_eq_mod_eq_0)

lemma cong_mod_nat: "(n::nat) ~= 0 \<Longrightarrow> [a mod n = a] (mod n)"
  by (simp add: cong_nat_def)

lemma cong_mod_int: "(n::int) ~= 0 \<Longrightarrow> [a mod n = a] (mod n)"
  by (simp add: cong_int_def)

lemma mod_mult_cong_nat: "(a::nat) ~= 0 \<Longrightarrow> b ~= 0
    \<Longrightarrow> [x mod (a * b) = y] (mod a) \<longleftrightarrow> [x = y] (mod a)"
  by (simp add: cong_nat_def mod_mult2_eq  mod_add_left_eq)

lemma neg_cong_int: "([(a::int) = b] (mod m)) = ([-a = -b] (mod m))"
  apply (simp add: cong_altdef_int)
  apply (subst dvd_minus_iff [symmetric])
  apply (simp add: field_simps)
  done

lemma cong_modulus_neg_int: "([(a::int) = b] (mod m)) = ([a = b] (mod -m))"
  by (auto simp add: cong_altdef_int)

lemma mod_mult_cong_int: "(a::int) ~= 0 \<Longrightarrow> b ~= 0
    \<Longrightarrow> [x mod (a * b) = y] (mod a) \<longleftrightarrow> [x = y] (mod a)"
  apply (cases "b > 0")
  apply (simp add: cong_int_def mod_mod_cancel mod_add_left_eq)
  apply (subst (1 2) cong_modulus_neg_int)
  apply (unfold cong_int_def)
  apply (subgoal_tac "a * b = (-a * -b)")
  apply (erule ssubst)
  apply (subst zmod_zmult2_eq)
  apply (auto simp add: mod_add_left_eq)
  done

lemma cong_to_1_nat: "([(a::nat) = 1] (mod n)) \<Longrightarrow> (n dvd (a - 1))"
  apply (cases "a = 0")
  apply force
  apply (subst (asm) cong_altdef_nat)
  apply auto
  done

lemma cong_0_1_nat: "[(0::nat) = 1] (mod n) = (n = 1)"
  unfolding cong_nat_def by auto

lemma cong_0_1_int: "[(0::int) = 1] (mod n) = ((n = 1) | (n = -1))"
  unfolding cong_int_def by (auto simp add: zmult_eq_1_iff)

lemma cong_to_1'_nat: "[(a::nat) = 1] (mod n) \<longleftrightarrow>
    a = 0 \<and> n = 1 \<or> (\<exists>m. a = 1 + m * n)"
  apply (cases "n = 1")
  apply auto [1]
  apply (drule_tac x = "a - 1" in spec)
  apply force
  apply (cases "a = 0")
  apply (auto simp add: cong_0_1_nat) [1]
  apply (rule iffI)
  apply (drule cong_to_1_nat)
  apply (unfold dvd_def)
  apply auto [1]
  apply (rule_tac x = k in exI)
  apply (auto simp add: field_simps) [1]
  apply (subst cong_altdef_nat)
  apply (auto simp add: dvd_def)
  done

lemma cong_le_nat: "(y::nat) <= x \<Longrightarrow> [x = y] (mod n) \<longleftrightarrow> (\<exists>q. x = q * n + y)"
  apply (subst cong_altdef_nat)
  apply assumption
  apply (unfold dvd_def, auto simp add: field_simps)
  apply (rule_tac x = k in exI)
  apply auto
  done

lemma cong_solve_nat: "(a::nat) \<noteq> 0 \<Longrightarrow> EX x. [a * x = gcd a n] (mod n)"
  apply (cases "n = 0")
  apply force
  apply (frule bezout_nat [of a n], auto)
  apply (rule exI, erule ssubst)
  apply (rule cong_trans_nat)
  apply (rule cong_add_nat)
  apply (subst mult_commute)
  apply (rule cong_mult_self_nat)
  prefer 2
  apply simp
  apply (rule cong_refl_nat)
  apply (rule cong_refl_nat)
  done

lemma cong_solve_int: "(a::int) \<noteq> 0 \<Longrightarrow> EX x. [a * x = gcd a n] (mod n)"
  apply (cases "n = 0")
  apply (cases "a \<ge> 0")
  apply auto
  apply (rule_tac x = "-1" in exI)
  apply auto
  apply (insert bezout_int [of a n], auto)
  apply (rule exI)
  apply (erule subst)
  apply (rule cong_trans_int)
  prefer 2
  apply (rule cong_add_int)
  apply (rule cong_refl_int)
  apply (rule cong_sym_int)
  apply (rule cong_mult_self_int)
  apply simp
  apply (subst mult_commute)
  apply (rule cong_refl_int)
  done

lemma cong_solve_dvd_nat:
  assumes a: "(a::nat) \<noteq> 0" and b: "gcd a n dvd d"
  shows "EX x. [a * x = d] (mod n)"
proof -
  from cong_solve_nat [OF a] obtain x where "[a * x = gcd a n](mod n)"
    by auto
  then have "[(d div gcd a n) * (a * x) = (d div gcd a n) * gcd a n] (mod n)"
    by (elim cong_scalar2_nat)
  also from b have "(d div gcd a n) * gcd a n = d"
    by (rule dvd_div_mult_self)
  also have "(d div gcd a n) * (a * x) = a * (d div gcd a n * x)"
    by auto
  finally show ?thesis
    by auto
qed

lemma cong_solve_dvd_int:
  assumes a: "(a::int) \<noteq> 0" and b: "gcd a n dvd d"
  shows "EX x. [a * x = d] (mod n)"
proof -
  from cong_solve_int [OF a] obtain x where "[a * x = gcd a n](mod n)"
    by auto
  then have "[(d div gcd a n) * (a * x) = (d div gcd a n) * gcd a n] (mod n)"
    by (elim cong_scalar2_int)
  also from b have "(d div gcd a n) * gcd a n = d"
    by (rule dvd_div_mult_self)
  also have "(d div gcd a n) * (a * x) = a * (d div gcd a n * x)"
    by auto
  finally show ?thesis
    by auto
qed

lemma cong_solve_coprime_nat: "coprime (a::nat) n \<Longrightarrow> EX x. [a * x = 1] (mod n)"
  apply (cases "a = 0")
  apply force
  apply (frule cong_solve_nat [of a n])
  apply auto
  done

lemma cong_solve_coprime_int: "coprime (a::int) n \<Longrightarrow> EX x. [a * x = 1] (mod n)"
  apply (cases "a = 0")
  apply auto
  apply (cases "n \<ge> 0")
  apply auto
  apply (subst cong_int_def, auto)
  apply (frule cong_solve_int [of a n])
  apply auto
  done

lemma coprime_iff_invertible_nat: "m > (1::nat) \<Longrightarrow> coprime a m = (EX x. [a * x = 1] (mod m))"
  apply (auto intro: cong_solve_coprime_nat)
  apply (unfold cong_nat_def, auto intro: invertible_coprime_nat)
  done

lemma coprime_iff_invertible_int: "m > (1::int) \<Longrightarrow> coprime a m = (EX x. [a * x = 1] (mod m))"
  apply (auto intro: cong_solve_coprime_int)
  apply (unfold cong_int_def)
  apply (auto intro: invertible_coprime_int)
  done

lemma coprime_iff_invertible'_int: "m > (1::int) \<Longrightarrow> coprime a m =
    (EX x. 0 <= x & x < m & [a * x = 1] (mod m))"
  apply (subst coprime_iff_invertible_int)
  apply auto
  apply (auto simp add: cong_int_def)
  apply (rule_tac x = "x mod m" in exI)
  apply (auto simp add: mod_mult_right_eq [symmetric])
  done


lemma cong_cong_lcm_nat: "[(x::nat) = y] (mod a) \<Longrightarrow>
    [x = y] (mod b) \<Longrightarrow> [x = y] (mod lcm a b)"
  apply (cases "y \<le> x")
  apply (auto simp add: cong_altdef_nat lcm_least_nat) [1]
  apply (rule cong_sym_nat)
  apply (subst (asm) (1 2) cong_sym_eq_nat)
  apply (auto simp add: cong_altdef_nat lcm_least_nat)
  done

lemma cong_cong_lcm_int: "[(x::int) = y] (mod a) \<Longrightarrow>
    [x = y] (mod b) \<Longrightarrow> [x = y] (mod lcm a b)"
  by (auto simp add: cong_altdef_int lcm_least_int) [1]

lemma cong_cong_coprime_nat: "coprime a b \<Longrightarrow> [(x::nat) = y] (mod a) \<Longrightarrow>
    [x = y] (mod b) \<Longrightarrow> [x = y] (mod a * b)"
  apply (frule (1) cong_cong_lcm_nat)
  back
  apply (simp add: lcm_nat_def)
  done

lemma cong_cong_coprime_int: "coprime a b \<Longrightarrow> [(x::int) = y] (mod a) \<Longrightarrow>
    [x = y] (mod b) \<Longrightarrow> [x = y] (mod a * b)"
  apply (frule (1) cong_cong_lcm_int)
  back
  apply (simp add: lcm_altdef_int cong_abs_int abs_mult [symmetric])
  done

lemma cong_cong_setprod_coprime_nat [rule_format]: "finite A \<Longrightarrow>
    (ALL i:A. (ALL j:A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))) \<longrightarrow>
    (ALL i:A. [(x::nat) = y] (mod m i)) \<longrightarrow>
      [x = y] (mod (PROD i:A. m i))"
  apply (induct set: finite)
  apply auto
  apply (rule cong_cong_coprime_nat)
  apply (subst gcd_commute_nat)
  apply (rule setprod_coprime_nat)
  apply auto
  done

lemma cong_cong_setprod_coprime_int [rule_format]: "finite A \<Longrightarrow>
    (ALL i:A. (ALL j:A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))) \<longrightarrow>
    (ALL i:A. [(x::int) = y] (mod m i)) \<longrightarrow>
      [x = y] (mod (PROD i:A. m i))"
  apply (induct set: finite)
  apply auto
  apply (rule cong_cong_coprime_int)
  apply (subst gcd_commute_int)
  apply (rule setprod_coprime_int)
  apply auto
  done

lemma binary_chinese_remainder_aux_nat:
  assumes a: "coprime (m1::nat) m2"
  shows "EX b1 b2. [b1 = 1] (mod m1) \<and> [b1 = 0] (mod m2) \<and>
    [b2 = 0] (mod m1) \<and> [b2 = 1] (mod m2)"
proof -
  from cong_solve_coprime_nat [OF a] obtain x1 where one: "[m1 * x1 = 1] (mod m2)"
    by auto
  from a have b: "coprime m2 m1"
    by (subst gcd_commute_nat)
  from cong_solve_coprime_nat [OF b] obtain x2 where two: "[m2 * x2 = 1] (mod m1)"
    by auto
  have "[m1 * x1 = 0] (mod m1)"
    by (subst mult_commute, rule cong_mult_self_nat)
  moreover have "[m2 * x2 = 0] (mod m2)"
    by (subst mult_commute, rule cong_mult_self_nat)
  moreover note one two
  ultimately show ?thesis by blast
qed

lemma binary_chinese_remainder_aux_int:
  assumes a: "coprime (m1::int) m2"
  shows "EX b1 b2. [b1 = 1] (mod m1) \<and> [b1 = 0] (mod m2) \<and>
    [b2 = 0] (mod m1) \<and> [b2 = 1] (mod m2)"
proof -
  from cong_solve_coprime_int [OF a] obtain x1 where one: "[m1 * x1 = 1] (mod m2)"
    by auto
  from a have b: "coprime m2 m1"
    by (subst gcd_commute_int)
  from cong_solve_coprime_int [OF b] obtain x2 where two: "[m2 * x2 = 1] (mod m1)"
    by auto
  have "[m1 * x1 = 0] (mod m1)"
    by (subst mult_commute, rule cong_mult_self_int)
  moreover have "[m2 * x2 = 0] (mod m2)"
    by (subst mult_commute, rule cong_mult_self_int)
  moreover note one two
  ultimately show ?thesis by blast
qed

lemma binary_chinese_remainder_nat:
  assumes a: "coprime (m1::nat) m2"
  shows "EX x. [x = u1] (mod m1) \<and> [x = u2] (mod m2)"
proof -
  from binary_chinese_remainder_aux_nat [OF a] obtain b1 b2
      where "[b1 = 1] (mod m1)" and "[b1 = 0] (mod m2)" and
            "[b2 = 0] (mod m1)" and "[b2 = 1] (mod m2)"
    by blast
  let ?x = "u1 * b1 + u2 * b2"
  have "[?x = u1 * 1 + u2 * 0] (mod m1)"
    apply (rule cong_add_nat)
    apply (rule cong_scalar2_nat)
    apply (rule `[b1 = 1] (mod m1)`)
    apply (rule cong_scalar2_nat)
    apply (rule `[b2 = 0] (mod m1)`)
    done
  then have "[?x = u1] (mod m1)" by simp
  have "[?x = u1 * 0 + u2 * 1] (mod m2)"
    apply (rule cong_add_nat)
    apply (rule cong_scalar2_nat)
    apply (rule `[b1 = 0] (mod m2)`)
    apply (rule cong_scalar2_nat)
    apply (rule `[b2 = 1] (mod m2)`)
    done
  then have "[?x = u2] (mod m2)" by simp
  with `[?x = u1] (mod m1)` show ?thesis by blast
qed

lemma binary_chinese_remainder_int:
  assumes a: "coprime (m1::int) m2"
  shows "EX x. [x = u1] (mod m1) \<and> [x = u2] (mod m2)"
proof -
  from binary_chinese_remainder_aux_int [OF a] obtain b1 b2
    where "[b1 = 1] (mod m1)" and "[b1 = 0] (mod m2)" and
          "[b2 = 0] (mod m1)" and "[b2 = 1] (mod m2)"
    by blast
  let ?x = "u1 * b1 + u2 * b2"
  have "[?x = u1 * 1 + u2 * 0] (mod m1)"
    apply (rule cong_add_int)
    apply (rule cong_scalar2_int)
    apply (rule `[b1 = 1] (mod m1)`)
    apply (rule cong_scalar2_int)
    apply (rule `[b2 = 0] (mod m1)`)
    done
  then have "[?x = u1] (mod m1)" by simp
  have "[?x = u1 * 0 + u2 * 1] (mod m2)"
    apply (rule cong_add_int)
    apply (rule cong_scalar2_int)
    apply (rule `[b1 = 0] (mod m2)`)
    apply (rule cong_scalar2_int)
    apply (rule `[b2 = 1] (mod m2)`)
    done
  then have "[?x = u2] (mod m2)" by simp
  with `[?x = u1] (mod m1)` show ?thesis by blast
qed

lemma cong_modulus_mult_nat: "[(x::nat) = y] (mod m * n) \<Longrightarrow>
    [x = y] (mod m)"
  apply (cases "y \<le> x")
  apply (simp add: cong_altdef_nat)
  apply (erule dvd_mult_left)
  apply (rule cong_sym_nat)
  apply (subst (asm) cong_sym_eq_nat)
  apply (simp add: cong_altdef_nat)
  apply (erule dvd_mult_left)
  done

lemma cong_modulus_mult_int: "[(x::int) = y] (mod m * n) \<Longrightarrow>
    [x = y] (mod m)"
  apply (simp add: cong_altdef_int)
  apply (erule dvd_mult_left)
  done

lemma cong_less_modulus_unique_nat:
    "[(x::nat) = y] (mod m) \<Longrightarrow> x < m \<Longrightarrow> y < m \<Longrightarrow> x = y"
  by (simp add: cong_nat_def)

lemma binary_chinese_remainder_unique_nat:
  assumes a: "coprime (m1::nat) m2"
    and nz: "m1 \<noteq> 0" "m2 \<noteq> 0"
  shows "EX! x. x < m1 * m2 \<and> [x = u1] (mod m1) \<and> [x = u2] (mod m2)"
proof -
  from binary_chinese_remainder_nat [OF a] obtain y where
      "[y = u1] (mod m1)" and "[y = u2] (mod m2)"
    by blast
  let ?x = "y mod (m1 * m2)"
  from nz have less: "?x < m1 * m2"
    by auto
  have one: "[?x = u1] (mod m1)"
    apply (rule cong_trans_nat)
    prefer 2
    apply (rule `[y = u1] (mod m1)`)
    apply (rule cong_modulus_mult_nat)
    apply (rule cong_mod_nat)
    using nz apply auto
    done
  have two: "[?x = u2] (mod m2)"
    apply (rule cong_trans_nat)
    prefer 2
    apply (rule `[y = u2] (mod m2)`)
    apply (subst mult_commute)
    apply (rule cong_modulus_mult_nat)
    apply (rule cong_mod_nat)
    using nz apply auto
    done
  have "ALL z. z < m1 * m2 \<and> [z = u1] (mod m1) \<and> [z = u2] (mod m2) \<longrightarrow> z = ?x"
  proof clarify
    fix z
    assume "z < m1 * m2"
    assume "[z = u1] (mod m1)" and  "[z = u2] (mod m2)"
    have "[?x = z] (mod m1)"
      apply (rule cong_trans_nat)
      apply (rule `[?x = u1] (mod m1)`)
      apply (rule cong_sym_nat)
      apply (rule `[z = u1] (mod m1)`)
      done
    moreover have "[?x = z] (mod m2)"
      apply (rule cong_trans_nat)
      apply (rule `[?x = u2] (mod m2)`)
      apply (rule cong_sym_nat)
      apply (rule `[z = u2] (mod m2)`)
      done
    ultimately have "[?x = z] (mod m1 * m2)"
      by (auto intro: coprime_cong_mult_nat a)
    with `z < m1 * m2` `?x < m1 * m2` show "z = ?x"
      apply (intro cong_less_modulus_unique_nat)
      apply (auto, erule cong_sym_nat)
      done
  qed
  with less one two show ?thesis by auto
 qed

lemma chinese_remainder_aux_nat:
  fixes A :: "'a set"
    and m :: "'a \<Rightarrow> nat"
  assumes fin: "finite A"
    and cop: "ALL i : A. (ALL j : A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))"
  shows "EX b. (ALL i : A. [b i = 1] (mod m i) \<and> [b i = 0] (mod (PROD j : A - {i}. m j)))"
proof (rule finite_set_choice, rule fin, rule ballI)
  fix i
  assume "i : A"
  with cop have "coprime (PROD j : A - {i}. m j) (m i)"
    by (intro setprod_coprime_nat, auto)
  then have "EX x. [(PROD j : A - {i}. m j) * x = 1] (mod m i)"
    by (elim cong_solve_coprime_nat)
  then obtain x where "[(PROD j : A - {i}. m j) * x = 1] (mod m i)"
    by auto
  moreover have "[(PROD j : A - {i}. m j) * x = 0]
    (mod (PROD j : A - {i}. m j))"
    by (subst mult_commute, rule cong_mult_self_nat)
  ultimately show "\<exists>a. [a = 1] (mod m i) \<and> [a = 0]
      (mod setprod m (A - {i}))"
    by blast
qed

lemma chinese_remainder_nat:
  fixes A :: "'a set"
    and m :: "'a \<Rightarrow> nat"
    and u :: "'a \<Rightarrow> nat"
  assumes fin: "finite A"
    and cop: "ALL i:A. (ALL j : A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))"
  shows "EX x. (ALL i:A. [x = u i] (mod m i))"
proof -
  from chinese_remainder_aux_nat [OF fin cop] obtain b where
    bprop: "ALL i:A. [b i = 1] (mod m i) \<and>
      [b i = 0] (mod (PROD j : A - {i}. m j))"
    by blast
  let ?x = "SUM i:A. (u i) * (b i)"
  show "?thesis"
  proof (rule exI, clarify)
    fix i
    assume a: "i : A"
    show "[?x = u i] (mod m i)"
    proof -
      from fin a have "?x = (SUM j:{i}. u j * b j) +
          (SUM j:A-{i}. u j * b j)"
        by (subst setsum_Un_disjoint [symmetric], auto intro: setsum_cong)
      then have "[?x = u i * b i + (SUM j:A-{i}. u j * b j)] (mod m i)"
        by auto
      also have "[u i * b i + (SUM j:A-{i}. u j * b j) =
                  u i * 1 + (SUM j:A-{i}. u j * 0)] (mod m i)"
        apply (rule cong_add_nat)
        apply (rule cong_scalar2_nat)
        using bprop a apply blast
        apply (rule cong_setsum_nat)
        apply (rule cong_scalar2_nat)
        using bprop apply auto
        apply (rule cong_dvd_modulus_nat)
        apply (drule (1) bspec)
        apply (erule conjE)
        apply assumption
        apply (rule dvd_setprod)
        using fin a apply auto
        done
      finally show ?thesis
        by simp
    qed
  qed
qed

lemma coprime_cong_prod_nat [rule_format]: "finite A \<Longrightarrow>
    (ALL i: A. (ALL j: A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))) \<longrightarrow>
      (ALL i: A. [(x::nat) = y] (mod m i)) \<longrightarrow>
         [x = y] (mod (PROD i:A. m i))"
  apply (induct set: finite)
  apply auto
  apply (erule (1) coprime_cong_mult_nat)
  apply (subst gcd_commute_nat)
  apply (rule setprod_coprime_nat)
  apply auto
  done

lemma chinese_remainder_unique_nat:
  fixes A :: "'a set"
    and m :: "'a \<Rightarrow> nat"
    and u :: "'a \<Rightarrow> nat"
  assumes fin: "finite A"
    and nz: "ALL i:A. m i \<noteq> 0"
    and cop: "ALL i:A. (ALL j : A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))"
  shows "EX! x. x < (PROD i:A. m i) \<and> (ALL i:A. [x = u i] (mod m i))"
proof -
  from chinese_remainder_nat [OF fin cop]
  obtain y where one: "(ALL i:A. [y = u i] (mod m i))"
    by blast
  let ?x = "y mod (PROD i:A. m i)"
  from fin nz have prodnz: "(PROD i:A. m i) \<noteq> 0"
    by auto
  then have less: "?x < (PROD i:A. m i)"
    by auto
  have cong: "ALL i:A. [?x = u i] (mod m i)"
    apply auto
    apply (rule cong_trans_nat)
    prefer 2
    using one apply auto
    apply (rule cong_dvd_modulus_nat)
    apply (rule cong_mod_nat)
    using prodnz apply auto
    apply (rule dvd_setprod)
    apply (rule fin)
    apply assumption
    done
  have unique: "ALL z. z < (PROD i:A. m i) \<and>
      (ALL i:A. [z = u i] (mod m i)) \<longrightarrow> z = ?x"
  proof (clarify)
    fix z
    assume zless: "z < (PROD i:A. m i)"
    assume zcong: "(ALL i:A. [z = u i] (mod m i))"
    have "ALL i:A. [?x = z] (mod m i)"
      apply clarify
      apply (rule cong_trans_nat)
      using cong apply (erule bspec)
      apply (rule cong_sym_nat)
      using zcong apply auto
      done
    with fin cop have "[?x = z] (mod (PROD i:A. m i))"
      apply (intro coprime_cong_prod_nat)
      apply auto
      done
    with zless less show "z = ?x"
      apply (intro cong_less_modulus_unique_nat)
      apply (auto, erule cong_sym_nat)
      done
  qed
  from less cong unique show ?thesis by blast
qed

end
