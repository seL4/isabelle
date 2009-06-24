(*  Title:      HOL/Library/Cong.thy
    ID:         
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
extended to the natural numbers by Chiaeb. Jeremy Avigad combined
these, revised and tidied them, made the development uniform for the
natural numbers and the integers, and added a number of new theorems.

*)


header {* Congruence *}

theory Cong
imports GCD
begin

subsection {* Turn off One_nat_def *}

lemma nat_induct' [case_names zero plus1, induct type: nat]: 
    "\<lbrakk> P (0::nat); !!n. P n \<Longrightarrow> P (n + 1)\<rbrakk> \<Longrightarrow> P n"
by (erule nat_induct) (simp add:One_nat_def)

lemma nat_cases [case_names zero plus1, cases type: nat]: 
    "P (0::nat) \<Longrightarrow> (!!n. P (n + 1)) \<Longrightarrow> P n"
by(metis nat_induct')

lemma power_plus_one [simp]: "(x::'a::power)^(n + 1) = x * x^n"
by (simp add: One_nat_def)

lemma nat_power_eq_one_eq [simp]: 
  "((x::nat)^m = 1) = (m = 0 | x = 1)"
by (induct m, auto)

lemma card_insert_if' [simp]: "finite A \<Longrightarrow>
  card (insert x A) = (if x \<in> A then (card A) else (card A) + 1)"
by (auto simp add: insert_absorb)

(* why wasn't card_insert_if a simp rule? *)
declare card_insert_disjoint [simp del]

lemma nat_1' [simp]: "nat 1 = 1"
by simp

(* For those annoying moments where Suc reappears, use Suc_eq_plus1 *)

declare nat_1 [simp del]
declare add_2_eq_Suc [simp del] 
declare add_2_eq_Suc' [simp del]


declare mod_pos_pos_trivial [simp]


subsection {* Main definitions *}

class cong =

fixes 
  cong :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("(1[_ = _] '(mod _'))")

begin

abbreviation
  notcong :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("(1[_ \<noteq> _] '(mod _'))")
where
  "notcong x y m == (~cong x y m)" 

end

(* definitions for the natural numbers *)

instantiation nat :: cong

begin 

definition 
  cong_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where 
  "cong_nat x y m = ((x mod m) = (y mod m))"

instance proof qed

end


(* definitions for the integers *)

instantiation int :: cong

begin 

definition 
  cong_int :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
where 
  "cong_int x y m = ((x mod m) = (y mod m))"

instance proof qed

end


subsection {* Set up Transfer *}


lemma transfer_nat_int_cong:
  "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> m >= 0 \<Longrightarrow> 
    ([(nat x) = (nat y)] (mod (nat m))) = ([x = y] (mod m))"
  unfolding cong_int_def cong_nat_def 
  apply (auto simp add: nat_mod_distrib [symmetric])
  apply (subst (asm) eq_nat_nat_iff)
  apply (case_tac "m = 0", force, rule pos_mod_sign, force)+
  apply assumption
done

declare TransferMorphism_nat_int[transfer add return: 
    transfer_nat_int_cong]

lemma transfer_int_nat_cong:
  "[(int x) = (int y)] (mod (int m)) = [x = y] (mod m)"
  apply (auto simp add: cong_int_def cong_nat_def)
  apply (auto simp add: zmod_int [symmetric])
done

declare TransferMorphism_int_nat[transfer add return: 
    transfer_int_nat_cong]


subsection {* Congruence *}

(* was zcong_0, etc. *)
lemma nat_cong_0 [simp, presburger]: "([(a::nat) = b] (mod 0)) = (a = b)"
  by (unfold cong_nat_def, auto)

lemma int_cong_0 [simp, presburger]: "([(a::int) = b] (mod 0)) = (a = b)"
  by (unfold cong_int_def, auto)

lemma nat_cong_1 [simp, presburger]: "[(a::nat) = b] (mod 1)"
  by (unfold cong_nat_def, auto)

lemma nat_cong_Suc_0 [simp, presburger]: "[(a::nat) = b] (mod Suc 0)"
  by (unfold cong_nat_def, auto simp add: One_nat_def)

lemma int_cong_1 [simp, presburger]: "[(a::int) = b] (mod 1)"
  by (unfold cong_int_def, auto)

lemma nat_cong_refl [simp]: "[(k::nat) = k] (mod m)"
  by (unfold cong_nat_def, auto)

lemma int_cong_refl [simp]: "[(k::int) = k] (mod m)"
  by (unfold cong_int_def, auto)

lemma nat_cong_sym: "[(a::nat) = b] (mod m) \<Longrightarrow> [b = a] (mod m)"
  by (unfold cong_nat_def, auto)

lemma int_cong_sym: "[(a::int) = b] (mod m) \<Longrightarrow> [b = a] (mod m)"
  by (unfold cong_int_def, auto)

lemma nat_cong_sym_eq: "[(a::nat) = b] (mod m) = [b = a] (mod m)"
  by (unfold cong_nat_def, auto)

lemma int_cong_sym_eq: "[(a::int) = b] (mod m) = [b = a] (mod m)"
  by (unfold cong_int_def, auto)

lemma nat_cong_trans [trans]:
    "[(a::nat) = b] (mod m) \<Longrightarrow> [b = c] (mod m) \<Longrightarrow> [a = c] (mod m)"
  by (unfold cong_nat_def, auto)

lemma int_cong_trans [trans]:
    "[(a::int) = b] (mod m) \<Longrightarrow> [b = c] (mod m) \<Longrightarrow> [a = c] (mod m)"
  by (unfold cong_int_def, auto)

lemma nat_cong_add:
    "[(a::nat) = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a + c = b + d] (mod m)"
  apply (unfold cong_nat_def)
  apply (subst (1 2) mod_add_eq)
  apply simp
done

lemma int_cong_add:
    "[(a::int) = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a + c = b + d] (mod m)"
  apply (unfold cong_int_def)
  apply (subst (1 2) mod_add_left_eq)
  apply (subst (1 2) mod_add_right_eq)
  apply simp
done

lemma int_cong_diff:
    "[(a::int) = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a - c = b - d] (mod m)"
  apply (unfold cong_int_def)
  apply (subst (1 2) mod_diff_eq)
  apply simp
done

lemma int_cong_diff_aux:
  "(a::int) >= c \<Longrightarrow> b >= d \<Longrightarrow> [(a::int) = b] (mod m) \<Longrightarrow> 
      [c = d] (mod m) \<Longrightarrow> [tsub a c = tsub b d] (mod m)"
  apply (subst (1 2) tsub_eq)
  apply (auto intro: int_cong_diff)
done;

lemma nat_cong_diff:
  assumes "(a::nat) >= c" and "b >= d" and "[a = b] (mod m)" and
    "[c = d] (mod m)"
  shows "[a - c = b - d] (mod m)"

  using prems by (rule int_cong_diff_aux [transferred]);

lemma nat_cong_mult:
    "[(a::nat) = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a * c = b * d] (mod m)"
  apply (unfold cong_nat_def)
  apply (subst (1 2) mod_mult_eq)
  apply simp
done

lemma int_cong_mult:
    "[(a::int) = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a * c = b * d] (mod m)"
  apply (unfold cong_int_def)
  apply (subst (1 2) zmod_zmult1_eq)
  apply (subst (1 2) mult_commute)
  apply (subst (1 2) zmod_zmult1_eq)
  apply simp
done

lemma nat_cong_exp: "[(x::nat) = y] (mod n) \<Longrightarrow> [x^k = y^k] (mod n)"
  apply (induct k)
  apply (auto simp add: nat_cong_refl nat_cong_mult)
done

lemma int_cong_exp: "[(x::int) = y] (mod n) \<Longrightarrow> [x^k = y^k] (mod n)"
  apply (induct k)
  apply (auto simp add: int_cong_refl int_cong_mult)
done

lemma nat_cong_setsum [rule_format]: 
    "(ALL x: A. [((f x)::nat) = g x] (mod m)) \<longrightarrow> 
      [(SUM x:A. f x) = (SUM x:A. g x)] (mod m)"
  apply (case_tac "finite A")
  apply (induct set: finite)
  apply (auto intro: nat_cong_add)
done

lemma int_cong_setsum [rule_format]:
    "(ALL x: A. [((f x)::int) = g x] (mod m)) \<longrightarrow> 
      [(SUM x:A. f x) = (SUM x:A. g x)] (mod m)"
  apply (case_tac "finite A")
  apply (induct set: finite)
  apply (auto intro: int_cong_add)
done

lemma nat_cong_setprod [rule_format]: 
    "(ALL x: A. [((f x)::nat) = g x] (mod m)) \<longrightarrow> 
      [(PROD x:A. f x) = (PROD x:A. g x)] (mod m)"
  apply (case_tac "finite A")
  apply (induct set: finite)
  apply (auto intro: nat_cong_mult)
done

lemma int_cong_setprod [rule_format]: 
    "(ALL x: A. [((f x)::int) = g x] (mod m)) \<longrightarrow> 
      [(PROD x:A. f x) = (PROD x:A. g x)] (mod m)"
  apply (case_tac "finite A")
  apply (induct set: finite)
  apply (auto intro: int_cong_mult)
done

lemma nat_cong_scalar: "[(a::nat)= b] (mod m) \<Longrightarrow> [a * k = b * k] (mod m)"
  by (rule nat_cong_mult, simp_all)

lemma int_cong_scalar: "[(a::int)= b] (mod m) \<Longrightarrow> [a * k = b * k] (mod m)"
  by (rule int_cong_mult, simp_all)

lemma nat_cong_scalar2: "[(a::nat)= b] (mod m) \<Longrightarrow> [k * a = k * b] (mod m)"
  by (rule nat_cong_mult, simp_all)

lemma int_cong_scalar2: "[(a::int)= b] (mod m) \<Longrightarrow> [k * a = k * b] (mod m)"
  by (rule int_cong_mult, simp_all)

lemma nat_cong_mult_self: "[(a::nat) * m = 0] (mod m)"
  by (unfold cong_nat_def, auto)

lemma int_cong_mult_self: "[(a::int) * m = 0] (mod m)"
  by (unfold cong_int_def, auto)

lemma int_cong_eq_diff_cong_0: "[(a::int) = b] (mod m) = [a - b = 0] (mod m)"
  apply (rule iffI)
  apply (erule int_cong_diff [of a b m b b, simplified])
  apply (erule int_cong_add [of "a - b" 0 m b b, simplified])
done

lemma int_cong_eq_diff_cong_0_aux: "a >= b \<Longrightarrow>
    [(a::int) = b] (mod m) = [tsub a b = 0] (mod m)"
  by (subst tsub_eq, assumption, rule int_cong_eq_diff_cong_0)

lemma nat_cong_eq_diff_cong_0:
  assumes "(a::nat) >= b"
  shows "[a = b] (mod m) = [a - b = 0] (mod m)"

  using prems by (rule int_cong_eq_diff_cong_0_aux [transferred])

lemma nat_cong_diff_cong_0': 
  "[(x::nat) = y] (mod n) \<longleftrightarrow> 
    (if x <= y then [y - x = 0] (mod n) else [x - y = 0] (mod n))"
  apply (case_tac "y <= x")
  apply (frule nat_cong_eq_diff_cong_0 [where m = n])
  apply auto [1]
  apply (subgoal_tac "x <= y")
  apply (frule nat_cong_eq_diff_cong_0 [where m = n])
  apply (subst nat_cong_sym_eq)
  apply auto
done

lemma nat_cong_altdef: "(a::nat) >= b \<Longrightarrow> [a = b] (mod m) = (m dvd (a - b))"
  apply (subst nat_cong_eq_diff_cong_0, assumption)
  apply (unfold cong_nat_def)
  apply (simp add: dvd_eq_mod_eq_0 [symmetric])
done

lemma int_cong_altdef: "[(a::int) = b] (mod m) = (m dvd (a - b))"
  apply (subst int_cong_eq_diff_cong_0)
  apply (unfold cong_int_def)
  apply (simp add: dvd_eq_mod_eq_0 [symmetric])
done

lemma int_cong_abs: "[(x::int) = y] (mod abs m) = [x = y] (mod m)"
  by (simp add: int_cong_altdef)

lemma int_cong_square:
   "\<lbrakk> prime (p::int); 0 < a; [a * a = 1] (mod p) \<rbrakk>
    \<Longrightarrow> [a = 1] (mod p) \<or> [a = - 1] (mod p)"
  apply (simp only: int_cong_altdef)
  apply (subst int_prime_dvd_mult_eq [symmetric], assumption)
  (* any way around this? *)
  apply (subgoal_tac "a * a - 1 = (a - 1) * (a - -1)")
  apply (auto simp add: ring_simps)
done

lemma int_cong_mult_rcancel:
  "coprime k (m::int) \<Longrightarrow> [a * k = b * k] (mod m) = [a = b] (mod m)"
  apply (subst (1 2) int_cong_altdef)
  apply (subst left_diff_distrib [symmetric])
  apply (rule int_coprime_dvd_mult_iff)
  apply (subst int_gcd_commute, assumption)
done

lemma nat_cong_mult_rcancel:
  assumes  "coprime k (m::nat)"
  shows "[a * k = b * k] (mod m) = [a = b] (mod m)"

  apply (rule int_cong_mult_rcancel [transferred])
  using prems apply auto
done

lemma nat_cong_mult_lcancel:
  "coprime k (m::nat) \<Longrightarrow> [k * a = k * b ] (mod m) = [a = b] (mod m)"
  by (simp add: mult_commute nat_cong_mult_rcancel)

lemma int_cong_mult_lcancel:
  "coprime k (m::int) \<Longrightarrow> [k * a = k * b] (mod m) = [a = b] (mod m)"
  by (simp add: mult_commute int_cong_mult_rcancel)

(* was zcong_zgcd_zmult_zmod *)
lemma int_coprime_cong_mult:
  "[(a::int) = b] (mod m) \<Longrightarrow> [a = b] (mod n) \<Longrightarrow> coprime m n
    \<Longrightarrow> [a = b] (mod m * n)"
  apply (simp only: int_cong_altdef)
  apply (erule (2) int_divides_mult)
done

lemma nat_coprime_cong_mult:
  assumes "[(a::nat) = b] (mod m)" and "[a = b] (mod n)" and "coprime m n"
  shows "[a = b] (mod m * n)"

  apply (rule int_coprime_cong_mult [transferred])
  using prems apply auto
done

lemma nat_cong_less_imp_eq: "0 \<le> (a::nat) \<Longrightarrow>
    a < m \<Longrightarrow> 0 \<le> b \<Longrightarrow> b < m \<Longrightarrow> [a = b] (mod m) \<Longrightarrow> a = b"
  by (auto simp add: cong_nat_def mod_pos_pos_trivial)

lemma int_cong_less_imp_eq: "0 \<le> (a::int) \<Longrightarrow>
    a < m \<Longrightarrow> 0 \<le> b \<Longrightarrow> b < m \<Longrightarrow> [a = b] (mod m) \<Longrightarrow> a = b"
  by (auto simp add: cong_int_def mod_pos_pos_trivial)

lemma nat_cong_less_unique:
    "0 < (m::nat) \<Longrightarrow> (\<exists>!b. 0 \<le> b \<and> b < m \<and> [a = b] (mod m))"
  apply auto
  apply (rule_tac x = "a mod m" in exI)
  apply (unfold cong_nat_def, auto)
done

lemma int_cong_less_unique:
    "0 < (m::int) \<Longrightarrow> (\<exists>!b. 0 \<le> b \<and> b < m \<and> [a = b] (mod m))"
  apply auto
  apply (rule_tac x = "a mod m" in exI)
  apply (unfold cong_int_def, auto simp add: mod_pos_pos_trivial)
done

lemma int_cong_iff_lin: "([(a::int) = b] (mod m)) = (\<exists>k. b = a + m * k)"
  apply (auto simp add: int_cong_altdef dvd_def ring_simps)
  apply (rule_tac [!] x = "-k" in exI, auto)
done

lemma nat_cong_iff_lin: "([(a::nat) = b] (mod m)) = 
    (\<exists>k1 k2. b + k1 * m = a + k2 * m)"
  apply (rule iffI)
  apply (case_tac "b <= a")
  apply (subst (asm) nat_cong_altdef, assumption)
  apply (unfold dvd_def, auto)
  apply (rule_tac x = k in exI)
  apply (rule_tac x = 0 in exI)
  apply (auto simp add: ring_simps)
  apply (subst (asm) nat_cong_sym_eq)
  apply (subst (asm) nat_cong_altdef)
  apply force
  apply (unfold dvd_def, auto)
  apply (rule_tac x = 0 in exI)
  apply (rule_tac x = k in exI)
  apply (auto simp add: ring_simps)
  apply (unfold cong_nat_def)
  apply (subgoal_tac "a mod m = (a + k2 * m) mod m")
  apply (erule ssubst)back
  apply (erule subst)
  apply auto
done

lemma int_cong_gcd_eq: "[(a::int) = b] (mod m) \<Longrightarrow> gcd a m = gcd b m"
  apply (subst (asm) int_cong_iff_lin, auto)
  apply (subst add_commute) 
  apply (subst (2) int_gcd_commute)
  apply (subst mult_commute)
  apply (subst int_gcd_add_mult)
  apply (rule int_gcd_commute)
done

lemma nat_cong_gcd_eq: 
  assumes "[(a::nat) = b] (mod m)"
  shows "gcd a m = gcd b m"

  apply (rule int_cong_gcd_eq [transferred])
  using prems apply auto
done

lemma nat_cong_imp_coprime: "[(a::nat) = b] (mod m) \<Longrightarrow> coprime a m \<Longrightarrow> 
    coprime b m"
  by (auto simp add: nat_cong_gcd_eq)

lemma int_cong_imp_coprime: "[(a::int) = b] (mod m) \<Longrightarrow> coprime a m \<Longrightarrow> 
    coprime b m"
  by (auto simp add: int_cong_gcd_eq)

lemma nat_cong_cong_mod: "[(a::nat) = b] (mod m) = 
    [a mod m = b mod m] (mod m)"
  by (auto simp add: cong_nat_def)

lemma int_cong_cong_mod: "[(a::int) = b] (mod m) = 
    [a mod m = b mod m] (mod m)"
  by (auto simp add: cong_int_def)

lemma int_cong_minus [iff]: "[(a::int) = b] (mod -m) = [a = b] (mod m)"
  by (subst (1 2) int_cong_altdef, auto)

lemma nat_cong_zero [iff]: "[(a::nat) = b] (mod 0) = (a = b)"
  by (auto simp add: cong_nat_def)

lemma int_cong_zero [iff]: "[(a::int) = b] (mod 0) = (a = b)"
  by (auto simp add: cong_int_def)

(*
lemma int_mod_dvd_mod:
    "0 < (m::int) \<Longrightarrow> m dvd b \<Longrightarrow> (a mod b mod m) = (a mod m)"
  apply (unfold dvd_def, auto)
  apply (rule mod_mod_cancel)
  apply auto
done

lemma mod_dvd_mod:
  assumes "0 < (m::nat)" and "m dvd b"
  shows "(a mod b mod m) = (a mod m)"

  apply (rule int_mod_dvd_mod [transferred])
  using prems apply auto
done
*)

lemma nat_cong_add_lcancel: 
    "[(a::nat) + x = a + y] (mod n) \<longleftrightarrow> [x = y] (mod n)" 
  by (simp add: nat_cong_iff_lin)

lemma int_cong_add_lcancel: 
    "[(a::int) + x = a + y] (mod n) \<longleftrightarrow> [x = y] (mod n)" 
  by (simp add: int_cong_iff_lin)

lemma nat_cong_add_rcancel: "[(x::nat) + a = y + a] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  by (simp add: nat_cong_iff_lin)

lemma int_cong_add_rcancel: "[(x::int) + a = y + a] (mod n) \<longleftrightarrow> [x = y] (mod n)"
  by (simp add: int_cong_iff_lin)

lemma nat_cong_add_lcancel_0: "[(a::nat) + x = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)" 
  by (simp add: nat_cong_iff_lin)

lemma int_cong_add_lcancel_0: "[(a::int) + x = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)" 
  by (simp add: int_cong_iff_lin)

lemma nat_cong_add_rcancel_0: "[x + (a::nat) = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)" 
  by (simp add: nat_cong_iff_lin)

lemma int_cong_add_rcancel_0: "[x + (a::int) = a] (mod n) \<longleftrightarrow> [x = 0] (mod n)" 
  by (simp add: int_cong_iff_lin)

lemma nat_cong_dvd_modulus: "[(x::nat) = y] (mod m) \<Longrightarrow> n dvd m \<Longrightarrow> 
    [x = y] (mod n)"
  apply (auto simp add: nat_cong_iff_lin dvd_def)
  apply (rule_tac x="k1 * k" in exI)
  apply (rule_tac x="k2 * k" in exI)
  apply (simp add: ring_simps)
done

lemma int_cong_dvd_modulus: "[(x::int) = y] (mod m) \<Longrightarrow> n dvd m \<Longrightarrow> 
    [x = y] (mod n)"
  by (auto simp add: int_cong_altdef dvd_def)

lemma nat_cong_dvd_eq: "[(x::nat) = y] (mod n) \<Longrightarrow> n dvd x \<longleftrightarrow> n dvd y"
  by (unfold cong_nat_def, auto simp add: dvd_eq_mod_eq_0)

lemma int_cong_dvd_eq: "[(x::int) = y] (mod n) \<Longrightarrow> n dvd x \<longleftrightarrow> n dvd y"
  by (unfold cong_int_def, auto simp add: dvd_eq_mod_eq_0)

lemma nat_cong_mod: "(n::nat) ~= 0 \<Longrightarrow> [a mod n = a] (mod n)" 
  by (simp add: cong_nat_def)

lemma int_cong_mod: "(n::int) ~= 0 \<Longrightarrow> [a mod n = a] (mod n)" 
  by (simp add: cong_int_def)

lemma nat_mod_mult_cong: "(a::nat) ~= 0 \<Longrightarrow> b ~= 0 
    \<Longrightarrow> [x mod (a * b) = y] (mod a) \<longleftrightarrow> [x = y] (mod a)"
  by (simp add: cong_nat_def mod_mult2_eq  mod_add_left_eq)

lemma int_neg_cong: "([(a::int) = b] (mod m)) = ([-a = -b] (mod m))"
  apply (simp add: int_cong_altdef)
  apply (subst dvd_minus_iff [symmetric])
  apply (simp add: ring_simps)
done

lemma int_cong_modulus_neg: "([(a::int) = b] (mod m)) = ([a = b] (mod -m))"
  by (auto simp add: int_cong_altdef)

lemma int_mod_mult_cong: "(a::int) ~= 0 \<Longrightarrow> b ~= 0 
    \<Longrightarrow> [x mod (a * b) = y] (mod a) \<longleftrightarrow> [x = y] (mod a)"
  apply (case_tac "b > 0")
  apply (simp add: cong_int_def mod_mod_cancel mod_add_left_eq)
  apply (subst (1 2) int_cong_modulus_neg)
  apply (unfold cong_int_def)
  apply (subgoal_tac "a * b = (-a * -b)")
  apply (erule ssubst)
  apply (subst zmod_zmult2_eq)
  apply (auto simp add: mod_add_left_eq) 
done

lemma nat_cong_to_1: "([(a::nat) = 1] (mod n)) \<Longrightarrow> (n dvd (a - 1))"
  apply (case_tac "a = 0")
  apply force
  apply (subst (asm) nat_cong_altdef)
  apply auto
done

lemma nat_0_cong_1: "[(0::nat) = 1] (mod n) = (n = 1)"
  by (unfold cong_nat_def, auto)

lemma int_0_cong_1: "[(0::int) = 1] (mod n) = ((n = 1) | (n = -1))"
  by (unfold cong_int_def, auto simp add: zmult_eq_1_iff)

lemma nat_cong_to_1': "[(a::nat) = 1] (mod n) \<longleftrightarrow> 
    a = 0 \<and> n = 1 \<or> (\<exists>m. a = 1 + m * n)"
  apply (case_tac "n = 1")
  apply auto [1]
  apply (drule_tac x = "a - 1" in spec)
  apply force
  apply (case_tac "a = 0")
  apply (auto simp add: nat_0_cong_1) [1]
  apply (rule iffI)
  apply (drule nat_cong_to_1)
  apply (unfold dvd_def)
  apply auto [1]
  apply (rule_tac x = k in exI)
  apply (auto simp add: ring_simps) [1]
  apply (subst nat_cong_altdef)
  apply (auto simp add: dvd_def)
done

lemma nat_cong_le: "(y::nat) <= x \<Longrightarrow> [x = y] (mod n) \<longleftrightarrow> (\<exists>q. x = q * n + y)"
  apply (subst nat_cong_altdef)
  apply assumption
  apply (unfold dvd_def, auto simp add: ring_simps)
  apply (rule_tac x = k in exI)
  apply auto
done

lemma nat_cong_solve: "(a::nat) \<noteq> 0 \<Longrightarrow> EX x. [a * x = gcd a n] (mod n)"
  apply (case_tac "n = 0")
  apply force
  apply (frule nat_bezout [of a n], auto)
  apply (rule exI, erule ssubst)
  apply (rule nat_cong_trans)
  apply (rule nat_cong_add)
  apply (subst mult_commute)
  apply (rule nat_cong_mult_self)
  prefer 2
  apply simp
  apply (rule nat_cong_refl)
  apply (rule nat_cong_refl)
done

lemma int_cong_solve: "(a::int) \<noteq> 0 \<Longrightarrow> EX x. [a * x = gcd a n] (mod n)"
  apply (case_tac "n = 0")
  apply (case_tac "a \<ge> 0")
  apply auto
  apply (rule_tac x = "-1" in exI)
  apply auto
  apply (insert int_bezout [of a n], auto)
  apply (rule exI)
  apply (erule subst)
  apply (rule int_cong_trans)
  prefer 2
  apply (rule int_cong_add)
  apply (rule int_cong_refl)
  apply (rule int_cong_sym)
  apply (rule int_cong_mult_self)
  apply simp
  apply (subst mult_commute)
  apply (rule int_cong_refl)
done
  
lemma nat_cong_solve_dvd: 
  assumes a: "(a::nat) \<noteq> 0" and b: "gcd a n dvd d"
  shows "EX x. [a * x = d] (mod n)"
proof -
  from nat_cong_solve [OF a] obtain x where 
      "[a * x = gcd a n](mod n)"
    by auto
  hence "[(d div gcd a n) * (a * x) = (d div gcd a n) * gcd a n] (mod n)" 
    by (elim nat_cong_scalar2)
  also from b have "(d div gcd a n) * gcd a n = d"
    by (rule dvd_div_mult_self)
  also have "(d div gcd a n) * (a * x) = a * (d div gcd a n * x)"
    by auto
  finally show ?thesis
    by auto
qed

lemma int_cong_solve_dvd: 
  assumes a: "(a::int) \<noteq> 0" and b: "gcd a n dvd d"
  shows "EX x. [a * x = d] (mod n)"
proof -
  from int_cong_solve [OF a] obtain x where 
      "[a * x = gcd a n](mod n)"
    by auto
  hence "[(d div gcd a n) * (a * x) = (d div gcd a n) * gcd a n] (mod n)" 
    by (elim int_cong_scalar2)
  also from b have "(d div gcd a n) * gcd a n = d"
    by (rule dvd_div_mult_self)
  also have "(d div gcd a n) * (a * x) = a * (d div gcd a n * x)"
    by auto
  finally show ?thesis
    by auto
qed

lemma nat_cong_solve_coprime: "coprime (a::nat) n \<Longrightarrow> 
    EX x. [a * x = 1] (mod n)"
  apply (case_tac "a = 0")
  apply force
  apply (frule nat_cong_solve [of a n])
  apply auto
done

lemma int_cong_solve_coprime: "coprime (a::int) n \<Longrightarrow> 
    EX x. [a * x = 1] (mod n)"
  apply (case_tac "a = 0")
  apply auto
  apply (case_tac "n \<ge> 0")
  apply auto
  apply (subst cong_int_def, auto)
  apply (frule int_cong_solve [of a n])
  apply auto
done

lemma nat_coprime_iff_invertible: "m > (1::nat) \<Longrightarrow> coprime a m = 
    (EX x. [a * x = 1] (mod m))"
  apply (auto intro: nat_cong_solve_coprime)
  apply (unfold cong_nat_def, auto intro: nat_invertible_coprime)
done

lemma int_coprime_iff_invertible: "m > (1::int) \<Longrightarrow> coprime a m = 
    (EX x. [a * x = 1] (mod m))"
  apply (auto intro: int_cong_solve_coprime)
  apply (unfold cong_int_def)
  apply (auto intro: int_invertible_coprime)
done

lemma int_coprime_iff_invertible': "m > (1::int) \<Longrightarrow> coprime a m = 
    (EX x. 0 <= x & x < m & [a * x = 1] (mod m))"
  apply (subst int_coprime_iff_invertible)
  apply auto
  apply (auto simp add: cong_int_def)
  apply (rule_tac x = "x mod m" in exI)
  apply (auto simp add: mod_mult_right_eq [symmetric])
done


lemma nat_cong_cong_lcm: "[(x::nat) = y] (mod a) \<Longrightarrow>
    [x = y] (mod b) \<Longrightarrow> [x = y] (mod lcm a b)"
  apply (case_tac "y \<le> x")
  apply (auto simp add: nat_cong_altdef nat_lcm_least) [1]
  apply (rule nat_cong_sym)
  apply (subst (asm) (1 2) nat_cong_sym_eq)
  apply (auto simp add: nat_cong_altdef nat_lcm_least)
done

lemma int_cong_cong_lcm: "[(x::int) = y] (mod a) \<Longrightarrow>
    [x = y] (mod b) \<Longrightarrow> [x = y] (mod lcm a b)"
  by (auto simp add: int_cong_altdef int_lcm_least) [1]

lemma nat_cong_cong_coprime: "coprime a b \<Longrightarrow> [(x::nat) = y] (mod a) \<Longrightarrow>
    [x = y] (mod b) \<Longrightarrow> [x = y] (mod a * b)"
  apply (frule (1) nat_cong_cong_lcm)back
  apply (simp add: lcm_nat_def)
done

lemma int_cong_cong_coprime: "coprime a b \<Longrightarrow> [(x::int) = y] (mod a) \<Longrightarrow>
    [x = y] (mod b) \<Longrightarrow> [x = y] (mod a * b)"
  apply (frule (1) int_cong_cong_lcm)back
  apply (simp add: int_lcm_altdef int_cong_abs abs_mult [symmetric])
done

lemma nat_cong_cong_setprod_coprime [rule_format]: "finite A \<Longrightarrow>
    (ALL i:A. (ALL j:A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))) \<longrightarrow>
    (ALL i:A. [(x::nat) = y] (mod m i)) \<longrightarrow>
      [x = y] (mod (PROD i:A. m i))"
  apply (induct set: finite)
  apply auto
  apply (rule nat_cong_cong_coprime)
  apply (subst nat_gcd_commute)
  apply (rule nat_setprod_coprime)
  apply auto
done

lemma int_cong_cong_setprod_coprime [rule_format]: "finite A \<Longrightarrow>
    (ALL i:A. (ALL j:A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))) \<longrightarrow>
    (ALL i:A. [(x::int) = y] (mod m i)) \<longrightarrow>
      [x = y] (mod (PROD i:A. m i))"
  apply (induct set: finite)
  apply auto
  apply (rule int_cong_cong_coprime)
  apply (subst int_gcd_commute)
  apply (rule int_setprod_coprime)
  apply auto
done

lemma nat_binary_chinese_remainder_aux: 
  assumes a: "coprime (m1::nat) m2"
  shows "EX b1 b2. [b1 = 1] (mod m1) \<and> [b1 = 0] (mod m2) \<and>
    [b2 = 0] (mod m1) \<and> [b2 = 1] (mod m2)"
proof -
  from nat_cong_solve_coprime [OF a]
      obtain x1 where one: "[m1 * x1 = 1] (mod m2)"
    by auto
  from a have b: "coprime m2 m1" 
    by (subst nat_gcd_commute)
  from nat_cong_solve_coprime [OF b]
      obtain x2 where two: "[m2 * x2 = 1] (mod m1)"
    by auto
  have "[m1 * x1 = 0] (mod m1)"
    by (subst mult_commute, rule nat_cong_mult_self)
  moreover have "[m2 * x2 = 0] (mod m2)"
    by (subst mult_commute, rule nat_cong_mult_self)
  moreover note one two
  ultimately show ?thesis by blast
qed

lemma int_binary_chinese_remainder_aux: 
  assumes a: "coprime (m1::int) m2"
  shows "EX b1 b2. [b1 = 1] (mod m1) \<and> [b1 = 0] (mod m2) \<and>
    [b2 = 0] (mod m1) \<and> [b2 = 1] (mod m2)"
proof -
  from int_cong_solve_coprime [OF a]
      obtain x1 where one: "[m1 * x1 = 1] (mod m2)"
    by auto
  from a have b: "coprime m2 m1" 
    by (subst int_gcd_commute)
  from int_cong_solve_coprime [OF b]
      obtain x2 where two: "[m2 * x2 = 1] (mod m1)"
    by auto
  have "[m1 * x1 = 0] (mod m1)"
    by (subst mult_commute, rule int_cong_mult_self)
  moreover have "[m2 * x2 = 0] (mod m2)"
    by (subst mult_commute, rule int_cong_mult_self)
  moreover note one two
  ultimately show ?thesis by blast
qed

lemma nat_binary_chinese_remainder:
  assumes a: "coprime (m1::nat) m2"
  shows "EX x. [x = u1] (mod m1) \<and> [x = u2] (mod m2)"
proof -
  from nat_binary_chinese_remainder_aux [OF a] obtain b1 b2
    where "[b1 = 1] (mod m1)" and "[b1 = 0] (mod m2)" and
          "[b2 = 0] (mod m1)" and "[b2 = 1] (mod m2)"
    by blast
  let ?x = "u1 * b1 + u2 * b2"
  have "[?x = u1 * 1 + u2 * 0] (mod m1)"
    apply (rule nat_cong_add)
    apply (rule nat_cong_scalar2)
    apply (rule `[b1 = 1] (mod m1)`)
    apply (rule nat_cong_scalar2)
    apply (rule `[b2 = 0] (mod m1)`)
    done
  hence "[?x = u1] (mod m1)" by simp
  have "[?x = u1 * 0 + u2 * 1] (mod m2)"
    apply (rule nat_cong_add)
    apply (rule nat_cong_scalar2)
    apply (rule `[b1 = 0] (mod m2)`)
    apply (rule nat_cong_scalar2)
    apply (rule `[b2 = 1] (mod m2)`)
    done
  hence "[?x = u2] (mod m2)" by simp
  with `[?x = u1] (mod m1)` show ?thesis by blast
qed

lemma int_binary_chinese_remainder:
  assumes a: "coprime (m1::int) m2"
  shows "EX x. [x = u1] (mod m1) \<and> [x = u2] (mod m2)"
proof -
  from int_binary_chinese_remainder_aux [OF a] obtain b1 b2
    where "[b1 = 1] (mod m1)" and "[b1 = 0] (mod m2)" and
          "[b2 = 0] (mod m1)" and "[b2 = 1] (mod m2)"
    by blast
  let ?x = "u1 * b1 + u2 * b2"
  have "[?x = u1 * 1 + u2 * 0] (mod m1)"
    apply (rule int_cong_add)
    apply (rule int_cong_scalar2)
    apply (rule `[b1 = 1] (mod m1)`)
    apply (rule int_cong_scalar2)
    apply (rule `[b2 = 0] (mod m1)`)
    done
  hence "[?x = u1] (mod m1)" by simp
  have "[?x = u1 * 0 + u2 * 1] (mod m2)"
    apply (rule int_cong_add)
    apply (rule int_cong_scalar2)
    apply (rule `[b1 = 0] (mod m2)`)
    apply (rule int_cong_scalar2)
    apply (rule `[b2 = 1] (mod m2)`)
    done
  hence "[?x = u2] (mod m2)" by simp
  with `[?x = u1] (mod m1)` show ?thesis by blast
qed

lemma nat_cong_modulus_mult: "[(x::nat) = y] (mod m * n) \<Longrightarrow> 
    [x = y] (mod m)"
  apply (case_tac "y \<le> x")
  apply (simp add: nat_cong_altdef)
  apply (erule dvd_mult_left)
  apply (rule nat_cong_sym)
  apply (subst (asm) nat_cong_sym_eq)
  apply (simp add: nat_cong_altdef) 
  apply (erule dvd_mult_left)
done

lemma int_cong_modulus_mult: "[(x::int) = y] (mod m * n) \<Longrightarrow> 
    [x = y] (mod m)"
  apply (simp add: int_cong_altdef) 
  apply (erule dvd_mult_left)
done

lemma nat_cong_less_modulus_unique: 
    "[(x::nat) = y] (mod m) \<Longrightarrow> x < m \<Longrightarrow> y < m \<Longrightarrow> x = y"
  by (simp add: cong_nat_def)

lemma nat_binary_chinese_remainder_unique:
  assumes a: "coprime (m1::nat) m2" and
         nz: "m1 \<noteq> 0" "m2 \<noteq> 0"
  shows "EX! x. x < m1 * m2 \<and> [x = u1] (mod m1) \<and> [x = u2] (mod m2)"
proof -
  from nat_binary_chinese_remainder [OF a] obtain y where 
      "[y = u1] (mod m1)" and "[y = u2] (mod m2)"
    by blast
  let ?x = "y mod (m1 * m2)"
  from nz have less: "?x < m1 * m2"
    by auto   
  have one: "[?x = u1] (mod m1)"
    apply (rule nat_cong_trans)
    prefer 2
    apply (rule `[y = u1] (mod m1)`)
    apply (rule nat_cong_modulus_mult)
    apply (rule nat_cong_mod)
    using nz apply auto
    done
  have two: "[?x = u2] (mod m2)"
    apply (rule nat_cong_trans)
    prefer 2
    apply (rule `[y = u2] (mod m2)`)
    apply (subst mult_commute)
    apply (rule nat_cong_modulus_mult)
    apply (rule nat_cong_mod)
    using nz apply auto
    done
  have "ALL z. z < m1 * m2 \<and> [z = u1] (mod m1) \<and> [z = u2] (mod m2) \<longrightarrow>
      z = ?x"
  proof (clarify)
    fix z
    assume "z < m1 * m2"
    assume "[z = u1] (mod m1)" and  "[z = u2] (mod m2)"
    have "[?x = z] (mod m1)"
      apply (rule nat_cong_trans)
      apply (rule `[?x = u1] (mod m1)`)
      apply (rule nat_cong_sym)
      apply (rule `[z = u1] (mod m1)`)
      done
    moreover have "[?x = z] (mod m2)"
      apply (rule nat_cong_trans)
      apply (rule `[?x = u2] (mod m2)`)
      apply (rule nat_cong_sym)
      apply (rule `[z = u2] (mod m2)`)
      done
    ultimately have "[?x = z] (mod m1 * m2)"
      by (auto intro: nat_coprime_cong_mult a)
    with `z < m1 * m2` `?x < m1 * m2` show "z = ?x"
      apply (intro nat_cong_less_modulus_unique)
      apply (auto, erule nat_cong_sym)
      done
  qed  
  with less one two show ?thesis
    by auto
 qed

lemma nat_chinese_remainder_aux:
  fixes A :: "'a set" and
        m :: "'a \<Rightarrow> nat"
  assumes fin: "finite A" and
          cop: "ALL i : A. (ALL j : A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))"
  shows "EX b. (ALL i : A. 
      [b i = 1] (mod m i) \<and> [b i = 0] (mod (PROD j : A - {i}. m j)))"
proof (rule finite_set_choice, rule fin, rule ballI)
  fix i
  assume "i : A"
  with cop have "coprime (PROD j : A - {i}. m j) (m i)"
    by (intro nat_setprod_coprime, auto)
  hence "EX x. [(PROD j : A - {i}. m j) * x = 1] (mod m i)"
    by (elim nat_cong_solve_coprime)
  then obtain x where "[(PROD j : A - {i}. m j) * x = 1] (mod m i)"
    by auto
  moreover have "[(PROD j : A - {i}. m j) * x = 0] 
    (mod (PROD j : A - {i}. m j))"
    by (subst mult_commute, rule nat_cong_mult_self)
  ultimately show "\<exists>a. [a = 1] (mod m i) \<and> [a = 0] 
      (mod setprod m (A - {i}))"
    by blast
qed

lemma nat_chinese_remainder:
  fixes A :: "'a set" and
        m :: "'a \<Rightarrow> nat" and
        u :: "'a \<Rightarrow> nat"
  assumes 
        fin: "finite A" and
        cop: "ALL i:A. (ALL j : A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))"
  shows "EX x. (ALL i:A. [x = u i] (mod m i))"
proof -
  from nat_chinese_remainder_aux [OF fin cop] obtain b where
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
      hence "[?x = u i * b i + (SUM j:A-{i}. u j * b j)] (mod m i)"
        by auto
      also have "[u i * b i + (SUM j:A-{i}. u j * b j) =
                  u i * 1 + (SUM j:A-{i}. u j * 0)] (mod m i)"
        apply (rule nat_cong_add)
        apply (rule nat_cong_scalar2)
        using bprop a apply blast
        apply (rule nat_cong_setsum)
        apply (rule nat_cong_scalar2)
        using bprop apply auto
        apply (rule nat_cong_dvd_modulus)
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

lemma nat_coprime_cong_prod [rule_format]: "finite A \<Longrightarrow> 
    (ALL i: A. (ALL j: A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))) \<longrightarrow>
      (ALL i: A. [(x::nat) = y] (mod m i)) \<longrightarrow>
         [x = y] (mod (PROD i:A. m i))" 
  apply (induct set: finite)
  apply auto
  apply (erule (1) nat_coprime_cong_mult)
  apply (subst nat_gcd_commute)
  apply (rule nat_setprod_coprime)
  apply auto
done

lemma nat_chinese_remainder_unique:
  fixes A :: "'a set" and
        m :: "'a \<Rightarrow> nat" and
        u :: "'a \<Rightarrow> nat"
  assumes 
        fin: "finite A" and
         nz: "ALL i:A. m i \<noteq> 0" and
        cop: "ALL i:A. (ALL j : A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))"
  shows "EX! x. x < (PROD i:A. m i) \<and> (ALL i:A. [x = u i] (mod m i))"
proof -
  from nat_chinese_remainder [OF fin cop] obtain y where
      one: "(ALL i:A. [y = u i] (mod m i))" 
    by blast
  let ?x = "y mod (PROD i:A. m i)"
  from fin nz have prodnz: "(PROD i:A. m i) \<noteq> 0"
    by auto
  hence less: "?x < (PROD i:A. m i)"
    by auto
  have cong: "ALL i:A. [?x = u i] (mod m i)"
    apply auto
    apply (rule nat_cong_trans)
    prefer 2
    using one apply auto
    apply (rule nat_cong_dvd_modulus)
    apply (rule nat_cong_mod)
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
      apply (rule nat_cong_trans)
      using cong apply (erule bspec)
      apply (rule nat_cong_sym)
      using zcong apply auto
      done
    with fin cop have "[?x = z] (mod (PROD i:A. m i))"
      by (intro nat_coprime_cong_prod, auto)
    with zless less show "z = ?x"
      apply (intro nat_cong_less_modulus_unique)
      apply (auto, erule nat_cong_sym)
      done
  qed 
  from less cong unique show ?thesis
    by blast  
qed

end
