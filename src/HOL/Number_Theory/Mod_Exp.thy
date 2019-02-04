(*
  File:    HOL/Number_Theory/Mod_Exp
  Author:  Manuel Eberl, TU München

  Fast implementation of modular exponentiation and "cong" using exponentiation by squaring.
  Includes code setup for nat and int.
*)
section \<open>Fast modular exponentiation\<close>
theory Mod_Exp
  imports Cong "HOL-Library.Power_By_Squaring"
begin

context euclidean_semiring_cancel
begin

definition mod_exp_aux :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"
  where "mod_exp_aux m = efficient_funpow (\<lambda>x y. x * y mod m)"

lemma mod_exp_aux_code [code]:
  "mod_exp_aux m y x n =
     (if n = 0 then y
      else if n = 1 then (x * y) mod m
      else if even n then mod_exp_aux m y ((x * x) mod m) (n div 2)
      else mod_exp_aux m ((x * y) mod m) ((x * x) mod m) (n div 2))"
  unfolding mod_exp_aux_def by (rule efficient_funpow_code)

lemma mod_exp_aux_correct:
  "mod_exp_aux m y x n mod m = (x ^ n * y) mod m"
proof -
  have "mod_exp_aux m y x n = efficient_funpow (\<lambda>x y. x * y mod m) y x n"
    by (simp add: mod_exp_aux_def)
  also have "\<dots> = ((\<lambda>y. x * y mod m) ^^ n) y"
    by (rule efficient_funpow_correct) (simp add: mod_mult_left_eq mod_mult_right_eq mult_ac)
  also have "((\<lambda>y. x * y mod m) ^^ n) y mod m = (x ^ n * y) mod m"
  proof (induction n)
    case (Suc n)
    hence "x * ((\<lambda>y. x * y mod m) ^^ n) y mod m = x * x ^ n * y mod m"
      by (metis mod_mult_right_eq mult.assoc)
    thus ?case by auto
  qed auto
  finally show ?thesis .
qed

definition mod_exp :: "'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"
  where "mod_exp b e m = (b ^ e) mod m"

lemma mod_exp_code [code]: "mod_exp b e m = mod_exp_aux m 1 b e mod m"
  by (simp add: mod_exp_def mod_exp_aux_correct)

end

(*
  TODO: Setup here only for nat and int. Could be done for any
  euclidean_semiring_cancel. Should it?
*)
lemmas [code_abbrev] = mod_exp_def[where ?'a = nat] mod_exp_def[where ?'a = int]

lemma cong_power_nat_code [code_unfold]:
  "[b ^ e = (x ::nat)] (mod m) \<longleftrightarrow> mod_exp b e m = x mod m"
  by (simp add: mod_exp_def cong_def)

lemma cong_power_int_code [code_unfold]:
  "[b ^ e = (x ::int)] (mod m) \<longleftrightarrow> mod_exp b e m = x mod m"
  by (simp add: mod_exp_def cong_def)


text \<open>
  The following rules allow the simplifier to evaluate @{const mod_exp} efficiently.
\<close>
lemma eval_mod_exp_aux [simp]:
  "mod_exp_aux m y x 0 = y"
  "mod_exp_aux m y x (Suc 0) = (x * y) mod m"
  "mod_exp_aux m y x (numeral (num.Bit0 n)) =
     mod_exp_aux m y (x\<^sup>2 mod m) (numeral n)"
  "mod_exp_aux m y x (numeral (num.Bit1 n)) =
     mod_exp_aux m ((x * y) mod m) (x\<^sup>2 mod m) (numeral n)"
proof -
  define n' where "n' = (numeral n :: nat)"
  have [simp]: "n' \<noteq> 0" by (auto simp: n'_def)
  
  show "mod_exp_aux m y x 0 = y" and "mod_exp_aux m y x (Suc 0) = (x * y) mod m"
    by (simp_all add: mod_exp_aux_def)

  have "numeral (num.Bit0 n) = (2 * n')"
    by (subst numeral.numeral_Bit0) (simp del: arith_simps add: n'_def)
  also have "mod_exp_aux m y x \<dots> = mod_exp_aux m y (x^2 mod m) n'"
    by (subst mod_exp_aux_code) (simp_all add: power2_eq_square)
  finally show "mod_exp_aux m y x (numeral (num.Bit0 n)) =
                  mod_exp_aux m y (x\<^sup>2 mod m) (numeral n)"
    by (simp add: n'_def)

  have "numeral (num.Bit1 n) = Suc (2 * n')"
    by (subst numeral.numeral_Bit1) (simp del: arith_simps add: n'_def)
  also have "mod_exp_aux m y x \<dots> = mod_exp_aux m ((x * y) mod m) (x^2 mod m) n'"
    by (subst mod_exp_aux_code) (simp_all add: power2_eq_square)
  finally show "mod_exp_aux m y x (numeral (num.Bit1 n)) =
                  mod_exp_aux m ((x * y) mod m) (x\<^sup>2 mod m) (numeral n)"
    by (simp add: n'_def)
qed

lemma eval_mod_exp [simp]:
  "mod_exp b' 0 m' = 1 mod m'"
  "mod_exp b' 1 m' = b' mod m'"
  "mod_exp b' (Suc 0) m' = b' mod m'"
  "mod_exp b' e' 0 = b' ^ e'"  
  "mod_exp b' e' 1 = 0"
  "mod_exp b' e' (Suc 0) = 0"
  "mod_exp 0 1 m' = 0"
  "mod_exp 0 (Suc 0) m' = 0"
  "mod_exp 0 (numeral e) m' = 0"
  "mod_exp 1 e' m' = 1 mod m'"
  "mod_exp (Suc 0) e' m' = 1 mod m'"
  "mod_exp (numeral b) (numeral e) (numeral m) =
     mod_exp_aux (numeral m) 1 (numeral b) (numeral e) mod numeral m"
  by (simp_all add: mod_exp_def mod_exp_aux_correct)

end
