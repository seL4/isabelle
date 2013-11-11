(* 
  Author:  Jeremy Dawson, NICTA
*) 

header {* Useful Numerical Lemmas *}

theory Misc_Numeric
imports Main Parity
begin

declare iszero_0 [iff]

lemma min_pm [simp]: "min a b + (a - b) = (a :: nat)" by arith
  
lemmas min_pm1 [simp] = trans [OF add_commute min_pm]

lemma rev_min_pm [simp]: "min b a + (a - b) = (a::nat)" by arith

lemmas rev_min_pm1 [simp] = trans [OF add_commute rev_min_pm]

lemma min_minus [simp] : "min m (m - k) = (m - k :: nat)" by arith
  
lemmas min_minus' [simp] = trans [OF min_max.inf_commute min_minus]

lemma z1pmod2:
  "(2 * b + 1) mod 2 = (1::int)" by arith

lemma emep1:
  "even n ==> even d ==> 0 <= d ==> (n + 1) mod (d :: int) = (n mod d) + 1"
  apply (simp add: add_commute)
  apply (safe dest!: even_equiv_def [THEN iffD1])
  apply (subst pos_zmod_mult_2)
   apply arith
  apply (simp add: mod_mult_mult1)
 done

lemma int_mod_lem: 
  "(0 :: int) < n ==> (0 <= b & b < n) = (b mod n = b)"
  apply safe
    apply (erule (1) mod_pos_pos_trivial)
   apply (erule_tac [!] subst)
   apply auto
  done

lemma int_mod_ge: "a < n ==> 0 < (n :: int) ==> a <= a mod n"
  apply (cases "0 <= a")
   apply (drule (1) mod_pos_pos_trivial)
   apply simp
  apply (rule order_trans [OF _ pos_mod_sign])
   apply simp
  apply assumption
  done

lemma int_mod_ge': "b < 0 ==> 0 < (n :: int) ==> b + n <= b mod n"
  by (rule int_mod_ge [where a = "b + n" and n = n, simplified])

lemma zless2:
  "0 < (2 :: int)"
  by arith

lemma zless2p:
  "0 < (2 ^ n :: int)"
  by arith

lemma zle2p:
  "0 \<le> (2 ^ n :: int)"
  by arith

lemma int_mod_le': "(0::int) <= b - n ==> b mod n <= b - n"
  using zmod_le_nonneg_dividend [of "b - n" "n"] by simp

lemma diff_le_eq': "(a - b \<le> c) = (a \<le> b + (c::int))" by arith

lemma m1mod2k:
  "-1 mod 2 ^ n = (2 ^ n - 1 :: int)"
  using zless2p by (rule zmod_minus1)

lemma p1mod22k':
  fixes b :: int
  shows "(1 + 2 * b) mod (2 * 2 ^ n) = 1 + 2 * (b mod 2 ^ n)"
  using zle2p by (rule pos_zmod_mult_2) 

lemma p1mod22k:
  fixes b :: int
  shows "(2 * b + 1) mod (2 * 2 ^ n) = 2 * (b mod 2 ^ n) + 1"
  by (simp add: p1mod22k' add_commute)

lemma lrlem':
  assumes d: "(i::nat) \<le> j \<or> m < j'"
  assumes R1: "i * k \<le> j * k \<Longrightarrow> R"
  assumes R2: "Suc m * k' \<le> j' * k' \<Longrightarrow> R"
  shows "R" using d
  apply safe
   apply (rule R1, erule mult_le_mono1)
  apply (rule R2, erule Suc_le_eq [THEN iffD2 [THEN mult_le_mono1]])
  done

lemma lrlem: "(0::nat) < sc ==>
    (sc - n + (n + lb * n) <= m * n) = (sc + lb * n <= m * n)"
  apply safe
   apply arith
  apply (case_tac "sc >= n")
   apply arith
  apply (insert linorder_le_less_linear [of m lb])
  apply (erule_tac k=n and k'=n in lrlem')
   apply arith
  apply simp
  done

end

