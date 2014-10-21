(* 
  Author:  Jeremy Dawson, NICTA
*) 

header {* Useful Numerical Lemmas *}

theory Misc_Numeric
imports Main Parity
begin

lemma mod_2_neq_1_eq_eq_0:
  fixes k :: int
  shows "k mod 2 \<noteq> 1 \<longleftrightarrow> k mod 2 = 0"
  by (fact not_mod_2_eq_1_eq_0)

lemma z1pmod2:
  fixes b :: int
  shows "(2 * b + 1) mod 2 = (1::int)"
  by arith

lemma diff_le_eq':
  "a - b \<le> c \<longleftrightarrow> a \<le> b + (c::int)"
  by arith

lemma emep1:
  fixes n d :: int
  shows "even n \<Longrightarrow> even d \<Longrightarrow> 0 \<le> d \<Longrightarrow> (n + 1) mod d = (n mod d) + 1"
  by (auto simp add: pos_zmod_mult_2 add.commute dvd_def)

lemma int_mod_ge:
  "a < n \<Longrightarrow> 0 < (n :: int) \<Longrightarrow> a \<le> a mod n"
  by (metis dual_order.trans le_cases mod_pos_pos_trivial pos_mod_conj)

lemma int_mod_ge':
  "b < 0 \<Longrightarrow> 0 < (n :: int) \<Longrightarrow> b + n \<le> b mod n"
  by (metis add_less_same_cancel2 int_mod_ge mod_add_self2)

lemma int_mod_le':
  "(0::int) \<le> b - n \<Longrightarrow> b mod n \<le> b - n"
  by (metis minus_mod_self2 zmod_le_nonneg_dividend)

lemma zless2:
  "0 < (2 :: int)"
  by (fact zero_less_numeral)

lemma zless2p:
  "0 < (2 ^ n :: int)"
  by arith

lemma zle2p:
  "0 \<le> (2 ^ n :: int)"
  by arith

lemma m1mod2k:
  "- 1 mod 2 ^ n = (2 ^ n - 1 :: int)"
  using zless2p by (rule zmod_minus1)

lemma p1mod22k':
  fixes b :: int
  shows "(1 + 2 * b) mod (2 * 2 ^ n) = 1 + 2 * (b mod 2 ^ n)"
  using zle2p by (rule pos_zmod_mult_2) 

lemma p1mod22k:
  fixes b :: int
  shows "(2 * b + 1) mod (2 * 2 ^ n) = 2 * (b mod 2 ^ n) + 1"
  by (simp add: p1mod22k' add.commute)

lemma int_mod_lem: 
  "(0 :: int) < n ==> (0 <= b & b < n) = (b mod n = b)"
  apply safe
    apply (erule (1) mod_pos_pos_trivial)
   apply (erule_tac [!] subst)
   apply auto
  done

end

