(*  Title:      HOL/Library/Code_Bit_Shifts_for_Arithmetic.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Rewrite arithmetic operations to bit-shifts if feasible\<close>

theory Code_Bit_Shifts_for_Arithmetic
  imports Main
begin

context semiring_bit_operations
begin

context
  includes bit_operations_syntax
begin

lemma [code_unfold]:
  \<open>of_bool (odd a) = a AND 1\<close>
  by (simp add: and_one_eq mod2_eq_if)

lemma [code_unfold]:
  \<open>even a \<longleftrightarrow> a AND 1 = 0\<close>
  by (simp add: and_one_eq mod2_eq_if)

lemma [code_unfold]:
  \<open>2 * a = push_bit 1 a\<close>
  by (simp add: ac_simps)

lemma [code_unfold]:
  \<open>a * 2 = push_bit 1 a\<close>
  by simp

lemma [code_unfold]:
  \<open>2 ^ n * a = push_bit n a\<close>
  by (simp add: push_bit_eq_mult ac_simps)

lemma [code_unfold]:
  \<open>a * 2 ^ n = push_bit n a\<close>
  by (simp add: push_bit_eq_mult)

lemma [code_unfold]:
  \<open>a div 2 = drop_bit 1 a\<close>
  by (simp add: drop_bit_eq_div)

lemma [code_unfold]:
  \<open>a div 2 ^ n = drop_bit n a\<close>
  by (simp add: drop_bit_eq_div)

lemma [code_unfold]:
  \<open>a mod 2 = take_bit 1 a\<close>
  by (simp add: take_bit_eq_mod)

lemma [code_unfold]:
  \<open>a mod 2 ^ n  = take_bit n a\<close>
  by (simp add: take_bit_eq_mod)

end

end

end
