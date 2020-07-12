(*  Title:      HOL/Word/Bit_Comprehension.thy
    Author:     Brian Huffman, PSU; Jeremy Dawson and Gerwin Klein, NICTA
*)

section \<open>Comprehension syntax for bit expressions\<close>

theory Bit_Comprehension
  imports Bits_Int
begin

class bit_comprehension = semiring_bits +
  fixes set_bits :: "(nat \<Rightarrow> bool) \<Rightarrow> 'a"  (binder "BITS " 10)

instantiation int :: bit_comprehension
begin

definition
  "set_bits f =
    (if \<exists>n. \<forall>n'\<ge>n. \<not> f n' then
      let n = LEAST n. \<forall>n'\<ge>n. \<not> f n'
      in horner_sum of_bool 2 (map f [0..<n])
     else if \<exists>n. \<forall>n'\<ge>n. f n' then
      let n = LEAST n. \<forall>n'\<ge>n. f n'
      in signed_take_bit n (horner_sum of_bool 2 (map f [0..<n] @ [True]))
     else 0 :: int)"

instance ..

end

lemma int_set_bits_K_False [simp]: "(BITS _. False) = (0 :: int)"
  by (simp add: set_bits_int_def)

lemma int_set_bits_K_True [simp]: "(BITS _. True) = (-1 :: int)"
  by (auto simp add: set_bits_int_def bl_to_bin_def)

end