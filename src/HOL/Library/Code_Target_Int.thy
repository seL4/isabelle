(*  Title:      HOL/Library/Code_Target_Int.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Implementation of integer numbers by target-language integers\<close>

theory Code_Target_Int
imports Main
begin

code_datatype int_of_integer

declare [[code drop: integer_of_int]]

context
includes integer.lifting
begin

lemma [code]:
  "integer_of_int (int_of_integer k) = k"
  by transfer rule

lemma [code]:
  "Int.Pos = int_of_integer \<circ> integer_of_num"
  by transfer (simp add: fun_eq_iff)

lemma [code]:
  "Int.Neg = int_of_integer \<circ> uminus \<circ> integer_of_num"
  by transfer (simp add: fun_eq_iff)

lemma [code_abbrev]:
  "int_of_integer (numeral k) = Int.Pos k"
  by transfer simp

lemma [code_abbrev]:
  "int_of_integer (- numeral k) = Int.Neg k"
  by transfer simp

context
begin

qualified definition positive :: "num \<Rightarrow> int"
  where [simp]: "positive = numeral"

qualified definition negative :: "num \<Rightarrow> int"
  where [simp]: "negative = uminus \<circ> numeral"

lemma [code_computation_unfold]:
  "numeral = positive"
  "Int.Pos = positive"
  "Int.Neg = negative"
  by (simp_all add: fun_eq_iff)

end

lemma [code, symmetric, code_post]:
  "0 = int_of_integer 0"
  by transfer simp

lemma [code, symmetric, code_post]:
  "1 = int_of_integer 1"
  by transfer simp

lemma [code_post]:
  "int_of_integer (- 1) = - 1"
  by simp

lemma [code]:
  "k + l = int_of_integer (of_int k + of_int l)"
  by transfer simp

lemma [code]:
  "- k = int_of_integer (- of_int k)"
  by transfer simp

lemma [code]:
  "k - l = int_of_integer (of_int k - of_int l)"
  by transfer simp

lemma [code]:
  "Int.dup k = int_of_integer (Code_Numeral.dup (of_int k))"
  by transfer simp

declare [[code drop: Int.sub]]

lemma [code]:
  "k * l = int_of_integer (of_int k * of_int l)"
  by simp

lemma [code]:
  "k div l = int_of_integer (of_int k div of_int l)"
  by simp

lemma [code]:
  "k mod l = int_of_integer (of_int k mod of_int l)"
  by simp

lemma [code]:
  "divmod m n = map_prod int_of_integer int_of_integer (divmod m n)"
  unfolding prod_eq_iff divmod_def map_prod_def case_prod_beta fst_conv snd_conv
  by transfer simp

lemma [code]:
  "HOL.equal k l = HOL.equal (of_int k :: integer) (of_int l)"
  by transfer (simp add: equal)

lemma [code]:
  "k \<le> l \<longleftrightarrow> (of_int k :: integer) \<le> of_int l"
  by transfer rule

lemma [code]:
  "k < l \<longleftrightarrow> (of_int k :: integer) < of_int l"
  by transfer rule

declare [[code drop: "gcd :: int \<Rightarrow> _" "lcm :: int \<Rightarrow> _"]]

lemma gcd_int_of_integer [code]:
  "gcd (int_of_integer x) (int_of_integer y) = int_of_integer (gcd x y)"
  by transfer rule

lemma lcm_int_of_integer [code]:
  "lcm (int_of_integer x) (int_of_integer y) = int_of_integer (lcm x y)"
  by transfer rule

end

lemma (in ring_1) of_int_code_if:
  "of_int k = (if k = 0 then 0
     else if k < 0 then - of_int (- k)
     else let
       l = 2 * of_int (k div 2);
       j = k mod 2
     in if j = 0 then l else l + 1)"
proof -
  from div_mult_mod_eq have *: "of_int k = of_int (k div 2 * 2 + k mod 2)" by simp
  show ?thesis
    by (simp add: Let_def of_int_add [symmetric]) (simp add: * mult.commute)
qed

declare of_int_code_if [code]

lemma [code]:
  "nat = nat_of_integer \<circ> of_int"
  including integer.lifting by transfer (simp add: fun_eq_iff)

definition char_of_int :: "int \<Rightarrow> char"
  where [code_abbrev]: "char_of_int = char_of"

definition int_of_char :: "char \<Rightarrow> int"
  where [code_abbrev]: "int_of_char = of_char"

lemma [code]:
  "char_of_int = char_of_integer \<circ> integer_of_int"
  including integer.lifting unfolding char_of_integer_def char_of_int_def
  by transfer (simp add: fun_eq_iff)

lemma [code]:
  "int_of_char = int_of_integer \<circ> integer_of_char"
  including integer.lifting unfolding integer_of_char_def int_of_char_def
  by transfer (simp add: fun_eq_iff)

context
  includes integer.lifting and bit_operations_syntax
begin

declare [[code drop: \<open>bit :: int \<Rightarrow> _\<close> \<open>not :: int \<Rightarrow> _\<close>
  \<open>and :: int \<Rightarrow> _\<close> \<open>or :: int \<Rightarrow> _\<close> \<open>xor :: int \<Rightarrow> _\<close>
  \<open>push_bit :: _ \<Rightarrow> _ \<Rightarrow> int\<close> \<open>drop_bit :: _ \<Rightarrow> _ \<Rightarrow> int\<close> \<open>take_bit :: _ \<Rightarrow> _ \<Rightarrow> int\<close>]]

lemma [code]:
  \<open>bit (int_of_integer k) n \<longleftrightarrow> bit k n\<close>
  by transfer rule

lemma [code]:
  \<open>NOT (int_of_integer k) = int_of_integer (NOT k)\<close>
  by transfer rule

lemma [code]:
  \<open>int_of_integer k AND int_of_integer l = int_of_integer (k AND l)\<close>
  by transfer rule

lemma [code]:
  \<open>int_of_integer k OR int_of_integer l = int_of_integer (k OR l)\<close>
  by transfer rule

lemma [code]:
  \<open>int_of_integer k XOR int_of_integer l = int_of_integer (k XOR l)\<close>
  by transfer rule

lemma [code]:
  \<open>push_bit n (int_of_integer k) = int_of_integer (push_bit n k)\<close>
  by transfer rule

lemma [code]:
  \<open>drop_bit n (int_of_integer k) = int_of_integer (drop_bit n k)\<close>
  by transfer rule

lemma [code]:
  \<open>take_bit n (int_of_integer k) = int_of_integer (take_bit n k)\<close>
  by transfer rule

lemma [code]:
  \<open>mask n = int_of_integer (mask n)\<close>
  by transfer rule

lemma [code]:
  \<open>set_bit n (int_of_integer k) = int_of_integer (set_bit n k)\<close>
  by transfer rule

lemma [code]:
  \<open>unset_bit n (int_of_integer k) = int_of_integer (unset_bit n k)\<close>
  by transfer rule

lemma [code]:
  \<open>flip_bit n (int_of_integer k) = int_of_integer (flip_bit n k)\<close>
  by transfer rule

end

code_identifier
  code_module Code_Target_Int \<rightharpoonup>
    (SML) Arith and (OCaml) Arith and (Haskell) Arith

end
