(*  Title:      HOL/Library/Code_Target_Nat.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Implementation of natural numbers by target-language integers\<close>

theory Code_Target_Nat
imports Code_Abstract_Nat
begin

subsection \<open>Implementation for \<^typ>\<open>nat\<close>\<close>

context
includes integer.lifting
begin

lift_definition Nat :: "integer \<Rightarrow> nat"
  is nat
  .

lemma [code_post]:
  "Nat 0 = 0"
  "Nat 1 = 1"
  "Nat (numeral k) = numeral k"
  by (transfer, simp)+

lemma [code_abbrev]:
  "integer_of_nat = of_nat"
  by transfer rule

lemma [code_unfold]:
  "Int.nat (int_of_integer k) = nat_of_integer k"
  by transfer rule

lemma [code abstype]:
  "Code_Target_Nat.Nat (integer_of_nat n) = n"
  by transfer simp

lemma [code abstract]:
  "integer_of_nat (nat_of_integer k) = max 0 k"
  by transfer auto

lemma [code_abbrev]:
  "nat_of_integer (numeral k) = nat_of_num k"
  by transfer (simp add: nat_of_num_numeral)

context
begin  

qualified definition natural :: "num \<Rightarrow> nat"
  where [simp]: "natural = nat_of_num"

lemma [code_computation_unfold]:
  "numeral = natural"
  "nat_of_num = natural"
  by (simp_all add: nat_of_num_numeral)

end

lemma [code abstract]:
  "integer_of_nat (nat_of_num n) = integer_of_num n"
  by (simp add: nat_of_num_numeral integer_of_nat_numeral)

lemma [code abstract]:
  "integer_of_nat 0 = 0"
  by transfer simp

lemma [code abstract]:
  "integer_of_nat 1 = 1"
  by transfer simp

lemma [code]:
  "Suc n = n + 1"
  by simp

lemma [code abstract]:
  "integer_of_nat (m + n) = of_nat m + of_nat n"
  by transfer simp

lemma [code abstract]:
  "integer_of_nat (m - n) = max 0 (of_nat m - of_nat n)"
  by transfer simp

lemma [code abstract]:
  "integer_of_nat (m * n) = of_nat m * of_nat n"
  by transfer (simp add: of_nat_mult)

lemma [code abstract]:
  "integer_of_nat (m div n) = of_nat m div of_nat n"
  by transfer (simp add: zdiv_int)

lemma [code abstract]:
  "integer_of_nat (m mod n) = of_nat m mod of_nat n"
  by transfer (simp add: zmod_int)

context
  includes integer.lifting
begin

lemma divmod_nat_code [code]: \<^marker>\<open>contributor \<open>René Thiemann\<close>\<close> \<^marker>\<open>contributor \<open>Akihisa Yamada\<close>\<close>
  "Euclidean_Rings.divmod_nat m n = (
     let k = integer_of_nat m; l = integer_of_nat n
     in map_prod nat_of_integer nat_of_integer
       (if k = 0 then (0, 0)
        else if l = 0 then (0, k) else
          Code_Numeral.divmod_abs k l))"
  by (simp add: prod_eq_iff Let_def Euclidean_Rings.divmod_nat_def; transfer)
    (simp add: nat_div_distrib nat_mod_distrib)

end

lemma [code]:
  "divmod m n = map_prod nat_of_integer nat_of_integer (divmod m n)"
  by (simp only: prod_eq_iff divmod_def map_prod_def case_prod_beta fst_conv snd_conv; transfer)
    (simp_all only: nat_div_distrib nat_mod_distrib
        zero_le_numeral nat_numeral)
  
lemma [code]:
  "HOL.equal m n = HOL.equal (of_nat m :: integer) (of_nat n)"
  by transfer (simp add: equal)

lemma [code]:
  "m \<le> n \<longleftrightarrow> (of_nat m :: integer) \<le> of_nat n"
  by simp

lemma [code]:
  "m < n \<longleftrightarrow> (of_nat m :: integer) < of_nat n"
  by simp

lemma num_of_nat_code [code]:
  "num_of_nat = num_of_integer \<circ> of_nat"
  by transfer (simp add: fun_eq_iff)

end

lemma (in semiring_1) of_nat_code_if:
  "of_nat n = (if n = 0 then 0
     else let
       (m, q) = Euclidean_Rings.divmod_nat n 2;
       m' = 2 * of_nat m
     in if q = 0 then m' else m' + 1)"
  by (cases n)
    (simp_all add: Let_def Euclidean_Rings.divmod_nat_def ac_simps
      flip: of_nat_numeral of_nat_mult minus_mod_eq_mult_div)

declare of_nat_code_if [code]

definition int_of_nat :: "nat \<Rightarrow> int" where
  [code_abbrev]: "int_of_nat = of_nat"

lemma [code]:
  "int_of_nat n = int_of_integer (of_nat n)"
  by (simp add: int_of_nat_def)

lemma [code abstract]:
  "integer_of_nat (nat k) = max 0 (integer_of_int k)"
  including integer.lifting by transfer auto

definition char_of_nat :: "nat \<Rightarrow> char"
  where [code_abbrev]: "char_of_nat = char_of"

definition nat_of_char :: "char \<Rightarrow> nat"
  where [code_abbrev]: "nat_of_char = of_char"

lemma [code]:
  "char_of_nat = char_of_integer \<circ> integer_of_nat"
  including integer.lifting unfolding char_of_integer_def char_of_nat_def
  by transfer (simp add: fun_eq_iff)

lemma [code abstract]:
  "integer_of_nat (nat_of_char c) = integer_of_char c"
  by (cases c) (simp add: nat_of_char_def integer_of_char_def integer_of_nat_eq_of_nat)

lemma term_of_nat_code [code]:
  \<comment> \<open>Use \<^term>\<open>Code_Numeral.nat_of_integer\<close> in term reconstruction
        instead of \<^term>\<open>Code_Target_Nat.Nat\<close> such that reconstructed
        terms can be fed back to the code generator\<close>
  "term_of_class.term_of n =
   Code_Evaluation.App
     (Code_Evaluation.Const (STR ''Code_Numeral.nat_of_integer'')
        (typerep.Typerep (STR ''fun'')
           [typerep.Typerep (STR ''Code_Numeral.integer'') [],
         typerep.Typerep (STR ''Nat.nat'') []]))
     (term_of_class.term_of (integer_of_nat n))"
  by (simp add: term_of_anything)

lemma nat_of_integer_code_post [code_post]:
  "nat_of_integer 0 = 0"
  "nat_of_integer 1 = 1"
  "nat_of_integer (numeral k) = numeral k"
  including integer.lifting by (transfer, simp)+

context
  includes integer.lifting and bit_operations_syntax
begin

declare [[code drop: \<open>bit :: nat \<Rightarrow> _\<close>
  \<open>and :: nat \<Rightarrow> _\<close> \<open>or :: nat \<Rightarrow> _\<close> \<open>xor :: nat \<Rightarrow> _\<close>
  \<open>push_bit :: _ \<Rightarrow> _ \<Rightarrow> nat\<close> \<open>drop_bit :: _ \<Rightarrow> _ \<Rightarrow> nat\<close> \<open>take_bit :: _ \<Rightarrow> _ \<Rightarrow> nat\<close>]]

lemma [code]:
  \<open>bit m n \<longleftrightarrow> bit (integer_of_nat m) n\<close>
  by transfer (simp add: bit_simps)

lemma [code]:
  \<open>integer_of_nat (m AND n) = integer_of_nat m AND integer_of_nat n\<close>
  by transfer (simp add: of_nat_and_eq)

lemma [code]:
  \<open>integer_of_nat (m OR n) = integer_of_nat m OR integer_of_nat n\<close>
  by transfer (simp add: of_nat_or_eq)

lemma [code]:
  \<open>integer_of_nat (m XOR n) = integer_of_nat m XOR integer_of_nat n\<close>
  by transfer (simp add: of_nat_xor_eq)

lemma [code]:
  \<open>integer_of_nat (push_bit n m) = push_bit n (integer_of_nat m)\<close>
  by transfer (simp add: of_nat_push_bit)

lemma [code]:
  \<open>integer_of_nat (drop_bit n m) = drop_bit n (integer_of_nat m)\<close>
  by transfer (simp add: of_nat_drop_bit)

lemma [code]:
  \<open>integer_of_nat (take_bit n m) = take_bit n (integer_of_nat m)\<close>
  by transfer (simp add: of_nat_take_bit)

lemma [code]:
  \<open>integer_of_nat (mask n) = mask n\<close>
  by transfer (simp add: of_nat_mask_eq)

lemma [code]:
  \<open>integer_of_nat (set_bit n m) = set_bit n (integer_of_nat m)\<close>
  by transfer (simp add: of_nat_set_bit_eq)

lemma [code]:
  \<open>integer_of_nat (unset_bit n m) = unset_bit n (integer_of_nat m)\<close>
  by transfer (simp add: of_nat_unset_bit_eq)

lemma [code]:
  \<open>integer_of_nat (flip_bit n m) = flip_bit n (integer_of_nat m)\<close>
  by transfer (simp add: of_nat_flip_bit_eq)

end

code_identifier
  code_module Code_Target_Nat \<rightharpoonup>
    (SML) Arith and (OCaml) Arith and (Haskell) Arith

end
