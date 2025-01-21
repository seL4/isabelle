(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Tests for simplifying bit operations on ground terms\<close>

theory Bit_Operation_Calculations
  imports
    "HOL.Bit_Operations"
    "HOL-Library.Word"
begin

unbundle bit_operations_syntax

subsection \<open>Generic unsigned computations\<close>

locale unsigned_computations =
  fixes type :: \<open>'a::semiring_bit_operations itself\<close>
begin

definition computations where
  \<open>computations = (
    [bit (473514 :: 'a) 5],
    [473514 AND 767063 :: 'a],
    [473514 OR 767063 :: 'a],
    [473514 XOR 767063 :: 'a],
    mask 11 :: 'a,
    [set_bit 15 473514 :: 'a],
    [unset_bit 13 473514 :: 'a],
    [flip_bit 15 473514 :: 'a],
    [push_bit 12 473514 :: 'a],
    [drop_bit 12 65344 :: 'a],
    [take_bit 12 473514 :: 'a]
  )\<close>

definition results where
  \<open>results = (
    [True],
    [208898 :: 'a::semiring_bit_operations],
    [1031679 :: 'a],
    [822781 :: 'a],
    2047 :: 'a,
    [506282 :: 'a],
    [465322 :: 'a],
    [506282 :: 'a],
    [1939513344 :: 'a],
    [15 :: 'a],
    [2474 :: 'a]
  )\<close>

lemmas evaluation_simps = computations_def results_def mask_numeral
   \<comment> \<open>Expressions like \<term>\<open>mask 42\<close> are deliberately not simplified by default\<close>

end

global_interpretation unsigned_computations_nat: unsigned_computations \<open>TYPE(nat)\<close>
  defines unsigned_computations_nat = unsigned_computations_nat.computations
    and unsigned_results_nat = unsigned_computations_nat.results .

lemma \<open>unsigned_computations_nat.computations = unsigned_computations_nat.results\<close>
  by (simp add: unsigned_computations_nat.evaluation_simps)

global_interpretation unsigned_computations_int: unsigned_computations \<open>TYPE(int)\<close>
  defines unsigned_computations_int = unsigned_computations_int.computations
    and unsigned_results_int = unsigned_computations_int.results .

lemma \<open>unsigned_computations_int.computations = unsigned_computations_int.results\<close>
  by (simp add: unsigned_computations_int.evaluation_simps)

global_interpretation unsigned_computations_word16: unsigned_computations \<open>TYPE(16 word)\<close>
  defines unsigned_computations_word16 = unsigned_computations_word16.computations
    and unsigned_results_word16 = unsigned_computations_word16.results .

lemma \<open>unsigned_computations_word16 = unsigned_results_word16\<close>
  by (simp add: unsigned_computations_word16.evaluation_simps)


subsection \<open>Generic unsigned computations\<close>

locale signed_computations =
  fixes type :: \<open>'a::ring_bit_operations itself\<close>
begin

definition computations where
  \<open>computations = (
    [bit (- 805167 :: 'a) 7],
    [- 805167 AND 767063, 473514 AND - 314527, - 805167 AND - 314527 :: 'a],
    [- 805167 OR 767063, 473514 OR - 314527, - 805167 OR - 314527 :: 'a],
    [- 805167 XOR 767063, 473514 XOR - 314527, - 805167 XOR - 314527 :: 'a],
    [NOT 473513, NOT (- 805167) :: 'a],
    [set_bit 11 (- 805167) :: 'a],
    [unset_bit 12 (- 805167) :: 'a],
    [flip_bit 12 (- 805167) :: 'a],
    [push_bit 12 (- 805167) :: 'a],
    [take_bit 12 (- 805167) :: 'a],
    [signed_take_bit 12 473514, signed_take_bit 12 (- 805167) :: 'a]
  )\<close>

definition results where
  \<open>results = (
    [True],
    [242769, 209184, - 839103 :: 'a],
    [- 280873, - 50197, - 280591 :: 'a],
    [- 523642, - 259381, 558512 :: 'a],
    [- 473514, 805166 :: 'a],
    [- 803119 :: 'a],
    [- 809263 :: 'a],
    [- 809263 :: 'a],
    [- 3297964032 :: 'a],
    [1745 :: 'a],
    [- 1622, - 2351 :: 'a]
  )\<close>

lemmas evaluation_simps = computations_def results_def

end

global_interpretation signed_computations_int: signed_computations \<open>TYPE(int)\<close>
  defines signed_computations_int = signed_computations_int.computations
    and signed_results_int = signed_computations_int.results .

lemma \<open>signed_computations_int.computations = signed_computations_int.results\<close>
  by (simp add: signed_computations_int.evaluation_simps)

global_interpretation signed_computations_word16: signed_computations \<open>TYPE(16 word)\<close>
  defines signed_computations_word16 = signed_computations_word16.computations
    and signed_results_word16 = signed_computations_word16.results .

lemma \<open>signed_computations_word16 = signed_results_word16\<close>
  by (simp add: signed_computations_word16.evaluation_simps)


subsection \<open>Special cases on particular type instances\<close>

lemma
  \<open>drop_bit 12 (- 17405 :: int) = - 5\<close>
  by simp

lemma
  \<open>signed_drop_bit 12 (- 17405 :: 16 word) = - 5\<close>
  by simp

lemma
  \<open>drop_bit 12 (- 17405 :: 16 word) = 11\<close>
  by simp

end
