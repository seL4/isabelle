(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Tests for simplifying word operations on ground terms\<close>

theory Word_Computations
  imports
    "HOL.Bit_Operations"
    "HOL-Library.Word"
begin

unbundle bit_operations_syntax

named_theorems eval

declare mask_numeral [eval]

type_synonym word16 = \<open>16 word\<close>
type_synonym word32 = \<open>32 word\<close>

definition computations_arith where
  [eval]: \<open>computations_arith = (
    [473514 + - 763, - 5324 - 7892 :: word16],
    [3131 * - 42, - 2342 div 1213, 2152 mod - 235 :: word16],
    [12323 \<le> (- 12132 :: word16), - 123 < (321312 :: word16), 12323 \<le>s (- 12132 :: word16), - 123 <s (321312 :: word16)]
  )\<close>

definition results_arith where
  [eval]: \<open>results_arith = (
    [472751, - 13216 :: word16],
    [- 131502, 52, 2152 :: word16],
    [True, False, False, False]
  )\<close>

lemma \<open>computations_arith = results_arith\<close>
  by (simp add: eval)
 
definition computations_bit where
  [eval]: \<open>computations_bit = (
    [bit (473514 :: word16) 5, bit (- 805167 :: word16) 7],
    [NOT 473513, NOT (- 805167) :: word16],
    [473514 AND 767063, - 805167 AND 767063, 473514 AND - 314527, - 805167 AND - 314527 :: word16],
    [473514 OR 767063, - 805167 OR 767063, 473514 OR - 314527, - 805167 OR - 314527 :: word16],
    [473514 XOR 767063, - 805167 XOR 767063, 473514 XOR - 314527, - 805167 XOR - 314527 :: word16],
    mask 11 :: word16,
    [set_bit 15 473514, set_bit 11 (- 805167)  :: word16],
    [unset_bit 13 473514, unset_bit 12 (- 805167) :: word16],
    [flip_bit 15 473514, flip_bit 12 (- 805167) :: word16],
    [push_bit 12 473514, push_bit 12 (- 805167) :: word16],
    [drop_bit 12 65344, drop_bit 12 (- 17405) :: word16],
    [signed_drop_bit 12 (- 17405) :: word16],
    [take_bit 12 473514, take_bit 12 (- 805167) :: word16],
    [signed_take_bit 12 473514, signed_take_bit 12 (- 805167) :: word16]
  )\<close>

definition results_bit where
  [eval]: \<open>results_bit = (
    [True, True],
    [- 473514, 805166 :: word16],
    [208898, 242769, 209184, - 839103 :: word16],
    [1031679, - 280873, - 50197, - 280591 :: word16],
    [822781, - 523642, - 259381, 558512 :: word16],
    2047 :: word16,
    [506282, - 803119 :: word16],
    [465322, - 809263 :: word16],
    [506282, - 809263 :: word16],
    [1939513344, - 3297964032 :: word16],
    [15, 11 :: word16],
    [- 5 :: word16],
    [2474, 1745 :: word16],
    [- 1622, - 2351 :: word16]
  )\<close>

lemma \<open>computations_bit = results_bit\<close>
  by (simp add: eval)

end
