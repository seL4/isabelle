(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Test of target-language bit operations\<close>

theory Generate_Target_Bit_Operations
imports
  "HOL-Library.Code_Test"
begin

context
  includes bit_operations_syntax
begin

qualified definition computations where
  \<open>computations = (
    [bit (473514 :: integer) 5, bit (- 805167 :: integer) 7],
    [473514 AND 767063, - 805167 AND 767063, 473514 AND - 314527, - 805167 AND - 314527 :: integer],
    [473514 OR 767063, - 805167 OR 767063, 473514 OR - 314527, - 805167 OR - 314527 :: integer],
    [473514 XOR 767063, - 805167 XOR 767063, 473514 XOR - 314527, - 805167 XOR - 314527 :: integer],
    [NOT 473513, NOT (- 805167) :: integer],
    mask 39 :: integer,
    [set_bit 15 473514, set_bit 11 (- 805167) :: integer],
    [unset_bit 13 473514, unset_bit 12 (- 805167) :: integer],
    [flip_bit 15 473514, flip_bit 12 (- 805167) :: integer],
    [push_bit 12 473514, push_bit 12 (- 805167) :: integer],
    [drop_bit 12 473514, drop_bit 12 (- 805167) :: integer],
    [take_bit 12 473514, take_bit 12 (- 805167) :: integer],
    [signed_take_bit 12 473514, signed_take_bit 12 (- 805167) :: integer]
  )\<close>

qualified definition results where
  \<open>results = (
    [True, True],
    [208898, 242769, 209184, - 839103 :: integer],
    [1031679, - 280873, - 50197, - 280591 :: integer],
    [822781, - 523642, - 259381, 558512 :: integer],
    [- 473514, 805166 :: integer],
    549755813887 :: integer,
    [506282, - 803119 :: integer],
    [465322, - 809263 :: integer],
    [506282, - 809263 :: integer],
    [1939513344, - 3297964032 :: integer],
    [115, - 197 :: integer],
    [2474, 1745 :: integer],
    [- 1622, - 2351 :: integer]
  )\<close>

qualified definition check where
  \<open>check \<longleftrightarrow> computations = results\<close>

lemma check
  by code_simp

lemma check
  by normalization

lemma check
  by eval

test_code check in Scala

text \<open>Checking the index maximum for \<^verbatim>\<open>PolyML\<close>.\<close>

qualified definition \<open>check_max = ()\<close>

qualified definition \<open>anchor = (Code_Numeral.drop_bit, check_max)\<close>

end

code_printing
    code_module Check_Max  \<rightharpoonup>
      (SML) \<open>
fun check_max max =
  let
    val _ = IntInf.~>> (0, max);
    val _ = ((IntInf.~>> (0, Word.+ (max, Word.fromInt 1)); raise Fail "Bad max") handle Size => ())
  in () end;
\<close>
  | constant Generate_Target_Bit_Operations.check_max \<rightharpoonup>
      (SML) "check'_max Bit'_Shifts.word'_max'_index"

test_code \<open>snd Generate_Target_Bit_Operations.anchor = ()\<close> in PolyML

end
