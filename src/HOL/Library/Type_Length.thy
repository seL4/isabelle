(*  Title:      HOL/Library/Type_Length.thy
    Author:     John Matthews, Galois Connections, Inc., Copyright 2006
*)

section \<open>Assigning lengths to types by type classes\<close>

theory Type_Length
imports Numeral_Type
begin

text \<open>
  The aim of this is to allow any type as index type, but to provide a
  default instantiation for numeral types. This independence requires
  some duplication with the definitions in \<^file>\<open>Numeral_Type.thy\<close>.
\<close>

class len0 =
  fixes len_of :: "'a itself \<Rightarrow> nat"

syntax "_type_length" :: "type \<Rightarrow> nat" (\<open>(1LENGTH/(1'(_')))\<close>)

translations "LENGTH('a)" \<rightharpoonup>
  "CONST len_of (CONST Pure.type :: 'a itself)"

print_translation \<open>
  let
    fun len_of_itself_tr' ctxt [Const (\<^const_syntax>\<open>Pure.type\<close>, Type (_, [T]))] =
      Syntax.const \<^syntax_const>\<open>_type_length\<close> $ Syntax_Phases.term_of_typ ctxt T
  in [(\<^const_syntax>\<open>len_of\<close>, len_of_itself_tr')] end
\<close>

text \<open>Some theorems are only true on words with length greater 0.\<close>

class len = len0 +
  assumes len_gt_0 [iff]: "0 < LENGTH('a)"
begin

lemma len_not_eq_0 [simp]:
  "LENGTH('a) \<noteq> 0"
  by simp

end

instantiation num0 and num1 :: len0
begin

definition len_num0: "len_of (_ :: num0 itself) = 0"
definition len_num1: "len_of (_ :: num1 itself) = 1"

instance ..

end

instantiation bit0 and bit1 :: (len0) len0
begin

definition len_bit0: "len_of (_ :: 'a::len0 bit0 itself) = 2 * LENGTH('a)"
definition len_bit1: "len_of (_ :: 'a::len0 bit1 itself) = 2 * LENGTH('a) + 1"

instance ..

end

lemmas len_of_numeral_defs [simp] = len_num0 len_num1 len_bit0 len_bit1

instance num1 :: len
  by standard simp
instance bit0 :: (len) len
  by standard simp
instance bit1 :: (len0) len
  by standard simp

instantiation Enum.finite_1 :: len
begin

definition
  "len_of_finite_1 (x :: Enum.finite_1 itself) \<equiv> (1 :: nat)"

instance
  by standard (auto simp: len_of_finite_1_def)

end

instantiation Enum.finite_2 :: len
begin

definition
  "len_of_finite_2 (x :: Enum.finite_2 itself) \<equiv> (2 :: nat)"

instance
  by standard (auto simp: len_of_finite_2_def)

end

instantiation Enum.finite_3 :: len
begin

definition
  "len_of_finite_3 (x :: Enum.finite_3 itself) \<equiv> (4 :: nat)"

instance
  by standard (auto simp: len_of_finite_3_def)

end

lemma length_not_greater_eq_2_iff [simp]:
  \<open>\<not> 2 \<le> LENGTH('a::len) \<longleftrightarrow> LENGTH('a) = 1\<close>
  by (auto simp add: not_le dest: less_2_cases)

context linordered_idom
begin

lemma two_less_eq_exp_length [simp]:
  \<open>2 \<le> 2 ^ LENGTH('b::len)\<close>
  using mult_left_mono [of 1 \<open>2 ^ (LENGTH('b::len) - 1)\<close> 2]
  by (cases \<open>LENGTH('b::len)\<close>) simp_all

end

lemma less_eq_decr_length_iff [simp]:
  \<open>n \<le> LENGTH('a::len) - Suc 0 \<longleftrightarrow> n < LENGTH('a)\<close>
  by (cases \<open>LENGTH('a)\<close>) (simp_all add: less_Suc_eq le_less)

lemma decr_length_less_iff [simp]:
  \<open>LENGTH('a::len) - Suc 0 < n \<longleftrightarrow> LENGTH('a) \<le> n\<close>
  by (cases \<open>LENGTH('a)\<close>) auto

end
