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

syntax "_type_length" :: "type \<Rightarrow> nat" ("(1LENGTH/(1'(_')))")

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

end
