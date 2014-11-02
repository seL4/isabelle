(*  Title:      HOL/Word/Type_Length.thy
    Author:     John Matthews, Galois Connections, Inc., copyright 2006
*)

section {* Assigning lengths to types by typeclasses *}

theory Type_Length
imports "~~/src/HOL/Library/Numeral_Type"
begin

text {*
  The aim of this is to allow any type as index type, but to provide a
  default instantiation for numeral types. This independence requires
  some duplication with the definitions in @{text "Numeral_Type"}.
*}

class len0 =
  fixes len_of :: "'a itself \<Rightarrow> nat"

text {* 
  Some theorems are only true on words with length greater 0.
*}

class len = len0 +
  assumes len_gt_0 [iff]: "0 < len_of TYPE ('a)"

instantiation num0 and num1 :: len0
begin

definition
  len_num0:  "len_of (x::num0 itself) = 0"

definition
  len_num1: "len_of (x::num1 itself) = 1"

instance ..

end

instantiation bit0 and bit1 :: (len0) len0
begin

definition
  len_bit0: "len_of (x::'a::len0 bit0 itself) = 2 * len_of TYPE ('a)"

definition
  len_bit1: "len_of (x::'a::len0 bit1 itself) = 2 * len_of TYPE ('a) + 1"

instance ..

end

lemmas len_of_numeral_defs [simp] = len_num0 len_num1 len_bit0 len_bit1

instance num1 :: len proof qed simp
instance bit0 :: (len) len proof qed simp
instance bit1 :: (len0) len proof qed simp

end

