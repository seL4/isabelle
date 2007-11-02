(* 
    ID:         $Id$
    Author:     John Matthews, Galois Connections, Inc., copyright 2006

    A typeclass for parameterizing types by size.
    Used primarily to parameterize machine word sizes. 
*)

header "The size class"

theory Size
imports Numeral_Type
begin

text {*
  The aim of this is to allow any type as index type, but to provide a
  default instantiation for numeral types. This independence requires
  some duplication with the definitions in Numeral\_Type.
*}
axclass len0 < type

consts
  len_of :: "('a :: len0 itself) => nat"

text {* 
  Some theorems are only true on words with length greater 0.
*}
axclass len < len0
  len_gt_0 [iff]: "0 < len_of TYPE ('a :: len0)"

instance num0  :: len0 ..
instance num1 :: len0 ..
instance bit0 :: (len0) len0 ..
instance bit1 :: (len0) len0 ..

defs (overloaded)
  len_num0:  "len_of (x::num0 itself) == 0"
  len_num1: "len_of (x::num1 itself) == 1"
  len_bit0: "len_of (x::'a::len0 bit0 itself) == 2 * len_of TYPE ('a)"
  len_bit1: "len_of (x::'a::len0 bit1 itself) == 2 * len_of TYPE ('a) + 1"

lemmas len_of_numeral_defs [simp] = len_num0 len_num1 len_bit0 len_bit1

instance num1 :: len by (intro_classes) simp
instance bit0 :: (len) len by (intro_classes) simp
instance bit1 :: (len0) len by (intro_classes) simp

-- "Examples:"
lemma "len_of TYPE(17) = 17" by simp
lemma "len_of TYPE(0) = 0" by simp

-- "not simplified:"
lemma "len_of TYPE('a::len0) = x"
  oops
   
end

