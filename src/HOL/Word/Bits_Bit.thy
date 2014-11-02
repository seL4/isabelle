(*  Title:      HOL/Word/Bits_Bit.thy
    Author:     Author: Brian Huffman, PSU and Gerwin Klein, NICTA
*)

section {* Bit operations in $\cal Z_2$ *}

theory Bits_Bit
imports Bits "~~/src/HOL/Library/Bit"
begin

instantiation bit :: bit
begin

primrec bitNOT_bit where
  "NOT 0 = (1::bit)"
  | "NOT 1 = (0::bit)"

primrec bitAND_bit where
  "0 AND y = (0::bit)"
  | "1 AND y = (y::bit)"

primrec bitOR_bit where
  "0 OR y = (y::bit)"
  | "1 OR y = (1::bit)"

primrec bitXOR_bit where
  "0 XOR y = (y::bit)"
  | "1 XOR y = (NOT y :: bit)"

instance  ..

end

lemmas bit_simps =
  bitNOT_bit.simps bitAND_bit.simps bitOR_bit.simps bitXOR_bit.simps

lemma bit_extra_simps [simp]: 
  "x AND 0 = (0::bit)"
  "x AND 1 = (x::bit)"
  "x OR 1 = (1::bit)"
  "x OR 0 = (x::bit)"
  "x XOR 1 = NOT (x::bit)"
  "x XOR 0 = (x::bit)"
  by (cases x, auto)+

lemma bit_ops_comm: 
  "(x::bit) AND y = y AND x"
  "(x::bit) OR y = y OR x"
  "(x::bit) XOR y = y XOR x"
  by (cases y, auto)+

lemma bit_ops_same [simp]: 
  "(x::bit) AND x = x"
  "(x::bit) OR x = x"
  "(x::bit) XOR x = 0"
  by (cases x, auto)+

lemma bit_not_not [simp]: "NOT (NOT (x::bit)) = x"
  by (cases x) auto

lemma bit_or_def: "(b::bit) OR c = NOT (NOT b AND NOT c)"
  by (induct b, simp_all)

lemma bit_xor_def: "(b::bit) XOR c = (b AND NOT c) OR (NOT b AND c)"
  by (induct b, simp_all)

lemma bit_NOT_eq_1_iff [simp]: "NOT (b::bit) = 1 \<longleftrightarrow> b = 0"
  by (induct b, simp_all)

lemma bit_AND_eq_1_iff [simp]: "(a::bit) AND b = 1 \<longleftrightarrow> a = 1 \<and> b = 1"
  by (induct a, simp_all)

end
