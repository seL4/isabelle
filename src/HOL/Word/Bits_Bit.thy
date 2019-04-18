(*  Title:      HOL/Word/Bits_Bit.thy
    Author:     Author: Brian Huffman, PSU and Gerwin Klein, NICTA
*)

section \<open>Bit operations in $\cal Z_2$\<close>

theory Bits_Bit
  imports Bits "HOL-Library.Bit"
begin

instantiation bit :: bit
begin

primrec bitNOT_bit
  where
    "NOT 0 = (1::bit)"
  | "NOT 1 = (0::bit)"

primrec bitAND_bit
  where
    "0 AND y = (0::bit)"
  | "1 AND y = (y::bit)"

primrec bitOR_bit
  where
    "0 OR y = (y::bit)"
  | "1 OR y = (1::bit)"

primrec bitXOR_bit
  where
    "0 XOR y = (y::bit)"
  | "1 XOR y = (NOT y :: bit)"

instance  ..

end

lemmas bit_simps =
  bitNOT_bit.simps bitAND_bit.simps bitOR_bit.simps bitXOR_bit.simps

lemma bit_extra_simps [simp]:
  "x AND 0 = 0"
  "x AND 1 = x"
  "x OR 1 = 1"
  "x OR 0 = x"
  "x XOR 1 = NOT x"
  "x XOR 0 = x"
  for x :: bit
  by (cases x; auto)+

lemma bit_ops_comm:
  "x AND y = y AND x"
  "x OR y = y OR x"
  "x XOR y = y XOR x"
  for x :: bit
  by (cases y; auto)+

lemma bit_ops_same [simp]:
  "x AND x = x"
  "x OR x = x"
  "x XOR x = 0"
  for x :: bit
  by (cases x; auto)+

lemma bit_not_not [simp]: "NOT (NOT x) = x"
  for x :: bit
  by (cases x) auto

lemma bit_or_def: "b OR c = NOT (NOT b AND NOT c)"
  for b c :: bit
  by (induct b) simp_all

lemma bit_xor_def: "b XOR c = (b AND NOT c) OR (NOT b AND c)"
  for b c :: bit
  by (induct b) simp_all

lemma bit_NOT_eq_1_iff [simp]: "NOT b = 1 \<longleftrightarrow> b = 0"
  for b :: bit
  by (induct b) simp_all

lemma bit_AND_eq_1_iff [simp]: "a AND b = 1 \<longleftrightarrow> a = 1 \<and> b = 1"
  for a b :: bit
  by (induct a) simp_all

lemma bit_nand_same [simp]: "x AND NOT x = 0"
  for x :: bit
  by (cases x) simp_all

end
