(*  Title:      HOL/Word/Bit_Operations.thy
    Author:     Author: Brian Huffman, PSU and Gerwin Klein, NICTA
*)

header {* Syntactic classes for bitwise operations *}

theory Bit_Operations
imports "~~/src/HOL/Library/Bit"
begin

subsection {* Abstract syntactic bit operations *}

class bit =
  fixes bitNOT :: "'a \<Rightarrow> 'a"       ("NOT _" [70] 71)
    and bitAND :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "AND" 64)
    and bitOR  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "OR"  59)
    and bitXOR :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "XOR" 59)

text {*
  We want the bitwise operations to bind slightly weaker
  than @{text "+"} and @{text "-"}, but @{text "~~"} to 
  bind slightly stronger than @{text "*"}.
*}

text {*
  Testing and shifting operations.
*}

class bits = bit +
  fixes test_bit :: "'a \<Rightarrow> nat \<Rightarrow> bool" (infixl "!!" 100)
    and lsb      :: "'a \<Rightarrow> bool"
    and set_bit  :: "'a \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 'a"
    and set_bits :: "(nat \<Rightarrow> bool) \<Rightarrow> 'a" (binder "BITS " 10)
    and shiftl   :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infixl "<<" 55)
    and shiftr   :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infixl ">>" 55)

class bitss = bits +
  fixes msb      :: "'a \<Rightarrow> bool"

  
subsection {* Bitwise operations on @{typ bit} *}

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

end
