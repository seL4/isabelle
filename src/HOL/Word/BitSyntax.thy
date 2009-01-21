(* 
  ID:     $Id$
  Author: Brian Huffman, PSU and Gerwin Klein, NICTA

  Syntactic class for bitwise operations.
*)


header {* Syntactic classes for bitwise operations *}

theory BitSyntax
imports BinGeneral
begin

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
  "NOT bit.B0 = bit.B1"
  | "NOT bit.B1 = bit.B0"

primrec bitAND_bit where
  "bit.B0 AND y = bit.B0"
  | "bit.B1 AND y = y"

primrec bitOR_bit where
  "bit.B0 OR y = y"
  | "bit.B1 OR y = bit.B1"

primrec bitXOR_bit where
  "bit.B0 XOR y = y"
  | "bit.B1 XOR y = NOT y"

instance  ..

end

lemmas bit_simps =
  bitNOT_bit.simps bitAND_bit.simps bitOR_bit.simps bitXOR_bit.simps

lemma bit_extra_simps [simp]: 
  "x AND bit.B0 = bit.B0"
  "x AND bit.B1 = x"
  "x OR bit.B1 = bit.B1"
  "x OR bit.B0 = x"
  "x XOR bit.B1 = NOT x"
  "x XOR bit.B0 = x"
  by (cases x, auto)+

lemma bit_ops_comm: 
  "(x::bit) AND y = y AND x"
  "(x::bit) OR y = y OR x"
  "(x::bit) XOR y = y XOR x"
  by (cases y, auto)+

lemma bit_ops_same [simp]: 
  "(x::bit) AND x = x"
  "(x::bit) OR x = x"
  "(x::bit) XOR x = bit.B0"
  by (cases x, auto)+

lemma bit_not_not [simp]: "NOT (NOT (x::bit)) = x"
  by (cases x) auto

end
