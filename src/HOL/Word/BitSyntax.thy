(* 
  ID:     $Id$
  Author: Brian Huffman, PSU and Gerwin Klein, NICTA

  Syntactic class for bitwise operations.
*)


header {* Syntactic class for bitwise operations *}

theory BitSyntax
imports Main
begin

class bit = type +
  fixes bitNOT :: "'a \<Rightarrow> 'a"
    and bitAND :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and bitOR  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and bitXOR :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

text {*
  We want the bitwise operations to bind slightly weaker
  than @{text "+"} and @{text "-"}, but @{text "~~"} to 
  bind slightly stronger than @{text "*"}.
*}

notation
  bitNOT  ("NOT _" [70] 71) and
  bitAND  (infixr "AND" 64) and
  bitOR   (infixr "OR"  59) and
  bitXOR  (infixr "XOR" 59)

text {*
  Testing and shifting operations.
*}
consts
  test_bit :: "'a::bit \<Rightarrow> nat \<Rightarrow> bool" (infixl "!!" 100)
  lsb      :: "'a::bit \<Rightarrow> bool"
  msb      :: "'a::bit \<Rightarrow> bool"
  set_bit  :: "'a::bit \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 'a"
  set_bits :: "(nat \<Rightarrow> bool) \<Rightarrow> 'a::bit" (binder "BITS " 10)
  shiftl   :: "'a::bit \<Rightarrow> nat \<Rightarrow> 'a" (infixl "<<" 55)
  shiftr   :: "'a::bit \<Rightarrow> nat \<Rightarrow> 'a" (infixl ">>" 55)


subsection {* Bitwise operations on type @{typ bit} *}

instantiation bit :: bit
begin

definition
  NOT_bit_def: "NOT x = (case x of bit.B0 \<Rightarrow> bit.B1 | bit.B1 \<Rightarrow> bit.B0)"

definition
  AND_bit_def: "x AND y = (case x of bit.B0 \<Rightarrow> bit.B0 | bit.B1 \<Rightarrow> y)"

definition
  OR_bit_def: "(x OR y \<Colon> bit) = NOT (NOT x AND NOT y)"

definition
  XOR_bit_def: "(x XOR y \<Colon> bit) = (x AND NOT y) OR (NOT x AND y)"

instance  ..

end

lemma bit_simps [simp]:
  "NOT bit.B0 = bit.B1"
  "NOT bit.B1 = bit.B0"
  "bit.B0 AND y = bit.B0"
  "bit.B1 AND y = y"
  "bit.B0 OR y = y"
  "bit.B1 OR y = bit.B1"
  "bit.B0 XOR y = y"
  "bit.B1 XOR y = NOT y"
  by (simp_all add: NOT_bit_def AND_bit_def OR_bit_def
                    XOR_bit_def split: bit.split)

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
