(* 
  ID:     $Id$
  Author: Brian Huffman, PSU and Gerwin Klein, NICTA

  Syntactic class for bitwise operations.
*)


header {* Syntactic class for bitwise operations *}

theory BitSyntax
imports Main
begin

axclass bit < type

text {*
  We want the bitwise operations to bind slightly weaker
  than @{text "+"} and @{text "-"}, but @{text "~~"} to 
  bind slightly stronger than @{text "*"}.
*}
consts
  bitNOT  :: "'a::bit \<Rightarrow> 'a"       ("NOT _" [70] 71)
  bitAND  :: "'a::bit \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "AND" 64)
  bitOR   :: "'a::bit \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "OR"  59)
  bitXOR  :: "'a::bit \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "XOR" 59)

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

instance bit :: bit ..

defs (overloaded)
  NOT_bit_def: "NOT x \<equiv> case x of bit.B0 \<Rightarrow> bit.B1 | bit.B1 \<Rightarrow> bit.B0"
  AND_bit_def: "x AND y \<equiv> case x of bit.B0 \<Rightarrow> bit.B0 | bit.B1 \<Rightarrow> y"
  OR_bit_def: "x OR y :: bit \<equiv> NOT (NOT x AND NOT y)"
  XOR_bit_def: "x XOR y :: bit \<equiv> (x AND NOT y) OR (NOT x AND y)"

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

lemma bit_NOT_NOT: "NOT (NOT (b::bit)) = b"
  by (induct b) simp_all

end
