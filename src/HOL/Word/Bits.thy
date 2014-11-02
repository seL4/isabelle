(*  Title:      HOL/Word/Bits.thy
    Author:     Author: Brian Huffman, PSU and Gerwin Klein, NICTA
*)

section {* Syntactic classes for bitwise operations *}

theory Bits
imports Main
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

end

