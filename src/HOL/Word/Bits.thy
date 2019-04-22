(*  Title:      HOL/Word/Bits.thy
    Author:     Author: Brian Huffman, PSU and Gerwin Klein, NICTA
*)

section \<open>Syntactic classes for bitwise operations\<close>

theory Bits
  imports Main
begin

class bit =
  fixes bitNOT :: "'a \<Rightarrow> 'a"  ("NOT _" [70] 71)
    and bitAND :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "AND" 64)
    and bitOR :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "OR"  59)
    and bitXOR :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "XOR" 59)

text \<open>
  We want the bitwise operations to bind slightly weaker
  than \<open>+\<close> and \<open>-\<close>, but \<open>~~\<close> to
  bind slightly stronger than \<open>*\<close>.
\<close>

class bits = bit +
  fixes test_bit :: "'a \<Rightarrow> nat \<Rightarrow> bool"  (infixl "!!" 100)
    and lsb :: "'a \<Rightarrow> bool"
    and msb :: "'a \<Rightarrow> bool"
    and set_bit :: "'a \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 'a"
    and set_bits :: "(nat \<Rightarrow> bool) \<Rightarrow> 'a"  (binder "BITS " 10)
    and shiftl :: "'a \<Rightarrow> nat \<Rightarrow> 'a"  (infixl "<<" 55)
    and shiftr :: "'a \<Rightarrow> nat \<Rightarrow> 'a"  (infixl ">>" 55)

end
