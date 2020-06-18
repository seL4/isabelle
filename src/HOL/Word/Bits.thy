(*  Title:      HOL/Word/Bits.thy
    Author:     Brian Huffman, PSU and Gerwin Klein, NICTA
*)

section \<open>Syntactic type classes for bit operations\<close>

theory Bits
  imports Main "HOL-Library.Bit_Operations"
begin

class bit_operations =
  fixes shiftl :: "'a \<Rightarrow> nat \<Rightarrow> 'a"  (infixl "<<" 55)
    and shiftr :: "'a \<Rightarrow> nat \<Rightarrow> 'a"  (infixl ">>" 55)
  fixes test_bit :: "'a \<Rightarrow> nat \<Rightarrow> bool"  (infixl "!!" 100)
    and lsb :: "'a \<Rightarrow> bool"
    and msb :: "'a \<Rightarrow> bool"
    and set_bit :: "'a \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> 'a"

text \<open>
  We want the bitwise operations to bind slightly weaker
  than \<open>+\<close> and \<open>-\<close>, but \<open>~~\<close> to
  bind slightly stronger than \<open>*\<close>.
\<close>

end
