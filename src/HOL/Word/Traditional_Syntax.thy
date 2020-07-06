(*  Author:     Jeremy Dawson, NICTA
*)

section \<open>Operation variants with traditional syntax\<close>

theory Traditional_Syntax
  imports Main
begin

class semiring_bit_syntax = semiring_bit_shifts +
  fixes test_bit :: \<open>'a \<Rightarrow> nat \<Rightarrow> bool\<close>  (infixl "!!" 100)
    and shiftl :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl "<<" 55)
    and shiftr :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl ">>" 55)
  assumes test_bit_eq_bit: \<open>test_bit = bit\<close>
    and shiftl_eq_push_bit: \<open>a << n = push_bit n a\<close>
    and shiftr_eq_drop_bit: \<open>a >> n = drop_bit n a\<close>

end
