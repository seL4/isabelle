(*  Author:  Stefan Berghofer et al.
*)

subsection \<open>Signed division: negative results rounded towards zero rather than minus infinity.\<close>

theory Signed_Division
  imports Main
begin

class signed_division =
  fixes signed_divide :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl "sdiv" 70)
  and signed_modulo :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl "smod" 70)

instantiation int :: signed_division
begin

definition signed_divide_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>k sdiv l = sgn k * sgn l * (\<bar>k\<bar> div \<bar>l\<bar>)\<close> for k l :: int

definition signed_modulo_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>k smod l = k - (k sdiv l) * l\<close> for k l :: int

instance ..

end

end
