(*  Title:      HOL/ex/Global_Interpretation.thy
    Author:     Florian Haftmann, TU Muenchen
*)

theory Global_Interpretation
  imports Main
begin

locale nat_on_monoid = monoid
begin

primrec npower :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close> where
  \<open>npower 0 a = \<^bold>1\<close>
| \<open>npower (Suc n) a = npower n a \<^bold>* a\<close>

lemma npower_one_eq [simp]:
  \<open>npower 1 = id\<close>
  by (simp add: fun_eq_iff)

end

locale int_on_group = group + nat_on_monoid
begin

definition zpower :: \<open>int \<Rightarrow> 'a \<Rightarrow> 'a\<close> where
  \<open>zpower k a = (if k < 0 then inverse (npower (nat (- k)) a) else npower (nat k) a)\<close>

lemma zpower_int_eq [simp]:
  \<open>zpower (int n) = npower n\<close>
  by (simp add: zpower_def fun_eq_iff)

lemma zpower_minus_eq:
  \<open>zpower (- k) = inverse \<circ> zpower k\<close>
  by (simp add: zpower_def fun_eq_iff)

lemma zpower_zero_eq [simp]:
  \<open>zpower 0 a = \<^bold>1\<close>
  by (simp add: zpower_def)

lemma zpower_one_eq [simp]:
  \<open>zpower 1 = id\<close>
  by (simp add: zpower_def fun_eq_iff)

lemma zpower_numeral_eq [simp]:
  \<open>zpower (numeral n) = npower (numeral n)\<close>
  by (simp add: zpower_def fun_eq_iff)

lemma zpower_minus_numeral_eq [simp]:
  \<open>zpower (- numeral n) = inverse \<circ> npower (numeral n)\<close>
  by (simp add: zpower_minus_eq)

end

global_interpretation nmult: nat_on_monoid \<open>(+)\<close> \<open>0 :: 'a::monoid_add\<close>
  defines nmult = \<open>nmult.npower\<close>
  ..

global_interpretation zmult: int_on_group \<open>(+)\<close> \<open>0 :: 'a::group_add\<close> uminus
  rewrites \<open>nat_on_monoid.npower (+) (0 :: 'a) = nmult\<close>
  defines zmult = \<open>zmult.zpower\<close>
proof -
  interpret int_on_group \<open>(+)\<close> \<open>0 :: 'a\<close> uminus ..
  show \<open>int_on_group (+) (0 :: 'a) uminus\<close>
    by standard
  show \<open>nat_on_monoid.npower (+) (0 :: 'a) = nmult\<close>
    by (simp only: nmult_def)
qed

global_interpretation npower: nat_on_monoid \<open>(*)\<close> \<open>1 :: 'a::monoid_mult\<close>
  defines npower = \<open>npower.npower\<close>
  ..

end
