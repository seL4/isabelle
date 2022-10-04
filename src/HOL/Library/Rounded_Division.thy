(*  Author:  Florian Haftmann, TU Muenchen
*)

subsection \<open>Rounded division: modulus centered towards zero.\<close>

theory Rounded_Division
  imports Main
begin

definition rounded_divide :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>  (infixl \<open>rdiv\<close> 70)
  where \<open>k rdiv l = (k + l div 2 + of_bool (l < 0)) div l\<close>

definition rounded_modulo :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>  (infixl \<open>rmod\<close> 70)
  where \<open>k rmod l = k - k rdiv l * l\<close>

lemma rdiv_mult_rmod_eq:
  \<open>k rdiv l * l + k rmod l = k\<close>
  by (simp add: rounded_divide_def rounded_modulo_def)

lemma mult_rdiv_rmod_eq:
  \<open>l * (k rdiv l) + k rmod l = k\<close>
  using rdiv_mult_rmod_eq [of k l] by (simp add: ac_simps)

lemma rmod_rdiv_mult_eq:
  \<open>k rmod l + k rdiv l * l = k\<close>
  using rdiv_mult_rmod_eq [of k l] by (simp add: ac_simps)

lemma rmod_mult_rdiv_eq:
  \<open>k rmod l + l * (k rdiv l) = k\<close>
  using rdiv_mult_rmod_eq [of k l] by (simp add: ac_simps)

lemma minus_rdiv_mult_eq_rmod:
  \<open>k - k rdiv l * l = k rmod l\<close>
  by (rule add_implies_diff [symmetric]) (fact rmod_rdiv_mult_eq)

lemma minus_mult_rdiv_eq_rmod:
  \<open>k - l * (k rdiv l) = k rmod l\<close>
  by (rule add_implies_diff [symmetric]) (fact rmod_mult_rdiv_eq)

lemma minus_rmod_eq_rdiv_mult:
  \<open>k - k rmod l = k rdiv l * l\<close>
  by (rule add_implies_diff [symmetric]) (fact rdiv_mult_rmod_eq)

lemma minus_rmod_eq_mult_rdiv:
  \<open>k - k rmod l = l * (k rdiv l)\<close>
  by (rule add_implies_diff [symmetric]) (fact mult_rdiv_rmod_eq)

lemma rdiv_0_eq [simp]:
  \<open>k rdiv 0 = 0\<close>
  by (simp add: rounded_divide_def)

lemma rmod_0_eq [simp]:
  \<open>k rmod 0 = k\<close>
  by (simp add: rounded_modulo_def)

lemma rdiv_1_eq [simp]:
  \<open>k rdiv 1 = k\<close>
  by (simp add: rounded_divide_def)

lemma rmod_1_eq [simp]:
  \<open>k rmod 1 = 0\<close>
  by (simp add: rounded_modulo_def)

lemma zero_rdiv_eq [simp]:
  \<open>0 rdiv k = 0\<close>
  by (auto simp add: rounded_divide_def not_less zdiv_eq_0_iff)

lemma zero_rmod_eq [simp]:
  \<open>0 rmod k = 0\<close>
  by (simp add: rounded_modulo_def)

lemma nonzero_mult_rdiv_cancel_right:
  \<open>k * l rdiv l = k\<close> if \<open>l \<noteq> 0\<close>
  using that by (auto simp add: rounded_divide_def ac_simps)

lemma rdiv_self_eq [simp]:
  \<open>k rdiv k = 1\<close> if \<open>k \<noteq> 0\<close>
  using that nonzero_mult_rdiv_cancel_right [of k 1] by simp

lemma rmod_self_eq [simp]:
  \<open>k rmod k = 0\<close>
  by (cases \<open>k = 0\<close>) (simp_all add: rounded_modulo_def)

end
