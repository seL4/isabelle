(*  Author:  Florian Haftmann, TU Muenchen
*)

subsection \<open>Rounded division: modulus centered towards zero.\<close>

theory Rounded_Division
  imports Main
begin

lemma off_iff_abs_mod_2_eq_one:
  \<open>odd l \<longleftrightarrow> \<bar>l\<bar> mod 2 = 1\<close> for l :: int
  by (simp flip: odd_iff_mod_2_eq_one)

definition rounded_divide :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>  (infixl \<open>rdiv\<close> 70)
  where \<open>k rdiv l = sgn l * ((k + \<bar>l\<bar> div 2) div \<bar>l\<bar>)\<close>

definition rounded_modulo :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>  (infixl \<open>rmod\<close> 70)
  where \<open>k rmod l = (k + \<bar>l\<bar> div 2) mod \<bar>l\<bar> - \<bar>l\<bar> div 2\<close>

lemma rdiv_mult_rmod_eq:
  \<open>k rdiv l * l + k rmod l = k\<close>
proof -
  have *: \<open>l * (sgn l * j) = \<bar>l\<bar> * j\<close> for j
    by (simp add: ac_simps abs_sgn)
  show ?thesis
    by (simp add: rounded_divide_def rounded_modulo_def algebra_simps *)
qed

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
  by (auto simp add: rounded_modulo_def not_less zmod_trivial_iff)

lemma rdiv_minus_eq:
  \<open>k rdiv - l = - (k rdiv l)\<close>
  by (simp add: rounded_divide_def)

lemma rmod_minus_eq [simp]:
  \<open>k rmod - l = k rmod l\<close>
  by (simp add: rounded_modulo_def)

lemma rdiv_abs_eq:
  \<open>k rdiv \<bar>l\<bar> = sgn l * (k rdiv l)\<close>
  by (simp add: rounded_divide_def)

lemma rmod_abs_eq [simp]:
  \<open>k rmod \<bar>l\<bar> = k rmod l\<close>
  by (simp add: rounded_modulo_def)

lemma nonzero_mult_rdiv_cancel_right:
  \<open>k * l rdiv l = k\<close> if \<open>l \<noteq> 0\<close>
proof -
  have \<open>sgn l * k * \<bar>l\<bar> rdiv l = k\<close>
    using that by (simp add: rounded_divide_def)
  with that show ?thesis
    by (simp add: ac_simps abs_sgn)
qed

lemma rdiv_self_eq [simp]:
  \<open>k rdiv k = 1\<close> if \<open>k \<noteq> 0\<close>
  using that nonzero_mult_rdiv_cancel_right [of k 1] by simp

lemma rmod_self_eq [simp]:
  \<open>k rmod k = 0\<close>
proof -
  have \<open>(sgn k * \<bar>k\<bar> + \<bar>k\<bar> div 2) mod \<bar>k\<bar> = \<bar>k\<bar> div 2\<close>
    by (auto simp add: zmod_trivial_iff)
  also have \<open>sgn k * \<bar>k\<bar> = k\<close>
    by (simp add: abs_sgn)
  finally show ?thesis
    by (simp add: rounded_modulo_def algebra_simps)
qed

lemma signed_take_bit_eq_rmod:
  \<open>signed_take_bit n k = k rmod (2 ^ Suc n)\<close>
  by (simp only: rounded_modulo_def power_abs abs_numeral flip: take_bit_eq_mod)
    (simp add: signed_take_bit_eq_take_bit_shift)

lemma rmod_less_divisor:
  \<open>k rmod l < \<bar>l\<bar> - \<bar>l\<bar> div 2\<close> if \<open>l \<noteq> 0\<close>
  using that pos_mod_bound [of \<open>\<bar>l\<bar>\<close>] by (simp add: rounded_modulo_def)

lemma rmod_less_equal_divisor:
  \<open>k rmod l \<le> \<bar>l\<bar> div 2\<close> if \<open>l \<noteq> 0\<close>
proof -
  from that rmod_less_divisor [of l k]
  have \<open>k rmod l < \<bar>l\<bar> - \<bar>l\<bar> div 2\<close>
    by simp
  also have \<open>\<bar>l\<bar> - \<bar>l\<bar> div 2 = \<bar>l\<bar> div 2 + of_bool (odd l)\<close>
    by auto
  finally show ?thesis
    by (cases \<open>even l\<close>) simp_all
qed

lemma divisor_less_equal_rmod':
  \<open>\<bar>l\<bar> div 2 - \<bar>l\<bar> \<le> k rmod l\<close> if \<open>l \<noteq> 0\<close>
proof -
  have \<open>0 \<le> (k + \<bar>l\<bar> div 2) mod \<bar>l\<bar>\<close>
    using that pos_mod_sign [of \<open>\<bar>l\<bar>\<close>] by simp
  then show ?thesis
    by (simp_all add: rounded_modulo_def)
qed

lemma divisor_less_equal_rmod:
  \<open>- (\<bar>l\<bar> div 2) \<le> k rmod l\<close> if \<open>l \<noteq> 0\<close>
  using that divisor_less_equal_rmod' [of l k]
  by (simp add: rounded_modulo_def)

lemma abs_rmod_less_equal:
  \<open>\<bar>k rmod l\<bar> \<le> \<bar>l\<bar> div 2\<close> if \<open>l \<noteq> 0\<close>
  using that divisor_less_equal_rmod [of l k]
  by (simp add: abs_le_iff rmod_less_equal_divisor)

end
