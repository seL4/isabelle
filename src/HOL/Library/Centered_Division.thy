(*  Author:  Florian Haftmann, TU Muenchen
*)

section \<open>Division with modulus centered towards zero.\<close>

theory Centered_Division
  imports Main
begin

lemma off_iff_abs_mod_2_eq_one:
  \<open>odd l \<longleftrightarrow> \<bar>l\<bar> mod 2 = 1\<close> for l :: int
  by (simp flip: odd_iff_mod_2_eq_one)

text \<open>
  \noindent The following specification of division on integers centers
  the modulus around zero.  This is useful e.g.~to define division
  on Gauss numbers.
  N.b.: This is not mentioned \cite{leijen01}.
\<close>

definition centered_divide :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>  (infixl \<open>cdiv\<close> 70)
  where \<open>k cdiv l = sgn l * ((k + \<bar>l\<bar> div 2) div \<bar>l\<bar>)\<close>

definition centered_modulo :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>  (infixl \<open>cmod\<close> 70)
  where \<open>k cmod l = (k + \<bar>l\<bar> div 2) mod \<bar>l\<bar> - \<bar>l\<bar> div 2\<close>

text \<open>
  \noindent Example: @{lemma \<open>k cmod 5 \<in> {-2, -1, 0, 1, 2}\<close> by (auto simp add: centered_modulo_def)}
\<close>

lemma signed_take_bit_eq_cmod:
  \<open>signed_take_bit n k = k cmod (2 ^ Suc n)\<close>
  by (simp only: centered_modulo_def power_abs abs_numeral flip: take_bit_eq_mod)
    (simp add: signed_take_bit_eq_take_bit_shift)

text \<open>
  \noindent Property @{thm signed_take_bit_eq_cmod [no_vars]} is the key to generalize
  centered division to arbitrary structures satisfying \<^class>\<open>ring_bit_operations\<close>,
  but so far it is not clear what practical relevance that would have.
\<close>

lemma cdiv_mult_cmod_eq:
  \<open>k cdiv l * l + k cmod l = k\<close>
proof -
  have *: \<open>l * (sgn l * j) = \<bar>l\<bar> * j\<close> for j
    by (simp add: ac_simps abs_sgn)
  show ?thesis
    by (simp add: centered_divide_def centered_modulo_def algebra_simps *)
qed

lemma mult_cdiv_cmod_eq:
  \<open>l * (k cdiv l) + k cmod l = k\<close>
  using cdiv_mult_cmod_eq [of k l] by (simp add: ac_simps)

lemma cmod_cdiv_mult_eq:
  \<open>k cmod l + k cdiv l * l = k\<close>
  using cdiv_mult_cmod_eq [of k l] by (simp add: ac_simps)

lemma cmod_mult_cdiv_eq:
  \<open>k cmod l + l * (k cdiv l) = k\<close>
  using cdiv_mult_cmod_eq [of k l] by (simp add: ac_simps)

lemma minus_cdiv_mult_eq_cmod:
  \<open>k - k cdiv l * l = k cmod l\<close>
  by (rule add_implies_diff [symmetric]) (fact cmod_cdiv_mult_eq)

lemma minus_mult_cdiv_eq_cmod:
  \<open>k - l * (k cdiv l) = k cmod l\<close>
  by (rule add_implies_diff [symmetric]) (fact cmod_mult_cdiv_eq)

lemma minus_cmod_eq_cdiv_mult:
  \<open>k - k cmod l = k cdiv l * l\<close>
  by (rule add_implies_diff [symmetric]) (fact cdiv_mult_cmod_eq)

lemma minus_cmod_eq_mult_cdiv:
  \<open>k - k cmod l = l * (k cdiv l)\<close>
  by (rule add_implies_diff [symmetric]) (fact mult_cdiv_cmod_eq)

lemma cdiv_0_eq [simp]:
  \<open>k cdiv 0 = 0\<close>
  by (simp add: centered_divide_def)

lemma cmod_0_eq [simp]:
  \<open>k cmod 0 = k\<close>
  by (simp add: centered_modulo_def)

lemma cdiv_1_eq [simp]:
  \<open>k cdiv 1 = k\<close>
  by (simp add: centered_divide_def)

lemma cmod_1_eq [simp]:
  \<open>k cmod 1 = 0\<close>
  by (simp add: centered_modulo_def)

lemma zero_cdiv_eq [simp]:
  \<open>0 cdiv k = 0\<close>
  by (auto simp add: centered_divide_def not_less zdiv_eq_0_iff)

lemma zero_cmod_eq [simp]:
  \<open>0 cmod k = 0\<close>
  by (auto simp add: centered_modulo_def not_less zmod_trivial_iff)

lemma cdiv_minus_eq:
  \<open>k cdiv - l = - (k cdiv l)\<close>
  by (simp add: centered_divide_def)

lemma cmod_minus_eq [simp]:
  \<open>k cmod - l = k cmod l\<close>
  by (simp add: centered_modulo_def)

lemma cdiv_abs_eq:
  \<open>k cdiv \<bar>l\<bar> = sgn l * (k cdiv l)\<close>
  by (simp add: centered_divide_def)

lemma cmod_abs_eq [simp]:
  \<open>k cmod \<bar>l\<bar> = k cmod l\<close>
  by (simp add: centered_modulo_def)

lemma nonzero_mult_cdiv_cancel_right:
  \<open>k * l cdiv l = k\<close> if \<open>l \<noteq> 0\<close>
proof -
  have \<open>sgn l * k * \<bar>l\<bar> cdiv l = k\<close>
    using that by (simp add: centered_divide_def)
  with that show ?thesis
    by (simp add: ac_simps abs_sgn)
qed

lemma cdiv_self_eq [simp]:
  \<open>k cdiv k = 1\<close> if \<open>k \<noteq> 0\<close>
  using that nonzero_mult_cdiv_cancel_right [of k 1] by simp

lemma cmod_self_eq [simp]:
  \<open>k cmod k = 0\<close>
proof -
  have \<open>(sgn k * \<bar>k\<bar> + \<bar>k\<bar> div 2) mod \<bar>k\<bar> = \<bar>k\<bar> div 2\<close>
    by (auto simp add: zmod_trivial_iff)
  also have \<open>sgn k * \<bar>k\<bar> = k\<close>
    by (simp add: abs_sgn)
  finally show ?thesis
    by (simp add: centered_modulo_def algebra_simps)
qed

lemma cmod_less_divisor:
  \<open>k cmod l < \<bar>l\<bar> - \<bar>l\<bar> div 2\<close> if \<open>l \<noteq> 0\<close>
  using that pos_mod_bound [of \<open>\<bar>l\<bar>\<close>] by (simp add: centered_modulo_def)

lemma cmod_less_equal_divisor:
  \<open>k cmod l \<le> \<bar>l\<bar> div 2\<close> if \<open>l \<noteq> 0\<close>
proof -
  from that cmod_less_divisor [of l k]
  have \<open>k cmod l < \<bar>l\<bar> - \<bar>l\<bar> div 2\<close>
    by simp
  also have \<open>\<bar>l\<bar> - \<bar>l\<bar> div 2 = \<bar>l\<bar> div 2 + of_bool (odd l)\<close>
    by auto
  finally show ?thesis
    by (cases \<open>even l\<close>) simp_all
qed

lemma divisor_less_equal_cmod':
  \<open>\<bar>l\<bar> div 2 - \<bar>l\<bar> \<le> k cmod l\<close> if \<open>l \<noteq> 0\<close>
proof -
  have \<open>0 \<le> (k + \<bar>l\<bar> div 2) mod \<bar>l\<bar>\<close>
    using that pos_mod_sign [of \<open>\<bar>l\<bar>\<close>] by simp
  then show ?thesis
    by (simp_all add: centered_modulo_def)
qed

lemma divisor_less_equal_cmod:
  \<open>- (\<bar>l\<bar> div 2) \<le> k cmod l\<close> if \<open>l \<noteq> 0\<close>
  using that divisor_less_equal_cmod' [of l k]
  by (simp add: centered_modulo_def)

lemma abs_cmod_less_equal:
  \<open>\<bar>k cmod l\<bar> \<le> \<bar>l\<bar> div 2\<close> if \<open>l \<noteq> 0\<close>
  using that divisor_less_equal_cmod [of l k]
  by (simp add: abs_le_iff cmod_less_equal_divisor)

end
