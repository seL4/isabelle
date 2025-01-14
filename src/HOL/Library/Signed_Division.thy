(*  Author:  Stefan Berghofer et al.
*)

section \<open>Signed division: negative results rounded towards zero rather than minus infinity.\<close>

theory Signed_Division
  imports Main
begin

class signed_divide =
  fixes signed_divide :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl \<open>sdiv\<close> 70)

class signed_modulo =
  fixes signed_modulo :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixl \<open>smod\<close> 70)

class signed_division = comm_semiring_1_cancel + signed_divide + signed_modulo +
  assumes sdiv_mult_smod_eq: \<open>a sdiv b * b + a smod b = a\<close>
begin

lemma mult_sdiv_smod_eq:
  \<open>b * (a sdiv b) + a smod b = a\<close>
  using sdiv_mult_smod_eq [of a b] by (simp add: ac_simps)

lemma smod_sdiv_mult_eq:
  \<open>a smod b + a sdiv b * b = a\<close>
  using sdiv_mult_smod_eq [of a b] by (simp add: ac_simps)

lemma smod_mult_sdiv_eq:
  \<open>a smod b + b * (a sdiv b) = a\<close>
  using sdiv_mult_smod_eq [of a b] by (simp add: ac_simps)

lemma minus_sdiv_mult_eq_smod:
  \<open>a - a sdiv b * b = a smod b\<close>
  by (rule add_implies_diff [symmetric]) (fact smod_sdiv_mult_eq)

lemma minus_mult_sdiv_eq_smod:
  \<open>a - b * (a sdiv b) = a smod b\<close>
  by (rule add_implies_diff [symmetric]) (fact smod_mult_sdiv_eq)

lemma minus_smod_eq_sdiv_mult:
  \<open>a - a smod b = a sdiv b * b\<close>
  by (rule add_implies_diff [symmetric]) (fact sdiv_mult_smod_eq)

lemma minus_smod_eq_mult_sdiv:
  \<open>a - a smod b = b * (a sdiv b)\<close>
  by (rule add_implies_diff [symmetric]) (fact mult_sdiv_smod_eq)

end

text \<open>
  \noindent The following specification of division is named ``T-division'' in \<^cite>\<open>"leijen01"\<close>.
  It is motivated by ISO C99, which in turn adopted the typical behavior of
  hardware modern in the beginning of the 1990ies; but note ISO C99 describes
  the instance on machine words, not mathematical integers.
\<close>

instantiation int :: signed_division
begin

definition signed_divide_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>k sdiv l = sgn k * sgn l * (\<bar>k\<bar> div \<bar>l\<bar>)\<close> for k l :: int

definition signed_modulo_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>k smod l = sgn k * (\<bar>k\<bar> mod \<bar>l\<bar>)\<close> for k l :: int

instance by standard
  (simp add: signed_divide_int_def signed_modulo_int_def div_abs_eq mod_abs_eq algebra_simps)

end

lemma divide_int_eq_signed_divide_int:
  \<open>k div l = k sdiv l - of_bool (l \<noteq> 0 \<and> sgn k \<noteq> sgn l \<and> \<not> l dvd k)\<close>
  for k l :: int
  by (simp add: div_eq_div_abs [of k l] signed_divide_int_def)

lemma signed_divide_int_eq_divide_int:
  \<open>k sdiv l = k div l + of_bool (l \<noteq> 0 \<and> sgn k \<noteq> sgn l \<and> \<not> l dvd k)\<close>
  for k l :: int
  by (simp add: divide_int_eq_signed_divide_int)

lemma modulo_int_eq_signed_modulo_int:
  \<open>k mod l = k smod l + l * of_bool (sgn k \<noteq> sgn l \<and> \<not> l dvd k)\<close>
  for k l :: int
  by (simp add: mod_eq_mod_abs [of k l] signed_modulo_int_def)

lemma signed_modulo_int_eq_modulo_int:
  \<open>k smod l = k mod l - l * of_bool (sgn k \<noteq> sgn l \<and> \<not> l dvd k)\<close>
  for k l :: int
  by (simp add: modulo_int_eq_signed_modulo_int)

lemma sdiv_int_div_0:
  "(x :: int) sdiv 0 = 0"
  by (clarsimp simp: signed_divide_int_def)

lemma sdiv_int_0_div [simp]:
  "0 sdiv (x :: int) = 0"
  by (clarsimp simp: signed_divide_int_def)

lemma smod_int_alt_def:
     "(a::int) smod b = sgn (a) * (abs a mod abs b)"
  by (fact signed_modulo_int_def)

lemma int_sdiv_simps [simp]:
    "(a :: int) sdiv 1 = a"
    "(a :: int) sdiv 0 = 0"
    "(a :: int) sdiv -1 = -a"
  by (auto simp: signed_divide_int_def sgn_if)

lemma smod_int_mod_0 [simp]:
  "x smod (0 :: int) = x"
  by (clarsimp simp: signed_modulo_int_def abs_mult_sgn ac_simps)

lemma smod_int_0_mod [simp]:
  "0 smod (x :: int) = 0"
  by (clarsimp simp: smod_int_alt_def)

lemma sgn_sdiv_eq_sgn_mult:
  "a sdiv b \<noteq> 0 \<Longrightarrow> sgn ((a :: int) sdiv b) = sgn (a * b)"
  by (auto simp: signed_divide_int_def sgn_div_eq_sgn_mult sgn_mult)

lemma int_sdiv_same_is_1 [simp]:
  assumes "a \<noteq> 0"
  shows  "((a :: int) sdiv b = a) = (b = 1)"
proof -
  have "b = 1" if "a sdiv b = a"
  proof -
    have "b>0"
      by (smt (verit, ccfv_threshold) assms mult_cancel_left2 sgn_if sgn_mult
          sgn_sdiv_eq_sgn_mult that)
    then show ?thesis
      by (smt (verit) assms dvd_eq_mod_eq_0 int_div_less_self of_bool_eq(1,2) sgn_if
          signed_divide_int_eq_divide_int that zdiv_zminus1_eq_if)
  qed
  then show ?thesis
    by auto
qed

lemma int_sdiv_negated_is_minus1 [simp]:
    "a \<noteq> 0 \<Longrightarrow> ((a :: int) sdiv b = - a) = (b = -1)"
  using int_sdiv_same_is_1 [of _ "-b"]
  using signed_divide_int_def by fastforce

lemma sdiv_int_range:
  \<open>a sdiv b \<in> {- \<bar>a\<bar>..\<bar>a\<bar>}\<close> for a b :: int
  using zdiv_mono2 [of \<open>\<bar>a\<bar>\<close> 1 \<open>\<bar>b\<bar>\<close>]
  by (cases \<open>b = 0\<close>; cases \<open>sgn b = sgn a\<close>)
     (auto simp add: signed_divide_int_def pos_imp_zdiv_nonneg_iff
     dest!: sgn_not_eq_imp intro: order_trans [of _ 0])

lemma smod_int_range:
  \<open>a smod b \<in> {- \<bar>b\<bar> + 1..\<bar>b\<bar> - 1}\<close>
  if \<open>b \<noteq> 0\<close> for a b :: int
proof -
  define m n where \<open>m = nat \<bar>a\<bar>\<close> \<open>n = nat \<bar>b\<bar>\<close>
  then have \<open>\<bar>a\<bar> = int m\<close> \<open>\<bar>b\<bar> = int n\<close>
    by simp_all
  with that have \<open>n > 0\<close>
    by simp
  with signed_modulo_int_def [of a b] \<open>\<bar>a\<bar> = int m\<close> \<open>\<bar>b\<bar> = int n\<close>
  show ?thesis
    by (auto simp add: sgn_if diff_le_eq int_one_le_iff_zero_less simp flip: of_nat_mod of_nat_diff)
qed

lemma smod_int_compares:
   "\<lbrakk> 0 \<le> a; 0 < b \<rbrakk> \<Longrightarrow> (a :: int) smod b < b"
   "\<lbrakk> 0 \<le> a; 0 < b \<rbrakk> \<Longrightarrow> 0 \<le> (a :: int) smod b"
   "\<lbrakk> a \<le> 0; 0 < b \<rbrakk> \<Longrightarrow> -b < (a :: int) smod b"
   "\<lbrakk> a \<le> 0; 0 < b \<rbrakk> \<Longrightarrow> (a :: int) smod b \<le> 0"
   "\<lbrakk> 0 \<le> a; b < 0 \<rbrakk> \<Longrightarrow> (a :: int) smod b < - b"
   "\<lbrakk> 0 \<le> a; b < 0 \<rbrakk> \<Longrightarrow> 0 \<le> (a :: int) smod b"
   "\<lbrakk> a \<le> 0; b < 0 \<rbrakk> \<Longrightarrow> (a :: int) smod b \<le> 0"
   "\<lbrakk> a \<le> 0; b < 0 \<rbrakk> \<Longrightarrow> b \<le> (a :: int) smod b"
  using smod_int_range [where a=a and b=b]
  by (auto simp: add1_zle_eq smod_int_alt_def sgn_if)

lemma smod_mod_positive:
    "\<lbrakk> 0 \<le> (a :: int); 0 \<le> b \<rbrakk> \<Longrightarrow> a smod b = a mod b"
  by (clarsimp simp: smod_int_alt_def zsgn_def)

lemma minus_sdiv_eq [simp]:
  \<open>- k sdiv l = - (k sdiv l)\<close> for k l :: int
  by (simp add: signed_divide_int_def)

lemma sdiv_minus_eq [simp]:
  \<open>k sdiv - l = - (k sdiv l)\<close> for k l :: int
  by (simp add: signed_divide_int_def)

lemma sdiv_int_numeral_numeral [simp]:
  \<open>numeral m sdiv numeral n = numeral m div (numeral n :: int)\<close>
  by (simp add: signed_divide_int_def)

lemma minus_smod_eq [simp]:
  \<open>- k smod l = - (k smod l)\<close> for k l :: int
  by (simp add: smod_int_alt_def)

lemma smod_minus_eq [simp]:
  \<open>k smod - l = k smod l\<close> for k l :: int
  by (simp add: smod_int_alt_def)

lemma smod_int_numeral_numeral [simp]:
  \<open>numeral m smod numeral n = numeral m mod (numeral n :: int)\<close>
  by (simp add: smod_int_alt_def) 

end
