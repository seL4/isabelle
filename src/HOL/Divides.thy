(*  Title:      HOL/Divides.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

section \<open>More on quotient and remainder\<close>

theory Divides
imports Parity
begin

subsection \<open>More on division\<close>

subsubsection \<open>Monotonicity in the First Argument (Dividend)\<close>

lemma unique_quotient_lemma:
  assumes "b * q' + r' \<le> b * q + r" "0 \<le> r'" "r' < b" "r < b" shows "q' \<le> (q::int)"
proof -
  have "r' + b * (q'-q) \<le> r"
    using assms by (simp add: right_diff_distrib)
  moreover have "0 < b * (1 + q - q') "
    using assms by (simp add: right_diff_distrib distrib_left)
  moreover have "b * q' < b * (1 + q)"
    using assms by (simp add: right_diff_distrib distrib_left)
  ultimately show ?thesis
    using assms by (simp add: mult_less_cancel_left)
qed

lemma unique_quotient_lemma_neg:
  "b * q' + r' \<le> b*q + r \<Longrightarrow> r \<le> 0 \<Longrightarrow> b < r \<Longrightarrow> b < r' \<Longrightarrow> q \<le> (q'::int)"
  using unique_quotient_lemma[where b = "-b" and r = "-r'" and r'="-r"] by auto

lemma zdiv_mono1:
  \<open>a div b \<le> a' div b\<close>
  if \<open>a \<le> a'\<close> \<open>0 < b\<close>
  for a b b' :: int
proof (rule unique_quotient_lemma)
  show "b * (a div b) + a mod b \<le> b * (a' div b) + a' mod b"
    using \<open>a \<le> a'\<close> by auto
qed (use that in auto)

lemma zdiv_mono1_neg:
  fixes b::int
  assumes "a \<le> a'" "b < 0" shows "a' div b \<le> a div b"
proof (rule unique_quotient_lemma_neg)
  show "b * (a div b) + a mod b \<le> b * (a' div b) + a' mod b"
    using assms(1) by auto
qed (use assms in auto)


subsubsection \<open>Monotonicity in the Second Argument (Divisor)\<close>

lemma q_pos_lemma:
  fixes q'::int
  assumes "0 \<le> b'*q' + r'" "r' < b'" "0 < b'"
  shows "0 \<le> q'"
proof -
  have "0 < b'* (q' + 1)"
    using assms by (simp add: distrib_left)
  with assms show ?thesis
    by (simp add: zero_less_mult_iff)
qed

lemma zdiv_mono2_lemma:
  fixes q'::int
  assumes eq: "b*q + r = b'*q' + r'" and le: "0 \<le> b'*q' + r'" and "r' < b'" "0 \<le> r" "0 < b'" "b' \<le> b"
  shows "q \<le> q'"
proof -
  have "0 \<le> q'"
    using q_pos_lemma le \<open>r' < b'\<close> \<open>0 < b'\<close> by blast
  moreover have "b*q = r' - r + b'*q'"
    using eq by linarith
  ultimately have "b*q < b* (q' + 1)"
    using mult_right_mono assms unfolding distrib_left by fastforce
  with assms show ?thesis
    by (simp add: mult_less_cancel_left_pos)
qed

lemma zdiv_mono2:
  fixes a::int
  assumes "0 \<le> a" "0 < b'" "b' \<le> b" shows "a div b \<le> a div b'"
proof (rule zdiv_mono2_lemma)
  have "b \<noteq> 0"
    using assms by linarith
  show "b * (a div b) + a mod b = b' * (a div b') + a mod b'"
    by simp
qed (use assms in auto)

lemma zdiv_mono2_neg_lemma:
    fixes q'::int
    assumes "b*q + r = b'*q' + r'" "b'*q' + r' < 0" "r < b" "0 \<le> r'" "0 < b'" "b' \<le> b"
    shows "q' \<le> q"
proof -
  have "b'*q' < 0"
    using assms by linarith
  with assms have "q' \<le> 0"
    by (simp add: mult_less_0_iff)
  have "b*q' \<le> b'*q'"
    by (simp add: \<open>q' \<le> 0\<close> assms(6) mult_right_mono_neg)
  then have "b*q' < b* (q + 1)"
    using assms by (simp add: distrib_left)
  then show ?thesis
    using assms by (simp add: mult_less_cancel_left)
qed

lemma zdiv_mono2_neg:
  fixes a::int
  assumes "a < 0" "0 < b'" "b' \<le> b" shows "a div b' \<le> a div b"
proof (rule zdiv_mono2_neg_lemma)
  have "b \<noteq> 0"
    using assms by linarith
  show "b * (a div b) + a mod b = b' * (a div b') + a mod b'"
    by simp
qed (use assms in auto)


subsubsection \<open>Quotients of Signs\<close>

lemma div_eq_minus1: "0 < b \<Longrightarrow> - 1 div b = - 1" for b :: int
  by (simp add: divide_int_def)

lemma zmod_minus1: "0 < b \<Longrightarrow> - 1 mod b = b - 1" for b :: int
  by (auto simp add: modulo_int_def)

lemma minus_mod_int_eq:
  \<open>- k mod l = l - 1 - (k - 1) mod l\<close> if \<open>l \<ge> 0\<close> for k l :: int
proof (cases \<open>l = 0\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  with that have \<open>l > 0\<close>
    by simp
  then show ?thesis
  proof (cases \<open>l dvd k\<close>)
    case True
    then obtain j where \<open>k = l * j\<close> ..
    moreover have \<open>(l * j mod l - 1) mod l = l - 1\<close>
      using \<open>l > 0\<close> by (simp add: zmod_minus1)
    then have \<open>(l * j - 1) mod l = l - 1\<close>
      by (simp only: mod_simps)
    ultimately show ?thesis
      by simp
  next
    case False
    moreover have 1: \<open>0 < k mod l\<close>
      using \<open>0 < l\<close> False le_less by fastforce
    moreover have 2: \<open>k mod l < 1 + l\<close>
      using \<open>0 < l\<close> pos_mod_bound[of l k] by linarith
    from 1 2 \<open>l > 0\<close> have \<open>(k mod l - 1) mod l = k mod l - 1\<close>
      by (simp add: zmod_trivial_iff)
    ultimately show ?thesis
      by (simp only: zmod_zminus1_eq_if)
         (simp add: mod_eq_0_iff_dvd algebra_simps mod_simps)
  qed
qed

lemma div_neg_pos_less0:
  fixes a::int
  assumes "a < 0" "0 < b" 
  shows "a div b < 0"
proof -
  have "a div b \<le> - 1 div b"
    using zdiv_mono1 assms by auto
  also have "... \<le> -1"
    by (simp add: assms(2) div_eq_minus1)
  finally show ?thesis 
    by force
qed

lemma div_nonneg_neg_le0: "[| (0::int) \<le> a; b < 0 |] ==> a div b \<le> 0"
  by (drule zdiv_mono1_neg, auto)

lemma div_nonpos_pos_le0: "[| (a::int) \<le> 0; b > 0 |] ==> a div b \<le> 0"
  by (drule zdiv_mono1, auto)

text\<open>Now for some equivalences of the form \<open>a div b >=< 0 \<longleftrightarrow> \<dots>\<close>
conditional upon the sign of \<open>a\<close> or \<open>b\<close>. There are many more.
They should all be simp rules unless that causes too much search.\<close>

lemma pos_imp_zdiv_nonneg_iff:
      fixes a::int
      assumes "0 < b" 
      shows "(0 \<le> a div b) = (0 \<le> a)"
proof
  show "0 \<le> a div b \<Longrightarrow> 0 \<le> a"
    using assms
    by (simp add: linorder_not_less [symmetric]) (blast intro: div_neg_pos_less0)
next
  assume "0 \<le> a"
  then have "0 div b \<le> a div b"
    using zdiv_mono1 assms by blast
  then show "0 \<le> a div b"
    by auto
qed

lemma pos_imp_zdiv_pos_iff:
  "0<k \<Longrightarrow> 0 < (i::int) div k \<longleftrightarrow> k \<le> i"
  using pos_imp_zdiv_nonneg_iff[of k i] zdiv_eq_0_iff[of i k] by arith

lemma neg_imp_zdiv_nonneg_iff:
  fixes a::int
  assumes "b < 0" 
  shows "(0 \<le> a div b) = (a \<le> 0)"
  using assms by (simp add: div_minus_minus [of a, symmetric] pos_imp_zdiv_nonneg_iff del: div_minus_minus)

(*But not (a div b \<le> 0 iff a\<le>0); consider a=1, b=2 when a div b = 0.*)
lemma pos_imp_zdiv_neg_iff: "(0::int) < b ==> (a div b < 0) = (a < 0)"
  by (simp add: linorder_not_le [symmetric] pos_imp_zdiv_nonneg_iff)

(*Again the law fails for \<le>: consider a = -1, b = -2 when a div b = 0*)
lemma neg_imp_zdiv_neg_iff: "b < (0::int) ==> (a div b < 0) = (0 < a)"
  by (simp add: linorder_not_le [symmetric] neg_imp_zdiv_nonneg_iff)

lemma nonneg1_imp_zdiv_pos_iff:
  fixes a::int
  assumes "0 \<le> a" 
  shows "a div b > 0 \<longleftrightarrow> a \<ge> b \<and> b>0"
proof -
  have "0 < a div b \<Longrightarrow> b \<le> a"
    using div_pos_pos_trivial[of a b] assms by arith
  moreover have "0 < a div b \<Longrightarrow> b > 0"
    using assms div_nonneg_neg_le0[of a b]  by(cases "b=0"; force)
  moreover have "b \<le> a \<and> 0 < b \<Longrightarrow> 0 < a div b"
    using int_one_le_iff_zero_less[of "a div b"] zdiv_mono1[of b a b] by simp
  ultimately show ?thesis
    by blast
qed

lemma zmod_le_nonneg_dividend: "(m::int) \<ge> 0 \<Longrightarrow> m mod k \<le> m"
  by (rule split_zmod[THEN iffD2]) (fastforce dest: q_pos_lemma intro: split_mult_pos_le)

lemma sgn_div_eq_sgn_mult:
  \<open>sgn (k div l) = of_bool (k div l \<noteq> 0) * sgn (k * l)\<close>
  for k l :: int
proof (cases \<open>k div l = 0\<close>)
  case True
  then show ?thesis
    by simp
next
  case False
  have \<open>0 \<le> \<bar>k\<bar> div \<bar>l\<bar>\<close>
    by (cases \<open>l = 0\<close>) (simp_all add: pos_imp_zdiv_nonneg_iff)
  then have \<open>\<bar>k\<bar> div \<bar>l\<bar> \<noteq> 0 \<longleftrightarrow> 0 < \<bar>k\<bar> div \<bar>l\<bar>\<close>
    by (simp add: less_le)
  also have \<open>\<dots> \<longleftrightarrow> \<bar>k\<bar> \<ge> \<bar>l\<bar>\<close>
    using False nonneg1_imp_zdiv_pos_iff by auto
  finally have *: \<open>\<bar>k\<bar> div \<bar>l\<bar> \<noteq> 0 \<longleftrightarrow> \<bar>l\<bar> \<le> \<bar>k\<bar>\<close> .
  show ?thesis
    using \<open>0 \<le> \<bar>k\<bar> div \<bar>l\<bar>\<close> False
  by (auto simp add: div_eq_div_abs [of k l] div_eq_sgn_abs [of k l]
    sgn_mult sgn_1_pos sgn_1_neg sgn_eq_0_iff nonneg1_imp_zdiv_pos_iff * dest: sgn_not_eq_imp)
qed

lemma
  fixes a b q r :: int
  assumes \<open>a = b * q + r\<close> \<open>0 \<le> r\<close> \<open>r < b\<close>
  shows int_div_pos_eq:
      \<open>a div b = q\<close> (is ?Q)
    and int_mod_pos_eq:
      \<open>a mod b = r\<close> (is ?R)
proof -
  from assms have \<open>(a div b, a mod b) = (q, r)\<close>
    by (cases b q r a rule: euclidean_relationI)
      (auto simp add: division_segment_int_def ac_simps dvd_add_left_iff dest: zdvd_imp_le)
  then show ?Q and ?R
    by simp_all
qed

lemma int_div_neg_eq:
  \<open>a div b = q\<close> if \<open>a = b * q + r\<close> \<open>r \<le> 0\<close> \<open>b < r\<close> for a b q r :: int
  using that int_div_pos_eq [of a \<open>- b\<close> \<open>- q\<close> \<open>- r\<close>] by simp_all

lemma int_mod_neg_eq:
  \<open>a mod b = r\<close> if \<open>a = b * q + r\<close> \<open>r \<le> 0\<close> \<open>b < r\<close> for a b q r :: int
  using that int_div_neg_eq [of a b q r] by simp


subsubsection \<open>Further properties\<close>

lemma div_int_pos_iff:
  "k div l \<ge> 0 \<longleftrightarrow> k = 0 \<or> l = 0 \<or> k \<ge> 0 \<and> l \<ge> 0
    \<or> k < 0 \<and> l < 0"
  for k l :: int
proof (cases "k = 0 \<or> l = 0")
  case False
  then have *: "k \<noteq> 0" "l \<noteq> 0"
    by auto
  then have "0 \<le> k div l \<Longrightarrow> \<not> k < 0 \<Longrightarrow> 0 \<le> l"
    by (meson neg_imp_zdiv_neg_iff not_le not_less_iff_gr_or_eq)
  then show ?thesis
   using * by (auto simp add: pos_imp_zdiv_nonneg_iff neg_imp_zdiv_nonneg_iff)
qed auto

lemma mod_int_pos_iff:
  "k mod l \<ge> 0 \<longleftrightarrow> l dvd k \<or> l = 0 \<and> k \<ge> 0 \<or> l > 0"
  for k l :: int
proof (cases "l > 0")
  case False
  then show ?thesis 
    by (simp add: dvd_eq_mod_eq_0) (use neg_mod_sign [of l k] in \<open>auto simp add: le_less not_less\<close>)
qed auto

text \<open>Simplify expressions in which div and mod combine numerical constants\<close>

lemma abs_div: "(y::int) dvd x \<Longrightarrow> \<bar>x div y\<bar> = \<bar>x\<bar> div \<bar>y\<bar>"
  unfolding dvd_def by (cases "y=0") (auto simp add: abs_mult)

text\<open>Suggested by Matthias Daum\<close>
lemma int_power_div_base:
  fixes k :: int
  assumes "0 < m" "0 < k"
  shows "k ^ m div k = (k::int) ^ (m - Suc 0)"
proof -
  have eq: "k ^ m = k ^ ((m - Suc 0) + Suc 0)"
    by (simp add: assms)
  show ?thesis
    using assms by (simp only: power_add eq) auto
qed

text\<open>Suggested by Matthias Daum\<close>
lemma int_div_less_self:
  fixes x::int
  assumes "0 < x" "1 < k"
  shows  "x div k < x"
proof -
  have "nat x div nat k < nat x"
    by (simp add: assms)
  with assms show ?thesis
    by (simp add: nat_div_distrib [symmetric])
qed

lemma mod_eq_dvd_iff_nat:
  "m mod q = n mod q \<longleftrightarrow> q dvd m - n" if "m \<ge> n" for m n q :: nat
proof -
  have "int m mod int q = int n mod int q \<longleftrightarrow> int q dvd int m - int n"
    by (simp add: mod_eq_dvd_iff)
  with that have "int (m mod q) = int (n mod q) \<longleftrightarrow> int q dvd int (m - n)"
    by (simp only: of_nat_mod of_nat_diff)
  then show ?thesis
    by simp
qed

lemma mod_eq_nat1E:
  fixes m n q :: nat
  assumes "m mod q = n mod q" and "m \<ge> n"
  obtains s where "m = n + q * s"
proof -
  from assms have "q dvd m - n"
    by (simp add: mod_eq_dvd_iff_nat)
  then obtain s where "m - n = q * s" ..
  with \<open>m \<ge> n\<close> have "m = n + q * s"
    by simp
  with that show thesis .
qed

lemma mod_eq_nat2E:
  fixes m n q :: nat
  assumes "m mod q = n mod q" and "n \<ge> m"
  obtains s where "n = m + q * s"
  using assms mod_eq_nat1E [of n q m] by (auto simp add: ac_simps)

lemma nat_mod_eq_lemma:
  assumes "(x::nat) mod n = y mod n" and "y \<le> x"
  shows "\<exists>q. x = y + n * q"
  using assms by (rule mod_eq_nat1E) (rule exI)

lemma nat_mod_eq_iff: "(x::nat) mod n = y mod n \<longleftrightarrow> (\<exists>q1 q2. x + n * q1 = y + n * q2)"
  (is "?lhs = ?rhs")
proof
  assume H: "x mod n = y mod n"
  {assume xy: "x \<le> y"
    from H have th: "y mod n = x mod n" by simp
    from nat_mod_eq_lemma[OF th xy] have ?rhs
    proof
      fix q
      assume "y = x + n * q"
      then have "x + n * q = y + n * 0"
        by simp
      then show "\<exists>q1 q2. x + n * q1 = y + n * q2"
        by blast
    qed}
  moreover
  {assume xy: "y \<le> x"
    from nat_mod_eq_lemma[OF H xy] have ?rhs
    proof
      fix q
      assume "x = y + n * q"
      then have "x + n * 0 = y + n * q"
        by simp
      then show "\<exists>q1 q2. x + n * q1 = y + n * q2"
        by blast
    qed}
  ultimately  show ?rhs using linear[of x y] by blast
next
  assume ?rhs then obtain q1 q2 where q12: "x + n * q1 = y + n * q2" by blast
  hence "(x + n * q1) mod n = (y + n * q2) mod n" by simp
  thus  ?lhs by simp
qed


subsubsection \<open>Uniqueness rules\<close>

lemma euclidean_relation_intI [case_names by0 divides euclidean_relation]:
  \<open>(k div l, k mod l) = (q, r)\<close>
    if by0': \<open>l = 0 \<Longrightarrow> q = 0 \<and> r = k\<close>
    and divides': \<open>l \<noteq> 0 \<Longrightarrow> l dvd k \<Longrightarrow> r = 0 \<and> k = q * l\<close>
    and euclidean_relation': \<open>l \<noteq> 0 \<Longrightarrow> \<not> l dvd k \<Longrightarrow> sgn r = sgn l
      \<and> \<bar>r\<bar> < \<bar>l\<bar> \<and> k = q * l + r\<close> for k l :: int
proof (cases l q r k rule: euclidean_relationI)
  case by0
  then show ?case
    by (rule by0')
next
  case divides
  then show ?case
    by (rule divides')
next
  case euclidean_relation
  with euclidean_relation' have \<open>sgn r = sgn l\<close> \<open>\<bar>r\<bar> < \<bar>l\<bar>\<close> \<open>k = q * l + r\<close>
    by simp_all
  from \<open>sgn r = sgn l\<close> \<open>l \<noteq> 0\<close> have \<open>division_segment r = division_segment l\<close>
    by (simp add: division_segment_int_def sgn_if split: if_splits)
  with \<open>\<bar>r\<bar> < \<bar>l\<bar>\<close> \<open>k = q * l + r\<close>
  show ?case
    by simp
qed


subsubsection \<open>Computing \<open>div\<close> and \<open>mod\<close> with shifting\<close>

lemma div_pos_geq:
  fixes k l :: int
  assumes "0 < l" and "l \<le> k"
  shows "k div l = (k - l) div l + 1"
proof -
  have "k = (k - l) + l" by simp
  then obtain j where k: "k = j + l" ..
  with assms show ?thesis by (simp add: div_add_self2)
qed

lemma mod_pos_geq:
  fixes k l :: int
  assumes "0 < l" and "l \<le> k"
  shows "k mod l = (k - l) mod l"
proof -
  have "k = (k - l) + l" by simp
  then obtain j where k: "k = j + l" ..
  with assms show ?thesis by simp
qed

text\<open>computing div by shifting\<close>

lemma pos_zdiv_mult_2: \<open>(1 + 2 * b) div (2 * a) = b div a\<close> (is ?Q)
  and pos_zmod_mult_2: \<open>(1 + 2 * b) mod (2 * a) = 1 + 2 * (b mod a)\<close> (is ?R)
  if \<open>0 \<le> a\<close> for a b :: int
proof -
  have \<open>((1 + 2 * b) div (2 * a), (1 + 2 * b) mod (2 * a)) = (b div a, 1 + 2 * (b mod a))\<close>
  proof (cases \<open>2 * a\<close> \<open>b div a\<close> \<open>1 + 2 * (b mod a)\<close> \<open>1 + 2 * b\<close> rule: euclidean_relation_intI)
    case by0
    then show ?case
      by simp
  next
    case divides
    have \<open>even (2 * a)\<close>
      by simp
    then have \<open>even (1 + 2 * b)\<close>
      using \<open>2 * a dvd 1 + 2 * b\<close> by (rule dvd_trans)
    then show ?case
      by simp
  next
    case euclidean_relation
    with that have \<open>a > 0\<close>
      by simp
    moreover have \<open>b mod a < a\<close>
      using \<open>a > 0\<close> by simp
    then have \<open>1 + 2 * (b mod a) < 2 * a\<close>
      by simp
    moreover have \<open>2 * (b mod a) + a * (2 * (b div a)) = 2 * (b div a * a + b mod a)\<close>
      by (simp only: algebra_simps)
    moreover have \<open>0 \<le> 2 * (b mod a)\<close>
      using \<open>a > 0\<close> by simp
    ultimately show ?case
      by (simp add: algebra_simps)
  qed
  then show ?Q and ?R
    by simp_all
qed

lemma neg_zdiv_mult_2: \<open>(1 + 2 * b) div (2 * a) = (b + 1) div a\<close> (is ?Q)
  and neg_zmod_mult_2: \<open>(1 + 2 * b) mod (2 * a) = 2 * ((b + 1) mod a) - 1\<close> (is ?R)
  if \<open>a \<le> 0\<close> for a b :: int
proof -
  have \<open>((1 + 2 * b) div (2 * a), (1 + 2 * b) mod (2 * a)) = ((b + 1) div a, 2 * ((b + 1) mod a) - 1)\<close>
  proof (cases \<open>2 * a\<close> \<open>(b + 1) div a\<close> \<open>2 * ((b + 1) mod a) - 1\<close> \<open>1 + 2 * b\<close> rule: euclidean_relation_intI)
    case by0
    then show ?case
      by simp
  next
    case divides
    have \<open>even (2 * a)\<close>
      by simp
    then have \<open>even (1 + 2 * b)\<close>
      using \<open>2 * a dvd 1 + 2 * b\<close> by (rule dvd_trans)
    then show ?case
      by simp
  next
    case euclidean_relation
    with that have \<open>a < 0\<close>
      by simp
    moreover have \<open>(b + 1) mod a > a\<close>
      using \<open>a < 0\<close> by simp
    then have \<open>2 * ((b + 1) mod a) > 1 + 2 * a\<close>
      by simp
    moreover have \<open>((1 + b) mod a) \<le> 0\<close>
      using \<open>a < 0\<close> by simp
    then have \<open>2 * ((1 + b) mod a) \<le> 0\<close>
      by simp
    moreover have \<open>2 * ((1 + b) mod a) + a * (2 * ((1 + b) div a)) =
      2 * ((1 + b) div a * a + (1 + b) mod a)\<close>
      by (simp only: algebra_simps)
    ultimately show ?case
      by (simp add: algebra_simps sgn_mult abs_mult)
  qed
  then show ?Q and ?R
    by simp_all
qed

lemma zdiv_numeral_Bit0 [simp]:
  "numeral (Num.Bit0 v) div numeral (Num.Bit0 w) =
    numeral v div (numeral w :: int)"
  unfolding numeral.simps unfolding mult_2 [symmetric]
  by (rule div_mult_mult1, simp)

lemma zdiv_numeral_Bit1 [simp]:
  "numeral (Num.Bit1 v) div numeral (Num.Bit0 w) =
    (numeral v div (numeral w :: int))"
  unfolding numeral.simps
  unfolding mult_2 [symmetric] add.commute [of _ 1]
  by (rule pos_zdiv_mult_2, simp)

lemma zmod_numeral_Bit0 [simp]:
  "numeral (Num.Bit0 v) mod numeral (Num.Bit0 w) =
    (2::int) * (numeral v mod numeral w)"
  unfolding numeral_Bit0 [of v] numeral_Bit0 [of w]
  unfolding mult_2 [symmetric] by (rule mod_mult_mult1)

lemma zmod_numeral_Bit1 [simp]:
  "numeral (Num.Bit1 v) mod numeral (Num.Bit0 w) =
    2 * (numeral v mod numeral w) + (1::int)"
  unfolding numeral_Bit1 [of v] numeral_Bit0 [of w]
  unfolding mult_2 [symmetric] add.commute [of _ 1]
  by (rule pos_zmod_mult_2, simp)

  
code_identifier
  code_module Divides \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith


subsection \<open>Lemmas of doubtful value\<close>

class unique_euclidean_semiring_numeral = unique_euclidean_semiring_with_nat + linordered_semidom +
  assumes div_less: "0 \<le> a \<Longrightarrow> a < b \<Longrightarrow> a div b = 0"
    and mod_less: " 0 \<le> a \<Longrightarrow> a < b \<Longrightarrow> a mod b = a"
    and div_positive: "0 < b \<Longrightarrow> b \<le> a \<Longrightarrow> a div b > 0"
    and mod_less_eq_dividend: "0 \<le> a \<Longrightarrow> a mod b \<le> a"
    and pos_mod_bound: "0 < b \<Longrightarrow> a mod b < b"
    and pos_mod_sign: "0 < b \<Longrightarrow> 0 \<le> a mod b"
    and mod_mult2_eq: "0 \<le> c \<Longrightarrow> a mod (b * c) = b * (a div b mod c) + a mod b"
    and div_mult2_eq: "0 \<le> c \<Longrightarrow> a div (b * c) = a div b div c"
  assumes discrete: "a < b \<longleftrightarrow> a + 1 \<le> b"
begin

lemma divmod_digit_1:
  assumes "0 \<le> a" "0 < b" and "b \<le> a mod (2 * b)"
  shows "2 * (a div (2 * b)) + 1 = a div b" (is "?P")
    and "a mod (2 * b) - b = a mod b" (is "?Q")
proof -
  from assms mod_less_eq_dividend [of a "2 * b"] have "b \<le> a"
    by (auto intro: trans)
  with \<open>0 < b\<close> have "0 < a div b" by (auto intro: div_positive)
  then have [simp]: "1 \<le> a div b" by (simp add: discrete)
  with \<open>0 < b\<close> have mod_less: "a mod b < b" by (simp add: pos_mod_bound)
  define w where "w = a div b mod 2"
  then have w_exhaust: "w = 0 \<or> w = 1" by auto
  have mod_w: "a mod (2 * b) = a mod b + b * w"
    by (simp add: w_def mod_mult2_eq ac_simps)
  from assms w_exhaust have "w = 1"
    using mod_less by (auto simp add: mod_w)
  with mod_w have mod: "a mod (2 * b) = a mod b + b" by simp
  have "2 * (a div (2 * b)) = a div b - w"
    by (simp add: w_def div_mult2_eq minus_mod_eq_mult_div ac_simps)
  with \<open>w = 1\<close> have div: "2 * (a div (2 * b)) = a div b - 1" by simp
  then show ?P and ?Q
    by (simp_all add: div mod add_implies_diff [symmetric])
qed

lemma divmod_digit_0:
  assumes "0 < b" and "a mod (2 * b) < b"
  shows "2 * (a div (2 * b)) = a div b" (is "?P")
    and "a mod (2 * b) = a mod b" (is "?Q")
proof -
  define w where "w = a div b mod 2"
  then have w_exhaust: "w = 0 \<or> w = 1" by auto
  have mod_w: "a mod (2 * b) = a mod b + b * w"
    by (simp add: w_def mod_mult2_eq ac_simps)
  moreover have "b \<le> a mod b + b"
  proof -
    from \<open>0 < b\<close> pos_mod_sign have "0 \<le> a mod b" by blast
    then have "0 + b \<le> a mod b + b" by (rule add_right_mono)
    then show ?thesis by simp
  qed
  moreover note assms w_exhaust
  ultimately have "w = 0" by auto
  with mod_w have mod: "a mod (2 * b) = a mod b" by simp
  have "2 * (a div (2 * b)) = a div b - w"
    by (simp add: w_def div_mult2_eq minus_mod_eq_mult_div ac_simps)
  with \<open>w = 0\<close> have div: "2 * (a div (2 * b)) = a div b" by simp
  then show ?P and ?Q
    by (simp_all add: div mod)
qed

lemma mod_double_modulus:
  assumes "m > 0" "x \<ge> 0"
  shows   "x mod (2 * m) = x mod m \<or> x mod (2 * m) = x mod m + m"
proof (cases "x mod (2 * m) < m")
  case True
  thus ?thesis using assms using divmod_digit_0(2)[of m x] by auto
next
  case False
  hence *: "x mod (2 * m) - m = x mod m"
    using assms by (intro divmod_digit_1) auto
  hence "x mod (2 * m) = x mod m + m"
    by (subst * [symmetric], subst le_add_diff_inverse2) (use False in auto)
  thus ?thesis by simp
qed

end

hide_fact (open) div_less mod_less mod_less_eq_dividend mod_mult2_eq div_mult2_eq

instance nat :: unique_euclidean_semiring_numeral
  by standard
    (auto simp add: div_greater_zero_iff div_mult2_eq mod_mult2_eq)

instance int :: unique_euclidean_semiring_numeral
  by standard (auto intro: zmod_le_nonneg_dividend simp add:
    pos_imp_zdiv_pos_iff zmod_zmult2_eq zdiv_zmult2_eq)

lemma div_geq: "m div n = Suc ((m - n) div n)" if "0 < n" and " \<not> m < n" for m n :: nat
  by (rule le_div_geq) (use that in \<open>simp_all add: not_less\<close>)

lemma mod_geq: "m mod n = (m - n) mod n" if "\<not> m < n" for m n :: nat
  by (rule le_mod_geq) (use that in \<open>simp add: not_less\<close>)

lemma mod_eq_0D: "\<exists>q. m = d * q" if "m mod d = 0" for m d :: nat
  using that by (auto simp add: mod_eq_0_iff_dvd)

lemma pos_mod_conj: "0 < b \<Longrightarrow> 0 \<le> a mod b \<and> a mod b < b" for a b :: int
  by simp

lemma neg_mod_conj: "b < 0 \<Longrightarrow> a mod b \<le> 0 \<and> b < a mod b" for a b :: int
  by simp

lemma zmod_eq_0_iff: "m mod d = 0 \<longleftrightarrow> (\<exists>q. m = d * q)" for m d :: int
  by (auto simp add: mod_eq_0_iff_dvd)

(* REVISIT: should this be generalized to all semiring_div types? *)
lemma zmod_eq_0D [dest!]: "\<exists>q. m = d * q" if "m mod d = 0" for m d :: int
  using that by auto

lemma div_positive_int:
  "k div l > 0" if "k \<ge> l" and "l > 0" for k l :: int
  using that by (simp add: nonneg1_imp_zdiv_pos_iff)

end
