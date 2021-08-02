(*  Title:      HOL/Divides.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

section \<open>More on quotient and remainder\<close>

theory Divides
imports Parity
begin

subsection \<open>More on division\<close>

inductive eucl_rel_int :: "int \<Rightarrow> int \<Rightarrow> int \<times> int \<Rightarrow> bool"
  where eucl_rel_int_by0: "eucl_rel_int k 0 (0, k)"
  | eucl_rel_int_dividesI: "l \<noteq> 0 \<Longrightarrow> k = q * l \<Longrightarrow> eucl_rel_int k l (q, 0)"
  | eucl_rel_int_remainderI: "sgn r = sgn l \<Longrightarrow> \<bar>r\<bar> < \<bar>l\<bar>
      \<Longrightarrow> k = q * l + r \<Longrightarrow> eucl_rel_int k l (q, r)"

lemma eucl_rel_int_iff:    
  "eucl_rel_int k l (q, r) \<longleftrightarrow> 
    k = l * q + r \<and>
     (if 0 < l then 0 \<le> r \<and> r < l else if l < 0 then l < r \<and> r \<le> 0 else q = 0)"
  by (cases "r = 0")
    (auto elim!: eucl_rel_int.cases intro: eucl_rel_int_by0 eucl_rel_int_dividesI eucl_rel_int_remainderI
    simp add: ac_simps sgn_1_pos sgn_1_neg)

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
  by (rule_tac b = "-b" and r = "-r'" and r' = "-r" in unique_quotient_lemma) auto

lemma unique_quotient:
  "eucl_rel_int a b (q, r) \<Longrightarrow> eucl_rel_int a b (q', r') \<Longrightarrow> q = q'"
  apply (rule order_antisym)
   apply (simp_all add: eucl_rel_int_iff linorder_neq_iff split: if_split_asm)
     apply (blast intro: order_eq_refl [THEN unique_quotient_lemma] order_eq_refl [THEN unique_quotient_lemma_neg] sym)+
  done

lemma unique_remainder:
  "eucl_rel_int a b (q, r) \<Longrightarrow> eucl_rel_int a b (q', r') \<Longrightarrow> r = r'"
apply (subgoal_tac "q = q'")
 apply (simp add: eucl_rel_int_iff)
apply (blast intro: unique_quotient)
done

lemma eucl_rel_int:
  "eucl_rel_int k l (k div l, k mod l)"
proof (cases k rule: int_cases3)
  case zero
  then show ?thesis
    by (simp add: eucl_rel_int_iff divide_int_def modulo_int_def)
next
  case (pos n)
  then show ?thesis
    using div_mult_mod_eq [of n]
    by (cases l rule: int_cases3)
      (auto simp del: of_nat_mult of_nat_add
        simp add: mod_greater_zero_iff_not_dvd of_nat_mult [symmetric] of_nat_add [symmetric] algebra_simps
        eucl_rel_int_iff divide_int_def modulo_int_def)
next
  case (neg n)
  then show ?thesis
    using div_mult_mod_eq [of n]
    by (cases l rule: int_cases3)
      (auto simp del: of_nat_mult of_nat_add
        simp add: mod_greater_zero_iff_not_dvd of_nat_mult [symmetric] of_nat_add [symmetric] algebra_simps
        eucl_rel_int_iff divide_int_def modulo_int_def)
qed

lemma divmod_int_unique:
  assumes "eucl_rel_int k l (q, r)"
  shows div_int_unique: "k div l = q" and mod_int_unique: "k mod l = r"
  using assms eucl_rel_int [of k l]
  using unique_quotient [of k l] unique_remainder [of k l]
  by auto

lemma div_abs_eq_div_nat:
  "\<bar>k\<bar> div \<bar>l\<bar> = int (nat \<bar>k\<bar> div nat \<bar>l\<bar>)"
  by (simp add: divide_int_def)

lemma mod_abs_eq_div_nat:
  "\<bar>k\<bar> mod \<bar>l\<bar> = int (nat \<bar>k\<bar> mod nat \<bar>l\<bar>)"
  by (simp add: modulo_int_def)

lemma zdiv_int:
  "int (a div b) = int a div int b"
  by (simp add: divide_int_def)

lemma zmod_int:
  "int (a mod b) = int a mod int b"
  by (simp add: modulo_int_def)

lemma div_sgn_abs_cancel:
  fixes k l v :: int
  assumes "v \<noteq> 0"
  shows "(sgn v * \<bar>k\<bar>) div (sgn v * \<bar>l\<bar>) = \<bar>k\<bar> div \<bar>l\<bar>"
proof -
  from assms have "sgn v = - 1 \<or> sgn v = 1"
    by (cases "v \<ge> 0") auto
  then show ?thesis
    using assms unfolding divide_int_def [of "sgn v * \<bar>k\<bar>" "sgn v * \<bar>l\<bar>"]
    by (fastforce simp add: not_less div_abs_eq_div_nat)
qed

lemma div_eq_sgn_abs:
  fixes k l v :: int
  assumes "sgn k = sgn l"
  shows "k div l = \<bar>k\<bar> div \<bar>l\<bar>"
proof (cases "l = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  with assms have "(sgn k * \<bar>k\<bar>) div (sgn l * \<bar>l\<bar>) = \<bar>k\<bar> div \<bar>l\<bar>"
    using div_sgn_abs_cancel [of l k l] by simp
  then show ?thesis
    by (simp add: sgn_mult_abs)
qed

lemma div_dvd_sgn_abs:
  fixes k l :: int
  assumes "l dvd k"
  shows "k div l = (sgn k * sgn l) * (\<bar>k\<bar> div \<bar>l\<bar>)"
proof (cases "k = 0 \<or> l = 0")
  case True
  then show ?thesis
    by auto
next
  case False
  then have "k \<noteq> 0" and "l \<noteq> 0"
    by auto
  show ?thesis
  proof (cases "sgn l = sgn k")
    case True
    then show ?thesis
      by (auto simp add: div_eq_sgn_abs)
  next
    case False
    with \<open>k \<noteq> 0\<close> \<open>l \<noteq> 0\<close>
    have "sgn l * sgn k = - 1"
      by (simp add: sgn_if split: if_splits)
    with assms show ?thesis
      unfolding divide_int_def [of k l]
      by (auto simp add: zdiv_int ac_simps)
  qed
qed

lemma div_noneq_sgn_abs:
  fixes k l :: int
  assumes "l \<noteq> 0"
  assumes "sgn k \<noteq> sgn l"
  shows "k div l = - (\<bar>k\<bar> div \<bar>l\<bar>) - of_bool (\<not> l dvd k)"
  using assms
  by (simp only: divide_int_def [of k l], auto simp add: not_less zdiv_int)
  

subsubsection \<open>Laws for div and mod with Unary Minus\<close>

lemma zminus1_lemma:
     "eucl_rel_int a b (q, r) ==> b \<noteq> 0
      ==> eucl_rel_int (-a) b (if r=0 then -q else -q - 1,
                          if r=0 then 0 else b-r)"
by (force simp add: eucl_rel_int_iff right_diff_distrib)


lemma zdiv_zminus1_eq_if:
     "b \<noteq> (0::int)
      \<Longrightarrow> (-a) div b = (if a mod b = 0 then - (a div b) else  - (a div b) - 1)"
by (blast intro: eucl_rel_int [THEN zminus1_lemma, THEN div_int_unique])

lemma zmod_zminus1_eq_if:
     "(-a::int) mod b = (if a mod b = 0 then 0 else  b - (a mod b))"
proof (cases "b = 0")
  case False
  then show ?thesis
    by (blast intro: eucl_rel_int [THEN zminus1_lemma, THEN mod_int_unique])
qed auto

lemma zmod_zminus1_not_zero:
  fixes k l :: int
  shows "- k mod l \<noteq> 0 \<Longrightarrow> k mod l \<noteq> 0"
  by (simp add: mod_eq_0_iff_dvd)

lemma zmod_zminus2_not_zero:
  fixes k l :: int
  shows "k mod - l \<noteq> 0 \<Longrightarrow> k mod l \<noteq> 0"
  by (simp add: mod_eq_0_iff_dvd)

lemma zdiv_zminus2_eq_if:
  "b \<noteq> (0::int)
      ==> a div (-b) =
          (if a mod b = 0 then - (a div b) else  - (a div b) - 1)"
  by (auto simp add: zdiv_zminus1_eq_if div_minus_right)

lemma zmod_zminus2_eq_if:
  "a mod (-b::int) = (if a mod b = 0 then 0 else  (a mod b) - b)"
  by (auto simp add: zmod_zminus1_eq_if mod_minus_right)


subsubsection \<open>Monotonicity in the First Argument (Dividend)\<close>

lemma zdiv_mono1:
  fixes b::int
  assumes "a \<le> a'" "0 < b" shows "a div b \<le> a' div b"
proof (rule unique_quotient_lemma)
  show "b * (a div b) + a mod b \<le> b * (a' div b) + a' mod b"
    using assms(1) by auto
qed (use assms in auto)

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


subsubsection \<open>Splitting Rules for div and mod\<close>

text\<open>The proofs of the two lemmas below are essentially identical\<close>

lemma split_pos_lemma:
 "0<k \<Longrightarrow>
    P(n div k :: int)(n mod k) = (\<forall>i j. 0\<le>j \<and> j<k \<and> n = k*i + j \<longrightarrow> P i j)"
  by auto

lemma split_neg_lemma:
 "k<0 \<Longrightarrow>
    P(n div k :: int)(n mod k) = (\<forall>i j. k<j \<and> j\<le>0 \<and> n = k*i + j \<longrightarrow> P i j)"
  by auto

lemma split_zdiv:
 "P(n div k :: int) =
  ((k = 0 \<longrightarrow> P 0) \<and>
   (0<k \<longrightarrow> (\<forall>i j. 0\<le>j \<and> j<k \<and> n = k*i + j \<longrightarrow> P i)) \<and>
   (k<0 \<longrightarrow> (\<forall>i j. k<j \<and> j\<le>0 \<and> n = k*i + j \<longrightarrow> P i)))"
proof (cases "k = 0")
  case False
  then show ?thesis
    unfolding linorder_neq_iff
    by (auto simp add: split_pos_lemma [of concl: "\<lambda>x y. P x"] split_neg_lemma [of concl: "\<lambda>x y. P x"])
qed auto

lemma split_zmod:
 "P(n mod k :: int) =
  ((k = 0 \<longrightarrow> P n) \<and>
   (0<k \<longrightarrow> (\<forall>i j. 0\<le>j \<and> j<k \<and> n = k*i + j \<longrightarrow> P j)) \<and>
   (k<0 \<longrightarrow> (\<forall>i j. k<j \<and> j\<le>0 \<and> n = k*i + j \<longrightarrow> P j)))"
proof (cases "k = 0")
  case False
  then show ?thesis
    unfolding linorder_neq_iff
    by (auto simp add: split_pos_lemma [of concl: "\<lambda>x y. P y"] split_neg_lemma [of concl: "\<lambda>x y. P y"])
qed auto

text \<open>Enable (lin)arith to deal with \<^const>\<open>divide\<close> and \<^const>\<open>modulo\<close>
  when these are applied to some constant that is of the form
  \<^term>\<open>numeral k\<close>:\<close>
declare split_zdiv [of _ _ "numeral k", arith_split] for k
declare split_zmod [of _ _ "numeral k", arith_split] for k


subsubsection \<open>Computing \<open>div\<close> and \<open>mod\<close> with shifting\<close>

lemma pos_eucl_rel_int_mult_2:
  assumes "0 \<le> b"
  assumes "eucl_rel_int a b (q, r)"
  shows "eucl_rel_int (1 + 2*a) (2*b) (q, 1 + 2*r)"
  using assms unfolding eucl_rel_int_iff by auto

lemma neg_eucl_rel_int_mult_2:
  assumes "b \<le> 0"
  assumes "eucl_rel_int (a + 1) b (q, r)"
  shows "eucl_rel_int (1 + 2*a) (2*b) (q, 2*r - 1)"
  using assms unfolding eucl_rel_int_iff by auto

text\<open>computing div by shifting\<close>

lemma pos_zdiv_mult_2: "(0::int) \<le> a ==> (1 + 2*b) div (2*a) = b div a"
  using pos_eucl_rel_int_mult_2 [OF _ eucl_rel_int]
  by (rule div_int_unique)

lemma neg_zdiv_mult_2:
  assumes A: "a \<le> (0::int)" shows "(1 + 2*b) div (2*a) = (b+1) div a"
  using neg_eucl_rel_int_mult_2 [OF A eucl_rel_int]
  by (rule div_int_unique)

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

lemma pos_zmod_mult_2:
  fixes a b :: int
  assumes "0 \<le> a"
  shows "(1 + 2 * b) mod (2 * a) = 1 + 2 * (b mod a)"
  using pos_eucl_rel_int_mult_2 [OF assms eucl_rel_int]
  by (rule mod_int_unique)

lemma neg_zmod_mult_2:
  fixes a b :: int
  assumes "a \<le> 0"
  shows "(1 + 2 * b) mod (2 * a) = 2 * ((b + 1) mod a) - 1"
  using neg_eucl_rel_int_mult_2 [OF assms eucl_rel_int]
  by (rule mod_int_unique)

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

lemma zdiv_eq_0_iff:
  "i div k = 0 \<longleftrightarrow> k = 0 \<or> 0 \<le> i \<and> i < k \<or> i \<le> 0 \<and> k < i" (is "?L = ?R")
  for i k :: int
proof
  assume ?L
  moreover have "?L \<longrightarrow> ?R"
    by (rule split_zdiv [THEN iffD2]) simp
  ultimately show ?R
    by blast
next
  assume ?R then show ?L
    by auto
qed

lemma zmod_trivial_iff:
  fixes i k :: int
  shows "i mod k = i \<longleftrightarrow> k = 0 \<or> 0 \<le> i \<and> i < k \<or> i \<le> 0 \<and> k < i"
proof -
  have "i mod k = i \<longleftrightarrow> i div k = 0"
    by safe (insert div_mult_mod_eq [of i k], auto)
  with zdiv_eq_0_iff
  show ?thesis
    by simp
qed

  
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
    moreover have \<open>0 < k mod l\<close> \<open>k mod l < 1 + l\<close>
      using \<open>0 < l\<close> le_imp_0_less False apply auto
      using le_less apply fastforce
      using pos_mod_bound [of l k] apply linarith 
      done
    with \<open>l > 0\<close> have \<open>(k mod l - 1) mod l = k mod l - 1\<close>
      by (simp add: zmod_trivial_iff)
    ultimately show ?thesis
      apply (simp only: zmod_zminus1_eq_if)
      apply (simp add: mod_eq_0_iff_dvd algebra_simps mod_simps)
      done
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


subsubsection \<open>Further properties\<close>

lemma div_int_pos_iff:
  "k div l \<ge> 0 \<longleftrightarrow> k = 0 \<or> l = 0 \<or> k \<ge> 0 \<and> l \<ge> 0
    \<or> k < 0 \<and> l < 0"
  for k l :: int
proof (cases "k = 0 \<or> l = 0")
  case False
  then show ?thesis
   apply (auto simp add: pos_imp_zdiv_nonneg_iff neg_imp_zdiv_nonneg_iff)
    by (meson neg_imp_zdiv_neg_iff not_le not_less_iff_gr_or_eq)
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

lemma int_div_pos_eq: "\<lbrakk>(a::int) = b * q + r; 0 \<le> r; r < b\<rbrakk> \<Longrightarrow> a div b = q"
  by (rule div_int_unique [of a b q r]) (simp add: eucl_rel_int_iff)

lemma int_div_neg_eq: "\<lbrakk>(a::int) = b * q + r; r \<le> 0; b < r\<rbrakk> \<Longrightarrow> a div b = q"
  by (rule div_int_unique [of a b q r],
    simp add: eucl_rel_int_iff)

lemma int_mod_pos_eq: "\<lbrakk>(a::int) = b * q + r; 0 \<le> r; r < b\<rbrakk> \<Longrightarrow> a mod b = r"
  by (rule mod_int_unique [of a b q r],
    simp add: eucl_rel_int_iff)

lemma int_mod_neg_eq: "\<lbrakk>(a::int) = b * q + r; r \<le> 0; b < r\<rbrakk> \<Longrightarrow> a mod b = r"
  by (rule mod_int_unique [of a b q r],
    simp add: eucl_rel_int_iff)

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
  using assms by (rule mod_eq_nat1E) rule

lemma nat_mod_eq_iff: "(x::nat) mod n = y mod n \<longleftrightarrow> (\<exists>q1 q2. x + n * q1 = y + n * q2)"
  (is "?lhs = ?rhs")
proof
  assume H: "x mod n = y mod n"
  {assume xy: "x \<le> y"
    from H have th: "y mod n = x mod n" by simp
    from nat_mod_eq_lemma[OF th xy] have ?rhs
      apply clarify  apply (rule_tac x="q" in exI) by (rule exI[where x="0"], simp)}
  moreover
  {assume xy: "y \<le> x"
    from nat_mod_eq_lemma[OF H xy] have ?rhs
      apply clarify  apply (rule_tac x="0" in exI) by (rule_tac x="q" in exI, simp)}
  ultimately  show ?rhs using linear[of x y] by blast
next
  assume ?rhs then obtain q1 q2 where q12: "x + n * q1 = y + n * q2" by blast
  hence "(x + n * q1) mod n = (y + n * q2) mod n" by simp
  thus  ?lhs by simp
qed


subsection \<open>Numeral division with a pragmatic type class\<close>

text \<open>
  The following type class contains everything necessary to formulate
  a division algorithm in ring structures with numerals, restricted
  to its positive segments.  This is its primary motivation, and it
  could surely be formulated using a more fine-grained, more algebraic
  and less technical class hierarchy.
\<close>

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
  fixes divmod :: "num \<Rightarrow> num \<Rightarrow> 'a \<times> 'a"
    and divmod_step :: "num \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a"
  assumes divmod_def: "divmod m n = (numeral m div numeral n, numeral m mod numeral n)"
    and divmod_step_def: "divmod_step l qr = (let (q, r) = qr
    in if r \<ge> numeral l then (2 * q + 1, r - numeral l)
    else (2 * q, r))"
    \<comment> \<open>These are conceptually definitions but force generated code
    to be monomorphic wrt. particular instances of this class which
    yields a significant speedup.\<close>
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
    by (auto simp add: mod_w) (insert mod_less, auto)
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

lemma fst_divmod:
  "fst (divmod m n) = numeral m div numeral n"
  by (simp add: divmod_def)

lemma snd_divmod:
  "snd (divmod m n) = numeral m mod numeral n"
  by (simp add: divmod_def)

text \<open>
  This is a formulation of one step (referring to one digit position)
  in school-method division: compare the dividend at the current
  digit position with the remainder from previous division steps
  and evaluate accordingly.
\<close>

lemma divmod_step_eq [simp]:
  "divmod_step l (q, r) = (if numeral l \<le> r
    then (2 * q + 1, r - numeral l) else (2 * q, r))"
  by (simp add: divmod_step_def)

text \<open>
  This is a formulation of school-method division.
  If the divisor is smaller than the dividend, terminate.
  If not, shift the dividend to the right until termination
  occurs and then reiterate single division steps in the
  opposite direction.
\<close>

lemma divmod_divmod_step:
  "divmod m n = (if m < n then (0, numeral m)
    else divmod_step n (divmod m (Num.Bit0 n)))"
proof (cases "m < n")
  case True then have "numeral m < numeral n" by simp
  then show ?thesis
    by (simp add: prod_eq_iff div_less mod_less fst_divmod snd_divmod)
next
  case False
  have "divmod m n =
    divmod_step n (numeral m div (2 * numeral n),
      numeral m mod (2 * numeral n))"
  proof (cases "numeral n \<le> numeral m mod (2 * numeral n)")
    case True
    with divmod_step_eq
      have "divmod_step n (numeral m div (2 * numeral n), numeral m mod (2 * numeral n)) =
        (2 * (numeral m div (2 * numeral n)) + 1, numeral m mod (2 * numeral n) - numeral n)"
        by simp
    moreover from True divmod_digit_1 [of "numeral m" "numeral n"]
      have "2 * (numeral m div (2 * numeral n)) + 1 = numeral m div numeral n"
      and "numeral m mod (2 * numeral n) - numeral n = numeral m mod numeral n"
      by simp_all
    ultimately show ?thesis by (simp only: divmod_def)
  next
    case False then have *: "numeral m mod (2 * numeral n) < numeral n"
      by (simp add: not_le)
    with divmod_step_eq
      have "divmod_step n (numeral m div (2 * numeral n), numeral m mod (2 * numeral n)) =
        (2 * (numeral m div (2 * numeral n)), numeral m mod (2 * numeral n))"
        by auto
    moreover from * divmod_digit_0 [of "numeral n" "numeral m"]
      have "2 * (numeral m div (2 * numeral n)) = numeral m div numeral n"
      and "numeral m mod (2 * numeral n) = numeral m mod numeral n"
      by (simp_all only: zero_less_numeral)
    ultimately show ?thesis by (simp only: divmod_def)
  qed
  then have "divmod m n =
    divmod_step n (numeral m div numeral (Num.Bit0 n),
      numeral m mod numeral (Num.Bit0 n))"
    by (simp only: numeral.simps distrib mult_1)
  then have "divmod m n = divmod_step n (divmod m (Num.Bit0 n))"
    by (simp add: divmod_def)
  with False show ?thesis by simp
qed

text \<open>The division rewrite proper -- first, trivial results involving \<open>1\<close>\<close>

lemma divmod_trivial [simp]:
  "divmod m Num.One = (numeral m, 0)"
  "divmod num.One (num.Bit0 n) = (0, Numeral1)"
  "divmod num.One (num.Bit1 n) = (0, Numeral1)"
  using divmod_divmod_step [of "Num.One"] by (simp_all add: divmod_def)

text \<open>Division by an even number is a right-shift\<close>

lemma divmod_cancel [simp]:
  "divmod (Num.Bit0 m) (Num.Bit0 n) = (case divmod m n of (q, r) \<Rightarrow> (q, 2 * r))" (is ?P)
  "divmod (Num.Bit1 m) (Num.Bit0 n) = (case divmod m n of (q, r) \<Rightarrow> (q, 2 * r + 1))" (is ?Q)
proof -
  have *: "\<And>q. numeral (Num.Bit0 q) = 2 * numeral q"
    "\<And>q. numeral (Num.Bit1 q) = 2 * numeral q + 1"
    by (simp_all only: numeral_mult numeral.simps distrib) simp_all
  have "1 div 2 = 0" "1 mod 2 = 1" by (auto intro: div_less mod_less)
  then show ?P and ?Q
    by (simp_all add: fst_divmod snd_divmod prod_eq_iff split_def * [of m] * [of n] mod_mult_mult1
      div_mult2_eq [of _ _ 2] mod_mult2_eq [of _ _ 2]
      add.commute del: numeral_times_numeral)
qed

text \<open>The really hard work\<close>

lemma divmod_steps [simp]:
  "divmod (num.Bit0 m) (num.Bit1 n) =
      (if m \<le> n then (0, numeral (num.Bit0 m))
       else divmod_step (num.Bit1 n)
             (divmod (num.Bit0 m)
               (num.Bit0 (num.Bit1 n))))"
  "divmod (num.Bit1 m) (num.Bit1 n) =
      (if m < n then (0, numeral (num.Bit1 m))
       else divmod_step (num.Bit1 n)
             (divmod (num.Bit1 m)
               (num.Bit0 (num.Bit1 n))))"
  by (simp_all add: divmod_divmod_step)

lemmas divmod_algorithm_code = divmod_step_eq divmod_trivial divmod_cancel divmod_steps  

text \<open>Special case: divisibility\<close>

definition divides_aux :: "'a \<times> 'a \<Rightarrow> bool"
where
  "divides_aux qr \<longleftrightarrow> snd qr = 0"

lemma divides_aux_eq [simp]:
  "divides_aux (q, r) \<longleftrightarrow> r = 0"
  by (simp add: divides_aux_def)

lemma dvd_numeral_simp [simp]:
  "numeral m dvd numeral n \<longleftrightarrow> divides_aux (divmod n m)"
  by (simp add: divmod_def mod_eq_0_iff_dvd)

text \<open>Generic computation of quotient and remainder\<close>  

lemma numeral_div_numeral [simp]: 
  "numeral k div numeral l = fst (divmod k l)"
  by (simp add: fst_divmod)

lemma numeral_mod_numeral [simp]: 
  "numeral k mod numeral l = snd (divmod k l)"
  by (simp add: snd_divmod)

lemma one_div_numeral [simp]:
  "1 div numeral n = fst (divmod num.One n)"
  by (simp add: fst_divmod)

lemma one_mod_numeral [simp]:
  "1 mod numeral n = snd (divmod num.One n)"
  by (simp add: snd_divmod)

text \<open>Computing congruences modulo \<open>2 ^ q\<close>\<close>

lemma cong_exp_iff_simps:
  "numeral n mod numeral Num.One = 0
    \<longleftrightarrow> True"
  "numeral (Num.Bit0 n) mod numeral (Num.Bit0 q) = 0
    \<longleftrightarrow> numeral n mod numeral q = 0"
  "numeral (Num.Bit1 n) mod numeral (Num.Bit0 q) = 0
    \<longleftrightarrow> False"
  "numeral m mod numeral Num.One = (numeral n mod numeral Num.One)
    \<longleftrightarrow> True"
  "numeral Num.One mod numeral (Num.Bit0 q) = (numeral Num.One mod numeral (Num.Bit0 q))
    \<longleftrightarrow> True"
  "numeral Num.One mod numeral (Num.Bit0 q) = (numeral (Num.Bit0 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> False"
  "numeral Num.One mod numeral (Num.Bit0 q) = (numeral (Num.Bit1 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> (numeral n mod numeral q) = 0"
  "numeral (Num.Bit0 m) mod numeral (Num.Bit0 q) = (numeral Num.One mod numeral (Num.Bit0 q))
    \<longleftrightarrow> False"
  "numeral (Num.Bit0 m) mod numeral (Num.Bit0 q) = (numeral (Num.Bit0 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> numeral m mod numeral q = (numeral n mod numeral q)"
  "numeral (Num.Bit0 m) mod numeral (Num.Bit0 q) = (numeral (Num.Bit1 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> False"
  "numeral (Num.Bit1 m) mod numeral (Num.Bit0 q) = (numeral Num.One mod numeral (Num.Bit0 q))
    \<longleftrightarrow> (numeral m mod numeral q) = 0"
  "numeral (Num.Bit1 m) mod numeral (Num.Bit0 q) = (numeral (Num.Bit0 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> False"
  "numeral (Num.Bit1 m) mod numeral (Num.Bit0 q) = (numeral (Num.Bit1 n) mod numeral (Num.Bit0 q))
    \<longleftrightarrow> numeral m mod numeral q = (numeral n mod numeral q)"
  by (auto simp add: case_prod_beta dest: arg_cong [of _ _ even])

end

hide_fact (open) div_less mod_less mod_less_eq_dividend mod_mult2_eq div_mult2_eq

instantiation nat :: unique_euclidean_semiring_numeral
begin

definition divmod_nat :: "num \<Rightarrow> num \<Rightarrow> nat \<times> nat"
where
  divmod'_nat_def: "divmod_nat m n = (numeral m div numeral n, numeral m mod numeral n)"

definition divmod_step_nat :: "num \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat"
where
  "divmod_step_nat l qr = (let (q, r) = qr
    in if r \<ge> numeral l then (2 * q + 1, r - numeral l)
    else (2 * q, r))"

instance by standard
  (auto simp add: divmod'_nat_def divmod_step_nat_def div_greater_zero_iff div_mult2_eq mod_mult2_eq)

end

declare divmod_algorithm_code [where ?'a = nat, code]

lemma Suc_0_div_numeral [simp]:
  fixes k l :: num
  shows "Suc 0 div numeral k = fst (divmod Num.One k)"
  by (simp_all add: fst_divmod)

lemma Suc_0_mod_numeral [simp]:
  fixes k l :: num
  shows "Suc 0 mod numeral k = snd (divmod Num.One k)"
  by (simp_all add: snd_divmod)

instantiation int :: unique_euclidean_semiring_numeral
begin

definition divmod_int :: "num \<Rightarrow> num \<Rightarrow> int \<times> int"
where
  "divmod_int m n = (numeral m div numeral n, numeral m mod numeral n)"

definition divmod_step_int :: "num \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int"
where
  "divmod_step_int l qr = (let (q, r) = qr
    in if r \<ge> numeral l then (2 * q + 1, r - numeral l)
    else (2 * q, r))"

instance
  by standard (auto intro: zmod_le_nonneg_dividend simp add: divmod_int_def divmod_step_int_def
    pos_imp_zdiv_pos_iff zmod_zmult2_eq zdiv_zmult2_eq)

end

declare divmod_algorithm_code [where ?'a = int, code]

context
begin
  
qualified definition adjust_div :: "int \<times> int \<Rightarrow> int"
where
  "adjust_div qr = (let (q, r) = qr in q + of_bool (r \<noteq> 0))"

qualified lemma adjust_div_eq [simp, code]:
  "adjust_div (q, r) = q + of_bool (r \<noteq> 0)"
  by (simp add: adjust_div_def)

qualified definition adjust_mod :: "int \<Rightarrow> int \<Rightarrow> int"
where
  [simp]: "adjust_mod l r = (if r = 0 then 0 else l - r)"

lemma minus_numeral_div_numeral [simp]:
  "- numeral m div numeral n = - (adjust_div (divmod m n) :: int)"
proof -
  have "int (fst (divmod m n)) = fst (divmod m n)"
    by (simp only: fst_divmod divide_int_def) auto
  then show ?thesis
    by (auto simp add: split_def Let_def adjust_div_def divides_aux_def divide_int_def)
qed

lemma minus_numeral_mod_numeral [simp]:
  "- numeral m mod numeral n = adjust_mod (numeral n) (snd (divmod m n) :: int)"
proof (cases "snd (divmod m n) = (0::int)")
  case True
  then show ?thesis
    by (simp add: mod_eq_0_iff_dvd divides_aux_def)
next
  case False
  then have "int (snd (divmod m n)) = snd (divmod m n)" if "snd (divmod m n) \<noteq> (0::int)"
    by (simp only: snd_divmod modulo_int_def) auto
  then show ?thesis
    by (simp add: divides_aux_def adjust_div_def)
      (simp add: divides_aux_def modulo_int_def)
qed

lemma numeral_div_minus_numeral [simp]:
  "numeral m div - numeral n = - (adjust_div (divmod m n) :: int)"
proof -
  have "int (fst (divmod m n)) = fst (divmod m n)"
    by (simp only: fst_divmod divide_int_def) auto
  then show ?thesis
    by (auto simp add: split_def Let_def adjust_div_def divides_aux_def divide_int_def)
qed
  
lemma numeral_mod_minus_numeral [simp]:
  "numeral m mod - numeral n = - adjust_mod (numeral n) (snd (divmod m n) :: int)"
proof (cases "snd (divmod m n) = (0::int)")
  case True
  then show ?thesis
    by (simp add: mod_eq_0_iff_dvd divides_aux_def)
next
  case False
  then have "int (snd (divmod m n)) = snd (divmod m n)" if "snd (divmod m n) \<noteq> (0::int)"
    by (simp only: snd_divmod modulo_int_def) auto
  then show ?thesis
    by (simp add: divides_aux_def adjust_div_def)
      (simp add: divides_aux_def modulo_int_def)
qed

lemma minus_one_div_numeral [simp]:
  "- 1 div numeral n = - (adjust_div (divmod Num.One n) :: int)"
  using minus_numeral_div_numeral [of Num.One n] by simp  

lemma minus_one_mod_numeral [simp]:
  "- 1 mod numeral n = adjust_mod (numeral n) (snd (divmod Num.One n) :: int)"
  using minus_numeral_mod_numeral [of Num.One n] by simp

lemma one_div_minus_numeral [simp]:
  "1 div - numeral n = - (adjust_div (divmod Num.One n) :: int)"
  using numeral_div_minus_numeral [of Num.One n] by simp
  
lemma one_mod_minus_numeral [simp]:
  "1 mod - numeral n = - adjust_mod (numeral n) (snd (divmod Num.One n) :: int)"
  using numeral_mod_minus_numeral [of Num.One n] by simp

end

lemma divmod_BitM_2_eq [simp]:
  \<open>divmod (Num.BitM m) (Num.Bit0 Num.One) = (numeral m - 1, (1 :: int))\<close>
  by (cases m) simp_all

lemma div_positive_int:
  "k div l > 0" if "k \<ge> l" and "l > 0" for k l :: int
  using that div_positive [of l k] by blast


subsubsection \<open>Dedicated simproc for calculation\<close>

text \<open>
  There is space for improvement here: the calculation itself
  could be carried out outside the logic, and a generic simproc
  (simplifier setup) for generic calculation would be helpful. 
\<close>

simproc_setup numeral_divmod
  ("0 div 0 :: 'a :: unique_euclidean_semiring_numeral" | "0 mod 0 :: 'a :: unique_euclidean_semiring_numeral" |
   "0 div 1 :: 'a :: unique_euclidean_semiring_numeral" | "0 mod 1 :: 'a :: unique_euclidean_semiring_numeral" |
   "0 div - 1 :: int" | "0 mod - 1 :: int" |
   "0 div numeral b :: 'a :: unique_euclidean_semiring_numeral" | "0 mod numeral b :: 'a :: unique_euclidean_semiring_numeral" |
   "0 div - numeral b :: int" | "0 mod - numeral b :: int" |
   "1 div 0 :: 'a :: unique_euclidean_semiring_numeral" | "1 mod 0 :: 'a :: unique_euclidean_semiring_numeral" |
   "1 div 1 :: 'a :: unique_euclidean_semiring_numeral" | "1 mod 1 :: 'a :: unique_euclidean_semiring_numeral" |
   "1 div - 1 :: int" | "1 mod - 1 :: int" |
   "1 div numeral b :: 'a :: unique_euclidean_semiring_numeral" | "1 mod numeral b :: 'a :: unique_euclidean_semiring_numeral" |
   "1 div - numeral b :: int" |"1 mod - numeral b :: int" |
   "- 1 div 0 :: int" | "- 1 mod 0 :: int" | "- 1 div 1 :: int" | "- 1 mod 1 :: int" |
   "- 1 div - 1 :: int" | "- 1 mod - 1 :: int" | "- 1 div numeral b :: int" | "- 1 mod numeral b :: int" |
   "- 1 div - numeral b :: int" | "- 1 mod - numeral b :: int" |
   "numeral a div 0 :: 'a :: unique_euclidean_semiring_numeral" | "numeral a mod 0 :: 'a :: unique_euclidean_semiring_numeral" |
   "numeral a div 1 :: 'a :: unique_euclidean_semiring_numeral" | "numeral a mod 1 :: 'a :: unique_euclidean_semiring_numeral" |
   "numeral a div - 1 :: int" | "numeral a mod - 1 :: int" |
   "numeral a div numeral b :: 'a :: unique_euclidean_semiring_numeral" | "numeral a mod numeral b :: 'a :: unique_euclidean_semiring_numeral" |
   "numeral a div - numeral b :: int" | "numeral a mod - numeral b :: int" |
   "- numeral a div 0 :: int" | "- numeral a mod 0 :: int" |
   "- numeral a div 1 :: int" | "- numeral a mod 1 :: int" |
   "- numeral a div - 1 :: int" | "- numeral a mod - 1 :: int" |
   "- numeral a div numeral b :: int" | "- numeral a mod numeral b :: int" |
   "- numeral a div - numeral b :: int" | "- numeral a mod - numeral b :: int") =
\<open> let
    val if_cong = the (Code.get_case_cong \<^theory> \<^const_name>\<open>If\<close>);
    fun successful_rewrite ctxt ct =
      let
        val thm = Simplifier.rewrite ctxt ct
      in if Thm.is_reflexive thm then NONE else SOME thm end;
  in fn phi =>
    let
      val simps = Morphism.fact phi (@{thms div_0 mod_0 div_by_0 mod_by_0 div_by_1 mod_by_1
        one_div_numeral one_mod_numeral minus_one_div_numeral minus_one_mod_numeral
        one_div_minus_numeral one_mod_minus_numeral
        numeral_div_numeral numeral_mod_numeral minus_numeral_div_numeral minus_numeral_mod_numeral
        numeral_div_minus_numeral numeral_mod_minus_numeral
        div_minus_minus mod_minus_minus Divides.adjust_div_eq of_bool_eq one_neq_zero
        numeral_neq_zero neg_equal_0_iff_equal arith_simps arith_special divmod_trivial
        divmod_cancel divmod_steps divmod_step_eq fst_conv snd_conv numeral_One
        case_prod_beta rel_simps Divides.adjust_mod_def div_minus1_right mod_minus1_right
        minus_minus numeral_times_numeral mult_zero_right mult_1_right}
        @ [@{lemma "0 = 0 \<longleftrightarrow> True" by simp}]);
      fun prepare_simpset ctxt = HOL_ss |> Simplifier.simpset_map ctxt
        (Simplifier.add_cong if_cong #> fold Simplifier.add_simp simps)
    in fn ctxt => successful_rewrite (Simplifier.put_simpset (prepare_simpset ctxt) ctxt) end
  end
\<close>


subsubsection \<open>Code generation\<close>

definition divmod_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat"
  where "divmod_nat m n = (m div n, m mod n)"

lemma fst_divmod_nat [simp]:
  "fst (divmod_nat m n) = m div n"
  by (simp add: divmod_nat_def)

lemma snd_divmod_nat [simp]:
  "snd (divmod_nat m n) = m mod n"
  by (simp add: divmod_nat_def)

lemma divmod_nat_if [code]:
  "Divides.divmod_nat m n = (if n = 0 \<or> m < n then (0, m) else
    let (q, r) = Divides.divmod_nat (m - n) n in (Suc q, r))"
  by (simp add: prod_eq_iff case_prod_beta not_less le_div_geq le_mod_geq)

lemma [code]:
  "m div n = fst (divmod_nat m n)"
  "m mod n = snd (divmod_nat m n)"
  by simp_all

lemma [code]:
  fixes k :: int
  shows 
    "k div 0 = 0"
    "k mod 0 = k"
    "0 div k = 0"
    "0 mod k = 0"
    "k div Int.Pos Num.One = k"
    "k mod Int.Pos Num.One = 0"
    "k div Int.Neg Num.One = - k"
    "k mod Int.Neg Num.One = 0"
    "Int.Pos m div Int.Pos n = (fst (divmod m n) :: int)"
    "Int.Pos m mod Int.Pos n = (snd (divmod m n) :: int)"
    "Int.Neg m div Int.Pos n = - (Divides.adjust_div (divmod m n) :: int)"
    "Int.Neg m mod Int.Pos n = Divides.adjust_mod (Int.Pos n) (snd (divmod m n) :: int)"
    "Int.Pos m div Int.Neg n = - (Divides.adjust_div (divmod m n) :: int)"
    "Int.Pos m mod Int.Neg n = - Divides.adjust_mod (Int.Pos n) (snd (divmod m n) :: int)"
    "Int.Neg m div Int.Neg n = (fst (divmod m n) :: int)"
    "Int.Neg m mod Int.Neg n = - (snd (divmod m n) :: int)"
  by simp_all

code_identifier
  code_module Divides \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith


subsection \<open>Lemmas of doubtful value\<close>

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

end
