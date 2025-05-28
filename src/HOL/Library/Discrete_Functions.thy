(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Common discrete functions\<close>

theory Discrete_Functions
imports Complex_Main
begin

subsection \<open>Discrete logarithm\<close>

fun floor_log :: "nat \<Rightarrow> nat"
  where [simp del]: "floor_log n = (if n < 2 then 0 else Suc (floor_log (n div 2)))"

lemma floor_log_induct [consumes 1, case_names one double]:
  fixes n :: nat
  assumes "n > 0"
  assumes one: "P 1"
  assumes double: "\<And>n. n \<ge> 2 \<Longrightarrow> P (n div 2) \<Longrightarrow> P n"
  shows "P n"
using \<open>n > 0\<close> proof (induct n rule: floor_log.induct)
  fix n
  assume "\<not> n < 2 \<Longrightarrow>
          0 < n div 2 \<Longrightarrow> P (n div 2)"
  then have *: "n \<ge> 2 \<Longrightarrow> P (n div 2)" by simp
  assume "n > 0"
  show "P n"
  proof (cases "n = 1")
    case True
    with one show ?thesis by simp
  next
    case False
    with \<open>n > 0\<close> have "n \<ge> 2" by auto
    with * have "P (n div 2)" .
    with \<open>n \<ge> 2\<close> show ?thesis by (rule double)
  qed
qed

lemma floor_log_zero [simp]: "floor_log 0 = 0"
  by (simp add: floor_log.simps)

lemma floor_log_one [simp]: "floor_log 1 = 0"
  by (simp add: floor_log.simps)

lemma floor_log_Suc_zero [simp]: "floor_log (Suc 0) = 0"
  using floor_log_one by simp

lemma floor_log_rec: "n \<ge> 2 \<Longrightarrow> floor_log n = Suc (floor_log (n div 2))"
  by (simp add: floor_log.simps)

lemma floor_log_twice [simp]: "n \<noteq> 0 \<Longrightarrow> floor_log (2 * n) = Suc (floor_log n)"
  by (simp add: floor_log_rec)

lemma floor_log_half [simp]: "floor_log (n div 2) = floor_log n - 1"
proof (cases "n < 2")
  case True
  then have "n = 0 \<or> n = 1" by arith
  then show ?thesis by (auto simp del: One_nat_def)
next
  case False
  then show ?thesis by (simp add: floor_log_rec)
qed

lemma floor_log_power [simp]: "floor_log (2 ^ n) = n"
  by (induct n) simp_all

lemma floor_log_mono: "mono floor_log"
proof
  fix m n :: nat
  assume "m \<le> n"
  then show "floor_log m \<le> floor_log n"
  proof (induct m arbitrary: n rule: floor_log.induct)
    case (1 m)
    then have mn2: "m div 2 \<le> n div 2" by arith
    show "floor_log m \<le> floor_log n"
    proof (cases "m \<ge> 2")
      case False
      then have "m = 0 \<or> m = 1" by arith
      then show ?thesis by (auto simp del: One_nat_def)
    next
      case True then have "\<not> m < 2" by simp
      with mn2 have "n \<ge> 2" by arith
      from True have m2_0: "m div 2 \<noteq> 0" by arith
      with mn2 have n2_0: "n div 2 \<noteq> 0" by arith
      from \<open>\<not> m < 2\<close> "1.hyps" mn2 have "floor_log (m div 2) \<le> floor_log (n div 2)" by blast
      with m2_0 n2_0 have "floor_log (2 * (m div 2)) \<le> floor_log (2 * (n div 2))" by simp
      with m2_0 n2_0 \<open>m \<ge> 2\<close> \<open>n \<ge> 2\<close> show ?thesis by (simp only: floor_log_rec [of m] floor_log_rec [of n]) simp
    qed
  qed
qed

lemma floor_log_exp2_le:
  assumes "n > 0"
  shows "2 ^ floor_log n \<le> n"
  using assms
proof (induct n rule: floor_log_induct)
  case one
  then show ?case by simp
next
  case (double n)
  with floor_log_mono have "floor_log n \<ge> Suc 0"
    by (simp add: floor_log.simps)
  assume "2 ^ floor_log (n div 2) \<le> n div 2"
  with \<open>n \<ge> 2\<close> have "2 ^ (floor_log n - Suc 0) \<le> n div 2" by simp
  then have "2 ^ (floor_log n - Suc 0) * 2 ^ 1 \<le> n div 2 * 2" by simp
  with \<open>floor_log n \<ge> Suc 0\<close> have "2 ^ floor_log n \<le> n div 2 * 2"
    unfolding power_add [symmetric] by simp
  also have "n div 2 * 2 \<le> n" by (cases "even n") simp_all
  finally show ?case .
qed

lemma floor_log_exp2_gt: "2 * 2 ^ floor_log n > n"
proof (cases "n > 0")
  case True
  thus ?thesis
  proof (induct n rule: floor_log_induct)
    case (double n)
    thus ?case
      by (cases "even n") (auto elim!: evenE oddE simp: field_simps floor_log.simps)
  qed simp_all
qed simp_all

lemma floor_log_exp2_ge: "2 * 2 ^ floor_log n \<ge> n"
  using floor_log_exp2_gt[of n] by simp

lemma floor_log_le_iff: "m \<le> n \<Longrightarrow> floor_log m \<le> floor_log n"
  by (rule monoD [OF floor_log_mono])

lemma floor_log_eqI:
  assumes "n > 0" "2^k \<le> n" "n < 2 * 2^k"
  shows   "floor_log n = k"
proof (rule antisym)
  from \<open>n > 0\<close> have "2 ^ floor_log n \<le> n" by (rule floor_log_exp2_le)
  also have "\<dots> < 2 ^ Suc k" using assms by simp
  finally have "floor_log n < Suc k" by (subst (asm) power_strict_increasing_iff) simp_all
  thus "floor_log n \<le> k" by simp
next
  have "2^k \<le> n" by fact
  also have "\<dots> < 2^(Suc (floor_log n))" by (simp add: floor_log_exp2_gt)
  finally have "k < Suc (floor_log n)" by (subst (asm) power_strict_increasing_iff) simp_all
  thus "k \<le> floor_log n" by simp
qed

lemma floor_log_altdef: "floor_log n = (if n = 0 then 0 else nat \<lfloor>log 2 (real_of_nat n)\<rfloor>)"
proof (cases "n = 0")
  case False
  have "\<lfloor>log 2 (real_of_nat n)\<rfloor> = int (floor_log n)"
  proof (rule floor_unique)
    from False have "2 powr (real (floor_log n)) \<le> real n"
      by (simp add: powr_realpow floor_log_exp2_le)
    hence "log 2 (2 powr (real (floor_log n))) \<le> log 2 (real n)"
      using False by (subst log_le_cancel_iff) simp_all
    also have "log 2 (2 powr (real (floor_log n))) = real (floor_log n)" by simp
    finally show "real_of_int (int (floor_log n)) \<le> log 2 (real n)" by simp
  next
    have "real n < real (2 * 2 ^ floor_log n)"
      by (subst of_nat_less_iff) (rule floor_log_exp2_gt)
    also have "\<dots> = 2 powr (real (floor_log n) + 1)"
      by (simp add: powr_add powr_realpow)
    finally have "log 2 (real n) < log 2 \<dots>"
      using False by (subst log_less_cancel_iff) simp_all
    also have "\<dots> = real (floor_log n) + 1" by simp
    finally show "log 2 (real n) < real_of_int (int (floor_log n)) + 1" by simp
  qed
  thus ?thesis by simp
qed simp_all


subsection \<open>Discrete square root\<close>

definition floor_sqrt :: "nat \<Rightarrow> nat"
  where "floor_sqrt n = Max {m. m\<^sup>2 \<le> n}"

lemma floor_sqrt_aux:
  fixes n :: nat
  shows "finite {m. m\<^sup>2 \<le> n}" and "{m. m\<^sup>2 \<le> n} \<noteq> {}"
proof -
  have **: "m \<le> n" if "m\<^sup>2 \<le> n" for m
    using that by (cases m) (simp_all add: power2_eq_square)
  then have "{m. m\<^sup>2 \<le> n} \<subseteq> {m. m \<le> n}" by auto
  then show "finite {m. m\<^sup>2 \<le> n}" by (rule finite_subset) rule
  have "0\<^sup>2 \<le> n" by simp
  then show *: "{m. m\<^sup>2 \<le> n} \<noteq> {}" by blast
qed

lemma floor_sqrt_unique:
  assumes "m^2 \<le> n" "n < (Suc m)^2"
  shows   "floor_sqrt n = m"
proof -
  have "m' \<le> m" if "m'^2 \<le> n" for m'
  proof -
    note that
    also note assms(2)
    finally have "m' < Suc m" by (rule power_less_imp_less_base) simp_all
    thus "m' \<le> m" by simp
  qed
  with \<open>m^2 \<le> n\<close> floor_sqrt_aux[of n] show ?thesis unfolding floor_sqrt_def
    by (intro antisym Max.boundedI Max.coboundedI) simp_all
qed


lemma floor_sqrt_code[code]: "floor_sqrt n = Max (Set.filter (\<lambda>m. m\<^sup>2 \<le> n) {0..n})"
proof -
  from power2_nat_le_imp_le [of _ n]
    have "{m. m \<le> n \<and> m\<^sup>2 \<le> n} = {m. m\<^sup>2 \<le> n}" by auto
    then show ?thesis
    by (simp add: floor_sqrt_def)
qed

lemma floor_sqrt_inverse_power2 [simp]: "floor_sqrt (n\<^sup>2) = n"
proof -
  have "{m. m \<le> n} \<noteq> {}" by auto
  then have "Max {m. m \<le> n} \<le> n" by auto
  then show ?thesis
    by (auto simp add: floor_sqrt_def power2_nat_le_eq_le intro: antisym)
qed

lemma floor_sqrt_zero [simp]: "floor_sqrt 0 = 0"
  using floor_sqrt_inverse_power2 [of 0] by simp

lemma floor_sqrt_one [simp]: "floor_sqrt 1 = 1"
  using floor_sqrt_inverse_power2 [of 1] by simp

lemma mono_floor_sqrt: "mono floor_sqrt"
proof
  fix m n :: nat
  have *: "0 * 0 \<le> m" by simp
  assume "m \<le> n"
  then show "floor_sqrt m \<le> floor_sqrt n"
    by (auto intro!: Max_mono \<open>0 * 0 \<le> m\<close> finite_less_ub simp add: power2_eq_square floor_sqrt_def)
qed

lemma mono_floor_sqrt': "m \<le> n \<Longrightarrow> floor_sqrt m \<le> floor_sqrt n"
  using mono_floor_sqrt unfolding mono_def by auto

lemma floor_sqrt_greater_zero_iff [simp]: "floor_sqrt n > 0 \<longleftrightarrow> n > 0"
proof -
  have *: "0 < Max {m. m\<^sup>2 \<le> n} \<longleftrightarrow> (\<exists>a\<in>{m. m\<^sup>2 \<le> n}. 0 < a)"
    by (rule Max_gr_iff) (fact floor_sqrt_aux)+
  show ?thesis
  proof
    assume "0 < floor_sqrt n"
    then have "0 < Max {m. m\<^sup>2 \<le> n}" by (simp add: floor_sqrt_def)
    with * show "0 < n" by (auto dest: power2_nat_le_imp_le)
  next
    assume "0 < n"
    then have "1\<^sup>2 \<le> n \<and> 0 < (1::nat)" by simp
    then have "\<exists>q. q\<^sup>2 \<le> n \<and> 0 < q" ..
    with * have "0 < Max {m. m\<^sup>2 \<le> n}" by blast
    then show "0 < floor_sqrt n" by  (simp add: floor_sqrt_def)
  qed
qed

lemma floor_sqrt_power2_le [simp]: "(floor_sqrt n)\<^sup>2 \<le> n" (* FIXME tune proof *)
proof (cases "n > 0")
  case False then show ?thesis by simp
next
  case True then have "floor_sqrt n > 0" by simp
  then have "mono (times (Max {m. m\<^sup>2 \<le> n}))" by (auto intro: mono_times_nat simp add: floor_sqrt_def)
  then have *: "Max {m. m\<^sup>2 \<le> n} * Max {m. m\<^sup>2 \<le> n} = Max (times (Max {m. m\<^sup>2 \<le> n}) ` {m. m\<^sup>2 \<le> n})"
    using floor_sqrt_aux [of n] by (rule mono_Max_commute)
  have "\<And>a. a * a \<le> n \<Longrightarrow> Max {m. m * m \<le> n} * a \<le> n"
  proof -
    fix q
    assume "q * q \<le> n"
    show "Max {m. m * m \<le> n} * q \<le> n"
    proof (cases "q > 0")
      case False then show ?thesis by simp
    next
      case True then have "mono (times q)" by (rule mono_times_nat)
      then have "q * Max {m. m * m \<le> n} = Max (times q ` {m. m * m \<le> n})"
        using floor_sqrt_aux [of n] by (auto simp add: power2_eq_square intro: mono_Max_commute)
      then have "Max {m. m * m \<le> n} * q = Max (times q ` {m. m * m \<le> n})" by (simp add: ac_simps)
      moreover have "finite ((*) q ` {m. m * m \<le> n})"
        by (metis (mono_tags) finite_imageI finite_less_ub le_square)
      moreover have "\<exists>x. x * x \<le> n"
        by (metis \<open>q * q \<le> n\<close>)
      ultimately show ?thesis
        by simp (metis \<open>q * q \<le> n\<close> le_cases mult_le_mono1 mult_le_mono2 order_trans)
    qed
  qed
  then have "Max ((*) (Max {m. m * m \<le> n}) ` {m. m * m \<le> n}) \<le> n"
    apply (subst Max_le_iff)
      apply (metis (mono_tags) finite_imageI finite_less_ub le_square)
     apply auto
    apply (metis le0 mult_0_right)
    done
  with * show ?thesis by (simp add: floor_sqrt_def power2_eq_square)
qed

lemma floor_sqrt_le: "floor_sqrt n \<le> n"
  using floor_sqrt_aux [of n] by (auto simp add: floor_sqrt_def intro: power2_nat_le_imp_le)

text \<open>Additional facts about the discrete square root, thanks to Julian Biendarra, Manuel Eberl\<close>

lemma Suc_floor_sqrt_power2_gt: "n < (Suc (floor_sqrt n))^2"
  using Max_ge[OF floor_sqrt_aux(1), of "floor_sqrt n + 1" n]
  by (cases "n < (Suc (floor_sqrt n))^2") (simp_all add: floor_sqrt_def)

lemma le_floor_sqrt_iff: "x \<le> floor_sqrt y \<longleftrightarrow> x^2 \<le> y"
proof -
  have "x \<le> floor_sqrt y \<longleftrightarrow> (\<exists>z. z\<^sup>2 \<le> y \<and> x \<le> z)"
    using Max_ge_iff[OF floor_sqrt_aux, of x y] by (simp add: floor_sqrt_def)
  also have "\<dots> \<longleftrightarrow> x^2 \<le> y"
  proof safe
    fix z assume "x \<le> z" "z ^ 2 \<le> y"
    thus "x^2 \<le> y" by (intro le_trans[of "x^2" "z^2" y]) (simp_all add: power2_nat_le_eq_le)
  qed auto
  finally show ?thesis .
qed

lemma le_floor_sqrtI: "x^2 \<le> y \<Longrightarrow> x \<le> floor_sqrt y"
  by (simp add: le_floor_sqrt_iff)

lemma floor_sqrt_le_iff: "floor_sqrt y \<le> x \<longleftrightarrow> (\<forall>z. z^2 \<le> y \<longrightarrow> z \<le> x)"
  using Max.bounded_iff[OF floor_sqrt_aux] by (simp add: floor_sqrt_def)

lemma floor_sqrt_leI:
  "(\<And>z. z^2 \<le> y \<Longrightarrow> z \<le> x) \<Longrightarrow> floor_sqrt y \<le> x"
  by (simp add: floor_sqrt_le_iff)

lemma floor_sqrt_Suc:
  "floor_sqrt (Suc n) = (if \<exists>m. Suc n = m^2 then Suc (floor_sqrt n) else floor_sqrt n)"
proof cases
  assume "\<exists> m. Suc n = m^2"
  then obtain m where m_def: "Suc n = m^2" by blast
  then have lhs: "floor_sqrt (Suc n) = m" by simp
  from m_def floor_sqrt_power2_le[of n]
    have "(floor_sqrt n)^2 < m^2" by linarith
  with power2_less_imp_less have lt_m: "floor_sqrt n < m" by blast
  from m_def Suc_floor_sqrt_power2_gt[of "n"]
    have "m^2 \<le> (Suc(floor_sqrt n))^2"
      by linarith
  with power2_nat_le_eq_le have "m \<le> Suc (floor_sqrt n)" by blast
  with lt_m have "m = Suc (floor_sqrt n)" by simp
  with lhs m_def show ?thesis by fastforce
next
  assume asm: "\<not> (\<exists> m. Suc n = m^2)"
  hence "Suc n \<noteq> (floor_sqrt (Suc n))^2" by simp
  with floor_sqrt_power2_le[of "Suc n"]
    have "floor_sqrt (Suc n) \<le> floor_sqrt n" by (intro le_floor_sqrtI) linarith
  moreover have "floor_sqrt (Suc n) \<ge> floor_sqrt n"
    by (intro monoD[OF mono_floor_sqrt]) simp_all
  ultimately show ?thesis using asm by simp
qed

end
