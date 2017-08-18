(*  Title:      HOL/Proofs/Extraction/Euclid.thy
    Author:     Markus Wenzel, TU Muenchen
    Author:     Freek Wiedijk, Radboud University Nijmegen
    Author:     Stefan Berghofer, TU Muenchen
*)

section \<open>Euclid's theorem\<close>

theory Euclid
imports
  "HOL-Computational_Algebra.Primes"
  Util
  "HOL-Library.Old_Datatype"
  "HOL-Library.Code_Target_Numeral"
begin

text \<open>
  A constructive version of the proof of Euclid's theorem by
  Markus Wenzel and Freek Wiedijk @{cite "Wenzel-Wiedijk-JAR2002"}.
\<close>

lemma factor_greater_one1: "n = m * k \<Longrightarrow> m < n \<Longrightarrow> k < n \<Longrightarrow> Suc 0 < m"
  by (induct m) auto

lemma factor_greater_one2: "n = m * k \<Longrightarrow> m < n \<Longrightarrow> k < n \<Longrightarrow> Suc 0 < k"
  by (induct k) auto

lemma prod_mn_less_k: "0 < n \<Longrightarrow> 0 < k \<Longrightarrow> Suc 0 < m \<Longrightarrow> m * n = k \<Longrightarrow> n < k"
  by (induct m) auto

lemma prime_eq: "prime (p::nat) \<longleftrightarrow> 1 < p \<and> (\<forall>m. m dvd p \<longrightarrow> 1 < m \<longrightarrow> m = p)"
  apply (simp add: prime_nat_iff)
  apply (rule iffI)
  apply blast
  apply (erule conjE)
  apply (rule conjI)
  apply assumption
  apply (rule allI impI)+
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (case_tac "m = 0")
  apply simp
  apply (case_tac "m = Suc 0")
  apply simp
  apply simp
  done

lemma prime_eq': "prime (p::nat) \<longleftrightarrow> 1 < p \<and> (\<forall>m k. p = m * k \<longrightarrow> 1 < m \<longrightarrow> m = p)"
  by (simp add: prime_eq dvd_def HOL.all_simps [symmetric] del: HOL.all_simps)

lemma not_prime_ex_mk:
  assumes n: "Suc 0 < n"
  shows "(\<exists>m k. Suc 0 < m \<and> Suc 0 < k \<and> m < n \<and> k < n \<and> n = m * k) \<or> prime n"
proof -
  from nat_eq_dec have "(\<exists>m<n. n = m * k) \<or> \<not> (\<exists>m<n. n = m * k)" for k
    by (rule search)
  then have "(\<exists>k<n. \<exists>m<n. n = m * k) \<or> \<not> (\<exists>k<n. \<exists>m<n. n = m * k)"
    by (rule search)
  then show ?thesis
  proof
    assume "\<exists>k<n. \<exists>m<n. n = m * k"
    then obtain k m where k: "k<n" and m: "m<n" and nmk: "n = m * k"
      by iprover
    from nmk m k have "Suc 0 < m" by (rule factor_greater_one1)
    moreover from nmk m k have "Suc 0 < k" by (rule factor_greater_one2)
    ultimately show ?thesis using k m nmk by iprover
  next
    assume "\<not> (\<exists>k<n. \<exists>m<n. n = m * k)"
    then have A: "\<forall>k<n. \<forall>m<n. n \<noteq> m * k" by iprover
    have "\<forall>m k. n = m * k \<longrightarrow> Suc 0 < m \<longrightarrow> m = n"
    proof (intro allI impI)
      fix m k
      assume nmk: "n = m * k"
      assume m: "Suc 0 < m"
      from n m nmk have k: "0 < k"
        by (cases k) auto
      moreover from n have n: "0 < n" by simp
      moreover note m
      moreover from nmk have "m * k = n" by simp
      ultimately have kn: "k < n" by (rule prod_mn_less_k)
      show "m = n"
      proof (cases "k = Suc 0")
        case True
        with nmk show ?thesis by (simp only: mult_Suc_right)
      next
        case False
        from m have "0 < m" by simp
        moreover note n
        moreover from False n nmk k have "Suc 0 < k" by auto
        moreover from nmk have "k * m = n" by (simp only: ac_simps)
        ultimately have mn: "m < n" by (rule prod_mn_less_k)
        with kn A nmk show ?thesis by iprover
      qed
    qed
    with n have "prime n"
      by (simp only: prime_eq' One_nat_def simp_thms)
    then show ?thesis ..
  qed
qed

lemma dvd_factorial: "0 < m \<Longrightarrow> m \<le> n \<Longrightarrow> m dvd fact n"
proof (induct n rule: nat_induct)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from \<open>m \<le> Suc n\<close> show ?case
  proof (rule le_SucE)
    assume "m \<le> n"
    with \<open>0 < m\<close> have "m dvd fact n" by (rule Suc)
    then have "m dvd (fact n * Suc n)" by (rule dvd_mult2)
    then show ?thesis by (simp add: mult.commute)
  next
    assume "m = Suc n"
    then have "m dvd (fact n * Suc n)"
      by (auto intro: dvdI simp: ac_simps)
    then show ?thesis by (simp add: mult.commute)
  qed
qed

lemma dvd_prod [iff]: "n dvd (\<Prod>m::nat \<in># mset (n # ns). m)"
  by (simp add: prod_mset_Un)

definition all_prime :: "nat list \<Rightarrow> bool"
  where "all_prime ps \<longleftrightarrow> (\<forall>p\<in>set ps. prime p)"

lemma all_prime_simps:
  "all_prime []"
  "all_prime (p # ps) \<longleftrightarrow> prime p \<and> all_prime ps"
  by (simp_all add: all_prime_def)

lemma all_prime_append: "all_prime (ps @ qs) \<longleftrightarrow> all_prime ps \<and> all_prime qs"
  by (simp add: all_prime_def ball_Un)

lemma split_all_prime:
  assumes "all_prime ms" and "all_prime ns"
  shows "\<exists>qs. all_prime qs \<and>
    (\<Prod>m::nat \<in># mset qs. m) = (\<Prod>m::nat \<in># mset ms. m) * (\<Prod>m::nat \<in># mset ns. m)"
  (is "\<exists>qs. ?P qs \<and> ?Q qs")
proof -
  from assms have "all_prime (ms @ ns)"
    by (simp add: all_prime_append)
  moreover
  have "(\<Prod>m::nat \<in># mset (ms @ ns). m) = (\<Prod>m::nat \<in># mset ms. m) * (\<Prod>m::nat \<in># mset ns. m)"
    using assms by (simp add: prod_mset_Un)
  ultimately have "?P (ms @ ns) \<and> ?Q (ms @ ns)" ..
  then show ?thesis ..
qed

lemma all_prime_nempty_g_one:
  assumes "all_prime ps" and "ps \<noteq> []"
  shows "Suc 0 < (\<Prod>m::nat \<in># mset ps. m)"
  using \<open>ps \<noteq> []\<close> \<open>all_prime ps\<close>
  unfolding One_nat_def [symmetric]
  by (induct ps rule: list_nonempty_induct)
    (simp_all add: all_prime_simps prod_mset_Un prime_gt_1_nat less_1_mult del: One_nat_def)

lemma factor_exists: "Suc 0 < n \<Longrightarrow> (\<exists>ps. all_prime ps \<and> (\<Prod>m::nat \<in># mset ps. m) = n)"
proof (induct n rule: nat_wf_ind)
  case (1 n)
  from \<open>Suc 0 < n\<close>
  have "(\<exists>m k. Suc 0 < m \<and> Suc 0 < k \<and> m < n \<and> k < n \<and> n = m * k) \<or> prime n"
    by (rule not_prime_ex_mk)
  then show ?case
  proof
    assume "\<exists>m k. Suc 0 < m \<and> Suc 0 < k \<and> m < n \<and> k < n \<and> n = m * k"
    then obtain m k where m: "Suc 0 < m" and k: "Suc 0 < k" and mn: "m < n"
      and kn: "k < n" and nmk: "n = m * k"
      by iprover
    from mn and m have "\<exists>ps. all_prime ps \<and> (\<Prod>m::nat \<in># mset ps. m) = m"
      by (rule 1)
    then obtain ps1 where "all_prime ps1" and prod_ps1_m: "(\<Prod>m::nat \<in># mset ps1. m) = m"
      by iprover
    from kn and k have "\<exists>ps. all_prime ps \<and> (\<Prod>m::nat \<in># mset ps. m) = k"
      by (rule 1)
    then obtain ps2 where "all_prime ps2" and prod_ps2_k: "(\<Prod>m::nat \<in># mset ps2. m) = k"
      by iprover
    from \<open>all_prime ps1\<close> \<open>all_prime ps2\<close>
    have "\<exists>ps. all_prime ps \<and> (\<Prod>m::nat \<in># mset ps. m) =
      (\<Prod>m::nat \<in># mset ps1. m) * (\<Prod>m::nat \<in># mset ps2. m)"
      by (rule split_all_prime)
    with prod_ps1_m prod_ps2_k nmk show ?thesis by simp
  next
    assume "prime n" then have "all_prime [n]" by (simp add: all_prime_simps)
    moreover have "(\<Prod>m::nat \<in># mset [n]. m) = n" by (simp)
    ultimately have "all_prime [n] \<and> (\<Prod>m::nat \<in># mset [n]. m) = n" ..
    then show ?thesis ..
  qed
qed

lemma prime_factor_exists:
  assumes N: "(1::nat) < n"
  shows "\<exists>p. prime p \<and> p dvd n"
proof -
  from N obtain ps where "all_prime ps" and prod_ps: "n = (\<Prod>m::nat \<in># mset ps. m)"
    using factor_exists by simp iprover
  with N have "ps \<noteq> []"
    by (auto simp add: all_prime_nempty_g_one)
  then obtain p qs where ps: "ps = p # qs"
    by (cases ps) simp
  with \<open>all_prime ps\<close> have "prime p"
    by (simp add: all_prime_simps)
  moreover from \<open>all_prime ps\<close> ps prod_ps have "p dvd n"
    by (simp only: dvd_prod)
  ultimately show ?thesis by iprover
qed

text \<open>Euclid's theorem: there are infinitely many primes.\<close>

lemma Euclid: "\<exists>p::nat. prime p \<and> n < p"
proof -
  let ?k = "fact n + (1::nat)"
  have "1 < ?k" by simp
  then obtain p where prime: "prime p" and dvd: "p dvd ?k"
    using prime_factor_exists by iprover
  have "n < p"
  proof -
    have "\<not> p \<le> n"
    proof
      assume pn: "p \<le> n"
      from \<open>prime p\<close> have "0 < p" by (rule prime_gt_0_nat)
      then have "p dvd fact n" using pn by (rule dvd_factorial)
      with dvd have "p dvd ?k - fact n" by (rule dvd_diff_nat)
      then have "p dvd 1" by simp
      with prime show False by auto
    qed
    then show ?thesis by simp
  qed
  with prime show ?thesis by iprover
qed

extract Euclid

text \<open>
  The program extracted from the proof of Euclid's theorem looks as follows.
  @{thm [display] Euclid_def}
  The program corresponding to the proof of the factorization theorem is
  @{thm [display] factor_exists_def}
\<close>

instantiation nat :: default
begin

definition "default = (0::nat)"

instance ..

end

instantiation list :: (type) default
begin

definition "default = []"

instance ..

end

primrec iterate :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list"
where
  "iterate 0 f x = []"
| "iterate (Suc n) f x = (let y = f x in y # iterate n f y)"

lemma "factor_exists 1007 = [53, 19]" by eval
lemma "factor_exists 567 = [7, 3, 3, 3, 3]" by eval
lemma "factor_exists 345 = [23, 5, 3]" by eval
lemma "factor_exists 999 = [37, 3, 3, 3]" by eval
lemma "factor_exists 876 = [73, 3, 2, 2]" by eval

lemma "iterate 4 Euclid 0 = [2, 3, 7, 71]" by eval

end
