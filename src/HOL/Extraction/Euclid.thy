(*  Title:      HOL/Extraction/Euclid.thy
    Author:     Markus Wenzel, TU Muenchen
    Author:     Freek Wiedijk, Radboud University Nijmegen
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* Euclid's theorem *}

theory Euclid
imports "~~/src/HOL/Old_Number_Theory/Factorization" Util Efficient_Nat
begin

text {*
A constructive version of the proof of Euclid's theorem by
Markus Wenzel and Freek Wiedijk \cite{Wenzel-Wiedijk-JAR2002}.
*}

lemma prime_eq: "prime p = (1 < p \<and> (\<forall>m. m dvd p \<longrightarrow> 1 < m \<longrightarrow> m = p))"
  apply (simp add: prime_def)
  apply (rule iffI)
  apply blast
  apply (erule conjE)
  apply (rule conjI)
  apply assumption
  apply (rule allI impI)+
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (case_tac "m=0")
  apply simp
  apply (case_tac "m=Suc 0")
  apply simp
  apply simp
  done

lemma prime_eq': "prime p = (1 < p \<and> (\<forall>m k. p = m * k \<longrightarrow> 1 < m \<longrightarrow> m = p))"
  by (simp add: prime_eq dvd_def all_simps [symmetric] del: all_simps)

lemma factor_greater_one1: "n = m * k \<Longrightarrow> m < n \<Longrightarrow> k < n \<Longrightarrow> Suc 0 < m"
  by (induct m) auto

lemma factor_greater_one2: "n = m * k \<Longrightarrow> m < n \<Longrightarrow> k < n \<Longrightarrow> Suc 0 < k"
  by (induct k) auto

lemma not_prime_ex_mk:
  assumes n: "Suc 0 < n"
  shows "(\<exists>m k. Suc 0 < m \<and> Suc 0 < k \<and> m < n \<and> k < n \<and> n = m * k) \<or> prime n"
proof -
  {
    fix k
    from nat_eq_dec
    have "(\<exists>m<n. n = m * k) \<or> \<not> (\<exists>m<n. n = m * k)"
      by (rule search)
  }
  hence "(\<exists>k<n. \<exists>m<n. n = m * k) \<or> \<not> (\<exists>k<n. \<exists>m<n. n = m * k)"
    by (rule search)
  thus ?thesis
  proof
    assume "\<exists>k<n. \<exists>m<n. n = m * k"
    then obtain k m where k: "k<n" and m: "m<n" and nmk: "n = m * k"
      by iprover
    from nmk m k have "Suc 0 < m" by (rule factor_greater_one1)
    moreover from nmk m k have "Suc 0 < k" by (rule factor_greater_one2)
    ultimately show ?thesis using k m nmk by iprover
  next
    assume "\<not> (\<exists>k<n. \<exists>m<n. n = m * k)"
    hence A: "\<forall>k<n. \<forall>m<n. n \<noteq> m * k" by iprover
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
        moreover from nmk have "k * m = n" by (simp only: mult_ac)
        ultimately have mn: "m < n" by (rule prod_mn_less_k)
        with kn A nmk show ?thesis by iprover
      qed
    qed
    with n have "prime n"
      by (simp only: prime_eq' One_nat_def simp_thms)
    thus ?thesis ..
  qed
qed

lemma factor_exists: "Suc 0 < n \<Longrightarrow> (\<exists>l. primel l \<and> prod l = n)"
proof (induct n rule: nat_wf_ind)
  case (1 n)
  from `Suc 0 < n`
  have "(\<exists>m k. Suc 0 < m \<and> Suc 0 < k \<and> m < n \<and> k < n \<and> n = m * k) \<or> prime n"
    by (rule not_prime_ex_mk)
  then show ?case
  proof 
    assume "\<exists>m k. Suc 0 < m \<and> Suc 0 < k \<and> m < n \<and> k < n \<and> n = m * k"
    then obtain m k where m: "Suc 0 < m" and k: "Suc 0 < k" and mn: "m < n"
      and kn: "k < n" and nmk: "n = m * k" by iprover
    from mn and m have "\<exists>l. primel l \<and> prod l = m" by (rule 1)
    then obtain l1 where primel_l1: "primel l1" and prod_l1_m: "prod l1 = m"
      by iprover
    from kn and k have "\<exists>l. primel l \<and> prod l = k" by (rule 1)
    then obtain l2 where primel_l2: "primel l2" and prod_l2_k: "prod l2 = k"
      by iprover
    from primel_l1 primel_l2
    have "\<exists>l. primel l \<and> prod l = prod l1 * prod l2"
      by (rule split_primel)
    with prod_l1_m prod_l2_k nmk show ?thesis by simp
  next
    assume "prime n"
    hence "primel [n] \<and> prod [n] = n" by (rule prime_primel)
    thus ?thesis ..
  qed
qed

lemma dvd_prod [iff]: "n dvd prod (n # ns)"
  by simp

primrec fact :: "nat \<Rightarrow> nat"    ("(_!)" [1000] 999)
where
    "0! = 1"
  | "(Suc n)! = n! * Suc n"

lemma fact_greater_0 [iff]: "0 < n!"
  by (induct n) simp_all

lemma dvd_factorial: "0 < m \<Longrightarrow> m \<le> n \<Longrightarrow> m dvd n!"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from `m \<le> Suc n` show ?case
  proof (rule le_SucE)
    assume "m \<le> n"
    with `0 < m` have "m dvd n!" by (rule Suc)
    then have "m dvd (n! * Suc n)" by (rule dvd_mult2)
    then show ?thesis by simp
  next
    assume "m = Suc n"
    then have "m dvd (n! * Suc n)"
      by (auto intro: dvdI simp: mult_ac)
    then show ?thesis by simp
  qed
qed

lemma prime_factor_exists:
  assumes N: "(1::nat) < n"
  shows "\<exists>p. prime p \<and> p dvd n"
proof -
  from N obtain l where primel_l: "primel l"
    and prod_l: "n = prod l" using factor_exists
    by simp iprover
  from prems have "l \<noteq> []"
    by (auto simp add: primel_nempty_g_one)
  then obtain x xs where l: "l = x # xs"
    by (cases l) simp
  from primel_l l have "prime x" by (simp add: primel_hd_tl)
  moreover from primel_l l prod_l
  have "x dvd n" by (simp only: dvd_prod)
  ultimately show ?thesis by iprover
qed

text {*
Euclid's theorem: there are infinitely many primes.
*}

lemma Euclid: "\<exists>p. prime p \<and> n < p"
proof -
  let ?k = "n! + 1"
  have "1 < n! + 1" by simp
  then obtain p where prime: "prime p" and dvd: "p dvd ?k" using prime_factor_exists by iprover
  have "n < p"
  proof -
    have "\<not> p \<le> n"
    proof
      assume pn: "p \<le> n"
      from `prime p` have "0 < p" by (rule prime_g_zero)
      then have "p dvd n!" using pn by (rule dvd_factorial)
      with dvd have "p dvd ?k - n!" by (rule dvd_diff_nat)
      then have "p dvd 1" by simp
      with prime show False using prime_nd_one by auto
    qed
    then show ?thesis by simp
  qed
  with prime show ?thesis by iprover
qed

extract Euclid

text {*
The program extracted from the proof of Euclid's theorem looks as follows.
@{thm [display] Euclid_def}
The program corresponding to the proof of the factorization theorem is
@{thm [display] factor_exists_def}
*}

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

consts_code
  default ("(error \"default\")")

lemma "factor_exists 1007 = [53, 19]" by evaluation
lemma "factor_exists 1007 = [53, 19]" by eval

lemma "factor_exists 567 = [7, 3, 3, 3, 3]" by evaluation
lemma "factor_exists 567 = [7, 3, 3, 3, 3]" by eval

lemma "factor_exists 345 = [23, 5, 3]" by evaluation
lemma "factor_exists 345 = [23, 5, 3]" by eval

lemma "factor_exists 999 = [37, 3, 3, 3]" by evaluation
lemma "factor_exists 999 = [37, 3, 3, 3]" by eval

lemma "factor_exists 876 = [73, 3, 2, 2]" by evaluation
lemma "factor_exists 876 = [73, 3, 2, 2]" by eval

primrec iterate :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "iterate 0 f x = []"
  | "iterate (Suc n) f x = (let y = f x in y # iterate n f y)"

lemma "iterate 4 Euclid 0 = [2, 3, 7, 71]" by evaluation
lemma "iterate 4 Euclid 0 = [2, 3, 7, 71]" by eval

end
