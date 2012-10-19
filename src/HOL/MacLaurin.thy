(*  Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
    Conversion of Mac Laurin to Isar by Lukas Bulwahn and Bernhard Häupler, 2005
*)

header{*MacLaurin Series*}

theory MacLaurin
imports Transcendental
begin

subsection{*Maclaurin's Theorem with Lagrange Form of Remainder*}

text{*This is a very long, messy proof even now that it's been broken down
into lemmas.*}

lemma Maclaurin_lemma:
    "0 < h ==>
     \<exists>B. f h = (\<Sum>m=0..<n. (j m / real (fact m)) * (h^m)) +
               (B * ((h^n) / real(fact n)))"
by (rule exI[where x = "(f h - (\<Sum>m=0..<n. (j m / real (fact m)) * h^m)) *
                 real(fact n) / (h^n)"]) simp

lemma eq_diff_eq': "(x = y - z) = (y = x + (z::real))"
by arith

lemma fact_diff_Suc [rule_format]:
  "n < Suc m ==> fact (Suc m - n) = (Suc m - n) * fact (m - n)"
  by (subst fact_reduce_nat, auto)

lemma Maclaurin_lemma2:
  fixes B
  assumes DERIV : "\<forall>m t. m < n \<and> 0\<le>t \<and> t\<le>h \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
    and INIT : "n = Suc k"
  defines "difg \<equiv> (\<lambda>m t. diff m t - ((\<Sum>p = 0..<n - m. diff (m + p) 0 / real (fact p) * t ^ p) +
    B * (t ^ (n - m) / real (fact (n - m)))))" (is "difg \<equiv> (\<lambda>m t. diff m t - ?difg m t)")
  shows "\<forall>m t. m < n & 0 \<le> t & t \<le> h --> DERIV (difg m) t :> difg (Suc m) t"
proof (rule allI impI)+
  fix m t assume INIT2: "m < n & 0 \<le> t & t \<le> h"
  have "DERIV (difg m) t :> diff (Suc m) t -
    ((\<Sum>x = 0..<n - m. real x * t ^ (x - Suc 0) * diff (m + x) 0 / real (fact x)) +
     real (n - m) * t ^ (n - Suc m) * B / real (fact (n - m)))" unfolding difg_def
    by (auto intro!: DERIV_intros DERIV[rule_format, OF INIT2])
      moreover
  from INIT2 have intvl: "{..<n - m} = insert 0 (Suc ` {..<n - Suc m})" and "0 < n - m"
    unfolding atLeast0LessThan[symmetric] by auto
  have "(\<Sum>x = 0..<n - m. real x * t ^ (x - Suc 0) * diff (m + x) 0 / real (fact x)) =
      (\<Sum>x = 0..<n - Suc m. real (Suc x) * t ^ x * diff (Suc m + x) 0 / real (fact (Suc x)))"
    unfolding intvl atLeast0LessThan by (subst setsum.insert) (auto simp: setsum.reindex)
  moreover
  have fact_neq_0: "\<And>x::nat. real (fact x) + real x * real (fact x) \<noteq> 0"
    by (metis fact_gt_zero_nat not_add_less1 real_of_nat_add real_of_nat_mult real_of_nat_zero_iff)
  have "\<And>x. real (Suc x) * t ^ x * diff (Suc m + x) 0 / real (fact (Suc x)) =
      diff (Suc m + x) 0 * t^x / real (fact x)"
    by (auto simp: field_simps real_of_nat_Suc fact_neq_0 intro!: nonzero_divide_eq_eq[THEN iffD2])
  moreover
  have "real (n - m) * t ^ (n - Suc m) * B / real (fact (n - m)) =
      B * (t ^ (n - Suc m) / real (fact (n - Suc m)))"
    using `0 < n - m` by (simp add: fact_reduce_nat)
  ultimately show "DERIV (difg m) t :> difg (Suc m) t"
    unfolding difg_def by simp
qed

lemma Maclaurin:
  assumes h: "0 < h"
  assumes n: "0 < n"
  assumes diff_0: "diff 0 = f"
  assumes diff_Suc:
    "\<forall>m t. m < n & 0 \<le> t & t \<le> h --> DERIV (diff m) t :> diff (Suc m) t"
  shows
    "\<exists>t. 0 < t & t < h &
              f h =
              setsum (%m. (diff m 0 / real (fact m)) * h ^ m) {0..<n} +
              (diff n t / real (fact n)) * h ^ n"
proof -
  from n obtain m where m: "n = Suc m"
    by (cases n) (simp add: n)

  obtain B where f_h: "f h =
        (\<Sum>m = 0..<n. diff m (0\<Colon>real) / real (fact m) * h ^ m) +
        B * (h ^ n / real (fact n))"
    using Maclaurin_lemma [OF h] ..

  def g \<equiv> "(\<lambda>t. f t -
    (setsum (\<lambda>m. (diff m 0 / real(fact m)) * t^m) {0..<n}
      + (B * (t^n / real(fact n)))))"

  have g2: "g 0 = 0 & g h = 0"
    apply (simp add: m f_h g_def del: setsum_op_ivl_Suc)
    apply (cut_tac n = m and k = "Suc 0" in sumr_offset2)
    apply (simp add: eq_diff_eq' diff_0 del: setsum_op_ivl_Suc)
    done

  def difg \<equiv> "(%m t. diff m t -
    (setsum (%p. (diff (m + p) 0 / real (fact p)) * (t ^ p)) {0..<n-m}
      + (B * ((t ^ (n - m)) / real (fact (n - m))))))"

  have difg_0: "difg 0 = g"
    unfolding difg_def g_def by (simp add: diff_0)

  have difg_Suc: "\<forall>(m\<Colon>nat) t\<Colon>real.
        m < n \<and> (0\<Colon>real) \<le> t \<and> t \<le> h \<longrightarrow> DERIV (difg m) t :> difg (Suc m) t"
    using diff_Suc m unfolding difg_def by (rule Maclaurin_lemma2)

  have difg_eq_0: "\<forall>m. m < n --> difg m 0 = 0"
    apply clarify
    apply (simp add: m difg_def)
    apply (frule less_iff_Suc_add [THEN iffD1], clarify)
    apply (simp del: setsum_op_ivl_Suc)
    apply (insert sumr_offset4 [of "Suc 0"])
    apply (simp del: setsum_op_ivl_Suc fact_Suc)
    done

  have isCont_difg: "\<And>m x. \<lbrakk>m < n; 0 \<le> x; x \<le> h\<rbrakk> \<Longrightarrow> isCont (difg m) x"
    by (rule DERIV_isCont [OF difg_Suc [rule_format]]) simp

  have differentiable_difg:
    "\<And>m x. \<lbrakk>m < n; 0 \<le> x; x \<le> h\<rbrakk> \<Longrightarrow> difg m differentiable x"
    by (rule differentiableI [OF difg_Suc [rule_format]]) simp

  have difg_Suc_eq_0: "\<And>m t. \<lbrakk>m < n; 0 \<le> t; t \<le> h; DERIV (difg m) t :> 0\<rbrakk>
        \<Longrightarrow> difg (Suc m) t = 0"
    by (rule DERIV_unique [OF difg_Suc [rule_format]]) simp

  have "m < n" using m by simp

  have "\<exists>t. 0 < t \<and> t < h \<and> DERIV (difg m) t :> 0"
  using `m < n`
  proof (induct m)
    case 0
    show ?case
    proof (rule Rolle)
      show "0 < h" by fact
      show "difg 0 0 = difg 0 h" by (simp add: difg_0 g2)
      show "\<forall>x. 0 \<le> x \<and> x \<le> h \<longrightarrow> isCont (difg (0\<Colon>nat)) x"
        by (simp add: isCont_difg n)
      show "\<forall>x. 0 < x \<and> x < h \<longrightarrow> difg (0\<Colon>nat) differentiable x"
        by (simp add: differentiable_difg n)
    qed
  next
    case (Suc m')
    hence "\<exists>t. 0 < t \<and> t < h \<and> DERIV (difg m') t :> 0" by simp
    then obtain t where t: "0 < t" "t < h" "DERIV (difg m') t :> 0" by fast
    have "\<exists>t'. 0 < t' \<and> t' < t \<and> DERIV (difg (Suc m')) t' :> 0"
    proof (rule Rolle)
      show "0 < t" by fact
      show "difg (Suc m') 0 = difg (Suc m') t"
        using t `Suc m' < n` by (simp add: difg_Suc_eq_0 difg_eq_0)
      show "\<forall>x. 0 \<le> x \<and> x \<le> t \<longrightarrow> isCont (difg (Suc m')) x"
        using `t < h` `Suc m' < n` by (simp add: isCont_difg)
      show "\<forall>x. 0 < x \<and> x < t \<longrightarrow> difg (Suc m') differentiable x"
        using `t < h` `Suc m' < n` by (simp add: differentiable_difg)
    qed
    thus ?case
      using `t < h` by auto
  qed

  then obtain t where "0 < t" "t < h" "DERIV (difg m) t :> 0" by fast

  hence "difg (Suc m) t = 0"
    using `m < n` by (simp add: difg_Suc_eq_0)

  show ?thesis
  proof (intro exI conjI)
    show "0 < t" by fact
    show "t < h" by fact
    show "f h =
      (\<Sum>m = 0..<n. diff m 0 / real (fact m) * h ^ m) +
      diff n t / real (fact n) * h ^ n"
      using `difg (Suc m) t = 0`
      by (simp add: m f_h difg_def del: fact_Suc)
  qed
qed

lemma Maclaurin_objl:
  "0 < h & n>0 & diff 0 = f &
  (\<forall>m t. m < n & 0 \<le> t & t \<le> h --> DERIV (diff m) t :> diff (Suc m) t)
   --> (\<exists>t. 0 < t & t < h &
            f h = (\<Sum>m=0..<n. diff m 0 / real (fact m) * h ^ m) +
                  diff n t / real (fact n) * h ^ n)"
by (blast intro: Maclaurin)


lemma Maclaurin2:
  assumes INIT1: "0 < h " and INIT2: "diff 0 = f"
  and DERIV: "\<forall>m t.
  m < n & 0 \<le> t & t \<le> h --> DERIV (diff m) t :> diff (Suc m) t"
  shows "\<exists>t. 0 < t \<and> t \<le> h \<and> f h =
  (\<Sum>m=0..<n. diff m 0 / real (fact m) * h ^ m) +
  diff n t / real (fact n) * h ^ n"
proof (cases "n")
  case 0 with INIT1 INIT2 show ?thesis by fastforce
next
  case Suc
  hence "n > 0" by simp
  from INIT1 this INIT2 DERIV have "\<exists>t>0. t < h \<and>
    f h =
    (\<Sum>m = 0..<n. diff m 0 / real (fact m) * h ^ m) + diff n t / real (fact n) * h ^ n"
    by (rule Maclaurin)
  thus ?thesis by fastforce
qed

lemma Maclaurin2_objl:
     "0 < h & diff 0 = f &
       (\<forall>m t.
          m < n & 0 \<le> t & t \<le> h --> DERIV (diff m) t :> diff (Suc m) t)
    --> (\<exists>t. 0 < t &
              t \<le> h &
              f h =
              (\<Sum>m=0..<n. diff m 0 / real (fact m) * h ^ m) +
              diff n t / real (fact n) * h ^ n)"
by (blast intro: Maclaurin2)

lemma Maclaurin_minus:
  assumes "h < 0" "0 < n" "diff 0 = f"
  and DERIV: "\<forall>m t. m < n & h \<le> t & t \<le> 0 --> DERIV (diff m) t :> diff (Suc m) t"
  shows "\<exists>t. h < t & t < 0 &
         f h = (\<Sum>m=0..<n. diff m 0 / real (fact m) * h ^ m) +
         diff n t / real (fact n) * h ^ n"
proof -
  txt "Transform @{text ABL'} into @{text DERIV_intros} format."
  note DERIV' = DERIV_chain'[OF _ DERIV[rule_format], THEN DERIV_cong]
  from assms
  have "\<exists>t>0. t < - h \<and>
    f (- (- h)) =
    (\<Sum>m = 0..<n.
    (- 1) ^ m * diff m (- 0) / real (fact m) * (- h) ^ m) +
    (- 1) ^ n * diff n (- t) / real (fact n) * (- h) ^ n"
    by (intro Maclaurin) (auto intro!: DERIV_intros DERIV')
  then guess t ..
  moreover
  have "-1 ^ n * diff n (- t) * (- h) ^ n / real (fact n) = diff n (- t) * h ^ n / real (fact n)"
    by (auto simp add: power_mult_distrib[symmetric])
  moreover
  have "(SUM m = 0..<n. -1 ^ m * diff m 0 * (- h) ^ m / real (fact m)) = (SUM m = 0..<n. diff m 0 * h ^ m / real (fact m))"
    by (auto intro: setsum_cong simp add: power_mult_distrib[symmetric])
  ultimately have " h < - t \<and>
    - t < 0 \<and>
    f h =
    (\<Sum>m = 0..<n. diff m 0 / real (fact m) * h ^ m) + diff n (- t) / real (fact n) * h ^ n"
    by auto
  thus ?thesis ..
qed

lemma Maclaurin_minus_objl:
     "(h < 0 & n > 0 & diff 0 = f &
       (\<forall>m t.
          m < n & h \<le> t & t \<le> 0 --> DERIV (diff m) t :> diff (Suc m) t))
    --> (\<exists>t. h < t &
              t < 0 &
              f h =
              (\<Sum>m=0..<n. diff m 0 / real (fact m) * h ^ m) +
              diff n t / real (fact n) * h ^ n)"
by (blast intro: Maclaurin_minus)


subsection{*More Convenient "Bidirectional" Version.*}

(* not good for PVS sin_approx, cos_approx *)

lemma Maclaurin_bi_le_lemma [rule_format]:
  "n>0 \<longrightarrow>
   diff 0 0 =
   (\<Sum>m = 0..<n. diff m 0 * 0 ^ m / real (fact m)) +
   diff n 0 * 0 ^ n / real (fact n)"
by (induct "n") auto

lemma Maclaurin_bi_le:
   assumes "diff 0 = f"
   and DERIV : "\<forall>m t. m < n & abs t \<le> abs x --> DERIV (diff m) t :> diff (Suc m) t"
   shows "\<exists>t. abs t \<le> abs x &
              f x =
              (\<Sum>m=0..<n. diff m 0 / real (fact m) * x ^ m) +
     diff n t / real (fact n) * x ^ n" (is "\<exists>t. _ \<and> f x = ?f x t")
proof cases
  assume "n = 0" with `diff 0 = f` show ?thesis by force
next
  assume "n \<noteq> 0"
  show ?thesis
  proof (cases rule: linorder_cases)
    assume "x = 0" with `n \<noteq> 0` `diff 0 = f` DERIV
    have "\<bar>0\<bar> \<le> \<bar>x\<bar> \<and> f x = ?f x 0" by (force simp add: Maclaurin_bi_le_lemma)
    thus ?thesis ..
  next
    assume "x < 0"
    with `n \<noteq> 0` DERIV
    have "\<exists>t>x. t < 0 \<and> diff 0 x = ?f x t" by (intro Maclaurin_minus) auto
    then guess t ..
    with `x < 0` `diff 0 = f` have "\<bar>t\<bar> \<le> \<bar>x\<bar> \<and> f x = ?f x t" by simp
    thus ?thesis ..
  next
    assume "x > 0"
    with `n \<noteq> 0` `diff 0 = f` DERIV
    have "\<exists>t>0. t < x \<and> diff 0 x = ?f x t" by (intro Maclaurin) auto
    then guess t ..
    with `x > 0` `diff 0 = f` have "\<bar>t\<bar> \<le> \<bar>x\<bar> \<and> f x = ?f x t" by simp
    thus ?thesis ..
  qed
qed

lemma Maclaurin_all_lt:
  assumes INIT1: "diff 0 = f" and INIT2: "0 < n" and INIT3: "x \<noteq> 0"
  and DERIV: "\<forall>m x. DERIV (diff m) x :> diff(Suc m) x"
  shows "\<exists>t. 0 < abs t & abs t < abs x & f x =
    (\<Sum>m=0..<n. (diff m 0 / real (fact m)) * x ^ m) +
                (diff n t / real (fact n)) * x ^ n" (is "\<exists>t. _ \<and> _ \<and> f x = ?f x t")
proof (cases rule: linorder_cases)
  assume "x = 0" with INIT3 show "?thesis"..
next
  assume "x < 0"
  with assms have "\<exists>t>x. t < 0 \<and> f x = ?f x t" by (intro Maclaurin_minus) auto
  then guess t ..
  with `x < 0` have "0 < \<bar>t\<bar> \<and> \<bar>t\<bar> < \<bar>x\<bar> \<and> f x = ?f x t" by simp
  thus ?thesis ..
next
  assume "x > 0"
  with assms have "\<exists>t>0. t < x \<and> f x = ?f x t " by (intro Maclaurin) auto
  then guess t ..
  with `x > 0` have "0 < \<bar>t\<bar> \<and> \<bar>t\<bar> < \<bar>x\<bar> \<and> f x = ?f x t" by simp
  thus ?thesis ..
qed


lemma Maclaurin_all_lt_objl:
     "diff 0 = f &
      (\<forall>m x. DERIV (diff m) x :> diff(Suc m) x) &
      x ~= 0 & n > 0
      --> (\<exists>t. 0 < abs t & abs t < abs x &
               f x = (\<Sum>m=0..<n. (diff m 0 / real (fact m)) * x ^ m) +
                     (diff n t / real (fact n)) * x ^ n)"
by (blast intro: Maclaurin_all_lt)

lemma Maclaurin_zero [rule_format]:
     "x = (0::real)
      ==> n \<noteq> 0 -->
          (\<Sum>m=0..<n. (diff m (0::real) / real (fact m)) * x ^ m) =
          diff 0 0"
by (induct n, auto)


lemma Maclaurin_all_le:
  assumes INIT: "diff 0 = f"
  and DERIV: "\<forall>m x. DERIV (diff m) x :> diff (Suc m) x"
  shows "\<exists>t. abs t \<le> abs x & f x =
    (\<Sum>m=0..<n. (diff m 0 / real (fact m)) * x ^ m) +
    (diff n t / real (fact n)) * x ^ n" (is "\<exists>t. _ \<and> f x = ?f x t")
proof cases
  assume "n = 0" with INIT show ?thesis by force
  next
  assume "n \<noteq> 0"
  show ?thesis
  proof cases
    assume "x = 0"
    with `n \<noteq> 0` have "(\<Sum>m = 0..<n. diff m 0 / real (fact m) * x ^ m) = diff 0 0"
      by (intro Maclaurin_zero) auto
    with INIT `x = 0` `n \<noteq> 0` have " \<bar>0\<bar> \<le> \<bar>x\<bar> \<and> f x = ?f x 0" by force
    thus ?thesis ..
  next
    assume "x \<noteq> 0"
    with INIT `n \<noteq> 0` DERIV have "\<exists>t. 0 < \<bar>t\<bar> \<and> \<bar>t\<bar> < \<bar>x\<bar> \<and> f x = ?f x t"
      by (intro Maclaurin_all_lt) auto
    then guess t ..
    hence "\<bar>t\<bar> \<le> \<bar>x\<bar> \<and> f x = ?f x t" by simp
    thus ?thesis ..
  qed
qed

lemma Maclaurin_all_le_objl: "diff 0 = f &
      (\<forall>m x. DERIV (diff m) x :> diff (Suc m) x)
      --> (\<exists>t. abs t \<le> abs x &
              f x = (\<Sum>m=0..<n. (diff m 0 / real (fact m)) * x ^ m) +
                    (diff n t / real (fact n)) * x ^ n)"
by (blast intro: Maclaurin_all_le)


subsection{*Version for Exponential Function*}

lemma Maclaurin_exp_lt: "[| x ~= 0; n > 0 |]
      ==> (\<exists>t. 0 < abs t &
                abs t < abs x &
                exp x = (\<Sum>m=0..<n. (x ^ m) / real (fact m)) +
                        (exp t / real (fact n)) * x ^ n)"
by (cut_tac diff = "%n. exp" and f = exp and x = x and n = n in Maclaurin_all_lt_objl, auto)


lemma Maclaurin_exp_le:
     "\<exists>t. abs t \<le> abs x &
            exp x = (\<Sum>m=0..<n. (x ^ m) / real (fact m)) +
                       (exp t / real (fact n)) * x ^ n"
by (cut_tac diff = "%n. exp" and f = exp and x = x and n = n in Maclaurin_all_le_objl, auto)


subsection{*Version for Sine Function*}

lemma mod_exhaust_less_4:
  "m mod 4 = 0 | m mod 4 = 1 | m mod 4 = 2 | m mod 4 = (3::nat)"
by auto

lemma Suc_Suc_mult_two_diff_two [rule_format, simp]:
  "n\<noteq>0 --> Suc (Suc (2 * n - 2)) = 2*n"
by (induct "n", auto)

lemma lemma_Suc_Suc_4n_diff_2 [rule_format, simp]:
  "n\<noteq>0 --> Suc (Suc (4*n - 2)) = 4*n"
by (induct "n", auto)

lemma Suc_mult_two_diff_one [rule_format, simp]:
  "n\<noteq>0 --> Suc (2 * n - 1) = 2*n"
by (induct "n", auto)


text{*It is unclear why so many variant results are needed.*}

lemma sin_expansion_lemma:
     "sin (x + real (Suc m) * pi / 2) =
      cos (x + real (m) * pi / 2)"
by (simp only: cos_add sin_add real_of_nat_Suc add_divide_distrib distrib_right, auto)

lemma Maclaurin_sin_expansion2:
     "\<exists>t. abs t \<le> abs x &
       sin x =
       (\<Sum>m=0..<n. sin_coeff m * x ^ m)
      + ((sin(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = sin and n = n and x = x
        and diff = "%n x. sin (x + 1/2*real n * pi)" in Maclaurin_all_lt_objl)
apply safe
apply (simp (no_asm))
apply (simp (no_asm) add: sin_expansion_lemma)
apply (force intro!: DERIV_intros)
apply (subst (asm) setsum_0', clarify, case_tac "a", simp, simp)
apply (cases n, simp, simp)
apply (rule ccontr, simp)
apply (drule_tac x = x in spec, simp)
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: sin_coeff_def sin_zero_iff odd_Suc_mult_two_ex)
done

lemma Maclaurin_sin_expansion:
     "\<exists>t. sin x =
       (\<Sum>m=0..<n. sin_coeff m * x ^ m)
      + ((sin(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (insert Maclaurin_sin_expansion2 [of x n])
apply (blast intro: elim:)
done

lemma Maclaurin_sin_expansion3:
     "[| n > 0; 0 < x |] ==>
       \<exists>t. 0 < t & t < x &
       sin x =
       (\<Sum>m=0..<n. sin_coeff m * x ^ m)
      + ((sin(t + 1/2 * real(n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = sin and n = n and h = x and diff = "%n x. sin (x + 1/2*real (n) *pi)" in Maclaurin_objl)
apply safe
apply simp
apply (simp (no_asm) add: sin_expansion_lemma)
apply (force intro!: DERIV_intros)
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: sin_coeff_def sin_zero_iff odd_Suc_mult_two_ex)
done

lemma Maclaurin_sin_expansion4:
     "0 < x ==>
       \<exists>t. 0 < t & t \<le> x &
       sin x =
       (\<Sum>m=0..<n. sin_coeff m * x ^ m)
      + ((sin(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = sin and n = n and h = x and diff = "%n x. sin (x + 1/2*real (n) *pi)" in Maclaurin2_objl)
apply safe
apply simp
apply (simp (no_asm) add: sin_expansion_lemma)
apply (force intro!: DERIV_intros)
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: sin_coeff_def sin_zero_iff odd_Suc_mult_two_ex)
done


subsection{*Maclaurin Expansion for Cosine Function*}

lemma sumr_cos_zero_one [simp]:
  "(\<Sum>m=0..<(Suc n). cos_coeff m * 0 ^ m) = 1"
by (induct "n", auto)

lemma cos_expansion_lemma:
  "cos (x + real(Suc m) * pi / 2) = -sin (x + real m * pi / 2)"
by (simp only: cos_add sin_add real_of_nat_Suc distrib_right add_divide_distrib, auto)

lemma Maclaurin_cos_expansion:
     "\<exists>t. abs t \<le> abs x &
       cos x =
       (\<Sum>m=0..<n. cos_coeff m * x ^ m)
      + ((cos(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = cos and n = n and x = x and diff = "%n x. cos (x + 1/2*real (n) *pi)" in Maclaurin_all_lt_objl)
apply safe
apply (simp (no_asm))
apply (simp (no_asm) add: cos_expansion_lemma)
apply (case_tac "n", simp)
apply (simp del: setsum_op_ivl_Suc)
apply (rule ccontr, simp)
apply (drule_tac x = x in spec, simp)
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: cos_coeff_def cos_zero_iff even_mult_two_ex)
done

lemma Maclaurin_cos_expansion2:
     "[| 0 < x; n > 0 |] ==>
       \<exists>t. 0 < t & t < x &
       cos x =
       (\<Sum>m=0..<n. cos_coeff m * x ^ m)
      + ((cos(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = cos and n = n and h = x and diff = "%n x. cos (x + 1/2*real (n) *pi)" in Maclaurin_objl)
apply safe
apply simp
apply (simp (no_asm) add: cos_expansion_lemma)
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: cos_coeff_def cos_zero_iff even_mult_two_ex)
done

lemma Maclaurin_minus_cos_expansion:
     "[| x < 0; n > 0 |] ==>
       \<exists>t. x < t & t < 0 &
       cos x =
       (\<Sum>m=0..<n. cos_coeff m * x ^ m)
      + ((cos(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = cos and n = n and h = x and diff = "%n x. cos (x + 1/2*real (n) *pi)" in Maclaurin_minus_objl)
apply safe
apply simp
apply (simp (no_asm) add: cos_expansion_lemma)
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: cos_coeff_def cos_zero_iff even_mult_two_ex)
done

(* ------------------------------------------------------------------------- *)
(* Version for ln(1 +/- x). Where is it??                                    *)
(* ------------------------------------------------------------------------- *)

lemma sin_bound_lemma:
    "[|x = y; abs u \<le> (v::real) |] ==> \<bar>(x + u) - y\<bar> \<le> v"
by auto

lemma Maclaurin_sin_bound:
  "abs(sin x - (\<Sum>m=0..<n. sin_coeff m * x ^ m))
  \<le> inverse(real (fact n)) * \<bar>x\<bar> ^ n"
proof -
  have "!! x (y::real). x \<le> 1 \<Longrightarrow> 0 \<le> y \<Longrightarrow> x * y \<le> 1 * y"
    by (rule_tac mult_right_mono,simp_all)
  note est = this[simplified]
  let ?diff = "\<lambda>(n::nat) x. if n mod 4 = 0 then sin(x) else if n mod 4 = 1 then cos(x) else if n mod 4 = 2 then -sin(x) else -cos(x)"
  have diff_0: "?diff 0 = sin" by simp
  have DERIV_diff: "\<forall>m x. DERIV (?diff m) x :> ?diff (Suc m) x"
    apply (clarify)
    apply (subst (1 2 3) mod_Suc_eq_Suc_mod)
    apply (cut_tac m=m in mod_exhaust_less_4)
    apply (safe, auto intro!: DERIV_intros)
    done
  from Maclaurin_all_le [OF diff_0 DERIV_diff]
  obtain t where t1: "\<bar>t\<bar> \<le> \<bar>x\<bar>" and
    t2: "sin x = (\<Sum>m = 0..<n. ?diff m 0 / real (fact m) * x ^ m) +
      ?diff n t / real (fact n) * x ^ n" by fast
  have diff_m_0:
    "\<And>m. ?diff m 0 = (if even m then 0
         else -1 ^ ((m - Suc 0) div 2))"
    apply (subst even_even_mod_4_iff)
    apply (cut_tac m=m in mod_exhaust_less_4)
    apply (elim disjE, simp_all)
    apply (safe dest!: mod_eqD, simp_all)
    done
  show ?thesis
    unfolding sin_coeff_def
    apply (subst t2)
    apply (rule sin_bound_lemma)
    apply (rule setsum_cong[OF refl])
    apply (subst diff_m_0, simp)
    apply (auto intro: mult_right_mono [where b=1, simplified] mult_right_mono
                simp add: est mult_nonneg_nonneg mult_ac divide_inverse
                          power_abs [symmetric] abs_mult)
    done
qed

end
