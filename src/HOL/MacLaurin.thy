(*  Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
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
apply (rule_tac x = "(f h - (\<Sum>m=0..<n. (j m / real (fact m)) * h^m)) *
                 real(fact n) / (h^n)"
       in exI)
apply (simp) 
done

lemma eq_diff_eq': "(x = y - z) = (y = x + (z::real))"
by arith

lemma fact_diff_Suc [rule_format]:
  "n < Suc m ==> fact (Suc m - n) = (Suc m - n) * fact (m - n)"
  by (subst fact_reduce_nat, auto)

lemma Maclaurin_lemma2:
  assumes diff: "\<forall>m t. m < n \<and> 0\<le>t \<and> t\<le>h \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
  assumes n: "n = Suc k"
  assumes difg: "difg =
        (\<lambda>m t. diff m t -
               ((\<Sum>p = 0..<n - m. diff (m + p) 0 / real (fact p) * t ^ p) +
                B * (t ^ (n - m) / real (fact (n - m)))))"
  shows
      "\<forall>m t. m < n & 0 \<le> t & t \<le> h --> DERIV (difg m) t :> difg (Suc m) t"
unfolding difg
 apply clarify
 apply (rule DERIV_diff)
  apply (simp add: diff)
 apply (simp only: n)
 apply (rule DERIV_add)
  apply (rule_tac [2] DERIV_cmult)
  apply (rule_tac [2] lemma_DERIV_subst)
   apply (rule_tac [2] DERIV_quotient)
     apply (rule_tac [3] DERIV_const)
    apply (rule_tac [2] DERIV_pow)
   prefer 3 

apply (simp add: fact_diff_Suc)
  prefer 2 apply simp
 apply (frule less_iff_Suc_add [THEN iffD1], clarify)
 apply (simp del: setsum_op_ivl_Suc)
 apply (insert sumr_offset4 [of "Suc 0"])
 apply (simp del: setsum_op_ivl_Suc fact_Suc_nat power_Suc)
 apply (rule lemma_DERIV_subst)
  apply (rule DERIV_add)
   apply (rule_tac [2] DERIV_const)
  apply (rule DERIV_sumr, clarify)
  prefer 2 apply simp
 apply (simp (no_asm) add: divide_inverse mult_assoc del: fact_Suc_nat power_Suc)
 apply (rule DERIV_cmult)
 apply (rule lemma_DERIV_subst)
  apply (best intro!: DERIV_intros)
 apply (subst fact_Suc_nat)
 apply (subst real_of_nat_mult)
 apply (simp add: mult_ac)
done

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
    by (cases n, simp add: n)

  obtain B where f_h: "f h =
        (\<Sum>m = 0..<n. diff m (0\<Colon>real) / real (fact m) * h ^ m) +
        B * (h ^ n / real (fact n))"
    using Maclaurin_lemma [OF h] ..

  obtain g where g_def: "g = (%t. f t -
    (setsum (%m. (diff m 0 / real(fact m)) * t^m) {0..<n}
      + (B * (t^n / real(fact n)))))" by blast

  have g2: "g 0 = 0 & g h = 0"
    apply (simp add: m f_h g_def del: setsum_op_ivl_Suc)
    apply (cut_tac n = m and k = "Suc 0" in sumr_offset2)
    apply (simp add: eq_diff_eq' diff_0 del: setsum_op_ivl_Suc)
    done

  obtain difg where difg_def: "difg = (%m t. diff m t -
    (setsum (%p. (diff (m + p) 0 / real (fact p)) * (t ^ p)) {0..<n-m}
      + (B * ((t ^ (n - m)) / real (fact (n - m))))))" by blast

  have difg_0: "difg 0 = g"
    unfolding difg_def g_def by (simp add: diff_0)

  have difg_Suc: "\<forall>(m\<Colon>nat) t\<Colon>real.
        m < n \<and> (0\<Colon>real) \<le> t \<and> t \<le> h \<longrightarrow> DERIV (difg m) t :> difg (Suc m) t"
    using diff_Suc m difg_def by (rule Maclaurin_lemma2)

  have difg_eq_0: "\<forall>m. m < n --> difg m 0 = 0"
    apply clarify
    apply (simp add: m difg_def)
    apply (frule less_iff_Suc_add [THEN iffD1], clarify)
    apply (simp del: setsum_op_ivl_Suc)
    apply (insert sumr_offset4 [of "Suc 0"])
    apply (simp del: setsum_op_ivl_Suc fact_Suc_nat)
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
      by (simp add: m f_h difg_def del: fact_Suc_nat)
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
   "[| 0 < h; diff 0 = f;
       \<forall>m t.
          m < n & 0 \<le> t & t \<le> h --> DERIV (diff m) t :> diff (Suc m) t |]
    ==> \<exists>t. 0 < t &
              t \<le> h &
              f h =
              (\<Sum>m=0..<n. diff m 0 / real (fact m) * h ^ m) +
              diff n t / real (fact n) * h ^ n"
apply (case_tac "n", auto)
apply (drule Maclaurin, auto)
done

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
   "[| h < 0; n > 0; diff 0 = f;
       \<forall>m t. m < n & h \<le> t & t \<le> 0 --> DERIV (diff m) t :> diff (Suc m) t |]
    ==> \<exists>t. h < t &
              t < 0 &
              f h =
              (\<Sum>m=0..<n. diff m 0 / real (fact m) * h ^ m) +
              diff n t / real (fact n) * h ^ n"
apply (cut_tac f = "%x. f (-x)"
        and diff = "%n x. (-1 ^ n) * diff n (-x)"
        and h = "-h" and n = n in Maclaurin_objl)
apply (simp)
apply safe
apply (subst minus_mult_right)
apply (rule DERIV_cmult)
apply (rule lemma_DERIV_subst)
apply (rule DERIV_chain2 [where g=uminus])
apply (rule_tac [2] DERIV_minus, rule_tac [2] DERIV_ident)
prefer 2 apply force
apply force
apply (rule_tac x = "-t" in exI, auto)
apply (subgoal_tac "(\<Sum>m = 0..<n. -1 ^ m * diff m 0 * (-h)^m / real(fact m)) =
                    (\<Sum>m = 0..<n. diff m 0 * h ^ m / real(fact m))")
apply (rule_tac [2] setsum_cong[OF refl])
apply (auto simp add: divide_inverse power_mult_distrib [symmetric])
done

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
by (induct "n", auto)

lemma Maclaurin_bi_le:
   "[| diff 0 = f;
       \<forall>m t. m < n & abs t \<le> abs x --> DERIV (diff m) t :> diff (Suc m) t |]
    ==> \<exists>t. abs t \<le> abs x &
              f x =
              (\<Sum>m=0..<n. diff m 0 / real (fact m) * x ^ m) +
              diff n t / real (fact n) * x ^ n"
apply (case_tac "n = 0", force)
apply (case_tac "x = 0")
 apply (rule_tac x = 0 in exI)
 apply (force simp add: Maclaurin_bi_le_lemma)
apply (cut_tac x = x and y = 0 in linorder_less_linear, auto)
 txt{*Case 1, where @{term "x < 0"}*}
 apply (cut_tac f = "diff 0" and diff = diff and h = x and n = n in Maclaurin_minus_objl, safe)
  apply (simp add: abs_if)
 apply (rule_tac x = t in exI)
 apply (simp add: abs_if)
txt{*Case 2, where @{term "0 < x"}*}
apply (cut_tac f = "diff 0" and diff = diff and h = x and n = n in Maclaurin_objl, safe)
 apply (simp add: abs_if)
apply (rule_tac x = t in exI)
apply (simp add: abs_if)
done

lemma Maclaurin_all_lt:
     "[| diff 0 = f;
         \<forall>m x. DERIV (diff m) x :> diff(Suc m) x;
        x ~= 0; n > 0
      |] ==> \<exists>t. 0 < abs t & abs t < abs x &
               f x = (\<Sum>m=0..<n. (diff m 0 / real (fact m)) * x ^ m) +
                     (diff n t / real (fact n)) * x ^ n"
apply (rule_tac x = x and y = 0 in linorder_cases)
prefer 2 apply blast
apply (drule_tac [2] diff=diff in Maclaurin)
apply (drule_tac diff=diff in Maclaurin_minus, simp_all, safe)
apply (rule_tac [!] x = t in exI, auto)
done

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

lemma Maclaurin_all_le: "[| diff 0 = f;
        \<forall>m x. DERIV (diff m) x :> diff (Suc m) x
      |] ==> \<exists>t. abs t \<le> abs x &
              f x = (\<Sum>m=0..<n. (diff m 0 / real (fact m)) * x ^ m) +
                    (diff n t / real (fact n)) * x ^ n"
apply(cases "n=0")
apply (force)
apply (case_tac "x = 0")
apply (frule_tac diff = diff and n = n in Maclaurin_zero, assumption)
apply (drule not0_implies_Suc)
apply (rule_tac x = 0 in exI, force)
apply (frule_tac diff = diff and n = n in Maclaurin_all_lt, auto)
apply (rule_tac x = t in exI, auto)
done

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

lemma Maclaurin_sin_expansion2:
     "\<exists>t. abs t \<le> abs x &
       sin x =
       (\<Sum>m=0..<n. (if even m then 0
                       else (-1 ^ ((m - Suc 0) div 2)) / real (fact m)) *
                       x ^ m)
      + ((sin(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = sin and n = n and x = x
        and diff = "%n x. sin (x + 1/2*real n * pi)" in Maclaurin_all_lt_objl)
apply safe
apply (simp (no_asm))
apply (simp (no_asm))
apply (case_tac "n", clarify, simp, simp add: lemma_STAR_sin)
apply (rule ccontr, simp)
apply (drule_tac x = x in spec, simp)
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: sin_zero_iff odd_Suc_mult_two_ex)
done

lemma Maclaurin_sin_expansion:
     "\<exists>t. sin x =
       (\<Sum>m=0..<n. (if even m then 0
                       else (-1 ^ ((m - Suc 0) div 2)) / real (fact m)) *
                       x ^ m)
      + ((sin(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (insert Maclaurin_sin_expansion2 [of x n]) 
apply (blast intro: elim:); 
done


lemma Maclaurin_sin_expansion3:
     "[| n > 0; 0 < x |] ==>
       \<exists>t. 0 < t & t < x &
       sin x =
       (\<Sum>m=0..<n. (if even m then 0
                       else (-1 ^ ((m - Suc 0) div 2)) / real (fact m)) *
                       x ^ m)
      + ((sin(t + 1/2 * real(n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = sin and n = n and h = x and diff = "%n x. sin (x + 1/2*real (n) *pi)" in Maclaurin_objl)
apply safe
apply simp
apply (simp (no_asm))
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: sin_zero_iff odd_Suc_mult_two_ex)
done

lemma Maclaurin_sin_expansion4:
     "0 < x ==>
       \<exists>t. 0 < t & t \<le> x &
       sin x =
       (\<Sum>m=0..<n. (if even m then 0
                       else (-1 ^ ((m - Suc 0) div 2)) / real (fact m)) *
                       x ^ m)
      + ((sin(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = sin and n = n and h = x and diff = "%n x. sin (x + 1/2*real (n) *pi)" in Maclaurin2_objl)
apply safe
apply simp
apply (simp (no_asm))
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: sin_zero_iff odd_Suc_mult_two_ex)
done


subsection{*Maclaurin Expansion for Cosine Function*}

lemma sumr_cos_zero_one [simp]:
 "(\<Sum>m=0..<(Suc n).
     (if even m then -1 ^ (m div 2)/(real  (fact m)) else 0) * 0 ^ m) = 1"
by (induct "n", auto)

lemma Maclaurin_cos_expansion:
     "\<exists>t. abs t \<le> abs x &
       cos x =
       (\<Sum>m=0..<n. (if even m
                       then -1 ^ (m div 2)/(real (fact m))
                       else 0) *
                       x ^ m)
      + ((cos(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = cos and n = n and x = x and diff = "%n x. cos (x + 1/2*real (n) *pi)" in Maclaurin_all_lt_objl)
apply safe
apply (simp (no_asm))
apply (simp (no_asm))
apply (case_tac "n", simp)
apply (simp del: setsum_op_ivl_Suc)
apply (rule ccontr, simp)
apply (drule_tac x = x in spec, simp)
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: cos_zero_iff even_mult_two_ex)
done

lemma Maclaurin_cos_expansion2:
     "[| 0 < x; n > 0 |] ==>
       \<exists>t. 0 < t & t < x &
       cos x =
       (\<Sum>m=0..<n. (if even m
                       then -1 ^ (m div 2)/(real (fact m))
                       else 0) *
                       x ^ m)
      + ((cos(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = cos and n = n and h = x and diff = "%n x. cos (x + 1/2*real (n) *pi)" in Maclaurin_objl)
apply safe
apply simp
apply (simp (no_asm))
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: cos_zero_iff even_mult_two_ex)
done

lemma Maclaurin_minus_cos_expansion:
     "[| x < 0; n > 0 |] ==>
       \<exists>t. x < t & t < 0 &
       cos x =
       (\<Sum>m=0..<n. (if even m
                       then -1 ^ (m div 2)/(real (fact m))
                       else 0) *
                       x ^ m)
      + ((cos(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = cos and n = n and h = x and diff = "%n x. cos (x + 1/2*real (n) *pi)" in Maclaurin_minus_objl)
apply safe
apply simp
apply (simp (no_asm))
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: cos_zero_iff even_mult_two_ex)
done

(* ------------------------------------------------------------------------- *)
(* Version for ln(1 +/- x). Where is it??                                    *)
(* ------------------------------------------------------------------------- *)

lemma sin_bound_lemma:
    "[|x = y; abs u \<le> (v::real) |] ==> \<bar>(x + u) - y\<bar> \<le> v"
by auto

lemma Maclaurin_sin_bound:
  "abs(sin x - (\<Sum>m=0..<n. (if even m then 0 else (-1 ^ ((m - Suc 0) div 2)) / real (fact m)) *
  x ^ m))  \<le> inverse(real (fact n)) * \<bar>x\<bar> ^ n"
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
