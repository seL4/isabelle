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
by (rule_tac x = "(f h - (\<Sum>m=0..<n. (j m / real (fact m)) * h^m)) *
                 real(fact n) / (h^n)"
       in exI, simp)

lemma eq_diff_eq': "(x = y - z) = (y = x + (z::real))"
by arith

lemma fact_diff_Suc [rule_format]:
  "n < Suc m ==> fact (Suc m - n) = (Suc m - n) * fact (m - n)"
  by (subst fact_reduce_nat, auto)

lemma Maclaurin_lemma2:
  assumes DERIV : "\<forall>m t. m < n \<and> 0\<le>t \<and> t\<le>h \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
  and INIT : "n = Suc k"
  and DIFG_DEF: "difg = (\<lambda>m t. diff m t - ((\<Sum>p = 0..<n - m. diff (m + p) 0 / real (fact p) * t ^ p) + 
  B * (t ^ (n - m) / real (fact (n - m)))))"
  shows "\<forall>m t. m < n & 0 \<le> t & t \<le> h --> DERIV (difg m) t :> difg (Suc m) t"
proof (rule allI)+
  fix m
  fix t
  show "m < n \<and> 0 \<le> t \<and> t \<le> h \<longrightarrow> DERIV (difg m) t :> difg (Suc m) t"
  proof
    assume INIT2: "m < n & 0 \<le> t & t \<le> h"
    hence INTERV: "0 \<le> t & t \<le> h" ..
    from INIT2 and INIT have mtok: "m < Suc k" by arith
    have "DERIV (\<lambda>t. diff m t -
    ((\<Sum>p = 0..<Suc k - m. diff (m + p) 0 / real (fact p) * t ^ p) +
    B * (t ^ (Suc k - m) / real (fact (Suc k - m)))))
    t :> diff (Suc m) t -
    ((\<Sum>p = 0..<Suc k - Suc m. diff (Suc m + p) 0 / real (fact p) * t ^ p) +
    B * (t ^ (Suc k - Suc m) / real (fact (Suc k - Suc m))))"
    proof -
      from DERIV and INIT2 have "DERIV (diff m) t :> diff (Suc m) t" by simp
      moreover
      have " DERIV (\<lambda>x. (\<Sum>p = 0..<Suc k - m. diff (m + p) 0 / real (fact p) * x ^ p) +
	B * (x ^ (Suc k - m) / real (fact (Suc k - m))))
	t :> (\<Sum>p = 0..<Suc k - Suc m. diff (Suc m + p) 0 / real (fact p) * t ^ p) +
	B * (t ^ (Suc k - Suc m) / real (fact (Suc k - Suc m)))"
      proof -
	have "DERIV (\<lambda>x. \<Sum>p = 0..<Suc k - m. diff (m + p) 0 / real (fact p) * x ^ p) t
	  :> (\<Sum>p = 0..<Suc k - Suc m. diff (Suc m + p) 0 / real (fact p) * t ^ p)"
	proof -
	  have "\<exists> d. k = m + d"
	  proof -
	    from INIT2 have "m < n" ..
	    hence "\<exists> d. n = m + d + Suc 0" by arith
	    with INIT show ?thesis by (simp del: setsum_op_ivl_Suc)
	  qed
	  from this obtain d where kmd: "k = m + d" ..
	  have "DERIV (\<lambda>x. (\<Sum>ma = 0..<d. diff (Suc (m + ma)) 0 * x ^ Suc ma / real (fact (Suc ma))) +
            diff m 0)
	    t :> (\<Sum>p = 0..<d. diff (Suc (m + p)) 0 * t ^ p / real (fact p))"
	    
	  proof - 
	    have "DERIV (\<lambda>x. (\<Sum>ma = 0..<d. diff (Suc (m + ma)) 0 * x ^ Suc ma / real (fact (Suc ma))) + diff m 0) t :>  (\<Sum>r = 0..<d. diff (Suc (m + r)) 0 * t ^ r / real (fact r)) + 0"
	    proof -
	      from DERIV and INTERV have "DERIV (\<lambda>x. (\<Sum>ma = 0..<d. diff (Suc (m + ma)) 0 * x ^ Suc ma / real (fact (Suc ma)))) t :>  (\<Sum>r = 0..<d. diff (Suc (m + r)) 0 * t ^ r / real (fact r))"
	      proof -
		have "\<forall>r. 0 \<le> r \<and> r < 0 + d \<longrightarrow>
		  DERIV (\<lambda>x. diff (Suc (m + r)) 0 * x ^ Suc r / real (fact (Suc r))) t
		  :> diff (Suc (m + r)) 0 * t ^ r / real (fact r)"
		proof (rule allI)
		  fix r
		  show " 0 \<le> r \<and> r < 0 + d \<longrightarrow>
		    DERIV (\<lambda>x. diff (Suc (m + r)) 0 * x ^ Suc r / real (fact (Suc r))) t
		    :> diff (Suc (m + r)) 0 * t ^ r / real (fact r)"
		  proof 
		    assume "0 \<le> r & r < 0 + d"
		    have "DERIV (\<lambda>x. diff (Suc (m + r)) 0 *
                      (x ^ Suc r * inverse (real (fact (Suc r)))))
		      t :> diff (Suc (m + r)) 0 * (t ^ r * inverse (real (fact r)))"
		    proof -
                      have "(1 + real r) * real (fact r) \<noteq> 0" by auto
		      from this have "real (fact r) + real r * real (fact r) \<noteq> 0"
                        by (metis add_nonneg_eq_0_iff mult_nonneg_nonneg real_of_nat_fact_not_zero real_of_nat_ge_zero)
                      from this have "DERIV (\<lambda>x. x ^ Suc r * inverse (real (fact (Suc r)))) t :> real (Suc r) * t ^ (Suc r - Suc 0) * inverse (real (fact (Suc r))) +
			0 * t ^ Suc r"
                        apply - by ( rule DERIV_intros | rule refl)+ auto
		      moreover
		      have "real (Suc r) * t ^ (Suc r - Suc 0) * inverse (real (fact (Suc r))) +
			0 * t ^ Suc r =
			t ^ r * inverse (real (fact r))"
		      proof -
			
			have " real (Suc r) * t ^ (Suc r - Suc 0) *
			  inverse (real (Suc r) * real (fact r)) +
			  0 * t ^ Suc r =
			  t ^ r * inverse (real (fact r))" by (simp add: mult_ac)
			hence "real (Suc r) * t ^ (Suc r - Suc 0) * inverse (real (Suc r * fact r)) +
			  0 * t ^ Suc r =
			  t ^ r * inverse (real (fact r))" by (subst real_of_nat_mult)
			thus ?thesis by (subst fact_Suc)
		      qed
		      ultimately have " DERIV (\<lambda>x. x ^ Suc r * inverse (real (fact (Suc r)))) t
			:> t ^ r * inverse (real (fact r))" by (rule lemma_DERIV_subst)
		      thus ?thesis by (rule DERIV_cmult)
		    qed
		    thus "DERIV (\<lambda>x. diff (Suc (m + r)) 0 * x ^ Suc r /
                      real (fact (Suc r)))
		      t :> diff (Suc (m + r)) 0 * t ^ r / real (fact r)" by (simp (no_asm) add: divide_inverse mult_assoc del: fact_Suc power_Suc)
		  qed
		qed
		thus ?thesis by (rule DERIV_sumr)
	      qed
	      moreover
	      from DERIV_const have "DERIV (\<lambda>x. diff m 0) t :> 0" .
	      ultimately show ?thesis by (rule DERIV_add)
	    qed
	    moreover
	    have " (\<Sum>r = 0..<d. diff (Suc (m + r)) 0 * t ^ r / real (fact r)) + 0 =  (\<Sum>p = 0..<d. diff (Suc (m + p)) 0 * t ^ p / real (fact p))"  by simp
	    ultimately show ?thesis by (rule lemma_DERIV_subst)
	  qed
	  with kmd and sumr_offset4 [of 1] show ?thesis by (simp del: setsum_op_ivl_Suc fact_Suc power_Suc)
	qed
	moreover
	have " DERIV (\<lambda>x. B * (x ^ (Suc k - m) / real (fact (Suc k - m)))) t
	  :> B * (t ^ (Suc k - Suc m) / real (fact (Suc k - Suc m)))"
	proof -
	  have " DERIV (\<lambda>x. x ^ (Suc k - m) / real (fact (Suc k - m))) t
	    :> t ^ (Suc k - Suc m) / real (fact (Suc k - Suc m))"
	  proof -
	    have "DERIV (\<lambda>x. x ^ (Suc k - m)) t :> real (Suc k - m) * t ^ (Suc k - m - Suc 0)" by (rule DERIV_pow)
	    moreover
	    have "DERIV (\<lambda>x. real (fact (Suc k - m))) t :> 0" by (rule DERIV_const)
	    moreover
	    have "(\<lambda>x. real (fact (Suc k - m))) t \<noteq> 0" by simp
	    ultimately have " DERIV (\<lambda>y. y ^ (Suc k - m) / real (fact (Suc k - m))) t
	      :>  ( real (Suc k - m) * t ^ (Suc k - m - Suc 0) * real (fact (Suc k - m)) + - (0 * t ^ (Suc k - m))) /
	      real (fact (Suc k - m)) ^ Suc (Suc 0)"
              apply -
              apply (rule DERIV_cong) by (rule DERIV_intros | rule refl)+ auto
	    moreover
	    from mtok and INIT have "( real (Suc k - m) * t ^ (Suc k - m - Suc 0) * real (fact (Suc k - m)) + - (0 * t ^ (Suc k - m))) /
	      real (fact (Suc k - m)) ^ Suc (Suc 0) =  t ^ (Suc k - Suc m) / real (fact (Suc k - Suc m))" by (simp add: fact_diff_Suc)
	    ultimately show ?thesis by (rule lemma_DERIV_subst)
	  qed
	  moreover
	  thus ?thesis by (rule DERIV_cmult)
	qed
	ultimately show ?thesis by (rule DERIV_add)
      qed
      ultimately show ?thesis by (rule DERIV_diff) 
    qed
    from INIT and this and DIFG_DEF show "DERIV (difg m) t :> difg (Suc m) t" by clarify
  qed
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
  case 0 with INIT1 INIT2 show ?thesis by fastsimp
next
  case Suc 
  hence "n > 0" by simp
  from INIT1 this INIT2 DERIV have "\<exists>t>0. t < h \<and>
    f h =
    (\<Sum>m = 0..<n. diff m 0 / real (fact m) * h ^ m) + diff n t / real (fact n) * h ^ n" 
    by (rule Maclaurin)
  thus ?thesis by fastsimp
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
  assumes INTERV : "h < 0" and
  INIT : "0 < n" "diff 0 = f" and
             ABL : "\<forall>m t. m < n & h \<le> t & t \<le> 0 --> DERIV (diff m) t :> diff (Suc m) t"
  shows "\<exists>t. h < t & t < 0 &
         f h = (\<Sum>m=0..<n. diff m 0 / real (fact m) * h ^ m) +
         diff n t / real (fact n) * h ^ n"
proof -
  from INTERV have "0 < -h" by simp
  moreover
  from INIT have "0 < n" by simp
  moreover
  from INIT have "(% x. ( - 1) ^ 0 * diff 0 (- x)) = (% x. f (- x))" by simp
  moreover
  have "\<forall>m t. m < n \<and> 0 \<le> t \<and> t \<le> - h \<longrightarrow>
    DERIV (\<lambda>x. (- 1) ^ m * diff m (- x)) t :> (- 1) ^ Suc m * diff (Suc m) (- t)"
  proof (rule allI impI)+
    fix m t
    assume tINTERV:" m < n \<and> 0 \<le> t \<and> t \<le> - h"
    with ABL show "DERIV (\<lambda>x. (- 1) ^ m * diff m (- x)) t :> (- 1) ^ Suc m * diff (Suc m) (- t)"
    proof -
      
      from ABL and tINTERV have "DERIV (\<lambda>x. diff m (- x)) t :> - diff (Suc m) (- t)" (is ?tABL)
      proof -
	from ABL and tINTERV have "DERIV (diff m) (- t) :> diff (Suc m) (- t)" by force
	moreover
	from DERIV_ident[of t] have "DERIV uminus t :> (- 1)" by (rule DERIV_minus) 
	ultimately have "DERIV (\<lambda>x. diff m (- x)) t :> diff (Suc m) (- t) * - 1" by (rule DERIV_chain2)
	thus ?thesis by simp
      qed
      thus ?thesis
      proof -
	assume ?tABL hence "DERIV (\<lambda>x. -1 ^ m * diff m (- x)) t :> -1 ^ m * - diff (Suc m) (- t)" by (rule DERIV_cmult)
	hence "DERIV (\<lambda>x. -1 ^ m * diff m (- x)) t :> - (-1 ^ m * diff (Suc m) (- t))" by (subst minus_mult_right)
	thus ?thesis by simp 
      qed
    qed
  qed
  ultimately have t_exists: "\<exists>t>0. t < - h \<and>
    f (- (- h)) =
    (\<Sum>m = 0..<n.
    (- 1) ^ m * diff m (- 0) / real (fact m) * (- h) ^ m) +
    (- 1) ^ n * diff n (- t) / real (fact n) * (- h) ^ n" (is "\<exists> t. ?P t") by (rule Maclaurin)
  from this obtain t where t_def: "?P t" ..
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
by (induct "n", auto)

lemma Maclaurin_bi_le:
   assumes INIT : "diff 0 = f"
   and DERIV : "\<forall>m t. m < n & abs t \<le> abs x --> DERIV (diff m) t :> diff (Suc m) t"
   shows "\<exists>t. abs t \<le> abs x &
              f x =
              (\<Sum>m=0..<n. diff m 0 / real (fact m) * x ^ m) +
              diff n t / real (fact n) * x ^ n"
proof (cases "n = 0")
  case True from INIT True show ?thesis by force
next
  case False
  from this have n_not_zero:"n \<noteq> 0" .
  from False INIT DERIV show ?thesis
  proof (cases "x = 0")
    case True show ?thesis
    proof -
      from n_not_zero True INIT DERIV have "\<bar>0\<bar> \<le> \<bar>x\<bar> \<and>
	f x = (\<Sum>m = 0..<n. diff m 0 / real (fact m) * x ^ m) + diff n 0 / real (fact n) * x ^ n" by(force simp add: Maclaurin_bi_le_lemma) 
      thus ?thesis ..
    qed
  next
    case False 
    note linorder_less_linear [of "x" "0"] 
    thus ?thesis
    proof (elim disjE)
      assume "x = 0" with False show ?thesis ..
      next
      assume x_less_zero: "x < 0" moreover
      from n_not_zero have "0 < n" by simp moreover
      have "diff 0 = diff 0" by simp moreover
      have "\<forall>m t. m < n \<and> x \<le> t \<and> t \<le> 0 \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
      proof (rule allI, rule allI, rule impI)
	fix m t
	assume "m < n & x \<le> t & t \<le> 0"
	with DERIV show " DERIV (diff m) t :> diff (Suc m) t" by (fastsimp simp add: abs_if)
      qed
      ultimately have t_exists:"\<exists>t>x. t < 0 \<and>
        diff 0 x =
        (\<Sum>m = 0..<n. diff m 0 / real (fact m) * x ^ m) + diff n t / real (fact n) * x ^ n" (is "\<exists> t. ?P t") by (rule Maclaurin_minus)
      from this obtain t where t_def: "?P t" ..
      from t_def x_less_zero INIT  have "\<bar>t\<bar> \<le> \<bar>x\<bar> \<and>
	f x = (\<Sum>m = 0..<n. diff m 0 / real (fact m) * x ^ m) + diff n t / real (fact n) * x ^ n"
	by (simp add: abs_if order_less_le)
      thus ?thesis by (rule exI)
    next
    assume x_greater_zero: "x > 0" moreover
    from n_not_zero have "0 < n" by simp moreover
    have "diff 0 = diff 0" by simp moreover
    have "\<forall>m t. m < n \<and> 0 \<le> t \<and> t \<le> x \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
      proof (rule allI, rule allI, rule impI)
	fix m t
	assume "m < n & 0 \<le> t & t \<le> x"
	with DERIV show " DERIV (diff m) t :> diff (Suc m) t" by fastsimp
      qed
      ultimately have t_exists:"\<exists>t>0. t < x \<and>
        diff 0 x =
        (\<Sum>m = 0..<n. diff m 0 / real (fact m) * x ^ m) + diff n t / real (fact n) * x ^ n" (is "\<exists> t. ?P t") by (rule Maclaurin)
      from this obtain t where t_def: "?P t" ..
      from t_def x_greater_zero INIT  have "\<bar>t\<bar> \<le> \<bar>x\<bar> \<and>
	f x = (\<Sum>m = 0..<n. diff m 0 / real (fact m) * x ^ m) + diff n t / real (fact n) * x ^ n"
	by fastsimp
      thus ?thesis ..
    qed
  qed
qed


lemma Maclaurin_all_lt:
  assumes INIT1: "diff 0 = f" and INIT2: "0 < n" and INIT3: "x \<noteq> 0"
  and DERIV: "\<forall>m x. DERIV (diff m) x :> diff(Suc m) x"
  shows "\<exists>t. 0 < abs t & abs t < abs x &
               f x = (\<Sum>m=0..<n. (diff m 0 / real (fact m)) * x ^ m) +
                     (diff n t / real (fact n)) * x ^ n" 
proof -
  have "(x = 0) \<Longrightarrow> ?thesis"
  proof -
    assume "x = 0"
    with INIT3 show "(x = 0) \<Longrightarrow> ?thesis"..
  qed
  moreover have "(x < 0) \<Longrightarrow> ?thesis"
  proof -
    assume x_less_zero: "x < 0"
    from DERIV have "\<forall>m t. m < n \<and> x \<le> t \<and> t \<le> 0 \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t" by simp 
    with x_less_zero INIT2 INIT1 have "\<exists>t>x. t < 0 \<and> f x = (\<Sum>m = 0..<n. diff m 0 / real (fact m) * x ^ m) + diff n t / real (fact n) * x ^ n" (is "\<exists> t. ?P t") by (rule Maclaurin_minus)
    from this obtain t where "?P t" ..
    with x_less_zero have "0 < \<bar>t\<bar> \<and>
      \<bar>t\<bar> < \<bar>x\<bar> \<and>
      f x = (\<Sum>m = 0..<n. diff m 0 / real (fact m) * x ^ m) + diff n t / real (fact n) * x ^ n" by simp
    thus ?thesis ..
  qed
  moreover have "(x > 0) \<Longrightarrow> ?thesis"
  proof -
    assume x_greater_zero: "x > 0"
    from DERIV have "\<forall>m t. m < n \<and> 0 \<le> t \<and> t \<le> x \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t" by simp
    with x_greater_zero INIT2 INIT1 have "\<exists>t>0. t < x \<and> f x = (\<Sum>m = 0..<n. diff m 0 / real (fact m) * x ^ m) + diff n t / real (fact n) * x ^ n" (is "\<exists> t. ?P t") by (rule Maclaurin)
    from this obtain t where "?P t" ..
    with x_greater_zero have "0 < \<bar>t\<bar> \<and>
      \<bar>t\<bar> < \<bar>x\<bar> \<and>
      f x = (\<Sum>m = 0..<n. diff m 0 / real (fact m) * x ^ m) + diff n t / real (fact n) * x ^ n" by fastsimp
    thus ?thesis ..
  qed
  ultimately show ?thesis by (fastsimp) 
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
  shows "\<exists>t. abs t \<le> abs x &
              f x = (\<Sum>m=0..<n. (diff m 0 / real (fact m)) * x ^ m) +
                    (diff n t / real (fact n)) * x ^ n"
proof -
  note linorder_le_less_linear [of n 0]
  thus ?thesis
  proof
    assume "n\<le> 0" with INIT show ?thesis by force
  next
    assume n_greater_zero: "n > 0" show ?thesis
    proof (cases "x = 0")
      case True
      from n_greater_zero have "n \<noteq> 0" by auto
      from True this  have f_0:"(\<Sum>m = 0..<n. diff m 0 / real (fact m) * x ^ m) = diff 0 0" by (rule Maclaurin_zero)
      from n_greater_zero have "n \<noteq> 0" by (rule gr_implies_not0)
      hence "\<exists> m. n = Suc m" by (rule not0_implies_Suc)
      with f_0 True INIT have " \<bar>0\<bar> \<le> \<bar>x\<bar> \<and>
       f x = (\<Sum>m = 0..<n. diff m 0 / real (fact m) * x ^ m) + diff n 0 / real (fact n) * x ^ n"
	by force
      thus ?thesis ..
    next
      case False
      from INIT n_greater_zero this DERIV have "\<exists>t. 0 < \<bar>t\<bar> \<and>
	\<bar>t\<bar> < \<bar>x\<bar> \<and> f x = (\<Sum>m = 0..<n. diff m 0 / real (fact m) * x ^ m) + diff n t / real (fact n) * x ^ n" (is "\<exists> t. ?P t") by (rule Maclaurin_all_lt)
      from this obtain t where "?P t" ..
      hence "\<bar>t\<bar> \<le> \<bar>x\<bar> \<and>
       f x = (\<Sum>m = 0..<n. diff m 0 / real (fact m) * x ^ m) + diff n t / real (fact n) * x ^ n" by (simp add: order_less_le)
      thus ?thesis ..
    qed
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
by (simp only: cos_add sin_add real_of_nat_Suc add_divide_distrib left_distrib, auto)

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
apply (simp (no_asm) add: sin_expansion_lemma)
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
apply (simp (no_asm) add: sin_expansion_lemma)
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
apply (simp (no_asm) add: sin_expansion_lemma)
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

lemma cos_expansion_lemma:
  "cos (x + real(Suc m) * pi / 2) = -sin (x + real m * pi / 2)"
by (simp only: cos_add sin_add real_of_nat_Suc left_distrib add_divide_distrib, auto)

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
apply (simp (no_asm) add: cos_expansion_lemma)
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
apply (simp (no_asm) add: cos_expansion_lemma)
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
apply (simp (no_asm) add: cos_expansion_lemma)
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
