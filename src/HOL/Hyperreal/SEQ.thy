(*  Title       : SEQ.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Convergence of sequences and series
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
    Additional contributions by Jeremy Avigad and Brian Huffman
*)

header {* Sequences and Series *}

theory SEQ
imports NatStar
begin

definition
  Zseq :: "[nat \<Rightarrow> 'a::real_normed_vector] \<Rightarrow> bool" where
    --{*Standard definition of sequence converging to zero*}
  "Zseq X = (\<forall>r>0. \<exists>no. \<forall>n\<ge>no. norm (X n) < r)"

definition
  LIMSEQ :: "[nat => 'a::real_normed_vector, 'a] => bool"
    ("((_)/ ----> (_))" [60, 60] 60) where
    --{*Standard definition of convergence of sequence*}
  "X ----> L = (\<forall>r. 0 < r --> (\<exists>no. \<forall>n. no \<le> n --> norm (X n - L) < r))"

definition
  NSLIMSEQ :: "[nat => 'a::real_normed_vector, 'a] => bool"
    ("((_)/ ----NS> (_))" [60, 60] 60) where
    --{*Nonstandard definition of convergence of sequence*}
  "X ----NS> L = (\<forall>N \<in> HNatInfinite. ( *f* X) N \<approx> star_of L)"

definition
  lim :: "(nat => 'a::real_normed_vector) => 'a" where
    --{*Standard definition of limit using choice operator*}
  "lim X = (THE L. X ----> L)"

definition
  nslim :: "(nat => 'a::real_normed_vector) => 'a" where
    --{*Nonstandard definition of limit using choice operator*}
  "nslim X = (THE L. X ----NS> L)"

definition
  convergent :: "(nat => 'a::real_normed_vector) => bool" where
    --{*Standard definition of convergence*}
  "convergent X = (\<exists>L. X ----> L)"

definition
  NSconvergent :: "(nat => 'a::real_normed_vector) => bool" where
    --{*Nonstandard definition of convergence*}
  "NSconvergent X = (\<exists>L. X ----NS> L)"

definition
  Bseq :: "(nat => 'a::real_normed_vector) => bool" where
    --{*Standard definition for bounded sequence*}
  "Bseq X = (\<exists>K>0.\<forall>n. norm (X n) \<le> K)"

definition
  NSBseq :: "(nat => 'a::real_normed_vector) => bool" where
    --{*Nonstandard definition for bounded sequence*}
  "NSBseq X = (\<forall>N \<in> HNatInfinite. ( *f* X) N : HFinite)"

definition
  monoseq :: "(nat=>real)=>bool" where
    --{*Definition for monotonicity*}
  "monoseq X = ((\<forall>m. \<forall>n\<ge>m. X m \<le> X n) | (\<forall>m. \<forall>n\<ge>m. X n \<le> X m))"

definition
  subseq :: "(nat => nat) => bool" where
    --{*Definition of subsequence*}
  "subseq f = (\<forall>m. \<forall>n>m. (f m) < (f n))"

definition
  Cauchy :: "(nat => 'a::real_normed_vector) => bool" where
    --{*Standard definition of the Cauchy condition*}
  "Cauchy X = (\<forall>e>0. \<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. norm (X m - X n) < e)"

definition
  NSCauchy :: "(nat => 'a::real_normed_vector) => bool" where
    --{*Nonstandard definition*}
  "NSCauchy X = (\<forall>M \<in> HNatInfinite. \<forall>N \<in> HNatInfinite. ( *f* X) M \<approx> ( *f* X) N)"


subsection {* Bounded Sequences *}

lemma BseqI: assumes K: "\<And>n. norm (X n) \<le> K" shows "Bseq X"
unfolding Bseq_def
proof (intro exI conjI allI)
  show "0 < max K 1" by simp
next
  fix n::nat
  have "norm (X n) \<le> K" by (rule K)
  thus "norm (X n) \<le> max K 1" by simp
qed

lemma BseqD: "Bseq X \<Longrightarrow> \<exists>K>0. \<forall>n. norm (X n) \<le> K"
unfolding Bseq_def by simp

lemma BseqE: "\<lbrakk>Bseq X; \<And>K. \<lbrakk>0 < K; \<forall>n. norm (X n) \<le> K\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
unfolding Bseq_def by auto

lemma BseqI2: assumes K: "\<forall>n\<ge>N. norm (X n) \<le> K" shows "Bseq X"
proof (rule BseqI)
  let ?A = "norm ` X ` {..N}"
  have 1: "finite ?A" by simp
  have 2: "?A \<noteq> {}" by auto
  fix n::nat
  show "norm (X n) \<le> max K (Max ?A)"
  proof (cases rule: linorder_le_cases)
    assume "n \<ge> N"
    hence "norm (X n) \<le> K" using K by simp
    thus "norm (X n) \<le> max K (Max ?A)" by simp
  next
    assume "n \<le> N"
    hence "norm (X n) \<in> ?A" by simp
    with 1 2 have "norm (X n) \<le> Max ?A" by (rule Max_ge)
    thus "norm (X n) \<le> max K (Max ?A)" by simp
  qed
qed

lemma Bseq_ignore_initial_segment: "Bseq X \<Longrightarrow> Bseq (\<lambda>n. X (n + k))"
unfolding Bseq_def by auto

lemma Bseq_offset: "Bseq (\<lambda>n. X (n + k)) \<Longrightarrow> Bseq X"
apply (erule BseqE)
apply (rule_tac N="k" and K="K" in BseqI2)
apply clarify
apply (drule_tac x="n - k" in spec, simp)
done


subsection {* Sequences That Converge to Zero *}

lemma ZseqI:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. norm (X n) < r) \<Longrightarrow> Zseq X"
unfolding Zseq_def by simp

lemma ZseqD:
  "\<lbrakk>Zseq X; 0 < r\<rbrakk> \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. norm (X n) < r"
unfolding Zseq_def by simp

lemma Zseq_zero: "Zseq (\<lambda>n. 0)"
unfolding Zseq_def by simp

lemma Zseq_const_iff: "Zseq (\<lambda>n. k) = (k = 0)"
unfolding Zseq_def by force

lemma Zseq_norm_iff: "Zseq (\<lambda>n. norm (X n)) = Zseq (\<lambda>n. X n)"
unfolding Zseq_def by simp

lemma Zseq_imp_Zseq:
  assumes X: "Zseq X"
  assumes Y: "\<And>n. norm (Y n) \<le> norm (X n) * K"
  shows "Zseq (\<lambda>n. Y n)"
proof (cases)
  assume K: "0 < K"
  show ?thesis
  proof (rule ZseqI)
    fix r::real assume "0 < r"
    hence "0 < r / K"
      using K by (rule divide_pos_pos)
    then obtain N where "\<forall>n\<ge>N. norm (X n) < r / K"
      using ZseqD [OF X] by fast
    hence "\<forall>n\<ge>N. norm (X n) * K < r"
      by (simp add: pos_less_divide_eq K)
    hence "\<forall>n\<ge>N. norm (Y n) < r"
      by (simp add: order_le_less_trans [OF Y])
    thus "\<exists>N. \<forall>n\<ge>N. norm (Y n) < r" ..
  qed
next
  assume "\<not> 0 < K"
  hence K: "K \<le> 0" by (simp only: linorder_not_less)
  {
    fix n::nat
    have "norm (Y n) \<le> norm (X n) * K" by (rule Y)
    also have "\<dots> \<le> norm (X n) * 0"
      using K norm_ge_zero by (rule mult_left_mono)
    finally have "norm (Y n) = 0" by simp
  }
  thus ?thesis by (simp add: Zseq_zero)
qed

lemma Zseq_le: "\<lbrakk>Zseq Y; \<forall>n. norm (X n) \<le> norm (Y n)\<rbrakk> \<Longrightarrow> Zseq X"
by (erule_tac K="1" in Zseq_imp_Zseq, simp)

lemma Zseq_add:
  assumes X: "Zseq X"
  assumes Y: "Zseq Y"
  shows "Zseq (\<lambda>n. X n + Y n)"
proof (rule ZseqI)
  fix r::real assume "0 < r"
  hence r: "0 < r / 2" by simp
  obtain M where M: "\<forall>n\<ge>M. norm (X n) < r/2"
    using ZseqD [OF X r] by fast
  obtain N where N: "\<forall>n\<ge>N. norm (Y n) < r/2"
    using ZseqD [OF Y r] by fast
  show "\<exists>N. \<forall>n\<ge>N. norm (X n + Y n) < r"
  proof (intro exI allI impI)
    fix n assume n: "max M N \<le> n"
    have "norm (X n + Y n) \<le> norm (X n) + norm (Y n)"
      by (rule norm_triangle_ineq)
    also have "\<dots> < r/2 + r/2"
    proof (rule add_strict_mono)
      from M n show "norm (X n) < r/2" by simp
      from N n show "norm (Y n) < r/2" by simp
    qed
    finally show "norm (X n + Y n) < r" by simp
  qed
qed

lemma Zseq_minus: "Zseq X \<Longrightarrow> Zseq (\<lambda>n. - X n)"
unfolding Zseq_def by simp

lemma Zseq_diff: "\<lbrakk>Zseq X; Zseq Y\<rbrakk> \<Longrightarrow> Zseq (\<lambda>n. X n - Y n)"
by (simp only: diff_minus Zseq_add Zseq_minus)

lemma (in bounded_linear) Zseq:
  assumes X: "Zseq X"
  shows "Zseq (\<lambda>n. f (X n))"
proof -
  obtain K where "\<And>x. norm (f x) \<le> norm x * K"
    using bounded by fast
  with X show ?thesis
    by (rule Zseq_imp_Zseq)
qed

lemma (in bounded_bilinear) Zseq_prod:
  assumes X: "Zseq X"
  assumes Y: "Zseq Y"
  shows "Zseq (\<lambda>n. X n ** Y n)"
proof (rule ZseqI)
  fix r::real assume r: "0 < r"
  obtain K where K: "0 < K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using pos_bounded by fast
  from K have K': "0 < inverse K"
    by (rule positive_imp_inverse_positive)
  obtain M where M: "\<forall>n\<ge>M. norm (X n) < r"
    using ZseqD [OF X r] by fast
  obtain N where N: "\<forall>n\<ge>N. norm (Y n) < inverse K"
    using ZseqD [OF Y K'] by fast
  show "\<exists>N. \<forall>n\<ge>N. norm (X n ** Y n) < r"
  proof (intro exI allI impI)
    fix n assume n: "max M N \<le> n"
    have "norm (X n ** Y n) \<le> norm (X n) * norm (Y n) * K"
      by (rule norm_le)
    also have "norm (X n) * norm (Y n) * K < r * inverse K * K"
    proof (intro mult_strict_right_mono mult_strict_mono' norm_ge_zero K)
      from M n show Xn: "norm (X n) < r" by simp
      from N n show Yn: "norm (Y n) < inverse K" by simp
    qed
    also from K have "r * inverse K * K = r" by simp
    finally show "norm (X n ** Y n) < r" .
  qed
qed

lemma (in bounded_bilinear) Zseq_prod_Bseq:
  assumes X: "Zseq X"
  assumes Y: "Bseq Y"
  shows "Zseq (\<lambda>n. X n ** Y n)"
proof -
  obtain K where K: "0 \<le> K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using nonneg_bounded by fast
  obtain B where B: "0 < B"
    and norm_Y: "\<And>n. norm (Y n) \<le> B"
    using Y [unfolded Bseq_def] by fast
  from X show ?thesis
  proof (rule Zseq_imp_Zseq)
    fix n::nat
    have "norm (X n ** Y n) \<le> norm (X n) * norm (Y n) * K"
      by (rule norm_le)
    also have "\<dots> \<le> norm (X n) * B * K"
      by (intro mult_mono' order_refl norm_Y norm_ge_zero
                mult_nonneg_nonneg K)
    also have "\<dots> = norm (X n) * (B * K)"
      by (rule mult_assoc)
    finally show "norm (X n ** Y n) \<le> norm (X n) * (B * K)" .
  qed
qed

lemma (in bounded_bilinear) Bseq_prod_Zseq:
  assumes X: "Bseq X"
  assumes Y: "Zseq Y"
  shows "Zseq (\<lambda>n. X n ** Y n)"
proof -
  obtain K where K: "0 \<le> K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using nonneg_bounded by fast
  obtain B where B: "0 < B"
    and norm_X: "\<And>n. norm (X n) \<le> B"
    using X [unfolded Bseq_def] by fast
  from Y show ?thesis
  proof (rule Zseq_imp_Zseq)
    fix n::nat
    have "norm (X n ** Y n) \<le> norm (X n) * norm (Y n) * K"
      by (rule norm_le)
    also have "\<dots> \<le> B * norm (Y n) * K"
      by (intro mult_mono' order_refl norm_X norm_ge_zero
                mult_nonneg_nonneg K)
    also have "\<dots> = norm (Y n) * (B * K)"
      by (simp only: mult_ac)
    finally show "norm (X n ** Y n) \<le> norm (Y n) * (B * K)" .
  qed
qed

lemma (in bounded_bilinear) Zseq_prod_left:
  "Zseq X \<Longrightarrow> Zseq (\<lambda>n. X n ** a)"
by (rule bounded_linear_left [THEN bounded_linear.Zseq])

lemma (in bounded_bilinear) Zseq_prod_right:
  "Zseq X \<Longrightarrow> Zseq (\<lambda>n. a ** X n)"
by (rule bounded_linear_right [THEN bounded_linear.Zseq])

lemmas Zseq_mult = bounded_bilinear_mult.Zseq_prod
lemmas Zseq_mult_right = bounded_bilinear_mult.Zseq_prod_right
lemmas Zseq_mult_left = bounded_bilinear_mult.Zseq_prod_left


subsection {* Limits of Sequences *}

subsubsection {* Purely standard proofs *}

lemma LIMSEQ_iff:
      "(X ----> L) = (\<forall>r>0. \<exists>no. \<forall>n \<ge> no. norm (X n - L) < r)"
by (rule LIMSEQ_def)

lemma LIMSEQ_Zseq_iff: "((\<lambda>n. X n) ----> L) = Zseq (\<lambda>n. X n - L)"
by (simp only: LIMSEQ_def Zseq_def)

lemma LIMSEQ_I:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. norm (X n - L) < r) \<Longrightarrow> X ----> L"
by (simp add: LIMSEQ_def)

lemma LIMSEQ_D:
  "\<lbrakk>X ----> L; 0 < r\<rbrakk> \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. norm (X n - L) < r"
by (simp add: LIMSEQ_def)

lemma LIMSEQ_const: "(\<lambda>n. k) ----> k"
by (simp add: LIMSEQ_def)

lemma LIMSEQ_const_iff: "(\<lambda>n. k) ----> l = (k = l)"
by (simp add: LIMSEQ_Zseq_iff Zseq_const_iff)

lemma LIMSEQ_norm: "X ----> a \<Longrightarrow> (\<lambda>n. norm (X n)) ----> norm a"
apply (simp add: LIMSEQ_def, safe)
apply (drule_tac x="r" in spec, safe)
apply (rule_tac x="no" in exI, safe)
apply (drule_tac x="n" in spec, safe)
apply (erule order_le_less_trans [OF norm_triangle_ineq3])
done

lemma LIMSEQ_ignore_initial_segment:
  "f ----> a \<Longrightarrow> (\<lambda>n. f (n + k)) ----> a"
apply (rule LIMSEQ_I)
apply (drule (1) LIMSEQ_D)
apply (erule exE, rename_tac N)
apply (rule_tac x=N in exI)
apply simp
done

lemma LIMSEQ_offset:
  "(\<lambda>n. f (n + k)) ----> a \<Longrightarrow> f ----> a"
apply (rule LIMSEQ_I)
apply (drule (1) LIMSEQ_D)
apply (erule exE, rename_tac N)
apply (rule_tac x="N + k" in exI)
apply clarify
apply (drule_tac x="n - k" in spec)
apply (simp add: le_diff_conv2)
done

lemma LIMSEQ_Suc: "f ----> l \<Longrightarrow> (\<lambda>n. f (Suc n)) ----> l"
by (drule_tac k="1" in LIMSEQ_ignore_initial_segment, simp)

lemma LIMSEQ_imp_Suc: "(\<lambda>n. f (Suc n)) ----> l \<Longrightarrow> f ----> l"
by (rule_tac k="1" in LIMSEQ_offset, simp)

lemma LIMSEQ_Suc_iff: "(\<lambda>n. f (Suc n)) ----> l = f ----> l"
by (blast intro: LIMSEQ_imp_Suc LIMSEQ_Suc)

lemma add_diff_add:
  fixes a b c d :: "'a::ab_group_add"
  shows "(a + c) - (b + d) = (a - b) + (c - d)"
by simp

lemma minus_diff_minus:
  fixes a b :: "'a::ab_group_add"
  shows "(- a) - (- b) = - (a - b)"
by simp

lemma LIMSEQ_add: "\<lbrakk>X ----> a; Y ----> b\<rbrakk> \<Longrightarrow> (\<lambda>n. X n + Y n) ----> a + b"
by (simp only: LIMSEQ_Zseq_iff add_diff_add Zseq_add)

lemma LIMSEQ_minus: "X ----> a \<Longrightarrow> (\<lambda>n. - X n) ----> - a"
by (simp only: LIMSEQ_Zseq_iff minus_diff_minus Zseq_minus)

lemma LIMSEQ_minus_cancel: "(\<lambda>n. - X n) ----> - a \<Longrightarrow> X ----> a"
by (drule LIMSEQ_minus, simp)

lemma LIMSEQ_diff: "\<lbrakk>X ----> a; Y ----> b\<rbrakk> \<Longrightarrow> (\<lambda>n. X n - Y n) ----> a - b"
by (simp add: diff_minus LIMSEQ_add LIMSEQ_minus)

lemma LIMSEQ_unique: "\<lbrakk>X ----> a; X ----> b\<rbrakk> \<Longrightarrow> a = b"
by (drule (1) LIMSEQ_diff, simp add: LIMSEQ_const_iff)

lemma (in bounded_linear) LIMSEQ:
  "X ----> a \<Longrightarrow> (\<lambda>n. f (X n)) ----> f a"
by (simp only: LIMSEQ_Zseq_iff diff [symmetric] Zseq)

lemma (in bounded_bilinear) LIMSEQ:
  "\<lbrakk>X ----> a; Y ----> b\<rbrakk> \<Longrightarrow> (\<lambda>n. X n ** Y n) ----> a ** b"
by (simp only: LIMSEQ_Zseq_iff prod_diff_prod
               Zseq_add Zseq_prod Zseq_prod_left Zseq_prod_right)

lemma LIMSEQ_mult:
  fixes a b :: "'a::real_normed_algebra"
  shows "[| X ----> a; Y ----> b |] ==> (%n. X n * Y n) ----> a * b"
by (rule bounded_bilinear_mult.LIMSEQ)

lemma inverse_diff_inverse:
  "\<lbrakk>(a::'a::division_ring) \<noteq> 0; b \<noteq> 0\<rbrakk>
   \<Longrightarrow> inverse a - inverse b = - (inverse a * (a - b) * inverse b)"
by (simp add: right_diff_distrib left_diff_distrib mult_assoc)

lemma Bseq_inverse_lemma:
  fixes x :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>r \<le> norm x; 0 < r\<rbrakk> \<Longrightarrow> norm (inverse x) \<le> inverse r"
apply (subst nonzero_norm_inverse, clarsimp)
apply (erule (1) le_imp_inverse_le)
done

lemma Bseq_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  assumes X: "X ----> a"
  assumes a: "a \<noteq> 0"
  shows "Bseq (\<lambda>n. inverse (X n))"
proof -
  from a have "0 < norm a" by simp
  hence "\<exists>r>0. r < norm a" by (rule dense)
  then obtain r where r1: "0 < r" and r2: "r < norm a" by fast
  obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> norm (X n - a) < r"
    using LIMSEQ_D [OF X r1] by fast
  show ?thesis
  proof (rule BseqI2 [rule_format])
    fix n assume n: "N \<le> n"
    hence 1: "norm (X n - a) < r" by (rule N)
    hence 2: "X n \<noteq> 0" using r2 by auto
    hence "norm (inverse (X n)) = inverse (norm (X n))"
      by (rule nonzero_norm_inverse)
    also have "\<dots> \<le> inverse (norm a - r)"
    proof (rule le_imp_inverse_le)
      show "0 < norm a - r" using r2 by simp
    next
      have "norm a - norm (X n) \<le> norm (a - X n)"
        by (rule norm_triangle_ineq2)
      also have "\<dots> = norm (X n - a)"
        by (rule norm_minus_commute)
      also have "\<dots> < r" using 1 .
      finally show "norm a - r \<le> norm (X n)" by simp
    qed
    finally show "norm (inverse (X n)) \<le> inverse (norm a - r)" .
  qed
qed

lemma LIMSEQ_inverse_lemma:
  fixes a :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>X ----> a; a \<noteq> 0; \<forall>n. X n \<noteq> 0\<rbrakk>
         \<Longrightarrow> (\<lambda>n. inverse (X n)) ----> inverse a"
apply (subst LIMSEQ_Zseq_iff)
apply (simp add: inverse_diff_inverse nonzero_imp_inverse_nonzero)
apply (rule Zseq_minus)
apply (rule Zseq_mult_left)
apply (rule bounded_bilinear_mult.Bseq_prod_Zseq)
apply (erule (1) Bseq_inverse)
apply (simp add: LIMSEQ_Zseq_iff)
done

lemma LIMSEQ_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  assumes X: "X ----> a"
  assumes a: "a \<noteq> 0"
  shows "(\<lambda>n. inverse (X n)) ----> inverse a"
proof -
  from a have "0 < norm a" by simp
  then obtain k where "\<forall>n\<ge>k. norm (X n - a) < norm a"
    using LIMSEQ_D [OF X] by fast
  hence "\<forall>n\<ge>k. X n \<noteq> 0" by auto
  hence k: "\<forall>n. X (n + k) \<noteq> 0" by simp

  from X have "(\<lambda>n. X (n + k)) ----> a"
    by (rule LIMSEQ_ignore_initial_segment)
  hence "(\<lambda>n. inverse (X (n + k))) ----> inverse a"
    using a k by (rule LIMSEQ_inverse_lemma)
  thus "(\<lambda>n. inverse (X n)) ----> inverse a"
    by (rule LIMSEQ_offset)
qed

lemma LIMSEQ_divide:
  fixes a b :: "'a::real_normed_field"
  shows "\<lbrakk>X ----> a; Y ----> b; b \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>n. X n / Y n) ----> a / b"
by (simp add: LIMSEQ_mult LIMSEQ_inverse divide_inverse)

lemma LIMSEQ_pow:
  fixes a :: "'a::{real_normed_algebra,recpower}"
  shows "X ----> a \<Longrightarrow> (\<lambda>n. (X n) ^ m) ----> a ^ m"
by (induct m) (simp_all add: power_Suc LIMSEQ_const LIMSEQ_mult)

lemma LIMSEQ_setsum:
  assumes n: "\<And>n. n \<in> S \<Longrightarrow> X n ----> L n"
  shows "(\<lambda>m. \<Sum>n\<in>S. X n m) ----> (\<Sum>n\<in>S. L n)"
proof (cases "finite S")
  case True
  thus ?thesis using n
  proof (induct)
    case empty
    show ?case
      by (simp add: LIMSEQ_const)
  next
    case insert
    thus ?case
      by (simp add: LIMSEQ_add)
  qed
next
  case False
  thus ?thesis
    by (simp add: LIMSEQ_const)
qed

lemma LIMSEQ_setprod:
  fixes L :: "'a \<Rightarrow> 'b::{real_normed_algebra,comm_ring_1}"
  assumes n: "\<And>n. n \<in> S \<Longrightarrow> X n ----> L n"
  shows "(\<lambda>m. \<Prod>n\<in>S. X n m) ----> (\<Prod>n\<in>S. L n)"
proof (cases "finite S")
  case True
  thus ?thesis using n
  proof (induct)
    case empty
    show ?case
      by (simp add: LIMSEQ_const)
  next
    case insert
    thus ?case
      by (simp add: LIMSEQ_mult)
  qed
next
  case False
  thus ?thesis
    by (simp add: setprod_def LIMSEQ_const)
qed

lemma LIMSEQ_add_const: "f ----> a ==> (%n.(f n + b)) ----> a + b"
by (simp add: LIMSEQ_add LIMSEQ_const)

(* FIXME: delete *)
lemma LIMSEQ_add_minus:
     "[| X ----> a; Y ----> b |] ==> (%n. X n + -Y n) ----> a + -b"
by (simp only: LIMSEQ_add LIMSEQ_minus)

lemma LIMSEQ_diff_const: "f ----> a ==> (%n.(f n  - b)) ----> a - b"
by (simp add: LIMSEQ_diff LIMSEQ_const)

lemma LIMSEQ_diff_approach_zero: 
  "g ----> L ==> (%x. f x - g x) ----> 0  ==>
     f ----> L"
  apply (drule LIMSEQ_add)
  apply assumption
  apply simp
done

lemma LIMSEQ_diff_approach_zero2: 
  "f ----> L ==> (%x. f x - g x) ----> 0  ==>
     g ----> L";
  apply (drule LIMSEQ_diff)
  apply assumption
  apply simp
done

text{*A sequence tends to zero iff its abs does*}
lemma LIMSEQ_norm_zero: "((\<lambda>n. norm (X n)) ----> 0) = (X ----> 0)"
by (simp add: LIMSEQ_def)

lemma LIMSEQ_rabs_zero: "((%n. \<bar>f n\<bar>) ----> 0) = (f ----> (0::real))"
by (simp add: LIMSEQ_def)

lemma LIMSEQ_imp_rabs: "f ----> (l::real) ==> (%n. \<bar>f n\<bar>) ----> \<bar>l\<bar>"
by (drule LIMSEQ_norm, simp)

text{*An unbounded sequence's inverse tends to 0*}

text{* standard proof seems easier *}
lemma LIMSEQ_inverse_zero:
      "\<forall>y::real. \<exists>N. \<forall>n \<ge> N. y < f(n) ==> (%n. inverse(f n)) ----> 0"
apply (simp add: LIMSEQ_def, safe)
apply (drule_tac x = "inverse r" in spec, safe)
apply (rule_tac x = N in exI, safe)
apply (drule spec, auto)
apply (frule positive_imp_inverse_positive)
apply (frule order_less_trans, assumption)
apply (frule_tac a = "f n" in positive_imp_inverse_positive)
apply (simp add: abs_if) 
apply (rule_tac t = r in inverse_inverse_eq [THEN subst])
apply (auto intro: inverse_less_iff_less [THEN iffD2]
            simp del: inverse_inverse_eq)
done

text{*The sequence @{term "1/n"} tends to 0 as @{term n} tends to infinity*}

lemma LIMSEQ_inverse_real_of_nat: "(%n. inverse(real(Suc n))) ----> 0"
apply (rule LIMSEQ_inverse_zero, safe)
apply (cut_tac x = y in reals_Archimedean2)
apply (safe, rule_tac x = n in exI)
apply (auto simp add: real_of_nat_Suc)
done

text{*The sequence @{term "r + 1/n"} tends to @{term r} as @{term n} tends to
infinity is now easily proved*}

lemma LIMSEQ_inverse_real_of_nat_add:
     "(%n. r + inverse(real(Suc n))) ----> r"
by (cut_tac LIMSEQ_add [OF LIMSEQ_const LIMSEQ_inverse_real_of_nat], auto)

lemma LIMSEQ_inverse_real_of_nat_add_minus:
     "(%n. r + -inverse(real(Suc n))) ----> r"
by (cut_tac LIMSEQ_add_minus [OF LIMSEQ_const LIMSEQ_inverse_real_of_nat], auto)

lemma LIMSEQ_inverse_real_of_nat_add_minus_mult:
     "(%n. r*( 1 + -inverse(real(Suc n)))) ----> r"
by (cut_tac b=1 in
        LIMSEQ_mult [OF LIMSEQ_const LIMSEQ_inverse_real_of_nat_add_minus], auto)

lemma LIMSEQ_le_const:
  "\<lbrakk>X ----> (x::real); \<exists>N. \<forall>n\<ge>N. a \<le> X n\<rbrakk> \<Longrightarrow> a \<le> x"
apply (rule ccontr, simp only: linorder_not_le)
apply (drule_tac r="a - x" in LIMSEQ_D, simp)
apply clarsimp
apply (drule_tac x="max N no" in spec, drule mp, rule le_maxI1)
apply (drule_tac x="max N no" in spec, drule mp, rule le_maxI2)
apply simp
done

lemma LIMSEQ_le_const2:
  "\<lbrakk>X ----> (x::real); \<exists>N. \<forall>n\<ge>N. X n \<le> a\<rbrakk> \<Longrightarrow> x \<le> a"
apply (subgoal_tac "- a \<le> - x", simp)
apply (rule LIMSEQ_le_const)
apply (erule LIMSEQ_minus)
apply simp
done

lemma LIMSEQ_le:
  "\<lbrakk>X ----> x; Y ----> y; \<exists>N. \<forall>n\<ge>N. X n \<le> Y n\<rbrakk> \<Longrightarrow> x \<le> (y::real)"
apply (subgoal_tac "0 \<le> y - x", simp)
apply (rule LIMSEQ_le_const)
apply (erule (1) LIMSEQ_diff)
apply (simp add: le_diff_eq)
done

subsubsection {* Purely nonstandard proofs *}

lemma NSLIMSEQ_iff:
    "(X ----NS> L) = (\<forall>N \<in> HNatInfinite. ( *f* X) N \<approx> star_of L)"
by (simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_I:
  "(\<And>N. N \<in> HNatInfinite \<Longrightarrow> starfun X N \<approx> star_of L) \<Longrightarrow> X ----NS> L"
by (simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_D:
  "\<lbrakk>X ----NS> L; N \<in> HNatInfinite\<rbrakk> \<Longrightarrow> starfun X N \<approx> star_of L"
by (simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_const: "(%n. k) ----NS> k"
by (simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_add:
      "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n + Y n) ----NS> a + b"
by (auto intro: approx_add simp add: NSLIMSEQ_def starfun_add [symmetric])

lemma NSLIMSEQ_add_const: "f ----NS> a ==> (%n.(f n + b)) ----NS> a + b"
by (simp only: NSLIMSEQ_add NSLIMSEQ_const)

lemma NSLIMSEQ_mult:
  fixes a b :: "'a::real_normed_algebra"
  shows "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n * Y n) ----NS> a * b"
by (auto intro!: approx_mult_HFinite simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_minus: "X ----NS> a ==> (%n. -(X n)) ----NS> -a"
by (auto simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_minus_cancel: "(%n. -(X n)) ----NS> -a ==> X ----NS> a"
by (drule NSLIMSEQ_minus, simp)

(* FIXME: delete *)
lemma NSLIMSEQ_add_minus:
     "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n + -Y n) ----NS> a + -b"
by (simp add: NSLIMSEQ_add NSLIMSEQ_minus)

lemma NSLIMSEQ_diff:
     "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n - Y n) ----NS> a - b"
by (simp add: diff_minus NSLIMSEQ_add NSLIMSEQ_minus)

lemma NSLIMSEQ_diff_const: "f ----NS> a ==> (%n.(f n - b)) ----NS> a - b"
by (simp add: NSLIMSEQ_diff NSLIMSEQ_const)

lemma NSLIMSEQ_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  shows "[| X ----NS> a;  a ~= 0 |] ==> (%n. inverse(X n)) ----NS> inverse(a)"
by (simp add: NSLIMSEQ_def star_of_approx_inverse)

lemma NSLIMSEQ_mult_inverse:
  fixes a b :: "'a::real_normed_field"
  shows
     "[| X ----NS> a;  Y ----NS> b;  b ~= 0 |] ==> (%n. X n / Y n) ----NS> a/b"
by (simp add: NSLIMSEQ_mult NSLIMSEQ_inverse divide_inverse)

lemma starfun_hnorm: "\<And>x. hnorm (( *f* f) x) = ( *f* (\<lambda>x. norm (f x))) x"
by transfer simp

lemma NSLIMSEQ_norm: "X ----NS> a \<Longrightarrow> (\<lambda>n. norm (X n)) ----NS> norm a"
by (simp add: NSLIMSEQ_def starfun_hnorm [symmetric] approx_hnorm)

text{*Uniqueness of limit*}
lemma NSLIMSEQ_unique: "[| X ----NS> a; X ----NS> b |] ==> a = b"
apply (simp add: NSLIMSEQ_def)
apply (drule HNatInfinite_whn [THEN [2] bspec])+
apply (auto dest: approx_trans3)
done

lemma NSLIMSEQ_pow [rule_format]:
  fixes a :: "'a::{real_normed_algebra,recpower}"
  shows "(X ----NS> a) --> ((%n. (X n) ^ m) ----NS> a ^ m)"
apply (induct "m")
apply (auto simp add: power_Suc intro: NSLIMSEQ_mult NSLIMSEQ_const)
done

text{*We can now try and derive a few properties of sequences,
     starting with the limit comparison property for sequences.*}

lemma NSLIMSEQ_le:
       "[| f ----NS> l; g ----NS> m;
           \<exists>N. \<forall>n \<ge> N. f(n) \<le> g(n)
        |] ==> l \<le> (m::real)"
apply (simp add: NSLIMSEQ_def, safe)
apply (drule starfun_le_mono)
apply (drule HNatInfinite_whn [THEN [2] bspec])+
apply (drule_tac x = whn in spec)
apply (drule bex_Infinitesimal_iff2 [THEN iffD2])+
apply clarify
apply (auto intro: hypreal_of_real_le_add_Infininitesimal_cancel2)
done

lemma NSLIMSEQ_le_const: "[| X ----NS> (r::real); \<forall>n. a \<le> X n |] ==> a \<le> r"
by (erule NSLIMSEQ_le [OF NSLIMSEQ_const], auto)

lemma NSLIMSEQ_le_const2: "[| X ----NS> (r::real); \<forall>n. X n \<le> a |] ==> r \<le> a"
by (erule NSLIMSEQ_le [OF _ NSLIMSEQ_const], auto)

text{*Shift a convergent series by 1:
  By the equivalence between Cauchiness and convergence and because
  the successor of an infinite hypernatural is also infinite.*}

lemma NSLIMSEQ_Suc: "f ----NS> l ==> (%n. f(Suc n)) ----NS> l"
apply (unfold NSLIMSEQ_def, safe)
apply (drule_tac x="N + 1" in bspec)
apply (erule HNatInfinite_add)
apply (simp add: starfun_shift_one)
done

lemma NSLIMSEQ_imp_Suc: "(%n. f(Suc n)) ----NS> l ==> f ----NS> l"
apply (unfold NSLIMSEQ_def, safe)
apply (drule_tac x="N - 1" in bspec) 
apply (erule Nats_1 [THEN [2] HNatInfinite_diff])
apply (simp add: starfun_shift_one one_le_HNatInfinite)
done

lemma NSLIMSEQ_Suc_iff: "((%n. f(Suc n)) ----NS> l) = (f ----NS> l)"
by (blast intro: NSLIMSEQ_imp_Suc NSLIMSEQ_Suc)

subsubsection {* Equivalence of @{term LIMSEQ} and @{term NSLIMSEQ} *}

lemma LIMSEQ_NSLIMSEQ:
  assumes X: "X ----> L" shows "X ----NS> L"
proof (rule NSLIMSEQ_I)
  fix N assume N: "N \<in> HNatInfinite"
  have "starfun X N - star_of L \<in> Infinitesimal"
  proof (rule InfinitesimalI2)
    fix r::real assume r: "0 < r"
    from LIMSEQ_D [OF X r]
    obtain no where "\<forall>n\<ge>no. norm (X n - L) < r" ..
    hence "\<forall>n\<ge>star_of no. hnorm (starfun X n - star_of L) < star_of r"
      by transfer
    thus "hnorm (starfun X N - star_of L) < star_of r"
      using N by (simp add: star_of_le_HNatInfinite)
  qed
  thus "starfun X N \<approx> star_of L"
    by (unfold approx_def)
qed

lemma NSLIMSEQ_LIMSEQ:
  assumes X: "X ----NS> L" shows "X ----> L"
proof (rule LIMSEQ_I)
  fix r::real assume r: "0 < r"
  have "\<exists>no. \<forall>n\<ge>no. hnorm (starfun X n - star_of L) < star_of r"
  proof (intro exI allI impI)
    fix n assume "whn \<le> n"
    with HNatInfinite_whn have "n \<in> HNatInfinite"
      by (rule HNatInfinite_upward_closed)
    with X have "starfun X n \<approx> star_of L"
      by (rule NSLIMSEQ_D)
    hence "starfun X n - star_of L \<in> Infinitesimal"
      by (unfold approx_def)
    thus "hnorm (starfun X n - star_of L) < star_of r"
      using r by (rule InfinitesimalD2)
  qed
  thus "\<exists>no. \<forall>n\<ge>no. norm (X n - L) < r"
    by transfer
qed

theorem LIMSEQ_NSLIMSEQ_iff: "(f ----> L) = (f ----NS> L)"
by (blast intro: LIMSEQ_NSLIMSEQ NSLIMSEQ_LIMSEQ)

(* Used once by Integration/Rats.thy in AFP *)
lemma NSLIMSEQ_finite_set:
     "!!(f::nat=>nat). \<forall>n. n \<le> f n ==> finite {n. f n \<le> u}"
by (rule_tac B="{..u}" in finite_subset, auto intro: order_trans)

subsubsection {* Derived theorems about @{term NSLIMSEQ} *}

text{*We prove the NS version from the standard one, since the NS proof
   seems more complicated than the standard one above!*}
lemma NSLIMSEQ_norm_zero: "((\<lambda>n. norm (X n)) ----NS> 0) = (X ----NS> 0)"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_norm_zero)

lemma NSLIMSEQ_rabs_zero: "((%n. \<bar>f n\<bar>) ----NS> 0) = (f ----NS> (0::real))"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_rabs_zero)

text{*Generalization to other limits*}
lemma NSLIMSEQ_imp_rabs: "f ----NS> (l::real) ==> (%n. \<bar>f n\<bar>) ----NS> \<bar>l\<bar>"
apply (simp add: NSLIMSEQ_def)
apply (auto intro: approx_hrabs 
            simp add: starfun_abs)
done

lemma NSLIMSEQ_inverse_zero:
     "\<forall>y::real. \<exists>N. \<forall>n \<ge> N. y < f(n)
      ==> (%n. inverse(f n)) ----NS> 0"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_zero)

lemma NSLIMSEQ_inverse_real_of_nat: "(%n. inverse(real(Suc n))) ----NS> 0"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat)

lemma NSLIMSEQ_inverse_real_of_nat_add:
     "(%n. r + inverse(real(Suc n))) ----NS> r"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat_add)

lemma NSLIMSEQ_inverse_real_of_nat_add_minus:
     "(%n. r + -inverse(real(Suc n))) ----NS> r"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat_add_minus)

lemma NSLIMSEQ_inverse_real_of_nat_add_minus_mult:
     "(%n. r*( 1 + -inverse(real(Suc n)))) ----NS> r"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat_add_minus_mult)


subsection {* Convergence *}

lemma limI: "X ----> L ==> lim X = L"
apply (simp add: lim_def)
apply (blast intro: LIMSEQ_unique)
done

lemma nslimI: "X ----NS> L ==> nslim X = L"
apply (simp add: nslim_def)
apply (blast intro: NSLIMSEQ_unique)
done

lemma lim_nslim_iff: "lim X = nslim X"
by (simp add: lim_def nslim_def LIMSEQ_NSLIMSEQ_iff)

lemma convergentD: "convergent X ==> \<exists>L. (X ----> L)"
by (simp add: convergent_def)

lemma convergentI: "(X ----> L) ==> convergent X"
by (auto simp add: convergent_def)

lemma NSconvergentD: "NSconvergent X ==> \<exists>L. (X ----NS> L)"
by (simp add: NSconvergent_def)

lemma NSconvergentI: "(X ----NS> L) ==> NSconvergent X"
by (auto simp add: NSconvergent_def)

lemma convergent_NSconvergent_iff: "convergent X = NSconvergent X"
by (simp add: convergent_def NSconvergent_def LIMSEQ_NSLIMSEQ_iff)

lemma NSconvergent_NSLIMSEQ_iff: "NSconvergent X = (X ----NS> nslim X)"
by (auto intro: theI NSLIMSEQ_unique simp add: NSconvergent_def nslim_def)

lemma convergent_LIMSEQ_iff: "convergent X = (X ----> lim X)"
by (auto intro: theI LIMSEQ_unique simp add: convergent_def lim_def)

lemma convergent_minus_iff: "(convergent X) = (convergent (%n. -(X n)))"
apply (simp add: convergent_def)
apply (auto dest: LIMSEQ_minus)
apply (drule LIMSEQ_minus, auto)
done


subsection {* Bounded Monotonic Sequences *}

text{*Subsequence (alternative definition, (e.g. Hoskins)*}

lemma subseq_Suc_iff: "subseq f = (\<forall>n. (f n) < (f (Suc n)))"
apply (simp add: subseq_def)
apply (auto dest!: less_imp_Suc_add)
apply (induct_tac k)
apply (auto intro: less_trans)
done

lemma monoseq_Suc:
   "monoseq X = ((\<forall>n. X n \<le> X (Suc n))
                 | (\<forall>n. X (Suc n) \<le> X n))"
apply (simp add: monoseq_def)
apply (auto dest!: le_imp_less_or_eq)
apply (auto intro!: lessI [THEN less_imp_le] dest!: less_imp_Suc_add)
apply (induct_tac "ka")
apply (auto intro: order_trans)
apply (erule contrapos_np)
apply (induct_tac "k")
apply (auto intro: order_trans)
done

lemma monoI1: "\<forall>m. \<forall> n \<ge> m. X m \<le> X n ==> monoseq X"
by (simp add: monoseq_def)

lemma monoI2: "\<forall>m. \<forall> n \<ge> m. X n \<le> X m ==> monoseq X"
by (simp add: monoseq_def)

lemma mono_SucI1: "\<forall>n. X n \<le> X (Suc n) ==> monoseq X"
by (simp add: monoseq_Suc)

lemma mono_SucI2: "\<forall>n. X (Suc n) \<le> X n ==> monoseq X"
by (simp add: monoseq_Suc)

text{*Bounded Sequence*}

lemma BseqD: "Bseq X ==> \<exists>K. 0 < K & (\<forall>n. norm (X n) \<le> K)"
by (simp add: Bseq_def)

lemma BseqI: "[| 0 < K; \<forall>n. norm (X n) \<le> K |] ==> Bseq X"
by (auto simp add: Bseq_def)

lemma lemma_NBseq_def:
     "(\<exists>K > 0. \<forall>n. norm (X n) \<le> K) =
      (\<exists>N. \<forall>n. norm (X n) \<le> real(Suc N))"
apply auto
 prefer 2 apply force
apply (cut_tac x = K in reals_Archimedean2, clarify)
apply (rule_tac x = n in exI, clarify)
apply (drule_tac x = na in spec)
apply (auto simp add: real_of_nat_Suc)
done

text{* alternative definition for Bseq *}
lemma Bseq_iff: "Bseq X = (\<exists>N. \<forall>n. norm (X n) \<le> real(Suc N))"
apply (simp add: Bseq_def)
apply (simp (no_asm) add: lemma_NBseq_def)
done

lemma lemma_NBseq_def2:
     "(\<exists>K > 0. \<forall>n. norm (X n) \<le> K) = (\<exists>N. \<forall>n. norm (X n) < real(Suc N))"
apply (subst lemma_NBseq_def, auto)
apply (rule_tac x = "Suc N" in exI)
apply (rule_tac [2] x = N in exI)
apply (auto simp add: real_of_nat_Suc)
 prefer 2 apply (blast intro: order_less_imp_le)
apply (drule_tac x = n in spec, simp)
done

(* yet another definition for Bseq *)
lemma Bseq_iff1a: "Bseq X = (\<exists>N. \<forall>n. norm (X n) < real(Suc N))"
by (simp add: Bseq_def lemma_NBseq_def2)

lemma NSBseqD: "[| NSBseq X;  N: HNatInfinite |] ==> ( *f* X) N : HFinite"
by (simp add: NSBseq_def)

lemma Standard_subset_HFinite: "Standard \<subseteq> HFinite"
unfolding Standard_def by auto

lemma NSBseqD2: "NSBseq X \<Longrightarrow> ( *f* X) N \<in> HFinite"
apply (cases "N \<in> HNatInfinite")
apply (erule (1) NSBseqD)
apply (rule subsetD [OF Standard_subset_HFinite])
apply (simp add: HNatInfinite_def Nats_eq_Standard)
done

lemma NSBseqI: "\<forall>N \<in> HNatInfinite. ( *f* X) N : HFinite ==> NSBseq X"
by (simp add: NSBseq_def)

text{*The standard definition implies the nonstandard definition*}

lemma lemma_Bseq: "\<forall>n. norm (X n) \<le> K ==> \<forall>n. norm(X((f::nat=>nat) n)) \<le> K"
by auto

lemma Bseq_NSBseq: "Bseq X ==> NSBseq X"
proof (unfold NSBseq_def, safe)
  assume X: "Bseq X"
  fix N assume N: "N \<in> HNatInfinite"
  from BseqD [OF X] obtain K where "\<forall>n. norm (X n) \<le> K" by fast
  hence "\<forall>N. hnorm (starfun X N) \<le> star_of K" by transfer
  hence "hnorm (starfun X N) \<le> star_of K" by simp
  also have "star_of K < star_of (K + 1)" by simp
  finally have "\<exists>x\<in>Reals. hnorm (starfun X N) < x" by (rule bexI, simp)
  thus "starfun X N \<in> HFinite" by (simp add: HFinite_def)
qed

text{*The nonstandard definition implies the standard definition*}

lemma SReal_less_omega: "r \<in> \<real> \<Longrightarrow> r < \<omega>"
apply (insert HInfinite_omega)
apply (simp add: HInfinite_def)
apply (simp add: order_less_imp_le)
done

lemma NSBseq_Bseq: "NSBseq X \<Longrightarrow> Bseq X"
proof (rule ccontr)
  let ?n = "\<lambda>K. LEAST n. K < norm (X n)"
  assume "NSBseq X"
  hence finite: "( *f* X) (( *f* ?n) \<omega>) \<in> HFinite"
    by (rule NSBseqD2)
  assume "\<not> Bseq X"
  hence "\<forall>K>0. \<exists>n. K < norm (X n)"
    by (simp add: Bseq_def linorder_not_le)
  hence "\<forall>K>0. K < norm (X (?n K))"
    by (auto intro: LeastI_ex)
  hence "\<forall>K>0. K < hnorm (( *f* X) (( *f* ?n) K))"
    by transfer
  hence "\<omega> < hnorm (( *f* X) (( *f* ?n) \<omega>))"
    by simp
  hence "\<forall>r\<in>\<real>. r < hnorm (( *f* X) (( *f* ?n) \<omega>))"
    by (simp add: order_less_trans [OF SReal_less_omega])
  hence "( *f* X) (( *f* ?n) \<omega>) \<in> HInfinite"
    by (simp add: HInfinite_def)
  with finite show "False"
    by (simp add: HFinite_HInfinite_iff)
qed

text{* Equivalence of nonstandard and standard definitions
  for a bounded sequence*}
lemma Bseq_NSBseq_iff: "(Bseq X) = (NSBseq X)"
by (blast intro!: NSBseq_Bseq Bseq_NSBseq)

text{*A convergent sequence is bounded: 
 Boundedness as a necessary condition for convergence. 
 The nonstandard version has no existential, as usual *}

lemma NSconvergent_NSBseq: "NSconvergent X ==> NSBseq X"
apply (simp add: NSconvergent_def NSBseq_def NSLIMSEQ_def)
apply (blast intro: HFinite_star_of approx_sym approx_HFinite)
done

text{*Standard Version: easily now proved using equivalence of NS and
 standard definitions *}
lemma convergent_Bseq: "convergent X ==> Bseq X"
by (simp add: NSconvergent_NSBseq convergent_NSconvergent_iff Bseq_NSBseq_iff)

subsubsection{*Upper Bounds and Lubs of Bounded Sequences*}

lemma Bseq_isUb:
  "!!(X::nat=>real). Bseq X ==> \<exists>U. isUb (UNIV::real set) {x. \<exists>n. X n = x} U"
by (auto intro: isUbI setleI simp add: Bseq_def abs_le_interval_iff)


text{* Use completeness of reals (supremum property)
   to show that any bounded sequence has a least upper bound*}

lemma Bseq_isLub:
  "!!(X::nat=>real). Bseq X ==>
   \<exists>U. isLub (UNIV::real set) {x. \<exists>n. X n = x} U"
by (blast intro: reals_complete Bseq_isUb)

lemma NSBseq_isUb: "NSBseq X ==> \<exists>U::real. isUb UNIV {x. \<exists>n. X n = x} U"
by (simp add: Bseq_NSBseq_iff [symmetric] Bseq_isUb)

lemma NSBseq_isLub: "NSBseq X ==> \<exists>U::real. isLub UNIV {x. \<exists>n. X n = x} U"
by (simp add: Bseq_NSBseq_iff [symmetric] Bseq_isLub)


subsubsection{*A Bounded and Monotonic Sequence Converges*}

lemma lemma_converg1:
     "!!(X::nat=>real). [| \<forall>m. \<forall> n \<ge> m. X m \<le> X n;
                  isLub (UNIV::real set) {x. \<exists>n. X n = x} (X ma)
               |] ==> \<forall>n \<ge> ma. X n = X ma"
apply safe
apply (drule_tac y = "X n" in isLubD2)
apply (blast dest: order_antisym)+
done

text{* The best of both worlds: Easier to prove this result as a standard
   theorem and then use equivalence to "transfer" it into the
   equivalent nonstandard form if needed!*}

lemma Bmonoseq_LIMSEQ: "\<forall>n. m \<le> n --> X n = X m ==> \<exists>L. (X ----> L)"
apply (simp add: LIMSEQ_def)
apply (rule_tac x = "X m" in exI, safe)
apply (rule_tac x = m in exI, safe)
apply (drule spec, erule impE, auto)
done

text{*Now, the same theorem in terms of NS limit *}
lemma Bmonoseq_NSLIMSEQ: "\<forall>n \<ge> m. X n = X m ==> \<exists>L. (X ----NS> L)"
by (auto dest!: Bmonoseq_LIMSEQ simp add: LIMSEQ_NSLIMSEQ_iff)

lemma lemma_converg2:
   "!!(X::nat=>real).
    [| \<forall>m. X m ~= U;  isLub UNIV {x. \<exists>n. X n = x} U |] ==> \<forall>m. X m < U"
apply safe
apply (drule_tac y = "X m" in isLubD2)
apply (auto dest!: order_le_imp_less_or_eq)
done

lemma lemma_converg3: "!!(X ::nat=>real). \<forall>m. X m \<le> U ==> isUb UNIV {x. \<exists>n. X n = x} U"
by (rule setleI [THEN isUbI], auto)

text{* FIXME: @{term "U - T < U"} is redundant *}
lemma lemma_converg4: "!!(X::nat=> real).
               [| \<forall>m. X m ~= U;
                  isLub UNIV {x. \<exists>n. X n = x} U;
                  0 < T;
                  U + - T < U
               |] ==> \<exists>m. U + -T < X m & X m < U"
apply (drule lemma_converg2, assumption)
apply (rule ccontr, simp)
apply (simp add: linorder_not_less)
apply (drule lemma_converg3)
apply (drule isLub_le_isUb, assumption)
apply (auto dest: order_less_le_trans)
done

text{*A standard proof of the theorem for monotone increasing sequence*}

lemma Bseq_mono_convergent:
     "[| Bseq X; \<forall>m. \<forall>n \<ge> m. X m \<le> X n |] ==> convergent (X::nat=>real)"
apply (simp add: convergent_def)
apply (frule Bseq_isLub, safe)
apply (case_tac "\<exists>m. X m = U", auto)
apply (blast dest: lemma_converg1 Bmonoseq_LIMSEQ)
(* second case *)
apply (rule_tac x = U in exI)
apply (subst LIMSEQ_iff, safe)
apply (frule lemma_converg2, assumption)
apply (drule lemma_converg4, auto)
apply (rule_tac x = m in exI, safe)
apply (subgoal_tac "X m \<le> X n")
 prefer 2 apply blast
apply (drule_tac x=n and P="%m. X m < U" in spec, arith)
done

text{*Nonstandard version of the theorem*}

lemma NSBseq_mono_NSconvergent:
     "[| NSBseq X; \<forall>m. \<forall>n \<ge> m. X m \<le> X n |] ==> NSconvergent (X::nat=>real)"
by (auto intro: Bseq_mono_convergent 
         simp add: convergent_NSconvergent_iff [symmetric] 
                   Bseq_NSBseq_iff [symmetric])

lemma Bseq_minus_iff: "Bseq (%n. -(X n)) = Bseq X"
by (simp add: Bseq_def)

text{*Main monotonicity theorem*}
lemma Bseq_monoseq_convergent: "[| Bseq X; monoseq X |] ==> convergent X"
apply (simp add: monoseq_def, safe)
apply (rule_tac [2] convergent_minus_iff [THEN ssubst])
apply (drule_tac [2] Bseq_minus_iff [THEN ssubst])
apply (auto intro!: Bseq_mono_convergent)
done

subsubsection{*A Few More Equivalence Theorems for Boundedness*}

text{*alternative formulation for boundedness*}
lemma Bseq_iff2: "Bseq X = (\<exists>k > 0. \<exists>x. \<forall>n. norm (X(n) + -x) \<le> k)"
apply (unfold Bseq_def, safe)
apply (rule_tac [2] x = "k + norm x" in exI)
apply (rule_tac x = K in exI, simp)
apply (rule exI [where x = 0], auto)
apply (erule order_less_le_trans, simp)
apply (drule_tac x=n in spec, fold diff_def)
apply (drule order_trans [OF norm_triangle_ineq2])
apply simp
done

text{*alternative formulation for boundedness*}
lemma Bseq_iff3: "Bseq X = (\<exists>k > 0. \<exists>N. \<forall>n. norm(X(n) + -X(N)) \<le> k)"
apply safe
apply (simp add: Bseq_def, safe)
apply (rule_tac x = "K + norm (X N)" in exI)
apply auto
apply (erule order_less_le_trans, simp)
apply (rule_tac x = N in exI, safe)
apply (drule_tac x = n in spec)
apply (rule order_trans [OF norm_triangle_ineq], simp)
apply (auto simp add: Bseq_iff2)
done

lemma BseqI2: "(\<forall>n. k \<le> f n & f n \<le> (K::real)) ==> Bseq f"
apply (simp add: Bseq_def)
apply (rule_tac x = " (\<bar>k\<bar> + \<bar>K\<bar>) + 1" in exI, auto)
apply (drule_tac x = n in spec, arith)
done


subsection {* Cauchy Sequences *}

lemma CauchyI:
  "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (X m - X n) < e) \<Longrightarrow> Cauchy X"
by (simp add: Cauchy_def)

lemma CauchyD:
  "\<lbrakk>Cauchy X; 0 < e\<rbrakk> \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (X m - X n) < e"
by (simp add: Cauchy_def)

lemma NSCauchyI:
  "(\<And>M N. \<lbrakk>M \<in> HNatInfinite; N \<in> HNatInfinite\<rbrakk> \<Longrightarrow> starfun X M \<approx> starfun X N)
   \<Longrightarrow> NSCauchy X"
by (simp add: NSCauchy_def)

lemma NSCauchyD:
  "\<lbrakk>NSCauchy X; M \<in> HNatInfinite; N \<in> HNatInfinite\<rbrakk>
   \<Longrightarrow> starfun X M \<approx> starfun X N"
by (simp add: NSCauchy_def)

subsubsection{*Equivalence Between NS and Standard*}

lemma Cauchy_NSCauchy:
  assumes X: "Cauchy X" shows "NSCauchy X"
proof (rule NSCauchyI)
  fix M assume M: "M \<in> HNatInfinite"
  fix N assume N: "N \<in> HNatInfinite"
  have "starfun X M - starfun X N \<in> Infinitesimal"
  proof (rule InfinitesimalI2)
    fix r :: real assume r: "0 < r"
    from CauchyD [OF X r]
    obtain k where "\<forall>m\<ge>k. \<forall>n\<ge>k. norm (X m - X n) < r" ..
    hence "\<forall>m\<ge>star_of k. \<forall>n\<ge>star_of k.
           hnorm (starfun X m - starfun X n) < star_of r"
      by transfer
    thus "hnorm (starfun X M - starfun X N) < star_of r"
      using M N by (simp add: star_of_le_HNatInfinite)
  qed
  thus "starfun X M \<approx> starfun X N"
    by (unfold approx_def)
qed

lemma NSCauchy_Cauchy:
  assumes X: "NSCauchy X" shows "Cauchy X"
proof (rule CauchyI)
  fix r::real assume r: "0 < r"
  have "\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. hnorm (starfun X m - starfun X n) < star_of r"
  proof (intro exI allI impI)
    fix M assume "whn \<le> M"
    with HNatInfinite_whn have M: "M \<in> HNatInfinite"
      by (rule HNatInfinite_upward_closed)
    fix N assume "whn \<le> N"
    with HNatInfinite_whn have N: "N \<in> HNatInfinite"
      by (rule HNatInfinite_upward_closed)
    from X M N have "starfun X M \<approx> starfun X N"
      by (rule NSCauchyD)
    hence "starfun X M - starfun X N \<in> Infinitesimal"
      by (unfold approx_def)
    thus "hnorm (starfun X M - starfun X N) < star_of r"
      using r by (rule InfinitesimalD2)
  qed
  thus "\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. norm (X m - X n) < r"
    by transfer
qed

theorem NSCauchy_Cauchy_iff: "NSCauchy X = Cauchy X"
by (blast intro!: NSCauchy_Cauchy Cauchy_NSCauchy)

subsubsection {* Cauchy Sequences are Bounded *}

text{*A Cauchy sequence is bounded -- this is the standard
  proof mechanization rather than the nonstandard proof*}

lemma lemmaCauchy: "\<forall>n \<ge> M. norm (X M - X n) < (1::real)
          ==>  \<forall>n \<ge> M. norm (X n :: 'a::real_normed_vector) < 1 + norm (X M)"
apply (clarify, drule spec, drule (1) mp)
apply (simp only: norm_minus_commute)
apply (drule order_le_less_trans [OF norm_triangle_ineq2])
apply simp
done

lemma Cauchy_Bseq: "Cauchy X ==> Bseq X"
apply (simp add: Cauchy_def)
apply (drule spec, drule mp, rule zero_less_one, safe)
apply (drule_tac x="M" in spec, simp)
apply (drule lemmaCauchy)
apply (rule_tac k="M" in Bseq_offset)
apply (simp add: Bseq_def)
apply (rule_tac x="1 + norm (X M)" in exI)
apply (rule conjI, rule order_less_le_trans [OF zero_less_one], simp)
apply (simp add: order_less_imp_le)
done

text{*A Cauchy sequence is bounded -- nonstandard version*}

lemma NSCauchy_NSBseq: "NSCauchy X ==> NSBseq X"
by (simp add: Cauchy_Bseq Bseq_NSBseq_iff [symmetric] NSCauchy_Cauchy_iff)

subsubsection {* Cauchy Sequences are Convergent *}

axclass banach \<subseteq> real_normed_vector
  Cauchy_convergent: "Cauchy X \<Longrightarrow> convergent X"

text{*Equivalence of Cauchy criterion and convergence:
  We will prove this using our NS formulation which provides a
  much easier proof than using the standard definition. We do not
  need to use properties of subsequences such as boundedness,
  monotonicity etc... Compare with Harrison's corresponding proof
  in HOL which is much longer and more complicated. Of course, we do
  not have problems which he encountered with guessing the right
  instantiations for his 'espsilon-delta' proof(s) in this case
  since the NS formulations do not involve existential quantifiers.*}

lemma NSconvergent_NSCauchy: "NSconvergent X \<Longrightarrow> NSCauchy X"
apply (simp add: NSconvergent_def NSLIMSEQ_def NSCauchy_def, safe)
apply (auto intro: approx_trans2)
done

theorem LIMSEQ_imp_Cauchy:
  assumes X: "X ----> a" shows "Cauchy X"
proof (rule CauchyI)
  fix e::real assume "0 < e"
  hence "0 < e/2" by simp
  with X have "\<exists>N. \<forall>n\<ge>N. norm (X n - a) < e/2" by (rule LIMSEQ_D)
  then obtain N where N: "\<forall>n\<ge>N. norm (X n - a) < e/2" ..
  show "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. norm (X m - X n) < e"
  proof (intro exI allI impI)
    fix m assume "N \<le> m"
    hence m: "norm (X m - a) < e/2" using N by fast
    fix n assume "N \<le> n"
    hence n: "norm (X n - a) < e/2" using N by fast
    have "norm (X m - X n) = norm ((X m - a) - (X n - a))" by simp
    also have "\<dots> \<le> norm (X m - a) + norm (X n - a)"
      by (rule norm_triangle_ineq4)
    also from m n have "\<dots> < e/2 + e/2" by (rule add_strict_mono)
    also have "e/2 + e/2 = e" by simp
    finally show "norm (X m - X n) < e" .
  qed
qed

lemma convergent_Cauchy: "convergent X \<Longrightarrow> Cauchy X"
unfolding convergent_def
by (erule exE, erule LIMSEQ_imp_Cauchy)

lemma real_NSCauchy_NSconvergent:
  fixes X :: "nat \<Rightarrow> real"
  shows "NSCauchy X \<Longrightarrow> NSconvergent X"
apply (simp add: NSconvergent_def NSLIMSEQ_def)
apply (frule NSCauchy_NSBseq)
apply (simp add: NSBseq_def NSCauchy_def)
apply (drule HNatInfinite_whn [THEN [2] bspec])
apply (drule HNatInfinite_whn [THEN [2] bspec])
apply (auto dest!: st_part_Ex simp add: SReal_iff)
apply (blast intro: approx_trans3)
done

text {*
Proof that Cauchy sequences converge based on the one from
http://pirate.shu.edu/~wachsmut/ira/numseq/proofs/cauconv.html
*}

text {*
  If sequence @{term "X"} is Cauchy, then its limit is the lub of
  @{term "{r::real. \<exists>N. \<forall>n\<ge>N. r < X n}"}
*}

lemma isUb_UNIV_I: "(\<And>y. y \<in> S \<Longrightarrow> y \<le> u) \<Longrightarrow> isUb UNIV S u"
by (simp add: isUbI setleI)

lemma real_abs_diff_less_iff:
  "(\<bar>x - a\<bar> < (r::real)) = (a - r < x \<and> x < a + r)"
by auto

locale (open) real_Cauchy =
  fixes X :: "nat \<Rightarrow> real"
  assumes X: "Cauchy X"
  fixes S :: "real set"
  defines S_def: "S \<equiv> {x::real. \<exists>N. \<forall>n\<ge>N. x < X n}"

lemma (in real_Cauchy) mem_S: "\<forall>n\<ge>N. x < X n \<Longrightarrow> x \<in> S"
by (unfold S_def, auto)

lemma (in real_Cauchy) bound_isUb:
  assumes N: "\<forall>n\<ge>N. X n < x"
  shows "isUb UNIV S x"
proof (rule isUb_UNIV_I)
  fix y::real assume "y \<in> S"
  hence "\<exists>M. \<forall>n\<ge>M. y < X n"
    by (simp add: S_def)
  then obtain M where "\<forall>n\<ge>M. y < X n" ..
  hence "y < X (max M N)" by simp
  also have "\<dots> < x" using N by simp
  finally show "y \<le> x"
    by (rule order_less_imp_le)
qed

lemma (in real_Cauchy) isLub_ex: "\<exists>u. isLub UNIV S u"
proof (rule reals_complete)
  obtain N where "\<forall>m\<ge>N. \<forall>n\<ge>N. norm (X m - X n) < 1"
    using CauchyD [OF X zero_less_one] by fast
  hence N: "\<forall>n\<ge>N. norm (X n - X N) < 1" by simp
  show "\<exists>x. x \<in> S"
  proof
    from N have "\<forall>n\<ge>N. X N - 1 < X n"
      by (simp add: real_abs_diff_less_iff)
    thus "X N - 1 \<in> S" by (rule mem_S)
  qed
  show "\<exists>u. isUb UNIV S u"
  proof
    from N have "\<forall>n\<ge>N. X n < X N + 1"
      by (simp add: real_abs_diff_less_iff)
    thus "isUb UNIV S (X N + 1)"
      by (rule bound_isUb)
  qed
qed

lemma (in real_Cauchy) isLub_imp_LIMSEQ:
  assumes x: "isLub UNIV S x"
  shows "X ----> x"
proof (rule LIMSEQ_I)
  fix r::real assume "0 < r"
  hence r: "0 < r/2" by simp
  obtain N where "\<forall>n\<ge>N. \<forall>m\<ge>N. norm (X n - X m) < r/2"
    using CauchyD [OF X r] by fast
  hence "\<forall>n\<ge>N. norm (X n - X N) < r/2" by simp
  hence N: "\<forall>n\<ge>N. X N - r/2 < X n \<and> X n < X N + r/2"
    by (simp only: real_norm_def real_abs_diff_less_iff)

  from N have "\<forall>n\<ge>N. X N - r/2 < X n" by fast
  hence "X N - r/2 \<in> S" by (rule mem_S)
  hence "X N - r/2 \<le> x" using x isLub_isUb isUbD by fast
  hence 1: "X N + r/2 \<le> x + r" by simp

  from N have "\<forall>n\<ge>N. X n < X N + r/2" by fast
  hence "isUb UNIV S (X N + r/2)" by (rule bound_isUb)
  hence "x \<le> X N + r/2" using x isLub_le_isUb by fast
  hence 2: "x - r \<le> X N - r/2" by simp

  show "\<exists>N. \<forall>n\<ge>N. norm (X n - x) < r"
  proof (intro exI allI impI)
    fix n assume n: "N \<le> n"
    from N n have 3: "X n < X N + r/2" by simp
    from N n have 4: "X N - r/2 < X n" by simp
    show "norm (X n - x) < r"
      using order_less_le_trans [OF 3 1]
            order_le_less_trans [OF 2 4]
      by (simp add: real_abs_diff_less_iff)
  qed
qed

lemma (in real_Cauchy) LIMSEQ_ex: "\<exists>x. X ----> x"
proof -
  obtain x where "isLub UNIV S x"
    using isLub_ex by fast
  hence "X ----> x"
    by (rule isLub_imp_LIMSEQ)
  thus ?thesis ..
qed

lemma real_Cauchy_convergent:
  fixes X :: "nat \<Rightarrow> real"
  shows "Cauchy X \<Longrightarrow> convergent X"
unfolding convergent_def by (rule real_Cauchy.LIMSEQ_ex)

instance real :: banach
by intro_classes (rule real_Cauchy_convergent)

lemma NSCauchy_NSconvergent:
  fixes X :: "nat \<Rightarrow> 'a::banach"
  shows "NSCauchy X \<Longrightarrow> NSconvergent X"
apply (drule NSCauchy_Cauchy [THEN Cauchy_convergent])
apply (erule convergent_NSconvergent_iff [THEN iffD1])
done

lemma NSCauchy_NSconvergent_iff:
  fixes X :: "nat \<Rightarrow> 'a::banach"
  shows "NSCauchy X = NSconvergent X"
by (fast intro: NSCauchy_NSconvergent NSconvergent_NSCauchy)

lemma Cauchy_convergent_iff:
  fixes X :: "nat \<Rightarrow> 'a::banach"
  shows "Cauchy X = convergent X"
by (fast intro: Cauchy_convergent convergent_Cauchy)


subsection {* Power Sequences *}

text{*The sequence @{term "x^n"} tends to 0 if @{term "0\<le>x"} and @{term
"x<1"}.  Proof will use (NS) Cauchy equivalence for convergence and
  also fact that bounded and monotonic sequence converges.*}

lemma Bseq_realpow: "[| 0 \<le> (x::real); x \<le> 1 |] ==> Bseq (%n. x ^ n)"
apply (simp add: Bseq_def)
apply (rule_tac x = 1 in exI)
apply (simp add: power_abs)
apply (auto dest: power_mono intro: order_less_imp_le simp add: abs_if)
done

lemma monoseq_realpow: "[| 0 \<le> x; x \<le> 1 |] ==> monoseq (%n. x ^ n)"
apply (clarify intro!: mono_SucI2)
apply (cut_tac n = n and N = "Suc n" and a = x in power_decreasing, auto)
done

lemma convergent_realpow:
  "[| 0 \<le> (x::real); x \<le> 1 |] ==> convergent (%n. x ^ n)"
by (blast intro!: Bseq_monoseq_convergent Bseq_realpow monoseq_realpow)

text{* We now use NS criterion to bring proof of theorem through *}

lemma NSLIMSEQ_realpow_zero:
  "[| 0 \<le> (x::real); x < 1 |] ==> (%n. x ^ n) ----NS> 0"
apply (simp add: NSLIMSEQ_def)
apply (auto dest!: convergent_realpow simp add: convergent_NSconvergent_iff)
apply (frule NSconvergentD)
apply (auto simp add: NSLIMSEQ_def NSCauchy_NSconvergent_iff [symmetric] NSCauchy_def starfun_pow)
apply (frule HNatInfinite_add_one)
apply (drule bspec, assumption)
apply (drule bspec, assumption)
apply (drule_tac x = "N + (1::hypnat) " in bspec, assumption)
apply (simp add: hyperpow_add)
apply (drule approx_mult_subst_star_of, assumption)
apply (drule approx_trans3, assumption)
apply (auto simp del: star_of_mult simp add: star_of_mult [symmetric])
done

lemma LIMSEQ_inverse_realpow_zero_lemma:
  fixes x :: real
  assumes x: "0 \<le> x"
  shows "real n * x + 1 \<le> (x + 1) ^ n"
apply (induct n)
apply simp
apply simp
apply (rule order_trans)
prefer 2
apply (erule mult_left_mono)
apply (rule add_increasing [OF x], simp)
apply (simp add: real_of_nat_Suc)
apply (simp add: ring_distrib)
apply (simp add: mult_nonneg_nonneg x)
done

lemma LIMSEQ_inverse_realpow_zero:
  "1 < (x::real) \<Longrightarrow> (\<lambda>n. inverse (x ^ n)) ----> 0"
proof (rule LIMSEQ_inverse_zero [rule_format])
  fix y :: real
  assume x: "1 < x"
  hence "0 < x - 1" by simp
  hence "\<forall>y. \<exists>N::nat. y < real N * (x - 1)"
    by (rule reals_Archimedean3)
  hence "\<exists>N::nat. y < real N * (x - 1)" ..
  then obtain N::nat where "y < real N * (x - 1)" ..
  also have "\<dots> \<le> real N * (x - 1) + 1" by simp
  also have "\<dots> \<le> (x - 1 + 1) ^ N"
    by (rule LIMSEQ_inverse_realpow_zero_lemma, cut_tac x, simp)
  also have "\<dots> = x ^ N" by simp
  finally have "y < x ^ N" .
  hence "\<forall>n\<ge>N. y < x ^ n"
    apply clarify
    apply (erule order_less_le_trans)
    apply (erule power_increasing)
    apply (rule order_less_imp_le [OF x])
    done
  thus "\<exists>N. \<forall>n\<ge>N. y < x ^ n" ..
qed

lemma LIMSEQ_realpow_zero:
  "\<lbrakk>0 \<le> (x::real); x < 1\<rbrakk> \<Longrightarrow> (\<lambda>n. x ^ n) ----> 0"
proof (cases)
  assume "x = 0"
  hence "(\<lambda>n. x ^ Suc n) ----> 0" by (simp add: LIMSEQ_const)
  thus ?thesis by (rule LIMSEQ_imp_Suc)
next
  assume "0 \<le> x" and "x \<noteq> 0"
  hence x0: "0 < x" by simp
  assume x1: "x < 1"
  from x0 x1 have "1 < inverse x"
    by (rule real_inverse_gt_one)
  hence "(\<lambda>n. inverse (inverse x ^ n)) ----> 0"
    by (rule LIMSEQ_inverse_realpow_zero)
  thus ?thesis by (simp add: power_inverse)
qed

lemma LIMSEQ_power_zero:
  fixes x :: "'a::{real_normed_div_algebra,recpower}"
  shows "norm x < 1 \<Longrightarrow> (\<lambda>n. x ^ n) ----> 0"
apply (drule LIMSEQ_realpow_zero [OF norm_ge_zero])
apply (simp add: norm_power [symmetric] LIMSEQ_norm_zero)
done

lemma LIMSEQ_divide_realpow_zero:
  "1 < (x::real) ==> (%n. a / (x ^ n)) ----> 0"
apply (cut_tac a = a and x1 = "inverse x" in
        LIMSEQ_mult [OF LIMSEQ_const LIMSEQ_realpow_zero])
apply (auto simp add: divide_inverse power_inverse)
apply (simp add: inverse_eq_divide pos_divide_less_eq)
done

text{*Limit of @{term "c^n"} for @{term"\<bar>c\<bar> < 1"}*}

lemma LIMSEQ_rabs_realpow_zero: "\<bar>c\<bar> < (1::real) ==> (%n. \<bar>c\<bar> ^ n) ----> 0"
by (rule LIMSEQ_realpow_zero [OF abs_ge_zero])

lemma NSLIMSEQ_rabs_realpow_zero: "\<bar>c\<bar> < (1::real) ==> (%n. \<bar>c\<bar> ^ n) ----NS> 0"
by (simp add: LIMSEQ_rabs_realpow_zero LIMSEQ_NSLIMSEQ_iff [symmetric])

lemma LIMSEQ_rabs_realpow_zero2: "\<bar>c\<bar> < (1::real) ==> (%n. c ^ n) ----> 0"
apply (rule LIMSEQ_rabs_zero [THEN iffD1])
apply (auto intro: LIMSEQ_rabs_realpow_zero simp add: power_abs)
done

lemma NSLIMSEQ_rabs_realpow_zero2: "\<bar>c\<bar> < (1::real) ==> (%n. c ^ n) ----NS> 0"
by (simp add: LIMSEQ_rabs_realpow_zero2 LIMSEQ_NSLIMSEQ_iff [symmetric])

(***---------------------------------------------------------------
    Theorems proved by Harrison in HOL that we do not need
    in order to prove equivalence between Cauchy criterion
    and convergence:
 -- Show that every sequence contains a monotonic subsequence
Goal "\<exists>f. subseq f & monoseq (%n. s (f n))"
 -- Show that a subsequence of a bounded sequence is bounded
Goal "Bseq X ==> Bseq (%n. X (f n))";
 -- Show we can take subsequential terms arbitrarily far
    up a sequence
Goal "subseq f ==> n \<le> f(n)";
Goal "subseq f ==> \<exists>n. N1 \<le> n & N2 \<le> f(n)";
 ---------------------------------------------------------------***)

end
