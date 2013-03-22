(*  Title       : Limits.thy
    Author      : Brian Huffman
*)

header {* Filters and Limits *}

theory Limits
imports RealVector
begin

definition at_infinity :: "'a::real_normed_vector filter" where
  "at_infinity = Abs_filter (\<lambda>P. \<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x)"

lemma eventually_at_infinity:
  "eventually P at_infinity \<longleftrightarrow> (\<exists>b. \<forall>x. b \<le> norm x \<longrightarrow> P x)"
unfolding at_infinity_def
proof (rule eventually_Abs_filter, rule is_filter.intro)
  fix P Q :: "'a \<Rightarrow> bool"
  assume "\<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x" and "\<exists>s. \<forall>x. s \<le> norm x \<longrightarrow> Q x"
  then obtain r s where
    "\<forall>x. r \<le> norm x \<longrightarrow> P x" and "\<forall>x. s \<le> norm x \<longrightarrow> Q x" by auto
  then have "\<forall>x. max r s \<le> norm x \<longrightarrow> P x \<and> Q x" by simp
  then show "\<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x \<and> Q x" ..
qed auto

lemma at_infinity_eq_at_top_bot:
  "(at_infinity \<Colon> real filter) = sup at_top at_bot"
  unfolding sup_filter_def at_infinity_def eventually_at_top_linorder eventually_at_bot_linorder
proof (intro arg_cong[where f=Abs_filter] ext iffI)
  fix P :: "real \<Rightarrow> bool" assume "\<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x"
  then guess r ..
  then have "(\<forall>x\<ge>r. P x) \<and> (\<forall>x\<le>-r. P x)" by auto
  then show "(\<exists>r. \<forall>x\<ge>r. P x) \<and> (\<exists>r. \<forall>x\<le>r. P x)" by auto
next
  fix P :: "real \<Rightarrow> bool" assume "(\<exists>r. \<forall>x\<ge>r. P x) \<and> (\<exists>r. \<forall>x\<le>r. P x)"
  then obtain p q where "\<forall>x\<ge>p. P x" "\<forall>x\<le>q. P x" by auto
  then show "\<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x"
    by (intro exI[of _ "max p (-q)"])
       (auto simp: abs_real_def)
qed

lemma at_top_le_at_infinity:
  "at_top \<le> (at_infinity :: real filter)"
  unfolding at_infinity_eq_at_top_bot by simp

lemma at_bot_le_at_infinity:
  "at_bot \<le> (at_infinity :: real filter)"
  unfolding at_infinity_eq_at_top_bot by simp

subsection {* Boundedness *}

definition Bfun :: "('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a filter \<Rightarrow> bool"
  where "Bfun f F = (\<exists>K>0. eventually (\<lambda>x. norm (f x) \<le> K) F)"

lemma BfunI:
  assumes K: "eventually (\<lambda>x. norm (f x) \<le> K) F" shows "Bfun f F"
unfolding Bfun_def
proof (intro exI conjI allI)
  show "0 < max K 1" by simp
next
  show "eventually (\<lambda>x. norm (f x) \<le> max K 1) F"
    using K by (rule eventually_elim1, simp)
qed

lemma BfunE:
  assumes "Bfun f F"
  obtains B where "0 < B" and "eventually (\<lambda>x. norm (f x) \<le> B) F"
using assms unfolding Bfun_def by fast


subsection {* Convergence to Zero *}

definition Zfun :: "('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a filter \<Rightarrow> bool"
  where "Zfun f F = (\<forall>r>0. eventually (\<lambda>x. norm (f x) < r) F)"

lemma ZfunI:
  "(\<And>r. 0 < r \<Longrightarrow> eventually (\<lambda>x. norm (f x) < r) F) \<Longrightarrow> Zfun f F"
  unfolding Zfun_def by simp

lemma ZfunD:
  "\<lbrakk>Zfun f F; 0 < r\<rbrakk> \<Longrightarrow> eventually (\<lambda>x. norm (f x) < r) F"
  unfolding Zfun_def by simp

lemma Zfun_ssubst:
  "eventually (\<lambda>x. f x = g x) F \<Longrightarrow> Zfun g F \<Longrightarrow> Zfun f F"
  unfolding Zfun_def by (auto elim!: eventually_rev_mp)

lemma Zfun_zero: "Zfun (\<lambda>x. 0) F"
  unfolding Zfun_def by simp

lemma Zfun_norm_iff: "Zfun (\<lambda>x. norm (f x)) F = Zfun (\<lambda>x. f x) F"
  unfolding Zfun_def by simp

lemma Zfun_imp_Zfun:
  assumes f: "Zfun f F"
  assumes g: "eventually (\<lambda>x. norm (g x) \<le> norm (f x) * K) F"
  shows "Zfun (\<lambda>x. g x) F"
proof (cases)
  assume K: "0 < K"
  show ?thesis
  proof (rule ZfunI)
    fix r::real assume "0 < r"
    hence "0 < r / K"
      using K by (rule divide_pos_pos)
    then have "eventually (\<lambda>x. norm (f x) < r / K) F"
      using ZfunD [OF f] by fast
    with g show "eventually (\<lambda>x. norm (g x) < r) F"
    proof eventually_elim
      case (elim x)
      hence "norm (f x) * K < r"
        by (simp add: pos_less_divide_eq K)
      thus ?case
        by (simp add: order_le_less_trans [OF elim(1)])
    qed
  qed
next
  assume "\<not> 0 < K"
  hence K: "K \<le> 0" by (simp only: not_less)
  show ?thesis
  proof (rule ZfunI)
    fix r :: real
    assume "0 < r"
    from g show "eventually (\<lambda>x. norm (g x) < r) F"
    proof eventually_elim
      case (elim x)
      also have "norm (f x) * K \<le> norm (f x) * 0"
        using K norm_ge_zero by (rule mult_left_mono)
      finally show ?case
        using `0 < r` by simp
    qed
  qed
qed

lemma Zfun_le: "\<lbrakk>Zfun g F; \<forall>x. norm (f x) \<le> norm (g x)\<rbrakk> \<Longrightarrow> Zfun f F"
  by (erule_tac K="1" in Zfun_imp_Zfun, simp)

lemma Zfun_add:
  assumes f: "Zfun f F" and g: "Zfun g F"
  shows "Zfun (\<lambda>x. f x + g x) F"
proof (rule ZfunI)
  fix r::real assume "0 < r"
  hence r: "0 < r / 2" by simp
  have "eventually (\<lambda>x. norm (f x) < r/2) F"
    using f r by (rule ZfunD)
  moreover
  have "eventually (\<lambda>x. norm (g x) < r/2) F"
    using g r by (rule ZfunD)
  ultimately
  show "eventually (\<lambda>x. norm (f x + g x) < r) F"
  proof eventually_elim
    case (elim x)
    have "norm (f x + g x) \<le> norm (f x) + norm (g x)"
      by (rule norm_triangle_ineq)
    also have "\<dots> < r/2 + r/2"
      using elim by (rule add_strict_mono)
    finally show ?case
      by simp
  qed
qed

lemma Zfun_minus: "Zfun f F \<Longrightarrow> Zfun (\<lambda>x. - f x) F"
  unfolding Zfun_def by simp

lemma Zfun_diff: "\<lbrakk>Zfun f F; Zfun g F\<rbrakk> \<Longrightarrow> Zfun (\<lambda>x. f x - g x) F"
  by (simp only: diff_minus Zfun_add Zfun_minus)

lemma (in bounded_linear) Zfun:
  assumes g: "Zfun g F"
  shows "Zfun (\<lambda>x. f (g x)) F"
proof -
  obtain K where "\<And>x. norm (f x) \<le> norm x * K"
    using bounded by fast
  then have "eventually (\<lambda>x. norm (f (g x)) \<le> norm (g x) * K) F"
    by simp
  with g show ?thesis
    by (rule Zfun_imp_Zfun)
qed

lemma (in bounded_bilinear) Zfun:
  assumes f: "Zfun f F"
  assumes g: "Zfun g F"
  shows "Zfun (\<lambda>x. f x ** g x) F"
proof (rule ZfunI)
  fix r::real assume r: "0 < r"
  obtain K where K: "0 < K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using pos_bounded by fast
  from K have K': "0 < inverse K"
    by (rule positive_imp_inverse_positive)
  have "eventually (\<lambda>x. norm (f x) < r) F"
    using f r by (rule ZfunD)
  moreover
  have "eventually (\<lambda>x. norm (g x) < inverse K) F"
    using g K' by (rule ZfunD)
  ultimately
  show "eventually (\<lambda>x. norm (f x ** g x) < r) F"
  proof eventually_elim
    case (elim x)
    have "norm (f x ** g x) \<le> norm (f x) * norm (g x) * K"
      by (rule norm_le)
    also have "norm (f x) * norm (g x) * K < r * inverse K * K"
      by (intro mult_strict_right_mono mult_strict_mono' norm_ge_zero elim K)
    also from K have "r * inverse K * K = r"
      by simp
    finally show ?case .
  qed
qed

lemma (in bounded_bilinear) Zfun_left:
  "Zfun f F \<Longrightarrow> Zfun (\<lambda>x. f x ** a) F"
  by (rule bounded_linear_left [THEN bounded_linear.Zfun])

lemma (in bounded_bilinear) Zfun_right:
  "Zfun f F \<Longrightarrow> Zfun (\<lambda>x. a ** f x) F"
  by (rule bounded_linear_right [THEN bounded_linear.Zfun])

lemmas Zfun_mult = bounded_bilinear.Zfun [OF bounded_bilinear_mult]
lemmas Zfun_mult_right = bounded_bilinear.Zfun_right [OF bounded_bilinear_mult]
lemmas Zfun_mult_left = bounded_bilinear.Zfun_left [OF bounded_bilinear_mult]

lemma tendsto_Zfun_iff: "(f ---> a) F = Zfun (\<lambda>x. f x - a) F"
  by (simp only: tendsto_iff Zfun_def dist_norm)

subsubsection {* Distance and norms *}

lemma norm_conv_dist: "norm x = dist x 0"
  unfolding dist_norm by simp

lemma tendsto_norm [tendsto_intros]:
  "(f ---> a) F \<Longrightarrow> ((\<lambda>x. norm (f x)) ---> norm a) F"
  unfolding norm_conv_dist by (intro tendsto_intros)

lemma tendsto_norm_zero:
  "(f ---> 0) F \<Longrightarrow> ((\<lambda>x. norm (f x)) ---> 0) F"
  by (drule tendsto_norm, simp)

lemma tendsto_norm_zero_cancel:
  "((\<lambda>x. norm (f x)) ---> 0) F \<Longrightarrow> (f ---> 0) F"
  unfolding tendsto_iff dist_norm by simp

lemma tendsto_norm_zero_iff:
  "((\<lambda>x. norm (f x)) ---> 0) F \<longleftrightarrow> (f ---> 0) F"
  unfolding tendsto_iff dist_norm by simp

lemma tendsto_rabs [tendsto_intros]:
  "(f ---> (l::real)) F \<Longrightarrow> ((\<lambda>x. \<bar>f x\<bar>) ---> \<bar>l\<bar>) F"
  by (fold real_norm_def, rule tendsto_norm)

lemma tendsto_rabs_zero:
  "(f ---> (0::real)) F \<Longrightarrow> ((\<lambda>x. \<bar>f x\<bar>) ---> 0) F"
  by (fold real_norm_def, rule tendsto_norm_zero)

lemma tendsto_rabs_zero_cancel:
  "((\<lambda>x. \<bar>f x\<bar>) ---> (0::real)) F \<Longrightarrow> (f ---> 0) F"
  by (fold real_norm_def, rule tendsto_norm_zero_cancel)

lemma tendsto_rabs_zero_iff:
  "((\<lambda>x. \<bar>f x\<bar>) ---> (0::real)) F \<longleftrightarrow> (f ---> 0) F"
  by (fold real_norm_def, rule tendsto_norm_zero_iff)

subsubsection {* Addition and subtraction *}

lemma tendsto_add [tendsto_intros]:
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>(f ---> a) F; (g ---> b) F\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x + g x) ---> a + b) F"
  by (simp only: tendsto_Zfun_iff add_diff_add Zfun_add)

lemma tendsto_add_zero:
  fixes f g :: "'a::type \<Rightarrow> 'b::real_normed_vector"
  shows "\<lbrakk>(f ---> 0) F; (g ---> 0) F\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x + g x) ---> 0) F"
  by (drule (1) tendsto_add, simp)

lemma tendsto_minus [tendsto_intros]:
  fixes a :: "'a::real_normed_vector"
  shows "(f ---> a) F \<Longrightarrow> ((\<lambda>x. - f x) ---> - a) F"
  by (simp only: tendsto_Zfun_iff minus_diff_minus Zfun_minus)

lemma tendsto_minus_cancel:
  fixes a :: "'a::real_normed_vector"
  shows "((\<lambda>x. - f x) ---> - a) F \<Longrightarrow> (f ---> a) F"
  by (drule tendsto_minus, simp)

lemma tendsto_minus_cancel_left:
    "(f ---> - (y::_::real_normed_vector)) F \<longleftrightarrow> ((\<lambda>x. - f x) ---> y) F"
  using tendsto_minus_cancel[of f "- y" F]  tendsto_minus[of f "- y" F]
  by auto

lemma tendsto_diff [tendsto_intros]:
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>(f ---> a) F; (g ---> b) F\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x - g x) ---> a - b) F"
  by (simp add: diff_minus tendsto_add tendsto_minus)

lemma tendsto_setsum [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_vector"
  assumes "\<And>i. i \<in> S \<Longrightarrow> (f i ---> a i) F"
  shows "((\<lambda>x. \<Sum>i\<in>S. f i x) ---> (\<Sum>i\<in>S. a i)) F"
proof (cases "finite S")
  assume "finite S" thus ?thesis using assms
    by (induct, simp add: tendsto_const, simp add: tendsto_add)
next
  assume "\<not> finite S" thus ?thesis
    by (simp add: tendsto_const)
qed

lemmas real_tendsto_sandwich = tendsto_sandwich[where 'b=real]

subsubsection {* Linear operators and multiplication *}

lemma (in bounded_linear) tendsto:
  "(g ---> a) F \<Longrightarrow> ((\<lambda>x. f (g x)) ---> f a) F"
  by (simp only: tendsto_Zfun_iff diff [symmetric] Zfun)

lemma (in bounded_linear) tendsto_zero:
  "(g ---> 0) F \<Longrightarrow> ((\<lambda>x. f (g x)) ---> 0) F"
  by (drule tendsto, simp only: zero)

lemma (in bounded_bilinear) tendsto:
  "\<lbrakk>(f ---> a) F; (g ---> b) F\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x ** g x) ---> a ** b) F"
  by (simp only: tendsto_Zfun_iff prod_diff_prod
                 Zfun_add Zfun Zfun_left Zfun_right)

lemma (in bounded_bilinear) tendsto_zero:
  assumes f: "(f ---> 0) F"
  assumes g: "(g ---> 0) F"
  shows "((\<lambda>x. f x ** g x) ---> 0) F"
  using tendsto [OF f g] by (simp add: zero_left)

lemma (in bounded_bilinear) tendsto_left_zero:
  "(f ---> 0) F \<Longrightarrow> ((\<lambda>x. f x ** c) ---> 0) F"
  by (rule bounded_linear.tendsto_zero [OF bounded_linear_left])

lemma (in bounded_bilinear) tendsto_right_zero:
  "(f ---> 0) F \<Longrightarrow> ((\<lambda>x. c ** f x) ---> 0) F"
  by (rule bounded_linear.tendsto_zero [OF bounded_linear_right])

lemmas tendsto_of_real [tendsto_intros] =
  bounded_linear.tendsto [OF bounded_linear_of_real]

lemmas tendsto_scaleR [tendsto_intros] =
  bounded_bilinear.tendsto [OF bounded_bilinear_scaleR]

lemmas tendsto_mult [tendsto_intros] =
  bounded_bilinear.tendsto [OF bounded_bilinear_mult]

lemmas tendsto_mult_zero =
  bounded_bilinear.tendsto_zero [OF bounded_bilinear_mult]

lemmas tendsto_mult_left_zero =
  bounded_bilinear.tendsto_left_zero [OF bounded_bilinear_mult]

lemmas tendsto_mult_right_zero =
  bounded_bilinear.tendsto_right_zero [OF bounded_bilinear_mult]

lemma tendsto_power [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b::{power,real_normed_algebra}"
  shows "(f ---> a) F \<Longrightarrow> ((\<lambda>x. f x ^ n) ---> a ^ n) F"
  by (induct n) (simp_all add: tendsto_const tendsto_mult)

lemma tendsto_setprod [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::{real_normed_algebra,comm_ring_1}"
  assumes "\<And>i. i \<in> S \<Longrightarrow> (f i ---> L i) F"
  shows "((\<lambda>x. \<Prod>i\<in>S. f i x) ---> (\<Prod>i\<in>S. L i)) F"
proof (cases "finite S")
  assume "finite S" thus ?thesis using assms
    by (induct, simp add: tendsto_const, simp add: tendsto_mult)
next
  assume "\<not> finite S" thus ?thesis
    by (simp add: tendsto_const)
qed

subsubsection {* Inverse and division *}

lemma (in bounded_bilinear) Zfun_prod_Bfun:
  assumes f: "Zfun f F"
  assumes g: "Bfun g F"
  shows "Zfun (\<lambda>x. f x ** g x) F"
proof -
  obtain K where K: "0 \<le> K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using nonneg_bounded by fast
  obtain B where B: "0 < B"
    and norm_g: "eventually (\<lambda>x. norm (g x) \<le> B) F"
    using g by (rule BfunE)
  have "eventually (\<lambda>x. norm (f x ** g x) \<le> norm (f x) * (B * K)) F"
  using norm_g proof eventually_elim
    case (elim x)
    have "norm (f x ** g x) \<le> norm (f x) * norm (g x) * K"
      by (rule norm_le)
    also have "\<dots> \<le> norm (f x) * B * K"
      by (intro mult_mono' order_refl norm_g norm_ge_zero
                mult_nonneg_nonneg K elim)
    also have "\<dots> = norm (f x) * (B * K)"
      by (rule mult_assoc)
    finally show "norm (f x ** g x) \<le> norm (f x) * (B * K)" .
  qed
  with f show ?thesis
    by (rule Zfun_imp_Zfun)
qed

lemma (in bounded_bilinear) flip:
  "bounded_bilinear (\<lambda>x y. y ** x)"
  apply default
  apply (rule add_right)
  apply (rule add_left)
  apply (rule scaleR_right)
  apply (rule scaleR_left)
  apply (subst mult_commute)
  using bounded by fast

lemma (in bounded_bilinear) Bfun_prod_Zfun:
  assumes f: "Bfun f F"
  assumes g: "Zfun g F"
  shows "Zfun (\<lambda>x. f x ** g x) F"
  using flip g f by (rule bounded_bilinear.Zfun_prod_Bfun)

lemma Bfun_inverse_lemma:
  fixes x :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>r \<le> norm x; 0 < r\<rbrakk> \<Longrightarrow> norm (inverse x) \<le> inverse r"
  apply (subst nonzero_norm_inverse, clarsimp)
  apply (erule (1) le_imp_inverse_le)
  done

lemma Bfun_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  assumes f: "(f ---> a) F"
  assumes a: "a \<noteq> 0"
  shows "Bfun (\<lambda>x. inverse (f x)) F"
proof -
  from a have "0 < norm a" by simp
  hence "\<exists>r>0. r < norm a" by (rule dense)
  then obtain r where r1: "0 < r" and r2: "r < norm a" by fast
  have "eventually (\<lambda>x. dist (f x) a < r) F"
    using tendstoD [OF f r1] by fast
  hence "eventually (\<lambda>x. norm (inverse (f x)) \<le> inverse (norm a - r)) F"
  proof eventually_elim
    case (elim x)
    hence 1: "norm (f x - a) < r"
      by (simp add: dist_norm)
    hence 2: "f x \<noteq> 0" using r2 by auto
    hence "norm (inverse (f x)) = inverse (norm (f x))"
      by (rule nonzero_norm_inverse)
    also have "\<dots> \<le> inverse (norm a - r)"
    proof (rule le_imp_inverse_le)
      show "0 < norm a - r" using r2 by simp
    next
      have "norm a - norm (f x) \<le> norm (a - f x)"
        by (rule norm_triangle_ineq2)
      also have "\<dots> = norm (f x - a)"
        by (rule norm_minus_commute)
      also have "\<dots> < r" using 1 .
      finally show "norm a - r \<le> norm (f x)" by simp
    qed
    finally show "norm (inverse (f x)) \<le> inverse (norm a - r)" .
  qed
  thus ?thesis by (rule BfunI)
qed

lemma tendsto_inverse [tendsto_intros]:
  fixes a :: "'a::real_normed_div_algebra"
  assumes f: "(f ---> a) F"
  assumes a: "a \<noteq> 0"
  shows "((\<lambda>x. inverse (f x)) ---> inverse a) F"
proof -
  from a have "0 < norm a" by simp
  with f have "eventually (\<lambda>x. dist (f x) a < norm a) F"
    by (rule tendstoD)
  then have "eventually (\<lambda>x. f x \<noteq> 0) F"
    unfolding dist_norm by (auto elim!: eventually_elim1)
  with a have "eventually (\<lambda>x. inverse (f x) - inverse a =
    - (inverse (f x) * (f x - a) * inverse a)) F"
    by (auto elim!: eventually_elim1 simp: inverse_diff_inverse)
  moreover have "Zfun (\<lambda>x. - (inverse (f x) * (f x - a) * inverse a)) F"
    by (intro Zfun_minus Zfun_mult_left
      bounded_bilinear.Bfun_prod_Zfun [OF bounded_bilinear_mult]
      Bfun_inverse [OF f a] f [unfolded tendsto_Zfun_iff])
  ultimately show ?thesis
    unfolding tendsto_Zfun_iff by (rule Zfun_ssubst)
qed

lemma tendsto_divide [tendsto_intros]:
  fixes a b :: "'a::real_normed_field"
  shows "\<lbrakk>(f ---> a) F; (g ---> b) F; b \<noteq> 0\<rbrakk>
    \<Longrightarrow> ((\<lambda>x. f x / g x) ---> a / b) F"
  by (simp add: tendsto_mult tendsto_inverse divide_inverse)

lemma tendsto_sgn [tendsto_intros]:
  fixes l :: "'a::real_normed_vector"
  shows "\<lbrakk>(f ---> l) F; l \<noteq> 0\<rbrakk> \<Longrightarrow> ((\<lambda>x. sgn (f x)) ---> sgn l) F"
  unfolding sgn_div_norm by (simp add: tendsto_intros)

lemma filterlim_at_infinity:
  fixes f :: "_ \<Rightarrow> 'a\<Colon>real_normed_vector"
  assumes "0 \<le> c"
  shows "(LIM x F. f x :> at_infinity) \<longleftrightarrow> (\<forall>r>c. eventually (\<lambda>x. r \<le> norm (f x)) F)"
  unfolding filterlim_iff eventually_at_infinity
proof safe
  fix P :: "'a \<Rightarrow> bool" and b
  assume *: "\<forall>r>c. eventually (\<lambda>x. r \<le> norm (f x)) F"
    and P: "\<forall>x. b \<le> norm x \<longrightarrow> P x"
  have "max b (c + 1) > c" by auto
  with * have "eventually (\<lambda>x. max b (c + 1) \<le> norm (f x)) F"
    by auto
  then show "eventually (\<lambda>x. P (f x)) F"
  proof eventually_elim
    fix x assume "max b (c + 1) \<le> norm (f x)"
    with P show "P (f x)" by auto
  qed
qed force

subsection {* Relate @{const at}, @{const at_left} and @{const at_right} *}

text {*

This lemmas are useful for conversion between @{term "at x"} to @{term "at_left x"} and
@{term "at_right x"} and also @{term "at_right 0"}.

*}

lemmas filterlim_split_at_real = filterlim_split_at[where 'a=real]

lemma filtermap_nhds_shift: "filtermap (\<lambda>x. x - d) (nhds a) = nhds (a - d::real)"
  unfolding filter_eq_iff eventually_filtermap eventually_nhds_metric
  by (intro allI ex_cong) (auto simp: dist_real_def field_simps)

lemma filtermap_nhds_minus: "filtermap (\<lambda>x. - x) (nhds a) = nhds (- a::real)"
  unfolding filter_eq_iff eventually_filtermap eventually_nhds_metric
  apply (intro allI ex_cong)
  apply (auto simp: dist_real_def field_simps)
  apply (erule_tac x="-x" in allE)
  apply simp
  done

lemma filtermap_at_shift: "filtermap (\<lambda>x. x - d) (at a) = at (a - d::real)"
  unfolding at_def filtermap_nhds_shift[symmetric]
  by (simp add: filter_eq_iff eventually_filtermap eventually_within)

lemma filtermap_at_right_shift: "filtermap (\<lambda>x. x - d) (at_right a) = at_right (a - d::real)"
  unfolding filtermap_at_shift[symmetric]
  by (simp add: filter_eq_iff eventually_filtermap eventually_within)

lemma at_right_to_0: "at_right (a::real) = filtermap (\<lambda>x. x + a) (at_right 0)"
  using filtermap_at_right_shift[of "-a" 0] by simp

lemma filterlim_at_right_to_0:
  "filterlim f F (at_right (a::real)) \<longleftrightarrow> filterlim (\<lambda>x. f (x + a)) F (at_right 0)"
  unfolding filterlim_def filtermap_filtermap at_right_to_0[of a] ..

lemma eventually_at_right_to_0:
  "eventually P (at_right (a::real)) \<longleftrightarrow> eventually (\<lambda>x. P (x + a)) (at_right 0)"
  unfolding at_right_to_0[of a] by (simp add: eventually_filtermap)

lemma filtermap_at_minus: "filtermap (\<lambda>x. - x) (at a) = at (- a::real)"
  unfolding at_def filtermap_nhds_minus[symmetric]
  by (simp add: filter_eq_iff eventually_filtermap eventually_within)

lemma at_left_minus: "at_left (a::real) = filtermap (\<lambda>x. - x) (at_right (- a))"
  by (simp add: filter_eq_iff eventually_filtermap eventually_within filtermap_at_minus[symmetric])

lemma at_right_minus: "at_right (a::real) = filtermap (\<lambda>x. - x) (at_left (- a))"
  by (simp add: filter_eq_iff eventually_filtermap eventually_within filtermap_at_minus[symmetric])

lemma filterlim_at_left_to_right:
  "filterlim f F (at_left (a::real)) \<longleftrightarrow> filterlim (\<lambda>x. f (- x)) F (at_right (-a))"
  unfolding filterlim_def filtermap_filtermap at_left_minus[of a] ..

lemma eventually_at_left_to_right:
  "eventually P (at_left (a::real)) \<longleftrightarrow> eventually (\<lambda>x. P (- x)) (at_right (-a))"
  unfolding at_left_minus[of a] by (simp add: eventually_filtermap)

lemma at_top_mirror: "at_top = filtermap uminus (at_bot :: real filter)"
  unfolding filter_eq_iff eventually_filtermap eventually_at_top_linorder eventually_at_bot_linorder
  by (metis le_minus_iff minus_minus)

lemma at_bot_mirror: "at_bot = filtermap uminus (at_top :: real filter)"
  unfolding at_top_mirror filtermap_filtermap by (simp add: filtermap_ident)

lemma filterlim_at_top_mirror: "(LIM x at_top. f x :> F) \<longleftrightarrow> (LIM x at_bot. f (-x::real) :> F)"
  unfolding filterlim_def at_top_mirror filtermap_filtermap ..

lemma filterlim_at_bot_mirror: "(LIM x at_bot. f x :> F) \<longleftrightarrow> (LIM x at_top. f (-x::real) :> F)"
  unfolding filterlim_def at_bot_mirror filtermap_filtermap ..

lemma filterlim_uminus_at_top_at_bot: "LIM x at_bot. - x :: real :> at_top"
  unfolding filterlim_at_top eventually_at_bot_dense
  by (metis leI minus_less_iff order_less_asym)

lemma filterlim_uminus_at_bot_at_top: "LIM x at_top. - x :: real :> at_bot"
  unfolding filterlim_at_bot eventually_at_top_dense
  by (metis leI less_minus_iff order_less_asym)

lemma filterlim_uminus_at_top: "(LIM x F. f x :> at_top) \<longleftrightarrow> (LIM x F. - (f x) :: real :> at_bot)"
  using filterlim_compose[OF filterlim_uminus_at_bot_at_top, of f F]
  using filterlim_compose[OF filterlim_uminus_at_top_at_bot, of "\<lambda>x. - f x" F]
  by auto

lemma filterlim_uminus_at_bot: "(LIM x F. f x :> at_bot) \<longleftrightarrow> (LIM x F. - (f x) :: real :> at_top)"
  unfolding filterlim_uminus_at_top by simp

lemma filterlim_inverse_at_top_right: "LIM x at_right (0::real). inverse x :> at_top"
  unfolding filterlim_at_top_gt[where c=0] eventually_within at_def
proof safe
  fix Z :: real assume [arith]: "0 < Z"
  then have "eventually (\<lambda>x. x < inverse Z) (nhds 0)"
    by (auto simp add: eventually_nhds_metric dist_real_def intro!: exI[of _ "\<bar>inverse Z\<bar>"])
  then show "eventually (\<lambda>x. x \<in> - {0} \<longrightarrow> x \<in> {0<..} \<longrightarrow> Z \<le> inverse x) (nhds 0)"
    by (auto elim!: eventually_elim1 simp: inverse_eq_divide field_simps)
qed

lemma filterlim_inverse_at_top:
  "(f ---> (0 :: real)) F \<Longrightarrow> eventually (\<lambda>x. 0 < f x) F \<Longrightarrow> LIM x F. inverse (f x) :> at_top"
  by (intro filterlim_compose[OF filterlim_inverse_at_top_right])
     (simp add: filterlim_def eventually_filtermap le_within_iff at_def eventually_elim1)

lemma filterlim_inverse_at_bot_neg:
  "LIM x (at_left (0::real)). inverse x :> at_bot"
  by (simp add: filterlim_inverse_at_top_right filterlim_uminus_at_bot filterlim_at_left_to_right)

lemma filterlim_inverse_at_bot:
  "(f ---> (0 :: real)) F \<Longrightarrow> eventually (\<lambda>x. f x < 0) F \<Longrightarrow> LIM x F. inverse (f x) :> at_bot"
  unfolding filterlim_uminus_at_bot inverse_minus_eq[symmetric]
  by (rule filterlim_inverse_at_top) (simp_all add: tendsto_minus_cancel_left[symmetric])

lemma tendsto_inverse_0:
  fixes x :: "_ \<Rightarrow> 'a\<Colon>real_normed_div_algebra"
  shows "(inverse ---> (0::'a)) at_infinity"
  unfolding tendsto_Zfun_iff diff_0_right Zfun_def eventually_at_infinity
proof safe
  fix r :: real assume "0 < r"
  show "\<exists>b. \<forall>x. b \<le> norm x \<longrightarrow> norm (inverse x :: 'a) < r"
  proof (intro exI[of _ "inverse (r / 2)"] allI impI)
    fix x :: 'a
    from `0 < r` have "0 < inverse (r / 2)" by simp
    also assume *: "inverse (r / 2) \<le> norm x"
    finally show "norm (inverse x) < r"
      using * `0 < r` by (subst nonzero_norm_inverse) (simp_all add: inverse_eq_divide field_simps)
  qed
qed

lemma at_right_to_top: "(at_right (0::real)) = filtermap inverse at_top"
proof (rule antisym)
  have "(inverse ---> (0::real)) at_top"
    by (metis tendsto_inverse_0 filterlim_mono at_top_le_at_infinity order_refl)
  then show "filtermap inverse at_top \<le> at_right (0::real)"
    unfolding at_within_eq
    by (intro le_withinI) (simp_all add: eventually_filtermap eventually_gt_at_top filterlim_def)
next
  have "filtermap inverse (filtermap inverse (at_right (0::real))) \<le> filtermap inverse at_top"
    using filterlim_inverse_at_top_right unfolding filterlim_def by (rule filtermap_mono)
  then show "at_right (0::real) \<le> filtermap inverse at_top"
    by (simp add: filtermap_ident filtermap_filtermap)
qed

lemma eventually_at_right_to_top:
  "eventually P (at_right (0::real)) \<longleftrightarrow> eventually (\<lambda>x. P (inverse x)) at_top"
  unfolding at_right_to_top eventually_filtermap ..

lemma filterlim_at_right_to_top:
  "filterlim f F (at_right (0::real)) \<longleftrightarrow> (LIM x at_top. f (inverse x) :> F)"
  unfolding filterlim_def at_right_to_top filtermap_filtermap ..

lemma at_top_to_right: "at_top = filtermap inverse (at_right (0::real))"
  unfolding at_right_to_top filtermap_filtermap inverse_inverse_eq filtermap_ident ..

lemma eventually_at_top_to_right:
  "eventually P at_top \<longleftrightarrow> eventually (\<lambda>x. P (inverse x)) (at_right (0::real))"
  unfolding at_top_to_right eventually_filtermap ..

lemma filterlim_at_top_to_right:
  "filterlim f F at_top \<longleftrightarrow> (LIM x (at_right (0::real)). f (inverse x) :> F)"
  unfolding filterlim_def at_top_to_right filtermap_filtermap ..

lemma filterlim_inverse_at_infinity:
  fixes x :: "_ \<Rightarrow> 'a\<Colon>{real_normed_div_algebra, division_ring_inverse_zero}"
  shows "filterlim inverse at_infinity (at (0::'a))"
  unfolding filterlim_at_infinity[OF order_refl]
proof safe
  fix r :: real assume "0 < r"
  then show "eventually (\<lambda>x::'a. r \<le> norm (inverse x)) (at 0)"
    unfolding eventually_at norm_inverse
    by (intro exI[of _ "inverse r"])
       (auto simp: norm_conv_dist[symmetric] field_simps inverse_eq_divide)
qed

lemma filterlim_inverse_at_iff:
  fixes g :: "'a \<Rightarrow> 'b\<Colon>{real_normed_div_algebra, division_ring_inverse_zero}"
  shows "(LIM x F. inverse (g x) :> at 0) \<longleftrightarrow> (LIM x F. g x :> at_infinity)"
  unfolding filterlim_def filtermap_filtermap[symmetric]
proof
  assume "filtermap g F \<le> at_infinity"
  then have "filtermap inverse (filtermap g F) \<le> filtermap inverse at_infinity"
    by (rule filtermap_mono)
  also have "\<dots> \<le> at 0"
    using tendsto_inverse_0
    by (auto intro!: le_withinI exI[of _ 1]
             simp: eventually_filtermap eventually_at_infinity filterlim_def at_def)
  finally show "filtermap inverse (filtermap g F) \<le> at 0" .
next
  assume "filtermap inverse (filtermap g F) \<le> at 0"
  then have "filtermap inverse (filtermap inverse (filtermap g F)) \<le> filtermap inverse (at 0)"
    by (rule filtermap_mono)
  with filterlim_inverse_at_infinity show "filtermap g F \<le> at_infinity"
    by (auto intro: order_trans simp: filterlim_def filtermap_filtermap)
qed

lemma tendsto_inverse_0_at_top:
  "LIM x F. f x :> at_top \<Longrightarrow> ((\<lambda>x. inverse (f x) :: real) ---> 0) F"
 by (metis at_top_le_at_infinity filterlim_at filterlim_inverse_at_iff filterlim_mono order_refl)

text {*

We only show rules for multiplication and addition when the functions are either against a real
value or against infinity. Further rules are easy to derive by using @{thm filterlim_uminus_at_top}.

*}

lemma filterlim_tendsto_pos_mult_at_top: 
  assumes f: "(f ---> c) F" and c: "0 < c"
  assumes g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x * g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real assume "0 < Z"
  from f `0 < c` have "eventually (\<lambda>x. c / 2 < f x) F"
    by (auto dest!: tendstoD[where e="c / 2"] elim!: eventually_elim1
             simp: dist_real_def abs_real_def split: split_if_asm)
  moreover from g have "eventually (\<lambda>x. (Z / c * 2) \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x * g x) F"
  proof eventually_elim
    fix x assume "c / 2 < f x" "Z / c * 2 \<le> g x"
    with `0 < Z` `0 < c` have "c / 2 * (Z / c * 2) \<le> f x * g x"
      by (intro mult_mono) (auto simp: zero_le_divide_iff)
    with `0 < c` show "Z \<le> f x * g x"
       by simp
  qed
qed

lemma filterlim_at_top_mult_at_top: 
  assumes f: "LIM x F. f x :> at_top"
  assumes g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x * g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real assume "0 < Z"
  from f have "eventually (\<lambda>x. 1 \<le> f x) F"
    unfolding filterlim_at_top by auto
  moreover from g have "eventually (\<lambda>x. Z \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x * g x) F"
  proof eventually_elim
    fix x assume "1 \<le> f x" "Z \<le> g x"
    with `0 < Z` have "1 * Z \<le> f x * g x"
      by (intro mult_mono) (auto simp: zero_le_divide_iff)
    then show "Z \<le> f x * g x"
       by simp
  qed
qed

lemma filterlim_tendsto_pos_mult_at_bot:
  assumes "(f ---> c) F" "0 < (c::real)" "filterlim g at_bot F"
  shows "LIM x F. f x * g x :> at_bot"
  using filterlim_tendsto_pos_mult_at_top[OF assms(1,2), of "\<lambda>x. - g x"] assms(3)
  unfolding filterlim_uminus_at_bot by simp

lemma filterlim_tendsto_add_at_top: 
  assumes f: "(f ---> c) F"
  assumes g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x + g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real assume "0 < Z"
  from f have "eventually (\<lambda>x. c - 1 < f x) F"
    by (auto dest!: tendstoD[where e=1] elim!: eventually_elim1 simp: dist_real_def)
  moreover from g have "eventually (\<lambda>x. Z - (c - 1) \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x + g x) F"
    by eventually_elim simp
qed

lemma LIM_at_top_divide:
  fixes f g :: "'a \<Rightarrow> real"
  assumes f: "(f ---> a) F" "0 < a"
  assumes g: "(g ---> 0) F" "eventually (\<lambda>x. 0 < g x) F"
  shows "LIM x F. f x / g x :> at_top"
  unfolding divide_inverse
  by (rule filterlim_tendsto_pos_mult_at_top[OF f]) (rule filterlim_inverse_at_top[OF g])

lemma filterlim_at_top_add_at_top: 
  assumes f: "LIM x F. f x :> at_top"
  assumes g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x + g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real assume "0 < Z"
  from f have "eventually (\<lambda>x. 0 \<le> f x) F"
    unfolding filterlim_at_top by auto
  moreover from g have "eventually (\<lambda>x. Z \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x + g x) F"
    by eventually_elim simp
qed

lemma tendsto_divide_0:
  fixes f :: "_ \<Rightarrow> 'a\<Colon>{real_normed_div_algebra, division_ring_inverse_zero}"
  assumes f: "(f ---> c) F"
  assumes g: "LIM x F. g x :> at_infinity"
  shows "((\<lambda>x. f x / g x) ---> 0) F"
  using tendsto_mult[OF f filterlim_compose[OF tendsto_inverse_0 g]] by (simp add: divide_inverse)

lemma linear_plus_1_le_power:
  fixes x :: real
  assumes x: "0 \<le> x"
  shows "real n * x + 1 \<le> (x + 1) ^ n"
proof (induct n)
  case (Suc n)
  have "real (Suc n) * x + 1 \<le> (x + 1) * (real n * x + 1)"
    by (simp add: field_simps real_of_nat_Suc mult_nonneg_nonneg x)
  also have "\<dots> \<le> (x + 1)^Suc n"
    using Suc x by (simp add: mult_left_mono)
  finally show ?case .
qed simp

lemma filterlim_realpow_sequentially_gt1:
  fixes x :: "'a :: real_normed_div_algebra"
  assumes x[arith]: "1 < norm x"
  shows "LIM n sequentially. x ^ n :> at_infinity"
proof (intro filterlim_at_infinity[THEN iffD2] allI impI)
  fix y :: real assume "0 < y"
  have "0 < norm x - 1" by simp
  then obtain N::nat where "y < real N * (norm x - 1)" by (blast dest: reals_Archimedean3)
  also have "\<dots> \<le> real N * (norm x - 1) + 1" by simp
  also have "\<dots> \<le> (norm x - 1 + 1) ^ N" by (rule linear_plus_1_le_power) simp
  also have "\<dots> = norm x ^ N" by simp
  finally have "\<forall>n\<ge>N. y \<le> norm x ^ n"
    by (metis order_less_le_trans power_increasing order_less_imp_le x)
  then show "eventually (\<lambda>n. y \<le> norm (x ^ n)) sequentially"
    unfolding eventually_sequentially
    by (auto simp: norm_power)
qed simp


(* Unfortunately eventually_within was overwritten by Multivariate_Analysis.
   Hence it was references as Limits.within, but now it is Basic_Topology.eventually_within *)
lemmas eventually_within = eventually_within

end

