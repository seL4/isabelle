(*  Title       : Lim.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{* Limits and Continuity *}

theory Lim
imports SEQ
begin

text{*Standard Definitions*}

definition
  LIM :: "['a::real_normed_vector => 'b::real_normed_vector, 'a, 'b] => bool"
        ("((_)/ -- (_)/ --> (_))" [60, 0, 60] 60) where
  [code del]: "f -- a --> L =
     (\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a & norm (x - a) < s
        --> norm (f x - L) < r)"

definition
  isCont :: "['a::real_normed_vector => 'b::real_normed_vector, 'a] => bool" where
  "isCont f a = (f -- a --> (f a))"

definition
  isUCont :: "['a::real_normed_vector => 'b::real_normed_vector] => bool" where
  [code del]: "isUCont f = (\<forall>r>0. \<exists>s>0. \<forall>x y. norm (x - y) < s \<longrightarrow> norm (f x - f y) < r)"


subsection {* Limits of Functions *}

subsubsection {* Purely standard proofs *}

lemma LIM_eq:
     "f -- a --> L =
     (\<forall>r>0.\<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r)"
by (simp add: LIM_def diff_minus)

lemma LIM_I:
     "(!!r. 0<r ==> \<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r)
      ==> f -- a --> L"
by (simp add: LIM_eq)

lemma LIM_D:
     "[| f -- a --> L; 0<r |]
      ==> \<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r"
by (simp add: LIM_eq)

lemma LIM_offset: "f -- a --> L \<Longrightarrow> (\<lambda>x. f (x + k)) -- a - k --> L"
apply (rule LIM_I)
apply (drule_tac r="r" in LIM_D, safe)
apply (rule_tac x="s" in exI, safe)
apply (drule_tac x="x + k" in spec)
apply (simp add: algebra_simps)
done

lemma LIM_offset_zero: "f -- a --> L \<Longrightarrow> (\<lambda>h. f (a + h)) -- 0 --> L"
by (drule_tac k="a" in LIM_offset, simp add: add_commute)

lemma LIM_offset_zero_cancel: "(\<lambda>h. f (a + h)) -- 0 --> L \<Longrightarrow> f -- a --> L"
by (drule_tac k="- a" in LIM_offset, simp)

lemma LIM_const [simp]: "(%x. k) -- x --> k"
by (simp add: LIM_def)

lemma LIM_add:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes f: "f -- a --> L" and g: "g -- a --> M"
  shows "(%x. f x + g(x)) -- a --> (L + M)"
proof (rule LIM_I)
  fix r :: real
  assume r: "0 < r"
  from LIM_D [OF f half_gt_zero [OF r]]
  obtain fs
    where fs:    "0 < fs"
      and fs_lt: "\<forall>x. x \<noteq> a & norm (x-a) < fs --> norm (f x - L) < r/2"
  by blast
  from LIM_D [OF g half_gt_zero [OF r]]
  obtain gs
    where gs:    "0 < gs"
      and gs_lt: "\<forall>x. x \<noteq> a & norm (x-a) < gs --> norm (g x - M) < r/2"
  by blast
  show "\<exists>s>0.\<forall>x. x \<noteq> a \<and> norm (x-a) < s \<longrightarrow> norm (f x + g x - (L + M)) < r"
  proof (intro exI conjI strip)
    show "0 < min fs gs"  by (simp add: fs gs)
    fix x :: 'a
    assume "x \<noteq> a \<and> norm (x-a) < min fs gs"
    hence "x \<noteq> a \<and> norm (x-a) < fs \<and> norm (x-a) < gs" by simp
    with fs_lt gs_lt
    have "norm (f x - L) < r/2" and "norm (g x - M) < r/2" by blast+
    hence "norm (f x - L) + norm (g x - M) < r" by arith
    thus "norm (f x + g x - (L + M)) < r"
      by (blast intro: norm_diff_triangle_ineq order_le_less_trans)
  qed
qed

lemma LIM_add_zero:
  "\<lbrakk>f -- a --> 0; g -- a --> 0\<rbrakk> \<Longrightarrow> (\<lambda>x. f x + g x) -- a --> 0"
by (drule (1) LIM_add, simp)

lemma minus_diff_minus:
  fixes a b :: "'a::ab_group_add"
  shows "(- a) - (- b) = - (a - b)"
by simp

lemma LIM_minus: "f -- a --> L ==> (%x. -f(x)) -- a --> -L"
by (simp only: LIM_eq minus_diff_minus norm_minus_cancel)

lemma LIM_add_minus:
    "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) + -g(x)) -- x --> (l + -m)"
by (intro LIM_add LIM_minus)

lemma LIM_diff:
    "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) - g(x)) -- x --> l-m"
by (simp only: diff_minus LIM_add LIM_minus)

lemma LIM_zero: "f -- a --> l \<Longrightarrow> (\<lambda>x. f x - l) -- a --> 0"
by (simp add: LIM_def)

lemma LIM_zero_cancel: "(\<lambda>x. f x - l) -- a --> 0 \<Longrightarrow> f -- a --> l"
by (simp add: LIM_def)

lemma LIM_zero_iff: "(\<lambda>x. f x - l) -- a --> 0 = f -- a --> l"
by (simp add: LIM_def)

lemma LIM_imp_LIM:
  assumes f: "f -- a --> l"
  assumes le: "\<And>x. x \<noteq> a \<Longrightarrow> norm (g x - m) \<le> norm (f x - l)"
  shows "g -- a --> m"
apply (rule LIM_I, drule LIM_D [OF f], safe)
apply (rule_tac x="s" in exI, safe)
apply (drule_tac x="x" in spec, safe)
apply (erule (1) order_le_less_trans [OF le])
done

lemma LIM_norm: "f -- a --> l \<Longrightarrow> (\<lambda>x. norm (f x)) -- a --> norm l"
by (erule LIM_imp_LIM, simp add: norm_triangle_ineq3)

lemma LIM_norm_zero: "f -- a --> 0 \<Longrightarrow> (\<lambda>x. norm (f x)) -- a --> 0"
by (drule LIM_norm, simp)

lemma LIM_norm_zero_cancel: "(\<lambda>x. norm (f x)) -- a --> 0 \<Longrightarrow> f -- a --> 0"
by (erule LIM_imp_LIM, simp)

lemma LIM_norm_zero_iff: "(\<lambda>x. norm (f x)) -- a --> 0 = f -- a --> 0"
by (rule iffI [OF LIM_norm_zero_cancel LIM_norm_zero])

lemma LIM_rabs: "f -- a --> (l::real) \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) -- a --> \<bar>l\<bar>"
by (fold real_norm_def, rule LIM_norm)

lemma LIM_rabs_zero: "f -- a --> (0::real) \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) -- a --> 0"
by (fold real_norm_def, rule LIM_norm_zero)

lemma LIM_rabs_zero_cancel: "(\<lambda>x. \<bar>f x\<bar>) -- a --> (0::real) \<Longrightarrow> f -- a --> 0"
by (fold real_norm_def, rule LIM_norm_zero_cancel)

lemma LIM_rabs_zero_iff: "(\<lambda>x. \<bar>f x\<bar>) -- a --> (0::real) = f -- a --> 0"
by (fold real_norm_def, rule LIM_norm_zero_iff)

lemma LIM_const_not_eq:
  fixes a :: "'a::real_normed_algebra_1"
  shows "k \<noteq> L \<Longrightarrow> \<not> (\<lambda>x. k) -- a --> L"
apply (simp add: LIM_eq)
apply (rule_tac x="norm (k - L)" in exI, simp, safe)
apply (rule_tac x="a + of_real (s/2)" in exI, simp add: norm_of_real)
done

lemmas LIM_not_zero = LIM_const_not_eq [where L = 0]

lemma LIM_const_eq:
  fixes a :: "'a::real_normed_algebra_1"
  shows "(\<lambda>x. k) -- a --> L \<Longrightarrow> k = L"
apply (rule ccontr)
apply (blast dest: LIM_const_not_eq)
done

lemma LIM_unique:
  fixes a :: "'a::real_normed_algebra_1"
  shows "\<lbrakk>f -- a --> L; f -- a --> M\<rbrakk> \<Longrightarrow> L = M"
apply (drule (1) LIM_diff)
apply (auto dest!: LIM_const_eq)
done

lemma LIM_ident [simp]: "(\<lambda>x. x) -- a --> a"
by (auto simp add: LIM_def)

text{*Limits are equal for functions equal except at limit point*}
lemma LIM_equal:
     "[| \<forall>x. x \<noteq> a --> (f x = g x) |] ==> (f -- a --> l) = (g -- a --> l)"
by (simp add: LIM_def)

lemma LIM_cong:
  "\<lbrakk>a = b; \<And>x. x \<noteq> b \<Longrightarrow> f x = g x; l = m\<rbrakk>
   \<Longrightarrow> ((\<lambda>x. f x) -- a --> l) = ((\<lambda>x. g x) -- b --> m)"
by (simp add: LIM_def)

lemma LIM_equal2:
  assumes 1: "0 < R"
  assumes 2: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < R\<rbrakk> \<Longrightarrow> f x = g x"
  shows "g -- a --> l \<Longrightarrow> f -- a --> l"
apply (unfold LIM_def, safe)
apply (drule_tac x="r" in spec, safe)
apply (rule_tac x="min s R" in exI, safe)
apply (simp add: 1)
apply (simp add: 2)
done

text{*Two uses in Hyperreal/Transcendental.ML*}
lemma LIM_trans:
     "[| (%x. f(x) + -g(x)) -- a --> 0;  g -- a --> l |] ==> f -- a --> l"
apply (drule LIM_add, assumption)
apply (auto simp add: add_assoc)
done

lemma LIM_compose:
  assumes g: "g -- l --> g l"
  assumes f: "f -- a --> l"
  shows "(\<lambda>x. g (f x)) -- a --> g l"
proof (rule LIM_I)
  fix r::real assume r: "0 < r"
  obtain s where s: "0 < s"
    and less_r: "\<And>y. \<lbrakk>y \<noteq> l; norm (y - l) < s\<rbrakk> \<Longrightarrow> norm (g y - g l) < r"
    using LIM_D [OF g r] by fast
  obtain t where t: "0 < t"
    and less_s: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < t\<rbrakk> \<Longrightarrow> norm (f x - l) < s"
    using LIM_D [OF f s] by fast

  show "\<exists>t>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < t \<longrightarrow> norm (g (f x) - g l) < r"
  proof (rule exI, safe)
    show "0 < t" using t .
  next
    fix x assume "x \<noteq> a" and "norm (x - a) < t"
    hence "norm (f x - l) < s" by (rule less_s)
    thus "norm (g (f x) - g l) < r"
      using r less_r by (case_tac "f x = l", simp_all)
  qed
qed

lemma LIM_compose2:
  assumes f: "f -- a --> b"
  assumes g: "g -- b --> c"
  assumes inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < d \<longrightarrow> f x \<noteq> b"
  shows "(\<lambda>x. g (f x)) -- a --> c"
proof (rule LIM_I)
  fix r :: real
  assume r: "0 < r"
  obtain s where s: "0 < s"
    and less_r: "\<And>y. \<lbrakk>y \<noteq> b; norm (y - b) < s\<rbrakk> \<Longrightarrow> norm (g y - c) < r"
    using LIM_D [OF g r] by fast
  obtain t where t: "0 < t"
    and less_s: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < t\<rbrakk> \<Longrightarrow> norm (f x - b) < s"
    using LIM_D [OF f s] by fast
  obtain d where d: "0 < d"
    and neq_b: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < d\<rbrakk> \<Longrightarrow> f x \<noteq> b"
    using inj by fast

  show "\<exists>t>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < t \<longrightarrow> norm (g (f x) - c) < r"
  proof (safe intro!: exI)
    show "0 < min d t" using d t by simp
  next
    fix x
    assume "x \<noteq> a" and "norm (x - a) < min d t"
    hence "f x \<noteq> b" and "norm (f x - b) < s"
      using neq_b less_s by simp_all
    thus "norm (g (f x) - c) < r"
      by (rule less_r)
  qed
qed

lemma LIM_o: "\<lbrakk>g -- l --> g l; f -- a --> l\<rbrakk> \<Longrightarrow> (g \<circ> f) -- a --> g l"
unfolding o_def by (rule LIM_compose)

lemma real_LIM_sandwich_zero:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> real"
  assumes f: "f -- a --> 0"
  assumes 1: "\<And>x. x \<noteq> a \<Longrightarrow> 0 \<le> g x"
  assumes 2: "\<And>x. x \<noteq> a \<Longrightarrow> g x \<le> f x"
  shows "g -- a --> 0"
proof (rule LIM_imp_LIM [OF f])
  fix x assume x: "x \<noteq> a"
  have "norm (g x - 0) = g x" by (simp add: 1 x)
  also have "g x \<le> f x" by (rule 2 [OF x])
  also have "f x \<le> \<bar>f x\<bar>" by (rule abs_ge_self)
  also have "\<bar>f x\<bar> = norm (f x - 0)" by simp
  finally show "norm (g x - 0) \<le> norm (f x - 0)" .
qed

text {* Bounded Linear Operators *}

lemma (in bounded_linear) cont: "f -- a --> f a"
proof (rule LIM_I)
  fix r::real assume r: "0 < r"
  obtain K where K: "0 < K" and norm_le: "\<And>x. norm (f x) \<le> norm x * K"
    using pos_bounded by fast
  show "\<exists>s>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < s \<longrightarrow> norm (f x - f a) < r"
  proof (rule exI, safe)
    from r K show "0 < r / K" by (rule divide_pos_pos)
  next
    fix x assume x: "norm (x - a) < r / K"
    have "norm (f x - f a) = norm (f (x - a))" by (simp only: diff)
    also have "\<dots> \<le> norm (x - a) * K" by (rule norm_le)
    also from K x have "\<dots> < r" by (simp only: pos_less_divide_eq)
    finally show "norm (f x - f a) < r" .
  qed
qed

lemma (in bounded_linear) LIM:
  "g -- a --> l \<Longrightarrow> (\<lambda>x. f (g x)) -- a --> f l"
by (rule LIM_compose [OF cont])

lemma (in bounded_linear) LIM_zero:
  "g -- a --> 0 \<Longrightarrow> (\<lambda>x. f (g x)) -- a --> 0"
by (drule LIM, simp only: zero)

text {* Bounded Bilinear Operators *}

lemma (in bounded_bilinear) LIM_prod_zero:
  assumes f: "f -- a --> 0"
  assumes g: "g -- a --> 0"
  shows "(\<lambda>x. f x ** g x) -- a --> 0"
proof (rule LIM_I)
  fix r::real assume r: "0 < r"
  obtain K where K: "0 < K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using pos_bounded by fast
  from K have K': "0 < inverse K"
    by (rule positive_imp_inverse_positive)
  obtain s where s: "0 < s"
    and norm_f: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < s\<rbrakk> \<Longrightarrow> norm (f x) < r"
    using LIM_D [OF f r] by auto
  obtain t where t: "0 < t"
    and norm_g: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < t\<rbrakk> \<Longrightarrow> norm (g x) < inverse K"
    using LIM_D [OF g K'] by auto
  show "\<exists>s>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < s \<longrightarrow> norm (f x ** g x - 0) < r"
  proof (rule exI, safe)
    from s t show "0 < min s t" by simp
  next
    fix x assume x: "x \<noteq> a"
    assume "norm (x - a) < min s t"
    hence xs: "norm (x - a) < s" and xt: "norm (x - a) < t" by simp_all
    from x xs have 1: "norm (f x) < r" by (rule norm_f)
    from x xt have 2: "norm (g x) < inverse K" by (rule norm_g)
    have "norm (f x ** g x) \<le> norm (f x) * norm (g x) * K" by (rule norm_le)
    also from 1 2 K have "\<dots> < r * inverse K * K"
      by (intro mult_strict_right_mono mult_strict_mono' norm_ge_zero)
    also from K have "r * inverse K * K = r" by simp
    finally show "norm (f x ** g x - 0) < r" by simp
  qed
qed

lemma (in bounded_bilinear) LIM_left_zero:
  "f -- a --> 0 \<Longrightarrow> (\<lambda>x. f x ** c) -- a --> 0"
by (rule bounded_linear.LIM_zero [OF bounded_linear_left])

lemma (in bounded_bilinear) LIM_right_zero:
  "f -- a --> 0 \<Longrightarrow> (\<lambda>x. c ** f x) -- a --> 0"
by (rule bounded_linear.LIM_zero [OF bounded_linear_right])

lemma (in bounded_bilinear) LIM:
  "\<lbrakk>f -- a --> L; g -- a --> M\<rbrakk> \<Longrightarrow> (\<lambda>x. f x ** g x) -- a --> L ** M"
apply (drule LIM_zero)
apply (drule LIM_zero)
apply (rule LIM_zero_cancel)
apply (subst prod_diff_prod)
apply (rule LIM_add_zero)
apply (rule LIM_add_zero)
apply (erule (1) LIM_prod_zero)
apply (erule LIM_left_zero)
apply (erule LIM_right_zero)
done

lemmas LIM_mult = mult.LIM

lemmas LIM_mult_zero = mult.LIM_prod_zero

lemmas LIM_mult_left_zero = mult.LIM_left_zero

lemmas LIM_mult_right_zero = mult.LIM_right_zero

lemmas LIM_scaleR = scaleR.LIM

lemmas LIM_of_real = of_real.LIM

lemma LIM_power:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::{power,real_normed_algebra}"
  assumes f: "f -- a --> l"
  shows "(\<lambda>x. f x ^ n) -- a --> l ^ n"
by (induct n, simp, simp add: LIM_mult f)

subsubsection {* Derived theorems about @{term LIM} *}

lemma LIM_inverse_lemma:
  fixes x :: "'a::real_normed_div_algebra"
  assumes r: "0 < r"
  assumes x: "norm (x - 1) < min (1/2) (r/2)"
  shows "norm (inverse x - 1) < r"
proof -
  from r have r2: "0 < r/2" by simp
  from x have 0: "x \<noteq> 0" by clarsimp
  from x have x': "norm (1 - x) < min (1/2) (r/2)"
    by (simp only: norm_minus_commute)
  hence less1: "norm (1 - x) < r/2" by simp
  have "norm (1::'a) - norm x \<le> norm (1 - x)" by (rule norm_triangle_ineq2)
  also from x' have "norm (1 - x) < 1/2" by simp
  finally have "1/2 < norm x" by simp
  hence "inverse (norm x) < inverse (1/2)"
    by (rule less_imp_inverse_less, simp)
  hence less2: "norm (inverse x) < 2"
    by (simp add: nonzero_norm_inverse 0)
  from less1 less2 r2 norm_ge_zero
  have "norm (1 - x) * norm (inverse x) < (r/2) * 2"
    by (rule mult_strict_mono)
  thus "norm (inverse x - 1) < r"
    by (simp only: norm_mult [symmetric] left_diff_distrib, simp add: 0)
qed

lemma LIM_inverse_fun:
  assumes a: "a \<noteq> (0::'a::real_normed_div_algebra)"
  shows "inverse -- a --> inverse a"
proof (rule LIM_equal2)
  from a show "0 < norm a" by simp
next
  fix x assume "norm (x - a) < norm a"
  hence "x \<noteq> 0" by auto
  with a show "inverse x = inverse (inverse a * x) * inverse a"
    by (simp add: nonzero_inverse_mult_distrib
                  nonzero_imp_inverse_nonzero
                  nonzero_inverse_inverse_eq mult_assoc)
next
  have 1: "inverse -- 1 --> inverse (1::'a)"
    apply (rule LIM_I)
    apply (rule_tac x="min (1/2) (r/2)" in exI)
    apply (simp add: LIM_inverse_lemma)
    done
  have "(\<lambda>x. inverse a * x) -- a --> inverse a * a"
    by (intro LIM_mult LIM_ident LIM_const)
  hence "(\<lambda>x. inverse a * x) -- a --> 1"
    by (simp add: a)
  with 1 have "(\<lambda>x. inverse (inverse a * x)) -- a --> inverse 1"
    by (rule LIM_compose)
  hence "(\<lambda>x. inverse (inverse a * x)) -- a --> 1"
    by simp
  hence "(\<lambda>x. inverse (inverse a * x) * inverse a) -- a --> 1 * inverse a"
    by (intro LIM_mult LIM_const)
  thus "(\<lambda>x. inverse (inverse a * x) * inverse a) -- a --> inverse a"
    by simp
qed

lemma LIM_inverse:
  fixes L :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>f -- a --> L; L \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>x. inverse (f x)) -- a --> inverse L"
by (rule LIM_inverse_fun [THEN LIM_compose])

lemma LIM_sgn:
  "\<lbrakk>f -- a --> l; l \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>x. sgn (f x)) -- a --> sgn l"
unfolding sgn_div_norm
by (simp add: LIM_scaleR LIM_inverse LIM_norm)


subsection {* Continuity *}

subsubsection {* Purely standard proofs *}

lemma LIM_isCont_iff: "(f -- a --> f a) = ((\<lambda>h. f (a + h)) -- 0 --> f a)"
by (rule iffI [OF LIM_offset_zero LIM_offset_zero_cancel])

lemma isCont_iff: "isCont f x = (\<lambda>h. f (x + h)) -- 0 --> f x"
by (simp add: isCont_def LIM_isCont_iff)

lemma isCont_ident [simp]: "isCont (\<lambda>x. x) a"
  unfolding isCont_def by (rule LIM_ident)

lemma isCont_const [simp]: "isCont (\<lambda>x. k) a"
  unfolding isCont_def by (rule LIM_const)

lemma isCont_norm: "isCont f a \<Longrightarrow> isCont (\<lambda>x. norm (f x)) a"
  unfolding isCont_def by (rule LIM_norm)

lemma isCont_rabs: "isCont f a \<Longrightarrow> isCont (\<lambda>x. \<bar>f x :: real\<bar>) a"
  unfolding isCont_def by (rule LIM_rabs)

lemma isCont_add: "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x + g x) a"
  unfolding isCont_def by (rule LIM_add)

lemma isCont_minus: "isCont f a \<Longrightarrow> isCont (\<lambda>x. - f x) a"
  unfolding isCont_def by (rule LIM_minus)

lemma isCont_diff: "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x - g x) a"
  unfolding isCont_def by (rule LIM_diff)

lemma isCont_mult:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  shows "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x * g x) a"
  unfolding isCont_def by (rule LIM_mult)

lemma isCont_inverse:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_div_algebra"
  shows "\<lbrakk>isCont f a; f a \<noteq> 0\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. inverse (f x)) a"
  unfolding isCont_def by (rule LIM_inverse)

lemma isCont_LIM_compose:
  "\<lbrakk>isCont g l; f -- a --> l\<rbrakk> \<Longrightarrow> (\<lambda>x. g (f x)) -- a --> g l"
  unfolding isCont_def by (rule LIM_compose)

lemma isCont_LIM_compose2:
  assumes f [unfolded isCont_def]: "isCont f a"
  assumes g: "g -- f a --> l"
  assumes inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < d \<longrightarrow> f x \<noteq> f a"
  shows "(\<lambda>x. g (f x)) -- a --> l"
by (rule LIM_compose2 [OF f g inj])

lemma isCont_o2: "\<lbrakk>isCont f a; isCont g (f a)\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. g (f x)) a"
  unfolding isCont_def by (rule LIM_compose)

lemma isCont_o: "\<lbrakk>isCont f a; isCont g (f a)\<rbrakk> \<Longrightarrow> isCont (g o f) a"
  unfolding o_def by (rule isCont_o2)

lemma (in bounded_linear) isCont: "isCont f a"
  unfolding isCont_def by (rule cont)

lemma (in bounded_bilinear) isCont:
  "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x ** g x) a"
  unfolding isCont_def by (rule LIM)

lemmas isCont_scaleR = scaleR.isCont

lemma isCont_of_real:
  "isCont f a \<Longrightarrow> isCont (\<lambda>x. of_real (f x)) a"
  unfolding isCont_def by (rule LIM_of_real)

lemma isCont_power:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::{power,real_normed_algebra}"
  shows "isCont f a \<Longrightarrow> isCont (\<lambda>x. f x ^ n) a"
  unfolding isCont_def by (rule LIM_power)

lemma isCont_sgn:
  "\<lbrakk>isCont f a; f a \<noteq> 0\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. sgn (f x)) a"
  unfolding isCont_def by (rule LIM_sgn)

lemma isCont_abs [simp]: "isCont abs (a::real)"
by (rule isCont_rabs [OF isCont_ident])

lemma isCont_setsum: fixes A :: "nat set" assumes "finite A"
  shows "\<forall> i \<in> A. isCont (f i) x \<Longrightarrow> isCont (\<lambda> x. \<Sum> i \<in> A. f i x) x"
  using `finite A`
proof induct
  case (insert a F) show "isCont (\<lambda> x. \<Sum> i \<in> (insert a F). f i x) x" 
    unfolding setsum_insert[OF `finite F` `a \<notin> F`] by (rule isCont_add, auto simp add: insert)
qed auto

lemma LIM_less_bound: fixes f :: "real \<Rightarrow> real" assumes "b < x"
  and all_le: "\<forall> x' \<in> { b <..< x}. 0 \<le> f x'" and isCont: "isCont f x"
  shows "0 \<le> f x"
proof (rule ccontr)
  assume "\<not> 0 \<le> f x" hence "f x < 0" by auto
  hence "0 < - f x / 2" by auto
  from isCont[unfolded isCont_def, THEN LIM_D, OF this]
  obtain s where "s > 0" and s_D: "\<And>x'. \<lbrakk> x' \<noteq> x ; \<bar> x' - x \<bar> < s \<rbrakk> \<Longrightarrow> \<bar> f x' - f x \<bar> < - f x / 2" by auto

  let ?x = "x - min (s / 2) ((x - b) / 2)"
  have "?x < x" and "\<bar> ?x - x \<bar> < s"
    using `b < x` and `0 < s` by auto
  have "b < ?x"
  proof (cases "s < x - b")
    case True thus ?thesis using `0 < s` by auto
  next
    case False hence "s / 2 \<ge> (x - b) / 2" by auto
    from inf_absorb2[OF this, unfolded inf_real_def]
    have "?x = (x + b) / 2" by auto
    thus ?thesis using `b < x` by auto
  qed
  hence "0 \<le> f ?x" using all_le `?x < x` by auto
  moreover have "\<bar>f ?x - f x\<bar> < - f x / 2"
    using s_D[OF _ `\<bar> ?x - x \<bar> < s`] `?x < x` by auto
  hence "f ?x - f x < - f x / 2" by auto
  hence "f ?x < f x / 2" by auto
  hence "f ?x < 0" using `f x < 0` by auto
  thus False using `0 \<le> f ?x` by auto
qed
  

subsection {* Uniform Continuity *}

lemma isUCont_isCont: "isUCont f ==> isCont f x"
by (simp add: isUCont_def isCont_def LIM_def, force)

lemma isUCont_Cauchy:
  "\<lbrakk>isUCont f; Cauchy X\<rbrakk> \<Longrightarrow> Cauchy (\<lambda>n. f (X n))"
unfolding isUCont_def
apply (rule CauchyI)
apply (drule_tac x=e in spec, safe)
apply (drule_tac e=s in CauchyD, safe)
apply (rule_tac x=M in exI, simp)
done

lemma (in bounded_linear) isUCont: "isUCont f"
unfolding isUCont_def
proof (intro allI impI)
  fix r::real assume r: "0 < r"
  obtain K where K: "0 < K" and norm_le: "\<And>x. norm (f x) \<le> norm x * K"
    using pos_bounded by fast
  show "\<exists>s>0. \<forall>x y. norm (x - y) < s \<longrightarrow> norm (f x - f y) < r"
  proof (rule exI, safe)
    from r K show "0 < r / K" by (rule divide_pos_pos)
  next
    fix x y :: 'a
    assume xy: "norm (x - y) < r / K"
    have "norm (f x - f y) = norm (f (x - y))" by (simp only: diff)
    also have "\<dots> \<le> norm (x - y) * K" by (rule norm_le)
    also from K xy have "\<dots> < r" by (simp only: pos_less_divide_eq)
    finally show "norm (f x - f y) < r" .
  qed
qed

lemma (in bounded_linear) Cauchy: "Cauchy X \<Longrightarrow> Cauchy (\<lambda>n. f (X n))"
by (rule isUCont [THEN isUCont_Cauchy])


subsection {* Relation of LIM and LIMSEQ *}

lemma LIMSEQ_SEQ_conv1:
  fixes a :: "'a::real_normed_vector"
  assumes X: "X -- a --> L"
  shows "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L"
proof (safe intro!: LIMSEQ_I)
  fix S :: "nat \<Rightarrow> 'a"
  fix r :: real
  assume rgz: "0 < r"
  assume as: "\<forall>n. S n \<noteq> a"
  assume S: "S ----> a"
  from LIM_D [OF X rgz] obtain s
    where sgz: "0 < s"
    and aux: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < s\<rbrakk> \<Longrightarrow> norm (X x - L) < r"
    by fast
  from LIMSEQ_D [OF S sgz]
  obtain no where "\<forall>n\<ge>no. norm (S n - a) < s" by blast
  hence "\<forall>n\<ge>no. norm (X (S n) - L) < r" by (simp add: aux as)
  thus "\<exists>no. \<forall>n\<ge>no. norm (X (S n) - L) < r" ..
qed

lemma LIMSEQ_SEQ_conv2:
  fixes a :: real
  assumes "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L"
  shows "X -- a --> L"
proof (rule ccontr)
  assume "\<not> (X -- a --> L)"
  hence "\<not> (\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a & norm (x - a) < s --> norm (X x - L) < r)" by (unfold LIM_def)
  hence "\<exists>r > 0. \<forall>s > 0. \<exists>x. \<not>(x \<noteq> a \<and> \<bar>x - a\<bar> < s --> norm (X x - L) < r)" by simp
  hence "\<exists>r > 0. \<forall>s > 0. \<exists>x. (x \<noteq> a \<and> \<bar>x - a\<bar> < s \<and> norm (X x - L) \<ge> r)" by (simp add: linorder_not_less)
  then obtain r where rdef: "r > 0 \<and> (\<forall>s > 0. \<exists>x. (x \<noteq> a \<and> \<bar>x - a\<bar> < s \<and> norm (X x - L) \<ge> r))" by auto

  let ?F = "\<lambda>n::nat. SOME x. x\<noteq>a \<and> \<bar>x - a\<bar> < inverse (real (Suc n)) \<and> norm (X x - L) \<ge> r"
  have "\<And>n. \<exists>x. x\<noteq>a \<and> \<bar>x - a\<bar> < inverse (real (Suc n)) \<and> norm (X x - L) \<ge> r"
    using rdef by simp
  hence F: "\<And>n. ?F n \<noteq> a \<and> \<bar>?F n - a\<bar> < inverse (real (Suc n)) \<and> norm (X (?F n) - L) \<ge> r"
    by (rule someI_ex)
  hence F1: "\<And>n. ?F n \<noteq> a"
    and F2: "\<And>n. \<bar>?F n - a\<bar> < inverse (real (Suc n))"
    and F3: "\<And>n. norm (X (?F n) - L) \<ge> r"
    by fast+

  have "?F ----> a"
  proof (rule LIMSEQ_I, unfold real_norm_def)
      fix e::real
      assume "0 < e"
        (* choose no such that inverse (real (Suc n)) < e *)
      then have "\<exists>no. inverse (real (Suc no)) < e" by (rule reals_Archimedean)
      then obtain m where nodef: "inverse (real (Suc m)) < e" by auto
      show "\<exists>no. \<forall>n. no \<le> n --> \<bar>?F n - a\<bar> < e"
      proof (intro exI allI impI)
        fix n
        assume mlen: "m \<le> n"
        have "\<bar>?F n - a\<bar> < inverse (real (Suc n))"
          by (rule F2)
        also have "inverse (real (Suc n)) \<le> inverse (real (Suc m))"
          using mlen by auto
        also from nodef have
          "inverse (real (Suc m)) < e" .
        finally show "\<bar>?F n - a\<bar> < e" .
      qed
  qed
  
  moreover have "\<forall>n. ?F n \<noteq> a"
    by (rule allI) (rule F1)

  moreover from prems have "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L" by simp
  ultimately have "(\<lambda>n. X (?F n)) ----> L" by simp
  
  moreover have "\<not> ((\<lambda>n. X (?F n)) ----> L)"
  proof -
    {
      fix no::nat
      obtain n where "n = no + 1" by simp
      then have nolen: "no \<le> n" by simp
        (* We prove this by showing that for any m there is an n\<ge>m such that |X (?F n) - L| \<ge> r *)
      have "norm (X (?F n) - L) \<ge> r"
        by (rule F3)
      with nolen have "\<exists>n. no \<le> n \<and> norm (X (?F n) - L) \<ge> r" by fast
    }
    then have "(\<forall>no. \<exists>n. no \<le> n \<and> norm (X (?F n) - L) \<ge> r)" by simp
    with rdef have "\<exists>e>0. (\<forall>no. \<exists>n. no \<le> n \<and> norm (X (?F n) - L) \<ge> e)" by auto
    thus ?thesis by (unfold LIMSEQ_def, auto simp add: linorder_not_less)
  qed
  ultimately show False by simp
qed

lemma LIMSEQ_SEQ_conv:
  "(\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> (a::real) \<longrightarrow> (\<lambda>n. X (S n)) ----> L) =
   (X -- a --> L)"
proof
  assume "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L"
  thus "X -- a --> L" by (rule LIMSEQ_SEQ_conv2)
next
  assume "(X -- a --> L)"
  thus "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L" by (rule LIMSEQ_SEQ_conv1)
qed

end
