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

abbreviation
  LIM :: "['a::topological_space \<Rightarrow> 'b::topological_space, 'a, 'b] \<Rightarrow> bool"
        ("((_)/ -- (_)/ --> (_))" [60, 0, 60] 60) where
  "f -- a --> L \<equiv> (f ---> L) (at a)"

definition
  isCont :: "['a::topological_space \<Rightarrow> 'b::topological_space, 'a] \<Rightarrow> bool" where
  "isCont f a = (f -- a --> (f a))"

definition
  isUCont :: "['a::metric_space \<Rightarrow> 'b::metric_space] \<Rightarrow> bool" where
  "isUCont f = (\<forall>r>0. \<exists>s>0. \<forall>x y. dist x y < s \<longrightarrow> dist (f x) (f y) < r)"

subsection {* Limits of Functions *}

lemma LIM_def: "f -- a --> L =
     (\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a & dist x a < s
        --> dist (f x) L < r)"
unfolding tendsto_iff eventually_at ..

lemma metric_LIM_I:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r)
    \<Longrightarrow> f -- a --> L"
by (simp add: LIM_def)

lemma metric_LIM_D:
  "\<lbrakk>f -- a --> L; 0 < r\<rbrakk>
    \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r"
by (simp add: LIM_def)

lemma LIM_eq:
  fixes a :: "'a::real_normed_vector" and L :: "'b::real_normed_vector"
  shows "f -- a --> L =
     (\<forall>r>0.\<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r)"
by (simp add: LIM_def dist_norm)

lemma LIM_I:
  fixes a :: "'a::real_normed_vector" and L :: "'b::real_normed_vector"
  shows "(!!r. 0<r ==> \<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r)
      ==> f -- a --> L"
by (simp add: LIM_eq)

lemma LIM_D:
  fixes a :: "'a::real_normed_vector" and L :: "'b::real_normed_vector"
  shows "[| f -- a --> L; 0<r |]
      ==> \<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r"
by (simp add: LIM_eq)

lemma LIM_offset:
  fixes a :: "'a::real_normed_vector"
  shows "f -- a --> L \<Longrightarrow> (\<lambda>x. f (x + k)) -- a - k --> L"
apply (rule topological_tendstoI)
apply (drule (2) topological_tendstoD)
apply (simp only: eventually_at dist_norm)
apply (clarify, rule_tac x=d in exI, safe)
apply (drule_tac x="x + k" in spec)
apply (simp add: algebra_simps)
done

lemma LIM_offset_zero:
  fixes a :: "'a::real_normed_vector"
  shows "f -- a --> L \<Longrightarrow> (\<lambda>h. f (a + h)) -- 0 --> L"
by (drule_tac k="a" in LIM_offset, simp add: add_commute)

lemma LIM_offset_zero_cancel:
  fixes a :: "'a::real_normed_vector"
  shows "(\<lambda>h. f (a + h)) -- 0 --> L \<Longrightarrow> f -- a --> L"
by (drule_tac k="- a" in LIM_offset, simp)

lemma LIM_cong_limit: "\<lbrakk> f -- x --> L ; K = L \<rbrakk> \<Longrightarrow> f -- x --> K" by simp

lemma LIM_zero:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "(f ---> l) F \<Longrightarrow> ((\<lambda>x. f x - l) ---> 0) F"
unfolding tendsto_iff dist_norm by simp

lemma LIM_zero_cancel:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "((\<lambda>x. f x - l) ---> 0) F \<Longrightarrow> (f ---> l) F"
unfolding tendsto_iff dist_norm by simp

lemma LIM_zero_iff:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "((\<lambda>x. f x - l) ---> 0) F = (f ---> l) F"
unfolding tendsto_iff dist_norm by simp

lemma metric_LIM_imp_LIM:
  assumes f: "f -- a --> l"
  assumes le: "\<And>x. x \<noteq> a \<Longrightarrow> dist (g x) m \<le> dist (f x) l"
  shows "g -- a --> m"
  by (rule metric_tendsto_imp_tendsto [OF f],
    auto simp add: eventually_at_topological le)

lemma LIM_imp_LIM:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  fixes g :: "'a::topological_space \<Rightarrow> 'c::real_normed_vector"
  assumes f: "f -- a --> l"
  assumes le: "\<And>x. x \<noteq> a \<Longrightarrow> norm (g x - m) \<le> norm (f x - l)"
  shows "g -- a --> m"
  by (rule metric_LIM_imp_LIM [OF f],
    simp add: dist_norm le)

lemma LIM_const_not_eq:
  fixes a :: "'a::perfect_space"
  fixes k L :: "'b::t2_space"
  shows "k \<noteq> L \<Longrightarrow> \<not> (\<lambda>x. k) -- a --> L"
  by (simp add: tendsto_const_iff)

lemmas LIM_not_zero = LIM_const_not_eq [where L = 0]

lemma LIM_const_eq:
  fixes a :: "'a::perfect_space"
  fixes k L :: "'b::t2_space"
  shows "(\<lambda>x. k) -- a --> L \<Longrightarrow> k = L"
  by (simp add: tendsto_const_iff)

lemma LIM_unique:
  fixes a :: "'a::perfect_space"
  fixes L M :: "'b::t2_space"
  shows "\<lbrakk>f -- a --> L; f -- a --> M\<rbrakk> \<Longrightarrow> L = M"
  using at_neq_bot by (rule tendsto_unique)

text{*Limits are equal for functions equal except at limit point*}
lemma LIM_equal:
     "[| \<forall>x. x \<noteq> a --> (f x = g x) |] ==> (f -- a --> l) = (g -- a --> l)"
unfolding tendsto_def eventually_at_topological by simp

lemma LIM_cong:
  "\<lbrakk>a = b; \<And>x. x \<noteq> b \<Longrightarrow> f x = g x; l = m\<rbrakk>
   \<Longrightarrow> ((\<lambda>x. f x) -- a --> l) = ((\<lambda>x. g x) -- b --> m)"
by (simp add: LIM_equal)

lemma metric_LIM_equal2:
  assumes 1: "0 < R"
  assumes 2: "\<And>x. \<lbrakk>x \<noteq> a; dist x a < R\<rbrakk> \<Longrightarrow> f x = g x"
  shows "g -- a --> l \<Longrightarrow> f -- a --> l"
apply (rule topological_tendstoI)
apply (drule (2) topological_tendstoD)
apply (simp add: eventually_at, safe)
apply (rule_tac x="min d R" in exI, safe)
apply (simp add: 1)
apply (simp add: 2)
done

lemma LIM_equal2:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::topological_space"
  assumes 1: "0 < R"
  assumes 2: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < R\<rbrakk> \<Longrightarrow> f x = g x"
  shows "g -- a --> l \<Longrightarrow> f -- a --> l"
by (rule metric_LIM_equal2 [OF 1 2], simp_all add: dist_norm)

lemma LIM_compose_eventually:
  assumes f: "f -- a --> b"
  assumes g: "g -- b --> c"
  assumes inj: "eventually (\<lambda>x. f x \<noteq> b) (at a)"
  shows "(\<lambda>x. g (f x)) -- a --> c"
  using g f inj by (rule tendsto_compose_eventually)

lemma metric_LIM_compose2:
  assumes f: "f -- a --> b"
  assumes g: "g -- b --> c"
  assumes inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> b"
  shows "(\<lambda>x. g (f x)) -- a --> c"
  using g f inj [folded eventually_at]
  by (rule tendsto_compose_eventually)

lemma LIM_compose2:
  fixes a :: "'a::real_normed_vector"
  assumes f: "f -- a --> b"
  assumes g: "g -- b --> c"
  assumes inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < d \<longrightarrow> f x \<noteq> b"
  shows "(\<lambda>x. g (f x)) -- a --> c"
by (rule metric_LIM_compose2 [OF f g inj [folded dist_norm]])

lemma LIM_o: "\<lbrakk>g -- l --> g l; f -- a --> l\<rbrakk> \<Longrightarrow> (g \<circ> f) -- a --> g l"
  unfolding o_def by (rule tendsto_compose)

lemma real_LIM_sandwich_zero:
  fixes f g :: "'a::topological_space \<Rightarrow> real"
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


subsection {* Continuity *}

lemma LIM_isCont_iff:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::topological_space"
  shows "(f -- a --> f a) = ((\<lambda>h. f (a + h)) -- 0 --> f a)"
by (rule iffI [OF LIM_offset_zero LIM_offset_zero_cancel])

lemma isCont_iff:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::topological_space"
  shows "isCont f x = (\<lambda>h. f (x + h)) -- 0 --> f x"
by (simp add: isCont_def LIM_isCont_iff)

lemma isCont_ident [simp]: "isCont (\<lambda>x. x) a"
  unfolding isCont_def by (rule tendsto_ident_at)

lemma isCont_const [simp]: "isCont (\<lambda>x. k) a"
  unfolding isCont_def by (rule tendsto_const)

lemma isCont_norm [simp]:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "isCont f a \<Longrightarrow> isCont (\<lambda>x. norm (f x)) a"
  unfolding isCont_def by (rule tendsto_norm)

lemma isCont_rabs [simp]:
  fixes f :: "'a::topological_space \<Rightarrow> real"
  shows "isCont f a \<Longrightarrow> isCont (\<lambda>x. \<bar>f x\<bar>) a"
  unfolding isCont_def by (rule tendsto_rabs)

lemma isCont_add [simp]:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x + g x) a"
  unfolding isCont_def by (rule tendsto_add)

lemma isCont_minus [simp]:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "isCont f a \<Longrightarrow> isCont (\<lambda>x. - f x) a"
  unfolding isCont_def by (rule tendsto_minus)

lemma isCont_diff [simp]:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x - g x) a"
  unfolding isCont_def by (rule tendsto_diff)

lemma isCont_mult [simp]:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::real_normed_algebra"
  shows "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x * g x) a"
  unfolding isCont_def by (rule tendsto_mult)

lemma isCont_inverse [simp]:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_div_algebra"
  shows "\<lbrakk>isCont f a; f a \<noteq> 0\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. inverse (f x)) a"
  unfolding isCont_def by (rule tendsto_inverse)

lemma isCont_divide [simp]:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::real_normed_field"
  shows "\<lbrakk>isCont f a; isCont g a; g a \<noteq> 0\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x / g x) a"
  unfolding isCont_def by (rule tendsto_divide)

lemma isCont_tendsto_compose:
  "\<lbrakk>isCont g l; (f ---> l) F\<rbrakk> \<Longrightarrow> ((\<lambda>x. g (f x)) ---> g l) F"
  unfolding isCont_def by (rule tendsto_compose)

lemma metric_isCont_LIM_compose2:
  assumes f [unfolded isCont_def]: "isCont f a"
  assumes g: "g -- f a --> l"
  assumes inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> f a"
  shows "(\<lambda>x. g (f x)) -- a --> l"
by (rule metric_LIM_compose2 [OF f g inj])

lemma isCont_LIM_compose2:
  fixes a :: "'a::real_normed_vector"
  assumes f [unfolded isCont_def]: "isCont f a"
  assumes g: "g -- f a --> l"
  assumes inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < d \<longrightarrow> f x \<noteq> f a"
  shows "(\<lambda>x. g (f x)) -- a --> l"
by (rule LIM_compose2 [OF f g inj])

lemma isCont_o2: "\<lbrakk>isCont f a; isCont g (f a)\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. g (f x)) a"
  unfolding isCont_def by (rule tendsto_compose)

lemma isCont_o: "\<lbrakk>isCont f a; isCont g (f a)\<rbrakk> \<Longrightarrow> isCont (g o f) a"
  unfolding o_def by (rule isCont_o2)

lemma (in bounded_linear) isCont:
  "isCont g a \<Longrightarrow> isCont (\<lambda>x. f (g x)) a"
  unfolding isCont_def by (rule tendsto)

lemma (in bounded_bilinear) isCont:
  "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x ** g x) a"
  unfolding isCont_def by (rule tendsto)

lemmas isCont_scaleR [simp] =
  bounded_bilinear.isCont [OF bounded_bilinear_scaleR]

lemmas isCont_of_real [simp] =
  bounded_linear.isCont [OF bounded_linear_of_real]

lemma isCont_power [simp]:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::{power,real_normed_algebra}"
  shows "isCont f a \<Longrightarrow> isCont (\<lambda>x. f x ^ n) a"
  unfolding isCont_def by (rule tendsto_power)

lemma isCont_sgn [simp]:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "\<lbrakk>isCont f a; f a \<noteq> 0\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. sgn (f x)) a"
  unfolding isCont_def by (rule tendsto_sgn)

lemma isCont_setsum [simp]:
  fixes f :: "'a \<Rightarrow> 'b::topological_space \<Rightarrow> 'c::real_normed_vector"
  fixes A :: "'a set"
  shows "\<forall>i\<in>A. isCont (f i) a \<Longrightarrow> isCont (\<lambda>x. \<Sum>i\<in>A. f i x) a"
  unfolding isCont_def by (simp add: tendsto_setsum)

lemmas isCont_intros =
  isCont_ident isCont_const isCont_norm isCont_rabs isCont_add isCont_minus
  isCont_diff isCont_mult isCont_inverse isCont_divide isCont_scaleR
  isCont_of_real isCont_power isCont_sgn isCont_setsum

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
    hence "?x = (x + b) / 2" by (simp add: field_simps min_max.inf_absorb2)
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
apply (rule metric_CauchyI)
apply (drule_tac x=e in spec, safe)
apply (drule_tac e=s in metric_CauchyD, safe)
apply (rule_tac x=M in exI, simp)
done

lemma (in bounded_linear) isUCont: "isUCont f"
unfolding isUCont_def dist_norm
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

lemma sequentially_imp_eventually_within:
  fixes a :: "'a::metric_space"
  assumes "\<forall>f. (\<forall>n. f n \<in> s \<and> f n \<noteq> a) \<and> f ----> a \<longrightarrow>
    eventually (\<lambda>n. P (f n)) sequentially"
  shows "eventually P (at a within s)"
proof (rule ccontr)
  let ?I = "\<lambda>n. inverse (real (Suc n))"
  def F \<equiv> "\<lambda>n::nat. SOME x. x \<in> s \<and> x \<noteq> a \<and> dist x a < ?I n \<and> \<not> P x"
  assume "\<not> eventually P (at a within s)"
  hence P: "\<forall>d>0. \<exists>x. x \<in> s \<and> x \<noteq> a \<and> dist x a < d \<and> \<not> P x"
    unfolding Limits.eventually_within Limits.eventually_at by fast
  hence "\<And>n. \<exists>x. x \<in> s \<and> x \<noteq> a \<and> dist x a < ?I n \<and> \<not> P x" by simp
  hence F: "\<And>n. F n \<in> s \<and> F n \<noteq> a \<and> dist (F n) a < ?I n \<and> \<not> P (F n)"
    unfolding F_def by (rule someI_ex)
  hence F0: "\<forall>n. F n \<in> s" and F1: "\<forall>n. F n \<noteq> a"
    and F2: "\<forall>n. dist (F n) a < ?I n" and F3: "\<forall>n. \<not> P (F n)"
    by fast+
  from LIMSEQ_inverse_real_of_nat have "F ----> a"
    by (rule metric_tendsto_imp_tendsto,
      simp add: dist_norm F2 less_imp_le)
  hence "eventually (\<lambda>n. P (F n)) sequentially"
    using assms F0 F1 by simp
  thus "False" by (simp add: F3)
qed

lemma sequentially_imp_eventually_at:
  fixes a :: "'a::metric_space"
  assumes "\<forall>f. (\<forall>n. f n \<noteq> a) \<and> f ----> a \<longrightarrow>
    eventually (\<lambda>n. P (f n)) sequentially"
  shows "eventually P (at a)"
  using assms sequentially_imp_eventually_within [where s=UNIV] by simp

lemma LIMSEQ_SEQ_conv1:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes f: "f -- a --> l"
  shows "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. f (S n)) ----> l"
  using tendsto_compose_eventually [OF f, where F=sequentially] by simp

lemma LIMSEQ_SEQ_conv2:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::topological_space"
  assumes "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. f (S n)) ----> l"
  shows "f -- a --> l"
  using assms unfolding tendsto_def [where l=l]
  by (simp add: sequentially_imp_eventually_at)

lemma LIMSEQ_SEQ_conv:
  "(\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> (a::'a::metric_space) \<longrightarrow> (\<lambda>n. X (S n)) ----> L) =
   (X -- a --> (L::'b::topological_space))"
  using LIMSEQ_SEQ_conv2 LIMSEQ_SEQ_conv1 ..

end
