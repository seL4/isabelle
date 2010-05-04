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
  [code del]: "isUCont f = (\<forall>r>0. \<exists>s>0. \<forall>x y. dist x y < s \<longrightarrow> dist (f x) (f y) < r)"

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

lemma LIM_const [simp]: "(%x. k) -- x --> k"
by (rule tendsto_const)

lemma LIM_cong_limit: "\<lbrakk> f -- x --> L ; K = L \<rbrakk> \<Longrightarrow> f -- x --> K" by simp

lemma LIM_add:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  assumes f: "f -- a --> L" and g: "g -- a --> M"
  shows "(\<lambda>x. f x + g x) -- a --> (L + M)"
using assms by (rule tendsto_add)

lemma LIM_add_zero:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "\<lbrakk>f -- a --> 0; g -- a --> 0\<rbrakk> \<Longrightarrow> (\<lambda>x. f x + g x) -- a --> 0"
by (drule (1) LIM_add, simp)

lemma LIM_minus:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "f -- a --> L \<Longrightarrow> (\<lambda>x. - f x) -- a --> - L"
by (rule tendsto_minus)

(* TODO: delete *)
lemma LIM_add_minus:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) + -g(x)) -- x --> (l + -m)"
by (intro LIM_add LIM_minus)

lemma LIM_diff:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "\<lbrakk>f -- x --> l; g -- x --> m\<rbrakk> \<Longrightarrow> (\<lambda>x. f x - g x) -- x --> l - m"
by (rule tendsto_diff)

lemma LIM_zero:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "f -- a --> l \<Longrightarrow> (\<lambda>x. f x - l) -- a --> 0"
unfolding tendsto_iff dist_norm by simp

lemma LIM_zero_cancel:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "(\<lambda>x. f x - l) -- a --> 0 \<Longrightarrow> f -- a --> l"
unfolding tendsto_iff dist_norm by simp

lemma LIM_zero_iff:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "(\<lambda>x. f x - l) -- a --> 0 = f -- a --> l"
unfolding tendsto_iff dist_norm by simp

lemma metric_LIM_imp_LIM:
  assumes f: "f -- a --> l"
  assumes le: "\<And>x. x \<noteq> a \<Longrightarrow> dist (g x) m \<le> dist (f x) l"
  shows "g -- a --> m"
apply (rule tendstoI, drule tendstoD [OF f])
apply (simp add: eventually_at_topological, safe)
apply (rule_tac x="S" in exI, safe)
apply (drule_tac x="x" in bspec, safe)
apply (erule (1) order_le_less_trans [OF le])
done

lemma LIM_imp_LIM:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  fixes g :: "'a::topological_space \<Rightarrow> 'c::real_normed_vector"
  assumes f: "f -- a --> l"
  assumes le: "\<And>x. x \<noteq> a \<Longrightarrow> norm (g x - m) \<le> norm (f x - l)"
  shows "g -- a --> m"
apply (rule metric_LIM_imp_LIM [OF f])
apply (simp add: dist_norm le)
done

lemma LIM_norm:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "f -- a --> l \<Longrightarrow> (\<lambda>x. norm (f x)) -- a --> norm l"
by (rule tendsto_norm)

lemma LIM_norm_zero:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "f -- a --> 0 \<Longrightarrow> (\<lambda>x. norm (f x)) -- a --> 0"
by (rule tendsto_norm_zero)

lemma LIM_norm_zero_cancel:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "(\<lambda>x. norm (f x)) -- a --> 0 \<Longrightarrow> f -- a --> 0"
by (rule tendsto_norm_zero_cancel)

lemma LIM_norm_zero_iff:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "(\<lambda>x. norm (f x)) -- a --> 0 = f -- a --> 0"
by (rule tendsto_norm_zero_iff)

lemma LIM_rabs: "f -- a --> (l::real) \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) -- a --> \<bar>l\<bar>"
by (fold real_norm_def, rule LIM_norm)

lemma LIM_rabs_zero: "f -- a --> (0::real) \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar>) -- a --> 0"
by (fold real_norm_def, rule LIM_norm_zero)

lemma LIM_rabs_zero_cancel: "(\<lambda>x. \<bar>f x\<bar>) -- a --> (0::real) \<Longrightarrow> f -- a --> 0"
by (fold real_norm_def, rule LIM_norm_zero_cancel)

lemma LIM_rabs_zero_iff: "(\<lambda>x. \<bar>f x\<bar>) -- a --> (0::real) = f -- a --> 0"
by (fold real_norm_def, rule LIM_norm_zero_iff)

lemma at_neq_bot:
  fixes a :: "'a::real_normed_algebra_1"
  shows "at a \<noteq> bot"  -- {* TODO: find a more appropriate class *}
unfolding eventually_False [symmetric]
unfolding eventually_at dist_norm
by (clarsimp, rule_tac x="a + of_real (d/2)" in exI, simp)

lemma LIM_const_not_eq:
  fixes a :: "'a::real_normed_algebra_1"
  fixes k L :: "'b::metric_space"
  shows "k \<noteq> L \<Longrightarrow> \<not> (\<lambda>x. k) -- a --> L"
by (simp add: tendsto_const_iff at_neq_bot)

lemmas LIM_not_zero = LIM_const_not_eq [where L = 0]

lemma LIM_const_eq:
  fixes a :: "'a::real_normed_algebra_1"
  fixes k L :: "'b::metric_space"
  shows "(\<lambda>x. k) -- a --> L \<Longrightarrow> k = L"
by (simp add: tendsto_const_iff at_neq_bot)

lemma LIM_unique:
  fixes a :: "'a::real_normed_algebra_1" -- {* TODO: find a more appropriate class *}
  fixes L M :: "'b::metric_space"
  shows "\<lbrakk>f -- a --> L; f -- a --> M\<rbrakk> \<Longrightarrow> L = M"
by (drule (1) tendsto_dist, simp add: tendsto_const_iff at_neq_bot)

lemma LIM_ident [simp]: "(\<lambda>x. x) -- a --> a"
by (rule tendsto_ident_at)

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

text{*Two uses in Transcendental.ML*} (* BH: no longer true; delete? *)
lemma LIM_trans:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "[| (%x. f(x) + -g(x)) -- a --> 0;  g -- a --> l |] ==> f -- a --> l"
apply (drule LIM_add, assumption)
apply (auto simp add: add_assoc)
done

lemma LIM_compose:
  assumes g: "g -- l --> g l"
  assumes f: "f -- a --> l"
  shows "(\<lambda>x. g (f x)) -- a --> g l"
proof (rule topological_tendstoI)
  fix C assume C: "open C" "g l \<in> C"
  obtain B where B: "open B" "l \<in> B"
    and gC: "\<And>y. y \<in> B \<Longrightarrow> y \<noteq> l \<Longrightarrow> g y \<in> C"
    using topological_tendstoD [OF g C]
    unfolding eventually_at_topological by fast
  obtain A where A: "open A" "a \<in> A"
    and fB: "\<And>x. x \<in> A \<Longrightarrow> x \<noteq> a \<Longrightarrow> f x \<in> B"
    using topological_tendstoD [OF f B]
    unfolding eventually_at_topological by fast
  show "eventually (\<lambda>x. g (f x) \<in> C) (at a)"
  unfolding eventually_at_topological
  proof (intro exI conjI ballI impI)
    show "open A" and "a \<in> A" using A .
  next
    fix x assume "x \<in> A" and "x \<noteq> a"
    then show "g (f x) \<in> C"
      by (cases "f x = l", simp add: C, simp add: gC fB)
  qed
qed

lemma LIM_compose_eventually:
  assumes f: "f -- a --> b"
  assumes g: "g -- b --> c"
  assumes inj: "eventually (\<lambda>x. f x \<noteq> b) (at a)"
  shows "(\<lambda>x. g (f x)) -- a --> c"
proof (rule topological_tendstoI)
  fix C assume C: "open C" "c \<in> C"
  obtain B where B: "open B" "b \<in> B"
    and gC: "\<And>y. y \<in> B \<Longrightarrow> y \<noteq> b \<Longrightarrow> g y \<in> C"
    using topological_tendstoD [OF g C]
    unfolding eventually_at_topological by fast
  obtain A where A: "open A" "a \<in> A"
    and fB: "\<And>x. x \<in> A \<Longrightarrow> x \<noteq> a \<Longrightarrow> f x \<in> B"
    using topological_tendstoD [OF f B]
    unfolding eventually_at_topological by fast
  have "eventually (\<lambda>x. f x \<noteq> b \<longrightarrow> g (f x) \<in> C) (at a)"
  unfolding eventually_at_topological
  proof (intro exI conjI ballI impI)
    show "open A" and "a \<in> A" using A .
  next
    fix x assume "x \<in> A" and "x \<noteq> a" and "f x \<noteq> b"
    then show "g (f x) \<in> C" by (simp add: gC fB)
  qed
  with inj show "eventually (\<lambda>x. g (f x) \<in> C) (at a)"
    by (rule eventually_rev_mp)
qed

lemma metric_LIM_compose2:
  assumes f: "f -- a --> b"
  assumes g: "g -- b --> c"
  assumes inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> b"
  shows "(\<lambda>x. g (f x)) -- a --> c"
using f g inj [folded eventually_at]
by (rule LIM_compose_eventually)

lemma LIM_compose2:
  fixes a :: "'a::real_normed_vector"
  assumes f: "f -- a --> b"
  assumes g: "g -- b --> c"
  assumes inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < d \<longrightarrow> f x \<noteq> b"
  shows "(\<lambda>x. g (f x)) -- a --> c"
by (rule metric_LIM_compose2 [OF f g inj [folded dist_norm]])

lemma LIM_o: "\<lbrakk>g -- l --> g l; f -- a --> l\<rbrakk> \<Longrightarrow> (g \<circ> f) -- a --> g l"
unfolding o_def by (rule LIM_compose)

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

text {* Bounded Linear Operators *}

lemma (in bounded_linear) LIM:
  "g -- a --> l \<Longrightarrow> (\<lambda>x. f (g x)) -- a --> f l"
by (rule tendsto)

lemma (in bounded_linear) cont: "f -- a --> f a"
by (rule LIM [OF LIM_ident])

lemma (in bounded_linear) LIM_zero:
  "g -- a --> 0 \<Longrightarrow> (\<lambda>x. f (g x)) -- a --> 0"
by (drule LIM, simp only: zero)

text {* Bounded Bilinear Operators *}

lemma (in bounded_bilinear) LIM:
  "\<lbrakk>f -- a --> L; g -- a --> M\<rbrakk> \<Longrightarrow> (\<lambda>x. f x ** g x) -- a --> L ** M"
by (rule tendsto)

lemma (in bounded_bilinear) LIM_prod_zero:
  fixes a :: "'d::metric_space"
  assumes f: "f -- a --> 0"
  assumes g: "g -- a --> 0"
  shows "(\<lambda>x. f x ** g x) -- a --> 0"
using LIM [OF f g] by (simp add: zero_left)

lemma (in bounded_bilinear) LIM_left_zero:
  "f -- a --> 0 \<Longrightarrow> (\<lambda>x. f x ** c) -- a --> 0"
by (rule bounded_linear.LIM_zero [OF bounded_linear_left])

lemma (in bounded_bilinear) LIM_right_zero:
  "f -- a --> 0 \<Longrightarrow> (\<lambda>x. c ** f x) -- a --> 0"
by (rule bounded_linear.LIM_zero [OF bounded_linear_right])

lemmas LIM_mult = mult.LIM

lemmas LIM_mult_zero = mult.LIM_prod_zero

lemmas LIM_mult_left_zero = mult.LIM_left_zero

lemmas LIM_mult_right_zero = mult.LIM_right_zero

lemmas LIM_scaleR = scaleR.LIM

lemmas LIM_of_real = of_real.LIM

lemma LIM_power:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::{power,real_normed_algebra}"
  assumes f: "f -- a --> l"
  shows "(\<lambda>x. f x ^ n) -- a --> l ^ n"
by (induct n, simp, simp add: LIM_mult f)

subsubsection {* Derived theorems about @{term LIM} *}

lemma LIM_inverse:
  fixes L :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>f -- a --> L; L \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>x. inverse (f x)) -- a --> inverse L"
by (rule tendsto_inverse)

lemma LIM_inverse_fun:
  assumes a: "a \<noteq> (0::'a::real_normed_div_algebra)"
  shows "inverse -- a --> inverse a"
by (rule LIM_inverse [OF LIM_ident a])

lemma LIM_sgn:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "\<lbrakk>f -- a --> l; l \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>x. sgn (f x)) -- a --> sgn l"
unfolding sgn_div_norm
by (simp add: LIM_scaleR LIM_inverse LIM_norm)


subsection {* Continuity *}

lemma LIM_isCont_iff:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::metric_space"
  shows "(f -- a --> f a) = ((\<lambda>h. f (a + h)) -- 0 --> f a)"
by (rule iffI [OF LIM_offset_zero LIM_offset_zero_cancel])

lemma isCont_iff:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::metric_space"
  shows "isCont f x = (\<lambda>h. f (x + h)) -- 0 --> f x"
by (simp add: isCont_def LIM_isCont_iff)

lemma isCont_ident [simp]: "isCont (\<lambda>x. x) a"
  unfolding isCont_def by (rule LIM_ident)

lemma isCont_const [simp]: "isCont (\<lambda>x. k) a"
  unfolding isCont_def by (rule LIM_const)

lemma isCont_norm:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "isCont f a \<Longrightarrow> isCont (\<lambda>x. norm (f x)) a"
  unfolding isCont_def by (rule LIM_norm)

lemma isCont_rabs: "isCont f a \<Longrightarrow> isCont (\<lambda>x. \<bar>f x :: real\<bar>) a"
  unfolding isCont_def by (rule LIM_rabs)

lemma isCont_add:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x + g x) a"
  unfolding isCont_def by (rule LIM_add)

lemma isCont_minus:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "isCont f a \<Longrightarrow> isCont (\<lambda>x. - f x) a"
  unfolding isCont_def by (rule LIM_minus)

lemma isCont_diff:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x - g x) a"
  unfolding isCont_def by (rule LIM_diff)

lemma isCont_mult:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::real_normed_algebra"
  shows "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x * g x) a"
  unfolding isCont_def by (rule LIM_mult)

lemma isCont_inverse:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_div_algebra"
  shows "\<lbrakk>isCont f a; f a \<noteq> 0\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. inverse (f x)) a"
  unfolding isCont_def by (rule LIM_inverse)

lemma isCont_LIM_compose:
  "\<lbrakk>isCont g l; f -- a --> l\<rbrakk> \<Longrightarrow> (\<lambda>x. g (f x)) -- a --> g l"
  unfolding isCont_def by (rule LIM_compose)

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
  "isCont f a \<Longrightarrow> isCont (\<lambda>x. of_real (f x)::'b::real_normed_algebra_1) a"
  unfolding isCont_def by (rule LIM_of_real)

lemma isCont_power:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::{power,real_normed_algebra}"
  shows "isCont f a \<Longrightarrow> isCont (\<lambda>x. f x ^ n) a"
  unfolding isCont_def by (rule LIM_power)

lemma isCont_sgn:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "\<lbrakk>isCont f a; f a \<noteq> 0\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. sgn (f x)) a"
  unfolding isCont_def by (rule LIM_sgn)

lemma isCont_abs [simp]: "isCont abs (a::real)"
by (rule isCont_rabs [OF isCont_ident])

lemma isCont_setsum:
  fixes f :: "'a \<Rightarrow> 'b::metric_space \<Rightarrow> 'c::real_normed_vector"
  fixes A :: "'a set" assumes "finite A"
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

lemma LIMSEQ_SEQ_conv1:
  fixes a :: "'a::metric_space" and L :: "'b::metric_space"
  assumes X: "X -- a --> L"
  shows "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L"
proof (safe intro!: metric_LIMSEQ_I)
  fix S :: "nat \<Rightarrow> 'a"
  fix r :: real
  assume rgz: "0 < r"
  assume as: "\<forall>n. S n \<noteq> a"
  assume S: "S ----> a"
  from metric_LIM_D [OF X rgz] obtain s
    where sgz: "0 < s"
    and aux: "\<And>x. \<lbrakk>x \<noteq> a; dist x a < s\<rbrakk> \<Longrightarrow> dist (X x) L < r"
    by fast
  from metric_LIMSEQ_D [OF S sgz]
  obtain no where "\<forall>n\<ge>no. dist (S n) a < s" by blast
  hence "\<forall>n\<ge>no. dist (X (S n)) L < r" by (simp add: aux as)
  thus "\<exists>no. \<forall>n\<ge>no. dist (X (S n)) L < r" ..
qed


lemma LIMSEQ_SEQ_conv2:
  fixes a :: real and L :: "'a::metric_space"
  assumes "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L"
  shows "X -- a --> L"
proof (rule ccontr)
  assume "\<not> (X -- a --> L)"
  hence "\<not> (\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a & norm (x - a) < s --> dist (X x) L < r)"
    unfolding LIM_def dist_norm .
  hence "\<exists>r > 0. \<forall>s > 0. \<exists>x. \<not>(x \<noteq> a \<and> \<bar>x - a\<bar> < s --> dist (X x) L < r)" by simp
  hence "\<exists>r > 0. \<forall>s > 0. \<exists>x. (x \<noteq> a \<and> \<bar>x - a\<bar> < s \<and> dist (X x) L \<ge> r)" by (simp add: not_less)
  then obtain r where rdef: "r > 0 \<and> (\<forall>s > 0. \<exists>x. (x \<noteq> a \<and> \<bar>x - a\<bar> < s \<and> dist (X x) L \<ge> r))" by auto

  let ?F = "\<lambda>n::nat. SOME x. x\<noteq>a \<and> \<bar>x - a\<bar> < inverse (real (Suc n)) \<and> dist (X x) L \<ge> r"
  have "\<And>n. \<exists>x. x\<noteq>a \<and> \<bar>x - a\<bar> < inverse (real (Suc n)) \<and> dist (X x) L \<ge> r"
    using rdef by simp
  hence F: "\<And>n. ?F n \<noteq> a \<and> \<bar>?F n - a\<bar> < inverse (real (Suc n)) \<and> dist (X (?F n)) L \<ge> r"
    by (rule someI_ex)
  hence F1: "\<And>n. ?F n \<noteq> a"
    and F2: "\<And>n. \<bar>?F n - a\<bar> < inverse (real (Suc n))"
    and F3: "\<And>n. dist (X (?F n)) L \<ge> r"
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
      have "dist (X (?F n)) L \<ge> r"
        by (rule F3)
      with nolen have "\<exists>n. no \<le> n \<and> dist (X (?F n)) L \<ge> r" by fast
    }
    then have "(\<forall>no. \<exists>n. no \<le> n \<and> dist (X (?F n)) L \<ge> r)" by simp
    with rdef have "\<exists>e>0. (\<forall>no. \<exists>n. no \<le> n \<and> dist (X (?F n)) L \<ge> e)" by auto
    thus ?thesis by (unfold LIMSEQ_def, auto simp add: not_less)
  qed
  ultimately show False by simp
qed

lemma LIMSEQ_SEQ_conv:
  "(\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> (a::real) \<longrightarrow> (\<lambda>n. X (S n)) ----> L) =
   (X -- a --> (L::'a::metric_space))"
proof
  assume "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L"
  thus "X -- a --> L" by (rule LIMSEQ_SEQ_conv2)
next
  assume "(X -- a --> L)"
  thus "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L" by (rule LIMSEQ_SEQ_conv1)
qed

end
