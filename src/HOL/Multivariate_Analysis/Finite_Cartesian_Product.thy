(*  Title:      HOL/Multivariate_Analysis/Finite_Cartesian_Product.thy
    Author:     Amine Chaieb, University of Cambridge
*)

header {* Definition of finite Cartesian product types. *}

theory Finite_Cartesian_Product
imports
  Euclidean_Space
  L2_Norm
  "~~/src/HOL/Library/Numeral_Type"
begin

subsection {* Finite Cartesian products, with indexing and lambdas. *}

typedef (open) ('a, 'b) vec = "UNIV :: (('b::finite) \<Rightarrow> 'a) set"
  morphisms vec_nth vec_lambda ..

notation
  vec_nth (infixl "$" 90) and
  vec_lambda (binder "\<chi>" 10)

(*
  Translate "'b ^ 'n" into "'b ^ ('n :: finite)". When 'n has already more than
  the finite type class write "vec 'b 'n"
*)

syntax "_finite_vec" :: "type \<Rightarrow> type \<Rightarrow> type" ("(_ ^/ _)" [15, 16] 15)

parse_translation {*
let
  fun vec t u = Syntax.const @{type_syntax vec} $ t $ u;
  fun finite_vec_tr [t, u] =
    (case Term_Position.strip_positions u of
      v as Free (x, _) =>
        if Lexicon.is_tid x then
          vec t (Syntax.const @{syntax_const "_ofsort"} $ v $ Syntax.const @{class_syntax finite})
        else vec t u
    | _ => vec t u)
in
  [(@{syntax_const "_finite_vec"}, finite_vec_tr)]
end
*}

lemma vec_eq_iff: "(x = y) \<longleftrightarrow> (\<forall>i. x$i = y$i)"
  by (simp add: vec_nth_inject [symmetric] fun_eq_iff)

lemma vec_lambda_beta [simp]: "vec_lambda g $ i = g i"
  by (simp add: vec_lambda_inverse)

lemma vec_lambda_unique: "(\<forall>i. f$i = g i) \<longleftrightarrow> vec_lambda g = f"
  by (auto simp add: vec_eq_iff)

lemma vec_lambda_eta: "(\<chi> i. (g$i)) = g"
  by (simp add: vec_eq_iff)


subsection {* Group operations and class instances *}

instantiation vec :: (zero, finite) zero
begin
  definition "0 \<equiv> (\<chi> i. 0)"
  instance ..
end

instantiation vec :: (plus, finite) plus
begin
  definition "op + \<equiv> (\<lambda> x y. (\<chi> i. x$i + y$i))"
  instance ..
end

instantiation vec :: (minus, finite) minus
begin
  definition "op - \<equiv> (\<lambda> x y. (\<chi> i. x$i - y$i))"
  instance ..
end

instantiation vec :: (uminus, finite) uminus
begin
  definition "uminus \<equiv> (\<lambda> x. (\<chi> i. - (x$i)))"
  instance ..
end

lemma zero_index [simp]: "0 $ i = 0"
  unfolding zero_vec_def by simp

lemma vector_add_component [simp]: "(x + y)$i = x$i + y$i"
  unfolding plus_vec_def by simp

lemma vector_minus_component [simp]: "(x - y)$i = x$i - y$i"
  unfolding minus_vec_def by simp

lemma vector_uminus_component [simp]: "(- x)$i = - (x$i)"
  unfolding uminus_vec_def by simp

instance vec :: (semigroup_add, finite) semigroup_add
  by default (simp add: vec_eq_iff add_assoc)

instance vec :: (ab_semigroup_add, finite) ab_semigroup_add
  by default (simp add: vec_eq_iff add_commute)

instance vec :: (monoid_add, finite) monoid_add
  by default (simp_all add: vec_eq_iff)

instance vec :: (comm_monoid_add, finite) comm_monoid_add
  by default (simp add: vec_eq_iff)

instance vec :: (cancel_semigroup_add, finite) cancel_semigroup_add
  by default (simp_all add: vec_eq_iff)

instance vec :: (cancel_ab_semigroup_add, finite) cancel_ab_semigroup_add
  by default (simp add: vec_eq_iff)

instance vec :: (cancel_comm_monoid_add, finite) cancel_comm_monoid_add ..

instance vec :: (group_add, finite) group_add
  by default (simp_all add: vec_eq_iff diff_minus)

instance vec :: (ab_group_add, finite) ab_group_add
  by default (simp_all add: vec_eq_iff)


subsection {* Real vector space *}

instantiation vec :: (real_vector, finite) real_vector
begin

definition "scaleR \<equiv> (\<lambda> r x. (\<chi> i. scaleR r (x$i)))"

lemma vector_scaleR_component [simp]: "(scaleR r x)$i = scaleR r (x$i)"
  unfolding scaleR_vec_def by simp

instance
  by default (simp_all add: vec_eq_iff scaleR_left_distrib scaleR_right_distrib)

end


subsection {* Topological space *}

instantiation vec :: (topological_space, finite) topological_space
begin

definition
  "open (S :: ('a ^ 'b) set) \<longleftrightarrow>
    (\<forall>x\<in>S. \<exists>A. (\<forall>i. open (A i) \<and> x$i \<in> A i) \<and>
      (\<forall>y. (\<forall>i. y$i \<in> A i) \<longrightarrow> y \<in> S))"

instance proof
  show "open (UNIV :: ('a ^ 'b) set)"
    unfolding open_vec_def by auto
next
  fix S T :: "('a ^ 'b) set"
  assume "open S" "open T" thus "open (S \<inter> T)"
    unfolding open_vec_def
    apply clarify
    apply (drule (1) bspec)+
    apply (clarify, rename_tac Sa Ta)
    apply (rule_tac x="\<lambda>i. Sa i \<inter> Ta i" in exI)
    apply (simp add: open_Int)
    done
next
  fix K :: "('a ^ 'b) set set"
  assume "\<forall>S\<in>K. open S" thus "open (\<Union>K)"
    unfolding open_vec_def
    apply clarify
    apply (drule (1) bspec)
    apply (drule (1) bspec)
    apply clarify
    apply (rule_tac x=A in exI)
    apply fast
    done
qed

end

lemma open_vector_box: "\<forall>i. open (S i) \<Longrightarrow> open {x. \<forall>i. x $ i \<in> S i}"
  unfolding open_vec_def by auto

lemma open_vimage_vec_nth: "open S \<Longrightarrow> open ((\<lambda>x. x $ i) -` S)"
  unfolding open_vec_def
  apply clarify
  apply (rule_tac x="\<lambda>k. if k = i then S else UNIV" in exI, simp)
  done

lemma closed_vimage_vec_nth: "closed S \<Longrightarrow> closed ((\<lambda>x. x $ i) -` S)"
  unfolding closed_open vimage_Compl [symmetric]
  by (rule open_vimage_vec_nth)

lemma closed_vector_box: "\<forall>i. closed (S i) \<Longrightarrow> closed {x. \<forall>i. x $ i \<in> S i}"
proof -
  have "{x. \<forall>i. x $ i \<in> S i} = (\<Inter>i. (\<lambda>x. x $ i) -` S i)" by auto
  thus "\<forall>i. closed (S i) \<Longrightarrow> closed {x. \<forall>i. x $ i \<in> S i}"
    by (simp add: closed_INT closed_vimage_vec_nth)
qed

lemma tendsto_vec_nth [tendsto_intros]:
  assumes "((\<lambda>x. f x) ---> a) net"
  shows "((\<lambda>x. f x $ i) ---> a $ i) net"
proof (rule topological_tendstoI)
  fix S assume "open S" "a $ i \<in> S"
  then have "open ((\<lambda>y. y $ i) -` S)" "a \<in> ((\<lambda>y. y $ i) -` S)"
    by (simp_all add: open_vimage_vec_nth)
  with assms have "eventually (\<lambda>x. f x \<in> (\<lambda>y. y $ i) -` S) net"
    by (rule topological_tendstoD)
  then show "eventually (\<lambda>x. f x $ i \<in> S) net"
    by simp
qed

lemma isCont_vec_nth [simp]: "isCont f a \<Longrightarrow> isCont (\<lambda>x. f x $ i) a"
  unfolding isCont_def by (rule tendsto_vec_nth)

lemma eventually_Ball_finite: (* TODO: move *)
  assumes "finite A" and "\<forall>y\<in>A. eventually (\<lambda>x. P x y) net"
  shows "eventually (\<lambda>x. \<forall>y\<in>A. P x y) net"
using assms by (induct set: finite, simp, simp add: eventually_conj)

lemma eventually_all_finite: (* TODO: move *)
  fixes P :: "'a \<Rightarrow> 'b::finite \<Rightarrow> bool"
  assumes "\<And>y. eventually (\<lambda>x. P x y) net"
  shows "eventually (\<lambda>x. \<forall>y. P x y) net"
using eventually_Ball_finite [of UNIV P] assms by simp

lemma vec_tendstoI:
  assumes "\<And>i. ((\<lambda>x. f x $ i) ---> a $ i) net"
  shows "((\<lambda>x. f x) ---> a) net"
proof (rule topological_tendstoI)
  fix S assume "open S" and "a \<in> S"
  then obtain A where A: "\<And>i. open (A i)" "\<And>i. a $ i \<in> A i"
    and S: "\<And>y. \<forall>i. y $ i \<in> A i \<Longrightarrow> y \<in> S"
    unfolding open_vec_def by metis
  have "\<And>i. eventually (\<lambda>x. f x $ i \<in> A i) net"
    using assms A by (rule topological_tendstoD)
  hence "eventually (\<lambda>x. \<forall>i. f x $ i \<in> A i) net"
    by (rule eventually_all_finite)
  thus "eventually (\<lambda>x. f x \<in> S) net"
    by (rule eventually_elim1, simp add: S)
qed

lemma tendsto_vec_lambda [tendsto_intros]:
  assumes "\<And>i. ((\<lambda>x. f x i) ---> a i) net"
  shows "((\<lambda>x. \<chi> i. f x i) ---> (\<chi> i. a i)) net"
  using assms by (simp add: vec_tendstoI)

lemma open_image_vec_nth: assumes "open S" shows "open ((\<lambda>x. x $ i) ` S)"
proof (rule openI)
  fix a assume "a \<in> (\<lambda>x. x $ i) ` S"
  then obtain z where "a = z $ i" and "z \<in> S" ..
  then obtain A where A: "\<forall>i. open (A i) \<and> z $ i \<in> A i"
    and S: "\<forall>y. (\<forall>i. y $ i \<in> A i) \<longrightarrow> y \<in> S"
    using `open S` unfolding open_vec_def by auto
  hence "A i \<subseteq> (\<lambda>x. x $ i) ` S"
    by (clarsimp, rule_tac x="\<chi> j. if j = i then x else z $ j" in image_eqI,
      simp_all)
  hence "open (A i) \<and> a \<in> A i \<and> A i \<subseteq> (\<lambda>x. x $ i) ` S"
    using A `a = z $ i` by simp
  then show "\<exists>T. open T \<and> a \<in> T \<and> T \<subseteq> (\<lambda>x. x $ i) ` S" by - (rule exI)
qed

instance vec :: (perfect_space, finite) perfect_space
proof
  fix x :: "'a ^ 'b" show "\<not> open {x}"
  proof
    assume "open {x}"
    hence "\<forall>i. open ((\<lambda>x. x $ i) ` {x})" by (fast intro: open_image_vec_nth)   
    hence "\<forall>i. open {x $ i}" by simp
    thus "False" by (simp add: not_open_singleton)
  qed
qed


subsection {* Metric space *}

instantiation vec :: (metric_space, finite) metric_space
begin

definition
  "dist x y = setL2 (\<lambda>i. dist (x$i) (y$i)) UNIV"

lemma dist_vec_nth_le: "dist (x $ i) (y $ i) \<le> dist x y"
  unfolding dist_vec_def by (rule member_le_setL2) simp_all

instance proof
  fix x y :: "'a ^ 'b"
  show "dist x y = 0 \<longleftrightarrow> x = y"
    unfolding dist_vec_def
    by (simp add: setL2_eq_0_iff vec_eq_iff)
next
  fix x y z :: "'a ^ 'b"
  show "dist x y \<le> dist x z + dist y z"
    unfolding dist_vec_def
    apply (rule order_trans [OF _ setL2_triangle_ineq])
    apply (simp add: setL2_mono dist_triangle2)
    done
next
  fix S :: "('a ^ 'b) set"
  show "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"
  proof
    assume "open S" show "\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S"
    proof
      fix x assume "x \<in> S"
      obtain A where A: "\<forall>i. open (A i)" "\<forall>i. x $ i \<in> A i"
        and S: "\<forall>y. (\<forall>i. y $ i \<in> A i) \<longrightarrow> y \<in> S"
        using `open S` and `x \<in> S` unfolding open_vec_def by metis
      have "\<forall>i\<in>UNIV. \<exists>r>0. \<forall>y. dist y (x $ i) < r \<longrightarrow> y \<in> A i"
        using A unfolding open_dist by simp
      hence "\<exists>r. \<forall>i\<in>UNIV. 0 < r i \<and> (\<forall>y. dist y (x $ i) < r i \<longrightarrow> y \<in> A i)"
        by (rule finite_set_choice [OF finite])
      then obtain r where r1: "\<forall>i. 0 < r i"
        and r2: "\<forall>i y. dist y (x $ i) < r i \<longrightarrow> y \<in> A i" by fast
      have "0 < Min (range r) \<and> (\<forall>y. dist y x < Min (range r) \<longrightarrow> y \<in> S)"
        by (simp add: r1 r2 S le_less_trans [OF dist_vec_nth_le])
      thus "\<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S" ..
    qed
  next
    assume *: "\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S" show "open S"
    proof (unfold open_vec_def, rule)
      fix x assume "x \<in> S"
      then obtain e where "0 < e" and S: "\<forall>y. dist y x < e \<longrightarrow> y \<in> S"
        using * by fast
      def r \<equiv> "\<lambda>i::'b. e / sqrt (of_nat CARD('b))"
      from `0 < e` have r: "\<forall>i. 0 < r i"
        unfolding r_def by (simp_all add: divide_pos_pos)
      from `0 < e` have e: "e = setL2 r UNIV"
        unfolding r_def by (simp add: setL2_constant)
      def A \<equiv> "\<lambda>i. {y. dist (x $ i) y < r i}"
      have "\<forall>i. open (A i) \<and> x $ i \<in> A i"
        unfolding A_def by (simp add: open_ball r)
      moreover have "\<forall>y. (\<forall>i. y $ i \<in> A i) \<longrightarrow> y \<in> S"
        by (simp add: A_def S dist_vec_def e setL2_strict_mono dist_commute)
      ultimately show "\<exists>A. (\<forall>i. open (A i) \<and> x $ i \<in> A i) \<and>
        (\<forall>y. (\<forall>i. y $ i \<in> A i) \<longrightarrow> y \<in> S)" by metis
    qed
  qed
qed

end

lemma Cauchy_vec_nth:
  "Cauchy (\<lambda>n. X n) \<Longrightarrow> Cauchy (\<lambda>n. X n $ i)"
  unfolding Cauchy_def by (fast intro: le_less_trans [OF dist_vec_nth_le])

lemma vec_CauchyI:
  fixes X :: "nat \<Rightarrow> 'a::metric_space ^ 'n"
  assumes X: "\<And>i. Cauchy (\<lambda>n. X n $ i)"
  shows "Cauchy (\<lambda>n. X n)"
proof (rule metric_CauchyI)
  fix r :: real assume "0 < r"
  then have "0 < r / of_nat CARD('n)" (is "0 < ?s")
    by (simp add: divide_pos_pos)
  def N \<equiv> "\<lambda>i. LEAST N. \<forall>m\<ge>N. \<forall>n\<ge>N. dist (X m $ i) (X n $ i) < ?s"
  def M \<equiv> "Max (range N)"
  have "\<And>i. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. dist (X m $ i) (X n $ i) < ?s"
    using X `0 < ?s` by (rule metric_CauchyD)
  hence "\<And>i. \<forall>m\<ge>N i. \<forall>n\<ge>N i. dist (X m $ i) (X n $ i) < ?s"
    unfolding N_def by (rule LeastI_ex)
  hence M: "\<And>i. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m $ i) (X n $ i) < ?s"
    unfolding M_def by simp
  {
    fix m n :: nat
    assume "M \<le> m" "M \<le> n"
    have "dist (X m) (X n) = setL2 (\<lambda>i. dist (X m $ i) (X n $ i)) UNIV"
      unfolding dist_vec_def ..
    also have "\<dots> \<le> setsum (\<lambda>i. dist (X m $ i) (X n $ i)) UNIV"
      by (rule setL2_le_setsum [OF zero_le_dist])
    also have "\<dots> < setsum (\<lambda>i::'n. ?s) UNIV"
      by (rule setsum_strict_mono, simp_all add: M `M \<le> m` `M \<le> n`)
    also have "\<dots> = r"
      by simp
    finally have "dist (X m) (X n) < r" .
  }
  hence "\<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < r"
    by simp
  then show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < r" ..
qed

instance vec :: (complete_space, finite) complete_space
proof
  fix X :: "nat \<Rightarrow> 'a ^ 'b" assume "Cauchy X"
  have "\<And>i. (\<lambda>n. X n $ i) ----> lim (\<lambda>n. X n $ i)"
    using Cauchy_vec_nth [OF `Cauchy X`]
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  hence "X ----> vec_lambda (\<lambda>i. lim (\<lambda>n. X n $ i))"
    by (simp add: vec_tendstoI)
  then show "convergent X"
    by (rule convergentI)
qed


subsection {* Normed vector space *}

instantiation vec :: (real_normed_vector, finite) real_normed_vector
begin

definition "norm x = setL2 (\<lambda>i. norm (x$i)) UNIV"

definition "sgn (x::'a^'b) = scaleR (inverse (norm x)) x"

instance proof
  fix a :: real and x y :: "'a ^ 'b"
  show "0 \<le> norm x"
    unfolding norm_vec_def
    by (rule setL2_nonneg)
  show "norm x = 0 \<longleftrightarrow> x = 0"
    unfolding norm_vec_def
    by (simp add: setL2_eq_0_iff vec_eq_iff)
  show "norm (x + y) \<le> norm x + norm y"
    unfolding norm_vec_def
    apply (rule order_trans [OF _ setL2_triangle_ineq])
    apply (simp add: setL2_mono norm_triangle_ineq)
    done
  show "norm (scaleR a x) = \<bar>a\<bar> * norm x"
    unfolding norm_vec_def
    by (simp add: setL2_right_distrib)
  show "sgn x = scaleR (inverse (norm x)) x"
    by (rule sgn_vec_def)
  show "dist x y = norm (x - y)"
    unfolding dist_vec_def norm_vec_def
    by (simp add: dist_norm)
qed

end

lemma norm_nth_le: "norm (x $ i) \<le> norm x"
unfolding norm_vec_def
by (rule member_le_setL2) simp_all

lemma bounded_linear_vec_nth: "bounded_linear (\<lambda>x. x $ i)"
apply default
apply (rule vector_add_component)
apply (rule vector_scaleR_component)
apply (rule_tac x="1" in exI, simp add: norm_nth_le)
done

instance vec :: (banach, finite) banach ..


subsection {* Inner product space *}

instantiation vec :: (real_inner, finite) real_inner
begin

definition "inner x y = setsum (\<lambda>i. inner (x$i) (y$i)) UNIV"

instance proof
  fix r :: real and x y z :: "'a ^ 'b"
  show "inner x y = inner y x"
    unfolding inner_vec_def
    by (simp add: inner_commute)
  show "inner (x + y) z = inner x z + inner y z"
    unfolding inner_vec_def
    by (simp add: inner_add_left setsum_addf)
  show "inner (scaleR r x) y = r * inner x y"
    unfolding inner_vec_def
    by (simp add: setsum_right_distrib)
  show "0 \<le> inner x x"
    unfolding inner_vec_def
    by (simp add: setsum_nonneg)
  show "inner x x = 0 \<longleftrightarrow> x = 0"
    unfolding inner_vec_def
    by (simp add: vec_eq_iff setsum_nonneg_eq_0_iff)
  show "norm x = sqrt (inner x x)"
    unfolding inner_vec_def norm_vec_def setL2_def
    by (simp add: power2_norm_eq_inner)
qed

end


subsection {* Euclidean space *}

text {* Vectors pointing along a single axis. *}

definition "axis k x = (\<chi> i. if i = k then x else 0)"

lemma axis_nth [simp]: "axis i x $ i = x"
  unfolding axis_def by simp

lemma axis_eq_axis: "axis i x = axis j y \<longleftrightarrow> x = y \<and> i = j \<or> x = 0 \<and> y = 0"
  unfolding axis_def vec_eq_iff by auto

lemma inner_axis_axis:
  "inner (axis i x) (axis j y) = (if i = j then inner x y else 0)"
  unfolding inner_vec_def
  apply (cases "i = j")
  apply clarsimp
  apply (subst setsum_diff1' [where a=j], simp_all)
  apply (rule setsum_0', simp add: axis_def)
  apply (rule setsum_0', simp add: axis_def)
  done

lemma setsum_single:
  assumes "finite A" and "k \<in> A" and "f k = y"
  assumes "\<And>i. i \<in> A \<Longrightarrow> i \<noteq> k \<Longrightarrow> f i = 0"
  shows "(\<Sum>i\<in>A. f i) = y"
  apply (subst setsum_diff1' [OF assms(1,2)])
  apply (simp add: setsum_0' assms(3,4))
  done

lemma inner_axis: "inner x (axis i y) = inner (x $ i) y"
  unfolding inner_vec_def
  apply (rule_tac k=i in setsum_single)
  apply simp_all
  apply (simp add: axis_def)
  done

text {* A bijection between @{text "'n::finite"} and @{text "{..<CARD('n)}"} *}

definition vec_bij_nat :: "nat \<Rightarrow> ('n::finite)" where
  "vec_bij_nat = (SOME p. bij_betw p {..<CARD('n)} (UNIV::'n set) )"

abbreviation "\<pi> \<equiv> vec_bij_nat"
definition "\<pi>' = inv_into {..<CARD('n)} (\<pi>::nat \<Rightarrow> ('n::finite))"

lemma bij_betw_pi:
  "bij_betw \<pi> {..<CARD('n::finite)} (UNIV::('n::finite) set)"
  using ex_bij_betw_nat_finite[of "UNIV::'n set"]
  by (auto simp: vec_bij_nat_def atLeast0LessThan
    intro!: someI_ex[of "\<lambda>x. bij_betw x {..<CARD('n)} (UNIV::'n set)"])

lemma bij_betw_pi'[intro]: "bij_betw \<pi>' (UNIV::'n set) {..<CARD('n::finite)}"
  using bij_betw_inv_into[OF bij_betw_pi] unfolding \<pi>'_def by auto

lemma pi'_inj[intro]: "inj \<pi>'"
  using bij_betw_pi' unfolding bij_betw_def by auto

lemma pi'_range[intro]: "\<And>i::'n. \<pi>' i < CARD('n::finite)"
  using bij_betw_pi' unfolding bij_betw_def by auto

lemma \<pi>\<pi>'[simp]: "\<And>i::'n::finite. \<pi> (\<pi>' i) = i"
  using bij_betw_pi by (auto intro!: f_inv_into_f simp: \<pi>'_def bij_betw_def)

lemma \<pi>'\<pi>[simp]: "\<And>i. i\<in>{..<CARD('n::finite)} \<Longrightarrow> \<pi>' (\<pi> i::'n) = i"
  using bij_betw_pi by (auto intro!: inv_into_f_eq simp: \<pi>'_def bij_betw_def)

lemma \<pi>\<pi>'_alt[simp]: "\<And>i. i<CARD('n::finite) \<Longrightarrow> \<pi>' (\<pi> i::'n) = i"
  by auto

lemma \<pi>_inj_on: "inj_on (\<pi>::nat\<Rightarrow>'n::finite) {..<CARD('n)}"
  using bij_betw_pi[where 'n='n] by (simp add: bij_betw_def)

instantiation vec :: (euclidean_space, finite) euclidean_space
begin

definition "Basis = (\<Union>i. \<Union>u\<in>Basis. {axis i u})"

definition "dimension (t :: ('a ^ 'b) itself) = CARD('b) * DIM('a)"

definition "basis i =
  (if i < (CARD('b) * DIM('a))
  then axis (\<pi>(i div DIM('a))) (basis (i mod DIM('a)))
  else 0)"

lemma basis_eq:
  assumes "i < CARD('b)" and "j < DIM('a)"
  shows "basis (j + i * DIM('a)) = axis (\<pi> i) (basis j)"
proof -
  have "j + i * DIM('a) <  DIM('a) * (i + 1)" using assms by (auto simp: field_simps)
  also have "\<dots> \<le> DIM('a) * CARD('b)" using assms unfolding mult_le_cancel1 by auto
  finally show ?thesis
    unfolding basis_vec_def using assms by (auto simp: vec_eq_iff not_less field_simps)
qed

lemma basis_eq_pi':
  assumes "j < DIM('a)"
  shows "basis (j + \<pi>' i * DIM('a)) $ k = (if k = i then basis j else 0)"
  apply (subst basis_eq)
  using pi'_range assms by (simp_all add: axis_def)

lemma split_times_into_modulo[consumes 1]:
  fixes k :: nat
  assumes "k < A * B"
  obtains i j where "i < A" and "j < B" and "k = j + i * B"
proof
  have "A * B \<noteq> 0"
  proof assume "A * B = 0" with assms show False by simp qed
  hence "0 < B" by auto
  thus "k mod B < B" using `0 < B` by auto
next
  have "k div B * B \<le> k div B * B + k mod B" by (rule le_add1)
  also have "... < A * B" using assms by simp
  finally show "k div B < A" by auto
qed simp

lemma linear_less_than_times:
  fixes i j A B :: nat assumes "i < B" "j < A"
  shows "j + i * A < B * A"
proof -
  have "i * A + j < (Suc i)*A" using `j < A` by simp
  also have "\<dots> \<le> B * A" using `i < B` unfolding mult_le_cancel2 by simp
  finally show ?thesis by simp
qed

lemma DIM_cart[simp]: "DIM('a^'b) = CARD('b) * DIM('a)"
  by (rule dimension_vec_def)

instance proof
  show "(Basis :: ('a ^ 'b) set) \<noteq> {}"
    unfolding Basis_vec_def by simp
next
  show "finite (Basis :: ('a ^ 'b) set)"
    unfolding Basis_vec_def by simp
next
  fix u v :: "'a ^ 'b"
  assume "u \<in> Basis" and "v \<in> Basis"
  thus "inner u v = (if u = v then 1 else 0)"
    unfolding Basis_vec_def
    by (auto simp add: inner_axis_axis axis_eq_axis inner_Basis)
next
  fix x :: "'a ^ 'b"
  show "(\<forall>u\<in>Basis. inner x u = 0) \<longleftrightarrow> x = 0"
    unfolding Basis_vec_def
    by (simp add: inner_axis euclidean_all_zero_iff vec_eq_iff)
next
  show "DIM('a ^ 'b) = card (Basis :: ('a ^ 'b) set)"
    unfolding Basis_vec_def dimension_vec_def dimension_def
    by (simp add: card_UN_disjoint [unfolded disjoint_iff_not_equal]
      axis_eq_axis nonzero_Basis)
next
  show "basis ` {..<DIM('a ^ 'b)} = (Basis :: ('a ^ 'b) set)"
    unfolding Basis_vec_def
    apply auto
    apply (erule split_times_into_modulo)
    apply (simp add: basis_eq axis_eq_axis)
    apply (erule Basis_elim)
    apply (simp add: image_def basis_vec_def axis_eq_axis)
    apply (rule rev_bexI, simp)
    apply (erule linear_less_than_times [OF pi'_range])
    apply simp
    done
next
  show "basis ` {DIM('a ^ 'b)..} = {0::'a ^ 'b}"
    by (auto simp add: image_def basis_vec_def)
qed

end

end
