(*  Title:      HOL/Multivariate_Analysis/Finite_Cartesian_Product.thy
    Author:     Amine Chaieb, University of Cambridge
*)

header {* Definition of finite Cartesian product types. *}

theory Finite_Cartesian_Product
imports Inner_Product L2_Norm Numeral_Type
begin

subsection {* Finite Cartesian products, with indexing and lambdas. *}

typedef (open Cart)
  ('a, 'b) cart = "UNIV :: (('b::finite) \<Rightarrow> 'a) set"
  morphisms Cart_nth Cart_lambda ..

notation
  Cart_nth (infixl "$" 90) and
  Cart_lambda (binder "\<chi>" 10)

(*
  Translate "'b ^ 'n" into "'b ^ ('n :: finite)". When 'n has already more than
  the finite type class write "cart 'b 'n"
*)

syntax "_finite_cart" :: "type \<Rightarrow> type \<Rightarrow> type" ("(_ ^/ _)" [15, 16] 15)

parse_translation {*
let
  fun cart t u = Syntax.const @{type_syntax cart} $ t $ u;
  fun finite_cart_tr [t, u as Free (x, _)] =
        if Syntax.is_tid x then
          cart t (Syntax.const @{syntax_const "_ofsort"} $ u $ Syntax.const @{class_syntax finite})
        else cart t u
    | finite_cart_tr [t, u] = cart t u
in
  [(@{syntax_const "_finite_cart"}, finite_cart_tr)]
end
*}

lemma stupid_ext: "(\<forall>x. f x = g x) \<longleftrightarrow> (f = g)"
  by (auto intro: ext)

lemma Cart_eq: "(x = y) \<longleftrightarrow> (\<forall>i. x$i = y$i)"
  by (simp add: Cart_nth_inject [symmetric] expand_fun_eq)

lemma Cart_lambda_beta [simp]: "Cart_lambda g $ i = g i"
  by (simp add: Cart_lambda_inverse)

lemma Cart_lambda_unique: "(\<forall>i. f$i = g i) \<longleftrightarrow> Cart_lambda g = f"
  by (auto simp add: Cart_eq)

lemma Cart_lambda_eta: "(\<chi> i. (g$i)) = g"
  by (simp add: Cart_eq)


subsection {* Group operations and class instances *}

instantiation cart :: (zero,finite) zero
begin
  definition vector_zero_def : "0 \<equiv> (\<chi> i. 0)"
  instance ..
end

instantiation cart :: (plus,finite) plus
begin
  definition  vector_add_def : "op + \<equiv> (\<lambda> x y.  (\<chi> i. (x$i) + (y$i)))"
  instance ..
end

instantiation cart :: (minus,finite) minus
begin
  definition vector_minus_def : "op - \<equiv> (\<lambda> x y.  (\<chi> i. (x$i) - (y$i)))"
  instance ..
end

instantiation cart :: (uminus,finite) uminus
begin
  definition vector_uminus_def : "uminus \<equiv> (\<lambda> x.  (\<chi> i. - (x$i)))"
  instance ..
end

lemma zero_index [simp]: "0 $ i = 0"
  unfolding vector_zero_def by simp

lemma vector_add_component [simp]: "(x + y)$i = x$i + y$i"
  unfolding vector_add_def by simp

lemma vector_minus_component [simp]: "(x - y)$i = x$i - y$i"
  unfolding vector_minus_def by simp

lemma vector_uminus_component [simp]: "(- x)$i = - (x$i)"
  unfolding vector_uminus_def by simp

instance cart :: (semigroup_add, finite) semigroup_add
  by default (simp add: Cart_eq add_assoc)

instance cart :: (ab_semigroup_add, finite) ab_semigroup_add
  by default (simp add: Cart_eq add_commute)

instance cart :: (monoid_add, finite) monoid_add
  by default (simp_all add: Cart_eq)

instance cart :: (comm_monoid_add, finite) comm_monoid_add
  by default (simp add: Cart_eq)

instance cart :: (cancel_semigroup_add, finite) cancel_semigroup_add
  by default (simp_all add: Cart_eq)

instance cart :: (cancel_ab_semigroup_add, finite) cancel_ab_semigroup_add
  by default (simp add: Cart_eq)

instance cart :: (cancel_comm_monoid_add, finite) cancel_comm_monoid_add ..

instance cart :: (group_add, finite) group_add
  by default (simp_all add: Cart_eq diff_minus)

instance cart :: (ab_group_add, finite) ab_group_add
  by default (simp_all add: Cart_eq)


subsection {* Real vector space *}

instantiation cart :: (real_vector, finite) real_vector
begin

definition vector_scaleR_def: "scaleR = (\<lambda> r x. (\<chi> i. scaleR r (x$i)))"

lemma vector_scaleR_component [simp]: "(scaleR r x)$i = scaleR r (x$i)"
  unfolding vector_scaleR_def by simp

instance
  by default (simp_all add: Cart_eq scaleR_left_distrib scaleR_right_distrib)

end


subsection {* Topological space *}

instantiation cart :: (topological_space, finite) topological_space
begin

definition open_vector_def:
  "open (S :: ('a ^ 'b) set) \<longleftrightarrow>
    (\<forall>x\<in>S. \<exists>A. (\<forall>i. open (A i) \<and> x$i \<in> A i) \<and>
      (\<forall>y. (\<forall>i. y$i \<in> A i) \<longrightarrow> y \<in> S))"

instance proof
  show "open (UNIV :: ('a ^ 'b) set)"
    unfolding open_vector_def by auto
next
  fix S T :: "('a ^ 'b) set"
  assume "open S" "open T" thus "open (S \<inter> T)"
    unfolding open_vector_def
    apply clarify
    apply (drule (1) bspec)+
    apply (clarify, rename_tac Sa Ta)
    apply (rule_tac x="\<lambda>i. Sa i \<inter> Ta i" in exI)
    apply (simp add: open_Int)
    done
next
  fix K :: "('a ^ 'b) set set"
  assume "\<forall>S\<in>K. open S" thus "open (\<Union>K)"
    unfolding open_vector_def
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
unfolding open_vector_def by auto

lemma open_vimage_Cart_nth: "open S \<Longrightarrow> open ((\<lambda>x. x $ i) -` S)"
unfolding open_vector_def
apply clarify
apply (rule_tac x="\<lambda>k. if k = i then S else UNIV" in exI, simp)
done

lemma closed_vimage_Cart_nth: "closed S \<Longrightarrow> closed ((\<lambda>x. x $ i) -` S)"
unfolding closed_open vimage_Compl [symmetric]
by (rule open_vimage_Cart_nth)

lemma closed_vector_box: "\<forall>i. closed (S i) \<Longrightarrow> closed {x. \<forall>i. x $ i \<in> S i}"
proof -
  have "{x. \<forall>i. x $ i \<in> S i} = (\<Inter>i. (\<lambda>x. x $ i) -` S i)" by auto
  thus "\<forall>i. closed (S i) \<Longrightarrow> closed {x. \<forall>i. x $ i \<in> S i}"
    by (simp add: closed_INT closed_vimage_Cart_nth)
qed

lemma tendsto_Cart_nth [tendsto_intros]:
  assumes "((\<lambda>x. f x) ---> a) net"
  shows "((\<lambda>x. f x $ i) ---> a $ i) net"
proof (rule topological_tendstoI)
  fix S assume "open S" "a $ i \<in> S"
  then have "open ((\<lambda>y. y $ i) -` S)" "a \<in> ((\<lambda>y. y $ i) -` S)"
    by (simp_all add: open_vimage_Cart_nth)
  with assms have "eventually (\<lambda>x. f x \<in> (\<lambda>y. y $ i) -` S) net"
    by (rule topological_tendstoD)
  then show "eventually (\<lambda>x. f x $ i \<in> S) net"
    by simp
qed

lemma eventually_Ball_finite: (* TODO: move *)
  assumes "finite A" and "\<forall>y\<in>A. eventually (\<lambda>x. P x y) net"
  shows "eventually (\<lambda>x. \<forall>y\<in>A. P x y) net"
using assms by (induct set: finite, simp, simp add: eventually_conj)

lemma eventually_all_finite: (* TODO: move *)
  fixes P :: "'a \<Rightarrow> 'b::finite \<Rightarrow> bool"
  assumes "\<And>y. eventually (\<lambda>x. P x y) net"
  shows "eventually (\<lambda>x. \<forall>y. P x y) net"
using eventually_Ball_finite [of UNIV P] assms by simp

lemma tendsto_vector:
  assumes "\<And>i. ((\<lambda>x. f x $ i) ---> a $ i) net"
  shows "((\<lambda>x. f x) ---> a) net"
proof (rule topological_tendstoI)
  fix S assume "open S" and "a \<in> S"
  then obtain A where A: "\<And>i. open (A i)" "\<And>i. a $ i \<in> A i"
    and S: "\<And>y. \<forall>i. y $ i \<in> A i \<Longrightarrow> y \<in> S"
    unfolding open_vector_def by metis
  have "\<And>i. eventually (\<lambda>x. f x $ i \<in> A i) net"
    using assms A by (rule topological_tendstoD)
  hence "eventually (\<lambda>x. \<forall>i. f x $ i \<in> A i) net"
    by (rule eventually_all_finite)
  thus "eventually (\<lambda>x. f x \<in> S) net"
    by (rule eventually_elim1, simp add: S)
qed

lemma tendsto_Cart_lambda [tendsto_intros]:
  assumes "\<And>i. ((\<lambda>x. f x i) ---> a i) net"
  shows "((\<lambda>x. \<chi> i. f x i) ---> (\<chi> i. a i)) net"
using assms by (simp add: tendsto_vector)


subsection {* Metric *}

(* TODO: move somewhere else *)
lemma finite_choice: "finite A \<Longrightarrow> \<forall>x\<in>A. \<exists>y. P x y \<Longrightarrow> \<exists>f. \<forall>x\<in>A. P x (f x)"
apply (induct set: finite, simp_all)
apply (clarify, rename_tac y)
apply (rule_tac x="f(x:=y)" in exI, simp)
done

instantiation cart :: (metric_space, finite) metric_space
begin

definition dist_vector_def:
  "dist x y = setL2 (\<lambda>i. dist (x$i) (y$i)) UNIV"

lemma dist_nth_le_cart: "dist (x $ i) (y $ i) \<le> dist x y"
unfolding dist_vector_def
by (rule member_le_setL2) simp_all

instance proof
  fix x y :: "'a ^ 'b"
  show "dist x y = 0 \<longleftrightarrow> x = y"
    unfolding dist_vector_def
    by (simp add: setL2_eq_0_iff Cart_eq)
next
  fix x y z :: "'a ^ 'b"
  show "dist x y \<le> dist x z + dist y z"
    unfolding dist_vector_def
    apply (rule order_trans [OF _ setL2_triangle_ineq])
    apply (simp add: setL2_mono dist_triangle2)
    done
next
  (* FIXME: long proof! *)
  fix S :: "('a ^ 'b) set"
  show "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"
    unfolding open_vector_def open_dist
    apply safe
     apply (drule (1) bspec)
     apply clarify
     apply (subgoal_tac "\<exists>e>0. \<forall>i y. dist y (x$i) < e \<longrightarrow> y \<in> A i")
      apply clarify
      apply (rule_tac x=e in exI, clarify)
      apply (drule spec, erule mp, clarify)
      apply (drule spec, drule spec, erule mp)
      apply (erule le_less_trans [OF dist_nth_le_cart])
     apply (subgoal_tac "\<forall>i\<in>UNIV. \<exists>e>0. \<forall>y. dist y (x$i) < e \<longrightarrow> y \<in> A i")
      apply (drule finite_choice [OF finite], clarify)
      apply (rule_tac x="Min (range f)" in exI, simp)
     apply clarify
     apply (drule_tac x=i in spec, clarify)
     apply (erule (1) bspec)
    apply (drule (1) bspec, clarify)
    apply (subgoal_tac "\<exists>r. (\<forall>i::'b. 0 < r i) \<and> e = setL2 r UNIV")
     apply clarify
     apply (rule_tac x="\<lambda>i. {y. dist y (x$i) < r i}" in exI)
     apply (rule conjI)
      apply clarify
      apply (rule conjI)
       apply (clarify, rename_tac y)
       apply (rule_tac x="r i - dist y (x$i)" in exI, rule conjI, simp)
       apply clarify
       apply (simp only: less_diff_eq)
       apply (erule le_less_trans [OF dist_triangle])
      apply simp
     apply clarify
     apply (drule spec, erule mp)
     apply (simp add: dist_vector_def setL2_strict_mono)
    apply (rule_tac x="\<lambda>i. e / sqrt (of_nat CARD('b))" in exI)
    apply (simp add: divide_pos_pos setL2_constant)
    done
qed

end

lemma Cauchy_Cart_nth:
  "Cauchy (\<lambda>n. X n) \<Longrightarrow> Cauchy (\<lambda>n. X n $ i)"
unfolding Cauchy_def by (fast intro: le_less_trans [OF dist_nth_le_cart])

lemma Cauchy_vector:
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
      unfolding dist_vector_def ..
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

instance cart :: (complete_space, finite) complete_space
proof
  fix X :: "nat \<Rightarrow> 'a ^ 'b" assume "Cauchy X"
  have "\<And>i. (\<lambda>n. X n $ i) ----> lim (\<lambda>n. X n $ i)"
    using Cauchy_Cart_nth [OF `Cauchy X`]
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  hence "X ----> Cart_lambda (\<lambda>i. lim (\<lambda>n. X n $ i))"
    by (simp add: tendsto_vector)
  then show "convergent X"
    by (rule convergentI)
qed


subsection {* Normed vector space *}

instantiation cart :: (real_normed_vector, finite) real_normed_vector
begin

definition norm_vector_def:
  "norm x = setL2 (\<lambda>i. norm (x$i)) UNIV"

definition vector_sgn_def:
  "sgn (x::'a^'b) = scaleR (inverse (norm x)) x"

instance proof
  fix a :: real and x y :: "'a ^ 'b"
  show "0 \<le> norm x"
    unfolding norm_vector_def
    by (rule setL2_nonneg)
  show "norm x = 0 \<longleftrightarrow> x = 0"
    unfolding norm_vector_def
    by (simp add: setL2_eq_0_iff Cart_eq)
  show "norm (x + y) \<le> norm x + norm y"
    unfolding norm_vector_def
    apply (rule order_trans [OF _ setL2_triangle_ineq])
    apply (simp add: setL2_mono norm_triangle_ineq)
    done
  show "norm (scaleR a x) = \<bar>a\<bar> * norm x"
    unfolding norm_vector_def
    by (simp add: setL2_right_distrib)
  show "sgn x = scaleR (inverse (norm x)) x"
    by (rule vector_sgn_def)
  show "dist x y = norm (x - y)"
    unfolding dist_vector_def norm_vector_def
    by (simp add: dist_norm)
qed

end

lemma norm_nth_le: "norm (x $ i) \<le> norm x"
unfolding norm_vector_def
by (rule member_le_setL2) simp_all

interpretation Cart_nth: bounded_linear "\<lambda>x. x $ i"
apply default
apply (rule vector_add_component)
apply (rule vector_scaleR_component)
apply (rule_tac x="1" in exI, simp add: norm_nth_le)
done

instance cart :: (banach, finite) banach ..


subsection {* Inner product space *}

instantiation cart :: (real_inner, finite) real_inner
begin

definition inner_vector_def:
  "inner x y = setsum (\<lambda>i. inner (x$i) (y$i)) UNIV"

instance proof
  fix r :: real and x y z :: "'a ^ 'b"
  show "inner x y = inner y x"
    unfolding inner_vector_def
    by (simp add: inner_commute)
  show "inner (x + y) z = inner x z + inner y z"
    unfolding inner_vector_def
    by (simp add: inner_add_left setsum_addf)
  show "inner (scaleR r x) y = r * inner x y"
    unfolding inner_vector_def
    by (simp add: setsum_right_distrib)
  show "0 \<le> inner x x"
    unfolding inner_vector_def
    by (simp add: setsum_nonneg)
  show "inner x x = 0 \<longleftrightarrow> x = 0"
    unfolding inner_vector_def
    by (simp add: Cart_eq setsum_nonneg_eq_0_iff)
  show "norm x = sqrt (inner x x)"
    unfolding inner_vector_def norm_vector_def setL2_def
    by (simp add: power2_norm_eq_inner)
qed

end

end
