(*  Title:      HOL/Analysis/Finite_Cartesian_Product.thy
    Author:     Amine Chaieb, University of Cambridge
*)

section \<open>Definition of finite Cartesian product types.\<close>

theory Finite_Cartesian_Product
imports
  Euclidean_Space
  L2_Norm
  "HOL-Library.Numeral_Type"
  "HOL-Library.Countable_Set"
  "HOL-Library.FuncSet"
begin

subsection \<open>Finite Cartesian products, with indexing and lambdas.\<close>

typedef ('a, 'b) vec = "UNIV :: ('b::finite \<Rightarrow> 'a) set"
  morphisms vec_nth vec_lambda ..

declare vec_lambda_inject [simplified, simp]

bundle vec_syntax begin
notation
  vec_nth (infixl "$" 90) and
  vec_lambda (binder "\<chi>" 10)
end

bundle no_vec_syntax begin
no_notation
  vec_nth (infixl "$" 90) and
  vec_lambda (binder "\<chi>" 10)
end

unbundle vec_syntax

text \<open>
  Concrete syntax for \<open>('a, 'b) vec\<close>:
    \<^item> \<open>'a^'b\<close> becomes \<open>('a, 'b::finite) vec\<close>
    \<^item> \<open>'a^'b::_\<close> becomes \<open>('a, 'b) vec\<close> without extra sort-constraint
\<close>
syntax "_vec_type" :: "type \<Rightarrow> type \<Rightarrow> type" (infixl "^" 15)
parse_translation \<open>
  let
    fun vec t u = Syntax.const @{type_syntax vec} $ t $ u;
    fun finite_vec_tr [t, u] =
      (case Term_Position.strip_positions u of
        v as Free (x, _) =>
          if Lexicon.is_tid x then
            vec t (Syntax.const @{syntax_const "_ofsort"} $ v $
              Syntax.const @{class_syntax finite})
          else vec t u
      | _ => vec t u)
  in
    [(@{syntax_const "_vec_type"}, K finite_vec_tr)]
  end
\<close>

lemma vec_eq_iff: "(x = y) \<longleftrightarrow> (\<forall>i. x$i = y$i)"
  by (simp add: vec_nth_inject [symmetric] fun_eq_iff)

lemma vec_lambda_beta [simp]: "vec_lambda g $ i = g i"
  by (simp add: vec_lambda_inverse)

lemma vec_lambda_unique: "(\<forall>i. f$i = g i) \<longleftrightarrow> vec_lambda g = f"
  by (auto simp add: vec_eq_iff)

lemma vec_lambda_eta [simp]: "(\<chi> i. (g$i)) = g"
  by (simp add: vec_eq_iff)

subsection \<open>Cardinality of vectors\<close>

instance vec :: (finite, finite) finite
proof
  show "finite (UNIV :: ('a, 'b) vec set)"
  proof (subst bij_betw_finite)
    show "bij_betw vec_nth UNIV (Pi (UNIV :: 'b set) (\<lambda>_. UNIV :: 'a set))"
      by (intro bij_betwI[of _ _ _ vec_lambda]) (auto simp: vec_eq_iff)
    have "finite (PiE (UNIV :: 'b set) (\<lambda>_. UNIV :: 'a set))"
      by (intro finite_PiE) auto
    also have "(PiE (UNIV :: 'b set) (\<lambda>_. UNIV :: 'a set)) = Pi UNIV (\<lambda>_. UNIV)"
      by auto
    finally show "finite \<dots>" .
  qed
qed

lemma countable_PiE:
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> countable (F i)) \<Longrightarrow> countable (Pi\<^sub>E I F)"
  by (induct I arbitrary: F rule: finite_induct) (auto simp: PiE_insert_eq)

instance vec :: (countable, finite) countable
proof
  have "countable (UNIV :: ('a, 'b) vec set)"
  proof (rule countableI_bij2)
    show "bij_betw vec_nth UNIV (Pi (UNIV :: 'b set) (\<lambda>_. UNIV :: 'a set))"
      by (intro bij_betwI[of _ _ _ vec_lambda]) (auto simp: vec_eq_iff)
    have "countable (PiE (UNIV :: 'b set) (\<lambda>_. UNIV :: 'a set))"
      by (intro countable_PiE) auto
    also have "(PiE (UNIV :: 'b set) (\<lambda>_. UNIV :: 'a set)) = Pi UNIV (\<lambda>_. UNIV)"
      by auto
    finally show "countable \<dots>" .
  qed
  thus "\<exists>t::('a, 'b) vec \<Rightarrow> nat. inj t"
    by (auto elim!: countableE)
qed

lemma infinite_UNIV_vec:
  assumes "infinite (UNIV :: 'a set)"
  shows   "infinite (UNIV :: ('a^'b) set)"
proof (subst bij_betw_finite)
  show "bij_betw vec_nth UNIV (Pi (UNIV :: 'b set) (\<lambda>_. UNIV :: 'a set))"
    by (intro bij_betwI[of _ _ _ vec_lambda]) (auto simp: vec_eq_iff)
  have "infinite (PiE (UNIV :: 'b set) (\<lambda>_. UNIV :: 'a set))" (is "infinite ?A")
  proof
    assume "finite ?A"
    hence "finite ((\<lambda>f. f undefined) ` ?A)"
      by (rule finite_imageI)
    also have "(\<lambda>f. f undefined) ` ?A = UNIV"
      by auto
    finally show False 
      using \<open>infinite (UNIV :: 'a set)\<close> by contradiction
  qed
  also have "?A = Pi UNIV (\<lambda>_. UNIV)" 
    by auto
  finally show "infinite (Pi (UNIV :: 'b set) (\<lambda>_. UNIV :: 'a set))" .
qed

lemma CARD_vec [simp]:
  "CARD('a^'b) = CARD('a) ^ CARD('b)"
proof (cases "finite (UNIV :: 'a set)")
  case True
  show ?thesis
  proof (subst bij_betw_same_card)
    show "bij_betw vec_nth UNIV (Pi (UNIV :: 'b set) (\<lambda>_. UNIV :: 'a set))"
      by (intro bij_betwI[of _ _ _ vec_lambda]) (auto simp: vec_eq_iff)
    have "CARD('a) ^ CARD('b) = card (PiE (UNIV :: 'b set) (\<lambda>_. UNIV :: 'a set))"
      (is "_ = card ?A")
      by (subst card_PiE) (auto simp: prod_constant)
    
    also have "?A = Pi UNIV (\<lambda>_. UNIV)" 
      by auto
    finally show "card \<dots> = CARD('a) ^ CARD('b)" ..
  qed
qed (simp_all add: infinite_UNIV_vec)

lemma countable_vector:
  fixes B:: "'n::finite \<Rightarrow> 'a set"
  assumes "\<And>i. countable (B i)"
  shows "countable {V. \<forall>i::'n::finite. V $ i \<in> B i}"
proof -
  have "f \<in> ($) ` {V. \<forall>i. V $ i \<in> B i}" if "f \<in> Pi\<^sub>E UNIV B" for f
  proof -
    have "\<exists>W. (\<forall>i. W $ i \<in> B i) \<and> ($) W = f"
      by (metis that PiE_iff UNIV_I vec_lambda_inverse)
    then show "f \<in> ($) ` {v. \<forall>i. v $ i \<in> B i}"
      by blast
  qed
  then have "Pi\<^sub>E UNIV B = vec_nth ` {V. \<forall>i::'n. V $ i \<in> B i}"
    by blast
  then have "countable (vec_nth ` {V. \<forall>i. V $ i \<in> B i})"
    by (metis finite_class.finite_UNIV countable_PiE assms)
  then have "countable (vec_lambda ` vec_nth ` {V. \<forall>i. V $ i \<in> B i})"
    by auto
  then show ?thesis
    by (simp add: image_comp o_def vec_nth_inverse)
qed

subsection \<open>Group operations and class instances\<close>

instantiation vec :: (zero, finite) zero
begin
  definition "0 \<equiv> (\<chi> i. 0)"
  instance ..
end

instantiation vec :: (plus, finite) plus
begin
  definition "(+) \<equiv> (\<lambda> x y. (\<chi> i. x$i + y$i))"
  instance ..
end

instantiation vec :: (minus, finite) minus
begin
  definition "(-) \<equiv> (\<lambda> x y. (\<chi> i. x$i - y$i))"
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
  by standard (simp add: vec_eq_iff add.assoc)

instance vec :: (ab_semigroup_add, finite) ab_semigroup_add
  by standard (simp add: vec_eq_iff add.commute)

instance vec :: (monoid_add, finite) monoid_add
  by standard (simp_all add: vec_eq_iff)

instance vec :: (comm_monoid_add, finite) comm_monoid_add
  by standard (simp add: vec_eq_iff)

instance vec :: (cancel_semigroup_add, finite) cancel_semigroup_add
  by standard (simp_all add: vec_eq_iff)

instance vec :: (cancel_ab_semigroup_add, finite) cancel_ab_semigroup_add
  by standard (simp_all add: vec_eq_iff diff_diff_eq)

instance vec :: (cancel_comm_monoid_add, finite) cancel_comm_monoid_add ..

instance vec :: (group_add, finite) group_add
  by standard (simp_all add: vec_eq_iff)

instance vec :: (ab_group_add, finite) ab_group_add
  by standard (simp_all add: vec_eq_iff)


subsection \<open>Real vector space\<close>

instantiation vec :: (real_vector, finite) real_vector
begin

definition "scaleR \<equiv> (\<lambda> r x. (\<chi> i. scaleR r (x$i)))"

lemma vector_scaleR_component [simp]: "(scaleR r x)$i = scaleR r (x$i)"
  unfolding scaleR_vec_def by simp

instance
  by standard (simp_all add: vec_eq_iff scaleR_left_distrib scaleR_right_distrib)

end


subsection \<open>Topological space\<close>

instantiation vec :: (topological_space, finite) topological_space
begin

definition [code del]:
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
  assumes "((\<lambda>x. f x) \<longlongrightarrow> a) net"
  shows "((\<lambda>x. f x $ i) \<longlongrightarrow> a $ i) net"
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

lemma vec_tendstoI:
  assumes "\<And>i. ((\<lambda>x. f x $ i) \<longlongrightarrow> a $ i) net"
  shows "((\<lambda>x. f x) \<longlongrightarrow> a) net"
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
    by (rule eventually_mono, simp add: S)
qed

lemma tendsto_vec_lambda [tendsto_intros]:
  assumes "\<And>i. ((\<lambda>x. f x i) \<longlongrightarrow> a i) net"
  shows "((\<lambda>x. \<chi> i. f x i) \<longlongrightarrow> (\<chi> i. a i)) net"
  using assms by (simp add: vec_tendstoI)

lemma open_image_vec_nth: assumes "open S" shows "open ((\<lambda>x. x $ i) ` S)"
proof (rule openI)
  fix a assume "a \<in> (\<lambda>x. x $ i) ` S"
  then obtain z where "a = z $ i" and "z \<in> S" ..
  then obtain A where A: "\<forall>i. open (A i) \<and> z $ i \<in> A i"
    and S: "\<forall>y. (\<forall>i. y $ i \<in> A i) \<longrightarrow> y \<in> S"
    using \<open>open S\<close> unfolding open_vec_def by auto
  hence "A i \<subseteq> (\<lambda>x. x $ i) ` S"
    by (clarsimp, rule_tac x="\<chi> j. if j = i then x else z $ j" in image_eqI,
      simp_all)
  hence "open (A i) \<and> a \<in> A i \<and> A i \<subseteq> (\<lambda>x. x $ i) ` S"
    using A \<open>a = z $ i\<close> by simp
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


subsection \<open>Metric space\<close>
(* TODO: Product of uniform spaces and compatibility with metric_spaces! *)

instantiation vec :: (metric_space, finite) dist
begin

definition
  "dist x y = L2_set (\<lambda>i. dist (x$i) (y$i)) UNIV"

instance ..
end

instantiation vec :: (metric_space, finite) uniformity_dist
begin

definition [code del]:
  "(uniformity :: (('a^'b::_) \<times> ('a^'b::_)) filter) =
    (INF e:{0 <..}. principal {(x, y). dist x y < e})"

instance
  by standard (rule uniformity_vec_def)
end

declare uniformity_Abort[where 'a="'a :: metric_space ^ 'b :: finite", code]

instantiation vec :: (metric_space, finite) metric_space
begin

lemma dist_vec_nth_le: "dist (x $ i) (y $ i) \<le> dist x y"
  unfolding dist_vec_def by (rule member_le_L2_set) simp_all

instance proof
  fix x y :: "'a ^ 'b"
  show "dist x y = 0 \<longleftrightarrow> x = y"
    unfolding dist_vec_def
    by (simp add: L2_set_eq_0_iff vec_eq_iff)
next
  fix x y z :: "'a ^ 'b"
  show "dist x y \<le> dist x z + dist y z"
    unfolding dist_vec_def
    apply (rule order_trans [OF _ L2_set_triangle_ineq])
    apply (simp add: L2_set_mono dist_triangle2)
    done
next
  fix S :: "('a ^ 'b) set"
  have *: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"
  proof
    assume "open S" show "\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S"
    proof
      fix x assume "x \<in> S"
      obtain A where A: "\<forall>i. open (A i)" "\<forall>i. x $ i \<in> A i"
        and S: "\<forall>y. (\<forall>i. y $ i \<in> A i) \<longrightarrow> y \<in> S"
        using \<open>open S\<close> and \<open>x \<in> S\<close> unfolding open_vec_def by metis
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
      define r where [abs_def]: "r i = e / sqrt (of_nat CARD('b))" for i :: 'b
      from \<open>0 < e\<close> have r: "\<forall>i. 0 < r i"
        unfolding r_def by simp_all
      from \<open>0 < e\<close> have e: "e = L2_set r UNIV"
        unfolding r_def by (simp add: L2_set_constant)
      define A where "A i = {y. dist (x $ i) y < r i}" for i
      have "\<forall>i. open (A i) \<and> x $ i \<in> A i"
        unfolding A_def by (simp add: open_ball r)
      moreover have "\<forall>y. (\<forall>i. y $ i \<in> A i) \<longrightarrow> y \<in> S"
        by (simp add: A_def S dist_vec_def e L2_set_strict_mono dist_commute)
      ultimately show "\<exists>A. (\<forall>i. open (A i) \<and> x $ i \<in> A i) \<and>
        (\<forall>y. (\<forall>i. y $ i \<in> A i) \<longrightarrow> y \<in> S)" by metis
    qed
  qed
  show "open S = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"
    unfolding * eventually_uniformity_metric
    by (simp del: split_paired_All add: dist_vec_def dist_commute)
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
  hence "0 < r / of_nat CARD('n)" (is "0 < ?s") by simp
  define N where "N i = (LEAST N. \<forall>m\<ge>N. \<forall>n\<ge>N. dist (X m $ i) (X n $ i) < ?s)" for i
  define M where "M = Max (range N)"
  have "\<And>i. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. dist (X m $ i) (X n $ i) < ?s"
    using X \<open>0 < ?s\<close> by (rule metric_CauchyD)
  hence "\<And>i. \<forall>m\<ge>N i. \<forall>n\<ge>N i. dist (X m $ i) (X n $ i) < ?s"
    unfolding N_def by (rule LeastI_ex)
  hence M: "\<And>i. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m $ i) (X n $ i) < ?s"
    unfolding M_def by simp
  {
    fix m n :: nat
    assume "M \<le> m" "M \<le> n"
    have "dist (X m) (X n) = L2_set (\<lambda>i. dist (X m $ i) (X n $ i)) UNIV"
      unfolding dist_vec_def ..
    also have "\<dots> \<le> sum (\<lambda>i. dist (X m $ i) (X n $ i)) UNIV"
      by (rule L2_set_le_sum [OF zero_le_dist])
    also have "\<dots> < sum (\<lambda>i::'n. ?s) UNIV"
      by (rule sum_strict_mono, simp_all add: M \<open>M \<le> m\<close> \<open>M \<le> n\<close>)
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
  have "\<And>i. (\<lambda>n. X n $ i) \<longlonglongrightarrow> lim (\<lambda>n. X n $ i)"
    using Cauchy_vec_nth [OF \<open>Cauchy X\<close>]
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff)
  hence "X \<longlonglongrightarrow> vec_lambda (\<lambda>i. lim (\<lambda>n. X n $ i))"
    by (simp add: vec_tendstoI)
  then show "convergent X"
    by (rule convergentI)
qed


subsection \<open>Normed vector space\<close>

instantiation vec :: (real_normed_vector, finite) real_normed_vector
begin

definition "norm x = L2_set (\<lambda>i. norm (x$i)) UNIV"

definition "sgn (x::'a^'b) = scaleR (inverse (norm x)) x"

instance proof
  fix a :: real and x y :: "'a ^ 'b"
  show "norm x = 0 \<longleftrightarrow> x = 0"
    unfolding norm_vec_def
    by (simp add: L2_set_eq_0_iff vec_eq_iff)
  show "norm (x + y) \<le> norm x + norm y"
    unfolding norm_vec_def
    apply (rule order_trans [OF _ L2_set_triangle_ineq])
    apply (simp add: L2_set_mono norm_triangle_ineq)
    done
  show "norm (scaleR a x) = \<bar>a\<bar> * norm x"
    unfolding norm_vec_def
    by (simp add: L2_set_right_distrib)
  show "sgn x = scaleR (inverse (norm x)) x"
    by (rule sgn_vec_def)
  show "dist x y = norm (x - y)"
    unfolding dist_vec_def norm_vec_def
    by (simp add: dist_norm)
qed

end

lemma norm_nth_le: "norm (x $ i) \<le> norm x"
unfolding norm_vec_def
by (rule member_le_L2_set) simp_all

lemma bounded_linear_vec_nth: "bounded_linear (\<lambda>x. x $ i)"
apply standard
apply (rule vector_add_component)
apply (rule vector_scaleR_component)
apply (rule_tac x="1" in exI, simp add: norm_nth_le)
done

instance vec :: (banach, finite) banach ..


subsection \<open>Inner product space\<close>

instantiation vec :: (real_inner, finite) real_inner
begin

definition "inner x y = sum (\<lambda>i. inner (x$i) (y$i)) UNIV"

instance proof
  fix r :: real and x y z :: "'a ^ 'b"
  show "inner x y = inner y x"
    unfolding inner_vec_def
    by (simp add: inner_commute)
  show "inner (x + y) z = inner x z + inner y z"
    unfolding inner_vec_def
    by (simp add: inner_add_left sum.distrib)
  show "inner (scaleR r x) y = r * inner x y"
    unfolding inner_vec_def
    by (simp add: sum_distrib_left)
  show "0 \<le> inner x x"
    unfolding inner_vec_def
    by (simp add: sum_nonneg)
  show "inner x x = 0 \<longleftrightarrow> x = 0"
    unfolding inner_vec_def
    by (simp add: vec_eq_iff sum_nonneg_eq_0_iff)
  show "norm x = sqrt (inner x x)"
    unfolding inner_vec_def norm_vec_def L2_set_def
    by (simp add: power2_norm_eq_inner)
qed

end


subsection \<open>Euclidean space\<close>

text \<open>Vectors pointing along a single axis.\<close>

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
  apply (subst sum.remove [of _ j], simp_all)
  apply (rule sum.neutral, simp add: axis_def)
  apply (rule sum.neutral, simp add: axis_def)
  done

lemma sum_single:
  assumes "finite A" and "k \<in> A" and "f k = y"
  assumes "\<And>i. i \<in> A \<Longrightarrow> i \<noteq> k \<Longrightarrow> f i = 0"
  shows "(\<Sum>i\<in>A. f i) = y"
  apply (subst sum.remove [OF assms(1,2)])
  apply (simp add: sum.neutral assms(3,4))
  done

lemma inner_axis: "inner x (axis i y) = inner (x $ i) y"
  unfolding inner_vec_def
  apply (rule_tac k=i in sum_single)
  apply simp_all
  apply (simp add: axis_def)
  done

lemma inner_axis': "inner(axis i y) x = inner y (x $ i)"
  by (simp add: inner_axis inner_commute)

instantiation vec :: (euclidean_space, finite) euclidean_space
begin

definition "Basis = (\<Union>i. \<Union>u\<in>Basis. {axis i u})"

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
qed

lemma DIM_cart[simp]: "DIM('a^'b) = CARD('b) * DIM('a)"
  apply (simp add: Basis_vec_def)
  apply (subst card_UN_disjoint)
     apply simp
    apply simp
   apply (auto simp: axis_eq_axis) [1]
  apply (subst card_UN_disjoint)
     apply (auto simp: axis_eq_axis)
  done

end

lemma cart_eq_inner_axis: "a $ i = inner a (axis i 1)"
  by (simp add: inner_axis)

lemma axis_in_Basis: "a \<in> Basis \<Longrightarrow> axis i a \<in> Basis"
  by (auto simp add: Basis_vec_def axis_eq_axis)

end
