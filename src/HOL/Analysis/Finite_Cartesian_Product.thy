(*  Title:      HOL/Analysis/Finite_Cartesian_Product.thy
    Author:     Amine Chaieb, University of Cambridge
*)

section \<open>Definition of Finite Cartesian Product Type\<close>

theory Finite_Cartesian_Product
imports
  Euclidean_Space
  L2_Norm
  "HOL-Library.Numeral_Type"
  "HOL-Library.Countable_Set"
  "HOL-Library.FuncSet"
begin

subsection\<^marker>\<open>tag unimportant\<close> \<open>Finite Cartesian products, with indexing and lambdas\<close>

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
    fun vec t u = Syntax.const \<^type_syntax>\<open>vec\<close> $ t $ u;
    fun finite_vec_tr [t, u] =
      (case Term_Position.strip_positions u of
        v as Free (x, _) =>
          if Lexicon.is_tid x then
            vec t (Syntax.const \<^syntax_const>\<open>_ofsort\<close> $ v $
              Syntax.const \<^class_syntax>\<open>finite\<close>)
          else vec t u
      | _ => vec t u)
  in
    [(\<^syntax_const>\<open>_vec_type\<close>, K finite_vec_tr)]
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

proposition CARD_vec [simp]:
  "CARD('a^'b) = CARD('a) ^ CARD('b)"
proof (cases "finite (UNIV :: 'a set)")
  case True
  show ?thesis
  proof (subst bij_betw_same_card)
    show "bij_betw vec_nth UNIV (Pi (UNIV :: 'b set) (\<lambda>_. UNIV :: 'a set))"
      by (intro bij_betwI[of _ _ _ vec_lambda]) (auto simp: vec_eq_iff)
    have "CARD('a) ^ CARD('b) = card (PiE (UNIV :: 'b set) (\<lambda>_. UNIV :: 'a set))"
      (is "_ = card ?A")
      by (subst card_PiE) (auto)
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

subsection\<^marker>\<open>tag unimportant\<close> \<open>Group operations and class instances\<close>

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


subsection\<^marker>\<open>tag unimportant\<close>\<open>Basic componentwise operations on vectors\<close>

instantiation vec :: (times, finite) times
begin

definition "(*) \<equiv> (\<lambda> x y.  (\<chi> i. (x$i) * (y$i)))"
instance ..

end

instantiation vec :: (one, finite) one
begin

definition "1 \<equiv> (\<chi> i. 1)"
instance ..

end

instantiation vec :: (ord, finite) ord
begin

definition "x \<le> y \<longleftrightarrow> (\<forall>i. x$i \<le> y$i)"
definition "x < (y::'a^'b) \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
instance ..

end

text\<open>The ordering on one-dimensional vectors is linear.\<close>

instance vec:: (order, finite) order
  by standard (auto simp: less_eq_vec_def less_vec_def vec_eq_iff
      intro: order.trans order.antisym order.strict_implies_order)

instance vec :: (linorder, CARD_1) linorder
proof
  obtain a :: 'b where all: "\<And>P. (\<forall>i. P i) \<longleftrightarrow> P a"
  proof -
    have "CARD ('b) = 1" by (rule CARD_1)
    then obtain b :: 'b where "UNIV = {b}" by (auto iff: card_Suc_eq)
    then have "\<And>P. (\<forall>i\<in>UNIV. P i) \<longleftrightarrow> P b" by auto
    then show thesis by (auto intro: that)
  qed
  fix x y :: "'a^'b::CARD_1"
  note [simp] = less_eq_vec_def less_vec_def all vec_eq_iff field_simps
  show "x \<le> y \<or> y \<le> x" by auto
qed

text\<open>Constant Vectors\<close>

definition "vec x = (\<chi> i. x)"

text\<open>Also the scalar-vector multiplication.\<close>

definition vector_scalar_mult:: "'a::times \<Rightarrow> 'a ^ 'n \<Rightarrow> 'a ^ 'n" (infixl "*s" 70)
  where "c *s x = (\<chi> i. c * (x$i))"

text \<open>scalar product\<close>

definition scalar_product :: "'a :: semiring_1 ^ 'n \<Rightarrow> 'a ^ 'n \<Rightarrow> 'a" where
  "scalar_product v w = (\<Sum> i \<in> UNIV. v $ i * w $ i)"


subsection \<open>Real vector space\<close>

instantiation\<^marker>\<open>tag unimportant\<close> vec :: (real_vector, finite) real_vector
begin

definition\<^marker>\<open>tag important\<close> "scaleR \<equiv> (\<lambda> r x. (\<chi> i. scaleR r (x$i)))"

lemma vector_scaleR_component [simp]: "(scaleR r x)$i = scaleR r (x$i)"
  unfolding scaleR_vec_def by simp

instance\<^marker>\<open>tag unimportant\<close>
  by standard (simp_all add: vec_eq_iff scaleR_left_distrib scaleR_right_distrib)

end


subsection \<open>Topological space\<close>

instantiation\<^marker>\<open>tag unimportant\<close> vec :: (topological_space, finite) topological_space
begin

definition\<^marker>\<open>tag important\<close> [code del]:
  "open (S :: ('a ^ 'b) set) \<longleftrightarrow>
    (\<forall>x\<in>S. \<exists>A. (\<forall>i. open (A i) \<and> x$i \<in> A i) \<and>
      (\<forall>y. (\<forall>i. y$i \<in> A i) \<longrightarrow> y \<in> S))"

instance\<^marker>\<open>tag unimportant\<close> proof
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
    by (metis Union_iff)
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

instance\<^marker>\<open>tag unimportant\<close> vec :: (perfect_space, finite) perfect_space
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

instantiation\<^marker>\<open>tag unimportant\<close> vec :: (metric_space, finite) dist
begin

definition\<^marker>\<open>tag important\<close>
  "dist x y = L2_set (\<lambda>i. dist (x$i) (y$i)) UNIV"

instance ..
end

instantiation\<^marker>\<open>tag unimportant\<close> vec :: (metric_space, finite) uniformity_dist
begin

definition\<^marker>\<open>tag important\<close> [code del]:
  "(uniformity :: (('a^'b::_) \<times> ('a^'b::_)) filter) =
    (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

instance\<^marker>\<open>tag unimportant\<close>
  by standard (rule uniformity_vec_def)
end

declare uniformity_Abort[where 'a="'a :: metric_space ^ 'b :: finite", code]

instantiation\<^marker>\<open>tag unimportant\<close> vec :: (metric_space, finite) metric_space
begin

proposition dist_vec_nth_le: "dist (x $ i) (y $ i) \<le> dist x y"
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

instance\<^marker>\<open>tag unimportant\<close> vec :: (complete_space, finite) complete_space
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

instantiation\<^marker>\<open>tag unimportant\<close> vec :: (real_normed_vector, finite) real_normed_vector
begin

definition\<^marker>\<open>tag important\<close> "norm x = L2_set (\<lambda>i. norm (x$i)) UNIV"

definition\<^marker>\<open>tag important\<close> "sgn (x::'a^'b) = scaleR (inverse (norm x)) x"

instance\<^marker>\<open>tag unimportant\<close> proof
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

lemma norm_le_componentwise_cart:
  fixes x :: "'a::real_normed_vector^'n"
  assumes "\<And>i. norm(x$i) \<le> norm(y$i)"
  shows "norm x \<le> norm y"
  unfolding norm_vec_def
  by (rule L2_set_mono) (auto simp: assms)

lemma component_le_norm_cart: "\<bar>x$i\<bar> \<le> norm x"
  by (metis norm_nth_le real_norm_def)

lemma norm_bound_component_le_cart: "norm x \<le> e ==> \<bar>x$i\<bar> \<le> e"
  by (metis component_le_norm_cart order_trans)

lemma norm_bound_component_lt_cart: "norm x < e ==> \<bar>x$i\<bar> < e"
  by (metis component_le_norm_cart le_less_trans)

lemma norm_le_l1_cart: "norm x \<le> sum(\<lambda>i. \<bar>x$i\<bar>) UNIV"
  by (simp add: norm_vec_def L2_set_le_sum)

lemma bounded_linear_vec_nth[intro]: "bounded_linear (\<lambda>x. x $ i)"
proof
  show "\<exists>K. \<forall>x. norm (x $ i) \<le> norm x * K"
    by (metis mult.commute mult.left_neutral norm_nth_le)
qed auto

instance vec :: (banach, finite) banach ..


subsection \<open>Inner product space\<close>

instantiation\<^marker>\<open>tag unimportant\<close> vec :: (real_inner, finite) real_inner
begin

definition\<^marker>\<open>tag important\<close> "inner x y = sum (\<lambda>i. inner (x$i) (y$i)) UNIV"

instance\<^marker>\<open>tag unimportant\<close> proof
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

definition\<^marker>\<open>tag important\<close> "axis k x = (\<chi> i. if i = k then x else 0)"

lemma axis_nth [simp]: "axis i x $ i = x"
  unfolding axis_def by simp

lemma axis_eq_axis: "axis i x = axis j y \<longleftrightarrow> x = y \<and> i = j \<or> x = 0 \<and> y = 0"
  unfolding axis_def vec_eq_iff by auto

lemma inner_axis_axis:
  "inner (axis i x) (axis j y) = (if i = j then inner x y else 0)"
  by (simp add: inner_vec_def axis_def sum.neutral sum.remove [of _ j])

lemma inner_axis: "inner x (axis i y) = inner (x $ i) y"
  by (simp add: inner_vec_def axis_def sum.remove [where x=i])

lemma inner_axis': "inner(axis i y) x = inner y (x $ i)"
  by (simp add: inner_axis inner_commute)

instantiation\<^marker>\<open>tag unimportant\<close> vec :: (euclidean_space, finite) euclidean_space
begin

definition\<^marker>\<open>tag important\<close> "Basis = (\<Union>i. \<Union>u\<in>Basis. {axis i u})"

instance\<^marker>\<open>tag unimportant\<close> proof
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

proposition DIM_cart [simp]: "DIM('a^'b) = CARD('b) * DIM('a)"
proof -
  have "card (\<Union>i::'b. \<Union>u::'a\<in>Basis. {axis i u}) = (\<Sum>i::'b\<in>UNIV. card (\<Union>u::'a\<in>Basis. {axis i u}))"
    by (rule card_UN_disjoint) (auto simp: axis_eq_axis) 
  also have "... = CARD('b) * DIM('a)"
    by (subst card_UN_disjoint) (auto simp: axis_eq_axis)
  finally show ?thesis
    by (simp add: Basis_vec_def)
qed

end

lemma norm_axis_1 [simp]: "norm (axis m (1::real)) = 1"
  by (simp add: inner_axis' norm_eq_1)

lemma sum_norm_allsubsets_bound_cart:
  fixes f:: "'a \<Rightarrow> real ^'n"
  assumes fP: "finite P" and fPs: "\<And>Q. Q \<subseteq> P \<Longrightarrow> norm (sum f Q) \<le> e"
  shows "sum (\<lambda>x. norm (f x)) P \<le> 2 * real CARD('n) *  e"
  using sum_norm_allsubsets_bound[OF assms]
  by simp

lemma cart_eq_inner_axis: "a $ i = inner a (axis i 1)"
  by (simp add: inner_axis)

lemma axis_eq_0_iff [simp]:
  shows "axis m x = 0 \<longleftrightarrow> x = 0"
  by (simp add: axis_def vec_eq_iff)

lemma axis_in_Basis_iff [simp]: "axis i a \<in> Basis \<longleftrightarrow> a \<in> Basis"
  by (auto simp: Basis_vec_def axis_eq_axis)

text\<open>Mapping each basis element to the corresponding finite index\<close>
definition axis_index :: "('a::comm_ring_1)^'n \<Rightarrow> 'n" where "axis_index v \<equiv> SOME i. v = axis i 1"

lemma axis_inverse:
  fixes v :: "real^'n"
  assumes "v \<in> Basis"
  shows "\<exists>i. v = axis i 1"
proof -
  have "v \<in> (\<Union>n. \<Union>r\<in>Basis. {axis n r})"
    using assms Basis_vec_def by blast
  then show ?thesis
    by (force simp add: vec_eq_iff)
qed

lemma axis_index:
  fixes v :: "real^'n"
  assumes "v \<in> Basis"
  shows "v = axis (axis_index v) 1"
  by (metis (mono_tags) assms axis_inverse axis_index_def someI_ex)

lemma axis_index_axis [simp]:
  fixes UU :: "real^'n"
  shows "(axis_index (axis u 1 :: real^'n)) = (u::'n)"
  by (simp add: axis_eq_axis axis_index_def)

subsection\<^marker>\<open>tag unimportant\<close> \<open>A naive proof procedure to lift really trivial arithmetic stuff from the basis of the vector space\<close>

lemma sum_cong_aux:
  "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> sum f A = sum g A"
  by (auto intro: sum.cong)

hide_fact (open) sum_cong_aux

method_setup vector = \<open>
let
  val ss1 =
    simpset_of (put_simpset HOL_basic_ss \<^context>
      addsimps [@{thm sum.distrib} RS sym,
      @{thm sum_subtractf} RS sym, @{thm sum_distrib_left},
      @{thm sum_distrib_right}, @{thm sum_negf} RS sym])
  val ss2 =
    simpset_of (\<^context> addsimps
             [@{thm plus_vec_def}, @{thm times_vec_def},
              @{thm minus_vec_def}, @{thm uminus_vec_def},
              @{thm one_vec_def}, @{thm zero_vec_def}, @{thm vec_def},
              @{thm scaleR_vec_def}, @{thm vector_scalar_mult_def}])
  fun vector_arith_tac ctxt ths =
    simp_tac (put_simpset ss1 ctxt)
    THEN' (fn i => resolve_tac ctxt @{thms Finite_Cartesian_Product.sum_cong_aux} i
         ORELSE resolve_tac ctxt @{thms sum.neutral} i
         ORELSE simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm vec_eq_iff}]) i)
    (* THEN' TRY o clarify_tac HOL_cs  THEN' (TRY o rtac @{thm iffI}) *)
    THEN' asm_full_simp_tac (put_simpset ss2 ctxt addsimps ths)
in
  Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD' (vector_arith_tac ctxt ths))
end
\<close> "lift trivial vector statements to real arith statements"

lemma vec_0[simp]: "vec 0 = 0" by vector
lemma vec_1[simp]: "vec 1 = 1" by vector

lemma vec_inj[simp]: "vec x = vec y \<longleftrightarrow> x = y" by vector

lemma vec_in_image_vec: "vec x \<in> (vec ` S) \<longleftrightarrow> x \<in> S" by auto

lemma vec_add: "vec(x + y) = vec x + vec y"  by vector
lemma vec_sub: "vec(x - y) = vec x - vec y" by vector
lemma vec_cmul: "vec(c * x) = c *s vec x " by vector
lemma vec_neg: "vec(- x) = - vec x " by vector

lemma vec_scaleR: "vec(c * x) = c *\<^sub>R vec x"
  by vector

lemma vec_sum:
  assumes "finite S"
  shows "vec(sum f S) = sum (vec \<circ> f) S"
  using assms
proof induct
  case empty
  then show ?case by simp
next
  case insert
  then show ?case by (auto simp add: vec_add)
qed

text\<open>Obvious "component-pushing".\<close>

lemma vec_component [simp]: "vec x $ i = x"
  by vector

lemma vector_mult_component [simp]: "(x * y)$i = x$i * y$i"
  by vector

lemma vector_smult_component [simp]: "(c *s y)$i = c * (y$i)"
  by vector

lemma cond_component: "(if b then x else y)$i = (if b then x$i else y$i)" by vector

lemmas\<^marker>\<open>tag unimportant\<close> vector_component =
  vec_component vector_add_component vector_mult_component
  vector_smult_component vector_minus_component vector_uminus_component
  vector_scaleR_component cond_component


subsection\<^marker>\<open>tag unimportant\<close> \<open>Some frequently useful arithmetic lemmas over vectors\<close>

instance vec :: (semigroup_mult, finite) semigroup_mult
  by standard (vector mult.assoc)

instance vec :: (monoid_mult, finite) monoid_mult
  by standard vector+

instance vec :: (ab_semigroup_mult, finite) ab_semigroup_mult
  by standard (vector mult.commute)

instance vec :: (comm_monoid_mult, finite) comm_monoid_mult
  by standard vector

instance vec :: (semiring, finite) semiring
  by standard (vector field_simps)+

instance vec :: (semiring_0, finite) semiring_0
  by standard (vector field_simps)+
instance vec :: (semiring_1, finite) semiring_1
  by standard vector
instance vec :: (comm_semiring, finite) comm_semiring
  by standard (vector field_simps)+

instance vec :: (comm_semiring_0, finite) comm_semiring_0 ..
instance vec :: (semiring_0_cancel, finite) semiring_0_cancel ..
instance vec :: (comm_semiring_0_cancel, finite) comm_semiring_0_cancel ..
instance vec :: (ring, finite) ring ..
instance vec :: (semiring_1_cancel, finite) semiring_1_cancel ..
instance vec :: (comm_semiring_1, finite) comm_semiring_1 ..

instance vec :: (ring_1, finite) ring_1 ..

instance vec :: (real_algebra, finite) real_algebra
  by standard (simp_all add: vec_eq_iff)

instance vec :: (real_algebra_1, finite) real_algebra_1 ..

lemma of_nat_index: "(of_nat n :: 'a::semiring_1 ^'n)$i = of_nat n"
proof (induct n)
  case 0
  then show ?case by vector
next
  case Suc
  then show ?case by vector
qed

lemma one_index [simp]: "(1 :: 'a :: one ^ 'n) $ i = 1"
  by vector

lemma neg_one_index [simp]: "(- 1 :: 'a :: {one, uminus} ^ 'n) $ i = - 1"
  by vector

instance vec :: (semiring_char_0, finite) semiring_char_0
proof
  fix m n :: nat
  show "inj (of_nat :: nat \<Rightarrow> 'a ^ 'b)"
    by (auto intro!: injI simp add: vec_eq_iff of_nat_index)
qed

instance vec :: (numeral, finite) numeral ..
instance vec :: (semiring_numeral, finite) semiring_numeral ..

lemma numeral_index [simp]: "numeral w $ i = numeral w"
  by (induct w) (simp_all only: numeral.simps vector_add_component one_index)

lemma neg_numeral_index [simp]: "- numeral w $ i = - numeral w"
  by (simp only: vector_uminus_component numeral_index)

instance vec :: (comm_ring_1, finite) comm_ring_1 ..
instance vec :: (ring_char_0, finite) ring_char_0 ..

lemma vector_smult_assoc: "a *s (b *s x) = ((a::'a::semigroup_mult) * b) *s x"
  by (vector mult.assoc)
lemma vector_sadd_rdistrib: "((a::'a::semiring) + b) *s x = a *s x + b *s x"
  by (vector field_simps)
lemma vector_add_ldistrib: "(c::'a::semiring) *s (x + y) = c *s x + c *s y"
  by (vector field_simps)
lemma vector_smult_lzero[simp]: "(0::'a::mult_zero) *s x = 0" by vector
lemma vector_smult_lid[simp]: "(1::'a::monoid_mult) *s x = x" by vector
lemma vector_ssub_ldistrib: "(c::'a::ring) *s (x - y) = c *s x - c *s y"
  by (vector field_simps)
lemma vector_smult_rneg: "(c::'a::ring) *s -x = -(c *s x)" by vector
lemma vector_smult_lneg: "- (c::'a::ring) *s x = -(c *s x)" by vector
lemma vector_sneg_minus1: "-x = (-1::'a::ring_1) *s x" by vector
lemma vector_smult_rzero[simp]: "c *s 0 = (0::'a::mult_zero ^ 'n)" by vector
lemma vector_sub_rdistrib: "((a::'a::ring) - b) *s x = a *s x - b *s x"
  by (vector field_simps)

lemma vec_eq[simp]: "(vec m = vec n) \<longleftrightarrow> (m = n)"
  by (simp add: vec_eq_iff)

lemma Vector_Spaces_linear_vec [simp]: "Vector_Spaces.linear (*) vector_scalar_mult vec"
  by unfold_locales (vector algebra_simps)+

lemma vector_mul_eq_0[simp]: "(a *s x = 0) \<longleftrightarrow> a = (0::'a::idom) \<or> x = 0"
  by vector

lemma vector_mul_lcancel[simp]: "a *s x = a *s y \<longleftrightarrow> a = (0::'a::field) \<or> x = y"
  by (metis eq_iff_diff_eq_0 vector_mul_eq_0 vector_ssub_ldistrib)

lemma vector_mul_rcancel[simp]: "a *s x = b *s x \<longleftrightarrow> (a::'a::field) = b \<or> x = 0"
  by (subst eq_iff_diff_eq_0, subst vector_sub_rdistrib [symmetric]) simp

lemma scalar_mult_eq_scaleR [abs_def]: "c *s x = c *\<^sub>R x"
  unfolding scaleR_vec_def vector_scalar_mult_def by simp

lemma dist_mul[simp]: "dist (c *s x) (c *s y) = \<bar>c\<bar> * dist x y"
  unfolding dist_norm scalar_mult_eq_scaleR
  unfolding scaleR_right_diff_distrib[symmetric] by simp

lemma sum_component [simp]:
  fixes f:: " 'a \<Rightarrow> ('b::comm_monoid_add) ^'n"
  shows "(sum f S)$i = sum (\<lambda>x. (f x)$i) S"
proof (cases "finite S")
  case True
  then show ?thesis by induct simp_all
next
  case False
  then show ?thesis by simp
qed

lemma sum_eq: "sum f S = (\<chi> i. sum (\<lambda>x. (f x)$i ) S)"
  by (simp add: vec_eq_iff)

lemma sum_cmul:
  fixes f:: "'c \<Rightarrow> ('a::semiring_1)^'n"
  shows "sum (\<lambda>x. c *s f x) S = c *s sum f S"
  by (simp add: vec_eq_iff sum_distrib_left)

lemma linear_vec [simp]: "linear vec"
  using Vector_Spaces_linear_vec
  by unfold_locales (vector algebra_simps)+

subsection \<open>Matrix operations\<close>

text\<open>Matrix notation. NB: an MxN matrix is of type \<^typ>\<open>'a^'n^'m\<close>, not \<^typ>\<open>'a^'m^'n\<close>\<close>

definition\<^marker>\<open>tag important\<close> map_matrix::"('a \<Rightarrow> 'b) \<Rightarrow> (('a, 'i::finite)vec, 'j::finite) vec \<Rightarrow> (('b, 'i)vec, 'j) vec" where
  "map_matrix f x = (\<chi> i j. f (x $ i $ j))"

lemma nth_map_matrix[simp]: "map_matrix f x $ i $ j = f (x $ i $ j)"
  by (simp add: map_matrix_def)

definition\<^marker>\<open>tag important\<close> matrix_matrix_mult :: "('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'p^'n \<Rightarrow> 'a ^ 'p ^'m"
    (infixl "**" 70)
  where "m ** m' == (\<chi> i j. sum (\<lambda>k. ((m$i)$k) * ((m'$k)$j)) (UNIV :: 'n set)) ::'a ^ 'p ^'m"

definition\<^marker>\<open>tag important\<close> matrix_vector_mult :: "('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'n \<Rightarrow> 'a ^ 'm"
    (infixl "*v" 70)
  where "m *v x \<equiv> (\<chi> i. sum (\<lambda>j. ((m$i)$j) * (x$j)) (UNIV ::'n set)) :: 'a^'m"

definition\<^marker>\<open>tag important\<close> vector_matrix_mult :: "'a ^ 'm \<Rightarrow> ('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'n "
    (infixl "v*" 70)
  where "v v* m == (\<chi> j. sum (\<lambda>i. ((m$i)$j) * (v$i)) (UNIV :: 'm set)) :: 'a^'n"

definition\<^marker>\<open>tag unimportant\<close> "(mat::'a::zero => 'a ^'n^'n) k = (\<chi> i j. if i = j then k else 0)"
definition\<^marker>\<open>tag unimportant\<close> transpose where
  "(transpose::'a^'n^'m \<Rightarrow> 'a^'m^'n) A = (\<chi> i j. ((A$j)$i))"
definition\<^marker>\<open>tag unimportant\<close> "(row::'m => 'a ^'n^'m \<Rightarrow> 'a ^'n) i A = (\<chi> j. ((A$i)$j))"
definition\<^marker>\<open>tag unimportant\<close> "(column::'n =>'a^'n^'m =>'a^'m) j A = (\<chi> i. ((A$i)$j))"
definition\<^marker>\<open>tag unimportant\<close> "rows(A::'a^'n^'m) = { row i A | i. i \<in> (UNIV :: 'm set)}"
definition\<^marker>\<open>tag unimportant\<close> "columns(A::'a^'n^'m) = { column i A | i. i \<in> (UNIV :: 'n set)}"

lemma times0_left [simp]: "(0::'a::semiring_1^'n^'m) ** (A::'a ^'p^'n) = 0" 
  by (simp add: matrix_matrix_mult_def zero_vec_def)

lemma times0_right [simp]: "(A::'a::semiring_1^'n^'m) ** (0::'a ^'p^'n) = 0" 
  by (simp add: matrix_matrix_mult_def zero_vec_def)

lemma mat_0[simp]: "mat 0 = 0" by (vector mat_def)
lemma matrix_add_ldistrib: "(A ** (B + C)) = (A ** B) + (A ** C)"
  by (vector matrix_matrix_mult_def sum.distrib[symmetric] field_simps)

lemma matrix_mul_lid [simp]:
  fixes A :: "'a::semiring_1 ^ 'm ^ 'n"
  shows "mat 1 ** A = A"
  unfolding matrix_matrix_mult_def mat_def
  by (auto simp: if_distrib if_distribR sum.delta'[OF finite] cong: if_cong)

lemma matrix_mul_rid [simp]:
  fixes A :: "'a::semiring_1 ^ 'm ^ 'n"
  shows "A ** mat 1 = A"
  unfolding matrix_matrix_mult_def mat_def
  by (auto simp: if_distrib if_distribR sum.delta'[OF finite] cong: if_cong)

proposition matrix_mul_assoc: "A ** (B ** C) = (A ** B) ** C"
  apply (vector matrix_matrix_mult_def sum_distrib_left sum_distrib_right mult.assoc)
  apply (subst sum.swap)
  apply simp
  done

proposition matrix_vector_mul_assoc: "A *v (B *v x) = (A ** B) *v x"
  apply (vector matrix_matrix_mult_def matrix_vector_mult_def
    sum_distrib_left sum_distrib_right mult.assoc)
  apply (subst sum.swap)
  apply simp
  done

proposition scalar_matrix_assoc:
  fixes A :: "('a::real_algebra_1)^'m^'n"
  shows "k *\<^sub>R (A ** B) = (k *\<^sub>R A) ** B"
  by (simp add: matrix_matrix_mult_def sum_distrib_left mult_ac vec_eq_iff scaleR_sum_right)

proposition matrix_scalar_ac:
  fixes A :: "('a::real_algebra_1)^'m^'n"
  shows "A ** (k *\<^sub>R B) = k *\<^sub>R A ** B"
  by (simp add: matrix_matrix_mult_def sum_distrib_left mult_ac vec_eq_iff)

lemma matrix_vector_mul_lid [simp]: "mat 1 *v x = (x::'a::semiring_1 ^ 'n)"
  apply (vector matrix_vector_mult_def mat_def)
  apply (simp add: if_distrib if_distribR cong del: if_weak_cong)
  done

lemma matrix_transpose_mul:
    "transpose(A ** B) = transpose B ** transpose (A::'a::comm_semiring_1^_^_)"
  by (simp add: matrix_matrix_mult_def transpose_def vec_eq_iff mult.commute)

lemma matrix_mult_transpose_dot_column:
  shows "transpose A ** A = (\<chi> i j. inner (column i A) (column j A))"
  by (simp add: matrix_matrix_mult_def vec_eq_iff transpose_def column_def inner_vec_def)

lemma matrix_mult_transpose_dot_row:
  shows "A ** transpose A = (\<chi> i j. inner (row i A) (row j A))"
  by (simp add: matrix_matrix_mult_def vec_eq_iff transpose_def row_def inner_vec_def)

lemma matrix_eq:
  fixes A B :: "'a::semiring_1 ^ 'n ^ 'm"
  shows "A = B \<longleftrightarrow> (\<forall>x. A *v x = B *v x)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then show ?lhs
    apply (subst vec_eq_iff)
    apply (clarsimp simp add: matrix_vector_mult_def if_distrib if_distribR vec_eq_iff cong: if_cong)
    apply (erule_tac x="axis ia 1" in allE)
    apply (erule_tac x="i" in allE)
    apply (auto simp add: if_distrib if_distribR axis_def
        sum.delta[OF finite] cong del: if_weak_cong)
    done
qed auto

lemma matrix_vector_mul_component: "(A *v x)$k = inner (A$k) x"
  by (simp add: matrix_vector_mult_def inner_vec_def)

lemma dot_lmul_matrix: "inner ((x::real ^_) v* A) y = inner x (A *v y)"
  apply (simp add: inner_vec_def matrix_vector_mult_def vector_matrix_mult_def sum_distrib_right sum_distrib_left ac_simps)
  apply (subst sum.swap)
  apply simp
  done

lemma transpose_mat [simp]: "transpose (mat n) = mat n"
  by (vector transpose_def mat_def)

lemma transpose_transpose [simp]: "transpose(transpose A) = A"
  by (vector transpose_def)

lemma row_transpose [simp]: "row i (transpose A) = column i A"
  by (simp add: row_def column_def transpose_def vec_eq_iff)

lemma column_transpose [simp]: "column i (transpose A) = row i A"
  by (simp add: row_def column_def transpose_def vec_eq_iff)

lemma rows_transpose [simp]: "rows(transpose A) = columns A"
  by (auto simp add: rows_def columns_def intro: set_eqI)

lemma columns_transpose [simp]: "columns(transpose A) = rows A"
  by (metis transpose_transpose rows_transpose)

lemma transpose_scalar: "transpose (k *\<^sub>R A) = k *\<^sub>R transpose A"
  unfolding transpose_def
  by (simp add: vec_eq_iff)

lemma transpose_iff [iff]: "transpose A = transpose B \<longleftrightarrow> A = B"
  by (metis transpose_transpose)

lemma matrix_mult_sum:
  "(A::'a::comm_semiring_1^'n^'m) *v x = sum (\<lambda>i. (x$i) *s column i A) (UNIV:: 'n set)"
  by (simp add: matrix_vector_mult_def vec_eq_iff column_def mult.commute)

lemma vector_componentwise:
  "(x::'a::ring_1^'n) = (\<chi> j. \<Sum>i\<in>UNIV. (x$i) * (axis i 1 :: 'a^'n) $ j)"
  by (simp add: axis_def if_distrib sum.If_cases vec_eq_iff)

lemma basis_expansion: "sum (\<lambda>i. (x$i) *s axis i 1) UNIV = (x::('a::ring_1) ^'n)"
  by (auto simp add: axis_def vec_eq_iff if_distrib sum.If_cases cong del: if_weak_cong)


text\<open>Correspondence between matrices and linear operators.\<close>

definition\<^marker>\<open>tag important\<close> matrix :: "('a::{plus,times, one, zero}^'m \<Rightarrow> 'a ^ 'n) \<Rightarrow> 'a^'m^'n"
  where "matrix f = (\<chi> i j. (f(axis j 1))$i)"

lemma matrix_id_mat_1: "matrix id = mat 1"
  by (simp add: mat_def matrix_def axis_def)

lemma matrix_scaleR: "(matrix ((*\<^sub>R) r)) = mat r"
  by (simp add: mat_def matrix_def axis_def if_distrib cong: if_cong)

lemma matrix_vector_mul_linear[intro, simp]: "linear (\<lambda>x. A *v (x::'a::real_algebra_1 ^ _))"
  by (simp add: linear_iff matrix_vector_mult_def vec_eq_iff field_simps sum_distrib_left
      sum.distrib scaleR_right.sum)

lemma vector_matrix_left_distrib [algebra_simps]:
  shows "(x + y) v* A = x v* A + y v* A"
  unfolding vector_matrix_mult_def
  by (simp add: algebra_simps sum.distrib vec_eq_iff)

lemma matrix_vector_right_distrib [algebra_simps]:
  "A *v (x + y) = A *v x + A *v y"
  by (vector matrix_vector_mult_def sum.distrib distrib_left)

lemma matrix_vector_mult_diff_distrib [algebra_simps]:
  fixes A :: "'a::ring_1^'n^'m"
  shows "A *v (x - y) = A *v x - A *v y"
  by (vector matrix_vector_mult_def sum_subtractf right_diff_distrib)

lemma matrix_vector_mult_scaleR[algebra_simps]:
  fixes A :: "real^'n^'m"
  shows "A *v (c *\<^sub>R x) = c *\<^sub>R (A *v x)"
  using linear_iff matrix_vector_mul_linear by blast

lemma matrix_vector_mult_0_right [simp]: "A *v 0 = 0"
  by (simp add: matrix_vector_mult_def vec_eq_iff)

lemma matrix_vector_mult_0 [simp]: "0 *v w = 0"
  by (simp add: matrix_vector_mult_def vec_eq_iff)

lemma matrix_vector_mult_add_rdistrib [algebra_simps]:
  "(A + B) *v x = (A *v x) + (B *v x)"
  by (vector matrix_vector_mult_def sum.distrib distrib_right)

lemma matrix_vector_mult_diff_rdistrib [algebra_simps]:
  fixes A :: "'a :: ring_1^'n^'m"
  shows "(A - B) *v x = (A *v x) - (B *v x)"
  by (vector matrix_vector_mult_def sum_subtractf left_diff_distrib)

lemma matrix_vector_column:
  "(A::'a::comm_semiring_1^'n^_) *v x = sum (\<lambda>i. (x$i) *s ((transpose A)$i)) (UNIV:: 'n set)"
  by (simp add: matrix_vector_mult_def transpose_def vec_eq_iff mult.commute)

subsection\<open>Inverse matrices  (not necessarily square)\<close>

definition\<^marker>\<open>tag important\<close>
  "invertible(A::'a::semiring_1^'n^'m) \<longleftrightarrow> (\<exists>A'::'a^'m^'n. A ** A' = mat 1 \<and> A' ** A = mat 1)"

definition\<^marker>\<open>tag important\<close>
  "matrix_inv(A:: 'a::semiring_1^'n^'m) =
    (SOME A'::'a^'m^'n. A ** A' = mat 1 \<and> A' ** A = mat 1)"

lemma inj_matrix_vector_mult:
  fixes A::"'a::field^'n^'m"
  assumes "invertible A"
  shows "inj ((*v) A)"
  by (metis assms inj_on_inverseI invertible_def matrix_vector_mul_assoc matrix_vector_mul_lid)

lemma scalar_invertible:
  fixes A :: "('a::real_algebra_1)^'m^'n"
  assumes "k \<noteq> 0" and "invertible A"
  shows "invertible (k *\<^sub>R A)"
proof -
  obtain A' where "A ** A' = mat 1" and "A' ** A = mat 1"
    using assms unfolding invertible_def by auto
  with \<open>k \<noteq> 0\<close>
  have "(k *\<^sub>R A) ** ((1/k) *\<^sub>R A') = mat 1" "((1/k) *\<^sub>R A') ** (k *\<^sub>R A) = mat 1"
    by (simp_all add: assms matrix_scalar_ac)
  thus "invertible (k *\<^sub>R A)"
    unfolding invertible_def by auto
qed

proposition scalar_invertible_iff:
  fixes A :: "('a::real_algebra_1)^'m^'n"
  assumes "k \<noteq> 0" and "invertible A"
  shows "invertible (k *\<^sub>R A) \<longleftrightarrow> k \<noteq> 0 \<and> invertible A"
  by (simp add: assms scalar_invertible)

lemma vector_transpose_matrix [simp]: "x v* transpose A = A *v x"
  unfolding transpose_def vector_matrix_mult_def matrix_vector_mult_def
  by simp

lemma transpose_matrix_vector [simp]: "transpose A *v x = x v* A"
  unfolding transpose_def vector_matrix_mult_def matrix_vector_mult_def
  by simp

lemma vector_scalar_commute:
  fixes A :: "'a::{field}^'m^'n"
  shows "A *v (c *s x) = c *s (A *v x)"
  by (simp add: vector_scalar_mult_def matrix_vector_mult_def mult_ac sum_distrib_left)

lemma scalar_vector_matrix_assoc:
  fixes k :: "'a::{field}" and x :: "'a::{field}^'n" and A :: "'a^'m^'n"
  shows "(k *s x) v* A = k *s (x v* A)"
  by (metis transpose_matrix_vector vector_scalar_commute)
 
lemma vector_matrix_mult_0 [simp]: "0 v* A = 0"
  unfolding vector_matrix_mult_def by (simp add: zero_vec_def)

lemma vector_matrix_mult_0_right [simp]: "x v* 0 = 0"
  unfolding vector_matrix_mult_def by (simp add: zero_vec_def)

lemma vector_matrix_mul_rid [simp]:
  fixes v :: "('a::semiring_1)^'n"
  shows "v v* mat 1 = v"
  by (metis matrix_vector_mul_lid transpose_mat vector_transpose_matrix)

lemma scaleR_vector_matrix_assoc:
  fixes k :: real and x :: "real^'n" and A :: "real^'m^'n"
  shows "(k *\<^sub>R x) v* A = k *\<^sub>R (x v* A)"
  by (metis matrix_vector_mult_scaleR transpose_matrix_vector)

proposition vector_scaleR_matrix_ac:
  fixes k :: real and x :: "real^'n" and A :: "real^'m^'n"
  shows "x v* (k *\<^sub>R A) = k *\<^sub>R (x v* A)"
proof -
  have "x v* (k *\<^sub>R A) = (k *\<^sub>R x) v* A"
    unfolding vector_matrix_mult_def
    by (simp add: algebra_simps)
  with scaleR_vector_matrix_assoc
  show "x v* (k *\<^sub>R A) = k *\<^sub>R (x v* A)"
    by auto
qed

end
