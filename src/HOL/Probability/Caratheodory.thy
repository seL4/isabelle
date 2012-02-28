(*  Title:      HOL/Probability/Caratheodory.thy
    Author:     Lawrence C Paulson
    Author:     Johannes Hölzl, TU München
*)

header {*Caratheodory Extension Theorem*}

theory Caratheodory
imports Sigma_Algebra "~~/src/HOL/Multivariate_Analysis/Extended_Real_Limits"
begin

lemma sums_def2:
  "f sums x \<longleftrightarrow> (\<lambda>n. (\<Sum>i\<le>n. f i)) ----> x"
  unfolding sums_def
  apply (subst LIMSEQ_Suc_iff[symmetric])
  unfolding atLeastLessThanSuc_atLeastAtMost atLeast0AtMost ..

text {*
  Originally from the Hurd/Coble measure theory development, translated by Lawrence Paulson.
*}

lemma suminf_ereal_2dimen:
  fixes f:: "nat \<times> nat \<Rightarrow> ereal"
  assumes pos: "\<And>p. 0 \<le> f p"
  assumes "\<And>m. g m = (\<Sum>n. f (m,n))"
  shows "(\<Sum>i. f (prod_decode i)) = suminf g"
proof -
  have g_def: "g = (\<lambda>m. (\<Sum>n. f (m,n)))"
    using assms by (simp add: fun_eq_iff)
  have reindex: "\<And>B. (\<Sum>x\<in>B. f (prod_decode x)) = setsum f (prod_decode ` B)"
    by (simp add: setsum_reindex[OF inj_prod_decode] comp_def)
  { fix n
    let ?M = "\<lambda>f. Suc (Max (f ` prod_decode ` {..<n}))"
    { fix a b x assume "x < n" and [symmetric]: "(a, b) = prod_decode x"
      then have "a < ?M fst" "b < ?M snd"
        by (auto intro!: Max_ge le_imp_less_Suc image_eqI) }
    then have "setsum f (prod_decode ` {..<n}) \<le> setsum f ({..<?M fst} \<times> {..<?M snd})"
      by (auto intro!: setsum_mono3 simp: pos)
    then have "\<exists>a b. setsum f (prod_decode ` {..<n}) \<le> setsum f ({..<a} \<times> {..<b})" by auto }
  moreover
  { fix a b
    let ?M = "prod_decode ` {..<Suc (Max (prod_encode ` ({..<a} \<times> {..<b})))}"
    { fix a' b' assume "a' < a" "b' < b" then have "(a', b') \<in> ?M"
        by (auto intro!: Max_ge le_imp_less_Suc image_eqI[where x="prod_encode (a', b')"]) }
    then have "setsum f ({..<a} \<times> {..<b}) \<le> setsum f ?M"
      by (auto intro!: setsum_mono3 simp: pos) }
  ultimately
  show ?thesis unfolding g_def using pos
    by (auto intro!: SUPR_eq  simp: setsum_cartesian_product reindex SUP_upper2
                     setsum_nonneg suminf_ereal_eq_SUPR SUPR_pair
                     SUPR_ereal_setsum[symmetric] incseq_setsumI setsum_nonneg)
qed

subsection {* Measure Spaces *}

record 'a measure_space = "'a algebra" +
  measure :: "'a set \<Rightarrow> ereal"

definition positive where "positive M f \<longleftrightarrow> f {} = (0::ereal) \<and> (\<forall>A\<in>sets M. 0 \<le> f A)"

definition additive where "additive M f \<longleftrightarrow>
  (\<forall>x \<in> sets M. \<forall>y \<in> sets M. x \<inter> y = {} \<longrightarrow> f (x \<union> y) = f x + f y)"

definition countably_additive :: "('a, 'b) algebra_scheme \<Rightarrow> ('a set \<Rightarrow> ereal) \<Rightarrow> bool" where
  "countably_additive M f \<longleftrightarrow> (\<forall>A. range A \<subseteq> sets M \<longrightarrow> disjoint_family A \<longrightarrow> (\<Union>i. A i) \<in> sets M \<longrightarrow>
    (\<Sum>i. f (A i)) = f (\<Union>i. A i))"

definition increasing where "increasing M f \<longleftrightarrow>
  (\<forall>x \<in> sets M. \<forall>y \<in> sets M. x \<subseteq> y \<longrightarrow> f x \<le> f y)"

definition subadditive where "subadditive M f \<longleftrightarrow>
  (\<forall>x \<in> sets M. \<forall>y \<in> sets M. x \<inter> y = {} \<longrightarrow> f (x \<union> y) \<le> f x + f y)"

definition countably_subadditive where "countably_subadditive M f \<longleftrightarrow>
  (\<forall>A. range A \<subseteq> sets M \<longrightarrow> disjoint_family A \<longrightarrow> (\<Union>i. A i) \<in> sets M \<longrightarrow>
    (f (\<Union>i. A i) \<le> (\<Sum>i. f (A i))))"

definition lambda_system where "lambda_system M f = {l \<in> sets M.
  \<forall>x \<in> sets M. f (l \<inter> x) + f ((space M - l) \<inter> x) = f x}"

definition outer_measure_space where "outer_measure_space M f \<longleftrightarrow>
  positive M f \<and> increasing M f \<and> countably_subadditive M f"

definition measure_set where "measure_set M f X = {r.
  \<exists>A. range A \<subseteq> sets M \<and> disjoint_family A \<and> X \<subseteq> (\<Union>i. A i) \<and> (\<Sum>i. f (A i)) = r}"

locale measure_space = sigma_algebra M for M :: "('a, 'b) measure_space_scheme" +
  assumes measure_positive: "positive M (measure M)"
      and ca: "countably_additive M (measure M)"

abbreviation (in measure_space) "\<mu> \<equiv> measure M"

lemma (in measure_space)
  shows empty_measure[simp, intro]: "\<mu> {} = 0"
  and positive_measure[simp, intro!]: "\<And>A. A \<in> sets M \<Longrightarrow> 0 \<le> \<mu> A"
  using measure_positive unfolding positive_def by auto

lemma increasingD:
  "increasing M f \<Longrightarrow> x \<subseteq> y \<Longrightarrow> x\<in>sets M \<Longrightarrow> y\<in>sets M \<Longrightarrow> f x \<le> f y"
  by (auto simp add: increasing_def)

lemma subadditiveD:
  "subadditive M f \<Longrightarrow> x \<inter> y = {} \<Longrightarrow> x \<in> sets M \<Longrightarrow> y \<in> sets M
    \<Longrightarrow> f (x \<union> y) \<le> f x + f y"
  by (auto simp add: subadditive_def)

lemma additiveD:
  "additive M f \<Longrightarrow> x \<inter> y = {} \<Longrightarrow> x \<in> sets M \<Longrightarrow> y \<in> sets M
    \<Longrightarrow> f (x \<union> y) = f x + f y"
  by (auto simp add: additive_def)

lemma countably_additiveI:
  assumes "\<And>A x. range A \<subseteq> sets M \<Longrightarrow> disjoint_family A \<Longrightarrow> (\<Union>i. A i) \<in> sets M
    \<Longrightarrow> (\<Sum>i. f (A i)) = f (\<Union>i. A i)"
  shows "countably_additive M f"
  using assms by (simp add: countably_additive_def)

section "Extend binary sets"

lemma LIMSEQ_binaryset:
  assumes f: "f {} = 0"
  shows  "(\<lambda>n. \<Sum>i<n. f (binaryset A B i)) ----> f A + f B"
proof -
  have "(\<lambda>n. \<Sum>i < Suc (Suc n). f (binaryset A B i)) = (\<lambda>n. f A + f B)"
    proof
      fix n
      show "(\<Sum>i < Suc (Suc n). f (binaryset A B i)) = f A + f B"
        by (induct n)  (auto simp add: binaryset_def f)
    qed
  moreover
  have "... ----> f A + f B" by (rule tendsto_const)
  ultimately
  have "(\<lambda>n. \<Sum>i< Suc (Suc n). f (binaryset A B i)) ----> f A + f B"
    by metis
  hence "(\<lambda>n. \<Sum>i< n+2. f (binaryset A B i)) ----> f A + f B"
    by simp
  thus ?thesis by (rule LIMSEQ_offset [where k=2])
qed

lemma binaryset_sums:
  assumes f: "f {} = 0"
  shows  "(\<lambda>n. f (binaryset A B n)) sums (f A + f B)"
    by (simp add: sums_def LIMSEQ_binaryset [where f=f, OF f] atLeast0LessThan)

lemma suminf_binaryset_eq:
  fixes f :: "'a set \<Rightarrow> 'b::{comm_monoid_add, t2_space}"
  shows "f {} = 0 \<Longrightarrow> (\<Sum>n. f (binaryset A B n)) = f A + f B"
  by (metis binaryset_sums sums_unique)

subsection {* Lambda Systems *}

lemma (in algebra) lambda_system_eq:
  shows "lambda_system M f = {l \<in> sets M.
    \<forall>x \<in> sets M. f (x \<inter> l) + f (x - l) = f x}"
proof -
  have [simp]: "!!l x. l \<in> sets M \<Longrightarrow> x \<in> sets M \<Longrightarrow> (space M - l) \<inter> x = x - l"
    by (metis Int_Diff Int_absorb1 Int_commute sets_into_space)
  show ?thesis
    by (auto simp add: lambda_system_def) (metis Int_commute)+
qed

lemma (in algebra) lambda_system_empty:
  "positive M f \<Longrightarrow> {} \<in> lambda_system M f"
  by (auto simp add: positive_def lambda_system_eq)

lemma lambda_system_sets:
  "x \<in> lambda_system M f \<Longrightarrow> x \<in> sets M"
  by (simp add: lambda_system_def)

lemma (in algebra) lambda_system_Compl:
  fixes f:: "'a set \<Rightarrow> ereal"
  assumes x: "x \<in> lambda_system M f"
  shows "space M - x \<in> lambda_system M f"
proof -
  have "x \<subseteq> space M"
    by (metis sets_into_space lambda_system_sets x)
  hence "space M - (space M - x) = x"
    by (metis double_diff equalityE)
  with x show ?thesis
    by (force simp add: lambda_system_def ac_simps)
qed

lemma (in algebra) lambda_system_Int:
  fixes f:: "'a set \<Rightarrow> ereal"
  assumes xl: "x \<in> lambda_system M f" and yl: "y \<in> lambda_system M f"
  shows "x \<inter> y \<in> lambda_system M f"
proof -
  from xl yl show ?thesis
  proof (auto simp add: positive_def lambda_system_eq Int)
    fix u
    assume x: "x \<in> sets M" and y: "y \<in> sets M" and u: "u \<in> sets M"
       and fx: "\<forall>z\<in>sets M. f (z \<inter> x) + f (z - x) = f z"
       and fy: "\<forall>z\<in>sets M. f (z \<inter> y) + f (z - y) = f z"
    have "u - x \<inter> y \<in> sets M"
      by (metis Diff Diff_Int Un u x y)
    moreover
    have "(u - (x \<inter> y)) \<inter> y = u \<inter> y - x" by blast
    moreover
    have "u - x \<inter> y - y = u - y" by blast
    ultimately
    have ey: "f (u - x \<inter> y) = f (u \<inter> y - x) + f (u - y)" using fy
      by force
    have "f (u \<inter> (x \<inter> y)) + f (u - x \<inter> y)
          = (f (u \<inter> (x \<inter> y)) + f (u \<inter> y - x)) + f (u - y)"
      by (simp add: ey ac_simps)
    also have "... =  (f ((u \<inter> y) \<inter> x) + f (u \<inter> y - x)) + f (u - y)"
      by (simp add: Int_ac)
    also have "... = f (u \<inter> y) + f (u - y)"
      using fx [THEN bspec, of "u \<inter> y"] Int y u
      by force
    also have "... = f u"
      by (metis fy u)
    finally show "f (u \<inter> (x \<inter> y)) + f (u - x \<inter> y) = f u" .
  qed
qed

lemma (in algebra) lambda_system_Un:
  fixes f:: "'a set \<Rightarrow> ereal"
  assumes xl: "x \<in> lambda_system M f" and yl: "y \<in> lambda_system M f"
  shows "x \<union> y \<in> lambda_system M f"
proof -
  have "(space M - x) \<inter> (space M - y) \<in> sets M"
    by (metis Diff_Un Un compl_sets lambda_system_sets xl yl)
  moreover
  have "x \<union> y = space M - ((space M - x) \<inter> (space M - y))"
    by auto (metis subsetD lambda_system_sets sets_into_space xl yl)+
  ultimately show ?thesis
    by (metis lambda_system_Compl lambda_system_Int xl yl)
qed

lemma (in algebra) lambda_system_algebra:
  "positive M f \<Longrightarrow> algebra (M\<lparr>sets := lambda_system M f\<rparr>)"
  apply (auto simp add: algebra_iff_Un)
  apply (metis lambda_system_sets set_mp sets_into_space)
  apply (metis lambda_system_empty)
  apply (metis lambda_system_Compl)
  apply (metis lambda_system_Un)
  done

lemma (in algebra) lambda_system_strong_additive:
  assumes z: "z \<in> sets M" and disj: "x \<inter> y = {}"
      and xl: "x \<in> lambda_system M f" and yl: "y \<in> lambda_system M f"
  shows "f (z \<inter> (x \<union> y)) = f (z \<inter> x) + f (z \<inter> y)"
proof -
  have "z \<inter> x = (z \<inter> (x \<union> y)) \<inter> x" using disj by blast
  moreover
  have "z \<inter> y = (z \<inter> (x \<union> y)) - x" using disj by blast
  moreover
  have "(z \<inter> (x \<union> y)) \<in> sets M"
    by (metis Int Un lambda_system_sets xl yl z)
  ultimately show ?thesis using xl yl
    by (simp add: lambda_system_eq)
qed

lemma (in algebra) lambda_system_additive:
     "additive (M (|sets := lambda_system M f|)) f"
proof (auto simp add: additive_def)
  fix x and y
  assume disj: "x \<inter> y = {}"
     and xl: "x \<in> lambda_system M f" and yl: "y \<in> lambda_system M f"
  hence  "x \<in> sets M" "y \<in> sets M" by (blast intro: lambda_system_sets)+
  thus "f (x \<union> y) = f x + f y"
    using lambda_system_strong_additive [OF top disj xl yl]
    by (simp add: Un)
qed

lemma (in ring_of_sets) disjointed_additive:
  assumes f: "positive M f" "additive M f" and A: "range A \<subseteq> sets M" "incseq A"
  shows "(\<Sum>i\<le>n. f (disjointed A i)) = f (A n)"
proof (induct n)
  case (Suc n)
  then have "(\<Sum>i\<le>Suc n. f (disjointed A i)) = f (A n) + f (disjointed A (Suc n))"
    by simp
  also have "\<dots> = f (A n \<union> disjointed A (Suc n))"
    using A by (subst f(2)[THEN additiveD]) (auto simp: disjointed_incseq)
  also have "A n \<union> disjointed A (Suc n) = A (Suc n)"
    using `incseq A` by (auto dest: incseq_SucD simp: disjointed_incseq)
  finally show ?case .
qed simp

lemma (in ring_of_sets) countably_subadditive_subadditive:
  assumes f: "positive M f" and cs: "countably_subadditive M f"
  shows  "subadditive M f"
proof (auto simp add: subadditive_def)
  fix x y
  assume x: "x \<in> sets M" and y: "y \<in> sets M" and "x \<inter> y = {}"
  hence "disjoint_family (binaryset x y)"
    by (auto simp add: disjoint_family_on_def binaryset_def)
  hence "range (binaryset x y) \<subseteq> sets M \<longrightarrow>
         (\<Union>i. binaryset x y i) \<in> sets M \<longrightarrow>
         f (\<Union>i. binaryset x y i) \<le> (\<Sum> n. f (binaryset x y n))"
    using cs by (auto simp add: countably_subadditive_def)
  hence "{x,y,{}} \<subseteq> sets M \<longrightarrow> x \<union> y \<in> sets M \<longrightarrow>
         f (x \<union> y) \<le> (\<Sum> n. f (binaryset x y n))"
    by (simp add: range_binaryset_eq UN_binaryset_eq)
  thus "f (x \<union> y) \<le>  f x + f y" using f x y
    by (auto simp add: Un o_def suminf_binaryset_eq positive_def)
qed

lemma (in ring_of_sets) additive_sum:
  fixes A:: "nat \<Rightarrow> 'a set"
  assumes f: "positive M f" and ad: "additive M f" and "finite S"
      and A: "range A \<subseteq> sets M"
      and disj: "disjoint_family_on A S"
  shows  "(\<Sum>i\<in>S. f (A i)) = f (\<Union>i\<in>S. A i)"
using `finite S` disj proof induct
  case empty show ?case using f by (simp add: positive_def)
next
  case (insert s S)
  then have "A s \<inter> (\<Union>i\<in>S. A i) = {}"
    by (auto simp add: disjoint_family_on_def neq_iff)
  moreover
  have "A s \<in> sets M" using A by blast
  moreover have "(\<Union>i\<in>S. A i) \<in> sets M"
    using A `finite S` by auto
  moreover
  ultimately have "f (A s \<union> (\<Union>i\<in>S. A i)) = f (A s) + f(\<Union>i\<in>S. A i)"
    using ad UNION_in_sets A by (auto simp add: additive_def)
  with insert show ?case using ad disjoint_family_on_mono[of S "insert s S" A]
    by (auto simp add: additive_def subset_insertI)
qed

lemma (in algebra) increasing_additive_bound:
  fixes A:: "nat \<Rightarrow> 'a set" and  f :: "'a set \<Rightarrow> ereal"
  assumes f: "positive M f" and ad: "additive M f"
      and inc: "increasing M f"
      and A: "range A \<subseteq> sets M"
      and disj: "disjoint_family A"
  shows  "(\<Sum>i. f (A i)) \<le> f (space M)"
proof (safe intro!: suminf_bound)
  fix N
  note disj_N = disjoint_family_on_mono[OF _ disj, of "{..<N}"]
  have "(\<Sum>i<N. f (A i)) = f (\<Union>i\<in>{..<N}. A i)"
    by (rule additive_sum [OF f ad _ A]) (auto simp: disj_N)
  also have "... \<le> f (space M)" using space_closed A
    by (intro increasingD[OF inc] finite_UN) auto
  finally show "(\<Sum>i<N. f (A i)) \<le> f (space M)" by simp
qed (insert f A, auto simp: positive_def)

lemma lambda_system_increasing:
 "increasing M f \<Longrightarrow> increasing (M (|sets := lambda_system M f|)) f"
  by (simp add: increasing_def lambda_system_def)

lemma lambda_system_positive:
  "positive M f \<Longrightarrow> positive (M (|sets := lambda_system M f|)) f"
  by (simp add: positive_def lambda_system_def)

lemma (in algebra) lambda_system_strong_sum:
  fixes A:: "nat \<Rightarrow> 'a set" and f :: "'a set \<Rightarrow> ereal"
  assumes f: "positive M f" and a: "a \<in> sets M"
      and A: "range A \<subseteq> lambda_system M f"
      and disj: "disjoint_family A"
  shows  "(\<Sum>i = 0..<n. f (a \<inter>A i)) = f (a \<inter> (\<Union>i\<in>{0..<n}. A i))"
proof (induct n)
  case 0 show ?case using f by (simp add: positive_def)
next
  case (Suc n)
  have 2: "A n \<inter> UNION {0..<n} A = {}" using disj
    by (force simp add: disjoint_family_on_def neq_iff)
  have 3: "A n \<in> lambda_system M f" using A
    by blast
  interpret l: algebra "M\<lparr>sets := lambda_system M f\<rparr>"
    using f by (rule lambda_system_algebra)
  have 4: "UNION {0..<n} A \<in> lambda_system M f"
    using A l.UNION_in_sets by simp
  from Suc.hyps show ?case
    by (simp add: atLeastLessThanSuc lambda_system_strong_additive [OF a 2 3 4])
qed

lemma (in sigma_algebra) lambda_system_caratheodory:
  assumes oms: "outer_measure_space M f"
      and A: "range A \<subseteq> lambda_system M f"
      and disj: "disjoint_family A"
  shows  "(\<Union>i. A i) \<in> lambda_system M f \<and> (\<Sum>i. f (A i)) = f (\<Union>i. A i)"
proof -
  have pos: "positive M f" and inc: "increasing M f"
   and csa: "countably_subadditive M f"
    by (metis oms outer_measure_space_def)+
  have sa: "subadditive M f"
    by (metis countably_subadditive_subadditive csa pos)
  have A': "range A \<subseteq> sets (M(|sets := lambda_system M f|))" using A
    by simp
  interpret ls: algebra "M\<lparr>sets := lambda_system M f\<rparr>"
    using pos by (rule lambda_system_algebra)
  have A'': "range A \<subseteq> sets M"
     by (metis A image_subset_iff lambda_system_sets)

  have U_in: "(\<Union>i. A i) \<in> sets M"
    by (metis A'' countable_UN)
  have U_eq: "f (\<Union>i. A i) = (\<Sum>i. f (A i))"
  proof (rule antisym)
    show "f (\<Union>i. A i) \<le> (\<Sum>i. f (A i))"
      using csa[unfolded countably_subadditive_def] A'' disj U_in by auto
    have *: "\<And>i. 0 \<le> f (A i)" using pos A'' unfolding positive_def by auto
    have dis: "\<And>N. disjoint_family_on A {..<N}" by (intro disjoint_family_on_mono[OF _ disj]) auto
    show "(\<Sum>i. f (A i)) \<le> f (\<Union>i. A i)"
      using ls.additive_sum [OF lambda_system_positive[OF pos] lambda_system_additive _ A' dis]
      using A''
      by (intro suminf_bound[OF _ *]) (auto intro!: increasingD[OF inc] allI countable_UN)
  qed
  {
    fix a
    assume a [iff]: "a \<in> sets M"
    have "f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i)) = f a"
    proof -
      show ?thesis
      proof (rule antisym)
        have "range (\<lambda>i. a \<inter> A i) \<subseteq> sets M" using A''
          by blast
        moreover
        have "disjoint_family (\<lambda>i. a \<inter> A i)" using disj
          by (auto simp add: disjoint_family_on_def)
        moreover
        have "a \<inter> (\<Union>i. A i) \<in> sets M"
          by (metis Int U_in a)
        ultimately
        have "f (a \<inter> (\<Union>i. A i)) \<le> (\<Sum>i. f (a \<inter> A i))"
          using csa[unfolded countably_subadditive_def, rule_format, of "(\<lambda>i. a \<inter> A i)"]
          by (simp add: o_def)
        hence "f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i)) \<le>
            (\<Sum>i. f (a \<inter> A i)) + f (a - (\<Union>i. A i))"
          by (rule add_right_mono)
        moreover
        have "(\<Sum>i. f (a \<inter> A i)) + f (a - (\<Union>i. A i)) \<le> f a"
          proof (intro suminf_bound_add allI)
            fix n
            have UNION_in: "(\<Union>i\<in>{0..<n}. A i) \<in> sets M"
              by (metis A'' UNION_in_sets)
            have le_fa: "f (UNION {0..<n} A \<inter> a) \<le> f a" using A''
              by (blast intro: increasingD [OF inc] A'' UNION_in_sets)
            have ls: "(\<Union>i\<in>{0..<n}. A i) \<in> lambda_system M f"
              using ls.UNION_in_sets by (simp add: A)
            hence eq_fa: "f a = f (a \<inter> (\<Union>i\<in>{0..<n}. A i)) + f (a - (\<Union>i\<in>{0..<n}. A i))"
              by (simp add: lambda_system_eq UNION_in)
            have "f (a - (\<Union>i. A i)) \<le> f (a - (\<Union>i\<in>{0..<n}. A i))"
              by (blast intro: increasingD [OF inc] UNION_in U_in)
            thus "(\<Sum>i<n. f (a \<inter> A i)) + f (a - (\<Union>i. A i)) \<le> f a"
              by (simp add: lambda_system_strong_sum pos A disj eq_fa add_left_mono atLeast0LessThan[symmetric])
          next
            have "\<And>i. a \<inter> A i \<in> sets M" using A'' by auto
            then show "\<And>i. 0 \<le> f (a \<inter> A i)" using pos[unfolded positive_def] by auto
            have "\<And>i. a - (\<Union>i. A i) \<in> sets M" using A'' by auto
            then have "\<And>i. 0 \<le> f (a - (\<Union>i. A i))" using pos[unfolded positive_def] by auto
            then show "f (a - (\<Union>i. A i)) \<noteq> -\<infinity>" by auto
          qed
        ultimately show "f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i)) \<le> f a"
          by (rule order_trans)
      next
        have "f a \<le> f (a \<inter> (\<Union>i. A i) \<union> (a - (\<Union>i. A i)))"
          by (blast intro:  increasingD [OF inc] U_in)
        also have "... \<le>  f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i))"
          by (blast intro: subadditiveD [OF sa] U_in)
        finally show "f a \<le> f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i))" .
        qed
     qed
  }
  thus  ?thesis
    by (simp add: lambda_system_eq sums_iff U_eq U_in)
qed

lemma (in sigma_algebra) caratheodory_lemma:
  assumes oms: "outer_measure_space M f"
  shows "measure_space \<lparr> space = space M, sets = lambda_system M f, measure = f \<rparr>"
    (is "measure_space ?M")
proof -
  have pos: "positive M f"
    by (metis oms outer_measure_space_def)
  have alg: "algebra ?M"
    using lambda_system_algebra [of f, OF pos]
    by (simp add: algebra_iff_Un)
  then
  have "sigma_algebra ?M"
    using lambda_system_caratheodory [OF oms]
    by (simp add: sigma_algebra_disjoint_iff)
  moreover
  have "measure_space_axioms ?M"
    using pos lambda_system_caratheodory [OF oms]
    by (simp add: measure_space_axioms_def positive_def lambda_system_sets
                  countably_additive_def o_def)
  ultimately
  show ?thesis
    by (simp add: measure_space_def)
qed

lemma (in ring_of_sets) additive_increasing:
  assumes posf: "positive M f" and addf: "additive M f"
  shows "increasing M f"
proof (auto simp add: increasing_def)
  fix x y
  assume xy: "x \<in> sets M" "y \<in> sets M" "x \<subseteq> y"
  then have "y - x \<in> sets M" by auto
  then have "0 \<le> f (y-x)" using posf[unfolded positive_def] by auto
  then have "f x + 0 \<le> f x + f (y-x)" by (intro add_left_mono) auto
  also have "... = f (x \<union> (y-x))" using addf
    by (auto simp add: additive_def) (metis Diff_disjoint Un_Diff_cancel Diff xy(1,2))
  also have "... = f y"
    by (metis Un_Diff_cancel Un_absorb1 xy(3))
  finally show "f x \<le> f y" by simp
qed

lemma (in ring_of_sets) countably_additive_additive:
  assumes posf: "positive M f" and ca: "countably_additive M f"
  shows "additive M f"
proof (auto simp add: additive_def)
  fix x y
  assume x: "x \<in> sets M" and y: "y \<in> sets M" and "x \<inter> y = {}"
  hence "disjoint_family (binaryset x y)"
    by (auto simp add: disjoint_family_on_def binaryset_def)
  hence "range (binaryset x y) \<subseteq> sets M \<longrightarrow>
         (\<Union>i. binaryset x y i) \<in> sets M \<longrightarrow>
         f (\<Union>i. binaryset x y i) = (\<Sum> n. f (binaryset x y n))"
    using ca
    by (simp add: countably_additive_def)
  hence "{x,y,{}} \<subseteq> sets M \<longrightarrow> x \<union> y \<in> sets M \<longrightarrow>
         f (x \<union> y) = (\<Sum>n. f (binaryset x y n))"
    by (simp add: range_binaryset_eq UN_binaryset_eq)
  thus "f (x \<union> y) = f x + f y" using posf x y
    by (auto simp add: Un suminf_binaryset_eq positive_def)
qed

lemma inf_measure_nonempty:
  assumes f: "positive M f" and b: "b \<in> sets M" and a: "a \<subseteq> b" "{} \<in> sets M"
  shows "f b \<in> measure_set M f a"
proof -
  let ?A = "\<lambda>i::nat. (if i = 0 then b else {})"
  have "(\<Sum>i. f (?A i)) = (\<Sum>i<1::nat. f (?A i))"
    by (rule suminf_finite) (simp add: f[unfolded positive_def])
  also have "... = f b"
    by simp
  finally show ?thesis using assms
    by (auto intro!: exI [of _ ?A]
             simp: measure_set_def disjoint_family_on_def split_if_mem2 comp_def)
qed

lemma (in ring_of_sets) inf_measure_agrees:
  assumes posf: "positive M f" and ca: "countably_additive M f"
      and s: "s \<in> sets M"
  shows "Inf (measure_set M f s) = f s"
  unfolding Inf_ereal_def
proof (safe intro!: Greatest_equality)
  fix z
  assume z: "z \<in> measure_set M f s"
  from this obtain A where
    A: "range A \<subseteq> sets M" and disj: "disjoint_family A"
    and "s \<subseteq> (\<Union>x. A x)" and si: "(\<Sum>i. f (A i)) = z"
    by (auto simp add: measure_set_def comp_def)
  hence seq: "s = (\<Union>i. A i \<inter> s)" by blast
  have inc: "increasing M f"
    by (metis additive_increasing ca countably_additive_additive posf)
  have sums: "(\<Sum>i. f (A i \<inter> s)) = f (\<Union>i. A i \<inter> s)"
    proof (rule ca[unfolded countably_additive_def, rule_format])
      show "range (\<lambda>n. A n \<inter> s) \<subseteq> sets M" using A s
        by blast
      show "disjoint_family (\<lambda>n. A n \<inter> s)" using disj
        by (auto simp add: disjoint_family_on_def)
      show "(\<Union>i. A i \<inter> s) \<in> sets M" using A s
        by (metis UN_extend_simps(4) s seq)
    qed
  hence "f s = (\<Sum>i. f (A i \<inter> s))"
    using seq [symmetric] by (simp add: sums_iff)
  also have "... \<le> (\<Sum>i. f (A i))"
    proof (rule suminf_le_pos)
      fix n show "f (A n \<inter> s) \<le> f (A n)" using A s
        by (force intro: increasingD [OF inc])
      fix N have "A N \<inter> s \<in> sets M"  using A s by auto
      then show "0 \<le> f (A N \<inter> s)" using posf unfolding positive_def by auto
    qed
  also have "... = z" by (rule si)
  finally show "f s \<le> z" .
next
  fix y
  assume y: "\<forall>u \<in> measure_set M f s. y \<le> u"
  thus "y \<le> f s"
    by (blast intro: inf_measure_nonempty [of _ f, OF posf s subset_refl])
qed

lemma measure_set_pos:
  assumes posf: "positive M f" "r \<in> measure_set M f X"
  shows "0 \<le> r"
proof -
  obtain A where "range A \<subseteq> sets M" and r: "r = (\<Sum>i. f (A i))"
    using `r \<in> measure_set M f X` unfolding measure_set_def by auto
  then show "0 \<le> r" using posf unfolding r positive_def
    by (intro suminf_0_le) auto
qed

lemma inf_measure_pos:
  assumes posf: "positive M f"
  shows "0 \<le> Inf (measure_set M f X)"
proof (rule complete_lattice_class.Inf_greatest)
  fix r assume "r \<in> measure_set M f X" with posf show "0 \<le> r"
    by (rule measure_set_pos)
qed

lemma inf_measure_empty:
  assumes posf: "positive M f" and "{} \<in> sets M"
  shows "Inf (measure_set M f {}) = 0"
proof (rule antisym)
  show "Inf (measure_set M f {}) \<le> 0"
    by (metis complete_lattice_class.Inf_lower `{} \<in> sets M`
              inf_measure_nonempty[OF posf] subset_refl posf[unfolded positive_def])
qed (rule inf_measure_pos[OF posf])

lemma (in ring_of_sets) inf_measure_positive:
  assumes p: "positive M f" and "{} \<in> sets M"
  shows "positive M (\<lambda>x. Inf (measure_set M f x))"
proof (unfold positive_def, intro conjI ballI)
  show "Inf (measure_set M f {}) = 0" using inf_measure_empty[OF assms] by auto
  fix A assume "A \<in> sets M"
qed (rule inf_measure_pos[OF p])

lemma (in ring_of_sets) inf_measure_increasing:
  assumes posf: "positive M f"
  shows "increasing \<lparr> space = space M, sets = Pow (space M) \<rparr>
                    (\<lambda>x. Inf (measure_set M f x))"
apply (clarsimp simp add: increasing_def)
apply (rule complete_lattice_class.Inf_greatest)
apply (rule complete_lattice_class.Inf_lower)
apply (clarsimp simp add: measure_set_def, rule_tac x=A in exI, blast)
done

lemma (in ring_of_sets) inf_measure_le:
  assumes posf: "positive M f" and inc: "increasing M f"
      and x: "x \<in> {r . \<exists>A. range A \<subseteq> sets M \<and> s \<subseteq> (\<Union>i. A i) \<and> (\<Sum>i. f (A i)) = r}"
  shows "Inf (measure_set M f s) \<le> x"
proof -
  obtain A where A: "range A \<subseteq> sets M" and ss: "s \<subseteq> (\<Union>i. A i)"
             and xeq: "(\<Sum>i. f (A i)) = x"
    using x by auto
  have dA: "range (disjointed A) \<subseteq> sets M"
    by (metis A range_disjointed_sets)
  have "\<forall>n. f (disjointed A n) \<le> f (A n)"
    by (metis increasingD [OF inc] UNIV_I dA image_subset_iff disjointed_subset A comp_def)
  moreover have "\<forall>i. 0 \<le> f (disjointed A i)"
    using posf dA unfolding positive_def by auto
  ultimately have sda: "(\<Sum>i. f (disjointed A i)) \<le> (\<Sum>i. f (A i))"
    by (blast intro!: suminf_le_pos)
  hence ley: "(\<Sum>i. f (disjointed A i)) \<le> x"
    by (metis xeq)
  hence y: "(\<Sum>i. f (disjointed A i)) \<in> measure_set M f s"
    apply (auto simp add: measure_set_def)
    apply (rule_tac x="disjointed A" in exI)
    apply (simp add: disjoint_family_disjointed UN_disjointed_eq ss dA comp_def)
    done
  show ?thesis
    by (blast intro: y order_trans [OF _ ley] posf complete_lattice_class.Inf_lower)
qed

lemma (in ring_of_sets) inf_measure_close:
  fixes e :: ereal
  assumes posf: "positive M f" and e: "0 < e" and ss: "s \<subseteq> (space M)" and "Inf (measure_set M f s) \<noteq> \<infinity>"
  shows "\<exists>A. range A \<subseteq> sets M \<and> disjoint_family A \<and> s \<subseteq> (\<Union>i. A i) \<and>
               (\<Sum>i. f (A i)) \<le> Inf (measure_set M f s) + e"
proof -
  from `Inf (measure_set M f s) \<noteq> \<infinity>` have fin: "\<bar>Inf (measure_set M f s)\<bar> \<noteq> \<infinity>"
    using inf_measure_pos[OF posf, of s] by auto
  obtain l where "l \<in> measure_set M f s" "l \<le> Inf (measure_set M f s) + e"
    using Inf_ereal_close[OF fin e] by auto
  thus ?thesis
    by (auto intro!: exI[of _ l] simp: measure_set_def comp_def)
qed

lemma (in ring_of_sets) inf_measure_countably_subadditive:
  assumes posf: "positive M f" and inc: "increasing M f"
  shows "countably_subadditive (| space = space M, sets = Pow (space M) |)
                  (\<lambda>x. Inf (measure_set M f x))"
proof (simp add: countably_subadditive_def, safe)
  fix A :: "nat \<Rightarrow> 'a set"
  let ?outer = "\<lambda>B. Inf (measure_set M f B)"
  assume A: "range A \<subseteq> Pow (space M)"
     and disj: "disjoint_family A"
     and sb: "(\<Union>i. A i) \<subseteq> space M"

  { fix e :: ereal assume e: "0 < e" and "\<forall>i. ?outer (A i) \<noteq> \<infinity>"
    hence "\<exists>BB. \<forall>n. range (BB n) \<subseteq> sets M \<and> disjoint_family (BB n) \<and>
        A n \<subseteq> (\<Union>i. BB n i) \<and> (\<Sum>i. f (BB n i)) \<le> ?outer (A n) + e * (1/2)^(Suc n)"
      apply (safe intro!: choice inf_measure_close [of f, OF posf])
      using e sb by (auto simp: ereal_zero_less_0_iff one_ereal_def)
    then obtain BB
      where BB: "\<And>n. (range (BB n) \<subseteq> sets M)"
      and disjBB: "\<And>n. disjoint_family (BB n)"
      and sbBB: "\<And>n. A n \<subseteq> (\<Union>i. BB n i)"
      and BBle: "\<And>n. (\<Sum>i. f (BB n i)) \<le> ?outer (A n) + e * (1/2)^(Suc n)"
      by auto blast
    have sll: "(\<Sum>n. \<Sum>i. (f (BB n i))) \<le> (\<Sum>n. ?outer (A n)) + e"
    proof -
      have sum_eq_1: "(\<Sum>n. e*(1/2) ^ Suc n) = e"
        using suminf_half_series_ereal e
        by (simp add: ereal_zero_le_0_iff zero_le_divide_ereal suminf_cmult_ereal)
      have "\<And>n i. 0 \<le> f (BB n i)" using posf[unfolded positive_def] BB by auto
      then have "\<And>n. 0 \<le> (\<Sum>i. f (BB n i))" by (rule suminf_0_le)
      then have "(\<Sum>n. \<Sum>i. (f (BB n i))) \<le> (\<Sum>n. ?outer (A n) + e*(1/2) ^ Suc n)"
        by (rule suminf_le_pos[OF BBle])
      also have "... = (\<Sum>n. ?outer (A n)) + e"
        using sum_eq_1 inf_measure_pos[OF posf] e
        by (subst suminf_add_ereal) (auto simp add: ereal_zero_le_0_iff)
      finally show ?thesis .
    qed
    def C \<equiv> "(split BB) o prod_decode"
    have C: "!!n. C n \<in> sets M"
      apply (rule_tac p="prod_decode n" in PairE)
      apply (simp add: C_def)
      apply (metis BB subsetD rangeI)
      done
    have sbC: "(\<Union>i. A i) \<subseteq> (\<Union>i. C i)"
    proof (auto simp add: C_def)
      fix x i
      assume x: "x \<in> A i"
      with sbBB [of i] obtain j where "x \<in> BB i j"
        by blast
      thus "\<exists>i. x \<in> split BB (prod_decode i)"
        by (metis prod_encode_inverse prod.cases)
    qed
    have "(f \<circ> C) = (f \<circ> (\<lambda>(x, y). BB x y)) \<circ> prod_decode"
      by (rule ext)  (auto simp add: C_def)
    moreover have "suminf ... = (\<Sum>n. \<Sum>i. f (BB n i))" using BBle
      using BB posf[unfolded positive_def]
      by (force intro!: suminf_ereal_2dimen simp: o_def)
    ultimately have Csums: "(\<Sum>i. f (C i)) = (\<Sum>n. \<Sum>i. f (BB n i))" by (simp add: o_def)
    have "?outer (\<Union>i. A i) \<le> (\<Sum>n. \<Sum>i. f (BB n i))"
      apply (rule inf_measure_le [OF posf(1) inc], auto)
      apply (rule_tac x="C" in exI)
      apply (auto simp add: C sbC Csums)
      done
    also have "... \<le> (\<Sum>n. ?outer (A n)) + e" using sll
      by blast
    finally have "?outer (\<Union>i. A i) \<le> (\<Sum>n. ?outer (A n)) + e" . }
  note for_finite_Inf = this

  show "?outer (\<Union>i. A i) \<le> (\<Sum>n. ?outer (A n))"
  proof cases
    assume "\<forall>i. ?outer (A i) \<noteq> \<infinity>"
    with for_finite_Inf show ?thesis
      by (intro ereal_le_epsilon) auto
  next
    assume "\<not> (\<forall>i. ?outer (A i) \<noteq> \<infinity>)"
    then have "\<exists>i. ?outer (A i) = \<infinity>"
      by auto
    then have "(\<Sum>n. ?outer (A n)) = \<infinity>"
      using suminf_PInfty[OF inf_measure_pos, OF posf]
      by metis
    then show ?thesis by simp
  qed
qed

lemma (in ring_of_sets) inf_measure_outer:
  "\<lbrakk> positive M f ; increasing M f \<rbrakk>
   \<Longrightarrow> outer_measure_space \<lparr> space = space M, sets = Pow (space M) \<rparr>
                          (\<lambda>x. Inf (measure_set M f x))"
  using inf_measure_pos[of M f]
  by (simp add: outer_measure_space_def inf_measure_empty
                inf_measure_increasing inf_measure_countably_subadditive positive_def)

lemma (in ring_of_sets) algebra_subset_lambda_system:
  assumes posf: "positive M f" and inc: "increasing M f"
      and add: "additive M f"
  shows "sets M \<subseteq> lambda_system \<lparr> space = space M, sets = Pow (space M) \<rparr>
                                (\<lambda>x. Inf (measure_set M f x))"
proof (auto dest: sets_into_space
            simp add: algebra.lambda_system_eq [OF algebra_Pow])
  fix x s
  assume x: "x \<in> sets M"
     and s: "s \<subseteq> space M"
  have [simp]: "!!x. x \<in> sets M \<Longrightarrow> s \<inter> (space M - x) = s-x" using s
    by blast
  have "Inf (measure_set M f (s\<inter>x)) + Inf (measure_set M f (s-x))
        \<le> Inf (measure_set M f s)"
  proof cases
    assume "Inf (measure_set M f s) = \<infinity>" then show ?thesis by simp
  next
    assume fin: "Inf (measure_set M f s) \<noteq> \<infinity>"
    then have "measure_set M f s \<noteq> {}"
      by (auto simp: top_ereal_def)
    show ?thesis
    proof (rule complete_lattice_class.Inf_greatest)
      fix r assume "r \<in> measure_set M f s"
      then obtain A where A: "disjoint_family A" "range A \<subseteq> sets M" "s \<subseteq> (\<Union>i. A i)"
        and r: "r = (\<Sum>i. f (A i))" unfolding measure_set_def by auto
      have "Inf (measure_set M f (s \<inter> x)) \<le> (\<Sum>i. f (A i \<inter> x))"
        unfolding measure_set_def
      proof (safe intro!: complete_lattice_class.Inf_lower exI[of _ "\<lambda>i. A i \<inter> x"])
        from A(1) show "disjoint_family (\<lambda>i. A i \<inter> x)"
          by (rule disjoint_family_on_bisimulation) auto
      qed (insert x A, auto)
      moreover
      have "Inf (measure_set M f (s - x)) \<le> (\<Sum>i. f (A i - x))"
        unfolding measure_set_def
      proof (safe intro!: complete_lattice_class.Inf_lower exI[of _ "\<lambda>i. A i - x"])
        from A(1) show "disjoint_family (\<lambda>i. A i - x)"
          by (rule disjoint_family_on_bisimulation) auto
      qed (insert x A, auto)
      ultimately have "Inf (measure_set M f (s \<inter> x)) + Inf (measure_set M f (s - x)) \<le>
          (\<Sum>i. f (A i \<inter> x)) + (\<Sum>i. f (A i - x))" by (rule add_mono)
      also have "\<dots> = (\<Sum>i. f (A i \<inter> x) + f (A i - x))"
        using A(2) x posf by (subst suminf_add_ereal) (auto simp: positive_def)
      also have "\<dots> = (\<Sum>i. f (A i))"
        using A x
        by (subst add[THEN additiveD, symmetric])
           (auto intro!: arg_cong[where f=suminf] arg_cong[where f=f])
      finally show "Inf (measure_set M f (s \<inter> x)) + Inf (measure_set M f (s - x)) \<le> r"
        using r by simp
    qed
  qed
  moreover
  have "Inf (measure_set M f s)
       \<le> Inf (measure_set M f (s\<inter>x)) + Inf (measure_set M f (s-x))"
  proof -
    have "Inf (measure_set M f s) = Inf (measure_set M f ((s\<inter>x) \<union> (s-x)))"
      by (metis Un_Diff_Int Un_commute)
    also have "... \<le> Inf (measure_set M f (s\<inter>x)) + Inf (measure_set M f (s-x))"
      apply (rule subadditiveD)
      apply (rule ring_of_sets.countably_subadditive_subadditive [OF ring_of_sets_Pow])
      apply (simp add: positive_def inf_measure_empty[OF posf] inf_measure_pos[OF posf])
      apply (rule inf_measure_countably_subadditive)
      using s by (auto intro!: posf inc)
    finally show ?thesis .
  qed
  ultimately
  show "Inf (measure_set M f (s\<inter>x)) + Inf (measure_set M f (s-x))
        = Inf (measure_set M f s)"
    by (rule order_antisym)
qed

lemma measure_down:
  "measure_space N \<Longrightarrow> sigma_algebra M \<Longrightarrow> sets M \<subseteq> sets N \<Longrightarrow> measure N = measure M \<Longrightarrow> measure_space M"
  by (simp add: measure_space_def measure_space_axioms_def positive_def
                countably_additive_def)
     blast

theorem (in ring_of_sets) caratheodory:
  assumes posf: "positive M f" and ca: "countably_additive M f"
  shows "\<exists>\<mu> :: 'a set \<Rightarrow> ereal. (\<forall>s \<in> sets M. \<mu> s = f s) \<and>
            measure_space \<lparr> space = space M, sets = sets (sigma M), measure = \<mu> \<rparr>"
proof -
  have inc: "increasing M f"
    by (metis additive_increasing ca countably_additive_additive posf)
  let ?infm = "(\<lambda>x. Inf (measure_set M f x))"
  def ls \<equiv> "lambda_system (|space = space M, sets = Pow (space M)|) ?infm"
  have mls: "measure_space \<lparr>space = space M, sets = ls, measure = ?infm\<rparr>"
    using sigma_algebra.caratheodory_lemma
            [OF sigma_algebra_Pow  inf_measure_outer [OF posf inc]]
    by (simp add: ls_def)
  hence sls: "sigma_algebra (|space = space M, sets = ls, measure = ?infm|)"
    by (simp add: measure_space_def)
  have "sets M \<subseteq> ls"
    by (simp add: ls_def)
       (metis ca posf inc countably_additive_additive algebra_subset_lambda_system)
  hence sgs_sb: "sigma_sets (space M) (sets M) \<subseteq> ls"
    using sigma_algebra.sigma_sets_subset [OF sls, of "sets M"]
    by simp
  have "measure_space \<lparr> space = space M, sets = sets (sigma M), measure = ?infm \<rparr>"
    unfolding sigma_def
    by (rule measure_down [OF mls], rule sigma_algebra_sigma_sets)
       (simp_all add: sgs_sb space_closed)
  thus ?thesis using inf_measure_agrees [OF posf ca]
    by (intro exI[of _ ?infm]) auto
qed

subsubsection {*Alternative instances of caratheodory*}

lemma (in ring_of_sets) countably_additive_iff_continuous_from_below:
  assumes f: "positive M f" "additive M f"
  shows "countably_additive M f \<longleftrightarrow>
    (\<forall>A. range A \<subseteq> sets M \<longrightarrow> incseq A \<longrightarrow> (\<Union>i. A i) \<in> sets M \<longrightarrow> (\<lambda>i. f (A i)) ----> f (\<Union>i. A i))"
  unfolding countably_additive_def
proof safe
  assume count_sum: "\<forall>A. range A \<subseteq> sets M \<longrightarrow> disjoint_family A \<longrightarrow> UNION UNIV A \<in> sets M \<longrightarrow> (\<Sum>i. f (A i)) = f (UNION UNIV A)"
  fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> sets M" "incseq A" "(\<Union>i. A i) \<in> sets M"
  then have dA: "range (disjointed A) \<subseteq> sets M" by (auto simp: range_disjointed_sets)
  with count_sum[THEN spec, of "disjointed A"] A(3)
  have f_UN: "(\<Sum>i. f (disjointed A i)) = f (\<Union>i. A i)"
    by (auto simp: UN_disjointed_eq disjoint_family_disjointed)
  moreover have "(\<lambda>n. (\<Sum>i=0..<n. f (disjointed A i))) ----> (\<Sum>i. f (disjointed A i))"
    using f(1)[unfolded positive_def] dA
    by (auto intro!: summable_sumr_LIMSEQ_suminf summable_ereal_pos)
  from LIMSEQ_Suc[OF this]
  have "(\<lambda>n. (\<Sum>i\<le>n. f (disjointed A i))) ----> (\<Sum>i. f (disjointed A i))"
    unfolding atLeastLessThanSuc_atLeastAtMost atLeast0AtMost .
  moreover have "\<And>n. (\<Sum>i\<le>n. f (disjointed A i)) = f (A n)"
    using disjointed_additive[OF f A(1,2)] .
  ultimately show "(\<lambda>i. f (A i)) ----> f (\<Union>i. A i)" by simp
next
  assume cont: "\<forall>A. range A \<subseteq> sets M \<longrightarrow> incseq A \<longrightarrow> (\<Union>i. A i) \<in> sets M \<longrightarrow> (\<lambda>i. f (A i)) ----> f (\<Union>i. A i)"
  fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> sets M" "disjoint_family A" "(\<Union>i. A i) \<in> sets M"
  have *: "(\<Union>n. (\<Union>i\<le>n. A i)) = (\<Union>i. A i)" by auto
  have "(\<lambda>n. f (\<Union>i\<le>n. A i)) ----> f (\<Union>i. A i)"
  proof (unfold *[symmetric], intro cont[rule_format])
    show "range (\<lambda>i. \<Union> i\<le>i. A i) \<subseteq> sets M" "(\<Union>i. \<Union> i\<le>i. A i) \<in> sets M"
      using A * by auto
  qed (force intro!: incseq_SucI)
  moreover have "\<And>n. f (\<Union>i\<le>n. A i) = (\<Sum>i\<le>n. f (A i))"
    using A
    by (intro additive_sum[OF f, of _ A, symmetric])
       (auto intro: disjoint_family_on_mono[where B=UNIV])
  ultimately
  have "(\<lambda>i. f (A i)) sums f (\<Union>i. A i)"
    unfolding sums_def2 by simp
  from sums_unique[OF this]
  show "(\<Sum>i. f (A i)) = f (\<Union>i. A i)" by simp
qed

lemma (in ring_of_sets) continuous_from_above_iff_empty_continuous:
  assumes f: "positive M f" "additive M f"
  shows "(\<forall>A. range A \<subseteq> sets M \<longrightarrow> decseq A \<longrightarrow> (\<Inter>i. A i) \<in> sets M \<longrightarrow> (\<forall>i. f (A i) \<noteq> \<infinity>) \<longrightarrow> (\<lambda>i. f (A i)) ----> f (\<Inter>i. A i))
     \<longleftrightarrow> (\<forall>A. range A \<subseteq> sets M \<longrightarrow> decseq A \<longrightarrow> (\<Inter>i. A i) = {} \<longrightarrow> (\<forall>i. f (A i) \<noteq> \<infinity>) \<longrightarrow> (\<lambda>i. f (A i)) ----> 0)"
proof safe
  assume cont: "(\<forall>A. range A \<subseteq> sets M \<longrightarrow> decseq A \<longrightarrow> (\<Inter>i. A i) \<in> sets M \<longrightarrow> (\<forall>i. f (A i) \<noteq> \<infinity>) \<longrightarrow> (\<lambda>i. f (A i)) ----> f (\<Inter>i. A i))"
  fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> sets M" "decseq A" "(\<Inter>i. A i) = {}" "\<forall>i. f (A i) \<noteq> \<infinity>"
  with cont[THEN spec, of A] show "(\<lambda>i. f (A i)) ----> 0"
    using `positive M f`[unfolded positive_def] by auto
next
  assume cont: "\<forall>A. range A \<subseteq> sets M \<longrightarrow> decseq A \<longrightarrow> (\<Inter>i. A i) = {} \<longrightarrow> (\<forall>i. f (A i) \<noteq> \<infinity>) \<longrightarrow> (\<lambda>i. f (A i)) ----> 0"
  fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> sets M" "decseq A" "(\<Inter>i. A i) \<in> sets M" "\<forall>i. f (A i) \<noteq> \<infinity>"

  have f_mono: "\<And>a b. a \<in> sets M \<Longrightarrow> b \<in> sets M \<Longrightarrow> a \<subseteq> b \<Longrightarrow> f a \<le> f b"
    using additive_increasing[OF f] unfolding increasing_def by simp

  have decseq_fA: "decseq (\<lambda>i. f (A i))"
    using A by (auto simp: decseq_def intro!: f_mono)
  have decseq: "decseq (\<lambda>i. A i - (\<Inter>i. A i))"
    using A by (auto simp: decseq_def)
  then have decseq_f: "decseq (\<lambda>i. f (A i - (\<Inter>i. A i)))"
    using A unfolding decseq_def by (auto intro!: f_mono Diff)
  have "f (\<Inter>x. A x) \<le> f (A 0)"
    using A by (auto intro!: f_mono)
  then have f_Int_fin: "f (\<Inter>x. A x) \<noteq> \<infinity>"
    using A by auto
  { fix i
    have "f (A i - (\<Inter>i. A i)) \<le> f (A i)" using A by (auto intro!: f_mono)
    then have "f (A i - (\<Inter>i. A i)) \<noteq> \<infinity>"
      using A by auto }
  note f_fin = this
  have "(\<lambda>i. f (A i - (\<Inter>i. A i))) ----> 0"
  proof (intro cont[rule_format, OF _ decseq _ f_fin])
    show "range (\<lambda>i. A i - (\<Inter>i. A i)) \<subseteq> sets M" "(\<Inter>i. A i - (\<Inter>i. A i)) = {}"
      using A by auto
  qed
  from INF_Lim_ereal[OF decseq_f this]
  have "(INF n. f (A n - (\<Inter>i. A i))) = 0" .
  moreover have "(INF n. f (\<Inter>i. A i)) = f (\<Inter>i. A i)"
    by auto
  ultimately have "(INF n. f (A n - (\<Inter>i. A i)) + f (\<Inter>i. A i)) = 0 + f (\<Inter>i. A i)"
    using A(4) f_fin f_Int_fin
    by (subst INFI_ereal_add) (auto simp: decseq_f)
  moreover {
    fix n
    have "f (A n - (\<Inter>i. A i)) + f (\<Inter>i. A i) = f ((A n - (\<Inter>i. A i)) \<union> (\<Inter>i. A i))"
      using A by (subst f(2)[THEN additiveD]) auto
    also have "(A n - (\<Inter>i. A i)) \<union> (\<Inter>i. A i) = A n"
      by auto
    finally have "f (A n - (\<Inter>i. A i)) + f (\<Inter>i. A i) = f (A n)" . }
  ultimately have "(INF n. f (A n)) = f (\<Inter>i. A i)"
    by simp
  with LIMSEQ_ereal_INFI[OF decseq_fA]
  show "(\<lambda>i. f (A i)) ----> f (\<Inter>i. A i)" by simp
qed

lemma positiveD1: "positive M f \<Longrightarrow> f {} = 0" by (auto simp: positive_def)
lemma positiveD2: "positive M f \<Longrightarrow> A \<in> sets M \<Longrightarrow> 0 \<le> f A" by (auto simp: positive_def)

lemma (in ring_of_sets) empty_continuous_imp_continuous_from_below:
  assumes f: "positive M f" "additive M f" "\<forall>A\<in>sets M. f A \<noteq> \<infinity>"
  assumes cont: "\<forall>A. range A \<subseteq> sets M \<longrightarrow> decseq A \<longrightarrow> (\<Inter>i. A i) = {} \<longrightarrow> (\<lambda>i. f (A i)) ----> 0"
  assumes A: "range A \<subseteq> sets M" "incseq A" "(\<Union>i. A i) \<in> sets M"
  shows "(\<lambda>i. f (A i)) ----> f (\<Union>i. A i)"
proof -
  have "\<forall>A\<in>sets M. \<exists>x. f A = ereal x"
  proof
    fix A assume "A \<in> sets M" with f show "\<exists>x. f A = ereal x"
      unfolding positive_def by (cases "f A") auto
  qed
  from bchoice[OF this] guess f' .. note f' = this[rule_format]
  from A have "(\<lambda>i. f ((\<Union>i. A i) - A i)) ----> 0"
    by (intro cont[rule_format]) (auto simp: decseq_def incseq_def)
  moreover
  { fix i
    have "f ((\<Union>i. A i) - A i) + f (A i) = f ((\<Union>i. A i) - A i \<union> A i)"
      using A by (intro f(2)[THEN additiveD, symmetric]) auto
    also have "(\<Union>i. A i) - A i \<union> A i = (\<Union>i. A i)"
      by auto
    finally have "f' (\<Union>i. A i) - f' (A i) = f' ((\<Union>i. A i) - A i)"
      using A by (subst (asm) (1 2 3) f') auto
    then have "f ((\<Union>i. A i) - A i) = ereal (f' (\<Union>i. A i) - f' (A i))"
      using A f' by auto }
  ultimately have "(\<lambda>i. f' (\<Union>i. A i) - f' (A i)) ----> 0"
    by (simp add: zero_ereal_def)
  then have "(\<lambda>i. f' (A i)) ----> f' (\<Union>i. A i)"
    by (rule LIMSEQ_diff_approach_zero2[OF tendsto_const])
  then show "(\<lambda>i. f (A i)) ----> f (\<Union>i. A i)"
    using A by (subst (1 2) f') auto
qed

lemma (in ring_of_sets) empty_continuous_imp_countably_additive:
  assumes f: "positive M f" "additive M f" and fin: "\<forall>A\<in>sets M. f A \<noteq> \<infinity>"
  assumes cont: "\<And>A. range A \<subseteq> sets M \<Longrightarrow> decseq A \<Longrightarrow> (\<Inter>i. A i) = {} \<Longrightarrow> (\<lambda>i. f (A i)) ----> 0"
  shows "countably_additive M f"
  using countably_additive_iff_continuous_from_below[OF f]
  using empty_continuous_imp_continuous_from_below[OF f fin] cont
  by blast

lemma (in ring_of_sets) caratheodory_empty_continuous:
  assumes f: "positive M f" "additive M f" and fin: "\<And>A. A \<in> sets M \<Longrightarrow> f A \<noteq> \<infinity>"
  assumes cont: "\<And>A. range A \<subseteq> sets M \<Longrightarrow> decseq A \<Longrightarrow> (\<Inter>i. A i) = {} \<Longrightarrow> (\<lambda>i. f (A i)) ----> 0"
  shows "\<exists>\<mu> :: 'a set \<Rightarrow> ereal. (\<forall>s \<in> sets M. \<mu> s = f s) \<and>
            measure_space \<lparr> space = space M, sets = sets (sigma M), measure = \<mu> \<rparr>"
proof (intro caratheodory empty_continuous_imp_countably_additive f)
  show "\<forall>A\<in>sets M. f A \<noteq> \<infinity>" using fin by auto
qed (rule cont)

end
