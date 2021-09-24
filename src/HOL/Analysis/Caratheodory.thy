(*  Title:      HOL/Analysis/Caratheodory.thy
    Author:     Lawrence C Paulson
    Author:     Johannes Hölzl, TU München
*)

section \<open>Caratheodory Extension Theorem\<close>

theory Caratheodory
imports Measure_Space
begin

text \<open>
  Originally from the Hurd/Coble measure theory development, translated by Lawrence Paulson.
\<close>

lemma suminf_ennreal_2dimen:
  fixes f:: "nat \<times> nat \<Rightarrow> ennreal"
  assumes "\<And>m. g m = (\<Sum>n. f (m,n))"
  shows "(\<Sum>i. f (prod_decode i)) = suminf g"
proof -
  have g_def: "g = (\<lambda>m. (\<Sum>n. f (m,n)))"
    using assms by (simp add: fun_eq_iff)
  have reindex: "\<And>B. (\<Sum>x\<in>B. f (prod_decode x)) = sum f (prod_decode ` B)"
    by (simp add: sum.reindex[OF inj_prod_decode] comp_def)
  have "(SUP n. \<Sum>i<n. f (prod_decode i)) = (SUP p \<in> UNIV \<times> UNIV. \<Sum>i<fst p. \<Sum>n<snd p. f (i, n))"
  proof (intro SUP_eq; clarsimp simp: sum.cartesian_product reindex)
    fix n
    let ?M = "\<lambda>f. Suc (Max (f ` prod_decode ` {..<n}))"
    { fix a b x assume "x < n" and [symmetric]: "(a, b) = prod_decode x"
      then have "a < ?M fst" "b < ?M snd"
        by (auto intro!: Max_ge le_imp_less_Suc image_eqI) }
    then have "sum f (prod_decode ` {..<n}) \<le> sum f ({..<?M fst} \<times> {..<?M snd})"
      by (auto intro!: sum_mono2)
    then show "\<exists>a b. sum f (prod_decode ` {..<n}) \<le> sum f ({..<a} \<times> {..<b})" by auto
  next
    fix a b
    let ?M = "prod_decode ` {..<Suc (Max (prod_encode ` ({..<a} \<times> {..<b})))}"
    { fix a' b' assume "a' < a" "b' < b" then have "(a', b') \<in> ?M"
        by (auto intro!: Max_ge le_imp_less_Suc image_eqI[where x="prod_encode (a', b')"]) }
    then have "sum f ({..<a} \<times> {..<b}) \<le> sum f ?M"
      by (auto intro!: sum_mono2)
    then show "\<exists>n. sum f ({..<a} \<times> {..<b}) \<le> sum f (prod_decode ` {..<n})"
      by auto
  qed
  also have "\<dots> = (SUP p. \<Sum>i<p. \<Sum>n. f (i, n))"
    unfolding suminf_sum[OF summableI, symmetric]
    by (simp add: suminf_eq_SUP SUP_pair sum.swap[of _ "{..< fst _}"])
  finally show ?thesis unfolding g_def
    by (simp add: suminf_eq_SUP)
qed

subsection \<open>Characterizations of Measures\<close>

definition\<^marker>\<open>tag important\<close> outer_measure_space where
  "outer_measure_space M f \<longleftrightarrow> positive M f \<and> increasing M f \<and> countably_subadditive M f"

subsubsection\<^marker>\<open>tag important\<close> \<open>Lambda Systems\<close>

definition\<^marker>\<open>tag important\<close> lambda_system :: "'a set \<Rightarrow> 'a set set \<Rightarrow> ('a set \<Rightarrow> ennreal) \<Rightarrow> 'a set set"
where
  "lambda_system \<Omega> M f = {l \<in> M. \<forall>x \<in> M. f (l \<inter> x) + f ((\<Omega> - l) \<inter> x) = f x}"

lemma (in algebra) lambda_system_eq:
  "lambda_system \<Omega> M f = {l \<in> M. \<forall>x \<in> M. f (x \<inter> l) + f (x - l) = f x}"
proof -
  have [simp]: "\<And>l x. l \<in> M \<Longrightarrow> x \<in> M \<Longrightarrow> (\<Omega> - l) \<inter> x = x - l"
    by (metis Int_Diff Int_absorb1 Int_commute sets_into_space)
  show ?thesis
    by (auto simp add: lambda_system_def) (metis Int_commute)+
qed

lemma (in algebra) lambda_system_empty: "positive M f \<Longrightarrow> {} \<in> lambda_system \<Omega> M f"
  by (auto simp add: positive_def lambda_system_eq)

lemma lambda_system_sets: "x \<in> lambda_system \<Omega> M f \<Longrightarrow> x \<in> M"
  by (simp add: lambda_system_def)

lemma (in algebra) lambda_system_Compl:
  fixes f:: "'a set \<Rightarrow> ennreal"
  assumes x: "x \<in> lambda_system \<Omega> M f"
  shows "\<Omega> - x \<in> lambda_system \<Omega> M f"
proof -
  have "x \<subseteq> \<Omega>"
    by (metis sets_into_space lambda_system_sets x)
  hence "\<Omega> - (\<Omega> - x) = x"
    by (metis double_diff equalityE)
  with x show ?thesis
    by (force simp add: lambda_system_def ac_simps)
qed

lemma (in algebra) lambda_system_Int:
  fixes f:: "'a set \<Rightarrow> ennreal"
  assumes xl: "x \<in> lambda_system \<Omega> M f" and yl: "y \<in> lambda_system \<Omega> M f"
  shows "x \<inter> y \<in> lambda_system \<Omega> M f"
proof -
  from xl yl show ?thesis
  proof (auto simp add: positive_def lambda_system_eq Int)
    fix u
    assume x: "x \<in> M" and y: "y \<in> M" and u: "u \<in> M"
       and fx: "\<forall>z\<in>M. f (z \<inter> x) + f (z - x) = f z"
       and fy: "\<forall>z\<in>M. f (z \<inter> y) + f (z - y) = f z"
    have "u - x \<inter> y \<in> M"
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
  fixes f:: "'a set \<Rightarrow> ennreal"
  assumes xl: "x \<in> lambda_system \<Omega> M f" and yl: "y \<in> lambda_system \<Omega> M f"
  shows "x \<union> y \<in> lambda_system \<Omega> M f"
proof -
  have "(\<Omega> - x) \<inter> (\<Omega> - y) \<in> M"
    by (metis Diff_Un Un compl_sets lambda_system_sets xl yl)
  moreover
  have "x \<union> y = \<Omega> - ((\<Omega> - x) \<inter> (\<Omega> - y))"
    by auto (metis subsetD lambda_system_sets sets_into_space xl yl)+
  ultimately show ?thesis
    by (metis lambda_system_Compl lambda_system_Int xl yl)
qed

lemma (in algebra) lambda_system_algebra:
  "positive M f \<Longrightarrow> algebra \<Omega> (lambda_system \<Omega> M f)"
  apply (auto simp add: algebra_iff_Un)
  apply (metis lambda_system_sets subsetD sets_into_space)
  apply (metis lambda_system_empty)
  apply (metis lambda_system_Compl)
  apply (metis lambda_system_Un)
  done

lemma (in algebra) lambda_system_strong_additive:
  assumes z: "z \<in> M" and disj: "x \<inter> y = {}"
      and xl: "x \<in> lambda_system \<Omega> M f" and yl: "y \<in> lambda_system \<Omega> M f"
  shows "f (z \<inter> (x \<union> y)) = f (z \<inter> x) + f (z \<inter> y)"
proof -
  have "z \<inter> x = (z \<inter> (x \<union> y)) \<inter> x" using disj by blast
  moreover
  have "z \<inter> y = (z \<inter> (x \<union> y)) - x" using disj by blast
  moreover
  have "(z \<inter> (x \<union> y)) \<in> M"
    by (metis Int Un lambda_system_sets xl yl z)
  ultimately show ?thesis using xl yl
    by (simp add: lambda_system_eq)
qed

lemma (in algebra) lambda_system_additive: "additive (lambda_system \<Omega> M f) f"
proof (auto simp add: additive_def)
  fix x and y
  assume disj: "x \<inter> y = {}"
     and xl: "x \<in> lambda_system \<Omega> M f" and yl: "y \<in> lambda_system \<Omega> M f"
  hence  "x \<in> M" "y \<in> M" by (blast intro: lambda_system_sets)+
  thus "f (x \<union> y) = f x + f y"
    using lambda_system_strong_additive [OF top disj xl yl]
    by (simp add: Un)
qed

lemma lambda_system_increasing: "increasing M f \<Longrightarrow> increasing (lambda_system \<Omega> M f) f"
  by (simp add: increasing_def lambda_system_def)

lemma lambda_system_positive: "positive M f \<Longrightarrow> positive (lambda_system \<Omega> M f) f"
  by (simp add: positive_def lambda_system_def)

lemma (in algebra) lambda_system_strong_sum:
  fixes A:: "nat \<Rightarrow> 'a set" and f :: "'a set \<Rightarrow> ennreal"
  assumes f: "positive M f" and a: "a \<in> M"
      and A: "range A \<subseteq> lambda_system \<Omega> M f"
      and disj: "disjoint_family A"
  shows  "(\<Sum>i = 0..<n. f (a \<inter>A i)) = f (a \<inter> (\<Union>i\<in>{0..<n}. A i))"
proof (induct n)
  case 0 show ?case using f by (simp add: positive_def)
next
  case (Suc n)
  have 2: "A n \<inter> \<Union> (A ` {0..<n}) = {}" using disj
    by (force simp add: disjoint_family_on_def neq_iff)
  have 3: "A n \<in> lambda_system \<Omega> M f" using A
    by blast
  interpret l: algebra \<Omega> "lambda_system \<Omega> M f"
    using f by (rule lambda_system_algebra)
  have 4: "\<Union> (A ` {0..<n}) \<in> lambda_system \<Omega> M f"
    using A l.UNION_in_sets by simp
  from Suc.hyps show ?case
    by (simp add: atLeastLessThanSuc lambda_system_strong_additive [OF a 2 3 4])
qed

proposition (in sigma_algebra) lambda_system_caratheodory:
  assumes oms: "outer_measure_space M f"
      and A: "range A \<subseteq> lambda_system \<Omega> M f"
      and disj: "disjoint_family A"
  shows  "(\<Union>i. A i) \<in> lambda_system \<Omega> M f \<and> (\<Sum>i. f (A i)) = f (\<Union>i. A i)"
proof -
  have pos: "positive M f" and inc: "increasing M f"
   and csa: "countably_subadditive M f"
    by (metis oms outer_measure_space_def)+
  have sa: "subadditive M f"
    by (metis countably_subadditive_subadditive csa pos)
  have A': "\<And>S. A`S \<subseteq> (lambda_system \<Omega> M f)" using A
    by auto
  interpret ls: algebra \<Omega> "lambda_system \<Omega> M f"
    using pos by (rule lambda_system_algebra)
  have A'': "range A \<subseteq> M"
     by (metis A image_subset_iff lambda_system_sets)

  have U_in: "(\<Union>i. A i) \<in> M"
    by (metis A'' countable_UN)
  have U_eq: "f (\<Union>i. A i) = (\<Sum>i. f (A i))"
  proof (rule antisym)
    show "f (\<Union>i. A i) \<le> (\<Sum>i. f (A i))"
      using csa[unfolded countably_subadditive_def] A'' disj U_in by auto
    have dis: "\<And>N. disjoint_family_on A {..<N}" by (intro disjoint_family_on_mono[OF _ disj]) auto
    show "(\<Sum>i. f (A i)) \<le> f (\<Union>i. A i)"
      using ls.additive_sum [OF lambda_system_positive[OF pos] lambda_system_additive _ A' dis] A''
      by (intro suminf_le_const[OF summableI]) (auto intro!: increasingD[OF inc] countable_UN)
  qed
  have "f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i)) = f a"
    if a [iff]: "a \<in> M" for a
  proof (rule antisym)
    have "range (\<lambda>i. a \<inter> A i) \<subseteq> M" using A''
      by blast
    moreover
    have "disjoint_family (\<lambda>i. a \<inter> A i)" using disj
      by (auto simp add: disjoint_family_on_def)
    moreover
    have "a \<inter> (\<Union>i. A i) \<in> M"
      by (metis Int U_in a)
    ultimately
    have "f (a \<inter> (\<Union>i. A i)) \<le> (\<Sum>i. f (a \<inter> A i))"
      using csa[unfolded countably_subadditive_def, rule_format, of "(\<lambda>i. a \<inter> A i)"]
      by (simp add: o_def)
    hence "f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i)) \<le> (\<Sum>i. f (a \<inter> A i)) + f (a - (\<Union>i. A i))"
      by (rule add_right_mono)
    also have "\<dots> \<le> f a"
    proof (intro ennreal_suminf_bound_add)
      fix n
      have UNION_in: "(\<Union>i\<in>{0..<n}. A i) \<in> M"
        by (metis A'' UNION_in_sets)
      have le_fa: "f (\<Union> (A ` {0..<n}) \<inter> a) \<le> f a" using A''
        by (blast intro: increasingD [OF inc] A'' UNION_in_sets)
      have ls: "(\<Union>i\<in>{0..<n}. A i) \<in> lambda_system \<Omega> M f"
        using ls.UNION_in_sets by (simp add: A)
      hence eq_fa: "f a = f (a \<inter> (\<Union>i\<in>{0..<n}. A i)) + f (a - (\<Union>i\<in>{0..<n}. A i))"
        by (simp add: lambda_system_eq UNION_in)
      have "f (a - (\<Union>i. A i)) \<le> f (a - (\<Union>i\<in>{0..<n}. A i))"
        by (blast intro: increasingD [OF inc] UNION_in U_in)
      thus "(\<Sum>i<n. f (a \<inter> A i)) + f (a - (\<Union>i. A i)) \<le> f a"
        by (simp add: lambda_system_strong_sum pos A disj eq_fa add_left_mono atLeast0LessThan[symmetric])
    qed
    finally show "f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i)) \<le> f a"
      by simp
  next
    have "f a \<le> f (a \<inter> (\<Union>i. A i) \<union> (a - (\<Union>i. A i)))"
      by (blast intro:  increasingD [OF inc] U_in)
    also have "... \<le>  f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i))"
      by (blast intro: subadditiveD [OF sa] U_in)
    finally show "f a \<le> f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i))" .
  qed
  thus  ?thesis
    by (simp add: lambda_system_eq sums_iff U_eq U_in)
qed

proposition (in sigma_algebra) caratheodory_lemma:
  assumes oms: "outer_measure_space M f"
  defines "L \<equiv> lambda_system \<Omega> M f"
  shows "measure_space \<Omega> L f"
proof -
  have pos: "positive M f"
    by (metis oms outer_measure_space_def)
  have alg: "algebra \<Omega> L"
    using lambda_system_algebra [of f, OF pos]
    by (simp add: algebra_iff_Un L_def)
  then
  have "sigma_algebra \<Omega> L"
    using lambda_system_caratheodory [OF oms]
    by (simp add: sigma_algebra_disjoint_iff L_def)
  moreover
  have "countably_additive L f" "positive L f"
    using pos lambda_system_caratheodory [OF oms]
    by (auto simp add: lambda_system_sets L_def countably_additive_def positive_def)
  ultimately
  show ?thesis
    using pos by (simp add: measure_space_def)
qed

definition\<^marker>\<open>tag important\<close> outer_measure :: "'a set set \<Rightarrow> ('a set \<Rightarrow> ennreal) \<Rightarrow> 'a set \<Rightarrow> ennreal" where
   "outer_measure M f X =
     (INF A\<in>{A. range A \<subseteq> M \<and> disjoint_family A \<and> X \<subseteq> (\<Union>i. A i)}. \<Sum>i. f (A i))"

lemma (in ring_of_sets) outer_measure_agrees:
  assumes posf: "positive M f" and ca: "countably_additive M f" and s: "s \<in> M"
  shows "outer_measure M f s = f s"
  unfolding outer_measure_def
proof (safe intro!: antisym INF_greatest)
  fix A :: "nat \<Rightarrow> 'a set" assume A: "range A \<subseteq> M" and dA: "disjoint_family A" and sA: "s \<subseteq> (\<Union>x. A x)"
  have inc: "increasing M f"
    by (metis additive_increasing ca countably_additive_additive posf)
  have "f s = f (\<Union>i. A i \<inter> s)"
    using sA by (auto simp: Int_absorb1)
  also have "\<dots> = (\<Sum>i. f (A i \<inter> s))"
    using sA dA A s
    by (intro ca[unfolded countably_additive_def, rule_format, symmetric])
       (auto simp: Int_absorb1 disjoint_family_on_def)
  also have "... \<le> (\<Sum>i. f (A i))"
    using A s by (auto intro!: suminf_le increasingD[OF inc])
  finally show "f s \<le> (\<Sum>i. f (A i))" .
next
  have "(\<Sum>i. f (if i = 0 then s else {})) \<le> f s"
    using positiveD1[OF posf] by (subst suminf_finite[of "{0}"]) auto
  with s show "(INF A\<in>{A. range A \<subseteq> M \<and> disjoint_family A \<and> s \<subseteq> \<Union>(A ` UNIV)}. \<Sum>i. f (A i)) \<le> f s"
    by (intro INF_lower2[of "\<lambda>i. if i = 0 then s else {}"])
       (auto simp: disjoint_family_on_def)
qed

lemma outer_measure_empty:
  "positive M f \<Longrightarrow> {} \<in> M \<Longrightarrow> outer_measure M f {} = 0"
  unfolding outer_measure_def
  by (intro antisym INF_lower2[of  "\<lambda>_. {}"]) (auto simp: disjoint_family_on_def positive_def)

lemma (in ring_of_sets) positive_outer_measure:
  assumes "positive M f" shows "positive (Pow \<Omega>) (outer_measure M f)"
  unfolding positive_def by (auto simp: assms outer_measure_empty)

lemma (in ring_of_sets) increasing_outer_measure: "increasing (Pow \<Omega>) (outer_measure M f)"
  by (force simp: increasing_def outer_measure_def intro!: INF_greatest intro: INF_lower)

lemma (in ring_of_sets) outer_measure_le:
  assumes pos: "positive M f" and inc: "increasing M f" and A: "range A \<subseteq> M" and X: "X \<subseteq> (\<Union>i. A i)"
  shows "outer_measure M f X \<le> (\<Sum>i. f (A i))"
  unfolding outer_measure_def
proof (safe intro!: INF_lower2[of "disjointed A"] del: subsetI)
  show dA: "range (disjointed A) \<subseteq> M"
    by (auto intro!: A range_disjointed_sets)
  have "\<forall>n. f (disjointed A n) \<le> f (A n)"
    by (metis increasingD [OF inc] UNIV_I dA image_subset_iff disjointed_subset A)
  then show "(\<Sum>i. f (disjointed A i)) \<le> (\<Sum>i. f (A i))"
    by (blast intro!: suminf_le)
qed (auto simp: X UN_disjointed_eq disjoint_family_disjointed)

lemma (in ring_of_sets) outer_measure_close:
  "outer_measure M f X < e \<Longrightarrow> \<exists>A. range A \<subseteq> M \<and> disjoint_family A \<and> X \<subseteq> (\<Union>i. A i) \<and> (\<Sum>i. f (A i)) < e"
  unfolding outer_measure_def INF_less_iff by auto

lemma (in ring_of_sets) countably_subadditive_outer_measure:
  assumes posf: "positive M f" and inc: "increasing M f"
  shows "countably_subadditive (Pow \<Omega>) (outer_measure M f)"
proof (simp add: countably_subadditive_def, safe)
  fix A :: "nat \<Rightarrow> _" assume A: "range A \<subseteq> Pow (\<Omega>)" and sb: "(\<Union>i. A i) \<subseteq> \<Omega>"
  let ?O = "outer_measure M f"
  show "?O (\<Union>i. A i) \<le> (\<Sum>n. ?O (A n))"
  proof (rule ennreal_le_epsilon)
    fix b and e :: real assume "0 < e" "(\<Sum>n. outer_measure M f (A n)) < top"
    then have *: "\<And>n. outer_measure M f (A n) < outer_measure M f (A n) + e * (1/2)^Suc n"
      by (auto simp add: less_top dest!: ennreal_suminf_lessD)
    obtain B
      where B: "\<And>n. range (B n) \<subseteq> M"
      and sbB: "\<And>n. A n \<subseteq> (\<Union>i. B n i)"
      and Ble: "\<And>n. (\<Sum>i. f (B n i)) \<le> ?O (A n) + e * (1/2)^(Suc n)"
      by (metis less_imp_le outer_measure_close[OF *])

    define C where "C = case_prod B o prod_decode"
    from B have B_in_M: "\<And>i j. B i j \<in> M"
      by (rule range_subsetD)
    then have C: "range C \<subseteq> M"
      by (auto simp add: C_def split_def)
    have A_C: "(\<Union>i. A i) \<subseteq> (\<Union>i. C i)"
      using sbB by (auto simp add: C_def subset_eq) (metis prod.case prod_encode_inverse)

    have "?O (\<Union>i. A i) \<le> ?O (\<Union>i. C i)"
      using A_C A C by (intro increasing_outer_measure[THEN increasingD]) (auto dest!: sets_into_space)
    also have "\<dots> \<le> (\<Sum>i. f (C i))"
      using C by (intro outer_measure_le[OF posf inc]) auto
    also have "\<dots> = (\<Sum>n. \<Sum>i. f (B n i))"
      using B_in_M unfolding C_def comp_def by (intro suminf_ennreal_2dimen) auto
    also have "\<dots> \<le> (\<Sum>n. ?O (A n) + e * (1/2) ^ Suc n)"
      using B_in_M by (intro suminf_le suminf_nonneg allI Ble) auto
    also have "... = (\<Sum>n. ?O (A n)) + (\<Sum>n. ennreal e * ennreal ((1/2) ^ Suc n))"
      using \<open>0 < e\<close> by (subst suminf_add[symmetric])
                       (auto simp del: ennreal_suminf_cmult simp add: ennreal_mult[symmetric])
    also have "\<dots> = (\<Sum>n. ?O (A n)) + e"
      unfolding ennreal_suminf_cmult
      by (subst suminf_ennreal_eq[OF zero_le_power power_half_series]) auto
    finally show "?O (\<Union>i. A i) \<le> (\<Sum>n. ?O (A n)) + e" .
  qed
qed

lemma (in ring_of_sets) outer_measure_space_outer_measure:
  "positive M f \<Longrightarrow> increasing M f \<Longrightarrow> outer_measure_space (Pow \<Omega>) (outer_measure M f)"
  by (simp add: outer_measure_space_def
    positive_outer_measure increasing_outer_measure countably_subadditive_outer_measure)

lemma (in ring_of_sets) algebra_subset_lambda_system:
  assumes posf: "positive M f" and inc: "increasing M f"
      and add: "additive M f"
  shows "M \<subseteq> lambda_system \<Omega> (Pow \<Omega>) (outer_measure M f)"
proof (auto dest: sets_into_space
            simp add: algebra.lambda_system_eq [OF algebra_Pow])
  fix x s assume x: "x \<in> M" and s: "s \<subseteq> \<Omega>"
  have [simp]: "\<And>x. x \<in> M \<Longrightarrow> s \<inter> (\<Omega> - x) = s - x" using s
    by blast
  have "outer_measure M f (s \<inter> x) + outer_measure M f (s - x) \<le> outer_measure M f s"
    unfolding outer_measure_def[of M f s]
  proof (safe intro!: INF_greatest)
    fix A :: "nat \<Rightarrow> 'a set" assume A: "disjoint_family A" "range A \<subseteq> M" "s \<subseteq> (\<Union>i. A i)"
    have "outer_measure M f (s \<inter> x) \<le> (\<Sum>i. f (A i \<inter> x))"
      unfolding outer_measure_def
    proof (safe intro!: INF_lower2[of "\<lambda>i. A i \<inter> x"])
      from A(1) show "disjoint_family (\<lambda>i. A i \<inter> x)"
        by (rule disjoint_family_on_bisimulation) auto
    qed (insert x A, auto)
    moreover
    have "outer_measure M f (s - x) \<le> (\<Sum>i. f (A i - x))"
      unfolding outer_measure_def
    proof (safe intro!: INF_lower2[of "\<lambda>i. A i - x"])
      from A(1) show "disjoint_family (\<lambda>i. A i - x)"
        by (rule disjoint_family_on_bisimulation) auto
    qed (insert x A, auto)
    ultimately have "outer_measure M f (s \<inter> x) + outer_measure M f (s - x) \<le>
        (\<Sum>i. f (A i \<inter> x)) + (\<Sum>i. f (A i - x))" by (rule add_mono)
    also have "\<dots> = (\<Sum>i. f (A i \<inter> x) + f (A i - x))"
      using A(2) x posf by (subst suminf_add) (auto simp: positive_def)
    also have "\<dots> = (\<Sum>i. f (A i))"
      using A x
      by (subst add[THEN additiveD, symmetric])
         (auto intro!: arg_cong[where f=suminf] arg_cong[where f=f])
    finally show "outer_measure M f (s \<inter> x) + outer_measure M f (s - x) \<le> (\<Sum>i. f (A i))" .
  qed
  moreover
  have "outer_measure M f s \<le> outer_measure M f (s \<inter> x) + outer_measure M f (s - x)"
  proof -
    have "outer_measure M f s = outer_measure M f ((s \<inter> x) \<union> (s - x))"
      by (metis Un_Diff_Int Un_commute)
    also have "... \<le> outer_measure M f (s \<inter> x) + outer_measure M f (s - x)"
      apply (rule subadditiveD)
      apply (rule ring_of_sets.countably_subadditive_subadditive [OF ring_of_sets_Pow])
      apply (simp add: positive_def outer_measure_empty[OF posf])
      apply (rule countably_subadditive_outer_measure)
      using s by (auto intro!: posf inc)
    finally show ?thesis .
  qed
  ultimately
  show "outer_measure M f (s \<inter> x) + outer_measure M f (s - x) = outer_measure M f s"
    by (rule order_antisym)
qed

lemma measure_down: "measure_space \<Omega> N \<mu> \<Longrightarrow> sigma_algebra \<Omega> M \<Longrightarrow> M \<subseteq> N \<Longrightarrow> measure_space \<Omega> M \<mu>"
  by (auto simp add: measure_space_def positive_def countably_additive_def subset_eq)

subsection \<open>Caratheodory's theorem\<close>

theorem (in ring_of_sets) caratheodory':
  assumes posf: "positive M f" and ca: "countably_additive M f"
  shows "\<exists>\<mu> :: 'a set \<Rightarrow> ennreal. (\<forall>s \<in> M. \<mu> s = f s) \<and> measure_space \<Omega> (sigma_sets \<Omega> M) \<mu>"
proof -
  have inc: "increasing M f"
    by (metis additive_increasing ca countably_additive_additive posf)
  let ?O = "outer_measure M f"
  define ls where "ls = lambda_system \<Omega> (Pow \<Omega>) ?O"
  have mls: "measure_space \<Omega> ls ?O"
    using sigma_algebra.caratheodory_lemma
            [OF sigma_algebra_Pow outer_measure_space_outer_measure [OF posf inc]]
    by (simp add: ls_def)
  hence sls: "sigma_algebra \<Omega> ls"
    by (simp add: measure_space_def)
  have "M \<subseteq> ls"
    by (simp add: ls_def)
       (metis ca posf inc countably_additive_additive algebra_subset_lambda_system)
  hence sgs_sb: "sigma_sets (\<Omega>) (M) \<subseteq> ls"
    using sigma_algebra.sigma_sets_subset [OF sls, of "M"]
    by simp
  have "measure_space \<Omega> (sigma_sets \<Omega> M) ?O"
    by (rule measure_down [OF mls], rule sigma_algebra_sigma_sets)
       (simp_all add: sgs_sb space_closed)
  thus ?thesis using outer_measure_agrees [OF posf ca]
    by (intro exI[of _ ?O]) auto
qed

lemma (in ring_of_sets) caratheodory_empty_continuous:
  assumes f: "positive M f" "additive M f" and fin: "\<And>A. A \<in> M \<Longrightarrow> f A \<noteq> \<infinity>"
  assumes cont: "\<And>A. range A \<subseteq> M \<Longrightarrow> decseq A \<Longrightarrow> (\<Inter>i. A i) = {} \<Longrightarrow> (\<lambda>i. f (A i)) \<longlonglongrightarrow> 0"
  shows "\<exists>\<mu> :: 'a set \<Rightarrow> ennreal. (\<forall>s \<in> M. \<mu> s = f s) \<and> measure_space \<Omega> (sigma_sets \<Omega> M) \<mu>"
proof (intro caratheodory' empty_continuous_imp_countably_additive f)
  show "\<forall>A\<in>M. f A \<noteq> \<infinity>" using fin by auto
qed (rule cont)

subsection \<open>Volumes\<close>

definition\<^marker>\<open>tag important\<close> volume :: "'a set set \<Rightarrow> ('a set \<Rightarrow> ennreal) \<Rightarrow> bool" where
  "volume M f \<longleftrightarrow>
  (f {} = 0) \<and> (\<forall>a\<in>M. 0 \<le> f a) \<and>
  (\<forall>C\<subseteq>M. disjoint C \<longrightarrow> finite C \<longrightarrow> \<Union>C \<in> M \<longrightarrow> f (\<Union>C) = (\<Sum>c\<in>C. f c))"

lemma volumeI:
  assumes "f {} = 0"
  assumes "\<And>a. a \<in> M \<Longrightarrow> 0 \<le> f a"
  assumes "\<And>C. C \<subseteq> M \<Longrightarrow> disjoint C \<Longrightarrow> finite C \<Longrightarrow> \<Union>C \<in> M \<Longrightarrow> f (\<Union>C) = (\<Sum>c\<in>C. f c)"
  shows "volume M f"
  using assms by (auto simp: volume_def)

lemma volume_positive:
  "volume M f \<Longrightarrow> a \<in> M \<Longrightarrow> 0 \<le> f a"
  by (auto simp: volume_def)

lemma volume_empty:
  "volume M f \<Longrightarrow> f {} = 0"
  by (auto simp: volume_def)

proposition volume_finite_additive:
  assumes "volume M f"
  assumes A: "\<And>i. i \<in> I \<Longrightarrow> A i \<in> M" "disjoint_family_on A I" "finite I" "\<Union>(A ` I) \<in> M"
  shows "f (\<Union>(A ` I)) = (\<Sum>i\<in>I. f (A i))"
proof -
  have "A`I \<subseteq> M" "disjoint (A`I)" "finite (A`I)" "\<Union>(A`I) \<in> M"
    using A by (auto simp: disjoint_family_on_disjoint_image)
  with \<open>volume M f\<close> have "f (\<Union>(A`I)) = (\<Sum>a\<in>A`I. f a)"
    unfolding volume_def by blast
  also have "\<dots> = (\<Sum>i\<in>I. f (A i))"
  proof (subst sum.reindex_nontrivial)
    fix i j assume "i \<in> I" "j \<in> I" "i \<noteq> j" "A i = A j"
    with \<open>disjoint_family_on A I\<close> have "A i = {}"
      by (auto simp: disjoint_family_on_def)
    then show "f (A i) = 0"
      using volume_empty[OF \<open>volume M f\<close>] by simp
  qed (auto intro: \<open>finite I\<close>)
  finally show "f (\<Union>(A ` I)) = (\<Sum>i\<in>I. f (A i))"
    by simp
qed

lemma (in ring_of_sets) volume_additiveI:
  assumes pos: "\<And>a. a \<in> M \<Longrightarrow> 0 \<le> \<mu> a"
  assumes [simp]: "\<mu> {} = 0"
  assumes add: "\<And>a b. a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> a \<inter> b = {} \<Longrightarrow> \<mu> (a \<union> b) = \<mu> a + \<mu> b"
  shows "volume M \<mu>"
proof (unfold volume_def, safe)
  fix C assume "finite C" "C \<subseteq> M" "disjoint C"
  then show "\<mu> (\<Union>C) = sum \<mu> C"
  proof (induct C)
    case (insert c C)
    from insert(1,2,4,5) have "\<mu> (\<Union>(insert c C)) = \<mu> c + \<mu> (\<Union>C)"
      by (auto intro!: add simp: disjoint_def)
    with insert show ?case
      by (simp add: disjoint_def)
  qed simp
qed fact+

proposition (in semiring_of_sets) extend_volume:
  assumes "volume M \<mu>"
  shows "\<exists>\<mu>'. volume generated_ring \<mu>' \<and> (\<forall>a\<in>M. \<mu>' a = \<mu> a)"
proof -
  let ?R = generated_ring
  have "\<forall>a\<in>?R. \<exists>m. \<exists>C\<subseteq>M. a = \<Union>C \<and> finite C \<and> disjoint C \<and> m = (\<Sum>c\<in>C. \<mu> c)"
    by (auto simp: generated_ring_def)
  from bchoice[OF this] obtain \<mu>'
    where \<mu>'_spec: "\<forall>x\<in>generated_ring. \<exists>C\<subseteq>M. x = \<Union> C \<and> finite C \<and> disjoint C \<and> \<mu>' x = sum \<mu> C"
    by blast
  { fix C assume C: "C \<subseteq> M" "finite C" "disjoint C"
    fix D assume D: "D \<subseteq> M" "finite D" "disjoint D"
    assume "\<Union>C = \<Union>D"
    have "(\<Sum>d\<in>D. \<mu> d) = (\<Sum>d\<in>D. \<Sum>c\<in>C. \<mu> (c \<inter> d))"
    proof (intro sum.cong refl)
      fix d assume "d \<in> D"
      have Un_eq_d: "(\<Union>c\<in>C. c \<inter> d) = d"
        using \<open>d \<in> D\<close> \<open>\<Union>C = \<Union>D\<close> by auto
      moreover have "\<mu> (\<Union>c\<in>C. c \<inter> d) = (\<Sum>c\<in>C. \<mu> (c \<inter> d))"
      proof (rule volume_finite_additive)
        { fix c assume "c \<in> C" then show "c \<inter> d \<in> M"
            using C D \<open>d \<in> D\<close> by auto }
        show "(\<Union>a\<in>C. a \<inter> d) \<in> M"
          unfolding Un_eq_d using \<open>d \<in> D\<close> D by auto
        show "disjoint_family_on (\<lambda>a. a \<inter> d) C"
          using \<open>disjoint C\<close> by (auto simp: disjoint_family_on_def disjoint_def)
      qed fact+
      ultimately show "\<mu> d = (\<Sum>c\<in>C. \<mu> (c \<inter> d))" by simp
    qed }
  note split_sum = this

  { fix C assume C: "C \<subseteq> M" "finite C" "disjoint C"
    fix D assume D: "D \<subseteq> M" "finite D" "disjoint D"
    assume "\<Union>C = \<Union>D"
    with split_sum[OF C D] split_sum[OF D C]
    have "(\<Sum>d\<in>D. \<mu> d) = (\<Sum>c\<in>C. \<mu> c)"
      by (simp, subst sum.swap, simp add: ac_simps) }
  note sum_eq = this

  { fix C assume C: "C \<subseteq> M" "finite C" "disjoint C"
    then have "\<Union>C \<in> ?R" by (auto simp: generated_ring_def)
    with \<mu>'_spec[THEN bspec, of "\<Union>C"]
    obtain D where
      D: "D \<subseteq> M" "finite D" "disjoint D" "\<Union>C = \<Union>D" and "\<mu>' (\<Union>C) = (\<Sum>d\<in>D. \<mu> d)"
      by auto
    with sum_eq[OF C D] have "\<mu>' (\<Union>C) = (\<Sum>c\<in>C. \<mu> c)" by simp }
  note \<mu>' = this

  show ?thesis
  proof (intro exI conjI ring_of_sets.volume_additiveI[OF generating_ring] ballI)
    fix a assume "a \<in> M" with \<mu>'[of "{a}"] show "\<mu>' a = \<mu> a"
      by (simp add: disjoint_def)
  next
    fix a assume "a \<in> ?R"
    then obtain Ca where Ca: "finite Ca" "disjoint Ca" "Ca \<subseteq> M" "a = \<Union> Ca" ..
    with \<mu>'[of Ca] \<open>volume M \<mu>\<close>[THEN volume_positive]
    show "0 \<le> \<mu>' a"
      by (auto intro!: sum_nonneg)
  next
    show "\<mu>' {} = 0" using \<mu>'[of "{}"] by auto
  next
    fix a b assume "a \<in> ?R" "b \<in> ?R"
    then obtain Ca Cb
      where Ca: "finite Ca" "disjoint Ca" "Ca \<subseteq> M" "a = \<Union> Ca"
        and Cb: "finite Cb" "disjoint Cb" "Cb \<subseteq> M" "b = \<Union> Cb"
      by (meson generated_ringE)
    assume "a \<inter> b = {}"
    with Ca Cb have "Ca \<inter> Cb \<subseteq> {{}}" by auto
    then have C_Int_cases: "Ca \<inter> Cb = {{}} \<or> Ca \<inter> Cb = {}" by auto

    from \<open>a \<inter> b = {}\<close> have "\<mu>' (\<Union>(Ca \<union> Cb)) = (\<Sum>c\<in>Ca \<union> Cb. \<mu> c)"
      using Ca Cb by (intro \<mu>') (auto intro!: disjoint_union)
    also have "\<dots> = (\<Sum>c\<in>Ca \<union> Cb. \<mu> c) + (\<Sum>c\<in>Ca \<inter> Cb. \<mu> c)"
      using C_Int_cases volume_empty[OF \<open>volume M \<mu>\<close>] by (elim disjE) simp_all
    also have "\<dots> = (\<Sum>c\<in>Ca. \<mu> c) + (\<Sum>c\<in>Cb. \<mu> c)"
      using Ca Cb by (simp add: sum.union_inter)
    also have "\<dots> = \<mu>' a + \<mu>' b"
      using Ca Cb by (simp add: \<mu>')
    finally show "\<mu>' (a \<union> b) = \<mu>' a + \<mu>' b"
      using Ca Cb by simp
  qed
qed

subsubsection\<^marker>\<open>tag important\<close> \<open>Caratheodory on semirings\<close>

theorem (in semiring_of_sets) caratheodory:
  assumes pos: "positive M \<mu>" and ca: "countably_additive M \<mu>"
  shows "\<exists>\<mu>' :: 'a set \<Rightarrow> ennreal. (\<forall>s \<in> M. \<mu>' s = \<mu> s) \<and> measure_space \<Omega> (sigma_sets \<Omega> M) \<mu>'"
proof -
  have "volume M \<mu>"
  proof (rule volumeI)
    { fix a assume "a \<in> M" then show "0 \<le> \<mu> a"
        using pos unfolding positive_def by auto }
    note p = this

    fix C assume sets_C: "C \<subseteq> M" "\<Union>C \<in> M" and "disjoint C" "finite C"
    have "\<exists>F'. bij_betw F' {..<card C} C"
      by (rule finite_same_card_bij[OF _ \<open>finite C\<close>]) auto
    then obtain F' where "bij_betw F' {..<card C} C" ..
    then have F': "C = F' ` {..< card C}" "inj_on F' {..< card C}"
      by (auto simp: bij_betw_def)
    { fix i j assume *: "i < card C" "j < card C" "i \<noteq> j"
      with F' have "F' i \<in> C" "F' j \<in> C" "F' i \<noteq> F' j"
        unfolding inj_on_def by auto
      with \<open>disjoint C\<close>[THEN disjointD]
      have "F' i \<inter> F' j = {}"
        by auto }
    note F'_disj = this
    define F where "F i = (if i < card C then F' i else {})" for i
    then have "disjoint_family F"
      using F'_disj by (auto simp: disjoint_family_on_def)
    moreover from F' have "(\<Union>i. F i) = \<Union>C"
      by (auto simp add: F_def split: if_split_asm cong del: SUP_cong)
    moreover have sets_F: "\<And>i. F i \<in> M"
      using F' sets_C by (auto simp: F_def)
    moreover note sets_C
    ultimately have "\<mu> (\<Union>C) = (\<Sum>i. \<mu> (F i))"
      using ca[unfolded countably_additive_def, THEN spec, of F] by auto
    also have "\<dots> = (\<Sum>i<card C. \<mu> (F' i))"
    proof -
      have "(\<lambda>i. if i \<in> {..< card C} then \<mu> (F' i) else 0) sums (\<Sum>i<card C. \<mu> (F' i))"
        by (rule sums_If_finite_set) auto
      also have "(\<lambda>i. if i \<in> {..< card C} then \<mu> (F' i) else 0) = (\<lambda>i. \<mu> (F i))"
        using pos by (auto simp: positive_def F_def)
      finally show "(\<Sum>i. \<mu> (F i)) = (\<Sum>i<card C. \<mu> (F' i))"
        by (simp add: sums_iff)
    qed
    also have "\<dots> = (\<Sum>c\<in>C. \<mu> c)"
      using F'(2) by (subst (2) F') (simp add: sum.reindex)
    finally show "\<mu> (\<Union>C) = (\<Sum>c\<in>C. \<mu> c)" .
  next
    show "\<mu> {} = 0"
      using \<open>positive M \<mu>\<close> by (rule positiveD1)
  qed
  from extend_volume[OF this] obtain \<mu>_r where
    V: "volume generated_ring \<mu>_r" "\<And>a. a \<in> M \<Longrightarrow> \<mu> a = \<mu>_r a"
    by auto

  interpret G: ring_of_sets \<Omega> generated_ring
    by (rule generating_ring)

  have pos: "positive generated_ring \<mu>_r"
    using V unfolding positive_def by (auto simp: positive_def intro!: volume_positive volume_empty)

  have "countably_additive generated_ring \<mu>_r"
  proof (rule countably_additiveI)
    fix A' :: "nat \<Rightarrow> 'a set"
    assume A': "range A' \<subseteq> generated_ring" "disjoint_family A'"
      and Un_A: "(\<Union>i. A' i) \<in> generated_ring"

    obtain C' where C': "finite C'" "disjoint C'" "C' \<subseteq> M" "\<Union> (range A') = \<Union> C'"
      using generated_ringE[OF Un_A] by auto

    { fix c assume "c \<in> C'"
      moreover define A where [abs_def]: "A i = A' i \<inter> c" for i
      ultimately have A: "range A \<subseteq> generated_ring" "disjoint_family A"
        and Un_A: "(\<Union>i. A i) \<in> generated_ring"
        using A' C'
        by (auto intro!: G.Int G.finite_Union intro: generated_ringI_Basic simp: disjoint_family_on_def)
      from A C' \<open>c \<in> C'\<close> have UN_eq: "(\<Union>i. A i) = c"
        by (auto simp: A_def)

      have "\<forall>i::nat. \<exists>f::nat \<Rightarrow> 'a set. \<mu>_r (A i) = (\<Sum>j. \<mu>_r (f j)) \<and> disjoint_family f \<and> \<Union>(range f) = A i \<and> (\<forall>j. f j \<in> M)"
        (is "\<forall>i. ?P i")
      proof
        fix i
        from A have Ai: "A i \<in> generated_ring" by auto
        from generated_ringE[OF this] obtain C
          where C: "finite C" "disjoint C" "C \<subseteq> M" "A i = \<Union> C" by auto
        have "\<exists>F'. bij_betw F' {..<card C} C"
          by (rule finite_same_card_bij[OF _ \<open>finite C\<close>]) auto
        then obtain F where F: "bij_betw F {..<card C} C" ..
        define f where [abs_def]: "f i = (if i < card C then F i else {})" for i
        then have f: "bij_betw f {..< card C} C"
          by (intro bij_betw_cong[THEN iffD1, OF _ F]) auto
        with C have "\<forall>j. f j \<in> M"
          by (auto simp: Pi_iff f_def dest!: bij_betw_imp_funcset)
        moreover
        from f C have d_f: "disjoint_family_on f {..<card C}"
          by (intro disjoint_image_disjoint_family_on) (auto simp: bij_betw_def)
        then have "disjoint_family f"
          by (auto simp: disjoint_family_on_def f_def)
        moreover
        have Ai_eq: "A i = (\<Union>x<card C. f x)"
          using f C Ai unfolding bij_betw_def by auto
        then have "\<Union>(range f) = A i"
          using f by (auto simp add: f_def)
        moreover
        { have "(\<Sum>j. \<mu>_r (f j)) = (\<Sum>j. if j \<in> {..< card C} then \<mu>_r (f j) else 0)"
            using volume_empty[OF V(1)] by (auto intro!: arg_cong[where f=suminf] simp: f_def)
          also have "\<dots> = (\<Sum>j<card C. \<mu>_r (f j))"
            by (rule sums_If_finite_set[THEN sums_unique, symmetric]) simp
          also have "\<dots> = \<mu>_r (A i)"
            using C f[THEN bij_betw_imp_funcset] unfolding Ai_eq
            by (intro volume_finite_additive[OF V(1) _ d_f, symmetric])
               (auto simp: Pi_iff Ai_eq intro: generated_ringI_Basic)
          finally have "\<mu>_r (A i) = (\<Sum>j. \<mu>_r (f j))" .. }
        ultimately show "?P i"
          by blast
      qed
      from choice[OF this] obtain f
        where f: "\<forall>x. \<mu>_r (A x) = (\<Sum>j. \<mu>_r (f x j)) \<and> disjoint_family (f x) \<and> \<Union> (range (f x)) = A x \<and> (\<forall>j. f x j \<in> M)"
        ..
      then have UN_f_eq: "(\<Union>i. case_prod f (prod_decode i)) = (\<Union>i. A i)"
        unfolding UN_extend_simps surj_prod_decode by (auto simp: set_eq_iff)

      have d: "disjoint_family (\<lambda>i. case_prod f (prod_decode i))"
        unfolding disjoint_family_on_def
      proof (intro ballI impI)
        fix m n :: nat assume "m \<noteq> n"
        then have neq: "prod_decode m \<noteq> prod_decode n"
          using inj_prod_decode[of UNIV] by (auto simp: inj_on_def)
        show "case_prod f (prod_decode m) \<inter> case_prod f (prod_decode n) = {}"
        proof cases
          assume "fst (prod_decode m) = fst (prod_decode n)"
          then show ?thesis
            using neq f by (fastforce simp: disjoint_family_on_def)
        next
          assume neq: "fst (prod_decode m) \<noteq> fst (prod_decode n)"
          have "case_prod f (prod_decode m) \<subseteq> A (fst (prod_decode m))"
            "case_prod f (prod_decode n) \<subseteq> A (fst (prod_decode n))"
            using f[THEN spec, of "fst (prod_decode m)"]
            using f[THEN spec, of "fst (prod_decode n)"]
            by (auto simp: set_eq_iff)
          with f A neq show ?thesis
            by (fastforce simp: disjoint_family_on_def subset_eq set_eq_iff)
        qed
      qed
      from f have "(\<Sum>n. \<mu>_r (A n)) = (\<Sum>n. \<mu>_r (case_prod f (prod_decode n)))"
        by (intro suminf_ennreal_2dimen[symmetric] generated_ringI_Basic)
         (auto split: prod.split)
      also have "\<dots> = (\<Sum>n. \<mu> (case_prod f (prod_decode n)))"
        using f V(2) by (auto intro!: arg_cong[where f=suminf] split: prod.split)
      also have "\<dots> = \<mu> (\<Union>i. case_prod f (prod_decode i))"
        using f \<open>c \<in> C'\<close> C'
        by (intro ca[unfolded countably_additive_def, rule_format])
           (auto split: prod.split simp: UN_f_eq d UN_eq)
      finally have "(\<Sum>n. \<mu>_r (A' n \<inter> c)) = \<mu> c"
        using UN_f_eq UN_eq by (simp add: A_def) }
    note eq = this

    have "(\<Sum>n. \<mu>_r (A' n)) = (\<Sum>n. \<Sum>c\<in>C'. \<mu>_r (A' n \<inter> c))"
      using C' A'
      by (subst volume_finite_additive[symmetric, OF V(1)])
         (auto simp: disjoint_def disjoint_family_on_def
               intro!: G.Int G.finite_Union arg_cong[where f="\<lambda>X. suminf (\<lambda>i. \<mu>_r (X i))"] ext
               intro: generated_ringI_Basic)
    also have "\<dots> = (\<Sum>c\<in>C'. \<Sum>n. \<mu>_r (A' n \<inter> c))"
      using C' A'
      by (intro suminf_sum G.Int G.finite_Union) (auto intro: generated_ringI_Basic)
    also have "\<dots> = (\<Sum>c\<in>C'. \<mu>_r c)"
      using eq V C' by (auto intro!: sum.cong)
    also have "\<dots> = \<mu>_r (\<Union>C')"
      using C' Un_A
      by (subst volume_finite_additive[symmetric, OF V(1)])
         (auto simp: disjoint_family_on_def disjoint_def
               intro: generated_ringI_Basic)
    finally show "(\<Sum>n. \<mu>_r (A' n)) = \<mu>_r (\<Union>i. A' i)"
      using C' by simp
  qed
  obtain \<mu>' where "(\<forall>s\<in>generated_ring. \<mu>' s = \<mu>_r s) \<and> measure_space \<Omega> (sigma_sets \<Omega> generated_ring) \<mu>'"
    using G.caratheodory'[OF pos \<open>countably_additive generated_ring \<mu>_r\<close>] by auto
  with V show ?thesis
    unfolding sigma_sets_generated_ring_eq
    by (intro exI[of _ \<mu>']) (auto intro: generated_ringI_Basic)
qed

lemma extend_measure_caratheodory:
  fixes G :: "'i \<Rightarrow> 'a set"
  assumes M: "M = extend_measure \<Omega> I G \<mu>"
  assumes "i \<in> I"
  assumes "semiring_of_sets \<Omega> (G ` I)"
  assumes empty: "\<And>i. i \<in> I \<Longrightarrow> G i = {} \<Longrightarrow> \<mu> i = 0"
  assumes inj: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> G i = G j \<Longrightarrow> \<mu> i = \<mu> j"
  assumes nonneg: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> \<mu> i"
  assumes add: "\<And>A::nat \<Rightarrow> 'i. \<And>j. A \<in> UNIV \<rightarrow> I \<Longrightarrow> j \<in> I \<Longrightarrow> disjoint_family (G \<circ> A) \<Longrightarrow>
    (\<Union>i. G (A i)) = G j \<Longrightarrow> (\<Sum>n. \<mu> (A n)) = \<mu> j"
  shows "emeasure M (G i) = \<mu> i"

proof -
  interpret semiring_of_sets \<Omega> "G ` I"
    by fact
  have "\<forall>g\<in>G`I. \<exists>i\<in>I. g = G i"
    by auto
  then obtain sel where sel: "\<And>g. g \<in> G ` I \<Longrightarrow> sel g \<in> I" "\<And>g. g \<in> G ` I \<Longrightarrow> G (sel g) = g"
    by metis

  have "\<exists>\<mu>'. (\<forall>s\<in>G ` I. \<mu>' s = \<mu> (sel s)) \<and> measure_space \<Omega> (sigma_sets \<Omega> (G ` I)) \<mu>'"
  proof (rule caratheodory)
    show "positive (G ` I) (\<lambda>s. \<mu> (sel s))"
      by (auto simp: positive_def intro!: empty sel nonneg)
    show "countably_additive (G ` I) (\<lambda>s. \<mu> (sel s))"
    proof (rule countably_additiveI)
      fix A :: "nat \<Rightarrow> 'a set" assume "range A \<subseteq> G ` I" "disjoint_family A" "(\<Union>i. A i) \<in> G ` I"
      then show "(\<Sum>i. \<mu> (sel (A i))) = \<mu> (sel (\<Union>i. A i))"
        by (intro add) (auto simp: sel image_subset_iff_funcset comp_def Pi_iff intro!: sel)
    qed
  qed
  then obtain \<mu>' where \<mu>': "\<forall>s\<in>G ` I. \<mu>' s = \<mu> (sel s)" "measure_space \<Omega> (sigma_sets \<Omega> (G ` I)) \<mu>'"
    by metis

  show ?thesis
  proof (rule emeasure_extend_measure[OF M])
    { fix i assume "i \<in> I" then show "\<mu>' (G i) = \<mu> i"
      using \<mu>' by (auto intro!: inj sel) }
    show "G ` I \<subseteq> Pow \<Omega>"
      by (rule space_closed)
    then show "positive (sets M) \<mu>'" "countably_additive (sets M) \<mu>'"
      using \<mu>' by (simp_all add: M sets_extend_measure measure_space_def)
  qed fact
qed

proposition extend_measure_caratheodory_pair:
  fixes G :: "'i \<Rightarrow> 'j \<Rightarrow> 'a set"
  assumes M: "M = extend_measure \<Omega> {(a, b). P a b} (\<lambda>(a, b). G a b) (\<lambda>(a, b). \<mu> a b)"
  assumes "P i j"
  assumes semiring: "semiring_of_sets \<Omega> {G a b | a b. P a b}"
  assumes empty: "\<And>i j. P i j \<Longrightarrow> G i j = {} \<Longrightarrow> \<mu> i j = 0"
  assumes inj: "\<And>i j k l. P i j \<Longrightarrow> P k l \<Longrightarrow> G i j = G k l \<Longrightarrow> \<mu> i j = \<mu> k l"
  assumes nonneg: "\<And>i j. P i j \<Longrightarrow> 0 \<le> \<mu> i j"
  assumes add: "\<And>A::nat \<Rightarrow> 'i. \<And>B::nat \<Rightarrow> 'j. \<And>j k.
    (\<And>n. P (A n) (B n)) \<Longrightarrow> P j k \<Longrightarrow> disjoint_family (\<lambda>n. G (A n) (B n)) \<Longrightarrow>
    (\<Union>i. G (A i) (B i)) = G j k \<Longrightarrow> (\<Sum>n. \<mu> (A n) (B n)) = \<mu> j k"
  shows "emeasure M (G i j) = \<mu> i j"
proof -
  have "emeasure M ((\<lambda>(a, b). G a b) (i, j)) = (\<lambda>(a, b). \<mu> a b) (i, j)"
  proof (rule extend_measure_caratheodory[OF M])
    show "semiring_of_sets \<Omega> ((\<lambda>(a, b). G a b) ` {(a, b). P a b})"
      using semiring by (simp add: image_def conj_commute)
  next
    fix A :: "nat \<Rightarrow> ('i \<times> 'j)" and j assume "A \<in> UNIV \<rightarrow> {(a, b). P a b}" "j \<in> {(a, b). P a b}"
      "disjoint_family ((\<lambda>(a, b). G a b) \<circ> A)"
      "(\<Union>i. case A i of (a, b) \<Rightarrow> G a b) = (case j of (a, b) \<Rightarrow> G a b)"
    then show "(\<Sum>n. case A n of (a, b) \<Rightarrow> \<mu> a b) = (case j of (a, b) \<Rightarrow> \<mu> a b)"
      using add[of "\<lambda>i. fst (A i)" "\<lambda>i. snd (A i)" "fst j" "snd j"]
      by (simp add: split_beta' comp_def Pi_iff)
  qed (auto split: prod.splits intro: assms)
  then show ?thesis by simp
qed

end
