header {*Caratheodory Extension Theorem*}

theory Caratheodory
  imports Sigma_Algebra Positive_Infinite_Real
begin

text{*From the Hurd/Coble measure theory development, translated by Lawrence Paulson.*}

subsection {* Measure Spaces *}

definition "positive f \<longleftrightarrow> f {} = (0::pinfreal)" -- "Positive is enforced by the type"

definition
  additive  where
  "additive M f \<longleftrightarrow>
    (\<forall>x \<in> sets M. \<forall>y \<in> sets M. x \<inter> y = {}
    \<longrightarrow> f (x \<union> y) = f x + f y)"

definition
  countably_additive  where
  "countably_additive M f \<longleftrightarrow>
    (\<forall>A. range A \<subseteq> sets M \<longrightarrow>
         disjoint_family A \<longrightarrow>
         (\<Union>i. A i) \<in> sets M \<longrightarrow>
         (\<Sum>\<^isub>\<infinity> n. f (A n)) = f (\<Union>i. A i))"

definition
  increasing  where
  "increasing M f \<longleftrightarrow> (\<forall>x \<in> sets M. \<forall>y \<in> sets M. x \<subseteq> y \<longrightarrow> f x \<le> f y)"

definition
  subadditive  where
  "subadditive M f \<longleftrightarrow>
    (\<forall>x \<in> sets M. \<forall>y \<in> sets M. x \<inter> y = {}
    \<longrightarrow> f (x \<union> y) \<le> f x + f y)"

definition
  countably_subadditive  where
  "countably_subadditive M f \<longleftrightarrow>
    (\<forall>A. range A \<subseteq> sets M \<longrightarrow>
         disjoint_family A \<longrightarrow>
         (\<Union>i. A i) \<in> sets M \<longrightarrow>
         f (\<Union>i. A i) \<le> psuminf (\<lambda>n. f (A n)))"

definition
  lambda_system where
  "lambda_system M f =
    {l. l \<in> sets M & (\<forall>x \<in> sets M. f (l \<inter> x) + f ((space M - l) \<inter> x) = f x)}"

definition
  outer_measure_space where
  "outer_measure_space M f  \<longleftrightarrow>
     positive f \<and> increasing M f \<and> countably_subadditive M f"

definition
  measure_set where
  "measure_set M f X =
     {r . \<exists>A. range A \<subseteq> sets M \<and> disjoint_family A \<and> X \<subseteq> (\<Union>i. A i) \<and> (\<Sum>\<^isub>\<infinity> i. f (A i)) = r}"

locale measure_space = sigma_algebra +
  fixes \<mu> :: "'a set \<Rightarrow> pinfreal"
  assumes empty_measure [simp]: "\<mu> {} = 0"
      and ca: "countably_additive M \<mu>"

lemma increasingD:
     "increasing M f \<Longrightarrow> x \<subseteq> y \<Longrightarrow> x\<in>sets M \<Longrightarrow> y\<in>sets M \<Longrightarrow> f x \<le> f y"
  by (auto simp add: increasing_def)

lemma subadditiveD:
     "subadditive M f \<Longrightarrow> x \<inter> y = {} \<Longrightarrow> x\<in>sets M \<Longrightarrow> y\<in>sets M
      \<Longrightarrow> f (x \<union> y) \<le> f x + f y"
  by (auto simp add: subadditive_def)

lemma additiveD:
     "additive M f \<Longrightarrow> x \<inter> y = {} \<Longrightarrow> x\<in>sets M \<Longrightarrow> y\<in>sets M
      \<Longrightarrow> f (x \<union> y) = f x + f y"
  by (auto simp add: additive_def)

lemma countably_additiveD:
  "countably_additive M f \<Longrightarrow> range A \<subseteq> sets M \<Longrightarrow> disjoint_family A
   \<Longrightarrow> (\<Union>i. A i) \<in> sets M \<Longrightarrow> (\<Sum>\<^isub>\<infinity> n. f (A n)) = f (\<Union>i. A i)"
  by (simp add: countably_additive_def)

section "Extend binary sets"

lemma LIMSEQ_binaryset:
  assumes f: "f {} = 0"
  shows  "(\<lambda>n. \<Sum>i = 0..<n. f (binaryset A B i)) ----> f A + f B"
proof -
  have "(\<lambda>n. \<Sum>i = 0..< Suc (Suc n). f (binaryset A B i)) = (\<lambda>n. f A + f B)"
    proof
      fix n
      show "(\<Sum>i\<Colon>nat = 0\<Colon>nat..<Suc (Suc n). f (binaryset A B i)) = f A + f B"
        by (induct n)  (auto simp add: binaryset_def f)
    qed
  moreover
  have "... ----> f A + f B" by (rule LIMSEQ_const)
  ultimately
  have "(\<lambda>n. \<Sum>i = 0..< Suc (Suc n). f (binaryset A B i)) ----> f A + f B"
    by metis
  hence "(\<lambda>n. \<Sum>i = 0..< n+2. f (binaryset A B i)) ----> f A + f B"
    by simp
  thus ?thesis by (rule LIMSEQ_offset [where k=2])
qed

lemma binaryset_sums:
  assumes f: "f {} = 0"
  shows  "(\<lambda>n. f (binaryset A B n)) sums (f A + f B)"
    by (simp add: sums_def LIMSEQ_binaryset [where f=f, OF f])

lemma suminf_binaryset_eq:
     "f {} = 0 \<Longrightarrow> suminf (\<lambda>n. f (binaryset A B n)) = f A + f B"
  by (metis binaryset_sums sums_unique)

lemma binaryset_psuminf:
  assumes "f {} = 0"
  shows "(\<Sum>\<^isub>\<infinity> n. f (binaryset A B n)) = f A + f B" (is "?suminf = ?sum")
proof -
  have *: "{..<2} = {0, 1::nat}" by auto
  have "\<forall>n\<ge>2. f (binaryset A B n) = 0"
    unfolding binaryset_def
    using assms by auto
  hence "?suminf = (\<Sum>N<2. f (binaryset A B N))"
    by (rule psuminf_finite)
  also have "... = ?sum" unfolding * binaryset_def
    by simp
  finally show ?thesis .
qed

subsection {* Lambda Systems *}

lemma (in algebra) lambda_system_eq:
    "lambda_system M f =
        {l. l \<in> sets M & (\<forall>x \<in> sets M. f (x \<inter> l) + f (x - l) = f x)}"
proof -
  have [simp]: "!!l x. l \<in> sets M \<Longrightarrow> x \<in> sets M \<Longrightarrow> (space M - l) \<inter> x = x - l"
    by (metis Int_Diff Int_absorb1 Int_commute sets_into_space)
  show ?thesis
    by (auto simp add: lambda_system_def) (metis Int_commute)+
qed

lemma (in algebra) lambda_system_empty:
  "positive f \<Longrightarrow> {} \<in> lambda_system M f"
  by (auto simp add: positive_def lambda_system_eq)

lemma lambda_system_sets:
    "x \<in> lambda_system M f \<Longrightarrow> x \<in> sets M"
  by (simp add:  lambda_system_def)

lemma (in algebra) lambda_system_Compl:
  fixes f:: "'a set \<Rightarrow> pinfreal"
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
  fixes f:: "'a set \<Rightarrow> pinfreal"
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
  fixes f:: "'a set \<Rightarrow> pinfreal"
  assumes xl: "x \<in> lambda_system M f" and yl: "y \<in> lambda_system M f"
  shows "x \<union> y \<in> lambda_system M f"
proof -
  have "(space M - x) \<inter> (space M - y) \<in> sets M"
    by (metis Diff_Un Un compl_sets lambda_system_sets xl yl)
  moreover
  have "x \<union> y = space M - ((space M - x) \<inter> (space M - y))"
    by auto  (metis subsetD lambda_system_sets sets_into_space xl yl)+
  ultimately show ?thesis
    by (metis lambda_system_Compl lambda_system_Int xl yl)
qed

lemma (in algebra) lambda_system_algebra:
  "positive f \<Longrightarrow> algebra (M (|sets := lambda_system M f|))"
  apply (auto simp add: algebra_def)
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


lemma (in algebra) countably_subadditive_subadditive:
  assumes f: "positive f" and cs: "countably_subadditive M f"
  shows  "subadditive M f"
proof (auto simp add: subadditive_def)
  fix x y
  assume x: "x \<in> sets M" and y: "y \<in> sets M" and "x \<inter> y = {}"
  hence "disjoint_family (binaryset x y)"
    by (auto simp add: disjoint_family_on_def binaryset_def)
  hence "range (binaryset x y) \<subseteq> sets M \<longrightarrow>
         (\<Union>i. binaryset x y i) \<in> sets M \<longrightarrow>
         f (\<Union>i. binaryset x y i) \<le> (\<Sum>\<^isub>\<infinity> n. f (binaryset x y n))"
    using cs by (simp add: countably_subadditive_def)
  hence "{x,y,{}} \<subseteq> sets M \<longrightarrow> x \<union> y \<in> sets M \<longrightarrow>
         f (x \<union> y) \<le> (\<Sum>\<^isub>\<infinity> n. f (binaryset x y n))"
    by (simp add: range_binaryset_eq UN_binaryset_eq)
  thus "f (x \<union> y) \<le>  f x + f y" using f x y
    by (auto simp add: Un o_def binaryset_psuminf positive_def)
qed

lemma (in algebra) additive_sum:
  fixes A:: "nat \<Rightarrow> 'a set"
  assumes f: "positive f" and ad: "additive M f"
      and A: "range A \<subseteq> sets M"
      and disj: "disjoint_family A"
  shows  "setsum (f \<circ> A) {0..<n} = f (\<Union>i\<in>{0..<n}. A i)"
proof (induct n)
  case 0 show ?case using f by (simp add: positive_def)
next
  case (Suc n)
  have "A n \<inter> (\<Union>i\<in>{0..<n}. A i) = {}" using disj
    by (auto simp add: disjoint_family_on_def neq_iff) blast
  moreover
  have "A n \<in> sets M" using A by blast
  moreover have "(\<Union>i\<in>{0..<n}. A i) \<in> sets M"
    by (metis A UNION_in_sets atLeast0LessThan)
  moreover
  ultimately have "f (A n \<union> (\<Union>i\<in>{0..<n}. A i)) = f (A n) + f(\<Union>i\<in>{0..<n}. A i)"
    using ad UNION_in_sets A by (auto simp add: additive_def)
  with Suc.hyps show ?case using ad
    by (auto simp add: atLeastLessThanSuc additive_def)
qed


lemma countably_subadditiveD:
  "countably_subadditive M f \<Longrightarrow> range A \<subseteq> sets M \<Longrightarrow> disjoint_family A \<Longrightarrow>
   (\<Union>i. A i) \<in> sets M \<Longrightarrow> f (\<Union>i. A i) \<le> psuminf (f o A)"
  by (auto simp add: countably_subadditive_def o_def)

lemma (in algebra) increasing_additive_bound:
  fixes A:: "nat \<Rightarrow> 'a set" and  f :: "'a set \<Rightarrow> pinfreal"
  assumes f: "positive f" and ad: "additive M f"
      and inc: "increasing M f"
      and A: "range A \<subseteq> sets M"
      and disj: "disjoint_family A"
  shows  "psuminf (f \<circ> A) \<le> f (space M)"
proof (safe intro!: psuminf_bound)
  fix N
  have "setsum (f \<circ> A) {0..<N} = f (\<Union>i\<in>{0..<N}. A i)"
    by (rule additive_sum [OF f ad A disj])
  also have "... \<le> f (space M)" using space_closed A
    by (blast intro: increasingD [OF inc] UNION_in_sets top)
  finally show "setsum (f \<circ> A) {..<N} \<le> f (space M)" by (simp add: atLeast0LessThan)
qed

lemma lambda_system_increasing:
   "increasing M f \<Longrightarrow> increasing (M (|sets := lambda_system M f|)) f"
  by (simp add: increasing_def lambda_system_def)

lemma (in algebra) lambda_system_strong_sum:
  fixes A:: "nat \<Rightarrow> 'a set" and f :: "'a set \<Rightarrow> pinfreal"
  assumes f: "positive f" and a: "a \<in> sets M"
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
  have 4: "UNION {0..<n} A \<in> lambda_system M f"
    using A algebra.UNION_in_sets [OF local.lambda_system_algebra, of f, OF f]
    by simp
  from Suc.hyps show ?case
    by (simp add: atLeastLessThanSuc lambda_system_strong_additive [OF a 2 3 4])
qed


lemma (in sigma_algebra) lambda_system_caratheodory:
  assumes oms: "outer_measure_space M f"
      and A: "range A \<subseteq> lambda_system M f"
      and disj: "disjoint_family A"
  shows  "(\<Union>i. A i) \<in> lambda_system M f \<and> psuminf (f \<circ> A) = f (\<Union>i. A i)"
proof -
  have pos: "positive f" and inc: "increasing M f"
   and csa: "countably_subadditive M f"
    by (metis oms outer_measure_space_def)+
  have sa: "subadditive M f"
    by (metis countably_subadditive_subadditive csa pos)
  have A': "range A \<subseteq> sets (M(|sets := lambda_system M f|))" using A
    by simp
  have alg_ls: "algebra (M(|sets := lambda_system M f|))"
    by (rule lambda_system_algebra) (rule pos)
  have A'': "range A \<subseteq> sets M"
     by (metis A image_subset_iff lambda_system_sets)

  have U_in: "(\<Union>i. A i) \<in> sets M"
    by (metis A'' countable_UN)
  have U_eq: "f (\<Union>i. A i) = psuminf (f o A)"
    proof (rule antisym)
      show "f (\<Union>i. A i) \<le> psuminf (f \<circ> A)"
        by (rule countably_subadditiveD [OF csa A'' disj U_in])
      show "psuminf (f \<circ> A) \<le> f (\<Union>i. A i)"
        by (rule psuminf_bound, unfold atLeast0LessThan[symmetric])
           (metis algebra.additive_sum [OF alg_ls] pos disj UN_Un Un_UNIV_right
                  lambda_system_additive subset_Un_eq increasingD [OF inc]
                  A' A'' UNION_in_sets U_in)
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
        have "f (a \<inter> (\<Union>i. A i)) \<le> psuminf (f \<circ> (\<lambda>i. a \<inter> i) \<circ> A)"
          using countably_subadditiveD [OF csa, of "(\<lambda>i. a \<inter> A i)"]
          by (simp add: o_def)
        hence "f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i)) \<le>
            psuminf (f \<circ> (\<lambda>i. a \<inter> i) \<circ> A) + f (a - (\<Union>i. A i))"
          by (rule add_right_mono)
        moreover
        have "psuminf (f \<circ> (\<lambda>i. a \<inter> i) \<circ> A) + f (a - (\<Union>i. A i)) \<le> f a"
          proof (safe intro!: psuminf_bound_add)
            fix n
            have UNION_in: "(\<Union>i\<in>{0..<n}. A i) \<in> sets M"
              by (metis A'' UNION_in_sets)
            have le_fa: "f (UNION {0..<n} A \<inter> a) \<le> f a" using A''
              by (blast intro: increasingD [OF inc] A'' UNION_in_sets)
            have ls: "(\<Union>i\<in>{0..<n}. A i) \<in> lambda_system M f"
              using algebra.UNION_in_sets [OF lambda_system_algebra [of f, OF pos]]
              by (simp add: A)
            hence eq_fa: "f a = f (a \<inter> (\<Union>i\<in>{0..<n}. A i)) + f (a - (\<Union>i\<in>{0..<n}. A i))"
              by (simp add: lambda_system_eq UNION_in)
            have "f (a - (\<Union>i. A i)) \<le> f (a - (\<Union>i\<in>{0..<n}. A i))"
              by (blast intro: increasingD [OF inc] UNION_eq_Union_image
                               UNION_in U_in)
            thus "setsum (f \<circ> (\<lambda>i. a \<inter> i) \<circ> A) {..<n} + f (a - (\<Union>i. A i)) \<le> f a"
              by (simp add: lambda_system_strong_sum pos A disj eq_fa add_left_mono atLeast0LessThan[symmetric])
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
  shows "measure_space (|space = space M, sets = lambda_system M f|) f"
proof -
  have pos: "positive f"
    by (metis oms outer_measure_space_def)
  have alg: "algebra (|space = space M, sets = lambda_system M f|)"
    using lambda_system_algebra [of f, OF pos]
    by (simp add: algebra_def)
  then moreover
  have "sigma_algebra (|space = space M, sets = lambda_system M f|)"
    using lambda_system_caratheodory [OF oms]
    by (simp add: sigma_algebra_disjoint_iff)
  moreover
  have "measure_space_axioms (|space = space M, sets = lambda_system M f|) f"
    using pos lambda_system_caratheodory [OF oms]
    by (simp add: measure_space_axioms_def positive_def lambda_system_sets
                  countably_additive_def o_def)
  ultimately
  show ?thesis
    by intro_locales (auto simp add: sigma_algebra_def)
qed

lemma (in algebra) additive_increasing:
  assumes posf: "positive f" and addf: "additive M f"
  shows "increasing M f"
proof (auto simp add: increasing_def)
  fix x y
  assume xy: "x \<in> sets M" "y \<in> sets M" "x \<subseteq> y"
  have "f x \<le> f x + f (y-x)" ..
  also have "... = f (x \<union> (y-x))" using addf
    by (auto simp add: additive_def) (metis Diff_disjoint Un_Diff_cancel Diff xy(1,2))
  also have "... = f y"
    by (metis Un_Diff_cancel Un_absorb1 xy(3))
  finally show "f x \<le> f y" .
qed

lemma (in algebra) countably_additive_additive:
  assumes posf: "positive f" and ca: "countably_additive M f"
  shows "additive M f"
proof (auto simp add: additive_def)
  fix x y
  assume x: "x \<in> sets M" and y: "y \<in> sets M" and "x \<inter> y = {}"
  hence "disjoint_family (binaryset x y)"
    by (auto simp add: disjoint_family_on_def binaryset_def)
  hence "range (binaryset x y) \<subseteq> sets M \<longrightarrow>
         (\<Union>i. binaryset x y i) \<in> sets M \<longrightarrow>
         f (\<Union>i. binaryset x y i) = (\<Sum>\<^isub>\<infinity> n. f (binaryset x y n))"
    using ca
    by (simp add: countably_additive_def)
  hence "{x,y,{}} \<subseteq> sets M \<longrightarrow> x \<union> y \<in> sets M \<longrightarrow>
         f (x \<union> y) = (\<Sum>\<^isub>\<infinity> n. f (binaryset x y n))"
    by (simp add: range_binaryset_eq UN_binaryset_eq)
  thus "f (x \<union> y) = f x + f y" using posf x y
    by (auto simp add: Un binaryset_psuminf positive_def)
qed

lemma inf_measure_nonempty:
  assumes f: "positive f" and b: "b \<in> sets M" and a: "a \<subseteq> b" "{} \<in> sets M"
  shows "f b \<in> measure_set M f a"
proof -
  have "psuminf (f \<circ> (\<lambda>i. {})(0 := b)) = setsum (f \<circ> (\<lambda>i. {})(0 := b)) {..<1::nat}"
    by (rule psuminf_finite) (simp add: f[unfolded positive_def])
  also have "... = f b"
    by simp
  finally have "psuminf (f \<circ> (\<lambda>i. {})(0 := b)) = f b" .
  thus ?thesis using assms
    by (auto intro!: exI [of _ "(\<lambda>i. {})(0 := b)"]
             simp: measure_set_def disjoint_family_on_def split_if_mem2 comp_def)
qed

lemma (in algebra) inf_measure_agrees:
  assumes posf: "positive f" and ca: "countably_additive M f"
      and s: "s \<in> sets M"
  shows "Inf (measure_set M f s) = f s"
  unfolding Inf_pinfreal_def
proof (safe intro!: Greatest_equality)
  fix z
  assume z: "z \<in> measure_set M f s"
  from this obtain A where
    A: "range A \<subseteq> sets M" and disj: "disjoint_family A"
    and "s \<subseteq> (\<Union>x. A x)" and si: "psuminf (f \<circ> A) = z"
    by (auto simp add: measure_set_def comp_def)
  hence seq: "s = (\<Union>i. A i \<inter> s)" by blast
  have inc: "increasing M f"
    by (metis additive_increasing ca countably_additive_additive posf)
  have sums: "psuminf (\<lambda>i. f (A i \<inter> s)) = f (\<Union>i. A i \<inter> s)"
    proof (rule countably_additiveD [OF ca])
      show "range (\<lambda>n. A n \<inter> s) \<subseteq> sets M" using A s
        by blast
      show "disjoint_family (\<lambda>n. A n \<inter> s)" using disj
        by (auto simp add: disjoint_family_on_def)
      show "(\<Union>i. A i \<inter> s) \<in> sets M" using A s
        by (metis UN_extend_simps(4) s seq)
    qed
  hence "f s = psuminf (\<lambda>i. f (A i \<inter> s))"
    using seq [symmetric] by (simp add: sums_iff)
  also have "... \<le> psuminf (f \<circ> A)"
    proof (rule psuminf_le)
      fix n show "f (A n \<inter> s) \<le> (f \<circ> A) n" using A s
        by (force intro: increasingD [OF inc])
    qed
  also have "... = z" by (rule si)
  finally show "f s \<le> z" .
next
  fix y
  assume y: "\<forall>u \<in> measure_set M f s. y \<le> u"
  thus "y \<le> f s"
    by (blast intro: inf_measure_nonempty [of f, OF posf s subset_refl])
qed

lemma (in algebra) inf_measure_empty:
  assumes posf: "positive f"  "{} \<in> sets M"
  shows "Inf (measure_set M f {}) = 0"
proof (rule antisym)
  show "Inf (measure_set M f {}) \<le> 0"
    by (metis complete_lattice_class.Inf_lower `{} \<in> sets M` inf_measure_nonempty[OF posf] subset_refl posf[unfolded positive_def])
qed simp

lemma (in algebra) inf_measure_positive:
  "positive f \<Longrightarrow>
   positive (\<lambda>x. Inf (measure_set M f x))"
  by (simp add: positive_def inf_measure_empty) 

lemma (in algebra) inf_measure_increasing:
  assumes posf: "positive f"
  shows "increasing (| space = space M, sets = Pow (space M) |)
                    (\<lambda>x. Inf (measure_set M f x))"
apply (auto simp add: increasing_def)
apply (rule complete_lattice_class.Inf_greatest)
apply (rule complete_lattice_class.Inf_lower)
apply (clarsimp simp add: measure_set_def, rule_tac x=A in exI, blast)
done


lemma (in algebra) inf_measure_le:
  assumes posf: "positive f" and inc: "increasing M f"
      and x: "x \<in> {r . \<exists>A. range A \<subseteq> sets M \<and> s \<subseteq> (\<Union>i. A i) \<and> psuminf (f \<circ> A) = r}"
  shows "Inf (measure_set M f s) \<le> x"
proof -
  from x
  obtain A where A: "range A \<subseteq> sets M" and ss: "s \<subseteq> (\<Union>i. A i)"
             and xeq: "psuminf (f \<circ> A) = x"
    by auto
  have dA: "range (disjointed A) \<subseteq> sets M"
    by (metis A range_disjointed_sets)
  have "\<forall>n.(f o disjointed A) n \<le> (f \<circ> A) n" unfolding comp_def
    by (metis increasingD [OF inc] UNIV_I dA image_subset_iff disjointed_subset A comp_def)
  hence sda: "psuminf (f o disjointed A) \<le> psuminf (f \<circ> A)"
    by (blast intro: psuminf_le)
  hence ley: "psuminf (f o disjointed A) \<le> x"
    by (metis xeq)
  hence y: "psuminf (f o disjointed A) \<in> measure_set M f s"
    apply (auto simp add: measure_set_def)
    apply (rule_tac x="disjointed A" in exI)
    apply (simp add: disjoint_family_disjointed UN_disjointed_eq ss dA comp_def)
    done
  show ?thesis
    by (blast intro: y order_trans [OF _ ley] posf complete_lattice_class.Inf_lower)
qed

lemma (in algebra) inf_measure_close:
  assumes posf: "positive f" and e: "0 < e" and ss: "s \<subseteq> (space M)"
  shows "\<exists>A. range A \<subseteq> sets M \<and> disjoint_family A \<and> s \<subseteq> (\<Union>i. A i) \<and>
               psuminf (f \<circ> A) \<le> Inf (measure_set M f s) + e"
proof (cases "Inf (measure_set M f s) = \<omega>")
  case False
  obtain l where "l \<in> measure_set M f s" "l \<le> Inf (measure_set M f s) + e"
    using Inf_close[OF False e] by auto
  thus ?thesis
    by (auto intro!: exI[of _ l] simp: measure_set_def comp_def)
next
  case True
  have "measure_set M f s \<noteq> {}"
    by (metis emptyE ss inf_measure_nonempty [of f, OF posf top _ empty_sets])
  then obtain l where "l \<in> measure_set M f s" by auto
  moreover from True have "l \<le> Inf (measure_set M f s) + e" by simp
  ultimately show ?thesis
    by (auto intro!: exI[of _ l] simp: measure_set_def comp_def)
qed

lemma (in algebra) inf_measure_countably_subadditive:
  assumes posf: "positive f" and inc: "increasing M f"
  shows "countably_subadditive (| space = space M, sets = Pow (space M) |)
                  (\<lambda>x. Inf (measure_set M f x))"
  unfolding countably_subadditive_def o_def
proof (safe, simp, rule pinfreal_le_epsilon)
  fix A :: "nat \<Rightarrow> 'a set" and e :: pinfreal

  let "?outer n" = "Inf (measure_set M f (A n))"
  assume A: "range A \<subseteq> Pow (space M)"
     and disj: "disjoint_family A"
     and sb: "(\<Union>i. A i) \<subseteq> space M"
     and e: "0 < e"
  hence "\<exists>BB. \<forall>n. range (BB n) \<subseteq> sets M \<and> disjoint_family (BB n) \<and>
                   A n \<subseteq> (\<Union>i. BB n i) \<and>
                   psuminf (f o BB n) \<le> ?outer n + e * (1/2)^(Suc n)"
    apply (safe intro!: choice inf_measure_close [of f, OF posf _])
    using e sb by (cases e, auto simp add: not_le mult_pos_pos)
  then obtain BB
    where BB: "\<And>n. (range (BB n) \<subseteq> sets M)"
      and disjBB: "\<And>n. disjoint_family (BB n)"
      and sbBB: "\<And>n. A n \<subseteq> (\<Union>i. BB n i)"
      and BBle: "\<And>n. psuminf (f o BB n) \<le> ?outer n + e * (1/2)^(Suc n)"
    by auto blast
  have sll: "(\<Sum>\<^isub>\<infinity> n. psuminf (f o BB n)) \<le> psuminf ?outer + e"
    proof -
      have "(\<Sum>\<^isub>\<infinity> n. psuminf (f o BB n)) \<le> (\<Sum>\<^isub>\<infinity> n. ?outer n + e*(1/2) ^ Suc n)"
        by (rule psuminf_le[OF BBle])
      also have "... = psuminf ?outer + e"
        using psuminf_half_series by simp
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
  moreover have "psuminf ... = (\<Sum>\<^isub>\<infinity> n. psuminf (f o BB n))" using BBle
    by (force intro!: psuminf_2dimen simp: o_def)
  ultimately have Csums: "psuminf (f \<circ> C) = (\<Sum>\<^isub>\<infinity> n. psuminf (f o BB n))" by simp
  have "Inf (measure_set M f (\<Union>i. A i)) \<le> (\<Sum>\<^isub>\<infinity> n. psuminf (f o BB n))"
    apply (rule inf_measure_le [OF posf(1) inc], auto)
    apply (rule_tac x="C" in exI)
    apply (auto simp add: C sbC Csums)
    done
  also have "... \<le> (\<Sum>\<^isub>\<infinity>n. Inf (measure_set M f (A n))) + e" using sll
    by blast
  finally show "Inf (measure_set M f (\<Union>i. A i)) \<le> psuminf ?outer + e" .
qed

lemma (in algebra) inf_measure_outer:
  "\<lbrakk> positive f ; increasing M f \<rbrakk>
   \<Longrightarrow> outer_measure_space (| space = space M, sets = Pow (space M) |)
                          (\<lambda>x. Inf (measure_set M f x))"
  by (simp add: outer_measure_space_def inf_measure_empty
                inf_measure_increasing inf_measure_countably_subadditive positive_def)

(*MOVE UP*)

lemma (in algebra) algebra_subset_lambda_system:
  assumes posf: "positive f" and inc: "increasing M f"
      and add: "additive M f"
  shows "sets M \<subseteq> lambda_system (| space = space M, sets = Pow (space M) |)
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
    proof (rule pinfreal_le_epsilon)
      fix e :: pinfreal
      assume e: "0 < e"
      from inf_measure_close [of f, OF posf e s]
      obtain A where A: "range A \<subseteq> sets M" and disj: "disjoint_family A"
                 and sUN: "s \<subseteq> (\<Union>i. A i)"
                 and l: "psuminf (f \<circ> A) \<le> Inf (measure_set M f s) + e"
        by auto
      have [simp]: "!!x. x \<in> sets M \<Longrightarrow>
                      (f o (\<lambda>z. z \<inter> (space M - x)) o A) = (f o (\<lambda>z. z - x) o A)"
        by (rule ext, simp, metis A Int_Diff Int_space_eq2 range_subsetD)
      have  [simp]: "!!n. f (A n \<inter> x) + f (A n - x) = f (A n)"
        by (subst additiveD [OF add, symmetric])
           (auto simp add: x range_subsetD [OF A] Int_Diff_Un Int_Diff_disjoint)
      { fix u
        assume u: "u \<in> sets M"
        have [simp]: "\<And>n. f (A n \<inter> u) \<le> f (A n)"
          by (simp add: increasingD [OF inc] u Int range_subsetD [OF A])
        have 2: "Inf (measure_set M f (s \<inter> u)) \<le> psuminf (f \<circ> (\<lambda>z. z \<inter> u) \<circ> A)"
          proof (rule complete_lattice_class.Inf_lower)
            show "psuminf (f \<circ> (\<lambda>z. z \<inter> u) \<circ> A) \<in> measure_set M f (s \<inter> u)"
              apply (simp add: measure_set_def)
              apply (rule_tac x="(\<lambda>z. z \<inter> u) o A" in exI)
              apply (auto simp add: disjoint_family_subset [OF disj] o_def)
              apply (blast intro: u range_subsetD [OF A])
              apply (blast dest: subsetD [OF sUN])
              done
          qed
      } note lesum = this
      have inf1: "Inf (measure_set M f (s\<inter>x)) \<le> psuminf (f o (\<lambda>z. z\<inter>x) o A)"
        and inf2: "Inf (measure_set M f (s \<inter> (space M - x)))
                   \<le> psuminf (f o (\<lambda>z. z \<inter> (space M - x)) o A)"
        by (metis Diff lesum top x)+
      hence "Inf (measure_set M f (s\<inter>x)) + Inf (measure_set M f (s-x))
           \<le> psuminf (f o (\<lambda>s. s\<inter>x) o A) + psuminf (f o (\<lambda>s. s-x) o A)"
        by (simp add: x add_mono)
      also have "... \<le> psuminf (f o A)"
        by (simp add: x psuminf_add[symmetric] o_def)
      also have "... \<le> Inf (measure_set M f s) + e"
        by (rule l)
      finally show "Inf (measure_set M f (s\<inter>x)) + Inf (measure_set M f (s-x))
        \<le> Inf (measure_set M f s) + e" .
    qed
  moreover
  have "Inf (measure_set M f s)
       \<le> Inf (measure_set M f (s\<inter>x)) + Inf (measure_set M f (s-x))"
    proof -
    have "Inf (measure_set M f s) = Inf (measure_set M f ((s\<inter>x) \<union> (s-x)))"
      by (metis Un_Diff_Int Un_commute)
    also have "... \<le> Inf (measure_set M f (s\<inter>x)) + Inf (measure_set M f (s-x))"
      apply (rule subadditiveD)
      apply (iprover intro: algebra.countably_subadditive_subadditive algebra_Pow
               inf_measure_positive inf_measure_countably_subadditive posf inc)
      apply (auto simp add: subsetD [OF s])
      done
    finally show ?thesis .
    qed
  ultimately
  show "Inf (measure_set M f (s\<inter>x)) + Inf (measure_set M f (s-x))
        = Inf (measure_set M f s)"
    by (rule order_antisym)
qed

lemma measure_down:
     "measure_space N \<mu> \<Longrightarrow> sigma_algebra M \<Longrightarrow> sets M \<subseteq> sets N \<Longrightarrow>
      (\<nu> = \<mu>) \<Longrightarrow> measure_space M \<nu>"
  by (simp add: measure_space_def measure_space_axioms_def positive_def
                countably_additive_def)
     blast

theorem (in algebra) caratheodory:
  assumes posf: "positive f" and ca: "countably_additive M f"
  shows "\<exists>\<mu> :: 'a set \<Rightarrow> pinfreal. (\<forall>s \<in> sets M. \<mu> s = f s) \<and> measure_space (sigma (space M) (sets M)) \<mu>"
  proof -
    have inc: "increasing M f"
      by (metis additive_increasing ca countably_additive_additive posf)
    let ?infm = "(\<lambda>x. Inf (measure_set M f x))"
    def ls \<equiv> "lambda_system (|space = space M, sets = Pow (space M)|) ?infm"
    have mls: "measure_space \<lparr>space = space M, sets = ls\<rparr> ?infm"
      using sigma_algebra.caratheodory_lemma
              [OF sigma_algebra_Pow  inf_measure_outer [OF posf inc]]
      by (simp add: ls_def)
    hence sls: "sigma_algebra (|space = space M, sets = ls|)"
      by (simp add: measure_space_def)
    have "sets M \<subseteq> ls"
      by (simp add: ls_def)
         (metis ca posf inc countably_additive_additive algebra_subset_lambda_system)
    hence sgs_sb: "sigma_sets (space M) (sets M) \<subseteq> ls"
      using sigma_algebra.sigma_sets_subset [OF sls, of "sets M"]
      by simp
    have "measure_space (sigma (space M) (sets M)) ?infm"
      unfolding sigma_def
      by (rule measure_down [OF mls], rule sigma_algebra_sigma_sets)
         (simp_all add: sgs_sb space_closed)
    thus ?thesis using inf_measure_agrees [OF posf ca] by (auto intro!: exI[of _ ?infm])
  qed

end
