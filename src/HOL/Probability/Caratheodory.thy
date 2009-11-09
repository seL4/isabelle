header {*Caratheodory Extension Theorem*}

theory Caratheodory
  imports Sigma_Algebra SupInf SeriesPlus
begin

text{*From the Hurd/Coble measure theory development, translated by Lawrence Paulson.*}

subsection {* Measure Spaces *}

text {*A measure assigns a nonnegative real to every measurable set. 
       It is countably additive for disjoint sets.*}

record 'a measure_space = "'a algebra" +
  measure:: "'a set \<Rightarrow> real"

definition
  disjoint_family  where
  "disjoint_family A \<longleftrightarrow> (\<forall>m n. m \<noteq> n \<longrightarrow> A m \<inter> A n = {})"

definition
  positive  where
  "positive M f \<longleftrightarrow> f {} = (0::real) & (\<forall>x \<in> sets M. 0 \<le> f x)"

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
         (\<lambda>n. f (A n))  sums  f (\<Union>i. A i))"

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
         summable (f o A) \<longrightarrow>
         f (\<Union>i. A i) \<le> suminf (\<lambda>n. f (A n)))"

definition
  lambda_system where
  "lambda_system M f = 
    {l. l \<in> sets M & (\<forall>x \<in> sets M. f (l \<inter> x) + f ((space M - l) \<inter> x) = f x)}"

definition
  outer_measure_space where
  "outer_measure_space M f  \<longleftrightarrow> 
     positive M f & increasing M f & countably_subadditive M f"

definition
  measure_set where
  "measure_set M f X =
     {r . \<exists>A. range A \<subseteq> sets M & disjoint_family A & X \<subseteq> (\<Union>i. A i) & (f \<circ> A) sums r}"


locale measure_space = sigma_algebra +
  assumes positive: "!!a. a \<in> sets M \<Longrightarrow> 0 \<le> measure M a"
      and empty_measure [simp]: "measure M {} = (0::real)"
      and ca: "countably_additive M (measure M)"

subsection {* Basic Lemmas *}

lemma positive_imp_0: "positive M f \<Longrightarrow> f {} = 0"
  by (simp add: positive_def) 

lemma positive_imp_pos: "positive M f \<Longrightarrow> x \<in> sets M \<Longrightarrow> 0 \<le> f x"
  by (simp add: positive_def) 

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
   \<Longrightarrow> (\<Union>i. A i) \<in> sets M \<Longrightarrow> (\<lambda>n. f (A n))  sums  f (\<Union>i. A i)"
  by (simp add: countably_additive_def) 

lemma Int_Diff_disjoint: "A \<inter> B \<inter> (A - B) = {}"
  by blast

lemma Int_Diff_Un: "A \<inter> B \<union> (A - B) = A"
  by blast

lemma disjoint_family_subset:
     "disjoint_family A \<Longrightarrow> (!!x. B x \<subseteq> A x) \<Longrightarrow> disjoint_family B"
  by (force simp add: disjoint_family_def) 

subsection {* A Two-Element Series *}

definition binaryset :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a set "
  where "binaryset A B = (\<lambda>\<^isup>x. {})(0 := A, Suc 0 := B)"

lemma range_binaryset_eq: "range(binaryset A B) = {A,B,{}}"
  apply (simp add: binaryset_def) 
  apply (rule set_ext) 
  apply (auto simp add: image_iff) 
  done

lemma UN_binaryset_eq: "(\<Union>i. binaryset A B i) = A \<union> B"
  by (simp add: UNION_eq_Union_image range_binaryset_eq) 

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


subsection {* Lambda Systems *}

lemma (in algebra) lambda_system_eq:
    "lambda_system M f = 
        {l. l \<in> sets M & (\<forall>x \<in> sets M. f (x \<inter> l) + f (x - l) = f x)}"
proof -
  have [simp]: "!!l x. l \<in> sets M \<Longrightarrow> x \<in> sets M \<Longrightarrow> (space M - l) \<inter> x = x - l"
    by (metis Diff_eq Int_Diff Int_absorb1 Int_commute sets_into_space)
  show ?thesis
    by (auto simp add: lambda_system_def) (metis Diff_Compl Int_commute)+
qed

lemma (in algebra) lambda_system_empty:
    "positive M f \<Longrightarrow> {} \<in> lambda_system M f"
  by (auto simp add: positive_def lambda_system_eq) 

lemma lambda_system_sets:
    "x \<in> lambda_system M f \<Longrightarrow> x \<in> sets M"
  by (simp add:  lambda_system_def)

lemma (in algebra) lambda_system_Compl:
  fixes f:: "'a set \<Rightarrow> real"
  assumes x: "x \<in> lambda_system M f"
  shows "space M - x \<in> lambda_system M f"
  proof -
    have "x \<subseteq> space M"
      by (metis sets_into_space lambda_system_sets x)
    hence "space M - (space M - x) = x"
      by (metis double_diff equalityE) 
    with x show ?thesis
      by (force simp add: lambda_system_def)
  qed

lemma (in algebra) lambda_system_Int:
  fixes f:: "'a set \<Rightarrow> real"
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
          by (simp add: ey) 
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
  fixes f:: "'a set \<Rightarrow> real"
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
    "positive M f \<Longrightarrow> algebra (M (|sets := lambda_system M f|))"
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

lemma (in algebra) Int_space_eq1 [simp]: "x \<in> sets M \<Longrightarrow> space M \<inter> x = x"
  by (metis Int_absorb1 sets_into_space)

lemma (in algebra) Int_space_eq2 [simp]: "x \<in> sets M \<Longrightarrow> x \<inter> space M = x"
  by (metis Int_absorb2 sets_into_space)

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
  assumes f: "positive M f" and cs: "countably_subadditive M f"
  shows  "subadditive M f"
proof (auto simp add: subadditive_def) 
  fix x y
  assume x: "x \<in> sets M" and y: "y \<in> sets M" and "x \<inter> y = {}"
  hence "disjoint_family (binaryset x y)"
    by (auto simp add: disjoint_family_def binaryset_def) 
  hence "range (binaryset x y) \<subseteq> sets M \<longrightarrow> 
         (\<Union>i. binaryset x y i) \<in> sets M \<longrightarrow> 
         summable (f o (binaryset x y)) \<longrightarrow>
         f (\<Union>i. binaryset x y i) \<le> suminf (\<lambda>n. f (binaryset x y n))"
    using cs by (simp add: countably_subadditive_def) 
  hence "{x,y,{}} \<subseteq> sets M \<longrightarrow> x \<union> y \<in> sets M \<longrightarrow> 
         summable (f o (binaryset x y)) \<longrightarrow>
         f (x \<union> y) \<le> suminf (\<lambda>n. f (binaryset x y n))"
    by (simp add: range_binaryset_eq UN_binaryset_eq)
  thus "f (x \<union> y) \<le>  f x + f y" using f x y binaryset_sums
    by (auto simp add: Un sums_iff positive_def o_def) 
qed 


definition disjointed :: "(nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> 'a set "
  where "disjointed A n = A n - (\<Union>i\<in>{0..<n}. A i)"

lemma finite_UN_disjointed_eq: "(\<Union>i\<in>{0..<n}. disjointed A i) = (\<Union>i\<in>{0..<n}. A i)"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  thus ?case by (simp add: atLeastLessThanSuc disjointed_def) 
qed

lemma UN_disjointed_eq: "(\<Union>i. disjointed A i) = (\<Union>i. A i)"
  apply (rule UN_finite2_eq [where k=0]) 
  apply (simp add: finite_UN_disjointed_eq) 
  done

lemma less_disjoint_disjointed: "m<n \<Longrightarrow> disjointed A m \<inter> disjointed A n = {}"
  by (auto simp add: disjointed_def)

lemma disjoint_family_disjointed: "disjoint_family (disjointed A)"
  by (simp add: disjoint_family_def) 
     (metis neq_iff Int_commute less_disjoint_disjointed)

lemma disjointed_subset: "disjointed A n \<subseteq> A n"
  by (auto simp add: disjointed_def)


lemma (in algebra) UNION_in_sets:
  fixes A:: "nat \<Rightarrow> 'a set"
  assumes A: "range A \<subseteq> sets M "
  shows  "(\<Union>i\<in>{0..<n}. A i) \<in> sets M"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n) 
  thus ?case
    by (simp add: atLeastLessThanSuc) (metis A Un UNIV_I image_subset_iff)
qed

lemma (in algebra) range_disjointed_sets:
  assumes A: "range A \<subseteq> sets M "
  shows  "range (disjointed A) \<subseteq> sets M"
proof (auto simp add: disjointed_def) 
  fix n
  show "A n - (\<Union>i\<in>{0..<n}. A i) \<in> sets M" using UNION_in_sets
    by (metis A Diff UNIV_I disjointed_def image_subset_iff)
qed

lemma sigma_algebra_disjoint_iff: 
     "sigma_algebra M \<longleftrightarrow> 
      algebra M &
      (\<forall>A. range A \<subseteq> sets M \<longrightarrow> disjoint_family A \<longrightarrow> 
           (\<Union>i::nat. A i) \<in> sets M)"
proof (auto simp add: sigma_algebra_iff)
  fix A :: "nat \<Rightarrow> 'a set"
  assume M: "algebra M"
     and A: "range A \<subseteq> sets M"
     and UnA: "\<forall>A. range A \<subseteq> sets M \<longrightarrow>
               disjoint_family A \<longrightarrow> (\<Union>i::nat. A i) \<in> sets M"
  hence "range (disjointed A) \<subseteq> sets M \<longrightarrow>
         disjoint_family (disjointed A) \<longrightarrow>
         (\<Union>i. disjointed A i) \<in> sets M" by blast
  hence "(\<Union>i. disjointed A i) \<in> sets M"
    by (simp add: algebra.range_disjointed_sets M A disjoint_family_disjointed) 
  thus "(\<Union>i::nat. A i) \<in> sets M" by (simp add: UN_disjointed_eq)
qed


lemma (in algebra) additive_sum:
  fixes A:: "nat \<Rightarrow> 'a set"
  assumes f: "positive M f" and ad: "additive M f"
      and A: "range A \<subseteq> sets M"
      and disj: "disjoint_family A"
  shows  "setsum (f o A) {0..<n} = f (\<Union>i\<in>{0..<n}. A i)"
proof (induct n)
  case 0 show ?case using f by (simp add: positive_def) 
next
  case (Suc n) 
  have "A n \<inter> (\<Union>i\<in>{0..<n}. A i) = {}" using disj 
    by (auto simp add: disjoint_family_def neq_iff) blast
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
   (\<Union>i. A i) \<in> sets M \<Longrightarrow> summable (f o A) \<Longrightarrow> f (\<Union>i. A i) \<le> suminf (f o A)" 
  by (auto simp add: countably_subadditive_def o_def)

lemma (in algebra) increasing_additive_summable:
  fixes A:: "nat \<Rightarrow> 'a set"
  assumes f: "positive M f" and ad: "additive M f"
      and inc: "increasing M f"
      and A: "range A \<subseteq> sets M"
      and disj: "disjoint_family A"
  shows  "summable (f o A)"
proof (rule pos_summable) 
  fix n
  show "0 \<le> (f \<circ> A) n" using f A
    by (force simp add: positive_def)
  next
  fix n
  have "setsum (f \<circ> A) {0..<n} = f (\<Union>i\<in>{0..<n}. A i)"
    by (rule additive_sum [OF f ad A disj]) 
  also have "... \<le> f (space M)" using space_closed A
    by (blast intro: increasingD [OF inc] UNION_in_sets top) 
  finally show "setsum (f \<circ> A) {0..<n} \<le> f (space M)" .
qed

lemma lambda_system_positive:
     "positive M f \<Longrightarrow> positive (M (|sets := lambda_system M f|)) f"
  by (simp add: positive_def lambda_system_def) 

lemma lambda_system_increasing:
   "increasing M f \<Longrightarrow> increasing (M (|sets := lambda_system M f|)) f"
  by (simp add: increasing_def lambda_system_def) 

lemma (in algebra) lambda_system_strong_sum:
  fixes A:: "nat \<Rightarrow> 'a set"
  assumes f: "positive M f" and a: "a \<in> sets M"
      and A: "range A \<subseteq> lambda_system M f"
      and disj: "disjoint_family A"
  shows  "(\<Sum>i = 0..<n. f (a \<inter>A i)) = f (a \<inter> (\<Union>i\<in>{0..<n}. A i))"
proof (induct n)
  case 0 show ?case using f by (simp add: positive_def) 
next
  case (Suc n) 
  have 2: "A n \<inter> UNION {0..<n} A = {}" using disj
    by (force simp add: disjoint_family_def neq_iff) 
  have 3: "A n \<in> lambda_system M f" using A
    by blast
  have 4: "UNION {0..<n} A \<in> lambda_system M f"
    using A algebra.UNION_in_sets [OF local.lambda_system_algebra [OF f]] 
    by simp
  from Suc.hyps show ?case
    by (simp add: atLeastLessThanSuc lambda_system_strong_additive [OF a 2 3 4])
qed


lemma (in sigma_algebra) lambda_system_caratheodory:
  assumes oms: "outer_measure_space M f"
      and A: "range A \<subseteq> lambda_system M f"
      and disj: "disjoint_family A"
  shows  "(\<Union>i. A i) \<in> lambda_system M f & (f \<circ> A)  sums  f (\<Union>i. A i)"
proof -
  have pos: "positive M f" and inc: "increasing M f" 
   and csa: "countably_subadditive M f" 
    by (metis oms outer_measure_space_def)+
  have sa: "subadditive M f"
    by (metis countably_subadditive_subadditive csa pos) 
  have A': "range A \<subseteq> sets (M(|sets := lambda_system M f|))" using A 
    by simp
  have alg_ls: "algebra (M(|sets := lambda_system M f|))"
    by (rule lambda_system_algebra [OF pos]) 
  have A'': "range A \<subseteq> sets M"
     by (metis A image_subset_iff lambda_system_sets)
  have sumfA: "summable (f \<circ> A)" 
    by (metis algebra.increasing_additive_summable [OF alg_ls]
          lambda_system_positive lambda_system_additive lambda_system_increasing
          A' oms outer_measure_space_def disj)
  have U_in: "(\<Union>i. A i) \<in> sets M"
    by (metis A countable_UN image_subset_iff lambda_system_sets)
  have U_eq: "f (\<Union>i. A i) = suminf (f o A)" 
    proof (rule antisym)
      show "f (\<Union>i. A i) \<le> suminf (f \<circ> A)"
        by (rule countably_subadditiveD [OF csa A'' disj U_in sumfA]) 
      show "suminf (f \<circ> A) \<le> f (\<Union>i. A i)"
        by (rule suminf_le [OF sumfA]) 
           (metis algebra.additive_sum [OF alg_ls] pos disj UN_Un Un_UNIV_right
                  lambda_system_positive lambda_system_additive 
                  subset_Un_eq increasingD [OF inc] A' A'' UNION_in_sets U_in) 
    qed
  {
    fix a 
    assume a [iff]: "a \<in> sets M" 
    have "f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i)) = f a"
    proof -
      have summ: "summable (f \<circ> (\<lambda>i. a \<inter> i) \<circ> A)" using pos A'' 
        apply -
        apply (rule summable_comparison_test [OF _ sumfA]) 
        apply (rule_tac x="0" in exI) 
        apply (simp add: positive_def) 
        apply (auto simp add: )
        apply (subst abs_of_nonneg)
        apply (metis A'' Int UNIV_I a image_subset_iff)
        apply (blast intro:  increasingD [OF inc] a)   
        done
      show ?thesis
      proof (rule antisym)
        have "range (\<lambda>i. a \<inter> A i) \<subseteq> sets M" using A''
          by blast
        moreover 
        have "disjoint_family (\<lambda>i. a \<inter> A i)" using disj
          by (auto simp add: disjoint_family_def) 
        moreover 
        have "a \<inter> (\<Union>i. A i) \<in> sets M"
          by (metis Int U_in a)
        ultimately 
        have "f (a \<inter> (\<Union>i. A i)) \<le> suminf (f \<circ> (\<lambda>i. a \<inter> i) \<circ> A)"
          using countably_subadditiveD [OF csa, of "(\<lambda>i. a \<inter> A i)"] summ
          by (simp add: o_def) 
        moreover 
        have "suminf (f \<circ> (\<lambda>i. a \<inter> i) \<circ> A)  \<le> f a - f (a - (\<Union>i. A i))"
          proof (rule suminf_le [OF summ])
            fix n
            have UNION_in: "(\<Union>i\<in>{0..<n}. A i) \<in> sets M"
              by (metis A'' UNION_in_sets) 
            have le_fa: "f (UNION {0..<n} A \<inter> a) \<le> f a" using A''
              by (blast intro: increasingD [OF inc] A'' Int UNION_in_sets a) 
            have ls: "(\<Union>i\<in>{0..<n}. A i) \<in> lambda_system M f"
              using algebra.UNION_in_sets [OF lambda_system_algebra [OF pos]]
              by (simp add: A) 
            hence eq_fa: "f (a \<inter> (\<Union>i\<in>{0..<n}. A i)) + f (a - (\<Union>i\<in>{0..<n}. A i)) = f a"
              by (simp add: lambda_system_eq UNION_in Diff_Compl a)
            have "f (a - (\<Union>i. A i)) \<le> f (a - (\<Union>i\<in>{0..<n}. A i))"
              by (blast intro: increasingD [OF inc] Diff UNION_eq_Union_image 
                               UNION_in U_in a) 
            thus "setsum (f \<circ> (\<lambda>i. a \<inter> i) \<circ> A) {0..<n} \<le> f a - f (a - (\<Union>i. A i))"
              using eq_fa
              by (simp add: suminf_le [OF summ] lambda_system_strong_sum pos 
                            a A disj)
          qed
        ultimately show "f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i)) \<le> f a" 
          by arith
      next
        have "f a \<le> f (a \<inter> (\<Union>i. A i) \<union> (a - (\<Union>i. A i)))" 
          by (blast intro:  increasingD [OF inc] a U_in)
        also have "... \<le>  f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i))"
          by (blast intro: subadditiveD [OF sa] Int Diff U_in) 
        finally show "f a \<le> f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i))" .
        qed
     qed
  }
  thus  ?thesis
    by (simp add: lambda_system_eq sums_iff U_eq U_in sumfA)
qed

lemma (in sigma_algebra) caratheodory_lemma:
  assumes oms: "outer_measure_space M f"
  shows "measure_space (|space = space M, sets = lambda_system M f, measure = f|)"
proof -
  have pos: "positive M f" 
    by (metis oms outer_measure_space_def)
  have alg: "algebra (|space = space M, sets = lambda_system M f, measure = f|)"
    using lambda_system_algebra [OF pos]
    by (simp add: algebra_def) 
  then moreover 
  have "sigma_algebra (|space = space M, sets = lambda_system M f, measure = f|)"
    using lambda_system_caratheodory [OF oms]
    by (simp add: sigma_algebra_disjoint_iff) 
  moreover 
  have "measure_space_axioms (|space = space M, sets = lambda_system M f, measure = f|)" 
    using pos lambda_system_caratheodory [OF oms]
    by (simp add: measure_space_axioms_def positive_def lambda_system_sets 
                  countably_additive_def o_def) 
  ultimately 
  show ?thesis
    by intro_locales (auto simp add: sigma_algebra_def) 
qed


lemma (in algebra) inf_measure_nonempty:
  assumes f: "positive M f" and b: "b \<in> sets M" and a: "a \<subseteq> b"
  shows "f b \<in> measure_set M f a"
proof -
  have "(f \<circ> (\<lambda>i. {})(0 := b)) sums setsum (f \<circ> (\<lambda>i. {})(0 := b)) {0..<1::nat}"
    by (rule series_zero)  (simp add: positive_imp_0 [OF f]) 
  also have "... = f b" 
    by simp
  finally have "(f \<circ> (\<lambda>i. {})(0 := b)) sums f b" .
  thus ?thesis using a
    by (auto intro!: exI [of _ "(\<lambda>i. {})(0 := b)"] 
             simp add: measure_set_def disjoint_family_def b split_if_mem2) 
qed  

lemma (in algebra) inf_measure_pos0:
     "positive M f \<Longrightarrow> x \<in> measure_set M f a \<Longrightarrow> 0 \<le> x"
apply (auto simp add: positive_def measure_set_def sums_iff intro!: suminf_ge_zero)
apply blast
done

lemma (in algebra) inf_measure_pos:
  shows "positive M f \<Longrightarrow> x \<subseteq> space M \<Longrightarrow> 0 \<le> Inf (measure_set M f x)"
apply (rule Inf_greatest)
apply (metis emptyE inf_measure_nonempty top)
apply (metis inf_measure_pos0) 
done

lemma (in algebra) additive_increasing:
  assumes posf: "positive M f" and addf: "additive M f" 
  shows "increasing M f"
proof (auto simp add: increasing_def) 
  fix x y
  assume xy: "x \<in> sets M" "y \<in> sets M" "x \<subseteq> y"
  have "f x \<le> f x + f (y-x)" using posf
    by (simp add: positive_def) (metis Diff xy)
  also have "... = f (x \<union> (y-x))" using addf
    by (auto simp add: additive_def) (metis Diff_disjoint Un_Diff_cancel Diff xy) 
  also have "... = f y"
    by (metis Un_Diff_cancel Un_absorb1 xy)
  finally show "f x \<le> f y" .
qed

lemma (in algebra) countably_additive_additive:
  assumes posf: "positive M f" and ca: "countably_additive M f" 
  shows "additive M f"
proof (auto simp add: additive_def) 
  fix x y
  assume x: "x \<in> sets M" and y: "y \<in> sets M" and "x \<inter> y = {}"
  hence "disjoint_family (binaryset x y)"
    by (auto simp add: disjoint_family_def binaryset_def) 
  hence "range (binaryset x y) \<subseteq> sets M \<longrightarrow> 
         (\<Union>i. binaryset x y i) \<in> sets M \<longrightarrow> 
         f (\<Union>i. binaryset x y i) = suminf (\<lambda>n. f (binaryset x y n))"
    using ca
    by (simp add: countably_additive_def) (metis UN_binaryset_eq sums_unique) 
  hence "{x,y,{}} \<subseteq> sets M \<longrightarrow> x \<union> y \<in> sets M \<longrightarrow> 
         f (x \<union> y) = suminf (\<lambda>n. f (binaryset x y n))"
    by (simp add: range_binaryset_eq UN_binaryset_eq)
  thus "f (x \<union> y) = f x + f y" using posf x y
    by (simp add: Un suminf_binaryset_eq positive_def)
qed 
 
lemma (in algebra) inf_measure_agrees:
  assumes posf: "positive M f" and ca: "countably_additive M f" 
      and s: "s \<in> sets M"  
  shows "Inf (measure_set M f s) = f s"
proof (rule Inf_eq) 
  fix z
  assume z: "z \<in> measure_set M f s"
  from this obtain A where 
    A: "range A \<subseteq> sets M" and disj: "disjoint_family A"
    and "s \<subseteq> (\<Union>x. A x)" and sm: "summable (f \<circ> A)"
    and si: "suminf (f \<circ> A) = z"
    by (auto simp add: measure_set_def sums_iff) 
  hence seq: "s = (\<Union>i. A i \<inter> s)" by blast
  have inc: "increasing M f"
    by (metis additive_increasing ca countably_additive_additive posf)
  have sums: "(\<lambda>i. f (A i \<inter> s)) sums f (\<Union>i. A i \<inter> s)"
    proof (rule countably_additiveD [OF ca]) 
      show "range (\<lambda>n. A n \<inter> s) \<subseteq> sets M" using A s
        by blast
      show "disjoint_family (\<lambda>n. A n \<inter> s)" using disj
        by (auto simp add: disjoint_family_def)
      show "(\<Union>i. A i \<inter> s) \<in> sets M" using A s
        by (metis UN_extend_simps(4) s seq)
    qed
  hence "f s = suminf (\<lambda>i. f (A i \<inter> s))"
    by (metis Int_commute UN_simps(4) seq sums_iff) 
  also have "... \<le> suminf (f \<circ> A)" 
    proof (rule summable_le [OF _ _ sm]) 
      show "\<forall>n. f (A n \<inter> s) \<le> (f \<circ> A) n" using A s
        by (force intro: increasingD [OF inc]) 
      show "summable (\<lambda>i. f (A i \<inter> s))" using sums
        by (simp add: sums_iff) 
    qed
  also have "... = z" by (rule si) 
  finally show "f s \<le> z" .
next
  fix y
  assume y: "!!u. u \<in> measure_set M f s \<Longrightarrow> y \<le> u"
  thus "y \<le> f s"
    by (blast intro: inf_measure_nonempty [OF posf s subset_refl])
qed

lemma (in algebra) inf_measure_empty:
  assumes posf: "positive M f"
  shows "Inf (measure_set M f {}) = 0"
proof (rule antisym)
  show "0 \<le> Inf (measure_set M f {})"
    by (metis empty_subsetI inf_measure_pos posf) 
  show "Inf (measure_set M f {}) \<le> 0"
    by (metis Inf_lower empty_sets inf_measure_pos0 inf_measure_nonempty posf
              positive_imp_0 subset_refl) 
qed

lemma (in algebra) inf_measure_positive:
  "positive M f \<Longrightarrow> 
   positive (| space = space M, sets = Pow (space M) |)
                  (\<lambda>x. Inf (measure_set M f x))"
  by (simp add: positive_def inf_measure_empty inf_measure_pos) 

lemma (in algebra) inf_measure_increasing:
  assumes posf: "positive M f"
  shows "increasing (| space = space M, sets = Pow (space M) |)
                    (\<lambda>x. Inf (measure_set M f x))"
apply (auto simp add: increasing_def) 
apply (rule Inf_greatest, metis emptyE inf_measure_nonempty top posf)
apply (rule Inf_lower) 
apply (clarsimp simp add: measure_set_def, blast) 
apply (blast intro: inf_measure_pos0 posf)
done


lemma (in algebra) inf_measure_le:
  assumes posf: "positive M f" and inc: "increasing M f" 
      and x: "x \<in> {r . \<exists>A. range A \<subseteq> sets M & s \<subseteq> (\<Union>i. A i) & (f \<circ> A) sums r}"
  shows "Inf (measure_set M f s) \<le> x"
proof -
  from x
  obtain A where A: "range A \<subseteq> sets M" and ss: "s \<subseteq> (\<Union>i. A i)" 
             and sm: "summable (f \<circ> A)" and xeq: "suminf (f \<circ> A) = x"
    by (auto simp add: sums_iff)
  have dA: "range (disjointed A) \<subseteq> sets M"
    by (metis A range_disjointed_sets)
  have "\<forall>n. \<bar>(f o disjointed A) n\<bar> \<le> (f \<circ> A) n"
    proof (auto)
      fix n
      have "\<bar>f (disjointed A n)\<bar> = f (disjointed A n)" using posf dA
        by (auto simp add: positive_def image_subset_iff)
      also have "... \<le> f (A n)" 
        by (metis increasingD [OF inc] UNIV_I dA image_subset_iff disjointed_subset A)
      finally show "\<bar>f (disjointed A n)\<bar> \<le> f (A n)" .
    qed
  from Series.summable_le2 [OF this sm]
  have sda:  "summable (f o disjointed A)"  
             "suminf (f o disjointed A) \<le> suminf (f \<circ> A)"
    by blast+
  hence ley: "suminf (f o disjointed A) \<le> x"
    by (metis xeq) 
  from sda have "(f \<circ> disjointed A) sums suminf (f \<circ> disjointed A)"
    by (simp add: sums_iff) 
  hence y: "suminf (f o disjointed A) \<in> measure_set M f s"
    apply (auto simp add: measure_set_def)
    apply (rule_tac x="disjointed A" in exI) 
    apply (simp add: disjoint_family_disjointed UN_disjointed_eq ss dA)
    done
  show ?thesis
    by (blast intro: Inf_lower y order_trans [OF _ ley] inf_measure_pos0 posf)
qed

lemma (in algebra) inf_measure_close:
  assumes posf: "positive M f" and e: "0 < e" and ss: "s \<subseteq> (space M)"
  shows "\<exists>A l. range A \<subseteq> sets M & disjoint_family A & s \<subseteq> (\<Union>i. A i) & 
               (f \<circ> A) sums l & l \<le> Inf (measure_set M f s) + e"
proof -
  have " measure_set M f s \<noteq> {}" 
    by (metis emptyE ss inf_measure_nonempty [OF posf top])
  hence "\<exists>l \<in> measure_set M f s. l < Inf (measure_set M f s) + e" 
    by (rule Inf_close [OF _ e])
  thus ?thesis 
    by (auto simp add: measure_set_def, rule_tac x=" A" in exI, auto)
qed

lemma (in algebra) inf_measure_countably_subadditive:
  assumes posf: "positive M f" and inc: "increasing M f" 
  shows "countably_subadditive (| space = space M, sets = Pow (space M) |)
                  (\<lambda>x. Inf (measure_set M f x))"
proof (auto simp add: countably_subadditive_def o_def, rule field_le_epsilon)
  fix A :: "nat \<Rightarrow> 'a set" and e :: real
    assume A: "range A \<subseteq> Pow (space M)"
       and disj: "disjoint_family A"
       and sb: "(\<Union>i. A i) \<subseteq> space M"
       and sum1: "summable (\<lambda>n. Inf (measure_set M f (A n)))"
       and e: "0 < e"
    have "!!n. \<exists>B l. range B \<subseteq> sets M \<and> disjoint_family B \<and> A n \<subseteq> (\<Union>i. B i) \<and>
                    (f o B) sums l \<and>
                    l \<le> Inf (measure_set M f (A n)) + e * (1/2)^(Suc n)"
      apply (rule inf_measure_close [OF posf])
      apply (metis e half mult_pos_pos zero_less_power) 
      apply (metis UNIV_I UN_subset_iff sb)
      done
    hence "\<exists>BB ll. \<forall>n. range (BB n) \<subseteq> sets M \<and> disjoint_family (BB n) \<and>
                       A n \<subseteq> (\<Union>i. BB n i) \<and> (f o BB n) sums ll n \<and>
                       ll n \<le> Inf (measure_set M f (A n)) + e * (1/2)^(Suc n)"
      by (rule choice2)
    then obtain BB ll
      where BB: "!!n. (range (BB n) \<subseteq> sets M)"
        and disjBB: "!!n. disjoint_family (BB n)" 
        and sbBB: "!!n. A n \<subseteq> (\<Union>i. BB n i)"
        and BBsums: "!!n. (f o BB n) sums ll n"
        and ll: "!!n. ll n \<le> Inf (measure_set M f (A n)) + e * (1/2)^(Suc n)"
      by auto blast
    have llpos: "!!n. 0 \<le> ll n"
        by (metis BBsums sums_iff o_apply posf positive_imp_pos suminf_ge_zero 
              range_subsetD BB) 
    have sll: "summable ll &
               suminf ll \<le> suminf (\<lambda>n. Inf (measure_set M f (A n))) + e"
      proof -
        have "(\<lambda>n. e * (1/2)^(Suc n)) sums (e*1)"
          by (rule sums_mult [OF power_half_series]) 
        hence sum0: "summable (\<lambda>n. e * (1 / 2) ^ Suc n)"
          and eqe:  "(\<Sum>n. e * (1 / 2) ^ n / 2) = e"
          by (auto simp add: sums_iff) 
        have 0: "suminf (\<lambda>n. Inf (measure_set M f (A n))) +
                 suminf (\<lambda>n. e * (1/2)^(Suc n)) =
                 suminf (\<lambda>n. Inf (measure_set M f (A n)) + e * (1/2)^(Suc n))"
          by (rule suminf_add [OF sum1 sum0]) 
        have 1: "\<forall>n. \<bar>ll n\<bar> \<le> Inf (measure_set M f (A n)) + e * (1/2) ^ Suc n"
          by (metis ll llpos abs_of_nonneg)
        have 2: "summable (\<lambda>n. Inf (measure_set M f (A n)) + e*(1/2)^(Suc n))"
          by (rule summable_add [OF sum1 sum0]) 
        have "suminf ll \<le> (\<Sum>n. Inf (measure_set M f (A n)) + e*(1/2) ^ Suc n)"
          using Series.summable_le2 [OF 1 2] by auto
        also have "... = (\<Sum>n. Inf (measure_set M f (A n))) + 
                         (\<Sum>n. e * (1 / 2) ^ Suc n)"
          by (metis 0) 
        also have "... = (\<Sum>n. Inf (measure_set M f (A n))) + e"
          by (simp add: eqe) 
        finally show ?thesis using  Series.summable_le2 [OF 1 2] by auto
      qed
    def C \<equiv> "(split BB) o nat_to_nat2"
    have C: "!!n. C n \<in> sets M"
      apply (rule_tac p="nat_to_nat2 n" in PairE)
      apply (simp add: C_def)
      apply (metis BB subsetD rangeI)  
      done
    have sbC: "(\<Union>i. A i) \<subseteq> (\<Union>i. C i)"
      proof (auto simp add: C_def)
        fix x i
        assume x: "x \<in> A i"
        with sbBB [of i] obtain j where "x \<in> BB i j"
          by blast        
        thus "\<exists>i. x \<in> split BB (nat_to_nat2 i)"
          by (metis nat_to_nat2_surj internal_split_def prod.cases 
                prod_case_split surj_f_inv_f)
      qed 
    have "(f \<circ> C) = (f \<circ> (\<lambda>(x, y). BB x y)) \<circ> nat_to_nat2"
      by (rule ext)  (auto simp add: C_def) 
    also have "... sums suminf ll" 
      proof (rule suminf_2dimen)
        show "\<And>m n. 0 \<le> (f \<circ> (\<lambda>(x, y). BB x y)) (m, n)" using posf BB 
          by (force simp add: positive_def)
        show "\<And>m. (\<lambda>n. (f \<circ> (\<lambda>(x, y). BB x y)) (m, n)) sums ll m"using BBsums BB
          by (force simp add: o_def)
        show "summable ll" using sll
          by auto
      qed
    finally have Csums: "(f \<circ> C) sums suminf ll" .
    have "Inf (measure_set M f (\<Union>i. A i)) \<le> suminf ll"
      apply (rule inf_measure_le [OF posf inc], auto)
      apply (rule_tac x="C" in exI)
      apply (auto simp add: C sbC Csums) 
      done
    also have "... \<le> (\<Sum>n. Inf (measure_set M f (A n))) + e" using sll
      by blast
    finally show "Inf (measure_set M f (\<Union>i. A i)) \<le> 
          (\<Sum>n. Inf (measure_set M f (A n))) + e" .
qed

lemma (in algebra) inf_measure_outer:
  "positive M f \<Longrightarrow> increasing M f 
   \<Longrightarrow> outer_measure_space (| space = space M, sets = Pow (space M) |)
                          (\<lambda>x. Inf (measure_set M f x))"
  by (simp add: outer_measure_space_def inf_measure_positive
                inf_measure_increasing inf_measure_countably_subadditive) 

(*MOVE UP*)

lemma (in algebra) algebra_subset_lambda_system:
  assumes posf: "positive M f" and inc: "increasing M f" 
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
    proof (rule field_le_epsilon) 
      fix e :: real
      assume e: "0 < e"
      from inf_measure_close [OF posf e s]
      obtain A l where A: "range A \<subseteq> sets M" and disj: "disjoint_family A"
                   and sUN: "s \<subseteq> (\<Union>i. A i)" and fsums: "(f \<circ> A) sums l"
                   and l: "l \<le> Inf (measure_set M f s) + e"
        by auto
      have [simp]: "!!x. x \<in> sets M \<Longrightarrow>
                      (f o (\<lambda>z. z \<inter> (space M - x)) o A) = (f o (\<lambda>z. z - x) o A)"
        by (rule ext, simp, metis A Int_Diff Int_space_eq2 range_subsetD)
      have  [simp]: "!!n. f (A n \<inter> x) + f (A n - x) = f (A n)"
        by (subst additiveD [OF add, symmetric])
           (auto simp add: x range_subsetD [OF A] Int_Diff_Un Int_Diff_disjoint)
      have fsumb: "summable (f \<circ> A)"
        by (metis fsums sums_iff) 
      { fix u
        assume u: "u \<in> sets M"
        have [simp]: "\<And>n. \<bar>f (A n \<inter> u)\<bar> \<le> f (A n)"
          by (simp add: positive_imp_pos [OF posf]  increasingD [OF inc] 
                        u Int  range_subsetD [OF A]) 
        have 1: "summable (f o (\<lambda>z. z\<inter>u) o A)" 
          by (rule summable_comparison_test [OF _ fsumb]) simp
        have 2: "Inf (measure_set M f (s\<inter>u)) \<le> suminf (f o (\<lambda>z. z\<inter>u) o A)"
          proof (rule Inf_lower) 
            show "suminf (f \<circ> (\<lambda>z. z \<inter> u) \<circ> A) \<in> measure_set M f (s \<inter> u)"
              apply (simp add: measure_set_def) 
              apply (rule_tac x="(\<lambda>z. z \<inter> u) o A" in exI) 
              apply (auto simp add: disjoint_family_subset [OF disj])
              apply (blast intro: u range_subsetD [OF A]) 
              apply (blast dest: subsetD [OF sUN])
              apply (metis 1 o_assoc sums_iff) 
              done
          next
            show "\<And>x. x \<in> measure_set M f (s \<inter> u) \<Longrightarrow> 0 \<le> x"
              by (blast intro: inf_measure_pos0 [OF posf]) 
            qed
          note 1 2
      } note lesum = this
      have sum1: "summable (f o (\<lambda>z. z\<inter>x) o A)"
        and inf1: "Inf (measure_set M f (s\<inter>x)) \<le> suminf (f o (\<lambda>z. z\<inter>x) o A)"
        and sum2: "summable (f o (\<lambda>z. z \<inter> (space M - x)) o A)"
        and inf2: "Inf (measure_set M f (s \<inter> (space M - x))) 
                   \<le> suminf (f o (\<lambda>z. z \<inter> (space M - x)) o A)"
        by (metis Diff lesum top x)+
      hence "Inf (measure_set M f (s\<inter>x)) + Inf (measure_set M f (s-x))
           \<le> suminf (f o (\<lambda>s. s\<inter>x) o A) + suminf (f o (\<lambda>s. s-x) o A)"
        by (simp add: x)
      also have "... \<le> suminf (f o A)" using suminf_add [OF sum1 sum2] 
        by (simp add: x) (simp add: o_def) 
      also have "... \<le> Inf (measure_set M f s) + e"
        by (metis fsums l sums_unique) 
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
     "measure_space N \<Longrightarrow> sigma_algebra M \<Longrightarrow> sets M \<subseteq> sets N \<Longrightarrow>
      (measure M = measure N) \<Longrightarrow> measure_space M"
  by (simp add: measure_space_def measure_space_axioms_def positive_def 
                countably_additive_def) 
     blast

theorem (in algebra) caratheodory:
  assumes posf: "positive M f" and ca: "countably_additive M f" 
  shows "\<exists>MS :: 'a measure_space. 
             (\<forall>s \<in> sets M. measure MS s = f s) \<and>
             ((|space = space MS, sets = sets MS|) = sigma (space M) (sets M)) \<and>
             measure_space MS" 
  proof -
    have inc: "increasing M f"
      by (metis additive_increasing ca countably_additive_additive posf) 
    let ?infm = "(\<lambda>x. Inf (measure_set M f x))"
    def ls \<equiv> "lambda_system (|space = space M, sets = Pow (space M)|) ?infm"
    have mls: "measure_space (|space = space M, sets = ls, measure = ?infm|)"
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
    have "measure_space (|space = space M, 
                          sets = sigma_sets (space M) (sets M),
                          measure = ?infm|)"
      by (rule measure_down [OF mls], rule sigma_algebra_sigma_sets) 
         (simp_all add: sgs_sb space_closed)
    thus ?thesis
      by (force simp add: sigma_def inf_measure_agrees [OF posf ca]) 
qed

end
