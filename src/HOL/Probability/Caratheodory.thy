(*  Title:      HOL/Probability/Caratheodory.thy
    Author:     Lawrence C Paulson
    Author:     Johannes Hölzl, TU München
*)

header {*Caratheodory Extension Theorem*}

theory Caratheodory
  imports Measure_Space
begin

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

definition subadditive where "subadditive M f \<longleftrightarrow>
  (\<forall>x\<in>M. \<forall>y\<in>M. x \<inter> y = {} \<longrightarrow> f (x \<union> y) \<le> f x + f y)"

definition countably_subadditive where "countably_subadditive M f \<longleftrightarrow>
  (\<forall>A. range A \<subseteq> M \<longrightarrow> disjoint_family A \<longrightarrow> (\<Union>i. A i) \<in> M \<longrightarrow>
    (f (\<Union>i. A i) \<le> (\<Sum>i. f (A i))))"

definition lambda_system where "lambda_system \<Omega> M f = {l \<in> M.
  \<forall>x \<in> M. f (l \<inter> x) + f ((\<Omega> - l) \<inter> x) = f x}"

definition outer_measure_space where "outer_measure_space M f \<longleftrightarrow>
  positive M f \<and> increasing M f \<and> countably_subadditive M f"

definition measure_set where "measure_set M f X = {r.
  \<exists>A. range A \<subseteq> M \<and> disjoint_family A \<and> X \<subseteq> (\<Union>i. A i) \<and> (\<Sum>i. f (A i)) = r}"

lemma subadditiveD:
  "subadditive M f \<Longrightarrow> x \<inter> y = {} \<Longrightarrow> x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> f (x \<union> y) \<le> f x + f y"
  by (auto simp add: subadditive_def)

subsection {* Lambda Systems *}

lemma (in algebra) lambda_system_eq:
  shows "lambda_system \<Omega> M f = {l \<in> M. \<forall>x \<in> M. f (x \<inter> l) + f (x - l) = f x}"
proof -
  have [simp]: "!!l x. l \<in> M \<Longrightarrow> x \<in> M \<Longrightarrow> (\<Omega> - l) \<inter> x = x - l"
    by (metis Int_Diff Int_absorb1 Int_commute sets_into_space)
  show ?thesis
    by (auto simp add: lambda_system_def) (metis Int_commute)+
qed

lemma (in algebra) lambda_system_empty:
  "positive M f \<Longrightarrow> {} \<in> lambda_system \<Omega> M f"
  by (auto simp add: positive_def lambda_system_eq)

lemma lambda_system_sets:
  "x \<in> lambda_system \<Omega> M f \<Longrightarrow> x \<in> M"
  by (simp add: lambda_system_def)

lemma (in algebra) lambda_system_Compl:
  fixes f:: "'a set \<Rightarrow> ereal"
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
  fixes f:: "'a set \<Rightarrow> ereal"
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
  fixes f:: "'a set \<Rightarrow> ereal"
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
  apply (metis lambda_system_sets set_mp sets_into_space)
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

lemma (in ring_of_sets) countably_subadditive_subadditive:
  assumes f: "positive M f" and cs: "countably_subadditive M f"
  shows  "subadditive M f"
proof (auto simp add: subadditive_def)
  fix x y
  assume x: "x \<in> M" and y: "y \<in> M" and "x \<inter> y = {}"
  hence "disjoint_family (binaryset x y)"
    by (auto simp add: disjoint_family_on_def binaryset_def)
  hence "range (binaryset x y) \<subseteq> M \<longrightarrow>
         (\<Union>i. binaryset x y i) \<in> M \<longrightarrow>
         f (\<Union>i. binaryset x y i) \<le> (\<Sum> n. f (binaryset x y n))"
    using cs by (auto simp add: countably_subadditive_def)
  hence "{x,y,{}} \<subseteq> M \<longrightarrow> x \<union> y \<in> M \<longrightarrow>
         f (x \<union> y) \<le> (\<Sum> n. f (binaryset x y n))"
    by (simp add: range_binaryset_eq UN_binaryset_eq)
  thus "f (x \<union> y) \<le>  f x + f y" using f x y
    by (auto simp add: Un o_def suminf_binaryset_eq positive_def)
qed

lemma lambda_system_increasing:
 "increasing M f \<Longrightarrow> increasing (lambda_system \<Omega> M f) f"
  by (simp add: increasing_def lambda_system_def)

lemma lambda_system_positive:
  "positive M f \<Longrightarrow> positive (lambda_system \<Omega> M f) f"
  by (simp add: positive_def lambda_system_def)

lemma (in algebra) lambda_system_strong_sum:
  fixes A:: "nat \<Rightarrow> 'a set" and f :: "'a set \<Rightarrow> ereal"
  assumes f: "positive M f" and a: "a \<in> M"
      and A: "range A \<subseteq> lambda_system \<Omega> M f"
      and disj: "disjoint_family A"
  shows  "(\<Sum>i = 0..<n. f (a \<inter>A i)) = f (a \<inter> (\<Union>i\<in>{0..<n}. A i))"
proof (induct n)
  case 0 show ?case using f by (simp add: positive_def)
next
  case (Suc n)
  have 2: "A n \<inter> UNION {0..<n} A = {}" using disj
    by (force simp add: disjoint_family_on_def neq_iff)
  have 3: "A n \<in> lambda_system \<Omega> M f" using A
    by blast
  interpret l: algebra \<Omega> "lambda_system \<Omega> M f"
    using f by (rule lambda_system_algebra)
  have 4: "UNION {0..<n} A \<in> lambda_system \<Omega> M f"
    using A l.UNION_in_sets by simp
  from Suc.hyps show ?case
    by (simp add: atLeastLessThanSuc lambda_system_strong_additive [OF a 2 3 4])
qed

lemma (in sigma_algebra) lambda_system_caratheodory:
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
    have *: "\<And>i. 0 \<le> f (A i)" using pos A'' unfolding positive_def by auto
    have dis: "\<And>N. disjoint_family_on A {..<N}" by (intro disjoint_family_on_mono[OF _ disj]) auto
    show "(\<Sum>i. f (A i)) \<le> f (\<Union>i. A i)"
      using ls.additive_sum [OF lambda_system_positive[OF pos] lambda_system_additive _ A' dis]
      using A''
      by (intro suminf_bound[OF _ *]) (auto intro!: increasingD[OF inc] countable_UN)
  qed
  {
    fix a
    assume a [iff]: "a \<in> M"
    have "f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i)) = f a"
    proof -
      show ?thesis
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
        hence "f (a \<inter> (\<Union>i. A i)) + f (a - (\<Union>i. A i)) \<le>
            (\<Sum>i. f (a \<inter> A i)) + f (a - (\<Union>i. A i))"
          by (rule add_right_mono)
        moreover
        have "(\<Sum>i. f (a \<inter> A i)) + f (a - (\<Union>i. A i)) \<le> f a"
          proof (intro suminf_bound_add allI)
            fix n
            have UNION_in: "(\<Union>i\<in>{0..<n}. A i) \<in> M"
              by (metis A'' UNION_in_sets)
            have le_fa: "f (UNION {0..<n} A \<inter> a) \<le> f a" using A''
              by (blast intro: increasingD [OF inc] A'' UNION_in_sets)
            have ls: "(\<Union>i\<in>{0..<n}. A i) \<in> lambda_system \<Omega> M f"
              using ls.UNION_in_sets by (simp add: A)
            hence eq_fa: "f a = f (a \<inter> (\<Union>i\<in>{0..<n}. A i)) + f (a - (\<Union>i\<in>{0..<n}. A i))"
              by (simp add: lambda_system_eq UNION_in)
            have "f (a - (\<Union>i. A i)) \<le> f (a - (\<Union>i\<in>{0..<n}. A i))"
              by (blast intro: increasingD [OF inc] UNION_in U_in)
            thus "(\<Sum>i<n. f (a \<inter> A i)) + f (a - (\<Union>i. A i)) \<le> f a"
              by (simp add: lambda_system_strong_sum pos A disj eq_fa add_left_mono atLeast0LessThan[symmetric])
          next
            have "\<And>i. a \<inter> A i \<in> M" using A'' by auto
            then show "\<And>i. 0 \<le> f (a \<inter> A i)" using pos[unfolded positive_def] by auto
            have "\<And>i. a - (\<Union>i. A i) \<in> M" using A'' by auto
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

lemma inf_measure_nonempty:
  assumes f: "positive M f" and b: "b \<in> M" and a: "a \<subseteq> b" "{} \<in> M"
  shows "f b \<in> measure_set M f a"
proof -
  let ?A = "\<lambda>i::nat. (if i = 0 then b else {})"
  have "(\<Sum>i. f (?A i)) = (\<Sum>i<1::nat. f (?A i))"
    by (rule suminf_finite) (simp_all add: f[unfolded positive_def])
  also have "... = f b"
    by simp
  finally show ?thesis using assms
    by (auto intro!: exI [of _ ?A]
             simp: measure_set_def disjoint_family_on_def split_if_mem2 comp_def)
qed

lemma (in ring_of_sets) inf_measure_agrees:
  assumes posf: "positive M f" and ca: "countably_additive M f"
      and s: "s \<in> M"
  shows "Inf (measure_set M f s) = f s"
  unfolding Inf_ereal_def
proof (safe intro!: Greatest_equality)
  fix z
  assume z: "z \<in> measure_set M f s"
  from this obtain A where
    A: "range A \<subseteq> M" and disj: "disjoint_family A"
    and "s \<subseteq> (\<Union>x. A x)" and si: "(\<Sum>i. f (A i)) = z"
    by (auto simp add: measure_set_def comp_def)
  hence seq: "s = (\<Union>i. A i \<inter> s)" by blast
  have inc: "increasing M f"
    by (metis additive_increasing ca countably_additive_additive posf)
  have sums: "(\<Sum>i. f (A i \<inter> s)) = f (\<Union>i. A i \<inter> s)"
    proof (rule ca[unfolded countably_additive_def, rule_format])
      show "range (\<lambda>n. A n \<inter> s) \<subseteq> M" using A s
        by blast
      show "disjoint_family (\<lambda>n. A n \<inter> s)" using disj
        by (auto simp add: disjoint_family_on_def)
      show "(\<Union>i. A i \<inter> s) \<in> M" using A s
        by (metis UN_extend_simps(4) s seq)
    qed
  hence "f s = (\<Sum>i. f (A i \<inter> s))"
    using seq [symmetric] by (simp add: sums_iff)
  also have "... \<le> (\<Sum>i. f (A i))"
    proof (rule suminf_le_pos)
      fix n show "f (A n \<inter> s) \<le> f (A n)" using A s
        by (force intro: increasingD [OF inc])
      fix N have "A N \<inter> s \<in> M"  using A s by auto
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
  obtain A where "range A \<subseteq> M" and r: "r = (\<Sum>i. f (A i))"
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
  assumes posf: "positive M f" and "{} \<in> M"
  shows "Inf (measure_set M f {}) = 0"
proof (rule antisym)
  show "Inf (measure_set M f {}) \<le> 0"
    by (metis complete_lattice_class.Inf_lower `{} \<in> M`
              inf_measure_nonempty[OF posf] subset_refl posf[unfolded positive_def])
qed (rule inf_measure_pos[OF posf])

lemma (in ring_of_sets) inf_measure_positive:
  assumes p: "positive M f" and "{} \<in> M"
  shows "positive M (\<lambda>x. Inf (measure_set M f x))"
proof (unfold positive_def, intro conjI ballI)
  show "Inf (measure_set M f {}) = 0" using inf_measure_empty[OF assms] by auto
  fix A assume "A \<in> M"
qed (rule inf_measure_pos[OF p])

lemma (in ring_of_sets) inf_measure_increasing:
  assumes posf: "positive M f"
  shows "increasing (Pow \<Omega>) (\<lambda>x. Inf (measure_set M f x))"
apply (clarsimp simp add: increasing_def)
apply (rule complete_lattice_class.Inf_greatest)
apply (rule complete_lattice_class.Inf_lower)
apply (clarsimp simp add: measure_set_def, rule_tac x=A in exI, blast)
done

lemma (in ring_of_sets) inf_measure_le:
  assumes posf: "positive M f" and inc: "increasing M f"
      and x: "x \<in> {r . \<exists>A. range A \<subseteq> M \<and> s \<subseteq> (\<Union>i. A i) \<and> (\<Sum>i. f (A i)) = r}"
  shows "Inf (measure_set M f s) \<le> x"
proof -
  obtain A where A: "range A \<subseteq> M" and ss: "s \<subseteq> (\<Union>i. A i)"
             and xeq: "(\<Sum>i. f (A i)) = x"
    using x by auto
  have dA: "range (disjointed A) \<subseteq> M"
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
  assumes posf: "positive M f" and e: "0 < e" and ss: "s \<subseteq> (\<Omega>)" and "Inf (measure_set M f s) \<noteq> \<infinity>"
  shows "\<exists>A. range A \<subseteq> M \<and> disjoint_family A \<and> s \<subseteq> (\<Union>i. A i) \<and>
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
  shows "countably_subadditive (Pow \<Omega>) (\<lambda>x. Inf (measure_set M f x))"
proof (simp add: countably_subadditive_def, safe)
  fix A :: "nat \<Rightarrow> 'a set"
  let ?outer = "\<lambda>B. Inf (measure_set M f B)"
  assume A: "range A \<subseteq> Pow (\<Omega>)"
     and disj: "disjoint_family A"
     and sb: "(\<Union>i. A i) \<subseteq> \<Omega>"

  { fix e :: ereal assume e: "0 < e" and "\<forall>i. ?outer (A i) \<noteq> \<infinity>"
    hence "\<exists>BB. \<forall>n. range (BB n) \<subseteq> M \<and> disjoint_family (BB n) \<and>
        A n \<subseteq> (\<Union>i. BB n i) \<and> (\<Sum>i. f (BB n i)) \<le> ?outer (A n) + e * (1/2)^(Suc n)"
      apply (safe intro!: choice inf_measure_close [of f, OF posf])
      using e sb by (auto simp: ereal_zero_less_0_iff one_ereal_def)
    then obtain BB
      where BB: "\<And>n. (range (BB n) \<subseteq> M)"
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
    have C: "!!n. C n \<in> M"
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
  "\<lbrakk> positive M f ; increasing M f \<rbrakk> \<Longrightarrow>
    outer_measure_space (Pow \<Omega>) (\<lambda>x. Inf (measure_set M f x))"
  using inf_measure_pos[of M f]
  by (simp add: outer_measure_space_def inf_measure_empty
                inf_measure_increasing inf_measure_countably_subadditive positive_def)

lemma (in ring_of_sets) algebra_subset_lambda_system:
  assumes posf: "positive M f" and inc: "increasing M f"
      and add: "additive M f"
  shows "M \<subseteq> lambda_system \<Omega> (Pow \<Omega>) (\<lambda>x. Inf (measure_set M f x))"
proof (auto dest: sets_into_space
            simp add: algebra.lambda_system_eq [OF algebra_Pow])
  fix x s
  assume x: "x \<in> M"
     and s: "s \<subseteq> \<Omega>"
  have [simp]: "!!x. x \<in> M \<Longrightarrow> s \<inter> (\<Omega> - x) = s-x" using s
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
      then obtain A where A: "disjoint_family A" "range A \<subseteq> M" "s \<subseteq> (\<Union>i. A i)"
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
  "measure_space \<Omega> N \<mu> \<Longrightarrow> sigma_algebra \<Omega> M \<Longrightarrow> M \<subseteq> N \<Longrightarrow> measure_space \<Omega> M \<mu>"
  by (simp add: measure_space_def positive_def countably_additive_def)
     blast

theorem (in ring_of_sets) caratheodory':
  assumes posf: "positive M f" and ca: "countably_additive M f"
  shows "\<exists>\<mu> :: 'a set \<Rightarrow> ereal. (\<forall>s \<in> M. \<mu> s = f s) \<and> measure_space \<Omega> (sigma_sets \<Omega> M) \<mu>"
proof -
  have inc: "increasing M f"
    by (metis additive_increasing ca countably_additive_additive posf)
  let ?infm = "(\<lambda>x. Inf (measure_set M f x))"
  def ls \<equiv> "lambda_system \<Omega> (Pow \<Omega>) ?infm"
  have mls: "measure_space \<Omega> ls ?infm"
    using sigma_algebra.caratheodory_lemma
            [OF sigma_algebra_Pow  inf_measure_outer [OF posf inc]]
    by (simp add: ls_def)
  hence sls: "sigma_algebra \<Omega> ls"
    by (simp add: measure_space_def)
  have "M \<subseteq> ls"
    by (simp add: ls_def)
       (metis ca posf inc countably_additive_additive algebra_subset_lambda_system)
  hence sgs_sb: "sigma_sets (\<Omega>) (M) \<subseteq> ls"
    using sigma_algebra.sigma_sets_subset [OF sls, of "M"]
    by simp
  have "measure_space \<Omega> (sigma_sets \<Omega> M) ?infm"
    by (rule measure_down [OF mls], rule sigma_algebra_sigma_sets)
       (simp_all add: sgs_sb space_closed)
  thus ?thesis using inf_measure_agrees [OF posf ca]
    by (intro exI[of _ ?infm]) auto
qed

subsubsection {*Alternative instances of caratheodory*}

lemma (in ring_of_sets) caratheodory_empty_continuous:
  assumes f: "positive M f" "additive M f" and fin: "\<And>A. A \<in> M \<Longrightarrow> f A \<noteq> \<infinity>"
  assumes cont: "\<And>A. range A \<subseteq> M \<Longrightarrow> decseq A \<Longrightarrow> (\<Inter>i. A i) = {} \<Longrightarrow> (\<lambda>i. f (A i)) ----> 0"
  shows "\<exists>\<mu> :: 'a set \<Rightarrow> ereal. (\<forall>s \<in> M. \<mu> s = f s) \<and> measure_space \<Omega> (sigma_sets \<Omega> M) \<mu>"
proof (intro caratheodory' empty_continuous_imp_countably_additive f)
  show "\<forall>A\<in>M. f A \<noteq> \<infinity>" using fin by auto
qed (rule cont)

section {* Volumes *}

definition volume :: "'a set set \<Rightarrow> ('a set \<Rightarrow> ereal) \<Rightarrow> bool" where
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

lemma volume_finite_additive:
  assumes "volume M f" 
  assumes A: "\<And>i. i \<in> I \<Longrightarrow> A i \<in> M" "disjoint_family_on A I" "finite I" "UNION I A \<in> M"
  shows "f (UNION I A) = (\<Sum>i\<in>I. f (A i))"
proof -
  have "A`I \<subseteq> M" "disjoint (A`I)" "finite (A`I)" "\<Union>A`I \<in> M"
    using A unfolding SUP_def by (auto simp: disjoint_family_on_disjoint_image)
  with `volume M f` have "f (\<Union>A`I) = (\<Sum>a\<in>A`I. f a)"
    unfolding volume_def by blast
  also have "\<dots> = (\<Sum>i\<in>I. f (A i))"
  proof (subst setsum_reindex_nonzero)
    fix i j assume "i \<in> I" "j \<in> I" "i \<noteq> j" "A i = A j"
    with `disjoint_family_on A I` have "A i = {}"
      by (auto simp: disjoint_family_on_def)
    then show "f (A i) = 0"
      using volume_empty[OF `volume M f`] by simp
  qed (auto intro: `finite I`)
  finally show "f (UNION I A) = (\<Sum>i\<in>I. f (A i))"
    by simp
qed

lemma (in ring_of_sets) volume_additiveI:
  assumes pos: "\<And>a. a \<in> M \<Longrightarrow> 0 \<le> \<mu> a" 
  assumes [simp]: "\<mu> {} = 0"
  assumes add: "\<And>a b. a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> a \<inter> b = {} \<Longrightarrow> \<mu> (a \<union> b) = \<mu> a + \<mu> b"
  shows "volume M \<mu>"
proof (unfold volume_def, safe)
  fix C assume "finite C" "C \<subseteq> M" "disjoint C"
  then show "\<mu> (\<Union>C) = setsum \<mu> C"
  proof (induct C)
    case (insert c C)
    from insert(1,2,4,5) have "\<mu> (\<Union>insert c C) = \<mu> c + \<mu> (\<Union>C)"
      by (auto intro!: add simp: disjoint_def)
    with insert show ?case
      by (simp add: disjoint_def)
  qed simp
qed fact+

lemma (in semiring_of_sets) extend_volume:
  assumes "volume M \<mu>"
  shows "\<exists>\<mu>'. volume generated_ring \<mu>' \<and> (\<forall>a\<in>M. \<mu>' a = \<mu> a)"
proof -
  let ?R = generated_ring
  have "\<forall>a\<in>?R. \<exists>m. \<exists>C\<subseteq>M. a = \<Union>C \<and> finite C \<and> disjoint C \<and> m = (\<Sum>c\<in>C. \<mu> c)"
    by (auto simp: generated_ring_def)
  from bchoice[OF this] guess \<mu>' .. note \<mu>'_spec = this
  
  { fix C assume C: "C \<subseteq> M" "finite C" "disjoint C"
    fix D assume D: "D \<subseteq> M" "finite D" "disjoint D"
    assume "\<Union>C = \<Union>D"
    have "(\<Sum>d\<in>D. \<mu> d) = (\<Sum>d\<in>D. \<Sum>c\<in>C. \<mu> (c \<inter> d))"
    proof (intro setsum_cong refl)
      fix d assume "d \<in> D"
      have Un_eq_d: "(\<Union>c\<in>C. c \<inter> d) = d"
        using `d \<in> D` `\<Union>C = \<Union>D` by auto
      moreover have "\<mu> (\<Union>c\<in>C. c \<inter> d) = (\<Sum>c\<in>C. \<mu> (c \<inter> d))"
      proof (rule volume_finite_additive)
        { fix c assume "c \<in> C" then show "c \<inter> d \<in> M"
            using C D `d \<in> D` by auto }
        show "(\<Union>a\<in>C. a \<inter> d) \<in> M"
          unfolding Un_eq_d using `d \<in> D` D by auto
        show "disjoint_family_on (\<lambda>a. a \<inter> d) C"
          using `disjoint C` by (auto simp: disjoint_family_on_def disjoint_def)
      qed fact+
      ultimately show "\<mu> d = (\<Sum>c\<in>C. \<mu> (c \<inter> d))" by simp
    qed }
  note split_sum = this

  { fix C assume C: "C \<subseteq> M" "finite C" "disjoint C"
    fix D assume D: "D \<subseteq> M" "finite D" "disjoint D"
    assume "\<Union>C = \<Union>D"
    with split_sum[OF C D] split_sum[OF D C]
    have "(\<Sum>d\<in>D. \<mu> d) = (\<Sum>c\<in>C. \<mu> c)"
      by (simp, subst setsum_commute, simp add: ac_simps) }
  note sum_eq = this

  { fix C assume C: "C \<subseteq> M" "finite C" "disjoint C"
    then have "\<Union>C \<in> ?R" by (auto simp: generated_ring_def)
    with \<mu>'_spec[THEN bspec, of "\<Union>C"]
    obtain D where
      D: "D \<subseteq> M" "finite D" "disjoint D" "\<Union>C = \<Union>D" and "\<mu>' (\<Union>C) = (\<Sum>d\<in>D. \<mu> d)"
      by blast
    with sum_eq[OF C D] have "\<mu>' (\<Union>C) = (\<Sum>c\<in>C. \<mu> c)" by simp }
  note \<mu>' = this

  show ?thesis
  proof (intro exI conjI ring_of_sets.volume_additiveI[OF generating_ring] ballI)
    fix a assume "a \<in> M" with \<mu>'[of "{a}"] show "\<mu>' a = \<mu> a"
      by (simp add: disjoint_def)
  next
    fix a assume "a \<in> ?R" then guess Ca .. note Ca = this
    with \<mu>'[of Ca] `volume M \<mu>`[THEN volume_positive]
    show "0 \<le> \<mu>' a"
      by (auto intro!: setsum_nonneg)
  next
    show "\<mu>' {} = 0" using \<mu>'[of "{}"] by auto
  next
    fix a assume "a \<in> ?R" then guess Ca .. note Ca = this
    fix b assume "b \<in> ?R" then guess Cb .. note Cb = this
    assume "a \<inter> b = {}"
    with Ca Cb have "Ca \<inter> Cb \<subseteq> {{}}" by auto
    then have C_Int_cases: "Ca \<inter> Cb = {{}} \<or> Ca \<inter> Cb = {}" by auto

    from `a \<inter> b = {}` have "\<mu>' (\<Union> (Ca \<union> Cb)) = (\<Sum>c\<in>Ca \<union> Cb. \<mu> c)"
      using Ca Cb by (intro \<mu>') (auto intro!: disjoint_union)
    also have "\<dots> = (\<Sum>c\<in>Ca \<union> Cb. \<mu> c) + (\<Sum>c\<in>Ca \<inter> Cb. \<mu> c)"
      using C_Int_cases volume_empty[OF `volume M \<mu>`] by (elim disjE) simp_all
    also have "\<dots> = (\<Sum>c\<in>Ca. \<mu> c) + (\<Sum>c\<in>Cb. \<mu> c)"
      using Ca Cb by (simp add: setsum_Un_Int)
    also have "\<dots> = \<mu>' a + \<mu>' b"
      using Ca Cb by (simp add: \<mu>')
    finally show "\<mu>' (a \<union> b) = \<mu>' a + \<mu>' b"
      using Ca Cb by simp
  qed
qed

section {* Caratheodory on semirings *}

theorem (in semiring_of_sets) caratheodory:
  assumes pos: "positive M \<mu>" and ca: "countably_additive M \<mu>"
  shows "\<exists>\<mu>' :: 'a set \<Rightarrow> ereal. (\<forall>s \<in> M. \<mu>' s = \<mu> s) \<and> measure_space \<Omega> (sigma_sets \<Omega> M) \<mu>'"
proof -
  have "volume M \<mu>"
  proof (rule volumeI)
    { fix a assume "a \<in> M" then show "0 \<le> \<mu> a"
        using pos unfolding positive_def by auto }
    note p = this

    fix C assume sets_C: "C \<subseteq> M" "\<Union>C \<in> M" and "disjoint C" "finite C"
    have "\<exists>F'. bij_betw F' {..<card C} C"
      by (rule finite_same_card_bij[OF _ `finite C`]) auto
    then guess F' .. note F' = this
    then have F': "C = F' ` {..< card C}" "inj_on F' {..< card C}"
      by (auto simp: bij_betw_def)
    { fix i j assume *: "i < card C" "j < card C" "i \<noteq> j"
      with F' have "F' i \<in> C" "F' j \<in> C" "F' i \<noteq> F' j"
        unfolding inj_on_def by auto
      with `disjoint C`[THEN disjointD]
      have "F' i \<inter> F' j = {}"
        by auto }
    note F'_disj = this
    def F \<equiv> "\<lambda>i. if i < card C then F' i else {}"
    then have "disjoint_family F"
      using F'_disj by (auto simp: disjoint_family_on_def)
    moreover from F' have "(\<Union>i. F i) = \<Union>C"
      by (auto simp: F_def set_eq_iff split: split_if_asm)
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
      using F'(2) by (subst (2) F') (simp add: setsum_reindex)
    finally show "\<mu> (\<Union>C) = (\<Sum>c\<in>C. \<mu> c)" .
  next
    show "\<mu> {} = 0"
      using `positive M \<mu>` by (rule positiveD1)
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
    fix A' :: "nat \<Rightarrow> 'a set" assume A': "range A' \<subseteq> generated_ring" "disjoint_family A'"
      and Un_A: "(\<Union>i. A' i) \<in> generated_ring"

    from generated_ringE[OF Un_A] guess C' . note C' = this

    { fix c assume "c \<in> C'"
      moreover def A \<equiv> "\<lambda>i. A' i \<inter> c"
      ultimately have A: "range A \<subseteq> generated_ring" "disjoint_family A"
        and Un_A: "(\<Union>i. A i) \<in> generated_ring"
        using A' C'
        by (auto intro!: G.Int G.finite_Union intro: generated_ringI_Basic simp: disjoint_family_on_def)
      from A C' `c \<in> C'` have UN_eq: "(\<Union>i. A i) = c"
        by (auto simp: A_def)

      have "\<forall>i::nat. \<exists>f::nat \<Rightarrow> 'a set. \<mu>_r (A i) = (\<Sum>j. \<mu>_r (f j)) \<and> disjoint_family f \<and> \<Union>range f = A i \<and> (\<forall>j. f j \<in> M)"
        (is "\<forall>i. ?P i")
      proof
        fix i
        from A have Ai: "A i \<in> generated_ring" by auto
        from generated_ringE[OF this] guess C . note C = this

        have "\<exists>F'. bij_betw F' {..<card C} C"
          by (rule finite_same_card_bij[OF _ `finite C`]) auto
        then guess F .. note F = this
        def f \<equiv> "\<lambda>i. if i < card C then F i else {}"
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
        have Ai_eq: "A i = (\<Union> x<card C. f x)"
          using f C Ai unfolding bij_betw_def by (simp add: Union_image_eq[symmetric])
        then have "\<Union>range f = A i"
          using f C Ai unfolding bij_betw_def by (auto simp: f_def)
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
      from choice[OF this] guess f .. note f = this
      then have UN_f_eq: "(\<Union>i. split f (prod_decode i)) = (\<Union>i. A i)"
        unfolding UN_extend_simps surj_prod_decode by (auto simp: set_eq_iff)

      have d: "disjoint_family (\<lambda>i. split f (prod_decode i))"
        unfolding disjoint_family_on_def
      proof (intro ballI impI)
        fix m n :: nat assume "m \<noteq> n"
        then have neq: "prod_decode m \<noteq> prod_decode n"
          using inj_prod_decode[of UNIV] by (auto simp: inj_on_def)
        show "split f (prod_decode m) \<inter> split f (prod_decode n) = {}"
        proof cases
          assume "fst (prod_decode m) = fst (prod_decode n)"
          then show ?thesis
            using neq f by (fastforce simp: disjoint_family_on_def)
        next
          assume neq: "fst (prod_decode m) \<noteq> fst (prod_decode n)"
          have "split f (prod_decode m) \<subseteq> A (fst (prod_decode m))"
            "split f (prod_decode n) \<subseteq> A (fst (prod_decode n))"
            using f[THEN spec, of "fst (prod_decode m)"]
            using f[THEN spec, of "fst (prod_decode n)"]
            by (auto simp: set_eq_iff)
          with f A neq show ?thesis
            by (fastforce simp: disjoint_family_on_def subset_eq set_eq_iff)
        qed
      qed
      from f have "(\<Sum>n. \<mu>_r (A n)) = (\<Sum>n. \<mu>_r (split f (prod_decode n)))"
        by (intro suminf_ereal_2dimen[symmetric] positiveD2[OF pos] generated_ringI_Basic)
         (auto split: prod.split)
      also have "\<dots> = (\<Sum>n. \<mu> (split f (prod_decode n)))"
        using f V(2) by (auto intro!: arg_cong[where f=suminf] split: prod.split)
      also have "\<dots> = \<mu> (\<Union>i. split f (prod_decode i))"
        using f `c \<in> C'` C'
        by (intro ca[unfolded countably_additive_def, rule_format])
           (auto split: prod.split simp: UN_f_eq d UN_eq)
      finally have "(\<Sum>n. \<mu>_r (A' n \<inter> c)) = \<mu> c"
        using UN_f_eq UN_eq by (simp add: A_def) }
    note eq = this

    have "(\<Sum>n. \<mu>_r (A' n)) = (\<Sum>n. \<Sum>c\<in>C'. \<mu>_r (A' n \<inter> c))"
      using C' A'
      by (subst volume_finite_additive[symmetric, OF V(1)])
         (auto simp: disjoint_def disjoint_family_on_def Union_image_eq[symmetric] simp del: Union_image_eq
               intro!: G.Int G.finite_Union arg_cong[where f="\<lambda>X. suminf (\<lambda>i. \<mu>_r (X i))"] ext
               intro: generated_ringI_Basic)
    also have "\<dots> = (\<Sum>c\<in>C'. \<Sum>n. \<mu>_r (A' n \<inter> c))"
      using C' A'
      by (intro suminf_setsum_ereal positiveD2[OF pos] G.Int G.finite_Union)
         (auto intro: generated_ringI_Basic)
    also have "\<dots> = (\<Sum>c\<in>C'. \<mu>_r c)"
      using eq V C' by (auto intro!: setsum_cong)
    also have "\<dots> = \<mu>_r (\<Union>C')"
      using C' Un_A
      by (subst volume_finite_additive[symmetric, OF V(1)])
         (auto simp: disjoint_family_on_def disjoint_def Union_image_eq[symmetric] simp del: Union_image_eq 
               intro: generated_ringI_Basic)
    finally show "(\<Sum>n. \<mu>_r (A' n)) = \<mu>_r (\<Union>i. A' i)"
      using C' by simp
  qed
  from G.caratheodory'[OF `positive generated_ring \<mu>_r` `countably_additive generated_ring \<mu>_r`]
  guess \<mu>' ..
  with V show ?thesis
    unfolding sigma_sets_generated_ring_eq
    by (intro exI[of _ \<mu>']) (auto intro: generated_ringI_Basic)
qed

end
