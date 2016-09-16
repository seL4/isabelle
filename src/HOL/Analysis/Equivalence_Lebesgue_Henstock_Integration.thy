theory Equivalence_Lebesgue_Henstock_Integration
  imports Lebesgue_Measure Henstock_Kurzweil_Integration
begin

subsection \<open>Equivalence Lebesgue integral on @{const lborel} and HK-integral\<close>

lemma has_integral_measure_lborel:
  fixes A :: "'a::euclidean_space set"
  assumes A[measurable]: "A \<in> sets borel" and finite: "emeasure lborel A < \<infinity>"
  shows "((\<lambda>x. 1) has_integral measure lborel A) A"
proof -
  { fix l u :: 'a
    have "((\<lambda>x. 1) has_integral measure lborel (box l u)) (box l u)"
    proof cases
      assume "\<forall>b\<in>Basis. l \<bullet> b \<le> u \<bullet> b"
      then show ?thesis
        apply simp
        apply (subst has_integral_restrict[symmetric, OF box_subset_cbox])
        apply (subst has_integral_spike_interior_eq[where g="\<lambda>_. 1"])
        using has_integral_const[of "1::real" l u]
        apply (simp_all add: inner_diff_left[symmetric] content_cbox_cases)
        done
    next
      assume "\<not> (\<forall>b\<in>Basis. l \<bullet> b \<le> u \<bullet> b)"
      then have "box l u = {}"
        unfolding box_eq_empty by (auto simp: not_le intro: less_imp_le)
      then show ?thesis
        by simp
    qed }
  note has_integral_box = this

  { fix a b :: 'a let ?M = "\<lambda>A. measure lborel (A \<inter> box a b)"
    have "Int_stable  (range (\<lambda>(a, b). box a b))"
      by (auto simp: Int_stable_def box_Int_box)
    moreover have "(range (\<lambda>(a, b). box a b)) \<subseteq> Pow UNIV"
      by auto
    moreover have "A \<in> sigma_sets UNIV (range (\<lambda>(a, b). box a b))"
       using A unfolding borel_eq_box by simp
    ultimately have "((\<lambda>x. 1) has_integral ?M A) (A \<inter> box a b)"
    proof (induction rule: sigma_sets_induct_disjoint)
      case (basic A) then show ?case
        by (auto simp: box_Int_box has_integral_box)
    next
      case empty then show ?case
        by simp
    next
      case (compl A)
      then have [measurable]: "A \<in> sets borel"
        by (simp add: borel_eq_box)

      have "((\<lambda>x. 1) has_integral ?M (box a b)) (box a b)"
        by (simp add: has_integral_box)
      moreover have "((\<lambda>x. if x \<in> A \<inter> box a b then 1 else 0) has_integral ?M A) (box a b)"
        by (subst has_integral_restrict) (auto intro: compl)
      ultimately have "((\<lambda>x. 1 - (if x \<in> A \<inter> box a b then 1 else 0)) has_integral ?M (box a b) - ?M A) (box a b)"
        by (rule has_integral_sub)
      then have "((\<lambda>x. (if x \<in> (UNIV - A) \<inter> box a b then 1 else 0)) has_integral ?M (box a b) - ?M A) (box a b)"
        by (rule has_integral_cong[THEN iffD1, rotated 1]) auto
      then have "((\<lambda>x. 1) has_integral ?M (box a b) - ?M A) ((UNIV - A) \<inter> box a b)"
        by (subst (asm) has_integral_restrict) auto
      also have "?M (box a b) - ?M A = ?M (UNIV - A)"
        by (subst measure_Diff[symmetric]) (auto simp: emeasure_lborel_box_eq Diff_Int_distrib2)
      finally show ?case .
    next
      case (union F)
      then have [measurable]: "\<And>i. F i \<in> sets borel"
        by (simp add: borel_eq_box subset_eq)
      have "((\<lambda>x. if x \<in> UNION UNIV F \<inter> box a b then 1 else 0) has_integral ?M (\<Union>i. F i)) (box a b)"
      proof (rule has_integral_monotone_convergence_increasing)
        let ?f = "\<lambda>k x. \<Sum>i<k. if x \<in> F i \<inter> box a b then 1 else 0 :: real"
        show "\<And>k. (?f k has_integral (\<Sum>i<k. ?M (F i))) (box a b)"
          using union.IH by (auto intro!: has_integral_setsum simp del: Int_iff)
        show "\<And>k x. ?f k x \<le> ?f (Suc k) x"
          by (intro setsum_mono2) auto
        from union(1) have *: "\<And>x i j. x \<in> F i \<Longrightarrow> x \<in> F j \<longleftrightarrow> j = i"
          by (auto simp add: disjoint_family_on_def)
        show "\<And>x. (\<lambda>k. ?f k x) \<longlonglongrightarrow> (if x \<in> UNION UNIV F \<inter> box a b then 1 else 0)"
          apply (auto simp: * setsum.If_cases Iio_Int_singleton)
          apply (rule_tac k="Suc xa" in LIMSEQ_offset)
          apply simp
          done
        have *: "emeasure lborel ((\<Union>x. F x) \<inter> box a b) \<le> emeasure lborel (box a b)"
          by (intro emeasure_mono) auto

        with union(1) show "(\<lambda>k. \<Sum>i<k. ?M (F i)) \<longlonglongrightarrow> ?M (\<Union>i. F i)"
          unfolding sums_def[symmetric] UN_extend_simps
          by (intro measure_UNION) (auto simp: disjoint_family_on_def emeasure_lborel_box_eq top_unique)
      qed
      then show ?case
        by (subst (asm) has_integral_restrict) auto
    qed }
  note * = this

  show ?thesis
  proof (rule has_integral_monotone_convergence_increasing)
    let ?B = "\<lambda>n::nat. box (- real n *\<^sub>R One) (real n *\<^sub>R One) :: 'a set"
    let ?f = "\<lambda>n::nat. \<lambda>x. if x \<in> A \<inter> ?B n then 1 else 0 :: real"
    let ?M = "\<lambda>n. measure lborel (A \<inter> ?B n)"

    show "\<And>n::nat. (?f n has_integral ?M n) A"
      using * by (subst has_integral_restrict) simp_all
    show "\<And>k x. ?f k x \<le> ?f (Suc k) x"
      by (auto simp: box_def)
    { fix x assume "x \<in> A"
      moreover have "(\<lambda>k. indicator (A \<inter> ?B k) x :: real) \<longlonglongrightarrow> indicator (\<Union>k::nat. A \<inter> ?B k) x"
        by (intro LIMSEQ_indicator_incseq) (auto simp: incseq_def box_def)
      ultimately show "(\<lambda>k. if x \<in> A \<inter> ?B k then 1 else 0::real) \<longlonglongrightarrow> 1"
        by (simp add: indicator_def UN_box_eq_UNIV) }

    have "(\<lambda>n. emeasure lborel (A \<inter> ?B n)) \<longlonglongrightarrow> emeasure lborel (\<Union>n::nat. A \<inter> ?B n)"
      by (intro Lim_emeasure_incseq) (auto simp: incseq_def box_def)
    also have "(\<lambda>n. emeasure lborel (A \<inter> ?B n)) = (\<lambda>n. measure lborel (A \<inter> ?B n))"
    proof (intro ext emeasure_eq_ennreal_measure)
      fix n have "emeasure lborel (A \<inter> ?B n) \<le> emeasure lborel (?B n)"
        by (intro emeasure_mono) auto
      then show "emeasure lborel (A \<inter> ?B n) \<noteq> top"
        by (auto simp: top_unique)
    qed
    finally show "(\<lambda>n. measure lborel (A \<inter> ?B n)) \<longlonglongrightarrow> measure lborel A"
      using emeasure_eq_ennreal_measure[of lborel A] finite
      by (simp add: UN_box_eq_UNIV less_top)
  qed
qed

lemma nn_integral_has_integral:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable borel" "\<And>x. 0 \<le> f x" "(\<integral>\<^sup>+x. f x \<partial>lborel) = ennreal r" "0 \<le> r"
  shows "(f has_integral r) UNIV"
using f proof (induct f arbitrary: r rule: borel_measurable_induct_real)
  case (set A)
  then have "((\<lambda>x. 1) has_integral measure lborel A) A"
    by (intro has_integral_measure_lborel) (auto simp: ennreal_indicator)
  with set show ?case
    by (simp add: ennreal_indicator measure_def) (simp add: indicator_def)
next
  case (mult g c)
  then have "ennreal c * (\<integral>\<^sup>+ x. g x \<partial>lborel) = ennreal r"
    by (subst nn_integral_cmult[symmetric]) (auto simp: ennreal_mult)
  with \<open>0 \<le> r\<close> \<open>0 \<le> c\<close>
  obtain r' where "(c = 0 \<and> r = 0) \<or> (0 \<le> r' \<and> (\<integral>\<^sup>+ x. ennreal (g x) \<partial>lborel) = ennreal r' \<and> r = c * r')"
    by (cases "\<integral>\<^sup>+ x. ennreal (g x) \<partial>lborel" rule: ennreal_cases)
       (auto split: if_split_asm simp: ennreal_mult_top ennreal_mult[symmetric])
  with mult show ?case
    by (auto intro!: has_integral_cmult_real)
next
  case (add g h)
  then have "(\<integral>\<^sup>+ x. h x + g x \<partial>lborel) = (\<integral>\<^sup>+ x. h x \<partial>lborel) + (\<integral>\<^sup>+ x. g x \<partial>lborel)"
    by (simp add: nn_integral_add)
  with add obtain a b where "0 \<le> a" "0 \<le> b" "(\<integral>\<^sup>+ x. h x \<partial>lborel) = ennreal a" "(\<integral>\<^sup>+ x. g x \<partial>lborel) = ennreal b" "r = a + b"
    by (cases "\<integral>\<^sup>+ x. h x \<partial>lborel" "\<integral>\<^sup>+ x. g x \<partial>lborel" rule: ennreal2_cases)
       (auto simp: add_top nn_integral_add top_add ennreal_plus[symmetric] simp del: ennreal_plus)
  with add show ?case
    by (auto intro!: has_integral_add)
next
  case (seq U)
  note seq(1)[measurable] and f[measurable]

  { fix i x
    have "U i x \<le> f x"
      using seq(5)
      apply (rule LIMSEQ_le_const)
      using seq(4)
      apply (auto intro!: exI[of _ i] simp: incseq_def le_fun_def)
      done }
  note U_le_f = this

  { fix i
    have "(\<integral>\<^sup>+x. U i x \<partial>lborel) \<le> (\<integral>\<^sup>+x. f x \<partial>lborel)"
      using seq(2) f(2) U_le_f by (intro nn_integral_mono) simp
    then obtain p where "(\<integral>\<^sup>+x. U i x \<partial>lborel) = ennreal p" "p \<le> r" "0 \<le> p"
      using seq(6) \<open>0\<le>r\<close> by (cases "\<integral>\<^sup>+x. U i x \<partial>lborel" rule: ennreal_cases) (auto simp: top_unique)
    moreover note seq
    ultimately have "\<exists>p. (\<integral>\<^sup>+x. U i x \<partial>lborel) = ennreal p \<and> 0 \<le> p \<and> p \<le> r \<and> (U i has_integral p) UNIV"
      by auto }
  then obtain p where p: "\<And>i. (\<integral>\<^sup>+x. ennreal (U i x) \<partial>lborel) = ennreal (p i)"
    and bnd: "\<And>i. p i \<le> r" "\<And>i. 0 \<le> p i"
    and U_int: "\<And>i.(U i has_integral (p i)) UNIV" by metis

  have int_eq: "\<And>i. integral UNIV (U i) = p i" using U_int by (rule integral_unique)

  have *: "f integrable_on UNIV \<and> (\<lambda>k. integral UNIV (U k)) \<longlonglongrightarrow> integral UNIV f"
  proof (rule monotone_convergence_increasing)
    show "\<forall>k. U k integrable_on UNIV" using U_int by auto
    show "\<forall>k. \<forall>x\<in>UNIV. U k x \<le> U (Suc k) x" using \<open>incseq U\<close> by (auto simp: incseq_def le_fun_def)
    then show "bounded {integral UNIV (U k) |k. True}"
      using bnd int_eq by (auto simp: bounded_real intro!: exI[of _ r])
    show "\<forall>x\<in>UNIV. (\<lambda>k. U k x) \<longlonglongrightarrow> f x"
      using seq by auto
  qed
  moreover have "(\<lambda>i. (\<integral>\<^sup>+x. U i x \<partial>lborel)) \<longlonglongrightarrow> (\<integral>\<^sup>+x. f x \<partial>lborel)"
    using seq f(2) U_le_f by (intro nn_integral_dominated_convergence[where w=f]) auto
  ultimately have "integral UNIV f = r"
    by (auto simp add: bnd int_eq p seq intro: LIMSEQ_unique)
  with * show ?case
    by (simp add: has_integral_integral)
qed

lemma nn_integral_lborel_eq_integral:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable borel" "\<And>x. 0 \<le> f x" "(\<integral>\<^sup>+x. f x \<partial>lborel) < \<infinity>"
  shows "(\<integral>\<^sup>+x. f x \<partial>lborel) = integral UNIV f"
proof -
  from f(3) obtain r where r: "(\<integral>\<^sup>+x. f x \<partial>lborel) = ennreal r" "0 \<le> r"
    by (cases "\<integral>\<^sup>+x. f x \<partial>lborel" rule: ennreal_cases) auto
  then show ?thesis
    using nn_integral_has_integral[OF f(1,2) r] by (simp add: integral_unique)
qed

lemma nn_integral_integrable_on:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable borel" "\<And>x. 0 \<le> f x" "(\<integral>\<^sup>+x. f x \<partial>lborel) < \<infinity>"
  shows "f integrable_on UNIV"
proof -
  from f(3) obtain r where r: "(\<integral>\<^sup>+x. f x \<partial>lborel) = ennreal r" "0 \<le> r"
    by (cases "\<integral>\<^sup>+x. f x \<partial>lborel" rule: ennreal_cases) auto
  then show ?thesis
    by (intro has_integral_integrable[where i=r] nn_integral_has_integral[where r=r] f)
qed

lemma nn_integral_has_integral_lborel:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes f_borel: "f \<in> borel_measurable borel" and nonneg: "\<And>x. 0 \<le> f x"
  assumes I: "(f has_integral I) UNIV"
  shows "integral\<^sup>N lborel f = I"
proof -
  from f_borel have "(\<lambda>x. ennreal (f x)) \<in> borel_measurable lborel" by auto
  from borel_measurable_implies_simple_function_sequence'[OF this] guess F . note F = this
  let ?B = "\<lambda>i::nat. box (- (real i *\<^sub>R One)) (real i *\<^sub>R One) :: 'a set"

  note F(1)[THEN borel_measurable_simple_function, measurable]

  have "0 \<le> I"
    using I by (rule has_integral_nonneg) (simp add: nonneg)

  have F_le_f: "enn2real (F i x) \<le> f x" for i x
    using F(3,4)[where x=x] nonneg SUP_upper[of i UNIV "\<lambda>i. F i x"]
    by (cases "F i x" rule: ennreal_cases) auto
  let ?F = "\<lambda>i x. F i x * indicator (?B i) x"
  have "(\<integral>\<^sup>+ x. ennreal (f x) \<partial>lborel) = (SUP i. integral\<^sup>N lborel (\<lambda>x. ?F i x))"
  proof (subst nn_integral_monotone_convergence_SUP[symmetric])
    { fix x
      obtain j where j: "x \<in> ?B j"
        using UN_box_eq_UNIV by auto

      have "ennreal (f x) = (SUP i. F i x)"
        using F(4)[of x] nonneg[of x] by (simp add: max_def)
      also have "\<dots> = (SUP i. ?F i x)"
      proof (rule SUP_eq)
        fix i show "\<exists>j\<in>UNIV. F i x \<le> ?F j x"
          using j F(2)
          by (intro bexI[of _ "max i j"])
             (auto split: split_max split_indicator simp: incseq_def le_fun_def box_def)
      qed (auto intro!: F split: split_indicator)
      finally have "ennreal (f x) =  (SUP i. ?F i x)" . }
    then show "(\<integral>\<^sup>+ x. ennreal (f x) \<partial>lborel) = (\<integral>\<^sup>+ x. (SUP i. ?F i x) \<partial>lborel)"
      by simp
  qed (insert F, auto simp: incseq_def le_fun_def box_def split: split_indicator)
  also have "\<dots> \<le> ennreal I"
  proof (rule SUP_least)
    fix i :: nat
    have finite_F: "(\<integral>\<^sup>+ x. ennreal (enn2real (F i x) * indicator (?B i) x) \<partial>lborel) < \<infinity>"
    proof (rule nn_integral_bound_simple_function)
      have "emeasure lborel {x \<in> space lborel. ennreal (enn2real (F i x) * indicator (?B i) x) \<noteq> 0} \<le>
        emeasure lborel (?B i)"
        by (intro emeasure_mono)  (auto split: split_indicator)
      then show "emeasure lborel {x \<in> space lborel. ennreal (enn2real (F i x) * indicator (?B i) x) \<noteq> 0} < \<infinity>"
        by (auto simp: less_top[symmetric] top_unique)
    qed (auto split: split_indicator
              intro!: F simple_function_compose1[where g="enn2real"] simple_function_ennreal)

    have int_F: "(\<lambda>x. enn2real (F i x) * indicator (?B i) x) integrable_on UNIV"
      using F(4) finite_F
      by (intro nn_integral_integrable_on) (auto split: split_indicator simp: enn2real_nonneg)

    have "(\<integral>\<^sup>+ x. F i x * indicator (?B i) x \<partial>lborel) =
      (\<integral>\<^sup>+ x. ennreal (enn2real (F i x) * indicator (?B i) x) \<partial>lborel)"
      using F(3,4)
      by (intro nn_integral_cong) (auto simp: image_iff eq_commute split: split_indicator)
    also have "\<dots> = ennreal (integral UNIV (\<lambda>x. enn2real (F i x) * indicator (?B i) x))"
      using F
      by (intro nn_integral_lborel_eq_integral[OF _ _ finite_F])
         (auto split: split_indicator intro: enn2real_nonneg)
    also have "\<dots> \<le> ennreal I"
      by (auto intro!: has_integral_le[OF integrable_integral[OF int_F] I] nonneg F_le_f
               simp: \<open>0 \<le> I\<close> split: split_indicator )
    finally show "(\<integral>\<^sup>+ x. F i x * indicator (?B i) x \<partial>lborel) \<le> ennreal I" .
  qed
  finally have "(\<integral>\<^sup>+ x. ennreal (f x) \<partial>lborel) < \<infinity>"
    by (auto simp: less_top[symmetric] top_unique)
  from nn_integral_lborel_eq_integral[OF assms(1,2) this] I show ?thesis
    by (simp add: integral_unique)
qed

lemma has_integral_iff_emeasure_lborel:
  fixes A :: "'a::euclidean_space set"
  assumes A[measurable]: "A \<in> sets borel" and [simp]: "0 \<le> r"
  shows "((\<lambda>x. 1) has_integral r) A \<longleftrightarrow> emeasure lborel A = ennreal r"
proof (cases "emeasure lborel A = \<infinity>")
  case emeasure_A: True
  have "\<not> (\<lambda>x. 1::real) integrable_on A"
  proof
    assume int: "(\<lambda>x. 1::real) integrable_on A"
    then have "(indicator A::'a \<Rightarrow> real) integrable_on UNIV"
      unfolding indicator_def[abs_def] integrable_restrict_univ .
    then obtain r where "((indicator A::'a\<Rightarrow>real) has_integral r) UNIV"
      by auto
    from nn_integral_has_integral_lborel[OF _ _ this] emeasure_A show False
      by (simp add: ennreal_indicator)
  qed
  with emeasure_A show ?thesis
    by auto
next
  case False
  then have "((\<lambda>x. 1) has_integral measure lborel A) A"
    by (simp add: has_integral_measure_lborel less_top)
  with False show ?thesis
    by (auto simp: emeasure_eq_ennreal_measure has_integral_unique)
qed

lemma has_integral_integral_real:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes f: "integrable lborel f"
  shows "(f has_integral (integral\<^sup>L lborel f)) UNIV"
using f proof induct
  case (base A c) then show ?case
    by (auto intro!: has_integral_mult_left simp: )
       (simp add: emeasure_eq_ennreal_measure indicator_def has_integral_measure_lborel)
next
  case (add f g) then show ?case
    by (auto intro!: has_integral_add)
next
  case (lim f s)
  show ?case
  proof (rule has_integral_dominated_convergence)
    show "\<And>i. (s i has_integral integral\<^sup>L lborel (s i)) UNIV" by fact
    show "(\<lambda>x. norm (2 * f x)) integrable_on UNIV"
      using \<open>integrable lborel f\<close>
      by (intro nn_integral_integrable_on)
         (auto simp: integrable_iff_bounded abs_mult  nn_integral_cmult ennreal_mult ennreal_mult_less_top)
    show "\<And>k. \<forall>x\<in>UNIV. norm (s k x) \<le> norm (2 * f x)"
      using lim by (auto simp add: abs_mult)
    show "\<forall>x\<in>UNIV. (\<lambda>k. s k x) \<longlonglongrightarrow> f x"
      using lim by auto
    show "(\<lambda>k. integral\<^sup>L lborel (s k)) \<longlonglongrightarrow> integral\<^sup>L lborel f"
      using lim lim(1)[THEN borel_measurable_integrable]
      by (intro integral_dominated_convergence[where w="\<lambda>x. 2 * norm (f x)"]) auto
  qed
qed

context
  fixes f::"'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
begin

lemma has_integral_integral_lborel:
  assumes f: "integrable lborel f"
  shows "(f has_integral (integral\<^sup>L lborel f)) UNIV"
proof -
  have "((\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) has_integral (\<Sum>b\<in>Basis. integral\<^sup>L lborel (\<lambda>x. f x \<bullet> b) *\<^sub>R b)) UNIV"
    using f by (intro has_integral_setsum finite_Basis ballI has_integral_scaleR_left has_integral_integral_real) auto
  also have eq_f: "(\<lambda>x. \<Sum>b\<in>Basis. (f x \<bullet> b) *\<^sub>R b) = f"
    by (simp add: fun_eq_iff euclidean_representation)
  also have "(\<Sum>b\<in>Basis. integral\<^sup>L lborel (\<lambda>x. f x \<bullet> b) *\<^sub>R b) = integral\<^sup>L lborel f"
    using f by (subst (2) eq_f[symmetric]) simp
  finally show ?thesis .
qed

lemma integrable_on_lborel: "integrable lborel f \<Longrightarrow> f integrable_on UNIV"
  using has_integral_integral_lborel by auto

lemma integral_lborel: "integrable lborel f \<Longrightarrow> integral UNIV f = (\<integral>x. f x \<partial>lborel)"
  using has_integral_integral_lborel by auto

end

subsection \<open>Fundamental Theorem of Calculus for the Lebesgue integral\<close>

text \<open>

For the positive integral we replace continuity with Borel-measurability.

\<close>

lemma
  fixes f :: "real \<Rightarrow> real"
  assumes [measurable]: "f \<in> borel_measurable borel"
  assumes f: "\<And>x. x \<in> {a..b} \<Longrightarrow> DERIV F x :> f x" "\<And>x. x \<in> {a..b} \<Longrightarrow> 0 \<le> f x" and "a \<le> b"
  shows nn_integral_FTC_Icc: "(\<integral>\<^sup>+x. ennreal (f x) * indicator {a .. b} x \<partial>lborel) = F b - F a" (is ?nn)
    and has_bochner_integral_FTC_Icc_nonneg:
      "has_bochner_integral lborel (\<lambda>x. f x * indicator {a .. b} x) (F b - F a)" (is ?has)
    and integral_FTC_Icc_nonneg: "(\<integral>x. f x * indicator {a .. b} x \<partial>lborel) = F b - F a" (is ?eq)
    and integrable_FTC_Icc_nonneg: "integrable lborel (\<lambda>x. f x * indicator {a .. b} x)" (is ?int)
proof -
  have *: "(\<lambda>x. f x * indicator {a..b} x) \<in> borel_measurable borel" "\<And>x. 0 \<le> f x * indicator {a..b} x"
    using f(2) by (auto split: split_indicator)

  have F_mono: "a \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> b\<Longrightarrow> F x \<le> F y" for x y
    using f by (intro DERIV_nonneg_imp_nondecreasing[of x y F]) (auto intro: order_trans)

  have "(f has_integral F b - F a) {a..b}"
    by (intro fundamental_theorem_of_calculus)
       (auto simp: has_field_derivative_iff_has_vector_derivative[symmetric]
             intro: has_field_derivative_subset[OF f(1)] \<open>a \<le> b\<close>)
  then have i: "((\<lambda>x. f x * indicator {a .. b} x) has_integral F b - F a) UNIV"
    unfolding indicator_def if_distrib[where f="\<lambda>x. a * x" for a]
    by (simp cong del: if_weak_cong del: atLeastAtMost_iff)
  then have nn: "(\<integral>\<^sup>+x. f x * indicator {a .. b} x \<partial>lborel) = F b - F a"
    by (rule nn_integral_has_integral_lborel[OF *])
  then show ?has
    by (rule has_bochner_integral_nn_integral[rotated 3]) (simp_all add: * F_mono \<open>a \<le> b\<close>)
  then show ?eq ?int
    unfolding has_bochner_integral_iff by auto
  show ?nn
    by (subst nn[symmetric])
       (auto intro!: nn_integral_cong simp add: ennreal_mult f split: split_indicator)
qed

lemma
  fixes f :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes "a \<le> b"
  assumes "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (F has_vector_derivative f x) (at x within {a .. b})"
  assumes cont: "continuous_on {a .. b} f"
  shows has_bochner_integral_FTC_Icc:
      "has_bochner_integral lborel (\<lambda>x. indicator {a .. b} x *\<^sub>R f x) (F b - F a)" (is ?has)
    and integral_FTC_Icc: "(\<integral>x. indicator {a .. b} x *\<^sub>R f x \<partial>lborel) = F b - F a" (is ?eq)
proof -
  let ?f = "\<lambda>x. indicator {a .. b} x *\<^sub>R f x"
  have int: "integrable lborel ?f"
    using borel_integrable_compact[OF _ cont] by auto
  have "(f has_integral F b - F a) {a..b}"
    using assms(1,2) by (intro fundamental_theorem_of_calculus) auto
  moreover
  have "(f has_integral integral\<^sup>L lborel ?f) {a..b}"
    using has_integral_integral_lborel[OF int]
    unfolding indicator_def if_distrib[where f="\<lambda>x. x *\<^sub>R a" for a]
    by (simp cong del: if_weak_cong del: atLeastAtMost_iff)
  ultimately show ?eq
    by (auto dest: has_integral_unique)
  then show ?has
    using int by (auto simp: has_bochner_integral_iff)
qed

lemma
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b"
  assumes deriv: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> DERIV F x :> f x"
  assumes cont: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> isCont f x"
  shows has_bochner_integral_FTC_Icc_real:
      "has_bochner_integral lborel (\<lambda>x. f x * indicator {a .. b} x) (F b - F a)" (is ?has)
    and integral_FTC_Icc_real: "(\<integral>x. f x * indicator {a .. b} x \<partial>lborel) = F b - F a" (is ?eq)
proof -
  have 1: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (F has_vector_derivative f x) (at x within {a .. b})"
    unfolding has_field_derivative_iff_has_vector_derivative[symmetric]
    using deriv by (auto intro: DERIV_subset)
  have 2: "continuous_on {a .. b} f"
    using cont by (intro continuous_at_imp_continuous_on) auto
  show ?has ?eq
    using has_bochner_integral_FTC_Icc[OF \<open>a \<le> b\<close> 1 2] integral_FTC_Icc[OF \<open>a \<le> b\<close> 1 2]
    by (auto simp: mult.commute)
qed

lemma nn_integral_FTC_atLeast:
  fixes f :: "real \<Rightarrow> real"
  assumes f_borel: "f \<in> borel_measurable borel"
  assumes f: "\<And>x. a \<le> x \<Longrightarrow> DERIV F x :> f x"
  assumes nonneg: "\<And>x. a \<le> x \<Longrightarrow> 0 \<le> f x"
  assumes lim: "(F \<longlongrightarrow> T) at_top"
  shows "(\<integral>\<^sup>+x. ennreal (f x) * indicator {a ..} x \<partial>lborel) = T - F a"
proof -
  let ?f = "\<lambda>(i::nat) (x::real). ennreal (f x) * indicator {a..a + real i} x"
  let ?fR = "\<lambda>x. ennreal (f x) * indicator {a ..} x"

  have F_mono: "a \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> F x \<le> F y" for x y
    using f nonneg by (intro DERIV_nonneg_imp_nondecreasing[of x y F]) (auto intro: order_trans)
  then have F_le_T: "a \<le> x \<Longrightarrow> F x \<le> T" for x
    by (intro tendsto_le_const[OF _ lim])
       (auto simp: trivial_limit_at_top_linorder eventually_at_top_linorder)

  have "(SUP i::nat. ?f i x) = ?fR x" for x
  proof (rule LIMSEQ_unique[OF LIMSEQ_SUP])
    from reals_Archimedean2[of "x - a"] guess n ..
    then have "eventually (\<lambda>n. ?f n x = ?fR x) sequentially"
      by (auto intro!: eventually_sequentiallyI[where c=n] split: split_indicator)
    then show "(\<lambda>n. ?f n x) \<longlonglongrightarrow> ?fR x"
      by (rule Lim_eventually)
  qed (auto simp: nonneg incseq_def le_fun_def split: split_indicator)
  then have "integral\<^sup>N lborel ?fR = (\<integral>\<^sup>+ x. (SUP i::nat. ?f i x) \<partial>lborel)"
    by simp
  also have "\<dots> = (SUP i::nat. (\<integral>\<^sup>+ x. ?f i x \<partial>lborel))"
  proof (rule nn_integral_monotone_convergence_SUP)
    show "incseq ?f"
      using nonneg by (auto simp: incseq_def le_fun_def split: split_indicator)
    show "\<And>i. (?f i) \<in> borel_measurable lborel"
      using f_borel by auto
  qed
  also have "\<dots> = (SUP i::nat. ennreal (F (a + real i) - F a))"
    by (subst nn_integral_FTC_Icc[OF f_borel f nonneg]) auto
  also have "\<dots> = T - F a"
  proof (rule LIMSEQ_unique[OF LIMSEQ_SUP])
    have "(\<lambda>x. F (a + real x)) \<longlonglongrightarrow> T"
      apply (rule filterlim_compose[OF lim filterlim_tendsto_add_at_top])
      apply (rule LIMSEQ_const_iff[THEN iffD2, OF refl])
      apply (rule filterlim_real_sequentially)
      done
    then show "(\<lambda>n. ennreal (F (a + real n) - F a)) \<longlonglongrightarrow> ennreal (T - F a)"
      by (simp add: F_mono F_le_T tendsto_diff)
  qed (auto simp: incseq_def intro!: ennreal_le_iff[THEN iffD2] F_mono)
  finally show ?thesis .
qed

lemma integral_power:
  "a \<le> b \<Longrightarrow> (\<integral>x. x^k * indicator {a..b} x \<partial>lborel) = (b^Suc k - a^Suc k) / Suc k"
proof (subst integral_FTC_Icc_real)
  fix x show "DERIV (\<lambda>x. x^Suc k / Suc k) x :> x^k"
    by (intro derivative_eq_intros) auto
qed (auto simp: field_simps simp del: of_nat_Suc)

subsection \<open>Integration by parts\<close>

lemma integral_by_parts_integrable:
  fixes f g F G::"real \<Rightarrow> real"
  assumes "a \<le> b"
  assumes cont_f[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont f x"
  assumes cont_g[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont g x"
  assumes [intro]: "!!x. DERIV F x :> f x"
  assumes [intro]: "!!x. DERIV G x :> g x"
  shows  "integrable lborel (\<lambda>x.((F x) * (g x) + (f x) * (G x)) * indicator {a .. b} x)"
  by (auto intro!: borel_integrable_atLeastAtMost continuous_intros) (auto intro!: DERIV_isCont)

lemma integral_by_parts:
  fixes f g F G::"real \<Rightarrow> real"
  assumes [arith]: "a \<le> b"
  assumes cont_f[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont f x"
  assumes cont_g[intro]: "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont g x"
  assumes [intro]: "!!x. DERIV F x :> f x"
  assumes [intro]: "!!x. DERIV G x :> g x"
  shows "(\<integral>x. (F x * g x) * indicator {a .. b} x \<partial>lborel)
            =  F b * G b - F a * G a - \<integral>x. (f x * G x) * indicator {a .. b} x \<partial>lborel"
proof-
  have 0: "(\<integral>x. (F x * g x + f x * G x) * indicator {a .. b} x \<partial>lborel) = F b * G b - F a * G a"
    by (rule integral_FTC_Icc_real, auto intro!: derivative_eq_intros continuous_intros)
      (auto intro!: DERIV_isCont)

  have "(\<integral>x. (F x * g x + f x * G x) * indicator {a .. b} x \<partial>lborel) =
    (\<integral>x. (F x * g x) * indicator {a .. b} x \<partial>lborel) + \<integral>x. (f x * G x) * indicator {a .. b} x \<partial>lborel"
    apply (subst Bochner_Integration.integral_add[symmetric])
    apply (auto intro!: borel_integrable_atLeastAtMost continuous_intros)
    by (auto intro!: DERIV_isCont Bochner_Integration.integral_cong split: split_indicator)

  thus ?thesis using 0 by auto
qed

lemma integral_by_parts':
  fixes f g F G::"real \<Rightarrow> real"
  assumes "a \<le> b"
  assumes "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont f x"
  assumes "!!x. a \<le>x \<Longrightarrow> x\<le>b \<Longrightarrow> isCont g x"
  assumes "!!x. DERIV F x :> f x"
  assumes "!!x. DERIV G x :> g x"
  shows "(\<integral>x. indicator {a .. b} x *\<^sub>R (F x * g x) \<partial>lborel)
            =  F b * G b - F a * G a - \<integral>x. indicator {a .. b} x *\<^sub>R (f x * G x) \<partial>lborel"
  using integral_by_parts[OF assms] by (simp add: ac_simps)

lemma has_bochner_integral_even_function:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes f: "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x) x"
  assumes even: "\<And>x. f (- x) = f x"
  shows "has_bochner_integral lborel f (2 *\<^sub>R x)"
proof -
  have indicator: "\<And>x::real. indicator {..0} (- x) = indicator {0..} x"
    by (auto split: split_indicator)
  have "has_bochner_integral lborel (\<lambda>x. indicator {.. 0} x *\<^sub>R f x) x"
    by (subst lborel_has_bochner_integral_real_affine_iff[where c="-1" and t=0])
       (auto simp: indicator even f)
  with f have "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x + indicator {.. 0} x *\<^sub>R f x) (x + x)"
    by (rule has_bochner_integral_add)
  then have "has_bochner_integral lborel f (x + x)"
    by (rule has_bochner_integral_discrete_difference[where X="{0}", THEN iffD1, rotated 4])
       (auto split: split_indicator)
  then show ?thesis
    by (simp add: scaleR_2)
qed

lemma has_bochner_integral_odd_function:
  fixes f :: "real \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes f: "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x) x"
  assumes odd: "\<And>x. f (- x) = - f x"
  shows "has_bochner_integral lborel f 0"
proof -
  have indicator: "\<And>x::real. indicator {..0} (- x) = indicator {0..} x"
    by (auto split: split_indicator)
  have "has_bochner_integral lborel (\<lambda>x. - indicator {.. 0} x *\<^sub>R f x) x"
    by (subst lborel_has_bochner_integral_real_affine_iff[where c="-1" and t=0])
       (auto simp: indicator odd f)
  from has_bochner_integral_minus[OF this]
  have "has_bochner_integral lborel (\<lambda>x. indicator {.. 0} x *\<^sub>R f x) (- x)"
    by simp
  with f have "has_bochner_integral lborel (\<lambda>x. indicator {0..} x *\<^sub>R f x + indicator {.. 0} x *\<^sub>R f x) (x + - x)"
    by (rule has_bochner_integral_add)
  then have "has_bochner_integral lborel f (x + - x)"
    by (rule has_bochner_integral_discrete_difference[where X="{0}", THEN iffD1, rotated 4])
       (auto split: split_indicator)
  then show ?thesis
    by simp
qed

end
