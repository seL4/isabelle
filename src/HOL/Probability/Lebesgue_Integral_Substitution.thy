(*  Title:      HOL/Probability/Lebesgue_Integral_Substitution.thy
    Author:     Manuel Eberl

    Provides lemmas for integration by substitution for the basic integral types.
    Note that the substitution function must have a nonnegative derivative.
    This could probably be weakened somehow.
*)

section {* Integration by Substition *}

theory Lebesgue_Integral_Substitution
imports Interval_Integral
begin

lemma measurable_sets_borel:
    "\<lbrakk>f \<in> measurable borel M; A \<in> sets M\<rbrakk> \<Longrightarrow> f -` A \<in> sets borel"
  by (drule (1) measurable_sets) simp

lemma closure_Iii: 
  assumes "a < b"
  shows "closure {a<..<b::real} = {a..b}"
proof-
  have "{a<..<b} = ball ((a+b)/2) ((b-a)/2)" by (auto simp: dist_real_def field_simps not_less)
  also from assms have "closure ... = cball ((a+b)/2) ((b-a)/2)" by (intro closure_ball) simp
  also have "... = {a..b}" by (auto simp: dist_real_def field_simps not_less)
  finally show ?thesis .
qed

lemma continuous_ge_on_Iii:
  assumes "continuous_on {c..d} g" "\<And>x. x \<in> {c<..<d} \<Longrightarrow> g x \<ge> a" "c < d" "x \<in> {c..d}"
  shows "g (x::real) \<ge> (a::real)"
proof-
  from assms(3) have "{c..d} = closure {c<..<d}" by (rule closure_Iii[symmetric])
  also from assms(2) have "{c<..<d} \<subseteq> (g -` {a..} \<inter> {c..d})" by auto
  hence "closure {c<..<d} \<subseteq> closure (g -` {a..} \<inter> {c..d})" by (rule closure_mono)
  also from assms(1) have "closed (g -` {a..} \<inter> {c..d})"
    by (auto simp: continuous_on_closed_vimage)
  hence "closure (g -` {a..} \<inter> {c..d}) = g -` {a..} \<inter> {c..d}" by simp
  finally show ?thesis using `x \<in> {c..d}` by auto 
qed 

lemma interior_real_semiline':
  fixes a :: real
  shows "interior {..a} = {..<a}"
proof -
  {
    fix y
    assume "a > y"
    then have "y \<in> interior {..a}"
      apply (simp add: mem_interior)
      apply (rule_tac x="(a-y)" in exI)
      apply (auto simp add: dist_norm)
      done
  }
  moreover
  {
    fix y
    assume "y \<in> interior {..a}"
    then obtain e where e: "e > 0" "cball y e \<subseteq> {..a}"
      using mem_interior_cball[of y "{..a}"] by auto
    moreover from e have "y + e \<in> cball y e"
      by (auto simp add: cball_def dist_norm)
    ultimately have "a \<ge> y + e" by auto
    then have "a > y" using e by auto
  }
  ultimately show ?thesis by auto
qed

lemma interior_atLeastAtMost_real: "interior {a..b} = {a<..<b :: real}"
proof-
  have "{a..b} = {a..} \<inter> {..b}" by auto
  also have "interior ... = {a<..} \<inter> {..<b}" 
    by (simp add: interior_real_semiline interior_real_semiline')
  also have "... = {a<..<b}" by auto
  finally show ?thesis .
qed

lemma nn_integral_indicator_singleton[simp]:
  assumes [measurable]: "{y} \<in> sets M"
  shows "(\<integral>\<^sup>+x. f x * indicator {y} x \<partial>M) = max 0 (f y) * emeasure M {y}"
proof-
  have "(\<integral>\<^sup>+x. f x * indicator {y} x \<partial>M) = (\<integral>\<^sup>+x. max 0 (f y) * indicator {y} x \<partial>M)"
    by (subst nn_integral_max_0[symmetric]) (auto intro!: nn_integral_cong split: split_indicator)
  then show ?thesis
    by (simp add: nn_integral_cmult)
qed

lemma nn_integral_set_ereal:
  "(\<integral>\<^sup>+x. ereal (f x) * indicator A x \<partial>M) = (\<integral>\<^sup>+x. ereal (f x * indicator A x) \<partial>M)"
  by (rule nn_integral_cong) (simp split: split_indicator)

lemma nn_integral_indicator_singleton'[simp]:
  assumes [measurable]: "{y} \<in> sets M"
  shows "(\<integral>\<^sup>+x. ereal (f x * indicator {y} x) \<partial>M) = max 0 (f y) * emeasure M {y}"
  by (subst nn_integral_set_ereal[symmetric]) simp

lemma set_borel_measurable_sets:
  fixes f :: "_ \<Rightarrow> _::real_normed_vector"
  assumes "set_borel_measurable M X f" "B \<in> sets borel" "X \<in> sets M"
  shows "f -` B \<inter> X \<in> sets M"
proof -
  have "f \<in> borel_measurable (restrict_space M X)"
    using assms by (subst borel_measurable_restrict_space_iff) auto
  then have "f -` B \<inter> space (restrict_space M X) \<in> sets (restrict_space M X)"
    by (rule measurable_sets) fact
  with `X \<in> sets M` show ?thesis
    by (subst (asm) sets_restrict_space_iff) (auto simp: space_restrict_space)
qed

lemma borel_set_induct[consumes 1, case_names empty interval compl union]:
  assumes "A \<in> sets borel" 
  assumes empty: "P {}" and int: "\<And>a b. a \<le> b \<Longrightarrow> P {a..b}" and compl: "\<And>A. A \<in> sets borel \<Longrightarrow> P A \<Longrightarrow> P (-A)" and
          un: "\<And>f. disjoint_family f \<Longrightarrow> (\<And>i. f i \<in> sets borel) \<Longrightarrow>  (\<And>i. P (f i)) \<Longrightarrow> P (\<Union>i::nat. f i)"
  shows "P (A::real set)"
proof-
  let ?G = "range (\<lambda>(a,b). {a..b::real})"
  have "Int_stable ?G" "?G \<subseteq> Pow UNIV" "A \<in> sigma_sets UNIV ?G" 
      using assms(1) by (auto simp add: borel_eq_atLeastAtMost Int_stable_def)
  thus ?thesis
  proof (induction rule: sigma_sets_induct_disjoint) 
    case (union f)
      from union.hyps(2) have "\<And>i. f i \<in> sets borel" by (auto simp: borel_eq_atLeastAtMost)
      with union show ?case by (auto intro: un)
  next
    case (basic A)
    then obtain a b where "A = {a .. b}" by auto
    then show ?case
      by (cases "a \<le> b") (auto intro: int empty)
  qed (auto intro: empty compl simp: Compl_eq_Diff_UNIV[symmetric] borel_eq_atLeastAtMost)
qed

definition "mono_on f A \<equiv> \<forall>r s. r \<in> A \<and> s \<in> A \<and> r \<le> s \<longrightarrow> f r \<le> f s"

lemma mono_onI:
  "(\<And>r s. r \<in> A \<Longrightarrow> s \<in> A \<Longrightarrow> r \<le> s \<Longrightarrow> f r \<le> f s) \<Longrightarrow> mono_on f A"
  unfolding mono_on_def by simp

lemma mono_onD:
  "\<lbrakk>mono_on f A; r \<in> A; s \<in> A; r \<le> s\<rbrakk> \<Longrightarrow> f r \<le> f s"
  unfolding mono_on_def by simp

lemma mono_imp_mono_on: "mono f \<Longrightarrow> mono_on f A"
  unfolding mono_def mono_on_def by auto

lemma mono_on_subset: "mono_on f A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> mono_on f B"
  unfolding mono_on_def by auto

definition "strict_mono_on f A \<equiv> \<forall>r s. r \<in> A \<and> s \<in> A \<and> r < s \<longrightarrow> f r < f s"

lemma strict_mono_onI:
  "(\<And>r s. r \<in> A \<Longrightarrow> s \<in> A \<Longrightarrow> r < s \<Longrightarrow> f r < f s) \<Longrightarrow> strict_mono_on f A"
  unfolding strict_mono_on_def by simp

lemma strict_mono_onD:
  "\<lbrakk>strict_mono_on f A; r \<in> A; s \<in> A; r < s\<rbrakk> \<Longrightarrow> f r < f s"
  unfolding strict_mono_on_def by simp

lemma mono_on_greaterD:
  assumes "mono_on g A" "x \<in> A" "y \<in> A" "g x > (g (y::_::linorder) :: _ :: linorder)"
  shows "x > y"
proof (rule ccontr)
  assume "\<not>x > y"
  hence "x \<le> y" by (simp add: not_less)
  from assms(1-3) and this have "g x \<le> g y" by (rule mono_onD)
  with assms(4) show False by simp
qed

lemma strict_mono_inv:
  fixes f :: "('a::linorder) \<Rightarrow> ('b::linorder)"
  assumes "strict_mono f" and "surj f" and inv: "\<And>x. g (f x) = x"
  shows "strict_mono g"
proof
  fix x y :: 'b assume "x < y"
  from `surj f` obtain x' y' where [simp]: "x = f x'" "y = f y'" by blast
  with `x < y` and `strict_mono f` have "x' < y'" by (simp add: strict_mono_less)
  with inv show "g x < g y" by simp
qed

lemma strict_mono_on_imp_inj_on:
  assumes "strict_mono_on (f :: (_ :: linorder) \<Rightarrow> (_ :: preorder)) A"
  shows "inj_on f A"
proof (rule inj_onI)
  fix x y assume "x \<in> A" "y \<in> A" "f x = f y"
  thus "x = y"
    by (cases x y rule: linorder_cases)
       (auto dest: strict_mono_onD[OF assms, of x y] strict_mono_onD[OF assms, of y x]) 
qed

lemma strict_mono_on_leD:
  assumes "strict_mono_on (f :: (_ :: linorder) \<Rightarrow> _ :: preorder) A" "x \<in> A" "y \<in> A" "x \<le> y"
  shows "f x \<le> f y"
proof (insert le_less_linear[of y x], elim disjE)
  assume "x < y"
  with assms have "f x < f y" by (rule_tac strict_mono_onD[OF assms(1)]) simp_all
  thus ?thesis by (rule less_imp_le)
qed (insert assms, simp)

lemma strict_mono_on_eqD:
  fixes f :: "(_ :: linorder) \<Rightarrow> (_ :: preorder)"
  assumes "strict_mono_on f A" "f x = f y" "x \<in> A" "y \<in> A"
  shows "y = x"
  using assms by (rule_tac linorder_cases[of x y]) (auto dest: strict_mono_onD)

lemma mono_on_imp_deriv_nonneg:
  assumes mono: "mono_on f A" and deriv: "(f has_real_derivative D) (at x)"
  assumes "x \<in> interior A"
  shows "D \<ge> 0"
proof (rule tendsto_le_const)
  let ?A' = "(\<lambda>y. y - x) ` interior A"
  from deriv show "((\<lambda>h. (f (x + h) - f x) / h) ---> D) (at 0)"
      by (simp add: field_has_derivative_at has_field_derivative_def)
  from mono have mono': "mono_on f (interior A)" by (rule mono_on_subset) (rule interior_subset)

  show "eventually (\<lambda>h. (f (x + h) - f x) / h \<ge> 0) (at 0)"
  proof (subst eventually_at_topological, intro exI conjI ballI impI)
    have "open (interior A)" by simp
    hence "open (op + (-x) ` interior A)" by (rule open_translation)
    also have "(op + (-x) ` interior A) = ?A'" by auto
    finally show "open ?A'" .
  next
    from `x \<in> interior A` show "0 \<in> ?A'" by auto
  next
    fix h assume "h \<in> ?A'"
    hence "x + h \<in> interior A" by auto
    with mono' and `x \<in> interior A` show "(f (x + h) - f x) / h \<ge> 0"
      by (cases h rule: linorder_cases[of _ 0])
         (simp_all add: divide_nonpos_neg divide_nonneg_pos mono_onD field_simps)
  qed
qed simp

lemma strict_mono_on_imp_mono_on: 
  "strict_mono_on (f :: (_ :: linorder) \<Rightarrow> _ :: preorder) A \<Longrightarrow> mono_on f A"
  by (rule mono_onI, rule strict_mono_on_leD)

lemma has_real_derivative_imp_continuous_on:
  assumes "\<And>x. x \<in> A \<Longrightarrow> (f has_real_derivative f' x) (at x)"
  shows "continuous_on A f"
  apply (intro differentiable_imp_continuous_on, unfold differentiable_on_def)
  apply (intro ballI Deriv.differentiableI)
  apply (rule has_field_derivative_subset[OF assms])
  apply simp_all
  done

lemma closure_contains_Sup:
  fixes S :: "real set"
  assumes "S \<noteq> {}" "bdd_above S"
  shows "Sup S \<in> closure S"
proof-
  have "Inf (uminus ` S) \<in> closure (uminus ` S)" 
      using assms by (intro closure_contains_Inf) auto
  also have "Inf (uminus ` S) = -Sup S" by (simp add: Inf_real_def)
  also have "closure (uminus ` S) = uminus ` closure S"
      by (rule sym, intro closure_injective_linear_image) (auto intro: linearI)
  finally show ?thesis by auto
qed

lemma closed_contains_Sup:
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> bdd_above S \<Longrightarrow> closed S \<Longrightarrow> Sup S \<in> S"
  by (subst closure_closed[symmetric], assumption, rule closure_contains_Sup)

lemma deriv_nonneg_imp_mono:
  assumes deriv: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_real_derivative g' x) (at x)"
  assumes nonneg: "\<And>x. x \<in> {a..b} \<Longrightarrow> g' x \<ge> 0"
  assumes ab: "a \<le> b"
  shows "g a \<le> g b"
proof (cases "a < b")
  assume "a < b"
  from deriv have "\<forall>x. x \<ge> a \<and> x \<le> b \<longrightarrow> (g has_real_derivative g' x) (at x)" by simp
  from MVT2[OF `a < b` this] and deriv 
    obtain \<xi> where \<xi>_ab: "\<xi> > a" "\<xi> < b" and g_ab: "g b - g a = (b - a) * g' \<xi>" by blast
  from \<xi>_ab ab nonneg have "(b - a) * g' \<xi> \<ge> 0" by simp
  with g_ab show ?thesis by simp
qed (insert ab, simp)

lemma continuous_interval_vimage_Int:
  assumes "continuous_on {a::real..b} g" and mono: "\<And>x y. a \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> b \<Longrightarrow> g x \<le> g y"
  assumes "a \<le> b" "(c::real) \<le> d" "{c..d} \<subseteq> {g a..g b}"
  obtains c' d' where "{a..b} \<inter> g -` {c..d} = {c'..d'}" "c' \<le> d'" "g c' = c" "g d' = d"
proof-
    let ?A = "{a..b} \<inter> g -` {c..d}"
    from IVT'[of g a c b, OF _ _ `a \<le> b` assms(1)] assms(4,5) 
         obtain c'' where c'': "c'' \<in> ?A" "g c'' = c" by auto
    from IVT'[of g a d b, OF _ _ `a \<le> b` assms(1)] assms(4,5) 
         obtain d'' where d'': "d'' \<in> ?A" "g d'' = d" by auto
    hence [simp]: "?A \<noteq> {}" by blast

    def c' \<equiv> "Inf ?A" and d' \<equiv> "Sup ?A"
    have "?A \<subseteq> {c'..d'}" unfolding c'_def d'_def
        by (intro subsetI) (auto intro: cInf_lower cSup_upper)
    moreover from assms have "closed ?A" 
        using continuous_on_closed_vimage[of "{a..b}" g] by (subst Int_commute) simp
    hence c'd'_in_set: "c' \<in> ?A" "d' \<in> ?A" unfolding c'_def d'_def
        by ((intro closed_contains_Inf closed_contains_Sup, simp_all)[])+
    hence "{c'..d'} \<subseteq> ?A" using assms 
        by (intro subsetI)
           (auto intro!: order_trans[of c "g c'" "g x" for x] order_trans[of "g x" "g d'" d for x] 
                 intro!: mono)
    moreover have "c' \<le> d'" using c'd'_in_set(2) unfolding c'_def by (intro cInf_lower) auto
    moreover have "g c' \<le> c" "g d' \<ge> d"
      apply (insert c'' d'' c'd'_in_set)
      apply (subst c''(2)[symmetric])
      apply (auto simp: c'_def intro!: mono cInf_lower c'') []
      apply (subst d''(2)[symmetric])
      apply (auto simp: d'_def intro!: mono cSup_upper d'') []
      done
    with c'd'_in_set have "g c' = c" "g d' = d" by auto
    ultimately show ?thesis using that by blast
qed

lemma nn_integral_substitution_aux:
  fixes f :: "real \<Rightarrow> ereal"
  assumes Mf: "f \<in> borel_measurable borel"
  assumes nonnegf: "\<And>x. f x \<ge> 0"
  assumes derivg: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_real_derivative g' x) (at x)"
  assumes contg': "continuous_on {a..b} g'" 
  assumes derivg_nonneg: "\<And>x. x \<in> {a..b} \<Longrightarrow> g' x \<ge> 0"
  assumes "a < b"
  shows "(\<integral>\<^sup>+x. f x * indicator {g a..g b} x \<partial>lborel) = 
             (\<integral>\<^sup>+x. f (g x) * g' x * indicator {a..b} x \<partial>lborel)"
proof-
  from `a < b` have [simp]: "a \<le> b" by simp
  from derivg have contg: "continuous_on {a..b} g" by (rule has_real_derivative_imp_continuous_on)
  from this and contg' have Mg: "set_borel_measurable borel {a..b} g" and 
                             Mg': "set_borel_measurable borel {a..b} g'" 
      by (simp_all only: set_measurable_continuous_on_ivl)
  from derivg have derivg': "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
    by (simp only: has_field_derivative_iff_has_vector_derivative)

  have real_ind[simp]: "\<And>A x. real (indicator A x :: ereal) = indicator A x" 
      by (auto split: split_indicator)
  have ereal_ind[simp]: "\<And>A x. ereal (indicator A x) = indicator A x" 
      by (auto split: split_indicator)
  have [simp]: "\<And>x A. indicator A (g x) = indicator (g -` A) x" 
      by (auto split: split_indicator)

  from derivg derivg_nonneg have monog: "\<And>x y. a \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> b \<Longrightarrow> g x \<le> g y"
    by (rule deriv_nonneg_imp_mono) simp_all
  with monog have [simp]: "g a \<le> g b" by (auto intro: mono_onD)

  show ?thesis
  proof (induction rule: borel_measurable_induct[OF Mf nonnegf, case_names cong set mult add sup])
    case (cong f1 f2)
    from cong.hyps(3) have "f1 = f2" by auto
    with cong show ?case by simp
  next
    case (set A)
    from set.hyps show ?case
    proof (induction rule: borel_set_induct)
      case empty
      thus ?case by simp
    next
      case (interval c d)
      {
        fix u v :: real assume asm: "{u..v} \<subseteq> {g a..g b}" "u \<le> v"
        
        obtain u' v' where u'v': "{a..b} \<inter> g-`{u..v} = {u'..v'}" "u' \<le> v'" "g u' = u" "g v' = v"
             using asm by (rule_tac continuous_interval_vimage_Int[OF contg monog, of u v]) simp_all
        hence "{u'..v'} \<subseteq> {a..b}" "{u'..v'} \<subseteq> g -` {u..v}" by blast+
        with u'v'(2) have "u' \<in> g -` {u..v}" "v' \<in> g -` {u..v}" by auto
        from u'v'(1) have [simp]: "{a..b} \<inter> g -` {u..v} \<in> sets borel" by simp
        
        have A: "continuous_on {min u' v'..max u' v'} g'"
            by (simp only: u'v' max_absorb2 min_absorb1) 
               (intro continuous_on_subset[OF contg'], insert u'v', auto)
        have "\<And>x. x \<in> {u'..v'} \<Longrightarrow> (g has_real_derivative g' x) (at x within {u'..v'})"
           using asm by (intro has_field_derivative_subset[OF derivg] set_mp[OF `{u'..v'} \<subseteq> {a..b}`]) auto
        hence B: "\<And>x. min u' v' \<le> x \<Longrightarrow> x \<le> max u' v' \<Longrightarrow> 
                      (g has_vector_derivative g' x) (at x within {min u' v'..max u' v'})" 
            by (simp only: u'v' max_absorb2 min_absorb1) 
               (auto simp: has_field_derivative_iff_has_vector_derivative)
        have "integrable lborel (\<lambda>x. indicator ({a..b} \<inter> g -` {u..v}) x *\<^sub>R g' x)"
          by (rule set_integrable_subset[OF borel_integrable_atLeastAtMost'[OF contg']]) simp_all
        hence "(\<integral>\<^sup>+x. ereal (g' x) * indicator ({a..b} \<inter> g-` {u..v}) x \<partial>lborel) = 
                   LBINT x:{a..b} \<inter> g-`{u..v}. g' x" 
          by (subst ereal_ind[symmetric], subst times_ereal.simps, subst nn_integral_eq_integral)
             (auto intro: measurable_sets Mg simp: derivg_nonneg mult.commute split: split_indicator)
        also from interval_integral_FTC_finite[OF A B]
            have "LBINT x:{a..b} \<inter> g-`{u..v}. g' x = v - u"
                by (simp add: u'v' interval_integral_Icc `u \<le> v`)
        finally have "(\<integral>\<^sup>+ x. ereal (g' x) * indicator ({a..b} \<inter> g -` {u..v}) x \<partial>lborel) =
                           ereal (v - u)" .
      } note A = this
  
      have "(\<integral>\<^sup>+x. indicator {c..d} (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel) =
               (\<integral>\<^sup>+ x. ereal (g' x) * indicator ({a..b} \<inter> g -` {c..d}) x \<partial>lborel)" 
        by (intro nn_integral_cong) (simp split: split_indicator)
      also have "{a..b} \<inter> g-`{c..d} = {a..b} \<inter> g-`{max (g a) c..min (g b) d}" 
        using `a \<le> b` `c \<le> d`
        by (auto intro!: monog intro: order.trans)
      also have "(\<integral>\<^sup>+ x. ereal (g' x) * indicator ... x \<partial>lborel) =
        (if max (g a) c \<le> min (g b) d then min (g b) d - max (g a) c else 0)"
         using `c \<le> d` by (simp add: A)
      also have "... = (\<integral>\<^sup>+ x. indicator ({g a..g b} \<inter> {c..d}) x \<partial>lborel)"
        by (subst nn_integral_indicator) (auto intro!: measurable_sets Mg simp:)
      also have "... = (\<integral>\<^sup>+ x. indicator {c..d} x * indicator {g a..g b} x \<partial>lborel)"
        by (intro nn_integral_cong) (auto split: split_indicator)
      finally show ?case ..

      next

      case (compl A)
      note `A \<in> sets borel`[measurable]
      from emeasure_mono[of "A \<inter> {g a..g b}" "{g a..g b}" lborel]
          have [simp]: "emeasure lborel (A \<inter> {g a..g b}) \<noteq> \<infinity>" by auto
      have [simp]: "g -` A \<inter> {a..b} \<in> sets borel"
        by (rule set_borel_measurable_sets[OF Mg]) auto
      have [simp]: "g -` (-A) \<inter> {a..b} \<in> sets borel"
        by (rule set_borel_measurable_sets[OF Mg]) auto

      have "(\<integral>\<^sup>+x. indicator (-A) x * indicator {g a..g b} x \<partial>lborel) = 
                (\<integral>\<^sup>+x. indicator (-A \<inter> {g a..g b}) x \<partial>lborel)" 
        by (rule nn_integral_cong) (simp split: split_indicator)
      also from compl have "... = emeasure lborel ({g a..g b} - A)" using derivg_nonneg
        by (simp add: vimage_Compl diff_eq Int_commute[of "-A"])
      also have "{g a..g b} - A = {g a..g b} - A \<inter> {g a..g b}" by blast
      also have "emeasure lborel ... = g b - g a - emeasure lborel (A \<inter> {g a..g b})"
             using `A \<in> sets borel` by (subst emeasure_Diff) (auto simp: real_of_ereal_minus)
     also have "emeasure lborel (A \<inter> {g a..g b}) = 
                    \<integral>\<^sup>+x. indicator A x * indicator {g a..g b} x \<partial>lborel" 
       using `A \<in> sets borel`
       by (subst nn_integral_indicator[symmetric], simp, intro nn_integral_cong)
          (simp split: split_indicator)
      also have "... = \<integral>\<^sup>+ x. indicator (g-`A \<inter> {a..b}) x * ereal (g' x * indicator {a..b} x) \<partial>lborel" (is "_ = ?I")
        by (subst compl.IH, intro nn_integral_cong) (simp split: split_indicator)
      also have "g b - g a = LBINT x:{a..b}. g' x" using derivg'
        by (intro integral_FTC_atLeastAtMost[symmetric])
           (auto intro: continuous_on_subset[OF contg'] has_field_derivative_subset[OF derivg]
                 has_vector_derivative_at_within)
      also have "ereal ... = \<integral>\<^sup>+ x. g' x * indicator {a..b} x \<partial>lborel"
        using borel_integrable_atLeastAtMost'[OF contg']
        by (subst nn_integral_eq_integral)
           (simp_all add: mult.commute derivg_nonneg split: split_indicator)
      also have Mg'': "(\<lambda>x. indicator (g -` A \<inter> {a..b}) x * ereal (g' x * indicator {a..b} x))
                            \<in> borel_measurable borel" using Mg'
        by (intro borel_measurable_ereal_times borel_measurable_indicator)
           (simp_all add: mult.commute)
      have le: "(\<integral>\<^sup>+x. indicator (g-`A \<inter> {a..b}) x * ereal (g' x * indicator {a..b} x) \<partial>lborel) \<le>
                        (\<integral>\<^sup>+x. ereal (g' x) * indicator {a..b} x \<partial>lborel)"
         by (intro nn_integral_mono) (simp split: split_indicator add: derivg_nonneg)
      note integrable = borel_integrable_atLeastAtMost'[OF contg']
      with le have notinf: "(\<integral>\<^sup>+x. indicator (g-`A \<inter> {a..b}) x * ereal (g' x * indicator {a..b} x) \<partial>lborel) \<noteq> \<infinity>"
          by (auto simp: real_integrable_def nn_integral_set_ereal mult.commute)
      have "(\<integral>\<^sup>+ x. g' x * indicator {a..b} x \<partial>lborel) - ?I = 
                  \<integral>\<^sup>+ x. ereal (g' x * indicator {a..b} x) - 
                        indicator (g -` A \<inter> {a..b}) x * ereal (g' x * indicator {a..b} x) \<partial>lborel"
        apply (intro nn_integral_diff[symmetric])
        apply (insert Mg', simp add: mult.commute) []
        apply (insert Mg'', simp) []
        apply (simp split: split_indicator add: derivg_nonneg)
        apply (rule notinf)
        apply (simp split: split_indicator add: derivg_nonneg)
        done
      also have "... = \<integral>\<^sup>+ x. indicator (-A) (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel"
        by (intro nn_integral_cong) (simp split: split_indicator)
      finally show ?case .

    next
      case (union f)
      then have [simp]: "\<And>i. {a..b} \<inter> g -` f i \<in> sets borel"
        by (subst Int_commute, intro set_borel_measurable_sets[OF Mg]) auto
      have "g -` (\<Union>i. f i) \<inter> {a..b} = (\<Union>i. {a..b} \<inter> g -` f i)" by auto
      hence "g -` (\<Union>i. f i) \<inter> {a..b} \<in> sets borel" by (auto simp del: UN_simps)

      have "(\<integral>\<^sup>+x. indicator (\<Union>i. f i) x * indicator {g a..g b} x \<partial>lborel) = 
                \<integral>\<^sup>+x. indicator (\<Union>i. {g a..g b} \<inter> f i) x \<partial>lborel"
          by (intro nn_integral_cong) (simp split: split_indicator)
      also from union have "... = emeasure lborel (\<Union>i. {g a..g b} \<inter> f i)" by simp
      also from union have "... = (\<Sum>i. emeasure lborel ({g a..g b} \<inter> f i))"
        by (intro suminf_emeasure[symmetric]) (auto simp: disjoint_family_on_def)
      also from union have "... = (\<Sum>i. \<integral>\<^sup>+x. indicator ({g a..g b} \<inter> f i) x \<partial>lborel)" by simp
      also have "(\<lambda>i. \<integral>\<^sup>+x. indicator ({g a..g b} \<inter> f i) x \<partial>lborel) = 
                           (\<lambda>i. \<integral>\<^sup>+x. indicator (f i) x * indicator {g a..g b} x \<partial>lborel)"
        by (intro ext nn_integral_cong) (simp split: split_indicator)
      also from union.IH have "(\<Sum>i. \<integral>\<^sup>+x. indicator (f i) x * indicator {g a..g b} x \<partial>lborel) = 
          (\<Sum>i. \<integral>\<^sup>+ x. indicator (f i) (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel)" by simp
      also have "(\<lambda>i. \<integral>\<^sup>+ x. indicator (f i) (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel) =
                         (\<lambda>i. \<integral>\<^sup>+ x. ereal (g' x * indicator {a..b} x) * indicator ({a..b} \<inter> g -` f i) x \<partial>lborel)"
        by (intro ext nn_integral_cong) (simp split: split_indicator)
      also have "(\<Sum>i. ... i) = \<integral>\<^sup>+ x. (\<Sum>i. ereal (g' x * indicator {a..b} x) * indicator ({a..b} \<inter> g -` f i) x) \<partial>lborel"
        using Mg'
        apply (intro nn_integral_suminf[symmetric])
        apply (rule borel_measurable_ereal_times, simp add: borel_measurable_ereal mult.commute)
        apply (rule borel_measurable_indicator, subst sets_lborel)
        apply (simp_all split: split_indicator add: derivg_nonneg)
        done
      also have "(\<lambda>x i. ereal (g' x * indicator {a..b} x) * indicator ({a..b} \<inter> g -` f i) x) =
                      (\<lambda>x i. ereal (g' x * indicator {a..b} x) * indicator (g -` f i) x)"
        by (intro ext) (simp split: split_indicator)
      also have "(\<integral>\<^sup>+ x. (\<Sum>i. ereal (g' x * indicator {a..b} x) * indicator (g -` f i) x) \<partial>lborel) =
                     \<integral>\<^sup>+ x. ereal (g' x * indicator {a..b} x) * (\<Sum>i. indicator (g -` f i) x) \<partial>lborel"
        by (intro nn_integral_cong suminf_cmult_ereal) (auto split: split_indicator simp: derivg_nonneg)
      also from union have "(\<lambda>x. \<Sum>i. indicator (g -` f i) x :: ereal) = (\<lambda>x. indicator (\<Union>i. g -` f i) x)"
        by (intro ext suminf_indicator) (auto simp: disjoint_family_on_def)
      also have "(\<integral>\<^sup>+x. ereal (g' x * indicator {a..b} x) * ... x \<partial>lborel) =
                    (\<integral>\<^sup>+x. indicator (\<Union>i. f i) (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel)"
       by (intro nn_integral_cong) (simp split: split_indicator)
      finally show ?case .
  qed

next
  case (mult f c)
    note Mf[measurable] = `f \<in> borel_measurable borel`
    let ?I = "indicator {a..b}"
    have "(\<lambda>x. f (g x * ?I x) * ereal (g' x * ?I x)) \<in> borel_measurable borel" using Mg Mg'
      by (intro borel_measurable_ereal_times measurable_compose[OF _ Mf])
         (simp_all add: borel_measurable_ereal mult.commute)
    also have "(\<lambda>x. f (g x * ?I x) * ereal (g' x * ?I x)) = (\<lambda>x. f (g x) * ereal (g' x) * ?I x)"
      by (intro ext) (simp split: split_indicator)
    finally have Mf': "(\<lambda>x. f (g x) * ereal (g' x) * ?I x) \<in> borel_measurable borel" .
    with mult show ?case
      by (subst (1 2 3) mult_ac, subst (1 2) nn_integral_cmult) (simp_all add: mult_ac)
 
next
  case (add f2 f1)
    let ?I = "indicator {a..b}"
    {
      fix f :: "real \<Rightarrow> ereal" assume Mf: "f \<in> borel_measurable borel"
      have "(\<lambda>x. f (g x * ?I x) * ereal (g' x * ?I x)) \<in> borel_measurable borel" using Mg Mg'
        by (intro borel_measurable_ereal_times measurable_compose[OF _ Mf])
           (simp_all add: borel_measurable_ereal mult.commute)
      also have "(\<lambda>x. f (g x * ?I x) * ereal (g' x * ?I x)) = (\<lambda>x. f (g x) * ereal (g' x) * ?I x)"
        by (intro ext) (simp split: split_indicator)
      finally have "(\<lambda>x. f (g x) * ereal (g' x) * ?I x) \<in> borel_measurable borel" .
    } note Mf' = this[OF `f1 \<in> borel_measurable borel`] this[OF `f2 \<in> borel_measurable borel`]
    from add have not_neginf: "\<And>x. f1 x \<noteq> -\<infinity>" "\<And>x. f2 x \<noteq> -\<infinity>" 
      by (metis Infty_neq_0(1) ereal_0_le_uminus_iff ereal_infty_less_eq(1))+

    have "(\<integral>\<^sup>+ x. (f1 x + f2 x) * indicator {g a..g b} x \<partial>lborel) =
             (\<integral>\<^sup>+ x. f1 x * indicator {g a..g b} x + f2 x * indicator {g a..g b} x \<partial>lborel)"
      by (intro nn_integral_cong) (simp split: split_indicator)
    also from add have "... = (\<integral>\<^sup>+ x. f1 (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel) +
                                (\<integral>\<^sup>+ x. f2 (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel)"
      by (simp_all add: nn_integral_add)
    also from add have "... = (\<integral>\<^sup>+ x. f1 (g x) * ereal (g' x) * indicator {a..b} x + 
                                      f2 (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel)"
      by (intro nn_integral_add[symmetric])
         (auto simp add: Mf' derivg_nonneg split: split_indicator)
    also from not_neginf have "... = \<integral>\<^sup>+ x. (f1 (g x) + f2 (g x)) * ereal (g' x) * indicator {a..b} x \<partial>lborel"
      by (intro nn_integral_cong) (simp split: split_indicator add: ereal_distrib)
    finally show ?case .

next
  case (sup F)
  {
    fix i
    let ?I = "indicator {a..b}"
    have "(\<lambda>x. F i (g x * ?I x) * ereal (g' x * ?I x)) \<in> borel_measurable borel" using Mg Mg'
      by (rule_tac borel_measurable_ereal_times, rule_tac measurable_compose[OF _ sup.hyps(1)])
         (simp_all add: mult.commute)
    also have "(\<lambda>x. F i (g x * ?I x) * ereal (g' x * ?I x)) = (\<lambda>x. F i (g x) * ereal (g' x) * ?I x)"
      by (intro ext) (simp split: split_indicator)
     finally have "... \<in> borel_measurable borel" .
  } note Mf' = this

    have "(\<integral>\<^sup>+x. (SUP i. F i x) * indicator {g a..g b} x \<partial>lborel) = 
               \<integral>\<^sup>+x. (SUP i. F i x* indicator {g a..g b} x) \<partial>lborel"
      by (intro nn_integral_cong) (simp split: split_indicator)
    also from sup have "... = (SUP i. \<integral>\<^sup>+x. F i x* indicator {g a..g b} x \<partial>lborel)"
      by (intro nn_integral_monotone_convergence_SUP)
         (auto simp: incseq_def le_fun_def split: split_indicator)
    also from sup have "... = (SUP i. \<integral>\<^sup>+x. F i (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel)"
      by simp
    also from sup have "... =  \<integral>\<^sup>+x. (SUP i. F i (g x) * ereal (g' x) * indicator {a..b} x) \<partial>lborel"
      by (intro nn_integral_monotone_convergence_SUP[symmetric])
         (auto simp: incseq_def le_fun_def derivg_nonneg Mf' split: split_indicator
               intro!: ereal_mult_right_mono)
    also from sup have "... = \<integral>\<^sup>+x. (SUP i. F i (g x)) * ereal (g' x) * indicator {a..b} x \<partial>lborel"
      by (subst mult.assoc, subst mult.commute, subst SUP_ereal_mult_left)
         (auto split: split_indicator simp: derivg_nonneg mult_ac)
    finally show ?case by simp
  qed
qed

lemma nn_integral_substitution:
  fixes f :: "real \<Rightarrow> real"
  assumes Mf[measurable]: "set_borel_measurable borel {g a..g b} f"
  assumes derivg: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_real_derivative g' x) (at x)"
  assumes contg': "continuous_on {a..b} g'" 
  assumes derivg_nonneg: "\<And>x. x \<in> {a..b} \<Longrightarrow> g' x \<ge> 0"
  assumes "a \<le> b"
  shows "(\<integral>\<^sup>+x. f x * indicator {g a..g b} x \<partial>lborel) = 
             (\<integral>\<^sup>+x. f (g x) * g' x * indicator {a..b} x \<partial>lborel)"
proof (cases "a = b")
  assume "a \<noteq> b"
  with `a \<le> b` have "a < b" by auto
  let ?f' = "\<lambda>x. max 0 (f x * indicator {g a..g b} x)"

  from derivg derivg_nonneg have monog: "\<And>x y. a \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> b \<Longrightarrow> g x \<le> g y"
    by (rule deriv_nonneg_imp_mono) simp_all
  have bounds: "\<And>x. x \<ge> a \<Longrightarrow> x \<le> b \<Longrightarrow> g x \<ge> g a" "\<And>x. x \<ge> a \<Longrightarrow> x \<le> b \<Longrightarrow> g x \<le> g b"
    by (auto intro: monog)

  from derivg_nonneg have nonneg: 
    "\<And>f x. x \<ge> a \<Longrightarrow> x \<le> b \<Longrightarrow> g' x \<noteq> 0 \<Longrightarrow> f x * ereal (g' x) \<ge> 0 \<Longrightarrow> f x \<ge> 0"
    by (force simp: ereal_zero_le_0_iff field_simps)
  have nonneg': "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> \<not> 0 \<le> f (g x) \<Longrightarrow> 0 \<le> f (g x) * g' x \<Longrightarrow> g' x = 0"
    by (metis atLeastAtMost_iff derivg_nonneg eq_iff mult_eq_0_iff mult_le_0_iff)

  have "(\<integral>\<^sup>+x. f x * indicator {g a..g b} x \<partial>lborel) = 
            (\<integral>\<^sup>+x. ereal (?f' x) * indicator {g a..g b} x \<partial>lborel)"
    by (subst nn_integral_max_0[symmetric], intro nn_integral_cong) 
       (auto split: split_indicator simp: zero_ereal_def)
  also have "... = \<integral>\<^sup>+ x. ?f' (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel" using Mf
    by (subst nn_integral_substitution_aux[OF _ _ derivg contg' derivg_nonneg `a < b`]) 
       (auto simp add: zero_ereal_def mult.commute)
  also have "... = \<integral>\<^sup>+ x. max 0 (f (g x)) * ereal (g' x) * indicator {a..b} x \<partial>lborel"
    by (intro nn_integral_cong) 
       (auto split: split_indicator simp: max_def dest: bounds)
  also have "... = \<integral>\<^sup>+ x. max 0 (f (g x) * ereal (g' x) * indicator {a..b} x) \<partial>lborel"
    by (intro nn_integral_cong)
       (auto simp: max_def derivg_nonneg split: split_indicator intro!: nonneg')
  also have "... = \<integral>\<^sup>+ x. f (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel"
    by (rule nn_integral_max_0)
  also have "... = \<integral>\<^sup>+x. ereal (f (g x) * g' x * indicator {a..b} x) \<partial>lborel"
    by (intro nn_integral_cong) (simp split: split_indicator)
  finally show ?thesis .
qed auto

lemma integral_substitution:
  assumes integrable: "set_integrable lborel {g a..g b} f"
  assumes derivg: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_real_derivative g' x) (at x)"
  assumes contg': "continuous_on {a..b} g'" 
  assumes derivg_nonneg: "\<And>x. x \<in> {a..b} \<Longrightarrow> g' x \<ge> 0"
  assumes "a \<le> b"
  shows "set_integrable lborel {a..b} (\<lambda>x. f (g x) * g' x)"
    and "(LBINT x. f x * indicator {g a..g b} x) = (LBINT x. f (g x) * g' x * indicator {a..b} x)"
proof-
  from derivg have contg: "continuous_on {a..b} g" by (rule has_real_derivative_imp_continuous_on)
  from this and contg' have Mg: "set_borel_measurable borel {a..b} g" and 
                             Mg': "set_borel_measurable borel {a..b} g'" 
      by (simp_all only: set_measurable_continuous_on_ivl)
  from derivg derivg_nonneg have monog: "\<And>x y. a \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> b \<Longrightarrow> g x \<le> g y"
    by (rule deriv_nonneg_imp_mono) simp_all

  have "(\<lambda>x. ereal (f x) * indicator {g a..g b} x) = 
           (\<lambda>x. ereal (f x * indicator {g a..g b} x))" 
    by (intro ext) (simp split: split_indicator)
  with integrable have M1: "(\<lambda>x. f x * indicator {g a..g b} x) \<in> borel_measurable borel"
    unfolding real_integrable_def by (force simp: mult.commute)
  have "(\<lambda>x. ereal (-f x) * indicator {g a..g b} x) = 
           (\<lambda>x. -ereal (f x * indicator {g a..g b} x))" 
    by (intro ext) (simp split: split_indicator)
  with integrable have M2: "(\<lambda>x. -f x * indicator {g a..g b} x) \<in> borel_measurable borel"
    unfolding real_integrable_def by (force simp: mult.commute)

  have "LBINT x. (f x :: real) * indicator {g a..g b} x = 
          real (\<integral>\<^sup>+ x. ereal (f x) * indicator {g a..g b} x \<partial>lborel) -
          real (\<integral>\<^sup>+ x. ereal (- (f x)) * indicator {g a..g b} x \<partial>lborel)" using integrable
    by (subst real_lebesgue_integral_def) (simp_all add: nn_integral_set_ereal mult.commute)
  also have "(\<integral>\<^sup>+x. ereal (f x) * indicator {g a..g b} x \<partial>lborel) =
               (\<integral>\<^sup>+x. ereal (f x * indicator {g a..g b} x) \<partial>lborel)"
    by (intro nn_integral_cong) (simp split: split_indicator)
  also with M1 have A: "(\<integral>\<^sup>+ x. ereal (f x * indicator {g a..g b} x) \<partial>lborel) =
                            (\<integral>\<^sup>+ x. ereal (f (g x) * g' x * indicator {a..b} x) \<partial>lborel)"
    by (subst nn_integral_substitution[OF _ derivg contg' derivg_nonneg `a \<le> b`]) 
       (auto simp: nn_integral_set_ereal mult.commute)
  also have "(\<integral>\<^sup>+ x. ereal (- (f x)) * indicator {g a..g b} x \<partial>lborel) =
               (\<integral>\<^sup>+ x. ereal (- (f x) * indicator {g a..g b} x) \<partial>lborel)"
    by (intro nn_integral_cong) (simp split: split_indicator)
  also with M2 have B: "(\<integral>\<^sup>+ x. ereal (- (f x) * indicator {g a..g b} x) \<partial>lborel) =
                            (\<integral>\<^sup>+ x. ereal (- (f (g x)) * g' x * indicator {a..b} x) \<partial>lborel)"
    by (subst nn_integral_substitution[OF _ derivg contg' derivg_nonneg `a \<le> b`])
       (auto simp: nn_integral_set_ereal mult.commute)

  also {
    from integrable have Mf: "set_borel_measurable borel {g a..g b} f" 
      unfolding real_integrable_def by simp
    from borel_measurable_times[OF measurable_compose[OF Mg Mf] Mg']
      have "(\<lambda>x. f (g x * indicator {a..b} x) * indicator {g a..g b} (g x * indicator {a..b} x) *
                     (g' x * indicator {a..b} x)) \<in> borel_measurable borel"  (is "?f \<in> _") 
      by (simp add: mult.commute)
    also have "?f = (\<lambda>x. f (g x) * g' x * indicator {a..b} x)"
      using monog by (intro ext) (auto split: split_indicator)
    finally show "set_integrable lborel {a..b} (\<lambda>x. f (g x) * g' x)"
      using A B integrable unfolding real_integrable_def 
      by (simp_all add: nn_integral_set_ereal mult.commute)
  } note integrable' = this

  have "real (\<integral>\<^sup>+ x. ereal (f (g x) * g' x * indicator {a..b} x) \<partial>lborel) -
                  real (\<integral>\<^sup>+ x. ereal (-f (g x) * g' x * indicator {a..b} x) \<partial>lborel) =
                (LBINT x. f (g x) * g' x * indicator {a..b} x)" using integrable'
    by (subst real_lebesgue_integral_def) (simp_all add: field_simps)
  finally show "(LBINT x. f x * indicator {g a..g b} x) = 
                     (LBINT x. f (g x) * g' x * indicator {a..b} x)" .
qed

lemma interval_integral_substitution:
  assumes integrable: "set_integrable lborel {g a..g b} f"
  assumes derivg: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_real_derivative g' x) (at x)"
  assumes contg': "continuous_on {a..b} g'" 
  assumes derivg_nonneg: "\<And>x. x \<in> {a..b} \<Longrightarrow> g' x \<ge> 0"
  assumes "a \<le> b"
  shows "set_integrable lborel {a..b} (\<lambda>x. f (g x) * g' x)"
    and "(LBINT x=g a..g b. f x) = (LBINT x=a..b. f (g x) * g' x)"
  apply (rule integral_substitution[OF assms], simp, simp)
  apply (subst (1 2) interval_integral_Icc, fact)
  apply (rule deriv_nonneg_imp_mono[OF derivg derivg_nonneg], simp, simp, fact)
  using integral_substitution(2)[OF assms]
  apply (simp add: mult.commute)
  done

lemma set_borel_integrable_singleton[simp]:
  "set_integrable lborel {x} (f :: real \<Rightarrow> real)"
  by (subst integrable_discrete_difference[where X="{x}" and g="\<lambda>_. 0"]) auto

end
