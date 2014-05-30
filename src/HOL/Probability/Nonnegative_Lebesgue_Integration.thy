(*  Title:      HOL/Probability/Nonnegative_Lebesgue_Integration.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

header {* Lebesgue Integration for Nonnegative Functions *}

theory Nonnegative_Lebesgue_Integration
  imports Measure_Space Borel_Space
begin

lemma indicator_less_ereal[simp]:
  "indicator A x \<le> (indicator B x::ereal) \<longleftrightarrow> (x \<in> A \<longrightarrow> x \<in> B)"
  by (simp add: indicator_def not_le)

subsection "Simple function"

text {*

Our simple functions are not restricted to nonnegative real numbers. Instead
they are just functions with a finite range and are measurable when singleton
sets are measurable.

*}

definition "simple_function M g \<longleftrightarrow>
    finite (g ` space M) \<and>
    (\<forall>x \<in> g ` space M. g -` {x} \<inter> space M \<in> sets M)"

lemma simple_functionD:
  assumes "simple_function M g"
  shows "finite (g ` space M)" and "g -` X \<inter> space M \<in> sets M"
proof -
  show "finite (g ` space M)"
    using assms unfolding simple_function_def by auto
  have "g -` X \<inter> space M = g -` (X \<inter> g`space M) \<inter> space M" by auto
  also have "\<dots> = (\<Union>x\<in>X \<inter> g`space M. g-`{x} \<inter> space M)" by auto
  finally show "g -` X \<inter> space M \<in> sets M" using assms
    by (auto simp del: UN_simps simp: simple_function_def)
qed

lemma measurable_simple_function[measurable_dest]:
  "simple_function M f \<Longrightarrow> f \<in> measurable M (count_space UNIV)"
  unfolding simple_function_def measurable_def
proof safe
  fix A assume "finite (f ` space M)" "\<forall>x\<in>f ` space M. f -` {x} \<inter> space M \<in> sets M"
  then have "(\<Union>x\<in>f ` space M. if x \<in> A then f -` {x} \<inter> space M else {}) \<in> sets M"
    by (intro sets.finite_UN) auto
  also have "(\<Union>x\<in>f ` space M. if x \<in> A then f -` {x} \<inter> space M else {}) = f -` A \<inter> space M"
    by (auto split: split_if_asm)
  finally show "f -` A \<inter> space M \<in> sets M" .
qed simp

lemma borel_measurable_simple_function:
  "simple_function M f \<Longrightarrow> f \<in> borel_measurable M"
  by (auto dest!: measurable_simple_function simp: measurable_def)

lemma simple_function_measurable2[intro]:
  assumes "simple_function M f" "simple_function M g"
  shows "f -` A \<inter> g -` B \<inter> space M \<in> sets M"
proof -
  have "f -` A \<inter> g -` B \<inter> space M = (f -` A \<inter> space M) \<inter> (g -` B \<inter> space M)"
    by auto
  then show ?thesis using assms[THEN simple_functionD(2)] by auto
qed

lemma simple_function_indicator_representation:
  fixes f ::"'a \<Rightarrow> ereal"
  assumes f: "simple_function M f" and x: "x \<in> space M"
  shows "f x = (\<Sum>y \<in> f ` space M. y * indicator (f -` {y} \<inter> space M) x)"
  (is "?l = ?r")
proof -
  have "?r = (\<Sum>y \<in> f ` space M.
    (if y = f x then y * indicator (f -` {y} \<inter> space M) x else 0))"
    by (auto intro!: setsum_cong2)
  also have "... =  f x *  indicator (f -` {f x} \<inter> space M) x"
    using assms by (auto dest: simple_functionD simp: setsum_delta)
  also have "... = f x" using x by (auto simp: indicator_def)
  finally show ?thesis by auto
qed

lemma simple_function_notspace:
  "simple_function M (\<lambda>x. h x * indicator (- space M) x::ereal)" (is "simple_function M ?h")
proof -
  have "?h ` space M \<subseteq> {0}" unfolding indicator_def by auto
  hence [simp, intro]: "finite (?h ` space M)" by (auto intro: finite_subset)
  have "?h -` {0} \<inter> space M = space M" by auto
  thus ?thesis unfolding simple_function_def by auto
qed

lemma simple_function_cong:
  assumes "\<And>t. t \<in> space M \<Longrightarrow> f t = g t"
  shows "simple_function M f \<longleftrightarrow> simple_function M g"
proof -
  have "f ` space M = g ` space M"
    "\<And>x. f -` {x} \<inter> space M = g -` {x} \<inter> space M"
    using assms by (auto intro!: image_eqI)
  thus ?thesis unfolding simple_function_def using assms by simp
qed

lemma simple_function_cong_algebra:
  assumes "sets N = sets M" "space N = space M"
  shows "simple_function M f \<longleftrightarrow> simple_function N f"
  unfolding simple_function_def assms ..

lemma simple_function_borel_measurable:
  fixes f :: "'a \<Rightarrow> 'x::{t2_space}"
  assumes "f \<in> borel_measurable M" and "finite (f ` space M)"
  shows "simple_function M f"
  using assms unfolding simple_function_def
  by (auto intro: borel_measurable_vimage)

lemma simple_function_eq_measurable:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "simple_function M f \<longleftrightarrow> finite (f`space M) \<and> f \<in> measurable M (count_space UNIV)"
  using simple_function_borel_measurable[of f] measurable_simple_function[of M f]
  by (fastforce simp: simple_function_def)

lemma simple_function_const[intro, simp]:
  "simple_function M (\<lambda>x. c)"
  by (auto intro: finite_subset simp: simple_function_def)
lemma simple_function_compose[intro, simp]:
  assumes "simple_function M f"
  shows "simple_function M (g \<circ> f)"
  unfolding simple_function_def
proof safe
  show "finite ((g \<circ> f) ` space M)"
    using assms unfolding simple_function_def by (auto simp: image_comp [symmetric])
next
  fix x assume "x \<in> space M"
  let ?G = "g -` {g (f x)} \<inter> (f`space M)"
  have *: "(g \<circ> f) -` {(g \<circ> f) x} \<inter> space M =
    (\<Union>x\<in>?G. f -` {x} \<inter> space M)" by auto
  show "(g \<circ> f) -` {(g \<circ> f) x} \<inter> space M \<in> sets M"
    using assms unfolding simple_function_def *
    by (rule_tac sets.finite_UN) auto
qed

lemma simple_function_indicator[intro, simp]:
  assumes "A \<in> sets M"
  shows "simple_function M (indicator A)"
proof -
  have "indicator A ` space M \<subseteq> {0, 1}" (is "?S \<subseteq> _")
    by (auto simp: indicator_def)
  hence "finite ?S" by (rule finite_subset) simp
  moreover have "- A \<inter> space M = space M - A" by auto
  ultimately show ?thesis unfolding simple_function_def
    using assms by (auto simp: indicator_def [abs_def])
qed

lemma simple_function_Pair[intro, simp]:
  assumes "simple_function M f"
  assumes "simple_function M g"
  shows "simple_function M (\<lambda>x. (f x, g x))" (is "simple_function M ?p")
  unfolding simple_function_def
proof safe
  show "finite (?p ` space M)"
    using assms unfolding simple_function_def
    by (rule_tac finite_subset[of _ "f`space M \<times> g`space M"]) auto
next
  fix x assume "x \<in> space M"
  have "(\<lambda>x. (f x, g x)) -` {(f x, g x)} \<inter> space M =
      (f -` {f x} \<inter> space M) \<inter> (g -` {g x} \<inter> space M)"
    by auto
  with `x \<in> space M` show "(\<lambda>x. (f x, g x)) -` {(f x, g x)} \<inter> space M \<in> sets M"
    using assms unfolding simple_function_def by auto
qed

lemma simple_function_compose1:
  assumes "simple_function M f"
  shows "simple_function M (\<lambda>x. g (f x))"
  using simple_function_compose[OF assms, of g]
  by (simp add: comp_def)

lemma simple_function_compose2:
  assumes "simple_function M f" and "simple_function M g"
  shows "simple_function M (\<lambda>x. h (f x) (g x))"
proof -
  have "simple_function M ((\<lambda>(x, y). h x y) \<circ> (\<lambda>x. (f x, g x)))"
    using assms by auto
  thus ?thesis by (simp_all add: comp_def)
qed

lemmas simple_function_add[intro, simp] = simple_function_compose2[where h="op +"]
  and simple_function_diff[intro, simp] = simple_function_compose2[where h="op -"]
  and simple_function_uminus[intro, simp] = simple_function_compose[where g="uminus"]
  and simple_function_mult[intro, simp] = simple_function_compose2[where h="op *"]
  and simple_function_div[intro, simp] = simple_function_compose2[where h="op /"]
  and simple_function_inverse[intro, simp] = simple_function_compose[where g="inverse"]
  and simple_function_max[intro, simp] = simple_function_compose2[where h=max]

lemma simple_function_setsum[intro, simp]:
  assumes "\<And>i. i \<in> P \<Longrightarrow> simple_function M (f i)"
  shows "simple_function M (\<lambda>x. \<Sum>i\<in>P. f i x)"
proof cases
  assume "finite P" from this assms show ?thesis by induct auto
qed auto

lemma simple_function_ereal[intro, simp]: 
  fixes f g :: "'a \<Rightarrow> real" assumes sf: "simple_function M f"
  shows "simple_function M (\<lambda>x. ereal (f x))"
  by (auto intro!: simple_function_compose1[OF sf])

lemma simple_function_real_of_nat[intro, simp]: 
  fixes f g :: "'a \<Rightarrow> nat" assumes sf: "simple_function M f"
  shows "simple_function M (\<lambda>x. real (f x))"
  by (auto intro!: simple_function_compose1[OF sf])

lemma borel_measurable_implies_simple_function_sequence:
  fixes u :: "'a \<Rightarrow> ereal"
  assumes u: "u \<in> borel_measurable M"
  shows "\<exists>f. incseq f \<and> (\<forall>i. \<infinity> \<notin> range (f i) \<and> simple_function M (f i)) \<and>
             (\<forall>x. (SUP i. f i x) = max 0 (u x)) \<and> (\<forall>i x. 0 \<le> f i x)"
proof -
  def f \<equiv> "\<lambda>x i. if real i \<le> u x then i * 2 ^ i else natfloor (real (u x) * 2 ^ i)"
  { fix x j have "f x j \<le> j * 2 ^ j" unfolding f_def
    proof (split split_if, intro conjI impI)
      assume "\<not> real j \<le> u x"
      then have "natfloor (real (u x) * 2 ^ j) \<le> natfloor (j * 2 ^ j)"
         by (cases "u x") (auto intro!: natfloor_mono)
      moreover have "real (natfloor (j * 2 ^ j)) \<le> j * 2^j"
        by (intro real_natfloor_le) auto
      ultimately show "natfloor (real (u x) * 2 ^ j) \<le> j * 2 ^ j"
        unfolding real_of_nat_le_iff by auto
    qed auto }
  note f_upper = this

  have real_f:
    "\<And>i x. real (f x i) = (if real i \<le> u x then i * 2 ^ i else real (natfloor (real (u x) * 2 ^ i)))"
    unfolding f_def by auto

  let ?g = "\<lambda>j x. real (f x j) / 2^j :: ereal"
  show ?thesis
  proof (intro exI[of _ ?g] conjI allI ballI)
    fix i
    have "simple_function M (\<lambda>x. real (f x i))"
    proof (intro simple_function_borel_measurable)
      show "(\<lambda>x. real (f x i)) \<in> borel_measurable M"
        using u by (auto simp: real_f)
      have "(\<lambda>x. real (f x i))`space M \<subseteq> real`{..i*2^i}"
        using f_upper[of _ i] by auto
      then show "finite ((\<lambda>x. real (f x i))`space M)"
        by (rule finite_subset) auto
    qed
    then show "simple_function M (?g i)"
      by (auto intro: simple_function_ereal simple_function_div)
  next
    show "incseq ?g"
    proof (intro incseq_ereal incseq_SucI le_funI)
      fix x and i :: nat
      have "f x i * 2 \<le> f x (Suc i)" unfolding f_def
      proof ((split split_if)+, intro conjI impI)
        assume "ereal (real i) \<le> u x" "\<not> ereal (real (Suc i)) \<le> u x"
        then show "i * 2 ^ i * 2 \<le> natfloor (real (u x) * 2 ^ Suc i)"
          by (cases "u x") (auto intro!: le_natfloor)
      next
        assume "\<not> ereal (real i) \<le> u x" "ereal (real (Suc i)) \<le> u x"
        then show "natfloor (real (u x) * 2 ^ i) * 2 \<le> Suc i * 2 ^ Suc i"
          by (cases "u x") auto
      next
        assume "\<not> ereal (real i) \<le> u x" "\<not> ereal (real (Suc i)) \<le> u x"
        have "natfloor (real (u x) * 2 ^ i) * 2 = natfloor (real (u x) * 2 ^ i) * natfloor 2"
          by simp
        also have "\<dots> \<le> natfloor (real (u x) * 2 ^ i * 2)"
        proof cases
          assume "0 \<le> u x" then show ?thesis
            by (intro le_mult_natfloor) 
        next
          assume "\<not> 0 \<le> u x" then show ?thesis
            by (cases "u x") (auto simp: natfloor_neg mult_nonpos_nonneg)
        qed
        also have "\<dots> = natfloor (real (u x) * 2 ^ Suc i)"
          by (simp add: ac_simps)
        finally show "natfloor (real (u x) * 2 ^ i) * 2 \<le> natfloor (real (u x) * 2 ^ Suc i)" .
      qed simp
      then show "?g i x \<le> ?g (Suc i) x"
        by (auto simp: field_simps)
    qed
  next
    fix x show "(SUP i. ?g i x) = max 0 (u x)"
    proof (rule SUP_eqI)
      fix i show "?g i x \<le> max 0 (u x)" unfolding max_def f_def
        by (cases "u x") (auto simp: field_simps real_natfloor_le natfloor_neg
                                     mult_nonpos_nonneg)
    next
      fix y assume *: "\<And>i. i \<in> UNIV \<Longrightarrow> ?g i x \<le> y"
      have "\<And>i. 0 \<le> ?g i x" by auto
      from order_trans[OF this *] have "0 \<le> y" by simp
      show "max 0 (u x) \<le> y"
      proof (cases y)
        case (real r)
        with * have *: "\<And>i. f x i \<le> r * 2^i" by (auto simp: divide_le_eq)
        from reals_Archimedean2[of r] * have "u x \<noteq> \<infinity>" by (auto simp: f_def) (metis less_le_not_le)
        then have "\<exists>p. max 0 (u x) = ereal p \<and> 0 \<le> p" by (cases "u x") (auto simp: max_def)
        then guess p .. note ux = this
        obtain m :: nat where m: "p < real m" using reals_Archimedean2 ..
        have "p \<le> r"
        proof (rule ccontr)
          assume "\<not> p \<le> r"
          with LIMSEQ_inverse_realpow_zero[unfolded LIMSEQ_iff, rule_format, of 2 "p - r"]
          obtain N where "\<forall>n\<ge>N. r * 2^n < p * 2^n - 1" by (auto simp: field_simps)
          then have "r * 2^max N m < p * 2^max N m - 1" by simp
          moreover
          have "real (natfloor (p * 2 ^ max N m)) \<le> r * 2 ^ max N m"
            using *[of "max N m"] m unfolding real_f using ux
            by (cases "0 \<le> u x") (simp_all add: max_def split: split_if_asm)
          then have "p * 2 ^ max N m - 1 < r * 2 ^ max N m"
            by (metis real_natfloor_gt_diff_one less_le_trans)
          ultimately show False by auto
        qed
        then show "max 0 (u x) \<le> y" using real ux by simp
      qed (insert `0 \<le> y`, auto)
    qed
  qed auto
qed

lemma borel_measurable_implies_simple_function_sequence':
  fixes u :: "'a \<Rightarrow> ereal"
  assumes u: "u \<in> borel_measurable M"
  obtains f where "\<And>i. simple_function M (f i)" "incseq f" "\<And>i. \<infinity> \<notin> range (f i)"
    "\<And>x. (SUP i. f i x) = max 0 (u x)" "\<And>i x. 0 \<le> f i x"
  using borel_measurable_implies_simple_function_sequence[OF u] by auto

lemma simple_function_induct[consumes 1, case_names cong set mult add, induct set: simple_function]:
  fixes u :: "'a \<Rightarrow> ereal"
  assumes u: "simple_function M u"
  assumes cong: "\<And>f g. simple_function M f \<Longrightarrow> simple_function M g \<Longrightarrow> (AE x in M. f x = g x) \<Longrightarrow> P f \<Longrightarrow> P g"
  assumes set: "\<And>A. A \<in> sets M \<Longrightarrow> P (indicator A)"
  assumes mult: "\<And>u c. P u \<Longrightarrow> P (\<lambda>x. c * u x)"
  assumes add: "\<And>u v. P u \<Longrightarrow> P v \<Longrightarrow> P (\<lambda>x. v x + u x)"
  shows "P u"
proof (rule cong)
  from AE_space show "AE x in M. (\<Sum>y\<in>u ` space M. y * indicator (u -` {y} \<inter> space M) x) = u x"
  proof eventually_elim
    fix x assume x: "x \<in> space M"
    from simple_function_indicator_representation[OF u x]
    show "(\<Sum>y\<in>u ` space M. y * indicator (u -` {y} \<inter> space M) x) = u x" ..
  qed
next
  from u have "finite (u ` space M)"
    unfolding simple_function_def by auto
  then show "P (\<lambda>x. \<Sum>y\<in>u ` space M. y * indicator (u -` {y} \<inter> space M) x)"
  proof induct
    case empty show ?case
      using set[of "{}"] by (simp add: indicator_def[abs_def])
  qed (auto intro!: add mult set simple_functionD u)
next
  show "simple_function M (\<lambda>x. (\<Sum>y\<in>u ` space M. y * indicator (u -` {y} \<inter> space M) x))"
    apply (subst simple_function_cong)
    apply (rule simple_function_indicator_representation[symmetric])
    apply (auto intro: u)
    done
qed fact

lemma simple_function_induct_nn[consumes 2, case_names cong set mult add]:
  fixes u :: "'a \<Rightarrow> ereal"
  assumes u: "simple_function M u" and nn: "\<And>x. 0 \<le> u x"
  assumes cong: "\<And>f g. simple_function M f \<Longrightarrow> simple_function M g \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> P f \<Longrightarrow> P g"
  assumes set: "\<And>A. A \<in> sets M \<Longrightarrow> P (indicator A)"
  assumes mult: "\<And>u c. 0 \<le> c \<Longrightarrow> simple_function M u \<Longrightarrow> (\<And>x. 0 \<le> u x) \<Longrightarrow> P u \<Longrightarrow> P (\<lambda>x. c * u x)"
  assumes add: "\<And>u v. simple_function M u \<Longrightarrow> (\<And>x. 0 \<le> u x) \<Longrightarrow> P u \<Longrightarrow> simple_function M v \<Longrightarrow> (\<And>x. 0 \<le> v x) \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> u x = 0 \<or> v x = 0) \<Longrightarrow> P v \<Longrightarrow> P (\<lambda>x. v x + u x)"
  shows "P u"
proof -
  show ?thesis
  proof (rule cong)
    fix x assume x: "x \<in> space M"
    from simple_function_indicator_representation[OF u x]
    show "(\<Sum>y\<in>u ` space M. y * indicator (u -` {y} \<inter> space M) x) = u x" ..
  next
    show "simple_function M (\<lambda>x. (\<Sum>y\<in>u ` space M. y * indicator (u -` {y} \<inter> space M) x))"
      apply (subst simple_function_cong)
      apply (rule simple_function_indicator_representation[symmetric])
      apply (auto intro: u)
      done
  next
    
    from u nn have "finite (u ` space M)" "\<And>x. x \<in> u ` space M \<Longrightarrow> 0 \<le> x"
      unfolding simple_function_def by auto
    then show "P (\<lambda>x. \<Sum>y\<in>u ` space M. y * indicator (u -` {y} \<inter> space M) x)"
    proof induct
      case empty show ?case
        using set[of "{}"] by (simp add: indicator_def[abs_def])
    next
      case (insert x S)
      { fix z have "(\<Sum>y\<in>S. y * indicator (u -` {y} \<inter> space M) z) = 0 \<or>
          x * indicator (u -` {x} \<inter> space M) z = 0"
          using insert by (subst setsum_ereal_0) (auto simp: indicator_def) }
      note disj = this
      from insert show ?case
        by (auto intro!: add mult set simple_functionD u setsum_nonneg simple_function_setsum disj)
    qed
  qed fact
qed

lemma borel_measurable_induct[consumes 2, case_names cong set mult add seq, induct set: borel_measurable]:
  fixes u :: "'a \<Rightarrow> ereal"
  assumes u: "u \<in> borel_measurable M" "\<And>x. 0 \<le> u x"
  assumes cong: "\<And>f g. f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> P g \<Longrightarrow> P f"
  assumes set: "\<And>A. A \<in> sets M \<Longrightarrow> P (indicator A)"
  assumes mult': "\<And>u c. 0 \<le> c \<Longrightarrow> c < \<infinity> \<Longrightarrow> u \<in> borel_measurable M \<Longrightarrow> (\<And>x. 0 \<le> u x) \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> u x < \<infinity>) \<Longrightarrow> P u \<Longrightarrow> P (\<lambda>x. c * u x)"
  assumes add: "\<And>u v. u \<in> borel_measurable M \<Longrightarrow> (\<And>x. 0 \<le> u x) \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> u x < \<infinity>) \<Longrightarrow> P u \<Longrightarrow> v \<in> borel_measurable M \<Longrightarrow> (\<And>x. 0 \<le> v x) \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> v x < \<infinity>) \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> u x = 0 \<or> v x = 0) \<Longrightarrow> P v \<Longrightarrow> P (\<lambda>x. v x + u x)"
  assumes seq: "\<And>U. (\<And>i. U i \<in> borel_measurable M) \<Longrightarrow> (\<And>i x. 0 \<le> U i x) \<Longrightarrow> (\<And>i x. x \<in> space M \<Longrightarrow> U i x < \<infinity>) \<Longrightarrow>  (\<And>i. P (U i)) \<Longrightarrow> incseq U \<Longrightarrow> u = (SUP i. U i) \<Longrightarrow> P (SUP i. U i)"
  shows "P u"
  using u
proof (induct rule: borel_measurable_implies_simple_function_sequence')
  fix U assume U: "\<And>i. simple_function M (U i)" "incseq U" "\<And>i. \<infinity> \<notin> range (U i)" and
    sup: "\<And>x. (SUP i. U i x) = max 0 (u x)" and nn: "\<And>i x. 0 \<le> U i x"
  have u_eq: "u = (SUP i. U i)"
    using nn u sup by (auto simp: max_def)

  have not_inf: "\<And>x i. x \<in> space M \<Longrightarrow> U i x < \<infinity>"
    using U by (auto simp: image_iff eq_commute)
  
  from U have "\<And>i. U i \<in> borel_measurable M"
    by (simp add: borel_measurable_simple_function)

  show "P u"
    unfolding u_eq
  proof (rule seq)
    fix i show "P (U i)"
      using `simple_function M (U i)` nn[of i] not_inf[of _ i]
    proof (induct rule: simple_function_induct_nn)
      case (mult u c)
      show ?case
      proof cases
        assume "c = 0 \<or> space M = {} \<or> (\<forall>x\<in>space M. u x = 0)"
        with mult(2) show ?thesis
          by (intro cong[of "\<lambda>x. c * u x" "indicator {}"] set)
             (auto dest!: borel_measurable_simple_function)
      next
        assume "\<not> (c = 0 \<or> space M = {} \<or> (\<forall>x\<in>space M. u x = 0))"
        with mult obtain x where u_fin: "\<And>x. x \<in> space M \<Longrightarrow> u x < \<infinity>"
          and x: "x \<in> space M" "u x \<noteq> 0" "c \<noteq> 0"
          by auto
        with mult have "P u"
          by auto
        from x mult(5)[OF `x \<in> space M`] mult(1) mult(3)[of x] have "c < \<infinity>"
          by auto
        with u_fin mult
        show ?thesis
          by (intro mult') (auto dest!: borel_measurable_simple_function)
      qed
    qed (auto intro: cong intro!: set add dest!: borel_measurable_simple_function)
  qed fact+
qed

lemma simple_function_If_set:
  assumes sf: "simple_function M f" "simple_function M g" and A: "A \<inter> space M \<in> sets M"
  shows "simple_function M (\<lambda>x. if x \<in> A then f x else g x)" (is "simple_function M ?IF")
proof -
  def F \<equiv> "\<lambda>x. f -` {x} \<inter> space M" and G \<equiv> "\<lambda>x. g -` {x} \<inter> space M"
  show ?thesis unfolding simple_function_def
  proof safe
    have "?IF ` space M \<subseteq> f ` space M \<union> g ` space M" by auto
    from finite_subset[OF this] assms
    show "finite (?IF ` space M)" unfolding simple_function_def by auto
  next
    fix x assume "x \<in> space M"
    then have *: "?IF -` {?IF x} \<inter> space M = (if x \<in> A
      then ((F (f x) \<inter> (A \<inter> space M)) \<union> (G (f x) - (G (f x) \<inter> (A \<inter> space M))))
      else ((F (g x) \<inter> (A \<inter> space M)) \<union> (G (g x) - (G (g x) \<inter> (A \<inter> space M)))))"
      using sets.sets_into_space[OF A] by (auto split: split_if_asm simp: G_def F_def)
    have [intro]: "\<And>x. F x \<in> sets M" "\<And>x. G x \<in> sets M"
      unfolding F_def G_def using sf[THEN simple_functionD(2)] by auto
    show "?IF -` {?IF x} \<inter> space M \<in> sets M" unfolding * using A by auto
  qed
qed

lemma simple_function_If:
  assumes sf: "simple_function M f" "simple_function M g" and P: "{x\<in>space M. P x} \<in> sets M"
  shows "simple_function M (\<lambda>x. if P x then f x else g x)"
proof -
  have "{x\<in>space M. P x} = {x. P x} \<inter> space M" by auto
  with simple_function_If_set[OF sf, of "{x. P x}"] P show ?thesis by simp
qed

lemma simple_function_subalgebra:
  assumes "simple_function N f"
  and N_subalgebra: "sets N \<subseteq> sets M" "space N = space M"
  shows "simple_function M f"
  using assms unfolding simple_function_def by auto

lemma simple_function_comp:
  assumes T: "T \<in> measurable M M'"
    and f: "simple_function M' f"
  shows "simple_function M (\<lambda>x. f (T x))"
proof (intro simple_function_def[THEN iffD2] conjI ballI)
  have "(\<lambda>x. f (T x)) ` space M \<subseteq> f ` space M'"
    using T unfolding measurable_def by auto
  then show "finite ((\<lambda>x. f (T x)) ` space M)"
    using f unfolding simple_function_def by (auto intro: finite_subset)
  fix i assume i: "i \<in> (\<lambda>x. f (T x)) ` space M"
  then have "i \<in> f ` space M'"
    using T unfolding measurable_def by auto
  then have "f -` {i} \<inter> space M' \<in> sets M'"
    using f unfolding simple_function_def by auto
  then have "T -` (f -` {i} \<inter> space M') \<inter> space M \<in> sets M"
    using T unfolding measurable_def by auto
  also have "T -` (f -` {i} \<inter> space M') \<inter> space M = (\<lambda>x. f (T x)) -` {i} \<inter> space M"
    using T unfolding measurable_def by auto
  finally show "(\<lambda>x. f (T x)) -` {i} \<inter> space M \<in> sets M" .
qed

subsection "Simple integral"

definition simple_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> ereal) \<Rightarrow> ereal" ("integral\<^sup>S") where
  "integral\<^sup>S M f = (\<Sum>x \<in> f ` space M. x * emeasure M (f -` {x} \<inter> space M))"

syntax
  "_simple_integral" :: "pttrn \<Rightarrow> ereal \<Rightarrow> 'a measure \<Rightarrow> ereal" ("\<integral>\<^sup>S _. _ \<partial>_" [60,61] 110)

translations
  "\<integral>\<^sup>S x. f \<partial>M" == "CONST simple_integral M (%x. f)"

lemma simple_integral_cong:
  assumes "\<And>t. t \<in> space M \<Longrightarrow> f t = g t"
  shows "integral\<^sup>S M f = integral\<^sup>S M g"
proof -
  have "f ` space M = g ` space M"
    "\<And>x. f -` {x} \<inter> space M = g -` {x} \<inter> space M"
    using assms by (auto intro!: image_eqI)
  thus ?thesis unfolding simple_integral_def by simp
qed

lemma simple_integral_const[simp]:
  "(\<integral>\<^sup>Sx. c \<partial>M) = c * (emeasure M) (space M)"
proof (cases "space M = {}")
  case True thus ?thesis unfolding simple_integral_def by simp
next
  case False hence "(\<lambda>x. c) ` space M = {c}" by auto
  thus ?thesis unfolding simple_integral_def by simp
qed

lemma simple_function_partition:
  assumes f: "simple_function M f" and g: "simple_function M g"
  assumes sub: "\<And>x y. x \<in> space M \<Longrightarrow> y \<in> space M \<Longrightarrow> g x = g y \<Longrightarrow> f x = f y"
  assumes v: "\<And>x. x \<in> space M \<Longrightarrow> f x = v (g x)"
  shows "integral\<^sup>S M f = (\<Sum>y\<in>g ` space M. v y * emeasure M {x\<in>space M. g x = y})"
    (is "_ = ?r")
proof -
  from f g have [simp]: "finite (f`space M)" "finite (g`space M)"
    by (auto simp: simple_function_def)
  from f g have [measurable]: "f \<in> measurable M (count_space UNIV)" "g \<in> measurable M (count_space UNIV)"
    by (auto intro: measurable_simple_function)

  { fix y assume "y \<in> space M"
    then have "f ` space M \<inter> {i. \<exists>x\<in>space M. i = f x \<and> g y = g x} = {v (g y)}"
      by (auto cong: sub simp: v[symmetric]) }
  note eq = this

  have "integral\<^sup>S M f =
    (\<Sum>y\<in>f`space M. y * (\<Sum>z\<in>g`space M. 
      if \<exists>x\<in>space M. y = f x \<and> z = g x then emeasure M {x\<in>space M. g x = z} else 0))"
    unfolding simple_integral_def
  proof (safe intro!: setsum_cong ereal_left_mult_cong)
    fix y assume y: "y \<in> space M" "f y \<noteq> 0"
    have [simp]: "g ` space M \<inter> {z. \<exists>x\<in>space M. f y = f x \<and> z = g x} = 
        {z. \<exists>x\<in>space M. f y = f x \<and> z = g x}"
      by auto
    have eq:"(\<Union>i\<in>{z. \<exists>x\<in>space M. f y = f x \<and> z = g x}. {x \<in> space M. g x = i}) =
        f -` {f y} \<inter> space M"
      by (auto simp: eq_commute cong: sub rev_conj_cong)
    have "finite (g`space M)" by simp
    then have "finite {z. \<exists>x\<in>space M. f y = f x \<and> z = g x}"
      by (rule rev_finite_subset) auto
    then show "emeasure M (f -` {f y} \<inter> space M) =
      (\<Sum>z\<in>g ` space M. if \<exists>x\<in>space M. f y = f x \<and> z = g x then emeasure M {x \<in> space M. g x = z} else 0)"
      apply (simp add: setsum_cases)
      apply (subst setsum_emeasure)
      apply (auto simp: disjoint_family_on_def eq)
      done
  qed
  also have "\<dots> = (\<Sum>y\<in>f`space M. (\<Sum>z\<in>g`space M. 
      if \<exists>x\<in>space M. y = f x \<and> z = g x then y * emeasure M {x\<in>space M. g x = z} else 0))"
    by (auto intro!: setsum_cong simp: setsum_ereal_right_distrib emeasure_nonneg)
  also have "\<dots> = ?r"
    by (subst setsum_commute)
       (auto intro!: setsum_cong simp: setsum_cases scaleR_setsum_right[symmetric] eq)
  finally show "integral\<^sup>S M f = ?r" .
qed

lemma simple_integral_add[simp]:
  assumes f: "simple_function M f" and "\<And>x. 0 \<le> f x" and g: "simple_function M g" and "\<And>x. 0 \<le> g x"
  shows "(\<integral>\<^sup>Sx. f x + g x \<partial>M) = integral\<^sup>S M f + integral\<^sup>S M g"
proof -
  have "(\<integral>\<^sup>Sx. f x + g x \<partial>M) =
    (\<Sum>y\<in>(\<lambda>x. (f x, g x))`space M. (fst y + snd y) * emeasure M {x\<in>space M. (f x, g x) = y})"
    by (intro simple_function_partition) (auto intro: f g)
  also have "\<dots> = (\<Sum>y\<in>(\<lambda>x. (f x, g x))`space M. fst y * emeasure M {x\<in>space M. (f x, g x) = y}) +
    (\<Sum>y\<in>(\<lambda>x. (f x, g x))`space M. snd y * emeasure M {x\<in>space M. (f x, g x) = y})"
    using assms(2,4) by (auto intro!: setsum_cong ereal_left_distrib simp: setsum_addf[symmetric])
  also have "(\<Sum>y\<in>(\<lambda>x. (f x, g x))`space M. fst y * emeasure M {x\<in>space M. (f x, g x) = y}) = (\<integral>\<^sup>Sx. f x \<partial>M)"
    by (intro simple_function_partition[symmetric]) (auto intro: f g)
  also have "(\<Sum>y\<in>(\<lambda>x. (f x, g x))`space M. snd y * emeasure M {x\<in>space M. (f x, g x) = y}) = (\<integral>\<^sup>Sx. g x \<partial>M)"
    by (intro simple_function_partition[symmetric]) (auto intro: f g)
  finally show ?thesis .
qed

lemma simple_integral_setsum[simp]:
  assumes "\<And>i x. i \<in> P \<Longrightarrow> 0 \<le> f i x"
  assumes "\<And>i. i \<in> P \<Longrightarrow> simple_function M (f i)"
  shows "(\<integral>\<^sup>Sx. (\<Sum>i\<in>P. f i x) \<partial>M) = (\<Sum>i\<in>P. integral\<^sup>S M (f i))"
proof cases
  assume "finite P"
  from this assms show ?thesis
    by induct (auto simp: simple_function_setsum simple_integral_add setsum_nonneg)
qed auto

lemma simple_integral_mult[simp]:
  assumes f: "simple_function M f" "\<And>x. 0 \<le> f x"
  shows "(\<integral>\<^sup>Sx. c * f x \<partial>M) = c * integral\<^sup>S M f"
proof -
  have "(\<integral>\<^sup>Sx. c * f x \<partial>M) = (\<Sum>y\<in>f ` space M. (c * y) * emeasure M {x\<in>space M. f x = y})"
    using f by (intro simple_function_partition) auto
  also have "\<dots> = c * integral\<^sup>S M f"
    using f unfolding simple_integral_def
    by (subst setsum_ereal_right_distrib) (auto simp: emeasure_nonneg mult_assoc Int_def conj_commute)
  finally show ?thesis .
qed

lemma simple_integral_mono_AE:
  assumes f[measurable]: "simple_function M f" and g[measurable]: "simple_function M g"
  and mono: "AE x in M. f x \<le> g x"
  shows "integral\<^sup>S M f \<le> integral\<^sup>S M g"
proof -
  let ?\<mu> = "\<lambda>P. emeasure M {x\<in>space M. P x}"
  have "integral\<^sup>S M f = (\<Sum>y\<in>(\<lambda>x. (f x, g x))`space M. fst y * ?\<mu> (\<lambda>x. (f x, g x) = y))"
    using f g by (intro simple_function_partition) auto
  also have "\<dots> \<le> (\<Sum>y\<in>(\<lambda>x. (f x, g x))`space M. snd y * ?\<mu> (\<lambda>x. (f x, g x) = y))"
  proof (clarsimp intro!: setsum_mono)
    fix x assume "x \<in> space M"
    let ?M = "?\<mu> (\<lambda>y. f y = f x \<and> g y = g x)"
    show "f x * ?M \<le> g x * ?M"
    proof cases
      assume "?M \<noteq> 0"
      then have "0 < ?M"
        by (simp add: less_le emeasure_nonneg)
      also have "\<dots> \<le> ?\<mu> (\<lambda>y. f x \<le> g x)"
        using mono by (intro emeasure_mono_AE) auto
      finally have "\<not> \<not> f x \<le> g x"
        by (intro notI) auto
      then show ?thesis
        by (intro ereal_mult_right_mono) auto
    qed simp
  qed
  also have "\<dots> = integral\<^sup>S M g"
    using f g by (intro simple_function_partition[symmetric]) auto
  finally show ?thesis .
qed

lemma simple_integral_mono:
  assumes "simple_function M f" and "simple_function M g"
  and mono: "\<And> x. x \<in> space M \<Longrightarrow> f x \<le> g x"
  shows "integral\<^sup>S M f \<le> integral\<^sup>S M g"
  using assms by (intro simple_integral_mono_AE) auto

lemma simple_integral_cong_AE:
  assumes "simple_function M f" and "simple_function M g"
  and "AE x in M. f x = g x"
  shows "integral\<^sup>S M f = integral\<^sup>S M g"
  using assms by (auto simp: eq_iff intro!: simple_integral_mono_AE)

lemma simple_integral_cong':
  assumes sf: "simple_function M f" "simple_function M g"
  and mea: "(emeasure M) {x\<in>space M. f x \<noteq> g x} = 0"
  shows "integral\<^sup>S M f = integral\<^sup>S M g"
proof (intro simple_integral_cong_AE sf AE_I)
  show "(emeasure M) {x\<in>space M. f x \<noteq> g x} = 0" by fact
  show "{x \<in> space M. f x \<noteq> g x} \<in> sets M"
    using sf[THEN borel_measurable_simple_function] by auto
qed simp

lemma simple_integral_indicator:
  assumes A: "A \<in> sets M"
  assumes f: "simple_function M f"
  shows "(\<integral>\<^sup>Sx. f x * indicator A x \<partial>M) =
    (\<Sum>x \<in> f ` space M. x * emeasure M (f -` {x} \<inter> space M \<inter> A))"
proof -
  have eq: "(\<lambda>x. (f x, indicator A x)) ` space M \<inter> {x. snd x = 1} = (\<lambda>x. (f x, 1::ereal))`A"
    using A[THEN sets.sets_into_space] by (auto simp: indicator_def image_iff split: split_if_asm)
  have eq2: "\<And>x. f x \<notin> f ` A \<Longrightarrow> f -` {f x} \<inter> space M \<inter> A = {}"
    by (auto simp: image_iff)

  have "(\<integral>\<^sup>Sx. f x * indicator A x \<partial>M) =
    (\<Sum>y\<in>(\<lambda>x. (f x, indicator A x))`space M. (fst y * snd y) * emeasure M {x\<in>space M. (f x, indicator A x) = y})"
    using assms by (intro simple_function_partition) auto
  also have "\<dots> = (\<Sum>y\<in>(\<lambda>x. (f x, indicator A x::ereal))`space M.
    if snd y = 1 then fst y * emeasure M (f -` {fst y} \<inter> space M \<inter> A) else 0)"
    by (auto simp: indicator_def split: split_if_asm intro!: arg_cong2[where f="op *"] arg_cong2[where f=emeasure] setsum_cong)
  also have "\<dots> = (\<Sum>y\<in>(\<lambda>x. (f x, 1::ereal))`A. fst y * emeasure M (f -` {fst y} \<inter> space M \<inter> A))"
    using assms by (subst setsum_cases) (auto intro!: simple_functionD(1) simp: eq)
  also have "\<dots> = (\<Sum>y\<in>fst`(\<lambda>x. (f x, 1::ereal))`A. y * emeasure M (f -` {y} \<inter> space M \<inter> A))"
    by (subst setsum_reindex[where f=fst]) (auto simp: inj_on_def)
  also have "\<dots> = (\<Sum>x \<in> f ` space M. x * emeasure M (f -` {x} \<inter> space M \<inter> A))"
    using A[THEN sets.sets_into_space]
    by (intro setsum_mono_zero_cong_left simple_functionD f) (auto simp: image_comp comp_def eq2)
  finally show ?thesis .
qed

lemma simple_integral_indicator_only[simp]:
  assumes "A \<in> sets M"
  shows "integral\<^sup>S M (indicator A) = emeasure M A"
  using simple_integral_indicator[OF assms, of "\<lambda>x. 1"] sets.sets_into_space[OF assms]
  by (simp_all add: image_constant_conv Int_absorb1 split: split_if_asm)

lemma simple_integral_null_set:
  assumes "simple_function M u" "\<And>x. 0 \<le> u x" and "N \<in> null_sets M"
  shows "(\<integral>\<^sup>Sx. u x * indicator N x \<partial>M) = 0"
proof -
  have "AE x in M. indicator N x = (0 :: ereal)"
    using `N \<in> null_sets M` by (auto simp: indicator_def intro!: AE_I[of _ _ N])
  then have "(\<integral>\<^sup>Sx. u x * indicator N x \<partial>M) = (\<integral>\<^sup>Sx. 0 \<partial>M)"
    using assms apply (intro simple_integral_cong_AE) by auto
  then show ?thesis by simp
qed

lemma simple_integral_cong_AE_mult_indicator:
  assumes sf: "simple_function M f" and eq: "AE x in M. x \<in> S" and "S \<in> sets M"
  shows "integral\<^sup>S M f = (\<integral>\<^sup>Sx. f x * indicator S x \<partial>M)"
  using assms by (intro simple_integral_cong_AE) auto

lemma simple_integral_cmult_indicator:
  assumes A: "A \<in> sets M"
  shows "(\<integral>\<^sup>Sx. c * indicator A x \<partial>M) = c * emeasure M A"
  using simple_integral_mult[OF simple_function_indicator[OF A]]
  unfolding simple_integral_indicator_only[OF A] by simp

lemma simple_integral_nonneg:
  assumes f: "simple_function M f" and ae: "AE x in M. 0 \<le> f x"
  shows "0 \<le> integral\<^sup>S M f"
proof -
  have "integral\<^sup>S M (\<lambda>x. 0) \<le> integral\<^sup>S M f"
    using simple_integral_mono_AE[OF _ f ae] by auto
  then show ?thesis by simp
qed

subsection {* Integral on nonnegative functions *}

definition nn_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> ereal) \<Rightarrow> ereal" ("integral\<^sup>N") where
  "integral\<^sup>N M f = (SUP g : {g. simple_function M g \<and> g \<le> max 0 \<circ> f}. integral\<^sup>S M g)"

syntax
  "_nn_integral" :: "pttrn \<Rightarrow> ereal \<Rightarrow> 'a measure \<Rightarrow> ereal" ("\<integral>\<^sup>+ _. _ \<partial>_" [60,61] 110)

translations
  "\<integral>\<^sup>+x. f \<partial>M" == "CONST nn_integral M (\<lambda>x. f)"

lemma nn_integral_nonneg: "0 \<le> integral\<^sup>N M f"
  by (auto intro!: SUP_upper2[of "\<lambda>x. 0"] simp: nn_integral_def le_fun_def)

lemma nn_integral_not_MInfty[simp]: "integral\<^sup>N M f \<noteq> -\<infinity>"
  using nn_integral_nonneg[of M f] by auto

lemma nn_integral_def_finite:
  "integral\<^sup>N M f = (SUP g : {g. simple_function M g \<and> g \<le> max 0 \<circ> f \<and> range g \<subseteq> {0 ..< \<infinity>}}. integral\<^sup>S M g)"
    (is "_ = SUPREMUM ?A ?f")
  unfolding nn_integral_def
proof (safe intro!: antisym SUP_least)
  fix g assume g: "simple_function M g" "g \<le> max 0 \<circ> f"
  let ?G = "{x \<in> space M. \<not> g x \<noteq> \<infinity>}"
  note gM = g(1)[THEN borel_measurable_simple_function]
  have \<mu>_G_pos: "0 \<le> (emeasure M) ?G" using gM by auto
  let ?g = "\<lambda>y x. if g x = \<infinity> then y else max 0 (g x)"
  from g gM have g_in_A: "\<And>y. 0 \<le> y \<Longrightarrow> y \<noteq> \<infinity> \<Longrightarrow> ?g y \<in> ?A"
    apply (safe intro!: simple_function_max simple_function_If)
    apply (force simp: max_def le_fun_def split: split_if_asm)+
    done
  show "integral\<^sup>S M g \<le> SUPREMUM ?A ?f"
  proof cases
    have g0: "?g 0 \<in> ?A" by (intro g_in_A) auto
    assume "(emeasure M) ?G = 0"
    with gM have "AE x in M. x \<notin> ?G"
      by (auto simp add: AE_iff_null intro!: null_setsI)
    with gM g show ?thesis
      by (intro SUP_upper2[OF g0] simple_integral_mono_AE)
         (auto simp: max_def intro!: simple_function_If)
  next
    assume \<mu>_G: "(emeasure M) ?G \<noteq> 0"
    have "SUPREMUM ?A (integral\<^sup>S M) = \<infinity>"
    proof (intro SUP_PInfty)
      fix n :: nat
      let ?y = "ereal (real n) / (if (emeasure M) ?G = \<infinity> then 1 else (emeasure M) ?G)"
      have "0 \<le> ?y" "?y \<noteq> \<infinity>" using \<mu>_G \<mu>_G_pos by (auto simp: ereal_divide_eq)
      then have "?g ?y \<in> ?A" by (rule g_in_A)
      have "real n \<le> ?y * (emeasure M) ?G"
        using \<mu>_G \<mu>_G_pos by (cases "(emeasure M) ?G") (auto simp: field_simps)
      also have "\<dots> = (\<integral>\<^sup>Sx. ?y * indicator ?G x \<partial>M)"
        using `0 \<le> ?y` `?g ?y \<in> ?A` gM
        by (subst simple_integral_cmult_indicator) auto
      also have "\<dots> \<le> integral\<^sup>S M (?g ?y)" using `?g ?y \<in> ?A` gM
        by (intro simple_integral_mono) auto
      finally show "\<exists>i\<in>?A. real n \<le> integral\<^sup>S M i"
        using `?g ?y \<in> ?A` by blast
    qed
    then show ?thesis by simp
  qed
qed (auto intro: SUP_upper)

lemma nn_integral_mono_AE:
  assumes ae: "AE x in M. u x \<le> v x" shows "integral\<^sup>N M u \<le> integral\<^sup>N M v"
  unfolding nn_integral_def
proof (safe intro!: SUP_mono)
  fix n assume n: "simple_function M n" "n \<le> max 0 \<circ> u"
  from ae[THEN AE_E] guess N . note N = this
  then have ae_N: "AE x in M. x \<notin> N" by (auto intro: AE_not_in)
  let ?n = "\<lambda>x. n x * indicator (space M - N) x"
  have "AE x in M. n x \<le> ?n x" "simple_function M ?n"
    using n N ae_N by auto
  moreover
  { fix x have "?n x \<le> max 0 (v x)"
    proof cases
      assume x: "x \<in> space M - N"
      with N have "u x \<le> v x" by auto
      with n(2)[THEN le_funD, of x] x show ?thesis
        by (auto simp: max_def split: split_if_asm)
    qed simp }
  then have "?n \<le> max 0 \<circ> v" by (auto simp: le_funI)
  moreover have "integral\<^sup>S M n \<le> integral\<^sup>S M ?n"
    using ae_N N n by (auto intro!: simple_integral_mono_AE)
  ultimately show "\<exists>m\<in>{g. simple_function M g \<and> g \<le> max 0 \<circ> v}. integral\<^sup>S M n \<le> integral\<^sup>S M m"
    by force
qed

lemma nn_integral_mono:
  "(\<And>x. x \<in> space M \<Longrightarrow> u x \<le> v x) \<Longrightarrow> integral\<^sup>N M u \<le> integral\<^sup>N M v"
  by (auto intro: nn_integral_mono_AE)

lemma nn_integral_cong_AE:
  "AE x in M. u x = v x \<Longrightarrow> integral\<^sup>N M u = integral\<^sup>N M v"
  by (auto simp: eq_iff intro!: nn_integral_mono_AE)

lemma nn_integral_cong:
  "(\<And>x. x \<in> space M \<Longrightarrow> u x = v x) \<Longrightarrow> integral\<^sup>N M u = integral\<^sup>N M v"
  by (auto intro: nn_integral_cong_AE)

lemma nn_integral_cong_strong:
  "M = N \<Longrightarrow> (\<And>x. x \<in> space M \<Longrightarrow> u x = v x) \<Longrightarrow> integral\<^sup>N M u = integral\<^sup>N N v"
  by (auto intro: nn_integral_cong)

lemma nn_integral_eq_simple_integral:
  assumes f: "simple_function M f" "\<And>x. 0 \<le> f x" shows "integral\<^sup>N M f = integral\<^sup>S M f"
proof -
  let ?f = "\<lambda>x. f x * indicator (space M) x"
  have f': "simple_function M ?f" using f by auto
  with f(2) have [simp]: "max 0 \<circ> ?f = ?f"
    by (auto simp: fun_eq_iff max_def split: split_indicator)
  have "integral\<^sup>N M ?f \<le> integral\<^sup>S M ?f" using f'
    by (force intro!: SUP_least simple_integral_mono simp: le_fun_def nn_integral_def)
  moreover have "integral\<^sup>S M ?f \<le> integral\<^sup>N M ?f"
    unfolding nn_integral_def
    using f' by (auto intro!: SUP_upper)
  ultimately show ?thesis
    by (simp cong: nn_integral_cong simple_integral_cong)
qed

lemma nn_integral_eq_simple_integral_AE:
  assumes f: "simple_function M f" "AE x in M. 0 \<le> f x" shows "integral\<^sup>N M f = integral\<^sup>S M f"
proof -
  have "AE x in M. f x = max 0 (f x)" using f by (auto split: split_max)
  with f have "integral\<^sup>N M f = integral\<^sup>S M (\<lambda>x. max 0 (f x))"
    by (simp cong: nn_integral_cong_AE simple_integral_cong_AE
             add: nn_integral_eq_simple_integral)
  with assms show ?thesis
    by (auto intro!: simple_integral_cong_AE split: split_max)
qed

lemma nn_integral_SUP_approx:
  assumes f: "incseq f" "\<And>i. f i \<in> borel_measurable M" "\<And>i x. 0 \<le> f i x"
  and u: "simple_function M u" "u \<le> (SUP i. f i)" "u`space M \<subseteq> {0..<\<infinity>}"
  shows "integral\<^sup>S M u \<le> (SUP i. integral\<^sup>N M (f i))" (is "_ \<le> ?S")
proof (rule ereal_le_mult_one_interval)
  have "0 \<le> (SUP i. integral\<^sup>N M (f i))"
    using f(3) by (auto intro!: SUP_upper2 nn_integral_nonneg)
  then show "(SUP i. integral\<^sup>N M (f i)) \<noteq> -\<infinity>" by auto
  have u_range: "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> u x \<and> u x \<noteq> \<infinity>"
    using u(3) by auto
  fix a :: ereal assume "0 < a" "a < 1"
  hence "a \<noteq> 0" by auto
  let ?B = "\<lambda>i. {x \<in> space M. a * u x \<le> f i x}"
  have B: "\<And>i. ?B i \<in> sets M"
    using f `simple_function M u`[THEN borel_measurable_simple_function] by auto

  let ?uB = "\<lambda>i x. u x * indicator (?B i) x"

  { fix i have "?B i \<subseteq> ?B (Suc i)"
    proof safe
      fix i x assume "a * u x \<le> f i x"
      also have "\<dots> \<le> f (Suc i) x"
        using `incseq f`[THEN incseq_SucD] unfolding le_fun_def by auto
      finally show "a * u x \<le> f (Suc i) x" .
    qed }
  note B_mono = this

  note B_u = sets.Int[OF u(1)[THEN simple_functionD(2)] B]

  let ?B' = "\<lambda>i n. (u -` {i} \<inter> space M) \<inter> ?B n"
  have measure_conv: "\<And>i. (emeasure M) (u -` {i} \<inter> space M) = (SUP n. (emeasure M) (?B' i n))"
  proof -
    fix i
    have 1: "range (?B' i) \<subseteq> sets M" using B_u by auto
    have 2: "incseq (?B' i)" using B_mono by (auto intro!: incseq_SucI)
    have "(\<Union>n. ?B' i n) = u -` {i} \<inter> space M"
    proof safe
      fix x i assume x: "x \<in> space M"
      show "x \<in> (\<Union>i. ?B' (u x) i)"
      proof cases
        assume "u x = 0" thus ?thesis using `x \<in> space M` f(3) by simp
      next
        assume "u x \<noteq> 0"
        with `a < 1` u_range[OF `x \<in> space M`]
        have "a * u x < 1 * u x"
          by (intro ereal_mult_strict_right_mono) (auto simp: image_iff)
        also have "\<dots> \<le> (SUP i. f i x)" using u(2) by (auto simp: le_fun_def)
        finally obtain i where "a * u x < f i x" unfolding SUP_def
          by (auto simp add: less_SUP_iff)
        hence "a * u x \<le> f i x" by auto
        thus ?thesis using `x \<in> space M` by auto
      qed
    qed
    then show "?thesis i" using SUP_emeasure_incseq[OF 1 2] by simp
  qed

  have "integral\<^sup>S M u = (SUP i. integral\<^sup>S M (?uB i))"
    unfolding simple_integral_indicator[OF B `simple_function M u`]
  proof (subst SUP_ereal_setsum, safe)
    fix x n assume "x \<in> space M"
    with u_range show "incseq (\<lambda>i. u x * (emeasure M) (?B' (u x) i))" "\<And>i. 0 \<le> u x * (emeasure M) (?B' (u x) i)"
      using B_mono B_u by (auto intro!: emeasure_mono ereal_mult_left_mono incseq_SucI simp: ereal_zero_le_0_iff)
  next
    show "integral\<^sup>S M u = (\<Sum>i\<in>u ` space M. SUP n. i * (emeasure M) (?B' i n))"
      using measure_conv u_range B_u unfolding simple_integral_def
      by (auto intro!: setsum_cong SUP_ereal_cmult [symmetric])
  qed
  moreover
  have "a * (SUP i. integral\<^sup>S M (?uB i)) \<le> ?S"
    apply (subst SUP_ereal_cmult [symmetric])
  proof (safe intro!: SUP_mono bexI)
    fix i
    have "a * integral\<^sup>S M (?uB i) = (\<integral>\<^sup>Sx. a * ?uB i x \<partial>M)"
      using B `simple_function M u` u_range
      by (subst simple_integral_mult) (auto split: split_indicator)
    also have "\<dots> \<le> integral\<^sup>N M (f i)"
    proof -
      have *: "simple_function M (\<lambda>x. a * ?uB i x)" using B `0 < a` u(1) by auto
      show ?thesis using f(3) * u_range `0 < a`
        by (subst nn_integral_eq_simple_integral[symmetric])
           (auto intro!: nn_integral_mono split: split_indicator)
    qed
    finally show "a * integral\<^sup>S M (?uB i) \<le> integral\<^sup>N M (f i)"
      by auto
  next
    fix i show "0 \<le> \<integral>\<^sup>S x. ?uB i x \<partial>M" using B `0 < a` u(1) u_range
      by (intro simple_integral_nonneg) (auto split: split_indicator)
  qed (insert `0 < a`, auto)
  ultimately show "a * integral\<^sup>S M u \<le> ?S" by simp
qed

lemma incseq_nn_integral:
  assumes "incseq f" shows "incseq (\<lambda>i. integral\<^sup>N M (f i))"
proof -
  have "\<And>i x. f i x \<le> f (Suc i) x"
    using assms by (auto dest!: incseq_SucD simp: le_fun_def)
  then show ?thesis
    by (auto intro!: incseq_SucI nn_integral_mono)
qed

text {* Beppo-Levi monotone convergence theorem *}
lemma nn_integral_monotone_convergence_SUP:
  assumes f: "incseq f" "\<And>i. f i \<in> borel_measurable M" "\<And>i x. 0 \<le> f i x"
  shows "(\<integral>\<^sup>+ x. (SUP i. f i x) \<partial>M) = (SUP i. integral\<^sup>N M (f i))"
proof (rule antisym)
  show "(SUP j. integral\<^sup>N M (f j)) \<le> (\<integral>\<^sup>+ x. (SUP i. f i x) \<partial>M)"
    by (auto intro!: SUP_least SUP_upper nn_integral_mono)
next
  show "(\<integral>\<^sup>+ x. (SUP i. f i x) \<partial>M) \<le> (SUP j. integral\<^sup>N M (f j))"
    unfolding nn_integral_def_finite[of _ "\<lambda>x. SUP i. f i x"]
  proof (safe intro!: SUP_least)
    fix g assume g: "simple_function M g"
      and *: "g \<le> max 0 \<circ> (\<lambda>x. SUP i. f i x)" "range g \<subseteq> {0..<\<infinity>}"
    then have "\<And>x. 0 \<le> (SUP i. f i x)" and g': "g`space M \<subseteq> {0..<\<infinity>}"
      using f by (auto intro!: SUP_upper2)
    with * show "integral\<^sup>S M g \<le> (SUP j. integral\<^sup>N M (f j))"
      by (intro  nn_integral_SUP_approx[OF f g _ g'])
         (auto simp: le_fun_def max_def)
  qed
qed

lemma nn_integral_monotone_convergence_SUP_AE:
  assumes f: "\<And>i. AE x in M. f i x \<le> f (Suc i) x \<and> 0 \<le> f i x" "\<And>i. f i \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ x. (SUP i. f i x) \<partial>M) = (SUP i. integral\<^sup>N M (f i))"
proof -
  from f have "AE x in M. \<forall>i. f i x \<le> f (Suc i) x \<and> 0 \<le> f i x"
    by (simp add: AE_all_countable)
  from this[THEN AE_E] guess N . note N = this
  let ?f = "\<lambda>i x. if x \<in> space M - N then f i x else 0"
  have f_eq: "AE x in M. \<forall>i. ?f i x = f i x" using N by (auto intro!: AE_I[of _ _ N])
  then have "(\<integral>\<^sup>+ x. (SUP i. f i x) \<partial>M) = (\<integral>\<^sup>+ x. (SUP i. ?f i x) \<partial>M)"
    by (auto intro!: nn_integral_cong_AE)
  also have "\<dots> = (SUP i. (\<integral>\<^sup>+ x. ?f i x \<partial>M))"
  proof (rule nn_integral_monotone_convergence_SUP)
    show "incseq ?f" using N(1) by (force intro!: incseq_SucI le_funI)
    { fix i show "(\<lambda>x. if x \<in> space M - N then f i x else 0) \<in> borel_measurable M"
        using f N(3) by (intro measurable_If_set) auto
      fix x show "0 \<le> ?f i x"
        using N(1) by auto }
  qed
  also have "\<dots> = (SUP i. (\<integral>\<^sup>+ x. f i x \<partial>M))"
    using f_eq by (force intro!: arg_cong[where f="SUPREMUM UNIV"] nn_integral_cong_AE ext)
  finally show ?thesis .
qed

lemma nn_integral_monotone_convergence_SUP_AE_incseq:
  assumes f: "incseq f" "\<And>i. AE x in M. 0 \<le> f i x" and borel: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<integral>\<^sup>+ x. (SUP i. f i x) \<partial>M) = (SUP i. integral\<^sup>N M (f i))"
  using f[unfolded incseq_Suc_iff le_fun_def]
  by (intro nn_integral_monotone_convergence_SUP_AE[OF _ borel])
     auto

lemma nn_integral_monotone_convergence_simple:
  assumes f: "incseq f" "\<And>i x. 0 \<le> f i x" "\<And>i. simple_function M (f i)"
  shows "(SUP i. integral\<^sup>S M (f i)) = (\<integral>\<^sup>+x. (SUP i. f i x) \<partial>M)"
  using assms unfolding nn_integral_monotone_convergence_SUP[OF f(1)
    f(3)[THEN borel_measurable_simple_function] f(2)]
  by (auto intro!: nn_integral_eq_simple_integral[symmetric] arg_cong[where f="SUPREMUM UNIV"] ext)

lemma nn_integral_max_0:
  "(\<integral>\<^sup>+x. max 0 (f x) \<partial>M) = integral\<^sup>N M f"
  by (simp add: le_fun_def nn_integral_def)

lemma nn_integral_cong_pos:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> f x \<le> 0 \<and> g x \<le> 0 \<or> f x = g x"
  shows "integral\<^sup>N M f = integral\<^sup>N M g"
proof -
  have "integral\<^sup>N M (\<lambda>x. max 0 (f x)) = integral\<^sup>N M (\<lambda>x. max 0 (g x))"
  proof (intro nn_integral_cong)
    fix x assume "x \<in> space M"
    from assms[OF this] show "max 0 (f x) = max 0 (g x)"
      by (auto split: split_max)
  qed
  then show ?thesis by (simp add: nn_integral_max_0)
qed

lemma SUP_simple_integral_sequences:
  assumes f: "incseq f" "\<And>i x. 0 \<le> f i x" "\<And>i. simple_function M (f i)"
  and g: "incseq g" "\<And>i x. 0 \<le> g i x" "\<And>i. simple_function M (g i)"
  and eq: "AE x in M. (SUP i. f i x) = (SUP i. g i x)"
  shows "(SUP i. integral\<^sup>S M (f i)) = (SUP i. integral\<^sup>S M (g i))"
    (is "SUPREMUM _ ?F = SUPREMUM _ ?G")
proof -
  have "(SUP i. integral\<^sup>S M (f i)) = (\<integral>\<^sup>+x. (SUP i. f i x) \<partial>M)"
    using f by (rule nn_integral_monotone_convergence_simple)
  also have "\<dots> = (\<integral>\<^sup>+x. (SUP i. g i x) \<partial>M)"
    unfolding eq[THEN nn_integral_cong_AE] ..
  also have "\<dots> = (SUP i. ?G i)"
    using g by (rule nn_integral_monotone_convergence_simple[symmetric])
  finally show ?thesis by simp
qed

lemma nn_integral_const[simp]:
  "0 \<le> c \<Longrightarrow> (\<integral>\<^sup>+ x. c \<partial>M) = c * (emeasure M) (space M)"
  by (subst nn_integral_eq_simple_integral) auto

lemma nn_integral_linear:
  assumes f: "f \<in> borel_measurable M" "\<And>x. 0 \<le> f x" and "0 \<le> a"
  and g: "g \<in> borel_measurable M" "\<And>x. 0 \<le> g x"
  shows "(\<integral>\<^sup>+ x. a * f x + g x \<partial>M) = a * integral\<^sup>N M f + integral\<^sup>N M g"
    (is "integral\<^sup>N M ?L = _")
proof -
  from borel_measurable_implies_simple_function_sequence'[OF f(1)] guess u .
  note u = nn_integral_monotone_convergence_simple[OF this(2,5,1)] this
  from borel_measurable_implies_simple_function_sequence'[OF g(1)] guess v .
  note v = nn_integral_monotone_convergence_simple[OF this(2,5,1)] this
  let ?L' = "\<lambda>i x. a * u i x + v i x"

  have "?L \<in> borel_measurable M" using assms by auto
  from borel_measurable_implies_simple_function_sequence'[OF this] guess l .
  note l = nn_integral_monotone_convergence_simple[OF this(2,5,1)] this

  have inc: "incseq (\<lambda>i. a * integral\<^sup>S M (u i))" "incseq (\<lambda>i. integral\<^sup>S M (v i))"
    using u v `0 \<le> a`
    by (auto simp: incseq_Suc_iff le_fun_def
             intro!: add_mono ereal_mult_left_mono simple_integral_mono)
  have pos: "\<And>i. 0 \<le> integral\<^sup>S M (u i)" "\<And>i. 0 \<le> integral\<^sup>S M (v i)" "\<And>i. 0 \<le> a * integral\<^sup>S M (u i)"
    using u v `0 \<le> a` by (auto simp: simple_integral_nonneg)
  { fix i from pos[of i] have "a * integral\<^sup>S M (u i) \<noteq> -\<infinity>" "integral\<^sup>S M (v i) \<noteq> -\<infinity>"
      by (auto split: split_if_asm) }
  note not_MInf = this

  have l': "(SUP i. integral\<^sup>S M (l i)) = (SUP i. integral\<^sup>S M (?L' i))"
  proof (rule SUP_simple_integral_sequences[OF l(3,6,2)])
    show "incseq ?L'" "\<And>i x. 0 \<le> ?L' i x" "\<And>i. simple_function M (?L' i)"
      using u v  `0 \<le> a` unfolding incseq_Suc_iff le_fun_def
      by (auto intro!: add_mono ereal_mult_left_mono)
    { fix x
      { fix i have "a * u i x \<noteq> -\<infinity>" "v i x \<noteq> -\<infinity>" "u i x \<noteq> -\<infinity>" using `0 \<le> a` u(6)[of i x] v(6)[of i x]
          by auto }
      then have "(SUP i. a * u i x + v i x) = a * (SUP i. u i x) + (SUP i. v i x)"
        using `0 \<le> a` u(3) v(3) u(6)[of _ x] v(6)[of _ x]
        by (subst SUP_ereal_cmult [symmetric, OF u(6) `0 \<le> a`])
           (auto intro!: SUP_ereal_add
                 simp: incseq_Suc_iff le_fun_def add_mono ereal_mult_left_mono) }
    then show "AE x in M. (SUP i. l i x) = (SUP i. ?L' i x)"
      unfolding l(5) using `0 \<le> a` u(5) v(5) l(5) f(2) g(2)
      by (intro AE_I2) (auto split: split_max)
  qed
  also have "\<dots> = (SUP i. a * integral\<^sup>S M (u i) + integral\<^sup>S M (v i))"
    using u(2, 6) v(2, 6) `0 \<le> a` by (auto intro!: arg_cong[where f="SUPREMUM UNIV"] ext)
  finally have "(\<integral>\<^sup>+ x. max 0 (a * f x + g x) \<partial>M) = a * (\<integral>\<^sup>+x. max 0 (f x) \<partial>M) + (\<integral>\<^sup>+x. max 0 (g x) \<partial>M)"
    unfolding l(5)[symmetric] u(5)[symmetric] v(5)[symmetric]
    unfolding l(1)[symmetric] u(1)[symmetric] v(1)[symmetric]
    apply (subst SUP_ereal_cmult [symmetric, OF pos(1) `0 \<le> a`])
    apply (subst SUP_ereal_add [symmetric, OF inc not_MInf]) .
  then show ?thesis by (simp add: nn_integral_max_0)
qed

lemma nn_integral_cmult:
  assumes f: "f \<in> borel_measurable M" "0 \<le> c"
  shows "(\<integral>\<^sup>+ x. c * f x \<partial>M) = c * integral\<^sup>N M f"
proof -
  have [simp]: "\<And>x. c * max 0 (f x) = max 0 (c * f x)" using `0 \<le> c`
    by (auto split: split_max simp: ereal_zero_le_0_iff)
  have "(\<integral>\<^sup>+ x. c * f x \<partial>M) = (\<integral>\<^sup>+ x. c * max 0 (f x) \<partial>M)"
    by (simp add: nn_integral_max_0)
  then show ?thesis
    using nn_integral_linear[OF _ _ `0 \<le> c`, of "\<lambda>x. max 0 (f x)" _ "\<lambda>x. 0"] f
    by (auto simp: nn_integral_max_0)
qed

lemma nn_integral_multc:
  assumes "f \<in> borel_measurable M" "0 \<le> c"
  shows "(\<integral>\<^sup>+ x. f x * c \<partial>M) = integral\<^sup>N M f * c"
  unfolding mult_commute[of _ c] nn_integral_cmult[OF assms] by simp

lemma nn_integral_indicator[simp]:
  "A \<in> sets M \<Longrightarrow> (\<integral>\<^sup>+ x. indicator A x\<partial>M) = (emeasure M) A"
  by (subst nn_integral_eq_simple_integral)
     (auto simp: simple_integral_indicator)

lemma nn_integral_cmult_indicator:
  "0 \<le> c \<Longrightarrow> A \<in> sets M \<Longrightarrow> (\<integral>\<^sup>+ x. c * indicator A x \<partial>M) = c * (emeasure M) A"
  by (subst nn_integral_eq_simple_integral)
     (auto simp: simple_function_indicator simple_integral_indicator)

lemma nn_integral_indicator':
  assumes [measurable]: "A \<inter> space M \<in> sets M"
  shows "(\<integral>\<^sup>+ x. indicator A x \<partial>M) = emeasure M (A \<inter> space M)"
proof -
  have "(\<integral>\<^sup>+ x. indicator A x \<partial>M) = (\<integral>\<^sup>+ x. indicator (A \<inter> space M) x \<partial>M)"
    by (intro nn_integral_cong) (simp split: split_indicator)
  also have "\<dots> = emeasure M (A \<inter> space M)"
    by simp
  finally show ?thesis .
qed

lemma nn_integral_add:
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
  and g: "g \<in> borel_measurable M" "AE x in M. 0 \<le> g x"
  shows "(\<integral>\<^sup>+ x. f x + g x \<partial>M) = integral\<^sup>N M f + integral\<^sup>N M g"
proof -
  have ae: "AE x in M. max 0 (f x) + max 0 (g x) = max 0 (f x + g x)"
    using assms by (auto split: split_max)
  have "(\<integral>\<^sup>+ x. f x + g x \<partial>M) = (\<integral>\<^sup>+ x. max 0 (f x + g x) \<partial>M)"
    by (simp add: nn_integral_max_0)
  also have "\<dots> = (\<integral>\<^sup>+ x. max 0 (f x) + max 0 (g x) \<partial>M)"
    unfolding ae[THEN nn_integral_cong_AE] ..
  also have "\<dots> = (\<integral>\<^sup>+ x. max 0 (f x) \<partial>M) + (\<integral>\<^sup>+ x. max 0 (g x) \<partial>M)"
    using nn_integral_linear[of "\<lambda>x. max 0 (f x)" _ 1 "\<lambda>x. max 0 (g x)"] f g
    by auto
  finally show ?thesis
    by (simp add: nn_integral_max_0)
qed

lemma nn_integral_setsum:
  assumes "\<And>i. i\<in>P \<Longrightarrow> f i \<in> borel_measurable M" "\<And>i. i\<in>P \<Longrightarrow> AE x in M. 0 \<le> f i x"
  shows "(\<integral>\<^sup>+ x. (\<Sum>i\<in>P. f i x) \<partial>M) = (\<Sum>i\<in>P. integral\<^sup>N M (f i))"
proof cases
  assume f: "finite P"
  from assms have "AE x in M. \<forall>i\<in>P. 0 \<le> f i x" unfolding AE_finite_all[OF f] by auto
  from f this assms(1) show ?thesis
  proof induct
    case (insert i P)
    then have "f i \<in> borel_measurable M" "AE x in M. 0 \<le> f i x"
      "(\<lambda>x. \<Sum>i\<in>P. f i x) \<in> borel_measurable M" "AE x in M. 0 \<le> (\<Sum>i\<in>P. f i x)"
      by (auto intro!: setsum_nonneg)
    from nn_integral_add[OF this]
    show ?case using insert by auto
  qed simp
qed simp

lemma nn_integral_Markov_inequality:
  assumes u: "u \<in> borel_measurable M" "AE x in M. 0 \<le> u x" and "A \<in> sets M" and c: "0 \<le> c"
  shows "(emeasure M) ({x\<in>space M. 1 \<le> c * u x} \<inter> A) \<le> c * (\<integral>\<^sup>+ x. u x * indicator A x \<partial>M)"
    (is "(emeasure M) ?A \<le> _ * ?PI")
proof -
  have "?A \<in> sets M"
    using `A \<in> sets M` u by auto
  hence "(emeasure M) ?A = (\<integral>\<^sup>+ x. indicator ?A x \<partial>M)"
    using nn_integral_indicator by simp
  also have "\<dots> \<le> (\<integral>\<^sup>+ x. c * (u x * indicator A x) \<partial>M)" using u c
    by (auto intro!: nn_integral_mono_AE
      simp: indicator_def ereal_zero_le_0_iff)
  also have "\<dots> = c * (\<integral>\<^sup>+ x. u x * indicator A x \<partial>M)"
    using assms
    by (auto intro!: nn_integral_cmult simp: ereal_zero_le_0_iff)
  finally show ?thesis .
qed

lemma nn_integral_noteq_infinite:
  assumes g: "g \<in> borel_measurable M" "AE x in M. 0 \<le> g x"
  and "integral\<^sup>N M g \<noteq> \<infinity>"
  shows "AE x in M. g x \<noteq> \<infinity>"
proof (rule ccontr)
  assume c: "\<not> (AE x in M. g x \<noteq> \<infinity>)"
  have "(emeasure M) {x\<in>space M. g x = \<infinity>} \<noteq> 0"
    using c g by (auto simp add: AE_iff_null)
  moreover have "0 \<le> (emeasure M) {x\<in>space M. g x = \<infinity>}" using g by (auto intro: measurable_sets)
  ultimately have "0 < (emeasure M) {x\<in>space M. g x = \<infinity>}" by auto
  then have "\<infinity> = \<infinity> * (emeasure M) {x\<in>space M. g x = \<infinity>}" by auto
  also have "\<dots> \<le> (\<integral>\<^sup>+x. \<infinity> * indicator {x\<in>space M. g x = \<infinity>} x \<partial>M)"
    using g by (subst nn_integral_cmult_indicator) auto
  also have "\<dots> \<le> integral\<^sup>N M g"
    using assms by (auto intro!: nn_integral_mono_AE simp: indicator_def)
  finally show False using `integral\<^sup>N M g \<noteq> \<infinity>` by auto
qed

lemma nn_integral_PInf:
  assumes f: "f \<in> borel_measurable M"
  and not_Inf: "integral\<^sup>N M f \<noteq> \<infinity>"
  shows "(emeasure M) (f -` {\<infinity>} \<inter> space M) = 0"
proof -
  have "\<infinity> * (emeasure M) (f -` {\<infinity>} \<inter> space M) = (\<integral>\<^sup>+ x. \<infinity> * indicator (f -` {\<infinity>} \<inter> space M) x \<partial>M)"
    using f by (subst nn_integral_cmult_indicator) (auto simp: measurable_sets)
  also have "\<dots> \<le> integral\<^sup>N M (\<lambda>x. max 0 (f x))"
    by (auto intro!: nn_integral_mono simp: indicator_def max_def)
  finally have "\<infinity> * (emeasure M) (f -` {\<infinity>} \<inter> space M) \<le> integral\<^sup>N M f"
    by (simp add: nn_integral_max_0)
  moreover have "0 \<le> (emeasure M) (f -` {\<infinity>} \<inter> space M)"
    by (rule emeasure_nonneg)
  ultimately show ?thesis
    using assms by (auto split: split_if_asm)
qed

lemma nn_integral_PInf_AE:
  assumes "f \<in> borel_measurable M" "integral\<^sup>N M f \<noteq> \<infinity>" shows "AE x in M. f x \<noteq> \<infinity>"
proof (rule AE_I)
  show "(emeasure M) (f -` {\<infinity>} \<inter> space M) = 0"
    by (rule nn_integral_PInf[OF assms])
  show "f -` {\<infinity>} \<inter> space M \<in> sets M"
    using assms by (auto intro: borel_measurable_vimage)
qed auto

lemma simple_integral_PInf:
  assumes "simple_function M f" "\<And>x. 0 \<le> f x"
  and "integral\<^sup>S M f \<noteq> \<infinity>"
  shows "(emeasure M) (f -` {\<infinity>} \<inter> space M) = 0"
proof (rule nn_integral_PInf)
  show "f \<in> borel_measurable M" using assms by (auto intro: borel_measurable_simple_function)
  show "integral\<^sup>N M f \<noteq> \<infinity>"
    using assms by (simp add: nn_integral_eq_simple_integral)
qed

lemma nn_integral_diff:
  assumes f: "f \<in> borel_measurable M"
  and g: "g \<in> borel_measurable M" "AE x in M. 0 \<le> g x"
  and fin: "integral\<^sup>N M g \<noteq> \<infinity>"
  and mono: "AE x in M. g x \<le> f x"
  shows "(\<integral>\<^sup>+ x. f x - g x \<partial>M) = integral\<^sup>N M f - integral\<^sup>N M g"
proof -
  have diff: "(\<lambda>x. f x - g x) \<in> borel_measurable M" "AE x in M. 0 \<le> f x - g x"
    using assms by (auto intro: ereal_diff_positive)
  have pos_f: "AE x in M. 0 \<le> f x" using mono g by auto
  { fix a b :: ereal assume "0 \<le> a" "a \<noteq> \<infinity>" "0 \<le> b" "a \<le> b" then have "b - a + a = b"
      by (cases rule: ereal2_cases[of a b]) auto }
  note * = this
  then have "AE x in M. f x = f x - g x + g x"
    using mono nn_integral_noteq_infinite[OF g fin] assms by auto
  then have **: "integral\<^sup>N M f = (\<integral>\<^sup>+x. f x - g x \<partial>M) + integral\<^sup>N M g"
    unfolding nn_integral_add[OF diff g, symmetric]
    by (rule nn_integral_cong_AE)
  show ?thesis unfolding **
    using fin nn_integral_nonneg[of M g]
    by (cases rule: ereal2_cases[of "\<integral>\<^sup>+ x. f x - g x \<partial>M" "integral\<^sup>N M g"]) auto
qed

lemma nn_integral_suminf:
  assumes f: "\<And>i. f i \<in> borel_measurable M" "\<And>i. AE x in M. 0 \<le> f i x"
  shows "(\<integral>\<^sup>+ x. (\<Sum>i. f i x) \<partial>M) = (\<Sum>i. integral\<^sup>N M (f i))"
proof -
  have all_pos: "AE x in M. \<forall>i. 0 \<le> f i x"
    using assms by (auto simp: AE_all_countable)
  have "(\<Sum>i. integral\<^sup>N M (f i)) = (SUP n. \<Sum>i<n. integral\<^sup>N M (f i))"
    using nn_integral_nonneg by (rule suminf_ereal_eq_SUP)
  also have "\<dots> = (SUP n. \<integral>\<^sup>+x. (\<Sum>i<n. f i x) \<partial>M)"
    unfolding nn_integral_setsum[OF f] ..
  also have "\<dots> = \<integral>\<^sup>+x. (SUP n. \<Sum>i<n. f i x) \<partial>M" using f all_pos
    by (intro nn_integral_monotone_convergence_SUP_AE[symmetric])
       (elim AE_mp, auto simp: setsum_nonneg simp del: setsum_lessThan_Suc intro!: AE_I2 setsum_mono3)
  also have "\<dots> = \<integral>\<^sup>+x. (\<Sum>i. f i x) \<partial>M" using all_pos
    by (intro nn_integral_cong_AE) (auto simp: suminf_ereal_eq_SUP)
  finally show ?thesis by simp
qed

lemma nn_integral_mult_bounded_inf:
  assumes f: "f \<in> borel_measurable M" "(\<integral>\<^sup>+x. f x \<partial>M) < \<infinity>"
    and c: "0 \<le> c" "c \<noteq> \<infinity>" and ae: "AE x in M. g x \<le> c * f x"
  shows "(\<integral>\<^sup>+x. g x \<partial>M) < \<infinity>"
proof -
  have "(\<integral>\<^sup>+x. g x \<partial>M) \<le> (\<integral>\<^sup>+x. c * f x \<partial>M)"
    by (intro nn_integral_mono_AE ae)
  also have "(\<integral>\<^sup>+x. c * f x \<partial>M) < \<infinity>"
    using c f by (subst nn_integral_cmult) auto
  finally show ?thesis .
qed

text {* Fatou's lemma: convergence theorem on limes inferior *}

lemma nn_integral_liminf:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes u: "\<And>i. u i \<in> borel_measurable M" "\<And>i. AE x in M. 0 \<le> u i x"
  shows "(\<integral>\<^sup>+ x. liminf (\<lambda>n. u n x) \<partial>M) \<le> liminf (\<lambda>n. integral\<^sup>N M (u n))"
proof -
  have pos: "AE x in M. \<forall>i. 0 \<le> u i x" using u by (auto simp: AE_all_countable)
  have "(\<integral>\<^sup>+ x. liminf (\<lambda>n. u n x) \<partial>M) =
    (SUP n. \<integral>\<^sup>+ x. (INF i:{n..}. u i x) \<partial>M)"
    unfolding liminf_SUP_INF using pos u
    by (intro nn_integral_monotone_convergence_SUP_AE)
       (elim AE_mp, auto intro!: AE_I2 intro: INF_greatest INF_superset_mono)
  also have "\<dots> \<le> liminf (\<lambda>n. integral\<^sup>N M (u n))"
    unfolding liminf_SUP_INF
    by (auto intro!: SUP_mono exI INF_greatest nn_integral_mono INF_lower)
  finally show ?thesis .
qed

lemma le_Limsup:
  "F \<noteq> bot \<Longrightarrow> eventually (\<lambda>x. c \<le> g x) F \<Longrightarrow> c \<le> Limsup F g"
  using Limsup_mono[of "\<lambda>_. c" g F] by (simp add: Limsup_const)

lemma Limsup_le:
  "F \<noteq> bot \<Longrightarrow> eventually (\<lambda>x. f x \<le> c) F \<Longrightarrow> Limsup F f \<le> c"
  using Limsup_mono[of f "\<lambda>_. c" F] by (simp add: Limsup_const)

lemma ereal_mono_minus_cancel:
  fixes a b c :: ereal
  shows "c - a \<le> c - b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c < \<infinity> \<Longrightarrow> b \<le> a"
  by (cases a b c rule: ereal3_cases) auto

lemma nn_integral_limsup:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes [measurable]: "\<And>i. u i \<in> borel_measurable M" "w \<in> borel_measurable M"
  assumes bounds: "\<And>i. AE x in M. 0 \<le> u i x" "\<And>i. AE x in M. u i x \<le> w x" and w: "(\<integral>\<^sup>+x. w x \<partial>M) < \<infinity>"
  shows "limsup (\<lambda>n. integral\<^sup>N M (u n)) \<le> (\<integral>\<^sup>+ x. limsup (\<lambda>n. u n x) \<partial>M)"
proof -
  have bnd: "AE x in M. \<forall>i. 0 \<le> u i x \<and> u i x \<le> w x"
    using bounds by (auto simp: AE_all_countable)

  from bounds[of 0] have w_nonneg: "AE x in M. 0 \<le> w x"
    by auto

  have "(\<integral>\<^sup>+x. w x \<partial>M) - (\<integral>\<^sup>+x. limsup (\<lambda>n. u n x) \<partial>M) = (\<integral>\<^sup>+x. w x - limsup (\<lambda>n. u n x) \<partial>M)"
  proof (intro nn_integral_diff[symmetric])
    show "AE x in M. 0 \<le> limsup (\<lambda>n. u n x)"
      using bnd by (auto intro!: le_Limsup)
    show "AE x in M. limsup (\<lambda>n. u n x) \<le> w x"
      using bnd by (auto intro!: Limsup_le)
    then have "(\<integral>\<^sup>+x. limsup (\<lambda>n. u n x) \<partial>M) < \<infinity>"
      by (intro nn_integral_mult_bounded_inf[OF _ w, of 1]) auto
    then show "(\<integral>\<^sup>+x. limsup (\<lambda>n. u n x) \<partial>M) \<noteq> \<infinity>"
      by simp
  qed auto
  also have "\<dots> = (\<integral>\<^sup>+x. liminf (\<lambda>n. w x - u n x) \<partial>M)"
    using w_nonneg
    by (intro nn_integral_cong_AE, eventually_elim)
       (auto intro!: liminf_ereal_cminus[symmetric])
  also have "\<dots> \<le> liminf (\<lambda>n. \<integral>\<^sup>+x. w x - u n x \<partial>M)"
  proof (rule nn_integral_liminf)
    fix i show "AE x in M. 0 \<le> w x - u i x"
      using bounds[of i] by eventually_elim (auto intro: ereal_diff_positive)
  qed simp
  also have "(\<lambda>n. \<integral>\<^sup>+x. w x - u n x \<partial>M) = (\<lambda>n. (\<integral>\<^sup>+x. w x \<partial>M) - (\<integral>\<^sup>+x. u n x \<partial>M))"
  proof (intro ext nn_integral_diff)
    fix i have "(\<integral>\<^sup>+x. u i x \<partial>M) < \<infinity>"
      using bounds by (intro nn_integral_mult_bounded_inf[OF _ w, of 1]) auto
    then show "(\<integral>\<^sup>+x. u i x \<partial>M) \<noteq> \<infinity>" by simp
  qed (insert bounds, auto)
  also have "liminf (\<lambda>n. (\<integral>\<^sup>+x. w x \<partial>M) - (\<integral>\<^sup>+x. u n x \<partial>M)) = (\<integral>\<^sup>+x. w x \<partial>M) - limsup (\<lambda>n. \<integral>\<^sup>+x. u n x \<partial>M)"
    using w by (intro liminf_ereal_cminus) auto
  finally show ?thesis
    by (rule ereal_mono_minus_cancel) (intro w nn_integral_nonneg)+
qed

lemma nn_integral_LIMSEQ:
  assumes f: "incseq f" "\<And>i. f i \<in> borel_measurable M" "\<And>n x. 0 \<le> f n x"
    and u: "\<And>x. (\<lambda>i. f i x) ----> u x"
  shows "(\<lambda>n. integral\<^sup>N M (f n)) ----> integral\<^sup>N M u"
proof -
  have "(\<lambda>n. integral\<^sup>N M (f n)) ----> (SUP n. integral\<^sup>N M (f n))"
    using f by (intro LIMSEQ_SUP[of "\<lambda>n. integral\<^sup>N M (f n)"] incseq_nn_integral)
  also have "(SUP n. integral\<^sup>N M (f n)) = integral\<^sup>N M (\<lambda>x. SUP n. f n x)"
    using f by (intro nn_integral_monotone_convergence_SUP[symmetric])
  also have "integral\<^sup>N M (\<lambda>x. SUP n. f n x) = integral\<^sup>N M (\<lambda>x. u x)"
    using f by (subst SUP_Lim_ereal[OF _ u]) (auto simp: incseq_def le_fun_def)
  finally show ?thesis .
qed

lemma nn_integral_dominated_convergence:
  assumes [measurable]:
       "\<And>i. u i \<in> borel_measurable M" "u' \<in> borel_measurable M" "w \<in> borel_measurable M"
    and bound: "\<And>j. AE x in M. 0 \<le> u j x" "\<And>j. AE x in M. u j x \<le> w x"
    and w: "(\<integral>\<^sup>+x. w x \<partial>M) < \<infinity>"
    and u': "AE x in M. (\<lambda>i. u i x) ----> u' x"
  shows "(\<lambda>i. (\<integral>\<^sup>+x. u i x \<partial>M)) ----> (\<integral>\<^sup>+x. u' x \<partial>M)"
proof -
  have "limsup (\<lambda>n. integral\<^sup>N M (u n)) \<le> (\<integral>\<^sup>+ x. limsup (\<lambda>n. u n x) \<partial>M)"
    by (intro nn_integral_limsup[OF _ _ bound w]) auto
  moreover have "(\<integral>\<^sup>+ x. limsup (\<lambda>n. u n x) \<partial>M) = (\<integral>\<^sup>+ x. u' x \<partial>M)"
    using u' by (intro nn_integral_cong_AE, eventually_elim) (metis tendsto_iff_Liminf_eq_Limsup sequentially_bot)
  moreover have "(\<integral>\<^sup>+ x. liminf (\<lambda>n. u n x) \<partial>M) = (\<integral>\<^sup>+ x. u' x \<partial>M)"
    using u' by (intro nn_integral_cong_AE, eventually_elim) (metis tendsto_iff_Liminf_eq_Limsup sequentially_bot)
  moreover have "(\<integral>\<^sup>+x. liminf (\<lambda>n. u n x) \<partial>M) \<le> liminf (\<lambda>n. integral\<^sup>N M (u n))"
    by (intro nn_integral_liminf[OF _ bound(1)]) auto
  moreover have "liminf (\<lambda>n. integral\<^sup>N M (u n)) \<le> limsup (\<lambda>n. integral\<^sup>N M (u n))"
    by (intro Liminf_le_Limsup sequentially_bot)
  ultimately show ?thesis
    by (intro Liminf_eq_Limsup) auto
qed

lemma nn_integral_null_set:
  assumes "N \<in> null_sets M" shows "(\<integral>\<^sup>+ x. u x * indicator N x \<partial>M) = 0"
proof -
  have "(\<integral>\<^sup>+ x. u x * indicator N x \<partial>M) = (\<integral>\<^sup>+ x. 0 \<partial>M)"
  proof (intro nn_integral_cong_AE AE_I)
    show "{x \<in> space M. u x * indicator N x \<noteq> 0} \<subseteq> N"
      by (auto simp: indicator_def)
    show "(emeasure M) N = 0" "N \<in> sets M"
      using assms by auto
  qed
  then show ?thesis by simp
qed

lemma nn_integral_0_iff:
  assumes u: "u \<in> borel_measurable M" and pos: "AE x in M. 0 \<le> u x"
  shows "integral\<^sup>N M u = 0 \<longleftrightarrow> emeasure M {x\<in>space M. u x \<noteq> 0} = 0"
    (is "_ \<longleftrightarrow> (emeasure M) ?A = 0")
proof -
  have u_eq: "(\<integral>\<^sup>+ x. u x * indicator ?A x \<partial>M) = integral\<^sup>N M u"
    by (auto intro!: nn_integral_cong simp: indicator_def)
  show ?thesis
  proof
    assume "(emeasure M) ?A = 0"
    with nn_integral_null_set[of ?A M u] u
    show "integral\<^sup>N M u = 0" by (simp add: u_eq null_sets_def)
  next
    { fix r :: ereal and n :: nat assume gt_1: "1 \<le> real n * r"
      then have "0 < real n * r" by (cases r) (auto split: split_if_asm simp: one_ereal_def)
      then have "0 \<le> r" by (auto simp add: ereal_zero_less_0_iff) }
    note gt_1 = this
    assume *: "integral\<^sup>N M u = 0"
    let ?M = "\<lambda>n. {x \<in> space M. 1 \<le> real (n::nat) * u x}"
    have "0 = (SUP n. (emeasure M) (?M n \<inter> ?A))"
    proof -
      { fix n :: nat
        from nn_integral_Markov_inequality[OF u pos, of ?A "ereal (real n)"]
        have "(emeasure M) (?M n \<inter> ?A) \<le> 0" unfolding u_eq * using u by simp
        moreover have "0 \<le> (emeasure M) (?M n \<inter> ?A)" using u by auto
        ultimately have "(emeasure M) (?M n \<inter> ?A) = 0" by auto }
      thus ?thesis by simp
    qed
    also have "\<dots> = (emeasure M) (\<Union>n. ?M n \<inter> ?A)"
    proof (safe intro!: SUP_emeasure_incseq)
      fix n show "?M n \<inter> ?A \<in> sets M"
        using u by (auto intro!: sets.Int)
    next
      show "incseq (\<lambda>n. {x \<in> space M. 1 \<le> real n * u x} \<inter> {x \<in> space M. u x \<noteq> 0})"
      proof (safe intro!: incseq_SucI)
        fix n :: nat and x
        assume *: "1 \<le> real n * u x"
        also from gt_1[OF *] have "real n * u x \<le> real (Suc n) * u x"
          using `0 \<le> u x` by (auto intro!: ereal_mult_right_mono)
        finally show "1 \<le> real (Suc n) * u x" by auto
      qed
    qed
    also have "\<dots> = (emeasure M) {x\<in>space M. 0 < u x}"
    proof (safe intro!: arg_cong[where f="(emeasure M)"] dest!: gt_1)
      fix x assume "0 < u x" and [simp, intro]: "x \<in> space M"
      show "x \<in> (\<Union>n. ?M n \<inter> ?A)"
      proof (cases "u x")
        case (real r) with `0 < u x` have "0 < r" by auto
        obtain j :: nat where "1 / r \<le> real j" using real_arch_simple ..
        hence "1 / r * r \<le> real j * r" unfolding mult_le_cancel_right using `0 < r` by auto
        hence "1 \<le> real j * r" using real `0 < r` by auto
        thus ?thesis using `0 < r` real by (auto simp: one_ereal_def)
      qed (insert `0 < u x`, auto)
    qed auto
    finally have "(emeasure M) {x\<in>space M. 0 < u x} = 0" by simp
    moreover
    from pos have "AE x in M. \<not> (u x < 0)" by auto
    then have "(emeasure M) {x\<in>space M. u x < 0} = 0"
      using AE_iff_null[of M] u by auto
    moreover have "(emeasure M) {x\<in>space M. u x \<noteq> 0} = (emeasure M) {x\<in>space M. u x < 0} + (emeasure M) {x\<in>space M. 0 < u x}"
      using u by (subst plus_emeasure) (auto intro!: arg_cong[where f="emeasure M"])
    ultimately show "(emeasure M) ?A = 0" by simp
  qed
qed

lemma nn_integral_0_iff_AE:
  assumes u: "u \<in> borel_measurable M"
  shows "integral\<^sup>N M u = 0 \<longleftrightarrow> (AE x in M. u x \<le> 0)"
proof -
  have sets: "{x\<in>space M. max 0 (u x) \<noteq> 0} \<in> sets M"
    using u by auto
  from nn_integral_0_iff[of "\<lambda>x. max 0 (u x)"]
  have "integral\<^sup>N M u = 0 \<longleftrightarrow> (AE x in M. max 0 (u x) = 0)"
    unfolding nn_integral_max_0
    using AE_iff_null[OF sets] u by auto
  also have "\<dots> \<longleftrightarrow> (AE x in M. u x \<le> 0)" by (auto split: split_max)
  finally show ?thesis .
qed

lemma AE_iff_nn_integral: 
  "{x\<in>space M. P x} \<in> sets M \<Longrightarrow> (AE x in M. P x) \<longleftrightarrow> integral\<^sup>N M (indicator {x. \<not> P x}) = 0"
  by (subst nn_integral_0_iff_AE) (auto simp: one_ereal_def zero_ereal_def
    sets.sets_Collect_neg indicator_def[abs_def] measurable_If)

lemma nn_integral_const_If:
  "(\<integral>\<^sup>+x. a \<partial>M) = (if 0 \<le> a then a * (emeasure M) (space M) else 0)"
  by (auto intro!: nn_integral_0_iff_AE[THEN iffD2])

lemma nn_integral_subalgebra:
  assumes f: "f \<in> borel_measurable N" "\<And>x. 0 \<le> f x"
  and N: "sets N \<subseteq> sets M" "space N = space M" "\<And>A. A \<in> sets N \<Longrightarrow> emeasure N A = emeasure M A"
  shows "integral\<^sup>N N f = integral\<^sup>N M f"
proof -
  have [simp]: "\<And>f :: 'a \<Rightarrow> ereal. f \<in> borel_measurable N \<Longrightarrow> f \<in> borel_measurable M"
    using N by (auto simp: measurable_def)
  have [simp]: "\<And>P. (AE x in N. P x) \<Longrightarrow> (AE x in M. P x)"
    using N by (auto simp add: eventually_ae_filter null_sets_def)
  have [simp]: "\<And>A. A \<in> sets N \<Longrightarrow> A \<in> sets M"
    using N by auto
  from f show ?thesis
    apply induct
    apply (simp_all add: nn_integral_add nn_integral_cmult nn_integral_monotone_convergence_SUP N)
    apply (auto intro!: nn_integral_cong cong: nn_integral_cong simp: N(2)[symmetric])
    done
qed

lemma nn_integral_nat_function:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "f \<in> measurable M (count_space UNIV)"
  shows "(\<integral>\<^sup>+x. ereal (of_nat (f x)) \<partial>M) = (\<Sum>t. emeasure M {x\<in>space M. t < f x})"
proof -
  def F \<equiv> "\<lambda>i. {x\<in>space M. i < f x}"
  with assms have [measurable]: "\<And>i. F i \<in> sets M"
    by auto

  { fix x assume "x \<in> space M"
    have "(\<lambda>i. if i < f x then 1 else 0) sums (of_nat (f x)::real)"
      using sums_If_finite[of "\<lambda>i. i < f x" "\<lambda>_. 1::real"] by simp
    then have "(\<lambda>i. ereal(if i < f x then 1 else 0)) sums (ereal(of_nat(f x)))"
      unfolding sums_ereal .
    moreover have "\<And>i. ereal (if i < f x then 1 else 0) = indicator (F i) x"
      using `x \<in> space M` by (simp add: one_ereal_def F_def)
    ultimately have "ereal(of_nat(f x)) = (\<Sum>i. indicator (F i) x)"
      by (simp add: sums_iff) }
  then have "(\<integral>\<^sup>+x. ereal (of_nat (f x)) \<partial>M) = (\<integral>\<^sup>+x. (\<Sum>i. indicator (F i) x) \<partial>M)"
    by (simp cong: nn_integral_cong)
  also have "\<dots> = (\<Sum>i. emeasure M (F i))"
    by (simp add: nn_integral_suminf)
  finally show ?thesis
    by (simp add: F_def)
qed

subsection {* Integral under concrete measures *}

subsubsection {* Distributions *}

lemma nn_integral_distr':
  assumes T: "T \<in> measurable M M'"
  and f: "f \<in> borel_measurable (distr M M' T)" "\<And>x. 0 \<le> f x"
  shows "integral\<^sup>N (distr M M' T) f = (\<integral>\<^sup>+ x. f (T x) \<partial>M)"
  using f 
proof induct
  case (cong f g)
  with T show ?case
    apply (subst nn_integral_cong[of _ f g])
    apply simp
    apply (subst nn_integral_cong[of _ "\<lambda>x. f (T x)" "\<lambda>x. g (T x)"])
    apply (simp add: measurable_def Pi_iff)
    apply simp
    done
next
  case (set A)
  then have eq: "\<And>x. x \<in> space M \<Longrightarrow> indicator A (T x) = indicator (T -` A \<inter> space M) x"
    by (auto simp: indicator_def)
  from set T show ?case
    by (subst nn_integral_cong[OF eq])
       (auto simp add: emeasure_distr intro!: nn_integral_indicator[symmetric] measurable_sets)
qed (simp_all add: measurable_compose[OF T] T nn_integral_cmult nn_integral_add
                   nn_integral_monotone_convergence_SUP le_fun_def incseq_def)

lemma nn_integral_distr:
  "T \<in> measurable M M' \<Longrightarrow> f \<in> borel_measurable M' \<Longrightarrow> integral\<^sup>N (distr M M' T) f = (\<integral>\<^sup>+ x. f (T x) \<partial>M)"
  by (subst (1 2) nn_integral_max_0[symmetric])
     (simp add: nn_integral_distr')

subsubsection {* Counting space *}

lemma simple_function_count_space[simp]:
  "simple_function (count_space A) f \<longleftrightarrow> finite (f ` A)"
  unfolding simple_function_def by simp

lemma nn_integral_count_space:
  assumes A: "finite {a\<in>A. 0 < f a}"
  shows "integral\<^sup>N (count_space A) f = (\<Sum>a|a\<in>A \<and> 0 < f a. f a)"
proof -
  have *: "(\<integral>\<^sup>+x. max 0 (f x) \<partial>count_space A) =
    (\<integral>\<^sup>+ x. (\<Sum>a|a\<in>A \<and> 0 < f a. f a * indicator {a} x) \<partial>count_space A)"
    by (auto intro!: nn_integral_cong
             simp add: indicator_def if_distrib setsum_cases[OF A] max_def le_less)
  also have "\<dots> = (\<Sum>a|a\<in>A \<and> 0 < f a. \<integral>\<^sup>+ x. f a * indicator {a} x \<partial>count_space A)"
    by (subst nn_integral_setsum)
       (simp_all add: AE_count_space ereal_zero_le_0_iff less_imp_le)
  also have "\<dots> = (\<Sum>a|a\<in>A \<and> 0 < f a. f a)"
    by (auto intro!: setsum_cong simp: nn_integral_cmult_indicator one_ereal_def[symmetric])
  finally show ?thesis by (simp add: nn_integral_max_0)
qed

lemma nn_integral_count_space_finite:
    "finite A \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>count_space A) = (\<Sum>a\<in>A. max 0 (f a))"
  by (subst nn_integral_max_0[symmetric])
     (auto intro!: setsum_mono_zero_left simp: nn_integral_count_space less_le)

lemma emeasure_UN_countable:
  assumes sets: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> sets M" and I: "countable I" 
  assumes disj: "disjoint_family_on X I"
  shows "emeasure M (UNION I X) = (\<integral>\<^sup>+i. emeasure M (X i) \<partial>count_space I)"
proof cases
  assume "finite I" with sets disj show ?thesis
    by (subst setsum_emeasure[symmetric])
       (auto intro!: setsum_cong simp add: max_def subset_eq nn_integral_count_space_finite emeasure_nonneg)
next
  assume f: "\<not> finite I"
  then have [intro]: "I \<noteq> {}" by auto
  from from_nat_into_inj_infinite[OF I f] from_nat_into[OF this] disj
  have disj2: "disjoint_family (\<lambda>i. X (from_nat_into I i))"
    unfolding disjoint_family_on_def by metis

  from f have "bij_betw (from_nat_into I) UNIV I"
    using bij_betw_from_nat_into[OF I] by simp
  then have "(\<Union>i\<in>I. X i) = (\<Union>i. (X \<circ> from_nat_into I) i)"
    unfolding SUP_def image_comp [symmetric] by (simp add: bij_betw_def)
  then have "emeasure M (UNION I X) = emeasure M (\<Union>i. X (from_nat_into I i))"
    by simp
  also have "\<dots> = (\<Sum>i. emeasure M (X (from_nat_into I i)))"
    by (intro suminf_emeasure[symmetric] disj disj2) (auto intro!: sets from_nat_into[OF `I \<noteq> {}`])
  also have "\<dots> = (\<Sum>n. \<integral>\<^sup>+i. emeasure M (X i) * indicator {from_nat_into I n} i \<partial>count_space I)"
  proof (intro arg_cong[where f=suminf] ext)
    fix i
    have eq: "{a \<in> I. 0 < emeasure M (X a) * indicator {from_nat_into I i} a}
     = (if 0 < emeasure M (X (from_nat_into I i)) then {from_nat_into I i} else {})"
     using ereal_0_less_1
     by (auto simp: ereal_zero_less_0_iff indicator_def from_nat_into `I \<noteq> {}` simp del: ereal_0_less_1)
    have "(\<integral>\<^sup>+ ia. emeasure M (X ia) * indicator {from_nat_into I i} ia \<partial>count_space I) =
      (if 0 < emeasure M (X (from_nat_into I i)) then emeasure M (X (from_nat_into I i)) else 0)"
      by (subst nn_integral_count_space) (simp_all add: eq)
    also have "\<dots> = emeasure M (X (from_nat_into I i))"
      by (simp add: less_le emeasure_nonneg)
    finally show "emeasure M (X (from_nat_into I i)) =
         \<integral>\<^sup>+ ia. emeasure M (X ia) * indicator {from_nat_into I i} ia \<partial>count_space I" ..
  qed
  also have "\<dots> = (\<integral>\<^sup>+i. emeasure M (X i) \<partial>count_space I)"
    apply (subst nn_integral_suminf[symmetric])
    apply (auto simp: emeasure_nonneg intro!: nn_integral_cong)
  proof -
    fix x assume "x \<in> I"
    then have "(\<Sum>i. emeasure M (X x) * indicator {from_nat_into I i} x) = (\<Sum>i\<in>{to_nat_on I x}. emeasure M (X x) * indicator {from_nat_into I i} x)"
      by (intro suminf_finite) (auto simp: indicator_def I f)
    also have "\<dots> = emeasure M (X x)"
      by (simp add: I f `x\<in>I`)
    finally show "(\<Sum>i. emeasure M (X x) * indicator {from_nat_into I i} x) = emeasure M (X x)" .
  qed
  finally show ?thesis .
qed

lemma nn_integral_count_space_nat:
  fixes f :: "nat \<Rightarrow> ereal"
  assumes nonneg: "\<And>i. 0 \<le> f i"
  shows "(\<integral>\<^sup>+i. f i \<partial>count_space UNIV) = (\<Sum>i. f i)"
proof -
  have "(\<integral>\<^sup>+i. f i \<partial>count_space UNIV) =
    (\<integral>\<^sup>+i. (\<Sum>j. f j * indicator {j} i) \<partial>count_space UNIV)"
  proof (intro nn_integral_cong)
    fix i
    have "f i = (\<Sum>j\<in>{i}. f j * indicator {j} i)"
      by simp
    also have "\<dots> = (\<Sum>j. f j * indicator {j} i)"
      by (rule suminf_finite[symmetric]) auto
    finally show "f i = (\<Sum>j. f j * indicator {j} i)" .
  qed
  also have "\<dots> = (\<Sum>j. (\<integral>\<^sup>+i. f j * indicator {j} i \<partial>count_space UNIV))"
    by (rule nn_integral_suminf) (auto simp: nonneg)
  also have "\<dots> = (\<Sum>j. f j)"
    by (simp add: nonneg nn_integral_cmult_indicator one_ereal_def[symmetric])
  finally show ?thesis .
qed

lemma emeasure_countable_singleton:
  assumes sets: "\<And>x. x \<in> X \<Longrightarrow> {x} \<in> sets M" and X: "countable X"
  shows "emeasure M X = (\<integral>\<^sup>+x. emeasure M {x} \<partial>count_space X)"
proof -
  have "emeasure M (\<Union>i\<in>X. {i}) = (\<integral>\<^sup>+x. emeasure M {x} \<partial>count_space X)"
    using assms by (intro emeasure_UN_countable) (auto simp: disjoint_family_on_def)
  also have "(\<Union>i\<in>X. {i}) = X" by auto
  finally show ?thesis .
qed

lemma measure_eqI_countable:
  assumes [simp]: "sets M = Pow A" "sets N = Pow A" and A: "countable A"
  assumes eq: "\<And>a. a \<in> A \<Longrightarrow> emeasure M {a} = emeasure N {a}"
  shows "M = N"
proof (rule measure_eqI)
  fix X assume "X \<in> sets M"
  then have X: "X \<subseteq> A" by auto
  moreover with A have "countable X" by (auto dest: countable_subset)
  ultimately have
    "emeasure M X = (\<integral>\<^sup>+a. emeasure M {a} \<partial>count_space X)"
    "emeasure N X = (\<integral>\<^sup>+a. emeasure N {a} \<partial>count_space X)"
    by (auto intro!: emeasure_countable_singleton)
  moreover have "(\<integral>\<^sup>+a. emeasure M {a} \<partial>count_space X) = (\<integral>\<^sup>+a. emeasure N {a} \<partial>count_space X)"
    using X by (intro nn_integral_cong eq) auto
  ultimately show "emeasure M X = emeasure N X"
    by simp
qed simp

subsubsection {* Measures with Restricted Space *}

lemma simple_function_iff_borel_measurable:
  fixes f :: "'a \<Rightarrow> 'x::{t2_space}"
  shows "simple_function M f \<longleftrightarrow> finite (f ` space M) \<and> f \<in> borel_measurable M"
  by (metis borel_measurable_simple_function simple_functionD(1) simple_function_borel_measurable)

lemma simple_function_restrict_space_ereal:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes "\<Omega> \<inter> space M \<in> sets M"
  shows "simple_function (restrict_space M \<Omega>) f \<longleftrightarrow> simple_function M (\<lambda>x. f x * indicator \<Omega> x)"
proof -
  { assume "finite (f ` space (restrict_space M \<Omega>))"
    then have "finite (f ` space (restrict_space M \<Omega>) \<union> {0})" by simp
    then have "finite ((\<lambda>x. f x * indicator \<Omega> x) ` space M)"
      by (rule rev_finite_subset) (auto split: split_indicator simp: space_restrict_space) }
  moreover
  { assume "finite ((\<lambda>x. f x * indicator \<Omega> x) ` space M)"
    then have "finite (f ` space (restrict_space M \<Omega>))"
      by (rule rev_finite_subset) (auto split: split_indicator simp: space_restrict_space) }
  ultimately show ?thesis
    unfolding simple_function_iff_borel_measurable
      borel_measurable_restrict_space_iff_ereal[OF assms]
    by auto
qed

lemma simple_function_restrict_space:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "\<Omega> \<inter> space M \<in> sets M"
  shows "simple_function (restrict_space M \<Omega>) f \<longleftrightarrow> simple_function M (\<lambda>x. indicator \<Omega> x *\<^sub>R f x)"
proof -
  { assume "finite (f ` space (restrict_space M \<Omega>))"
    then have "finite (f ` space (restrict_space M \<Omega>) \<union> {0})" by simp
    then have "finite ((\<lambda>x. indicator \<Omega> x *\<^sub>R f x) ` space M)"
      by (rule rev_finite_subset) (auto split: split_indicator simp: space_restrict_space) }
  moreover
  { assume "finite ((\<lambda>x. indicator \<Omega> x *\<^sub>R f x) ` space M)"
    then have "finite (f ` space (restrict_space M \<Omega>))"
      by (rule rev_finite_subset) (auto split: split_indicator simp: space_restrict_space) }
  ultimately show ?thesis
    unfolding simple_function_iff_borel_measurable
      borel_measurable_restrict_space_iff[OF assms]
    by auto
qed


lemma split_indicator_asm: "P (indicator Q x) = (\<not> (x \<in> Q \<and> \<not> P 1 \<or> x \<notin> Q \<and> \<not> P 0))"
  by (auto split: split_indicator)

lemma simple_integral_restrict_space:
  assumes \<Omega>: "\<Omega> \<inter> space M \<in> sets M" "simple_function (restrict_space M \<Omega>) f"
  shows "simple_integral (restrict_space M \<Omega>) f = simple_integral M (\<lambda>x. f x * indicator \<Omega> x)"
  using simple_function_restrict_space_ereal[THEN iffD1, OF \<Omega>, THEN simple_functionD(1)]
  by (auto simp add: space_restrict_space emeasure_restrict_space[OF \<Omega>(1)] le_infI2 simple_integral_def
           split: split_indicator split_indicator_asm
           intro!: setsum_mono_zero_cong_left ereal_left_mult_cong arg_cong2[where f=emeasure])

lemma one_not_less_zero[simp]: "\<not> 1 < (0::ereal)"
  by (simp add: zero_ereal_def one_ereal_def) 

lemma nn_integral_restrict_space:
  assumes \<Omega>[simp]: "\<Omega> \<inter> space M \<in> sets M"
  shows "nn_integral (restrict_space M \<Omega>) f = nn_integral M (\<lambda>x. f x * indicator \<Omega> x)"
proof -
  let ?R = "restrict_space M \<Omega>" and ?X = "\<lambda>M f. {s. simple_function M s \<and> s \<le> max 0 \<circ> f \<and> range s \<subseteq> {0 ..< \<infinity>}}"
  have "integral\<^sup>S ?R ` ?X ?R f = integral\<^sup>S M ` ?X M (\<lambda>x. f x * indicator \<Omega> x)"
  proof (safe intro!: image_eqI)
    fix s assume s: "simple_function ?R s" "s \<le> max 0 \<circ> f" "range s \<subseteq> {0..<\<infinity>}"
    from s show "integral\<^sup>S (restrict_space M \<Omega>) s = integral\<^sup>S M (\<lambda>x. s x * indicator \<Omega> x)"
      by (intro simple_integral_restrict_space) auto
    from s show "simple_function M (\<lambda>x. s x * indicator \<Omega> x)"
      by (simp add: simple_function_restrict_space_ereal)
    from s show "(\<lambda>x. s x * indicator \<Omega> x) \<le> max 0 \<circ> (\<lambda>x. f x * indicator \<Omega> x)"
      "\<And>x. s x * indicator \<Omega> x \<in> {0..<\<infinity>}"
      by (auto split: split_indicator simp: le_fun_def image_subset_iff)
  next
    fix s assume s: "simple_function M s" "s \<le> max 0 \<circ> (\<lambda>x. f x * indicator \<Omega> x)" "range s \<subseteq> {0..<\<infinity>}"
    then have "simple_function M (\<lambda>x. s x * indicator (\<Omega> \<inter> space M) x)" (is ?s')
      by (intro simple_function_mult simple_function_indicator) auto
    also have "?s' \<longleftrightarrow> simple_function M (\<lambda>x. s x * indicator \<Omega> x)"
      by (rule simple_function_cong) (auto split: split_indicator)
    finally show sf: "simple_function (restrict_space M \<Omega>) s"
      by (simp add: simple_function_restrict_space_ereal)

    from s have s_eq: "s = (\<lambda>x. s x * indicator \<Omega> x)"
      by (auto simp add: fun_eq_iff le_fun_def image_subset_iff
                  split: split_indicator split_indicator_asm
                  intro: antisym)

    show "integral\<^sup>S M s = integral\<^sup>S (restrict_space M \<Omega>) s"
      by (subst s_eq) (rule simple_integral_restrict_space[symmetric, OF \<Omega> sf])
    show "\<And>x. s x \<in> {0..<\<infinity>}"
      using s by (auto simp: image_subset_iff)
    from s show "s \<le> max 0 \<circ> f" 
      by (subst s_eq) (auto simp: image_subset_iff le_fun_def split: split_indicator split_indicator_asm)
  qed
  then show ?thesis
    unfolding nn_integral_def_finite SUP_def by simp
qed

subsubsection {* Measure spaces with an associated density *}

definition density :: "'a measure \<Rightarrow> ('a \<Rightarrow> ereal) \<Rightarrow> 'a measure" where
  "density M f = measure_of (space M) (sets M) (\<lambda>A. \<integral>\<^sup>+ x. f x * indicator A x \<partial>M)"

lemma 
  shows sets_density[simp]: "sets (density M f) = sets M"
    and space_density[simp]: "space (density M f) = space M"
  by (auto simp: density_def)

(* FIXME: add conversion to simplify space, sets and measurable *)
lemma space_density_imp[measurable_dest]:
  "\<And>x M f. x \<in> space (density M f) \<Longrightarrow> x \<in> space M" by auto

lemma 
  shows measurable_density_eq1[simp]: "g \<in> measurable (density Mg f) Mg' \<longleftrightarrow> g \<in> measurable Mg Mg'"
    and measurable_density_eq2[simp]: "h \<in> measurable Mh (density Mh' f) \<longleftrightarrow> h \<in> measurable Mh Mh'"
    and simple_function_density_eq[simp]: "simple_function (density Mu f) u \<longleftrightarrow> simple_function Mu u"
  unfolding measurable_def simple_function_def by simp_all

lemma density_cong: "f \<in> borel_measurable M \<Longrightarrow> f' \<in> borel_measurable M \<Longrightarrow>
  (AE x in M. f x = f' x) \<Longrightarrow> density M f = density M f'"
  unfolding density_def by (auto intro!: measure_of_eq nn_integral_cong_AE sets.space_closed)

lemma density_max_0: "density M f = density M (\<lambda>x. max 0 (f x))"
proof -
  have "\<And>x A. max 0 (f x) * indicator A x = max 0 (f x * indicator A x)"
    by (auto simp: indicator_def)
  then show ?thesis
    unfolding density_def by (simp add: nn_integral_max_0)
qed

lemma density_ereal_max_0: "density M (\<lambda>x. ereal (f x)) = density M (\<lambda>x. ereal (max 0 (f x)))"
  by (subst density_max_0) (auto intro!: arg_cong[where f="density M"] split: split_max)

lemma emeasure_density:
  assumes f[measurable]: "f \<in> borel_measurable M" and A[measurable]: "A \<in> sets M"
  shows "emeasure (density M f) A = (\<integral>\<^sup>+ x. f x * indicator A x \<partial>M)"
    (is "_ = ?\<mu> A")
  unfolding density_def
proof (rule emeasure_measure_of_sigma)
  show "sigma_algebra (space M) (sets M)" ..
  show "positive (sets M) ?\<mu>"
    using f by (auto simp: positive_def intro!: nn_integral_nonneg)
  have \<mu>_eq: "?\<mu> = (\<lambda>A. \<integral>\<^sup>+ x. max 0 (f x) * indicator A x \<partial>M)" (is "?\<mu> = ?\<mu>'")
    apply (subst nn_integral_max_0[symmetric])
    apply (intro ext nn_integral_cong_AE AE_I2)
    apply (auto simp: indicator_def)
    done
  show "countably_additive (sets M) ?\<mu>"
    unfolding \<mu>_eq
  proof (intro countably_additiveI)
    fix A :: "nat \<Rightarrow> 'a set" assume "range A \<subseteq> sets M"
    then have "\<And>i. A i \<in> sets M" by auto
    then have *: "\<And>i. (\<lambda>x. max 0 (f x) * indicator (A i) x) \<in> borel_measurable M"
      by (auto simp: set_eq_iff)
    assume disj: "disjoint_family A"
    have "(\<Sum>n. ?\<mu>' (A n)) = (\<integral>\<^sup>+ x. (\<Sum>n. max 0 (f x) * indicator (A n) x) \<partial>M)"
      using f * by (simp add: nn_integral_suminf)
    also have "\<dots> = (\<integral>\<^sup>+ x. max 0 (f x) * (\<Sum>n. indicator (A n) x) \<partial>M)" using f
      by (auto intro!: suminf_cmult_ereal nn_integral_cong_AE)
    also have "\<dots> = (\<integral>\<^sup>+ x. max 0 (f x) * indicator (\<Union>n. A n) x \<partial>M)"
      unfolding suminf_indicator[OF disj] ..
    finally show "(\<Sum>n. ?\<mu>' (A n)) = ?\<mu>' (\<Union>x. A x)" by simp
  qed
qed fact

lemma null_sets_density_iff:
  assumes f: "f \<in> borel_measurable M"
  shows "A \<in> null_sets (density M f) \<longleftrightarrow> A \<in> sets M \<and> (AE x in M. x \<in> A \<longrightarrow> f x \<le> 0)"
proof -
  { assume "A \<in> sets M"
    have eq: "(\<integral>\<^sup>+x. f x * indicator A x \<partial>M) = (\<integral>\<^sup>+x. max 0 (f x) * indicator A x \<partial>M)"
      apply (subst nn_integral_max_0[symmetric])
      apply (intro nn_integral_cong)
      apply (auto simp: indicator_def)
      done
    have "(\<integral>\<^sup>+x. f x * indicator A x \<partial>M) = 0 \<longleftrightarrow> 
      emeasure M {x \<in> space M. max 0 (f x) * indicator A x \<noteq> 0} = 0"
      unfolding eq
      using f `A \<in> sets M`
      by (intro nn_integral_0_iff) auto
    also have "\<dots> \<longleftrightarrow> (AE x in M. max 0 (f x) * indicator A x = 0)"
      using f `A \<in> sets M`
      by (intro AE_iff_measurable[OF _ refl, symmetric]) auto
    also have "(AE x in M. max 0 (f x) * indicator A x = 0) \<longleftrightarrow> (AE x in M. x \<in> A \<longrightarrow> f x \<le> 0)"
      by (auto simp add: indicator_def max_def split: split_if_asm)
    finally have "(\<integral>\<^sup>+x. f x * indicator A x \<partial>M) = 0 \<longleftrightarrow> (AE x in M. x \<in> A \<longrightarrow> f x \<le> 0)" . }
  with f show ?thesis
    by (simp add: null_sets_def emeasure_density cong: conj_cong)
qed

lemma AE_density:
  assumes f: "f \<in> borel_measurable M"
  shows "(AE x in density M f. P x) \<longleftrightarrow> (AE x in M. 0 < f x \<longrightarrow> P x)"
proof
  assume "AE x in density M f. P x"
  with f obtain N where "{x \<in> space M. \<not> P x} \<subseteq> N" "N \<in> sets M" and ae: "AE x in M. x \<in> N \<longrightarrow> f x \<le> 0"
    by (auto simp: eventually_ae_filter null_sets_density_iff)
  then have "AE x in M. x \<notin> N \<longrightarrow> P x" by auto
  with ae show "AE x in M. 0 < f x \<longrightarrow> P x"
    by (rule eventually_elim2) auto
next
  fix N assume ae: "AE x in M. 0 < f x \<longrightarrow> P x"
  then obtain N where "{x \<in> space M. \<not> (0 < f x \<longrightarrow> P x)} \<subseteq> N" "N \<in> null_sets M"
    by (auto simp: eventually_ae_filter)
  then have *: "{x \<in> space (density M f). \<not> P x} \<subseteq> N \<union> {x\<in>space M. \<not> 0 < f x}"
    "N \<union> {x\<in>space M. \<not> 0 < f x} \<in> sets M" and ae2: "AE x in M. x \<notin> N"
    using f by (auto simp: subset_eq intro!: sets.sets_Collect_neg AE_not_in)
  show "AE x in density M f. P x"
    using ae2
    unfolding eventually_ae_filter[of _ "density M f"] Bex_def null_sets_density_iff[OF f]
    by (intro exI[of _ "N \<union> {x\<in>space M. \<not> 0 < f x}"] conjI *)
       (auto elim: eventually_elim2)
qed

lemma nn_integral_density':
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
  assumes g: "g \<in> borel_measurable M" "\<And>x. 0 \<le> g x"
  shows "integral\<^sup>N (density M f) g = (\<integral>\<^sup>+ x. f x * g x \<partial>M)"
using g proof induct
  case (cong u v)
  then show ?case
    apply (subst nn_integral_cong[OF cong(3)])
    apply (simp_all cong: nn_integral_cong)
    done
next
  case (set A) then show ?case
    by (simp add: emeasure_density f)
next
  case (mult u c)
  moreover have "\<And>x. f x * (c * u x) = c * (f x * u x)" by (simp add: field_simps)
  ultimately show ?case
    using f by (simp add: nn_integral_cmult)
next
  case (add u v)
  then have "\<And>x. f x * (v x + u x) = f x * v x + f x * u x"
    by (simp add: ereal_right_distrib)
  with add f show ?case
    by (auto simp add: nn_integral_add ereal_zero_le_0_iff intro!: nn_integral_add[symmetric])
next
  case (seq U)
  from f(2) have eq: "AE x in M. f x * (SUP i. U i x) = (SUP i. f x * U i x)"
    by eventually_elim (simp add: SUP_ereal_cmult seq)
  from seq f show ?case
    apply (simp add: nn_integral_monotone_convergence_SUP)
    apply (subst nn_integral_cong_AE[OF eq])
    apply (subst nn_integral_monotone_convergence_SUP_AE)
    apply (auto simp: incseq_def le_fun_def intro!: ereal_mult_left_mono)
    done
qed

lemma nn_integral_density:
  "f \<in> borel_measurable M \<Longrightarrow> AE x in M. 0 \<le> f x \<Longrightarrow> g' \<in> borel_measurable M \<Longrightarrow> 
    integral\<^sup>N (density M f) g' = (\<integral>\<^sup>+ x. f x * g' x \<partial>M)"
  by (subst (1 2) nn_integral_max_0[symmetric])
     (auto intro!: nn_integral_cong_AE
           simp: measurable_If max_def ereal_zero_le_0_iff nn_integral_density')

lemma emeasure_restricted:
  assumes S: "S \<in> sets M" and X: "X \<in> sets M"
  shows "emeasure (density M (indicator S)) X = emeasure M (S \<inter> X)"
proof -
  have "emeasure (density M (indicator S)) X = (\<integral>\<^sup>+x. indicator S x * indicator X x \<partial>M)"
    using S X by (simp add: emeasure_density)
  also have "\<dots> = (\<integral>\<^sup>+x. indicator (S \<inter> X) x \<partial>M)"
    by (auto intro!: nn_integral_cong simp: indicator_def)
  also have "\<dots> = emeasure M (S \<inter> X)"
    using S X by (simp add: sets.Int)
  finally show ?thesis .
qed

lemma measure_restricted:
  "S \<in> sets M \<Longrightarrow> X \<in> sets M \<Longrightarrow> measure (density M (indicator S)) X = measure M (S \<inter> X)"
  by (simp add: emeasure_restricted measure_def)

lemma (in finite_measure) finite_measure_restricted:
  "S \<in> sets M \<Longrightarrow> finite_measure (density M (indicator S))"
  by default (simp add: emeasure_restricted)

lemma emeasure_density_const:
  "A \<in> sets M \<Longrightarrow> 0 \<le> c \<Longrightarrow> emeasure (density M (\<lambda>_. c)) A = c * emeasure M A"
  by (auto simp: nn_integral_cmult_indicator emeasure_density)

lemma measure_density_const:
  "A \<in> sets M \<Longrightarrow> 0 < c \<Longrightarrow> c \<noteq> \<infinity> \<Longrightarrow> measure (density M (\<lambda>_. c)) A = real c * measure M A"
  by (auto simp: emeasure_density_const measure_def)

lemma density_density_eq:
   "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> AE x in M. 0 \<le> f x \<Longrightarrow>
   density (density M f) g = density M (\<lambda>x. f x * g x)"
  by (auto intro!: measure_eqI simp: emeasure_density nn_integral_density ac_simps)

lemma distr_density_distr:
  assumes T: "T \<in> measurable M M'" and T': "T' \<in> measurable M' M"
    and inv: "\<forall>x\<in>space M. T' (T x) = x"
  assumes f: "f \<in> borel_measurable M'"
  shows "distr (density (distr M M' T) f) M T' = density M (f \<circ> T)" (is "?R = ?L")
proof (rule measure_eqI)
  fix A assume A: "A \<in> sets ?R"
  { fix x assume "x \<in> space M"
    with sets.sets_into_space[OF A]
    have "indicator (T' -` A \<inter> space M') (T x) = (indicator A x :: ereal)"
      using T inv by (auto simp: indicator_def measurable_space) }
  with A T T' f show "emeasure ?R A = emeasure ?L A"
    by (simp add: measurable_comp emeasure_density emeasure_distr
                  nn_integral_distr measurable_sets cong: nn_integral_cong)
qed simp

lemma density_density_divide:
  fixes f g :: "'a \<Rightarrow> real"
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
  assumes g: "g \<in> borel_measurable M" "AE x in M. 0 \<le> g x"
  assumes ac: "AE x in M. f x = 0 \<longrightarrow> g x = 0"
  shows "density (density M f) (\<lambda>x. g x / f x) = density M g"
proof -
  have "density M g = density M (\<lambda>x. f x * (g x / f x))"
    using f g ac by (auto intro!: density_cong measurable_If)
  then show ?thesis
    using f g by (subst density_density_eq) auto
qed

subsubsection {* Point measure *}

definition point_measure :: "'a set \<Rightarrow> ('a \<Rightarrow> ereal) \<Rightarrow> 'a measure" where
  "point_measure A f = density (count_space A) f"

lemma
  shows space_point_measure: "space (point_measure A f) = A"
    and sets_point_measure: "sets (point_measure A f) = Pow A"
  by (auto simp: point_measure_def)

lemma measurable_point_measure_eq1[simp]:
  "g \<in> measurable (point_measure A f) M \<longleftrightarrow> g \<in> A \<rightarrow> space M"
  unfolding point_measure_def by simp

lemma measurable_point_measure_eq2_finite[simp]:
  "finite A \<Longrightarrow>
   g \<in> measurable M (point_measure A f) \<longleftrightarrow>
    (g \<in> space M \<rightarrow> A \<and> (\<forall>a\<in>A. g -` {a} \<inter> space M \<in> sets M))"
  unfolding point_measure_def by (simp add: measurable_count_space_eq2)

lemma simple_function_point_measure[simp]:
  "simple_function (point_measure A f) g \<longleftrightarrow> finite (g ` A)"
  by (simp add: point_measure_def)

lemma emeasure_point_measure:
  assumes A: "finite {a\<in>X. 0 < f a}" "X \<subseteq> A"
  shows "emeasure (point_measure A f) X = (\<Sum>a|a\<in>X \<and> 0 < f a. f a)"
proof -
  have "{a. (a \<in> X \<longrightarrow> a \<in> A \<and> 0 < f a) \<and> a \<in> X} = {a\<in>X. 0 < f a}"
    using `X \<subseteq> A` by auto
  with A show ?thesis
    by (simp add: emeasure_density nn_integral_count_space ereal_zero_le_0_iff
                  point_measure_def indicator_def)
qed

lemma emeasure_point_measure_finite:
  "finite A \<Longrightarrow> (\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> X \<subseteq> A \<Longrightarrow> emeasure (point_measure A f) X = (\<Sum>a\<in>X. f a)"
  by (subst emeasure_point_measure) (auto dest: finite_subset intro!: setsum_mono_zero_left simp: less_le)

lemma emeasure_point_measure_finite2:
  "X \<subseteq> A \<Longrightarrow> finite X \<Longrightarrow> (\<And>i. i \<in> X \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> emeasure (point_measure A f) X = (\<Sum>a\<in>X. f a)"
  by (subst emeasure_point_measure)
     (auto dest: finite_subset intro!: setsum_mono_zero_left simp: less_le)

lemma null_sets_point_measure_iff:
  "X \<in> null_sets (point_measure A f) \<longleftrightarrow> X \<subseteq> A \<and> (\<forall>x\<in>X. f x \<le> 0)"
 by (auto simp: AE_count_space null_sets_density_iff point_measure_def)

lemma AE_point_measure:
  "(AE x in point_measure A f. P x) \<longleftrightarrow> (\<forall>x\<in>A. 0 < f x \<longrightarrow> P x)"
  unfolding point_measure_def
  by (subst AE_density) (auto simp: AE_density AE_count_space point_measure_def)

lemma nn_integral_point_measure:
  "finite {a\<in>A. 0 < f a \<and> 0 < g a} \<Longrightarrow>
    integral\<^sup>N (point_measure A f) g = (\<Sum>a|a\<in>A \<and> 0 < f a \<and> 0 < g a. f a * g a)"
  unfolding point_measure_def
  apply (subst density_max_0)
  apply (subst nn_integral_density)
  apply (simp_all add: AE_count_space nn_integral_density)
  apply (subst nn_integral_count_space )
  apply (auto intro!: setsum_cong simp: max_def ereal_zero_less_0_iff)
  apply (rule finite_subset)
  prefer 2
  apply assumption
  apply auto
  done

lemma nn_integral_point_measure_finite:
  "finite A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> 0 \<le> f a) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> 0 \<le> g a) \<Longrightarrow>
    integral\<^sup>N (point_measure A f) g = (\<Sum>a\<in>A. f a * g a)"
  by (subst nn_integral_point_measure) (auto intro!: setsum_mono_zero_left simp: less_le)

subsubsection {* Uniform measure *}

definition "uniform_measure M A = density M (\<lambda>x. indicator A x / emeasure M A)"

lemma
  shows sets_uniform_measure[simp]: "sets (uniform_measure M A) = sets M"
    and space_uniform_measure[simp]: "space (uniform_measure M A) = space M"
  by (auto simp: uniform_measure_def)

lemma emeasure_uniform_measure[simp]:
  assumes A: "A \<in> sets M" and B: "B \<in> sets M"
  shows "emeasure (uniform_measure M A) B = emeasure M (A \<inter> B) / emeasure M A"
proof -
  from A B have "emeasure (uniform_measure M A) B = (\<integral>\<^sup>+x. (1 / emeasure M A) * indicator (A \<inter> B) x \<partial>M)"
    by (auto simp add: uniform_measure_def emeasure_density split: split_indicator
             intro!: nn_integral_cong)
  also have "\<dots> = emeasure M (A \<inter> B) / emeasure M A"
    using A B
    by (subst nn_integral_cmult_indicator) (simp_all add: sets.Int emeasure_nonneg)
  finally show ?thesis .
qed

lemma measure_uniform_measure[simp]:
  assumes A: "emeasure M A \<noteq> 0" "emeasure M A \<noteq> \<infinity>" and B: "B \<in> sets M"
  shows "measure (uniform_measure M A) B = measure M (A \<inter> B) / measure M A"
  using emeasure_uniform_measure[OF emeasure_neq_0_sets[OF A(1)] B] A
  by (cases "emeasure M A" "emeasure M (A \<inter> B)" rule: ereal2_cases) (simp_all add: measure_def)

subsubsection {* Uniform count measure *}

definition "uniform_count_measure A = point_measure A (\<lambda>x. 1 / card A)"
 
lemma 
  shows space_uniform_count_measure: "space (uniform_count_measure A) = A"
    and sets_uniform_count_measure: "sets (uniform_count_measure A) = Pow A"
    unfolding uniform_count_measure_def by (auto simp: space_point_measure sets_point_measure)
 
lemma emeasure_uniform_count_measure:
  "finite A \<Longrightarrow> X \<subseteq> A \<Longrightarrow> emeasure (uniform_count_measure A) X = card X / card A"
  by (simp add: real_eq_of_nat emeasure_point_measure_finite uniform_count_measure_def)
 
lemma measure_uniform_count_measure:
  "finite A \<Longrightarrow> X \<subseteq> A \<Longrightarrow> measure (uniform_count_measure A) X = card X / card A"
  by (simp add: real_eq_of_nat emeasure_point_measure_finite uniform_count_measure_def measure_def)

end
