(*  Title:      HOL/Probability/Lebesgue_Integration.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

header {*Lebesgue Integration*}

theory Lebesgue_Integration
  imports Measure Borel_Space
begin

lemma real_ereal_1[simp]: "real (1::ereal) = 1"
  unfolding one_ereal_def by simp

lemma ereal_indicator_pos[simp,intro]: "0 \<le> (indicator A x ::ereal)"
  unfolding indicator_def by auto

lemma tendsto_real_max:
  fixes x y :: real
  assumes "(X ---> x) net"
  assumes "(Y ---> y) net"
  shows "((\<lambda>x. max (X x) (Y x)) ---> max x y) net"
proof -
  have *: "\<And>x y :: real. max x y = y + ((x - y) + norm (x - y)) / 2"
    by (auto split: split_max simp: field_simps)
  show ?thesis
    unfolding *
    by (intro tendsto_add assms tendsto_divide tendsto_norm tendsto_diff) auto
qed

lemma (in measure_space) measure_Union:
  assumes "finite S" "S \<subseteq> sets M" "\<And>A B. A \<in> S \<Longrightarrow> B \<in> S \<Longrightarrow> A \<noteq> B \<Longrightarrow> A \<inter> B = {}"
  shows "setsum \<mu> S = \<mu> (\<Union>S)"
proof -
  have "setsum \<mu> S = \<mu> (\<Union>i\<in>S. i)"
    using assms by (intro measure_setsum[OF `finite S`]) (auto simp: disjoint_family_on_def)
  also have "\<dots> = \<mu> (\<Union>S)" by (auto intro!: arg_cong[where f=\<mu>])
  finally show ?thesis .
qed

lemma (in sigma_algebra) measurable_sets2[intro]:
  assumes "f \<in> measurable M M'" "g \<in> measurable M M''"
  and "A \<in> sets M'" "B \<in> sets M''"
  shows "f -` A \<inter> g -` B \<inter> space M \<in> sets M"
proof -
  have "f -` A \<inter> g -` B \<inter> space M = (f -` A \<inter> space M) \<inter> (g -` B \<inter> space M)"
    by auto
  then show ?thesis using assms by (auto intro: measurable_sets)
qed

lemma incseq_Suc_iff: "incseq f \<longleftrightarrow> (\<forall>n. f n \<le> f (Suc n))"
proof
  assume "\<forall>n. f n \<le> f (Suc n)" then show "incseq f" by (auto intro!: incseq_SucI)
qed (auto simp: incseq_def)

lemma borel_measurable_real_floor:
  "(\<lambda>x::real. real \<lfloor>x\<rfloor>) \<in> borel_measurable borel"
  unfolding borel.borel_measurable_iff_ge
proof (intro allI)
  fix a :: real
  { fix x have "a \<le> real \<lfloor>x\<rfloor> \<longleftrightarrow> real \<lceil>a\<rceil> \<le> x"
      using le_floor_eq[of "\<lceil>a\<rceil>" x] ceiling_le_iff[of a "\<lfloor>x\<rfloor>"]
      unfolding real_eq_of_int by simp }
  then have "{w::real \<in> space borel. a \<le> real \<lfloor>w\<rfloor>} = {real \<lceil>a\<rceil>..}" by auto
  then show "{w::real \<in> space borel. a \<le> real \<lfloor>w\<rfloor>} \<in> sets borel" by auto
qed

lemma measure_preservingD2:
  "f \<in> measure_preserving A B \<Longrightarrow> f \<in> measurable A B"
  unfolding measure_preserving_def by auto

lemma measure_preservingD3:
  "f \<in> measure_preserving A B \<Longrightarrow> f \<in> space A \<rightarrow> space B"
  unfolding measure_preserving_def measurable_def by auto

lemma measure_preservingD:
  "T \<in> measure_preserving A B \<Longrightarrow> X \<in> sets B \<Longrightarrow> measure A (T -` X \<inter> space A) = measure B X"
  unfolding measure_preserving_def by auto

lemma (in sigma_algebra) borel_measurable_real_natfloor[intro, simp]:
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. real (natfloor (f x))) \<in> borel_measurable M"
proof -
  have "\<And>x. real (natfloor (f x)) = max 0 (real \<lfloor>f x\<rfloor>)"
    by (auto simp: max_def natfloor_def)
  with borel_measurable_max[OF measurable_comp[OF assms borel_measurable_real_floor] borel_measurable_const]
  show ?thesis by (simp add: comp_def)
qed

lemma (in measure_space) AE_not_in:
  assumes N: "N \<in> null_sets" shows "AE x. x \<notin> N"
  using N by (rule AE_I') auto

lemma sums_If_finite:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  assumes finite: "finite {r. P r}"
  shows "(\<lambda>r. if P r then f r else 0) sums (\<Sum>r\<in>{r. P r}. f r)" (is "?F sums _")
proof cases
  assume "{r. P r} = {}" hence "\<And>r. \<not> P r" by auto
  thus ?thesis by (simp add: sums_zero)
next
  assume not_empty: "{r. P r} \<noteq> {}"
  have "?F sums (\<Sum>r = 0..< Suc (Max {r. P r}). ?F r)"
    by (rule series_zero)
       (auto simp add: Max_less_iff[OF finite not_empty] less_eq_Suc_le[symmetric])
  also have "(\<Sum>r = 0..< Suc (Max {r. P r}). ?F r) = (\<Sum>r\<in>{r. P r}. f r)"
    by (subst setsum_cases)
       (auto intro!: setsum_cong simp: Max_ge_iff[OF finite not_empty] less_Suc_eq_le)
  finally show ?thesis .
qed

lemma sums_single:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "(\<lambda>r. if r = i then f r else 0) sums f i"
  using sums_If_finite[of "\<lambda>r. r = i" f] by simp

section "Simple function"

text {*

Our simple functions are not restricted to positive real numbers. Instead
they are just functions with a finite range and are measurable when singleton
sets are measurable.

*}

definition "simple_function M g \<longleftrightarrow>
    finite (g ` space M) \<and>
    (\<forall>x \<in> g ` space M. g -` {x} \<inter> space M \<in> sets M)"

lemma (in sigma_algebra) simple_functionD:
  assumes "simple_function M g"
  shows "finite (g ` space M)" and "g -` X \<inter> space M \<in> sets M"
proof -
  show "finite (g ` space M)"
    using assms unfolding simple_function_def by auto
  have "g -` X \<inter> space M = g -` (X \<inter> g`space M) \<inter> space M" by auto
  also have "\<dots> = (\<Union>x\<in>X \<inter> g`space M. g-`{x} \<inter> space M)" by auto
  finally show "g -` X \<inter> space M \<in> sets M" using assms
    by (auto intro!: finite_UN simp del: UN_simps simp: simple_function_def)
qed

lemma (in sigma_algebra) simple_function_measurable2[intro]:
  assumes "simple_function M f" "simple_function M g"
  shows "f -` A \<inter> g -` B \<inter> space M \<in> sets M"
proof -
  have "f -` A \<inter> g -` B \<inter> space M = (f -` A \<inter> space M) \<inter> (g -` B \<inter> space M)"
    by auto
  then show ?thesis using assms[THEN simple_functionD(2)] by auto
qed

lemma (in sigma_algebra) simple_function_indicator_representation:
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

lemma (in measure_space) simple_function_notspace:
  "simple_function M (\<lambda>x. h x * indicator (- space M) x::ereal)" (is "simple_function M ?h")
proof -
  have "?h ` space M \<subseteq> {0}" unfolding indicator_def by auto
  hence [simp, intro]: "finite (?h ` space M)" by (auto intro: finite_subset)
  have "?h -` {0} \<inter> space M = space M" by auto
  thus ?thesis unfolding simple_function_def by auto
qed

lemma (in sigma_algebra) simple_function_cong:
  assumes "\<And>t. t \<in> space M \<Longrightarrow> f t = g t"
  shows "simple_function M f \<longleftrightarrow> simple_function M g"
proof -
  have "f ` space M = g ` space M"
    "\<And>x. f -` {x} \<inter> space M = g -` {x} \<inter> space M"
    using assms by (auto intro!: image_eqI)
  thus ?thesis unfolding simple_function_def using assms by simp
qed

lemma (in sigma_algebra) simple_function_cong_algebra:
  assumes "sets N = sets M" "space N = space M"
  shows "simple_function M f \<longleftrightarrow> simple_function N f"
  unfolding simple_function_def assms ..

lemma (in sigma_algebra) borel_measurable_simple_function:
  assumes "simple_function M f"
  shows "f \<in> borel_measurable M"
proof (rule borel_measurableI)
  fix S
  let ?I = "f ` (f -` S \<inter> space M)"
  have *: "(\<Union>x\<in>?I. f -` {x} \<inter> space M) = f -` S \<inter> space M" (is "?U = _") by auto
  have "finite ?I"
    using assms unfolding simple_function_def
    using finite_subset[of "f ` (f -` S \<inter> space M)" "f ` space M"] by auto
  hence "?U \<in> sets M"
    apply (rule finite_UN)
    using assms unfolding simple_function_def by auto
  thus "f -` S \<inter> space M \<in> sets M" unfolding * .
qed

lemma (in sigma_algebra) simple_function_borel_measurable:
  fixes f :: "'a \<Rightarrow> 'x::{t2_space}"
  assumes "f \<in> borel_measurable M" and "finite (f ` space M)"
  shows "simple_function M f"
  using assms unfolding simple_function_def
  by (auto intro: borel_measurable_vimage)

lemma (in sigma_algebra) simple_function_eq_borel_measurable:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "simple_function M f \<longleftrightarrow> finite (f`space M) \<and> f \<in> borel_measurable M"
  using simple_function_borel_measurable[of f]
    borel_measurable_simple_function[of f]
  by (fastforce simp: simple_function_def)

lemma (in sigma_algebra) simple_function_const[intro, simp]:
  "simple_function M (\<lambda>x. c)"
  by (auto intro: finite_subset simp: simple_function_def)
lemma (in sigma_algebra) simple_function_compose[intro, simp]:
  assumes "simple_function M f"
  shows "simple_function M (g \<circ> f)"
  unfolding simple_function_def
proof safe
  show "finite ((g \<circ> f) ` space M)"
    using assms unfolding simple_function_def by (auto simp: image_compose)
next
  fix x assume "x \<in> space M"
  let ?G = "g -` {g (f x)} \<inter> (f`space M)"
  have *: "(g \<circ> f) -` {(g \<circ> f) x} \<inter> space M =
    (\<Union>x\<in>?G. f -` {x} \<inter> space M)" by auto
  show "(g \<circ> f) -` {(g \<circ> f) x} \<inter> space M \<in> sets M"
    using assms unfolding simple_function_def *
    by (rule_tac finite_UN) (auto intro!: finite_UN)
qed

lemma (in sigma_algebra) simple_function_indicator[intro, simp]:
  assumes "A \<in> sets M"
  shows "simple_function M (indicator A)"
proof -
  have "indicator A ` space M \<subseteq> {0, 1}" (is "?S \<subseteq> _")
    by (auto simp: indicator_def)
  hence "finite ?S" by (rule finite_subset) simp
  moreover have "- A \<inter> space M = space M - A" by auto
  ultimately show ?thesis unfolding simple_function_def
    using assms by (auto simp: indicator_def_raw)
qed

lemma (in sigma_algebra) simple_function_Pair[intro, simp]:
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

lemma (in sigma_algebra) simple_function_compose1:
  assumes "simple_function M f"
  shows "simple_function M (\<lambda>x. g (f x))"
  using simple_function_compose[OF assms, of g]
  by (simp add: comp_def)

lemma (in sigma_algebra) simple_function_compose2:
  assumes "simple_function M f" and "simple_function M g"
  shows "simple_function M (\<lambda>x. h (f x) (g x))"
proof -
  have "simple_function M ((\<lambda>(x, y). h x y) \<circ> (\<lambda>x. (f x, g x)))"
    using assms by auto
  thus ?thesis by (simp_all add: comp_def)
qed

lemmas (in sigma_algebra) simple_function_add[intro, simp] = simple_function_compose2[where h="op +"]
  and simple_function_diff[intro, simp] = simple_function_compose2[where h="op -"]
  and simple_function_uminus[intro, simp] = simple_function_compose[where g="uminus"]
  and simple_function_mult[intro, simp] = simple_function_compose2[where h="op *"]
  and simple_function_div[intro, simp] = simple_function_compose2[where h="op /"]
  and simple_function_inverse[intro, simp] = simple_function_compose[where g="inverse"]
  and simple_function_max[intro, simp] = simple_function_compose2[where h=max]

lemma (in sigma_algebra) simple_function_setsum[intro, simp]:
  assumes "\<And>i. i \<in> P \<Longrightarrow> simple_function M (f i)"
  shows "simple_function M (\<lambda>x. \<Sum>i\<in>P. f i x)"
proof cases
  assume "finite P" from this assms show ?thesis by induct auto
qed auto

lemma (in sigma_algebra)
  fixes f g :: "'a \<Rightarrow> real" assumes sf: "simple_function M f"
  shows simple_function_ereal[intro, simp]: "simple_function M (\<lambda>x. ereal (f x))"
  by (auto intro!: simple_function_compose1[OF sf])

lemma (in sigma_algebra)
  fixes f g :: "'a \<Rightarrow> nat" assumes sf: "simple_function M f"
  shows simple_function_real_of_nat[intro, simp]: "simple_function M (\<lambda>x. real (f x))"
  by (auto intro!: simple_function_compose1[OF sf])

lemma (in sigma_algebra) borel_measurable_implies_simple_function_sequence:
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
         by (cases "u x") (auto intro!: natfloor_mono simp: mult_nonneg_nonneg)
      moreover have "real (natfloor (j * 2 ^ j)) \<le> j * 2^j"
        by (intro real_natfloor_le) (auto simp: mult_nonneg_nonneg)
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
        using u by (auto intro!: measurable_If simp: real_f)
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
    proof (rule ereal_SUPI)
      fix i show "?g i x \<le> max 0 (u x)" unfolding max_def f_def
        by (cases "u x") (auto simp: field_simps real_natfloor_le natfloor_neg
                                     mult_nonpos_nonneg mult_nonneg_nonneg)
    next
      fix y assume *: "\<And>i. i \<in> UNIV \<Longrightarrow> ?g i x \<le> y"
      have "\<And>i. 0 \<le> ?g i x" by (auto simp: divide_nonneg_pos)
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
          obtain N where "\<forall>n\<ge>N. r * 2^n < p * 2^n - 1" by (auto simp: inverse_eq_divide field_simps)
          then have "r * 2^max N m < p * 2^max N m - 1" by simp
          moreover
          have "real (natfloor (p * 2 ^ max N m)) \<le> r * 2 ^ max N m"
            using *[of "max N m"] m unfolding real_f using ux
            by (cases "0 \<le> u x") (simp_all add: max_def mult_nonneg_nonneg split: split_if_asm)
          then have "p * 2 ^ max N m - 1 < r * 2 ^ max N m"
            by (metis real_natfloor_gt_diff_one less_le_trans)
          ultimately show False by auto
        qed
        then show "max 0 (u x) \<le> y" using real ux by simp
      qed (insert `0 \<le> y`, auto)
    qed
  qed (auto simp: divide_nonneg_pos)
qed

lemma (in sigma_algebra) borel_measurable_implies_simple_function_sequence':
  fixes u :: "'a \<Rightarrow> ereal"
  assumes u: "u \<in> borel_measurable M"
  obtains f where "\<And>i. simple_function M (f i)" "incseq f" "\<And>i. \<infinity> \<notin> range (f i)"
    "\<And>x. (SUP i. f i x) = max 0 (u x)" "\<And>i x. 0 \<le> f i x"
  using borel_measurable_implies_simple_function_sequence[OF u] by auto

lemma (in sigma_algebra) simple_function_If_set:
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
      using sets_into_space[OF A] by (auto split: split_if_asm simp: G_def F_def)
    have [intro]: "\<And>x. F x \<in> sets M" "\<And>x. G x \<in> sets M"
      unfolding F_def G_def using sf[THEN simple_functionD(2)] by auto
    show "?IF -` {?IF x} \<inter> space M \<in> sets M" unfolding * using A by auto
  qed
qed

lemma (in sigma_algebra) simple_function_If:
  assumes sf: "simple_function M f" "simple_function M g" and P: "{x\<in>space M. P x} \<in> sets M"
  shows "simple_function M (\<lambda>x. if P x then f x else g x)"
proof -
  have "{x\<in>space M. P x} = {x. P x} \<inter> space M" by auto
  with simple_function_If_set[OF sf, of "{x. P x}"] P show ?thesis by simp
qed

lemma (in measure_space) simple_function_restricted:
  fixes f :: "'a \<Rightarrow> ereal" assumes "A \<in> sets M"
  shows "simple_function (restricted_space A) f \<longleftrightarrow> simple_function M (\<lambda>x. f x * indicator A x)"
    (is "simple_function ?R f \<longleftrightarrow> simple_function M ?f")
proof -
  interpret R: sigma_algebra ?R by (rule restricted_sigma_algebra[OF `A \<in> sets M`])
  have f: "finite (f`A) \<longleftrightarrow> finite (?f`space M)"
  proof cases
    assume "A = space M"
    then have "f`A = ?f`space M" by (fastforce simp: image_iff)
    then show ?thesis by simp
  next
    assume "A \<noteq> space M"
    then obtain x where x: "x \<in> space M" "x \<notin> A"
      using sets_into_space `A \<in> sets M` by auto
    have *: "?f`space M = f`A \<union> {0}"
    proof (auto simp add: image_iff)
      show "\<exists>x\<in>space M. f x = 0 \<or> indicator A x = 0"
        using x by (auto intro!: bexI[of _ x])
    next
      fix x assume "x \<in> A"
      then show "\<exists>y\<in>space M. f x = f y * indicator A y"
        using `A \<in> sets M` sets_into_space by (auto intro!: bexI[of _ x])
    next
      fix x
      assume "indicator A x \<noteq> (0::ereal)"
      then have "x \<in> A" by (auto simp: indicator_def split: split_if_asm)
      moreover assume "x \<in> space M" "\<forall>y\<in>A. ?f x \<noteq> f y"
      ultimately show "f x = 0" by auto
    qed
    then show ?thesis by auto
  qed
  then show ?thesis
    unfolding simple_function_eq_borel_measurable
      R.simple_function_eq_borel_measurable
    unfolding borel_measurable_restricted[OF `A \<in> sets M`]
    using assms(1)[THEN sets_into_space]
    by (auto simp: indicator_def)
qed

lemma (in sigma_algebra) simple_function_subalgebra:
  assumes "simple_function N f"
  and N_subalgebra: "sets N \<subseteq> sets M" "space N = space M"
  shows "simple_function M f"
  using assms unfolding simple_function_def by auto

lemma (in measure_space) simple_function_vimage:
  assumes T: "sigma_algebra M'" "T \<in> measurable M M'"
    and f: "simple_function M' f"
  shows "simple_function M (\<lambda>x. f (T x))"
proof (intro simple_function_def[THEN iffD2] conjI ballI)
  interpret T: sigma_algebra M' by fact
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

section "Simple integral"

definition simple_integral_def:
  "integral\<^isup>S M f = (\<Sum>x \<in> f ` space M. x * measure M (f -` {x} \<inter> space M))"

syntax
  "_simple_integral" :: "pttrn \<Rightarrow> ereal \<Rightarrow> ('a, 'b) measure_space_scheme \<Rightarrow> ereal" ("\<integral>\<^isup>S _. _ \<partial>_" [60,61] 110)

translations
  "\<integral>\<^isup>S x. f \<partial>M" == "CONST integral\<^isup>S M (%x. f)"

lemma (in measure_space) simple_integral_cong:
  assumes "\<And>t. t \<in> space M \<Longrightarrow> f t = g t"
  shows "integral\<^isup>S M f = integral\<^isup>S M g"
proof -
  have "f ` space M = g ` space M"
    "\<And>x. f -` {x} \<inter> space M = g -` {x} \<inter> space M"
    using assms by (auto intro!: image_eqI)
  thus ?thesis unfolding simple_integral_def by simp
qed

lemma (in measure_space) simple_integral_cong_measure:
  assumes "\<And>A. A \<in> sets M \<Longrightarrow> measure N A = \<mu> A" "sets N = sets M" "space N = space M"
    and "simple_function M f"
  shows "integral\<^isup>S N f = integral\<^isup>S M f"
proof -
  interpret v: measure_space N
    by (rule measure_space_cong) fact+
  from simple_functionD[OF `simple_function M f`] assms show ?thesis
    by (auto intro!: setsum_cong simp: simple_integral_def)
qed

lemma (in measure_space) simple_integral_const[simp]:
  "(\<integral>\<^isup>Sx. c \<partial>M) = c * \<mu> (space M)"
proof (cases "space M = {}")
  case True thus ?thesis unfolding simple_integral_def by simp
next
  case False hence "(\<lambda>x. c) ` space M = {c}" by auto
  thus ?thesis unfolding simple_integral_def by simp
qed

lemma (in measure_space) simple_function_partition:
  assumes f: "simple_function M f" and g: "simple_function M g"
  shows "integral\<^isup>S M f = (\<Sum>A\<in>(\<lambda>x. f -` {f x} \<inter> g -` {g x} \<inter> space M) ` space M. the_elem (f`A) * \<mu> A)"
    (is "_ = setsum _ (?p ` space M)")
proof-
  let ?sub = "\<lambda>x. ?p ` (f -` {x} \<inter> space M)"
  let ?SIGMA = "Sigma (f`space M) ?sub"

  have [intro]:
    "finite (f ` space M)"
    "finite (g ` space M)"
    using assms unfolding simple_function_def by simp_all

  { fix A
    have "?p ` (A \<inter> space M) \<subseteq>
      (\<lambda>(x,y). f -` {x} \<inter> g -` {y} \<inter> space M) ` (f`space M \<times> g`space M)"
      by auto
    hence "finite (?p ` (A \<inter> space M))"
      by (rule finite_subset) auto }
  note this[intro, simp]
  note sets = simple_function_measurable2[OF f g]

  { fix x assume "x \<in> space M"
    have "\<Union>(?sub (f x)) = (f -` {f x} \<inter> space M)" by auto
    with sets have "\<mu> (f -` {f x} \<inter> space M) = setsum \<mu> (?sub (f x))"
      by (subst measure_Union) auto }
  hence "integral\<^isup>S M f = (\<Sum>(x,A)\<in>?SIGMA. x * \<mu> A)"
    unfolding simple_integral_def using f sets
    by (subst setsum_Sigma[symmetric])
       (auto intro!: setsum_cong setsum_ereal_right_distrib)
  also have "\<dots> = (\<Sum>A\<in>?p ` space M. the_elem (f`A) * \<mu> A)"
  proof -
    have [simp]: "\<And>x. x \<in> space M \<Longrightarrow> f ` ?p x = {f x}" by (auto intro!: imageI)
    have "(\<lambda>A. (the_elem (f ` A), A)) ` ?p ` space M
      = (\<lambda>x. (f x, ?p x)) ` space M"
    proof safe
      fix x assume "x \<in> space M"
      thus "(f x, ?p x) \<in> (\<lambda>A. (the_elem (f`A), A)) ` ?p ` space M"
        by (auto intro!: image_eqI[of _ _ "?p x"])
    qed auto
    thus ?thesis
      apply (auto intro!: setsum_reindex_cong[of "\<lambda>A. (the_elem (f`A), A)"] inj_onI)
      apply (rule_tac x="xa" in image_eqI)
      by simp_all
  qed
  finally show ?thesis .
qed

lemma (in measure_space) simple_integral_add[simp]:
  assumes f: "simple_function M f" and "\<And>x. 0 \<le> f x" and g: "simple_function M g" and "\<And>x. 0 \<le> g x"
  shows "(\<integral>\<^isup>Sx. f x + g x \<partial>M) = integral\<^isup>S M f + integral\<^isup>S M g"
proof -
  { fix x let ?S = "g -` {g x} \<inter> f -` {f x} \<inter> space M"
    assume "x \<in> space M"
    hence "(\<lambda>a. f a + g a) ` ?S = {f x + g x}" "f ` ?S = {f x}" "g ` ?S = {g x}"
        "(\<lambda>x. (f x, g x)) -` {(f x, g x)} \<inter> space M = ?S"
      by auto }
  with assms show ?thesis
    unfolding
      simple_function_partition[OF simple_function_add[OF f g] simple_function_Pair[OF f g]]
      simple_function_partition[OF f g]
      simple_function_partition[OF g f]
    by (subst (3) Int_commute)
       (auto simp add: ereal_left_distrib setsum_addf[symmetric] intro!: setsum_cong)
qed

lemma (in measure_space) simple_integral_setsum[simp]:
  assumes "\<And>i x. i \<in> P \<Longrightarrow> 0 \<le> f i x"
  assumes "\<And>i. i \<in> P \<Longrightarrow> simple_function M (f i)"
  shows "(\<integral>\<^isup>Sx. (\<Sum>i\<in>P. f i x) \<partial>M) = (\<Sum>i\<in>P. integral\<^isup>S M (f i))"
proof cases
  assume "finite P"
  from this assms show ?thesis
    by induct (auto simp: simple_function_setsum simple_integral_add setsum_nonneg)
qed auto

lemma (in measure_space) simple_integral_mult[simp]:
  assumes f: "simple_function M f" "\<And>x. 0 \<le> f x"
  shows "(\<integral>\<^isup>Sx. c * f x \<partial>M) = c * integral\<^isup>S M f"
proof -
  note mult = simple_function_mult[OF simple_function_const[of c] f(1)]
  { fix x let ?S = "f -` {f x} \<inter> (\<lambda>x. c * f x) -` {c * f x} \<inter> space M"
    assume "x \<in> space M"
    hence "(\<lambda>x. c * f x) ` ?S = {c * f x}" "f ` ?S = {f x}"
      by auto }
  with assms show ?thesis
    unfolding simple_function_partition[OF mult f(1)]
              simple_function_partition[OF f(1) mult]
    by (subst setsum_ereal_right_distrib)
       (auto intro!: ereal_0_le_mult setsum_cong simp: mult_assoc)
qed

lemma (in measure_space) simple_integral_mono_AE:
  assumes f: "simple_function M f" and g: "simple_function M g"
  and mono: "AE x. f x \<le> g x"
  shows "integral\<^isup>S M f \<le> integral\<^isup>S M g"
proof -
  let ?S = "\<lambda>x. (g -` {g x} \<inter> space M) \<inter> (f -` {f x} \<inter> space M)"
  have *: "\<And>x. g -` {g x} \<inter> f -` {f x} \<inter> space M = ?S x"
    "\<And>x. f -` {f x} \<inter> g -` {g x} \<inter> space M = ?S x" by auto
  show ?thesis
    unfolding *
      simple_function_partition[OF f g]
      simple_function_partition[OF g f]
  proof (safe intro!: setsum_mono)
    fix x assume "x \<in> space M"
    then have *: "f ` ?S x = {f x}" "g ` ?S x = {g x}" by auto
    show "the_elem (f`?S x) * \<mu> (?S x) \<le> the_elem (g`?S x) * \<mu> (?S x)"
    proof (cases "f x \<le> g x")
      case True then show ?thesis
        using * assms(1,2)[THEN simple_functionD(2)]
        by (auto intro!: ereal_mult_right_mono)
    next
      case False
      obtain N where N: "{x\<in>space M. \<not> f x \<le> g x} \<subseteq> N" "N \<in> sets M" "\<mu> N = 0"
        using mono by (auto elim!: AE_E)
      have "?S x \<subseteq> N" using N `x \<in> space M` False by auto
      moreover have "?S x \<in> sets M" using assms
        by (rule_tac Int) (auto intro!: simple_functionD)
      ultimately have "\<mu> (?S x) \<le> \<mu> N"
        using `N \<in> sets M` by (auto intro!: measure_mono)
      moreover have "0 \<le> \<mu> (?S x)"
        using assms(1,2)[THEN simple_functionD(2)] by auto
      ultimately have "\<mu> (?S x) = 0" using `\<mu> N = 0` by auto
      then show ?thesis by simp
    qed
  qed
qed

lemma (in measure_space) simple_integral_mono:
  assumes "simple_function M f" and "simple_function M g"
  and mono: "\<And> x. x \<in> space M \<Longrightarrow> f x \<le> g x"
  shows "integral\<^isup>S M f \<le> integral\<^isup>S M g"
  using assms by (intro simple_integral_mono_AE) auto

lemma (in measure_space) simple_integral_cong_AE:
  assumes "simple_function M f" and "simple_function M g"
  and "AE x. f x = g x"
  shows "integral\<^isup>S M f = integral\<^isup>S M g"
  using assms by (auto simp: eq_iff intro!: simple_integral_mono_AE)

lemma (in measure_space) simple_integral_cong':
  assumes sf: "simple_function M f" "simple_function M g"
  and mea: "\<mu> {x\<in>space M. f x \<noteq> g x} = 0"
  shows "integral\<^isup>S M f = integral\<^isup>S M g"
proof (intro simple_integral_cong_AE sf AE_I)
  show "\<mu> {x\<in>space M. f x \<noteq> g x} = 0" by fact
  show "{x \<in> space M. f x \<noteq> g x} \<in> sets M"
    using sf[THEN borel_measurable_simple_function] by auto
qed simp

lemma (in measure_space) simple_integral_indicator:
  assumes "A \<in> sets M"
  assumes "simple_function M f"
  shows "(\<integral>\<^isup>Sx. f x * indicator A x \<partial>M) =
    (\<Sum>x \<in> f ` space M. x * \<mu> (f -` {x} \<inter> space M \<inter> A))"
proof cases
  assume "A = space M"
  moreover hence "(\<integral>\<^isup>Sx. f x * indicator A x \<partial>M) = integral\<^isup>S M f"
    by (auto intro!: simple_integral_cong)
  moreover have "\<And>X. X \<inter> space M \<inter> space M = X \<inter> space M" by auto
  ultimately show ?thesis by (simp add: simple_integral_def)
next
  assume "A \<noteq> space M"
  then obtain x where x: "x \<in> space M" "x \<notin> A" using sets_into_space[OF assms(1)] by auto
  have I: "(\<lambda>x. f x * indicator A x) ` space M = f ` A \<union> {0}" (is "?I ` _ = _")
  proof safe
    fix y assume "?I y \<notin> f ` A" hence "y \<notin> A" by auto thus "?I y = 0" by auto
  next
    fix y assume "y \<in> A" thus "f y \<in> ?I ` space M"
      using sets_into_space[OF assms(1)] by (auto intro!: image_eqI[of _ _ y])
  next
    show "0 \<in> ?I ` space M" using x by (auto intro!: image_eqI[of _ _ x])
  qed
  have *: "(\<integral>\<^isup>Sx. f x * indicator A x \<partial>M) =
    (\<Sum>x \<in> f ` space M \<union> {0}. x * \<mu> (f -` {x} \<inter> space M \<inter> A))"
    unfolding simple_integral_def I
  proof (rule setsum_mono_zero_cong_left)
    show "finite (f ` space M \<union> {0})"
      using assms(2) unfolding simple_function_def by auto
    show "f ` A \<union> {0} \<subseteq> f`space M \<union> {0}"
      using sets_into_space[OF assms(1)] by auto
    have "\<And>x. f x \<notin> f ` A \<Longrightarrow> f -` {f x} \<inter> space M \<inter> A = {}"
      by (auto simp: image_iff)
    thus "\<forall>i\<in>f ` space M \<union> {0} - (f ` A \<union> {0}).
      i * \<mu> (f -` {i} \<inter> space M \<inter> A) = 0" by auto
  next
    fix x assume "x \<in> f`A \<union> {0}"
    hence "x \<noteq> 0 \<Longrightarrow> ?I -` {x} \<inter> space M = f -` {x} \<inter> space M \<inter> A"
      by (auto simp: indicator_def split: split_if_asm)
    thus "x * \<mu> (?I -` {x} \<inter> space M) =
      x * \<mu> (f -` {x} \<inter> space M \<inter> A)" by (cases "x = 0") simp_all
  qed
  show ?thesis unfolding *
    using assms(2) unfolding simple_function_def
    by (auto intro!: setsum_mono_zero_cong_right)
qed

lemma (in measure_space) simple_integral_indicator_only[simp]:
  assumes "A \<in> sets M"
  shows "integral\<^isup>S M (indicator A) = \<mu> A"
proof cases
  assume "space M = {}" hence "A = {}" using sets_into_space[OF assms] by auto
  thus ?thesis unfolding simple_integral_def using `space M = {}` by auto
next
  assume "space M \<noteq> {}" hence "(\<lambda>x. 1) ` space M = {1::ereal}" by auto
  thus ?thesis
    using simple_integral_indicator[OF assms simple_function_const[of 1]]
    using sets_into_space[OF assms]
    by (auto intro!: arg_cong[where f="\<mu>"])
qed

lemma (in measure_space) simple_integral_null_set:
  assumes "simple_function M u" "\<And>x. 0 \<le> u x" and "N \<in> null_sets"
  shows "(\<integral>\<^isup>Sx. u x * indicator N x \<partial>M) = 0"
proof -
  have "AE x. indicator N x = (0 :: ereal)"
    using `N \<in> null_sets` by (auto simp: indicator_def intro!: AE_I[of _ N])
  then have "(\<integral>\<^isup>Sx. u x * indicator N x \<partial>M) = (\<integral>\<^isup>Sx. 0 \<partial>M)"
    using assms apply (intro simple_integral_cong_AE) by auto
  then show ?thesis by simp
qed

lemma (in measure_space) simple_integral_cong_AE_mult_indicator:
  assumes sf: "simple_function M f" and eq: "AE x. x \<in> S" and "S \<in> sets M"
  shows "integral\<^isup>S M f = (\<integral>\<^isup>Sx. f x * indicator S x \<partial>M)"
  using assms by (intro simple_integral_cong_AE) auto

lemma (in measure_space) simple_integral_restricted:
  assumes "A \<in> sets M"
  assumes sf: "simple_function M (\<lambda>x. f x * indicator A x)"
  shows "integral\<^isup>S (restricted_space A) f = (\<integral>\<^isup>Sx. f x * indicator A x \<partial>M)"
    (is "_ = integral\<^isup>S M ?f")
  unfolding simple_integral_def
proof (simp, safe intro!: setsum_mono_zero_cong_left)
  from sf show "finite (?f ` space M)"
    unfolding simple_function_def by auto
next
  fix x assume "x \<in> A"
  then show "f x \<in> ?f ` space M"
    using sets_into_space `A \<in> sets M` by (auto intro!: image_eqI[of _ _ x])
next
  fix x assume "x \<in> space M" "?f x \<notin> f`A"
  then have "x \<notin> A" by (auto simp: image_iff)
  then show "?f x * \<mu> (?f -` {?f x} \<inter> space M) = 0" by simp
next
  fix x assume "x \<in> A"
  then have "f x \<noteq> 0 \<Longrightarrow>
    f -` {f x} \<inter> A = ?f -` {f x} \<inter> space M"
    using `A \<in> sets M` sets_into_space
    by (auto simp: indicator_def split: split_if_asm)
  then show "f x * \<mu> (f -` {f x} \<inter> A) =
    f x * \<mu> (?f -` {f x} \<inter> space M)"
    unfolding ereal_mult_cancel_left by auto
qed

lemma (in measure_space) simple_integral_subalgebra:
  assumes N: "measure_space N" and [simp]: "space N = space M" "measure N = measure M"
  shows "integral\<^isup>S N = integral\<^isup>S M"
  unfolding simple_integral_def_raw by simp

lemma (in measure_space) simple_integral_vimage:
  assumes T: "sigma_algebra M'" "T \<in> measure_preserving M M'"
    and f: "simple_function M' f"
  shows "integral\<^isup>S M' f = (\<integral>\<^isup>S x. f (T x) \<partial>M)"
proof -
  interpret T: measure_space M' by (rule measure_space_vimage[OF T])
  show "integral\<^isup>S M' f = (\<integral>\<^isup>S x. f (T x) \<partial>M)"
    unfolding simple_integral_def
  proof (intro setsum_mono_zero_cong_right ballI)
    show "(\<lambda>x. f (T x)) ` space M \<subseteq> f ` space M'"
      using T unfolding measurable_def measure_preserving_def by auto
    show "finite (f ` space M')"
      using f unfolding simple_function_def by auto
  next
    fix i assume "i \<in> f ` space M' - (\<lambda>x. f (T x)) ` space M"
    then have "T -` (f -` {i} \<inter> space M') \<inter> space M = {}" by (auto simp: image_iff)
    with f[THEN T.simple_functionD(2), THEN measure_preservingD[OF T(2)], of "{i}"]
    show "i * T.\<mu> (f -` {i} \<inter> space M') = 0" by simp
  next
    fix i assume "i \<in> (\<lambda>x. f (T x)) ` space M"
    then have "T -` (f -` {i} \<inter> space M') \<inter> space M = (\<lambda>x. f (T x)) -` {i} \<inter> space M"
      using T unfolding measurable_def measure_preserving_def by auto
    with f[THEN T.simple_functionD(2), THEN measure_preservingD[OF T(2)], of "{i}"]
    show "i * T.\<mu> (f -` {i} \<inter> space M') = i * \<mu> ((\<lambda>x. f (T x)) -` {i} \<inter> space M)"
      by auto
  qed
qed

lemma (in measure_space) simple_integral_cmult_indicator:
  assumes A: "A \<in> sets M"
  shows "(\<integral>\<^isup>Sx. c * indicator A x \<partial>M) = c * \<mu> A"
  using simple_integral_mult[OF simple_function_indicator[OF A]]
  unfolding simple_integral_indicator_only[OF A] by simp

lemma (in measure_space) simple_integral_positive:
  assumes f: "simple_function M f" and ae: "AE x. 0 \<le> f x"
  shows "0 \<le> integral\<^isup>S M f"
proof -
  have "integral\<^isup>S M (\<lambda>x. 0) \<le> integral\<^isup>S M f"
    using simple_integral_mono_AE[OF _ f ae] by auto
  then show ?thesis by simp
qed

section "Continuous positive integration"

definition positive_integral_def:
  "integral\<^isup>P M f = (SUP g : {g. simple_function M g \<and> g \<le> max 0 \<circ> f}. integral\<^isup>S M g)"

syntax
  "_positive_integral" :: "pttrn \<Rightarrow> ereal \<Rightarrow> ('a, 'b) measure_space_scheme \<Rightarrow> ereal" ("\<integral>\<^isup>+ _. _ \<partial>_" [60,61] 110)

translations
  "\<integral>\<^isup>+ x. f \<partial>M" == "CONST integral\<^isup>P M (%x. f)"

lemma (in measure_space) positive_integral_cong_measure:
  assumes "\<And>A. A \<in> sets M \<Longrightarrow> measure N A = \<mu> A" "sets N = sets M" "space N = space M"
  shows "integral\<^isup>P N f = integral\<^isup>P M f"
  unfolding positive_integral_def
  unfolding simple_function_cong_algebra[OF assms(2,3), symmetric]
  using AE_cong_measure[OF assms]
  using simple_integral_cong_measure[OF assms]
  by (auto intro!: SUP_cong)

lemma (in measure_space) positive_integral_positive:
  "0 \<le> integral\<^isup>P M f"
  by (auto intro!: SUP_upper2[of "\<lambda>x. 0"] simp: positive_integral_def le_fun_def)

lemma (in measure_space) positive_integral_def_finite:
  "integral\<^isup>P M f = (SUP g : {g. simple_function M g \<and> g \<le> max 0 \<circ> f \<and> range g \<subseteq> {0 ..< \<infinity>}}. integral\<^isup>S M g)"
    (is "_ = SUPR ?A ?f")
  unfolding positive_integral_def
proof (safe intro!: antisym SUP_least)
  fix g assume g: "simple_function M g" "g \<le> max 0 \<circ> f"
  let ?G = "{x \<in> space M. \<not> g x \<noteq> \<infinity>}"
  note gM = g(1)[THEN borel_measurable_simple_function]
  have \<mu>G_pos: "0 \<le> \<mu> ?G" using gM by auto
  let ?g = "\<lambda>y x. if g x = \<infinity> then y else max 0 (g x)"
  from g gM have g_in_A: "\<And>y. 0 \<le> y \<Longrightarrow> y \<noteq> \<infinity> \<Longrightarrow> ?g y \<in> ?A"
    apply (safe intro!: simple_function_max simple_function_If)
    apply (force simp: max_def le_fun_def split: split_if_asm)+
    done
  show "integral\<^isup>S M g \<le> SUPR ?A ?f"
  proof cases
    have g0: "?g 0 \<in> ?A" by (intro g_in_A) auto
    assume "\<mu> ?G = 0"
    with gM have "AE x. x \<notin> ?G" by (simp add: AE_iff_null_set)
    with gM g show ?thesis
      by (intro SUP_upper2[OF g0] simple_integral_mono_AE)
         (auto simp: max_def intro!: simple_function_If)
  next
    assume \<mu>G: "\<mu> ?G \<noteq> 0"
    have "SUPR ?A (integral\<^isup>S M) = \<infinity>"
    proof (intro SUP_PInfty)
      fix n :: nat
      let ?y = "ereal (real n) / (if \<mu> ?G = \<infinity> then 1 else \<mu> ?G)"
      have "0 \<le> ?y" "?y \<noteq> \<infinity>" using \<mu>G \<mu>G_pos by (auto simp: ereal_divide_eq)
      then have "?g ?y \<in> ?A" by (rule g_in_A)
      have "real n \<le> ?y * \<mu> ?G"
        using \<mu>G \<mu>G_pos by (cases "\<mu> ?G") (auto simp: field_simps)
      also have "\<dots> = (\<integral>\<^isup>Sx. ?y * indicator ?G x \<partial>M)"
        using `0 \<le> ?y` `?g ?y \<in> ?A` gM
        by (subst simple_integral_cmult_indicator) auto
      also have "\<dots> \<le> integral\<^isup>S M (?g ?y)" using `?g ?y \<in> ?A` gM
        by (intro simple_integral_mono) auto
      finally show "\<exists>i\<in>?A. real n \<le> integral\<^isup>S M i"
        using `?g ?y \<in> ?A` by blast
    qed
    then show ?thesis by simp
  qed
qed (auto intro: SUP_upper)

lemma (in measure_space) positive_integral_mono_AE:
  assumes ae: "AE x. u x \<le> v x" shows "integral\<^isup>P M u \<le> integral\<^isup>P M v"
  unfolding positive_integral_def
proof (safe intro!: SUP_mono)
  fix n assume n: "simple_function M n" "n \<le> max 0 \<circ> u"
  from ae[THEN AE_E] guess N . note N = this
  then have ae_N: "AE x. x \<notin> N" by (auto intro: AE_not_in)
  let ?n = "\<lambda>x. n x * indicator (space M - N) x"
  have "AE x. n x \<le> ?n x" "simple_function M ?n"
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
  moreover have "integral\<^isup>S M n \<le> integral\<^isup>S M ?n"
    using ae_N N n by (auto intro!: simple_integral_mono_AE)
  ultimately show "\<exists>m\<in>{g. simple_function M g \<and> g \<le> max 0 \<circ> v}. integral\<^isup>S M n \<le> integral\<^isup>S M m"
    by force
qed

lemma (in measure_space) positive_integral_mono:
  "(\<And>x. x \<in> space M \<Longrightarrow> u x \<le> v x) \<Longrightarrow> integral\<^isup>P M u \<le> integral\<^isup>P M v"
  by (auto intro: positive_integral_mono_AE)

lemma (in measure_space) positive_integral_cong_AE:
  "AE x. u x = v x \<Longrightarrow> integral\<^isup>P M u = integral\<^isup>P M v"
  by (auto simp: eq_iff intro!: positive_integral_mono_AE)

lemma (in measure_space) positive_integral_cong:
  "(\<And>x. x \<in> space M \<Longrightarrow> u x = v x) \<Longrightarrow> integral\<^isup>P M u = integral\<^isup>P M v"
  by (auto intro: positive_integral_cong_AE)

lemma (in measure_space) positive_integral_eq_simple_integral:
  assumes f: "simple_function M f" "\<And>x. 0 \<le> f x" shows "integral\<^isup>P M f = integral\<^isup>S M f"
proof -
  let ?f = "\<lambda>x. f x * indicator (space M) x"
  have f': "simple_function M ?f" using f by auto
  with f(2) have [simp]: "max 0 \<circ> ?f = ?f"
    by (auto simp: fun_eq_iff max_def split: split_indicator)
  have "integral\<^isup>P M ?f \<le> integral\<^isup>S M ?f" using f'
    by (force intro!: SUP_least simple_integral_mono simp: le_fun_def positive_integral_def)
  moreover have "integral\<^isup>S M ?f \<le> integral\<^isup>P M ?f"
    unfolding positive_integral_def
    using f' by (auto intro!: SUP_upper)
  ultimately show ?thesis
    by (simp cong: positive_integral_cong simple_integral_cong)
qed

lemma (in measure_space) positive_integral_eq_simple_integral_AE:
  assumes f: "simple_function M f" "AE x. 0 \<le> f x" shows "integral\<^isup>P M f = integral\<^isup>S M f"
proof -
  have "AE x. f x = max 0 (f x)" using f by (auto split: split_max)
  with f have "integral\<^isup>P M f = integral\<^isup>S M (\<lambda>x. max 0 (f x))"
    by (simp cong: positive_integral_cong_AE simple_integral_cong_AE
             add: positive_integral_eq_simple_integral)
  with assms show ?thesis
    by (auto intro!: simple_integral_cong_AE split: split_max)
qed

lemma (in measure_space) positive_integral_SUP_approx:
  assumes f: "incseq f" "\<And>i. f i \<in> borel_measurable M" "\<And>i x. 0 \<le> f i x"
  and u: "simple_function M u" "u \<le> (SUP i. f i)" "u`space M \<subseteq> {0..<\<infinity>}"
  shows "integral\<^isup>S M u \<le> (SUP i. integral\<^isup>P M (f i))" (is "_ \<le> ?S")
proof (rule ereal_le_mult_one_interval)
  have "0 \<le> (SUP i. integral\<^isup>P M (f i))"
    using f(3) by (auto intro!: SUP_upper2 positive_integral_positive)
  then show "(SUP i. integral\<^isup>P M (f i)) \<noteq> -\<infinity>" by auto
  have u_range: "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> u x \<and> u x \<noteq> \<infinity>"
    using u(3) by auto
  fix a :: ereal assume "0 < a" "a < 1"
  hence "a \<noteq> 0" by auto
  let ?B = "\<lambda>i. {x \<in> space M. a * u x \<le> f i x}"
  have B: "\<And>i. ?B i \<in> sets M"
    using f `simple_function M u` by (auto simp: borel_measurable_simple_function)

  let ?uB = "\<lambda>i x. u x * indicator (?B i) x"

  { fix i have "?B i \<subseteq> ?B (Suc i)"
    proof safe
      fix i x assume "a * u x \<le> f i x"
      also have "\<dots> \<le> f (Suc i) x"
        using `incseq f`[THEN incseq_SucD] unfolding le_fun_def by auto
      finally show "a * u x \<le> f (Suc i) x" .
    qed }
  note B_mono = this

  note B_u = Int[OF u(1)[THEN simple_functionD(2)] B]

  let ?B' = "\<lambda>i n. (u -` {i} \<inter> space M) \<inter> ?B n"
  have measure_conv: "\<And>i. \<mu> (u -` {i} \<inter> space M) = (SUP n. \<mu> (?B' i n))"
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
        also have "\<dots> \<le> (SUP i. f i x)" using u(2) by (auto simp: le_fun_def SUP_apply)
        finally obtain i where "a * u x < f i x" unfolding SUP_def
          by (auto simp add: less_Sup_iff)
        hence "a * u x \<le> f i x" by auto
        thus ?thesis using `x \<in> space M` by auto
      qed
    qed
    then show "?thesis i" using continuity_from_below[OF 1 2] by simp
  qed

  have "integral\<^isup>S M u = (SUP i. integral\<^isup>S M (?uB i))"
    unfolding simple_integral_indicator[OF B `simple_function M u`]
  proof (subst SUPR_ereal_setsum, safe)
    fix x n assume "x \<in> space M"
    with u_range show "incseq (\<lambda>i. u x * \<mu> (?B' (u x) i))" "\<And>i. 0 \<le> u x * \<mu> (?B' (u x) i)"
      using B_mono B_u by (auto intro!: measure_mono ereal_mult_left_mono incseq_SucI simp: ereal_zero_le_0_iff)
  next
    show "integral\<^isup>S M u = (\<Sum>i\<in>u ` space M. SUP n. i * \<mu> (?B' i n))"
      using measure_conv u_range B_u unfolding simple_integral_def
      by (auto intro!: setsum_cong SUPR_ereal_cmult[symmetric])
  qed
  moreover
  have "a * (SUP i. integral\<^isup>S M (?uB i)) \<le> ?S"
    apply (subst SUPR_ereal_cmult[symmetric])
  proof (safe intro!: SUP_mono bexI)
    fix i
    have "a * integral\<^isup>S M (?uB i) = (\<integral>\<^isup>Sx. a * ?uB i x \<partial>M)"
      using B `simple_function M u` u_range
      by (subst simple_integral_mult) (auto split: split_indicator)
    also have "\<dots> \<le> integral\<^isup>P M (f i)"
    proof -
      have *: "simple_function M (\<lambda>x. a * ?uB i x)" using B `0 < a` u(1) by auto
      show ?thesis using f(3) * u_range `0 < a`
        by (subst positive_integral_eq_simple_integral[symmetric])
           (auto intro!: positive_integral_mono split: split_indicator)
    qed
    finally show "a * integral\<^isup>S M (?uB i) \<le> integral\<^isup>P M (f i)"
      by auto
  next
    fix i show "0 \<le> \<integral>\<^isup>S x. ?uB i x \<partial>M" using B `0 < a` u(1) u_range
      by (intro simple_integral_positive) (auto split: split_indicator)
  qed (insert `0 < a`, auto)
  ultimately show "a * integral\<^isup>S M u \<le> ?S" by simp
qed

lemma (in measure_space) incseq_positive_integral:
  assumes "incseq f" shows "incseq (\<lambda>i. integral\<^isup>P M (f i))"
proof -
  have "\<And>i x. f i x \<le> f (Suc i) x"
    using assms by (auto dest!: incseq_SucD simp: le_fun_def)
  then show ?thesis
    by (auto intro!: incseq_SucI positive_integral_mono)
qed

text {* Beppo-Levi monotone convergence theorem *}
lemma (in measure_space) positive_integral_monotone_convergence_SUP:
  assumes f: "incseq f" "\<And>i. f i \<in> borel_measurable M" "\<And>i x. 0 \<le> f i x"
  shows "(\<integral>\<^isup>+ x. (SUP i. f i x) \<partial>M) = (SUP i. integral\<^isup>P M (f i))"
proof (rule antisym)
  show "(SUP j. integral\<^isup>P M (f j)) \<le> (\<integral>\<^isup>+ x. (SUP i. f i x) \<partial>M)"
    by (auto intro!: SUP_least SUP_upper positive_integral_mono)
next
  show "(\<integral>\<^isup>+ x. (SUP i. f i x) \<partial>M) \<le> (SUP j. integral\<^isup>P M (f j))"
    unfolding positive_integral_def_finite[of "\<lambda>x. SUP i. f i x"]
  proof (safe intro!: SUP_least)
    fix g assume g: "simple_function M g"
      and "g \<le> max 0 \<circ> (\<lambda>x. SUP i. f i x)" "range g \<subseteq> {0..<\<infinity>}"
    moreover then have "\<And>x. 0 \<le> (SUP i. f i x)" and g': "g`space M \<subseteq> {0..<\<infinity>}"
      using f by (auto intro!: SUP_upper2)
    ultimately show "integral\<^isup>S M g \<le> (SUP j. integral\<^isup>P M (f j))"
      by (intro  positive_integral_SUP_approx[OF f g _ g'])
         (auto simp: le_fun_def max_def SUP_apply)
  qed
qed

lemma (in measure_space) positive_integral_monotone_convergence_SUP_AE:
  assumes f: "\<And>i. AE x. f i x \<le> f (Suc i) x \<and> 0 \<le> f i x" "\<And>i. f i \<in> borel_measurable M"
  shows "(\<integral>\<^isup>+ x. (SUP i. f i x) \<partial>M) = (SUP i. integral\<^isup>P M (f i))"
proof -
  from f have "AE x. \<forall>i. f i x \<le> f (Suc i) x \<and> 0 \<le> f i x"
    by (simp add: AE_all_countable)
  from this[THEN AE_E] guess N . note N = this
  let ?f = "\<lambda>i x. if x \<in> space M - N then f i x else 0"
  have f_eq: "AE x. \<forall>i. ?f i x = f i x" using N by (auto intro!: AE_I[of _ N])
  then have "(\<integral>\<^isup>+ x. (SUP i. f i x) \<partial>M) = (\<integral>\<^isup>+ x. (SUP i. ?f i x) \<partial>M)"
    by (auto intro!: positive_integral_cong_AE)
  also have "\<dots> = (SUP i. (\<integral>\<^isup>+ x. ?f i x \<partial>M))"
  proof (rule positive_integral_monotone_convergence_SUP)
    show "incseq ?f" using N(1) by (force intro!: incseq_SucI le_funI)
    { fix i show "(\<lambda>x. if x \<in> space M - N then f i x else 0) \<in> borel_measurable M"
        using f N(3) by (intro measurable_If_set) auto
      fix x show "0 \<le> ?f i x"
        using N(1) by auto }
  qed
  also have "\<dots> = (SUP i. (\<integral>\<^isup>+ x. f i x \<partial>M))"
    using f_eq by (force intro!: arg_cong[where f="SUPR UNIV"] positive_integral_cong_AE ext)
  finally show ?thesis .
qed

lemma (in measure_space) positive_integral_monotone_convergence_SUP_AE_incseq:
  assumes f: "incseq f" "\<And>i. AE x. 0 \<le> f i x" and borel: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<integral>\<^isup>+ x. (SUP i. f i x) \<partial>M) = (SUP i. integral\<^isup>P M (f i))"
  using f[unfolded incseq_Suc_iff le_fun_def]
  by (intro positive_integral_monotone_convergence_SUP_AE[OF _ borel])
     auto

lemma (in measure_space) positive_integral_monotone_convergence_simple:
  assumes f: "incseq f" "\<And>i x. 0 \<le> f i x" "\<And>i. simple_function M (f i)"
  shows "(SUP i. integral\<^isup>S M (f i)) = (\<integral>\<^isup>+x. (SUP i. f i x) \<partial>M)"
  using assms unfolding positive_integral_monotone_convergence_SUP[OF f(1)
    f(3)[THEN borel_measurable_simple_function] f(2)]
  by (auto intro!: positive_integral_eq_simple_integral[symmetric] arg_cong[where f="SUPR UNIV"] ext)

lemma positive_integral_max_0:
  "(\<integral>\<^isup>+x. max 0 (f x) \<partial>M) = integral\<^isup>P M f"
  by (simp add: le_fun_def positive_integral_def)

lemma (in measure_space) positive_integral_cong_pos:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> f x \<le> 0 \<and> g x \<le> 0 \<or> f x = g x"
  shows "integral\<^isup>P M f = integral\<^isup>P M g"
proof -
  have "integral\<^isup>P M (\<lambda>x. max 0 (f x)) = integral\<^isup>P M (\<lambda>x. max 0 (g x))"
  proof (intro positive_integral_cong)
    fix x assume "x \<in> space M"
    from assms[OF this] show "max 0 (f x) = max 0 (g x)"
      by (auto split: split_max)
  qed
  then show ?thesis by (simp add: positive_integral_max_0)
qed

lemma (in measure_space) SUP_simple_integral_sequences:
  assumes f: "incseq f" "\<And>i x. 0 \<le> f i x" "\<And>i. simple_function M (f i)"
  and g: "incseq g" "\<And>i x. 0 \<le> g i x" "\<And>i. simple_function M (g i)"
  and eq: "AE x. (SUP i. f i x) = (SUP i. g i x)"
  shows "(SUP i. integral\<^isup>S M (f i)) = (SUP i. integral\<^isup>S M (g i))"
    (is "SUPR _ ?F = SUPR _ ?G")
proof -
  have "(SUP i. integral\<^isup>S M (f i)) = (\<integral>\<^isup>+x. (SUP i. f i x) \<partial>M)"
    using f by (rule positive_integral_monotone_convergence_simple)
  also have "\<dots> = (\<integral>\<^isup>+x. (SUP i. g i x) \<partial>M)"
    unfolding eq[THEN positive_integral_cong_AE] ..
  also have "\<dots> = (SUP i. ?G i)"
    using g by (rule positive_integral_monotone_convergence_simple[symmetric])
  finally show ?thesis by simp
qed

lemma (in measure_space) positive_integral_const[simp]:
  "0 \<le> c \<Longrightarrow> (\<integral>\<^isup>+ x. c \<partial>M) = c * \<mu> (space M)"
  by (subst positive_integral_eq_simple_integral) auto

lemma (in measure_space) positive_integral_vimage:
  assumes T: "sigma_algebra M'" "T \<in> measure_preserving M M'"
  and f: "f \<in> borel_measurable M'"
  shows "integral\<^isup>P M' f = (\<integral>\<^isup>+ x. f (T x) \<partial>M)"
proof -
  interpret T: measure_space M' by (rule measure_space_vimage[OF T])
  from T.borel_measurable_implies_simple_function_sequence'[OF f]
  guess f' . note f' = this
  let ?f = "\<lambda>i x. f' i (T x)"
  have inc: "incseq ?f" using f' by (force simp: le_fun_def incseq_def)
  have sup: "\<And>x. (SUP i. ?f i x) = max 0 (f (T x))"
    using f'(4) .
  have sf: "\<And>i. simple_function M (\<lambda>x. f' i (T x))"
    using simple_function_vimage[OF T(1) measure_preservingD2[OF T(2)] f'(1)] .
  show "integral\<^isup>P M' f = (\<integral>\<^isup>+ x. f (T x) \<partial>M)"
    using
      T.positive_integral_monotone_convergence_simple[OF f'(2,5,1)]
      positive_integral_monotone_convergence_simple[OF inc f'(5) sf]
    by (simp add: positive_integral_max_0 simple_integral_vimage[OF T f'(1)] f')
qed

lemma (in measure_space) positive_integral_linear:
  assumes f: "f \<in> borel_measurable M" "\<And>x. 0 \<le> f x" and "0 \<le> a"
  and g: "g \<in> borel_measurable M" "\<And>x. 0 \<le> g x"
  shows "(\<integral>\<^isup>+ x. a * f x + g x \<partial>M) = a * integral\<^isup>P M f + integral\<^isup>P M g"
    (is "integral\<^isup>P M ?L = _")
proof -
  from borel_measurable_implies_simple_function_sequence'[OF f(1)] guess u .
  note u = positive_integral_monotone_convergence_simple[OF this(2,5,1)] this
  from borel_measurable_implies_simple_function_sequence'[OF g(1)] guess v .
  note v = positive_integral_monotone_convergence_simple[OF this(2,5,1)] this
  let ?L' = "\<lambda>i x. a * u i x + v i x"

  have "?L \<in> borel_measurable M" using assms by auto
  from borel_measurable_implies_simple_function_sequence'[OF this] guess l .
  note l = positive_integral_monotone_convergence_simple[OF this(2,5,1)] this

  have inc: "incseq (\<lambda>i. a * integral\<^isup>S M (u i))" "incseq (\<lambda>i. integral\<^isup>S M (v i))"
    using u v `0 \<le> a`
    by (auto simp: incseq_Suc_iff le_fun_def
             intro!: add_mono ereal_mult_left_mono simple_integral_mono)
  have pos: "\<And>i. 0 \<le> integral\<^isup>S M (u i)" "\<And>i. 0 \<le> integral\<^isup>S M (v i)" "\<And>i. 0 \<le> a * integral\<^isup>S M (u i)"
    using u v `0 \<le> a` by (auto simp: simple_integral_positive)
  { fix i from pos[of i] have "a * integral\<^isup>S M (u i) \<noteq> -\<infinity>" "integral\<^isup>S M (v i) \<noteq> -\<infinity>"
      by (auto split: split_if_asm) }
  note not_MInf = this

  have l': "(SUP i. integral\<^isup>S M (l i)) = (SUP i. integral\<^isup>S M (?L' i))"
  proof (rule SUP_simple_integral_sequences[OF l(3,6,2)])
    show "incseq ?L'" "\<And>i x. 0 \<le> ?L' i x" "\<And>i. simple_function M (?L' i)"
      using u v  `0 \<le> a` unfolding incseq_Suc_iff le_fun_def
      by (auto intro!: add_mono ereal_mult_left_mono ereal_add_nonneg_nonneg)
    { fix x
      { fix i have "a * u i x \<noteq> -\<infinity>" "v i x \<noteq> -\<infinity>" "u i x \<noteq> -\<infinity>" using `0 \<le> a` u(6)[of i x] v(6)[of i x]
          by auto }
      then have "(SUP i. a * u i x + v i x) = a * (SUP i. u i x) + (SUP i. v i x)"
        using `0 \<le> a` u(3) v(3) u(6)[of _ x] v(6)[of _ x]
        by (subst SUPR_ereal_cmult[symmetric, OF u(6) `0 \<le> a`])
           (auto intro!: SUPR_ereal_add
                 simp: incseq_Suc_iff le_fun_def add_mono ereal_mult_left_mono ereal_add_nonneg_nonneg) }
    then show "AE x. (SUP i. l i x) = (SUP i. ?L' i x)"
      unfolding l(5) using `0 \<le> a` u(5) v(5) l(5) f(2) g(2)
      by (intro AE_I2) (auto split: split_max simp add: ereal_add_nonneg_nonneg)
  qed
  also have "\<dots> = (SUP i. a * integral\<^isup>S M (u i) + integral\<^isup>S M (v i))"
    using u(2, 6) v(2, 6) `0 \<le> a` by (auto intro!: arg_cong[where f="SUPR UNIV"] ext)
  finally have "(\<integral>\<^isup>+ x. max 0 (a * f x + g x) \<partial>M) = a * (\<integral>\<^isup>+x. max 0 (f x) \<partial>M) + (\<integral>\<^isup>+x. max 0 (g x) \<partial>M)"
    unfolding l(5)[symmetric] u(5)[symmetric] v(5)[symmetric]
    unfolding l(1)[symmetric] u(1)[symmetric] v(1)[symmetric]
    apply (subst SUPR_ereal_cmult[symmetric, OF pos(1) `0 \<le> a`])
    apply (subst SUPR_ereal_add[symmetric, OF inc not_MInf]) .
  then show ?thesis by (simp add: positive_integral_max_0)
qed

lemma (in measure_space) positive_integral_cmult:
  assumes f: "f \<in> borel_measurable M" "AE x. 0 \<le> f x" "0 \<le> c"
  shows "(\<integral>\<^isup>+ x. c * f x \<partial>M) = c * integral\<^isup>P M f"
proof -
  have [simp]: "\<And>x. c * max 0 (f x) = max 0 (c * f x)" using `0 \<le> c`
    by (auto split: split_max simp: ereal_zero_le_0_iff)
  have "(\<integral>\<^isup>+ x. c * f x \<partial>M) = (\<integral>\<^isup>+ x. c * max 0 (f x) \<partial>M)"
    by (simp add: positive_integral_max_0)
  then show ?thesis
    using positive_integral_linear[OF _ _ `0 \<le> c`, of "\<lambda>x. max 0 (f x)" "\<lambda>x. 0"] f
    by (auto simp: positive_integral_max_0)
qed

lemma (in measure_space) positive_integral_multc:
  assumes "f \<in> borel_measurable M" "AE x. 0 \<le> f x" "0 \<le> c"
  shows "(\<integral>\<^isup>+ x. f x * c \<partial>M) = integral\<^isup>P M f * c"
  unfolding mult_commute[of _ c] positive_integral_cmult[OF assms] by simp

lemma (in measure_space) positive_integral_indicator[simp]:
  "A \<in> sets M \<Longrightarrow> (\<integral>\<^isup>+ x. indicator A x\<partial>M) = \<mu> A"
  by (subst positive_integral_eq_simple_integral)
     (auto simp: simple_function_indicator simple_integral_indicator)

lemma (in measure_space) positive_integral_cmult_indicator:
  "0 \<le> c \<Longrightarrow> A \<in> sets M \<Longrightarrow> (\<integral>\<^isup>+ x. c * indicator A x \<partial>M) = c * \<mu> A"
  by (subst positive_integral_eq_simple_integral)
     (auto simp: simple_function_indicator simple_integral_indicator)

lemma (in measure_space) positive_integral_add:
  assumes f: "f \<in> borel_measurable M" "AE x. 0 \<le> f x"
  and g: "g \<in> borel_measurable M" "AE x. 0 \<le> g x"
  shows "(\<integral>\<^isup>+ x. f x + g x \<partial>M) = integral\<^isup>P M f + integral\<^isup>P M g"
proof -
  have ae: "AE x. max 0 (f x) + max 0 (g x) = max 0 (f x + g x)"
    using assms by (auto split: split_max simp: ereal_add_nonneg_nonneg)
  have "(\<integral>\<^isup>+ x. f x + g x \<partial>M) = (\<integral>\<^isup>+ x. max 0 (f x + g x) \<partial>M)"
    by (simp add: positive_integral_max_0)
  also have "\<dots> = (\<integral>\<^isup>+ x. max 0 (f x) + max 0 (g x) \<partial>M)"
    unfolding ae[THEN positive_integral_cong_AE] ..
  also have "\<dots> = (\<integral>\<^isup>+ x. max 0 (f x) \<partial>M) + (\<integral>\<^isup>+ x. max 0 (g x) \<partial>M)"
    using positive_integral_linear[of "\<lambda>x. max 0 (f x)" 1 "\<lambda>x. max 0 (g x)"] f g
    by auto
  finally show ?thesis
    by (simp add: positive_integral_max_0)
qed

lemma (in measure_space) positive_integral_setsum:
  assumes "\<And>i. i\<in>P \<Longrightarrow> f i \<in> borel_measurable M" "\<And>i. i\<in>P \<Longrightarrow> AE x. 0 \<le> f i x"
  shows "(\<integral>\<^isup>+ x. (\<Sum>i\<in>P. f i x) \<partial>M) = (\<Sum>i\<in>P. integral\<^isup>P M (f i))"
proof cases
  assume f: "finite P"
  from assms have "AE x. \<forall>i\<in>P. 0 \<le> f i x" unfolding AE_finite_all[OF f] by auto
  from f this assms(1) show ?thesis
  proof induct
    case (insert i P)
    then have "f i \<in> borel_measurable M" "AE x. 0 \<le> f i x"
      "(\<lambda>x. \<Sum>i\<in>P. f i x) \<in> borel_measurable M" "AE x. 0 \<le> (\<Sum>i\<in>P. f i x)"
      by (auto intro!: borel_measurable_ereal_setsum setsum_nonneg)
    from positive_integral_add[OF this]
    show ?case using insert by auto
  qed simp
qed simp

lemma (in measure_space) positive_integral_Markov_inequality:
  assumes u: "u \<in> borel_measurable M" "AE x. 0 \<le> u x" and "A \<in> sets M" and c: "0 \<le> c" "c \<noteq> \<infinity>"
  shows "\<mu> ({x\<in>space M. 1 \<le> c * u x} \<inter> A) \<le> c * (\<integral>\<^isup>+ x. u x * indicator A x \<partial>M)"
    (is "\<mu> ?A \<le> _ * ?PI")
proof -
  have "?A \<in> sets M"
    using `A \<in> sets M` u by auto
  hence "\<mu> ?A = (\<integral>\<^isup>+ x. indicator ?A x \<partial>M)"
    using positive_integral_indicator by simp
  also have "\<dots> \<le> (\<integral>\<^isup>+ x. c * (u x * indicator A x) \<partial>M)" using u c
    by (auto intro!: positive_integral_mono_AE
      simp: indicator_def ereal_zero_le_0_iff)
  also have "\<dots> = c * (\<integral>\<^isup>+ x. u x * indicator A x \<partial>M)"
    using assms
    by (auto intro!: positive_integral_cmult borel_measurable_indicator simp: ereal_zero_le_0_iff)
  finally show ?thesis .
qed

lemma (in measure_space) positive_integral_noteq_infinite:
  assumes g: "g \<in> borel_measurable M" "AE x. 0 \<le> g x"
  and "integral\<^isup>P M g \<noteq> \<infinity>"
  shows "AE x. g x \<noteq> \<infinity>"
proof (rule ccontr)
  assume c: "\<not> (AE x. g x \<noteq> \<infinity>)"
  have "\<mu> {x\<in>space M. g x = \<infinity>} \<noteq> 0"
    using c g by (simp add: AE_iff_null_set)
  moreover have "0 \<le> \<mu> {x\<in>space M. g x = \<infinity>}" using g by (auto intro: measurable_sets)
  ultimately have "0 < \<mu> {x\<in>space M. g x = \<infinity>}" by auto
  then have "\<infinity> = \<infinity> * \<mu> {x\<in>space M. g x = \<infinity>}" by auto
  also have "\<dots> \<le> (\<integral>\<^isup>+x. \<infinity> * indicator {x\<in>space M. g x = \<infinity>} x \<partial>M)"
    using g by (subst positive_integral_cmult_indicator) auto
  also have "\<dots> \<le> integral\<^isup>P M g"
    using assms by (auto intro!: positive_integral_mono_AE simp: indicator_def)
  finally show False using `integral\<^isup>P M g \<noteq> \<infinity>` by auto
qed

lemma (in measure_space) positive_integral_diff:
  assumes f: "f \<in> borel_measurable M"
  and g: "g \<in> borel_measurable M" "AE x. 0 \<le> g x"
  and fin: "integral\<^isup>P M g \<noteq> \<infinity>"
  and mono: "AE x. g x \<le> f x"
  shows "(\<integral>\<^isup>+ x. f x - g x \<partial>M) = integral\<^isup>P M f - integral\<^isup>P M g"
proof -
  have diff: "(\<lambda>x. f x - g x) \<in> borel_measurable M" "AE x. 0 \<le> f x - g x"
    using assms by (auto intro: ereal_diff_positive)
  have pos_f: "AE x. 0 \<le> f x" using mono g by auto
  { fix a b :: ereal assume "0 \<le> a" "a \<noteq> \<infinity>" "0 \<le> b" "a \<le> b" then have "b - a + a = b"
      by (cases rule: ereal2_cases[of a b]) auto }
  note * = this
  then have "AE x. f x = f x - g x + g x"
    using mono positive_integral_noteq_infinite[OF g fin] assms by auto
  then have **: "integral\<^isup>P M f = (\<integral>\<^isup>+x. f x - g x \<partial>M) + integral\<^isup>P M g"
    unfolding positive_integral_add[OF diff g, symmetric]
    by (rule positive_integral_cong_AE)
  show ?thesis unfolding **
    using fin positive_integral_positive[of g]
    by (cases rule: ereal2_cases[of "\<integral>\<^isup>+ x. f x - g x \<partial>M" "integral\<^isup>P M g"]) auto
qed

lemma (in measure_space) positive_integral_suminf:
  assumes f: "\<And>i. f i \<in> borel_measurable M" "\<And>i. AE x. 0 \<le> f i x"
  shows "(\<integral>\<^isup>+ x. (\<Sum>i. f i x) \<partial>M) = (\<Sum>i. integral\<^isup>P M (f i))"
proof -
  have all_pos: "AE x. \<forall>i. 0 \<le> f i x"
    using assms by (auto simp: AE_all_countable)
  have "(\<Sum>i. integral\<^isup>P M (f i)) = (SUP n. \<Sum>i<n. integral\<^isup>P M (f i))"
    using positive_integral_positive by (rule suminf_ereal_eq_SUPR)
  also have "\<dots> = (SUP n. \<integral>\<^isup>+x. (\<Sum>i<n. f i x) \<partial>M)"
    unfolding positive_integral_setsum[OF f] ..
  also have "\<dots> = \<integral>\<^isup>+x. (SUP n. \<Sum>i<n. f i x) \<partial>M" using f all_pos
    by (intro positive_integral_monotone_convergence_SUP_AE[symmetric])
       (elim AE_mp, auto simp: setsum_nonneg simp del: setsum_lessThan_Suc intro!: AE_I2 setsum_mono3)
  also have "\<dots> = \<integral>\<^isup>+x. (\<Sum>i. f i x) \<partial>M" using all_pos
    by (intro positive_integral_cong_AE) (auto simp: suminf_ereal_eq_SUPR)
  finally show ?thesis by simp
qed

text {* Fatou's lemma: convergence theorem on limes inferior *}
lemma (in measure_space) positive_integral_lim_INF:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes u: "\<And>i. u i \<in> borel_measurable M" "\<And>i. AE x. 0 \<le> u i x"
  shows "(\<integral>\<^isup>+ x. liminf (\<lambda>n. u n x) \<partial>M) \<le> liminf (\<lambda>n. integral\<^isup>P M (u n))"
proof -
  have pos: "AE x. \<forall>i. 0 \<le> u i x" using u by (auto simp: AE_all_countable)
  have "(\<integral>\<^isup>+ x. liminf (\<lambda>n. u n x) \<partial>M) =
    (SUP n. \<integral>\<^isup>+ x. (INF i:{n..}. u i x) \<partial>M)"
    unfolding liminf_SUPR_INFI using pos u
    by (intro positive_integral_monotone_convergence_SUP_AE)
       (elim AE_mp, auto intro!: AE_I2 intro: INF_greatest INF_superset_mono)
  also have "\<dots> \<le> liminf (\<lambda>n. integral\<^isup>P M (u n))"
    unfolding liminf_SUPR_INFI
    by (auto intro!: SUP_mono exI INF_greatest positive_integral_mono INF_lower)
  finally show ?thesis .
qed

lemma (in measure_space) measure_space_density:
  assumes u: "u \<in> borel_measurable M" "AE x. 0 \<le> u x"
    and M'[simp]: "M' = (M\<lparr>measure := \<lambda>A. (\<integral>\<^isup>+ x. u x * indicator A x \<partial>M)\<rparr>)"
  shows "measure_space M'"
proof -
  interpret M': sigma_algebra M' by (intro sigma_algebra_cong) auto
  show ?thesis
  proof
    have pos: "\<And>A. AE x. 0 \<le> u x * indicator A x"
      using u by (auto simp: ereal_zero_le_0_iff)
    then show "positive M' (measure M')" unfolding M'
      using u(1) by (auto simp: positive_def intro!: positive_integral_positive)
    show "countably_additive M' (measure M')"
    proof (intro countably_additiveI)
      fix A :: "nat \<Rightarrow> 'a set" assume "range A \<subseteq> sets M'"
      then have *: "\<And>i. (\<lambda>x. u x * indicator (A i) x) \<in> borel_measurable M"
        using u by (auto intro: borel_measurable_indicator)
      assume disj: "disjoint_family A"
      have "(\<Sum>n. measure M' (A n)) = (\<integral>\<^isup>+ x. (\<Sum>n. u x * indicator (A n) x) \<partial>M)"
        unfolding M' using u(1) *
        by (simp add: positive_integral_suminf[OF _ pos, symmetric])
      also have "\<dots> = (\<integral>\<^isup>+ x. u x * (\<Sum>n. indicator (A n) x) \<partial>M)" using u
        by (intro positive_integral_cong_AE)
           (elim AE_mp, auto intro!: AE_I2 suminf_cmult_ereal)
      also have "\<dots> = (\<integral>\<^isup>+ x. u x * indicator (\<Union>n. A n) x \<partial>M)"
        unfolding suminf_indicator[OF disj] ..
      finally show "(\<Sum>n. measure M' (A n)) = measure M' (\<Union>x. A x)"
        unfolding M' by simp
    qed
  qed
qed

lemma (in measure_space) positive_integral_null_set:
  assumes "N \<in> null_sets" shows "(\<integral>\<^isup>+ x. u x * indicator N x \<partial>M) = 0"
proof -
  have "(\<integral>\<^isup>+ x. u x * indicator N x \<partial>M) = (\<integral>\<^isup>+ x. 0 \<partial>M)"
  proof (intro positive_integral_cong_AE AE_I)
    show "{x \<in> space M. u x * indicator N x \<noteq> 0} \<subseteq> N"
      by (auto simp: indicator_def)
    show "\<mu> N = 0" "N \<in> sets M"
      using assms by auto
  qed
  then show ?thesis by simp
qed

lemma (in measure_space) positive_integral_translated_density:
  assumes f: "f \<in> borel_measurable M" "AE x. 0 \<le> f x"
  assumes g: "g \<in> borel_measurable M" "AE x. 0 \<le> g x"
    and M': "M' = (M\<lparr> measure := \<lambda>A. (\<integral>\<^isup>+ x. f x * indicator A x \<partial>M)\<rparr>)"
  shows "integral\<^isup>P M' g = (\<integral>\<^isup>+ x. f x * g x \<partial>M)"
proof -
  from measure_space_density[OF f M']
  interpret T: measure_space M' .
  have borel[simp]:
    "borel_measurable M' = borel_measurable M"
    "simple_function M' = simple_function M"
    unfolding measurable_def simple_function_def_raw by (auto simp: M')
  from borel_measurable_implies_simple_function_sequence'[OF g(1)] guess G . note G = this
  note G' = borel_measurable_simple_function[OF this(1)] simple_functionD[OF G(1)]
  note G'(2)[simp]
  { fix P have "AE x. P x \<Longrightarrow> AE x in M'. P x"
      using positive_integral_null_set[of _ f]
      unfolding T.almost_everywhere_def almost_everywhere_def
      by (auto simp: M') }
  note ac = this
  from G(4) g(2) have G_M': "AE x in M'. (SUP i. G i x) = g x"
    by (auto intro!: ac split: split_max)
  { fix i
    let ?I = "\<lambda>y x. indicator (G i -` {y} \<inter> space M) x"
    { fix x assume *: "x \<in> space M" "0 \<le> f x" "0 \<le> g x"
      then have [simp]: "G i ` space M \<inter> {y. G i x = y \<and> x \<in> space M} = {G i x}" by auto
      from * G' G have "(\<Sum>y\<in>G i`space M. y * (f x * ?I y x)) = f x * (\<Sum>y\<in>G i`space M. (y * ?I y x))"
        by (subst setsum_ereal_right_distrib) (auto simp: ac_simps)
      also have "\<dots> = f x * G i x"
        by (simp add: indicator_def if_distrib setsum_cases)
      finally have "(\<Sum>y\<in>G i`space M. y * (f x * ?I y x)) = f x * G i x" . }
    note to_singleton = this
    have "integral\<^isup>P M' (G i) = integral\<^isup>S M' (G i)"
      using G T.positive_integral_eq_simple_integral by simp
    also have "\<dots> = (\<Sum>y\<in>G i`space M. y * (\<integral>\<^isup>+x. f x * ?I y x \<partial>M))"
      unfolding simple_integral_def M' by simp
    also have "\<dots> = (\<Sum>y\<in>G i`space M. (\<integral>\<^isup>+x. y * (f x * ?I y x) \<partial>M))"
      using f G' G by (auto intro!: setsum_cong positive_integral_cmult[symmetric])
    also have "\<dots> = (\<integral>\<^isup>+x. (\<Sum>y\<in>G i`space M. y * (f x * ?I y x)) \<partial>M)"
      using f G' G by (auto intro!: positive_integral_setsum[symmetric])
    finally have "integral\<^isup>P M' (G i) = (\<integral>\<^isup>+x. f x * G i x \<partial>M)"
      using f g G' to_singleton by (auto intro!: positive_integral_cong_AE) }
  note [simp] = this
  have "integral\<^isup>P M' g = (SUP i. integral\<^isup>P M' (G i))" using G'(1) G_M'(1) G
    using T.positive_integral_monotone_convergence_SUP[symmetric, OF `incseq G`]
    by (simp cong: T.positive_integral_cong_AE)
  also have "\<dots> = (SUP i. (\<integral>\<^isup>+x. f x * G i x \<partial>M))" by simp
  also have "\<dots> = (\<integral>\<^isup>+x. (SUP i. f x * G i x) \<partial>M)"
    using f G' G(2)[THEN incseq_SucD] G
    by (intro positive_integral_monotone_convergence_SUP_AE[symmetric])
       (auto simp: ereal_mult_left_mono le_fun_def ereal_zero_le_0_iff)
  also have "\<dots> = (\<integral>\<^isup>+x. f x * g x \<partial>M)" using f G' G g
    by (intro positive_integral_cong_AE)
       (auto simp add: SUPR_ereal_cmult split: split_max)
  finally show "integral\<^isup>P M' g = (\<integral>\<^isup>+x. f x * g x \<partial>M)" .
qed

lemma (in measure_space) positive_integral_0_iff:
  assumes u: "u \<in> borel_measurable M" and pos: "AE x. 0 \<le> u x"
  shows "integral\<^isup>P M u = 0 \<longleftrightarrow> \<mu> {x\<in>space M. u x \<noteq> 0} = 0"
    (is "_ \<longleftrightarrow> \<mu> ?A = 0")
proof -
  have u_eq: "(\<integral>\<^isup>+ x. u x * indicator ?A x \<partial>M) = integral\<^isup>P M u"
    by (auto intro!: positive_integral_cong simp: indicator_def)
  show ?thesis
  proof
    assume "\<mu> ?A = 0"
    with positive_integral_null_set[of ?A u] u
    show "integral\<^isup>P M u = 0" by (simp add: u_eq)
  next
    { fix r :: ereal and n :: nat assume gt_1: "1 \<le> real n * r"
      then have "0 < real n * r" by (cases r) (auto split: split_if_asm simp: one_ereal_def)
      then have "0 \<le> r" by (auto simp add: ereal_zero_less_0_iff) }
    note gt_1 = this
    assume *: "integral\<^isup>P M u = 0"
    let ?M = "\<lambda>n. {x \<in> space M. 1 \<le> real (n::nat) * u x}"
    have "0 = (SUP n. \<mu> (?M n \<inter> ?A))"
    proof -
      { fix n :: nat
        from positive_integral_Markov_inequality[OF u pos, of ?A "ereal (real n)"]
        have "\<mu> (?M n \<inter> ?A) \<le> 0" unfolding u_eq * using u by simp
        moreover have "0 \<le> \<mu> (?M n \<inter> ?A)" using u by auto
        ultimately have "\<mu> (?M n \<inter> ?A) = 0" by auto }
      thus ?thesis by simp
    qed
    also have "\<dots> = \<mu> (\<Union>n. ?M n \<inter> ?A)"
    proof (safe intro!: continuity_from_below)
      fix n show "?M n \<inter> ?A \<in> sets M"
        using u by (auto intro!: Int)
    next
      show "incseq (\<lambda>n. {x \<in> space M. 1 \<le> real n * u x} \<inter> {x \<in> space M. u x \<noteq> 0})"
      proof (safe intro!: incseq_SucI)
        fix n :: nat and x
        assume *: "1 \<le> real n * u x"
        also from gt_1[OF this] have "real n * u x \<le> real (Suc n) * u x"
          using `0 \<le> u x` by (auto intro!: ereal_mult_right_mono)
        finally show "1 \<le> real (Suc n) * u x" by auto
      qed
    qed
    also have "\<dots> = \<mu> {x\<in>space M. 0 < u x}"
    proof (safe intro!: arg_cong[where f="\<mu>"] dest!: gt_1)
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
    finally have "\<mu> {x\<in>space M. 0 < u x} = 0" by simp
    moreover
    from pos have "AE x. \<not> (u x < 0)" by auto
    then have "\<mu> {x\<in>space M. u x < 0} = 0"
      using AE_iff_null_set u by auto
    moreover have "\<mu> {x\<in>space M. u x \<noteq> 0} = \<mu> {x\<in>space M. u x < 0} + \<mu> {x\<in>space M. 0 < u x}"
      using u by (subst measure_additive) (auto intro!: arg_cong[where f=\<mu>])
    ultimately show "\<mu> ?A = 0" by simp
  qed
qed

lemma (in measure_space) positive_integral_0_iff_AE:
  assumes u: "u \<in> borel_measurable M"
  shows "integral\<^isup>P M u = 0 \<longleftrightarrow> (AE x. u x \<le> 0)"
proof -
  have sets: "{x\<in>space M. max 0 (u x) \<noteq> 0} \<in> sets M"
    using u by auto
  from positive_integral_0_iff[of "\<lambda>x. max 0 (u x)"]
  have "integral\<^isup>P M u = 0 \<longleftrightarrow> (AE x. max 0 (u x) = 0)"
    unfolding positive_integral_max_0
    using AE_iff_null_set[OF sets] u by auto
  also have "\<dots> \<longleftrightarrow> (AE x. u x \<le> 0)" by (auto split: split_max)
  finally show ?thesis .
qed

lemma (in measure_space) positive_integral_const_If:
  "(\<integral>\<^isup>+x. a \<partial>M) = (if 0 \<le> a then a * \<mu> (space M) else 0)"
  by (auto intro!: positive_integral_0_iff_AE[THEN iffD2])

lemma (in measure_space) positive_integral_restricted:
  assumes A: "A \<in> sets M"
  shows "integral\<^isup>P (restricted_space A) f = (\<integral>\<^isup>+ x. f x * indicator A x \<partial>M)"
    (is "integral\<^isup>P ?R f = integral\<^isup>P M ?f")
proof -
  interpret R: measure_space ?R
    by (rule restricted_measure_space) fact
  let ?I = "\<lambda>g x. g x * indicator A x :: ereal"
  show ?thesis
    unfolding positive_integral_def
    unfolding simple_function_restricted[OF A]
    unfolding AE_restricted[OF A]
  proof (safe intro!: SUPR_eq)
    fix g assume g: "simple_function M (?I g)" and le: "g \<le> max 0 \<circ> f"
    show "\<exists>j\<in>{g. simple_function M g \<and> g \<le> max 0 \<circ> ?I f}.
      integral\<^isup>S (restricted_space A) g \<le> integral\<^isup>S M j"
    proof (safe intro!: bexI[of _ "?I g"])
      show "integral\<^isup>S (restricted_space A) g \<le> integral\<^isup>S M (?I g)"
        using g A by (simp add: simple_integral_restricted)
      show "?I g \<le> max 0 \<circ> ?I f"
        using le by (auto simp: le_fun_def max_def indicator_def split: split_if_asm)
    qed fact
  next
    fix g assume g: "simple_function M g" and le: "g \<le> max 0 \<circ> ?I f"
    show "\<exists>i\<in>{g. simple_function M (?I g) \<and> g \<le> max 0 \<circ> f}.
      integral\<^isup>S M g \<le> integral\<^isup>S (restricted_space A) i"
    proof (safe intro!: bexI[of _ "?I g"])
      show "?I g \<le> max 0 \<circ> f"
        using le by (auto simp: le_fun_def max_def indicator_def split: split_if_asm)
      from le have "\<And>x. g x \<le> ?I (?I g) x"
        by (auto simp: le_fun_def max_def indicator_def split: split_if_asm)
      then show "integral\<^isup>S M g \<le> integral\<^isup>S (restricted_space A) (?I g)"
        using A g by (auto intro!: simple_integral_mono simp: simple_integral_restricted)
      show "simple_function M (?I (?I g))" using g A by auto
    qed
  qed
qed

lemma (in measure_space) positive_integral_subalgebra:
  assumes f: "f \<in> borel_measurable N" "AE x in N. 0 \<le> f x"
  and N: "sets N \<subseteq> sets M" "space N = space M" "\<And>A. A \<in> sets N \<Longrightarrow> measure N A = \<mu> A"
  and sa: "sigma_algebra N"
  shows "integral\<^isup>P N f = integral\<^isup>P M f"
proof -
  interpret N: measure_space N using measure_space_subalgebra[OF sa N] .
  from N.borel_measurable_implies_simple_function_sequence'[OF f(1)] guess fs . note fs = this
  note sf = simple_function_subalgebra[OF fs(1) N(1,2)]
  from N.positive_integral_monotone_convergence_simple[OF fs(2,5,1), symmetric]
  have "integral\<^isup>P N f = (SUP i. \<Sum>x\<in>fs i ` space M. x * N.\<mu> (fs i -` {x} \<inter> space M))"
    unfolding fs(4) positive_integral_max_0
    unfolding simple_integral_def `space N = space M` by simp
  also have "\<dots> = (SUP i. \<Sum>x\<in>fs i ` space M. x * \<mu> (fs i -` {x} \<inter> space M))"
    using N N.simple_functionD(2)[OF fs(1)] unfolding `space N = space M` by auto
  also have "\<dots> = integral\<^isup>P M f"
    using positive_integral_monotone_convergence_simple[OF fs(2,5) sf, symmetric]
    unfolding fs(4) positive_integral_max_0
    unfolding simple_integral_def `space N = space M` by simp
  finally show ?thesis .
qed

section "Lebesgue Integral"

definition integrable where
  "integrable M f \<longleftrightarrow> f \<in> borel_measurable M \<and>
    (\<integral>\<^isup>+ x. ereal (f x) \<partial>M) \<noteq> \<infinity> \<and> (\<integral>\<^isup>+ x. ereal (- f x) \<partial>M) \<noteq> \<infinity>"

lemma integrableD[dest]:
  assumes "integrable M f"
  shows "f \<in> borel_measurable M" "(\<integral>\<^isup>+ x. ereal (f x) \<partial>M) \<noteq> \<infinity>" "(\<integral>\<^isup>+ x. ereal (- f x) \<partial>M) \<noteq> \<infinity>"
  using assms unfolding integrable_def by auto

definition lebesgue_integral_def:
  "integral\<^isup>L M f = real ((\<integral>\<^isup>+ x. ereal (f x) \<partial>M)) - real ((\<integral>\<^isup>+ x. ereal (- f x) \<partial>M))"

syntax
  "_lebesgue_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> ('a, 'b) measure_space_scheme \<Rightarrow> real" ("\<integral> _. _ \<partial>_" [60,61] 110)

translations
  "\<integral> x. f \<partial>M" == "CONST integral\<^isup>L M (%x. f)"

lemma (in measure_space) integrableE:
  assumes "integrable M f"
  obtains r q where
    "(\<integral>\<^isup>+x. ereal (f x)\<partial>M) = ereal r"
    "(\<integral>\<^isup>+x. ereal (-f x)\<partial>M) = ereal q"
    "f \<in> borel_measurable M" "integral\<^isup>L M f = r - q"
  using assms unfolding integrable_def lebesgue_integral_def
  using positive_integral_positive[of "\<lambda>x. ereal (f x)"]
  using positive_integral_positive[of "\<lambda>x. ereal (-f x)"]
  by (cases rule: ereal2_cases[of "(\<integral>\<^isup>+x. ereal (-f x)\<partial>M)" "(\<integral>\<^isup>+x. ereal (f x)\<partial>M)"]) auto

lemma (in measure_space) integral_cong:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> f x = g x"
  shows "integral\<^isup>L M f = integral\<^isup>L M g"
  using assms by (simp cong: positive_integral_cong add: lebesgue_integral_def)

lemma (in measure_space) integral_cong_measure:
  assumes "\<And>A. A \<in> sets M \<Longrightarrow> measure N A = \<mu> A" "sets N = sets M" "space N = space M"
  shows "integral\<^isup>L N f = integral\<^isup>L M f"
  by (simp add: positive_integral_cong_measure[OF assms] lebesgue_integral_def)

lemma (in measure_space) integrable_cong_measure:
  assumes "\<And>A. A \<in> sets M \<Longrightarrow> measure N A = \<mu> A" "sets N = sets M" "space N = space M"
  shows "integrable N f \<longleftrightarrow> integrable M f"
  using assms
  by (simp add: positive_integral_cong_measure[OF assms] integrable_def measurable_def)

lemma (in measure_space) integral_cong_AE:
  assumes cong: "AE x. f x = g x"
  shows "integral\<^isup>L M f = integral\<^isup>L M g"
proof -
  have *: "AE x. ereal (f x) = ereal (g x)"
    "AE x. ereal (- f x) = ereal (- g x)" using cong by auto
  show ?thesis
    unfolding *[THEN positive_integral_cong_AE] lebesgue_integral_def ..
qed

lemma (in measure_space) integrable_cong_AE:
  assumes borel: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes "AE x. f x = g x"
  shows "integrable M f = integrable M g"
proof -
  have "(\<integral>\<^isup>+ x. ereal (f x) \<partial>M) = (\<integral>\<^isup>+ x. ereal (g x) \<partial>M)"
    "(\<integral>\<^isup>+ x. ereal (- f x) \<partial>M) = (\<integral>\<^isup>+ x. ereal (- g x) \<partial>M)"
    using assms by (auto intro!: positive_integral_cong_AE)
  with assms show ?thesis
    by (auto simp: integrable_def)
qed

lemma (in measure_space) integrable_cong:
  "(\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> integrable M f \<longleftrightarrow> integrable M g"
  by (simp cong: positive_integral_cong measurable_cong add: integrable_def)

lemma (in measure_space) integral_eq_positive_integral:
  assumes f: "\<And>x. 0 \<le> f x"
  shows "integral\<^isup>L M f = real (\<integral>\<^isup>+ x. ereal (f x) \<partial>M)"
proof -
  { fix x have "max 0 (ereal (- f x)) = 0" using f[of x] by (simp split: split_max) }
  then have "0 = (\<integral>\<^isup>+ x. max 0 (ereal (- f x)) \<partial>M)" by simp
  also have "\<dots> = (\<integral>\<^isup>+ x. ereal (- f x) \<partial>M)" unfolding positive_integral_max_0 ..
  finally show ?thesis
    unfolding lebesgue_integral_def by simp
qed

lemma (in measure_space) integral_vimage:
  assumes T: "sigma_algebra M'" "T \<in> measure_preserving M M'"
  assumes f: "f \<in> borel_measurable M'"
  shows "integral\<^isup>L M' f = (\<integral>x. f (T x) \<partial>M)"
proof -
  interpret T: measure_space M' by (rule measure_space_vimage[OF T])
  from measurable_comp[OF measure_preservingD2[OF T(2)], of f borel]
  have borel: "(\<lambda>x. ereal (f x)) \<in> borel_measurable M'" "(\<lambda>x. ereal (- f x)) \<in> borel_measurable M'"
    and "(\<lambda>x. f (T x)) \<in> borel_measurable M"
    using f by (auto simp: comp_def)
  then show ?thesis
    using f unfolding lebesgue_integral_def integrable_def
    by (auto simp: borel[THEN positive_integral_vimage[OF T]])
qed

lemma (in measure_space) integrable_vimage:
  assumes T: "sigma_algebra M'" "T \<in> measure_preserving M M'"
  assumes f: "integrable M' f"
  shows "integrable M (\<lambda>x. f (T x))"
proof -
  interpret T: measure_space M' by (rule measure_space_vimage[OF T])
  from measurable_comp[OF measure_preservingD2[OF T(2)], of f borel]
  have borel: "(\<lambda>x. ereal (f x)) \<in> borel_measurable M'" "(\<lambda>x. ereal (- f x)) \<in> borel_measurable M'"
    and "(\<lambda>x. f (T x)) \<in> borel_measurable M"
    using f by (auto simp: comp_def)
  then show ?thesis
    using f unfolding lebesgue_integral_def integrable_def
    by (auto simp: borel[THEN positive_integral_vimage[OF T]])
qed

lemma (in measure_space) integral_translated_density:
  assumes f: "f \<in> borel_measurable M" "AE x. 0 \<le> f x"
    and g: "g \<in> borel_measurable M"
    and N: "space N = space M" "sets N = sets M"
    and density: "\<And>A. A \<in> sets M \<Longrightarrow> measure N A = (\<integral>\<^isup>+ x. f x * indicator A x \<partial>M)"
      (is "\<And>A. _ \<Longrightarrow> _ = ?d A")
  shows "integral\<^isup>L N g = (\<integral> x. f x * g x \<partial>M)" (is ?integral)
    and "integrable N g = integrable M (\<lambda>x. f x * g x)" (is ?integrable)
proof -
  from f have ms: "measure_space (M\<lparr>measure := ?d\<rparr>)"
    by (intro measure_space_density[where u="\<lambda>x. ereal (f x)"]) auto

  from ms density N have "(\<integral>\<^isup>+ x. g x \<partial>N) =  (\<integral>\<^isup>+ x. max 0 (ereal (g x)) \<partial>M\<lparr>measure := ?d\<rparr>)"
    unfolding positive_integral_max_0
    by (intro measure_space.positive_integral_cong_measure) auto
  also have "\<dots> = (\<integral>\<^isup>+ x. ereal (f x) * max 0 (ereal (g x)) \<partial>M)"
    using f g by (intro positive_integral_translated_density) auto
  also have "\<dots> = (\<integral>\<^isup>+ x. max 0 (ereal (f x * g x)) \<partial>M)"
    using f by (intro positive_integral_cong_AE)
               (auto simp: ereal_max_0 zero_le_mult_iff split: split_max)
  finally have pos: "(\<integral>\<^isup>+ x. g x \<partial>N) = (\<integral>\<^isup>+ x. f x * g x \<partial>M)"
    by (simp add: positive_integral_max_0)
  
  from ms density N have "(\<integral>\<^isup>+ x. - (g x) \<partial>N) =  (\<integral>\<^isup>+ x. max 0 (ereal (- g x)) \<partial>M\<lparr>measure := ?d\<rparr>)"
    unfolding positive_integral_max_0
    by (intro measure_space.positive_integral_cong_measure) auto
  also have "\<dots> = (\<integral>\<^isup>+ x. ereal (f x) * max 0 (ereal (- g x)) \<partial>M)"
    using f g by (intro positive_integral_translated_density) auto
  also have "\<dots> = (\<integral>\<^isup>+ x. max 0 (ereal (- f x * g x)) \<partial>M)"
    using f by (intro positive_integral_cong_AE)
               (auto simp: ereal_max_0 mult_le_0_iff split: split_max)
  finally have neg: "(\<integral>\<^isup>+ x. - g x \<partial>N) = (\<integral>\<^isup>+ x. - (f x * g x) \<partial>M)"
    by (simp add: positive_integral_max_0)

  have g_N: "g \<in> borel_measurable N"
    using g N unfolding measurable_def by simp

  show ?integral ?integrable
    unfolding lebesgue_integral_def integrable_def
    using pos neg f g g_N by auto
qed

lemma (in measure_space) integral_minus[intro, simp]:
  assumes "integrable M f"
  shows "integrable M (\<lambda>x. - f x)" "(\<integral>x. - f x \<partial>M) = - integral\<^isup>L M f"
  using assms by (auto simp: integrable_def lebesgue_integral_def)

lemma (in measure_space) integral_minus_iff[simp]:
  "integrable M (\<lambda>x. - f x) \<longleftrightarrow> integrable M f"
proof
  assume "integrable M (\<lambda>x. - f x)"
  then have "integrable M (\<lambda>x. - (- f x))"
    by (rule integral_minus)
  then show "integrable M f" by simp
qed (rule integral_minus)

lemma (in measure_space) integral_of_positive_diff:
  assumes integrable: "integrable M u" "integrable M v"
  and f_def: "\<And>x. f x = u x - v x" and pos: "\<And>x. 0 \<le> u x" "\<And>x. 0 \<le> v x"
  shows "integrable M f" and "integral\<^isup>L M f = integral\<^isup>L M u - integral\<^isup>L M v"
proof -
  let ?f = "\<lambda>x. max 0 (ereal (f x))"
  let ?mf = "\<lambda>x. max 0 (ereal (- f x))"
  let ?u = "\<lambda>x. max 0 (ereal (u x))"
  let ?v = "\<lambda>x. max 0 (ereal (v x))"

  from borel_measurable_diff[of u v] integrable
  have f_borel: "?f \<in> borel_measurable M" and
    mf_borel: "?mf \<in> borel_measurable M" and
    v_borel: "?v \<in> borel_measurable M" and
    u_borel: "?u \<in> borel_measurable M" and
    "f \<in> borel_measurable M"
    by (auto simp: f_def[symmetric] integrable_def)

  have "(\<integral>\<^isup>+ x. ereal (u x - v x) \<partial>M) \<le> integral\<^isup>P M ?u"
    using pos by (auto intro!: positive_integral_mono simp: positive_integral_max_0)
  moreover have "(\<integral>\<^isup>+ x. ereal (v x - u x) \<partial>M) \<le> integral\<^isup>P M ?v"
    using pos by (auto intro!: positive_integral_mono simp: positive_integral_max_0)
  ultimately show f: "integrable M f"
    using `integrable M u` `integrable M v` `f \<in> borel_measurable M`
    by (auto simp: integrable_def f_def positive_integral_max_0)

  have "\<And>x. ?u x + ?mf x = ?v x + ?f x"
    unfolding f_def using pos by (simp split: split_max)
  then have "(\<integral>\<^isup>+ x. ?u x + ?mf x \<partial>M) = (\<integral>\<^isup>+ x. ?v x + ?f x \<partial>M)" by simp
  then have "real (integral\<^isup>P M ?u + integral\<^isup>P M ?mf) =
      real (integral\<^isup>P M ?v + integral\<^isup>P M ?f)"
    using positive_integral_add[OF u_borel _ mf_borel]
    using positive_integral_add[OF v_borel _ f_borel]
    by auto
  then show "integral\<^isup>L M f = integral\<^isup>L M u - integral\<^isup>L M v"
    unfolding positive_integral_max_0
    unfolding pos[THEN integral_eq_positive_integral]
    using integrable f by (auto elim!: integrableE)
qed

lemma (in measure_space) integral_linear:
  assumes "integrable M f" "integrable M g" and "0 \<le> a"
  shows "integrable M (\<lambda>t. a * f t + g t)"
  and "(\<integral> t. a * f t + g t \<partial>M) = a * integral\<^isup>L M f + integral\<^isup>L M g" (is ?EQ)
proof -
  let ?f = "\<lambda>x. max 0 (ereal (f x))"
  let ?g = "\<lambda>x. max 0 (ereal (g x))"
  let ?mf = "\<lambda>x. max 0 (ereal (- f x))"
  let ?mg = "\<lambda>x. max 0 (ereal (- g x))"
  let ?p = "\<lambda>t. max 0 (a * f t) + max 0 (g t)"
  let ?n = "\<lambda>t. max 0 (- (a * f t)) + max 0 (- g t)"

  from assms have linear:
    "(\<integral>\<^isup>+ x. ereal a * ?f x + ?g x \<partial>M) = ereal a * integral\<^isup>P M ?f + integral\<^isup>P M ?g"
    "(\<integral>\<^isup>+ x. ereal a * ?mf x + ?mg x \<partial>M) = ereal a * integral\<^isup>P M ?mf + integral\<^isup>P M ?mg"
    by (auto intro!: positive_integral_linear simp: integrable_def)

  have *: "(\<integral>\<^isup>+x. ereal (- ?p x) \<partial>M) = 0" "(\<integral>\<^isup>+x. ereal (- ?n x) \<partial>M) = 0"
    using `0 \<le> a` assms by (auto simp: positive_integral_0_iff_AE integrable_def)
  have **: "\<And>x. ereal a * ?f x + ?g x = max 0 (ereal (?p x))"
           "\<And>x. ereal a * ?mf x + ?mg x = max 0 (ereal (?n x))"
    using `0 \<le> a` by (auto split: split_max simp: zero_le_mult_iff mult_le_0_iff)

  have "integrable M ?p" "integrable M ?n"
      "\<And>t. a * f t + g t = ?p t - ?n t" "\<And>t. 0 \<le> ?p t" "\<And>t. 0 \<le> ?n t"
    using linear assms unfolding integrable_def ** *
    by (auto simp: positive_integral_max_0)
  note diff = integral_of_positive_diff[OF this]

  show "integrable M (\<lambda>t. a * f t + g t)" by (rule diff)
  from assms linear show ?EQ
    unfolding diff(2) ** positive_integral_max_0
    unfolding lebesgue_integral_def *
    by (auto elim!: integrableE simp: field_simps)
qed

lemma (in measure_space) integral_add[simp, intro]:
  assumes "integrable M f" "integrable M g"
  shows "integrable M (\<lambda>t. f t + g t)"
  and "(\<integral> t. f t + g t \<partial>M) = integral\<^isup>L M f + integral\<^isup>L M g"
  using assms integral_linear[where a=1] by auto

lemma (in measure_space) integral_zero[simp, intro]:
  shows "integrable M (\<lambda>x. 0)" "(\<integral> x.0 \<partial>M) = 0"
  unfolding integrable_def lebesgue_integral_def
  by (auto simp add: borel_measurable_const)

lemma (in measure_space) integral_cmult[simp, intro]:
  assumes "integrable M f"
  shows "integrable M (\<lambda>t. a * f t)" (is ?P)
  and "(\<integral> t. a * f t \<partial>M) = a * integral\<^isup>L M f" (is ?I)
proof -
  have "integrable M (\<lambda>t. a * f t) \<and> (\<integral> t. a * f t \<partial>M) = a * integral\<^isup>L M f"
  proof (cases rule: le_cases)
    assume "0 \<le> a" show ?thesis
      using integral_linear[OF assms integral_zero(1) `0 \<le> a`]
      by (simp add: integral_zero)
  next
    assume "a \<le> 0" hence "0 \<le> - a" by auto
    have *: "\<And>t. - a * t + 0 = (-a) * t" by simp
    show ?thesis using integral_linear[OF assms integral_zero(1) `0 \<le> - a`]
        integral_minus(1)[of "\<lambda>t. - a * f t"]
      unfolding * integral_zero by simp
  qed
  thus ?P ?I by auto
qed

lemma (in measure_space) integral_multc:
  assumes "integrable M f"
  shows "(\<integral> x. f x * c \<partial>M) = integral\<^isup>L M f * c"
  unfolding mult_commute[of _ c] integral_cmult[OF assms] ..

lemma (in measure_space) integral_mono_AE:
  assumes fg: "integrable M f" "integrable M g"
  and mono: "AE t. f t \<le> g t"
  shows "integral\<^isup>L M f \<le> integral\<^isup>L M g"
proof -
  have "AE x. ereal (f x) \<le> ereal (g x)"
    using mono by auto
  moreover have "AE x. ereal (- g x) \<le> ereal (- f x)"
    using mono by auto
  ultimately show ?thesis using fg
    by (auto intro!: add_mono positive_integral_mono_AE real_of_ereal_positive_mono
             simp: positive_integral_positive lebesgue_integral_def diff_minus)
qed

lemma (in measure_space) integral_mono:
  assumes "integrable M f" "integrable M g" "\<And>t. t \<in> space M \<Longrightarrow> f t \<le> g t"
  shows "integral\<^isup>L M f \<le> integral\<^isup>L M g"
  using assms by (auto intro: integral_mono_AE)

lemma (in measure_space) integral_diff[simp, intro]:
  assumes f: "integrable M f" and g: "integrable M g"
  shows "integrable M (\<lambda>t. f t - g t)"
  and "(\<integral> t. f t - g t \<partial>M) = integral\<^isup>L M f - integral\<^isup>L M g"
  using integral_add[OF f integral_minus(1)[OF g]]
  unfolding diff_minus integral_minus(2)[OF g]
  by auto

lemma (in measure_space) integral_indicator[simp, intro]:
  assumes "A \<in> sets M" and "\<mu> A \<noteq> \<infinity>"
  shows "integral\<^isup>L M (indicator A) = real (\<mu> A)" (is ?int)
  and "integrable M (indicator A)" (is ?able)
proof -
  from `A \<in> sets M` have *:
    "\<And>x. ereal (indicator A x) = indicator A x"
    "(\<integral>\<^isup>+x. ereal (- indicator A x) \<partial>M) = 0"
    by (auto split: split_indicator simp: positive_integral_0_iff_AE one_ereal_def)
  show ?int ?able
    using assms unfolding lebesgue_integral_def integrable_def
    by (auto simp: * positive_integral_indicator borel_measurable_indicator)
qed

lemma (in measure_space) integral_cmul_indicator:
  assumes "A \<in> sets M" and "c \<noteq> 0 \<Longrightarrow> \<mu> A \<noteq> \<infinity>"
  shows "integrable M (\<lambda>x. c * indicator A x)" (is ?P)
  and "(\<integral>x. c * indicator A x \<partial>M) = c * real (\<mu> A)" (is ?I)
proof -
  show ?P
  proof (cases "c = 0")
    case False with assms show ?thesis by simp
  qed simp

  show ?I
  proof (cases "c = 0")
    case False with assms show ?thesis by simp
  qed simp
qed

lemma (in measure_space) integral_setsum[simp, intro]:
  assumes "\<And>n. n \<in> S \<Longrightarrow> integrable M (f n)"
  shows "(\<integral>x. (\<Sum> i \<in> S. f i x) \<partial>M) = (\<Sum> i \<in> S. integral\<^isup>L M (f i))" (is "?int S")
    and "integrable M (\<lambda>x. \<Sum> i \<in> S. f i x)" (is "?I S")
proof -
  have "?int S \<and> ?I S"
  proof (cases "finite S")
    assume "finite S"
    from this assms show ?thesis by (induct S) simp_all
  qed simp
  thus "?int S" and "?I S" by auto
qed

lemma (in measure_space) integrable_abs:
  assumes "integrable M f"
  shows "integrable M (\<lambda> x. \<bar>f x\<bar>)"
proof -
  from assms have *: "(\<integral>\<^isup>+x. ereal (- \<bar>f x\<bar>)\<partial>M) = 0"
    "\<And>x. ereal \<bar>f x\<bar> = max 0 (ereal (f x)) + max 0 (ereal (- f x))"
    by (auto simp: integrable_def positive_integral_0_iff_AE split: split_max)
  with assms show ?thesis
    by (simp add: positive_integral_add positive_integral_max_0 integrable_def)
qed

lemma (in measure_space) integral_subalgebra:
  assumes borel: "f \<in> borel_measurable N"
  and N: "sets N \<subseteq> sets M" "space N = space M" "\<And>A. A \<in> sets N \<Longrightarrow> measure N A = \<mu> A" and sa: "sigma_algebra N"
  shows "integrable N f \<longleftrightarrow> integrable M f" (is ?P)
    and "integral\<^isup>L N f = integral\<^isup>L M f" (is ?I)
proof -
  interpret N: measure_space N using measure_space_subalgebra[OF sa N] .
  have "(\<integral>\<^isup>+ x. max 0 (ereal (f x)) \<partial>N) = (\<integral>\<^isup>+ x. max 0 (ereal (f x)) \<partial>M)"
       "(\<integral>\<^isup>+ x. max 0 (ereal (- f x)) \<partial>N) = (\<integral>\<^isup>+ x. max 0 (ereal (- f x)) \<partial>M)"
    using borel by (auto intro!: positive_integral_subalgebra N sa)
  moreover have "f \<in> borel_measurable M \<longleftrightarrow> f \<in> borel_measurable N"
    using assms unfolding measurable_def by auto
  ultimately show ?P ?I
    by (auto simp: integrable_def lebesgue_integral_def positive_integral_max_0)
qed

lemma (in measure_space) integrable_bound:
  assumes "integrable M f"
  and f: "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> f x"
    "\<And>x. x \<in> space M \<Longrightarrow> \<bar>g x\<bar> \<le> f x"
  assumes borel: "g \<in> borel_measurable M"
  shows "integrable M g"
proof -
  have "(\<integral>\<^isup>+ x. ereal (g x) \<partial>M) \<le> (\<integral>\<^isup>+ x. ereal \<bar>g x\<bar> \<partial>M)"
    by (auto intro!: positive_integral_mono)
  also have "\<dots> \<le> (\<integral>\<^isup>+ x. ereal (f x) \<partial>M)"
    using f by (auto intro!: positive_integral_mono)
  also have "\<dots> < \<infinity>"
    using `integrable M f` unfolding integrable_def by auto
  finally have pos: "(\<integral>\<^isup>+ x. ereal (g x) \<partial>M) < \<infinity>" .

  have "(\<integral>\<^isup>+ x. ereal (- g x) \<partial>M) \<le> (\<integral>\<^isup>+ x. ereal (\<bar>g x\<bar>) \<partial>M)"
    by (auto intro!: positive_integral_mono)
  also have "\<dots> \<le> (\<integral>\<^isup>+ x. ereal (f x) \<partial>M)"
    using f by (auto intro!: positive_integral_mono)
  also have "\<dots> < \<infinity>"
    using `integrable M f` unfolding integrable_def by auto
  finally have neg: "(\<integral>\<^isup>+ x. ereal (- g x) \<partial>M) < \<infinity>" .

  from neg pos borel show ?thesis
    unfolding integrable_def by auto
qed

lemma (in measure_space) integrable_abs_iff:
  "f \<in> borel_measurable M \<Longrightarrow> integrable M (\<lambda> x. \<bar>f x\<bar>) \<longleftrightarrow> integrable M f"
  by (auto intro!: integrable_bound[where g=f] integrable_abs)

lemma (in measure_space) integrable_max:
  assumes int: "integrable M f" "integrable M g"
  shows "integrable M (\<lambda> x. max (f x) (g x))"
proof (rule integrable_bound)
  show "integrable M (\<lambda>x. \<bar>f x\<bar> + \<bar>g x\<bar>)"
    using int by (simp add: integrable_abs)
  show "(\<lambda>x. max (f x) (g x)) \<in> borel_measurable M"
    using int unfolding integrable_def by auto
next
  fix x assume "x \<in> space M"
  show "0 \<le> \<bar>f x\<bar> + \<bar>g x\<bar>" "\<bar>max (f x) (g x)\<bar> \<le> \<bar>f x\<bar> + \<bar>g x\<bar>"
    by auto
qed

lemma (in measure_space) integrable_min:
  assumes int: "integrable M f" "integrable M g"
  shows "integrable M (\<lambda> x. min (f x) (g x))"
proof (rule integrable_bound)
  show "integrable M (\<lambda>x. \<bar>f x\<bar> + \<bar>g x\<bar>)"
    using int by (simp add: integrable_abs)
  show "(\<lambda>x. min (f x) (g x)) \<in> borel_measurable M"
    using int unfolding integrable_def by auto
next
  fix x assume "x \<in> space M"
  show "0 \<le> \<bar>f x\<bar> + \<bar>g x\<bar>" "\<bar>min (f x) (g x)\<bar> \<le> \<bar>f x\<bar> + \<bar>g x\<bar>"
    by auto
qed

lemma (in measure_space) integral_triangle_inequality:
  assumes "integrable M f"
  shows "\<bar>integral\<^isup>L M f\<bar> \<le> (\<integral>x. \<bar>f x\<bar> \<partial>M)"
proof -
  have "\<bar>integral\<^isup>L M f\<bar> = max (integral\<^isup>L M f) (- integral\<^isup>L M f)" by auto
  also have "\<dots> \<le> (\<integral>x. \<bar>f x\<bar> \<partial>M)"
      using assms integral_minus(2)[of f, symmetric]
      by (auto intro!: integral_mono integrable_abs simp del: integral_minus)
  finally show ?thesis .
qed

lemma (in measure_space) integral_positive:
  assumes "integrable M f" "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> f x"
  shows "0 \<le> integral\<^isup>L M f"
proof -
  have "0 = (\<integral>x. 0 \<partial>M)" by (auto simp: integral_zero)
  also have "\<dots> \<le> integral\<^isup>L M f"
    using assms by (rule integral_mono[OF integral_zero(1)])
  finally show ?thesis .
qed

lemma (in measure_space) integral_monotone_convergence_pos:
  assumes i: "\<And>i. integrable M (f i)" and mono: "\<And>x. mono (\<lambda>n. f n x)"
  and pos: "\<And>x i. 0 \<le> f i x"
  and lim: "\<And>x. (\<lambda>i. f i x) ----> u x"
  and ilim: "(\<lambda>i. integral\<^isup>L M (f i)) ----> x"
  shows "integrable M u"
  and "integral\<^isup>L M u = x"
proof -
  { fix x have "0 \<le> u x"
      using mono pos[of 0 x] incseq_le[OF _ lim, of x 0]
      by (simp add: mono_def incseq_def) }
  note pos_u = this

  have SUP_F: "\<And>x. (SUP n. ereal (f n x)) = ereal (u x)"
    unfolding SUP_eq_LIMSEQ[OF mono] by (rule lim)

  have borel_f: "\<And>i. (\<lambda>x. ereal (f i x)) \<in> borel_measurable M"
    using i unfolding integrable_def by auto
  hence "(\<lambda>x. SUP i. ereal (f i x)) \<in> borel_measurable M"
    by auto
  hence borel_u: "u \<in> borel_measurable M"
    by (auto simp: borel_measurable_ereal_iff SUP_F)

  hence [simp]: "\<And>i. (\<integral>\<^isup>+x. ereal (- f i x) \<partial>M) = 0" "(\<integral>\<^isup>+x. ereal (- u x) \<partial>M) = 0"
    using i borel_u pos pos_u by (auto simp: positive_integral_0_iff_AE integrable_def)

  have integral_eq: "\<And>n. (\<integral>\<^isup>+ x. ereal (f n x) \<partial>M) = ereal (integral\<^isup>L M (f n))"
    using i positive_integral_positive by (auto simp: ereal_real lebesgue_integral_def integrable_def)

  have pos_integral: "\<And>n. 0 \<le> integral\<^isup>L M (f n)"
    using pos i by (auto simp: integral_positive)
  hence "0 \<le> x"
    using LIMSEQ_le_const[OF ilim, of 0] by auto

  from mono pos i have pI: "(\<integral>\<^isup>+ x. ereal (u x) \<partial>M) = (SUP n. (\<integral>\<^isup>+ x. ereal (f n x) \<partial>M))"
    by (auto intro!: positive_integral_monotone_convergence_SUP
      simp: integrable_def incseq_mono incseq_Suc_iff le_fun_def SUP_F[symmetric])
  also have "\<dots> = ereal x" unfolding integral_eq
  proof (rule SUP_eq_LIMSEQ[THEN iffD2])
    show "mono (\<lambda>n. integral\<^isup>L M (f n))"
      using mono i by (auto simp: mono_def intro!: integral_mono)
    show "(\<lambda>n. integral\<^isup>L M (f n)) ----> x" using ilim .
  qed
  finally show  "integrable M u" "integral\<^isup>L M u = x" using borel_u `0 \<le> x`
    unfolding integrable_def lebesgue_integral_def by auto
qed

lemma (in measure_space) integral_monotone_convergence:
  assumes f: "\<And>i. integrable M (f i)" and "mono f"
  and lim: "\<And>x. (\<lambda>i. f i x) ----> u x"
  and ilim: "(\<lambda>i. integral\<^isup>L M (f i)) ----> x"
  shows "integrable M u"
  and "integral\<^isup>L M u = x"
proof -
  have 1: "\<And>i. integrable M (\<lambda>x. f i x - f 0 x)"
      using f by (auto intro!: integral_diff)
  have 2: "\<And>x. mono (\<lambda>n. f n x - f 0 x)" using `mono f`
      unfolding mono_def le_fun_def by auto
  have 3: "\<And>x n. 0 \<le> f n x - f 0 x" using `mono f`
      unfolding mono_def le_fun_def by (auto simp: field_simps)
  have 4: "\<And>x. (\<lambda>i. f i x - f 0 x) ----> u x - f 0 x"
    using lim by (auto intro!: tendsto_diff)
  have 5: "(\<lambda>i. (\<integral>x. f i x - f 0 x \<partial>M)) ----> x - integral\<^isup>L M (f 0)"
    using f ilim by (auto intro!: tendsto_diff simp: integral_diff)
  note diff = integral_monotone_convergence_pos[OF 1 2 3 4 5]
  have "integrable M (\<lambda>x. (u x - f 0 x) + f 0 x)"
    using diff(1) f by (rule integral_add(1))
  with diff(2) f show "integrable M u" "integral\<^isup>L M u = x"
    by (auto simp: integral_diff)
qed

lemma (in measure_space) integral_0_iff:
  assumes "integrable M f"
  shows "(\<integral>x. \<bar>f x\<bar> \<partial>M) = 0 \<longleftrightarrow> \<mu> {x\<in>space M. f x \<noteq> 0} = 0"
proof -
  have *: "(\<integral>\<^isup>+x. ereal (- \<bar>f x\<bar>) \<partial>M) = 0"
    using assms by (auto simp: positive_integral_0_iff_AE integrable_def)
  have "integrable M (\<lambda>x. \<bar>f x\<bar>)" using assms by (rule integrable_abs)
  hence "(\<lambda>x. ereal (\<bar>f x\<bar>)) \<in> borel_measurable M"
    "(\<integral>\<^isup>+ x. ereal \<bar>f x\<bar> \<partial>M) \<noteq> \<infinity>" unfolding integrable_def by auto
  from positive_integral_0_iff[OF this(1)] this(2)
  show ?thesis unfolding lebesgue_integral_def *
    using positive_integral_positive[of "\<lambda>x. ereal \<bar>f x\<bar>"]
    by (auto simp add: real_of_ereal_eq_0)
qed

lemma (in measure_space) positive_integral_PInf:
  assumes f: "f \<in> borel_measurable M"
  and not_Inf: "integral\<^isup>P M f \<noteq> \<infinity>"
  shows "\<mu> (f -` {\<infinity>} \<inter> space M) = 0"
proof -
  have "\<infinity> * \<mu> (f -` {\<infinity>} \<inter> space M) = (\<integral>\<^isup>+ x. \<infinity> * indicator (f -` {\<infinity>} \<inter> space M) x \<partial>M)"
    using f by (subst positive_integral_cmult_indicator) (auto simp: measurable_sets)
  also have "\<dots> \<le> integral\<^isup>P M (\<lambda>x. max 0 (f x))"
    by (auto intro!: positive_integral_mono simp: indicator_def max_def)
  finally have "\<infinity> * \<mu> (f -` {\<infinity>} \<inter> space M) \<le> integral\<^isup>P M f"
    by (simp add: positive_integral_max_0)
  moreover have "0 \<le> \<mu> (f -` {\<infinity>} \<inter> space M)"
    using f by (simp add: measurable_sets)
  ultimately show ?thesis
    using assms by (auto split: split_if_asm)
qed

lemma (in measure_space) positive_integral_PInf_AE:
  assumes "f \<in> borel_measurable M" "integral\<^isup>P M f \<noteq> \<infinity>" shows "AE x. f x \<noteq> \<infinity>"
proof (rule AE_I)
  show "\<mu> (f -` {\<infinity>} \<inter> space M) = 0"
    by (rule positive_integral_PInf[OF assms])
  show "f -` {\<infinity>} \<inter> space M \<in> sets M"
    using assms by (auto intro: borel_measurable_vimage)
qed auto

lemma (in measure_space) simple_integral_PInf:
  assumes "simple_function M f" "\<And>x. 0 \<le> f x"
  and "integral\<^isup>S M f \<noteq> \<infinity>"
  shows "\<mu> (f -` {\<infinity>} \<inter> space M) = 0"
proof (rule positive_integral_PInf)
  show "f \<in> borel_measurable M" using assms by (auto intro: borel_measurable_simple_function)
  show "integral\<^isup>P M f \<noteq> \<infinity>"
    using assms by (simp add: positive_integral_eq_simple_integral)
qed

lemma (in measure_space) integral_real:
  "AE x. \<bar>f x\<bar> \<noteq> \<infinity> \<Longrightarrow> (\<integral>x. real (f x) \<partial>M) = real (integral\<^isup>P M f) - real (integral\<^isup>P M (\<lambda>x. - f x))"
  using assms unfolding lebesgue_integral_def
  by (subst (1 2) positive_integral_cong_AE) (auto simp add: ereal_real)

lemma (in finite_measure) lebesgue_integral_const[simp]:
  shows "integrable M (\<lambda>x. a)"
  and  "(\<integral>x. a \<partial>M) = a * \<mu>' (space M)"
proof -
  { fix a :: real assume "0 \<le> a"
    then have "(\<integral>\<^isup>+ x. ereal a \<partial>M) = ereal a * \<mu> (space M)"
      by (subst positive_integral_const) auto
    moreover
    from `0 \<le> a` have "(\<integral>\<^isup>+ x. ereal (-a) \<partial>M) = 0"
      by (subst positive_integral_0_iff_AE) auto
    ultimately have "integrable M (\<lambda>x. a)" by (auto simp: integrable_def) }
  note * = this
  show "integrable M (\<lambda>x. a)"
  proof cases
    assume "0 \<le> a" with * show ?thesis .
  next
    assume "\<not> 0 \<le> a"
    then have "0 \<le> -a" by auto
    from *[OF this] show ?thesis by simp
  qed
  show "(\<integral>x. a \<partial>M) = a * \<mu>' (space M)"
    by (simp add: \<mu>'_def lebesgue_integral_def positive_integral_const_If)
qed

lemma indicator_less[simp]:
  "indicator A x \<le> (indicator B x::ereal) \<longleftrightarrow> (x \<in> A \<longrightarrow> x \<in> B)"
  by (simp add: indicator_def not_le)

lemma (in finite_measure) integral_less_AE:
  assumes int: "integrable M X" "integrable M Y"
  assumes A: "\<mu> A \<noteq> 0" "A \<in> sets M" "AE x. x \<in> A \<longrightarrow> X x \<noteq> Y x"
  assumes gt: "AE x. X x \<le> Y x"
  shows "integral\<^isup>L M X < integral\<^isup>L M Y"
proof -
  have "integral\<^isup>L M X \<le> integral\<^isup>L M Y"
    using gt int by (intro integral_mono_AE) auto
  moreover
  have "integral\<^isup>L M X \<noteq> integral\<^isup>L M Y"
  proof
    assume eq: "integral\<^isup>L M X = integral\<^isup>L M Y"
    have "integral\<^isup>L M (\<lambda>x. \<bar>Y x - X x\<bar>) = integral\<^isup>L M (\<lambda>x. Y x - X x)"
      using gt by (intro integral_cong_AE) auto
    also have "\<dots> = 0"
      using eq int by simp
    finally have "\<mu> {x \<in> space M. Y x - X x \<noteq> 0} = 0"
      using int by (simp add: integral_0_iff)
    moreover
    have "(\<integral>\<^isup>+x. indicator A x \<partial>M) \<le> (\<integral>\<^isup>+x. indicator {x \<in> space M. Y x - X x \<noteq> 0} x \<partial>M)"
      using A by (intro positive_integral_mono_AE) auto
    then have "\<mu> A \<le> \<mu> {x \<in> space M. Y x - X x \<noteq> 0}"
      using int A by (simp add: integrable_def)
    moreover note `\<mu> A \<noteq> 0` positive_measure[OF `A \<in> sets M`]
    ultimately show False by auto
  qed
  ultimately show ?thesis by auto
qed

lemma (in finite_measure) integral_less_AE_space:
  assumes int: "integrable M X" "integrable M Y"
  assumes gt: "AE x. X x < Y x" "\<mu> (space M) \<noteq> 0"
  shows "integral\<^isup>L M X < integral\<^isup>L M Y"
  using gt by (intro integral_less_AE[OF int, where A="space M"]) auto

lemma (in measure_space) integral_dominated_convergence:
  assumes u: "\<And>i. integrable M (u i)" and bound: "\<And>x j. x\<in>space M \<Longrightarrow> \<bar>u j x\<bar> \<le> w x"
  and w: "integrable M w"
  and u': "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. u i x) ----> u' x"
  shows "integrable M u'"
  and "(\<lambda>i. (\<integral>x. \<bar>u i x - u' x\<bar> \<partial>M)) ----> 0" (is "?lim_diff")
  and "(\<lambda>i. integral\<^isup>L M (u i)) ----> integral\<^isup>L M u'" (is ?lim)
proof -
  { fix x j assume x: "x \<in> space M"
    from u'[OF x] have "(\<lambda>i. \<bar>u i x\<bar>) ----> \<bar>u' x\<bar>" by (rule tendsto_rabs)
    from LIMSEQ_le_const2[OF this]
    have "\<bar>u' x\<bar> \<le> w x" using bound[OF x] by auto }
  note u'_bound = this

  from u[unfolded integrable_def]
  have u'_borel: "u' \<in> borel_measurable M"
    using u' by (blast intro: borel_measurable_LIMSEQ[of u])

  { fix x assume x: "x \<in> space M"
    then have "0 \<le> \<bar>u 0 x\<bar>" by auto
    also have "\<dots> \<le> w x" using bound[OF x] by auto
    finally have "0 \<le> w x" . }
  note w_pos = this

  show "integrable M u'"
  proof (rule integrable_bound)
    show "integrable M w" by fact
    show "u' \<in> borel_measurable M" by fact
  next
    fix x assume x: "x \<in> space M" then show "0 \<le> w x" by fact
    show "\<bar>u' x\<bar> \<le> w x" using u'_bound[OF x] .
  qed

  let ?diff = "\<lambda>n x. 2 * w x - \<bar>u n x - u' x\<bar>"
  have diff: "\<And>n. integrable M (\<lambda>x. \<bar>u n x - u' x\<bar>)"
    using w u `integrable M u'`
    by (auto intro!: integral_add integral_diff integral_cmult integrable_abs)

  { fix j x assume x: "x \<in> space M"
    have "\<bar>u j x - u' x\<bar> \<le> \<bar>u j x\<bar> + \<bar>u' x\<bar>" by auto
    also have "\<dots> \<le> w x + w x"
      by (rule add_mono[OF bound[OF x] u'_bound[OF x]])
    finally have "\<bar>u j x - u' x\<bar> \<le> 2 * w x" by simp }
  note diff_less_2w = this

  have PI_diff: "\<And>n. (\<integral>\<^isup>+ x. ereal (?diff n x) \<partial>M) =
    (\<integral>\<^isup>+ x. ereal (2 * w x) \<partial>M) - (\<integral>\<^isup>+ x. ereal \<bar>u n x - u' x\<bar> \<partial>M)"
    using diff w diff_less_2w w_pos
    by (subst positive_integral_diff[symmetric])
       (auto simp: integrable_def intro!: positive_integral_cong)

  have "integrable M (\<lambda>x. 2 * w x)"
    using w by (auto intro: integral_cmult)
  hence I2w_fin: "(\<integral>\<^isup>+ x. ereal (2 * w x) \<partial>M) \<noteq> \<infinity>" and
    borel_2w: "(\<lambda>x. ereal (2 * w x)) \<in> borel_measurable M"
    unfolding integrable_def by auto

  have "limsup (\<lambda>n. \<integral>\<^isup>+ x. ereal \<bar>u n x - u' x\<bar> \<partial>M) = 0" (is "limsup ?f = 0")
  proof cases
    assume eq_0: "(\<integral>\<^isup>+ x. max 0 (ereal (2 * w x)) \<partial>M) = 0" (is "?wx = 0")
    { fix n
      have "?f n \<le> ?wx" (is "integral\<^isup>P M ?f' \<le> _")
        using diff_less_2w[of _ n] unfolding positive_integral_max_0
        by (intro positive_integral_mono) auto
      then have "?f n = 0"
        using positive_integral_positive[of ?f'] eq_0 by auto }
    then show ?thesis by (simp add: Limsup_const)
  next
    assume neq_0: "(\<integral>\<^isup>+ x. max 0 (ereal (2 * w x)) \<partial>M) \<noteq> 0" (is "?wx \<noteq> 0")
    have "0 = limsup (\<lambda>n. 0 :: ereal)" by (simp add: Limsup_const)
    also have "\<dots> \<le> limsup (\<lambda>n. \<integral>\<^isup>+ x. ereal \<bar>u n x - u' x\<bar> \<partial>M)"
      by (intro limsup_mono positive_integral_positive)
    finally have pos: "0 \<le> limsup (\<lambda>n. \<integral>\<^isup>+ x. ereal \<bar>u n x - u' x\<bar> \<partial>M)" .
    have "?wx = (\<integral>\<^isup>+ x. liminf (\<lambda>n. max 0 (ereal (?diff n x))) \<partial>M)"
    proof (rule positive_integral_cong)
      fix x assume x: "x \<in> space M"
      show "max 0 (ereal (2 * w x)) = liminf (\<lambda>n. max 0 (ereal (?diff n x)))"
        unfolding ereal_max_0
      proof (rule lim_imp_Liminf[symmetric], unfold lim_ereal)
        have "(\<lambda>i. ?diff i x) ----> 2 * w x - \<bar>u' x - u' x\<bar>"
          using u'[OF x] by (safe intro!: tendsto_intros)
        then show "(\<lambda>i. max 0 (?diff i x)) ----> max 0 (2 * w x)"
          by (auto intro!: tendsto_real_max simp add: lim_ereal)
      qed (rule trivial_limit_sequentially)
    qed
    also have "\<dots> \<le> liminf (\<lambda>n. \<integral>\<^isup>+ x. max 0 (ereal (?diff n x)) \<partial>M)"
      using u'_borel w u unfolding integrable_def
      by (intro positive_integral_lim_INF) (auto intro!: positive_integral_lim_INF)
    also have "\<dots> = (\<integral>\<^isup>+ x. ereal (2 * w x) \<partial>M) -
        limsup (\<lambda>n. \<integral>\<^isup>+ x. ereal \<bar>u n x - u' x\<bar> \<partial>M)"
      unfolding PI_diff positive_integral_max_0
      using positive_integral_positive[of "\<lambda>x. ereal (2 * w x)"]
      by (subst liminf_ereal_cminus) auto
    finally show ?thesis
      using neq_0 I2w_fin positive_integral_positive[of "\<lambda>x. ereal (2 * w x)"] pos
      unfolding positive_integral_max_0
      by (cases rule: ereal2_cases[of "\<integral>\<^isup>+ x. ereal (2 * w x) \<partial>M" "limsup (\<lambda>n. \<integral>\<^isup>+ x. ereal \<bar>u n x - u' x\<bar> \<partial>M)"])
         auto
  qed

  have "liminf ?f \<le> limsup ?f"
    by (intro ereal_Liminf_le_Limsup trivial_limit_sequentially)
  moreover
  { have "0 = liminf (\<lambda>n. 0 :: ereal)" by (simp add: Liminf_const)
    also have "\<dots> \<le> liminf ?f"
      by (intro liminf_mono positive_integral_positive)
    finally have "0 \<le> liminf ?f" . }
  ultimately have liminf_limsup_eq: "liminf ?f = ereal 0" "limsup ?f = ereal 0"
    using `limsup ?f = 0` by auto
  have "\<And>n. (\<integral>\<^isup>+ x. ereal \<bar>u n x - u' x\<bar> \<partial>M) = ereal (\<integral>x. \<bar>u n x - u' x\<bar> \<partial>M)"
    using diff positive_integral_positive
    by (subst integral_eq_positive_integral) (auto simp: ereal_real integrable_def)
  then show ?lim_diff
    using ereal_Liminf_eq_Limsup[OF trivial_limit_sequentially liminf_limsup_eq]
    by (simp add: lim_ereal)

  show ?lim
  proof (rule LIMSEQ_I)
    fix r :: real assume "0 < r"
    from LIMSEQ_D[OF `?lim_diff` this]
    obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> (\<integral>x. \<bar>u n x - u' x\<bar> \<partial>M) < r"
      using diff by (auto simp: integral_positive)

    show "\<exists>N. \<forall>n\<ge>N. norm (integral\<^isup>L M (u n) - integral\<^isup>L M u') < r"
    proof (safe intro!: exI[of _ N])
      fix n assume "N \<le> n"
      have "\<bar>integral\<^isup>L M (u n) - integral\<^isup>L M u'\<bar> = \<bar>(\<integral>x. u n x - u' x \<partial>M)\<bar>"
        using u `integrable M u'` by (auto simp: integral_diff)
      also have "\<dots> \<le> (\<integral>x. \<bar>u n x - u' x\<bar> \<partial>M)" using u `integrable M u'`
        by (rule_tac integral_triangle_inequality) (auto intro!: integral_diff)
      also note N[OF `N \<le> n`]
      finally show "norm (integral\<^isup>L M (u n) - integral\<^isup>L M u') < r" by simp
    qed
  qed
qed

lemma (in measure_space) integral_sums:
  assumes borel: "\<And>i. integrable M (f i)"
  and summable: "\<And>x. x \<in> space M \<Longrightarrow> summable (\<lambda>i. \<bar>f i x\<bar>)"
  and sums: "summable (\<lambda>i. (\<integral>x. \<bar>f i x\<bar> \<partial>M))"
  shows "integrable M (\<lambda>x. (\<Sum>i. f i x))" (is "integrable M ?S")
  and "(\<lambda>i. integral\<^isup>L M (f i)) sums (\<integral>x. (\<Sum>i. f i x) \<partial>M)" (is ?integral)
proof -
  have "\<forall>x\<in>space M. \<exists>w. (\<lambda>i. \<bar>f i x\<bar>) sums w"
    using summable unfolding summable_def by auto
  from bchoice[OF this]
  obtain w where w: "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. \<bar>f i x\<bar>) sums w x" by auto

  let ?w = "\<lambda>y. if y \<in> space M then w y else 0"

  obtain x where abs_sum: "(\<lambda>i. (\<integral>x. \<bar>f i x\<bar> \<partial>M)) sums x"
    using sums unfolding summable_def ..

  have 1: "\<And>n. integrable M (\<lambda>x. \<Sum>i = 0..<n. f i x)"
    using borel by (auto intro!: integral_setsum)

  { fix j x assume [simp]: "x \<in> space M"
    have "\<bar>\<Sum>i = 0..< j. f i x\<bar> \<le> (\<Sum>i = 0..< j. \<bar>f i x\<bar>)" by (rule setsum_abs)
    also have "\<dots> \<le> w x" using w[of x] series_pos_le[of "\<lambda>i. \<bar>f i x\<bar>"] unfolding sums_iff by auto
    finally have "\<bar>\<Sum>i = 0..<j. f i x\<bar> \<le> ?w x" by simp }
  note 2 = this

  have 3: "integrable M ?w"
  proof (rule integral_monotone_convergence(1))
    let ?F = "\<lambda>n y. (\<Sum>i = 0..<n. \<bar>f i y\<bar>)"
    let ?w' = "\<lambda>n y. if y \<in> space M then ?F n y else 0"
    have "\<And>n. integrable M (?F n)"
      using borel by (auto intro!: integral_setsum integrable_abs)
    thus "\<And>n. integrable M (?w' n)" by (simp cong: integrable_cong)
    show "mono ?w'"
      by (auto simp: mono_def le_fun_def intro!: setsum_mono2)
    { fix x show "(\<lambda>n. ?w' n x) ----> ?w x"
        using w by (cases "x \<in> space M") (simp_all add: tendsto_const sums_def) }
    have *: "\<And>n. integral\<^isup>L M (?w' n) = (\<Sum>i = 0..< n. (\<integral>x. \<bar>f i x\<bar> \<partial>M))"
      using borel by (simp add: integral_setsum integrable_abs cong: integral_cong)
    from abs_sum
    show "(\<lambda>i. integral\<^isup>L M (?w' i)) ----> x" unfolding * sums_def .
  qed

  from summable[THEN summable_rabs_cancel]
  have 4: "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>n. \<Sum>i = 0..<n. f i x) ----> (\<Sum>i. f i x)"
    by (auto intro: summable_sumr_LIMSEQ_suminf)

  note int = integral_dominated_convergence(1,3)[OF 1 2 3 4]

  from int show "integrable M ?S" by simp

  show ?integral unfolding sums_def integral_setsum(1)[symmetric, OF borel]
    using int(2) by simp
qed

section "Lebesgue integration on countable spaces"

lemma (in measure_space) integral_on_countable:
  assumes f: "f \<in> borel_measurable M"
  and bij: "bij_betw enum S (f ` space M)"
  and enum_zero: "enum ` (-S) \<subseteq> {0}"
  and fin: "\<And>x. x \<noteq> 0 \<Longrightarrow> \<mu> (f -` {x} \<inter> space M) \<noteq> \<infinity>"
  and abs_summable: "summable (\<lambda>r. \<bar>enum r * real (\<mu> (f -` {enum r} \<inter> space M))\<bar>)"
  shows "integrable M f"
  and "(\<lambda>r. enum r * real (\<mu> (f -` {enum r} \<inter> space M))) sums integral\<^isup>L M f" (is ?sums)
proof -
  let ?A = "\<lambda>r. f -` {enum r} \<inter> space M"
  let ?F = "\<lambda>r x. enum r * indicator (?A r) x"
  have enum_eq: "\<And>r. enum r * real (\<mu> (?A r)) = integral\<^isup>L M (?F r)"
    using f fin by (simp add: borel_measurable_vimage integral_cmul_indicator)

  { fix x assume "x \<in> space M"
    hence "f x \<in> enum ` S" using bij unfolding bij_betw_def by auto
    then obtain i where "i\<in>S" "enum i = f x" by auto
    have F: "\<And>j. ?F j x = (if j = i then f x else 0)"
    proof cases
      fix j assume "j = i"
      thus "?thesis j" using `x \<in> space M` `enum i = f x` by (simp add: indicator_def)
    next
      fix j assume "j \<noteq> i"
      show "?thesis j" using bij `i \<in> S` `j \<noteq> i` `enum i = f x` enum_zero
        by (cases "j \<in> S") (auto simp add: indicator_def bij_betw_def inj_on_def)
    qed
    hence F_abs: "\<And>j. \<bar>if j = i then f x else 0\<bar> = (if j = i then \<bar>f x\<bar> else 0)" by auto
    have "(\<lambda>i. ?F i x) sums f x"
         "(\<lambda>i. \<bar>?F i x\<bar>) sums \<bar>f x\<bar>"
      by (auto intro!: sums_single simp: F F_abs) }
  note F_sums_f = this(1) and F_abs_sums_f = this(2)

  have int_f: "integral\<^isup>L M f = (\<integral>x. (\<Sum>r. ?F r x) \<partial>M)" "integrable M f = integrable M (\<lambda>x. \<Sum>r. ?F r x)"
    using F_sums_f by (auto intro!: integral_cong integrable_cong simp: sums_iff)

  { fix r
    have "(\<integral>x. \<bar>?F r x\<bar> \<partial>M) = (\<integral>x. \<bar>enum r\<bar> * indicator (?A r) x \<partial>M)"
      by (auto simp: indicator_def intro!: integral_cong)
    also have "\<dots> = \<bar>enum r\<bar> * real (\<mu> (?A r))"
      using f fin by (simp add: borel_measurable_vimage integral_cmul_indicator)
    finally have "(\<integral>x. \<bar>?F r x\<bar> \<partial>M) = \<bar>enum r * real (\<mu> (?A r))\<bar>"
      using f by (subst (2) abs_mult_pos[symmetric]) (auto intro!: real_of_ereal_pos measurable_sets) }
  note int_abs_F = this

  have 1: "\<And>i. integrable M (\<lambda>x. ?F i x)"
    using f fin by (simp add: borel_measurable_vimage integral_cmul_indicator)

  have 2: "\<And>x. x \<in> space M \<Longrightarrow> summable (\<lambda>i. \<bar>?F i x\<bar>)"
    using F_abs_sums_f unfolding sums_iff by auto

  from integral_sums(2)[OF 1 2, unfolded int_abs_F, OF _ abs_summable]
  show ?sums unfolding enum_eq int_f by simp

  from integral_sums(1)[OF 1 2, unfolded int_abs_F, OF _ abs_summable]
  show "integrable M f" unfolding int_f by simp
qed

section "Lebesgue integration on finite space"

lemma (in measure_space) integral_on_finite:
  assumes f: "f \<in> borel_measurable M" and finite: "finite (f`space M)"
  and fin: "\<And>x. x \<noteq> 0 \<Longrightarrow> \<mu> (f -` {x} \<inter> space M) \<noteq> \<infinity>"
  shows "integrable M f"
  and "(\<integral>x. f x \<partial>M) =
    (\<Sum> r \<in> f`space M. r * real (\<mu> (f -` {r} \<inter> space M)))" (is "?integral")
proof -
  let ?A = "\<lambda>r. f -` {r} \<inter> space M"
  let ?S = "\<lambda>x. \<Sum>r\<in>f`space M. r * indicator (?A r) x"

  { fix x assume "x \<in> space M"
    have "f x = (\<Sum>r\<in>f`space M. if x \<in> ?A r then r else 0)"
      using finite `x \<in> space M` by (simp add: setsum_cases)
    also have "\<dots> = ?S x"
      by (auto intro!: setsum_cong)
    finally have "f x = ?S x" . }
  note f_eq = this

  have f_eq_S: "integrable M f \<longleftrightarrow> integrable M ?S" "integral\<^isup>L M f = integral\<^isup>L M ?S"
    by (auto intro!: integrable_cong integral_cong simp only: f_eq)

  show "integrable M f" ?integral using fin f f_eq_S
    by (simp_all add: integral_cmul_indicator borel_measurable_vimage)
qed

lemma (in finite_measure_space) simple_function_finite[simp, intro]: "simple_function M f"
  unfolding simple_function_def using finite_space by auto

lemma (in finite_measure_space) borel_measurable_finite[intro, simp]: "f \<in> borel_measurable M"
  by (auto intro: borel_measurable_simple_function)

lemma (in finite_measure_space) positive_integral_finite_eq_setsum:
  assumes pos: "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> f x"
  shows "integral\<^isup>P M f = (\<Sum>x \<in> space M. f x * \<mu> {x})"
proof -
  have *: "integral\<^isup>P M f = (\<integral>\<^isup>+ x. (\<Sum>y\<in>space M. f y * indicator {y} x) \<partial>M)"
    by (auto intro!: positive_integral_cong simp add: indicator_def if_distrib setsum_cases[OF finite_space])
  show ?thesis unfolding * using borel_measurable_finite[of f] pos
    by (simp add: positive_integral_setsum positive_integral_cmult_indicator)
qed

lemma (in finite_measure_space) integral_finite_singleton:
  shows "integrable M f"
  and "integral\<^isup>L M f = (\<Sum>x \<in> space M. f x * real (\<mu> {x}))" (is ?I)
proof -
  have *:
    "(\<integral>\<^isup>+ x. max 0 (ereal (f x)) \<partial>M) = (\<Sum>x \<in> space M. max 0 (ereal (f x)) * \<mu> {x})"
    "(\<integral>\<^isup>+ x. max 0 (ereal (- f x)) \<partial>M) = (\<Sum>x \<in> space M. max 0 (ereal (- f x)) * \<mu> {x})"
    by (simp_all add: positive_integral_finite_eq_setsum)
  then show "integrable M f" using finite_space finite_measure
    by (simp add: setsum_Pinfty integrable_def positive_integral_max_0
             split: split_max)
  show ?I using finite_measure *
    apply (simp add: positive_integral_max_0 lebesgue_integral_def)
    apply (subst (1 2) setsum_real_of_ereal[symmetric])
    apply (simp_all split: split_max add: setsum_subtractf[symmetric])
    apply (intro setsum_cong[OF refl])
    apply (simp split: split_max)
    done
qed

end
