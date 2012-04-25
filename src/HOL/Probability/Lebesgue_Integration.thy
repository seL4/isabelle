(*  Title:      HOL/Probability/Lebesgue_Integration.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

header {*Lebesgue Integration*}

theory Lebesgue_Integration
  imports Measure_Space Borel_Space
begin

lemma ereal_minus_eq_PInfty_iff:
  fixes x y :: ereal shows "x - y = \<infinity> \<longleftrightarrow> y = -\<infinity> \<or> x = \<infinity>"
  by (cases x y rule: ereal2_cases) simp_all

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

lemma measurable_sets2[intro]:
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

section "Simple function"

text {*

Our simple functions are not restricted to positive real numbers. Instead
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
    by (auto intro!: finite_UN simp del: UN_simps simp: simple_function_def)
qed

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

lemma borel_measurable_simple_function:
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

lemma simple_function_borel_measurable:
  fixes f :: "'a \<Rightarrow> 'x::{t2_space}"
  assumes "f \<in> borel_measurable M" and "finite (f ` space M)"
  shows "simple_function M f"
  using assms unfolding simple_function_def
  by (auto intro: borel_measurable_vimage)

lemma simple_function_eq_borel_measurable:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "simple_function M f \<longleftrightarrow> finite (f`space M) \<and> f \<in> borel_measurable M"
  using simple_function_borel_measurable[of f] borel_measurable_simple_function[of M f]
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

lemma
  fixes f g :: "'a \<Rightarrow> real" assumes sf: "simple_function M f"
  shows simple_function_ereal[intro, simp]: "simple_function M (\<lambda>x. ereal (f x))"
  by (auto intro!: simple_function_compose1[OF sf])

lemma
  fixes f g :: "'a \<Rightarrow> nat" assumes sf: "simple_function M f"
  shows simple_function_real_of_nat[intro, simp]: "simple_function M (\<lambda>x. real (f x))"
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

lemma borel_measurable_implies_simple_function_sequence':
  fixes u :: "'a \<Rightarrow> ereal"
  assumes u: "u \<in> borel_measurable M"
  obtains f where "\<And>i. simple_function M (f i)" "incseq f" "\<And>i. \<infinity> \<notin> range (f i)"
    "\<And>x. (SUP i. f i x) = max 0 (u x)" "\<And>i x. 0 \<le> f i x"
  using borel_measurable_implies_simple_function_sequence[OF u] by auto

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
      using sets_into_space[OF A] by (auto split: split_if_asm simp: G_def F_def)
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

section "Simple integral"

definition simple_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> ereal) \<Rightarrow> ereal" ("integral\<^isup>S") where
  "integral\<^isup>S M f = (\<Sum>x \<in> f ` space M. x * emeasure M (f -` {x} \<inter> space M))"

syntax
  "_simple_integral" :: "pttrn \<Rightarrow> ereal \<Rightarrow> 'a measure \<Rightarrow> ereal" ("\<integral>\<^isup>S _. _ \<partial>_" [60,61] 110)

translations
  "\<integral>\<^isup>S x. f \<partial>M" == "CONST simple_integral M (%x. f)"

lemma simple_integral_cong:
  assumes "\<And>t. t \<in> space M \<Longrightarrow> f t = g t"
  shows "integral\<^isup>S M f = integral\<^isup>S M g"
proof -
  have "f ` space M = g ` space M"
    "\<And>x. f -` {x} \<inter> space M = g -` {x} \<inter> space M"
    using assms by (auto intro!: image_eqI)
  thus ?thesis unfolding simple_integral_def by simp
qed

lemma simple_integral_const[simp]:
  "(\<integral>\<^isup>Sx. c \<partial>M) = c * (emeasure M) (space M)"
proof (cases "space M = {}")
  case True thus ?thesis unfolding simple_integral_def by simp
next
  case False hence "(\<lambda>x. c) ` space M = {c}" by auto
  thus ?thesis unfolding simple_integral_def by simp
qed

lemma simple_function_partition:
  assumes f: "simple_function M f" and g: "simple_function M g"
  shows "integral\<^isup>S M f = (\<Sum>A\<in>(\<lambda>x. f -` {f x} \<inter> g -` {g x} \<inter> space M) ` space M. the_elem (f`A) * (emeasure M) A)"
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
    with sets have "(emeasure M) (f -` {f x} \<inter> space M) = setsum (emeasure M) (?sub (f x))"
      by (subst setsum_emeasure) (auto simp: disjoint_family_on_def) }
  hence "integral\<^isup>S M f = (\<Sum>(x,A)\<in>?SIGMA. x * (emeasure M) A)"
    unfolding simple_integral_def using f sets
    by (subst setsum_Sigma[symmetric])
       (auto intro!: setsum_cong setsum_ereal_right_distrib)
  also have "\<dots> = (\<Sum>A\<in>?p ` space M. the_elem (f`A) * (emeasure M) A)"
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

lemma simple_integral_add[simp]:
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

lemma simple_integral_setsum[simp]:
  assumes "\<And>i x. i \<in> P \<Longrightarrow> 0 \<le> f i x"
  assumes "\<And>i. i \<in> P \<Longrightarrow> simple_function M (f i)"
  shows "(\<integral>\<^isup>Sx. (\<Sum>i\<in>P. f i x) \<partial>M) = (\<Sum>i\<in>P. integral\<^isup>S M (f i))"
proof cases
  assume "finite P"
  from this assms show ?thesis
    by induct (auto simp: simple_function_setsum simple_integral_add setsum_nonneg)
qed auto

lemma simple_integral_mult[simp]:
  assumes f: "simple_function M f" "\<And>x. 0 \<le> f x"
  shows "(\<integral>\<^isup>Sx. c * f x \<partial>M) = c * integral\<^isup>S M f"
proof -
  note mult = simple_function_mult[OF simple_function_const[of _ c] f(1)]
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

lemma simple_integral_mono_AE:
  assumes f: "simple_function M f" and g: "simple_function M g"
  and mono: "AE x in M. f x \<le> g x"
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
    show "the_elem (f`?S x) * (emeasure M) (?S x) \<le> the_elem (g`?S x) * (emeasure M) (?S x)"
    proof (cases "f x \<le> g x")
      case True then show ?thesis
        using * assms(1,2)[THEN simple_functionD(2)]
        by (auto intro!: ereal_mult_right_mono)
    next
      case False
      obtain N where N: "{x\<in>space M. \<not> f x \<le> g x} \<subseteq> N" "N \<in> sets M" "(emeasure M) N = 0"
        using mono by (auto elim!: AE_E)
      have "?S x \<subseteq> N" using N `x \<in> space M` False by auto
      moreover have "?S x \<in> sets M" using assms
        by (rule_tac Int) (auto intro!: simple_functionD)
      ultimately have "(emeasure M) (?S x) \<le> (emeasure M) N"
        using `N \<in> sets M` by (auto intro!: emeasure_mono)
      moreover have "0 \<le> (emeasure M) (?S x)"
        using assms(1,2)[THEN simple_functionD(2)] by auto
      ultimately have "(emeasure M) (?S x) = 0" using `(emeasure M) N = 0` by auto
      then show ?thesis by simp
    qed
  qed
qed

lemma simple_integral_mono:
  assumes "simple_function M f" and "simple_function M g"
  and mono: "\<And> x. x \<in> space M \<Longrightarrow> f x \<le> g x"
  shows "integral\<^isup>S M f \<le> integral\<^isup>S M g"
  using assms by (intro simple_integral_mono_AE) auto

lemma simple_integral_cong_AE:
  assumes "simple_function M f" and "simple_function M g"
  and "AE x in M. f x = g x"
  shows "integral\<^isup>S M f = integral\<^isup>S M g"
  using assms by (auto simp: eq_iff intro!: simple_integral_mono_AE)

lemma simple_integral_cong':
  assumes sf: "simple_function M f" "simple_function M g"
  and mea: "(emeasure M) {x\<in>space M. f x \<noteq> g x} = 0"
  shows "integral\<^isup>S M f = integral\<^isup>S M g"
proof (intro simple_integral_cong_AE sf AE_I)
  show "(emeasure M) {x\<in>space M. f x \<noteq> g x} = 0" by fact
  show "{x \<in> space M. f x \<noteq> g x} \<in> sets M"
    using sf[THEN borel_measurable_simple_function] by auto
qed simp

lemma simple_integral_indicator:
  assumes "A \<in> sets M"
  assumes "simple_function M f"
  shows "(\<integral>\<^isup>Sx. f x * indicator A x \<partial>M) =
    (\<Sum>x \<in> f ` space M. x * (emeasure M) (f -` {x} \<inter> space M \<inter> A))"
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
    (\<Sum>x \<in> f ` space M \<union> {0}. x * (emeasure M) (f -` {x} \<inter> space M \<inter> A))"
    unfolding simple_integral_def I
  proof (rule setsum_mono_zero_cong_left)
    show "finite (f ` space M \<union> {0})"
      using assms(2) unfolding simple_function_def by auto
    show "f ` A \<union> {0} \<subseteq> f`space M \<union> {0}"
      using sets_into_space[OF assms(1)] by auto
    have "\<And>x. f x \<notin> f ` A \<Longrightarrow> f -` {f x} \<inter> space M \<inter> A = {}"
      by (auto simp: image_iff)
    thus "\<forall>i\<in>f ` space M \<union> {0} - (f ` A \<union> {0}).
      i * (emeasure M) (f -` {i} \<inter> space M \<inter> A) = 0" by auto
  next
    fix x assume "x \<in> f`A \<union> {0}"
    hence "x \<noteq> 0 \<Longrightarrow> ?I -` {x} \<inter> space M = f -` {x} \<inter> space M \<inter> A"
      by (auto simp: indicator_def split: split_if_asm)
    thus "x * (emeasure M) (?I -` {x} \<inter> space M) =
      x * (emeasure M) (f -` {x} \<inter> space M \<inter> A)" by (cases "x = 0") simp_all
  qed
  show ?thesis unfolding *
    using assms(2) unfolding simple_function_def
    by (auto intro!: setsum_mono_zero_cong_right)
qed

lemma simple_integral_indicator_only[simp]:
  assumes "A \<in> sets M"
  shows "integral\<^isup>S M (indicator A) = emeasure M A"
proof cases
  assume "space M = {}" hence "A = {}" using sets_into_space[OF assms] by auto
  thus ?thesis unfolding simple_integral_def using `space M = {}` by auto
next
  assume "space M \<noteq> {}" hence "(\<lambda>x. 1) ` space M = {1::ereal}" by auto
  thus ?thesis
    using simple_integral_indicator[OF assms simple_function_const[of _ 1]]
    using sets_into_space[OF assms]
    by (auto intro!: arg_cong[where f="(emeasure M)"])
qed

lemma simple_integral_null_set:
  assumes "simple_function M u" "\<And>x. 0 \<le> u x" and "N \<in> null_sets M"
  shows "(\<integral>\<^isup>Sx. u x * indicator N x \<partial>M) = 0"
proof -
  have "AE x in M. indicator N x = (0 :: ereal)"
    using `N \<in> null_sets M` by (auto simp: indicator_def intro!: AE_I[of _ _ N])
  then have "(\<integral>\<^isup>Sx. u x * indicator N x \<partial>M) = (\<integral>\<^isup>Sx. 0 \<partial>M)"
    using assms apply (intro simple_integral_cong_AE) by auto
  then show ?thesis by simp
qed

lemma simple_integral_cong_AE_mult_indicator:
  assumes sf: "simple_function M f" and eq: "AE x in M. x \<in> S" and "S \<in> sets M"
  shows "integral\<^isup>S M f = (\<integral>\<^isup>Sx. f x * indicator S x \<partial>M)"
  using assms by (intro simple_integral_cong_AE) auto

lemma simple_integral_distr:
  assumes T: "T \<in> measurable M M'"
    and f: "simple_function M' f"
  shows "integral\<^isup>S (distr M M' T) f = (\<integral>\<^isup>S x. f (T x) \<partial>M)"
  unfolding simple_integral_def
proof (intro setsum_mono_zero_cong_right ballI)
  show "(\<lambda>x. f (T x)) ` space M \<subseteq> f ` space (distr M M' T)"
    using T unfolding measurable_def by auto
  show "finite (f ` space (distr M M' T))"
    using f unfolding simple_function_def by auto
next
  fix i assume "i \<in> f ` space (distr M M' T) - (\<lambda>x. f (T x)) ` space M"
  then have "T -` (f -` {i} \<inter> space (distr M M' T)) \<inter> space M = {}" by (auto simp: image_iff)
  with f[THEN simple_functionD(2), of "{i}"]
  show "i * emeasure (distr M M' T) (f -` {i} \<inter> space (distr M M' T)) = 0"
    using T by (simp add: emeasure_distr)
next
  fix i assume "i \<in> (\<lambda>x. f (T x)) ` space M"
  then have "T -` (f -` {i} \<inter> space M') \<inter> space M = (\<lambda>x. f (T x)) -` {i} \<inter> space M"
    using T unfolding measurable_def by auto
  with f[THEN simple_functionD(2), of "{i}"] T
  show "i * emeasure (distr M M' T) (f -` {i} \<inter> space (distr M M' T)) =
      i * (emeasure M) ((\<lambda>x. f (T x)) -` {i} \<inter> space M)"
    by (auto simp add: emeasure_distr)
qed

lemma simple_integral_cmult_indicator:
  assumes A: "A \<in> sets M"
  shows "(\<integral>\<^isup>Sx. c * indicator A x \<partial>M) = c * (emeasure M) A"
  using simple_integral_mult[OF simple_function_indicator[OF A]]
  unfolding simple_integral_indicator_only[OF A] by simp

lemma simple_integral_positive:
  assumes f: "simple_function M f" and ae: "AE x in M. 0 \<le> f x"
  shows "0 \<le> integral\<^isup>S M f"
proof -
  have "integral\<^isup>S M (\<lambda>x. 0) \<le> integral\<^isup>S M f"
    using simple_integral_mono_AE[OF _ f ae] by auto
  then show ?thesis by simp
qed

section "Continuous positive integration"

definition positive_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> ereal) \<Rightarrow> ereal" ("integral\<^isup>P") where
  "integral\<^isup>P M f = (SUP g : {g. simple_function M g \<and> g \<le> max 0 \<circ> f}. integral\<^isup>S M g)"

syntax
  "_positive_integral" :: "pttrn \<Rightarrow> ereal \<Rightarrow> 'a measure \<Rightarrow> ereal" ("\<integral>\<^isup>+ _. _ \<partial>_" [60,61] 110)

translations
  "\<integral>\<^isup>+ x. f \<partial>M" == "CONST positive_integral M (%x. f)"

lemma positive_integral_positive:
  "0 \<le> integral\<^isup>P M f"
  by (auto intro!: SUP_upper2[of "\<lambda>x. 0"] simp: positive_integral_def le_fun_def)

lemma positive_integral_not_MInfty[simp]: "integral\<^isup>P M f \<noteq> -\<infinity>"
  using positive_integral_positive[of M f] by auto

lemma positive_integral_def_finite:
  "integral\<^isup>P M f = (SUP g : {g. simple_function M g \<and> g \<le> max 0 \<circ> f \<and> range g \<subseteq> {0 ..< \<infinity>}}. integral\<^isup>S M g)"
    (is "_ = SUPR ?A ?f")
  unfolding positive_integral_def
proof (safe intro!: antisym SUP_least)
  fix g assume g: "simple_function M g" "g \<le> max 0 \<circ> f"
  let ?G = "{x \<in> space M. \<not> g x \<noteq> \<infinity>}"
  note gM = g(1)[THEN borel_measurable_simple_function]
  have \<mu>G_pos: "0 \<le> (emeasure M) ?G" using gM by auto
  let ?g = "\<lambda>y x. if g x = \<infinity> then y else max 0 (g x)"
  from g gM have g_in_A: "\<And>y. 0 \<le> y \<Longrightarrow> y \<noteq> \<infinity> \<Longrightarrow> ?g y \<in> ?A"
    apply (safe intro!: simple_function_max simple_function_If)
    apply (force simp: max_def le_fun_def split: split_if_asm)+
    done
  show "integral\<^isup>S M g \<le> SUPR ?A ?f"
  proof cases
    have g0: "?g 0 \<in> ?A" by (intro g_in_A) auto
    assume "(emeasure M) ?G = 0"
    with gM have "AE x in M. x \<notin> ?G"
      by (auto simp add: AE_iff_null intro!: null_setsI)
    with gM g show ?thesis
      by (intro SUP_upper2[OF g0] simple_integral_mono_AE)
         (auto simp: max_def intro!: simple_function_If)
  next
    assume \<mu>G: "(emeasure M) ?G \<noteq> 0"
    have "SUPR ?A (integral\<^isup>S M) = \<infinity>"
    proof (intro SUP_PInfty)
      fix n :: nat
      let ?y = "ereal (real n) / (if (emeasure M) ?G = \<infinity> then 1 else (emeasure M) ?G)"
      have "0 \<le> ?y" "?y \<noteq> \<infinity>" using \<mu>G \<mu>G_pos by (auto simp: ereal_divide_eq)
      then have "?g ?y \<in> ?A" by (rule g_in_A)
      have "real n \<le> ?y * (emeasure M) ?G"
        using \<mu>G \<mu>G_pos by (cases "(emeasure M) ?G") (auto simp: field_simps)
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

lemma positive_integral_mono_AE:
  assumes ae: "AE x in M. u x \<le> v x" shows "integral\<^isup>P M u \<le> integral\<^isup>P M v"
  unfolding positive_integral_def
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
  moreover have "integral\<^isup>S M n \<le> integral\<^isup>S M ?n"
    using ae_N N n by (auto intro!: simple_integral_mono_AE)
  ultimately show "\<exists>m\<in>{g. simple_function M g \<and> g \<le> max 0 \<circ> v}. integral\<^isup>S M n \<le> integral\<^isup>S M m"
    by force
qed

lemma positive_integral_mono:
  "(\<And>x. x \<in> space M \<Longrightarrow> u x \<le> v x) \<Longrightarrow> integral\<^isup>P M u \<le> integral\<^isup>P M v"
  by (auto intro: positive_integral_mono_AE)

lemma positive_integral_cong_AE:
  "AE x in M. u x = v x \<Longrightarrow> integral\<^isup>P M u = integral\<^isup>P M v"
  by (auto simp: eq_iff intro!: positive_integral_mono_AE)

lemma positive_integral_cong:
  "(\<And>x. x \<in> space M \<Longrightarrow> u x = v x) \<Longrightarrow> integral\<^isup>P M u = integral\<^isup>P M v"
  by (auto intro: positive_integral_cong_AE)

lemma positive_integral_eq_simple_integral:
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

lemma positive_integral_eq_simple_integral_AE:
  assumes f: "simple_function M f" "AE x in M. 0 \<le> f x" shows "integral\<^isup>P M f = integral\<^isup>S M f"
proof -
  have "AE x in M. f x = max 0 (f x)" using f by (auto split: split_max)
  with f have "integral\<^isup>P M f = integral\<^isup>S M (\<lambda>x. max 0 (f x))"
    by (simp cong: positive_integral_cong_AE simple_integral_cong_AE
             add: positive_integral_eq_simple_integral)
  with assms show ?thesis
    by (auto intro!: simple_integral_cong_AE split: split_max)
qed

lemma positive_integral_SUP_approx:
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
          by (auto simp add: less_Sup_iff)
        hence "a * u x \<le> f i x" by auto
        thus ?thesis using `x \<in> space M` by auto
      qed
    qed
    then show "?thesis i" using SUP_emeasure_incseq[OF 1 2] by simp
  qed

  have "integral\<^isup>S M u = (SUP i. integral\<^isup>S M (?uB i))"
    unfolding simple_integral_indicator[OF B `simple_function M u`]
  proof (subst SUPR_ereal_setsum, safe)
    fix x n assume "x \<in> space M"
    with u_range show "incseq (\<lambda>i. u x * (emeasure M) (?B' (u x) i))" "\<And>i. 0 \<le> u x * (emeasure M) (?B' (u x) i)"
      using B_mono B_u by (auto intro!: emeasure_mono ereal_mult_left_mono incseq_SucI simp: ereal_zero_le_0_iff)
  next
    show "integral\<^isup>S M u = (\<Sum>i\<in>u ` space M. SUP n. i * (emeasure M) (?B' i n))"
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

lemma incseq_positive_integral:
  assumes "incseq f" shows "incseq (\<lambda>i. integral\<^isup>P M (f i))"
proof -
  have "\<And>i x. f i x \<le> f (Suc i) x"
    using assms by (auto dest!: incseq_SucD simp: le_fun_def)
  then show ?thesis
    by (auto intro!: incseq_SucI positive_integral_mono)
qed

text {* Beppo-Levi monotone convergence theorem *}
lemma positive_integral_monotone_convergence_SUP:
  assumes f: "incseq f" "\<And>i. f i \<in> borel_measurable M" "\<And>i x. 0 \<le> f i x"
  shows "(\<integral>\<^isup>+ x. (SUP i. f i x) \<partial>M) = (SUP i. integral\<^isup>P M (f i))"
proof (rule antisym)
  show "(SUP j. integral\<^isup>P M (f j)) \<le> (\<integral>\<^isup>+ x. (SUP i. f i x) \<partial>M)"
    by (auto intro!: SUP_least SUP_upper positive_integral_mono)
next
  show "(\<integral>\<^isup>+ x. (SUP i. f i x) \<partial>M) \<le> (SUP j. integral\<^isup>P M (f j))"
    unfolding positive_integral_def_finite[of _ "\<lambda>x. SUP i. f i x"]
  proof (safe intro!: SUP_least)
    fix g assume g: "simple_function M g"
      and "g \<le> max 0 \<circ> (\<lambda>x. SUP i. f i x)" "range g \<subseteq> {0..<\<infinity>}"
    moreover then have "\<And>x. 0 \<le> (SUP i. f i x)" and g': "g`space M \<subseteq> {0..<\<infinity>}"
      using f by (auto intro!: SUP_upper2)
    ultimately show "integral\<^isup>S M g \<le> (SUP j. integral\<^isup>P M (f j))"
      by (intro  positive_integral_SUP_approx[OF f g _ g'])
         (auto simp: le_fun_def max_def)
  qed
qed

lemma positive_integral_monotone_convergence_SUP_AE:
  assumes f: "\<And>i. AE x in M. f i x \<le> f (Suc i) x \<and> 0 \<le> f i x" "\<And>i. f i \<in> borel_measurable M"
  shows "(\<integral>\<^isup>+ x. (SUP i. f i x) \<partial>M) = (SUP i. integral\<^isup>P M (f i))"
proof -
  from f have "AE x in M. \<forall>i. f i x \<le> f (Suc i) x \<and> 0 \<le> f i x"
    by (simp add: AE_all_countable)
  from this[THEN AE_E] guess N . note N = this
  let ?f = "\<lambda>i x. if x \<in> space M - N then f i x else 0"
  have f_eq: "AE x in M. \<forall>i. ?f i x = f i x" using N by (auto intro!: AE_I[of _ _ N])
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

lemma positive_integral_monotone_convergence_SUP_AE_incseq:
  assumes f: "incseq f" "\<And>i. AE x in M. 0 \<le> f i x" and borel: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<integral>\<^isup>+ x. (SUP i. f i x) \<partial>M) = (SUP i. integral\<^isup>P M (f i))"
  using f[unfolded incseq_Suc_iff le_fun_def]
  by (intro positive_integral_monotone_convergence_SUP_AE[OF _ borel])
     auto

lemma positive_integral_monotone_convergence_simple:
  assumes f: "incseq f" "\<And>i x. 0 \<le> f i x" "\<And>i. simple_function M (f i)"
  shows "(SUP i. integral\<^isup>S M (f i)) = (\<integral>\<^isup>+x. (SUP i. f i x) \<partial>M)"
  using assms unfolding positive_integral_monotone_convergence_SUP[OF f(1)
    f(3)[THEN borel_measurable_simple_function] f(2)]
  by (auto intro!: positive_integral_eq_simple_integral[symmetric] arg_cong[where f="SUPR UNIV"] ext)

lemma positive_integral_max_0:
  "(\<integral>\<^isup>+x. max 0 (f x) \<partial>M) = integral\<^isup>P M f"
  by (simp add: le_fun_def positive_integral_def)

lemma positive_integral_cong_pos:
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

lemma SUP_simple_integral_sequences:
  assumes f: "incseq f" "\<And>i x. 0 \<le> f i x" "\<And>i. simple_function M (f i)"
  and g: "incseq g" "\<And>i x. 0 \<le> g i x" "\<And>i. simple_function M (g i)"
  and eq: "AE x in M. (SUP i. f i x) = (SUP i. g i x)"
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

lemma positive_integral_const[simp]:
  "0 \<le> c \<Longrightarrow> (\<integral>\<^isup>+ x. c \<partial>M) = c * (emeasure M) (space M)"
  by (subst positive_integral_eq_simple_integral) auto

lemma positive_integral_linear:
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
    then show "AE x in M. (SUP i. l i x) = (SUP i. ?L' i x)"
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

lemma positive_integral_cmult:
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x" "0 \<le> c"
  shows "(\<integral>\<^isup>+ x. c * f x \<partial>M) = c * integral\<^isup>P M f"
proof -
  have [simp]: "\<And>x. c * max 0 (f x) = max 0 (c * f x)" using `0 \<le> c`
    by (auto split: split_max simp: ereal_zero_le_0_iff)
  have "(\<integral>\<^isup>+ x. c * f x \<partial>M) = (\<integral>\<^isup>+ x. c * max 0 (f x) \<partial>M)"
    by (simp add: positive_integral_max_0)
  then show ?thesis
    using positive_integral_linear[OF _ _ `0 \<le> c`, of "\<lambda>x. max 0 (f x)" _ "\<lambda>x. 0"] f
    by (auto simp: positive_integral_max_0)
qed

lemma positive_integral_multc:
  assumes "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x" "0 \<le> c"
  shows "(\<integral>\<^isup>+ x. f x * c \<partial>M) = integral\<^isup>P M f * c"
  unfolding mult_commute[of _ c] positive_integral_cmult[OF assms] by simp

lemma positive_integral_indicator[simp]:
  "A \<in> sets M \<Longrightarrow> (\<integral>\<^isup>+ x. indicator A x\<partial>M) = (emeasure M) A"
  by (subst positive_integral_eq_simple_integral)
     (auto simp: simple_function_indicator simple_integral_indicator)

lemma positive_integral_cmult_indicator:
  "0 \<le> c \<Longrightarrow> A \<in> sets M \<Longrightarrow> (\<integral>\<^isup>+ x. c * indicator A x \<partial>M) = c * (emeasure M) A"
  by (subst positive_integral_eq_simple_integral)
     (auto simp: simple_function_indicator simple_integral_indicator)

lemma positive_integral_add:
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
  and g: "g \<in> borel_measurable M" "AE x in M. 0 \<le> g x"
  shows "(\<integral>\<^isup>+ x. f x + g x \<partial>M) = integral\<^isup>P M f + integral\<^isup>P M g"
proof -
  have ae: "AE x in M. max 0 (f x) + max 0 (g x) = max 0 (f x + g x)"
    using assms by (auto split: split_max simp: ereal_add_nonneg_nonneg)
  have "(\<integral>\<^isup>+ x. f x + g x \<partial>M) = (\<integral>\<^isup>+ x. max 0 (f x + g x) \<partial>M)"
    by (simp add: positive_integral_max_0)
  also have "\<dots> = (\<integral>\<^isup>+ x. max 0 (f x) + max 0 (g x) \<partial>M)"
    unfolding ae[THEN positive_integral_cong_AE] ..
  also have "\<dots> = (\<integral>\<^isup>+ x. max 0 (f x) \<partial>M) + (\<integral>\<^isup>+ x. max 0 (g x) \<partial>M)"
    using positive_integral_linear[of "\<lambda>x. max 0 (f x)" _ 1 "\<lambda>x. max 0 (g x)"] f g
    by auto
  finally show ?thesis
    by (simp add: positive_integral_max_0)
qed

lemma positive_integral_setsum:
  assumes "\<And>i. i\<in>P \<Longrightarrow> f i \<in> borel_measurable M" "\<And>i. i\<in>P \<Longrightarrow> AE x in M. 0 \<le> f i x"
  shows "(\<integral>\<^isup>+ x. (\<Sum>i\<in>P. f i x) \<partial>M) = (\<Sum>i\<in>P. integral\<^isup>P M (f i))"
proof cases
  assume f: "finite P"
  from assms have "AE x in M. \<forall>i\<in>P. 0 \<le> f i x" unfolding AE_finite_all[OF f] by auto
  from f this assms(1) show ?thesis
  proof induct
    case (insert i P)
    then have "f i \<in> borel_measurable M" "AE x in M. 0 \<le> f i x"
      "(\<lambda>x. \<Sum>i\<in>P. f i x) \<in> borel_measurable M" "AE x in M. 0 \<le> (\<Sum>i\<in>P. f i x)"
      by (auto intro!: borel_measurable_ereal_setsum setsum_nonneg)
    from positive_integral_add[OF this]
    show ?case using insert by auto
  qed simp
qed simp

lemma positive_integral_Markov_inequality:
  assumes u: "u \<in> borel_measurable M" "AE x in M. 0 \<le> u x" and "A \<in> sets M" and c: "0 \<le> c" "c \<noteq> \<infinity>"
  shows "(emeasure M) ({x\<in>space M. 1 \<le> c * u x} \<inter> A) \<le> c * (\<integral>\<^isup>+ x. u x * indicator A x \<partial>M)"
    (is "(emeasure M) ?A \<le> _ * ?PI")
proof -
  have "?A \<in> sets M"
    using `A \<in> sets M` u by auto
  hence "(emeasure M) ?A = (\<integral>\<^isup>+ x. indicator ?A x \<partial>M)"
    using positive_integral_indicator by simp
  also have "\<dots> \<le> (\<integral>\<^isup>+ x. c * (u x * indicator A x) \<partial>M)" using u c
    by (auto intro!: positive_integral_mono_AE
      simp: indicator_def ereal_zero_le_0_iff)
  also have "\<dots> = c * (\<integral>\<^isup>+ x. u x * indicator A x \<partial>M)"
    using assms
    by (auto intro!: positive_integral_cmult borel_measurable_indicator simp: ereal_zero_le_0_iff)
  finally show ?thesis .
qed

lemma positive_integral_noteq_infinite:
  assumes g: "g \<in> borel_measurable M" "AE x in M. 0 \<le> g x"
  and "integral\<^isup>P M g \<noteq> \<infinity>"
  shows "AE x in M. g x \<noteq> \<infinity>"
proof (rule ccontr)
  assume c: "\<not> (AE x in M. g x \<noteq> \<infinity>)"
  have "(emeasure M) {x\<in>space M. g x = \<infinity>} \<noteq> 0"
    using c g by (auto simp add: AE_iff_null)
  moreover have "0 \<le> (emeasure M) {x\<in>space M. g x = \<infinity>}" using g by (auto intro: measurable_sets)
  ultimately have "0 < (emeasure M) {x\<in>space M. g x = \<infinity>}" by auto
  then have "\<infinity> = \<infinity> * (emeasure M) {x\<in>space M. g x = \<infinity>}" by auto
  also have "\<dots> \<le> (\<integral>\<^isup>+x. \<infinity> * indicator {x\<in>space M. g x = \<infinity>} x \<partial>M)"
    using g by (subst positive_integral_cmult_indicator) auto
  also have "\<dots> \<le> integral\<^isup>P M g"
    using assms by (auto intro!: positive_integral_mono_AE simp: indicator_def)
  finally show False using `integral\<^isup>P M g \<noteq> \<infinity>` by auto
qed

lemma positive_integral_diff:
  assumes f: "f \<in> borel_measurable M"
  and g: "g \<in> borel_measurable M" "AE x in M. 0 \<le> g x"
  and fin: "integral\<^isup>P M g \<noteq> \<infinity>"
  and mono: "AE x in M. g x \<le> f x"
  shows "(\<integral>\<^isup>+ x. f x - g x \<partial>M) = integral\<^isup>P M f - integral\<^isup>P M g"
proof -
  have diff: "(\<lambda>x. f x - g x) \<in> borel_measurable M" "AE x in M. 0 \<le> f x - g x"
    using assms by (auto intro: ereal_diff_positive)
  have pos_f: "AE x in M. 0 \<le> f x" using mono g by auto
  { fix a b :: ereal assume "0 \<le> a" "a \<noteq> \<infinity>" "0 \<le> b" "a \<le> b" then have "b - a + a = b"
      by (cases rule: ereal2_cases[of a b]) auto }
  note * = this
  then have "AE x in M. f x = f x - g x + g x"
    using mono positive_integral_noteq_infinite[OF g fin] assms by auto
  then have **: "integral\<^isup>P M f = (\<integral>\<^isup>+x. f x - g x \<partial>M) + integral\<^isup>P M g"
    unfolding positive_integral_add[OF diff g, symmetric]
    by (rule positive_integral_cong_AE)
  show ?thesis unfolding **
    using fin positive_integral_positive[of M g]
    by (cases rule: ereal2_cases[of "\<integral>\<^isup>+ x. f x - g x \<partial>M" "integral\<^isup>P M g"]) auto
qed

lemma positive_integral_suminf:
  assumes f: "\<And>i. f i \<in> borel_measurable M" "\<And>i. AE x in M. 0 \<le> f i x"
  shows "(\<integral>\<^isup>+ x. (\<Sum>i. f i x) \<partial>M) = (\<Sum>i. integral\<^isup>P M (f i))"
proof -
  have all_pos: "AE x in M. \<forall>i. 0 \<le> f i x"
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
lemma positive_integral_lim_INF:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes u: "\<And>i. u i \<in> borel_measurable M" "\<And>i. AE x in M. 0 \<le> u i x"
  shows "(\<integral>\<^isup>+ x. liminf (\<lambda>n. u n x) \<partial>M) \<le> liminf (\<lambda>n. integral\<^isup>P M (u n))"
proof -
  have pos: "AE x in M. \<forall>i. 0 \<le> u i x" using u by (auto simp: AE_all_countable)
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

lemma positive_integral_null_set:
  assumes "N \<in> null_sets M" shows "(\<integral>\<^isup>+ x. u x * indicator N x \<partial>M) = 0"
proof -
  have "(\<integral>\<^isup>+ x. u x * indicator N x \<partial>M) = (\<integral>\<^isup>+ x. 0 \<partial>M)"
  proof (intro positive_integral_cong_AE AE_I)
    show "{x \<in> space M. u x * indicator N x \<noteq> 0} \<subseteq> N"
      by (auto simp: indicator_def)
    show "(emeasure M) N = 0" "N \<in> sets M"
      using assms by auto
  qed
  then show ?thesis by simp
qed

lemma positive_integral_0_iff:
  assumes u: "u \<in> borel_measurable M" and pos: "AE x in M. 0 \<le> u x"
  shows "integral\<^isup>P M u = 0 \<longleftrightarrow> emeasure M {x\<in>space M. u x \<noteq> 0} = 0"
    (is "_ \<longleftrightarrow> (emeasure M) ?A = 0")
proof -
  have u_eq: "(\<integral>\<^isup>+ x. u x * indicator ?A x \<partial>M) = integral\<^isup>P M u"
    by (auto intro!: positive_integral_cong simp: indicator_def)
  show ?thesis
  proof
    assume "(emeasure M) ?A = 0"
    with positive_integral_null_set[of ?A M u] u
    show "integral\<^isup>P M u = 0" by (simp add: u_eq null_sets_def)
  next
    { fix r :: ereal and n :: nat assume gt_1: "1 \<le> real n * r"
      then have "0 < real n * r" by (cases r) (auto split: split_if_asm simp: one_ereal_def)
      then have "0 \<le> r" by (auto simp add: ereal_zero_less_0_iff) }
    note gt_1 = this
    assume *: "integral\<^isup>P M u = 0"
    let ?M = "\<lambda>n. {x \<in> space M. 1 \<le> real (n::nat) * u x}"
    have "0 = (SUP n. (emeasure M) (?M n \<inter> ?A))"
    proof -
      { fix n :: nat
        from positive_integral_Markov_inequality[OF u pos, of ?A "ereal (real n)"]
        have "(emeasure M) (?M n \<inter> ?A) \<le> 0" unfolding u_eq * using u by simp
        moreover have "0 \<le> (emeasure M) (?M n \<inter> ?A)" using u by auto
        ultimately have "(emeasure M) (?M n \<inter> ?A) = 0" by auto }
      thus ?thesis by simp
    qed
    also have "\<dots> = (emeasure M) (\<Union>n. ?M n \<inter> ?A)"
    proof (safe intro!: SUP_emeasure_incseq)
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

lemma positive_integral_0_iff_AE:
  assumes u: "u \<in> borel_measurable M"
  shows "integral\<^isup>P M u = 0 \<longleftrightarrow> (AE x in M. u x \<le> 0)"
proof -
  have sets: "{x\<in>space M. max 0 (u x) \<noteq> 0} \<in> sets M"
    using u by auto
  from positive_integral_0_iff[of "\<lambda>x. max 0 (u x)"]
  have "integral\<^isup>P M u = 0 \<longleftrightarrow> (AE x in M. max 0 (u x) = 0)"
    unfolding positive_integral_max_0
    using AE_iff_null[OF sets] u by auto
  also have "\<dots> \<longleftrightarrow> (AE x in M. u x \<le> 0)" by (auto split: split_max)
  finally show ?thesis .
qed

lemma positive_integral_const_If:
  "(\<integral>\<^isup>+x. a \<partial>M) = (if 0 \<le> a then a * (emeasure M) (space M) else 0)"
  by (auto intro!: positive_integral_0_iff_AE[THEN iffD2])

lemma positive_integral_subalgebra:
  assumes f: "f \<in> borel_measurable N" "AE x in N. 0 \<le> f x"
  and N: "sets N \<subseteq> sets M" "space N = space M" "\<And>A. A \<in> sets N \<Longrightarrow> emeasure N A = emeasure M A"
  shows "integral\<^isup>P N f = integral\<^isup>P M f"
proof -
  from borel_measurable_implies_simple_function_sequence'[OF f(1)] guess fs . note fs = this
  note sf = simple_function_subalgebra[OF fs(1) N(1,2)]
  from positive_integral_monotone_convergence_simple[OF fs(2,5,1), symmetric]
  have "integral\<^isup>P N f = (SUP i. \<Sum>x\<in>fs i ` space M. x * emeasure N (fs i -` {x} \<inter> space M))"
    unfolding fs(4) positive_integral_max_0
    unfolding simple_integral_def `space N = space M` by simp
  also have "\<dots> = (SUP i. \<Sum>x\<in>fs i ` space M. x * (emeasure M) (fs i -` {x} \<inter> space M))"
    using N simple_functionD(2)[OF fs(1)] unfolding `space N = space M` by auto
  also have "\<dots> = integral\<^isup>P M f"
    using positive_integral_monotone_convergence_simple[OF fs(2,5) sf, symmetric]
    unfolding fs(4) positive_integral_max_0
    unfolding simple_integral_def `space N = space M` by simp
  finally show ?thesis .
qed

section "Lebesgue Integral"

definition integrable :: "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
  "integrable M f \<longleftrightarrow> f \<in> borel_measurable M \<and>
    (\<integral>\<^isup>+ x. ereal (f x) \<partial>M) \<noteq> \<infinity> \<and> (\<integral>\<^isup>+ x. ereal (- f x) \<partial>M) \<noteq> \<infinity>"

lemma integrableD[dest]:
  assumes "integrable M f"
  shows "f \<in> borel_measurable M" "(\<integral>\<^isup>+ x. ereal (f x) \<partial>M) \<noteq> \<infinity>" "(\<integral>\<^isup>+ x. ereal (- f x) \<partial>M) \<noteq> \<infinity>"
  using assms unfolding integrable_def by auto

definition lebesgue_integral :: "'a measure \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" ("integral\<^isup>L") where
  "integral\<^isup>L M f = real ((\<integral>\<^isup>+ x. ereal (f x) \<partial>M)) - real ((\<integral>\<^isup>+ x. ereal (- f x) \<partial>M))"

syntax
  "_lebesgue_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> 'a measure \<Rightarrow> real" ("\<integral> _. _ \<partial>_" [60,61] 110)

translations
  "\<integral> x. f \<partial>M" == "CONST lebesgue_integral M (%x. f)"

lemma integrableE:
  assumes "integrable M f"
  obtains r q where
    "(\<integral>\<^isup>+x. ereal (f x)\<partial>M) = ereal r"
    "(\<integral>\<^isup>+x. ereal (-f x)\<partial>M) = ereal q"
    "f \<in> borel_measurable M" "integral\<^isup>L M f = r - q"
  using assms unfolding integrable_def lebesgue_integral_def
  using positive_integral_positive[of M "\<lambda>x. ereal (f x)"]
  using positive_integral_positive[of M "\<lambda>x. ereal (-f x)"]
  by (cases rule: ereal2_cases[of "(\<integral>\<^isup>+x. ereal (-f x)\<partial>M)" "(\<integral>\<^isup>+x. ereal (f x)\<partial>M)"]) auto

lemma integral_cong:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> f x = g x"
  shows "integral\<^isup>L M f = integral\<^isup>L M g"
  using assms by (simp cong: positive_integral_cong add: lebesgue_integral_def)

lemma integral_cong_AE:
  assumes cong: "AE x in M. f x = g x"
  shows "integral\<^isup>L M f = integral\<^isup>L M g"
proof -
  have *: "AE x in M. ereal (f x) = ereal (g x)"
    "AE x in M. ereal (- f x) = ereal (- g x)" using cong by auto
  show ?thesis
    unfolding *[THEN positive_integral_cong_AE] lebesgue_integral_def ..
qed

lemma integrable_cong_AE:
  assumes borel: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  assumes "AE x in M. f x = g x"
  shows "integrable M f = integrable M g"
proof -
  have "(\<integral>\<^isup>+ x. ereal (f x) \<partial>M) = (\<integral>\<^isup>+ x. ereal (g x) \<partial>M)"
    "(\<integral>\<^isup>+ x. ereal (- f x) \<partial>M) = (\<integral>\<^isup>+ x. ereal (- g x) \<partial>M)"
    using assms by (auto intro!: positive_integral_cong_AE)
  with assms show ?thesis
    by (auto simp: integrable_def)
qed

lemma integrable_cong:
  "(\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> integrable M f \<longleftrightarrow> integrable M g"
  by (simp cong: positive_integral_cong measurable_cong add: integrable_def)

lemma positive_integral_eq_integral:
  assumes f: "integrable M f"
  assumes nonneg: "AE x in M. 0 \<le> f x" 
  shows "(\<integral>\<^isup>+ x. ereal (f x) \<partial>M) = integral\<^isup>L M f"
proof -
  have "(\<integral>\<^isup>+ x. max 0 (ereal (- f x)) \<partial>M) = (\<integral>\<^isup>+ x. 0 \<partial>M)"
    using nonneg by (intro positive_integral_cong_AE) (auto split: split_max)
  with f positive_integral_positive show ?thesis
    by (cases "\<integral>\<^isup>+ x. ereal (f x) \<partial>M")
       (auto simp add: lebesgue_integral_def positive_integral_max_0 integrable_def)
qed
  
lemma integral_eq_positive_integral:
  assumes f: "\<And>x. 0 \<le> f x"
  shows "integral\<^isup>L M f = real (\<integral>\<^isup>+ x. ereal (f x) \<partial>M)"
proof -
  { fix x have "max 0 (ereal (- f x)) = 0" using f[of x] by (simp split: split_max) }
  then have "0 = (\<integral>\<^isup>+ x. max 0 (ereal (- f x)) \<partial>M)" by simp
  also have "\<dots> = (\<integral>\<^isup>+ x. ereal (- f x) \<partial>M)" unfolding positive_integral_max_0 ..
  finally show ?thesis
    unfolding lebesgue_integral_def by simp
qed

lemma integral_minus[intro, simp]:
  assumes "integrable M f"
  shows "integrable M (\<lambda>x. - f x)" "(\<integral>x. - f x \<partial>M) = - integral\<^isup>L M f"
  using assms by (auto simp: integrable_def lebesgue_integral_def)

lemma integral_minus_iff[simp]:
  "integrable M (\<lambda>x. - f x) \<longleftrightarrow> integrable M f"
proof
  assume "integrable M (\<lambda>x. - f x)"
  then have "integrable M (\<lambda>x. - (- f x))"
    by (rule integral_minus)
  then show "integrable M f" by simp
qed (rule integral_minus)

lemma integral_of_positive_diff:
  assumes integrable: "integrable M u" "integrable M v"
  and f_def: "\<And>x. f x = u x - v x" and pos: "\<And>x. 0 \<le> u x" "\<And>x. 0 \<le> v x"
  shows "integrable M f" and "integral\<^isup>L M f = integral\<^isup>L M u - integral\<^isup>L M v"
proof -
  let ?f = "\<lambda>x. max 0 (ereal (f x))"
  let ?mf = "\<lambda>x. max 0 (ereal (- f x))"
  let ?u = "\<lambda>x. max 0 (ereal (u x))"
  let ?v = "\<lambda>x. max 0 (ereal (v x))"

  from borel_measurable_diff[of u M v] integrable
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

lemma integral_linear:
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

lemma integral_add[simp, intro]:
  assumes "integrable M f" "integrable M g"
  shows "integrable M (\<lambda>t. f t + g t)"
  and "(\<integral> t. f t + g t \<partial>M) = integral\<^isup>L M f + integral\<^isup>L M g"
  using assms integral_linear[where a=1] by auto

lemma integral_zero[simp, intro]:
  shows "integrable M (\<lambda>x. 0)" "(\<integral> x.0 \<partial>M) = 0"
  unfolding integrable_def lebesgue_integral_def
  by (auto simp add: borel_measurable_const)

lemma integral_cmult[simp, intro]:
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
        integral_minus(1)[of M "\<lambda>t. - a * f t"]
      unfolding * integral_zero by simp
  qed
  thus ?P ?I by auto
qed

lemma lebesgue_integral_cmult_nonneg:
  assumes f: "f \<in> borel_measurable M" and "0 \<le> c"
  shows "(\<integral>x. c * f x \<partial>M) = c * integral\<^isup>L M f"
proof -
  { have "c * real (integral\<^isup>P M (\<lambda>x. max 0 (ereal (f x)))) =
      real (ereal c * integral\<^isup>P M (\<lambda>x. max 0 (ereal (f x))))"
      by simp
    also have "\<dots> = real (integral\<^isup>P M (\<lambda>x. ereal c * max 0 (ereal (f x))))"
      using f `0 \<le> c` by (subst positive_integral_cmult) auto
    also have "\<dots> = real (integral\<^isup>P M (\<lambda>x. max 0 (ereal (c * f x))))"
      using `0 \<le> c` by (auto intro!: arg_cong[where f=real] positive_integral_cong simp: max_def zero_le_mult_iff)
    finally have "real (integral\<^isup>P M (\<lambda>x. ereal (c * f x))) = c * real (integral\<^isup>P M (\<lambda>x. ereal (f x)))"
      by (simp add: positive_integral_max_0) }
  moreover
  { have "c * real (integral\<^isup>P M (\<lambda>x. max 0 (ereal (- f x)))) =
      real (ereal c * integral\<^isup>P M (\<lambda>x. max 0 (ereal (- f x))))"
      by simp
    also have "\<dots> = real (integral\<^isup>P M (\<lambda>x. ereal c * max 0 (ereal (- f x))))"
      using f `0 \<le> c` by (subst positive_integral_cmult) auto
    also have "\<dots> = real (integral\<^isup>P M (\<lambda>x. max 0 (ereal (- c * f x))))"
      using `0 \<le> c` by (auto intro!: arg_cong[where f=real] positive_integral_cong simp: max_def mult_le_0_iff)
    finally have "real (integral\<^isup>P M (\<lambda>x. ereal (- c * f x))) = c * real (integral\<^isup>P M (\<lambda>x. ereal (- f x)))"
      by (simp add: positive_integral_max_0) }
  ultimately show ?thesis
    by (simp add: lebesgue_integral_def field_simps)
qed

lemma lebesgue_integral_uminus:
  "(\<integral>x. - f x \<partial>M) = - integral\<^isup>L M f"
    unfolding lebesgue_integral_def by simp

lemma lebesgue_integral_cmult:
  assumes f: "f \<in> borel_measurable M"
  shows "(\<integral>x. c * f x \<partial>M) = c * integral\<^isup>L M f"
proof (cases rule: linorder_le_cases)
  assume "0 \<le> c" with f show ?thesis by (rule lebesgue_integral_cmult_nonneg)
next
  assume "c \<le> 0"
  with lebesgue_integral_cmult_nonneg[OF f, of "-c"]
  show ?thesis
    by (simp add: lebesgue_integral_def)
qed

lemma integral_multc:
  assumes "integrable M f"
  shows "(\<integral> x. f x * c \<partial>M) = integral\<^isup>L M f * c"
  unfolding mult_commute[of _ c] integral_cmult[OF assms] ..

lemma integral_mono_AE:
  assumes fg: "integrable M f" "integrable M g"
  and mono: "AE t in M. f t \<le> g t"
  shows "integral\<^isup>L M f \<le> integral\<^isup>L M g"
proof -
  have "AE x in M. ereal (f x) \<le> ereal (g x)"
    using mono by auto
  moreover have "AE x in M. ereal (- g x) \<le> ereal (- f x)"
    using mono by auto
  ultimately show ?thesis using fg
    by (auto intro!: add_mono positive_integral_mono_AE real_of_ereal_positive_mono
             simp: positive_integral_positive lebesgue_integral_def diff_minus)
qed

lemma integral_mono:
  assumes "integrable M f" "integrable M g" "\<And>t. t \<in> space M \<Longrightarrow> f t \<le> g t"
  shows "integral\<^isup>L M f \<le> integral\<^isup>L M g"
  using assms by (auto intro: integral_mono_AE)

lemma integral_diff[simp, intro]:
  assumes f: "integrable M f" and g: "integrable M g"
  shows "integrable M (\<lambda>t. f t - g t)"
  and "(\<integral> t. f t - g t \<partial>M) = integral\<^isup>L M f - integral\<^isup>L M g"
  using integral_add[OF f integral_minus(1)[OF g]]
  unfolding diff_minus integral_minus(2)[OF g]
  by auto

lemma integral_indicator[simp, intro]:
  assumes "A \<in> sets M" and "(emeasure M) A \<noteq> \<infinity>"
  shows "integral\<^isup>L M (indicator A) = real ((emeasure M) A)" (is ?int)
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

lemma integral_cmul_indicator:
  assumes "A \<in> sets M" and "c \<noteq> 0 \<Longrightarrow> (emeasure M) A \<noteq> \<infinity>"
  shows "integrable M (\<lambda>x. c * indicator A x)" (is ?P)
  and "(\<integral>x. c * indicator A x \<partial>M) = c * real ((emeasure M) A)" (is ?I)
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

lemma integral_setsum[simp, intro]:
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

lemma integrable_abs:
  assumes "integrable M f"
  shows "integrable M (\<lambda> x. \<bar>f x\<bar>)"
proof -
  from assms have *: "(\<integral>\<^isup>+x. ereal (- \<bar>f x\<bar>)\<partial>M) = 0"
    "\<And>x. ereal \<bar>f x\<bar> = max 0 (ereal (f x)) + max 0 (ereal (- f x))"
    by (auto simp: integrable_def positive_integral_0_iff_AE split: split_max)
  with assms show ?thesis
    by (simp add: positive_integral_add positive_integral_max_0 integrable_def)
qed

lemma integral_subalgebra:
  assumes borel: "f \<in> borel_measurable N"
  and N: "sets N \<subseteq> sets M" "space N = space M" "\<And>A. A \<in> sets N \<Longrightarrow> emeasure N A = emeasure M A"
  shows "integrable N f \<longleftrightarrow> integrable M f" (is ?P)
    and "integral\<^isup>L N f = integral\<^isup>L M f" (is ?I)
proof -
  have "(\<integral>\<^isup>+ x. max 0 (ereal (f x)) \<partial>N) = (\<integral>\<^isup>+ x. max 0 (ereal (f x)) \<partial>M)"
       "(\<integral>\<^isup>+ x. max 0 (ereal (- f x)) \<partial>N) = (\<integral>\<^isup>+ x. max 0 (ereal (- f x)) \<partial>M)"
    using borel by (auto intro!: positive_integral_subalgebra N)
  moreover have "f \<in> borel_measurable M \<longleftrightarrow> f \<in> borel_measurable N"
    using assms unfolding measurable_def by auto
  ultimately show ?P ?I
    by (auto simp: integrable_def lebesgue_integral_def positive_integral_max_0)
qed

lemma integrable_bound:
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

lemma lebesgue_integral_nonneg:
  assumes ae: "(AE x in M. 0 \<le> f x)" shows "0 \<le> integral\<^isup>L M f"
proof -
  have "(\<integral>\<^isup>+x. max 0 (ereal (- f x)) \<partial>M) = (\<integral>\<^isup>+x. 0 \<partial>M)"
    using ae by (intro positive_integral_cong_AE) (auto simp: max_def)
  then show ?thesis
    by (auto simp: lebesgue_integral_def positive_integral_max_0
             intro!: real_of_ereal_pos positive_integral_positive)
qed

lemma integrable_abs_iff:
  "f \<in> borel_measurable M \<Longrightarrow> integrable M (\<lambda> x. \<bar>f x\<bar>) \<longleftrightarrow> integrable M f"
  by (auto intro!: integrable_bound[where g=f] integrable_abs)

lemma integrable_max:
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

lemma integrable_min:
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

lemma integral_triangle_inequality:
  assumes "integrable M f"
  shows "\<bar>integral\<^isup>L M f\<bar> \<le> (\<integral>x. \<bar>f x\<bar> \<partial>M)"
proof -
  have "\<bar>integral\<^isup>L M f\<bar> = max (integral\<^isup>L M f) (- integral\<^isup>L M f)" by auto
  also have "\<dots> \<le> (\<integral>x. \<bar>f x\<bar> \<partial>M)"
      using assms integral_minus(2)[of M f, symmetric]
      by (auto intro!: integral_mono integrable_abs simp del: integral_minus)
  finally show ?thesis .
qed

lemma integral_positive:
  assumes "integrable M f" "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> f x"
  shows "0 \<le> integral\<^isup>L M f"
proof -
  have "0 = (\<integral>x. 0 \<partial>M)" by (auto simp: integral_zero)
  also have "\<dots> \<le> integral\<^isup>L M f"
    using assms by (rule integral_mono[OF integral_zero(1)])
  finally show ?thesis .
qed

lemma integral_monotone_convergence_pos:
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
    using i positive_integral_positive[of M] by (auto simp: ereal_real lebesgue_integral_def integrable_def)

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

lemma integral_monotone_convergence:
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

lemma integral_0_iff:
  assumes "integrable M f"
  shows "(\<integral>x. \<bar>f x\<bar> \<partial>M) = 0 \<longleftrightarrow> (emeasure M) {x\<in>space M. f x \<noteq> 0} = 0"
proof -
  have *: "(\<integral>\<^isup>+x. ereal (- \<bar>f x\<bar>) \<partial>M) = 0"
    using assms by (auto simp: positive_integral_0_iff_AE integrable_def)
  have "integrable M (\<lambda>x. \<bar>f x\<bar>)" using assms by (rule integrable_abs)
  hence "(\<lambda>x. ereal (\<bar>f x\<bar>)) \<in> borel_measurable M"
    "(\<integral>\<^isup>+ x. ereal \<bar>f x\<bar> \<partial>M) \<noteq> \<infinity>" unfolding integrable_def by auto
  from positive_integral_0_iff[OF this(1)] this(2)
  show ?thesis unfolding lebesgue_integral_def *
    using positive_integral_positive[of M "\<lambda>x. ereal \<bar>f x\<bar>"]
    by (auto simp add: real_of_ereal_eq_0)
qed

lemma positive_integral_PInf:
  assumes f: "f \<in> borel_measurable M"
  and not_Inf: "integral\<^isup>P M f \<noteq> \<infinity>"
  shows "(emeasure M) (f -` {\<infinity>} \<inter> space M) = 0"
proof -
  have "\<infinity> * (emeasure M) (f -` {\<infinity>} \<inter> space M) = (\<integral>\<^isup>+ x. \<infinity> * indicator (f -` {\<infinity>} \<inter> space M) x \<partial>M)"
    using f by (subst positive_integral_cmult_indicator) (auto simp: measurable_sets)
  also have "\<dots> \<le> integral\<^isup>P M (\<lambda>x. max 0 (f x))"
    by (auto intro!: positive_integral_mono simp: indicator_def max_def)
  finally have "\<infinity> * (emeasure M) (f -` {\<infinity>} \<inter> space M) \<le> integral\<^isup>P M f"
    by (simp add: positive_integral_max_0)
  moreover have "0 \<le> (emeasure M) (f -` {\<infinity>} \<inter> space M)"
    by (rule emeasure_nonneg)
  ultimately show ?thesis
    using assms by (auto split: split_if_asm)
qed

lemma positive_integral_PInf_AE:
  assumes "f \<in> borel_measurable M" "integral\<^isup>P M f \<noteq> \<infinity>" shows "AE x in M. f x \<noteq> \<infinity>"
proof (rule AE_I)
  show "(emeasure M) (f -` {\<infinity>} \<inter> space M) = 0"
    by (rule positive_integral_PInf[OF assms])
  show "f -` {\<infinity>} \<inter> space M \<in> sets M"
    using assms by (auto intro: borel_measurable_vimage)
qed auto

lemma simple_integral_PInf:
  assumes "simple_function M f" "\<And>x. 0 \<le> f x"
  and "integral\<^isup>S M f \<noteq> \<infinity>"
  shows "(emeasure M) (f -` {\<infinity>} \<inter> space M) = 0"
proof (rule positive_integral_PInf)
  show "f \<in> borel_measurable M" using assms by (auto intro: borel_measurable_simple_function)
  show "integral\<^isup>P M f \<noteq> \<infinity>"
    using assms by (simp add: positive_integral_eq_simple_integral)
qed

lemma integral_real:
  "AE x in M. \<bar>f x\<bar> \<noteq> \<infinity> \<Longrightarrow> (\<integral>x. real (f x) \<partial>M) = real (integral\<^isup>P M f) - real (integral\<^isup>P M (\<lambda>x. - f x))"
  using assms unfolding lebesgue_integral_def
  by (subst (1 2) positive_integral_cong_AE) (auto simp add: ereal_real)

lemma (in finite_measure) lebesgue_integral_const[simp]:
  shows "integrable M (\<lambda>x. a)"
  and  "(\<integral>x. a \<partial>M) = a * (measure M) (space M)"
proof -
  { fix a :: real assume "0 \<le> a"
    then have "(\<integral>\<^isup>+ x. ereal a \<partial>M) = ereal a * (emeasure M) (space M)"
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
  show "(\<integral>x. a \<partial>M) = a * measure M (space M)"
    by (simp add: lebesgue_integral_def positive_integral_const_If emeasure_eq_measure)
qed

lemma indicator_less[simp]:
  "indicator A x \<le> (indicator B x::ereal) \<longleftrightarrow> (x \<in> A \<longrightarrow> x \<in> B)"
  by (simp add: indicator_def not_le)

lemma (in finite_measure) integral_less_AE:
  assumes int: "integrable M X" "integrable M Y"
  assumes A: "(emeasure M) A \<noteq> 0" "A \<in> sets M" "AE x in M. x \<in> A \<longrightarrow> X x \<noteq> Y x"
  assumes gt: "AE x in M. X x \<le> Y x"
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
    finally have "(emeasure M) {x \<in> space M. Y x - X x \<noteq> 0} = 0"
      using int by (simp add: integral_0_iff)
    moreover
    have "(\<integral>\<^isup>+x. indicator A x \<partial>M) \<le> (\<integral>\<^isup>+x. indicator {x \<in> space M. Y x - X x \<noteq> 0} x \<partial>M)"
      using A by (intro positive_integral_mono_AE) auto
    then have "(emeasure M) A \<le> (emeasure M) {x \<in> space M. Y x - X x \<noteq> 0}"
      using int A by (simp add: integrable_def)
    ultimately have "emeasure M A = 0"
      using emeasure_nonneg[of M A] by simp
    with `(emeasure M) A \<noteq> 0` show False by auto
  qed
  ultimately show ?thesis by auto
qed

lemma (in finite_measure) integral_less_AE_space:
  assumes int: "integrable M X" "integrable M Y"
  assumes gt: "AE x in M. X x < Y x" "(emeasure M) (space M) \<noteq> 0"
  shows "integral\<^isup>L M X < integral\<^isup>L M Y"
  using gt by (intro integral_less_AE[OF int, where A="space M"]) auto

lemma integral_dominated_convergence:
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
    using u' by (blast intro: borel_measurable_LIMSEQ[of M u])

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
        using positive_integral_positive[of M ?f'] eq_0 by auto }
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
      using positive_integral_positive[of M "\<lambda>x. ereal (2 * w x)"]
      by (subst liminf_ereal_cminus) auto
    finally show ?thesis
      using neq_0 I2w_fin positive_integral_positive[of M "\<lambda>x. ereal (2 * w x)"] pos
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
    using diff positive_integral_positive[of M]
    by (subst integral_eq_positive_integral[of _ M]) (auto simp: ereal_real integrable_def)
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

lemma integral_sums:
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

lemma integral_on_countable:
  assumes f: "f \<in> borel_measurable M"
  and bij: "bij_betw enum S (f ` space M)"
  and enum_zero: "enum ` (-S) \<subseteq> {0}"
  and fin: "\<And>x. x \<noteq> 0 \<Longrightarrow> (emeasure M) (f -` {x} \<inter> space M) \<noteq> \<infinity>"
  and abs_summable: "summable (\<lambda>r. \<bar>enum r * real ((emeasure M) (f -` {enum r} \<inter> space M))\<bar>)"
  shows "integrable M f"
  and "(\<lambda>r. enum r * real ((emeasure M) (f -` {enum r} \<inter> space M))) sums integral\<^isup>L M f" (is ?sums)
proof -
  let ?A = "\<lambda>r. f -` {enum r} \<inter> space M"
  let ?F = "\<lambda>r x. enum r * indicator (?A r) x"
  have enum_eq: "\<And>r. enum r * real ((emeasure M) (?A r)) = integral\<^isup>L M (?F r)"
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
    also have "\<dots> = \<bar>enum r\<bar> * real ((emeasure M) (?A r))"
      using f fin by (simp add: borel_measurable_vimage integral_cmul_indicator)
    finally have "(\<integral>x. \<bar>?F r x\<bar> \<partial>M) = \<bar>enum r * real ((emeasure M) (?A r))\<bar>"
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

section {* Distributions *}

lemma simple_function_distr[simp]:
  "simple_function (distr M M' T) f \<longleftrightarrow> simple_function M' (\<lambda>x. f x)"
 unfolding simple_function_def by simp

lemma positive_integral_distr:
  assumes T: "T \<in> measurable M M'"
  and f: "f \<in> borel_measurable M'"
  shows "integral\<^isup>P (distr M M' T) f = (\<integral>\<^isup>+ x. f (T x) \<partial>M)"
proof -
  from borel_measurable_implies_simple_function_sequence'[OF f]
  guess f' . note f' = this
  then have f_distr: "\<And>i. simple_function (distr M M' T) (f' i)"
    by simp
  let ?f = "\<lambda>i x. f' i (T x)"
  have inc: "incseq ?f" using f' by (force simp: le_fun_def incseq_def)
  have sup: "\<And>x. (SUP i. ?f i x) = max 0 (f (T x))"
    using f'(4) .
  have sf: "\<And>i. simple_function M (\<lambda>x. f' i (T x))"
    using simple_function_comp[OF T(1) f'(1)] .
  show "integral\<^isup>P (distr M M' T) f = (\<integral>\<^isup>+ x. f (T x) \<partial>M)"
    using
      positive_integral_monotone_convergence_simple[OF f'(2,5) f_distr]
      positive_integral_monotone_convergence_simple[OF inc f'(5) sf]
    by (simp add: positive_integral_max_0 simple_integral_distr[OF T f'(1)] f')
qed

lemma integral_distr:
  assumes T: "T \<in> measurable M M'"
  assumes f: "f \<in> borel_measurable M'"
  shows "integral\<^isup>L (distr M M' T) f = (\<integral>x. f (T x) \<partial>M)"
proof -
  from measurable_comp[OF T, of f borel]
  have borel: "(\<lambda>x. ereal (f x)) \<in> borel_measurable M'" "(\<lambda>x. ereal (- f x)) \<in> borel_measurable M'"
    and "(\<lambda>x. f (T x)) \<in> borel_measurable M"
    using f by (auto simp: comp_def)
  then show ?thesis
    using f unfolding lebesgue_integral_def integrable_def
    by (auto simp: borel[THEN positive_integral_distr[OF T]])
qed

lemma integrable_distr:
  assumes T: "T \<in> measurable M M'" and f: "integrable (distr M M' T) f"
  shows "integrable M (\<lambda>x. f (T x))"
proof -
  from measurable_comp[OF T, of f borel]
  have borel: "(\<lambda>x. ereal (f x)) \<in> borel_measurable M'" "(\<lambda>x. ereal (- f x)) \<in> borel_measurable M'"
    and "(\<lambda>x. f (T x)) \<in> borel_measurable M"
    using f by (auto simp: comp_def)
  then show ?thesis
    using f unfolding lebesgue_integral_def integrable_def
    using borel[THEN positive_integral_distr[OF T]]
    by (auto simp: borel[THEN positive_integral_distr[OF T]])
qed

section {* Lebesgue integration on @{const count_space} *}

lemma simple_function_count_space[simp]:
  "simple_function (count_space A) f \<longleftrightarrow> finite (f ` A)"
  unfolding simple_function_def by simp

lemma positive_integral_count_space:
  assumes A: "finite {a\<in>A. 0 < f a}"
  shows "integral\<^isup>P (count_space A) f = (\<Sum>a|a\<in>A \<and> 0 < f a. f a)"
proof -
  have *: "(\<integral>\<^isup>+x. max 0 (f x) \<partial>count_space A) =
    (\<integral>\<^isup>+ x. (\<Sum>a|a\<in>A \<and> 0 < f a. f a * indicator {a} x) \<partial>count_space A)"
    by (auto intro!: positive_integral_cong
             simp add: indicator_def if_distrib setsum_cases[OF A] max_def le_less)
  also have "\<dots> = (\<Sum>a|a\<in>A \<and> 0 < f a. \<integral>\<^isup>+ x. f a * indicator {a} x \<partial>count_space A)"
    by (subst positive_integral_setsum)
       (simp_all add: AE_count_space ereal_zero_le_0_iff less_imp_le)
  also have "\<dots> = (\<Sum>a|a\<in>A \<and> 0 < f a. f a)"
    by (auto intro!: setsum_cong simp: positive_integral_cmult_indicator one_ereal_def[symmetric])
  finally show ?thesis by (simp add: positive_integral_max_0)
qed

lemma integrable_count_space:
  "finite X \<Longrightarrow> integrable (count_space X) f"
  by (auto simp: positive_integral_count_space integrable_def)

lemma positive_integral_count_space_finite:
    "finite A \<Longrightarrow> (\<integral>\<^isup>+x. f x \<partial>count_space A) = (\<Sum>a\<in>A. max 0 (f a))"
  by (subst positive_integral_max_0[symmetric])
     (auto intro!: setsum_mono_zero_left simp: positive_integral_count_space less_le)

lemma lebesgue_integral_count_space_finite:
    "finite A \<Longrightarrow> (\<integral>x. f x \<partial>count_space A) = (\<Sum>a\<in>A. f a)"
  apply (auto intro!: setsum_mono_zero_left
              simp: positive_integral_count_space_finite lebesgue_integral_def)
  apply (subst (1 2)  setsum_real_of_ereal[symmetric])
  apply (auto simp: max_def setsum_subtractf[symmetric] intro!: setsum_cong)
  done

section {* Measure spaces with an associated density *}

definition density :: "'a measure \<Rightarrow> ('a \<Rightarrow> ereal) \<Rightarrow> 'a measure" where
  "density M f = measure_of (space M) (sets M) (\<lambda>A. \<integral>\<^isup>+ x. f x * indicator A x \<partial>M)"

lemma 
  shows sets_density[simp]: "sets (density M f) = sets M"
    and space_density[simp]: "space (density M f) = space M"
  by (auto simp: density_def)

lemma 
  shows measurable_density_eq1[simp]: "g \<in> measurable (density Mg f) Mg' \<longleftrightarrow> g \<in> measurable Mg Mg'"
    and measurable_density_eq2[simp]: "h \<in> measurable Mh (density Mh' f) \<longleftrightarrow> h \<in> measurable Mh Mh'"
    and simple_function_density_eq[simp]: "simple_function (density Mu f) u \<longleftrightarrow> simple_function Mu u"
  unfolding measurable_def simple_function_def by simp_all

lemma density_cong: "f \<in> borel_measurable M \<Longrightarrow> f' \<in> borel_measurable M \<Longrightarrow>
  (AE x in M. f x = f' x) \<Longrightarrow> density M f = density M f'"
  unfolding density_def by (auto intro!: measure_of_eq positive_integral_cong_AE space_closed)

lemma density_max_0: "density M f = density M (\<lambda>x. max 0 (f x))"
proof -
  have "\<And>x A. max 0 (f x) * indicator A x = max 0 (f x * indicator A x)"
    by (auto simp: indicator_def)
  then show ?thesis
    unfolding density_def by (simp add: positive_integral_max_0)
qed

lemma density_ereal_max_0: "density M (\<lambda>x. ereal (f x)) = density M (\<lambda>x. ereal (max 0 (f x)))"
  by (subst density_max_0) (auto intro!: arg_cong[where f="density M"] split: split_max)

lemma emeasure_density:
  assumes f: "f \<in> borel_measurable M" and A: "A \<in> sets M"
  shows "emeasure (density M f) A = (\<integral>\<^isup>+ x. f x * indicator A x \<partial>M)"
    (is "_ = ?\<mu> A")
  unfolding density_def
proof (rule emeasure_measure_of_sigma)
  show "sigma_algebra (space M) (sets M)" ..
  show "positive (sets M) ?\<mu>"
    using f by (auto simp: positive_def intro!: positive_integral_positive)
  have \<mu>_eq: "?\<mu> = (\<lambda>A. \<integral>\<^isup>+ x. max 0 (f x) * indicator A x \<partial>M)" (is "?\<mu> = ?\<mu>'")
    apply (subst positive_integral_max_0[symmetric])
    apply (intro ext positive_integral_cong_AE AE_I2)
    apply (auto simp: indicator_def)
    done
  show "countably_additive (sets M) ?\<mu>"
    unfolding \<mu>_eq
  proof (intro countably_additiveI)
    fix A :: "nat \<Rightarrow> 'a set" assume "range A \<subseteq> sets M"
    then have *: "\<And>i. (\<lambda>x. max 0 (f x) * indicator (A i) x) \<in> borel_measurable M"
      using f by (auto intro!: borel_measurable_ereal_times)
    assume disj: "disjoint_family A"
    have "(\<Sum>n. ?\<mu>' (A n)) = (\<integral>\<^isup>+ x. (\<Sum>n. max 0 (f x) * indicator (A n) x) \<partial>M)"
      using f * by (simp add: positive_integral_suminf)
    also have "\<dots> = (\<integral>\<^isup>+ x. max 0 (f x) * (\<Sum>n. indicator (A n) x) \<partial>M)" using f
      by (auto intro!: suminf_cmult_ereal positive_integral_cong_AE)
    also have "\<dots> = (\<integral>\<^isup>+ x. max 0 (f x) * indicator (\<Union>n. A n) x \<partial>M)"
      unfolding suminf_indicator[OF disj] ..
    finally show "(\<Sum>n. ?\<mu>' (A n)) = ?\<mu>' (\<Union>x. A x)" by simp
  qed
qed fact

lemma null_sets_density_iff:
  assumes f: "f \<in> borel_measurable M"
  shows "A \<in> null_sets (density M f) \<longleftrightarrow> A \<in> sets M \<and> (AE x in M. x \<in> A \<longrightarrow> f x \<le> 0)"
proof -
  { assume "A \<in> sets M"
    have eq: "(\<integral>\<^isup>+x. f x * indicator A x \<partial>M) = (\<integral>\<^isup>+x. max 0 (f x) * indicator A x \<partial>M)"
      apply (subst positive_integral_max_0[symmetric])
      apply (intro positive_integral_cong)
      apply (auto simp: indicator_def)
      done
    have "(\<integral>\<^isup>+x. f x * indicator A x \<partial>M) = 0 \<longleftrightarrow> 
      emeasure M {x \<in> space M. max 0 (f x) * indicator A x \<noteq> 0} = 0"
      unfolding eq
      using f `A \<in> sets M`
      by (intro positive_integral_0_iff) auto
    also have "\<dots> \<longleftrightarrow> (AE x in M. max 0 (f x) * indicator A x = 0)"
      using f `A \<in> sets M`
      by (intro AE_iff_measurable[OF _ refl, symmetric])
         (auto intro!: sets_Collect borel_measurable_ereal_eq)
    also have "(AE x in M. max 0 (f x) * indicator A x = 0) \<longleftrightarrow> (AE x in M. x \<in> A \<longrightarrow> f x \<le> 0)"
      by (auto simp add: indicator_def max_def split: split_if_asm)
    finally have "(\<integral>\<^isup>+x. f x * indicator A x \<partial>M) = 0 \<longleftrightarrow> (AE x in M. x \<in> A \<longrightarrow> f x \<le> 0)" . }
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
    using f by (auto simp: subset_eq intro!: sets_Collect_neg AE_not_in)
  show "AE x in density M f. P x"
    using ae2
    unfolding eventually_ae_filter[of _ "density M f"] Bex_def null_sets_density_iff[OF f]
    by (intro exI[of _ "N \<union> {x\<in>space M. \<not> 0 < f x}"] conjI *)
       (auto elim: eventually_elim2)
qed

lemma positive_integral_density:
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
  assumes g': "g' \<in> borel_measurable M"
  shows "integral\<^isup>P (density M f) g' = (\<integral>\<^isup>+ x. f x * g' x \<partial>M)"
proof -
  def g \<equiv> "\<lambda>x. max 0 (g' x)"
  then have g: "g \<in> borel_measurable M" "AE x in M. 0 \<le> g x"
    using g' by auto
  from borel_measurable_implies_simple_function_sequence'[OF g(1)] guess G . note G = this
  note G' = borel_measurable_simple_function[OF this(1)] simple_functionD[OF G(1)]
  note G'(2)[simp]
  { fix P have "AE x in M. P x \<Longrightarrow> AE x in M. P x"
      using positive_integral_null_set[of _ _ f]
      by (auto simp: eventually_ae_filter ) }
  note ac = this
  with G(4) f g have G_M': "AE x in density M f. (SUP i. G i x) = g x"
    by (auto simp add: AE_density[OF f(1)] max_def)
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
    have "integral\<^isup>P (density M f) (G i) = integral\<^isup>S (density M f) (G i)"
      using G by (intro positive_integral_eq_simple_integral) simp_all
    also have "\<dots> = (\<Sum>y\<in>G i`space M. y * (\<integral>\<^isup>+x. f x * ?I y x \<partial>M))"
      using f G(1)
      by (auto intro!: setsum_cong arg_cong2[where f="op *"] emeasure_density
               simp: simple_function_def simple_integral_def)
    also have "\<dots> = (\<Sum>y\<in>G i`space M. (\<integral>\<^isup>+x. y * (f x * ?I y x) \<partial>M))"
      using f G' G by (auto intro!: setsum_cong positive_integral_cmult[symmetric])
    also have "\<dots> = (\<integral>\<^isup>+x. (\<Sum>y\<in>G i`space M. y * (f x * ?I y x)) \<partial>M)"
      using f G' G by (auto intro!: positive_integral_setsum[symmetric])
    finally have "integral\<^isup>P (density M f) (G i) = (\<integral>\<^isup>+x. f x * G i x \<partial>M)"
      using f g G' to_singleton by (auto intro!: positive_integral_cong_AE) }
  note [simp] = this
  have "integral\<^isup>P (density M f) g = (SUP i. integral\<^isup>P (density M f) (G i))" using G'(1) G_M'(1) G
    using positive_integral_monotone_convergence_SUP[symmetric, OF `incseq G`, of "density M f"]
    by (simp cong: positive_integral_cong_AE)
  also have "\<dots> = (SUP i. (\<integral>\<^isup>+x. f x * G i x \<partial>M))" by simp
  also have "\<dots> = (\<integral>\<^isup>+x. (SUP i. f x * G i x) \<partial>M)"
    using f G' G(2)[THEN incseq_SucD] G
    by (intro positive_integral_monotone_convergence_SUP_AE[symmetric])
       (auto simp: ereal_mult_left_mono le_fun_def ereal_zero_le_0_iff)
  also have "\<dots> = (\<integral>\<^isup>+x. f x * g x \<partial>M)" using f G' G g
    by (intro positive_integral_cong_AE)
       (auto simp add: SUPR_ereal_cmult split: split_max)
  also have "\<dots> = (\<integral>\<^isup>+x. f x * g' x \<partial>M)"
    using f(2)
    by (subst (2) positive_integral_max_0[symmetric])
       (auto simp: g_def max_def ereal_zero_le_0_iff intro!: positive_integral_cong_AE)
  finally show "integral\<^isup>P (density M f) g' = (\<integral>\<^isup>+x. f x * g' x \<partial>M)"
    unfolding g_def positive_integral_max_0 .
qed

lemma integral_density:
  assumes f: "f \<in> borel_measurable M" "AE x in M. 0 \<le> f x"
    and g: "g \<in> borel_measurable M"
  shows "integral\<^isup>L (density M f) g = (\<integral> x. f x * g x \<partial>M)"
    and "integrable (density M f) g \<longleftrightarrow> integrable M (\<lambda>x. f x * g x)"
  unfolding lebesgue_integral_def integrable_def using f g
  by (auto simp: positive_integral_density)

lemma emeasure_restricted:
  assumes S: "S \<in> sets M" and X: "X \<in> sets M"
  shows "emeasure (density M (indicator S)) X = emeasure M (S \<inter> X)"
proof -
  have "emeasure (density M (indicator S)) X = (\<integral>\<^isup>+x. indicator S x * indicator X x \<partial>M)"
    using S X by (simp add: emeasure_density)
  also have "\<dots> = (\<integral>\<^isup>+x. indicator (S \<inter> X) x \<partial>M)"
    by (auto intro!: positive_integral_cong simp: indicator_def)
  also have "\<dots> = emeasure M (S \<inter> X)"
    using S X by (simp add: Int)
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
  by (auto simp: positive_integral_cmult_indicator emeasure_density)

lemma measure_density_const:
  "A \<in> sets M \<Longrightarrow> 0 < c \<Longrightarrow> c \<noteq> \<infinity> \<Longrightarrow> measure (density M (\<lambda>_. c)) A = real c * measure M A"
  by (auto simp: emeasure_density_const measure_def)

lemma density_density_eq:
   "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> AE x in M. 0 \<le> f x \<Longrightarrow>
   density (density M f) g = density M (\<lambda>x. f x * g x)"
  by (auto intro!: measure_eqI simp: emeasure_density positive_integral_density ac_simps)

lemma distr_density_distr:
  assumes T: "T \<in> measurable M M'" and T': "T' \<in> measurable M' M"
    and inv: "\<forall>x\<in>space M. T' (T x) = x"
  assumes f: "f \<in> borel_measurable M'"
  shows "distr (density (distr M M' T) f) M T' = density M (f \<circ> T)" (is "?R = ?L")
proof (rule measure_eqI)
  fix A assume A: "A \<in> sets ?R"
  { fix x assume "x \<in> space M"
    with sets_into_space[OF A]
    have "indicator (T' -` A \<inter> space M') (T x) = (indicator A x :: ereal)"
      using T inv by (auto simp: indicator_def measurable_space) }
  with A T T' f show "emeasure ?R A = emeasure ?L A"
    by (simp add: measurable_comp emeasure_density emeasure_distr
                  positive_integral_distr measurable_sets cong: positive_integral_cong)
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

section {* Point measure *}

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
  unfolding point_measure_def by simp

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
    by (simp add: emeasure_density positive_integral_count_space ereal_zero_le_0_iff
                  point_measure_def indicator_def)
qed

lemma emeasure_point_measure_finite:
  "finite A \<Longrightarrow> (\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> X \<subseteq> A \<Longrightarrow> emeasure (point_measure A f) X = (\<Sum>a|a\<in>X. f a)"
  by (subst emeasure_point_measure) (auto dest: finite_subset intro!: setsum_mono_zero_left simp: less_le)

lemma null_sets_point_measure_iff:
  "X \<in> null_sets (point_measure A f) \<longleftrightarrow> X \<subseteq> A \<and> (\<forall>x\<in>X. f x \<le> 0)"
 by (auto simp: AE_count_space null_sets_density_iff point_measure_def)

lemma AE_point_measure:
  "(AE x in point_measure A f. P x) \<longleftrightarrow> (\<forall>x\<in>A. 0 < f x \<longrightarrow> P x)"
  unfolding point_measure_def
  by (subst AE_density) (auto simp: AE_density AE_count_space point_measure_def)

lemma positive_integral_point_measure:
  "finite {a\<in>A. 0 < f a \<and> 0 < g a} \<Longrightarrow>
    integral\<^isup>P (point_measure A f) g = (\<Sum>a|a\<in>A \<and> 0 < f a \<and> 0 < g a. f a * g a)"
  unfolding point_measure_def
  apply (subst density_max_0)
  apply (subst positive_integral_density)
  apply (simp_all add: AE_count_space positive_integral_density)
  apply (subst positive_integral_count_space )
  apply (auto intro!: setsum_cong simp: max_def ereal_zero_less_0_iff)
  apply (rule finite_subset)
  prefer 2
  apply assumption
  apply auto
  done

lemma positive_integral_point_measure_finite:
  "finite A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> 0 \<le> f a) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> 0 \<le> g a) \<Longrightarrow>
    integral\<^isup>P (point_measure A f) g = (\<Sum>a\<in>A. f a * g a)"
  by (subst positive_integral_point_measure) (auto intro!: setsum_mono_zero_left simp: less_le)

lemma lebesgue_integral_point_measure_finite:
  "finite A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> 0 \<le> f a) \<Longrightarrow> integral\<^isup>L (point_measure A f) g = (\<Sum>a\<in>A. f a * g a)"
  by (simp add: lebesgue_integral_count_space_finite AE_count_space integral_density point_measure_def)

lemma integrable_point_measure_finite:
  "finite A \<Longrightarrow> integrable (point_measure A (\<lambda>x. ereal (f x))) g"
  unfolding point_measure_def
  apply (subst density_ereal_max_0)
  apply (subst integral_density)
  apply (auto simp: AE_count_space integrable_count_space)
  done

section {* Uniform measure *}

definition "uniform_measure M A = density M (\<lambda>x. indicator A x / emeasure M A)"

lemma
  shows sets_uniform_measure[simp]: "sets (uniform_measure M A) = sets M"
    and space_uniform_measure[simp]: "space (uniform_measure M A) = space M"
  by (auto simp: uniform_measure_def)

lemma emeasure_uniform_measure[simp]:
  assumes A: "A \<in> sets M" and B: "B \<in> sets M"
  shows "emeasure (uniform_measure M A) B = emeasure M (A \<inter> B) / emeasure M A"
proof -
  from A B have "emeasure (uniform_measure M A) B = (\<integral>\<^isup>+x. (1 / emeasure M A) * indicator (A \<inter> B) x \<partial>M)"
    by (auto simp add: uniform_measure_def emeasure_density split: split_indicator
             intro!: positive_integral_cong)
  also have "\<dots> = emeasure M (A \<inter> B) / emeasure M A"
    using A B
    by (subst positive_integral_cmult_indicator) (simp_all add: Int emeasure_nonneg)
  finally show ?thesis .
qed

lemma emeasure_neq_0_sets: "emeasure M A \<noteq> 0 \<Longrightarrow> A \<in> sets M"
  using emeasure_notin_sets[of A M] by blast

lemma measure_uniform_measure[simp]:
  assumes A: "emeasure M A \<noteq> 0" "emeasure M A \<noteq> \<infinity>" and B: "B \<in> sets M"
  shows "measure (uniform_measure M A) B = measure M (A \<inter> B) / measure M A"
  using emeasure_uniform_measure[OF emeasure_neq_0_sets[OF A(1)] B] A
  by (cases "emeasure M A" "emeasure M (A \<inter> B)" rule: ereal2_cases) (simp_all add: measure_def)

section {* Uniform count measure *}

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
