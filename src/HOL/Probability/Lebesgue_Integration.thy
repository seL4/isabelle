(* Author: Armin Heller, Johannes Hoelzl, TU Muenchen *)

header {*Lebesgue Integration*}

theory Lebesgue_Integration
imports Measure Borel_Space
begin

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

lemma (in sigma_algebra) simple_function_indicator_representation:
  fixes f ::"'a \<Rightarrow> pextreal"
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
  "simple_function M (\<lambda>x. h x * indicator (- space M) x::pextreal)" (is "simple_function M ?h")
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
  fixes f :: "'a \<Rightarrow> 'x::t2_space"
  assumes "f \<in> borel_measurable M" and "finite (f ` space M)"
  shows "simple_function M f"
  using assms unfolding simple_function_def
  by (auto intro: borel_measurable_vimage)

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

lemma (in sigma_algebra) simple_function_setsum[intro, simp]:
  assumes "\<And>i. i \<in> P \<Longrightarrow> simple_function M (f i)"
  shows "simple_function M (\<lambda>x. \<Sum>i\<in>P. f i x)"
proof cases
  assume "finite P" from this assms show ?thesis by induct auto
qed auto

lemma (in sigma_algebra) simple_function_le_measurable:
  assumes "simple_function M f" "simple_function M g"
  shows "{x \<in> space M. f x \<le> g x} \<in> sets M"
proof -
  have *: "{x \<in> space M. f x \<le> g x} =
    (\<Union>(F, G)\<in>f`space M \<times> g`space M.
      if F \<le> G then (f -` {F} \<inter> space M) \<inter> (g -` {G} \<inter> space M) else {})"
    apply (auto split: split_if_asm)
    apply (rule_tac x=x in bexI)
    apply (rule_tac x=x in bexI)
    by simp_all
  have **: "\<And>x y. x \<in> space M \<Longrightarrow> y \<in> space M \<Longrightarrow>
    (f -` {f x} \<inter> space M) \<inter> (g -` {g y} \<inter> space M) \<in> sets M"
    using assms unfolding simple_function_def by auto
  have "finite (f`space M \<times> g`space M)"
    using assms unfolding simple_function_def by auto
  thus ?thesis unfolding *
    apply (rule finite_UN)
    using assms unfolding simple_function_def
    by (auto intro!: **)
qed

lemma (in sigma_algebra) borel_measurable_implies_simple_function_sequence:
  fixes u :: "'a \<Rightarrow> pextreal"
  assumes u: "u \<in> borel_measurable M"
  shows "\<exists>f. (\<forall>i. simple_function M (f i) \<and> (\<forall>x\<in>space M. f i x \<noteq> \<omega>)) \<and> f \<up> u"
proof -
  have "\<exists>f. \<forall>x j. (of_nat j \<le> u x \<longrightarrow> f x j = j*2^j) \<and>
    (u x < of_nat j \<longrightarrow> of_nat (f x j) \<le> u x * 2^j \<and> u x * 2^j < of_nat (Suc (f x j)))"
    (is "\<exists>f. \<forall>x j. ?P x j (f x j)")
  proof(rule choice, rule, rule choice, rule)
    fix x j show "\<exists>n. ?P x j n"
    proof cases
      assume *: "u x < of_nat j"
      then obtain r where r: "u x = Real r" "0 \<le> r" by (cases "u x") auto
      from reals_Archimedean6a[of "r * 2^j"]
      obtain n :: nat where "real n \<le> r * 2 ^ j" "r * 2 ^ j < real (Suc n)"
        using `0 \<le> r` by (auto simp: zero_le_power zero_le_mult_iff)
      thus ?thesis using r * by (auto intro!: exI[of _ n])
    qed auto
  qed
  then obtain f where top: "\<And>j x. of_nat j \<le> u x \<Longrightarrow> f x j = j*2^j" and
    upper: "\<And>j x. u x < of_nat j \<Longrightarrow> of_nat (f x j) \<le> u x * 2^j" and
    lower: "\<And>j x. u x < of_nat j \<Longrightarrow> u x * 2^j < of_nat (Suc (f x j))" by blast

  { fix j x P
    assume 1: "of_nat j \<le> u x \<Longrightarrow> P (j * 2^j)"
    assume 2: "\<And>k. \<lbrakk> u x < of_nat j ; of_nat k \<le> u x * 2^j ; u x * 2^j < of_nat (Suc k) \<rbrakk> \<Longrightarrow> P k"
    have "P (f x j)"
    proof cases
      assume "of_nat j \<le> u x" thus "P (f x j)"
        using top[of j x] 1 by auto
    next
      assume "\<not> of_nat j \<le> u x"
      hence "u x < of_nat j" "of_nat (f x j) \<le> u x * 2^j" "u x * 2^j < of_nat (Suc (f x j))"
        using upper lower by auto
      from 2[OF this] show "P (f x j)" .
    qed }
  note fI = this

  { fix j x
    have "f x j = j * 2 ^ j \<longleftrightarrow> of_nat j \<le> u x"
      by (rule fI, simp, cases "u x") (auto split: split_if_asm) }
  note f_eq = this

  { fix j x
    have "f x j \<le> j * 2 ^ j"
    proof (rule fI)
      fix k assume *: "u x < of_nat j"
      assume "of_nat k \<le> u x * 2 ^ j"
      also have "\<dots> \<le> of_nat (j * 2^j)"
        using * by (cases "u x") (auto simp: zero_le_mult_iff)
      finally show "k \<le> j*2^j" by (auto simp del: real_of_nat_mult)
    qed simp }
  note f_upper = this

  let "?g j x" = "of_nat (f x j) / 2^j :: pextreal"
  show ?thesis unfolding simple_function_def isoton_fun_expand unfolding isoton_def
  proof (safe intro!: exI[of _ ?g])
    fix j
    have *: "?g j ` space M \<subseteq> (\<lambda>x. of_nat x / 2^j) ` {..j * 2^j}"
      using f_upper by auto
    thus "finite (?g j ` space M)" by (rule finite_subset) auto
  next
    fix j t assume "t \<in> space M"
    have **: "?g j -` {?g j t} \<inter> space M = {x \<in> space M. f t j = f x j}"
      by (auto simp: power_le_zero_eq Real_eq_Real mult_le_0_iff)

    show "?g j -` {?g j t} \<inter> space M \<in> sets M"
    proof cases
      assume "of_nat j \<le> u t"
      hence "?g j -` {?g j t} \<inter> space M = {x\<in>space M. of_nat j \<le> u x}"
        unfolding ** f_eq[symmetric] by auto
      thus "?g j -` {?g j t} \<inter> space M \<in> sets M"
        using u by auto
    next
      assume not_t: "\<not> of_nat j \<le> u t"
      hence less: "f t j < j*2^j" using f_eq[symmetric] `f t j \<le> j*2^j` by auto
      have split_vimage: "?g j -` {?g j t} \<inter> space M =
          {x\<in>space M. of_nat (f t j)/2^j \<le> u x} \<inter> {x\<in>space M. u x < of_nat (Suc (f t j))/2^j}"
        unfolding **
      proof safe
        fix x assume [simp]: "f t j = f x j"
        have *: "\<not> of_nat j \<le> u x" using not_t f_eq[symmetric] by simp
        hence "of_nat (f t j) \<le> u x * 2^j \<and> u x * 2^j < of_nat (Suc (f t j))"
          using upper lower by auto
        hence "of_nat (f t j) / 2^j \<le> u x \<and> u x < of_nat (Suc (f t j))/2^j" using *
          by (cases "u x") (auto simp: zero_le_mult_iff power_le_zero_eq divide_real_def[symmetric] field_simps)
        thus "of_nat (f t j) / 2^j \<le> u x" "u x < of_nat (Suc (f t j))/2^j" by auto
      next
        fix x
        assume "of_nat (f t j) / 2^j \<le> u x" "u x < of_nat (Suc (f t j))/2^j"
        hence "of_nat (f t j) \<le> u x * 2 ^ j \<and> u x * 2 ^ j < of_nat (Suc (f t j))"
          by (cases "u x") (auto simp: zero_le_mult_iff power_le_zero_eq divide_real_def[symmetric] field_simps)
        hence 1: "of_nat (f t j) \<le> u x * 2 ^ j" and 2: "u x * 2 ^ j < of_nat (Suc (f t j))" by auto
        note 2
        also have "\<dots> \<le> of_nat (j*2^j)"
          using less by (auto simp: zero_le_mult_iff simp del: real_of_nat_mult)
        finally have bound_ux: "u x < of_nat j"
          by (cases "u x") (auto simp: zero_le_mult_iff power_le_zero_eq)
        show "f t j = f x j"
        proof (rule antisym)
          from 1 lower[OF bound_ux]
          show "f t j \<le> f x j" by (cases "u x") (auto split: split_if_asm)
          from upper[OF bound_ux] 2
          show "f x j \<le> f t j" by (cases "u x") (auto split: split_if_asm)
        qed
      qed
      show ?thesis unfolding split_vimage using u by auto
    qed
  next
    fix j t assume "?g j t = \<omega>" thus False by (auto simp: power_le_zero_eq)
  next
    fix t
    { fix i
      have "f t i * 2 \<le> f t (Suc i)"
      proof (rule fI)
        assume "of_nat (Suc i) \<le> u t"
        hence "of_nat i \<le> u t" by (cases "u t") auto
        thus "f t i * 2 \<le> Suc i * 2 ^ Suc i" unfolding f_eq[symmetric] by simp
      next
        fix k
        assume *: "u t * 2 ^ Suc i < of_nat (Suc k)"
        show "f t i * 2 \<le> k"
        proof (rule fI)
          assume "of_nat i \<le> u t"
          hence "of_nat (i * 2^Suc i) \<le> u t * 2^Suc i"
            by (cases "u t") (auto simp: zero_le_mult_iff power_le_zero_eq)
          also have "\<dots> < of_nat (Suc k)" using * by auto
          finally show "i * 2 ^ i * 2 \<le> k"
            by (auto simp del: real_of_nat_mult)
        next
          fix j assume "of_nat j \<le> u t * 2 ^ i"
          with * show "j * 2 \<le> k" by (cases "u t") (auto simp: zero_le_mult_iff power_le_zero_eq)
        qed
      qed
      thus "?g i t \<le> ?g (Suc i) t"
        by (auto simp: zero_le_mult_iff power_le_zero_eq divide_real_def[symmetric] field_simps) }
    hence mono: "mono (\<lambda>i. ?g i t)" unfolding mono_iff_le_Suc by auto

    show "(SUP j. of_nat (f t j) / 2 ^ j) = u t"
    proof (rule pextreal_SUPI)
      fix j show "of_nat (f t j) / 2 ^ j \<le> u t"
      proof (rule fI)
        assume "of_nat j \<le> u t" thus "of_nat (j * 2 ^ j) / 2 ^ j \<le> u t"
          by (cases "u t") (auto simp: power_le_zero_eq divide_real_def[symmetric] field_simps)
      next
        fix k assume "of_nat k \<le> u t * 2 ^ j"
        thus "of_nat k / 2 ^ j \<le> u t"
          by (cases "u t")
             (auto simp: power_le_zero_eq divide_real_def[symmetric] field_simps zero_le_mult_iff)
      qed
    next
      fix y :: pextreal assume *: "\<And>j. j \<in> UNIV \<Longrightarrow> of_nat (f t j) / 2 ^ j \<le> y"
      show "u t \<le> y"
      proof (cases "u t")
        case (preal r)
        show ?thesis
        proof (rule ccontr)
          assume "\<not> u t \<le> y"
          then obtain p where p: "y = Real p" "0 \<le> p" "p < r" using preal by (cases y) auto
          with LIMSEQ_inverse_realpow_zero[of 2, unfolded LIMSEQ_iff, rule_format, of "r - p"]
          obtain n where n: "\<And>N. n \<le> N \<Longrightarrow> inverse (2^N) < r - p" by auto
          let ?N = "max n (natfloor r + 1)"
          have "u t < of_nat ?N" "n \<le> ?N"
            using ge_natfloor_plus_one_imp_gt[of r n] preal
            using real_natfloor_add_one_gt
            by (auto simp: max_def real_of_nat_Suc)
          from lower[OF this(1)]
          have "r < (real (f t ?N) + 1) / 2 ^ ?N" unfolding less_divide_eq
            using preal by (auto simp add: power_le_zero_eq zero_le_mult_iff real_of_nat_Suc split: split_if_asm)
          hence "u t < of_nat (f t ?N) / 2 ^ ?N + 1 / 2 ^ ?N"
            using preal by (auto simp: field_simps divide_real_def[symmetric])
          with n[OF `n \<le> ?N`] p preal *[of ?N]
          show False
            by (cases "f t ?N") (auto simp: power_le_zero_eq split: split_if_asm)
        qed
      next
        case infinite
        { fix j have "f t j = j*2^j" using top[of j t] infinite by simp
          hence "of_nat j \<le> y" using *[of j]
            by (cases y) (auto simp: power_le_zero_eq zero_le_mult_iff field_simps) }
        note all_less_y = this
        show ?thesis unfolding infinite
        proof (rule ccontr)
          assume "\<not> \<omega> \<le> y" then obtain r where r: "y = Real r" "0 \<le> r" by (cases y) auto
          moreover obtain n ::nat where "r < real n" using ex_less_of_nat by (auto simp: real_eq_of_nat)
          with all_less_y[of n] r show False by auto
        qed
      qed
    qed
  qed
qed

lemma (in sigma_algebra) borel_measurable_implies_simple_function_sequence':
  fixes u :: "'a \<Rightarrow> pextreal"
  assumes "u \<in> borel_measurable M"
  obtains (x) f where "f \<up> u" "\<And>i. simple_function M (f i)" "\<And>i. \<omega>\<notin>f i`space M"
proof -
  from borel_measurable_implies_simple_function_sequence[OF assms]
  obtain f where x: "\<And>i. simple_function M (f i)" "f \<up> u"
    and fin: "\<And>i. \<And>x. x\<in>space M \<Longrightarrow> f i x \<noteq> \<omega>" by auto
  { fix i from fin[of _ i] have "\<omega> \<notin> f i`space M" by fastsimp }
  with x show thesis by (auto intro!: that[of f])
qed

lemma (in sigma_algebra) simple_function_eq_borel_measurable:
  fixes f :: "'a \<Rightarrow> pextreal"
  shows "simple_function M f \<longleftrightarrow>
    finite (f`space M) \<and> f \<in> borel_measurable M"
  using simple_function_borel_measurable[of f]
    borel_measurable_simple_function[of f]
  by (fastsimp simp: simple_function_def)

lemma (in measure_space) simple_function_restricted:
  fixes f :: "'a \<Rightarrow> pextreal" assumes "A \<in> sets M"
  shows "simple_function (restricted_space A) f \<longleftrightarrow> simple_function M (\<lambda>x. f x * indicator A x)"
    (is "simple_function ?R f \<longleftrightarrow> simple_function M ?f")
proof -
  interpret R: sigma_algebra ?R by (rule restricted_sigma_algebra[OF `A \<in> sets M`])
  have "finite (f`A) \<longleftrightarrow> finite (?f`space M)"
  proof cases
    assume "A = space M"
    then have "f`A = ?f`space M" by (fastsimp simp: image_iff)
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
      assume "indicator A x \<noteq> (0::pextreal)"
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
    by auto
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
  "_simple_integral" :: "'a \<Rightarrow> ('a \<Rightarrow> pextreal) \<Rightarrow> ('a, 'b) measure_space_scheme \<Rightarrow> pextreal" ("\<integral>\<^isup>S _. _ \<partial>_" [60,61] 110)

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
  assumes "simple_function M f" and "simple_function M g"
  shows "integral\<^isup>S M f = (\<Sum>A\<in>(\<lambda>x. f -` {f x} \<inter> g -` {g x} \<inter> space M) ` space M. the_elem (f`A) * \<mu> A)"
    (is "_ = setsum _ (?p ` space M)")
proof-
  let "?sub x" = "?p ` (f -` {x} \<inter> space M)"
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

  { fix x assume "x \<in> space M"
    have "\<Union>(?sub (f x)) = (f -` {f x} \<inter> space M)" by auto
    moreover {
      fix x y
      have *: "f -` {f x} \<inter> g -` {g x} \<inter> space M
          = (f -` {f x} \<inter> space M) \<inter> (g -` {g x} \<inter> space M)" by auto
      assume "x \<in> space M" "y \<in> space M"
      hence "f -` {f x} \<inter> g -` {g x} \<inter> space M \<in> sets M"
        using assms unfolding simple_function_def * by auto }
    ultimately
    have "\<mu> (f -` {f x} \<inter> space M) = setsum (\<mu>) (?sub (f x))"
      by (subst measure_finitely_additive) auto }
  hence "integral\<^isup>S M f = (\<Sum>(x,A)\<in>?SIGMA. x * \<mu> A)"
    unfolding simple_integral_def
    by (subst setsum_Sigma[symmetric],
       auto intro!: setsum_cong simp: setsum_right_distrib[symmetric])
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
  assumes "simple_function M f" and "simple_function M g"
  shows "(\<integral>\<^isup>Sx. f x + g x \<partial>M) = integral\<^isup>S M f + integral\<^isup>S M g"
proof -
  { fix x let ?S = "g -` {g x} \<inter> f -` {f x} \<inter> space M"
    assume "x \<in> space M"
    hence "(\<lambda>a. f a + g a) ` ?S = {f x + g x}" "f ` ?S = {f x}" "g ` ?S = {g x}"
        "(\<lambda>x. (f x, g x)) -` {(f x, g x)} \<inter> space M = ?S"
      by auto }
  thus ?thesis
    unfolding
      simple_function_partition[OF simple_function_add[OF assms] simple_function_Pair[OF assms]]
      simple_function_partition[OF `simple_function M f` `simple_function M g`]
      simple_function_partition[OF `simple_function M g` `simple_function M f`]
    apply (subst (3) Int_commute)
    by (auto simp add: field_simps setsum_addf[symmetric] intro!: setsum_cong)
qed

lemma (in measure_space) simple_integral_setsum[simp]:
  assumes "\<And>i. i \<in> P \<Longrightarrow> simple_function M (f i)"
  shows "(\<integral>\<^isup>Sx. (\<Sum>i\<in>P. f i x) \<partial>M) = (\<Sum>i\<in>P. integral\<^isup>S M (f i))"
proof cases
  assume "finite P"
  from this assms show ?thesis
    by induct (auto simp: simple_function_setsum simple_integral_add)
qed auto

lemma (in measure_space) simple_integral_mult[simp]:
  assumes "simple_function M f"
  shows "(\<integral>\<^isup>Sx. c * f x \<partial>M) = c * integral\<^isup>S M f"
proof -
  note mult = simple_function_mult[OF simple_function_const[of c] assms]
  { fix x let ?S = "f -` {f x} \<inter> (\<lambda>x. c * f x) -` {c * f x} \<inter> space M"
    assume "x \<in> space M"
    hence "(\<lambda>x. c * f x) ` ?S = {c * f x}" "f ` ?S = {f x}"
      by auto }
  thus ?thesis
    unfolding simple_function_partition[OF mult assms]
      simple_function_partition[OF assms mult]
    by (auto simp: setsum_right_distrib field_simps intro!: setsum_cong)
qed

lemma (in sigma_algebra) simple_function_If:
  assumes sf: "simple_function M f" "simple_function M g" and A: "A \<in> sets M"
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
      then ((F (f x) \<inter> A) \<union> (G (f x) - (G (f x) \<inter> A)))
      else ((F (g x) \<inter> A) \<union> (G (g x) - (G (g x) \<inter> A))))"
      using sets_into_space[OF A] by (auto split: split_if_asm simp: G_def F_def)
    have [intro]: "\<And>x. F x \<in> sets M" "\<And>x. G x \<in> sets M"
      unfolding F_def G_def using sf[THEN simple_functionD(2)] by auto
    show "?IF -` {?IF x} \<inter> space M \<in> sets M" unfolding * using A by auto
  qed
qed

lemma (in measure_space) simple_integral_mono_AE:
  assumes "simple_function M f" and "simple_function M g"
  and mono: "AE x. f x \<le> g x"
  shows "integral\<^isup>S M f \<le> integral\<^isup>S M g"
proof -
  let "?S x" = "(g -` {g x} \<inter> space M) \<inter> (f -` {f x} \<inter> space M)"
  have *: "\<And>x. g -` {g x} \<inter> f -` {f x} \<inter> space M = ?S x"
    "\<And>x. f -` {f x} \<inter> g -` {g x} \<inter> space M = ?S x" by auto
  show ?thesis
    unfolding *
      simple_function_partition[OF `simple_function M f` `simple_function M g`]
      simple_function_partition[OF `simple_function M g` `simple_function M f`]
  proof (safe intro!: setsum_mono)
    fix x assume "x \<in> space M"
    then have *: "f ` ?S x = {f x}" "g ` ?S x = {g x}" by auto
    show "the_elem (f`?S x) * \<mu> (?S x) \<le> the_elem (g`?S x) * \<mu> (?S x)"
    proof (cases "f x \<le> g x")
      case True then show ?thesis using * by (auto intro!: mult_right_mono)
    next
      case False
      obtain N where N: "{x\<in>space M. \<not> f x \<le> g x} \<subseteq> N" "N \<in> sets M" "\<mu> N = 0"
        using mono by (auto elim!: AE_E)
      have "?S x \<subseteq> N" using N `x \<in> space M` False by auto
      moreover have "?S x \<in> sets M" using assms
        by (rule_tac Int) (auto intro!: simple_functionD)
      ultimately have "\<mu> (?S x) \<le> \<mu> N"
        using `N \<in> sets M` by (auto intro!: measure_mono)
      then show ?thesis using `\<mu> N = 0` by auto
    qed
  qed
qed

lemma (in measure_space) simple_integral_mono:
  assumes "simple_function M f" and "simple_function M g"
  and mono: "\<And> x. x \<in> space M \<Longrightarrow> f x \<le> g x"
  shows "integral\<^isup>S M f \<le> integral\<^isup>S M g"
  using assms by (intro simple_integral_mono_AE) auto

lemma (in measure_space) simple_integral_cong_AE:
  assumes "simple_function M f" "simple_function M g" and "AE x. f x = g x"
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
  assume "space M \<noteq> {}" hence "(\<lambda>x. 1) ` space M = {1::pextreal}" by auto
  thus ?thesis
    using simple_integral_indicator[OF assms simple_function_const[of 1]]
    using sets_into_space[OF assms]
    by (auto intro!: arg_cong[where f="\<mu>"])
qed

lemma (in measure_space) simple_integral_null_set:
  assumes "simple_function M u" "N \<in> null_sets"
  shows "(\<integral>\<^isup>Sx. u x * indicator N x \<partial>M) = 0"
proof -
  have "AE x. indicator N x = (0 :: pextreal)"
    using `N \<in> null_sets` by (auto simp: indicator_def intro!: AE_I[of _ N])
  then have "(\<integral>\<^isup>Sx. u x * indicator N x \<partial>M) = (\<integral>\<^isup>Sx. 0 \<partial>M)"
    using assms by (intro simple_integral_cong_AE) auto
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
    unfolding pextreal_mult_cancel_left by auto
qed

lemma (in measure_space) simple_integral_subalgebra:
  assumes N: "measure_space N" and [simp]: "space N = space M" "measure N = measure M"
  shows "integral\<^isup>S N = integral\<^isup>S M"
  unfolding simple_integral_def_raw by simp

lemma (in measure_space) simple_integral_vimage:
  assumes T: "sigma_algebra M'" "T \<in> measurable M M'"
    and f: "simple_function M' f"
    and \<nu>: "\<And>A. A \<in> sets M' \<Longrightarrow> measure M' A = \<mu> (T -` A \<inter> space M)"
  shows "integral\<^isup>S M' f = (\<integral>\<^isup>S x. f (T x) \<partial>M)"
proof -
  interpret T: measure_space M' using \<nu> by (rule measure_space_vimage[OF T])
  show "integral\<^isup>S M' f = (\<integral>\<^isup>S x. f (T x) \<partial>M)"
    unfolding simple_integral_def
  proof (intro setsum_mono_zero_cong_right ballI)
    show "(\<lambda>x. f (T x)) ` space M \<subseteq> f ` space M'"
      using T unfolding measurable_def by auto
    show "finite (f ` space M')"
      using f unfolding simple_function_def by auto
  next
    fix i assume "i \<in> f ` space M' - (\<lambda>x. f (T x)) ` space M"
    then have "T -` (f -` {i} \<inter> space M') \<inter> space M = {}" by (auto simp: image_iff)
    with f[THEN T.simple_functionD(2), THEN \<nu>]
    show "i * T.\<mu> (f -` {i} \<inter> space M') = 0" by simp
  next
    fix i assume "i \<in> (\<lambda>x. f (T x)) ` space M"
    then have "T -` (f -` {i} \<inter> space M') \<inter> space M = (\<lambda>x. f (T x)) -` {i} \<inter> space M"
      using T unfolding measurable_def by auto
    with f[THEN T.simple_functionD(2), THEN \<nu>]
    show "i * T.\<mu> (f -` {i} \<inter> space M') = i * \<mu> ((\<lambda>x. f (T x)) -` {i} \<inter> space M)"
      by auto
  qed
qed

section "Continuous positive integration"

definition positive_integral_def:
  "integral\<^isup>P M f = (SUP g : {g. simple_function M g \<and> g \<le> f}. integral\<^isup>S M g)"

syntax
  "_positive_integral" :: "'a \<Rightarrow> ('a \<Rightarrow> pextreal) \<Rightarrow> ('a, 'b) measure_space_scheme \<Rightarrow> pextreal" ("\<integral>\<^isup>+ _. _ \<partial>_" [60,61] 110)

translations
  "\<integral>\<^isup>+ x. f \<partial>M" == "CONST integral\<^isup>P M (%x. f)"

lemma (in measure_space) positive_integral_alt: "integral\<^isup>P M f =
    (SUP g : {g. simple_function M g \<and> g \<le> f \<and> \<omega> \<notin> g`space M}. integral\<^isup>S M g)"
  (is "_ = ?alt")
proof (rule antisym SUP_leI)
  show "integral\<^isup>P M f \<le> ?alt" unfolding positive_integral_def
  proof (safe intro!: SUP_leI)
    fix g assume g: "simple_function M g" "g \<le> f"
    let ?G = "g -` {\<omega>} \<inter> space M"
    show "integral\<^isup>S M g \<le>
      (SUP h : {i. simple_function M i \<and> i \<le> f \<and> \<omega> \<notin> i ` space M}. integral\<^isup>S M h)"
      (is "integral\<^isup>S M g \<le> SUPR ?A _")
    proof cases
      let ?g = "\<lambda>x. indicator (space M - ?G) x * g x"
      have g': "simple_function M ?g"
        using g by (auto intro: simple_functionD)
      moreover
      assume "\<mu> ?G = 0"
      then have "AE x. g x = ?g x" using g
        by (intro AE_I[where N="?G"])
           (auto intro: simple_functionD simp: indicator_def)
      with g(1) g' have "integral\<^isup>S M g = integral\<^isup>S M ?g"
        by (rule simple_integral_cong_AE)
      moreover have "?g \<le> g" by (auto simp: le_fun_def indicator_def)
      from this `g \<le> f` have "?g \<le> f" by (rule order_trans)
      moreover have "\<omega> \<notin> ?g ` space M"
        by (auto simp: indicator_def split: split_if_asm)
      ultimately show ?thesis by (auto intro!: le_SUPI)
    next
      assume "\<mu> ?G \<noteq> 0"
      then have "?G \<noteq> {}" by auto
      then have "\<omega> \<in> g`space M" by force
      then have "space M \<noteq> {}" by auto
      have "SUPR ?A (integral\<^isup>S M) = \<omega>"
      proof (intro SUP_\<omega>[THEN iffD2] allI impI)
        fix x assume "x < \<omega>"
        then guess n unfolding less_\<omega>_Ex_of_nat .. note n = this
        then have "0 < n" by (intro neq0_conv[THEN iffD1] notI) simp
        let ?g = "\<lambda>x. (of_nat n / (if \<mu> ?G = \<omega> then 1 else \<mu> ?G)) * indicator ?G x"
        show "\<exists>i\<in>?A. x < integral\<^isup>S M i"
        proof (intro bexI impI CollectI conjI)
          show "simple_function M ?g" using g
            by (auto intro!: simple_functionD simple_function_add)
          have "?g \<le> g" by (auto simp: le_fun_def indicator_def)
          from this g(2) show "?g \<le> f" by (rule order_trans)
          show "\<omega> \<notin> ?g ` space M"
            using `\<mu> ?G \<noteq> 0` by (auto simp: indicator_def split: split_if_asm)
          have "x < (of_nat n / (if \<mu> ?G = \<omega> then 1 else \<mu> ?G)) * \<mu> ?G"
            using n `\<mu> ?G \<noteq> 0` `0 < n`
            by (auto simp: pextreal_noteq_omega_Ex field_simps)
          also have "\<dots> = integral\<^isup>S M ?g" using g `space M \<noteq> {}`
            by (subst simple_integral_indicator)
               (auto simp: image_constant ac_simps dest: simple_functionD)
          finally show "x < integral\<^isup>S M ?g" .
        qed
      qed
      then show ?thesis by simp
    qed
  qed
qed (auto intro!: SUP_subset simp: positive_integral_def)

lemma (in measure_space) positive_integral_cong_measure:
  assumes "\<And>A. A \<in> sets M \<Longrightarrow> measure N A = \<mu> A" "sets N = sets M" "space N = space M"
  shows "integral\<^isup>P N f = integral\<^isup>P M f"
proof -
  interpret v: measure_space N
    by (rule measure_space_cong) fact+
  with assms show ?thesis
    unfolding positive_integral_def SUPR_def
    by (auto intro!: arg_cong[where f=Sup] image_cong
             simp: simple_integral_cong_measure[OF assms]
                   simple_function_cong_algebra[OF assms(2,3)])
qed

lemma (in measure_space) positive_integral_alt1:
  "integral\<^isup>P M f =
    (SUP g : {g. simple_function M g \<and> (\<forall>x\<in>space M. g x \<le> f x \<and> g x \<noteq> \<omega>)}. integral\<^isup>S M g)"
  unfolding positive_integral_alt SUPR_def
proof (safe intro!: arg_cong[where f=Sup])
  fix g let ?g = "\<lambda>x. if x \<in> space M then g x else f x"
  assume "simple_function M g" "\<forall>x\<in>space M. g x \<le> f x \<and> g x \<noteq> \<omega>"
  hence "?g \<le> f" "simple_function M ?g" "integral\<^isup>S M g = integral\<^isup>S M ?g"
    "\<omega> \<notin> g`space M"
    unfolding le_fun_def by (auto cong: simple_function_cong simple_integral_cong)
  thus "integral\<^isup>S M g \<in> integral\<^isup>S M ` {g. simple_function M g \<and> g \<le> f \<and> \<omega> \<notin> g`space M}"
    by auto
next
  fix g assume "simple_function M g" "g \<le> f" "\<omega> \<notin> g`space M"
  hence "simple_function M g" "\<forall>x\<in>space M. g x \<le> f x \<and> g x \<noteq> \<omega>"
    by (auto simp add: le_fun_def image_iff)
  thus "integral\<^isup>S M g \<in> integral\<^isup>S M ` {g. simple_function M g \<and> (\<forall>x\<in>space M. g x \<le> f x \<and> g x \<noteq> \<omega>)}"
    by auto
qed

lemma (in measure_space) positive_integral_cong:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> f x = g x"
  shows "integral\<^isup>P M f = integral\<^isup>P M g"
proof -
  have "\<And>h. (\<forall>x\<in>space M. h x \<le> f x \<and> h x \<noteq> \<omega>) = (\<forall>x\<in>space M. h x \<le> g x \<and> h x \<noteq> \<omega>)"
    using assms by auto
  thus ?thesis unfolding positive_integral_alt1 by auto
qed

lemma (in measure_space) positive_integral_eq_simple_integral:
  assumes "simple_function M f"
  shows "integral\<^isup>P M f = integral\<^isup>S M f"
  unfolding positive_integral_def
proof (safe intro!: pextreal_SUPI)
  fix g assume "simple_function M g" "g \<le> f"
  with assms show "integral\<^isup>S M g \<le> integral\<^isup>S M f"
    by (auto intro!: simple_integral_mono simp: le_fun_def)
next
  fix y assume "\<forall>x. x\<in>{g. simple_function M g \<and> g \<le> f} \<longrightarrow> integral\<^isup>S M x \<le> y"
  with assms show "integral\<^isup>S M f \<le> y" by auto
qed

lemma (in measure_space) positive_integral_mono_AE:
  assumes ae: "AE x. u x \<le> v x"
  shows "integral\<^isup>P M u \<le> integral\<^isup>P M v"
  unfolding positive_integral_alt1
proof (safe intro!: SUPR_mono)
  fix a assume a: "simple_function M a" and mono: "\<forall>x\<in>space M. a x \<le> u x \<and> a x \<noteq> \<omega>"
  from ae obtain N where N: "{x\<in>space M. \<not> u x \<le> v x} \<subseteq> N" "N \<in> sets M" "\<mu> N = 0"
    by (auto elim!: AE_E)
  have "simple_function M (\<lambda>x. a x * indicator (space M - N) x)"
    using `N \<in> sets M` a by auto
  with a show "\<exists>b\<in>{g. simple_function M g \<and> (\<forall>x\<in>space M. g x \<le> v x \<and> g x \<noteq> \<omega>)}.
    integral\<^isup>S M a \<le> integral\<^isup>S M b"
  proof (safe intro!: bexI[of _ "\<lambda>x. a x * indicator (space M - N) x"]
                      simple_integral_mono_AE)
    show "AE x. a x \<le> a x * indicator (space M - N) x"
    proof (rule AE_I, rule subset_refl)
      have *: "{x \<in> space M. \<not> a x \<le> a x * indicator (space M - N) x} =
        N \<inter> {x \<in> space M. a x \<noteq> 0}" (is "?N = _")
        using `N \<in> sets M`[THEN sets_into_space] by (auto simp: indicator_def)
      then show "?N \<in> sets M"
        using `N \<in> sets M` `simple_function M a`[THEN borel_measurable_simple_function]
        by (auto intro!: measure_mono Int)
      then have "\<mu> ?N \<le> \<mu> N"
        unfolding * using `N \<in> sets M` by (auto intro!: measure_mono)
      then show "\<mu> ?N = 0" using `\<mu> N = 0` by auto
    qed
  next
    fix x assume "x \<in> space M"
    show "a x * indicator (space M - N) x \<le> v x"
    proof (cases "x \<in> N")
      case True then show ?thesis by simp
    next
      case False
      with N mono have "a x \<le> u x" "u x \<le> v x" using `x \<in> space M` by auto
      with False `x \<in> space M` show "a x * indicator (space M - N) x \<le> v x" by auto
    qed
    assume "a x * indicator (space M - N) x = \<omega>"
    with mono `x \<in> space M` show False
      by (simp split: split_if_asm add: indicator_def)
  qed
qed

lemma (in measure_space) positive_integral_cong_AE:
  "AE x. u x = v x \<Longrightarrow> integral\<^isup>P M u = integral\<^isup>P M v"
  by (auto simp: eq_iff intro!: positive_integral_mono_AE)

lemma (in measure_space) positive_integral_mono:
  "(\<And>x. x \<in> space M \<Longrightarrow> u x \<le> v x) \<Longrightarrow> integral\<^isup>P M u \<le> integral\<^isup>P M v"
  by (auto intro: positive_integral_mono_AE)

lemma image_set_cong:
  assumes A: "\<And>x. x \<in> A \<Longrightarrow> \<exists>y\<in>B. f x = g y"
  assumes B: "\<And>y. y \<in> B \<Longrightarrow> \<exists>x\<in>A. g y = f x"
  shows "f ` A = g ` B"
  using assms by blast

lemma (in measure_space) positive_integral_SUP_approx:
  assumes "f \<up> s"
  and f: "\<And>i. f i \<in> borel_measurable M"
  and "simple_function M u"
  and le: "u \<le> s" and real: "\<omega> \<notin> u`space M"
  shows "integral\<^isup>S M u \<le> (SUP i. integral\<^isup>P M (f i))" (is "_ \<le> ?S")
proof (rule pextreal_le_mult_one_interval)
  fix a :: pextreal assume "0 < a" "a < 1"
  hence "a \<noteq> 0" by auto
  let "?B i" = "{x \<in> space M. a * u x \<le> f i x}"
  have B: "\<And>i. ?B i \<in> sets M"
    using f `simple_function M u` by (auto simp: borel_measurable_simple_function)

  let "?uB i x" = "u x * indicator (?B i) x"

  { fix i have "?B i \<subseteq> ?B (Suc i)"
    proof safe
      fix i x assume "a * u x \<le> f i x"
      also have "\<dots> \<le> f (Suc i) x"
        using `f \<up> s` unfolding isoton_def le_fun_def by auto
      finally show "a * u x \<le> f (Suc i) x" .
    qed }
  note B_mono = this

  have u: "\<And>x. x \<in> space M \<Longrightarrow> u -` {u x} \<inter> space M \<in> sets M"
    using `simple_function M u` by (auto simp add: simple_function_def)

  have "\<And>i. (\<lambda>n. (u -` {i} \<inter> space M) \<inter> ?B n) \<up> (u -` {i} \<inter> space M)" using B_mono unfolding isoton_def
  proof safe
    fix x i assume "x \<in> space M"
    show "x \<in> (\<Union>i. (u -` {u x} \<inter> space M) \<inter> ?B i)"
    proof cases
      assume "u x = 0" thus ?thesis using `x \<in> space M` by simp
    next
      assume "u x \<noteq> 0"
      with `a < 1` real `x \<in> space M`
      have "a * u x < 1 * u x" by (rule_tac pextreal_mult_strict_right_mono) (auto simp: image_iff)
      also have "\<dots> \<le> (SUP i. f i x)" using le `f \<up> s`
        unfolding isoton_fun_expand by (auto simp: isoton_def le_fun_def)
      finally obtain i where "a * u x < f i x" unfolding SUPR_def
        by (auto simp add: less_Sup_iff)
      hence "a * u x \<le> f i x" by auto
      thus ?thesis using `x \<in> space M` by auto
    qed
  qed auto
  note measure_conv = measure_up[OF Int[OF u B] this]

  have "integral\<^isup>S M u = (SUP i. integral\<^isup>S M (?uB i))"
    unfolding simple_integral_indicator[OF B `simple_function M u`]
  proof (subst SUPR_pextreal_setsum, safe)
    fix x n assume "x \<in> space M"
    have "\<mu> (u -` {u x} \<inter> space M \<inter> {x \<in> space M. a * u x \<le> f n x})
      \<le> \<mu> (u -` {u x} \<inter> space M \<inter> {x \<in> space M. a * u x \<le> f (Suc n) x})"
      using B_mono Int[OF u[OF `x \<in> space M`] B] by (auto intro!: measure_mono)
    thus "u x * \<mu> (u -` {u x} \<inter> space M \<inter> ?B n)
            \<le> u x * \<mu> (u -` {u x} \<inter> space M \<inter> ?B (Suc n))"
      by (auto intro: mult_left_mono)
  next
    show "integral\<^isup>S M u =
      (\<Sum>i\<in>u ` space M. SUP n. i * \<mu> (u -` {i} \<inter> space M \<inter> ?B n))"
      using measure_conv unfolding simple_integral_def isoton_def
      by (auto intro!: setsum_cong simp: pextreal_SUP_cmult)
  qed
  moreover
  have "a * (SUP i. integral\<^isup>S M (?uB i)) \<le> ?S"
    unfolding pextreal_SUP_cmult[symmetric]
  proof (safe intro!: SUP_mono bexI)
    fix i
    have "a * integral\<^isup>S M (?uB i) = (\<integral>\<^isup>Sx. a * ?uB i x \<partial>M)"
      using B `simple_function M u`
      by (subst simple_integral_mult[symmetric]) (auto simp: field_simps)
    also have "\<dots> \<le> integral\<^isup>P M (f i)"
    proof -
      have "\<And>x. a * ?uB i x \<le> f i x" unfolding indicator_def by auto
      hence *: "simple_function M (\<lambda>x. a * ?uB i x)" using B assms(3)
        by (auto intro!: simple_integral_mono)
      show ?thesis unfolding positive_integral_eq_simple_integral[OF *, symmetric]
        by (auto intro!: positive_integral_mono simp: indicator_def)
    qed
    finally show "a * integral\<^isup>S M (?uB i) \<le> integral\<^isup>P M (f i)"
      by auto
  qed simp
  ultimately show "a * integral\<^isup>S M u \<le> ?S" by simp
qed

text {* Beppo-Levi monotone convergence theorem *}
lemma (in measure_space) positive_integral_isoton:
  assumes "f \<up> u" "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>i. integral\<^isup>P M (f i)) \<up> integral\<^isup>P M u"
  unfolding isoton_def
proof safe
  fix i show "integral\<^isup>P M (f i) \<le> integral\<^isup>P M (f (Suc i))"
    apply (rule positive_integral_mono)
    using `f \<up> u` unfolding isoton_def le_fun_def by auto
next
  have u: "u = (SUP i. f i)" using `f \<up> u` unfolding isoton_def by auto
  show "(SUP i. integral\<^isup>P M (f i)) = integral\<^isup>P M u"
  proof (rule antisym)
    from `f \<up> u`[THEN isoton_Sup, unfolded le_fun_def]
    show "(SUP j. integral\<^isup>P M (f j)) \<le> integral\<^isup>P M u"
      by (auto intro!: SUP_leI positive_integral_mono)
  next
    show "integral\<^isup>P M u \<le> (SUP i. integral\<^isup>P M (f i))"
      unfolding positive_integral_alt[of u]
      by (auto intro!: SUP_leI positive_integral_SUP_approx[OF assms])
  qed
qed

lemma (in measure_space) positive_integral_monotone_convergence_SUP:
  assumes "\<And>i x. x \<in> space M \<Longrightarrow> f i x \<le> f (Suc i) x"
  assumes "\<And>i. f i \<in> borel_measurable M"
  shows "(SUP i. integral\<^isup>P M (f i)) = (\<integral>\<^isup>+ x. (SUP i. f i x) \<partial>M)"
    (is "_ = integral\<^isup>P M ?u")
proof -
  show ?thesis
  proof (rule antisym)
    show "(SUP j. integral\<^isup>P M (f j)) \<le> integral\<^isup>P M ?u"
      by (auto intro!: SUP_leI positive_integral_mono le_SUPI)
  next
    def rf \<equiv> "\<lambda>i. \<lambda>x\<in>space M. f i x" and ru \<equiv> "\<lambda>x\<in>space M. ?u x"
    have "\<And>i. rf i \<in> borel_measurable M" unfolding rf_def
      using assms by (simp cong: measurable_cong)
    moreover have iso: "rf \<up> ru" using assms unfolding rf_def ru_def
      unfolding isoton_def le_fun_def fun_eq_iff SUPR_apply
      using SUP_const[OF UNIV_not_empty]
      by (auto simp: restrict_def le_fun_def fun_eq_iff)
    ultimately have "integral\<^isup>P M ru \<le> (SUP i. integral\<^isup>P M (rf i))"
      unfolding positive_integral_alt[of ru]
      by (auto simp: le_fun_def intro!: SUP_leI positive_integral_SUP_approx)
    then show "integral\<^isup>P M ?u \<le> (SUP i. integral\<^isup>P M (f i))"
      unfolding ru_def rf_def by (simp cong: positive_integral_cong)
  qed
qed

lemma (in measure_space) SUP_simple_integral_sequences:
  assumes f: "f \<up> u" "\<And>i. simple_function M (f i)"
  and g: "g \<up> u" "\<And>i. simple_function M (g i)"
  shows "(SUP i. integral\<^isup>S M (f i)) = (SUP i. integral\<^isup>S M (g i))"
    (is "SUPR _ ?F = SUPR _ ?G")
proof -
  have "(SUP i. ?F i) = (SUP i. integral\<^isup>P M (f i))"
    using assms by (simp add: positive_integral_eq_simple_integral)
  also have "\<dots> = integral\<^isup>P M u"
    using positive_integral_isoton[OF f(1) borel_measurable_simple_function[OF f(2)]]
    unfolding isoton_def by simp
  also have "\<dots> = (SUP i. integral\<^isup>P M (g i))"
    using positive_integral_isoton[OF g(1) borel_measurable_simple_function[OF g(2)]]
    unfolding isoton_def by simp
  also have "\<dots> = (SUP i. ?G i)"
    using assms by (simp add: positive_integral_eq_simple_integral)
  finally show ?thesis .
qed

lemma (in measure_space) positive_integral_const[simp]:
  "(\<integral>\<^isup>+ x. c \<partial>M) = c * \<mu> (space M)"
  by (subst positive_integral_eq_simple_integral) auto

lemma (in measure_space) positive_integral_isoton_simple:
  assumes "f \<up> u" and e: "\<And>i. simple_function M (f i)"
  shows "(\<lambda>i. integral\<^isup>S M (f i)) \<up> integral\<^isup>P M u"
  using positive_integral_isoton[OF `f \<up> u` e(1)[THEN borel_measurable_simple_function]]
  unfolding positive_integral_eq_simple_integral[OF e] .

lemma (in measure_space) positive_integral_vimage:
  assumes T: "sigma_algebra M'" "T \<in> measurable M M'" and f: "f \<in> borel_measurable M'"
    and \<nu>: "\<And>A. A \<in> sets M' \<Longrightarrow> measure M' A = \<mu> (T -` A \<inter> space M)"
  shows "integral\<^isup>P M' f = (\<integral>\<^isup>+ x. f (T x) \<partial>M)"
proof -
  interpret T: measure_space M' using \<nu> by (rule measure_space_vimage[OF T])
  obtain f' where f': "f' \<up> f" "\<And>i. simple_function M' (f' i)"
    using T.borel_measurable_implies_simple_function_sequence[OF f] by blast
  then have f: "(\<lambda>i x. f' i (T x)) \<up> (\<lambda>x. f (T x))" "\<And>i. simple_function M (\<lambda>x. f' i (T x))"
    using simple_function_vimage[OF T] unfolding isoton_fun_expand by auto
  show "integral\<^isup>P M' f = (\<integral>\<^isup>+ x. f (T x) \<partial>M)"
    using positive_integral_isoton_simple[OF f]
    using T.positive_integral_isoton_simple[OF f']
    by (simp add: simple_integral_vimage[OF T f'(2) \<nu>] isoton_def)
qed

lemma (in measure_space) positive_integral_linear:
  assumes f: "f \<in> borel_measurable M"
  and g: "g \<in> borel_measurable M"
  shows "(\<integral>\<^isup>+ x. a * f x + g x \<partial>M) = a * integral\<^isup>P M f + integral\<^isup>P M g"
    (is "integral\<^isup>P M ?L = _")
proof -
  from borel_measurable_implies_simple_function_sequence'[OF f] guess u .
  note u = this positive_integral_isoton_simple[OF this(1-2)]
  from borel_measurable_implies_simple_function_sequence'[OF g] guess v .
  note v = this positive_integral_isoton_simple[OF this(1-2)]
  let "?L' i x" = "a * u i x + v i x"

  have "?L \<in> borel_measurable M"
    using assms by simp
  from borel_measurable_implies_simple_function_sequence'[OF this] guess l .
  note positive_integral_isoton_simple[OF this(1-2)] and l = this
  moreover have "(SUP i. integral\<^isup>S M (l i)) = (SUP i. integral\<^isup>S M (?L' i))"
  proof (rule SUP_simple_integral_sequences[OF l(1-2)])
    show "?L' \<up> ?L" "\<And>i. simple_function M (?L' i)"
      using u v by (auto simp: isoton_fun_expand isoton_add isoton_cmult_right)
  qed
  moreover from u v have L'_isoton:
      "(\<lambda>i. integral\<^isup>S M (?L' i)) \<up> a * integral\<^isup>P M f + integral\<^isup>P M g"
    by (simp add: isoton_add isoton_cmult_right)
  ultimately show ?thesis by (simp add: isoton_def)
qed

lemma (in measure_space) positive_integral_cmult:
  assumes "f \<in> borel_measurable M"
  shows "(\<integral>\<^isup>+ x. c * f x \<partial>M) = c * integral\<^isup>P M f"
  using positive_integral_linear[OF assms, of "\<lambda>x. 0" c] by auto

lemma (in measure_space) positive_integral_multc:
  assumes "f \<in> borel_measurable M"
  shows "(\<integral>\<^isup>+ x. f x * c \<partial>M) = integral\<^isup>P M f * c"
  unfolding mult_commute[of _ c] positive_integral_cmult[OF assms] by simp

lemma (in measure_space) positive_integral_indicator[simp]:
  "A \<in> sets M \<Longrightarrow> (\<integral>\<^isup>+ x. indicator A x\<partial>M) = \<mu> A"
  by (subst positive_integral_eq_simple_integral)
     (auto simp: simple_function_indicator simple_integral_indicator)

lemma (in measure_space) positive_integral_cmult_indicator:
  "A \<in> sets M \<Longrightarrow> (\<integral>\<^isup>+ x. c * indicator A x \<partial>M) = c * \<mu> A"
  by (subst positive_integral_eq_simple_integral)
     (auto simp: simple_function_indicator simple_integral_indicator)

lemma (in measure_space) positive_integral_add:
  assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "(\<integral>\<^isup>+ x. f x + g x \<partial>M) = integral\<^isup>P M f + integral\<^isup>P M g"
  using positive_integral_linear[OF assms, of 1] by simp

lemma (in measure_space) positive_integral_setsum:
  assumes "\<And>i. i\<in>P \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<integral>\<^isup>+ x. (\<Sum>i\<in>P. f i x) \<partial>M) = (\<Sum>i\<in>P. integral\<^isup>P M (f i))"
proof cases
  assume "finite P"
  from this assms show ?thesis
  proof induct
    case (insert i P)
    have "f i \<in> borel_measurable M"
      "(\<lambda>x. \<Sum>i\<in>P. f i x) \<in> borel_measurable M"
      using insert by (auto intro!: borel_measurable_pextreal_setsum)
    from positive_integral_add[OF this]
    show ?case using insert by auto
  qed simp
qed simp

lemma (in measure_space) positive_integral_diff:
  assumes f: "f \<in> borel_measurable M" and g: "g \<in> borel_measurable M"
  and fin: "integral\<^isup>P M g \<noteq> \<omega>"
  and mono: "\<And>x. x \<in> space M \<Longrightarrow> g x \<le> f x"
  shows "(\<integral>\<^isup>+ x. f x - g x \<partial>M) = integral\<^isup>P M f - integral\<^isup>P M g"
proof -
  have borel: "(\<lambda>x. f x - g x) \<in> borel_measurable M"
    using f g by (rule borel_measurable_pextreal_diff)
  have "(\<integral>\<^isup>+x. f x - g x \<partial>M) + integral\<^isup>P M g = integral\<^isup>P M f"
    unfolding positive_integral_add[OF borel g, symmetric]
  proof (rule positive_integral_cong)
    fix x assume "x \<in> space M"
    from mono[OF this] show "f x - g x + g x = f x"
      by (cases "f x", cases "g x", simp, simp, cases "g x", auto)
  qed
  with mono show ?thesis
    by (subst minus_pextreal_eq2[OF _ fin]) (auto intro!: positive_integral_mono)
qed

lemma (in measure_space) positive_integral_psuminf:
  assumes "\<And>i. f i \<in> borel_measurable M"
  shows "(\<integral>\<^isup>+ x. (\<Sum>\<^isub>\<infinity> i. f i x) \<partial>M) = (\<Sum>\<^isub>\<infinity> i. integral\<^isup>P M (f i))"
proof -
  have "(\<lambda>i. (\<integral>\<^isup>+x. (\<Sum>i<i. f i x) \<partial>M)) \<up> (\<integral>\<^isup>+x. (\<Sum>\<^isub>\<infinity>i. f i x) \<partial>M)"
    by (rule positive_integral_isoton)
       (auto intro!: borel_measurable_pextreal_setsum assms positive_integral_mono
                     arg_cong[where f=Sup]
             simp: isoton_def le_fun_def psuminf_def fun_eq_iff SUPR_def Sup_fun_def)
  thus ?thesis
    by (auto simp: isoton_def psuminf_def positive_integral_setsum[OF assms])
qed

text {* Fatou's lemma: convergence theorem on limes inferior *}
lemma (in measure_space) positive_integral_lim_INF:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> pextreal"
  assumes "\<And>i. u i \<in> borel_measurable M"
  shows "(\<integral>\<^isup>+ x. (SUP n. INF m. u (m + n) x) \<partial>M) \<le>
    (SUP n. INF m. integral\<^isup>P M (u (m + n)))"
proof -
  have "(\<integral>\<^isup>+x. (SUP n. INF m. u (m + n) x) \<partial>M)
      = (SUP n. (\<integral>\<^isup>+x. (INF m. u (m + n) x) \<partial>M))"
    using assms
    by (intro positive_integral_monotone_convergence_SUP[symmetric] INF_mono)
       (auto simp del: add_Suc simp add: add_Suc[symmetric])
  also have "\<dots> \<le> (SUP n. INF m. integral\<^isup>P M (u (m + n)))"
    by (auto intro!: SUP_mono bexI le_INFI positive_integral_mono INF_leI)
  finally show ?thesis .
qed

lemma (in measure_space) measure_space_density:
  assumes borel: "u \<in> borel_measurable M"
    and M'[simp]: "M' = (M\<lparr>measure := \<lambda>A. (\<integral>\<^isup>+ x. u x * indicator A x \<partial>M)\<rparr>)"
  shows "measure_space M'"
proof -
  interpret M': sigma_algebra M' by (intro sigma_algebra_cong) auto
  show ?thesis
  proof
    show "measure M' {} = 0" unfolding M' by simp
    show "countably_additive M' (measure M')"
    proof (intro countably_additiveI)
      fix A :: "nat \<Rightarrow> 'a set" assume "range A \<subseteq> sets M'"
      then have "\<And>i. (\<lambda>x. u x * indicator (A i) x) \<in> borel_measurable M"
        using borel by (auto intro: borel_measurable_indicator)
      moreover assume "disjoint_family A"
      note psuminf_indicator[OF this]
      ultimately show "(\<Sum>\<^isub>\<infinity>n. measure M' (A n)) = measure M' (\<Union>x. A x)"
        by (simp add: positive_integral_psuminf[symmetric])
    qed
  qed
qed

lemma (in measure_space) positive_integral_translated_density:
  assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
    and M': "M' = (M\<lparr> measure := \<lambda>A. (\<integral>\<^isup>+ x. f x * indicator A x \<partial>M)\<rparr>)"
  shows "integral\<^isup>P M' g = (\<integral>\<^isup>+ x. f x * g x \<partial>M)"
proof -
  from measure_space_density[OF assms(1) M']
  interpret T: measure_space M' .
  have borel[simp]:
    "borel_measurable M' = borel_measurable M"
    "simple_function M' = simple_function M"
    unfolding measurable_def simple_function_def_raw by (auto simp: M')
  from borel_measurable_implies_simple_function_sequence[OF assms(2)]
  obtain G where G: "\<And>i. simple_function M (G i)" "G \<up> g" by blast
  note G_borel = borel_measurable_simple_function[OF this(1)]
  from T.positive_integral_isoton[unfolded borel, OF `G \<up> g` G_borel]
  have *: "(\<lambda>i. integral\<^isup>P M' (G i)) \<up> integral\<^isup>P M' g" .
  { fix i
    have [simp]: "finite (G i ` space M)"
      using G(1) unfolding simple_function_def by auto
    have "integral\<^isup>P M' (G i) = integral\<^isup>S M' (G i)"
      using G T.positive_integral_eq_simple_integral by simp
    also have "\<dots> = (\<integral>\<^isup>+x. f x * (\<Sum>y\<in>G i`space M. y * indicator (G i -` {y} \<inter> space M) x) \<partial>M)"
      apply (simp add: simple_integral_def M')
      apply (subst positive_integral_cmult[symmetric])
      using G_borel assms(1) apply (fastsimp intro: borel_measurable_vimage)
      apply (subst positive_integral_setsum[symmetric])
      using G_borel assms(1) apply (fastsimp intro: borel_measurable_vimage)
      by (simp add: setsum_right_distrib field_simps)
    also have "\<dots> = (\<integral>\<^isup>+x. f x * G i x \<partial>M)"
      by (auto intro!: positive_integral_cong
               simp: indicator_def if_distrib setsum_cases)
    finally have "integral\<^isup>P M' (G i) = (\<integral>\<^isup>+x. f x * G i x \<partial>M)" . }
  with * have eq_Tg: "(\<lambda>i. (\<integral>\<^isup>+x. f x * G i x \<partial>M)) \<up> integral\<^isup>P M' g" by simp
  from G(2) have "(\<lambda>i x. f x * G i x) \<up> (\<lambda>x. f x * g x)"
    unfolding isoton_fun_expand by (auto intro!: isoton_cmult_right)
  then have "(\<lambda>i. (\<integral>\<^isup>+x. f x * G i x \<partial>M)) \<up> (\<integral>\<^isup>+x. f x * g x \<partial>M)"
    using assms(1) G_borel by (auto intro!: positive_integral_isoton borel_measurable_pextreal_times)
  with eq_Tg show "integral\<^isup>P M' g = (\<integral>\<^isup>+x. f x * g x \<partial>M)"
    unfolding isoton_def by simp
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

lemma (in measure_space) positive_integral_Markov_inequality:
  assumes borel: "u \<in> borel_measurable M" and "A \<in> sets M" and c: "c \<noteq> \<omega>"
  shows "\<mu> ({x\<in>space M. 1 \<le> c * u x} \<inter> A) \<le> c * (\<integral>\<^isup>+ x. u x * indicator A x \<partial>M)"
    (is "\<mu> ?A \<le> _ * ?PI")
proof -
  have "?A \<in> sets M"
    using `A \<in> sets M` borel by auto
  hence "\<mu> ?A = (\<integral>\<^isup>+ x. indicator ?A x \<partial>M)"
    using positive_integral_indicator by simp
  also have "\<dots> \<le> (\<integral>\<^isup>+ x. c * (u x * indicator A x) \<partial>M)"
  proof (rule positive_integral_mono)
    fix x assume "x \<in> space M"
    show "indicator ?A x \<le> c * (u x * indicator A x)"
      by (cases "x \<in> ?A") auto
  qed
  also have "\<dots> = c * (\<integral>\<^isup>+ x. u x * indicator A x \<partial>M)"
    using assms
    by (auto intro!: positive_integral_cmult borel_measurable_indicator)
  finally show ?thesis .
qed

lemma (in measure_space) positive_integral_0_iff:
  assumes borel: "u \<in> borel_measurable M"
  shows "integral\<^isup>P M u = 0 \<longleftrightarrow> \<mu> {x\<in>space M. u x \<noteq> 0} = 0"
    (is "_ \<longleftrightarrow> \<mu> ?A = 0")
proof -
  have A: "?A \<in> sets M" using borel by auto
  have u: "(\<integral>\<^isup>+ x. u x * indicator ?A x \<partial>M) = integral\<^isup>P M u"
    by (auto intro!: positive_integral_cong simp: indicator_def)

  show ?thesis
  proof
    assume "\<mu> ?A = 0"
    hence "?A \<in> null_sets" using `?A \<in> sets M` by auto
    from positive_integral_null_set[OF this]
    have "0 = (\<integral>\<^isup>+ x. u x * indicator ?A x \<partial>M)" by simp
    thus "integral\<^isup>P M u = 0" unfolding u by simp
  next
    assume *: "integral\<^isup>P M u = 0"
    let "?M n" = "{x \<in> space M. 1 \<le> of_nat n * u x}"
    have "0 = (SUP n. \<mu> (?M n \<inter> ?A))"
    proof -
      { fix n
        from positive_integral_Markov_inequality[OF borel `?A \<in> sets M`, of "of_nat n"]
        have "\<mu> (?M n \<inter> ?A) = 0" unfolding * u by simp }
      thus ?thesis by simp
    qed
    also have "\<dots> = \<mu> (\<Union>n. ?M n \<inter> ?A)"
    proof (safe intro!: continuity_from_below)
      fix n show "?M n \<inter> ?A \<in> sets M"
        using borel by (auto intro!: Int)
    next
      fix n x assume "1 \<le> of_nat n * u x"
      also have "\<dots> \<le> of_nat (Suc n) * u x"
        by (subst (1 2) mult_commute) (auto intro!: pextreal_mult_cancel)
      finally show "1 \<le> of_nat (Suc n) * u x" .
    qed
    also have "\<dots> = \<mu> ?A"
    proof (safe intro!: arg_cong[where f="\<mu>"])
      fix x assume "u x \<noteq> 0" and [simp, intro]: "x \<in> space M"
      show "x \<in> (\<Union>n. ?M n \<inter> ?A)"
      proof (cases "u x")
        case (preal r)
        obtain j where "1 / r \<le> of_nat j" using ex_le_of_nat ..
        hence "1 / r * r \<le> of_nat j * r" using preal unfolding mult_le_cancel_right by auto
        hence "1 \<le> of_nat j * r" using preal `u x \<noteq> 0` by auto
        thus ?thesis using `u x \<noteq> 0` preal by (auto simp: real_of_nat_def[symmetric])
      qed auto
    qed
    finally show "\<mu> ?A = 0" by simp
  qed
qed

lemma (in measure_space) positive_integral_0_iff_AE:
  assumes u: "u \<in> borel_measurable M"
  shows "integral\<^isup>P M u = 0 \<longleftrightarrow> (AE x. u x = 0)"
proof -
  have sets: "{x\<in>space M. u x \<noteq> 0} \<in> sets M"
    using u by auto
  then show ?thesis
    using positive_integral_0_iff[OF u] AE_iff_null_set[OF sets] by auto
qed

lemma (in measure_space) positive_integral_restricted:
  assumes "A \<in> sets M"
  shows "integral\<^isup>P (restricted_space A) f = (\<integral>\<^isup>+ x. f x * indicator A x \<partial>M)"
    (is "integral\<^isup>P ?R f = integral\<^isup>P M ?f")
proof -
  have msR: "measure_space ?R" by (rule restricted_measure_space[OF `A \<in> sets M`])
  then interpret R: measure_space ?R .
  have saR: "sigma_algebra ?R" by fact
  have *: "integral\<^isup>P ?R f = integral\<^isup>P ?R ?f"
    by (intro R.positive_integral_cong) auto
  show ?thesis
    unfolding * positive_integral_def
    unfolding simple_function_restricted[OF `A \<in> sets M`]
    apply (simp add: SUPR_def)
    apply (rule arg_cong[where f=Sup])
  proof (auto simp add: image_iff simple_integral_restricted[OF `A \<in> sets M`])
    fix g assume "simple_function M (\<lambda>x. g x * indicator A x)"
      "g \<le> f"
    then show "\<exists>x. simple_function M x \<and> x \<le> (\<lambda>x. f x * indicator A x) \<and>
      (\<integral>\<^isup>Sx. g x * indicator A x \<partial>M) = integral\<^isup>S M x"
      apply (rule_tac exI[of _ "\<lambda>x. g x * indicator A x"])
      by (auto simp: indicator_def le_fun_def)
  next
    fix g assume g: "simple_function M g" "g \<le> (\<lambda>x. f x * indicator A x)"
    then have *: "(\<lambda>x. g x * indicator A x) = g"
      "\<And>x. g x * indicator A x = g x"
      "\<And>x. g x \<le> f x"
      by (auto simp: le_fun_def fun_eq_iff indicator_def split: split_if_asm)
    from g show "\<exists>x. simple_function M (\<lambda>xa. x xa * indicator A xa) \<and> x \<le> f \<and>
      integral\<^isup>S M g = integral\<^isup>S M (\<lambda>xa. x xa * indicator A xa)"
      using `A \<in> sets M`[THEN sets_into_space]
      apply (rule_tac exI[of _ "\<lambda>x. g x * indicator A x"])
      by (fastsimp simp: le_fun_def *)
  qed
qed

lemma (in measure_space) positive_integral_subalgebra:
  assumes borel: "f \<in> borel_measurable N"
  and N: "sets N \<subseteq> sets M" "space N = space M" "\<And>A. A \<in> sets N \<Longrightarrow> measure N A = \<mu> A"
  and sa: "sigma_algebra N"
  shows "integral\<^isup>P N f = integral\<^isup>P M f"
proof -
  interpret N: measure_space N using measure_space_subalgebra[OF sa N] .
  from N.borel_measurable_implies_simple_function_sequence[OF borel]
  obtain fs where Nsf: "\<And>i. simple_function N (fs i)" and "fs \<up> f" by blast
  then have sf: "\<And>i. simple_function M (fs i)"
    using simple_function_subalgebra[OF _ N(1,2)] by blast
  from N.positive_integral_isoton_simple[OF `fs \<up> f` Nsf]
  have "integral\<^isup>P N f = (SUP i. \<Sum>x\<in>fs i ` space M. x * N.\<mu> (fs i -` {x} \<inter> space M))"
    unfolding isoton_def simple_integral_def `space N = space M` by simp
  also have "\<dots> = (SUP i. \<Sum>x\<in>fs i ` space M. x * \<mu> (fs i -` {x} \<inter> space M))"
    using N N.simple_functionD(2)[OF Nsf] unfolding `space N = space M` by auto
  also have "\<dots> = integral\<^isup>P M f"
    using positive_integral_isoton_simple[OF `fs \<up> f` sf]
    unfolding isoton_def simple_integral_def `space N = space M` by simp
  finally show ?thesis .
qed

section "Lebesgue Integral"

definition integrable where
  "integrable M f \<longleftrightarrow> f \<in> borel_measurable M \<and>
    (\<integral>\<^isup>+ x. Real (f x) \<partial>M) \<noteq> \<omega> \<and>
    (\<integral>\<^isup>+ x. Real (- f x) \<partial>M) \<noteq> \<omega>"

lemma integrableD[dest]:
  assumes "integrable M f"
  shows "f \<in> borel_measurable M" "(\<integral>\<^isup>+ x. Real (f x) \<partial>M) \<noteq> \<omega>" "(\<integral>\<^isup>+ x. Real (- f x) \<partial>M) \<noteq> \<omega>"
  using assms unfolding integrable_def by auto

definition lebesgue_integral_def:
  "integral\<^isup>L M f = real ((\<integral>\<^isup>+ x. Real (f x) \<partial>M)) - real ((\<integral>\<^isup>+ x. Real (- f x) \<partial>M))"

syntax
  "_lebesgue_integral" :: "'a \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a, 'b) measure_space_scheme \<Rightarrow> real" ("\<integral> _. _ \<partial>_" [60,61] 110)

translations
  "\<integral> x. f \<partial>M" == "CONST integral\<^isup>L M (%x. f)"

lemma (in measure_space) integral_cong:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> f x = g x"
  shows "integral\<^isup>L M f = integral\<^isup>L M g"
  using assms by (simp cong: positive_integral_cong add: lebesgue_integral_def)

lemma (in measure_space) integral_cong_measure:
  assumes "\<And>A. A \<in> sets M \<Longrightarrow> measure N A = \<mu> A" "sets N = sets M" "space N = space M"
  shows "integral\<^isup>L N f = integral\<^isup>L M f"
proof -
  interpret v: measure_space N
    by (rule measure_space_cong) fact+
  show ?thesis
    by (simp add: positive_integral_cong_measure[OF assms] lebesgue_integral_def)
qed

lemma (in measure_space) integral_cong_AE:
  assumes cong: "AE x. f x = g x"
  shows "integral\<^isup>L M f = integral\<^isup>L M g"
proof -
  have "AE x. Real (f x) = Real (g x)" using cong by auto
  moreover have "AE x. Real (- f x) = Real (- g x)" using cong by auto
  ultimately show ?thesis
    by (simp cong: positive_integral_cong_AE add: lebesgue_integral_def)
qed

lemma (in measure_space) integrable_cong:
  "(\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> integrable M f \<longleftrightarrow> integrable M g"
  by (simp cong: positive_integral_cong measurable_cong add: integrable_def)

lemma (in measure_space) integral_eq_positive_integral:
  assumes "\<And>x. 0 \<le> f x"
  shows "integral\<^isup>L M f = real (\<integral>\<^isup>+ x. Real (f x) \<partial>M)"
proof -
  have "\<And>x. Real (- f x) = 0" using assms by simp
  thus ?thesis by (simp del: Real_eq_0 add: lebesgue_integral_def)
qed

lemma (in measure_space) integral_vimage:
  assumes T: "sigma_algebra M'" "T \<in> measurable M M'"
    and \<nu>: "\<And>A. A \<in> sets M' \<Longrightarrow> measure M' A = \<mu> (T -` A \<inter> space M)"
  assumes f: "integrable M' f"
  shows "integrable M (\<lambda>x. f (T x))" (is ?P)
    and "integral\<^isup>L M' f = (\<integral>x. f (T x) \<partial>M)" (is ?I)
proof -
  interpret T: measure_space M' using \<nu> by (rule measure_space_vimage[OF T])
  from measurable_comp[OF T(2), of f borel]
  have borel: "(\<lambda>x. Real (f x)) \<in> borel_measurable M'" "(\<lambda>x. Real (- f x)) \<in> borel_measurable M'"
    and "(\<lambda>x. f (T x)) \<in> borel_measurable M"
    using f unfolding integrable_def by (auto simp: comp_def)
  then show ?P ?I
    using f unfolding lebesgue_integral_def integrable_def
    by (auto simp: borel[THEN positive_integral_vimage[OF T], OF \<nu>])
qed

lemma (in measure_space) integral_minus[intro, simp]:
  assumes "integrable M f"
  shows "integrable M (\<lambda>x. - f x)" "(\<integral>x. - f x \<partial>M) = - integral\<^isup>L M f"
  using assms by (auto simp: integrable_def lebesgue_integral_def)

lemma (in measure_space) integral_of_positive_diff:
  assumes integrable: "integrable M u" "integrable M v"
  and f_def: "\<And>x. f x = u x - v x" and pos: "\<And>x. 0 \<le> u x" "\<And>x. 0 \<le> v x"
  shows "integrable M f" and "integral\<^isup>L M f = integral\<^isup>L M u - integral\<^isup>L M v"
proof -
  let "?f x" = "Real (f x)"
  let "?mf x" = "Real (- f x)"
  let "?u x" = "Real (u x)"
  let "?v x" = "Real (v x)"

  from borel_measurable_diff[of u v] integrable
  have f_borel: "?f \<in> borel_measurable M" and
    mf_borel: "?mf \<in> borel_measurable M" and
    v_borel: "?v \<in> borel_measurable M" and
    u_borel: "?u \<in> borel_measurable M" and
    "f \<in> borel_measurable M"
    by (auto simp: f_def[symmetric] integrable_def)

  have "(\<integral>\<^isup>+ x. Real (u x - v x) \<partial>M) \<le> integral\<^isup>P M ?u"
    using pos by (auto intro!: positive_integral_mono)
  moreover have "(\<integral>\<^isup>+ x. Real (v x - u x) \<partial>M) \<le> integral\<^isup>P M ?v"
    using pos by (auto intro!: positive_integral_mono)
  ultimately show f: "integrable M f"
    using `integrable M u` `integrable M v` `f \<in> borel_measurable M`
    by (auto simp: integrable_def f_def)
  hence mf: "integrable M (\<lambda>x. - f x)" ..

  have *: "\<And>x. Real (- v x) = 0" "\<And>x. Real (- u x) = 0"
    using pos by auto

  have "\<And>x. ?u x + ?mf x = ?v x + ?f x"
    unfolding f_def using pos by simp
  hence "(\<integral>\<^isup>+ x. ?u x + ?mf x \<partial>M) = (\<integral>\<^isup>+ x. ?v x + ?f x \<partial>M)" by simp
  hence "real (integral\<^isup>P M ?u + integral\<^isup>P M ?mf) =
      real (integral\<^isup>P M ?v + integral\<^isup>P M ?f)"
    using positive_integral_add[OF u_borel mf_borel]
    using positive_integral_add[OF v_borel f_borel]
    by auto
  then show "integral\<^isup>L M f = integral\<^isup>L M u - integral\<^isup>L M v"
    using f mf `integrable M u` `integrable M v`
    unfolding lebesgue_integral_def integrable_def *
    by (cases "integral\<^isup>P M ?f", cases "integral\<^isup>P M ?mf", cases "integral\<^isup>P M ?v", cases "integral\<^isup>P M ?u")
       (auto simp add: field_simps)
qed

lemma (in measure_space) integral_linear:
  assumes "integrable M f" "integrable M g" and "0 \<le> a"
  shows "integrable M (\<lambda>t. a * f t + g t)"
  and "(\<integral> t. a * f t + g t \<partial>M) = a * integral\<^isup>L M f + integral\<^isup>L M g"
proof -
  let ?PI = "integral\<^isup>P M"
  let "?f x" = "Real (f x)"
  let "?g x" = "Real (g x)"
  let "?mf x" = "Real (- f x)"
  let "?mg x" = "Real (- g x)"
  let "?p t" = "max 0 (a * f t) + max 0 (g t)"
  let "?n t" = "max 0 (- (a * f t)) + max 0 (- g t)"

  have pos: "?f \<in> borel_measurable M" "?g \<in> borel_measurable M"
    and neg: "?mf \<in> borel_measurable M" "?mg \<in> borel_measurable M"
    and p: "?p \<in> borel_measurable M"
    and n: "?n \<in> borel_measurable M"
    using assms by (simp_all add: integrable_def)

  have *: "\<And>x. Real (?p x) = Real a * ?f x + ?g x"
          "\<And>x. Real (?n x) = Real a * ?mf x + ?mg x"
          "\<And>x. Real (- ?p x) = 0"
          "\<And>x. Real (- ?n x) = 0"
    using `0 \<le> a` by (auto simp: max_def min_def zero_le_mult_iff mult_le_0_iff add_nonpos_nonpos)

  note linear =
    positive_integral_linear[OF pos]
    positive_integral_linear[OF neg]

  have "integrable M ?p" "integrable M ?n"
      "\<And>t. a * f t + g t = ?p t - ?n t" "\<And>t. 0 \<le> ?p t" "\<And>t. 0 \<le> ?n t"
    using assms p n unfolding integrable_def * linear by auto
  note diff = integral_of_positive_diff[OF this]

  show "integrable M (\<lambda>t. a * f t + g t)" by (rule diff)

  from assms show "(\<integral> t. a * f t + g t \<partial>M) = a * integral\<^isup>L M f + integral\<^isup>L M g"
    unfolding diff(2) unfolding lebesgue_integral_def * linear integrable_def
    by (cases "?PI ?f", cases "?PI ?mf", cases "?PI ?g", cases "?PI ?mg")
       (auto simp add: field_simps zero_le_mult_iff)
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
  have "AE x. Real (f x) \<le> Real (g x)"
    using mono by auto
  moreover have "AE x. Real (- g x) \<le> Real (- f x)"
    using mono by auto
  ultimately show ?thesis using fg
    by (auto simp: lebesgue_integral_def integrable_def diff_minus
             intro!: add_mono real_of_pextreal_mono positive_integral_mono_AE)
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
  assumes "a \<in> sets M" and "\<mu> a \<noteq> \<omega>"
  shows "integral\<^isup>L M (indicator a) = real (\<mu> a)" (is ?int)
  and "integrable M (indicator a)" (is ?able)
proof -
  have *:
    "\<And>A x. Real (indicator A x) = indicator A x"
    "\<And>A x. Real (- indicator A x) = 0" unfolding indicator_def by auto
  show ?int ?able
    using assms unfolding lebesgue_integral_def integrable_def
    by (auto simp: * positive_integral_indicator borel_measurable_indicator)
qed

lemma (in measure_space) integral_cmul_indicator:
  assumes "A \<in> sets M" and "c \<noteq> 0 \<Longrightarrow> \<mu> A \<noteq> \<omega>"
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
  have *:
    "\<And>x. Real \<bar>f x\<bar> = Real (f x) + Real (- f x)"
    "\<And>x. Real (- \<bar>f x\<bar>) = 0" by auto
  have abs: "(\<lambda>x. \<bar>f x\<bar>) \<in> borel_measurable M" and
    f: "(\<lambda>x. Real (f x)) \<in> borel_measurable M"
        "(\<lambda>x. Real (- f x)) \<in> borel_measurable M"
    using assms unfolding integrable_def by auto
  from abs assms show ?thesis unfolding integrable_def *
    using positive_integral_linear[OF f, of 1] by simp
qed

lemma (in measure_space) integral_subalgebra:
  assumes borel: "f \<in> borel_measurable N"
  and N: "sets N \<subseteq> sets M" "space N = space M" "\<And>A. A \<in> sets N \<Longrightarrow> measure N A = \<mu> A" and sa: "sigma_algebra N"
  shows "integrable N f \<longleftrightarrow> integrable M f" (is ?P)
    and "integral\<^isup>L N f = integral\<^isup>L M f" (is ?I)
proof -
  interpret N: measure_space N using measure_space_subalgebra[OF sa N] .
  have "(\<lambda>x. Real (f x)) \<in> borel_measurable N" "(\<lambda>x. Real (- f x)) \<in> borel_measurable N"
    using borel by auto
  note * = this[THEN positive_integral_subalgebra[OF _ N sa]]
  have "f \<in> borel_measurable M \<longleftrightarrow> f \<in> borel_measurable N"
    using assms unfolding measurable_def by auto
  then show ?P ?I by (auto simp: * integrable_def lebesgue_integral_def)
qed

lemma (in measure_space) integrable_bound:
  assumes "integrable M f"
  and f: "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> f x"
    "\<And>x. x \<in> space M \<Longrightarrow> \<bar>g x\<bar> \<le> f x"
  assumes borel: "g \<in> borel_measurable M"
  shows "integrable M g"
proof -
  have "(\<integral>\<^isup>+ x. Real (g x) \<partial>M) \<le> (\<integral>\<^isup>+ x. Real \<bar>g x\<bar> \<partial>M)"
    by (auto intro!: positive_integral_mono)
  also have "\<dots> \<le> (\<integral>\<^isup>+ x. Real (f x) \<partial>M)"
    using f by (auto intro!: positive_integral_mono)
  also have "\<dots> < \<omega>"
    using `integrable M f` unfolding integrable_def by (auto simp: pextreal_less_\<omega>)
  finally have pos: "(\<integral>\<^isup>+ x. Real (g x) \<partial>M) < \<omega>" .

  have "(\<integral>\<^isup>+ x. Real (- g x) \<partial>M) \<le> (\<integral>\<^isup>+ x. Real (\<bar>g x\<bar>) \<partial>M)"
    by (auto intro!: positive_integral_mono)
  also have "\<dots> \<le> (\<integral>\<^isup>+ x. Real (f x) \<partial>M)"
    using f by (auto intro!: positive_integral_mono)
  also have "\<dots> < \<omega>"
    using `integrable M f` unfolding integrable_def by (auto simp: pextreal_less_\<omega>)
  finally have neg: "(\<integral>\<^isup>+ x. Real (- g x) \<partial>M) < \<omega>" .

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

  hence [simp]: "\<And>i x. Real (- f i x) = 0" "\<And>x. Real (- u x) = 0"
    using pos by auto

  have SUP_F: "\<And>x. (SUP n. Real (f n x)) = Real (u x)"
    using mono pos pos_u lim by (rule SUP_eq_LIMSEQ[THEN iffD2])

  have borel_f: "\<And>i. (\<lambda>x. Real (f i x)) \<in> borel_measurable M"
    using i unfolding integrable_def by auto
  hence "(\<lambda>x. SUP i. Real (f i x)) \<in> borel_measurable M"
    by auto
  hence borel_u: "u \<in> borel_measurable M"
    using pos_u by (auto simp: borel_measurable_Real_eq SUP_F)

  have integral_eq: "\<And>n. (\<integral>\<^isup>+ x. Real (f n x) \<partial>M) = Real (integral\<^isup>L M (f n))"
    using i unfolding lebesgue_integral_def integrable_def by (auto simp: Real_real)

  have pos_integral: "\<And>n. 0 \<le> integral\<^isup>L M (f n)"
    using pos i by (auto simp: integral_positive)
  hence "0 \<le> x"
    using LIMSEQ_le_const[OF ilim, of 0] by auto

  have "(\<lambda>i. (\<integral>\<^isup>+ x. Real (f i x) \<partial>M)) \<up> (\<integral>\<^isup>+ x. Real (u x) \<partial>M)"
  proof (rule positive_integral_isoton)
    from SUP_F mono pos
    show "(\<lambda>i x. Real (f i x)) \<up> (\<lambda>x. Real (u x))"
      unfolding isoton_fun_expand by (auto simp: isoton_def mono_def)
  qed (rule borel_f)
  hence pI: "(\<integral>\<^isup>+ x. Real (u x) \<partial>M) = (SUP n. (\<integral>\<^isup>+ x. Real (f n x) \<partial>M))"
    unfolding isoton_def by simp
  also have "\<dots> = Real x" unfolding integral_eq
  proof (rule SUP_eq_LIMSEQ[THEN iffD2])
    show "mono (\<lambda>n. integral\<^isup>L M (f n))"
      using mono i by (auto simp: mono_def intro!: integral_mono)
    show "\<And>n. 0 \<le> integral\<^isup>L M (f n)" using pos_integral .
    show "0 \<le> x" using `0 \<le> x` .
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
    using lim by (auto intro!: LIMSEQ_diff)
  have 5: "(\<lambda>i. (\<integral>x. f i x - f 0 x \<partial>M)) ----> x - integral\<^isup>L M (f 0)"
    using f ilim by (auto intro!: LIMSEQ_diff simp: integral_diff)
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
  have *: "\<And>x. Real (- \<bar>f x\<bar>) = 0" by auto
  have "integrable M (\<lambda>x. \<bar>f x\<bar>)" using assms by (rule integrable_abs)
  hence "(\<lambda>x. Real (\<bar>f x\<bar>)) \<in> borel_measurable M"
    "(\<integral>\<^isup>+ x. Real \<bar>f x\<bar> \<partial>M) \<noteq> \<omega>" unfolding integrable_def by auto
  from positive_integral_0_iff[OF this(1)] this(2)
  show ?thesis unfolding lebesgue_integral_def *
    by (simp add: real_of_pextreal_eq_0)
qed

lemma (in measure_space) positive_integral_omega:
  assumes "f \<in> borel_measurable M"
  and "integral\<^isup>P M f \<noteq> \<omega>"
  shows "\<mu> (f -` {\<omega>} \<inter> space M) = 0"
proof -
  have "\<omega> * \<mu> (f -` {\<omega>} \<inter> space M) = (\<integral>\<^isup>+ x. \<omega> * indicator (f -` {\<omega>} \<inter> space M) x \<partial>M)"
    using positive_integral_cmult_indicator[OF borel_measurable_vimage, OF assms(1), of \<omega> \<omega>] by simp
  also have "\<dots> \<le> integral\<^isup>P M f"
    by (auto intro!: positive_integral_mono simp: indicator_def)
  finally show ?thesis
    using assms(2) by (cases ?thesis) auto
qed

lemma (in measure_space) positive_integral_omega_AE:
  assumes "f \<in> borel_measurable M" "integral\<^isup>P M f \<noteq> \<omega>" shows "AE x. f x \<noteq> \<omega>"
proof (rule AE_I)
  show "\<mu> (f -` {\<omega>} \<inter> space M) = 0"
    by (rule positive_integral_omega[OF assms])
  show "f -` {\<omega>} \<inter> space M \<in> sets M"
    using assms by (auto intro: borel_measurable_vimage)
qed auto

lemma (in measure_space) simple_integral_omega:
  assumes "simple_function M f"
  and "integral\<^isup>S M f \<noteq> \<omega>"
  shows "\<mu> (f -` {\<omega>} \<inter> space M) = 0"
proof (rule positive_integral_omega)
  show "f \<in> borel_measurable M" using assms by (auto intro: borel_measurable_simple_function)
  show "integral\<^isup>P M f \<noteq> \<omega>"
    using assms by (simp add: positive_integral_eq_simple_integral)
qed

lemma (in measure_space) integral_real:
  fixes f :: "'a \<Rightarrow> pextreal"
  assumes [simp]: "AE x. f x \<noteq> \<omega>"
  shows "(\<integral>x. real (f x) \<partial>M) = real (integral\<^isup>P M f)" (is ?plus)
    and "(\<integral>x. - real (f x) \<partial>M) = - real (integral\<^isup>P M f)" (is ?minus)
proof -
  have "(\<integral>\<^isup>+ x. Real (real (f x)) \<partial>M) = integral\<^isup>P M f"
    by (auto intro!: positive_integral_cong_AE simp: Real_real)
  moreover
  have "(\<integral>\<^isup>+ x. Real (- real (f x)) \<partial>M) = (\<integral>\<^isup>+ x. 0 \<partial>M)"
    by (intro positive_integral_cong) auto
  ultimately show ?plus ?minus
    by (auto simp: lebesgue_integral_def integrable_def)
qed

lemma (in measure_space) integral_dominated_convergence:
  assumes u: "\<And>i. integrable M (u i)" and bound: "\<And>x j. x\<in>space M \<Longrightarrow> \<bar>u j x\<bar> \<le> w x"
  and w: "integrable M w"
  and u': "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. u i x) ----> u' x"
  shows "integrable M u'"
  and "(\<lambda>i. (\<integral>x. \<bar>u i x - u' x\<bar> \<partial>M)) ----> 0" (is "?lim_diff")
  and "(\<lambda>i. integral\<^isup>L M (u i)) ----> integral\<^isup>L M u'" (is ?lim)
proof -
  { fix x j assume x: "x \<in> space M"
    from u'[OF x] have "(\<lambda>i. \<bar>u i x\<bar>) ----> \<bar>u' x\<bar>" by (rule LIMSEQ_imp_rabs)
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

  let "?diff n x" = "2 * w x - \<bar>u n x - u' x\<bar>"
  have diff: "\<And>n. integrable M (\<lambda>x. \<bar>u n x - u' x\<bar>)"
    using w u `integrable M u'`
    by (auto intro!: integral_add integral_diff integral_cmult integrable_abs)

  { fix j x assume x: "x \<in> space M"
    have "\<bar>u j x - u' x\<bar> \<le> \<bar>u j x\<bar> + \<bar>u' x\<bar>" by auto
    also have "\<dots> \<le> w x + w x"
      by (rule add_mono[OF bound[OF x] u'_bound[OF x]])
    finally have "\<bar>u j x - u' x\<bar> \<le> 2 * w x" by simp }
  note diff_less_2w = this

  have PI_diff: "\<And>m n. (\<integral>\<^isup>+ x. Real (?diff (m + n) x) \<partial>M) =
    (\<integral>\<^isup>+ x. Real (2 * w x) \<partial>M) - (\<integral>\<^isup>+ x. Real \<bar>u (m + n) x - u' x\<bar> \<partial>M)"
    using diff w diff_less_2w w_pos
    by (subst positive_integral_diff[symmetric])
       (auto simp: integrable_def intro!: positive_integral_cong)

  have "integrable M (\<lambda>x. 2 * w x)"
    using w by (auto intro: integral_cmult)
  hence I2w_fin: "(\<integral>\<^isup>+ x. Real (2 * w x) \<partial>M) \<noteq> \<omega>" and
    borel_2w: "(\<lambda>x. Real (2 * w x)) \<in> borel_measurable M"
    unfolding integrable_def by auto

  have "(INF n. SUP m. (\<integral>\<^isup>+ x. Real \<bar>u (m + n) x - u' x\<bar> \<partial>M)) = 0" (is "?lim_SUP = 0")
  proof cases
    assume eq_0: "(\<integral>\<^isup>+ x. Real (2 * w x) \<partial>M) = 0"
    have "\<And>i. (\<integral>\<^isup>+ x. Real \<bar>u i x - u' x\<bar> \<partial>M) \<le> (\<integral>\<^isup>+ x. Real (2 * w x) \<partial>M)"
    proof (rule positive_integral_mono)
      fix i x assume "x \<in> space M" from diff_less_2w[OF this, of i]
      show "Real \<bar>u i x - u' x\<bar> \<le> Real (2 * w x)" by auto
    qed
    hence "\<And>i. (\<integral>\<^isup>+ x. Real \<bar>u i x - u' x\<bar> \<partial>M) = 0" using eq_0 by auto
    thus ?thesis by simp
  next
    assume neq_0: "(\<integral>\<^isup>+ x. Real (2 * w x) \<partial>M) \<noteq> 0"
    have "(\<integral>\<^isup>+ x. Real (2 * w x) \<partial>M) = (\<integral>\<^isup>+ x. (SUP n. INF m. Real (?diff (m + n) x)) \<partial>M)"
    proof (rule positive_integral_cong, subst add_commute)
      fix x assume x: "x \<in> space M"
      show "Real (2 * w x) = (SUP n. INF m. Real (?diff (n + m) x))"
      proof (rule LIMSEQ_imp_lim_INF[symmetric])
        fix j show "0 \<le> ?diff j x" using diff_less_2w[OF x, of j] by simp
      next
        have "(\<lambda>i. ?diff i x) ----> 2 * w x - \<bar>u' x - u' x\<bar>"
          using u'[OF x] by (safe intro!: LIMSEQ_diff LIMSEQ_const LIMSEQ_imp_rabs)
        thus "(\<lambda>i. ?diff i x) ----> 2 * w x" by simp
      qed
    qed
    also have "\<dots> \<le> (SUP n. INF m. (\<integral>\<^isup>+ x. Real (?diff (m + n) x) \<partial>M))"
      using u'_borel w u unfolding integrable_def
      by (auto intro!: positive_integral_lim_INF)
    also have "\<dots> = (\<integral>\<^isup>+ x. Real (2 * w x) \<partial>M) -
        (INF n. SUP m. \<integral>\<^isup>+ x. Real \<bar>u (m + n) x - u' x\<bar> \<partial>M)"
      unfolding PI_diff pextreal_INF_minus[OF I2w_fin] pextreal_SUP_minus ..
    finally show ?thesis using neq_0 I2w_fin by (rule pextreal_le_minus_imp_0)
  qed

  have [simp]: "\<And>n m x. Real (- \<bar>u (m + n) x - u' x\<bar>) = 0" by auto

  have [simp]: "\<And>n m. (\<integral>\<^isup>+ x. Real \<bar>u (m + n) x - u' x\<bar> \<partial>M) =
    Real ((\<integral>x. \<bar>u (n + m) x - u' x\<bar> \<partial>M))"
    using diff by (subst add_commute) (simp add: lebesgue_integral_def integrable_def Real_real)

  have "(SUP n. INF m. (\<integral>\<^isup>+ x. Real \<bar>u (m + n) x - u' x\<bar> \<partial>M)) \<le> ?lim_SUP"
    (is "?lim_INF \<le> _") by (subst (1 2) add_commute) (rule lim_INF_le_lim_SUP)
  hence "?lim_INF = Real 0" "?lim_SUP = Real 0" using `?lim_SUP = 0` by auto
  thus ?lim_diff using diff by (auto intro!: integral_positive lim_INF_eq_lim_SUP)

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

  let "?w y" = "if y \<in> space M then w y else 0"

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
    let "?F n y" = "(\<Sum>i = 0..<n. \<bar>f i y\<bar>)"
    let "?w' n y" = "if y \<in> space M then ?F n y else 0"
    have "\<And>n. integrable M (?F n)"
      using borel by (auto intro!: integral_setsum integrable_abs)
    thus "\<And>n. integrable M (?w' n)" by (simp cong: integrable_cong)
    show "mono ?w'"
      by (auto simp: mono_def le_fun_def intro!: setsum_mono2)
    { fix x show "(\<lambda>n. ?w' n x) ----> ?w x"
        using w by (cases "x \<in> space M") (simp_all add: LIMSEQ_const sums_def) }
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
  and fin: "\<And>x. x \<noteq> 0 \<Longrightarrow> \<mu> (f -` {x} \<inter> space M) \<noteq> \<omega>"
  and abs_summable: "summable (\<lambda>r. \<bar>enum r * real (\<mu> (f -` {enum r} \<inter> space M))\<bar>)"
  shows "integrable M f"
  and "(\<lambda>r. enum r * real (\<mu> (f -` {enum r} \<inter> space M))) sums integral\<^isup>L M f" (is ?sums)
proof -
  let "?A r" = "f -` {enum r} \<inter> space M"
  let "?F r x" = "enum r * indicator (?A r) x"
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
      by (simp add: abs_mult_pos real_pextreal_pos) }
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
  and fin: "\<And>x. x \<noteq> 0 \<Longrightarrow> \<mu> (f -` {x} \<inter> space M) \<noteq> \<omega>"
  shows "integrable M f"
  and "(\<integral>x. f x \<partial>M) =
    (\<Sum> r \<in> f`space M. r * real (\<mu> (f -` {r} \<inter> space M)))" (is "?integral")
proof -
  let "?A r" = "f -` {r} \<inter> space M"
  let "?S x" = "\<Sum>r\<in>f`space M. r * indicator (?A r) x"

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
  "integral\<^isup>P M f = (\<Sum>x \<in> space M. f x * \<mu> {x})"
proof -
  have *: "integral\<^isup>P M f = (\<integral>\<^isup>+ x. (\<Sum>y\<in>space M. f y * indicator {y} x) \<partial>M)"
    by (auto intro!: positive_integral_cong simp add: indicator_def if_distrib setsum_cases[OF finite_space])
  show ?thesis unfolding * using borel_measurable_finite[of f]
    by (simp add: positive_integral_setsum positive_integral_cmult_indicator)
qed

lemma (in finite_measure_space) integral_finite_singleton:
  shows "integrable M f"
  and "integral\<^isup>L M f = (\<Sum>x \<in> space M. f x * real (\<mu> {x}))" (is ?I)
proof -
  have [simp]:
    "(\<integral>\<^isup>+ x. Real (f x) \<partial>M) = (\<Sum>x \<in> space M. Real (f x) * \<mu> {x})"
    "(\<integral>\<^isup>+ x. Real (- f x) \<partial>M) = (\<Sum>x \<in> space M. Real (- f x) * \<mu> {x})"
    unfolding positive_integral_finite_eq_setsum by auto
  show "integrable M f" using finite_space finite_measure
    by (simp add: setsum_\<omega> integrable_def)
  show ?I using finite_measure
    apply (simp add: lebesgue_integral_def real_of_pextreal_setsum[symmetric]
      real_of_pextreal_mult[symmetric] setsum_subtractf[symmetric])
    by (rule setsum_cong) (simp_all split: split_if)
qed

end
