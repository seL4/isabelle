(* Author: Armin Heller, Johannes Hoelzl, TU Muenchen *)

header {*Lebesgue Integration*}

theory Lebesgue_Integration
imports Measure Borel
begin

section "@{text \<mu>}-null sets"

abbreviation (in measure_space) "null_sets \<equiv> {N\<in>sets M. \<mu> N = 0}"

lemma sums_If_finite:
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
  "(\<lambda>r. if r = i then f r else 0) sums f i"
  using sums_If_finite[of "\<lambda>r. r = i" f] by simp

section "Simple function"

text {*

Our simple functions are not restricted to positive real numbers. Instead
they are just functions with a finite range and are measurable when singleton
sets are measurable.

*}

definition (in sigma_algebra) "simple_function g \<longleftrightarrow>
    finite (g ` space M) \<and>
    (\<forall>x \<in> g ` space M. g -` {x} \<inter> space M \<in> sets M)"

lemma (in sigma_algebra) simple_functionD:
  assumes "simple_function g"
  shows "finite (g ` space M)"
  "x \<in> g ` space M \<Longrightarrow> g -` {x} \<inter> space M \<in> sets M"
  using assms unfolding simple_function_def by auto

lemma (in sigma_algebra) simple_function_indicator_representation:
  fixes f ::"'a \<Rightarrow> pinfreal"
  assumes f: "simple_function f" and x: "x \<in> space M"
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
  "simple_function (\<lambda>x. h x * indicator (- space M) x::pinfreal)" (is "simple_function ?h")
proof -
  have "?h ` space M \<subseteq> {0}" unfolding indicator_def by auto
  hence [simp, intro]: "finite (?h ` space M)" by (auto intro: finite_subset)
  have "?h -` {0} \<inter> space M = space M" by auto
  thus ?thesis unfolding simple_function_def by auto
qed

lemma (in sigma_algebra) simple_function_cong:
  assumes "\<And>t. t \<in> space M \<Longrightarrow> f t = g t"
  shows "simple_function f \<longleftrightarrow> simple_function g"
proof -
  have "f ` space M = g ` space M"
    "\<And>x. f -` {x} \<inter> space M = g -` {x} \<inter> space M"
    using assms by (auto intro!: image_eqI)
  thus ?thesis unfolding simple_function_def using assms by simp
qed

lemma (in sigma_algebra) borel_measurable_simple_function:
  assumes "simple_function f"
  shows "f \<in> borel_measurable M"
proof (rule borel_measurableI)
  fix S
  let ?I = "f ` (f -` S \<inter> space M)"
  have *: "(\<Union>x\<in>?I. f -` {x} \<inter> space M) = f -` S \<inter> space M" (is "?U = _") by auto
  have "finite ?I"
    using assms unfolding simple_function_def by (auto intro: finite_subset)
  hence "?U \<in> sets M"
    apply (rule finite_UN)
    using assms unfolding simple_function_def by auto
  thus "f -` S \<inter> space M \<in> sets M" unfolding * .
qed

lemma (in sigma_algebra) simple_function_borel_measurable:
  fixes f :: "'a \<Rightarrow> 'x::t2_space"
  assumes "f \<in> borel_measurable M" and "finite (f ` space M)"
  shows "simple_function f"
  using assms unfolding simple_function_def
  by (auto intro: borel_measurable_vimage)

lemma (in sigma_algebra) simple_function_const[intro, simp]:
  "simple_function (\<lambda>x. c)"
  by (auto intro: finite_subset simp: simple_function_def)

lemma (in sigma_algebra) simple_function_compose[intro, simp]:
  assumes "simple_function f"
  shows "simple_function (g \<circ> f)"
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
  shows "simple_function (indicator A)"
proof -
  have "indicator A ` space M \<subseteq> {0, 1}" (is "?S \<subseteq> _")
    by (auto simp: indicator_def)
  hence "finite ?S" by (rule finite_subset) simp
  moreover have "- A \<inter> space M = space M - A" by auto
  ultimately show ?thesis unfolding simple_function_def
    using assms by (auto simp: indicator_def_raw)
qed

lemma (in sigma_algebra) simple_function_Pair[intro, simp]:
  assumes "simple_function f"
  assumes "simple_function g"
  shows "simple_function (\<lambda>x. (f x, g x))" (is "simple_function ?p")
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
  assumes "simple_function f"
  shows "simple_function (\<lambda>x. g (f x))"
  using simple_function_compose[OF assms, of g]
  by (simp add: comp_def)

lemma (in sigma_algebra) simple_function_compose2:
  assumes "simple_function f" and "simple_function g"
  shows "simple_function (\<lambda>x. h (f x) (g x))"
proof -
  have "simple_function ((\<lambda>(x, y). h x y) \<circ> (\<lambda>x. (f x, g x)))"
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
  assumes "\<And>i. i \<in> P \<Longrightarrow> simple_function (f i)"
  shows "simple_function (\<lambda>x. \<Sum>i\<in>P. f i x)"
proof cases
  assume "finite P" from this assms show ?thesis by induct auto
qed auto

lemma (in sigma_algebra) simple_function_le_measurable:
  assumes "simple_function f" "simple_function g"
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
  fixes u :: "'a \<Rightarrow> pinfreal"
  assumes u: "u \<in> borel_measurable M"
  shows "\<exists>f. (\<forall>i. simple_function (f i) \<and> (\<forall>x\<in>space M. f i x \<noteq> \<omega>)) \<and> f \<up> u"
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

  let "?g j x" = "of_nat (f x j) / 2^j :: pinfreal"
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
    proof (rule pinfreal_SUPI)
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
      fix y :: pinfreal assume *: "\<And>j. j \<in> UNIV \<Longrightarrow> of_nat (f t j) / 2 ^ j \<le> y"
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
  fixes u :: "'a \<Rightarrow> pinfreal"
  assumes "u \<in> borel_measurable M"
  obtains (x) f where "f \<up> u" "\<And>i. simple_function (f i)" "\<And>i. \<omega>\<notin>f i`space M"
proof -
  from borel_measurable_implies_simple_function_sequence[OF assms]
  obtain f where x: "\<And>i. simple_function (f i)" "f \<up> u"
    and fin: "\<And>i. \<And>x. x\<in>space M \<Longrightarrow> f i x \<noteq> \<omega>" by auto
  { fix i from fin[of _ i] have "\<omega> \<notin> f i`space M" by fastsimp }
  with x show thesis by (auto intro!: that[of f])
qed

lemma (in sigma_algebra) simple_function_eq_borel_measurable:
  fixes f :: "'a \<Rightarrow> pinfreal"
  shows "simple_function f \<longleftrightarrow>
    finite (f`space M) \<and> f \<in> borel_measurable M"
  using simple_function_borel_measurable[of f]
    borel_measurable_simple_function[of f]
  by (fastsimp simp: simple_function_def)

lemma (in measure_space) simple_function_restricted:
  fixes f :: "'a \<Rightarrow> pinfreal" assumes "A \<in> sets M"
  shows "sigma_algebra.simple_function (restricted_space A) f \<longleftrightarrow> simple_function (\<lambda>x. f x * indicator A x)"
    (is "sigma_algebra.simple_function ?R f \<longleftrightarrow> simple_function ?f")
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
      assume "indicator A x \<noteq> (0::pinfreal)"
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
  assumes "sigma_algebra.simple_function (M\<lparr>sets:=N\<rparr>) f"
  and N_subalgebra: "N \<subseteq> sets M" "sigma_algebra (M\<lparr>sets:=N\<rparr>)"
  shows "simple_function f"
  using assms
  unfolding simple_function_def
  unfolding sigma_algebra.simple_function_def[OF N_subalgebra(2)]
  by auto

section "Simple integral"

definition (in measure_space)
  "simple_integral f = (\<Sum>x \<in> f ` space M. x * \<mu> (f -` {x} \<inter> space M))"

lemma (in measure_space) simple_integral_cong:
  assumes "\<And>t. t \<in> space M \<Longrightarrow> f t = g t"
  shows "simple_integral f = simple_integral g"
proof -
  have "f ` space M = g ` space M"
    "\<And>x. f -` {x} \<inter> space M = g -` {x} \<inter> space M"
    using assms by (auto intro!: image_eqI)
  thus ?thesis unfolding simple_integral_def by simp
qed

lemma (in measure_space) simple_integral_const[simp]:
  "simple_integral (\<lambda>x. c) = c * \<mu> (space M)"
proof (cases "space M = {}")
  case True thus ?thesis unfolding simple_integral_def by simp
next
  case False hence "(\<lambda>x. c) ` space M = {c}" by auto
  thus ?thesis unfolding simple_integral_def by simp
qed

lemma (in measure_space) simple_function_partition:
  assumes "simple_function f" and "simple_function g"
  shows "simple_integral f = (\<Sum>A\<in>(\<lambda>x. f -` {f x} \<inter> g -` {g x} \<inter> space M) ` space M. the_elem (f`A) * \<mu> A)"
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
      by (rule finite_subset) (auto intro: finite_SigmaI finite_imageI) }
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
  hence "simple_integral f = (\<Sum>(x,A)\<in>?SIGMA. x * \<mu> A)"
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
  assumes "simple_function f" and "simple_function g"
  shows "simple_integral (\<lambda>x. f x + g x) = simple_integral f + simple_integral g"
proof -
  { fix x let ?S = "g -` {g x} \<inter> f -` {f x} \<inter> space M"
    assume "x \<in> space M"
    hence "(\<lambda>a. f a + g a) ` ?S = {f x + g x}" "f ` ?S = {f x}" "g ` ?S = {g x}"
        "(\<lambda>x. (f x, g x)) -` {(f x, g x)} \<inter> space M = ?S"
      by auto }
  thus ?thesis
    unfolding
      simple_function_partition[OF simple_function_add[OF assms] simple_function_Pair[OF assms]]
      simple_function_partition[OF `simple_function f` `simple_function g`]
      simple_function_partition[OF `simple_function g` `simple_function f`]
    apply (subst (3) Int_commute)
    by (auto simp add: field_simps setsum_addf[symmetric] intro!: setsum_cong)
qed

lemma (in measure_space) simple_integral_setsum[simp]:
  assumes "\<And>i. i \<in> P \<Longrightarrow> simple_function (f i)"
  shows "simple_integral (\<lambda>x. \<Sum>i\<in>P. f i x) = (\<Sum>i\<in>P. simple_integral (f i))"
proof cases
  assume "finite P"
  from this assms show ?thesis
    by induct (auto simp: simple_function_setsum simple_integral_add)
qed auto

lemma (in measure_space) simple_integral_mult[simp]:
  assumes "simple_function f"
  shows "simple_integral (\<lambda>x. c * f x) = c * simple_integral f"
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

lemma (in measure_space) simple_integral_mono:
  assumes "simple_function f" and "simple_function g"
  and mono: "\<And> x. x \<in> space M \<Longrightarrow> f x \<le> g x"
  shows "simple_integral f \<le> simple_integral g"
  unfolding
    simple_function_partition[OF `simple_function f` `simple_function g`]
    simple_function_partition[OF `simple_function g` `simple_function f`]
  apply (subst Int_commute)
proof (safe intro!: setsum_mono)
  fix x let ?S = "g -` {g x} \<inter> f -` {f x} \<inter> space M"
  assume "x \<in> space M"
  hence "f ` ?S = {f x}" "g ` ?S = {g x}" by auto
  thus "the_elem (f`?S) * \<mu> ?S \<le> the_elem (g`?S) * \<mu> ?S"
    using mono[OF `x \<in> space M`] by (auto intro!: mult_right_mono)
qed

lemma (in measure_space) simple_integral_indicator:
  assumes "A \<in> sets M"
  assumes "simple_function f"
  shows "simple_integral (\<lambda>x. f x * indicator A x) =
    (\<Sum>x \<in> f ` space M. x * \<mu> (f -` {x} \<inter> space M \<inter> A))"
proof cases
  assume "A = space M"
  moreover hence "simple_integral (\<lambda>x. f x * indicator A x) = simple_integral f"
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
  have *: "simple_integral (\<lambda>x. f x * indicator A x) =
    (\<Sum>x \<in> f ` space M \<union> {0}. x * \<mu> (f -` {x} \<inter> space M \<inter> A))"
    unfolding simple_integral_def I
  proof (rule setsum_mono_zero_cong_left)
    show "finite (f ` space M \<union> {0})"
      using assms(2) unfolding simple_function_def by auto
    show "f ` A \<union> {0} \<subseteq> f`space M \<union> {0}"
      using sets_into_space[OF assms(1)] by auto
    have "\<And>x. f x \<notin> f ` A \<Longrightarrow> f -` {f x} \<inter> space M \<inter> A = {}" by (auto simp: image_iff)
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
  shows "simple_integral (indicator A) = \<mu> A"
proof cases
  assume "space M = {}" hence "A = {}" using sets_into_space[OF assms] by auto
  thus ?thesis unfolding simple_integral_def using `space M = {}` by auto
next
  assume "space M \<noteq> {}" hence "(\<lambda>x. 1) ` space M = {1::pinfreal}" by auto
  thus ?thesis
    using simple_integral_indicator[OF assms simple_function_const[of 1]]
    using sets_into_space[OF assms]
    by (auto intro!: arg_cong[where f="\<mu>"])
qed

lemma (in measure_space) simple_integral_null_set:
  assumes "simple_function u" "N \<in> null_sets"
  shows "simple_integral (\<lambda>x. u x * indicator N x) = 0"
proof -
  have "simple_integral (\<lambda>x. u x * indicator N x) \<le>
    simple_integral (\<lambda>x. \<omega> * indicator N x)"
    using assms
    by (safe intro!: simple_integral_mono simple_function_mult simple_function_indicator simple_function_const) simp
  also have "... = 0" apply(subst simple_integral_mult)
    using assms(2) by auto
  finally show ?thesis by auto
qed

lemma (in measure_space) simple_integral_cong':
  assumes f: "simple_function f" and g: "simple_function g"
  and mea: "\<mu> {x\<in>space M. f x \<noteq> g x} = 0"
  shows "simple_integral f = simple_integral g"
proof -
  let ?h = "\<lambda>h. \<lambda>x. (h x * indicator {x\<in>space M. f x = g x} x
    + h x * indicator {x\<in>space M. f x \<noteq> g x} x
    + h x * indicator (-space M) x::pinfreal)"
  have *:"\<And>h. h = ?h h" unfolding indicator_def apply rule by auto
  have mea_neq:"{x \<in> space M. f x \<noteq> g x} \<in> sets M" using f g by (auto simp: borel_measurable_simple_function)
  then have mea_nullset: "{x \<in> space M. f x \<noteq> g x} \<in> null_sets" using mea by auto
  have h1:"\<And>h::_=>pinfreal. simple_function h \<Longrightarrow>
    simple_function (\<lambda>x. h x * indicator {x\<in>space M. f x = g x} x)"
    apply(safe intro!: simple_function_add simple_function_mult simple_function_indicator)
    using f g by (auto simp: borel_measurable_simple_function)
  have h2:"\<And>h::_\<Rightarrow>pinfreal. simple_function h \<Longrightarrow>
    simple_function (\<lambda>x. h x * indicator {x\<in>space M. f x \<noteq> g x} x)"
    apply(safe intro!: simple_function_add simple_function_mult simple_function_indicator)
    by(rule mea_neq)
  have **:"\<And>a b c d e f. a = b \<Longrightarrow> c = d \<Longrightarrow> e = f \<Longrightarrow> a+c+e = b+d+f" by auto
  note *** = simple_integral_add[OF simple_function_add[OF h1 h2] simple_function_notspace]
    simple_integral_add[OF h1 h2]
  show ?thesis apply(subst *[of g]) apply(subst *[of f])
    unfolding ***[OF f f] ***[OF g g]
  proof(rule **) case goal1 show ?case apply(rule arg_cong[where f=simple_integral]) apply rule 
      unfolding indicator_def by auto
  next note * = simple_integral_null_set[OF _ mea_nullset]
    case goal2 show ?case unfolding *[OF f] *[OF g] ..
  next case goal3 show ?case apply(rule simple_integral_cong) by auto
  qed
qed

lemma (in measure_space) simple_integral_restricted:
  assumes "A \<in> sets M"
  assumes sf: "simple_function (\<lambda>x. f x * indicator A x)"
  shows "measure_space.simple_integral (restricted_space A) \<mu> f = simple_integral (\<lambda>x. f x * indicator A x)"
    (is "_ = simple_integral ?f")
  unfolding measure_space.simple_integral_def[OF restricted_measure_space[OF `A \<in> sets M`]]
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
    unfolding pinfreal_mult_cancel_left by auto
qed

lemma (in measure_space) simple_integral_subalgebra[simp]:
  assumes "measure_space (M\<lparr>sets := N\<rparr>) \<mu>"
  shows "measure_space.simple_integral (M\<lparr>sets := N\<rparr>) \<mu> = simple_integral"
  unfolding simple_integral_def_raw
  unfolding measure_space.simple_integral_def_raw[OF assms] by simp

section "Continuous posititve integration"

definition (in measure_space)
  "positive_integral f =
    (SUP g : {g. simple_function g \<and> g \<le> f \<and> \<omega> \<notin> g`space M}. simple_integral g)"

lemma (in measure_space) positive_integral_alt1:
  "positive_integral f =
    (SUP g : {g. simple_function g \<and> (\<forall>x\<in>space M. g x \<le> f x \<and> g x \<noteq> \<omega>)}. simple_integral g)"
  unfolding positive_integral_def SUPR_def
proof (safe intro!: arg_cong[where f=Sup])
  fix g let ?g = "\<lambda>x. if x \<in> space M then g x else f x"
  assume "simple_function g" "\<forall>x\<in>space M. g x \<le> f x \<and> g x \<noteq> \<omega>"
  hence "?g \<le> f" "simple_function ?g" "simple_integral g = simple_integral ?g"
    "\<omega> \<notin> g`space M"
    unfolding le_fun_def by (auto cong: simple_function_cong simple_integral_cong)
  thus "simple_integral g \<in> simple_integral ` {g. simple_function g \<and> g \<le> f \<and> \<omega> \<notin> g`space M}"
    by auto
next
  fix g assume "simple_function g" "g \<le> f" "\<omega> \<notin> g`space M"
  hence "simple_function g" "\<forall>x\<in>space M. g x \<le> f x \<and> g x \<noteq> \<omega>"
    by (auto simp add: le_fun_def image_iff)
  thus "simple_integral g \<in> simple_integral ` {g. simple_function g \<and> (\<forall>x\<in>space M. g x \<le> f x \<and> g x \<noteq> \<omega>)}"
    by auto
qed

lemma (in measure_space) positive_integral_alt:
  "positive_integral f =
    (SUP g : {g. simple_function g \<and> g \<le> f}. simple_integral g)"
  apply(rule order_class.antisym) unfolding positive_integral_def 
  apply(rule SUPR_subset) apply blast apply(rule SUPR_mono_lim)
proof safe fix u assume u:"simple_function u" and uf:"u \<le> f"
  let ?u = "\<lambda>n x. if u x = \<omega> then Real (real (n::nat)) else u x"
  have su:"\<And>n. simple_function (?u n)" using simple_function_compose1[OF u] .
  show "\<exists>b. \<forall>n. b n \<in> {g. simple_function g \<and> g \<le> f \<and> \<omega> \<notin> g ` space M} \<and>
    (\<lambda>n. simple_integral (b n)) ----> simple_integral u"
    apply(rule_tac x="?u" in exI, safe) apply(rule su)
  proof- fix n::nat have "?u n \<le> u" unfolding le_fun_def by auto
    also note uf finally show "?u n \<le> f" .
    let ?s = "{x \<in> space M. u x = \<omega>}"
    show "(\<lambda>n. simple_integral (?u n)) ----> simple_integral u"
    proof(cases "\<mu> ?s = 0")
      case True have *:"\<And>n. {x\<in>space M. ?u n x \<noteq> u x} = {x\<in>space M. u x = \<omega>}" by auto 
      have *:"\<And>n. simple_integral (?u n) = simple_integral u"
        apply(rule simple_integral_cong'[OF su u]) unfolding * True ..
      show ?thesis unfolding * by auto 
    next case False note m0=this
      have s:"{x \<in> space M. u x = \<omega>} \<in> sets M" using u  by (auto simp: borel_measurable_simple_function)
      have "\<omega> = simple_integral (\<lambda>x. \<omega> * indicator {x\<in>space M. u x = \<omega>} x)"
        apply(subst simple_integral_mult) using s
        unfolding simple_integral_indicator_only[OF s] using False by auto
      also have "... \<le> simple_integral u"
        apply (rule simple_integral_mono)
        apply (rule simple_function_mult)
        apply (rule simple_function_const)
        apply(rule ) prefer 3 apply(subst indicator_def)
        using s u by auto
      finally have *:"simple_integral u = \<omega>" by auto
      show ?thesis unfolding * Lim_omega_pos
      proof safe case goal1
        from real_arch_simple[of "B / real (\<mu> ?s)"] guess N0 .. note N=this
        def N \<equiv> "Suc N0" have N:"real N \<ge> B / real (\<mu> ?s)" "N > 0"
          unfolding N_def using N by auto
        show ?case apply-apply(rule_tac x=N in exI,safe) 
        proof- case goal1
          have "Real B \<le> Real (real N) * \<mu> ?s"
          proof(cases "\<mu> ?s = \<omega>")
            case True thus ?thesis using `B>0` N by auto
          next case False
            have *:"B \<le> real N * real (\<mu> ?s)" 
              using N(1) apply-apply(subst (asm) pos_divide_le_eq)
              apply rule using m0 False by auto
            show ?thesis apply(subst Real_real'[THEN sym,OF False])
              apply(subst pinfreal_times,subst if_P) defer
              apply(subst pinfreal_less_eq,subst if_P) defer
              using * N `B>0` by(auto intro: mult_nonneg_nonneg)
          qed
          also have "... \<le> Real (real n) * \<mu> ?s"
            apply(rule mult_right_mono) using goal1 by auto
          also have "... = simple_integral (\<lambda>x. Real (real n) * indicator ?s x)" 
            apply(subst simple_integral_mult) apply(rule simple_function_indicator[OF s])
            unfolding simple_integral_indicator_only[OF s] ..
          also have "... \<le> simple_integral (\<lambda>x. if u x = \<omega> then Real (real n) else u x)"
            apply(rule simple_integral_mono) apply(rule simple_function_mult)
            apply(rule simple_function_const)
            apply(rule simple_function_indicator) apply(rule s su)+ by auto
          finally show ?case .
        qed qed qed
    fix x assume x:"\<omega> = (if u x = \<omega> then Real (real n) else u x)" "x \<in> space M"
    hence "u x = \<omega>" apply-apply(rule ccontr) by auto
    hence "\<omega> = Real (real n)" using x by auto
    thus False by auto
  qed
qed

lemma (in measure_space) positive_integral_cong:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> f x = g x"
  shows "positive_integral f = positive_integral g"
proof -
  have "\<And>h. (\<forall>x\<in>space M. h x \<le> f x \<and> h x \<noteq> \<omega>) = (\<forall>x\<in>space M. h x \<le> g x \<and> h x \<noteq> \<omega>)"
    using assms by auto
  thus ?thesis unfolding positive_integral_alt1 by auto
qed

lemma (in measure_space) positive_integral_eq_simple_integral:
  assumes "simple_function f"
  shows "positive_integral f = simple_integral f"
  unfolding positive_integral_alt
proof (safe intro!: pinfreal_SUPI)
  fix g assume "simple_function g" "g \<le> f"
  with assms show "simple_integral g \<le> simple_integral f"
    by (auto intro!: simple_integral_mono simp: le_fun_def)
next
  fix y assume "\<forall>x. x\<in>{g. simple_function g \<and> g \<le> f} \<longrightarrow> simple_integral x \<le> y"
  with assms show "simple_integral f \<le> y" by auto
qed

lemma (in measure_space) positive_integral_mono:
  assumes mono: "\<And>x. x \<in> space M \<Longrightarrow> u x \<le> v x"
  shows "positive_integral u \<le> positive_integral v"
  unfolding positive_integral_alt1
proof (safe intro!: SUPR_mono)
  fix a assume a: "simple_function a" and "\<forall>x\<in>space M. a x \<le> u x \<and> a x \<noteq> \<omega>"
  with mono have "\<forall>x\<in>space M. a x \<le> v x \<and> a x \<noteq> \<omega>" by fastsimp
  with a show "\<exists>b\<in>{g. simple_function g \<and> (\<forall>x\<in>space M. g x \<le> v x \<and> g x \<noteq> \<omega>)}. simple_integral a \<le> simple_integral b"
    by (auto intro!: bexI[of _ a])
qed

lemma (in measure_space) positive_integral_SUP_approx:
  assumes "f \<up> s"
  and f: "\<And>i. f i \<in> borel_measurable M"
  and "simple_function u"
  and le: "u \<le> s" and real: "\<omega> \<notin> u`space M"
  shows "simple_integral u \<le> (SUP i. positive_integral (f i))" (is "_ \<le> ?S")
proof (rule pinfreal_le_mult_one_interval)
  fix a :: pinfreal assume "0 < a" "a < 1"
  hence "a \<noteq> 0" by auto
  let "?B i" = "{x \<in> space M. a * u x \<le> f i x}"
  have B: "\<And>i. ?B i \<in> sets M"
    using f `simple_function u` by (auto simp: borel_measurable_simple_function)

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
    using `simple_function u` by (auto simp add: simple_function_def)

  { fix i
    have "(\<lambda>n. (u -` {i} \<inter> space M) \<inter> ?B n) \<up> (u -` {i} \<inter> space M)" using B_mono unfolding isoton_def
    proof safe
      fix x assume "x \<in> space M"
      show "x \<in> (\<Union>i. (u -` {u x} \<inter> space M) \<inter> ?B i)"
      proof cases
        assume "u x = 0" thus ?thesis using `x \<in> space M` by simp
      next
        assume "u x \<noteq> 0"
        with `a < 1` real `x \<in> space M`
        have "a * u x < 1 * u x" by (rule_tac pinfreal_mult_strict_right_mono) (auto simp: image_iff)
        also have "\<dots> \<le> (SUP i. f i x)" using le `f \<up> s`
          unfolding isoton_fun_expand by (auto simp: isoton_def le_fun_def)
        finally obtain i where "a * u x < f i x" unfolding SUPR_def
          by (auto simp add: less_Sup_iff)
        hence "a * u x \<le> f i x" by auto
        thus ?thesis using `x \<in> space M` by auto
      qed
    qed auto }
  note measure_conv = measure_up[OF u Int[OF u B] this]

  have "simple_integral u = (SUP i. simple_integral (?uB i))"
    unfolding simple_integral_indicator[OF B `simple_function u`]
  proof (subst SUPR_pinfreal_setsum, safe)
    fix x n assume "x \<in> space M"
    have "\<mu> (u -` {u x} \<inter> space M \<inter> {x \<in> space M. a * u x \<le> f n x})
      \<le> \<mu> (u -` {u x} \<inter> space M \<inter> {x \<in> space M. a * u x \<le> f (Suc n) x})"
      using B_mono Int[OF u[OF `x \<in> space M`] B] by (auto intro!: measure_mono)
    thus "u x * \<mu> (u -` {u x} \<inter> space M \<inter> ?B n)
            \<le> u x * \<mu> (u -` {u x} \<inter> space M \<inter> ?B (Suc n))"
      by (auto intro: mult_left_mono)
  next
    show "simple_integral u =
      (\<Sum>i\<in>u ` space M. SUP n. i * \<mu> (u -` {i} \<inter> space M \<inter> ?B n))"
      using measure_conv unfolding simple_integral_def isoton_def
      by (auto intro!: setsum_cong simp: pinfreal_SUP_cmult)
  qed
  moreover
  have "a * (SUP i. simple_integral (?uB i)) \<le> ?S"
    unfolding pinfreal_SUP_cmult[symmetric]
  proof (safe intro!: SUP_mono bexI)
    fix i
    have "a * simple_integral (?uB i) = simple_integral (\<lambda>x. a * ?uB i x)"
      using B `simple_function u`
      by (subst simple_integral_mult[symmetric]) (auto simp: field_simps)
    also have "\<dots> \<le> positive_integral (f i)"
    proof -
      have "\<And>x. a * ?uB i x \<le> f i x" unfolding indicator_def by auto
      hence *: "simple_function (\<lambda>x. a * ?uB i x)" using B assms(3)
        by (auto intro!: simple_integral_mono)
      show ?thesis unfolding positive_integral_eq_simple_integral[OF *, symmetric]
        by (auto intro!: positive_integral_mono simp: indicator_def)
    qed
    finally show "a * simple_integral (?uB i) \<le> positive_integral (f i)"
      by auto
  qed simp
  ultimately show "a * simple_integral u \<le> ?S" by simp
qed

text {* Beppo-Levi monotone convergence theorem *}
lemma (in measure_space) positive_integral_isoton:
  assumes "f \<up> u" "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>i. positive_integral (f i)) \<up> positive_integral u"
  unfolding isoton_def
proof safe
  fix i show "positive_integral (f i) \<le> positive_integral (f (Suc i))"
    apply (rule positive_integral_mono)
    using `f \<up> u` unfolding isoton_def le_fun_def by auto
next
  have "u \<in> borel_measurable M"
    using borel_measurable_SUP[of UNIV f] assms by (auto simp: isoton_def)
  have u: "u = (SUP i. f i)" using `f \<up> u` unfolding isoton_def by auto

  show "(SUP i. positive_integral (f i)) = positive_integral u"
  proof (rule antisym)
    from `f \<up> u`[THEN isoton_Sup, unfolded le_fun_def]
    show "(SUP j. positive_integral (f j)) \<le> positive_integral u"
      by (auto intro!: SUP_leI positive_integral_mono)
  next
    show "positive_integral u \<le> (SUP i. positive_integral (f i))"
      unfolding positive_integral_def[of u]
      by (auto intro!: SUP_leI positive_integral_SUP_approx[OF assms])
  qed
qed

lemma (in measure_space) SUP_simple_integral_sequences:
  assumes f: "f \<up> u" "\<And>i. simple_function (f i)"
  and g: "g \<up> u" "\<And>i. simple_function (g i)"
  shows "(SUP i. simple_integral (f i)) = (SUP i. simple_integral (g i))"
    (is "SUPR _ ?F = SUPR _ ?G")
proof -
  have "(SUP i. ?F i) = (SUP i. positive_integral (f i))"
    using assms by (simp add: positive_integral_eq_simple_integral)
  also have "\<dots> = positive_integral u"
    using positive_integral_isoton[OF f(1) borel_measurable_simple_function[OF f(2)]]
    unfolding isoton_def by simp
  also have "\<dots> = (SUP i. positive_integral (g i))"
    using positive_integral_isoton[OF g(1) borel_measurable_simple_function[OF g(2)]]
    unfolding isoton_def by simp
  also have "\<dots> = (SUP i. ?G i)"
    using assms by (simp add: positive_integral_eq_simple_integral)
  finally show ?thesis .
qed

lemma (in measure_space) positive_integral_const[simp]:
  "positive_integral (\<lambda>x. c) = c * \<mu> (space M)"
  by (subst positive_integral_eq_simple_integral) auto

lemma (in measure_space) positive_integral_isoton_simple:
  assumes "f \<up> u" and e: "\<And>i. simple_function (f i)"
  shows "(\<lambda>i. simple_integral (f i)) \<up> positive_integral u"
  using positive_integral_isoton[OF `f \<up> u` e(1)[THEN borel_measurable_simple_function]]
  unfolding positive_integral_eq_simple_integral[OF e] .

lemma (in measure_space) positive_integral_linear:
  assumes f: "f \<in> borel_measurable M"
  and g: "g \<in> borel_measurable M"
  shows "positive_integral (\<lambda>x. a * f x + g x) =
      a * positive_integral f + positive_integral g"
    (is "positive_integral ?L = _")
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
  moreover have
      "(SUP i. simple_integral (l i)) = (SUP i. simple_integral (?L' i))"
  proof (rule SUP_simple_integral_sequences[OF l(1-2)])
    show "?L' \<up> ?L" "\<And>i. simple_function (?L' i)"
      using u v by (auto simp: isoton_fun_expand isoton_add isoton_cmult_right)
  qed
  moreover from u v have L'_isoton:
      "(\<lambda>i. simple_integral (?L' i)) \<up> a * positive_integral f + positive_integral g"
    by (simp add: isoton_add isoton_cmult_right)
  ultimately show ?thesis by (simp add: isoton_def)
qed

lemma (in measure_space) positive_integral_cmult:
  assumes "f \<in> borel_measurable M"
  shows "positive_integral (\<lambda>x. c * f x) = c * positive_integral f"
  using positive_integral_linear[OF assms, of "\<lambda>x. 0" c] by auto

lemma (in measure_space) positive_integral_indicator[simp]:
  "A \<in> sets M \<Longrightarrow> positive_integral (\<lambda>x. indicator A x) = \<mu> A"
by (subst positive_integral_eq_simple_integral) (auto simp: simple_function_indicator simple_integral_indicator)

lemma (in measure_space) positive_integral_cmult_indicator:
  "A \<in> sets M \<Longrightarrow> positive_integral (\<lambda>x. c * indicator A x) = c * \<mu> A"
by (subst positive_integral_eq_simple_integral) (auto simp: simple_function_indicator simple_integral_indicator)

lemma (in measure_space) positive_integral_add:
  assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "positive_integral (\<lambda>x. f x + g x) = positive_integral f + positive_integral g"
  using positive_integral_linear[OF assms, of 1] by simp

lemma (in measure_space) positive_integral_setsum:
  assumes "\<And>i. i\<in>P \<Longrightarrow> f i \<in> borel_measurable M"
  shows "positive_integral (\<lambda>x. \<Sum>i\<in>P. f i x) = (\<Sum>i\<in>P. positive_integral (f i))"
proof cases
  assume "finite P"
  from this assms show ?thesis
  proof induct
    case (insert i P)
    have "f i \<in> borel_measurable M"
      "(\<lambda>x. \<Sum>i\<in>P. f i x) \<in> borel_measurable M"
      using insert by (auto intro!: borel_measurable_pinfreal_setsum)
    from positive_integral_add[OF this]
    show ?case using insert by auto
  qed simp
qed simp

lemma (in measure_space) positive_integral_diff:
  assumes f: "f \<in> borel_measurable M" and g: "g \<in> borel_measurable M"
  and fin: "positive_integral g \<noteq> \<omega>"
  and mono: "\<And>x. x \<in> space M \<Longrightarrow> g x \<le> f x"
  shows "positive_integral (\<lambda>x. f x - g x) = positive_integral f - positive_integral g"
proof -
  have borel: "(\<lambda>x. f x - g x) \<in> borel_measurable M"
    using f g by (rule borel_measurable_pinfreal_diff)
  have "positive_integral (\<lambda>x. f x - g x) + positive_integral g =
    positive_integral f"
    unfolding positive_integral_add[OF borel g, symmetric]
  proof (rule positive_integral_cong)
    fix x assume "x \<in> space M"
    from mono[OF this] show "f x - g x + g x = f x"
      by (cases "f x", cases "g x", simp, simp, cases "g x", auto)
  qed
  with mono show ?thesis
    by (subst minus_pinfreal_eq2[OF _ fin]) (auto intro!: positive_integral_mono)
qed

lemma (in measure_space) positive_integral_psuminf:
  assumes "\<And>i. f i \<in> borel_measurable M"
  shows "positive_integral (\<lambda>x. \<Sum>\<^isub>\<infinity> i. f i x) = (\<Sum>\<^isub>\<infinity> i. positive_integral (f i))"
proof -
  have "(\<lambda>i. positive_integral (\<lambda>x. \<Sum>i<i. f i x)) \<up> positive_integral (\<lambda>x. \<Sum>\<^isub>\<infinity>i. f i x)"
    by (rule positive_integral_isoton)
       (auto intro!: borel_measurable_pinfreal_setsum assms positive_integral_mono
                     arg_cong[where f=Sup]
             simp: isoton_def le_fun_def psuminf_def fun_eq_iff SUPR_def Sup_fun_def)
  thus ?thesis
    by (auto simp: isoton_def psuminf_def positive_integral_setsum[OF assms])
qed

text {* Fatou's lemma: convergence theorem on limes inferior *}
lemma (in measure_space) positive_integral_lim_INF:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> pinfreal"
  assumes "\<And>i. u i \<in> borel_measurable M"
  shows "positive_integral (SUP n. INF m. u (m + n)) \<le>
    (SUP n. INF m. positive_integral (u (m + n)))"
proof -
  have "(SUP n. INF m. u (m + n)) \<in> borel_measurable M"
    by (auto intro!: borel_measurable_SUP borel_measurable_INF assms)

  have "(\<lambda>n. INF m. u (m + n)) \<up> (SUP n. INF m. u (m + n))"
  proof (unfold isoton_def, safe intro!: INF_mono bexI)
    fix i m show "u (Suc m + i) \<le> u (m + Suc i)" by simp
  qed simp
  from positive_integral_isoton[OF this] assms
  have "positive_integral (SUP n. INF m. u (m + n)) =
    (SUP n. positive_integral (INF m. u (m + n)))"
    unfolding isoton_def by (simp add: borel_measurable_INF)
  also have "\<dots> \<le> (SUP n. INF m. positive_integral (u (m + n)))"
    apply (rule SUP_mono)
    apply (rule_tac x=n in bexI)
    by (auto intro!: positive_integral_mono INFI_bound INF_leI exI simp: INFI_fun_expand)
  finally show ?thesis .
qed

lemma (in measure_space) measure_space_density:
  assumes borel: "u \<in> borel_measurable M"
  shows "measure_space M (\<lambda>A. positive_integral (\<lambda>x. u x * indicator A x))" (is "measure_space M ?v")
proof
  show "?v {} = 0" by simp
  show "countably_additive M ?v"
    unfolding countably_additive_def
  proof safe
    fix A :: "nat \<Rightarrow> 'a set"
    assume "range A \<subseteq> sets M"
    hence "\<And>i. (\<lambda>x. u x * indicator (A i) x) \<in> borel_measurable M"
      using borel by (auto intro: borel_measurable_indicator)
    moreover assume "disjoint_family A"
    note psuminf_indicator[OF this]
    ultimately show "(\<Sum>\<^isub>\<infinity>n. ?v (A n)) = ?v (\<Union>x. A x)"
      by (simp add: positive_integral_psuminf[symmetric])
  qed
qed

lemma (in measure_space) positive_integral_translated_density:
  assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "measure_space.positive_integral M (\<lambda>A. positive_integral (\<lambda>x. f x * indicator A x)) g =
    positive_integral (\<lambda>x. f x * g x)" (is "measure_space.positive_integral M ?T _ = _")
proof -
  from measure_space_density[OF assms(1)]
  interpret T: measure_space M ?T .
  from borel_measurable_implies_simple_function_sequence[OF assms(2)]
  obtain G where G: "\<And>i. simple_function (G i)" "G \<up> g" by blast
  note G_borel = borel_measurable_simple_function[OF this(1)]
  from T.positive_integral_isoton[OF `G \<up> g` G_borel]
  have *: "(\<lambda>i. T.positive_integral (G i)) \<up> T.positive_integral g" .
  { fix i
    have [simp]: "finite (G i ` space M)"
      using G(1) unfolding simple_function_def by auto
    have "T.positive_integral (G i) = T.simple_integral (G i)"
      using G T.positive_integral_eq_simple_integral by simp
    also have "\<dots> = positive_integral (\<lambda>x. f x * (\<Sum>y\<in>G i`space M. y * indicator (G i -` {y} \<inter> space M) x))"
      apply (simp add: T.simple_integral_def)
      apply (subst positive_integral_cmult[symmetric])
      using G_borel assms(1) apply (fastsimp intro: borel_measurable_indicator borel_measurable_vimage)
      apply (subst positive_integral_setsum[symmetric])
      using G_borel assms(1) apply (fastsimp intro: borel_measurable_indicator borel_measurable_vimage)
      by (simp add: setsum_right_distrib field_simps)
    also have "\<dots> = positive_integral (\<lambda>x. f x * G i x)"
      by (auto intro!: positive_integral_cong
               simp: indicator_def if_distrib setsum_cases)
    finally have "T.positive_integral (G i) = positive_integral (\<lambda>x. f x * G i x)" . }
  with * have eq_Tg: "(\<lambda>i. positive_integral (\<lambda>x. f x * G i x)) \<up> T.positive_integral g" by simp
  from G(2) have "(\<lambda>i x. f x * G i x) \<up> (\<lambda>x. f x * g x)"
    unfolding isoton_fun_expand by (auto intro!: isoton_cmult_right)
  then have "(\<lambda>i. positive_integral (\<lambda>x. f x * G i x)) \<up> positive_integral (\<lambda>x. f x * g x)"
    using assms(1) G_borel by (auto intro!: positive_integral_isoton borel_measurable_pinfreal_times)
  with eq_Tg show "T.positive_integral g = positive_integral (\<lambda>x. f x * g x)"
    unfolding isoton_def by simp
qed

lemma (in measure_space) positive_integral_null_set:
  assumes borel: "u \<in> borel_measurable M" and "N \<in> null_sets"
  shows "positive_integral (\<lambda>x. u x * indicator N x) = 0" (is "?I = 0")
proof -
  have "N \<in> sets M" using `N \<in> null_sets` by auto
  have "(\<lambda>i x. min (of_nat i) (u x) * indicator N x) \<up> (\<lambda>x. u x * indicator N x)"
    unfolding isoton_fun_expand
  proof (safe intro!: isoton_cmult_left, unfold isoton_def, safe)
    fix j i show "min (of_nat j) (u i) \<le> min (of_nat (Suc j)) (u i)"
      by (rule min_max.inf_mono) auto
  next
    fix i show "(SUP j. min (of_nat j) (u i)) = u i"
    proof (cases "u i")
      case infinite
      moreover hence "\<And>j. min (of_nat j) (u i) = of_nat j"
        by (auto simp: min_def)
      ultimately show ?thesis by (simp add: Sup_\<omega>)
    next
      case (preal r)
      obtain j where "r \<le> of_nat j" using ex_le_of_nat ..
      hence "u i \<le> of_nat j" using preal by (auto simp: real_of_nat_def)
      show ?thesis
      proof (rule pinfreal_SUPI)
        fix y assume "\<And>j. j \<in> UNIV \<Longrightarrow> min (of_nat j) (u i) \<le> y"
        note this[of j]
        moreover have "min (of_nat j) (u i) = u i"
          using `u i \<le> of_nat j` by (auto simp: min_def)
        ultimately show "u i \<le> y" by simp
      qed simp
    qed
  qed
  from positive_integral_isoton[OF this]
  have "?I = (SUP i. positive_integral (\<lambda>x. min (of_nat i) (u x) * indicator N x))"
    unfolding isoton_def using borel `N \<in> sets M` by (simp add: borel_measurable_indicator)
  also have "\<dots> \<le> (SUP i. positive_integral (\<lambda>x. of_nat i * indicator N x))"
  proof (rule SUP_mono, rule bexI, rule positive_integral_mono)
    fix x i show "min (of_nat i) (u x) * indicator N x \<le> of_nat i * indicator N x"
      by (cases "x \<in> N") auto
  qed simp
  also have "\<dots> = 0"
    using `N \<in> null_sets` by (simp add: positive_integral_cmult_indicator)
  finally show ?thesis by simp
qed

lemma (in measure_space) positive_integral_Markov_inequality:
  assumes borel: "u \<in> borel_measurable M" and "A \<in> sets M" and c: "c \<noteq> \<omega>"
  shows "\<mu> ({x\<in>space M. 1 \<le> c * u x} \<inter> A) \<le> c * positive_integral (\<lambda>x. u x * indicator A x)"
    (is "\<mu> ?A \<le> _ * ?PI")
proof -
  have "?A \<in> sets M"
    using `A \<in> sets M` borel by auto
  hence "\<mu> ?A = positive_integral (\<lambda>x. indicator ?A x)"
    using positive_integral_indicator by simp
  also have "\<dots> \<le> positive_integral (\<lambda>x. c * (u x * indicator A x))"
  proof (rule positive_integral_mono)
    fix x assume "x \<in> space M"
    show "indicator ?A x \<le> c * (u x * indicator A x)"
      by (cases "x \<in> ?A") auto
  qed
  also have "\<dots> = c * positive_integral (\<lambda>x. u x * indicator A x)"
    using assms
    by (auto intro!: positive_integral_cmult borel_measurable_indicator)
  finally show ?thesis .
qed

lemma (in measure_space) positive_integral_0_iff:
  assumes borel: "u \<in> borel_measurable M"
  shows "positive_integral u = 0 \<longleftrightarrow> \<mu> {x\<in>space M. u x \<noteq> 0} = 0"
    (is "_ \<longleftrightarrow> \<mu> ?A = 0")
proof -
  have A: "?A \<in> sets M" using borel by auto
  have u: "positive_integral (\<lambda>x. u x * indicator ?A x) = positive_integral u"
    by (auto intro!: positive_integral_cong simp: indicator_def)

  show ?thesis
  proof
    assume "\<mu> ?A = 0"
    hence "?A \<in> null_sets" using `?A \<in> sets M` by auto
    from positive_integral_null_set[OF borel this]
    have "0 = positive_integral (\<lambda>x. u x * indicator ?A x)" by simp
    thus "positive_integral u = 0" unfolding u by simp
  next
    assume *: "positive_integral u = 0"
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
        by (subst (1 2) mult_commute) (auto intro!: pinfreal_mult_cancel)
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

lemma (in measure_space) positive_integral_cong_on_null_sets:
  assumes f: "f \<in> borel_measurable M" and g: "g \<in> borel_measurable M"
  and measure: "\<mu> {x\<in>space M. f x \<noteq> g x} = 0"
  shows "positive_integral f = positive_integral g"
proof -
  let ?N = "{x\<in>space M. f x \<noteq> g x}" and ?E = "{x\<in>space M. f x = g x}"
  let "?A h x" = "h x * indicator ?E x :: pinfreal"
  let "?B h x" = "h x * indicator ?N x :: pinfreal"

  have A: "positive_integral (?A f) = positive_integral (?A g)"
    by (auto intro!: positive_integral_cong simp: indicator_def)

  have [intro]: "?N \<in> sets M" "?E \<in> sets M" using f g by auto
  hence "?N \<in> null_sets" using measure by auto
  hence B: "positive_integral (?B f) = positive_integral (?B g)"
    using f g by (simp add: positive_integral_null_set)

  have "positive_integral f = positive_integral (\<lambda>x. ?A f x + ?B f x)"
    by (auto intro!: positive_integral_cong simp: indicator_def)
  also have "\<dots> = positive_integral (?A f) + positive_integral (?B f)"
    using f g by (auto intro!: positive_integral_add borel_measurable_indicator)
  also have "\<dots> = positive_integral (\<lambda>x. ?A g x + ?B g x)"
    unfolding A B using f g by (auto intro!: positive_integral_add[symmetric] borel_measurable_indicator)
  also have "\<dots> = positive_integral g"
    by (auto intro!: positive_integral_cong simp: indicator_def)
  finally show ?thesis by simp
qed

lemma (in measure_space) positive_integral_restricted:
  assumes "A \<in> sets M"
  shows "measure_space.positive_integral (restricted_space A) \<mu> f = positive_integral (\<lambda>x. f x * indicator A x)"
    (is "measure_space.positive_integral ?R \<mu> f = positive_integral ?f")
proof -
  have msR: "measure_space ?R \<mu>" by (rule restricted_measure_space[OF `A \<in> sets M`])
  then interpret R: measure_space ?R \<mu> .
  have saR: "sigma_algebra ?R" by fact
  have *: "R.positive_integral f = R.positive_integral ?f"
    by (auto intro!: R.positive_integral_cong)
  show ?thesis
    unfolding * R.positive_integral_def positive_integral_def
    unfolding simple_function_restricted[OF `A \<in> sets M`]
    apply (simp add: SUPR_def)
    apply (rule arg_cong[where f=Sup])
  proof (auto simp: image_iff simple_integral_restricted[OF `A \<in> sets M`])
    fix g assume "simple_function (\<lambda>x. g x * indicator A x)"
      "g \<le> f" "\<forall>x\<in>A. \<omega> \<noteq> g x"
    then show "\<exists>x. simple_function x \<and> x \<le> (\<lambda>x. f x * indicator A x) \<and> (\<forall>y\<in>space M. \<omega> \<noteq> x y) \<and>
      simple_integral (\<lambda>x. g x * indicator A x) = simple_integral x"
      apply (rule_tac exI[of _ "\<lambda>x. g x * indicator A x"])
      by (auto simp: indicator_def le_fun_def)
  next
    fix g assume g: "simple_function g" "g \<le> (\<lambda>x. f x * indicator A x)"
      "\<forall>x\<in>space M. \<omega> \<noteq> g x"
    then have *: "(\<lambda>x. g x * indicator A x) = g"
      "\<And>x. g x * indicator A x = g x"
      "\<And>x. g x \<le> f x"
      by (auto simp: le_fun_def fun_eq_iff indicator_def split: split_if_asm)
    from g show "\<exists>x. simple_function (\<lambda>xa. x xa * indicator A xa) \<and> x \<le> f \<and> (\<forall>xa\<in>A. \<omega> \<noteq> x xa) \<and>
      simple_integral g = simple_integral (\<lambda>xa. x xa * indicator A xa)"
      using `A \<in> sets M`[THEN sets_into_space]
      apply (rule_tac exI[of _ "\<lambda>x. g x * indicator A x"])
      by (fastsimp simp: le_fun_def *)
  qed
qed

lemma (in measure_space) positive_integral_subalgebra[simp]:
  assumes borel: "f \<in> borel_measurable (M\<lparr>sets := N\<rparr>)"
  and N_subalgebra: "N \<subseteq> sets M" "sigma_algebra (M\<lparr>sets := N\<rparr>)"
  shows "measure_space.positive_integral (M\<lparr>sets := N\<rparr>) \<mu> f = positive_integral f"
proof -
  note msN = measure_space_subalgebra[OF N_subalgebra]
  then interpret N: measure_space "M\<lparr>sets:=N\<rparr>" \<mu> .
  from N.borel_measurable_implies_simple_function_sequence[OF borel]
  obtain fs where Nsf: "\<And>i. N.simple_function (fs i)" and "fs \<up> f" by blast
  then have sf: "\<And>i. simple_function (fs i)"
    using simple_function_subalgebra[OF _ N_subalgebra] by blast
  from positive_integral_isoton_simple[OF `fs \<up> f` sf] N.positive_integral_isoton_simple[OF `fs \<up> f` Nsf]
  show ?thesis unfolding simple_integral_subalgebra[OF msN] isoton_def by simp
qed

section "Lebesgue Integral"

definition (in measure_space) integrable where
  "integrable f \<longleftrightarrow> f \<in> borel_measurable M \<and>
    positive_integral (\<lambda>x. Real (f x)) \<noteq> \<omega> \<and>
    positive_integral (\<lambda>x. Real (- f x)) \<noteq> \<omega>"

lemma (in measure_space) integrableD[dest]:
  assumes "integrable f"
  shows "f \<in> borel_measurable M"
  "positive_integral (\<lambda>x. Real (f x)) \<noteq> \<omega>"
  "positive_integral (\<lambda>x. Real (- f x)) \<noteq> \<omega>"
  using assms unfolding integrable_def by auto

definition (in measure_space) integral where
  "integral f =
    real (positive_integral (\<lambda>x. Real (f x))) -
    real (positive_integral (\<lambda>x. Real (- f x)))"

lemma (in measure_space) integral_cong:
  assumes cong: "\<And>x. x \<in> space M \<Longrightarrow> f x = g x"
  shows "integral f = integral g"
  using assms by (simp cong: positive_integral_cong add: integral_def)

lemma (in measure_space) integrable_cong:
  "(\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> integrable f \<longleftrightarrow> integrable g"
  by (simp cong: positive_integral_cong measurable_cong add: integrable_def)

lemma (in measure_space) integral_eq_positive_integral:
  assumes "\<And>x. 0 \<le> f x"
  shows "integral f = real (positive_integral (\<lambda>x. Real (f x)))"
proof -
  have "\<And>x. Real (- f x) = 0" using assms by simp
  thus ?thesis by (simp del: Real_eq_0 add: integral_def)
qed

lemma (in measure_space) integral_minus[intro, simp]:
  assumes "integrable f"
  shows "integrable (\<lambda>x. - f x)" "integral (\<lambda>x. - f x) = - integral f"
  using assms by (auto simp: integrable_def integral_def)

lemma (in measure_space) integral_of_positive_diff:
  assumes integrable: "integrable u" "integrable v"
  and f_def: "\<And>x. f x = u x - v x" and pos: "\<And>x. 0 \<le> u x" "\<And>x. 0 \<le> v x"
  shows "integrable f" and "integral f = integral u - integral v"
proof -
  let ?PI = positive_integral
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

  have "?PI (\<lambda>x. Real (u x - v x)) \<le> ?PI ?u"
    using pos by (auto intro!: positive_integral_mono)
  moreover have "?PI (\<lambda>x. Real (v x - u x)) \<le> ?PI ?v"
    using pos by (auto intro!: positive_integral_mono)
  ultimately show f: "integrable f"
    using `integrable u` `integrable v` `f \<in> borel_measurable M`
    by (auto simp: integrable_def f_def)
  hence mf: "integrable (\<lambda>x. - f x)" ..

  have *: "\<And>x. Real (- v x) = 0" "\<And>x. Real (- u x) = 0"
    using pos by auto

  have "\<And>x. ?u x + ?mf x = ?v x + ?f x"
    unfolding f_def using pos by simp
  hence "?PI (\<lambda>x. ?u x + ?mf x) = ?PI (\<lambda>x. ?v x + ?f x)" by simp
  hence "real (?PI ?u + ?PI ?mf) = real (?PI ?v + ?PI ?f)"
    using positive_integral_add[OF u_borel mf_borel]
    using positive_integral_add[OF v_borel f_borel]
    by auto
  then show "integral f = integral u - integral v"
    using f mf `integrable u` `integrable v`
    unfolding integral_def integrable_def *
    by (cases "?PI ?f", cases "?PI ?mf", cases "?PI ?v", cases "?PI ?u")
       (auto simp add: field_simps)
qed

lemma (in measure_space) integral_linear:
  assumes "integrable f" "integrable g" and "0 \<le> a"
  shows "integrable (\<lambda>t. a * f t + g t)"
  and "integral (\<lambda>t. a * f t + g t) = a * integral f + integral g"
proof -
  let ?PI = positive_integral
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

  have "integrable ?p" "integrable ?n"
      "\<And>t. a * f t + g t = ?p t - ?n t" "\<And>t. 0 \<le> ?p t" "\<And>t. 0 \<le> ?n t"
    using assms p n unfolding integrable_def * linear by auto
  note diff = integral_of_positive_diff[OF this]

  show "integrable (\<lambda>t. a * f t + g t)" by (rule diff)

  from assms show "integral (\<lambda>t. a * f t + g t) = a * integral f + integral g"
    unfolding diff(2) unfolding integral_def * linear integrable_def
    by (cases "?PI ?f", cases "?PI ?mf", cases "?PI ?g", cases "?PI ?mg")
       (auto simp add: field_simps zero_le_mult_iff)
qed

lemma (in measure_space) integral_add[simp, intro]:
  assumes "integrable f" "integrable g"
  shows "integrable (\<lambda>t. f t + g t)"
  and "integral (\<lambda>t. f t + g t) = integral f + integral g"
  using assms integral_linear[where a=1] by auto

lemma (in measure_space) integral_zero[simp, intro]:
  shows "integrable (\<lambda>x. 0)"
  and "integral (\<lambda>x. 0) = 0"
  unfolding integrable_def integral_def
  by (auto simp add: borel_measurable_const)

lemma (in measure_space) integral_cmult[simp, intro]:
  assumes "integrable f"
  shows "integrable (\<lambda>t. a * f t)" (is ?P)
  and "integral (\<lambda>t. a * f t) = a * integral f" (is ?I)
proof -
  have "integrable (\<lambda>t. a * f t) \<and> integral (\<lambda>t. a * f t) = a * integral f"
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

lemma (in measure_space) integral_mono:
  assumes fg: "integrable f" "integrable g"
  and mono: "\<And>t. t \<in> space M \<Longrightarrow> f t \<le> g t"
  shows "integral f \<le> integral g"
  using fg unfolding integral_def integrable_def diff_minus
proof (safe intro!: add_mono real_of_pinfreal_mono le_imp_neg_le positive_integral_mono)
  fix x assume "x \<in> space M" from mono[OF this]
  show "Real (f x) \<le> Real (g x)" "Real (- g x) \<le> Real (- f x)" by auto
qed

lemma (in measure_space) integral_diff[simp, intro]:
  assumes f: "integrable f" and g: "integrable g"
  shows "integrable (\<lambda>t. f t - g t)"
  and "integral (\<lambda>t. f t - g t) = integral f - integral g"
  using integral_add[OF f integral_minus(1)[OF g]]
  unfolding diff_minus integral_minus(2)[OF g]
  by auto

lemma (in measure_space) integral_indicator[simp, intro]:
  assumes "a \<in> sets M" and "\<mu> a \<noteq> \<omega>"
  shows "integral (indicator a) = real (\<mu> a)" (is ?int)
  and "integrable (indicator a)" (is ?able)
proof -
  have *:
    "\<And>A x. Real (indicator A x) = indicator A x"
    "\<And>A x. Real (- indicator A x) = 0" unfolding indicator_def by auto
  show ?int ?able
    using assms unfolding integral_def integrable_def
    by (auto simp: * positive_integral_indicator borel_measurable_indicator)
qed

lemma (in measure_space) integral_cmul_indicator:
  assumes "A \<in> sets M" and "c \<noteq> 0 \<Longrightarrow> \<mu> A \<noteq> \<omega>"
  shows "integrable (\<lambda>x. c * indicator A x)" (is ?P)
  and "integral (\<lambda>x. c * indicator A x) = c * real (\<mu> A)" (is ?I)
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
  assumes "\<And>n. n \<in> S \<Longrightarrow> integrable (f n)"
  shows "integral (\<lambda>x. \<Sum> i \<in> S. f i x) = (\<Sum> i \<in> S. integral (f i))" (is "?int S")
    and "integrable (\<lambda>x. \<Sum> i \<in> S. f i x)" (is "?I S")
proof -
  have "?int S \<and> ?I S"
  proof (cases "finite S")
    assume "finite S"
    from this assms show ?thesis by (induct S) simp_all
  qed simp
  thus "?int S" and "?I S" by auto
qed

lemma (in measure_space) integrable_abs:
  assumes "integrable f"
  shows "integrable (\<lambda> x. \<bar>f x\<bar>)"
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

lemma (in measure_space) integrable_bound:
  assumes "integrable f"
  and f: "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> f x"
    "\<And>x. x \<in> space M \<Longrightarrow> \<bar>g x\<bar> \<le> f x"
  assumes borel: "g \<in> borel_measurable M"
  shows "integrable g"
proof -
  have "positive_integral (\<lambda>x. Real (g x)) \<le> positive_integral (\<lambda>x. Real \<bar>g x\<bar>)"
    by (auto intro!: positive_integral_mono)
  also have "\<dots> \<le> positive_integral (\<lambda>x. Real (f x))"
    using f by (auto intro!: positive_integral_mono)
  also have "\<dots> < \<omega>"
    using `integrable f` unfolding integrable_def by (auto simp: pinfreal_less_\<omega>)
  finally have pos: "positive_integral (\<lambda>x. Real (g x)) < \<omega>" .

  have "positive_integral (\<lambda>x. Real (- g x)) \<le> positive_integral (\<lambda>x. Real (\<bar>g x\<bar>))"
    by (auto intro!: positive_integral_mono)
  also have "\<dots> \<le> positive_integral (\<lambda>x. Real (f x))"
    using f by (auto intro!: positive_integral_mono)
  also have "\<dots> < \<omega>"
    using `integrable f` unfolding integrable_def by (auto simp: pinfreal_less_\<omega>)
  finally have neg: "positive_integral (\<lambda>x. Real (- g x)) < \<omega>" .

  from neg pos borel show ?thesis
    unfolding integrable_def by auto
qed

lemma (in measure_space) integrable_abs_iff:
  "f \<in> borel_measurable M \<Longrightarrow> integrable (\<lambda> x. \<bar>f x\<bar>) \<longleftrightarrow> integrable f"
  by (auto intro!: integrable_bound[where g=f] integrable_abs)

lemma (in measure_space) integrable_max:
  assumes int: "integrable f" "integrable g"
  shows "integrable (\<lambda> x. max (f x) (g x))"
proof (rule integrable_bound)
  show "integrable (\<lambda>x. \<bar>f x\<bar> + \<bar>g x\<bar>)"
    using int by (simp add: integrable_abs)
  show "(\<lambda>x. max (f x) (g x)) \<in> borel_measurable M"
    using int unfolding integrable_def by auto
next
  fix x assume "x \<in> space M"
  show "0 \<le> \<bar>f x\<bar> + \<bar>g x\<bar>" "\<bar>max (f x) (g x)\<bar> \<le> \<bar>f x\<bar> + \<bar>g x\<bar>"
    by auto
qed

lemma (in measure_space) integrable_min:
  assumes int: "integrable f" "integrable g"
  shows "integrable (\<lambda> x. min (f x) (g x))"
proof (rule integrable_bound)
  show "integrable (\<lambda>x. \<bar>f x\<bar> + \<bar>g x\<bar>)"
    using int by (simp add: integrable_abs)
  show "(\<lambda>x. min (f x) (g x)) \<in> borel_measurable M"
    using int unfolding integrable_def by auto
next
  fix x assume "x \<in> space M"
  show "0 \<le> \<bar>f x\<bar> + \<bar>g x\<bar>" "\<bar>min (f x) (g x)\<bar> \<le> \<bar>f x\<bar> + \<bar>g x\<bar>"
    by auto
qed

lemma (in measure_space) integral_triangle_inequality:
  assumes "integrable f"
  shows "\<bar>integral f\<bar> \<le> integral (\<lambda>x. \<bar>f x\<bar>)"
proof -
  have "\<bar>integral f\<bar> = max (integral f) (- integral f)" by auto
  also have "\<dots> \<le> integral (\<lambda>x. \<bar>f x\<bar>)"
      using assms integral_minus(2)[of f, symmetric]
      by (auto intro!: integral_mono integrable_abs simp del: integral_minus)
  finally show ?thesis .
qed

lemma (in measure_space) integral_positive:
  assumes "integrable f" "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> f x"
  shows "0 \<le> integral f"
proof -
  have "0 = integral (\<lambda>x. 0)" by (auto simp: integral_zero)
  also have "\<dots> \<le> integral f"
    using assms by (rule integral_mono[OF integral_zero(1)])
  finally show ?thesis .
qed

lemma (in measure_space) integral_monotone_convergence_pos:
  assumes i: "\<And>i. integrable (f i)" and mono: "\<And>x. mono (\<lambda>n. f n x)"
  and pos: "\<And>x i. 0 \<le> f i x"
  and lim: "\<And>x. (\<lambda>i. f i x) ----> u x"
  and ilim: "(\<lambda>i. integral (f i)) ----> x"
  shows "integrable u"
  and "integral u = x"
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
  hence "(SUP i. (\<lambda>x. Real (f i x))) \<in> borel_measurable M"
    by auto
  hence borel_u: "u \<in> borel_measurable M"
    using pos_u by (auto simp: borel_measurable_Real_eq SUPR_fun_expand SUP_F)

  have integral_eq: "\<And>n. positive_integral (\<lambda>x. Real (f n x)) = Real (integral (f n))"
    using i unfolding integral_def integrable_def by (auto simp: Real_real)

  have pos_integral: "\<And>n. 0 \<le> integral (f n)"
    using pos i by (auto simp: integral_positive)
  hence "0 \<le> x"
    using LIMSEQ_le_const[OF ilim, of 0] by auto

  have "(\<lambda>i. positive_integral (\<lambda>x. Real (f i x))) \<up> positive_integral (\<lambda>x. Real (u x))"
  proof (rule positive_integral_isoton)
    from SUP_F mono pos
    show "(\<lambda>i x. Real (f i x)) \<up> (\<lambda>x. Real (u x))"
      unfolding isoton_fun_expand by (auto simp: isoton_def mono_def)
  qed (rule borel_f)
  hence pI: "positive_integral (\<lambda>x. Real (u x)) =
      (SUP n. positive_integral (\<lambda>x. Real (f n x)))"
    unfolding isoton_def by simp
  also have "\<dots> = Real x" unfolding integral_eq
  proof (rule SUP_eq_LIMSEQ[THEN iffD2])
    show "mono (\<lambda>n. integral (f n))"
      using mono i by (auto simp: mono_def intro!: integral_mono)
    show "\<And>n. 0 \<le> integral (f n)" using pos_integral .
    show "0 \<le> x" using `0 \<le> x` .
    show "(\<lambda>n. integral (f n)) ----> x" using ilim .
  qed
  finally show  "integrable u" "integral u = x" using borel_u `0 \<le> x`
    unfolding integrable_def integral_def by auto
qed

lemma (in measure_space) integral_monotone_convergence:
  assumes f: "\<And>i. integrable (f i)" and "mono f"
  and lim: "\<And>x. (\<lambda>i. f i x) ----> u x"
  and ilim: "(\<lambda>i. integral (f i)) ----> x"
  shows "integrable u"
  and "integral u = x"
proof -
  have 1: "\<And>i. integrable (\<lambda>x. f i x - f 0 x)"
      using f by (auto intro!: integral_diff)
  have 2: "\<And>x. mono (\<lambda>n. f n x - f 0 x)" using `mono f`
      unfolding mono_def le_fun_def by auto
  have 3: "\<And>x n. 0 \<le> f n x - f 0 x" using `mono f`
      unfolding mono_def le_fun_def by (auto simp: field_simps)
  have 4: "\<And>x. (\<lambda>i. f i x - f 0 x) ----> u x - f 0 x"
    using lim by (auto intro!: LIMSEQ_diff)
  have 5: "(\<lambda>i. integral (\<lambda>x. f i x - f 0 x)) ----> x - integral (f 0)"
    using f ilim by (auto intro!: LIMSEQ_diff simp: integral_diff)
  note diff = integral_monotone_convergence_pos[OF 1 2 3 4 5]
  have "integrable (\<lambda>x. (u x - f 0 x) + f 0 x)"
    using diff(1) f by (rule integral_add(1))
  with diff(2) f show "integrable u" "integral u = x"
    by (auto simp: integral_diff)
qed

lemma (in measure_space) integral_0_iff:
  assumes "integrable f"
  shows "integral (\<lambda>x. \<bar>f x\<bar>) = 0 \<longleftrightarrow> \<mu> {x\<in>space M. f x \<noteq> 0} = 0"
proof -
  have *: "\<And>x. Real (- \<bar>f x\<bar>) = 0" by auto
  have "integrable (\<lambda>x. \<bar>f x\<bar>)" using assms by (rule integrable_abs)
  hence "(\<lambda>x. Real (\<bar>f x\<bar>)) \<in> borel_measurable M"
    "positive_integral (\<lambda>x. Real \<bar>f x\<bar>) \<noteq> \<omega>" unfolding integrable_def by auto
  from positive_integral_0_iff[OF this(1)] this(2)
  show ?thesis unfolding integral_def *
    by (simp add: real_of_pinfreal_eq_0)
qed

lemma (in measure_space) integral_dominated_convergence:
  assumes u: "\<And>i. integrable (u i)" and bound: "\<And>x j. x\<in>space M \<Longrightarrow> \<bar>u j x\<bar> \<le> w x"
  and w: "integrable w" "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> w x"
  and u': "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. u i x) ----> u' x"
  shows "integrable u'"
  and "(\<lambda>i. integral (\<lambda>x. \<bar>u i x - u' x\<bar>)) ----> 0" (is "?lim_diff")
  and "(\<lambda>i. integral (u i)) ----> integral u'" (is ?lim)
proof -
  { fix x j assume x: "x \<in> space M"
    from u'[OF x] have "(\<lambda>i. \<bar>u i x\<bar>) ----> \<bar>u' x\<bar>" by (rule LIMSEQ_imp_rabs)
    from LIMSEQ_le_const2[OF this]
    have "\<bar>u' x\<bar> \<le> w x" using bound[OF x] by auto }
  note u'_bound = this

  from u[unfolded integrable_def]
  have u'_borel: "u' \<in> borel_measurable M"
    using u' by (blast intro: borel_measurable_LIMSEQ[of u])

  show "integrable u'"
  proof (rule integrable_bound)
    show "integrable w" by fact
    show "u' \<in> borel_measurable M" by fact
  next
    fix x assume x: "x \<in> space M"
    thus "0 \<le> w x" by fact
    show "\<bar>u' x\<bar> \<le> w x" using u'_bound[OF x] .
  qed

  let "?diff n x" = "2 * w x - \<bar>u n x - u' x\<bar>"
  have diff: "\<And>n. integrable (\<lambda>x. \<bar>u n x - u' x\<bar>)"
    using w u `integrable u'`
    by (auto intro!: integral_add integral_diff integral_cmult integrable_abs)

  { fix j x assume x: "x \<in> space M"
    have "\<bar>u j x - u' x\<bar> \<le> \<bar>u j x\<bar> + \<bar>u' x\<bar>" by auto
    also have "\<dots> \<le> w x + w x"
      by (rule add_mono[OF bound[OF x] u'_bound[OF x]])
    finally have "\<bar>u j x - u' x\<bar> \<le> 2 * w x" by simp }
  note diff_less_2w = this

  have PI_diff: "\<And>m n. positive_integral (\<lambda>x. Real (?diff (m + n) x)) =
    positive_integral (\<lambda>x. Real (2 * w x)) - positive_integral (\<lambda>x. Real \<bar>u (m + n) x - u' x\<bar>)"
    using diff w diff_less_2w
    by (subst positive_integral_diff[symmetric])
       (auto simp: integrable_def intro!: positive_integral_cong)

  have "integrable (\<lambda>x. 2 * w x)"
    using w by (auto intro: integral_cmult)
  hence I2w_fin: "positive_integral (\<lambda>x. Real (2 * w x)) \<noteq> \<omega>" and
    borel_2w: "(\<lambda>x. Real (2 * w x)) \<in> borel_measurable M"
    unfolding integrable_def by auto

  have "(INF n. SUP m. positive_integral (\<lambda>x. Real \<bar>u (m + n) x - u' x\<bar>)) = 0" (is "?lim_SUP = 0")
  proof cases
    assume eq_0: "positive_integral (\<lambda>x. Real (2 * w x)) = 0"
    have "\<And>i. positive_integral (\<lambda>x. Real \<bar>u i x - u' x\<bar>) \<le> positive_integral (\<lambda>x. Real (2 * w x))"
    proof (rule positive_integral_mono)
      fix i x assume "x \<in> space M" from diff_less_2w[OF this, of i]
      show "Real \<bar>u i x - u' x\<bar> \<le> Real (2 * w x)" by auto
    qed
    hence "\<And>i. positive_integral (\<lambda>x. Real \<bar>u i x - u' x\<bar>) = 0" using eq_0 by auto
    thus ?thesis by simp
  next
    assume neq_0: "positive_integral (\<lambda>x. Real (2 * w x)) \<noteq> 0"
    have "positive_integral (\<lambda>x. Real (2 * w x)) = positive_integral (SUP n. INF m. (\<lambda>x. Real (?diff (m + n) x)))"
    proof (rule positive_integral_cong, unfold SUPR_fun_expand INFI_fun_expand, subst add_commute)
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
    also have "\<dots> \<le> (SUP n. INF m. positive_integral (\<lambda>x. Real (?diff (m + n) x)))"
      using u'_borel w u unfolding integrable_def
      by (auto intro!: positive_integral_lim_INF)
    also have "\<dots> = positive_integral (\<lambda>x. Real (2 * w x)) -
        (INF n. SUP m. positive_integral (\<lambda>x. Real \<bar>u (m + n) x - u' x\<bar>))"
      unfolding PI_diff pinfreal_INF_minus[OF I2w_fin] pinfreal_SUP_minus ..
    finally show ?thesis using neq_0 I2w_fin by (rule pinfreal_le_minus_imp_0)
  qed

  have [simp]: "\<And>n m x. Real (- \<bar>u (m + n) x - u' x\<bar>) = 0" by auto

  have [simp]: "\<And>n m. positive_integral (\<lambda>x. Real \<bar>u (m + n) x - u' x\<bar>) =
    Real (integral (\<lambda>x. \<bar>u (n + m) x - u' x\<bar>))"
    using diff by (subst add_commute) (simp add: integral_def integrable_def Real_real)

  have "(SUP n. INF m. positive_integral (\<lambda>x. Real \<bar>u (m + n) x - u' x\<bar>)) \<le> ?lim_SUP"
    (is "?lim_INF \<le> _") by (subst (1 2) add_commute) (rule lim_INF_le_lim_SUP)
  hence "?lim_INF = Real 0" "?lim_SUP = Real 0" using `?lim_SUP = 0` by auto
  thus ?lim_diff using diff by (auto intro!: integral_positive lim_INF_eq_lim_SUP)

  show ?lim
  proof (rule LIMSEQ_I)
    fix r :: real assume "0 < r"
    from LIMSEQ_D[OF `?lim_diff` this]
    obtain N where N: "\<And>n. N \<le> n \<Longrightarrow> integral (\<lambda>x. \<bar>u n x - u' x\<bar>) < r"
      using diff by (auto simp: integral_positive)

    show "\<exists>N. \<forall>n\<ge>N. norm (integral (u n) - integral u') < r"
    proof (safe intro!: exI[of _ N])
      fix n assume "N \<le> n"
      have "\<bar>integral (u n) - integral u'\<bar> = \<bar>integral (\<lambda>x. u n x - u' x)\<bar>"
        using u `integrable u'` by (auto simp: integral_diff)
      also have "\<dots> \<le> integral (\<lambda>x. \<bar>u n x - u' x\<bar>)" using u `integrable u'`
        by (rule_tac integral_triangle_inequality) (auto intro!: integral_diff)
      also note N[OF `N \<le> n`]
      finally show "norm (integral (u n) - integral u') < r" by simp
    qed
  qed
qed

lemma (in measure_space) integral_sums:
  assumes borel: "\<And>i. integrable (f i)"
  and summable: "\<And>x. x \<in> space M \<Longrightarrow> summable (\<lambda>i. \<bar>f i x\<bar>)"
  and sums: "summable (\<lambda>i. integral (\<lambda>x. \<bar>f i x\<bar>))"
  shows "integrable (\<lambda>x. (\<Sum>i. f i x))" (is "integrable ?S")
  and "(\<lambda>i. integral (f i)) sums integral (\<lambda>x. (\<Sum>i. f i x))" (is ?integral)
proof -
  have "\<forall>x\<in>space M. \<exists>w. (\<lambda>i. \<bar>f i x\<bar>) sums w"
    using summable unfolding summable_def by auto
  from bchoice[OF this]
  obtain w where w: "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. \<bar>f i x\<bar>) sums w x" by auto

  let "?w y" = "if y \<in> space M then w y else 0"

  obtain x where abs_sum: "(\<lambda>i. integral (\<lambda>x. \<bar>f i x\<bar>)) sums x"
    using sums unfolding summable_def ..

  have 1: "\<And>n. integrable (\<lambda>x. \<Sum>i = 0..<n. f i x)"
    using borel by (auto intro!: integral_setsum)

  { fix j x assume [simp]: "x \<in> space M"
    have "\<bar>\<Sum>i = 0..< j. f i x\<bar> \<le> (\<Sum>i = 0..< j. \<bar>f i x\<bar>)" by (rule setsum_abs)
    also have "\<dots> \<le> w x" using w[of x] series_pos_le[of "\<lambda>i. \<bar>f i x\<bar>"] unfolding sums_iff by auto
    finally have "\<bar>\<Sum>i = 0..<j. f i x\<bar> \<le> ?w x" by simp }
  note 2 = this

  have 3: "integrable ?w"
  proof (rule integral_monotone_convergence(1))
    let "?F n y" = "(\<Sum>i = 0..<n. \<bar>f i y\<bar>)"
    let "?w' n y" = "if y \<in> space M then ?F n y else 0"
    have "\<And>n. integrable (?F n)"
      using borel by (auto intro!: integral_setsum integrable_abs)
    thus "\<And>n. integrable (?w' n)" by (simp cong: integrable_cong)
    show "mono ?w'"
      by (auto simp: mono_def le_fun_def intro!: setsum_mono2)
    { fix x show "(\<lambda>n. ?w' n x) ----> ?w x"
        using w by (cases "x \<in> space M") (simp_all add: LIMSEQ_const sums_def) }
    have *: "\<And>n. integral (?w' n) = (\<Sum>i = 0..< n. integral (\<lambda>x. \<bar>f i x\<bar>))"
      using borel by (simp add: integral_setsum integrable_abs cong: integral_cong)
    from abs_sum
    show "(\<lambda>i. integral (?w' i)) ----> x" unfolding * sums_def .
  qed

  have 4: "\<And>x. x \<in> space M \<Longrightarrow> 0 \<le> ?w x" using 2[of _ 0] by simp

  from summable[THEN summable_rabs_cancel]
  have 5: "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>n. \<Sum>i = 0..<n. f i x) ----> (\<Sum>i. f i x)"
    by (auto intro: summable_sumr_LIMSEQ_suminf)

  note int = integral_dominated_convergence(1,3)[OF 1 2 3 4 5]

  from int show "integrable ?S" by simp

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
  shows "integrable f"
  and "(\<lambda>r. enum r * real (\<mu> (f -` {enum r} \<inter> space M))) sums integral f" (is ?sums)
proof -
  let "?A r" = "f -` {enum r} \<inter> space M"
  let "?F r x" = "enum r * indicator (?A r) x"
  have enum_eq: "\<And>r. enum r * real (\<mu> (?A r)) = integral (?F r)"
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

  have int_f: "integral f = integral (\<lambda>x. \<Sum>r. ?F r x)" "integrable f = integrable (\<lambda>x. \<Sum>r. ?F r x)"
    using F_sums_f by (auto intro!: integral_cong integrable_cong simp: sums_iff)

  { fix r
    have "integral (\<lambda>x. \<bar>?F r x\<bar>) = integral (\<lambda>x. \<bar>enum r\<bar> * indicator (?A r) x)"
      by (auto simp: indicator_def intro!: integral_cong)
    also have "\<dots> = \<bar>enum r\<bar> * real (\<mu> (?A r))"
      using f fin by (simp add: borel_measurable_vimage integral_cmul_indicator)
    finally have "integral (\<lambda>x. \<bar>?F r x\<bar>) = \<bar>enum r * real (\<mu> (?A r))\<bar>"
      by (simp add: abs_mult_pos real_pinfreal_pos) }
  note int_abs_F = this

  have 1: "\<And>i. integrable (\<lambda>x. ?F i x)"
    using f fin by (simp add: borel_measurable_vimage integral_cmul_indicator)

  have 2: "\<And>x. x \<in> space M \<Longrightarrow> summable (\<lambda>i. \<bar>?F i x\<bar>)"
    using F_abs_sums_f unfolding sums_iff by auto

  from integral_sums(2)[OF 1 2, unfolded int_abs_F, OF _ abs_summable]
  show ?sums unfolding enum_eq int_f by simp

  from integral_sums(1)[OF 1 2, unfolded int_abs_F, OF _ abs_summable]
  show "integrable f" unfolding int_f by simp
qed

section "Lebesgue integration on finite space"

lemma (in measure_space) integral_on_finite:
  assumes f: "f \<in> borel_measurable M" and finite: "finite (f`space M)"
  and fin: "\<And>x. x \<noteq> 0 \<Longrightarrow> \<mu> (f -` {x} \<inter> space M) \<noteq> \<omega>"
  shows "integrable f"
  and "integral (\<lambda>x. f x) =
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

  have f_eq_S: "integrable f \<longleftrightarrow> integrable ?S" "integral f = integral ?S"
    by (auto intro!: integrable_cong integral_cong simp only: f_eq)

  show "integrable f" ?integral using fin f f_eq_S
    by (simp_all add: integral_cmul_indicator borel_measurable_vimage)
qed

lemma (in finite_measure_space) simple_function_finite[simp, intro]: "simple_function f"
  unfolding simple_function_def sets_eq_Pow using finite_space by auto

lemma (in finite_measure_space) borel_measurable_finite[intro, simp]: "f \<in> borel_measurable M"
  by (auto intro: borel_measurable_simple_function)

lemma (in finite_measure_space) positive_integral_finite_eq_setsum:
  "positive_integral f = (\<Sum>x \<in> space M. f x * \<mu> {x})"
proof -
  have *: "positive_integral f = positive_integral (\<lambda>x. \<Sum>y\<in>space M. f y * indicator {y} x)"
    by (auto intro!: positive_integral_cong simp add: indicator_def if_distrib setsum_cases[OF finite_space])
  show ?thesis unfolding * using borel_measurable_finite[of f]
    by (simp add: positive_integral_setsum positive_integral_cmult_indicator sets_eq_Pow)
qed

lemma (in finite_measure_space) integral_finite_singleton:
  shows "integrable f"
  and "integral f = (\<Sum>x \<in> space M. f x * real (\<mu> {x}))" (is ?I)
proof -
  have [simp]:
    "positive_integral (\<lambda>x. Real (f x)) = (\<Sum>x \<in> space M. Real (f x) * \<mu> {x})"
    "positive_integral (\<lambda>x. Real (- f x)) = (\<Sum>x \<in> space M. Real (- f x) * \<mu> {x})"
    unfolding positive_integral_finite_eq_setsum by auto
  show "integrable f" using finite_space finite_measure
    by (simp add: setsum_\<omega> integrable_def sets_eq_Pow)
  show ?I using finite_measure
    apply (simp add: integral_def sets_eq_Pow real_of_pinfreal_setsum[symmetric]
      real_of_pinfreal_mult[symmetric] setsum_subtractf[symmetric])
    by (rule setsum_cong) (simp_all split: split_if)
qed

end
