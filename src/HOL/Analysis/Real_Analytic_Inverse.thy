section \<open>The formal-series local inverse of a real-analytic map (majorant method)\<close>

text \<open>
  For a real-analytic self-map \<open>f\<close> of a Euclidean space with \<open>f 0 = 0\<close> and
  \<open>Df(0) = id\<close>, we construct a convergent power series \<open>h\<close> with \<open>f (h y) = y\<close> near \<open>0\<close>.
  Writing \<open>f = id - \<phi>\<close>, the coefficients of \<open>h\<close> are determined degree by degree by
  \<open>h y = y + \<phi> (h y)\<close> (\<open>ra_inverse_coeffs\<close>); a bootstrap argument in the style of Gou\"ezel bounds
  them by a convergent majorant.
\<close>

theory Real_Analytic_Inverse
  imports Real_Analytic
begin

subsection \<open>A fixed enumeration of the Euclidean basis\<close>

definition ra_basis_list :: "'a::euclidean_space list" where
  "ra_basis_list = (SOME l. set l = (Basis::'a set) \<and> distinct l)"

lemma ra_basis_list:
  "set (ra_basis_list::'a::euclidean_space list) = (Basis::'a set)"
  "distinct (ra_basis_list::'a::euclidean_space list)"
proof -
  obtain l :: "'a list" where l: "set l = (Basis::'a set) \<and> distinct l"
    using finite_distinct_list[OF finite_Basis] by blast
  have "set (ra_basis_list::'a list) = (Basis::'a set) \<and> distinct (ra_basis_list::'a list)"
    unfolding ra_basis_list_def by (rule someI[of _ l]) (rule l)
  thus "set (ra_basis_list::'a list) = (Basis::'a set)"
       "distinct (ra_basis_list::'a list)" by simp_all
qed

subsection \<open>Unit multi-indices and the concrete identity coefficient family\<close>

definition ra_idx_unit :: "'a::euclidean_space \<Rightarrow> ('a \<Rightarrow> nat)" where
  "ra_idx_unit b = (\<lambda>x. if x = b then 1 else 0)"

lemma ra_idx_unit_in_ra_idx: "b \<in> Basis \<Longrightarrow> ra_idx_unit b \<in> ra_idx"
  by (auto simp: ra_idx_unit_def ra_idx_def)

lemma ra_deg_idx_unit: "b \<in> Basis \<Longrightarrow> ra_deg (ra_idx_unit b) = 1"
  by (simp add: ra_deg_def ra_idx_unit_def sum.remove[where x = b])

lemma inj_on_idx_unit: "inj_on ra_idx_unit (Basis :: 'a::euclidean_space set)"
proof (rule inj_onI)
  fix b c :: 'a
  assume "b \<in> Basis" "c \<in> Basis" and eq: "ra_idx_unit b = ra_idx_unit c"
  have h: "ra_idx_unit b b = ra_idx_unit c b" using eq by simp
  show "b = c"
  proof (rule ccontr)
    assume "b \<noteq> c"
    thus False using h by (simp add: ra_idx_unit_def)
  qed
qed

lemma ra_idx_unit_neq_idx_zero: "ra_idx_unit b \<noteq> ra_idx_zero"
proof
  assume "ra_idx_unit b = ra_idx_zero"
  hence "ra_idx_unit b b = ra_idx_zero b" by simp
  thus False by (simp add: ra_idx_unit_def ra_idx_zero_def)
qed

lemma ra_monomial_idx_unit:
  "b \<in> Basis \<Longrightarrow> ra_monomial y (ra_idx_unit b) = y \<bullet> b" for y :: "'a::euclidean_space"
proof -
  assume b: "b \<in> Basis"
  have "ra_monomial y (ra_idx_unit b) =
      (y \<bullet> b) ^ (ra_idx_unit b b) * (\<Prod>c\<in>Basis - {b}. (y \<bullet> c) ^ (ra_idx_unit b c))"
    using b by (simp add: ra_monomial_def prod.remove)
  also have "\<dots> = y \<bullet> b"
    by (simp add: ra_idx_unit_def)
  finally show ?thesis .
qed

text \<open>Classification of the degree-one multi-indices.\<close>

lemma ra_deg_one_unit:
  fixes \<alpha> :: "'a::euclidean_space \<Rightarrow> nat"
  assumes a: "\<alpha> \<in> ra_idx" and d1: "ra_deg \<alpha> = 1"
  obtains b where "b \<in> Basis" "\<alpha> = ra_idx_unit b"
proof -
  have s1: "(\<Sum>b\<in>(Basis::'a set). \<alpha> b) = 1"
    using d1 by (simp add: ra_deg_def)
  have "\<exists>b\<in>(Basis::'a set). \<alpha> b \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>b\<in>(Basis::'a set). \<alpha> b \<noteq> 0)"
    hence "(\<Sum>b\<in>(Basis::'a set). \<alpha> b) = 0" by simp
    thus False using s1 by simp
  qed
  then obtain b where b: "b \<in> Basis" and nz: "\<alpha> b \<noteq> 0" by blast
  have ble: "\<alpha> b \<le> 1"
  proof -
    have "\<alpha> b \<le> (\<Sum>c\<in>(Basis::'a set). \<alpha> c)"
      using b by (intro member_le_sum) auto
    thus ?thesis using s1 by simp
  qed
  have b1: "\<alpha> b = 1"
    using nz ble by simp
  have rest0: "(\<Sum>c\<in>Basis - {b}. \<alpha> c) = 0"
    using s1 b b1 by (simp add: sum.remove[where x = b])
  have z: "\<alpha> c = 0" if "c \<in> Basis" "c \<noteq> b" for c
  proof -
    have "\<alpha> c \<le> (\<Sum>c\<in>Basis - {b}. \<alpha> c)"
      using that by (intro member_le_sum) auto
    thus ?thesis using rest0 by simp
  qed
  have "\<alpha> = ra_idx_unit b"
  proof (rule ext)
    fix x
    show "\<alpha> x = ra_idx_unit b x"
    proof (cases "x \<in> Basis")
      case True thus ?thesis using b1 z by (auto simp: ra_idx_unit_def)
    next
      case False
      hence "\<alpha> x = 0" using a by (auto simp: ra_idx_def)
      moreover have "x \<noteq> b" using False b by blast
      ultimately show ?thesis by (simp add: ra_idx_unit_def)
    qed
  qed
  thus ?thesis using b that by blast
qed

text \<open>The concrete identity coefficient family: \<open>\<Sum>\<^sub>\<alpha> y\<^sup>\<alpha> (ra_coeff_id \<alpha>) = y\<close>.\<close>

definition ra_coeff_id :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a" where
  "ra_coeff_id = (\<lambda>\<alpha>. \<Sum>b\<in>Basis. if \<alpha> = ra_idx_unit b then b else 0)"

lemma ra_coeff_id_unit: "b \<in> Basis \<Longrightarrow> ra_coeff_id (ra_idx_unit b) = b"
proof -
  assume b: "b \<in> Basis"
  have "ra_coeff_id (ra_idx_unit b) = (\<Sum>c\<in>Basis. if c = b then c else 0)"
    unfolding ra_coeff_id_def
    by (rule sum.cong[OF refl])
       (use b inj_on_idx_unit in \<open>auto simp: inj_on_def\<close>)
  also have "\<dots> = b"
    using b by simp
  finally show ?thesis .
qed

lemma ra_coeff_id_off_units: "\<alpha> \<notin> ra_idx_unit ` Basis \<Longrightarrow> ra_coeff_id \<alpha> = 0"
  unfolding ra_coeff_id_def by (rule sum.neutral) auto

lemma ra_coeff_id_idx_zero: "ra_coeff_id ra_idx_zero = 0"
  by (rule ra_coeff_id_off_units, metis image_iff ra_idx_unit_neq_idx_zero)

lemma ra_coeff_id_deg: "ra_coeff_id \<alpha> \<noteq> 0 \<Longrightarrow> ra_deg \<alpha> = 1"
proof -
  assume nz: "ra_coeff_id \<alpha> \<noteq> 0"
  have "\<alpha> \<in> ra_idx_unit ` Basis"
    using nz ra_coeff_id_off_units by blast
  then obtain b where "b \<in> Basis" "\<alpha> = ra_idx_unit b" by blast
  thus "ra_deg \<alpha> = 1" by (simp add: ra_deg_idx_unit)
qed

lemma ra_coeff_id_series:
  fixes y :: "'a::euclidean_space"
  shows "((\<lambda>\<alpha>. ra_monomial y \<alpha> *\<^sub>R ra_coeff_id \<alpha>) has_sum y) ra_idx"
proof (rule has_sum_finite_neutralI)
  show "finite (ra_idx_unit ` (Basis :: 'a set))"
    by simp
  show "ra_idx_unit ` (Basis :: 'a set) \<subseteq> ra_idx"
    using ra_idx_unit_in_ra_idx by blast
  have "(\<Sum>\<alpha>\<in>ra_idx_unit ` Basis. ra_monomial y \<alpha> *\<^sub>R ra_coeff_id \<alpha>) =
      (\<Sum>b\<in>Basis. ra_monomial y (ra_idx_unit b) *\<^sub>R ra_coeff_id (ra_idx_unit b))"
    by (rule sum.reindex_cong[where l = ra_idx_unit, OF inj_on_idx_unit refl]) simp
  also have "\<dots> = (\<Sum>b\<in>Basis. (y \<bullet> b) *\<^sub>R b)"
    by (rule sum.cong[OF refl]) (simp add: ra_monomial_idx_unit ra_coeff_id_unit)
  also have "\<dots> = y"
    by (simp add: euclidean_representation)
  finally show "y = (\<Sum>\<alpha>\<in>ra_idx_unit ` Basis. ra_monomial y \<alpha> *\<^sub>R ra_coeff_id \<alpha>)"
    by simp
  show "\<And>\<alpha>. \<alpha> \<in> ra_idx - ra_idx_unit ` Basis \<Longrightarrow> ra_monomial y \<alpha> *\<^sub>R ra_coeff_id \<alpha> = 0"
    by (simp add: ra_coeff_id_off_units)
qed

lemma norm_coeff_id_le: "norm (ra_coeff_id \<alpha>) \<le> 1"
proof (cases "\<alpha> \<in> ra_idx_unit ` Basis")
  case True
  then obtain b where b: "b \<in> Basis" and e: "\<alpha> = ra_idx_unit b" by blast
  show ?thesis using b by (simp add: e ra_coeff_id_unit)
next
  case False
  thus ?thesis by (simp add: ra_coeff_id_off_units)
qed

subsection \<open>Cauchy-product support helpers\<close>

lemma ra_idx_below_ra_idx: "\<alpha> \<in> ra_idx_below \<gamma> \<Longrightarrow> \<alpha> \<in> ra_idx"
  by (simp add: ra_idx_below_def)

lemma self_in_idx_below: "\<gamma> \<in> ra_idx \<Longrightarrow> \<gamma> \<in> ra_idx_below \<gamma>"
  by (simp add: ra_idx_below_def ra_idx_le_def)

lemma ra_idx_zero_in_idx_below: "\<gamma> \<in> ra_idx \<Longrightarrow> ra_idx_zero \<in> ra_idx_below \<gamma>"
  by (simp add: ra_idx_below_def ra_idx_le_def ra_idx_zero_def ra_idx_zero_in, simp add: ra_idx_def)

lemma ra_idx_diff_idx_zero: "ra_idx_diff \<gamma> ra_idx_zero = \<gamma>"
  by (simp add: ra_idx_diff_def ra_idx_zero_def)

lemma ra_idx_diff_self: "ra_idx_diff \<gamma> \<gamma> = ra_idx_zero"
  by (simp add: ra_idx_diff_def ra_idx_zero_def)

lemma ra_idx_add_idx_diff: "\<alpha> \<in> ra_idx_below \<gamma> \<Longrightarrow> ra_idx_add \<alpha> (ra_idx_diff \<gamma> \<alpha>) = \<gamma>"
proof (rule ext)
  fix b
  assume "\<alpha> \<in> ra_idx_below \<gamma>"
  hence "\<alpha> b \<le> \<gamma> b" by (simp add: ra_idx_below_def ra_idx_le_def)
  thus "ra_idx_add \<alpha> (ra_idx_diff \<gamma> \<alpha>) b = \<gamma> b" by (simp add: ra_idx_add_def ra_idx_diff_def)
qed

lemma ra_idx_diff_idx_add: "ra_idx_diff (ra_idx_add \<alpha> \<delta>) \<alpha> = \<delta>"
  by (rule ext) (simp add: ra_idx_add_def ra_idx_diff_def)

lemma ra_deg_idx_add: "ra_deg (ra_idx_add \<alpha> \<delta>) = ra_deg \<alpha> + ra_deg \<delta>"
  by (simp add: ra_deg_def ra_idx_add_def sum.distrib)

lemma ra_idx_add_in_idx_below: "\<alpha> \<in> ra_idx \<Longrightarrow> \<alpha> \<in> ra_idx_below (ra_idx_add \<alpha> \<delta>)"
  by (simp add: ra_idx_below_def ra_idx_le_def ra_idx_add_def)

lemma ra_idx_diff_deg_eq:
  assumes "\<alpha> \<in> ra_idx_below \<gamma>" and "ra_deg (ra_idx_diff \<gamma> \<alpha>) = 0" and "\<gamma> \<in> ra_idx"
  shows "\<alpha> = \<gamma>"
proof -
  have "ra_idx_diff \<gamma> \<alpha> \<in> ra_idx" using assms(3) by (rule idx_sub)
  hence sz: "ra_idx_diff \<gamma> \<alpha> = ra_idx_zero" using assms(2) by (simp add: ra_deg_eq0_iff)
  have le: "\<gamma> b \<le> \<alpha> b" for b
  proof -
    have "ra_idx_diff \<gamma> \<alpha> b = ra_idx_zero b" using sz by simp
    thus ?thesis by (simp add: ra_idx_diff_def ra_idx_zero_def)
  qed
  have ge: "\<And>b. \<alpha> b \<le> \<gamma> b" using assms(1) by (simp add: ra_idx_below_def ra_idx_le_def)
  show ?thesis by (rule ext) (use le ge le_antisym in blast)
qed

text \<open>The unit \<open>ra_coeff_one\<close> is a two-sided identity for the Cauchy product (on \<open>ra_idx\<close>).\<close>

lemma ra_cauchy_prod_coeff_one_right: "\<gamma> \<in> ra_idx \<Longrightarrow> ra_cauchy_prod u ra_coeff_one \<gamma> = u \<gamma>"
proof -
  assume g: "\<gamma> \<in> ra_idx"
  have fin: "finite (ra_idx_below \<gamma>)" by (rule idx_lower_fin)
  have "ra_cauchy_prod u ra_coeff_one \<gamma> = (\<Sum>\<alpha>\<in>ra_idx_below \<gamma>. u \<alpha> * ra_coeff_one (ra_idx_diff \<gamma> \<alpha>))"
    by (simp add: ra_cauchy_prod_def)
  also have "\<dots> = (\<Sum>\<alpha>\<in>{\<gamma>}. u \<alpha> * ra_coeff_one (ra_idx_diff \<gamma> \<alpha>))"
  proof (rule sum.mono_neutral_right[OF fin])
    show "{\<gamma>} \<subseteq> ra_idx_below \<gamma>" using self_in_idx_below[OF g] by blast
    show "\<forall>\<alpha>\<in>ra_idx_below \<gamma> - {\<gamma>}. u \<alpha> * ra_coeff_one (ra_idx_diff \<gamma> \<alpha>) = 0"
    proof
      fix \<alpha> assume a: "\<alpha> \<in> ra_idx_below \<gamma> - {\<gamma>}"
      have "ra_idx_diff \<gamma> \<alpha> \<noteq> ra_idx_zero"
      proof
        assume "ra_idx_diff \<gamma> \<alpha> = ra_idx_zero"
        hence "ra_deg (ra_idx_diff \<gamma> \<alpha>) = 0" by (simp add: ra_deg_def ra_idx_zero_def)
        hence "\<alpha> = \<gamma>" using a g by (intro ra_idx_diff_deg_eq) auto
        thus False using a by blast
      qed
      thus "u \<alpha> * ra_coeff_one (ra_idx_diff \<gamma> \<alpha>) = 0" by (simp add: ra_coeff_one_def)
    qed
  qed
  also have "\<dots> = u \<gamma>"
    by (simp add: ra_idx_diff_self ra_coeff_one_def)
  finally show ?thesis .
qed

lemma ra_cauchy_prod_coeff_one_left: "\<gamma> \<in> ra_idx \<Longrightarrow> ra_cauchy_prod ra_coeff_one v \<gamma> = v \<gamma>"
proof -
  assume g: "\<gamma> \<in> ra_idx"
  have fin: "finite (ra_idx_below \<gamma>)" by (rule idx_lower_fin)
  have "ra_cauchy_prod ra_coeff_one v \<gamma> = (\<Sum>\<alpha>\<in>ra_idx_below \<gamma>. ra_coeff_one \<alpha> * v (ra_idx_diff \<gamma> \<alpha>))"
    by (simp add: ra_cauchy_prod_def)
  also have "\<dots> = (\<Sum>\<alpha>\<in>{ra_idx_zero}. ra_coeff_one \<alpha> * v (ra_idx_diff \<gamma> \<alpha>))"
  proof (rule sum.mono_neutral_right[OF fin])
    show "{ra_idx_zero} \<subseteq> ra_idx_below \<gamma>" using ra_idx_zero_in_idx_below[OF g] by blast
    show "\<forall>\<alpha>\<in>ra_idx_below \<gamma> - {ra_idx_zero}. ra_coeff_one \<alpha> * v (ra_idx_diff \<gamma> \<alpha>) = 0"
      by (simp add: ra_coeff_one_def)
  qed
  also have "\<dots> = v \<gamma>"
    by (simp add: ra_idx_diff_idx_zero ra_coeff_one_def)
  finally show ?thesis .
qed

subsection \<open>Valuation (vanishing below a degree) under Cauchy products\<close>

text \<open>\<open>ra_vanish_below u p\<close>: the scalar family \<open>u\<close> has no coefficients of degree \<open>< p\<close>.\<close>

definition ra_vanish_below :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "ra_vanish_below u p \<longleftrightarrow> (\<forall>\<alpha>. \<alpha> \<in> ra_idx \<longrightarrow> ra_deg \<alpha> < p \<longrightarrow> u \<alpha> = 0)"

lemma ra_vanish_below_0: "ra_vanish_below u 0"
  by (simp add: ra_vanish_below_def)

lemma ra_vanish_below_mono: "ra_vanish_below u p \<Longrightarrow> q \<le> p \<Longrightarrow> ra_vanish_below u q"
  by (auto simp: ra_vanish_below_def)

lemma ra_cauchy_prod_vanish:
  assumes u: "ra_vanish_below u p" and v: "ra_vanish_below v q"
  shows "ra_vanish_below (ra_cauchy_prod u v) (p + q)"
  unfolding ra_vanish_below_def
proof (intro allI impI)
  fix \<gamma> :: "'a \<Rightarrow> nat"
  assume g: "\<gamma> \<in> ra_idx" and dg: "ra_deg \<gamma> < p + q"
  have "ra_cauchy_prod u v \<gamma> = (\<Sum>\<alpha>\<in>ra_idx_below \<gamma>. u \<alpha> * v (ra_idx_diff \<gamma> \<alpha>))"
    by (simp add: ra_cauchy_prod_def)
  also have "\<dots> = 0"
  proof (rule sum.neutral, rule ballI)
    fix \<alpha> assume a: "\<alpha> \<in> ra_idx_below \<gamma>"
    have ara: "\<alpha> \<in> ra_idx" using a by (rule ra_idx_below_ra_idx)
    have dra: "ra_idx_diff \<gamma> \<alpha> \<in> ra_idx" using g by (rule idx_sub)
    have split: "ra_deg \<gamma> = ra_deg \<alpha> + ra_deg (ra_idx_diff \<gamma> \<alpha>)"
      using a by (rule ra_deg_split)
    have "ra_deg \<alpha> < p \<or> ra_deg (ra_idx_diff \<gamma> \<alpha>) < q"
      using dg split by linarith
    thus "u \<alpha> * v (ra_idx_diff \<gamma> \<alpha>) = 0"
      using u v ara dra by (auto simp: ra_vanish_below_def)
  qed
  finally show "ra_cauchy_prod u v \<gamma> = 0" .
qed

lemma ra_cauchy_pow_vanish:
  assumes u: "ra_vanish_below u 1"
  shows "ra_vanish_below (ra_cauchy_pow u n) n"
proof (induction n)
  case 0
  show ?case by (simp add: ra_cauchy_pow_0 ra_vanish_below_0)
next
  case (Suc n)
  have "ra_vanish_below (ra_cauchy_prod u (ra_cauchy_pow u n)) (1 + n)"
    by (rule ra_cauchy_prod_vanish[OF u Suc.IH])
  thus ?case by (simp add: ra_cauchy_pow_Suc)
qed

subsection \<open>Degree locality of Cauchy products and powers\<close>

text \<open>If two pairs of families agree up to certain degrees (and have the stated
  valuations), their Cauchy products agree up to the corresponding degree.\<close>

lemma ra_cauchy_prod_local:
  fixes u u' v v' :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  assumes up: "ra_vanish_below u p" and up': "ra_vanish_below u' p"
    and vq: "ra_vanish_below v q" and vq': "ra_vanish_below v' q"
    and uu': "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> Du \<Longrightarrow> u \<alpha> = u' \<alpha>"
    and vv': "\<And>\<delta>. \<delta> \<in> ra_idx \<Longrightarrow> ra_deg \<delta> \<le> Dv \<Longrightarrow> v \<delta> = v' \<delta>"
    and g: "\<gamma> \<in> ra_idx" and dgu: "ra_deg \<gamma> \<le> Du + q" and dgv: "ra_deg \<gamma> \<le> Dv + p"
  shows "ra_cauchy_prod u v \<gamma> = ra_cauchy_prod u' v' \<gamma>"
proof -
  have "(\<Sum>\<alpha>\<in>ra_idx_below \<gamma>. u \<alpha> * v (ra_idx_diff \<gamma> \<alpha>)) = (\<Sum>\<alpha>\<in>ra_idx_below \<gamma>. u' \<alpha> * v' (ra_idx_diff \<gamma> \<alpha>))"
  proof (rule sum.cong[OF refl])
    fix \<alpha> assume a: "\<alpha> \<in> ra_idx_below \<gamma>"
    have ara: "\<alpha> \<in> ra_idx" using a by (rule ra_idx_below_ra_idx)
    have dra: "ra_idx_diff \<gamma> \<alpha> \<in> ra_idx" using g by (rule idx_sub)
    have split: "ra_deg \<gamma> = ra_deg \<alpha> + ra_deg (ra_idx_diff \<gamma> \<alpha>)"
      using a by (rule ra_deg_split)
    show "u \<alpha> * v (ra_idx_diff \<gamma> \<alpha>) = u' \<alpha> * v' (ra_idx_diff \<gamma> \<alpha>)"
    proof (cases "ra_deg \<alpha> < p")
      case True
      thus ?thesis
        using up up' ara by (simp add: ra_vanish_below_def)
    next
      case False
      note ap = False
      show ?thesis
      proof (cases "ra_deg (ra_idx_diff \<gamma> \<alpha>) < q")
        case True
        thus ?thesis
          using vq vq' dra by (simp add: ra_vanish_below_def)
      next
        case False
        have da: "ra_deg \<alpha> \<le> Du"
          using ap False split dgu by linarith
        have dd: "ra_deg (ra_idx_diff \<gamma> \<alpha>) \<le> Dv"
          using ap False split dgv by linarith
        show ?thesis
          using uu'[OF ara da] vv'[OF dra dd] by simp
      qed
    qed
  qed
  thus ?thesis by (simp add: ra_cauchy_prod_def)
qed

lemma ra_cauchy_pow_local:
  fixes u u' :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  assumes u1: "ra_vanish_below u 1" and u1': "ra_vanish_below u' 1"
    and uu': "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D \<Longrightarrow> u \<alpha> = u' \<alpha>"
    and n1: "1 \<le> n"
    and g: "\<gamma> \<in> ra_idx" and dg: "ra_deg \<gamma> \<le> D + n - 1"
  shows "ra_cauchy_pow u n \<gamma> = ra_cauchy_pow u' n \<gamma>"
  using n1 g dg
proof (induction n arbitrary: \<gamma>)
  case 0
  thus ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "n = 0")
    case True
    have "ra_cauchy_pow u (Suc 0) \<gamma> = ra_cauchy_prod u ra_coeff_one \<gamma>"
      by (simp add: ra_cauchy_pow_Suc ra_cauchy_pow_0)
    also have "\<dots> = u \<gamma>" using Suc.prems(2) by (rule ra_cauchy_prod_coeff_one_right)
    also have "\<dots> = u' \<gamma>"
      using Suc.prems(2,3) True by (intro uu') simp_all
    also have "\<dots> = ra_cauchy_prod u' ra_coeff_one \<gamma>"
      using Suc.prems(2) by (simp add: ra_cauchy_prod_coeff_one_right)
    also have "\<dots> = ra_cauchy_pow u' (Suc 0) \<gamma>"
      by (simp add: ra_cauchy_pow_Suc ra_cauchy_pow_0)
    finally show ?thesis using True by simp
  next
    case False
    hence n1': "1 \<le> n" by simp
    have IH: "\<And>\<delta>. \<delta> \<in> ra_idx \<Longrightarrow> ra_deg \<delta> \<le> D + n - 1 \<Longrightarrow> ra_cauchy_pow u n \<delta> = ra_cauchy_pow u' n \<delta>"
      using Suc.IH n1' by blast
    have "ra_cauchy_prod u (ra_cauchy_pow u n) \<gamma> = ra_cauchy_prod u' (ra_cauchy_pow u' n) \<gamma>"
    proof (rule ra_cauchy_prod_local[where p = 1 and q = n and Du = D and Dv = "D + n - 1"])
      show "ra_vanish_below u 1" by (rule u1)
      show "ra_vanish_below u' 1" by (rule u1')
      show "ra_vanish_below (ra_cauchy_pow u n) n" by (rule ra_cauchy_pow_vanish[OF u1])
      show "ra_vanish_below (ra_cauchy_pow u' n) n" by (rule ra_cauchy_pow_vanish[OF u1'])
      show "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D \<Longrightarrow> u \<alpha> = u' \<alpha>" by (rule uu')
      show "\<And>\<delta>. \<delta> \<in> ra_idx \<Longrightarrow> ra_deg \<delta> \<le> D + n - 1 \<Longrightarrow> ra_cauchy_pow u n \<delta> = ra_cauchy_pow u' n \<delta>"
        by (rule IH)
      show "\<gamma> \<in> ra_idx" by (rule Suc.prems(2))
      show "ra_deg \<gamma> \<le> D + n" using Suc.prems(3) n1' by simp
      show "ra_deg \<gamma> \<le> (D + n - 1) + 1" using Suc.prems(3) n1' by simp
    qed
    thus ?thesis by (simp add: ra_cauchy_pow_Suc)
  qed
qed

subsection \<open>Canonical monomial-composition coefficients along the basis list\<close>

text \<open>\<open>ra_mono_coeffs_list c \<beta> l\<close> is the coefficient family of \<open>y \<mapsto> \<Prod>b\<leftarrow>l. (H y \<bullet> b) ^ \<beta> b\<close>
  when \<open>c\<close> is one for \<open>H\<close>, built by iterated Cauchy products along \<open>l\<close>.\<close>

fun ra_mono_coeffs_list :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a list
              \<Rightarrow> (('a \<Rightarrow> nat) \<Rightarrow> real)" where
  "ra_mono_coeffs_list c \<beta> [] = ra_coeff_one"
| "ra_mono_coeffs_list c \<beta> (b # bs) = ra_cauchy_prod (ra_cauchy_pow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) (ra_mono_coeffs_list c \<beta> bs)"

lemma ra_mono_coeffs_list_series:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a" and H :: "'a \<Rightarrow> 'a"
  assumes VC: "\<And>y. dist y (0::'a) < r \<Longrightarrow>
                 ((\<lambda>\<alpha>. ra_monomial y \<alpha> *\<^sub>R c \<alpha>) has_sum H y) ra_idx"
  shows "ra_series_on (0::'a) r (ra_mono_coeffs_list c \<beta> l) (\<lambda>y. \<Prod>b\<leftarrow>l. (H y \<bullet> b) ^ \<beta> b)"
proof (induction l)
  case Nil
  show ?case using ra_series_on_one[of "0::'a" r] by simp
next
  case (Cons b bs)
  have VC': "\<And>y. dist y (0::'a) < r \<Longrightarrow>
               ((\<lambda>\<alpha>. ra_monomial (y - 0) \<alpha> *\<^sub>R c \<alpha>) has_sum H y) ra_idx"
    using VC by simp
  have comp: "ra_series_on (0::'a) r (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<lambda>y. H y \<bullet> b)"
    by (rule ra_series_on_component[OF VC'])
  have pow: "ra_series_on (0::'a) r (ra_cauchy_pow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) (\<lambda>y. (H y \<bullet> b) ^ \<beta> b)"
    by (rule ra_series_on_power[OF comp])
  have "ra_series_on (0::'a) r (ra_cauchy_prod (ra_cauchy_pow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) (ra_mono_coeffs_list c \<beta> bs))
          (\<lambda>y. (H y \<bullet> b) ^ \<beta> b * (\<Prod>b'\<leftarrow>bs. (H y \<bullet> b') ^ \<beta> b'))"
    by (rule ra_series_on_mult[OF pow Cons.IH])
  thus ?case by simp
qed

lemma ra_mono_coeffs_list_vanish:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes c0: "c ra_idx_zero = 0"
  shows "ra_vanish_below (ra_mono_coeffs_list c \<beta> l) (sum_list (map \<beta> l))"
proof (induction l)
  case Nil
  show ?case by (simp add: ra_vanish_below_0)
next
  case (Cons b bs)
  have comp1: "ra_vanish_below (\<lambda>\<alpha>. c \<alpha> \<bullet> b) 1"
    unfolding ra_vanish_below_def
  proof (intro allI impI)
    fix \<alpha> :: "'a \<Rightarrow> nat"
    assume "\<alpha> \<in> ra_idx" "ra_deg \<alpha> < 1"
    hence "\<alpha> = ra_idx_zero" by (simp add: ra_deg_eq0_iff)
    thus "c \<alpha> \<bullet> b = 0" by (simp add: c0)
  qed
  have "ra_vanish_below (ra_cauchy_prod (ra_cauchy_pow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) (ra_mono_coeffs_list c \<beta> bs))
          (\<beta> b + sum_list (map \<beta> bs))"
    by (rule ra_cauchy_prod_vanish[OF ra_cauchy_pow_vanish[OF comp1] Cons.IH])
  thus ?case by simp
qed

lemma ra_mono_coeffs_list_indep:
  fixes c c' :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes z: "sum_list (map \<beta> l) = 0" and g: "\<gamma> \<in> ra_idx"
  shows "ra_mono_coeffs_list c \<beta> l \<gamma> = ra_mono_coeffs_list c' \<beta> l \<gamma>"
  using z g
proof (induction l arbitrary: \<gamma>)
  case Nil
  show ?case by simp
next
  case (Cons b bs)
  have b0: "\<beta> b = 0" and bs0: "sum_list (map \<beta> bs) = 0"
    using Cons.prems(1) by simp_all
  have "ra_mono_coeffs_list c \<beta> (b # bs) \<gamma> = ra_cauchy_prod ra_coeff_one (ra_mono_coeffs_list c \<beta> bs) \<gamma>"
    by (simp add: b0 ra_cauchy_pow_0)
  also have "\<dots> = ra_mono_coeffs_list c \<beta> bs \<gamma>"
    using Cons.prems(2) by (rule ra_cauchy_prod_coeff_one_left)
  also have "\<dots> = ra_mono_coeffs_list c' \<beta> bs \<gamma>"
    using bs0 Cons.prems(2) by (rule Cons.IH)
  also have "\<dots> = ra_cauchy_prod ra_coeff_one (ra_mono_coeffs_list c' \<beta> bs) \<gamma>"
    using Cons.prems(2) by (simp add: ra_cauchy_prod_coeff_one_left)
  also have "\<dots> = ra_mono_coeffs_list c' \<beta> (b # bs) \<gamma>"
    by (simp add: b0 ra_cauchy_pow_0)
  finally show ?case .
qed

lemma ra_mono_coeffs_list_local:
  fixes c c' :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes c0: "c ra_idx_zero = 0" and c0': "c' ra_idx_zero = 0"
    and agree: "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D \<Longrightarrow> c \<alpha> = c' \<alpha>"
    and g: "\<gamma> \<in> ra_idx"
    and pos: "1 \<le> sum_list (map \<beta> l)"
    and dg: "ra_deg \<gamma> \<le> D + sum_list (map \<beta> l) - 1"
  shows "ra_mono_coeffs_list c \<beta> l \<gamma> = ra_mono_coeffs_list c' \<beta> l \<gamma>"
  using pos dg g
proof (induction l arbitrary: \<gamma>)
  case Nil
  thus ?case by simp
next
  case (Cons b bs)
  define u where "u = (\<lambda>\<alpha>. c \<alpha> \<bullet> b)"
  define u' where "u' = (\<lambda>\<alpha>. c' \<alpha> \<bullet> b)"
  have u1: "ra_vanish_below u 1"
    unfolding ra_vanish_below_def u_def
  proof (intro allI impI)
    fix \<alpha> :: "'a \<Rightarrow> nat"
    assume "\<alpha> \<in> ra_idx" "ra_deg \<alpha> < 1"
    hence "\<alpha> = ra_idx_zero" by (simp add: ra_deg_eq0_iff)
    thus "c \<alpha> \<bullet> b = 0" by (simp add: c0)
  qed
  have u1': "ra_vanish_below u' 1"
    unfolding ra_vanish_below_def u'_def
  proof (intro allI impI)
    fix \<alpha> :: "'a \<Rightarrow> nat"
    assume "\<alpha> \<in> ra_idx" "ra_deg \<alpha> < 1"
    hence "\<alpha> = ra_idx_zero" by (simp add: ra_deg_eq0_iff)
    thus "c' \<alpha> \<bullet> b = 0" by (simp add: c0')
  qed
  have uu': "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D \<Longrightarrow> u \<alpha> = u' \<alpha>"
    unfolding u_def u'_def using agree by simp
  define vbs where "vbs = sum_list (map \<beta> bs)"
  show ?case
  proof (cases "\<beta> b = 0")
    case True
    have pos_bs: "1 \<le> vbs"
      using Cons.prems(1) True by (simp add: vbs_def)
    have dg_bs: "ra_deg \<gamma> \<le> D + vbs - 1"
      using Cons.prems(2) True by (simp add: vbs_def)
    have "ra_mono_coeffs_list c \<beta> (b # bs) \<gamma> = ra_cauchy_prod ra_coeff_one (ra_mono_coeffs_list c \<beta> bs) \<gamma>"
      by (simp add: True ra_cauchy_pow_0)
    also have "\<dots> = ra_mono_coeffs_list c \<beta> bs \<gamma>"
      using Cons.prems(3) by (rule ra_cauchy_prod_coeff_one_left)
    also have "\<dots> = ra_mono_coeffs_list c' \<beta> bs \<gamma>"
      using pos_bs dg_bs Cons.prems(3) unfolding vbs_def by (rule Cons.IH)
    also have "\<dots> = ra_cauchy_prod ra_coeff_one (ra_mono_coeffs_list c' \<beta> bs) \<gamma>"
      using Cons.prems(3) by (simp add: ra_cauchy_prod_coeff_one_left)
    also have "\<dots> = ra_mono_coeffs_list c' \<beta> (b # bs) \<gamma>"
      by (simp add: True ra_cauchy_pow_0)
    finally show ?thesis .
  next
    case False
    hence bb1: "1 \<le> \<beta> b" by simp
    show ?thesis
    proof (cases "vbs = 0")
      case True
      \<comment> \<open>the tail is \<open>c\<close>-independent; only the head power carries locality\<close>
      have tail_eq: "\<And>\<delta>. \<delta> \<in> ra_idx \<Longrightarrow> ra_mono_coeffs_list c \<beta> bs \<delta> = ra_mono_coeffs_list c' \<beta> bs \<delta>"
        using True unfolding vbs_def by (intro ra_mono_coeffs_list_indep)
      have "ra_cauchy_prod (ra_cauchy_pow u (\<beta> b)) (ra_mono_coeffs_list c \<beta> bs) \<gamma>
              = ra_cauchy_prod (ra_cauchy_pow u' (\<beta> b)) (ra_mono_coeffs_list c' \<beta> bs) \<gamma>"
      proof (rule ra_cauchy_prod_local[where p = "\<beta> b" and q = 0
              and Du = "D + \<beta> b - 1" and Dv = "ra_deg \<gamma>"])
        show "ra_vanish_below (ra_cauchy_pow u (\<beta> b)) (\<beta> b)" by (rule ra_cauchy_pow_vanish[OF u1])
        show "ra_vanish_below (ra_cauchy_pow u' (\<beta> b)) (\<beta> b)" by (rule ra_cauchy_pow_vanish[OF u1'])
        show "ra_vanish_below (ra_mono_coeffs_list c \<beta> bs) 0" by (rule ra_vanish_below_0)
        show "ra_vanish_below (ra_mono_coeffs_list c' \<beta> bs) 0" by (rule ra_vanish_below_0)
        show "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D + \<beta> b - 1 \<Longrightarrow>
                ra_cauchy_pow u (\<beta> b) \<alpha> = ra_cauchy_pow u' (\<beta> b) \<alpha>"
          by (rule ra_cauchy_pow_local[OF u1 u1' uu' bb1])
        show "\<And>\<delta>. \<delta> \<in> ra_idx \<Longrightarrow> ra_deg \<delta> \<le> ra_deg \<gamma> \<Longrightarrow>
                ra_mono_coeffs_list c \<beta> bs \<delta> = ra_mono_coeffs_list c' \<beta> bs \<delta>"
          using tail_eq by blast
        show "\<gamma> \<in> ra_idx" by (rule Cons.prems(3))
        show "ra_deg \<gamma> \<le> (D + \<beta> b - 1) + 0"
          using Cons.prems(2) True
          using vbs_def by fastforce
        show "ra_deg \<gamma> \<le> ra_deg \<gamma> + \<beta> b" by simp
      qed
      thus ?thesis unfolding u_def u'_def by simp
    next
      case False
      hence vbs1: "1 \<le> vbs" by simp
      have "ra_cauchy_prod (ra_cauchy_pow u (\<beta> b)) (ra_mono_coeffs_list c \<beta> bs) \<gamma>
              = ra_cauchy_prod (ra_cauchy_pow u' (\<beta> b)) (ra_mono_coeffs_list c' \<beta> bs) \<gamma>"
      proof (rule ra_cauchy_prod_local[where p = "\<beta> b" and q = vbs
              and Du = "D + \<beta> b - 1" and Dv = "D + vbs - 1"])
        show "ra_vanish_below (ra_cauchy_pow u (\<beta> b)) (\<beta> b)" by (rule ra_cauchy_pow_vanish[OF u1])
        show "ra_vanish_below (ra_cauchy_pow u' (\<beta> b)) (\<beta> b)" by (rule ra_cauchy_pow_vanish[OF u1'])
        show "ra_vanish_below (ra_mono_coeffs_list c \<beta> bs) vbs"
          unfolding vbs_def
          by (simp add: c0 ra_mono_coeffs_list_vanish)
        show "ra_vanish_below (ra_mono_coeffs_list c' \<beta> bs) vbs"
          unfolding vbs_def
          by (simp add: c0' ra_mono_coeffs_list_vanish)
        show "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D + \<beta> b - 1 \<Longrightarrow>
                ra_cauchy_pow u (\<beta> b) \<alpha> = ra_cauchy_pow u' (\<beta> b) \<alpha>"
          by (rule ra_cauchy_pow_local[OF u1 u1' uu' bb1])
        show "\<And>\<delta>. \<delta> \<in> ra_idx \<Longrightarrow> ra_deg \<delta> \<le> D + vbs - 1 \<Longrightarrow>
                ra_mono_coeffs_list c \<beta> bs \<delta> = ra_mono_coeffs_list c' \<beta> bs \<delta>"
          using Cons.IH vbs1 unfolding vbs_def by blast
        show "\<gamma> \<in> ra_idx" by (rule Cons.prems(3))
        show "ra_deg \<gamma> \<le> (D + \<beta> b - 1) + vbs"
          using Cons.prems(2) bb1 by (simp add: vbs_def)
        show "ra_deg \<gamma> \<le> (D + vbs - 1) + \<beta> b"
          using Cons.prems(2) vbs1 by (simp add: vbs_def)
      qed
      thus ?thesis unfolding u_def u'_def by simp
    qed
  qed
qed

text \<open>The packaged composition coefficients: canonical coefficients of
  \<open>y \<mapsto> ra_monomial (H y) \<beta>\<close>.\<close>

definition ra_mono_coeffs :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> nat)
                         \<Rightarrow> (('a \<Rightarrow> nat) \<Rightarrow> real)" where
  "ra_mono_coeffs c \<beta> = ra_mono_coeffs_list c \<beta> ra_basis_list"

lemma sum_list_basis_ra_deg:
  "sum_list (map \<beta> (ra_basis_list::'a::euclidean_space list)) = ra_deg \<beta>"
proof -
  have "sum_list (map \<beta> (ra_basis_list::'a list)) = (\<Sum>b\<in>set (ra_basis_list::'a list). \<beta> b)"
    by (rule sum_list_distinct_conv_sum_set[OF ra_basis_list(2)])
  also have "\<dots> = (\<Sum>b\<in>(Basis::'a set). \<beta> b)"
    by (simp add: ra_basis_list(1))
  finally show ?thesis by (simp add: ra_deg_def)
qed

lemma ra_mono_coeffs_series:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a" and H :: "'a \<Rightarrow> 'a"
  assumes VC: "\<And>y. dist y (0::'a) < r \<Longrightarrow>
                 ((\<lambda>\<alpha>. ra_monomial y \<alpha> *\<^sub>R c \<alpha>) has_sum H y) ra_idx"
  shows "ra_series_on (0::'a) r (ra_mono_coeffs c \<beta>) (\<lambda>y. ra_monomial (H y) \<beta>)"
proof -
  have base: "ra_series_on (0::'a) r (ra_mono_coeffs_list c \<beta> ra_basis_list)
                (\<lambda>y. \<Prod>b\<leftarrow>(ra_basis_list::'a list). (H y \<bullet> b) ^ \<beta> b)"
    by (rule ra_mono_coeffs_list_series[OF VC])
  have eq: "(\<Prod>b\<leftarrow>(ra_basis_list::'a list). (H y \<bullet> b) ^ \<beta> b) = ra_monomial (H y) \<beta>" for y
  proof -
    have "ra_monomial (H y) \<beta> = (\<Prod>b\<in>set (ra_basis_list::'a list). (H y \<bullet> b) ^ \<beta> b)"
      by (simp add: ra_monomial_def ra_basis_list(1))
    also have "\<dots> = (\<Prod>b\<leftarrow>(ra_basis_list::'a list). (H y \<bullet> b) ^ \<beta> b)"
      by (rule prod.distinct_set_conv_list[OF ra_basis_list(2)])
    finally show ?thesis by simp
  qed
  show ?thesis
    using base unfolding ra_series_on_def eq ra_mono_coeffs_def by simp
qed

lemma ra_mono_coeffs_vanish:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes c0: "c ra_idx_zero = 0"
  shows "ra_vanish_below (ra_mono_coeffs c \<beta>) (ra_deg \<beta>)"
  unfolding ra_mono_coeffs_def
  by (metis c0 ra_mono_coeffs_list_vanish sum_list_basis_ra_deg)

lemma ra_mono_coeffs_zero_below_degree:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes c0: "c ra_idx_zero = 0"
    and g: "\<gamma> \<in> ra_idx"
    and lt: "ra_deg \<gamma> < ra_deg \<beta>"
  shows "ra_mono_coeffs c \<beta> \<gamma> = 0"
  by (meson c0 g lt ra_mono_coeffs_vanish ra_vanish_below_def)


lemma ra_mono_coeffs_local:
  fixes c c' :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes c0: "c ra_idx_zero = 0" and c0': "c' ra_idx_zero = 0"
    and agree: "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D \<Longrightarrow> c \<alpha> = c' \<alpha>"
    and g: "\<gamma> \<in> ra_idx"
    and pos: "1 \<le> ra_deg \<beta>"
    and dg: "ra_deg \<gamma> \<le> D + ra_deg \<beta> - 1"
  shows "ra_mono_coeffs c \<beta> \<gamma> = ra_mono_coeffs c' \<beta> \<gamma>"
  unfolding ra_mono_coeffs_def
  by (metis agree c0 c0' dg g ra_mono_coeffs_list_local pos sum_list_basis_ra_deg)


subsection \<open>Convolution algebra on scalar degree sequences\<close>

definition ra_seq_conv :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real)" where
  "ra_seq_conv A B = (\<lambda>d. \<Sum>i\<le>d. A i * B (d - i))"

definition ra_seq_delta :: "nat \<Rightarrow> real" where
  "ra_seq_delta = (\<lambda>d. if d = 0 then 1 else 0)"

primrec ra_seq_conv_pow :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> real)" where
  "ra_seq_conv_pow A 0 = ra_seq_delta"
| "ra_seq_conv_pow A (Suc k) = ra_seq_conv A (ra_seq_conv_pow A k)"

lemma ra_seq_conv_delta_right: "ra_seq_conv A ra_seq_delta = A"
proof (rule ext)
  fix d :: nat
  have "ra_seq_conv A ra_seq_delta d = (\<Sum>i\<le>d. if i = d then A d else 0)"
    unfolding ra_seq_conv_def ra_seq_delta_def
    by (rule sum.cong[OF refl]) auto
  also have "\<dots> = A d"
    by (simp add: if_distrib)
  finally show "ra_seq_conv A ra_seq_delta d = A d" .
qed

lemma ra_seq_conv_delta_left: "ra_seq_conv ra_seq_delta B = B"
proof (rule ext)
  fix d :: nat
  have "ra_seq_conv ra_seq_delta B d = (\<Sum>i\<le>d. if i = 0 then B d else 0)"
    unfolding ra_seq_conv_def ra_seq_delta_def
    by (rule sum.cong[OF refl]) auto
  also have "\<dots> = B d"
    by simp
  finally show "ra_seq_conv ra_seq_delta B d = B d" .
qed

lemma ra_seq_conv_nonneg:
  assumes "\<And>i. 0 \<le> A i" and "\<And>i. 0 \<le> B i"
  shows "0 \<le> ra_seq_conv A B d"
  unfolding ra_seq_conv_def by (intro sum_nonneg mult_nonneg_nonneg assms)

lemma ra_seq_delta_nonneg: "0 \<le> ra_seq_delta d"
  by (simp add: ra_seq_delta_def)

lemma ra_seq_conv_pow_nonneg:
  assumes "\<And>i. 0 \<le> A i"
  shows "0 \<le> ra_seq_conv_pow A k d"
proof (induction k arbitrary: d)
  case 0
  show ?case by (simp add: ra_seq_delta_nonneg)
next
  case (Suc k)
  show ?case by (simp add: ra_seq_conv_nonneg[OF assms Suc.IH])
qed

lemma ra_seq_conv_mono:
  assumes AA': "\<And>i. A i \<le> A' i" and BB': "\<And>i. B i \<le> B' i"
    and Ann: "\<And>i. 0 \<le> A i" and Bnn': "\<And>i. 0 \<le> B' i"
  shows "ra_seq_conv A B d \<le> ra_seq_conv A' B' d"
  unfolding ra_seq_conv_def
  by (rule sum_mono) (meson AA' Ann BB' Bnn' mult_left_mono mult_right_mono order_trans)


lemma ra_seq_conv_pow_mono_base:
  assumes AA': "\<And>i. A i \<le> A' i" and Ann: "\<And>i. 0 \<le> A i"
  shows "ra_seq_conv_pow A k d \<le> ra_seq_conv_pow A' k d"
proof (induction k arbitrary: d)
  case 0
  show ?case by simp
next
  case (Suc k)
  have Ann': "\<And>i. 0 \<le> A' i"
    using Ann AA' order_trans by blast
  show ?case
    unfolding ra_seq_conv_pow.simps
    by (rule ra_seq_conv_mono[OF AA' Suc.IH Ann ra_seq_conv_pow_nonneg[OF Ann']])
qed

lemma ra_seq_conv_assoc: "ra_seq_conv (ra_seq_conv A B) C = ra_seq_conv A (ra_seq_conv B C)"
proof (rule ext)
  fix d :: nat
  have "ra_seq_conv (ra_seq_conv A B) C d = (\<Sum>m\<le>d. (\<Sum>i\<le>m. A i * B (m - i)) * C (d - m))"
    by (simp add: ra_seq_conv_def)
  also have "\<dots> = (\<Sum>m\<le>d. \<Sum>i\<le>m. A i * B (m - i) * C (d - m))"
    by (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>i\<le>d. \<Sum>e\<le>d - i. A i * B e * C (d - (i + e)))"
    using sum_triangle_exchange[of "\<lambda>i e. A i * B e * C (d - (i + e))" d]
    by (simp add: algebra_simps)
  also have "\<dots> = (\<Sum>i\<le>d. A i * (\<Sum>e\<le>d - i. B e * C (d - i - e)))"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = ra_seq_conv A (ra_seq_conv B C) d"
    by (simp add: ra_seq_conv_def)
  finally show "ra_seq_conv (ra_seq_conv A B) C d = ra_seq_conv A (ra_seq_conv B C) d" .
qed

lemma ra_seq_conv_pow_add: "ra_seq_conv (ra_seq_conv_pow A m) (ra_seq_conv_pow A k) = ra_seq_conv_pow A (m + k)"
proof (induction m)
  case 0
  show ?case by (simp add: ra_seq_conv_delta_left)
next
  case (Suc m)
  have "ra_seq_conv (ra_seq_conv_pow A (Suc m)) (ra_seq_conv_pow A k)
          = ra_seq_conv A (ra_seq_conv (ra_seq_conv_pow A m) (ra_seq_conv_pow A k))"
    by (simp add: ra_seq_conv_assoc)
  also have "\<dots> = ra_seq_conv A (ra_seq_conv_pow A (m + k))"
    by (simp add: Suc.IH)
  also have "\<dots> = ra_seq_conv_pow A (Suc m + k)"
    by simp
  finally show ?case .
qed

lemma ra_seq_conv_pow_vanish:
  assumes A0: "A 0 = 0" and dk: "d < k"
  shows "ra_seq_conv_pow A k d = 0"
  using dk
proof (induction k arbitrary: d)
  case 0
  thus ?case by simp
next
  case (Suc k)
  have "ra_seq_conv A (ra_seq_conv_pow A k) d = (\<Sum>i\<le>d. A i * ra_seq_conv_pow A k (d - i))"
    by (simp add: ra_seq_conv_def)
  also have "\<dots> = 0"
  proof (rule sum.neutral, rule ballI)
    fix i assume i: "i \<in> {..d}"
    show "A i * ra_seq_conv_pow A k (d - i) = 0"
    proof (cases "i = 0")
      case True
      thus ?thesis by (simp add: A0)
    next
      case False
      have "d - i < k" using i False Suc.prems by simp
      thus ?thesis by (simp add: Suc.IH)
    qed
  qed
  finally show ?case by simp
qed

text \<open>The key partial-sum estimate: a weighted partial sum of a convolution power is
  dominated by the corresponding power of a (shorter) weighted partial sum.\<close>

lemma ra_seq_conv_pow_partial_sum_le:
  fixes A :: "nat \<Rightarrow> real" and x :: real
  assumes Ann: "\<And>i. 0 \<le> A i" and A0: "A 0 = 0" and x0: "0 \<le> x" and k1: "1 \<le> k"
  shows "(\<Sum>d\<le>N. ra_seq_conv_pow A k d * x ^ d) \<le> (\<Sum>i=1..N + 1 - k. A i * x ^ i) ^ k"
  using k1
proof (induction k arbitrary: N)
  case 0
  thus ?case by simp
next
  case (Suc k)
  show ?case
  proof (cases "k = 0")
    case True
    have "(\<Sum>d\<le>N. ra_seq_conv_pow A (Suc 0) d * x ^ d) = (\<Sum>d\<le>N. A d * x ^ d)"
      by (simp add: ra_seq_conv_delta_right)
    also have "\<dots> = (\<Sum>d=1..N. A d * x ^ d)"
    proof -
      have "{..N} = insert 0 {1..N}" by auto
      thus ?thesis by (simp add: A0)
    qed
    finally show ?thesis using True by simp
  next
    case False
    hence k1': "1 \<le> k" by simp
    have expand: "(\<Sum>d\<le>N. ra_seq_conv_pow A (Suc k) d * x ^ d)
        = (\<Sum>i\<le>N. \<Sum>e\<le>N - i. A i * x ^ i * (ra_seq_conv_pow A k e * x ^ e))"
    proof -
      have "(\<Sum>d\<le>N. ra_seq_conv_pow A (Suc k) d * x ^ d)
          = (\<Sum>d\<le>N. \<Sum>i\<le>d. A i * ra_seq_conv_pow A k (d - i) * x ^ d)"
        by (simp add: ra_seq_conv_def sum_distrib_right)
      also have "\<dots> = (\<Sum>d\<le>N. \<Sum>i\<le>d. A i * x ^ i * (ra_seq_conv_pow A k (d - i) * x ^ (d - i)))"
      proof (rule sum.cong[OF refl], rule sum.cong[OF refl])
        fix d i :: nat assume "d \<in> {..N}" "i \<in> {..d}"
        hence "i + (d - i) = d" by simp
        hence "x ^ d = x ^ i * x ^ (d - i)"
          by (simp flip: power_add)
        thus "A i * ra_seq_conv_pow A k (d - i) * x ^ d
                = A i * x ^ i * (ra_seq_conv_pow A k (d - i) * x ^ (d - i))"
          by (simp add: algebra_simps)
      qed
      also have "\<dots> = (\<Sum>i\<le>N. \<Sum>e\<le>N - i. A i * x ^ i * (ra_seq_conv_pow A k e * x ^ e))"
        by (rule sum_triangle_exchange)
      finally show ?thesis .
    qed
    define S where "S = (\<Sum>i=1..N + 1 - Suc k. A i * x ^ i)"
    have Snn: "0 \<le> S"
      unfolding S_def by (intro sum_nonneg mult_nonneg_nonneg Ann zero_le_power x0)
    have inner_bound: "(\<Sum>e\<le>N - i. ra_seq_conv_pow A k e * x ^ e) \<le> S ^ k"
      if i: "1 \<le> i" "i \<le> N" and nz: "k \<le> N - i" for i
    proof -
      have "(\<Sum>e\<le>N - i. ra_seq_conv_pow A k e * x ^ e) \<le> (\<Sum>j=1..(N - i) + 1 - k. A j * x ^ j) ^ k"
        by (rule Suc.IH[OF k1'])
      also have "\<dots> \<le> S ^ k"
      proof (rule power_mono)
        show "(\<Sum>j=1..(N - i) + 1 - k. A j * x ^ j) \<le> S"
          unfolding S_def
        proof (rule sum_mono2)
          show "finite {1..N + 1 - Suc k}" by simp
          show "{1..(N - i) + 1 - k} \<subseteq> {1..N + 1 - Suc k}"
            using i by auto
          show "\<And>j. j \<in> {1..N + 1 - Suc k} - {1..(N - i) + 1 - k} \<Longrightarrow> 0 \<le> A j * x ^ j"
            by (intro mult_nonneg_nonneg Ann zero_le_power x0)
        qed
        show "0 \<le> (\<Sum>j=1..(N - i) + 1 - k. A j * x ^ j)"
          by (intro sum_nonneg mult_nonneg_nonneg Ann zero_le_power x0)
      qed
      finally show ?thesis .
    qed
    have "(\<Sum>i\<le>N. \<Sum>e\<le>N - i. A i * x ^ i * (ra_seq_conv_pow A k e * x ^ e))
        = (\<Sum>i\<le>N. A i * x ^ i * (\<Sum>e\<le>N - i. ra_seq_conv_pow A k e * x ^ e))"
      by (simp add: sum_distrib_left)
    also have "\<dots> \<le> (\<Sum>i\<le>N. (if 1 \<le> i \<and> i \<le> N + 1 - Suc k then A i * x ^ i * S ^ k else 0))"
    proof (rule sum_mono)
      fix i assume iN: "i \<in> {..N}"
      show "A i * x ^ i * (\<Sum>e\<le>N - i. ra_seq_conv_pow A k e * x ^ e)
              \<le> (if 1 \<le> i \<and> i \<le> N + 1 - Suc k then A i * x ^ i * S ^ k else 0)"
      proof (cases "i = 0")
        case True
        thus ?thesis by (simp add: A0)
      next
        case False
        hence i1: "1 \<le> i" by simp
        show ?thesis
        proof (cases "k \<le> N - i")
          case True
          have iub: "i \<le> N + 1 - Suc k"
            using True i1 iN by simp
          have "A i * x ^ i * (\<Sum>e\<le>N - i. ra_seq_conv_pow A k e * x ^ e)
                  \<le> A i * x ^ i * S ^ k"
            by (intro mult_left_mono inner_bound[OF i1 _ True]
                  mult_nonneg_nonneg Ann zero_le_power x0) (use iN in simp)
          thus ?thesis using i1 iub by simp
        next
          case False
          have zero_inner: "(\<Sum>e\<le>N - i. ra_seq_conv_pow A k e * x ^ e) = 0"
          proof (rule sum.neutral, rule ballI)
            fix e assume "e \<in> {..N - i}"
            hence "e < k" using False by simp
            thus "ra_seq_conv_pow A k e * x ^ e = 0"
              by (simp only: A0 ra_seq_conv_pow_vanish)
          qed
          show ?thesis
          proof (cases "1 \<le> i \<and> i \<le> N + 1 - Suc k")
            case True
            thus ?thesis
              using zero_inner
              by (auto intro!: mult_nonneg_nonneg Ann zero_le_power x0
                    ra_seq_conv_pow_nonneg simp: Snn zero_le_power)
          next
            case False
            thus ?thesis using zero_inner
              by auto
          qed
        qed
      qed
    qed
    also have "\<dots> = (\<Sum>i=1..N + 1 - Suc k. A i * x ^ i * S ^ k)"
    proof -
      have sub: "{1..N + 1 - Suc k} \<subseteq> {..N}" by auto
      show ?thesis
        by (rule sum.mono_neutral_cong_right[OF finite_atMost sub]) auto
    qed
    also have "\<dots> = S * S ^ k"
      by (simp add: S_def sum_distrib_right)
    also have "\<dots> = S ^ Suc k"
      by simp
    finally show ?thesis
      using expand by (simp add: S_def)
  qed
qed

subsection \<open>Per-degree $\ell^1$ profiles of coefficient families\<close>

definition ra_deg_block :: "nat \<Rightarrow> ('a::euclidean_space \<Rightarrow> nat) set" where
  "ra_deg_block d = {\<alpha>. \<alpha> \<in> ra_idx \<and> ra_deg \<alpha> = d}"

lemma finite_ra_deg_block: "finite (ra_deg_block d :: ('a::euclidean_space \<Rightarrow> nat) set)"
  unfolding ra_deg_block_def by (rule ra_deg_block_finite)

lemma ra_deg_block_0: "(ra_deg_block 0 :: ('a::euclidean_space \<Rightarrow> nat) set) = {ra_idx_zero}"
proof
  show "(ra_deg_block 0 :: ('a \<Rightarrow> nat) set) \<subseteq> {ra_idx_zero}"
    unfolding ra_deg_block_def using ra_deg_eq0_iff by auto
  have "ra_deg (ra_idx_zero :: 'a \<Rightarrow> nat) = 0"
    by (simp add: ra_deg_def ra_idx_zero_def)
  thus "{ra_idx_zero} \<subseteq> (ra_deg_block 0 :: ('a \<Rightarrow> nat) set)"
    unfolding ra_deg_block_def using ra_idx_zero_in by auto
qed

definition ra_profile_real :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "ra_profile_real u d = (\<Sum>\<alpha>\<in>ra_deg_block d. \<bar>u \<alpha>\<bar>)"

definition ra_profile :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> real" where
  "ra_profile c d = (\<Sum>\<alpha>\<in>ra_deg_block d. norm (c \<alpha>))"

lemma ra_profile_real_nonneg: "0 \<le> ra_profile_real u d"
  unfolding ra_profile_real_def by (rule sum_nonneg) simp

lemma ra_profile_nonneg: "0 \<le> ra_profile c d"
  unfolding ra_profile_def by (rule sum_nonneg) simp

text \<open>The core regrouping estimate: profiles are submultiplicative under the Cauchy
  product, with the scalar convolution as upper bound.\<close>

lemma ra_profile_real_cauchy_prod:
  fixes u v :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  shows "ra_profile_real (ra_cauchy_prod u v) d \<le> ra_seq_conv (ra_profile_real u) (ra_profile_real v) d"
proof -
  have step1: "ra_profile_real (ra_cauchy_prod u v) d
      \<le> (\<Sum>\<gamma>\<in>ra_deg_block d. \<Sum>\<alpha>\<in>ra_idx_below \<gamma>. \<bar>u \<alpha>\<bar> * \<bar>v (ra_idx_diff \<gamma> \<alpha>)\<bar>)"
    unfolding ra_profile_real_def ra_cauchy_prod_def
  proof (rule sum_mono)
    fix \<gamma> :: "'a \<Rightarrow> nat" assume "\<gamma> \<in> ra_deg_block d"
    have "\<bar>\<Sum>\<alpha>\<in>ra_idx_below \<gamma>. u \<alpha> * v (ra_idx_diff \<gamma> \<alpha>)\<bar> \<le> (\<Sum>\<alpha>\<in>ra_idx_below \<gamma>. \<bar>u \<alpha> * v (ra_idx_diff \<gamma> \<alpha>)\<bar>)"
      by (rule sum_abs)
    also have "\<dots> = (\<Sum>\<alpha>\<in>ra_idx_below \<gamma>. \<bar>u \<alpha>\<bar> * \<bar>v (ra_idx_diff \<gamma> \<alpha>)\<bar>)"
      by (simp add: abs_mult)
    finally show "\<bar>\<Sum>\<alpha>\<in>ra_idx_below \<gamma>. u \<alpha> * v (ra_idx_diff \<gamma> \<alpha>)\<bar>
        \<le> (\<Sum>\<alpha>\<in>ra_idx_below \<gamma>. \<bar>u \<alpha>\<bar> * \<bar>v (ra_idx_diff \<gamma> \<alpha>)\<bar>)" .
  qed
  have step2: "(\<Sum>\<gamma>\<in>ra_deg_block d. \<Sum>\<alpha>\<in>ra_idx_below \<gamma>. \<bar>u \<alpha>\<bar> * \<bar>v (ra_idx_diff \<gamma> \<alpha>)\<bar>)
      = (\<Sum>(\<gamma>, \<alpha>)\<in>(SIGMA \<gamma>:(ra_deg_block d :: ('a \<Rightarrow> nat) set). ra_idx_below \<gamma>).
           \<bar>u \<alpha>\<bar> * \<bar>v (ra_idx_diff \<gamma> \<alpha>)\<bar>)"
    by (rule sum.Sigma[OF finite_ra_deg_block]) (simp add: idx_lower_fin)
  define T :: "(('a \<Rightarrow> nat) \<times> ('a \<Rightarrow> nat)) set" where
    "T = {(\<alpha>, \<delta>). \<alpha> \<in> ra_idx \<and> \<delta> \<in> ra_idx \<and> ra_deg \<alpha> + ra_deg \<delta> = d}"
  have step3: "(\<Sum>(\<gamma>, \<alpha>)\<in>(SIGMA \<gamma>:(ra_deg_block d :: ('a \<Rightarrow> nat) set). ra_idx_below \<gamma>).
           \<bar>u \<alpha>\<bar> * \<bar>v (ra_idx_diff \<gamma> \<alpha>)\<bar>)
      = (\<Sum>(\<alpha>, \<delta>)\<in>T. \<bar>u \<alpha>\<bar> * \<bar>v \<delta>\<bar>)"
  proof (rule sum.reindex_bij_witness[where
        i = "\<lambda>(\<alpha>, \<delta>). (ra_idx_add \<alpha> \<delta>, \<alpha>)" and j = "\<lambda>(\<gamma>, \<alpha>). (\<alpha>, ra_idx_diff \<gamma> \<alpha>)"])
    fix a :: "('a \<Rightarrow> nat) \<times> ('a \<Rightarrow> nat)"
    assume a: "a \<in> (SIGMA \<gamma>:(ra_deg_block d :: ('a \<Rightarrow> nat) set). ra_idx_below \<gamma>)"
    obtain \<gamma> \<alpha> :: "'a \<Rightarrow> nat" where ga: "a = (\<gamma>, \<alpha>)" by (cases a)
    have gblk: "\<gamma> \<in> ra_deg_block d" and alow: "\<alpha> \<in> ra_idx_below \<gamma>" using a ga by auto
    have gra: "\<gamma> \<in> ra_idx" and gdeg: "ra_deg \<gamma> = d" using gblk by (auto simp: ra_deg_block_def)
    have ara: "\<alpha> \<in> ra_idx" using alow by (rule ra_idx_below_ra_idx)
    have dra: "ra_idx_diff \<gamma> \<alpha> \<in> ra_idx" using gra by (rule idx_sub)
    have degsplit: "ra_deg \<alpha> + ra_deg (ra_idx_diff \<gamma> \<alpha>) = d"
      using ra_deg_split[OF alow] gdeg by simp
    show "(case case a of (\<gamma>, \<alpha>) \<Rightarrow> (\<alpha>, ra_idx_diff \<gamma> \<alpha>) of (\<alpha>, \<delta>) \<Rightarrow> (ra_idx_add \<alpha> \<delta>, \<alpha>)) = a"
      using ga ra_idx_add_idx_diff[OF alow] by simp
    show "(case a of (\<gamma>, \<alpha>) \<Rightarrow> (\<alpha>, ra_idx_diff \<gamma> \<alpha>)) \<in> T"
      using ga ara dra degsplit by (simp add: T_def)
  next
    fix b :: "('a \<Rightarrow> nat) \<times> ('a \<Rightarrow> nat)"
    assume b: "b \<in> T"
    obtain \<alpha> \<delta> :: "'a \<Rightarrow> nat" where ad: "b = (\<alpha>, \<delta>)" by (cases b)
    have ara: "\<alpha> \<in> ra_idx" and dra: "\<delta> \<in> ra_idx" and degs: "ra_deg \<alpha> + ra_deg \<delta> = d"
      using b ad by (auto simp: T_def)
    have gra: "ra_idx_add \<alpha> \<delta> \<in> ra_idx" using ara dra by (rule idx_add)
    have gdeg: "ra_deg (ra_idx_add \<alpha> \<delta>) = d" using degs by (simp add: ra_deg_idx_add)
    show "(case case b of (\<alpha>, \<delta>) \<Rightarrow> (ra_idx_add \<alpha> \<delta>, \<alpha>) of (\<gamma>, \<alpha>) \<Rightarrow> (\<alpha>, ra_idx_diff \<gamma> \<alpha>)) = b"
      using ad ra_idx_diff_idx_add by simp
    show "(case b of (\<alpha>, \<delta>) \<Rightarrow> (ra_idx_add \<alpha> \<delta>, \<alpha>))
            \<in> (SIGMA \<gamma>:(ra_deg_block d :: ('a \<Rightarrow> nat) set). ra_idx_below \<gamma>)"
      using ad gra gdeg ara ra_idx_add_in_idx_below[OF ara] by (auto simp: ra_deg_block_def)
  next
    show "\<And>a :: ('a \<Rightarrow> nat) \<times> ('a \<Rightarrow> nat).
        a \<in> (SIGMA \<gamma>:(ra_deg_block d :: ('a \<Rightarrow> nat) set). ra_idx_below \<gamma>) \<Longrightarrow>
        (case case a of (\<gamma>, \<alpha>) \<Rightarrow> (\<alpha>, ra_idx_diff \<gamma> \<alpha>) of (\<alpha>, \<delta>) \<Rightarrow> \<bar>u \<alpha>\<bar> * \<bar>v \<delta>\<bar>)
          = (case a of (\<gamma>, \<alpha>) \<Rightarrow> \<bar>u \<alpha>\<bar> * \<bar>v (ra_idx_diff \<gamma> \<alpha>)\<bar>)"
      by fastforce
  qed
  have Tsplit: "T = (\<Union>i\<in>{..d}. ra_deg_block i \<times> ra_deg_block (d - i))"
  proof
    show "T \<subseteq> (\<Union>i\<in>{..d}. ra_deg_block i \<times> ra_deg_block (d - i))"
    proof
      fix p :: "('a \<Rightarrow> nat) \<times> ('a \<Rightarrow> nat)"
      assume p: "p \<in> T"
      obtain \<alpha> \<delta> :: "'a \<Rightarrow> nat" where ad: "p = (\<alpha>, \<delta>)" by (cases p)
      have ara: "\<alpha> \<in> ra_idx" and dra: "\<delta> \<in> ra_idx" and degs: "ra_deg \<alpha> + ra_deg \<delta> = d"
        using p ad by (auto simp: T_def)
      have "ra_deg \<alpha> \<le> d" using degs by simp
      moreover have "\<alpha> \<in> ra_deg_block (ra_deg \<alpha>)" using ara by (simp add: ra_deg_block_def)
      moreover have "\<delta> \<in> ra_deg_block (d - ra_deg \<alpha>)"
        using dra degs by (simp add: ra_deg_block_def)
      ultimately show "p \<in> (\<Union>i\<in>{..d}. ra_deg_block i \<times> ra_deg_block (d - i))"
        using ad by auto
    qed
    show "(\<Union>i\<in>{..d}. ra_deg_block i \<times> ra_deg_block (d - i)) \<subseteq> T"
    proof
      fix p :: "('a \<Rightarrow> nat) \<times> ('a \<Rightarrow> nat)"
      assume "p \<in> (\<Union>i\<in>{..d}. ra_deg_block i \<times> ra_deg_block (d - i))"
      then obtain i and \<alpha> \<delta> :: "'a \<Rightarrow> nat" where i: "i \<le> d" and ad: "p = (\<alpha>, \<delta>)"
        and a: "\<alpha> \<in> ra_deg_block i" and dd: "\<delta> \<in> ra_deg_block (d - i)"
        by auto
      show "p \<in> T"
        using i ad a dd by (auto simp: T_def ra_deg_block_def)
    qed
  qed
  have step4: "(\<Sum>(\<alpha>, \<delta>)\<in>T. \<bar>u \<alpha>\<bar> * \<bar>v \<delta>\<bar>) = ra_seq_conv (ra_profile_real u) (ra_profile_real v) d"
  proof -
    have disj: "\<And>i j. i \<in> {..d} \<Longrightarrow> j \<in> {..d} \<Longrightarrow> i \<noteq> j \<Longrightarrow>
        (ra_deg_block i \<times> ra_deg_block (d - i)) \<inter> (ra_deg_block j \<times> ra_deg_block (d - j)) = {}"
      by (auto simp: ra_deg_block_def)
    have "(\<Sum>(\<alpha>, \<delta>)\<in>T. \<bar>u \<alpha>\<bar> * \<bar>v \<delta>\<bar>)
        = (\<Sum>i\<le>d. \<Sum>(\<alpha>, \<delta>)\<in>ra_deg_block i \<times> ra_deg_block (d - i). \<bar>u \<alpha>\<bar> * \<bar>v \<delta>\<bar>)"
      unfolding Tsplit
      by (rule sum.UNION_disjoint)
         (auto simp: finite_ra_deg_block disj intro: finite_cartesian_product)
    also have "\<dots> = (\<Sum>i\<le>d. (\<Sum>\<alpha>\<in>ra_deg_block i. \<bar>u \<alpha>\<bar>) * (\<Sum>\<delta>\<in>ra_deg_block (d - i). \<bar>v \<delta>\<bar>))"
      by (simp add: sum_product sum.cartesian_product)
    also have "\<dots> = ra_seq_conv (ra_profile_real u) (ra_profile_real v) d"
      by (simp add: ra_seq_conv_def ra_profile_real_def)
    finally show ?thesis .
  qed
  show ?thesis
    using step1 step2 step3 step4 by simp
qed

lemma ra_profile_real_coeff_one: "ra_profile_real (ra_coeff_one :: ('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real) = ra_seq_delta"
proof (rule ext)
  fix d :: nat
  show "ra_profile_real (ra_coeff_one :: ('a \<Rightarrow> nat) \<Rightarrow> real) d = ra_seq_delta d"
  proof (cases "d = 0")
    case True
    thus ?thesis
      by (simp add: ra_profile_real_def ra_deg_block_0 ra_coeff_one_def ra_seq_delta_def)
  next
    case False
    have "\<And>\<alpha>. \<alpha> \<in> (ra_deg_block d :: ('a \<Rightarrow> nat) set) \<Longrightarrow> ra_coeff_one \<alpha> = 0"
    proof -
      fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> ra_deg_block d"
      hence da: "ra_deg \<alpha> = d" by (simp add: ra_deg_block_def)
      have "\<alpha> \<noteq> ra_idx_zero"
      proof
        assume "\<alpha> = ra_idx_zero"
        hence "ra_deg \<alpha> = 0" by (simp add: ra_deg_def ra_idx_zero_def)
        thus False using da False by simp
      qed
      thus "ra_coeff_one \<alpha> = 0" by (simp add: ra_coeff_one_def)
    qed
    thus ?thesis by (simp add: ra_profile_real_def ra_seq_delta_def False)
  qed
qed

lemma ra_profile_real_cauchy_pow:
  fixes u :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  shows "ra_profile_real (ra_cauchy_pow u k) d \<le> ra_seq_conv_pow (ra_profile_real u) k d"
proof (induction k arbitrary: d)
  case 0
  show ?case by (simp add: ra_cauchy_pow_0 ra_profile_real_coeff_one)
next
  case (Suc k)
  have "ra_profile_real (ra_cauchy_pow u (Suc k)) d = ra_profile_real (ra_cauchy_prod u (ra_cauchy_pow u k)) d"
    by (simp add: ra_cauchy_pow_Suc)
  also have "\<dots> \<le> ra_seq_conv (ra_profile_real u) (ra_profile_real (ra_cauchy_pow u k)) d"
    by (rule ra_profile_real_cauchy_prod)
  also have "\<dots> \<le> ra_seq_conv (ra_profile_real u) (ra_seq_conv_pow (ra_profile_real u) k) d"
    by (rule ra_seq_conv_mono[OF order_refl Suc.IH ra_profile_real_nonneg
          ra_seq_conv_pow_nonneg[OF ra_profile_real_nonneg]])
  finally show ?case by simp
qed

lemma ra_profile_real_component:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes b: "b \<in> Basis"
  shows "ra_profile_real (\<lambda>\<alpha>. c \<alpha> \<bullet> b) d \<le> ra_profile c d"
  unfolding ra_profile_real_def ra_profile_def
  by (rule sum_mono) (simp add: Basis_le_norm[OF b])

lemma ra_profile_real_mono_coeffs_list:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes bs: "set l \<subseteq> Basis"
  shows "ra_profile_real (ra_mono_coeffs_list c \<beta> l) d \<le> ra_seq_conv_pow (ra_profile c) (sum_list (map \<beta> l)) d"
  using bs
proof (induction l arbitrary: d)
  case Nil
  show ?case by (simp add: ra_profile_real_coeff_one)
next
  case (Cons b bs)
  have bB: "b \<in> Basis" and rest: "set bs \<subseteq> Basis"
    using Cons.prems by auto
  have "ra_profile_real (ra_mono_coeffs_list c \<beta> (b # bs)) d
      = ra_profile_real (ra_cauchy_prod (ra_cauchy_pow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) (ra_mono_coeffs_list c \<beta> bs)) d"
    by simp
  also have "\<dots> \<le> ra_seq_conv (ra_profile_real (ra_cauchy_pow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b))) (ra_profile_real (ra_mono_coeffs_list c \<beta> bs)) d"
    by (rule ra_profile_real_cauchy_prod)
  also have "\<dots> \<le> ra_seq_conv (ra_seq_conv_pow (ra_profile c) (\<beta> b))
                    (ra_seq_conv_pow (ra_profile c) (sum_list (map \<beta> bs))) d"
  proof (rule ra_seq_conv_mono)
    fix i
    have "ra_profile_real (ra_cauchy_pow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) i \<le> ra_seq_conv_pow (ra_profile_real (\<lambda>\<alpha>. c \<alpha> \<bullet> b)) (\<beta> b) i"
      by (rule ra_profile_real_cauchy_pow)
    also have "\<dots> \<le> ra_seq_conv_pow (ra_profile c) (\<beta> b) i"
      by (rule ra_seq_conv_pow_mono_base[OF ra_profile_real_component[OF bB] ra_profile_real_nonneg])
    finally show "ra_profile_real (ra_cauchy_pow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) i \<le> ra_seq_conv_pow (ra_profile c) (\<beta> b) i" .
  next
    fix i
    show "ra_profile_real (ra_mono_coeffs_list c \<beta> bs) i \<le> ra_seq_conv_pow (ra_profile c) (sum_list (map \<beta> bs)) i"
      by (rule Cons.IH[OF rest])
  next
    fix i
    show "0 \<le> ra_profile_real (ra_cauchy_pow (\<lambda>\<alpha>. c \<alpha> \<bullet> b) (\<beta> b)) i" by (rule ra_profile_real_nonneg)
  next
    fix i
    show "0 \<le> ra_seq_conv_pow (ra_profile c) (sum_list (map \<beta> bs)) i"
      by (rule ra_seq_conv_pow_nonneg[OF ra_profile_nonneg])
  qed
  also have "\<dots> = ra_seq_conv_pow (ra_profile c) (\<beta> b + sum_list (map \<beta> bs)) d"
    by (simp add: ra_seq_conv_pow_add)
  finally show ?case by simp
qed

lemma ra_profile_real_mono_coeffs:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  shows "ra_profile_real (ra_mono_coeffs c \<beta>) d \<le> ra_seq_conv_pow (ra_profile c) (ra_deg \<beta>) d"
proof -
  have sub: "set (ra_basis_list :: 'a list) \<subseteq> Basis"
    by (simp add: ra_basis_list(1))
  have "ra_profile_real (ra_mono_coeffs_list c \<beta> ra_basis_list) d
      \<le> ra_seq_conv_pow (ra_profile c) (sum_list (map \<beta> (ra_basis_list :: 'a list))) d"
    by (rule ra_profile_real_mono_coeffs_list[OF sub])
  thus ?thesis
    unfolding ra_mono_coeffs_def by (simp add: sum_list_basis_ra_deg)
qed

lemma ra_profile_coeff_id:
  "ra_profile (ra_coeff_id :: ('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a) d
     \<le> (if d = 1 then real (card (Basis :: 'a set)) else 0)"
proof (cases "d = 1")
  case False
  have "\<And>\<alpha>. \<alpha> \<in> (ra_deg_block d :: ('a \<Rightarrow> nat) set) \<Longrightarrow> ra_coeff_id \<alpha> = 0"
  proof -
    fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> ra_deg_block d"
    hence "ra_deg \<alpha> = d" by (simp add: ra_deg_block_def)
    thus "ra_coeff_id \<alpha> = 0" using False ra_coeff_id_deg by fastforce
  qed
  thus ?thesis by (simp add: ra_profile_def False)
next
  case True
  have "ra_profile (ra_coeff_id :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) d
      = (\<Sum>\<alpha>\<in>(ra_deg_block d :: ('a \<Rightarrow> nat) set). norm (ra_coeff_id \<alpha>))"
    by (simp add: ra_profile_def)
  also have "\<dots> \<le> (\<Sum>\<alpha>\<in>(ra_deg_block d :: ('a \<Rightarrow> nat) set). 1)"
    by (rule sum_mono) (rule norm_coeff_id_le)
  also have "\<dots> = real (card (ra_deg_block d :: ('a \<Rightarrow> nat) set))"
    by simp
  also have "\<dots> \<le> real (card (Basis :: 'a set))"
  proof -
    have sub: "(ra_deg_block d :: ('a \<Rightarrow> nat) set) \<subseteq> ra_idx_unit ` (Basis :: 'a set)"
    proof
      fix \<alpha> :: "'a \<Rightarrow> nat" assume "\<alpha> \<in> ra_deg_block d"
      hence "\<alpha> \<in> ra_idx" "ra_deg \<alpha> = 1" using True by (auto simp: ra_deg_block_def)
      thus "\<alpha> \<in> ra_idx_unit ` Basis"
        by (metis ra_deg_one_unit imageI)
    qed
    have "card (ra_deg_block d :: ('a \<Rightarrow> nat) set) \<le> card (ra_idx_unit ` (Basis :: 'a set))"
      by (rule card_mono[OF finite_imageI[OF finite_Basis] sub])
    also have "\<dots> = card (Basis :: 'a set)"
      by (rule card_image[OF inj_on_idx_unit])
    finally show ?thesis by simp
  qed
  finally show ?thesis using True by simp
qed

subsection \<open>The composition operator \<open>ra_inverse_step\<close> and the formal fixed point\<close>

definition ra_deg_range :: "nat \<Rightarrow> nat \<Rightarrow> ('a::euclidean_space \<Rightarrow> nat) set" where
  "ra_deg_range j d = {\<beta>. \<beta> \<in> ra_idx \<and> j \<le> ra_deg \<beta> \<and> ra_deg \<beta> \<le> d}"

lemma finite_ra_deg_range: "finite (ra_deg_range j d :: ('a::euclidean_space \<Rightarrow> nat) set)"
proof -
  have "(ra_deg_range j d :: ('a \<Rightarrow> nat) set) \<subseteq> (\<Union>k\<in>{..d}. ra_deg_block k)"
    by (auto simp: ra_deg_range_def ra_deg_block_def)
  moreover have "finite (\<Union>k\<in>{..d}. ra_deg_block k :: ('a \<Rightarrow> nat) set)"
    by (intro finite_UN_I finite_atMost finite_ra_deg_block)
  ultimately show ?thesis by (rule finite_subset)
qed

definition ra_inverse_step :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> (('a \<Rightarrow> nat) \<Rightarrow> 'a)
                       \<Rightarrow> (('a \<Rightarrow> nat) \<Rightarrow> 'a)" where
  "ra_inverse_step bphi c =
     (\<lambda>\<gamma>. ra_coeff_id \<gamma> + (\<Sum>\<beta>\<in>ra_deg_range 2 (ra_deg \<gamma>). ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>))"

lemma ra_deg_range_2_empty: "ra_deg \<gamma> < 2 \<Longrightarrow> (ra_deg_range 2 (ra_deg \<gamma>)) = {}"
  by (auto simp: ra_deg_range_def)

lemma ra_inverse_step_low_deg: "ra_deg \<gamma> < 2 \<Longrightarrow> ra_inverse_step bphi c \<gamma> = ra_coeff_id \<gamma>"
  by (simp add: ra_inverse_step_def ra_deg_range_2_empty)

lemma ra_inverse_step_idx_zero: "ra_inverse_step bphi c ra_idx_zero = 0"
proof -
  have "ra_deg (ra_idx_zero :: 'a \<Rightarrow> nat) = 0"
    by (simp add: ra_deg_def ra_idx_zero_def)
  thus ?thesis by (simp add: ra_inverse_step_low_deg ra_coeff_id_idx_zero)
qed

lemma ra_inverse_step_sum_le_degree:
  fixes bphi c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes low: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> ra_deg \<beta> < 2 \<Longrightarrow> bphi \<beta> = 0"
  shows "ra_inverse_step bphi c \<gamma> =
    ra_coeff_id \<gamma> + (\<Sum>\<beta>\<in>ra_deg_range 0 (ra_deg \<gamma>). ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
proof -
  have "(\<Sum>\<beta>\<in>ra_deg_range 2 (ra_deg \<gamma>). ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      = (\<Sum>\<beta>\<in>ra_deg_range 0 (ra_deg \<gamma>). ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
  proof (rule sum.mono_neutral_cong_left)
    show "finite (ra_deg_range 0 (ra_deg \<gamma>) :: ('a \<Rightarrow> nat) set)"
      by (rule finite_ra_deg_range)
    show "ra_deg_range 2 (ra_deg \<gamma>) \<subseteq> ra_deg_range 0 (ra_deg \<gamma>)"
      by (auto simp: ra_deg_range_def)
    show "\<forall>\<beta>\<in>ra_deg_range 0 (ra_deg \<gamma>) - ra_deg_range 2 (ra_deg \<gamma>).
      ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta> = 0"
    proof
      fix \<beta> :: "'a \<Rightarrow> nat"
      assume "\<beta> \<in> ra_deg_range 0 (ra_deg \<gamma>) - ra_deg_range 2 (ra_deg \<gamma>)"
      hence "\<beta> \<in> ra_idx" "ra_deg \<beta> < 2"
        by (auto simp: ra_deg_range_def)
      hence "bphi \<beta> = 0"
        by (rule low)
      thus "ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta> = 0"
        by simp
    qed
    show "\<And>\<beta>. \<beta> \<in> ra_deg_range 2 (ra_deg \<gamma>) \<Longrightarrow>
      ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta> = ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>"
      by simp
  qed
  thus ?thesis
    by (simp add: ra_inverse_step_def)
qed

lemma ra_inverse_step_local:
  fixes c c' :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes c0: "c ra_idx_zero = 0" and c0': "c' ra_idx_zero = 0"
    and agree: "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D \<Longrightarrow> c \<alpha> = c' \<alpha>"
    and g: "\<gamma> \<in> ra_idx" and dg: "ra_deg \<gamma> \<le> D + 1"
  shows "ra_inverse_step bphi c \<gamma> = ra_inverse_step bphi c' \<gamma>"
proof -
  have "(\<Sum>\<beta>\<in>ra_deg_range 2 (ra_deg \<gamma>). ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      = (\<Sum>\<beta>\<in>ra_deg_range 2 (ra_deg \<gamma>). ra_mono_coeffs c' \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
  proof (rule sum.cong[OF refl])
    fix \<beta> :: "'a \<Rightarrow> nat" assume "\<beta> \<in> ra_deg_range 2 (ra_deg \<gamma>)"
    hence b2: "2 \<le> ra_deg \<beta>" by (simp add: ra_deg_range_def)
    have "ra_mono_coeffs c \<beta> \<gamma> = ra_mono_coeffs c' \<beta> \<gamma>"
    proof (rule ra_mono_coeffs_local[where D = D])
      show "c ra_idx_zero = 0" by (rule c0)
      show "c' ra_idx_zero = 0" by (rule c0')
      show "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> D \<Longrightarrow> c \<alpha> = c' \<alpha>" by (rule agree)
      show "\<gamma> \<in> ra_idx" by (rule g)
      show "1 \<le> ra_deg \<beta>" using b2 by simp
      show "ra_deg \<gamma> \<le> D + ra_deg \<beta> - 1" using dg b2 by simp
    qed
    thus "ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta> = ra_mono_coeffs c' \<beta> \<gamma> *\<^sub>R bphi \<beta>" by simp
  qed
  thus ?thesis by (simp add: ra_inverse_step_def)
qed

lemma ra_profile_inverse_step:
  fixes bphi c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  shows "ra_profile (ra_inverse_step bphi c) d
      \<le> ra_profile (ra_coeff_id :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) d
          + (\<Sum>k=2..d. ra_profile bphi k * ra_seq_conv_pow (ra_profile c) k d)"
proof -
  have "ra_profile (ra_inverse_step bphi c) d
      = (\<Sum>\<gamma>\<in>(ra_deg_block d :: ('a \<Rightarrow> nat) set).
           norm (ra_coeff_id \<gamma> + (\<Sum>\<beta>\<in>ra_deg_range 2 (ra_deg \<gamma>). ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>)))"
    by (simp add: ra_profile_def ra_inverse_step_def)
  also have "\<dots> \<le> (\<Sum>\<gamma>\<in>(ra_deg_block d :: ('a \<Rightarrow> nat) set).
           norm (ra_coeff_id \<gamma>)
             + norm (\<Sum>\<beta>\<in>ra_deg_range 2 (ra_deg \<gamma>). ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>))"
    by (rule sum_mono) (rule norm_triangle_ineq)
  also have "\<dots> = (\<Sum>\<gamma>\<in>(ra_deg_block d :: ('a \<Rightarrow> nat) set). norm (ra_coeff_id \<gamma>))
        + (\<Sum>\<gamma>\<in>(ra_deg_block d :: ('a \<Rightarrow> nat) set).
             norm (\<Sum>\<beta>\<in>ra_deg_range 2 (ra_deg \<gamma>). ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>))"
    by (rule sum.distrib)
  finally have "ra_profile (ra_inverse_step bphi c) d
      \<le> (\<Sum>\<gamma>\<in>(ra_deg_block d :: ('a \<Rightarrow> nat) set). norm (ra_coeff_id \<gamma>))
        + (\<Sum>\<gamma>\<in>(ra_deg_block d :: ('a \<Rightarrow> nat) set).
             norm (\<Sum>\<beta>\<in>ra_deg_range 2 (ra_deg \<gamma>). ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>))" .
  also have "\<dots> \<le> ra_profile (ra_coeff_id :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) d
        + (\<Sum>k=2..d. ra_profile bphi k * ra_seq_conv_pow (ra_profile c) k d)"
  proof -
    have inner: "(\<Sum>\<gamma>\<in>(ra_deg_block d :: ('a \<Rightarrow> nat) set).
             norm (\<Sum>\<beta>\<in>ra_deg_range 2 (ra_deg \<gamma>). ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>))
        \<le> (\<Sum>k=2..d. ra_profile bphi k * ra_seq_conv_pow (ra_profile c) k d)"
    proof -
      have rng_const: "\<And>\<gamma>. \<gamma> \<in> (ra_deg_block d :: ('a \<Rightarrow> nat) set) \<Longrightarrow>
          ra_deg_range 2 (ra_deg \<gamma>) = ra_deg_range 2 d"
        by (simp add: ra_deg_block_def)
      have "(\<Sum>\<gamma>\<in>(ra_deg_block d :: ('a \<Rightarrow> nat) set).
               norm (\<Sum>\<beta>\<in>ra_deg_range 2 (ra_deg \<gamma>). ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>))
          \<le> (\<Sum>\<gamma>\<in>(ra_deg_block d :: ('a \<Rightarrow> nat) set).
               \<Sum>\<beta>\<in>ra_deg_range 2 d. \<bar>ra_mono_coeffs c \<beta> \<gamma>\<bar> * norm (bphi \<beta>))"
      proof (rule sum_mono)
        fix \<gamma> :: "'a \<Rightarrow> nat" assume gblk: "\<gamma> \<in> ra_deg_block d"
        have "norm (\<Sum>\<beta>\<in>ra_deg_range 2 (ra_deg \<gamma>). ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
            \<le> (\<Sum>\<beta>\<in>ra_deg_range 2 (ra_deg \<gamma>). norm (ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>))"
          by (rule norm_sum)
        also have "\<dots> = (\<Sum>\<beta>\<in>ra_deg_range 2 d. \<bar>ra_mono_coeffs c \<beta> \<gamma>\<bar> * norm (bphi \<beta>))"
          by (simp add: rng_const[OF gblk])
        finally show "norm (\<Sum>\<beta>\<in>ra_deg_range 2 (ra_deg \<gamma>). ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
            \<le> (\<Sum>\<beta>\<in>ra_deg_range 2 d. \<bar>ra_mono_coeffs c \<beta> \<gamma>\<bar> * norm (bphi \<beta>))" .
      qed
      also have "\<dots> = (\<Sum>\<beta>\<in>ra_deg_range 2 d.
               norm (bphi \<beta>) * (\<Sum>\<gamma>\<in>ra_deg_block d. \<bar>ra_mono_coeffs c \<beta> \<gamma>\<bar>))"
        by (subst sum.swap) (simp add: sum_distrib_left algebra_simps)
      also have "\<dots> = (\<Sum>\<beta>\<in>(ra_deg_range 2 d :: ('a \<Rightarrow> nat) set).
               norm (bphi \<beta>) * ra_profile_real (ra_mono_coeffs c \<beta>) d)"
        by (simp add: ra_profile_real_def)
      also have "\<dots> \<le> (\<Sum>\<beta>\<in>(ra_deg_range 2 d :: ('a \<Rightarrow> nat) set).
               norm (bphi \<beta>) * ra_seq_conv_pow (ra_profile c) (ra_deg \<beta>) d)"
        by (rule sum_mono) (intro mult_left_mono ra_profile_real_mono_coeffs norm_ge_zero)
      also have "\<dots> = (\<Sum>k=2..d. \<Sum>\<beta>\<in>(ra_deg_block k :: ('a \<Rightarrow> nat) set).
               norm (bphi \<beta>) * ra_seq_conv_pow (ra_profile c) (ra_deg \<beta>) d)"
      proof -
        have split: "(ra_deg_range 2 d :: ('a \<Rightarrow> nat) set) = (\<Union>k\<in>{2..d}. ra_deg_block k)"
          by (auto simp: ra_deg_range_def ra_deg_block_def)
        show ?thesis
          unfolding split using finite_ra_deg_block
          apply (subst sum.UNION_disjoint)
          apply simp_all
          apply blast
          by (simp add: disjoint_iff ra_deg_block_def)
      qed
      also have "\<dots> = (\<Sum>k=2..d. ra_profile bphi k * ra_seq_conv_pow (ra_profile c) k d)"
      proof (rule sum.cong[OF refl])
        fix k assume "k \<in> {2..d}"
        have "(\<Sum>\<beta>\<in>(ra_deg_block k :: ('a \<Rightarrow> nat) set).
                 norm (bphi \<beta>) * ra_seq_conv_pow (ra_profile c) (ra_deg \<beta>) d)
            = (\<Sum>\<beta>\<in>(ra_deg_block k :: ('a \<Rightarrow> nat) set).
                 norm (bphi \<beta>) * ra_seq_conv_pow (ra_profile c) k d)"
          by (rule sum.cong[OF refl], simp add: ra_deg_block_def)
        also have "\<dots> = ra_profile bphi k * ra_seq_conv_pow (ra_profile c) k d"
          by (simp add: ra_profile_def sum_distrib_right)
        finally show "(\<Sum>\<beta>\<in>(ra_deg_block k :: ('a \<Rightarrow> nat) set).
                 norm (bphi \<beta>) * ra_seq_conv_pow (ra_profile c) (ra_deg \<beta>) d)
            = ra_profile bphi k * ra_seq_conv_pow (ra_profile c) k d" .
      qed
      finally show ?thesis .
    qed
    have ra_coeff_id_eq: "(\<Sum>\<gamma>\<in>(ra_deg_block d :: ('a \<Rightarrow> nat) set). norm (ra_coeff_id \<gamma>))
                    = ra_profile (ra_coeff_id :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) d"
      by (simp add: ra_profile_def)
    show ?thesis
      unfolding ra_coeff_id_eq by (rule add_left_mono[OF inner])
  qed
  finally show ?thesis .
qed

text \<open>Stage-wise construction of the formal fixed point.\<close>

primrec ra_inverse_stage :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> (('a \<Rightarrow> nat) \<Rightarrow> 'a)" where
  "ra_inverse_stage bphi 0 = (\<lambda>_. 0)"
| "ra_inverse_stage bphi (Suc d) = ra_inverse_step bphi (ra_inverse_stage bphi d)"

lemma ra_inverse_stage_idx_zero: "ra_inverse_stage bphi d ra_idx_zero = 0"
  by (cases d) (simp_all add: ra_inverse_step_idx_zero)

lemma ra_inverse_stage_stable_succ:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes "\<gamma> \<in> ra_idx" and "ra_deg \<gamma> \<le> d"
  shows "ra_inverse_stage bphi (Suc d) \<gamma> = ra_inverse_stage bphi d \<gamma>"
  using assms
proof (induction d arbitrary: \<gamma>)
  case 0
  hence "\<gamma> = ra_idx_zero" by (simp add: ra_deg_eq0_iff)
  thus ?case by (simp add: ra_inverse_step_idx_zero)
next
  case (Suc d)
  have "ra_inverse_step bphi (ra_inverse_stage bphi (Suc d)) \<gamma> = ra_inverse_step bphi (ra_inverse_stage bphi d) \<gamma>"
  proof (rule ra_inverse_step_local[where D = d])
    show "ra_inverse_stage bphi (Suc d) ra_idx_zero = 0" by (rule ra_inverse_stage_idx_zero)
    show "ra_inverse_stage bphi d ra_idx_zero = 0" by (rule ra_inverse_stage_idx_zero)
    show "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> d \<Longrightarrow>
            ra_inverse_stage bphi (Suc d) \<alpha> = ra_inverse_stage bphi d \<alpha>"
      by (rule Suc.IH)
    show "\<gamma> \<in> ra_idx" by (rule Suc.prems(1))
    show "ra_deg \<gamma> \<le> d + 1" using Suc.prems(2) by simp
  qed
  thus ?case by simp
qed

lemma ra_inverse_stage_stable:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes g: "\<gamma> \<in> ra_idx" and dd: "ra_deg \<gamma> \<le> d" and de: "d \<le> e"
  shows "ra_inverse_stage bphi e \<gamma> = ra_inverse_stage bphi d \<gamma>"
  using de
proof (induction e)
  case 0
  thus ?case by simp
next
  case (Suc e)
  show ?case
  proof (cases "d = Suc e")
    case True
    thus ?thesis by simp
  next
    case False
    hence "d \<le> e" using Suc.prems by simp
    hence IH: "ra_inverse_stage bphi e \<gamma> = ra_inverse_stage bphi d \<gamma>" by (rule Suc.IH)
    have "ra_inverse_stage bphi (Suc e) \<gamma> = ra_inverse_stage bphi e \<gamma>"
      by (rule ra_inverse_stage_stable_succ[OF g]) (use dd \<open>d \<le> e\<close> in simp)
    thus ?thesis using IH by simp
  qed
qed

definition ra_inverse_coeffs :: "(('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a) \<Rightarrow> (('a \<Rightarrow> nat) \<Rightarrow> 'a)" where
  "ra_inverse_coeffs bphi = (\<lambda>\<gamma>. ra_inverse_stage bphi (ra_deg \<gamma>) \<gamma>)"

lemma ra_inverse_coeffs_idx_zero: "ra_inverse_coeffs bphi ra_idx_zero = 0"
  by (simp add: ra_inverse_coeffs_def ra_inverse_stage_idx_zero)

lemma ra_inverse_coeffs_agrees_inverse_stage:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes a: "\<alpha> \<in> ra_idx" and dd: "ra_deg \<alpha> \<le> d"
  shows "ra_inverse_coeffs bphi \<alpha> = ra_inverse_stage bphi d \<alpha>"
  unfolding ra_inverse_coeffs_def
  by (rule ra_inverse_stage_stable[OF a order_refl dd, symmetric])

theorem ra_inverse_coeffs_fixed_point:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes g: "\<gamma> \<in> ra_idx"
  shows "ra_inverse_coeffs bphi \<gamma> = ra_inverse_step bphi (ra_inverse_coeffs bphi) \<gamma>"
proof -
  define d where "d = ra_deg \<gamma>"
  have T_eq: "ra_inverse_step bphi (ra_inverse_coeffs bphi) \<gamma> = ra_inverse_step bphi (ra_inverse_stage bphi d) \<gamma>"
  proof (rule ra_inverse_step_local[where D = d])
    show "ra_inverse_coeffs bphi ra_idx_zero = 0" by (rule ra_inverse_coeffs_idx_zero)
    show "ra_inverse_stage bphi d ra_idx_zero = 0" by (rule ra_inverse_stage_idx_zero)
    show "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> \<le> d \<Longrightarrow> ra_inverse_coeffs bphi \<alpha> = ra_inverse_stage bphi d \<alpha>"
      by (rule ra_inverse_coeffs_agrees_inverse_stage)
    show "\<gamma> \<in> ra_idx" by (rule g)
    show "ra_deg \<gamma> \<le> d + 1" by (simp add: d_def)
  qed
  have "ra_inverse_step bphi (ra_inverse_stage bphi d) \<gamma> = ra_inverse_stage bphi (Suc d) \<gamma>"
    by simp
  also have "\<dots> = ra_inverse_stage bphi d \<gamma>"
    by (rule ra_inverse_stage_stable_succ[OF g]) (simp add: d_def)
  also have "\<dots> = ra_inverse_coeffs bphi \<gamma>"
    by (simp add: ra_inverse_coeffs_def d_def)
  finally show ?thesis
    using T_eq by simp
qed

corollary ra_inverse_coeffs_coeff_equation_le_degree:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes g: "\<gamma> \<in> ra_idx"
    and low: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> ra_deg \<beta> < 2 \<Longrightarrow> bphi \<beta> = 0"
  shows "ra_inverse_coeffs bphi \<gamma> =
    ra_coeff_id \<gamma> + (\<Sum>\<beta>\<in>ra_deg_range 0 (ra_deg \<gamma>). ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
  using ra_inverse_coeffs_fixed_point[OF g]
    ra_inverse_step_sum_le_degree[where bphi=bphi and c="ra_inverse_coeffs bphi" and \<gamma>=\<gamma>, OF low]
  by simp

lemma ra_mono_coeffs_term_has_sum_le_degree:
  fixes c bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes c0: "c ra_idx_zero = 0"
    and g: "\<gamma> \<in> ra_idx"
  shows "((\<lambda>\<beta>. ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      has_sum (\<Sum>\<beta>\<in>ra_deg_range 0 (ra_deg \<gamma>). ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>))
      (ra_idx::('a \<Rightarrow> nat) set)"
proof -
  let ?S = "ra_deg_range 0 (ra_deg \<gamma>) :: ('a \<Rightarrow> nat) set"
  have finite_sum:
    "((\<lambda>\<beta>. ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      has_sum (\<Sum>\<beta>\<in>?S. ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>)) ?S"
    by (rule has_sum_finite) (rule finite_ra_deg_range)
  have neutral:
    "ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta> = 0"
    if "\<beta> \<in> (ra_idx::('a \<Rightarrow> nat) set) - ?S" for \<beta>
  proof -
    have "ra_deg \<gamma> < ra_deg \<beta>"
      using that by (auto simp: ra_deg_range_def)
    hence "ra_mono_coeffs c \<beta> \<gamma> = 0"
      by (rule ra_mono_coeffs_zero_below_degree[where c=c and \<beta>=\<beta>, OF c0 g])
    thus ?thesis by simp
  qed
  have "(((\<lambda>\<beta>. ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      has_sum (\<Sum>\<beta>\<in>?S. ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>))
      (ra_idx::('a \<Rightarrow> nat) set))
    = (((\<lambda>\<beta>. ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      has_sum (\<Sum>\<beta>\<in>?S. ra_mono_coeffs c \<beta> \<gamma> *\<^sub>R bphi \<beta>)) ?S)"
    by (rule has_sum_cong_neutral)
       (use neutral in \<open>auto simp: ra_deg_range_def\<close>)
  thus ?thesis
    using finite_sum by simp
qed

corollary ra_inverse_coeffs_coeff_equation_infsum:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes g: "\<gamma> \<in> ra_idx"
    and low: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> ra_deg \<beta> < 2 \<Longrightarrow> bphi \<beta> = 0"
  shows "ra_inverse_coeffs bphi \<gamma> =
    ra_coeff_id \<gamma> + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
proof -
  have hs: "((\<lambda>\<beta>. ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      has_sum (\<Sum>\<beta>\<in>ra_deg_range 0 (ra_deg \<gamma>). ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>))
      (ra_idx::('a \<Rightarrow> nat) set)"
    by (rule ra_mono_coeffs_term_has_sum_le_degree[where c = "ra_inverse_coeffs bphi", OF ra_inverse_coeffs_idx_zero g])
  hence inf_eq:
    "(\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)
      = (\<Sum>\<beta>\<in>ra_deg_range 0 (ra_deg \<gamma>). ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
    by (rule infsumI)
  show ?thesis
    using ra_inverse_coeffs_coeff_equation_le_degree[OF g low] inf_eq by simp
qed

subsection \<open>The majorant bootstrap for the fixed point\<close>

text \<open>Weighted partial sums of the profile of \<open>ra_inverse_coeffs\<close> stay below \<open>2n\<sigma>\<close> for small \<open>\<sigma>\<close>.\<close>

lemma geom_tail_le:
  fixes q :: real
  assumes q0: "0 \<le> q" and qh: "q \<le> 1/2"
  shows "(\<Sum>k=2..K. q ^ k) \<le> 2 * q\<^sup>2"
proof -
  have "(\<Sum>k=2..K. q ^ k) = (\<Sum>j<K - 1. q ^ (j + 2))"
  proof (cases "2 \<le> K")
    case True
    show ?thesis
      using le_Suc_ex
      by (subst sum.reindex_bij_witness[where i = "\<lambda>j. j + 2" and j = "\<lambda>k. k - 2"], auto, fastforce)
  next
    case False
    thus ?thesis by simp
  qed
  also have "\<dots> = q\<^sup>2 * (\<Sum>j<K - 1. q ^ j)"
    by (simp only: power_add sum_distrib_left mult.assoc mult.commute power2_eq_square)
  also have "\<dots> \<le> q\<^sup>2 * 2"
  proof (rule mult_left_mono)
    have "(\<Sum>j<K - 1. q ^ j) \<le> (\<Sum>j<K - 1. (1/2) ^ j)"
      by (rule sum_mono) (rule power_mono[OF qh q0])
    also have "\<dots> \<le> 2"
    proof (cases "K - 1 = 0")
      case True
      thus ?thesis by simp
    next
      case False
      have "(\<Sum>j<K - 1. (1/2::real) ^ j) = (1 - (1/2) ^ (K - 1)) / (1 - 1/2)"
        by (subst geometric_sum, auto)
      also have "\<dots> \<le> 2"
        by simp
      finally show ?thesis.
    qed
    finally show "(\<Sum>j<K - 1. q ^ j) \<le> 2".
    show "0 \<le> q\<^sup>2" by simp
  qed
  finally show ?thesis by simp
qed

text \<open>Block sums of a majorized family are geometrically bounded.\<close>

lemma ra_profile_le_majorized:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes t0: "0 < t" and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
  shows "ra_profile bphi k \<le> M / t ^ k"
proof -
  have summ: "ra_weighted_abs t (\<lambda>\<beta>. norm (bphi \<beta>)) summable_on ra_idx"
    and inf_le: "(\<Sum>\<^sub>\<infinity>\<beta>\<in>ra_idx. ra_weighted_abs t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>) \<le> M"
    using majb by (simp_all add: ra_majorized_def)
  have blk_le: "(\<Sum>\<beta>\<in>(ra_deg_block k :: ('a \<Rightarrow> nat) set). ra_weighted_abs t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>)
      \<le> (\<Sum>\<^sub>\<infinity>\<beta>\<in>ra_idx. ra_weighted_abs t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>)"
  proof (rule finite_sum_le_infsum[OF summ finite_ra_deg_block])
    show "(ra_deg_block k :: ('a \<Rightarrow> nat) set) \<subseteq> ra_idx" by (auto simp: ra_deg_block_def)
    show "\<And>\<beta>. \<beta> \<in> ra_idx - (ra_deg_block k :: ('a \<Rightarrow> nat) set) \<Longrightarrow>
            0 \<le> ra_weighted_abs t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>"
      using t0 by (simp add: ra_weighted_abs_nonneg)
  qed
  have blk_eq: "(\<Sum>\<beta>\<in>(ra_deg_block k :: ('a \<Rightarrow> nat) set). ra_weighted_abs t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>)
      = ra_profile bphi k * t ^ k"
    unfolding ra_weighted_abs_def ra_profile_def
    by (simp add: ra_deg_block_def sum_distrib_right)
  have "ra_profile bphi k * t ^ k \<le> M"
    using blk_le blk_eq inf_le by simp
  thus ?thesis
    using t0 by (simp add: field_simps)
qed

text \<open>Single coefficients of a majorized family are geometrically bounded.\<close>

lemma coeff_le_majorized:
  fixes u :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  assumes t0: "0 < t" and majb: "ra_majorized t u M"
    and unn: "\<And>\<beta>. 0 \<le> u \<beta>" and b: "\<beta> \<in> ra_idx"
  shows "u \<beta> \<le> M / t ^ ra_deg \<beta>"
proof -
  have summ: "ra_weighted_abs t u summable_on ra_idx"
    and inf_le: "(\<Sum>\<^sub>\<infinity>\<beta>\<in>ra_idx. ra_weighted_abs t u \<beta>) \<le> M"
    using majb by (simp_all add: ra_majorized_def)
  have "(\<Sum>\<beta>'\<in>{\<beta>}. ra_weighted_abs t u \<beta>') \<le> (\<Sum>\<^sub>\<infinity>\<beta>'\<in>ra_idx. ra_weighted_abs t u \<beta>')"
    by (rule finite_sum_le_infsum[OF summ])
       (use b t0 in \<open>auto simp: ra_weighted_abs_nonneg\<close>)
  hence "u \<beta> * t ^ ra_deg \<beta> \<le> M"
    using inf_le unn by (simp add: ra_weighted_abs_def abs_of_nonneg)
  thus ?thesis
    using t0 by (simp add: field_simps)
qed

text \<open>The profile of the fixed point obeys the composition recursion.\<close>

lemma ra_profile_inverse_coeffs_rec:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  shows "ra_profile (ra_inverse_coeffs bphi) d
      \<le> ra_profile (ra_coeff_id :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) d + (\<Sum>k=2..d. ra_profile bphi k * ra_seq_conv_pow (ra_profile (ra_inverse_coeffs bphi)) k d)"
proof -
  have "ra_profile (ra_inverse_coeffs bphi) d = ra_profile (ra_inverse_step bphi (ra_inverse_coeffs bphi)) d"
    unfolding ra_profile_def
    by (rule sum.cong[OF refl])
       (simp add: ra_deg_block_def ra_inverse_coeffs_fixed_point)
  also have "\<dots> \<le> ra_profile (ra_coeff_id :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) d + (\<Sum>k=2..d. ra_profile bphi k * ra_seq_conv_pow (ra_profile (ra_inverse_coeffs bphi)) k d)"
    by (rule ra_profile_inverse_step)
  finally show ?thesis .
qed

lemma ra_profile_inverse_coeffs_0:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  shows "ra_profile (ra_inverse_coeffs bphi) 0 = 0"
  by (simp add: ra_profile_def ra_deg_block_0 ra_inverse_coeffs_idx_zero)

text \<open>The bootstrap: the weighted partial profile sums of \<open>ra_inverse_coeffs\<close> never exceed \<open>2n\<sigma>\<close>.\<close>

lemma ra_inverse_coeffs_partial_sums_bounded:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  defines "A \<equiv> ra_profile (ra_inverse_coeffs bphi)"
  assumes t0: "0 < t" and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows "(\<Sum>i=1..N. A i * \<sigma> ^ i) \<le> 2 * n * \<sigma>"
proof (induction N)
  case 0
  have "0 \<le> 2 * n * \<sigma>"
    using s0 by (simp add: n_def)
  thus ?case by simp
next
  case (Suc N)
  define W where "W = (\<Sum>i=1..N. A i * \<sigma> ^ i)"
  have Wnn: "0 \<le> W"
    unfolding W_def A_def
    by (intro sum_nonneg mult_nonneg_nonneg ra_profile_nonneg zero_le_power) (use s0 in simp)
  have WB: "W \<le> 2 * n * \<sigma>"
    unfolding W_def by (rule Suc.IH)
  have n1: "1 \<le> n"
    unfolding n_def
    by simp
  have M0: "0 \<le> M"
  proof -
    have "0 \<le> (\<Sum>\<^sub>\<infinity>\<beta>\<in>ra_idx. ra_weighted_abs t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>)"
      using t0 by (intro infsum_nonneg) (simp add: ra_weighted_abs_nonneg)
    also have "\<dots> \<le> M" using majb by (simp add: ra_majorized_def)
    finally show ?thesis .
  qed
  have A0: "A 0 = 0" unfolding A_def by (rule ra_profile_inverse_coeffs_0)
  have Ann: "\<And>i. 0 \<le> A i" unfolding A_def by (rule ra_profile_nonneg)
  have mknn: "\<And>k. 0 \<le> ra_profile bphi k" by (rule ra_profile_nonneg)
  have mkle: "\<And>k. ra_profile bphi k \<le> M / t ^ k"
    by (rule ra_profile_le_majorized[OF t0 majb])

  \<comment> \<open>step 1: the per-degree recursion, weighted and summed\<close>
  have "(\<Sum>i=1..Suc N. A i * \<sigma> ^ i)
      \<le> (\<Sum>i=1..Suc N. (ra_profile (ra_coeff_id :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) i
            + (\<Sum>k=2..i. ra_profile bphi k * ra_seq_conv_pow A k i)) * \<sigma> ^ i)"
    unfolding A_def
    by (rule sum_mono, rule mult_right_mono)
       (rule ra_profile_inverse_coeffs_rec, use s0 in simp)
  also have "\<dots> = (\<Sum>i=1..Suc N. ra_profile (ra_coeff_id :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) i * \<sigma> ^ i)
      + (\<Sum>i=1..Suc N. (\<Sum>k=2..i. ra_profile bphi k * ra_seq_conv_pow A k i) * \<sigma> ^ i)"
    by (simp add: algebra_simps sum.distrib)
  also have "\<dots> \<le> n * \<sigma>
      + (\<Sum>i=1..Suc N. (\<Sum>k=2..i. ra_profile bphi k * ra_seq_conv_pow A k i) * \<sigma> ^ i)"
  proof -
    have "(\<Sum>i=1..Suc N. ra_profile (ra_coeff_id :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) i * \<sigma> ^ i)
        \<le> (\<Sum>i=1..Suc N. (if i = 1 then n else 0) * \<sigma> ^ i)"
    proof (rule sum_mono)
      fix i
      assume i: "i \<in> {1..Suc N}"
      have cid_le: "ra_profile (ra_coeff_id :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) i \<le> (if i = 1 then n else 0)"
        using n_def ra_profile_coeff_id by blast
      have sig_nonneg: "0 \<le> \<sigma> ^ i"
        using s0 by simp
      show "ra_profile (ra_coeff_id :: ('a \<Rightarrow> nat) \<Rightarrow> 'a) i * \<sigma> ^ i
          \<le> (if i = 1 then n else 0) * \<sigma> ^ i"
        by (rule mult_right_mono[OF cid_le sig_nonneg])
    qed
    also have "\<dots> = n * \<sigma>"
    proof -
      have "{1..Suc N} = insert 1 {2..Suc N}"
        by auto
      then have "(\<Sum>i=1..Suc N. (if i = 1 then n else 0) * \<sigma> ^ i)
          = n * \<sigma> + (\<Sum>i=2..Suc N. (if i = 1 then n else 0) * \<sigma> ^ i)"
        by simp
      also have "\<dots> = n * \<sigma>"
        by simp
      finally show ?thesis .
    qed
    finally show ?thesis
      by linarith
  qed
  also have "\<dots> \<le> n * \<sigma> + M * (2 * (W / t)\<^sup>2)"
  proof -
    \<comment> \<open>extend the inner \<open>k\<close>-range (vanishing above the diagonal), swap, apply the key bound\<close>
    have diag: "\<And>i. i \<in> {1..Suc N} \<Longrightarrow>
        (\<Sum>k=2..i. ra_profile bphi k * ra_seq_conv_pow A k i)
          = (\<Sum>k=2..Suc N. ra_profile bphi k * ra_seq_conv_pow A k i)"
    proof -
      fix i assume i: "i \<in> {1..Suc N}"
      show "(\<Sum>k=2..i. ra_profile bphi k * ra_seq_conv_pow A k i)
          = (\<Sum>k=2..Suc N. ra_profile bphi k * ra_seq_conv_pow A k i)"
      proof (rule sum.mono_neutral_left)
        show "finite {2..Suc N}" by simp
        show "{2..i} \<subseteq> {2..Suc N}" using i by auto
        show "\<forall>k\<in>{2..Suc N} - {2..i}. ra_profile bphi k * ra_seq_conv_pow A k i = 0"
        proof
          fix k assume "k \<in> {2..Suc N} - {2..i}"
          hence "i < k" by auto
          thus "ra_profile bphi k * ra_seq_conv_pow A k i = 0"
            by (simp add: A0 ra_seq_conv_pow_vanish)
        qed
      qed
    qed
    have "(\<Sum>i=1..Suc N. (\<Sum>k=2..i. ra_profile bphi k * ra_seq_conv_pow A k i) * \<sigma> ^ i)
        = (\<Sum>i=1..Suc N. \<Sum>k=2..Suc N. ra_profile bphi k * ra_seq_conv_pow A k i * \<sigma> ^ i)"
    proof (rule sum.cong[OF refl])
      fix x :: nat
      assume "x \<in> {1..Suc N}"
      then have "(\<Sum>n = 2..x. ra_profile bphi n * ra_seq_conv_pow A n x) * \<sigma> ^ x = (\<Sum>n = 2..Suc N. ra_profile bphi n * ra_seq_conv_pow A n x) * \<sigma> ^ x"
        using diag by moura
      then show "(\<Sum>n = 2..x. ra_profile bphi n * ra_seq_conv_pow A n x) * \<sigma> ^ x = (\<Sum>n = 2..Suc N. ra_profile bphi n * ra_seq_conv_pow A n x * \<sigma> ^ x)"
        by (metis (no_types) sum_distrib_right)
    qed
    also have "\<dots> = (\<Sum>k=2..Suc N. \<Sum>i=1..Suc N. ra_profile bphi k * ra_seq_conv_pow A k i * \<sigma> ^ i)"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>k=2..Suc N. ra_profile bphi k * (\<Sum>i=1..Suc N. ra_seq_conv_pow A k i * \<sigma> ^ i))"
      by (simp add: sum_distrib_left algebra_simps)
    also have "\<dots> \<le> (\<Sum>k=2..Suc N. (M / t ^ k) * W ^ k)"
    proof (rule sum_mono)
      fix k assume k: "k \<in> {2..Suc N}"
      hence k2: "2 \<le> k" by simp
      have inner_le: "(\<Sum>i=1..Suc N. ra_seq_conv_pow A k i * \<sigma> ^ i) \<le> W ^ k"
      proof -
        have ext: "(\<Sum>i=1..Suc N. ra_seq_conv_pow A k i * \<sigma> ^ i)
            = (\<Sum>i\<le>Suc N. ra_seq_conv_pow A k i * \<sigma> ^ i)"
        proof -
          have "{..Suc N} = insert 0 {1..Suc N}" by auto
          moreover have "ra_seq_conv_pow A k 0 = 0"
            using A0 k2 ra_seq_conv_pow_vanish by force
          ultimately show ?thesis by simp
        qed
        have "(\<Sum>i\<le>Suc N. ra_seq_conv_pow A k i * \<sigma> ^ i)
            \<le> (\<Sum>i=1..Suc N + 1 - k. A i * \<sigma> ^ i) ^ k"
          by (metis (no_types, lifting) A0 Ann Suc_eq_plus1 add_leE k2 linorder_le_cases
              linorder_not_le ra_seq_conv_pow_partial_sum_le numeral_2_eq_2 s0)
        also have "\<dots> \<le> W ^ k"
        proof (rule power_mono)
          show "(\<Sum>i=1..Suc N + 1 - k. A i * \<sigma> ^ i) \<le> W"
            unfolding W_def
          proof (rule sum_mono2)
            show "finite {1..N}" by simp
            show "{1..Suc N + 1 - k} \<subseteq> {1..N}" using k2 by auto
            show "\<And>i. i \<in> {1..N} - {1..Suc N + 1 - k} \<Longrightarrow> 0 \<le> A i * \<sigma> ^ i"
              by (intro mult_nonneg_nonneg Ann zero_le_power) (use s0 in simp)
          qed
          show "0 \<le> (\<Sum>i=1..Suc N + 1 - k. A i * \<sigma> ^ i)"
            by (intro sum_nonneg mult_nonneg_nonneg Ann zero_le_power) (use s0 in simp)
        qed
        finally show ?thesis using ext by simp
      qed
      have Wknn: "0 \<le> (\<Sum>i=1..Suc N. ra_seq_conv_pow A k i * \<sigma> ^ i)"
        by (intro sum_nonneg mult_nonneg_nonneg ra_seq_conv_pow_nonneg[OF Ann] zero_le_power)
           (use s0 in simp)
      have "ra_profile bphi k * (\<Sum>i=1..Suc N. ra_seq_conv_pow A k i * \<sigma> ^ i)
          \<le> (M / t ^ k) * (\<Sum>i=1..Suc N. ra_seq_conv_pow A k i * \<sigma> ^ i)"
        by (rule mult_right_mono[OF mkle Wknn])
      also have "\<dots> \<le> (M / t ^ k) * W ^ k"
        by (rule mult_left_mono[OF inner_le])
           (use M0 t0 in \<open>simp add: divide_nonneg_pos\<close>)
      finally show "ra_profile bphi k * (\<Sum>i=1..Suc N. ra_seq_conv_pow A k i * \<sigma> ^ i)
          \<le> (M / t ^ k) * W ^ k" .
    qed
    also have "\<dots> = M * (\<Sum>k=2..Suc N. (W / t) ^ k)"
      by (simp add: power_divide sum_distrib_left algebra_simps)
       also have "\<dots> \<le> M * (2 * (W / t)\<^sup>2)"
    proof (rule mult_left_mono[OF _ M0])
      have Wt_nn: "0 \<le> W / t" using Wnn t0 by simp
      have "W / t \<le> 1/2"
      proof -
        have "W \<le> 2 * n * \<sigma>" by (rule WB)
        also have "\<dots> \<le> 2 * n * (t / (4 * n))"
          using s1 n1 by (intro mult_left_mono) simp_all
        also have "\<dots> = t / 2"
          using n1 by (simp add: field_simps)
        finally have "W \<le> t / 2" .
        thus ?thesis using t0 by (simp add: divide_le_eq)
      qed
      thus "(\<Sum>k=2..Suc N. (W / t) ^ k) \<le> 2 * (W / t)\<^sup>2"
        using geom_tail_le[OF Wt_nn] by presburger
    qed
    finally have conv_bound:
      "(\<Sum>i=1..Suc N. (\<Sum>k=2..i. ra_profile bphi k * ra_seq_conv_pow A k i) * \<sigma> ^ i)
        \<le> M * (2 * (W / t)\<^sup>2)" .
    show ?thesis
      using conv_bound by linarith
  qed
  also have "\<dots> \<le> n * \<sigma> + n * \<sigma>"
  proof -
    have "M * (2 * (W / t)\<^sup>2) \<le> n * \<sigma>"
    proof -
      have "M * (2 * (W / t)\<^sup>2) = 2 * M * W\<^sup>2 / t\<^sup>2"
        by (simp add: power_divide)
      also have "\<dots> \<le> 2 * M * (2 * n * \<sigma>)\<^sup>2 / t\<^sup>2"
        using WB Wnn M0 t0
        by (intro divide_right_mono mult_left_mono power_mono) simp_all
      also have "\<dots> = 8 * M * n\<^sup>2 * \<sigma>\<^sup>2 / t\<^sup>2"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> \<le> n * \<sigma>"
      proof -
        have "8 * (M + 1) * n * \<sigma> \<le> t\<^sup>2"
        proof -
          have pos: "0 < 8 * (M + 1) * n"
            using M0 n1 by (intro mult_pos_pos) simp_all
          have "\<sigma> * (8 * (M + 1) * n)
              \<le> (t\<^sup>2 / (8 * (M + 1) * n)) * (8 * (M + 1) * n)"
            by (rule mult_right_mono[OF s2]) (use pos in simp)
          also have "\<dots> = t\<^sup>2"
            using pos by (simp add: field_simps)
          finally show ?thesis
            by (simp add: mult_ac)
        qed
        moreover have "8 * M * n * \<sigma> \<le> 8 * (M + 1) * n * \<sigma>"
          using n1 s0 by (intro mult_right_mono) (simp_all add: algebra_simps)
        ultimately have "8 * M * n * \<sigma> \<le> t\<^sup>2"
          by linarith
        hence "8 * M * n * \<sigma> * (n * \<sigma>) \<le> t\<^sup>2 * (n * \<sigma>)"
          using n1 s0 by (intro mult_right_mono) simp_all
        hence "8 * M * n\<^sup>2 * \<sigma>\<^sup>2 \<le> t\<^sup>2 * (n * \<sigma>)"
          by (simp add: power2_eq_square algebra_simps)
        thus ?thesis
          using t0 by (simp add: pos_divide_le_eq, argo)

      qed
      finally show ?thesis .
    qed
    thus ?thesis by linarith
  qed
  also have "\<dots> = 2 * n * \<sigma>" by simp
  finally show ?case .
qed

text \<open>The majorant bound for @{const ra_inverse_coeffs}, and the induced bounds for the composed
  monomial families.\<close>

lemma ra_majorized_of_partial_profile_bounds:
  fixes u :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  assumes unn: "\<And>\<gamma>. 0 \<le> u \<gamma>"
    and s0: "0 < \<sigma>"
    and bnd: "\<And>D. (\<Sum>d\<le>D. ra_profile_real u d * \<sigma> ^ d) \<le> B"
  shows "ra_majorized \<sigma> u B"
proof -
  have partial: "(\<Sum>\<gamma>\<in>F. ra_weighted_abs \<sigma> u \<gamma>) \<le> B" if F: "finite F" "F \<subseteq> ra_idx" for F
  proof -
    define D where "D = Max (insert 0 (ra_deg ` F))"
    have degF: "\<And>\<gamma>. \<gamma> \<in> F \<Longrightarrow> ra_deg \<gamma> \<le> D"
      unfolding D_def using F(1) by (intro Max_ge) auto
    have Fsub: "F \<subseteq> (\<Union>d\<in>{..D}. ra_deg_block d)"
      using F(2) degF by (auto simp: ra_deg_block_def)
    have "(\<Sum>\<gamma>\<in>F. ra_weighted_abs \<sigma> u \<gamma>) \<le> (\<Sum>\<gamma>\<in>(\<Union>d\<in>{..D}. ra_deg_block d). ra_weighted_abs \<sigma> u \<gamma>)"
      by (rule sum_mono2[OF _ Fsub],
          auto intro: finite_UN_I finite_ra_deg_block ra_weighted_abs_nonneg simp: ra_weighted_abs_nonneg s0 less_imp_le)
    also have "\<dots> = (\<Sum>d\<le>D. \<Sum>\<gamma>\<in>ra_deg_block d. ra_weighted_abs \<sigma> u \<gamma>)"
      using finite_ra_deg_block by (subst sum.UNION_disjoint, auto, simp add: disjoint_iff ra_deg_block_def)
    also have "\<dots> = (\<Sum>d\<le>D. ra_profile_real u d * \<sigma> ^ d)"
      unfolding ra_weighted_abs_def ra_profile_real_def
      by (rule sum.cong[OF refl], simp add: ra_deg_block_def sum_distrib_right abs_of_nonneg unn)
    also have "\<dots> \<le> B" by (rule bnd)
    finally show ?thesis .
  qed
  have summ: "ra_weighted_abs \<sigma> u summable_on ra_idx"
  proof (rule nonneg_bdd_above_summable_on)
    show "\<And>\<gamma>. \<gamma> \<in> ra_idx \<Longrightarrow> 0 \<le> ra_weighted_abs \<sigma> u \<gamma>"
      using s0 by (simp add: ra_weighted_abs_nonneg)
    show "bdd_above (sum (ra_weighted_abs \<sigma> u) ` {F. F \<subseteq> ra_idx \<and> finite F})"
      by (rule bdd_aboveI[where M = B]) (use partial in auto)
  qed
  moreover have "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>ra_idx. ra_weighted_abs \<sigma> u \<gamma>) \<le> B"
    by (rule infsum_le_finite_sums[OF summ]) (use partial in auto)
  ultimately show ?thesis by (simp add: ra_majorized_def)
qed

theorem ra_inverse_coeffs_majorized:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows "ra_majorized \<sigma> (\<lambda>\<gamma>. norm (ra_inverse_coeffs bphi \<gamma>)) (2 * n * \<sigma>)"
proof (rule ra_majorized_of_partial_profile_bounds)
  show "\<And>\<gamma>. 0 \<le> norm (ra_inverse_coeffs bphi \<gamma>)" by simp
  show "0 < \<sigma>" by (rule s0)
  fix D :: nat
  have prof_eq: "ra_profile_real (\<lambda>\<gamma>. norm (ra_inverse_coeffs bphi \<gamma>)) = ra_profile (ra_inverse_coeffs bphi)"
    by (rule ext) (simp add: ra_profile_real_def ra_profile_def)
  have "(\<Sum>d\<le>D. ra_profile (ra_inverse_coeffs bphi) d * \<sigma> ^ d) = (\<Sum>d=1..D. ra_profile (ra_inverse_coeffs bphi) d * \<sigma> ^ d)"
  proof -
    have "{..D} = insert 0 {1..D}" by auto
    thus ?thesis by (simp add: ra_profile_inverse_coeffs_0)
  qed
  also have "\<dots> \<le> 2 * n * \<sigma>"
    unfolding n_def
    by (rule ra_inverse_coeffs_partial_sums_bounded[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  finally show "(\<Sum>d\<le>D. ra_profile_real (\<lambda>\<gamma>. norm (ra_inverse_coeffs bphi \<gamma>)) d * \<sigma> ^ d) \<le> 2 * n * \<sigma>"
    by (simp add: prof_eq)
qed

text \<open>A majorant bound on vector coefficients gives an absolutely convergent
  power series on the closed working ball.\<close>

lemma ra_majorized_vector_power_series_summable:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::banach"
  assumes s0: "0 \<le> \<sigma>"
    and maj: "ra_majorized \<sigma> (\<lambda>\<gamma>. norm (c \<gamma>)) K"
    and hle: "norm h \<le> \<sigma>"
  shows "(\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R c \<gamma>) summable_on (ra_idx::('a \<Rightarrow> nat) set)"
proof (rule abs_summable_summable,
    rule summable_on_comparison_test[where f = "ra_weighted_abs \<sigma> (\<lambda>\<gamma>. norm (c \<gamma>))"])
  show "ra_weighted_abs \<sigma> (\<lambda>\<gamma>. norm (c \<gamma>)) summable_on (ra_idx::('a \<Rightarrow> nat) set)"
    using maj by (simp add: ra_majorized_def)
next
  fix \<gamma> :: "'a \<Rightarrow> nat"
  assume g: "\<gamma> \<in> ra_idx"
  have "norm (ra_monomial h \<gamma> *\<^sub>R c \<gamma>) = \<bar>ra_monomial h \<gamma>\<bar> * norm (c \<gamma>)"
    by simp
  also have "\<dots> \<le> \<sigma> ^ ra_deg \<gamma> * norm (c \<gamma>)"
    by (rule mult_right_mono[OF ra_monomial_abs_le_pow[OF g hle]]) simp
  also have "\<dots> = ra_weighted_abs \<sigma> (\<lambda>\<gamma>. norm (c \<gamma>)) \<gamma>"
    by (simp add: ra_weighted_abs_def mult.commute)
  finally show "norm (ra_monomial h \<gamma> *\<^sub>R c \<gamma>) \<le> ra_weighted_abs \<sigma> (\<lambda>\<gamma>. norm (c \<gamma>)) \<gamma>" .
next
  fix \<gamma> :: "'a \<Rightarrow> nat"
  assume "\<gamma> \<in> ra_idx"
  show "0 \<le> norm (ra_monomial h \<gamma> *\<^sub>R c \<gamma>)"
    by simp
qed

lemma ra_majorized_vector_power_series_has_sum:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::banach"
  assumes s0: "0 \<le> \<sigma>"
    and maj: "ra_majorized \<sigma> (\<lambda>\<gamma>. norm (c \<gamma>)) K"
    and hle: "norm h \<le> \<sigma>"
  shows "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R c \<gamma>)
          has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R c \<gamma>))
          (ra_idx::('a \<Rightarrow> nat) set)"
  by (rule has_sum_infsum)
     (rule ra_majorized_vector_power_series_summable[OF s0 maj hle])

corollary ra_inverse_coeffs_power_series_has_sum:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
    and hle: "norm h \<le> \<sigma>"
  shows "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
          has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>))
          (ra_idx::('a \<Rightarrow> nat) set)"
proof (rule ra_majorized_vector_power_series_has_sum)
  show "0 \<le> \<sigma>"
    using s0 by simp
  show "ra_majorized \<sigma> (\<lambda>\<gamma>. norm (ra_inverse_coeffs bphi \<gamma>)) (2 * n * \<sigma>)"
    unfolding n_def
    by (rule ra_inverse_coeffs_majorized[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  show "norm h \<le> \<sigma>"
    by (rule hle)
qed

lemma ra_inverse_coeffs_value_norm_bound_at_scale:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
    and hle: "norm h \<le> \<sigma>"
  shows "norm (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
      \<le> 2 * n * \<sigma>"
proof -
  let ?H = "\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>"
  have hs: "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
      has_sum ?H) (ra_idx::('a \<Rightarrow> nat) set)"
    unfolding n_def
    by (rule ra_inverse_coeffs_power_series_has_sum[OF t0 majb s0])
       (use s1 s2 hle in \<open>simp_all add: n_def\<close>)
  have maj: "ra_majorized \<sigma> (\<lambda>\<gamma>. norm (ra_inverse_coeffs bphi \<gamma>)) (2 * n * \<sigma>)"
    unfolding n_def
    by (rule ra_inverse_coeffs_majorized[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  define S where "S = (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
      ra_weighted_abs \<sigma> (\<lambda>\<gamma>. norm (ra_inverse_coeffs bphi \<gamma>)) \<gamma>)"
  have dom_sum: "((ra_weighted_abs \<sigma> (\<lambda>\<gamma>. norm (ra_inverse_coeffs bphi \<gamma>))) has_sum S)
      (ra_idx::('a \<Rightarrow> nat) set)"
    unfolding S_def using maj by (simp add: ra_majorized_def has_sum_infsum)
  have term_bound: "norm (ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
      \<le> ra_weighted_abs \<sigma> (\<lambda>\<gamma>. norm (ra_inverse_coeffs bphi \<gamma>)) \<gamma>"
    if g: "\<gamma> \<in> (ra_idx::('a \<Rightarrow> nat) set)" for \<gamma>
  proof -
    have "norm (ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
        = \<bar>ra_monomial h \<gamma>\<bar> * norm (ra_inverse_coeffs bphi \<gamma>)"
      by simp
    also have "\<dots> \<le> \<sigma> ^ ra_deg \<gamma> * norm (ra_inverse_coeffs bphi \<gamma>)"
      by (rule mult_right_mono[OF ra_monomial_abs_le_pow[OF g hle]]) simp
    also have "\<dots> = ra_weighted_abs \<sigma> (\<lambda>\<gamma>. norm (ra_inverse_coeffs bphi \<gamma>)) \<gamma>"
      by (simp add: ra_weighted_abs_def mult.commute)
    finally show ?thesis .
  qed
  have "norm ?H \<le> S"
    by (rule norm_infsum_le[OF hs dom_sum]) (use term_bound in simp)
  also have "\<dots> \<le> 2 * n * \<sigma>"
    using maj by (simp add: S_def ra_majorized_def)
  finally show ?thesis .
qed

lemma ra_majorized_geometric_weight_summable:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'b::real_normed_vector"
  assumes t0: "0 < t"
    and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and K0: "0 \<le> K"
    and Kt: "K < t"
  shows "(\<lambda>\<beta>. norm (bphi \<beta>) * K ^ ra_deg \<beta>)
    summable_on (ra_idx::('a \<Rightarrow> nat) set)"
proof (rule summable_on_comparison_test
    [where f = "\<lambda>\<beta>. M * (K / t) ^ ra_deg \<beta>"])
  have M0: "0 \<le> M"
  proof -
    have "0 \<le> (\<Sum>\<^sub>\<infinity>\<beta>\<in>ra_idx. ra_weighted_abs t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>)"
      using t0 by (intro infsum_nonneg) (simp add: ra_weighted_abs_nonneg)
    also have "\<dots> \<le> M"
      using majb by (simp add: ra_majorized_def)
    finally show ?thesis .
  qed
  have q0: "0 \<le> K / t"
    using K0 t0 by simp
  have q1: "K / t < 1"
    using Kt t0 by (simp add: divide_less_eq)
  have "(\<lambda>\<beta>::'a \<Rightarrow> nat. (K / t) ^ ra_deg \<beta>) summable_on ra_idx"
    by (rule geom_idx_summable[OF q0 q1])
  thus "(\<lambda>\<beta>. M * (K / t) ^ ra_deg \<beta>)
      summable_on (ra_idx::('a \<Rightarrow> nat) set)"
    by (rule summable_on_cmult_right)
next
  fix \<beta> :: "'a \<Rightarrow> nat"
  assume b: "\<beta> \<in> ra_idx"
  have "norm (bphi \<beta>) * K ^ ra_deg \<beta>
      \<le> (M / t ^ ra_deg \<beta>) * K ^ ra_deg \<beta>"
    by (rule mult_right_mono[OF coeff_le_majorized[OF t0 majb _ b]])
       (use K0 in simp_all)
  also have "\<dots> = M * (K / t) ^ ra_deg \<beta>"
    using t0 by (simp add: power_divide)
  finally show "norm (bphi \<beta>) * K ^ ra_deg \<beta>
      \<le> M * (K / t) ^ ra_deg \<beta>" .
next
  fix \<beta> :: "'a \<Rightarrow> nat"
  assume "\<beta> \<in> ra_idx"
  show "0 \<le> norm (bphi \<beta>) * K ^ ra_deg \<beta>"
    using K0 by simp
qed

lemma ra_inverse_coeffs_power_series_real_analytic_on_ball_at_scale:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  defines "H \<equiv> (\<lambda>h::'a. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
      ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)"
  assumes t0: "0 < t" and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows "real_analytic_on H (ball (0::'a) (\<sigma> / 2))"
proof -
  have n1: "1 \<le> n"
    unfolding n_def by simp
  have Hmaj: "ra_majorized \<sigma> (\<lambda>\<gamma>. norm (ra_inverse_coeffs bphi \<gamma>)) (2 * n * \<sigma>)"
    unfolding n_def
    by (rule ra_inverse_coeffs_majorized[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  show ?thesis
    unfolding real_analytic_on_def
  proof (intro conjI ballI)
    show "open (ball (0::'a) (\<sigma> / 2))"
      by simp
  next
    fix y0 :: 'a
    assume y0: "y0 \<in> ball (0::'a) (\<sigma> / 2)"
    have y0_lt: "norm y0 < \<sigma> / 2"
      using y0 by (simp add: dist_norm)
    define r where "r = (\<sigma> - norm y0) / (2 * n)"
    have r0: "0 < r"
      using y0_lt n1 s0 by (simp add: r_def)
    have rle: "r \<le> r"
      by simp
    define K where "K = n * r + norm y0"
    have K0: "0 \<le> K"
      using n1 r0 by (simp add: K_def)
    have Klt: "K < \<sigma>"
    proof -
      have "n * r = (\<sigma> - norm y0) / 2"
        using n1 by (simp add: r_def field_simps)
      hence "K = (\<sigma> + norm y0) / 2"
        by (simp add: K_def)
      also have "\<dots> < \<sigma>"
        using y0_lt s0 by simp
      finally show ?thesis .
    qed
    obtain cid :: "('a \<Rightarrow> nat) \<Rightarrow> 'a" where
      cid_series: "\<And>y::'a. ((\<lambda>\<alpha>. ra_monomial y \<alpha> *\<^sub>R cid \<alpha>) has_sum y) ra_idx"
      and cid_maj: "\<And>\<rho>::real. 0 \<le> \<rho> \<Longrightarrow>
        ra_majorized \<rho> (\<lambda>\<alpha>. norm (cid \<alpha>)) (real (card (Basis :: 'a set)) * \<rho>)"
    proof -
      show thesis
      proof (rule identity_coeff_series_majorized)
        fix cid :: "('a \<Rightarrow> nat) \<Rightarrow> 'a"
        assume cid_series: "\<And>y::'a. ((\<lambda>\<alpha>. ra_monomial y \<alpha> *\<^sub>R cid \<alpha>) has_sum y) ra_idx"
          and cid_maj: "\<And>\<rho>::real. 0 \<le> \<rho> \<Longrightarrow>
            ra_majorized \<rho> (\<lambda>\<alpha>. norm (cid \<alpha>)) (real (card (Basis :: 'a set)) * \<rho>)"
        show thesis
          by (rule that[OF cid_series cid_maj])
      qed
    qed
    have id_ser: "\<And>x. dist x y0 < r \<Longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (x - y0) \<alpha> *\<^sub>R cid \<alpha>) has_sum (x - y0))
          (ra_idx::('a \<Rightarrow> nat) set)"
      using cid_series by simp
    have cidmaj_r: "ra_majorized r (\<lambda>\<alpha>. norm (cid \<alpha>)) (n * r)"
      using cid_maj[of r] r0 by (simp add: n_def)
    have mon_ser: "\<exists>cc. ra_series_majorized y0 r r cc (\<lambda>x::'a. ra_monomial x \<beta>) (K ^ ra_deg \<beta>)"
      if b: "\<beta> \<in> (ra_idx::('a \<Rightarrow> nat) set)" for \<beta>
    proof -
      have raw: "\<exists>cc. ra_series_majorized y0 r r cc
          (\<lambda>x::'a. ra_monomial ((x - y0) - (- y0)) \<beta>) (K ^ ra_deg \<beta>)"
      proof (rule ra_series_majorized_ra_monomial_compose[where z = "- y0", OF _ id_ser cidmaj_r _ K0])
        show "0 \<le> r"
          using r0 by simp
        fix e :: 'a
        assume e: "e \<in> Basis"
        have "\<bar>(- y0) \<bullet> e\<bar> \<le> norm y0"
          using Basis_le_norm[OF e, of "- y0"] by simp
        thus "n * r + \<bar>(- y0) \<bullet> e\<bar> \<le> K"
          by (simp add: K_def)
      qed
      thus ?thesis
        by simp
    qed
    obtain CC where CC:
      "\<And>\<beta>. \<beta> \<in> (ra_idx::('a \<Rightarrow> nat) set) \<Longrightarrow>
        ra_series_majorized y0 r r (CC \<beta>) (\<lambda>x::'a. ra_monomial x \<beta>) (K ^ ra_deg \<beta>)"
      using mon_ser by metis
    have ser: "ra_series_on y0 r (CC \<beta>) (\<lambda>x::'a. ra_monomial x \<beta>)"
      if b: "\<beta> \<in> (ra_idx::('a \<Rightarrow> nat) set)" for \<beta>
      using CC[OF b] by (simp add: ra_series_majorized_def)
    have maj: "ra_majorized r (CC \<beta>) (K ^ ra_deg \<beta>)"
      if b: "\<beta> \<in> (ra_idx::('a \<Rightarrow> nat) set)" for \<beta>
      using CC[OF b] by (simp add: ra_series_majorized_def)
    have gsum: "(\<lambda>\<beta>. norm (ra_inverse_coeffs bphi \<beta>) * (K ^ ra_deg \<beta>))
      summable_on (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule ra_majorized_geometric_weight_summable[OF s0 Hmaj K0 Klt])
    have Gval: "\<And>x::'a. dist x y0 < r \<Longrightarrow>
        ((\<lambda>\<beta>. ra_monomial x \<beta> *\<^sub>R ra_inverse_coeffs bphi \<beta>) has_sum H x)
          (ra_idx::('a \<Rightarrow> nat) set)"
    proof -
      fix x :: 'a
      assume x: "dist x y0 < r"
      have nx: "norm x \<le> \<sigma>"
      proof -
        have "norm x \<le> norm (x - y0) + norm y0"
          by (metis add.commute add_diff_cancel_left' norm_triangle_sub)
        also have "\<dots> < r + norm y0"
          using x by (simp add: dist_norm)
        also have "\<dots> \<le> n * r + norm y0"
          using n1 r0 by (intro add_right_mono mult_left_le_one_le) simp_all
        also have "\<dots> = K"
          by (simp add: K_def)
        also have "\<dots> < \<sigma>"
          by (rule Klt)
        finally show ?thesis
          by simp
      qed
      show "((\<lambda>\<beta>. ra_monomial x \<beta> *\<^sub>R ra_inverse_coeffs bphi \<beta>) has_sum H x)
          (ra_idx::('a \<Rightarrow> nat) set)"
        unfolding H_def n_def
        by (rule ra_inverse_coeffs_power_series_has_sum[OF t0 majb s0])
           (use s1 s2 nx in \<open>simp_all add: n_def\<close>)
    qed
    have recentered: "\<forall>x. dist x y0 < r \<longrightarrow>
       ((\<lambda>\<gamma>. ra_monomial (x - y0) \<gamma> *\<^sub>R
          (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set). CC \<beta> \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<beta>))
        has_sum H x) (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule ra_series_on_majdom_vec[OF r0 rle ser maj gsum Gval])
    show "\<exists>r>0. \<exists>c. \<forall>x. dist x y0 < r \<longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial (x - y0) \<alpha> *\<^sub>R c \<alpha>) has_sum H x)
          (ra_idx::('a \<Rightarrow> nat) set)"
      by (intro exI[where x=r] conjI exI[where x="\<lambda>\<gamma>. \<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            CC \<beta> \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<beta>"]) (use r0 recentered in auto)
  qed
qed

corollary ra_inverse_coeffs_power_series_converges_near_zero:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes t0: "0 < t"
    and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
  obtains \<sigma> where "0 < \<sigma>"
    and "\<And>h::'a. norm h < \<sigma> \<Longrightarrow>
      ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
        has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>))
        (ra_idx::('a \<Rightarrow> nat) set)"
proof -
  define n where "n = real (card (Basis :: 'a set))"
  have n1: "1 \<le> n"
    unfolding n_def by simp
  have M0: "0 \<le> M"
  proof -
    have "0 \<le> (\<Sum>\<^sub>\<infinity>\<beta>\<in>ra_idx. ra_weighted_abs t (\<lambda>\<beta>. norm (bphi \<beta>)) \<beta>)"
      using t0 by (intro infsum_nonneg) (simp add: ra_weighted_abs_nonneg)
    also have "\<dots> \<le> M"
      using majb by (simp add: ra_majorized_def)
    finally show ?thesis .
  qed
  define \<sigma> where "\<sigma> = min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n)) / 2"
  have a_pos: "0 < t / (4 * n)"
    using t0 n1 by simp
  have b_pos: "0 < t\<^sup>2 / (8 * (M + 1) * n)"
    using t0 M0 n1 by (intro divide_pos_pos mult_pos_pos) simp_all
  have \<sigma>0: "0 < \<sigma>"
    using a_pos b_pos by (simp add: \<sigma>_def)
  have min_nonneg: "0 \<le> min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n))"
    using a_pos b_pos by simp
  have half_min_le:
    "min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n)) / 2
      \<le> min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n))"
  proof -
    have "min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n)) / 2
        = (1/2) * min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n))"
      by simp
    also have "\<dots> \<le> 1 * min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n))"
      by (rule mult_right_mono) (use min_nonneg in simp_all)
    finally show ?thesis
      by simp
  qed
  have s1: "\<sigma> \<le> t / (4 * n)"
  proof -
    have "\<sigma> \<le> min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n))"
      unfolding \<sigma>_def by (rule half_min_le)
    also have "\<dots> \<le> t / (4 * n)"
      by simp
    finally show ?thesis .
  qed
  have s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  proof -
    have "\<sigma> \<le> min (t / (4 * n)) (t\<^sup>2 / (8 * (M + 1) * n))"
      unfolding \<sigma>_def by (rule half_min_le)
    also have "\<dots> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
      by simp
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule that[OF \<sigma>0])
    fix h :: 'a
    assume h: "norm h < \<sigma>"
    have s1': "\<sigma> \<le> t / (4 * real DIM('a))"
      using s1 by (simp add: n_def)
    have s2': "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * real DIM('a))"
      using s2 by (simp add: n_def)
    show "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
        has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>))
        (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule ra_inverse_coeffs_power_series_has_sum[OF t0 majb \<sigma>0 s1' s2'])
         (use h in simp)
  qed
qed

theorem ra_inverse_coeffs_formal_inverse_data:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes t0: "0 < t"
    and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and low: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> ra_deg \<beta> < 2 \<Longrightarrow> bphi \<beta> = 0"
  obtains \<sigma> where "0 < \<sigma>"
    and "\<And>h::'a. norm h < \<sigma> \<Longrightarrow>
      ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
        has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>))
        (ra_idx::('a \<Rightarrow> nat) set)"
    and "\<And>\<gamma>. \<gamma> \<in> ra_idx \<Longrightarrow>
      ra_inverse_coeffs bphi \<gamma> =
        ra_coeff_id \<gamma> + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
proof -
  show ?thesis
  proof (rule ra_inverse_coeffs_power_series_converges_near_zero[OF t0 majb])
    fix \<sigma>
    assume s0: "0 < \<sigma>"
      and conv: "\<And>h::'a. norm h < \<sigma> \<Longrightarrow>
        ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
          has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>))
          (ra_idx::('a \<Rightarrow> nat) set)"
    have coeff: "\<And>\<gamma>. \<gamma> \<in> ra_idx \<Longrightarrow>
        ra_inverse_coeffs bphi \<gamma> =
          ra_coeff_id \<gamma> + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)"
      by (rule ra_inverse_coeffs_coeff_equation_infsum[OF _ low])
    show thesis
      by (rule that[OF s0 conv coeff])
  qed
qed

corollary ra_inverse_coeffs_component_series_on_near_zero:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes t0: "0 < t"
    and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
  obtains \<sigma> where "0 < \<sigma>"
    and "\<And>b. b \<in> Basis \<Longrightarrow>
      ra_series_on (0::'a) \<sigma> (\<lambda>\<gamma>. ra_inverse_coeffs bphi \<gamma> \<bullet> b)
        (\<lambda>h. (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<bullet> b)"
proof -
  show ?thesis
  proof (rule ra_inverse_coeffs_power_series_converges_near_zero[OF t0 majb])
    fix \<sigma>
    assume s0: "0 < \<sigma>"
      and conv: "\<And>h::'a. norm h < \<sigma> \<Longrightarrow>
        ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
          has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>))
          (ra_idx::('a \<Rightarrow> nat) set)"
    have ser: "ra_series_on (0::'a) \<sigma> (\<lambda>\<gamma>. ra_inverse_coeffs bphi \<gamma> \<bullet> b)
        (\<lambda>h. (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<bullet> b)"
      if b: "b \<in> Basis" for b
      unfolding ra_series_on_def
    proof (intro allI impI)
      fix h :: 'a
      assume h: "dist h (0::'a) < \<sigma>"
      have hs: "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
          has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>))
          (ra_idx::('a \<Rightarrow> nat) set)"
        by (rule conv) (use h in \<open>simp add: dist_norm\<close>)
      have "((\<lambda>\<gamma>. (ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<bullet> b)
          has_sum ((\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<bullet> b))
          (ra_idx::('a \<Rightarrow> nat) set)"
        by (rule has_sum_bounded_linear[OF bounded_linear_inner_left hs])
      thus "((\<lambda>\<gamma>. ra_monomial (h - 0) \<gamma> *\<^sub>R (ra_inverse_coeffs bphi \<gamma> \<bullet> b))
          has_sum ((\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<bullet> b))
          (ra_idx::('a \<Rightarrow> nat) set)"
        by simp
    qed
    show thesis
      by (rule that[OF s0 ser])
  qed
qed

corollary ra_inverse_coeffs_mono_coeffs_series_on_near_zero:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes t0: "0 < t"
    and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
  obtains \<sigma> where "0 < \<sigma>"
    and "\<And>\<beta>. ra_series_on (0::'a) \<sigma> (ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta>)
      (\<lambda>h. ra_monomial
        (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<beta>)"
proof -
  show ?thesis
  proof (rule ra_inverse_coeffs_power_series_converges_near_zero[OF t0 majb])
    fix \<sigma>
    assume s0: "0 < \<sigma>"
      and conv: "\<And>h::'a. norm h < \<sigma> \<Longrightarrow>
        ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
          has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>))
          (ra_idx::('a \<Rightarrow> nat) set)"
    have ser: "ra_series_on (0::'a) \<sigma> (ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta>)
      (\<lambda>h. ra_monomial
        (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<beta>)"
      for \<beta>
      by (rule ra_mono_coeffs_series[where c = "ra_inverse_coeffs bphi"])
         (use conv in \<open>simp add: dist_norm\<close>)
    show thesis
      by (rule that[OF s0 ser])
  qed
qed

text \<open>Majorant bounds for the composed monomial families of any family without constant term
  whose weighted profile partial sums are bounded.\<close>

lemma ra_mono_coeffs_majorized:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  assumes s0: "0 < \<sigma>"
    and Bnn: "0 \<le> B"
    and bnd: "\<And>D. (\<Sum>i=1..D. ra_profile c i * \<sigma> ^ i) \<le> B"
    and A0: "ra_profile c 0 = 0"
  shows "ra_majorized \<sigma> (ra_mono_coeffs c \<beta>) (B ^ ra_deg \<beta>)"
proof -
  have majabs: "ra_majorized \<sigma> (\<lambda>\<gamma>. \<bar>ra_mono_coeffs c \<beta> \<gamma>\<bar>) (B ^ ra_deg \<beta>)"
  proof (rule ra_majorized_of_partial_profile_bounds)
    show "\<And>\<gamma>. 0 \<le> \<bar>ra_mono_coeffs c \<beta> \<gamma>\<bar>" by simp
    show "0 < \<sigma>" by (rule s0)
    fix D :: nat
    have prof_eq: "ra_profile_real (\<lambda>\<gamma>. \<bar>ra_mono_coeffs c \<beta> \<gamma>\<bar>) = ra_profile_real (ra_mono_coeffs c \<beta>)"
      by (rule ext) (simp add: ra_profile_real_def)
    show "(\<Sum>d\<le>D. ra_profile_real (\<lambda>\<gamma>. \<bar>ra_mono_coeffs c \<beta> \<gamma>\<bar>) d * \<sigma> ^ d) \<le> B ^ ra_deg \<beta>"
    proof (cases "ra_deg \<beta> = 0")
      case True
      \<comment> \<open>degree-zero monomial: the coefficients are (at most) the \<open>ra_coeff_one\<close> family\<close>
      have "(\<Sum>d\<le>D. ra_profile_real (ra_mono_coeffs c \<beta>) d * \<sigma> ^ d)
          \<le> (\<Sum>d\<le>D. ra_seq_conv_pow (ra_profile c) 0 d * \<sigma> ^ d)"
        by (smt (verit) True mult_right_mono ra_profile_real_mono_coeffs s0 sum_mono zero_le_power)
      also have "\<dots> = 1"
      proof -
        have "{..D} = insert 0 {1..D}" by auto
        thus ?thesis
          by (simp add: ra_seq_delta_def)
      qed
      finally show ?thesis
        using True by (simp add: prof_eq)
    next
      case False
      hence k1: "1 \<le> ra_deg \<beta>" by simp
      have "(\<Sum>d\<le>D. ra_profile_real (ra_mono_coeffs c \<beta>) d * \<sigma> ^ d)
          \<le> (\<Sum>d\<le>D. ra_seq_conv_pow (ra_profile c) (ra_deg \<beta>) d * \<sigma> ^ d)"
        by (rule sum_mono, rule mult_right_mono)
           (use ra_profile_real_mono_coeffs s0 in simp_all)
      also have "\<dots> \<le> (\<Sum>i=1..D + 1 - ra_deg \<beta>. ra_profile c i * \<sigma> ^ i) ^ ra_deg \<beta>"
        apply (rule ra_seq_conv_pow_partial_sum_le)
        apply (simp add: ra_profile_nonneg)
        apply (simp add: A0)
        using s0 apply fastforce
        using k1 by blast
      also have "\<dots> \<le> B ^ ra_deg \<beta>"
        by (rule power_mono[OF bnd])
           (intro sum_nonneg mult_nonneg_nonneg ra_profile_nonneg zero_le_power,
            use s0 in simp)
      finally show ?thesis by (simp add: prof_eq)
    qed
  qed
  \<comment> \<open>transfer from the absolute-value family: \<open>ra_weighted_abs\<close> only sees absolute values\<close>
  have ra_weighted_abs_eq: "ra_weighted_abs \<sigma> (\<lambda>\<gamma>. \<bar>ra_mono_coeffs c \<beta> \<gamma>\<bar>) = ra_weighted_abs \<sigma> (ra_mono_coeffs c \<beta>)"
    by (rule ext) (simp add: ra_weighted_abs_def)
  show ?thesis
    using majabs by (simp add: ra_majorized_def ra_weighted_abs_eq)
qed

corollary ra_inverse_coeffs_mono_coeffs_majorized:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows "ra_majorized \<sigma> (ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta>) ((2 * n * \<sigma>) ^ ra_deg \<beta>)"
proof (rule ra_mono_coeffs_majorized)
  show "0 < \<sigma>" by (rule s0)
  show "0 \<le> 2 * n * \<sigma>"
    using s0 by (simp add: n_def)
  show "\<And>D. (\<Sum>i=1..D. ra_profile (ra_inverse_coeffs bphi) i * \<sigma> ^ i) \<le> 2 * n * \<sigma>"
    unfolding n_def
    by (rule ra_inverse_coeffs_partial_sums_bounded[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  show "ra_profile (ra_inverse_coeffs bphi) 0 = 0"
    by (rule ra_profile_inverse_coeffs_0)
qed

lemma ra_series_on_majorized_value_bound:
  fixes c :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> real"
  assumes s0: "0 \<le> \<sigma>"
    and r\<sigma>: "r \<le> \<sigma>"
    and ser: "ra_series_on x0 r c F"
    and maj: "ra_majorized \<sigma> c K"
    and x: "dist x x0 < r"
  shows "\<bar>F x\<bar> \<le> K"
proof -
  have hs: "((\<lambda>\<alpha>. ra_monomial (x - x0) \<alpha> * c \<alpha>) has_sum F x) ra_idx"
    using ser x by (simp add: ra_series_on_def)
  define S where "S = (\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. ra_weighted_abs \<sigma> c \<alpha>)"
  have dom_sum: "(ra_weighted_abs \<sigma> c has_sum S) ra_idx"
    unfolding S_def
    using maj by (simp add: ra_majorized_def has_sum_infsum)
  have hle: "norm (x - x0) \<le> \<sigma>"
    using x r\<sigma> by (simp add: dist_norm)
  have term_bound:
    "\<bar>ra_monomial (x - x0) \<alpha> * c \<alpha>\<bar> \<le> ra_weighted_abs \<sigma> c \<alpha>"
    if a: "\<alpha> \<in> ra_idx" for \<alpha>
  proof -
    have "\<bar>ra_monomial (x - x0) \<alpha> * c \<alpha>\<bar>
        = \<bar>ra_monomial (x - x0) \<alpha>\<bar> * \<bar>c \<alpha>\<bar>"
      by (simp add: abs_mult)
    also have "\<dots> \<le> \<sigma> ^ ra_deg \<alpha> * \<bar>c \<alpha>\<bar>"
      by (rule mult_right_mono[OF ra_monomial_abs_le_pow[OF a hle]]) simp
    also have "\<dots> = ra_weighted_abs \<sigma> c \<alpha>"
      by (simp add: ra_weighted_abs_def mult.commute)
    finally show ?thesis .
  qed
  have norm_le: "norm (F x) \<le> S"
    by (rule norm_infsum_le[OF hs dom_sum]) (use term_bound in simp)
  hence "\<bar>F x\<bar> \<le> S"
    by simp
  also have "\<dots> \<le> K"
    using maj by (simp add: S_def ra_majorized_def)
  finally show ?thesis .
qed

lemma ra_inverse_coeffs_mono_coeffs_fubini_inputs_at_scale:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows mono_series:
    "ra_series_on (0::'a) \<sigma> (ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta>)
      (\<lambda>h. ra_monomial
        (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<beta>)"
    and mono_maj:
    "ra_majorized \<sigma> (ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta>) ((2 * n * \<sigma>) ^ ra_deg \<beta>)"
    and outer_summable:
    "(\<lambda>\<beta>. norm (bphi \<beta>) * (2 * n * \<sigma>) ^ ra_deg \<beta>)
      summable_on (ra_idx::('a \<Rightarrow> nat) set)"
proof -
  show "ra_series_on (0::'a) \<sigma> (ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta>)
      (\<lambda>h. ra_monomial
        (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<beta>)"
  proof (rule ra_mono_coeffs_series[where c = "ra_inverse_coeffs bphi"])
    fix h :: 'a
    assume "dist h (0::'a) < \<sigma>"
    show "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
        has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>))
        (ra_idx::('a \<Rightarrow> nat) set)"
      unfolding n_def
      by (rule ra_inverse_coeffs_power_series_has_sum[OF t0 majb s0])
         (use s1 s2 \<open>dist h (0::'a) < \<sigma>\<close> in \<open>simp_all add: n_def dist_norm\<close>)
  qed
next
  show "ra_majorized \<sigma> (ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta>) ((2 * n * \<sigma>) ^ ra_deg \<beta>)"
    unfolding n_def
    by (rule ra_inverse_coeffs_mono_coeffs_majorized[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
next
  have n1: "1 \<le> n"
    unfolding n_def by simp
  have K0: "0 \<le> 2 * n * \<sigma>"
    using n1 s0 by simp
  have Kt: "2 * n * \<sigma> < t"
  proof -
    have "2 * n * \<sigma> \<le> 2 * n * (t / (4 * n))"
      using s1 n1 by (intro mult_left_mono) simp_all
    also have "\<dots> = t / 2"
      using n1 by (simp add: field_simps)
    also have "\<dots> < t"
      using t0 by simp
    finally show ?thesis .
  qed
  show "(\<lambda>\<beta>. norm (bphi \<beta>) * (2 * n * \<sigma>) ^ ra_deg \<beta>)
      summable_on (ra_idx::('a \<Rightarrow> nat) set)"
    by (rule ra_majorized_geometric_weight_summable[OF t0 majb K0 Kt])
qed

lemma ra_inverse_coeffs_phi_comp_series_at_scale:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows "\<forall>h. dist h (0::'a) < \<sigma> \<longrightarrow>
    ((\<lambda>\<gamma>. ra_monomial (h - 0) \<gamma> *\<^sub>R
        (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>))
      has_sum
        (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial
            (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>))
      (ra_idx::('a \<Rightarrow> nat) set)"
proof -
  define H where "H = (\<lambda>h::'a.
    \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)"
  have mono_series:
    "ra_series_on (0::'a) \<sigma> (ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta>)
      (\<lambda>h. ra_monomial (H h) \<beta>)" for \<beta>
    unfolding H_def n_def
    by (rule ra_inverse_coeffs_mono_coeffs_fubini_inputs_at_scale(1)[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  have mono_maj:
    "ra_majorized \<sigma> (ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta>) ((2 * n * \<sigma>) ^ ra_deg \<beta>)" for \<beta>
    unfolding n_def
    by (rule ra_inverse_coeffs_mono_coeffs_fubini_inputs_at_scale(2)[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  have outer_summable:
    "(\<lambda>\<beta>. norm (bphi \<beta>) * (2 * n * \<sigma>) ^ ra_deg \<beta>)
      summable_on (ra_idx::('a \<Rightarrow> nat) set)"
    unfolding n_def
    by (rule ra_inverse_coeffs_mono_coeffs_fubini_inputs_at_scale(3)[OF t0 majb s0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  have Gval:
    "((\<lambda>\<beta>. ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>)
        has_sum
          (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>))
        (ra_idx::('a \<Rightarrow> nat) set)"
    if h: "dist h (0::'a) < \<sigma>" for h
  proof -
    have val_bound:
      "\<bar>ra_monomial (H h) \<beta>\<bar> \<le> (2 * n * \<sigma>) ^ ra_deg \<beta>"
      if b: "\<beta> \<in> (ra_idx::('a \<Rightarrow> nat) set)" for \<beta>
      by (rule ra_series_on_majorized_value_bound[OF _ _ mono_series mono_maj h])
         (use s0 in simp_all)
    have abs_summ:
      "(\<lambda>\<beta>. norm (ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>))
        summable_on (ra_idx::('a \<Rightarrow> nat) set)"
    proof (rule summable_on_comparison_test[OF outer_summable])
      fix \<beta> :: "'a \<Rightarrow> nat"
      assume b: "\<beta> \<in> ra_idx"
      have "norm (ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>)
          = \<bar>ra_monomial (H h) \<beta>\<bar> * norm (bphi \<beta>)"
        by simp
      also have "\<dots> \<le> (2 * n * \<sigma>) ^ ra_deg \<beta> * norm (bphi \<beta>)"
        by (rule mult_right_mono[OF val_bound[OF b]]) simp
      also have "\<dots> = norm (bphi \<beta>) * (2 * n * \<sigma>) ^ ra_deg \<beta>"
        by (simp add: mult.commute)
      finally show "norm (ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>)
          \<le> norm (bphi \<beta>) * (2 * n * \<sigma>) ^ ra_deg \<beta>" .
    next
      fix \<beta> :: "'a \<Rightarrow> nat"
      assume "\<beta> \<in> ra_idx"
      show "0 \<le> norm (ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>)"
        by simp
    qed
    have summ: "(\<lambda>\<beta>. ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>)
        summable_on (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule abs_summable_summable[OF abs_summ])
    show ?thesis
      by (rule has_sum_infsum[OF summ])
  qed
  have main: "\<forall>h. dist h (0::'a) < \<sigma> \<longrightarrow>
    ((\<lambda>\<gamma>. ra_monomial (h - 0) \<gamma> *\<^sub>R
        (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>))
      has_sum
        (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>))
      (ra_idx::('a \<Rightarrow> nat) set)"
    by (rule ra_series_on_majdom_vec
        [where CC = "\<lambda>\<beta>. ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta>"
           and Fn = "\<lambda>\<beta> h. ra_monomial (H h) \<beta>"
           and vg = bphi
           and Kk = "\<lambda>\<beta>. (2 * n * \<sigma>) ^ ra_deg \<beta>"
           and \<sigma> = \<sigma> and r = \<sigma>
           and G = "\<lambda>h. \<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
             ra_monomial (H h) \<beta> *\<^sub>R bphi \<beta>"])
       (use s0 mono_series mono_maj outer_summable Gval in auto)
  show ?thesis
    using main by (simp add: H_def)
qed

lemma ra_inverse_coeffs_functional_fixed_point_at_scale:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and low: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> ra_deg \<beta> < 2 \<Longrightarrow> bphi \<beta> = 0"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows "\<forall>h. dist h (0::'a) < \<sigma> \<longrightarrow>
    (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
      = h + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial
            (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>)"
proof (intro allI impI)
  fix h :: 'a
  assume h: "dist h (0::'a) < \<sigma>"
  define H where "H =
    (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)"
  define N where "N =
    (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
      ra_monomial H \<beta> *\<^sub>R bphi \<beta>)"
  have Hhs: "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) has_sum H)
      (ra_idx::('a \<Rightarrow> nat) set)"
    unfolding H_def n_def
    by (rule ra_inverse_coeffs_power_series_has_sum[OF t0 majb s0])
       (use s1 s2 h in \<open>simp_all add: n_def dist_norm\<close>)
  have Nhs: "((\<lambda>\<gamma>. ra_monomial (h - 0) \<gamma> *\<^sub>R
        (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>))
      has_sum N) (ra_idx::('a \<Rightarrow> nat) set)"
  proof -
    have comp: "\<forall>h. dist h (0::'a) < \<sigma> \<longrightarrow>
      ((\<lambda>\<gamma>. ra_monomial (h - 0) \<gamma> *\<^sub>R
          (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>))
        has_sum
          (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial
              (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
                ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>))
        (ra_idx::('a \<Rightarrow> nat) set)"
      unfolding n_def
      by (rule ra_inverse_coeffs_phi_comp_series_at_scale[OF t0 majb s0])
         (use s1 s2 in \<open>simp_all add: n_def\<close>)
    show ?thesis
      using comp h by (simp add: N_def H_def)
  qed
  have rhs_hs: "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R
        (ra_coeff_id \<gamma> + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)))
      has_sum (h + N)) (ra_idx::('a \<Rightarrow> nat) set)"
  proof -
    have "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_coeff_id \<gamma>
          + ra_monomial h \<gamma> *\<^sub>R
            (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>))
        has_sum (h + N)) (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule has_sum_add[OF ra_coeff_id_series Nhs[unfolded diff_zero]])
    thus ?thesis
      by (simp add: scaleR_add_right)
  qed
  have rhs_eq_inverse_coeffs:
    "ra_monomial h \<gamma> *\<^sub>R
        (ra_coeff_id \<gamma> + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>))
      = ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>"
    if g: "\<gamma> \<in> (ra_idx::('a \<Rightarrow> nat) set)" for \<gamma>
    using ra_inverse_coeffs_coeff_equation_infsum[OF g low] by simp
  have rhs_inverse_coeffs_hs: "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
      has_sum (h + N)) (ra_idx::('a \<Rightarrow> nat) set)"
  proof -
    have "(((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R
          (ra_coeff_id \<gamma> + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_mono_coeffs (ra_inverse_coeffs bphi) \<beta> \<gamma> *\<^sub>R bphi \<beta>)))
        has_sum (h + N)) (ra_idx::('a \<Rightarrow> nat) set))
      = (((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
        has_sum (h + N)) (ra_idx::('a \<Rightarrow> nat) set))"
      by (rule has_sum_cong) (use rhs_eq_inverse_coeffs in simp)
    thus ?thesis
      using rhs_hs by simp
  qed
  have "H = h + N"
    using has_sum_unique[OF Hhs rhs_inverse_coeffs_hs] .
  thus "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
      = h + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial
            (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>)"
    by (simp add: H_def N_def)
qed

corollary ra_inverse_coeffs_right_inverse_at_scale:
  fixes bphi :: "('a::euclidean_space \<Rightarrow> nat) \<Rightarrow> 'a"
  defines "n \<equiv> real (card (Basis :: 'a set))"
  assumes t0: "0 < t" and majb: "ra_majorized t (\<lambda>\<beta>. norm (bphi \<beta>)) M"
    and low: "\<And>\<beta>. \<beta> \<in> ra_idx \<Longrightarrow> ra_deg \<beta> < 2 \<Longrightarrow> bphi \<beta> = 0"
    and s0: "0 < \<sigma>"
    and s1: "\<sigma> \<le> t / (4 * n)"
    and s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  shows "\<forall>h. dist h (0::'a) < \<sigma> \<longrightarrow>
    ((\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
        ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
      - (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial
            (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>))
      = h"
proof (intro allI impI)
  fix h :: 'a
  assume h: "dist h (0::'a) < \<sigma>"
  have fp: "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
      = h + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial
            (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>)"
  proof -
    have allfp: "\<forall>h. dist h (0::'a) < \<sigma> \<longrightarrow>
      (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set). ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
        = h + (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial
              (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
                ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>)"
      unfolding n_def
      by (rule ra_inverse_coeffs_functional_fixed_point_at_scale[OF t0 majb low s0])
         (use s1 s2 in \<open>simp_all add: n_def\<close>)
    show ?thesis
      using allfp h by simp
  qed
  define P where "P = (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial
            (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>)"
  have "(\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
        ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) - P = (h + P) - P"
    using fp by (simp add: P_def)
  also have "\<dots> = h"
    by simp
  finally show "((\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
        ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
      - (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial
            (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>))
      = h"
    by (simp add: P_def)
qed

lemma normalized_analytic_perturbation_coefficients:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes ana: "real_analytic_on f U"
    and zero_U: "0 \<in> U"
    and f0: "f 0 = 0"
    and der0: "(f has_derivative id) (at 0)"
  obtains r t bphi M where
    "0 < r" "0 < t"
    "\<And>x. dist x (0::'a) < r \<Longrightarrow>
      ((\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R bphi \<alpha>) has_sum (x - f x))
        (ra_idx::('a \<Rightarrow> nat) set)"
    "ra_majorized t (\<lambda>\<alpha>. norm (bphi \<alpha>)) M"
    "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> < 2 \<Longrightarrow> bphi \<alpha> = 0"
proof -
  from ana zero_U obtain r c where r0: "0 < r"
    and fser: "\<And>x. dist x (0::'a) < r \<Longrightarrow>
      ((\<lambda>\<alpha>. ra_monomial (x - 0) \<alpha> *\<^sub>R c \<alpha>) has_sum f x)
        (ra_idx::('a \<Rightarrow> nat) set)"
    unfolding real_analytic_on_def by blast
  define bphi where "bphi = (\<lambda>\<alpha>. ra_coeff_id \<alpha> - c \<alpha>)"
  have phiser: "((\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R bphi \<alpha>) has_sum (x - f x))
      (ra_idx::('a \<Rightarrow> nat) set)"
    if x: "dist x (0::'a) < r" for x
  proof -
    have idser: "((\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R ra_coeff_id \<alpha>) has_sum x)
        (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule ra_coeff_id_series)
    have fserx: "((\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R c \<alpha>) has_sum f x)
        (ra_idx::('a \<Rightarrow> nat) set)"
      using fser[OF x] by simp
    have neg_fser: "((\<lambda>\<alpha>. - (ra_monomial x \<alpha> *\<^sub>R c \<alpha>)) has_sum (- f x))
        (ra_idx::('a \<Rightarrow> nat) set)"
      using fserx by (simp add: has_sum_uminus)
    have "((\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R ra_coeff_id \<alpha>
          + (- (ra_monomial x \<alpha> *\<^sub>R c \<alpha>))) has_sum (x + (- f x)))
        (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule has_sum_add[OF idser neg_fser])
    thus ?thesis
      by (simp add: bphi_def scaleR_diff_right)
  qed

  have c0: "c ra_idx_zero = 0"
  proof -
    have hs: "((\<lambda>\<alpha>. ra_monomial (0::'a) \<alpha> *\<^sub>R c \<alpha>) has_sum f 0)
        (ra_idx::('a \<Rightarrow> nat) set)"
      using fser[of 0] r0 by simp
    show ?thesis
      using ra_series_at_zero_coeff[OF hs] f0 by simp
  qed
  have fd_id: "frechet_derivative f (at 0) = id"
    using frechet_derivative_at[OF der0] by simp
  have low: "bphi \<alpha> = 0" if a: "\<alpha> \<in> ra_idx" and lt: "ra_deg \<alpha> < 2" for \<alpha>
  proof (cases "ra_deg \<alpha> = 0")
    case True
    hence "\<alpha> = ra_idx_zero"
      using ra_deg_eq0_iff[OF a] by simp
    thus ?thesis
      by (simp add: bphi_def c0 ra_coeff_id_idx_zero)
  next
    case False
    hence d1: "ra_deg \<alpha> = 1"
      using lt by simp
    obtain b where b: "b \<in> Basis" and alpha: "\<alpha> = ra_idx_unit b"
      by (rule ra_deg_one_unit[OF a d1])
    have c_lin: "c (ra_idx_unit b) = b"
    proof -
      have "c (\<lambda>x. if x = b then 1 else 0) = frechet_derivative f (at 0) b"
        by (rule ra_linear_coeff_eq_frechet_derivative_basis[OF b r0 fser])
      thus ?thesis
        by (simp add: ra_idx_unit_def fd_id)
    qed
    show ?thesis
      using b by (simp add: bphi_def alpha c_lin ra_coeff_id_unit)
  qed

  define eB where "eB = (\<Sum>b\<in>(Basis::'a set). b)"
  have eBpos: "0 < norm eB"
  proof -
    have "eB \<noteq> 0"
    proof
      assume "eB = 0"
      then have zero_inner: "eB \<bullet> (SOME b. b \<in> (Basis::'a set)) = 0"
        by simp
      obtain b0 :: 'a where b0: "b0 \<in> Basis"
        using nonempty_Basis by blast
      have someB: "(SOME b. b \<in> (Basis::'a set)) \<in> Basis"
        using b0 by (rule someI)
      hence "eB \<bullet> (SOME b. b \<in> (Basis::'a set)) = 1"
        by (simp add: eB_def inner_sum_left inner_Basis)
      thus False
        using zero_inner by simp
    qed
    thus ?thesis by simp
  qed
  define \<rho> where "\<rho> = r / (2 * norm eB)"
  have \<rho>0: "0 < \<rho>"
    using r0 eBpos by (simp add: \<rho>_def)
  have corner: "\<rho> * norm (\<Sum>b\<in>(Basis::'a set). b) < r"
  proof -
    have "\<rho> * norm eB = r / 2"
      using eBpos by (simp add: \<rho>_def)
    also have "\<dots> < r"
      using r0 by simp
    finally show ?thesis
      by (simp add: eB_def)
  qed
  have phiser0: "\<And>z. dist z (0::'a) < r \<Longrightarrow>
      ((\<lambda>\<alpha>. ra_monomial (z - 0) \<alpha> *\<^sub>R bphi \<alpha>) has_sum (z - f z))
        (ra_idx::('a \<Rightarrow> nat) set)"
    using phiser by simp
  obtain M0 where M0nn: "M0 \<ge> 0"
    and bnd: "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> norm (bphi \<alpha>) \<le> M0 / \<rho> ^ ra_deg \<alpha>"
    using ra_coeff_bound[OF r0 phiser0 \<rho>0 corner] by blast
  define t where "t = \<rho> / 2"
  have t0: "0 < t"
    using \<rho>0 by (simp add: t_def)
  have t_lt: "t < \<rho>"
    using \<rho>0 by (simp add: t_def)
  define M where "M = M0 * (\<Sum>\<^sub>\<infinity>\<alpha>\<in>(ra_idx::('a \<Rightarrow> nat) set). (t / \<rho>) ^ ra_deg \<alpha>)"
  have maj: "ra_majorized t (\<lambda>\<alpha>. norm (bphi \<alpha>)) M"
    unfolding M_def
    by (rule coeff_majorized_of_bound[OF M0nn bnd \<rho>0])
       (use t0 t_lt in simp_all)

  show ?thesis
    by (rule that[OF r0 t0 phiser maj low])
qed

theorem normalized_analytic_formal_right_inverse:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes ana: "real_analytic_on f U"
    and zero_U: "0 \<in> U"
    and f0: "f 0 = 0"
    and der0: "(f has_derivative id) (at 0)"
  obtains \<sigma> bphi where
    "0 < \<sigma>"
    "real_analytic_on
      (\<lambda>h::'a. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
        ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
      (ball (0::'a) (\<sigma> / 2))"
    "\<And>h::'a. norm h < \<sigma> \<Longrightarrow>
      ((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
        has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>))
        (ra_idx::('a \<Rightarrow> nat) set)"
    "\<And>h::'a. norm h < \<sigma> \<Longrightarrow>
      f (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) = h"
proof -
  show ?thesis
  proof (rule normalized_analytic_perturbation_coefficients[OF ana zero_U f0 der0])
    fix r t bphi M
    assume r0: "0 < r" and t0: "0 < t"
      and phiser: "\<And>x. dist x (0::'a) < r \<Longrightarrow>
        ((\<lambda>\<alpha>. ra_monomial x \<alpha> *\<^sub>R bphi \<alpha>) has_sum (x - f x))
          (ra_idx::('a \<Rightarrow> nat) set)"
      and majb: "ra_majorized t (\<lambda>\<alpha>. norm (bphi \<alpha>)) M"
      and low: "\<And>\<alpha>. \<alpha> \<in> ra_idx \<Longrightarrow> ra_deg \<alpha> < 2 \<Longrightarrow> bphi \<alpha> = 0"
  define n where "n = real (card (Basis :: 'a set))"
  have n1: "1 \<le> n"
    unfolding n_def by simp
  have M0: "0 \<le> M"
  proof -
    have "0 \<le> (\<Sum>\<^sub>\<infinity>\<alpha>\<in>ra_idx. ra_weighted_abs t (\<lambda>\<alpha>. norm (bphi \<alpha>)) \<alpha>)"
      using t0 by (intro infsum_nonneg) (simp add: ra_weighted_abs_nonneg)
    also have "\<dots> \<le> M"
      using majb by (simp add: ra_majorized_def)
    finally show ?thesis .
  qed
  define a where "a = t / (4 * n)"
  define b where "b = t\<^sup>2 / (8 * (M + 1) * n)"
  define c where "c = r / (4 * n)"
  define \<sigma> where "\<sigma> = min (min a b) c / 2"
  have a0: "0 < a"
    using t0 n1 by (simp add: a_def)
  have b0: "0 < b"
    unfolding b_def
    using t0 M0 n1 by (intro divide_pos_pos mult_pos_pos) simp_all
  have c0: "0 < c"
    using r0 n1 by (simp add: c_def)
  have min0: "0 < min (min a b) c"
    using a0 b0 c0 by simp
  have \<sigma>0: "0 < \<sigma>"
    using min0 by (simp add: \<sigma>_def)
  have half_min_le: "min (min a b) c / 2 \<le> min (min a b) c"
  proof -
    have "min (min a b) c / 2 = (1/2) * min (min a b) c"
      by simp
    also have "\<dots> \<le> 1 * min (min a b) c"
      by (rule mult_right_mono) (use min0 in simp_all)
    finally show ?thesis by simp
  qed
  have s1: "\<sigma> \<le> t / (4 * n)"
  proof -
    have "\<sigma> \<le> min (min a b) c"
      unfolding \<sigma>_def by (rule half_min_le)
    also have "\<dots> \<le> a"
      by simp
    finally show ?thesis
      by (simp add: a_def)
  qed
  have s2: "\<sigma> \<le> t\<^sup>2 / (8 * (M + 1) * n)"
  proof -
    have "\<sigma> \<le> min (min a b) c"
      unfolding \<sigma>_def by (rule half_min_le)
    also have "\<dots> \<le> b"
      by simp
    finally show ?thesis
      by (simp add: b_def)
  qed
  have s3: "2 * n * \<sigma> < r"
  proof -
    have "\<sigma> \<le> c / 2"
    proof -
      have "min (min a b) c \<le> c"
        by simp
      hence "min (min a b) c / 2 \<le> c / 2"
        by simp
      thus ?thesis
        by (simp add: \<sigma>_def)
    qed
    hence "2 * n * \<sigma> \<le> 2 * n * (c / 2)"
      using n1 by (intro mult_left_mono) simp_all
    also have "\<dots> = r / 4"
      using n1 by (simp add: c_def field_simps)
    also have "\<dots> < r"
      using r0 by simp
    finally show ?thesis .
  qed
  have Hana: "real_analytic_on
      (\<lambda>h::'a. \<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
        ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
      (ball (0::'a) (\<sigma> / 2))"
    unfolding n_def
    by (rule ra_inverse_coeffs_power_series_real_analytic_on_ball_at_scale[OF t0 majb \<sigma>0])
       (use s1 s2 in \<open>simp_all add: n_def\<close>)
  show ?thesis
  proof (rule that[OF \<sigma>0 Hana])
    fix h :: 'a
    assume h: "norm h < \<sigma>"
    show "((\<lambda>\<gamma>. ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
        has_sum (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>))
        (ra_idx::('a \<Rightarrow> nat) set)"
      unfolding n_def
      by (rule ra_inverse_coeffs_power_series_has_sum[OF t0 majb \<sigma>0])
         (use h s1 s2 in \<open>simp_all add: n_def\<close>)
  next
    fix h :: 'a
    assume h: "norm h < \<sigma>"
    let ?H = "\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>"
    let ?P = "\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
          ra_monomial ?H \<beta> *\<^sub>R bphi \<beta>"
    have hle: "norm h \<le> \<sigma>"
      using h by simp
    have Hle: "norm ?H \<le> 2 * n * \<sigma>"
      unfolding n_def
      by (rule ra_inverse_coeffs_value_norm_bound_at_scale[OF t0 majb \<sigma>0])
         (use s1 s2 hle in \<open>simp_all add: n_def\<close>)
    have Hr: "dist ?H (0::'a) < r"
      using Hle s3 by (simp add: dist_norm)
    have phi_hs: "((\<lambda>\<beta>. ra_monomial ?H \<beta> *\<^sub>R bphi \<beta>) has_sum (?H - f ?H))
        (ra_idx::('a \<Rightarrow> nat) set)"
      using phiser[OF Hr] by simp
    have phi_sum: "((\<lambda>\<beta>. ra_monomial ?H \<beta> *\<^sub>R bphi \<beta>) has_sum ?P)
        (ra_idx::('a \<Rightarrow> nat) set)"
      by (rule has_sum_infsum) (rule has_sum_imp_summable[OF phi_hs])
    have Peq: "?P = ?H - f ?H"
      by (rule has_sum_unique[OF phi_sum phi_hs])
    have right: "?H - ?P = h"
    proof -
      have all_right: "\<forall>h. dist h (0::'a) < \<sigma> \<longrightarrow>
        ((\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
            ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>)
          - (\<Sum>\<^sub>\<infinity>\<beta>\<in>(ra_idx::('a \<Rightarrow> nat) set).
              ra_monomial
                (\<Sum>\<^sub>\<infinity>\<gamma>\<in>(ra_idx::('a \<Rightarrow> nat) set).
                  ra_monomial h \<gamma> *\<^sub>R ra_inverse_coeffs bphi \<gamma>) \<beta> *\<^sub>R bphi \<beta>))
          = h"
        unfolding n_def
        by (rule ra_inverse_coeffs_right_inverse_at_scale[OF t0 majb low \<sigma>0])
           (use s1 s2 in \<open>simp_all add: n_def\<close>)
      show ?thesis
        using all_right h by (simp add: dist_norm)
    qed
    show "f ?H = h"
      using right Peq by simp
  qed
  qed
qed

end
