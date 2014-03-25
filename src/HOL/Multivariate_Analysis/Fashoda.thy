(*  Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (translation from HOL light)
*)

header {* Fashoda meet theorem *}

theory Fashoda
imports Brouwer_Fixpoint Path_Connected Cartesian_Euclidean_Space
begin

(* move *)

lemma cart_eq_inner_axis: "a $ i = a \<bullet> axis i 1"
  by (simp add: inner_axis)

lemma axis_in_Basis: "a \<in> Basis \<Longrightarrow> axis i a \<in> Basis"
  by (auto simp add: Basis_vec_def axis_eq_axis)

lemma divide_nonneg_nonneg:
  fixes a b :: "'a :: {linordered_field, field_inverse_zero}"
  shows "a \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> 0 \<le> a / b"
  by (cases "b = 0") (auto intro!: divide_nonneg_pos)

subsection {*Bijections between intervals. *}

definition interval_bij :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<Rightarrow> 'a::euclidean_space"
  where "interval_bij =
    (\<lambda>(a, b) (u, v) x. (\<Sum>i\<in>Basis. (u\<bullet>i + (x\<bullet>i - a\<bullet>i) / (b\<bullet>i - a\<bullet>i) * (v\<bullet>i - u\<bullet>i)) *\<^sub>R i))"

lemma interval_bij_affine:
  "interval_bij (a,b) (u,v) = (\<lambda>x. (\<Sum>i\<in>Basis. ((v\<bullet>i - u\<bullet>i) / (b\<bullet>i - a\<bullet>i) * (x\<bullet>i)) *\<^sub>R i) +
    (\<Sum>i\<in>Basis. (u\<bullet>i - (v\<bullet>i - u\<bullet>i) / (b\<bullet>i - a\<bullet>i) * (a\<bullet>i)) *\<^sub>R i))"
  by (auto simp: setsum_addf[symmetric] scaleR_add_left[symmetric] interval_bij_def fun_eq_iff
    field_simps inner_simps add_divide_distrib[symmetric] intro!: setsum_cong)

lemma continuous_interval_bij:
  fixes a b :: "'a::euclidean_space"
  shows "continuous (at x) (interval_bij (a, b) (u, v))"
  by (auto simp add: divide_inverse interval_bij_def intro!: continuous_setsum continuous_intros)

lemma continuous_on_interval_bij: "continuous_on s (interval_bij (a, b) (u, v))"
  apply(rule continuous_at_imp_continuous_on)
  apply (rule, rule continuous_interval_bij)
  done

lemma in_interval_interval_bij:
  fixes a b u v x :: "'a::euclidean_space"
  assumes "x \<in> cbox a b"
    and "cbox u v \<noteq> {}"
  shows "interval_bij (a, b) (u, v) x \<in> cbox u v"
  apply (simp only: interval_bij_def split_conv mem_box inner_setsum_left_Basis cong: ball_cong)
  apply safe
proof -
  fix i :: 'a
  assume i: "i \<in> Basis"
  have "cbox a b \<noteq> {}"
    using assms by auto
  with i have *: "a\<bullet>i \<le> b\<bullet>i" "u\<bullet>i \<le> v\<bullet>i"
    using assms(2) by (auto simp add: box_eq_empty)
  have x: "a\<bullet>i\<le>x\<bullet>i" "x\<bullet>i\<le>b\<bullet>i"
    using assms(1)[unfolded mem_box] using i by auto
  have "0 \<le> (x \<bullet> i - a \<bullet> i) / (b \<bullet> i - a \<bullet> i) * (v \<bullet> i - u \<bullet> i)"
    using * x by (auto intro!: mult_nonneg_nonneg divide_nonneg_nonneg)
  then show "u \<bullet> i \<le> u \<bullet> i + (x \<bullet> i - a \<bullet> i) / (b \<bullet> i - a \<bullet> i) * (v \<bullet> i - u \<bullet> i)"
    using * by auto
  have "((x \<bullet> i - a \<bullet> i) / (b \<bullet> i - a \<bullet> i)) * (v \<bullet> i - u \<bullet> i) \<le> 1 * (v \<bullet> i - u \<bullet> i)"
    apply (rule mult_right_mono)
    unfolding divide_le_eq_1
    using * x
    apply auto
    done
  then show "u \<bullet> i + (x \<bullet> i - a \<bullet> i) / (b \<bullet> i - a \<bullet> i) * (v \<bullet> i - u \<bullet> i) \<le> v \<bullet> i"
    using * by auto
qed

lemma interval_bij_bij:
  "\<forall>(i::'a::euclidean_space)\<in>Basis. a\<bullet>i < b\<bullet>i \<and> u\<bullet>i < v\<bullet>i \<Longrightarrow>
    interval_bij (a, b) (u, v) (interval_bij (u, v) (a, b) x) = x"
  by (auto simp: interval_bij_def euclidean_eq_iff[where 'a='a])

lemma interval_bij_bij_cart: fixes x::"real^'n" assumes "\<forall>i. a$i < b$i \<and> u$i < v$i" 
  shows "interval_bij (a,b) (u,v) (interval_bij (u,v) (a,b) x) = x"
  using assms by (intro interval_bij_bij) (auto simp: Basis_vec_def inner_axis)


subsection {* Fashoda meet theorem *}

lemma infnorm_2:
  fixes x :: "real^2"
  shows "infnorm x = max (abs (x$1)) (abs (x$2))"
  unfolding infnorm_cart UNIV_2 by (rule cSup_eq) auto

lemma infnorm_eq_1_2:
  fixes x :: "real^2"
  shows "infnorm x = 1 \<longleftrightarrow>
    abs (x$1) \<le> 1 \<and> abs (x$2) \<le> 1 \<and> (x$1 = -1 \<or> x$1 = 1 \<or> x$2 = -1 \<or> x$2 = 1)"
  unfolding infnorm_2 by auto

lemma infnorm_eq_1_imp:
  fixes x :: "real^2"
  assumes "infnorm x = 1"
  shows "abs (x$1) \<le> 1" and "abs (x$2) \<le> 1"
  using assms unfolding infnorm_eq_1_2 by auto

lemma fashoda_unit:
  fixes f g :: "real \<Rightarrow> real^2"
  assumes "f ` {-1 .. 1} \<subseteq> cbox (-1) 1"
    and "g ` {-1 .. 1} \<subseteq> cbox (-1) 1"
    and "continuous_on {-1 .. 1} f"
    and "continuous_on {-1 .. 1} g"
    and "f (- 1)$1 = - 1"
    and "f 1$1 = 1" "g (- 1) $2 = -1"
    and "g 1 $2 = 1"
  shows "\<exists>s\<in>{-1 .. 1}. \<exists>t\<in>{-1 .. 1}. f s = g t"
proof (rule ccontr)
  assume "\<not> ?thesis"
  note as = this[unfolded bex_simps,rule_format]
  def sqprojection \<equiv> "\<lambda>z::real^2. (inverse (infnorm z)) *\<^sub>R z" 
  def negatex \<equiv> "\<lambda>x::real^2. (vector [-(x$1), x$2])::real^2"
  have lem1: "\<forall>z::real^2. infnorm (negatex z) = infnorm z"
    unfolding negatex_def infnorm_2 vector_2 by auto
  have lem2: "\<forall>z. z \<noteq> 0 \<longrightarrow> infnorm (sqprojection z) = 1"
    unfolding sqprojection_def
    unfolding infnorm_mul[unfolded scalar_mult_eq_scaleR]
    unfolding abs_inverse real_abs_infnorm
    apply (subst infnorm_eq_0[symmetric])
    apply auto
    done
  let ?F = "\<lambda>w::real^2. (f \<circ> (\<lambda>x. x$1)) w - (g \<circ> (\<lambda>x. x$2)) w"
  have *: "\<And>i. (\<lambda>x::real^2. x $ i) ` cbox (- 1) 1 = {-1 .. 1}"
    apply (rule set_eqI)
    unfolding image_iff Bex_def mem_interval_cart interval_cbox_cart
    apply rule
    defer
    apply (rule_tac x="vec x" in exI)
    apply auto
    done
  {
    fix x
    assume "x \<in> (\<lambda>w. (f \<circ> (\<lambda>x. x $ 1)) w - (g \<circ> (\<lambda>x. x $ 2)) w) ` (cbox (- 1) (1::real^2))"
    then obtain w :: "real^2" where w:
        "w \<in> cbox (- 1) 1"
        "x = (f \<circ> (\<lambda>x. x $ 1)) w - (g \<circ> (\<lambda>x. x $ 2)) w"
      unfolding image_iff ..
    then have "x \<noteq> 0"
      using as[of "w$1" "w$2"]
      unfolding mem_interval_cart atLeastAtMost_iff
      by auto
  } note x0 = this
  have 21: "\<And>i::2. i \<noteq> 1 \<Longrightarrow> i = 2"
    using UNIV_2 by auto
  have 1: "box (- 1) (1::real^2) \<noteq> {}"
    unfolding interval_eq_empty_cart by auto
  have 2: "continuous_on (cbox -1 1) (negatex \<circ> sqprojection \<circ> ?F)"
    apply (intro continuous_on_intros continuous_on_component)
    unfolding *
    apply (rule assms)+
    apply (subst sqprojection_def)
    apply (intro continuous_on_intros)
    apply (simp add: infnorm_eq_0 x0)
    apply (rule linear_continuous_on)
  proof -
    show "bounded_linear negatex"
      apply (rule bounded_linearI')
      unfolding vec_eq_iff
    proof (rule_tac[!] allI)
      fix i :: 2
      fix x y :: "real^2"
      fix c :: real
      show "negatex (x + y) $ i =
        (negatex x + negatex y) $ i" "negatex (c *\<^sub>R x) $ i = (c *\<^sub>R negatex x) $ i"
        apply -
        apply (case_tac[!] "i\<noteq>1")
        prefer 3
        apply (drule_tac[1-2] 21) 
        unfolding negatex_def
        apply (auto simp add:vector_2)
        done
    qed
  qed
  have 3: "(negatex \<circ> sqprojection \<circ> ?F) ` cbox (-1) 1 \<subseteq> cbox (-1) 1"
    unfolding subset_eq
    apply rule
  proof -
    case goal1
    then obtain y :: "real^2" where y:
        "y \<in> cbox -1 1"
        "x = (negatex \<circ> sqprojection \<circ> (\<lambda>w. (f \<circ> (\<lambda>x. x $ 1)) w - (g \<circ> (\<lambda>x. x $ 2)) w)) y"
      unfolding image_iff ..
    have "?F y \<noteq> 0"
      apply (rule x0)
      using y(1)
      apply auto
      done
    then have *: "infnorm (sqprojection (?F y)) = 1"
      unfolding y o_def
      by - (rule lem2[rule_format])
    have "infnorm x = 1"
      unfolding *[symmetric] y o_def
      by (rule lem1[rule_format])
    then show "x \<in> cbox (-1) 1"
      unfolding mem_interval_cart interval_cbox_cart infnorm_2
      apply -
      apply rule
    proof -
      case goal1
      then show ?case
        apply (cases "i = 1")
        defer
        apply (drule 21)
        apply auto
        done
    qed
  qed
  obtain x :: "real^2" where x:
      "x \<in> cbox -1 1"
      "(negatex \<circ> sqprojection \<circ> (\<lambda>w. (f \<circ> (\<lambda>x. x $ 1)) w - (g \<circ> (\<lambda>x. x $ 2)) w)) x = x"
    apply (rule brouwer_weak[of "cbox -1 (1::real^2)" "negatex \<circ> sqprojection \<circ> ?F"])
    apply (rule compact_cbox convex_box)+
    unfolding interior_cbox
    apply (rule 1 2 3)+
    apply blast
    done
  have "?F x \<noteq> 0"
    apply (rule x0)
    using x(1)
    apply auto
    done
  then have *: "infnorm (sqprojection (?F x)) = 1"
    unfolding o_def
    by (rule lem2[rule_format])
  have nx: "infnorm x = 1"
    apply (subst x(2)[symmetric])
    unfolding *[symmetric] o_def
    apply (rule lem1[rule_format])
    done
  have "\<forall>x i. x \<noteq> 0 \<longrightarrow> (0 < (sqprojection x)$i \<longleftrightarrow> 0 < x$i)"
    and "\<forall>x i. x \<noteq> 0 \<longrightarrow> ((sqprojection x)$i < 0 \<longleftrightarrow> x$i < 0)"
    apply -
    apply (rule_tac[!] allI impI)+
  proof -
    fix x :: "real^2"
    fix i :: 2
    assume x: "x \<noteq> 0"
    have "inverse (infnorm x) > 0"
      using x[unfolded infnorm_pos_lt[symmetric]] by auto
    then show "(0 < sqprojection x $ i) = (0 < x $ i)"
      and "(sqprojection x $ i < 0) = (x $ i < 0)"
      unfolding sqprojection_def vector_component_simps vector_scaleR_component real_scaleR_def
      unfolding zero_less_mult_iff mult_less_0_iff
      by (auto simp add: field_simps)
  qed
  note lem3 = this[rule_format]
  have x1: "x $ 1 \<in> {- 1..1::real}" "x $ 2 \<in> {- 1..1::real}"
    using x(1) unfolding mem_interval_cart by auto
  then have nz: "f (x $ 1) - g (x $ 2) \<noteq> 0"
    unfolding right_minus_eq
    apply -
    apply (rule as)
    apply auto
    done
  have "x $ 1 = -1 \<or> x $ 1 = 1 \<or> x $ 2 = -1 \<or> x $ 2 = 1"
    using nx unfolding infnorm_eq_1_2 by auto 
  then show False
  proof -
    fix P Q R S 
    presume "P \<or> Q \<or> R \<or> S"
      and "P \<Longrightarrow> False"
      and "Q \<Longrightarrow> False"
      and "R \<Longrightarrow> False"
      and "S \<Longrightarrow> False"
    then show False by auto
  next
    assume as: "x$1 = 1"
    then have *: "f (x $ 1) $ 1 = 1"
      using assms(6) by auto
    have "sqprojection (f (x$1) - g (x$2)) $ 1 < 0"
      using x(2)[unfolded o_def vec_eq_iff,THEN spec[where x=1]]
      unfolding as negatex_def vector_2
      by auto
    moreover
    from x1 have "g (x $ 2) \<in> cbox (-1) 1"
      apply -
      apply (rule assms(2)[unfolded subset_eq,rule_format])
      apply auto
      done
    ultimately show False
      unfolding lem3[OF nz] vector_component_simps * mem_interval_cart 
      apply (erule_tac x=1 in allE)
      apply auto
      done
  next
    assume as: "x$1 = -1"
    then have *: "f (x $ 1) $ 1 = - 1"
      using assms(5) by auto
    have "sqprojection (f (x$1) - g (x$2)) $ 1 > 0"
      using x(2)[unfolded o_def vec_eq_iff,THEN spec[where x=1]]
      unfolding as negatex_def vector_2
      by auto
    moreover
    from x1 have "g (x $ 2) \<in> cbox (-1) 1"
      apply -
      apply (rule assms(2)[unfolded subset_eq,rule_format])
      apply auto
      done
    ultimately show False
      unfolding lem3[OF nz] vector_component_simps * mem_interval_cart 
      apply (erule_tac x=1 in allE)
      apply auto
      done
  next
    assume as: "x$2 = 1"
    then have *: "g (x $ 2) $ 2 = 1"
      using assms(8) by auto
    have "sqprojection (f (x$1) - g (x$2)) $ 2 > 0"
      using x(2)[unfolded o_def vec_eq_iff,THEN spec[where x=2]]
      unfolding as negatex_def vector_2
      by auto
    moreover
    from x1 have "f (x $ 1) \<in> cbox (-1) 1"
      apply -
      apply (rule assms(1)[unfolded subset_eq,rule_format])
      apply auto
      done
    ultimately show False
      unfolding lem3[OF nz] vector_component_simps * mem_interval_cart
      apply (erule_tac x=2 in allE)
      apply auto
      done
  next
    assume as: "x$2 = -1"
    then have *: "g (x $ 2) $ 2 = - 1"
      using assms(7) by auto
    have "sqprojection (f (x$1) - g (x$2)) $ 2 < 0"
      using x(2)[unfolded o_def vec_eq_iff,THEN spec[where x=2]]
      unfolding as negatex_def vector_2
      by auto
    moreover
    from x1 have "f (x $ 1) \<in> cbox (-1) 1"
      apply -
      apply (rule assms(1)[unfolded subset_eq,rule_format])
      apply auto
      done
    ultimately show False
      unfolding lem3[OF nz] vector_component_simps * mem_interval_cart
      apply (erule_tac x=2 in allE)
      apply auto
      done
  qed auto
qed

lemma fashoda_unit_path:
  fixes f g :: "real \<Rightarrow> real^2"
  assumes "path f"
    and "path g"
    and "path_image f \<subseteq> cbox (-1) 1"
    and "path_image g \<subseteq> cbox (-1) 1"
    and "(pathstart f)$1 = -1"
    and "(pathfinish f)$1 = 1"
    and "(pathstart g)$2 = -1"
    and "(pathfinish g)$2 = 1"
  obtains z where "z \<in> path_image f" and "z \<in> path_image g"
proof -
  note assms=assms[unfolded path_def pathstart_def pathfinish_def path_image_def]
  def iscale \<equiv> "\<lambda>z::real. inverse 2 *\<^sub>R (z + 1)"
  have isc: "iscale ` {- 1..1} \<subseteq> {0..1}"
    unfolding iscale_def by auto
  have "\<exists>s\<in>{- 1..1}. \<exists>t\<in>{- 1..1}. (f \<circ> iscale) s = (g \<circ> iscale) t"
  proof (rule fashoda_unit)
    show "(f \<circ> iscale) ` {- 1..1} \<subseteq> cbox -1 1" "(g \<circ> iscale) ` {- 1..1} \<subseteq> cbox -1 1"
      using isc and assms(3-4) by (auto simp add: image_comp [symmetric])
    have *: "continuous_on {- 1..1} iscale"
      unfolding iscale_def by (rule continuous_on_intros)+
    show "continuous_on {- 1..1} (f \<circ> iscale)" "continuous_on {- 1..1} (g \<circ> iscale)"
      apply -
      apply (rule_tac[!] continuous_on_compose[OF *])
      apply (rule_tac[!] continuous_on_subset[OF _ isc])
      apply (rule assms)+
      done
    have *: "(1 / 2) *\<^sub>R (1 + (1::real^1)) = 1"
      unfolding vec_eq_iff by auto
    show "(f \<circ> iscale) (- 1) $ 1 = - 1"
      and "(f \<circ> iscale) 1 $ 1 = 1"
      and "(g \<circ> iscale) (- 1) $ 2 = -1"
      and "(g \<circ> iscale) 1 $ 2 = 1"
      unfolding o_def iscale_def
      using assms
      by (auto simp add: *)
  qed
  then obtain s t where st:
      "s \<in> {- 1..1}"
      "t \<in> {- 1..1}"
      "(f \<circ> iscale) s = (g \<circ> iscale) t"
    by auto
  show thesis
    apply (rule_tac z = "f (iscale s)" in that)
    using st
    unfolding o_def path_image_def image_iff
    apply -
    apply (rule_tac x="iscale s" in bexI)
    prefer 3
    apply (rule_tac x="iscale t" in bexI)
    using isc[unfolded subset_eq, rule_format]
    apply auto
    done
qed

lemma fashoda:
  fixes b :: "real^2"
  assumes "path f"
    and "path g"
    and "path_image f \<subseteq> cbox a b"
    and "path_image g \<subseteq> cbox a b"
    and "(pathstart f)$1 = a$1"
    and "(pathfinish f)$1 = b$1"
    and "(pathstart g)$2 = a$2"
    and "(pathfinish g)$2 = b$2"
  obtains z where "z \<in> path_image f" and "z \<in> path_image g"
proof -
  fix P Q S
  presume "P \<or> Q \<or> S" "P \<Longrightarrow> thesis" and "Q \<Longrightarrow> thesis" and "S \<Longrightarrow> thesis"
  then show thesis
    by auto
next
  have "cbox a b \<noteq> {}"
    using assms(3) using path_image_nonempty[of f] by auto
  then have "a \<le> b"
    unfolding interval_eq_empty_cart less_eq_vec_def by (auto simp add: not_less)
  then show "a$1 = b$1 \<or> a$2 = b$2 \<or> (a$1 < b$1 \<and> a$2 < b$2)"
    unfolding less_eq_vec_def forall_2 by auto
next
  assume as: "a$1 = b$1"
  have "\<exists>z\<in>path_image g. z$2 = (pathstart f)$2"
    apply (rule connected_ivt_component_cart)
    apply (rule connected_path_image assms)+
    apply (rule pathstart_in_path_image)
    apply (rule pathfinish_in_path_image)
    unfolding assms using assms(3)[unfolded path_image_def subset_eq,rule_format,of "f 0"]
    unfolding pathstart_def
    apply (auto simp add: less_eq_vec_def mem_interval_cart)
    done
  then obtain z :: "real^2" where z: "z \<in> path_image g" "z $ 2 = pathstart f $ 2" ..
  have "z \<in> cbox a b"
    using z(1) assms(4)
    unfolding path_image_def
    by blast
  then have "z = f 0"
    unfolding vec_eq_iff forall_2
    unfolding z(2) pathstart_def
    using assms(3)[unfolded path_image_def subset_eq mem_interval_cart,rule_format,of "f 0" 1]
    unfolding mem_interval_cart
    apply (erule_tac x=1 in allE)
    using as
    apply auto
    done
  then show thesis
    apply -
    apply (rule that[OF _ z(1)])
    unfolding path_image_def
    apply auto
    done
next
  assume as: "a$2 = b$2"
  have "\<exists>z\<in>path_image f. z$1 = (pathstart g)$1"
    apply (rule connected_ivt_component_cart)
    apply (rule connected_path_image assms)+
    apply (rule pathstart_in_path_image)
    apply (rule pathfinish_in_path_image)
    unfolding assms
    using assms(4)[unfolded path_image_def subset_eq,rule_format,of "g 0"]
    unfolding pathstart_def
    apply (auto simp add: less_eq_vec_def mem_interval_cart)
    done
  then obtain z where z: "z \<in> path_image f" "z $ 1 = pathstart g $ 1" ..
  have "z \<in> cbox a b"
    using z(1) assms(3)
    unfolding path_image_def
    by blast
  then have "z = g 0"
    unfolding vec_eq_iff forall_2
    unfolding z(2) pathstart_def
    using assms(4)[unfolded path_image_def subset_eq mem_interval_cart,rule_format,of "g 0" 2]
    unfolding mem_interval_cart
    apply (erule_tac x=2 in allE)
    using as
    apply auto
    done
  then show thesis
    apply -
    apply (rule that[OF z(1)])
    unfolding path_image_def
    apply auto
    done
next
  assume as: "a $ 1 < b $ 1 \<and> a $ 2 < b $ 2"
  have int_nem: "cbox (-1) (1::real^2) \<noteq> {}"
    unfolding interval_eq_empty_cart by auto
  obtain z :: "real^2" where z:
      "z \<in> (interval_bij (a, b) (- 1, 1) \<circ> f) ` {0..1}"
      "z \<in> (interval_bij (a, b) (- 1, 1) \<circ> g) ` {0..1}"
    apply (rule fashoda_unit_path[of "interval_bij (a,b) (- 1,1) \<circ> f" "interval_bij (a,b) (- 1,1) \<circ> g"]) 
    unfolding path_def path_image_def pathstart_def pathfinish_def
    apply (rule_tac[1-2] continuous_on_compose)
    apply (rule assms[unfolded path_def] continuous_on_interval_bij)+
    unfolding subset_eq
    apply(rule_tac[1-2] ballI)
  proof -
    fix x
    assume "x \<in> (interval_bij (a, b) (- 1, 1) \<circ> f) ` {0..1}"
    then obtain y where y:
        "y \<in> {0..1}"
        "x = (interval_bij (a, b) (- 1, 1) \<circ> f) y"
      unfolding image_iff ..
    show "x \<in> cbox -1 1"
      unfolding y o_def
      apply (rule in_interval_interval_bij)
      using y(1)
      using assms(3)[unfolded path_image_def subset_eq] int_nem
      apply auto
      done
  next
    fix x
    assume "x \<in> (interval_bij (a, b) (- 1, 1) \<circ> g) ` {0..1}"
    then obtain y where y:
        "y \<in> {0..1}"
        "x = (interval_bij (a, b) (- 1, 1) \<circ> g) y"
      unfolding image_iff ..
    show "x \<in> cbox -1 1"
      unfolding y o_def
      apply (rule in_interval_interval_bij)
      using y(1)
      using assms(4)[unfolded path_image_def subset_eq] int_nem
      apply auto
      done
  next
    show "(interval_bij (a, b) (- 1, 1) \<circ> f) 0 $ 1 = -1"
      and "(interval_bij (a, b) (- 1, 1) \<circ> f) 1 $ 1 = 1"
      and "(interval_bij (a, b) (- 1, 1) \<circ> g) 0 $ 2 = -1"
      and "(interval_bij (a, b) (- 1, 1) \<circ> g) 1 $ 2 = 1"
      using assms as
      by (simp_all add: axis_in_Basis cart_eq_inner_axis pathstart_def pathfinish_def interval_bij_def)
         (simp_all add: inner_axis)
  qed
  from z(1) obtain zf where zf:
      "zf \<in> {0..1}"
      "z = (interval_bij (a, b) (- 1, 1) \<circ> f) zf"
    unfolding image_iff ..
  from z(2) obtain zg where zg:
      "zg \<in> {0..1}"
      "z = (interval_bij (a, b) (- 1, 1) \<circ> g) zg"
    unfolding image_iff ..
  have *: "\<forall>i. (- 1) $ i < (1::real^2) $ i \<and> a $ i < b $ i"
    unfolding forall_2
    using as
    by auto
  show thesis
    apply (rule_tac z="interval_bij (- 1,1) (a,b) z" in that)
    apply (subst zf)
    defer
    apply (subst zg)
    unfolding o_def interval_bij_bij_cart[OF *] path_image_def
    using zf(1) zg(1)
    apply auto
    done
qed


subsection {* Some slightly ad hoc lemmas I use below *}

lemma segment_vertical:
  fixes a :: "real^2"
  assumes "a$1 = b$1"
  shows "x \<in> closed_segment a b \<longleftrightarrow>
    x$1 = a$1 \<and> x$1 = b$1 \<and> (a$2 \<le> x$2 \<and> x$2 \<le> b$2 \<or> b$2 \<le> x$2 \<and> x$2 \<le> a$2)"
  (is "_ = ?R")
proof -
  let ?L = "\<exists>u. (x $ 1 = (1 - u) * a $ 1 + u * b $ 1 \<and> x $ 2 = (1 - u) * a $ 2 + u * b $ 2) \<and> 0 \<le> u \<and> u \<le> 1"
  {
    presume "?L \<Longrightarrow> ?R" and "?R \<Longrightarrow> ?L"
    then show ?thesis
      unfolding closed_segment_def mem_Collect_eq
      unfolding vec_eq_iff forall_2 scalar_mult_eq_scaleR[symmetric] vector_component_simps
      by blast
  }
  {
    assume ?L
    then obtain u where u:
        "x $ 1 = (1 - u) * a $ 1 + u * b $ 1"
        "x $ 2 = (1 - u) * a $ 2 + u * b $ 2"
        "0 \<le> u"
        "u \<le> 1"
      by blast
    { fix b a
      assume "b + u * a > a + u * b"
      then have "(1 - u) * b > (1 - u) * a"
        by (auto simp add:field_simps)
      then have "b \<ge> a"
        apply (drule_tac mult_less_imp_less_left)
        using u
        apply auto
        done
      then have "u * a \<le> u * b"
        apply -
        apply (rule mult_left_mono[OF _ u(3)]) 
        using u(3-4)
        apply (auto simp add: field_simps)
        done
    } note * = this
    {
      fix a b
      assume "u * b > u * a"
      then have "(1 - u) * a \<le> (1 - u) * b"
        apply -
        apply (rule mult_left_mono)
        apply (drule mult_less_imp_less_left)
        using u
        apply auto
        done
      then have "a + u * b \<le> b + u * a"
        by (auto simp add: field_simps)
    } note ** = this
    then show ?R
      unfolding u assms
      using u
      by (auto simp add:field_simps not_le intro: * **)
  }
  {
    assume ?R
    then show ?L
    proof (cases "x$2 = b$2")
      case True
      then show ?L
        apply (rule_tac x="(x$2 - a$2) / (b$2 - a$2)" in exI)
        unfolding assms True
        using `?R`
        apply (auto simp add: field_simps)
        done
    next
      case False
      then show ?L
        apply (rule_tac x="1 - (x$2 - b$2) / (a$2 - b$2)" in exI)
        unfolding assms
        using `?R`
        apply (auto simp add: field_simps)
        done
    qed
  }
qed

lemma segment_horizontal:
  fixes a :: "real^2"
  assumes "a$2 = b$2"
  shows "x \<in> closed_segment a b \<longleftrightarrow>
    x$2 = a$2 \<and> x$2 = b$2 \<and> (a$1 \<le> x$1 \<and> x$1 \<le> b$1 \<or> b$1 \<le> x$1 \<and> x$1 \<le> a$1)"
  (is "_ = ?R")
proof -
  let ?L = "\<exists>u. (x $ 1 = (1 - u) * a $ 1 + u * b $ 1 \<and> x $ 2 = (1 - u) * a $ 2 + u * b $ 2) \<and> 0 \<le> u \<and> u \<le> 1"
  {
    presume "?L \<Longrightarrow> ?R" and "?R \<Longrightarrow> ?L"
    then show ?thesis
      unfolding closed_segment_def mem_Collect_eq
      unfolding vec_eq_iff forall_2 scalar_mult_eq_scaleR[symmetric] vector_component_simps
      by blast
  }
  {
    assume ?L
    then obtain u where u:
        "x $ 1 = (1 - u) * a $ 1 + u * b $ 1"
        "x $ 2 = (1 - u) * a $ 2 + u * b $ 2"
        "0 \<le> u"
        "u \<le> 1"
      by blast
    {
      fix b a
      assume "b + u * a > a + u * b"
      then have "(1 - u) * b > (1 - u) * a"
        by (auto simp add: field_simps)
      then have "b \<ge> a"
        apply (drule_tac mult_less_imp_less_left)
        using u
        apply auto
        done
      then have "u * a \<le> u * b"
        apply -
        apply (rule mult_left_mono[OF _ u(3)])
        using u(3-4)
        apply (auto simp add: field_simps)
        done
    } note * = this
    {
      fix a b
      assume "u * b > u * a"
      then have "(1 - u) * a \<le> (1 - u) * b"
        apply -
        apply (rule mult_left_mono)
        apply (drule mult_less_imp_less_left)
        using u
        apply auto
        done
      then have "a + u * b \<le> b + u * a"
        by (auto simp add: field_simps)
    } note ** = this
    then show ?R
      unfolding u assms
      using u
      by (auto simp add: field_simps not_le intro: * **)
  }
  {
    assume ?R
    then show ?L
    proof (cases "x$1 = b$1")
      case True
      then show ?L
        apply (rule_tac x="(x$1 - a$1) / (b$1 - a$1)" in exI)
        unfolding assms True
        using `?R`
        apply (auto simp add: field_simps)
        done
    next
      case False
      then show ?L
        apply (rule_tac x="1 - (x$1 - b$1) / (a$1 - b$1)" in exI)
        unfolding assms
        using `?R`
        apply (auto simp add: field_simps)
        done
    qed
  }
qed


subsection {* Useful Fashoda corollary pointed out to me by Tom Hales *}

lemma fashoda_interlace:
  fixes a :: "real^2"
  assumes "path f"
    and "path g"
    and "path_image f \<subseteq> cbox a b"
    and "path_image g \<subseteq> cbox a b"
    and "(pathstart f)$2 = a$2"
    and "(pathfinish f)$2 = a$2"
    and "(pathstart g)$2 = a$2"
    and "(pathfinish g)$2 = a$2"
    and "(pathstart f)$1 < (pathstart g)$1"
    and "(pathstart g)$1 < (pathfinish f)$1"
    and "(pathfinish f)$1 < (pathfinish g)$1"
  obtains z where "z \<in> path_image f" and "z \<in> path_image g"
proof -
  have "cbox a b \<noteq> {}"
    using path_image_nonempty[of f] using assms(3) by auto
  note ab=this[unfolded interval_eq_empty_cart not_ex forall_2 not_less]
  have "pathstart f \<in> cbox a b"
    and "pathfinish f \<in> cbox a b"
    and "pathstart g \<in> cbox a b"
    and "pathfinish g \<in> cbox a b"
    using pathstart_in_path_image pathfinish_in_path_image
    using assms(3-4)
    by auto
  note startfin = this[unfolded mem_interval_cart forall_2]
  let ?P1 = "linepath (vector[a$1 - 2, a$2 - 2]) (vector[(pathstart f)$1,a$2 - 2]) +++
     linepath(vector[(pathstart f)$1,a$2 - 2])(pathstart f) +++ f +++
     linepath(pathfinish f)(vector[(pathfinish f)$1,a$2 - 2]) +++
     linepath(vector[(pathfinish f)$1,a$2 - 2])(vector[b$1 + 2,a$2 - 2])" 
  let ?P2 = "linepath(vector[(pathstart g)$1, (pathstart g)$2 - 3])(pathstart g) +++ g +++
     linepath(pathfinish g)(vector[(pathfinish g)$1,a$2 - 1]) +++
     linepath(vector[(pathfinish g)$1,a$2 - 1])(vector[b$1 + 1,a$2 - 1]) +++
     linepath(vector[b$1 + 1,a$2 - 1])(vector[b$1 + 1,b$2 + 3])"
  let ?a = "vector[a$1 - 2, a$2 - 3]"
  let ?b = "vector[b$1 + 2, b$2 + 3]"
  have P1P2: "path_image ?P1 = path_image (linepath (vector[a$1 - 2, a$2 - 2]) (vector[(pathstart f)$1,a$2 - 2])) \<union>
      path_image (linepath(vector[(pathstart f)$1,a$2 - 2])(pathstart f)) \<union> path_image f \<union>
      path_image (linepath(pathfinish f)(vector[(pathfinish f)$1,a$2 - 2])) \<union>
      path_image (linepath(vector[(pathfinish f)$1,a$2 - 2])(vector[b$1 + 2,a$2 - 2]))"
    "path_image ?P2 = path_image(linepath(vector[(pathstart g)$1, (pathstart g)$2 - 3])(pathstart g)) \<union> path_image g \<union>
      path_image(linepath(pathfinish g)(vector[(pathfinish g)$1,a$2 - 1])) \<union>
      path_image(linepath(vector[(pathfinish g)$1,a$2 - 1])(vector[b$1 + 1,a$2 - 1])) \<union>
      path_image(linepath(vector[b$1 + 1,a$2 - 1])(vector[b$1 + 1,b$2 + 3]))" using assms(1-2)
      by(auto simp add: path_image_join path_linepath)
  have abab: "cbox a b \<subseteq> cbox ?a ?b"
    unfolding interval_cbox_cart[symmetric]
    by (auto simp add:less_eq_vec_def forall_2 vector_2)
  obtain z where
    "z \<in> path_image
          (linepath (vector [a $ 1 - 2, a $ 2 - 2]) (vector [pathstart f $ 1, a $ 2 - 2]) +++
           linepath (vector [pathstart f $ 1, a $ 2 - 2]) (pathstart f) +++
           f +++
           linepath (pathfinish f) (vector [pathfinish f $ 1, a $ 2 - 2]) +++
           linepath (vector [pathfinish f $ 1, a $ 2 - 2]) (vector [b $ 1 + 2, a $ 2 - 2]))"
    "z \<in> path_image
          (linepath (vector [pathstart g $ 1, pathstart g $ 2 - 3]) (pathstart g) +++
           g +++
           linepath (pathfinish g) (vector [pathfinish g $ 1, a $ 2 - 1]) +++
           linepath (vector [pathfinish g $ 1, a $ 2 - 1]) (vector [b $ 1 + 1, a $ 2 - 1]) +++
           linepath (vector [b $ 1 + 1, a $ 2 - 1]) (vector [b $ 1 + 1, b $ 2 + 3]))"
    apply (rule fashoda[of ?P1 ?P2 ?a ?b])
    unfolding pathstart_join pathfinish_join pathstart_linepath pathfinish_linepath vector_2
  proof -
    show "path ?P1" and "path ?P2"
      using assms by auto
    have "path_image ?P1 \<subseteq> cbox ?a ?b"
      unfolding P1P2 path_image_linepath
      apply (rule Un_least)+
      defer 3
      apply (rule_tac[1-4] convex_box(1)[unfolded convex_contains_segment,rule_format])
      unfolding mem_interval_cart forall_2 vector_2
      using ab startfin abab assms(3)
      using assms(9-)
      unfolding assms
      apply (auto simp add: field_simps box_def)
      done
    then show "path_image ?P1 \<subseteq> cbox ?a ?b" .
    have "path_image ?P2 \<subseteq> cbox ?a ?b"
      unfolding P1P2 path_image_linepath
      apply (rule Un_least)+
      defer 2
      apply (rule_tac[1-4] convex_box(1)[unfolded convex_contains_segment,rule_format])
      unfolding mem_interval_cart forall_2 vector_2
      using ab startfin abab assms(4)
      using assms(9-)
      unfolding assms
      apply (auto simp add: field_simps box_def)
      done
    then show "path_image ?P2 \<subseteq> cbox ?a ?b" .
    show "a $ 1 - 2 = a $ 1 - 2"
      and "b $ 1 + 2 = b $ 1 + 2"
      and "pathstart g $ 2 - 3 = a $ 2 - 3"
      and "b $ 2 + 3 = b $ 2 + 3"
      by (auto simp add: assms)
  qed
  note z=this[unfolded P1P2 path_image_linepath]
  show thesis
    apply (rule that[of z])
  proof -
    have "(z \<in> closed_segment (vector [a $ 1 - 2, a $ 2 - 2]) (vector [pathstart f $ 1, a $ 2 - 2]) \<or>
      z \<in> closed_segment (vector [pathstart f $ 1, a $ 2 - 2]) (pathstart f)) \<or>
      z \<in> closed_segment (pathfinish f) (vector [pathfinish f $ 1, a $ 2 - 2]) \<or>
      z \<in> closed_segment (vector [pathfinish f $ 1, a $ 2 - 2]) (vector [b $ 1 + 2, a $ 2 - 2]) \<Longrightarrow>
    (((z \<in> closed_segment (vector [pathstart g $ 1, pathstart g $ 2 - 3]) (pathstart g)) \<or>
      z \<in> closed_segment (pathfinish g) (vector [pathfinish g $ 1, a $ 2 - 1])) \<or>
      z \<in> closed_segment (vector [pathfinish g $ 1, a $ 2 - 1]) (vector [b $ 1 + 1, a $ 2 - 1])) \<or>
      z \<in> closed_segment (vector [b $ 1 + 1, a $ 2 - 1]) (vector [b $ 1 + 1, b $ 2 + 3]) \<Longrightarrow> False"
      apply (simp only: segment_vertical segment_horizontal vector_2)
    proof -
      case goal1 note as=this
      have "pathfinish f \<in> cbox a b"
        using assms(3) pathfinish_in_path_image[of f] by auto 
      then have "1 + b $ 1 \<le> pathfinish f $ 1 \<Longrightarrow> False"
        unfolding mem_interval_cart forall_2 by auto
      then have "z$1 \<noteq> pathfinish f$1"
        using as(2)
        using assms ab
        by (auto simp add: field_simps)
      moreover have "pathstart f \<in> cbox a b"
        using assms(3) pathstart_in_path_image[of f]
        by auto
      then have "1 + b $ 1 \<le> pathstart f $ 1 \<Longrightarrow> False"
        unfolding mem_interval_cart forall_2
        by auto
      then have "z$1 \<noteq> pathstart f$1"
        using as(2) using assms ab
        by (auto simp add: field_simps)
      ultimately have *: "z$2 = a$2 - 2"
        using goal1(1)
        by auto
      have "z$1 \<noteq> pathfinish g$1"
        using as(2)
        using assms ab
        by (auto simp add: field_simps *)
      moreover have "pathstart g \<in> cbox a b"
        using assms(4) pathstart_in_path_image[of g]
        by auto 
      note this[unfolded mem_interval_cart forall_2]
      then have "z$1 \<noteq> pathstart g$1"
        using as(1)
        using assms ab
        by (auto simp add: field_simps *)
      ultimately have "a $ 2 - 1 \<le> z $ 2 \<and> z $ 2 \<le> b $ 2 + 3 \<or> b $ 2 + 3 \<le> z $ 2 \<and> z $ 2 \<le> a $ 2 - 1"
        using as(2)
        unfolding * assms
        by (auto simp add: field_simps)
      then show False
        unfolding * using ab by auto
    qed
    then have "z \<in> path_image f \<or> z \<in> path_image g"
      using z unfolding Un_iff by blast
    then have z': "z \<in> cbox a b"
      using assms(3-4)
      by auto
    have "a $ 2 = z $ 2 \<Longrightarrow> (z $ 1 = pathstart f $ 1 \<or> z $ 1 = pathfinish f $ 1) \<Longrightarrow>
      z = pathstart f \<or> z = pathfinish f"
      unfolding vec_eq_iff forall_2 assms
      by auto
    with z' show "z \<in> path_image f"
      using z(1)
      unfolding Un_iff mem_interval_cart forall_2
      apply -
      apply (simp only: segment_vertical segment_horizontal vector_2)
      unfolding assms
      apply auto
      done
    have "a $ 2 = z $ 2 \<Longrightarrow> (z $ 1 = pathstart g $ 1 \<or> z $ 1 = pathfinish g $ 1) \<Longrightarrow>
      z = pathstart g \<or> z = pathfinish g"
      unfolding vec_eq_iff forall_2 assms
      by auto
    with z' show "z \<in> path_image g"
      using z(2)
      unfolding Un_iff mem_interval_cart forall_2
      apply (simp only: segment_vertical segment_horizontal vector_2)
      unfolding assms
      apply auto
      done
  qed
qed

(** The Following still needs to be translated. Maybe I will do that later.

(* ------------------------------------------------------------------------- *)
(* Complement in dimension N >= 2 of set homeomorphic to any interval in     *)
(* any dimension is (path-)connected. This naively generalizes the argument  *)
(* in Ryuji Maehara's paper "The Jordan curve theorem via the Brouwer        *)
(* fixed point theorem", American Mathematical Monthly 1984.                 *)
(* ------------------------------------------------------------------------- *)

let RETRACTION_INJECTIVE_IMAGE_INTERVAL = prove
 (`!p:real^M->real^N a b.
        ~(interval[a,b] = {}) /\
        p continuous_on interval[a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ p x = p y ==> x = y)
        ==> ?f. f continuous_on (:real^N) /\
                IMAGE f (:real^N) SUBSET (IMAGE p (interval[a,b])) /\
                (!x. x IN (IMAGE p (interval[a,b])) ==> f x = x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
  DISCH_THEN(X_CHOOSE_TAC `q:real^N->real^M`) THEN
  SUBGOAL_THEN `(q:real^N->real^M) continuous_on
                (IMAGE p (interval[a:real^M,b]))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_INVERSE THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^N->real^M`;
                 `IMAGE (p:real^M->real^N)
                 (interval[a,b])`;
                 `a:real^M`; `b:real^M`]
        TIETZE_CLOSED_INTERVAL) THEN
  ASM_SIMP_TAC[COMPACT_INTERVAL; COMPACT_CONTINUOUS_IMAGE;
               COMPACT_IMP_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(p:real^M->real^N) o (r:real^N->real^M)` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_UNIV] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let UNBOUNDED_PATH_COMPONENTS_COMPLEMENT_HOMEOMORPHIC_INTERVAL = prove
 (`!s:real^N->bool a b:real^M.
        s homeomorphic (interval[a,b])
        ==> !x. ~(x IN s) ==> ~bounded(path_component((:real^N) DIFF s) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic; homeomorphism] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p':real^N->real^M`; `p:real^M->real^N`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!x y. x IN interval[a,b] /\ y IN interval[a,b] /\
          (p:real^M->real^N) x = p y ==> x = y`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o funpow 4 CONJUNCT2) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ASM_CASES_TAC `interval[a:real^M,b] = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; DIFF_EMPTY; PATH_COMPONENT_UNIV;
                  NOT_BOUNDED_UNIV] THEN
  ABBREV_TAC `s = (:real^N) DIFF (IMAGE p (interval[a:real^M,b]))` THEN
  X_GEN_TAC `c:real^N` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c:real^N) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `bounded((path_component s c) UNION
                        (IMAGE (p:real^M->real^N) (interval[a,b])))`
  MP_TAC THENL
   [ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED; COMPACT_IMP_BOUNDED;
                 COMPACT_CONTINUOUS_IMAGE; COMPACT_INTERVAL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^N` o MATCH_MP BOUNDED_SUBSET_BALL) THEN
  REWRITE_TAC[UNION_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p:real^M->real^N`; `a:real^M`; `b:real^M`]
    RETRACTION_INJECTIVE_IMAGE_INTERVAL) THEN
  ASM_REWRITE_TAC[SUBSET; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN DISCH_TAC THEN
  ABBREV_TAC `q = \z:real^N. if z IN path_component s c then r(z) else z` THEN
  SUBGOAL_THEN
    `(q:real^N->real^N) continuous_on
     (closure(path_component s c) UNION ((:real^N) DIFF (path_component s c)))`
  MP_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    REWRITE_TAC[CLOSED_CLOSURE; CONTINUOUS_ON_ID; GSYM OPEN_CLOSED] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PATH_COMPONENT THEN EXPAND_TAC "s" THEN
      ASM_SIMP_TAC[GSYM CLOSED_OPEN; COMPACT_IMP_CLOSED;
                   COMPACT_CONTINUOUS_IMAGE; COMPACT_INTERVAL];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[SET_RULE `~(z IN (s DIFF t) /\ z IN t)`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL
     [`path_component s (z:real^N)`; `path_component s (c:real^N)`]
     OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[GSYM DISJOINT; PATH_COMPONENT_DISJOINT] THEN ANTS_TAC THENL
     [MATCH_MP_TAC OPEN_PATH_COMPONENT THEN EXPAND_TAC "s" THEN
      ASM_SIMP_TAC[GSYM CLOSED_OPEN; COMPACT_IMP_CLOSED;
                   COMPACT_CONTINUOUS_IMAGE; COMPACT_INTERVAL];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN] THEN
      REWRITE_TAC[PATH_COMPONENT_REFL_EQ] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closure(path_component s c) UNION ((:real^N) DIFF (path_component s c)) =
    (:real^N)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `s SUBSET t ==> t UNION (UNIV DIFF s) = UNIV`) THEN
    REWRITE_TAC[CLOSURE_SUBSET];
    DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`(\x. &2 % c - x) o
     (\x. c + B / norm(x - c) % (x - c)) o (q:real^N->real^N)`;
    `cball(c:real^N,B)`]
    BROUWER) THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC; COMPACT_CBALL; CONVEX_CBALL] THEN
  ASM_SIMP_TAC[CBALL_EQ_EMPTY; REAL_LT_IMP_LE; REAL_NOT_LT] THEN
  SUBGOAL_THEN `!x. ~((q:real^N->real^N) x = c)` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN EXPAND_TAC "q" THEN
    REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN COND_CASES_TAC THEN
    ASM SET_TAC[PATH_COMPONENT_REFL_EQ];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[o_DEF; real_div; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; NORM_EQ_0; VECTOR_SUB_EQ] THEN
    SUBGOAL_THEN
     `(\x:real^N. lift(norm(x - c))) = (lift o norm) o (\x. x - c)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST;
                 CONTINUOUS_ON_LIFT_NORM];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL; o_THM; dist] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `c - (&2 % c - (c + x)) = x`] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(c /\ b) <=> c ==> ~b`] THEN
    REWRITE_TAC[IN_CBALL; o_THM; dist] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `&2 % c - (c + x') = x <=> --x' = x - c`] THEN
    ASM_CASES_TAC `(x:real^N) IN path_component s c` THENL
     [MATCH_MP_TAC(NORM_ARITH `norm(y) < B /\ norm(x) = B ==> ~(--x = y)`) THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < B ==> abs B = B`] THEN
      UNDISCH_TAC `path_component s c SUBSET ball(c:real^N,B)` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN ASM_MESON_TAC[dist; NORM_SUB];
      EXPAND_TAC "q" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_ARITH `--(c % x) = x <=> (&1 + c) % x = vec 0`] THEN
      ASM_REWRITE_TAC[DE_MORGAN_THM; VECTOR_SUB_EQ; VECTOR_MUL_EQ_0] THEN
      SUBGOAL_THEN `~(x:real^N = c)` ASSUME_TAC THENL
       [ASM_MESON_TAC[PATH_COMPONENT_REFL; IN]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&1 + x = &0)`) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ]]]);;

let PATH_CONNECTED_COMPLEMENT_HOMEOMORPHIC_INTERVAL = prove
 (`!s:real^N->bool a b:real^M.
        2 <= dimindex(:N) /\ s homeomorphic interval[a,b]
        ==> path_connected((:real^N) DIFF s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
    UNBOUNDED_PATH_COMPONENTS_COMPLEMENT_HOMEOMORPHIC_INTERVAL) THEN
  ASM_REWRITE_TAC[SET_RULE `~(x IN s) <=> x IN (UNIV DIFF s)`] THEN
  ABBREV_TAC `t = (:real^N) DIFF s` THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_COMPACTNESS) THEN
  REWRITE_TAC[COMPACT_INTERVAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `B:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(?u:real^N. u IN path_component t x /\ B < norm(u)) /\
                (?v:real^N. v IN path_component t y /\ B < norm(v))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[BOUNDED_POS; REAL_NOT_LE]; ALL_TAC] THEN
  MATCH_MP_TAC PATH_COMPONENT_TRANS THEN EXISTS_TAC `u:real^N` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[IN]; ALL_TAC] THEN
  MATCH_MP_TAC PATH_COMPONENT_SYM THEN
  MATCH_MP_TAC PATH_COMPONENT_TRANS THEN EXISTS_TAC `v:real^N` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[IN]; ALL_TAC] THEN
  MATCH_MP_TAC PATH_COMPONENT_OF_SUBSET THEN
  EXISTS_TAC `(:real^N) DIFF cball(vec 0,B)` THEN CONJ_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC(SET_RULE
     `s SUBSET t ==> (u DIFF t) SUBSET (u DIFF s)`) THEN
    ASM_REWRITE_TAC[SUBSET; IN_CBALL_0];
    MP_TAC(ISPEC `cball(vec 0:real^N,B)`
       PATH_CONNECTED_COMPLEMENT_BOUNDED_CONVEX) THEN
    ASM_REWRITE_TAC[BOUNDED_CBALL; CONVEX_CBALL] THEN
    REWRITE_TAC[PATH_CONNECTED_IFF_PATH_COMPONENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_CBALL_0; REAL_NOT_LE]]);;

(* ------------------------------------------------------------------------- *)
(* In particular, apply all these to the special case of an arc.             *)
(* ------------------------------------------------------------------------- *)

let RETRACTION_ARC = prove
 (`!p. arc p
       ==> ?f. f continuous_on (:real^N) /\
               IMAGE f (:real^N) SUBSET path_image p /\
               (!x. x IN path_image p ==> f x = x)`,
  REWRITE_TAC[arc; path; path_image] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RETRACTION_INJECTIVE_IMAGE_INTERVAL THEN
  ASM_REWRITE_TAC[INTERVAL_EQ_EMPTY_CART_1; DROP_VEC; REAL_NOT_LT; REAL_POS]);;

let PATH_CONNECTED_ARC_COMPLEMENT = prove
 (`!p. 2 <= dimindex(:N) /\ arc p
       ==> path_connected((:real^N) DIFF path_image p)`,
  REWRITE_TAC[arc; path] THEN REPEAT STRIP_TAC THEN SIMP_TAC[path_image] THEN
  MP_TAC(ISPECL [`path_image p:real^N->bool`; `vec 0:real^1`; `vec 1:real^1`]
    PATH_CONNECTED_COMPLEMENT_HOMEOMORPHIC_INTERVAL) THEN
  ASM_REWRITE_TAC[path_image] THEN DISCH_THEN MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
  EXISTS_TAC `p:real^1->real^N` THEN ASM_REWRITE_TAC[COMPACT_INTERVAL]);;

let CONNECTED_ARC_COMPLEMENT = prove
 (`!p. 2 <= dimindex(:N) /\ arc p
       ==> connected((:real^N) DIFF path_image p)`,
  SIMP_TAC[PATH_CONNECTED_ARC_COMPLEMENT; PATH_CONNECTED_IMP_CONNECTED]);; *)

end
