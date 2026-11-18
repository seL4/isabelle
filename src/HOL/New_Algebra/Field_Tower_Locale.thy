section \<open>Nested Carrier-Set Fields as a Vector Space\<close>

theory Field_Tower_Locale
  imports Rank_Nullity Poly_Ring
begin

lemma (in Field) polynomial_vector_space:
  "Vector_Space R addition multiplication zero unit
    poly_add poly_zero poly_carrier
    (\<lambda>c p. poly_mult (poly_const c) p)"
proof -
  interpret P: Ring poly_carrier poly_add poly_mult poly_zero poly_one
    by (rule poly_ring)
  show ?thesis
  proof (intro Vector_Space.intro Vector_Space_axioms.intro)
    show "Field R addition multiplication zero unit"
      by (rule Field_axioms)
    show "Abelian_Group poly_carrier poly_add poly_zero"
      by (rule P.additive.Abelian_Group_axioms)
    show "\<And>c p. \<lbrakk>c \<in> R; p \<in> poly_carrier\<rbrakk> \<Longrightarrow>
      poly_mult (poly_const c) p \<in> poly_carrier"
      by (simp add: poly_mult_closed poly_const_closed)
    show "\<And>c p q. \<lbrakk>c \<in> R; p \<in> poly_carrier; q \<in> poly_carrier\<rbrakk>
      \<Longrightarrow> poly_mult (poly_const c) (poly_add p q) =
        poly_add (poly_mult (poly_const c) p) (poly_mult (poly_const c) q)"
      by (simp add: poly_mult_add_distrib_left poly_const_closed)
    show "\<And>c d p. \<lbrakk>c \<in> R; d \<in> R; p \<in> poly_carrier\<rbrakk>
      \<Longrightarrow> poly_mult (poly_const (addition c d)) p =
        poly_add (poly_mult (poly_const c) p) (poly_mult (poly_const d) p)"
      by (simp add: poly_const_add [symmetric] poly_const_closed
          poly_mult_add_distrib_right)
    show "\<And>c d p. \<lbrakk>c \<in> R; d \<in> R; p \<in> poly_carrier\<rbrakk>
      \<Longrightarrow> poly_mult (poly_const (multiplication c d)) p =
        poly_mult (poly_const c) (poly_mult (poly_const d) p)"
      by (simp add: poly_const_mult [symmetric] poly_const_closed poly_mult_assoc)
    show "\<And>p. p \<in> poly_carrier \<Longrightarrow> poly_mult (poly_const unit) p = p"
      by (simp add: poly_mult_one_left)
  qed
qed

text \<open>Two fields on nested carriers, sharing operations.  The larger carrier is a vector
  space over the smaller one.  No field type class is needed.\<close>
locale field_tower_locale =
  base: Field K addition multiplication zero unit +
  ext: Field L addition multiplication zero unit
  for K L :: "'a set"
    and addition multiplication :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and zero unit :: 'a +
  assumes base_subset: "K \<subseteq> L"
begin

sublocale vs: Vector_Space K addition multiplication zero unit addition zero L multiplication
proof (intro Vector_Space.intro Vector_Space.Vector_Space_axioms.intro)
  show "Field K addition multiplication zero unit" by (rule base.Field_axioms)
  show "Abelian_Group L addition zero" by (rule ext.additive.Abelian_Group_axioms)
  fix a v
  assume "a \<in> K" "v \<in> L"
  then show "multiplication a v \<in> L"
    using base_subset by (blast intro: ext.multiplicative.composition_closed)
next
  fix a u v
  assume "a \<in> K" "u \<in> L" "v \<in> L"
  then show "multiplication a (addition u v) =
    addition (multiplication a u) (multiplication a v)"
    using base_subset ext.distributive(1) by blast
next
  fix a b v
  assume "a \<in> K" "b \<in> K" "v \<in> L"
  then show "multiplication (addition a b) v =
    addition (multiplication a v) (multiplication b v)"
    using base_subset ext.distributive(2) by blast
next
  fix a b v
  assume "a \<in> K" "b \<in> K" "v \<in> L"
  then show "multiplication (multiplication a b) v =
    multiplication a (multiplication b v)"
    using base_subset ext.multiplicative.associative by blast
next
  fix v assume "v \<in> L"
  then show "multiplication unit v = v"
    by (rule ext.multiplicative.left_unit)
qed

sublocale pvs: Vector_Space K addition multiplication zero unit
  ext.poly_add ext.poly_zero ext.poly_carrier
  "(\<lambda>c p. ext.poly_mult (ext.poly_const c) p)"
proof -
  interpret W: Vector_Space L addition multiplication zero unit
    ext.poly_add ext.poly_zero ext.poly_carrier
    "(\<lambda>c p. ext.poly_mult (ext.poly_const c) p)"
    by (rule ext.polynomial_vector_space)
  show "Vector_Space K addition multiplication zero unit
    ext.poly_add ext.poly_zero ext.poly_carrier
    (\<lambda>c p. ext.poly_mult (ext.poly_const c) p)"
  proof (intro Vector_Space.intro Vector_Space_axioms.intro)
    show "Field K addition multiplication zero unit"
      by (rule base.Field_axioms)
    show "Abelian_Group ext.poly_carrier ext.poly_add ext.poly_zero"
      by (rule W.vadd_group)
    show "\<And>c p. \<lbrakk>c \<in> K; p \<in> ext.poly_carrier\<rbrakk>
      \<Longrightarrow> ext.poly_mult (ext.poly_const c) p \<in> ext.poly_carrier"
      using base_subset W.scale_closed by blast
    show "\<And>c p q. \<lbrakk>c \<in> K; p \<in> ext.poly_carrier; q \<in> ext.poly_carrier\<rbrakk>
      \<Longrightarrow> ext.poly_mult (ext.poly_const c) (ext.poly_add p q) =
        ext.poly_add (ext.poly_mult (ext.poly_const c) p)
          (ext.poly_mult (ext.poly_const c) q)"
      using base_subset W.scale_distrib_vadd by blast
    show "\<And>c d p. \<lbrakk>c \<in> K; d \<in> K; p \<in> ext.poly_carrier\<rbrakk>
      \<Longrightarrow> ext.poly_mult (ext.poly_const (addition c d)) p =
        ext.poly_add (ext.poly_mult (ext.poly_const c) p)
          (ext.poly_mult (ext.poly_const d) p)"
      using base_subset W.scale_distrib_add by blast
    show "\<And>c d p. \<lbrakk>c \<in> K; d \<in> K; p \<in> ext.poly_carrier\<rbrakk>
      \<Longrightarrow> ext.poly_mult (ext.poly_const (multiplication c d)) p =
        ext.poly_mult (ext.poly_const c) (ext.poly_mult (ext.poly_const d) p)"
      using base_subset W.scale_scale by blast
    show "\<And>p. p \<in> ext.poly_carrier \<Longrightarrow>
      ext.poly_mult (ext.poly_const unit) p = p"
      by (rule W.scale_one)
  qed
qed

lemma monom_module_homomorphism:
  "module_homomorphism K addition multiplication zero unit
    L addition zero multiplication
    ext.poly_carrier ext.poly_add ext.poly_zero
      (\<lambda>c p. ext.poly_mult (ext.poly_const c) p)
    (restrict (\<lambda>x. ext.monom x j) L)"
proof (intro module_homomorphism.intro vs.mod.Module_axioms
    pvs.mod.Module_axioms module_homomorphism_axioms.intro)
  show "Set_Theory.map (restrict (\<lambda>x. ext.monom x j) L)
    L ext.poly_carrier"
    by unfold_locales (use ext.monom_closed in \<open>auto simp: PiE_def extensional_def\<close>)
  fix x y assume x: "x \<in> L" and y: "y \<in> L"
  show "restrict (\<lambda>x. ext.monom x j) L (addition x y) =
    ext.poly_add (restrict (\<lambda>x. ext.monom x j) L x)
      (restrict (\<lambda>x. ext.monom x j) L y)"
    using x y by (auto simp: ext.monom_def ext.poly_add_def)
next
  fix c x assume c: "c \<in> K" and x: "x \<in> L"
  have cL: "c \<in> L" using c base_subset by blast
  have cx: "multiplication c x \<in> L"
    by (rule ext.multiplicative.composition_closed [OF cL x])
  have mx: "ext.monom x j \<in> ext.poly_carrier"
    by (rule ext.monom_closed [OF x])
  have eq: "ext.poly_mult (ext.poly_const c) (ext.monom x j) =
    ext.monom (multiplication c x) j"
  proof (rule ext)
    fix k
    have coeff: "ext.poly_mult (ext.poly_const c) (ext.monom x j) k =
      multiplication c (ext.monom x j k)"
      using ext.coeff_monom_mult [OF cL mx, of 0 k]
      by (simp add: ext.monom_0_eq_const)
    show "ext.poly_mult (ext.poly_const c) (ext.monom x j) k =
      ext.monom (multiplication c x) j k"
      using coeff cL x by (auto simp: ext.monom_def)
  qed
  show "restrict (\<lambda>x. ext.monom x j) L (multiplication c x) =
    ext.poly_mult (ext.poly_const c)
      (restrict (\<lambda>x. ext.monom x j) L x)"
    using x cx eq by simp
qed

lemma monom_span:
  assumes BL: "B \<subseteq> L" and x: "x \<in> vs.span B"
  shows "ext.monom x j \<in> pvs.span ((\<lambda>b. ext.monom b j) ` B)"
proof -
  interpret H: module_homomorphism K addition multiplication zero unit
    L addition zero multiplication
    ext.poly_carrier ext.poly_add ext.poly_zero
      "(\<lambda>c p. ext.poly_mult (ext.poly_const c) p)"
    "restrict (\<lambda>x. ext.monom x j) L"
    by (rule monom_module_homomorphism)
  have xL: "x \<in> L"
    using x vs.span_closed [OF BL] by blast
  have "restrict (\<lambda>x. ext.monom x j) L x \<in>
    pvs.span (restrict (\<lambda>x. ext.monom x j) L ` B)"
    using H.hom_span [OF BL] x by blast
  moreover have "restrict (\<lambda>x. ext.monom x j) L ` B =
    (\<lambda>b. ext.monom b j) ` B"
    using BL by (auto simp: image_def)
  ultimately show ?thesis using xL by simp
qed

lemma polynomial_fincomp_in_span:
  assumes fin: "finite A" and S: "S \<subseteq> ext.poly_carrier"
    and g: "\<And>i. i \<in> A \<Longrightarrow> g i \<in> pvs.span S"
  shows "pvs.vadd.fincomp g A \<in> pvs.span S"
  using fin g
proof (induct A rule: finite_induct)
  case empty
  then show ?case by (simp add: pvs.span_zero)
next
  case (insert a A)
  have ga: "g a \<in> pvs.span S" and gA: "\<And>i. i \<in> A \<Longrightarrow> g i \<in> pvs.span S"
    using insert.prems by auto
  have gAc: "g \<in> A \<rightarrow> ext.poly_carrier"
    using gA S pvs.span_closed by blast
  have gac: "g a \<in> ext.poly_carrier"
    using ga S pvs.span_closed by blast
  show ?case
    using insert.hyps gA ga
    by (simp add: pvs.vadd.fincomp_insert gAc gac pvs.span_vadd S)
qed

lemma low_polys_span:
  assumes finite: "finite B" and BL: "B \<subseteq> L"
    and spanning: "L \<subseteq> vs.span B"
    and pos: "0 < n" and r: "r \<in> ext.low_poly n"
  shows "r \<in> pvs.span
    ((\<lambda>(b,j). ext.monom b j) ` (B \<times> {..<n}))"
proof -
  let ?D = "(\<lambda>(b,j). ext.monom b j) ` (B \<times> {..<n})"
  have DL: "?D \<subseteq> ext.poly_carrier"
    using BL by (auto intro: ext.monom_closed)
  have rc: "r \<in> ext.poly_carrier"
    by (rule ext.low_poly_closed [OF r])
  have dr: "ext.degree r \<le> n - 1"
    using ext.low_poly_iff_degree [OF rc] r pos by auto
  have term_span: "ext.monom (r j) j \<in> pvs.span ?D" if j: "j < n" for j
  proof -
    have rj: "r j \<in> L" by (rule ext.poly_carrier_coeff_closed [OF rc])
    have small: "ext.monom (r j) j \<in>
      pvs.span ((\<lambda>b. ext.monom b j) ` B)"
      by (rule monom_span [OF BL]) (use rj spanning in blast)
    have sub: "(\<lambda>b. ext.monom b j) ` B \<subseteq> ?D"
      using j by auto
    show ?thesis using small pvs.span_mono [OF sub] by blast
  qed
  have sum: "pvs.vadd.fincomp (\<lambda>j. ext.monom (r j) j) {..<n} = r"
  proof -
    have "{..<n} = {..n - 1}" using pos by auto
    then show ?thesis using ext.poly_sum_monom [OF rc dr] by simp
  qed
  have "pvs.vadd.fincomp (\<lambda>j. ext.monom (r j) j) {..<n}
    \<in> pvs.span ?D"
    by (rule polynomial_fincomp_in_span [OF _ DL]) (auto intro: term_span)
  then show ?thesis using sum by simp
qed

lemma bounded_remainder_relation:
  assumes p: "p \<in> ext.poly_carrier" and pnz: "p \<noteq> ext.poly_zero"
    and pos: "0 < ext.degree p"
    and cK: "\<And>i. i \<le> N \<Longrightarrow> c i \<in> K"
    and cnz: "\<exists>i\<le>N. c i \<noteq> zero"
    and relation: "pvs.vadd.fincomp
      (\<lambda>i. ext.poly_mult (ext.poly_const (c i))
        (ext.pmod (ext.monom unit i) p)) {..N} = ext.poly_zero"
  shows "\<exists>Q. Q \<in> base.poly_carrier \<and> Q \<noteq> base.poly_zero
    \<and> ext.pmod Q p = ext.poly_zero"
proof -
  define Q where "Q = (\<lambda>i. if i \<le> N then c i else zero)"
  have QK: "Q \<in> base.poly_carrier"
  proof (rule base.poly_carrierI)
    have "{i. Q i \<noteq> zero} \<subseteq> {..N}"
      by (auto simp: Q_def)
    then show "finite {i. Q i \<noteq> zero}"
      by (rule finite_subset) simp
    show "\<And>i. Q i \<in> K"
      using cK by (auto simp: Q_def)
  qed
  have Qnz: "Q \<noteq> base.poly_zero"
    using cnz by (auto simp: Q_def base.poly_zero_def fun_eq_iff)
  have QL: "Q \<in> ext.poly_carrier"
  proof (rule ext.poly_carrierI)
    show "finite {i. Q i \<noteq> zero}"
      by (rule base.poly_carrier_finite [OF QK])
    show "\<And>i. Q i \<in> L"
      using QK base_subset base.poly_carrier_coeff_closed by blast
  qed
  have degQ: "ext.degree Q \<le> N"
    by (rule ext.degree_leI [OF QL])
      (auto simp: Q_def)
  have sumQ: "pvs.vadd.fincomp (\<lambda>i. ext.monom (c i) i) {..N} = Q"
  proof -
    have same: "pvs.vadd.fincomp (\<lambda>i. ext.monom (Q i) i) {..N} =
      pvs.vadd.fincomp (\<lambda>i. ext.monom (c i) i) {..N}"
      by (rule pvs.vadd.fincomp_cong')
        (use cK base_subset in \<open>auto simp: Q_def intro: ext.monom_closed\<close>)
    show ?thesis using ext.poly_sum_monom [OF QL degQ] same by simp
  qed
  have term_eq: "ext.pmod (ext.monom (c i) i) p =
    ext.poly_mult (ext.poly_const (c i))
      (ext.pmod (ext.monom unit i) p)" if i: "i \<le> N" for i
  proof -
    have ciL: "c i \<in> L" using cK [OF i] base_subset by blast
    have mi: "ext.monom (c i) i =
      ext.poly_mult (ext.poly_const (c i)) (ext.monom unit i)"
      using ciL ext.poly_const_mult_monom [OF ciL] by simp
    show ?thesis
      unfolding mi
      by (rule ext.pmod_const_mult
        [OF ciL ext.monom_closed [OF ext.multiplicative.unit_closed] p pnz pos])
  qed
  have mono: "\<And>i. i \<le> N \<Longrightarrow> ext.monom (c i) i \<in> ext.poly_carrier"
    using cK base_subset by (blast intro: ext.monom_closed)
  have rr: "\<And>i. i \<le> N \<Longrightarrow> ext.pmod (ext.monom (c i) i) p
    \<in> ext.poly_carrier"
    by (rule ext.pmod_closed [OF mono p pnz])
  have prod: "\<And>i. i \<le> N \<Longrightarrow>
    ext.poly_mult (ext.poly_const (c i))
      (ext.pmod (ext.monom unit i) p) \<in> ext.poly_carrier"
    using rr term_eq by simp
  have eq: "pvs.vadd.fincomp
      (\<lambda>i. ext.pmod (ext.monom (c i) i) p) {..N} =
    pvs.vadd.fincomp
      (\<lambda>i. ext.poly_mult (ext.poly_const (c i))
        (ext.pmod (ext.monom unit i) p)) {..N}"
    by (rule pvs.vadd.fincomp_cong') (use rr prod term_eq in auto)
  have "ext.pmod Q p =
    pvs.vadd.fincomp (\<lambda>i. ext.pmod (ext.monom (c i) i) p) {..N}"
  proof -
    have pm: "pvs.vadd.fincomp
        (\<lambda>i. ext.pmod (ext.monom (c i) i) p) {..N} =
      ext.pmod (pvs.vadd.fincomp (\<lambda>i. ext.monom (c i) i) {..N}) p"
      by (rule ext.pmod_fincomp
        [where I="{..N}" and f="\<lambda>i. ext.monom (c i) i",
          OF _ _ p pnz]) (auto intro: mono)
    show ?thesis using pm sumQ by simp
  qed
  then have "ext.pmod Q p = ext.poly_zero"
    using eq relation by simp
  then show ?thesis using QK Qnz by blast
qed

theorem finite_spanning_polynomial_multiple:
  assumes finB: "finite B" and BL: "B \<subseteq> L"
    and spanning: "L \<subseteq> vs.span B"
    and p: "p \<in> ext.poly_carrier" and pos: "0 < ext.degree p"
  shows "\<exists>Q. Q \<in> base.poly_carrier \<and> Q \<noteq> base.poly_zero
    \<and> ext.pmod Q p = ext.poly_zero"
proof -
  let ?n = "ext.degree p"
  let ?D = "(\<lambda>(b,j). ext.monom b j) ` (B \<times> {..<?n})"
  let ?N = "card ?D"
  let ?J = "{..?N}"
  let ?r = "\<lambda>i. ext.pmod (ext.monom unit i) p"
  have pnz: "p \<noteq> ext.poly_zero" using pos by auto
  have finD: "finite ?D" using finB by simp
  have DL: "?D \<subseteq> ext.poly_carrier"
    using BL by (auto intro: ext.monom_closed)
  have rlow: "?r i \<in> ext.low_poly ?n" for i
    by (rule ext.pmod_low_poly
      [OF ext.monom_closed [OF ext.multiplicative.unit_closed] p pnz])
  have rspan: "?r i \<in> pvs.span ?D" for i
    by (rule low_polys_span [OF finB BL spanning pos rlow])
  show ?thesis
  proof (cases "inj_on ?r ?J")
    case True
    let ?P = "?r ` ?J"
    have pc: "?P \<subseteq> ext.poly_carrier"
      using rlow ext.low_poly_closed by blast
    have Pspan: "?P \<subseteq> pvs.span ?D"
      using rspan by blast
    have cardP: "card ?P = ?N + 1"
      using True by (simp add: card_image)
    have dep: "\<not> pvs.lin_indep ?P"
      using pvs.independent_le_span [OF _ finD DL Pspan] cardP by force
    obtain d where dPiE: "d \<in> ?P \<rightarrow>\<^sub>E K"
      and lin0: "pvs.lincomb d ?P = ext.poly_zero"
      and non: "\<not> (\<forall>v\<in>?P. d v = zero)"
      using dep pc by (auto simp: pvs.lin_indep_def)
    have dK: "d v \<in> K" if "v \<in> ?P" for v
      using dPiE that by auto
    have terms: "(\<lambda>v. ext.poly_mult (ext.poly_const (d v)) v)
      \<in> ?P \<rightarrow> ext.poly_carrier"
      using pc dK pvs.scale_closed by auto
    have rel: "pvs.vadd.fincomp
      (\<lambda>i. ext.poly_mult (ext.poly_const (d (?r i))) (?r i)) ?J
      = ext.poly_zero"
      using lin0 pvs.vadd.fincomp_reindex [OF terms True]
      by (simp add: pvs.lincomb_def)
    have cK: "\<And>i. i \<le> ?N \<Longrightarrow> d (?r i) \<in> K"
      using dK by blast
    have cnz: "\<exists>i\<le>?N. d (?r i) \<noteq> zero"
      using non by blast
    show ?thesis
      by (rule bounded_remainder_relation [OF p pnz pos cK cnz rel])
  next
    case False
    then obtain i j where i: "i \<in> ?J" and j: "j \<in> ?J"
      and ij: "i \<noteq> j" and eq: "?r i = ?r j"
      by (auto simp: inj_on_def)
    define c where "c = (\<lambda>k. if k = i then unit
      else if k = j then base.additive.inverse unit else zero)"
    have cK: "c k \<in> K" if "k \<le> ?N" for k
      using that by (auto simp: c_def)
    have cnz: "\<exists>k\<le>?N. c k \<noteq> zero"
      using i ij base.nontrivial by (auto simp: c_def)
    let ?f = "\<lambda>k. ext.poly_mult (ext.poly_const (c k)) (?r k)"
    have rc: "?r k \<in> ext.poly_carrier" for k
      by (rule ext.low_poly_closed [OF rlow])
    have fcar: "?f \<in> ?J \<rightarrow> ext.poly_carrier"
      using cK rc pvs.scale_closed by auto
    have fi: "?f i = ?r i"
      using i ij rc [of i] by (simp add: c_def ext.poly_mult_one_left)
    have fj: "?f j = pvs.vadd.inverse (?r j)"
      using ij rc [of j] pvs.mod.scale_neg_scalar
        [OF base.multiplicative.unit_closed rc [of j]]
      by (simp add: c_def ext.poly_mult_one_left)
    have fk: "?f k = ext.poly_zero" if "k \<in> ?J - {i,j}" for k
      using that rc [of k] by (simp add: c_def ext.poly_mult_zero_left)
    let ?S = "?J - {i,j}"
    have finS: "finite ?S" by simp
    have fS: "?f \<in> ?S \<rightarrow> ext.poly_carrier"
      using fcar by auto
    have tail0: "pvs.vadd.fincomp ?f ?S = ext.poly_zero"
      by (rule pvs.vadd.fincomp_unit_eqI) (use fk in auto)
    have stepj: "pvs.vadd.fincomp ?f (insert j ?S) = ?f j"
      using pvs.vadd.fincomp_insert [OF finS _ fS] tail0 fcar j
      by auto
    have decomp: "?J = insert i (insert j ?S)"
      using i j by auto
    have fJS: "?f \<in> insert j ?S \<rightarrow> ext.poly_carrier"
      using fcar j by auto
    have fiC: "?f i \<in> ext.poly_carrier"
      using fcar i by auto
    have first: "pvs.vadd.fincomp ?f ?J =
      ext.poly_add (?f i) (pvs.vadd.fincomp ?f (insert j ?S))"
      using pvs.vadd.fincomp_insert
        [OF _ _ fJS fiC] decomp ij
      by auto
    have rel: "pvs.vadd.fincomp ?f ?J = ext.poly_zero"
      using first stepj fi fj eq rc [of i]
      by (simp add: pvs.vadd.invertible_right_inverse)
    show ?thesis
      by (rule bounded_remainder_relation [OF p pnz pos cK cnz rel])
  qed
qed

definition algebraic_over_base :: "'a \<Rightarrow> bool"
  where "algebraic_over_base x \<longleftrightarrow>
    x \<in> L \<and> (\<exists>p \<in> base.poly_carrier.
      p \<noteq> base.poly_zero \<and> ext.eval x p = zero)"

lemma algebraic_over_baseI:
  assumes "x \<in> L" and "p \<in> base.poly_carrier"
    and "p \<noteq> base.poly_zero" and "ext.eval x p = zero"
  shows "algebraic_over_base x"
  using assms by (auto simp: algebraic_over_base_def)

lemma algebraic_over_baseD:
  assumes "algebraic_over_base x"
  obtains p where "x \<in> L" and "p \<in> base.poly_carrier"
    and "p \<noteq> base.poly_zero" and "ext.eval x p = zero"
  using assms by (auto simp: algebraic_over_base_def)

lemma base_poly_carrier_subset_ext:
  "base.poly_carrier \<subseteq> ext.poly_carrier"
proof
  fix p assume p: "p \<in> base.poly_carrier"
  show "p \<in> ext.poly_carrier"
  proof (rule ext.poly_carrierI)
    show "finite {i. p i \<noteq> zero}"
      using p by (rule base.poly_carrier_finite)
    show "\<And>i. p i \<in> L"
      using p base_subset by (blast intro: base.poly_carrier_coeff_closed)
  qed
qed

lemma additive_inverse_agrees:
  assumes x: "x \<in> K"
  shows "base.additive.inverse x = ext.additive.inverse x"
proof -
  have S: "Subgroup K L addition zero"
    by unfold_locales
      (use base_subset in
        \<open>blast intro: base.additive.composition_closed base.additive.unit_closed\<close>)+
  interpret S: Subgroup K L addition zero by (rule S)
  show ?thesis using S.subgroup_inverse_equality [OF x] by simp
qed

lemma additive_fincomp_agrees:
  assumes fin: "finite A" and f: "f \<in> A \<rightarrow> K"
  shows "base.additive.fincomp f A = ext.additive.fincomp f A"
  using fin f
proof (induct A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a A)
  have fA: "f \<in> A \<rightarrow> K" and fa: "f a \<in> K"
    using insert.prems by auto
  have fAL: "f \<in> A \<rightarrow> L" and faL: "f a \<in> L"
    using fA fa base_subset by auto
  show ?case
    using insert fA
    by (simp add: base.additive.fincomp_insert
        ext.additive.fincomp_insert fA fa fAL faL)
qed

lemma additive_fincomp_in_span:
  assumes fin: "finite A" and SL: "S \<subseteq> L"
    and g: "\<And>i. i \<in> A \<Longrightarrow> g i \<in> vs.span S"
  shows "ext.additive.fincomp g A \<in> vs.span S"
  using fin g
proof (induct A rule: finite_induct)
  case empty
  then show ?case by (simp add: vs.span_zero)
next
  case (insert a A)
  have ga: "g a \<in> vs.span S" and gA: "\<And>i. i \<in> A \<Longrightarrow> g i \<in> vs.span S"
    using insert.prems by auto
  have gAL: "g \<in> A \<rightarrow> L" and gaL: "g a \<in> L"
    using ga gA SL vs.span_subset_V by auto
  show ?case
    using insert gA ga
    by (simp add: ext.additive.fincomp_insert gAL gaL vs.span_vadd SL)
qed

lemma poly_add_agrees:
  "base.poly_add p q = ext.poly_add p q"
  by (simp add: base.poly_add_def ext.poly_add_def)

lemma poly_mult_agrees:
  assumes p: "p \<in> base.poly_carrier" and q: "q \<in> base.poly_carrier"
  shows "base.poly_mult p q = ext.poly_mult p q"
proof (rule ext)
  fix k
  have termsK: "(\<lambda>i. multiplication (p i) (q (k - i))) \<in> {..k} \<rightarrow> K"
    using p q by (auto intro: base.multiplicative.composition_closed
        base.poly_carrier_coeff_closed)
  show "base.poly_mult p q k = ext.poly_mult p q k"
    using additive_fincomp_agrees [OF _ termsK]
    by (simp add: base.poly_mult_def ext.poly_mult_def)
qed

lemma poly_neg_agrees:
  assumes p: "p \<in> base.poly_carrier"
  shows "base.poly_neg p = ext.poly_neg p"
proof (rule ext)
  fix k
  have pk: "p k \<in> K" by (rule base.poly_carrier_coeff_closed [OF p])
  show "base.poly_neg p k = ext.poly_neg p k"
    using additive_inverse_agrees [OF pk]
    by (simp only: base.poly_neg_def ext.poly_neg_def)
qed

lemma root_factor_agrees:
  assumes a: "a \<in> K"
  shows "base.root_factor a = ext.root_factor a"
proof -
  have pc: "base.poly_const a \<in> base.poly_carrier"
    by (rule base.poly_const_closed [OF a])
  show ?thesis
    unfolding base.root_factor_def ext.root_factor_def
    by (subst poly_neg_agrees [OF pc]) (rule refl)
qed

lemma poly_prod_agrees:
  assumes fs: "\<And>f. f \<in> set fs \<Longrightarrow> f \<in> base.poly_carrier"
  shows "base.poly_prod fs = ext.poly_prod fs"
  using fs
proof (induct fs)
  case Nil
  then show ?case by simp
next
  case (Cons f fs)
  have f: "f \<in> base.poly_carrier" using Cons.prems by simp
  have tail: "\<And>g. g \<in> set fs \<Longrightarrow> g \<in> base.poly_carrier"
    using Cons.prems by simp
  have prod: "base.poly_prod fs \<in> base.poly_carrier"
    by (rule base.poly_prod_closed [OF tail])
  show ?case
    using Cons.hyps [OF tail] poly_mult_agrees [OF f prod] by simp
qed

theorem splits_descends:
  assumes p: "p \<in> base.poly_carrier" and sp: "ext.splits p"
    and roots: "\<And>x. \<lbrakk>x \<in> L; ext.eval x p = zero\<rbrakk> \<Longrightarrow> x \<in> K"
  shows "base.splits p"
proof (cases "p = base.poly_zero")
  case True
  then show ?thesis by simp
next
  case False
  have pL: "p \<in> ext.poly_carrier"
    using p base_poly_carrier_subset_ext by blast
  have pneq: "p \<noteq> ext.poly_zero"
    using False by (simp add: base.poly_zero_def ext.poly_zero_def)
  obtain c as where cL: "c \<in> L" and asL: "set as \<subseteq> L"
    and peq: "p = ext.poly_mult (ext.poly_const c)
      (ext.poly_prod (List.map ext.root_factor as))"
    using sp by (rule ext.splitsE)
  have asK: "set as \<subseteq> K"
  proof
    fix x assume x: "x \<in> set as"
    have xL: "x \<in> L" using x asL by blast
    have ev: "ext.eval x p = zero"
      by (rule ext.splits_factor_root [OF cL asL peq x])
    show "x \<in> K" by (rule roots [OF xL ev])
  qed
  have factorsK: "\<And>f. f \<in> set (List.map base.root_factor as)
      \<Longrightarrow> f \<in> base.poly_carrier"
    using asK by (auto intro: base.root_factor_closed)
  have qK: "base.poly_prod (List.map base.root_factor as)
      \<in> base.poly_carrier"
    by (rule base.poly_prod_closed [OF factorsK])
  have rf: "List.map base.root_factor as = List.map ext.root_factor as"
    using asK by (intro list.map_cong) (auto intro: root_factor_agrees)
  have qeq0: "base.poly_prod (List.map base.root_factor as) =
      ext.poly_prod (List.map base.root_factor as)"
    by (rule poly_prod_agrees [OF factorsK])
  have qeq1: "ext.poly_prod (List.map base.root_factor as) =
      ext.poly_prod (List.map ext.root_factor as)"
    by (rule arg_cong [OF rf])
  have qeq: "base.poly_prod (List.map base.root_factor as) =
      ext.poly_prod (List.map ext.root_factor as)"
    by (rule trans [OF qeq0 qeq1])
  let ?q = "ext.poly_prod (List.map ext.root_factor as)"
  have qL: "?q \<in> ext.poly_carrier"
    by (subst qeq [symmetric])
      (rule subsetD [OF base_poly_carrier_subset_ext qK])
  have qnz: "?q \<noteq> ext.poly_zero"
  proof
    assume "?q = ext.poly_zero"
    then have "p = ext.poly_zero"
      using peq ext.poly_const_closed [OF cL]
      by (simp add: ext.poly_mult_zero_right)
    then show False using pneq by contradiction
  qed
  obtain k where qknz: "?q k \<noteq> zero"
    using qnz by (auto simp: ext.poly_zero_def fun_eq_iff)
  have pk: "p k \<in> K" by (rule base.poly_carrier_coeff_closed [OF p])
  have qk: "?q k \<in> K"
    by (subst qeq [symmetric])
      (rule base.poly_carrier_coeff_closed [OF qK])
  have qi: "base.multiplicative.invertible (?q k)"
    by (rule base.field_inverse [OF qk qknz])
  have iqK: "base.multiplicative.inverse (?q k) \<in> K"
    by (rule base.multiplicative.invertible_inverse_closed [OF qi qk])
  have ri: "multiplication (?q k) (base.multiplicative.inverse (?q k)) = unit"
    by (rule base.multiplicative.invertible_right_inverse [OF qi qk])
  have coeff: "p k = multiplication c (?q k)"
    using peq ext.coeff_monom_mult [OF cL qL, of 0 k]
    by (simp add: ext.monom_0_eq_const)
  have qkL: "?q k \<in> L" and iqL: "base.multiplicative.inverse (?q k) \<in> L"
    using base_subset qk iqK by blast+
  have cexpr: "c = multiplication (p k) (base.multiplicative.inverse (?q k))"
  proof -
    have "c = multiplication c unit"
      using cL by simp
    also have "\<dots> =
      multiplication c (multiplication (?q k) (base.multiplicative.inverse (?q k)))"
      using ri by simp
    also have "\<dots> =
      multiplication (multiplication c (?q k)) (base.multiplicative.inverse (?q k))"
      using ext.multiplicative.associative [OF cL qkL iqL] by simp
    also have "\<dots> = multiplication (p k) (base.multiplicative.inverse (?q k))"
      using coeff by simp
    finally show ?thesis .
  qed
  have cK: "c \<in> K"
    using cexpr pk iqK by (blast intro: base.multiplicative.composition_closed)
  have pcK: "base.poly_const c \<in> base.poly_carrier"
    by (rule base.poly_const_closed [OF cK])
  have peqK: "p = base.poly_mult (base.poly_const c)
    (base.poly_prod (List.map base.root_factor as))"
    using peq qeq poly_mult_agrees [OF pcK qK] by simp
  show ?thesis
    by (rule base.splitsI [OF cK asK peqK])
qed

lemma eval_agrees_on_base:
  assumes x: "x \<in> K" and p: "p \<in> base.poly_carrier"
  shows "base.eval x p = ext.eval x p"
proof -
  have terms: "(\<lambda>i. multiplication (p i) (base.rpow x i))
    \<in> {..base.degree p} \<rightarrow> K"
    using x p by (auto intro: base.multiplicative.composition_closed
        base.poly_carrier_coeff_closed base.rpow_closed)
  show ?thesis
    unfolding base.eval_def ext.eval_def
    by (rule additive_fincomp_agrees [OF _ terms]) simp
qed

lemma eval_pmod_at_root:
  assumes x: "x \<in> L" and q: "q \<in> base.poly_carrier"
    and qnz: "q \<noteq> base.poly_zero" and root: "ext.eval x q = zero"
    and p: "p \<in> base.poly_carrier"
  shows "ext.eval x p = ext.eval x (base.pmod p q)"
proof -
  obtain t where t: "t \<in> base.poly_carrier"
    and r: "base.pmod p q \<in> base.poly_carrier"
    and eq: "p = base.poly_add (base.poly_mult q t) (base.pmod p q)"
    using base.pmod_spec [OF p q qnz] by blast
  have qL: "q \<in> ext.poly_carrier" and tL: "t \<in> ext.poly_carrier"
    and rL: "base.pmod p q \<in> ext.poly_carrier"
    using q t r base_poly_carrier_subset_ext by blast+
  have "ext.eval x p =
      ext.eval x (ext.poly_add (ext.poly_mult q t) (base.pmod p q))"
    using eq poly_add_agrees poly_mult_agrees [OF q t] by simp
  also have "\<dots> = addition (ext.eval x (ext.poly_mult q t))
      (ext.eval x (base.pmod p q))"
    using ext.eval_add [OF ext.poly_mult_closed [OF qL tL] rL x] by simp
  also have "\<dots> = ext.eval x (base.pmod p q)"
  proof -
    have z: "ext.eval x (ext.poly_mult q t) = zero"
      using ext.eval_mult [OF qL tL x] ext.eval_closed [OF tL x] root
      by simp
    have rclosed: "ext.eval x (base.pmod p q) \<in> L"
      by (rule ext.eval_closed [OF rL x])
    show ?thesis
      using z ext.additive.left_unit [OF rclosed] by simp
  qed
  finally show ?thesis .
qed

definition simple_extension :: "'a \<Rightarrow> 'a set"
  where "simple_extension x = ext.eval x ` base.poly_carrier"

lemma simple_extension_subset:
  assumes x: "x \<in> L"
  shows "simple_extension x \<subseteq> L"
  using x base_poly_carrier_subset_ext
  by (auto simp: simple_extension_def intro: ext.eval_closed)

lemma simple_extension_contains_base:
  assumes x: "x \<in> L"
  shows "K \<subseteq> simple_extension x"
proof
  fix a assume a: "a \<in> K"
  have p: "base.poly_const a \<in> base.poly_carrier"
    by (rule base.poly_const_closed [OF a])
  have aL: "a \<in> L" using a base_subset by blast
  have ev: "ext.eval x (base.poly_const a) = a"
    using ext.eval_const [OF x aL]
    by (simp only: base.poly_const_def ext.poly_const_def)
  have "ext.eval x (base.poly_const a) \<in> simple_extension x"
    unfolding simple_extension_def by (rule imageI [OF p])
  then show "a \<in> simple_extension x" using ev by simp
qed

lemma simple_extension_contains_generator:
  assumes x: "x \<in> L"
  shows "x \<in> simple_extension x"
proof -
  have v: "base.var \<in> base.poly_carrier"
    by (rule base.var_closed)
  have eq: "base.var = ext.var"
    by (rule refl)
  have ev: "ext.eval x base.var = x"
    using ext.eval_var [OF x] eq by metis
  have "ext.eval x base.var \<in> simple_extension x"
    unfolding simple_extension_def by (rule imageI [OF v])
  then show ?thesis using ev by simp
qed

lemma simple_extension_add:
  assumes x: "x \<in> L" and a: "a \<in> simple_extension x"
    and b: "b \<in> simple_extension x"
  shows "addition a b \<in> simple_extension x"
proof -
  obtain p q where p: "p \<in> base.poly_carrier" and ap: "a = ext.eval x p"
    and q: "q \<in> base.poly_carrier" and bq: "b = ext.eval x q"
    using a b by (auto simp: simple_extension_def)
  have pq: "base.poly_add p q \<in> base.poly_carrier"
    by (rule base.poly_add_closed [OF p q])
  have pL: "p \<in> ext.poly_carrier" and qL: "q \<in> ext.poly_carrier"
    using p q base_poly_carrier_subset_ext by blast+
  have ev: "ext.eval x (base.poly_add p q) = addition a b"
    using ext.eval_add [OF pL qL x] poly_add_agrees ap bq
    by metis
  have "ext.eval x (base.poly_add p q) \<in> simple_extension x"
    unfolding simple_extension_def by (rule imageI [OF pq])
  then show ?thesis using ev by simp
qed

lemma simple_extension_mult:
  assumes x: "x \<in> L" and a: "a \<in> simple_extension x"
    and b: "b \<in> simple_extension x"
  shows "multiplication a b \<in> simple_extension x"
proof -
  obtain p q where p: "p \<in> base.poly_carrier" and ap: "a = ext.eval x p"
    and q: "q \<in> base.poly_carrier" and bq: "b = ext.eval x q"
    using a b by (auto simp: simple_extension_def)
  have pq: "base.poly_mult p q \<in> base.poly_carrier"
    by (rule base.poly_mult_closed [OF p q])
  have pL: "p \<in> ext.poly_carrier" and qL: "q \<in> ext.poly_carrier"
    using p q base_poly_carrier_subset_ext by blast+
  have ev: "ext.eval x (base.poly_mult p q) = multiplication a b"
    using ext.eval_mult [OF pL qL x] poly_mult_agrees [OF p q] ap bq
    by metis
  have "ext.eval x (base.poly_mult p q) \<in> simple_extension x"
    unfolding simple_extension_def by (rule imageI [OF pq])
  then show ?thesis using ev by simp
qed

lemma simple_extension_neg:
  assumes x: "x \<in> L" and a: "a \<in> simple_extension x"
  shows "ext.additive.inverse a \<in> simple_extension x"
proof -
  obtain p where p: "p \<in> base.poly_carrier" and ap: "a = ext.eval x p"
    using a by (auto simp: simple_extension_def)
  have np: "base.poly_neg p \<in> base.poly_carrier"
    by (rule base.poly_neg_closed [OF p])
  have pL: "p \<in> ext.poly_carrier"
    using p base_poly_carrier_subset_ext by blast
  have ev: "ext.eval x (base.poly_neg p) = ext.additive.inverse a"
    using ext.eval_neg [OF pL x] poly_neg_agrees [OF p] ap
    by metis
  have "ext.eval x (base.poly_neg p) \<in> simple_extension x"
    unfolding simple_extension_def by (rule imageI [OF np])
  then show ?thesis using ev by simp
qed

lemma simple_extension_submodule:
  assumes x: "x \<in> L"
  shows "vs.mod.submodule (simple_extension x)"
proof (rule vs.mod.submoduleI)
  show "simple_extension x \<subseteq> L"
    by (rule simple_extension_subset [OF x])
  have KS: "K \<subseteq> simple_extension x"
    by (rule simple_extension_contains_base [OF x])
  show "zero \<in> simple_extension x"
    using KS base.additive.unit_closed by blast
  fix u v
  assume "u \<in> simple_extension x" "v \<in> simple_extension x"
  then show "addition u v \<in> simple_extension x"
    by (rule simple_extension_add [OF x])
next
  fix a v
  assume a: "a \<in> K" and v: "v \<in> simple_extension x"
  have "a \<in> simple_extension x"
    using a simple_extension_contains_base [OF x] by blast
  then show "multiplication a v \<in> simple_extension x"
    by (rule simple_extension_mult [OF x _ v])
qed

theorem simple_extension_finite_span:
  assumes alg: "algebraic_over_base x"
  obtains B where "finite B" "B \<subseteq> simple_extension x"
    "simple_extension x \<subseteq> vs.span B"
proof -
  obtain q where x: "x \<in> L" and q: "q \<in> base.poly_carrier"
    and qnz: "q \<noteq> base.poly_zero" and root: "ext.eval x q = zero"
    using alg by (rule algebraic_over_baseD)
  let ?d = "base.degree q"
  let ?B = "ext.rpow x ` {..< ?d}"
  have finB: "finite ?B" by simp
  have BL: "?B \<subseteq> L"
    using x by (auto intro: ext.rpow_closed)
  have Bsimple: "?B \<subseteq> simple_extension x"
  proof
    fix y assume "y \<in> ?B"
    then obtain i where i: "i < ?d" and y: "y = ext.rpow x i"
      by auto
    have m: "base.monom unit i \<in> base.poly_carrier"
      using base.multiplicative.unit_closed by (rule base.monom_closed)
    have meq: "base.monom unit i = ext.monom unit i"
      by (simp add: base.monom_def ext.monom_def)
    have ev: "ext.eval x (ext.monom unit i) =
      multiplication unit (ext.rpow x i)"
      by (rule ext.eval_monom [OF ext.multiplicative.unit_closed x])
    have one: "multiplication unit (ext.rpow x i) = ext.rpow x i"
      by (rule ext.multiplicative.left_unit [OF ext.rpow_closed [OF x]])
    have "ext.eval x (base.monom unit i) = y"
      using ev one meq y by metis
    then show "y \<in> simple_extension x"
      using m by (auto simp: simple_extension_def)
  qed
  have spanning: "simple_extension x \<subseteq> vs.span ?B"
  proof
    fix y assume "y \<in> simple_extension x"
    then obtain p where p: "p \<in> base.poly_carrier" and y: "y = ext.eval x p"
      by (auto simp: simple_extension_def)
    let ?r = "base.pmod p q"
    have rlow: "?r \<in> base.low_poly ?d"
      by (rule base.pmod_low_poly [OF p q qnz])
    have r: "?r \<in> base.poly_carrier"
      by (rule base.low_poly_closed [OF rlow])
    have rL: "?r \<in> ext.poly_carrier"
      using r base_poly_carrier_subset_ext by blast
    have deg: "ext.degree ?r \<le> ?d"
      by (rule ext.degree_leI [OF rL])
        (use rlow in \<open>auto intro: base.low_poly_coeff\<close>)
    have terms: "\<And>i. i \<le> ?d \<Longrightarrow>
      multiplication (?r i) (ext.rpow x i) \<in> vs.span ?B"
    proof -
      fix i assume i: "i \<le> ?d"
      show "multiplication (?r i) (ext.rpow x i) \<in> vs.span ?B"
      proof (cases "i < ?d")
        case True
        have pow: "ext.rpow x i \<in> vs.span ?B"
          using True vs.span_incl [OF BL] by blast
        show ?thesis
          by (rule vs.span_scale [OF BL base.poly_carrier_coeff_closed [OF r] pow])
      next
        case False
        have ri: "?r i = zero"
          by (rule base.low_poly_coeff [OF rlow]) (use i False in auto)
        show ?thesis
          using ext.rpow_closed [OF x, of i]
          by (simp add: ri)
      qed
    qed
    have "y = ext.eval x ?r"
      using y eval_pmod_at_root [OF x q qnz root p] by simp
    also have "\<dots> = ext.additive.fincomp
      (\<lambda>i. multiplication (?r i) (ext.rpow x i)) {..?d}"
      by (rule ext.eval_fincomp_le [OF rL x deg])
    also have "\<dots> \<in> vs.span ?B"
      by (rule additive_fincomp_in_span [OF _ BL]) (use terms in auto)
    finally show "y \<in> vs.span ?B" .
  qed
  show thesis using that [OF finB Bsimple spanning] .
qed

theorem simple_extension_has_basis:
  assumes alg: "algebraic_over_base x"
  obtains B where "finite B" "B \<subseteq> simple_extension x"
    "simple_extension x \<subseteq> vs.span B" "vs.lin_indep B"
proof -
  have x: "x \<in> L"
    using alg by (auto simp: algebraic_over_base_def)
  interpret S: vector_subspace K addition multiplication zero unit
    addition zero L multiplication "simple_extension x"
    by unfold_locales (rule simple_extension_submodule [OF x])
  obtain D where D: "finite D" "D \<subseteq> simple_extension x"
    "simple_extension x \<subseteq> vs.span D"
    by (rule simple_extension_finite_span [OF alg])
  have spmod: "S.sub.mod.spanning D"
  proof (rule S.sub.mod.spanningI [OF D(2)])
    fix v assume "v \<in> simple_extension x"
    then have "v \<in> vs.span D" using D(3) by blast
    then show "v \<in> S.sub.span D"
      using S.sub_span_eq [OF D(2)] by simp
  qed
  have sp: "S.sub.spanning D"
    using spmod S.sub.spanning_iff_mod_spanning [OF D(1,2)] by blast
  obtain B where BD: "B \<subseteq> D" and basis: "S.sub.basis B"
    using S.sub.basis_exists_from_spanning [OF sp] by blast
  have BS: "B \<subseteq> simple_extension x" using BD D(2) by blast
  have finB: "finite B"
    using basis by (simp add: S.sub.basis_def)
  have Bmod: "S.sub.mod.spanning B"
    using S.sub.basis_spanning [OF basis]
      S.sub.spanning_iff_mod_spanning [OF finB BS] by blast
  have spanning: "simple_extension x \<subseteq> vs.span B"
  proof
    fix v assume v: "v \<in> simple_extension x"
    have "v \<in> S.sub.span B"
      by (rule S.sub.mod.spanningD [OF Bmod v])
    then show "v \<in> vs.span B"
      using S.sub_span_eq [OF BS] by simp
  qed
  have indep: "vs.lin_indep B"
    using basis S.sub.basis_lin_indep S.sub_lin_indep_iff [OF BS] by blast
  show thesis by (rule that [OF finB BS spanning indep])
qed

lemma simple_extension_multiplication_linear:
  assumes x: "x \<in> L" and a: "a \<in> simple_extension x"
  shows "linear_map K addition multiplication zero unit
    (simple_extension x) addition zero multiplication
    (simple_extension x) addition zero multiplication
    (restrict (\<lambda>v. multiplication a v) (simple_extension x))"
proof -
  let ?S = "simple_extension x"
  let ?f = "restrict (\<lambda>v. multiplication a v) ?S"
  interpret S: vector_subspace K addition multiplication zero unit
    addition zero L multiplication ?S
    by unfold_locales (rule simple_extension_submodule [OF x])
  have fgraph: "?f \<in> ?S \<rightarrow>\<^sub>E ?S"
    using a simple_extension_mult [OF x] by (auto simp: PiE_def extensional_def)
  have hom: "module_homomorphism K addition multiplication zero unit
    ?S addition zero multiplication ?S addition zero multiplication ?f"
  proof (intro module_homomorphism.intro S.sub.mod.Module_axioms
      module_homomorphism_axioms.intro)
    show "Set_Theory.map ?f ?S ?S"
      by unfold_locales (rule fgraph)
    fix u v assume u: "u \<in> ?S" and v: "v \<in> ?S"
    have aL: "a \<in> L" using a simple_extension_subset [OF x] by blast
    have uL: "u \<in> L" and vL: "v \<in> L"
      using u v simple_extension_subset [OF x] by blast+
    show "?f (addition u v) = addition (?f u) (?f v)"
      using u v simple_extension_add [OF x u v]
        ext.distributive(1) [OF aL uL vL]
      by simp
  next
    fix c v assume c: "c \<in> K" and v: "v \<in> ?S"
    have aL: "a \<in> L" and cL: "c \<in> L" and vL: "v \<in> L"
      using a c v base_subset simple_extension_subset [OF x] by blast+
    have cv: "multiplication c v \<in> ?S"
      using c v simple_extension_contains_base [OF x]
      by (blast intro: simple_extension_mult [OF x])
    show "?f (multiplication c v) = multiplication c (?f v)"
      using ext.multiplicative.associative [OF aL cL vL]
        ext.multiplicative.associative [OF cL aL vL]
        ext.multiplicative.commutative [OF aL cL] cv v
      by simp
  qed
  show ?thesis
    by (rule linear_map.intro [OF S.sub.Vector_Space_axioms
      S.sub.Vector_Space_axioms hom])
qed

theorem simple_extension_inverse:
  assumes alg: "algebraic_over_base x"
    and a: "a \<in> simple_extension x" and anz: "a \<noteq> zero"
  shows "ext.multiplicative.inverse a \<in> simple_extension x"
proof -
  let ?S = "simple_extension x"
  let ?f = "restrict (\<lambda>v. multiplication a v) ?S"
  have x: "x \<in> L"
    using alg by (auto simp: algebraic_over_base_def)
  interpret S: vector_subspace K addition multiplication zero unit
    addition zero L multiplication ?S
    by unfold_locales (rule simple_extension_submodule [OF x])
  interpret M: linear_map K addition multiplication zero unit
    ?S addition zero multiplication ?S addition zero multiplication ?f
    by (rule simple_extension_multiplication_linear [OF x a])
  obtain B where B: "finite B" "B \<subseteq> ?S" "?S \<subseteq> vs.span B"
    "vs.lin_indep B"
    by (rule simple_extension_has_basis [OF alg])
  have spmod: "S.sub.mod.spanning B"
  proof (rule S.sub.mod.spanningI [OF B(2)])
    fix v assume "v \<in> ?S"
    then have "v \<in> vs.span B" using B(3) by blast
    then show "v \<in> S.sub.span B"
      using S.sub_span_eq [OF B(2)] by simp
  qed
  have sp: "S.sub.spanning B"
    using spmod S.sub.spanning_iff_mod_spanning [OF B(1,2)] by blast
  have ind: "S.sub.lin_indep B"
    using B(4) S.sub_lin_indep_iff [OF B(2)] by blast
  have basis: "S.sub.basis B"
    by (rule S.sub.basisI [OF sp ind])
  have aL: "a \<in> L"
    using a simple_extension_subset [OF x] by blast
  have ai: "ext.multiplicative.invertible a"
    by (rule ext.field_inverse [OF aL anz])
  have inj: "inj_on ?f ?S"
  proof (rule inj_onI)
    fix u v
    assume u: "u \<in> ?S" and v: "v \<in> ?S"
      and eq: "?f u = ?f v"
    have uL: "u \<in> L" and vL: "v \<in> L"
      using u v simple_extension_subset [OF x] by blast+
    have "multiplication a u = multiplication a v"
      using u v eq by simp
    then show "u = v"
      using ext.multiplicative.invertible_left_cancel [OF ai aL uL vL]
      by blast
  qed
  have surj: "?f ` ?S = ?S"
    using M.injective_iff_surjective [OF basis basis refl] inj by blast
  have unitS: "unit \<in> ?S"
    using simple_extension_contains_base [OF x] base.multiplicative.unit_closed by blast
  have unit_image: "unit \<in> ?f ` ?S"
    using surj unitS by metis
  obtain b where bS: "b \<in> ?S" and fb: "?f b = unit"
    using unit_image by (auto simp: image_iff)
  have bL: "b \<in> L"
    using bS simple_extension_subset [OF x] by blast
  have ab: "multiplication a b = unit"
    using bS fb by simp
  have ba: "multiplication b a = unit"
    using ab ext.multiplicative.commutative [OF aL bL] by simp
  have "ext.multiplicative.inverse a = b"
    by (rule ext.multiplicative.inverse_equality [OF ab ba aL bL])
  then show ?thesis using bS by simp
qed

theorem simple_extension_field:
  assumes alg: "algebraic_over_base x"
  shows "Field (simple_extension x) addition multiplication zero unit"
proof -
  let ?S = "simple_extension x"
  have x: "x \<in> L"
    using alg by (auto simp: algebraic_over_base_def)
  have SL: "?S \<subseteq> L"
    by (rule simple_extension_subset [OF x])
  interpret V: vector_subspace K addition multiplication zero unit
    addition zero L multiplication ?S
    by unfold_locales (rule simple_extension_submodule [OF x])
  have submon: "Submonoid ?S L multiplication unit"
  proof (intro Submonoid.intro ext.multiplicative.Monoid_axioms
      Submonoid_axioms.intro)
    show "?S \<subseteq> L" by (rule SL)
    show "\<And>a b. \<lbrakk>a \<in> ?S; b \<in> ?S\<rbrakk> \<Longrightarrow> multiplication a b \<in> ?S"
      by (rule simple_extension_mult [OF x])
    show "unit \<in> ?S"
      using simple_extension_contains_base [OF x] base.multiplicative.unit_closed
      by blast
  qed
  interpret M: Submonoid ?S L multiplication unit by (rule submon)
  have ring: "Ring ?S addition multiplication zero unit"
  proof (intro Ring.intro V.sub.vadd.Abelian_Group_axioms M.sub.Monoid_axioms
      Ring_axioms.intro)
    fix a b c
    assume a: "a \<in> ?S" and b: "b \<in> ?S" and c: "c \<in> ?S"
    have aL: "a \<in> L" and bL: "b \<in> L" and cL: "c \<in> L"
      using SL a b c by blast+
    show "multiplication a (addition b c) =
      addition (multiplication a b) (multiplication a c)"
      by (rule ext.distributive(1) [OF aL bL cL])
    show "multiplication (addition b c) a =
      addition (multiplication b a) (multiplication c a)"
      by (rule ext.distributive(2) [OF aL bL cL])
  qed
  have cmon: "commutative_monoid ?S multiplication unit"
  proof (intro commutative_monoid.intro M.sub.Monoid_axioms
      commutative_monoid_axioms.intro)
    fix a b assume a: "a \<in> ?S" and b: "b \<in> ?S"
    show "multiplication a b = multiplication b a"
      using SL a b by (blast intro: ext.multiplicative.commutative)
  qed
  have cring: "commutative_ring ?S addition multiplication zero unit"
    by (rule commutative_ring.intro [OF ring cmon])
  have nontrivial: "nontrivial_ring ?S addition multiplication zero unit"
    by (intro nontrivial_ring.intro [OF ring]
        nontrivial_ring_axioms.intro base.nontrivial)
  show ?thesis
  proof (intro Field.intro cring nontrivial Field_axioms.intro)
    fix a assume a: "a \<in> ?S" and anz: "a \<noteq> zero"
    have aL: "a \<in> L" using a SL by blast
    have ai: "ext.multiplicative.invertible a"
      by (rule ext.field_inverse [OF aL anz])
    have bS: "ext.multiplicative.inverse a \<in> ?S"
      by (rule simple_extension_inverse [OF alg a anz])
    show "M.sub.invertible a"
      by (rule M.sub.invertibleI [OF
          ext.multiplicative.invertible_right_inverse [OF ai aL]
          ext.multiplicative.invertible_left_inverse [OF ai aL] bS])
  qed
qed

lemma algebraic_of_bounded_relation:
  assumes x: "x \<in> L"
    and coeff: "\<And>i. i \<le> n \<Longrightarrow> c i \<in> K"
    and nz: "\<exists>i\<le>n. c i \<noteq> zero"
    and rel: "ext.additive.fincomp
      (\<lambda>i. multiplication (c i) (ext.rpow x i)) {..n} = zero"
  shows "algebraic_over_base x"
proof -
  define p where "p = (\<lambda>i. if i \<le> n then c i else zero)"
  have pc: "p \<in> base.poly_carrier"
  proof (rule base.poly_carrierI)
    have "{i. p i \<noteq> zero} \<subseteq> {..n}"
      by (auto simp: p_def)
    then show "finite {i. p i \<noteq> zero}"
      by (rule finite_subset) simp
    show "\<And>i. p i \<in> K"
      using coeff by (simp add: p_def)
  qed
  have pnz: "p \<noteq> base.poly_zero"
    using nz by (auto simp: p_def base.poly_zero_def fun_eq_iff)
  have deg: "ext.degree p \<le> n"
    by (rule base.degree_leI [OF pc]) (simp add: p_def)
  have pL: "p \<in> ext.poly_carrier"
    using pc base_poly_carrier_subset_ext by blast
  have terms: "(\<lambda>i. multiplication (c i) (ext.rpow x i)) \<in> {..n} \<rightarrow> L"
    using coeff x base_subset
    by (auto intro: ext.multiplicative.composition_closed ext.rpow_closed)
  have ev: "ext.eval x p =
    ext.additive.fincomp (\<lambda>i. multiplication (p i) (ext.rpow x i)) {..n}"
    by (rule ext.eval_fincomp_le [OF pL x deg])
  have "ext.eval x p =
    ext.additive.fincomp (\<lambda>i. multiplication (c i) (ext.rpow x i)) {..n}"
    unfolding ev
    by (rule ext.additive.fincomp_cong')
      (use terms in \<open>auto simp: p_def\<close>)
  then have "ext.eval x p = zero"
    using rel by simp
  then show ?thesis
    by (rule algebraic_over_baseI [OF x pc pnz])
qed

lemma base_elements_algebraic:
  assumes x: "x \<in> K"
  shows "algebraic_over_base x"
proof -
  have xL: "x \<in> L" using x base_subset by blast
  define c :: "nat \<Rightarrow> 'a"
    where "c = (\<lambda>i. if i = 0 then base.additive.inverse x else unit)"
  have cK: "\<And>i. i \<le> 1 \<Longrightarrow> c i \<in> K"
    using x by (simp add: c_def)
  have cnz: "\<exists>i\<le>1. c i \<noteq> zero"
    using base.nontrivial by (auto simp: c_def)
  have inv: "base.additive.inverse x = ext.additive.inverse x"
    by (rule additive_inverse_agrees [OF x])
  have rel: "ext.additive.fincomp
    (\<lambda>i. multiplication (c i) (ext.rpow x i)) {..1} = zero"
    using xL
    by (simp add: c_def inv ext.right_minus ext.additive.invertible_left_inverse)
  show ?thesis
    by (rule algebraic_of_bounded_relation [OF xL cK cnz rel])
qed

lemma finite_span_powers_dependent:
  assumes finite: "finite B" and BL: "B \<subseteq> L"
    and spanning: "L \<subseteq> vs.span B" and x: "x \<in> L"
  shows "\<not> inj_on (ext.rpow x) {..card B} \<or>
    \<not> vs.lin_indep ((ext.rpow x) ` {..card B})"
proof (cases "inj_on (ext.rpow x) {..card B}")
  case False
  then show ?thesis by simp
next
  case True
  let ?P = "(ext.rpow x) ` {..card B}"
  have PL: "?P \<subseteq> L"
    using x by (auto intro: ext.rpow_closed)
  have Pspan: "?P \<subseteq> vs.span B"
    using PL spanning by blast
  have cardP: "card ?P = card B + 1"
    using True by (simp add: card_image)
  have "\<not> vs.lin_indep ?P"
    using vs.independent_le_span [OF _ finite BL Pspan] cardP by force
  then show ?thesis by simp
qed

lemma repeated_powers_algebraic:
  assumes x: "x \<in> L" and i: "i \<le> n" and j: "j \<le> n"
    and ij: "i \<noteq> j" and eq: "ext.rpow x i = ext.rpow x j"
  shows "algebraic_over_base x"
proof -
  define c where "c = (\<lambda>k. if k = i then unit
    else if k = j then base.additive.inverse unit else zero)"
  have neg1: "base.additive.inverse unit \<in> K"
    by simp
  have coeff: "\<And>k. k \<le> n \<Longrightarrow> c k \<in> K"
    using neg1 by (auto simp: c_def)
  have nz: "\<exists>k\<le>n. c k \<noteq> zero"
    using i base.nontrivial by (auto simp: c_def)
  let ?f = "\<lambda>k. multiplication (c k) (ext.rpow x k)"
  have fL: "?f \<in> {..n} \<rightarrow> L"
    using coeff x base_subset
    by (auto intro: ext.multiplicative.composition_closed ext.rpow_closed)
  have rest: "ext.additive.fincomp ?f ({..n} - {i,j}) = zero"
  proof (rule ext.additive.fincomp_unit_eqI)
    fix k assume "k \<in> {..n} - {i,j}"
    then have "c k = zero" by (simp add: c_def)
    then show "?f k = zero"
      using x by (simp add: ext.left_zero)
  qed
  have fi: "?f i = ext.rpow x i"
    using x by (simp add: c_def ext.multiplicative.left_unit ext.rpow_closed)
  have fj: "?f j = ext.additive.inverse (ext.rpow x j)"
    using x ij additive_inverse_agrees [OF base.multiplicative.unit_closed]
    by (simp add: c_def ext.left_minus ext.rpow_closed)
  have decomp: "{..n} = insert i (insert j ({..n} - {i,j}))"
    using i j by auto
  let ?A = "{..n} - {i,j}"
  have fA: "?f \<in> ?A \<rightarrow> L" using fL by auto
  have fiL: "?f i \<in> L" and fjL: "?f j \<in> L"
    using fL i j by auto
  have fJA: "?f \<in> insert j ?A \<rightarrow> L"
    using fA fjL by auto
  have stepj: "ext.additive.fincomp ?f (insert j ?A) = ?f j"
    using ext.additive.fincomp_insert [OF _ _ fA fjL] rest
    by (simp add: fjL)
  have sum: "ext.additive.fincomp ?f {..n} = addition (?f i) (?f j)"
    apply (subst decomp)
    using ext.additive.fincomp_insert [OF _ _ fJA fiL] stepj ij
    by simp
  have relation: "ext.additive.fincomp ?f {..n} = zero"
    using sum fi fj eq x
    by (simp add: ext.additive.invertible_right_inverse ext.rpow_closed)
  show ?thesis
    by (rule algebraic_of_bounded_relation [OF x coeff nz relation])
qed

lemma dependent_distinct_powers_algebraic:
  assumes x: "x \<in> L" and inj: "inj_on (ext.rpow x) {..n}"
    and dep: "\<not> vs.lin_indep ((ext.rpow x) ` {..n})"
  shows "algebraic_over_base x"
proof -
  let ?P = "(ext.rpow x) ` {..n}"
  have finP: "finite ?P" by simp
  have PL: "?P \<subseteq> L" using x by (auto intro: ext.rpow_closed)
  obtain c where cPiE: "c \<in> ?P \<rightarrow>\<^sub>E K"
    and lc0: "vs.lincomb c ?P = zero"
    and nz: "\<not> (\<forall>v\<in>?P. c v = zero)"
    using dep finP PL by (auto simp: vs.lin_indep_def)
  have cK: "\<And>v. v \<in> ?P \<Longrightarrow> c v \<in> K"
    using cPiE by auto
  have termsL: "(\<lambda>v. multiplication (c v) v) \<in> ?P \<rightarrow> L"
    using cK PL base_subset by (auto intro: ext.multiplicative.composition_closed)
  have sum0: "ext.additive.fincomp (\<lambda>v. multiplication (c v) v) ?P = zero"
    using lc0 by (simp add: vs.lincomb_def)
  define d where "d = (\<lambda>i. c (ext.rpow x i))"
  have dK: "\<And>i. i \<le> n \<Longrightarrow> d i \<in> K"
    using cK by (auto simp: d_def)
  have dnz: "\<exists>i\<le>n. d i \<noteq> zero"
    using nz by (auto simp: d_def)
  have rel: "ext.additive.fincomp
    (\<lambda>i. multiplication (d i) (ext.rpow x i)) {..n} = zero"
    using sum0 ext.additive.fincomp_reindex [OF termsL inj]
    by (simp add: d_def)
  show ?thesis
    by (rule algebraic_of_bounded_relation [OF x dK dnz rel])
qed

theorem finite_spanning_implies_algebraic:
  assumes finite: "finite B" and BL: "B \<subseteq> L"
    and spanning: "L \<subseteq> vs.span B" and x: "x \<in> L"
  shows "algebraic_over_base x"
proof -
  let ?n = "card B"
  have dep: "\<not> inj_on (ext.rpow x) {..?n} \<or>
    \<not> vs.lin_indep ((ext.rpow x) ` {..?n})"
    by (rule finite_span_powers_dependent [OF finite BL spanning x])
  show ?thesis
  proof (cases "inj_on (ext.rpow x) {..?n}")
    case False
    then obtain i j where i: "i \<le> ?n" and j: "j \<le> ?n"
      and ij: "i \<noteq> j" and eq: "ext.rpow x i = ext.rpow x j"
      by (auto simp: inj_on_def)
    show ?thesis
      by (rule repeated_powers_algebraic [OF x i j ij eq])
  next
    case True
    then show ?thesis
      using dep by (intro dependent_distinct_powers_algebraic [OF x True]) blast
  qed
qed

end

section \<open>Chains of Carrier-Set Field Extensions\<close>

locale field_tower_chain_locale =
  KE: field_tower_locale K E addition multiplication zero unit +
  EL: field_tower_locale E L addition multiplication zero unit
  for K E L :: "'a set"
    and addition multiplication :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and zero unit :: 'a
begin

lemma KL_field_tower:
  "field_tower_locale K L addition multiplication zero unit"
  by (rule field_tower_locale.intro [OF KE.base.Field_axioms EL.ext.Field_axioms])
    (unfold_locales; use KE.base_subset EL.base_subset in blast)

sublocale KL: field_tower_locale K L addition multiplication zero unit
  by (rule KL_field_tower)

lemma algebraic_over_base_mono:
  assumes "KL.algebraic_over_base x"
  shows "EL.algebraic_over_base x"
proof -
  obtain p where xL: "x \<in> L" and p: "p \<in> KE.base.poly_carrier"
    and pnz: "p \<noteq> KE.base.poly_zero" and ev: "EL.ext.eval x p = zero"
    using assms by (rule KL.algebraic_over_baseD)
  have pE: "p \<in> KE.ext.poly_carrier"
    using p KE.base_poly_carrier_subset_ext by blast
  show ?thesis
    by (rule EL.algebraic_over_baseI [OF xL pE pnz ev])
qed

lemma algebraic_over_ambient_mono:
  assumes "KE.algebraic_over_base x"
  shows "KL.algebraic_over_base x"
proof -
  obtain p where xE: "x \<in> E" and p: "p \<in> KE.base.poly_carrier"
    and pnz: "p \<noteq> KE.base.poly_zero"
    and ev: "KE.ext.eval x p = zero"
    using assms by (rule KE.algebraic_over_baseD)
  have xL: "x \<in> L" using xE EL.base_subset by blast
  have pE: "p \<in> KE.ext.poly_carrier"
    using p KE.base_poly_carrier_subset_ext by blast
  have evL: "EL.ext.eval x p = zero"
    using ev EL.eval_agrees_on_base [OF xE pE] by simp
  show ?thesis
    by (rule KL.algebraic_over_baseI [OF xL p pnz evL])
qed

lemma middle_span_eq:
  assumes BE: "B \<subseteq> E"
  shows "KE.vs.span B = KL.vs.span B"
proof -
  have Esub: "KL.vs.mod.submodule E"
  proof (rule KL.vs.mod.submoduleI)
    show "E \<subseteq> L" by (rule EL.base_subset)
    show "zero \<in> E" by simp
    fix a b assume "a \<in> E" "b \<in> E"
    then show "addition a b \<in> E"
      by (rule KE.ext.additive.composition_closed)
  next
    fix a v assume "a \<in> K" "v \<in> E"
    then show "multiplication a v \<in> E"
      by (rule KE.vs.scale_closed)
  qed
  interpret S: vector_subspace K addition multiplication zero unit
    addition zero L multiplication E
    by unfold_locales (rule Esub)
  show ?thesis using S.sub_span_eq [OF BE] by simp
qed

lemma right_multiply_span:
  assumes BE: "B \<subseteq> E" and cL: "c \<in> L"
    and eSpan: "e \<in> KE.vs.span B"
  shows "multiplication e c \<in>
    KL.vs.span ((\<lambda>b. multiplication b c) ` B)"
proof -
  let ?D = "(\<lambda>b. multiplication b c) ` B"
  have DL: "?D \<subseteq> L"
    using BE cL KE.base_subset EL.base_subset
    by (auto intro: EL.ext.multiplicative.composition_closed)
  obtain d A where finA: "finite A" and AB: "A \<subseteq> B"
    and dA: "KE.vs.mod.coeffs_on d A"
    and e: "e = KE.vs.lincomb d A"
    using eSpan by (rule KE.vs.mod.spanE)
  have AE: "A \<subseteq> E" using AB BE by blast
  have dK: "\<And>b. b \<in> A \<Longrightarrow> d b \<in> K"
    using dA by (auto simp: KE.vs.mod.coeffs_on_def)
  have termsE: "(\<lambda>b. multiplication (d b) b) \<in> A \<rightarrow> E"
    using dK AE KE.base_subset
    by (auto intro: KE.ext.multiplicative.composition_closed)
  have termsL: "(\<lambda>b. multiplication (d b) b) \<in> A \<rightarrow> L"
    using termsE EL.base_subset by auto
  have eSum: "e = KE.ext.additive.fincomp
    (\<lambda>b. multiplication (d b) b) A"
    using e by (simp add: KE.vs.lincomb_def)
  have eSumL: "e = EL.ext.additive.fincomp
    (\<lambda>b. multiplication (d b) b) A"
    using eSum EL.additive_fincomp_agrees [OF finA termsE] by simp
  have eq: "multiplication e c =
    EL.ext.additive.fincomp
      (\<lambda>b. multiplication (d b) (multiplication b c)) A"
  proof -
    have "multiplication e c =
      multiplication (EL.ext.additive.fincomp
        (\<lambda>b. multiplication (d b) b) A) c"
      using eSumL by simp
    also have "\<dots> =
      EL.ext.additive.fincomp
        (\<lambda>b. multiplication (multiplication (d b) b) c) A"
      by (rule EL.ext.fincomp_mult_distrib_right [OF cL termsL])
    also have "\<dots> =
      EL.ext.additive.fincomp
        (\<lambda>b. multiplication (d b) (multiplication b c)) A"
    proof (rule EL.ext.additive.fincomp_cong')
      show "A = A" ..
      show "(\<lambda>b. multiplication (d b) (multiplication b c)) \<in> A \<rightarrow> L"
      proof
        fix b assume bA: "b \<in> A"
        have dbL: "d b \<in> L" using dK [OF bA] KE.base_subset EL.base_subset by blast
        have bL: "b \<in> L" using bA AE EL.base_subset by blast
        have bcL: "multiplication b c \<in> L"
          by (rule EL.ext.multiplicative.composition_closed [OF bL cL])
        show "multiplication (d b) (multiplication b c) \<in> L"
          by (rule EL.ext.multiplicative.composition_closed [OF dbL bcL])
      qed
      fix b assume bA: "b \<in> A"
      have dbL: "d b \<in> L" using dK [OF bA] KE.base_subset EL.base_subset by blast
      have bL: "b \<in> L" using bA AE EL.base_subset by blast
      show "multiplication (multiplication (d b) b) c =
        multiplication (d b) (multiplication b c)"
        by (rule EL.ext.multiplicative.associative [OF dbL bL cL])
    qed
    finally show ?thesis .
  qed
  have term_span: "multiplication (d b) (multiplication b c) \<in> KL.vs.span ?D"
    if "b \<in> A" for b
  proof -
    have bD: "multiplication b c \<in> ?D" using that AB by blast
    have "multiplication b c \<in> KL.vs.span ?D"
      by (rule KL.vs.span_incl [OF DL bD])
    then show ?thesis
      by (rule KL.vs.span_scale [OF DL dK [OF that]])
  qed
  show ?thesis
    using eq KL.additive_fincomp_in_span [OF finA DL term_span] by simp
qed

theorem finite_spanning_tower:
  assumes finB: "finite B" and BE: "B \<subseteq> E"
    and ESpan: "E \<subseteq> KE.vs.span B"
    and finC: "finite C" and CL: "C \<subseteq> L"
    and LSpan: "L \<subseteq> EL.vs.span C"
  shows "\<exists>D. finite D \<and> D \<subseteq> L \<and> L \<subseteq> KL.vs.span D"
proof -
  define D where "D = (\<lambda>(b,c). multiplication b c) ` (B \<times> C)"
  have finD: "finite D" using finB finC by (simp add: D_def)
  have DL: "D \<subseteq> L"
    using BE CL EL.base_subset
    by (auto simp: D_def intro: EL.ext.multiplicative.composition_closed)
  have spanD: "L \<subseteq> KL.vs.span D"
  proof
    fix x assume xL: "x \<in> L"
    have xSpan: "x \<in> EL.vs.span C" using xL LSpan by blast
    obtain d A where finA: "finite A" and AC: "A \<subseteq> C"
      and dA: "EL.vs.mod.coeffs_on d A"
      and x: "x = EL.vs.lincomb d A"
      using xSpan by (rule EL.vs.mod.spanE)
    have dE: "\<And>c. c \<in> A \<Longrightarrow> d c \<in> E"
      using dA by (auto simp: EL.vs.mod.coeffs_on_def)
    have xSum: "x = EL.ext.additive.fincomp
      (\<lambda>c. multiplication (d c) c) A"
      using x by (simp add: EL.vs.lincomb_def)
    have summand: "multiplication (d c) c \<in> KL.vs.span D"
      if cA: "c \<in> A" for c
    proof -
      have cL: "c \<in> L" using cA AC CL by blast
      have dSpan: "d c \<in> KE.vs.span B" using dE [OF cA] ESpan by blast
      have small: "multiplication (d c) c \<in>
        KL.vs.span ((\<lambda>b. multiplication b c) ` B)"
        by (rule right_multiply_span [OF BE cL dSpan])
      have sub: "(\<lambda>b. multiplication b c) ` B \<subseteq> D"
        using cA AC by (auto simp: D_def)
      show ?thesis using small KL.vs.span_mono [OF sub] by blast
    qed
    have "EL.ext.additive.fincomp
      (\<lambda>c. multiplication (d c) c) A \<in> KL.vs.span D"
      by (rule KL.additive_fincomp_in_span [OF finA DL summand])
    then show "x \<in> KL.vs.span D" using xSum by simp
  qed
  show ?thesis using finD DL spanD by blast
qed

end

context field_tower_locale
begin

theorem finite_algebraic_set_in_finite_extension:
  assumes fin: "finite A"
    and alg: "\<forall>x\<in>A. algebraic_over_base x"
  shows "\<exists>E B. Field E addition multiplication zero unit \<and>
    K \<subseteq> E \<and> E \<subseteq> L \<and> A \<subseteq> E \<and>
    finite B \<and> B \<subseteq> E \<and> E \<subseteq> vs.span B"
  using fin alg
proof (induction A rule: finite_induct)
  case empty
  have uL: "unit \<in> L"
    using base.multiplicative.unit_closed base_subset by blast
  have BL: "{unit} \<subseteq> L" using uL by blast
  have uspan: "unit \<in> vs.span {unit}"
    using vs.span_incl [OF BL] by blast
  have Kspan: "K \<subseteq> vs.span {unit}"
  proof
    fix y assume yK: "y \<in> K"
    have yL: "y \<in> L" using yK base_subset by blast
    have "multiplication y unit \<in> vs.span {unit}"
      by (rule vs.span_scale [OF BL yK uspan])
    then show "y \<in> vs.span {unit}"
      using ext.multiplicative.right_unit [OF yL] by simp
  qed
  show ?case
    by (rule exI [where x=K], rule exI [where x="{unit}"])
      (use base.Field_axioms base.multiplicative.unit_closed Kspan base_subset in auto)
next
  case (insert a F)
  have algF: "\<forall>x\<in>F. algebraic_over_base x"
    using insert.prems by simp
  have alga: "algebraic_over_base a"
    using insert.prems by simp
  have aL: "a \<in> L"
    using alga by (auto simp: algebraic_over_base_def)
  obtain E B where FE: "Field E addition multiplication zero unit"
    and KEsub: "K \<subseteq> E" and ELsub: "E \<subseteq> L"
    and Fsub: "F \<subseteq> E" and finB: "finite B" and BE: "B \<subseteq> E"
    and ESpan: "E \<subseteq> vs.span B"
    using insert.IH [OF algF] by blast
  have KE: "field_tower_locale K E addition multiplication zero unit"
    by (rule field_tower_locale.intro [OF base.Field_axioms FE])
      (unfold_locales; use KEsub in blast)
  have EL: "field_tower_locale E L addition multiplication zero unit"
    by (rule field_tower_locale.intro [OF FE ext.Field_axioms])
      (unfold_locales; use ELsub in blast)
  interpret C: field_tower_chain_locale K E L
    addition multiplication zero unit
    by (rule field_tower_chain_locale.intro [OF KE EL])
  have algE: "C.EL.algebraic_over_base a"
    by (rule C.algebraic_over_base_mono [OF alga])
  let ?S = "C.EL.simple_extension a"
  have FS: "Field ?S addition multiplication zero unit"
    by (rule C.EL.simple_extension_field [OF algE])
  have ESsub: "E \<subseteq> ?S"
    by (rule C.EL.simple_extension_contains_base [OF aL])
  have SLsub: "?S \<subseteq> L"
    by (rule C.EL.simple_extension_subset [OF aL])
  have aS: "a \<in> ?S"
    by (rule C.EL.simple_extension_contains_generator [OF aL])
  obtain Cset where finC: "finite Cset" and CS: "Cset \<subseteq> ?S"
    and SSpanL: "?S \<subseteq> C.EL.vs.span Cset"
    by (rule C.EL.simple_extension_finite_span [OF algE])
  interpret V: vector_subspace E addition multiplication zero unit
    addition zero L multiplication ?S
    by unfold_locales (rule C.EL.simple_extension_submodule [OF aL])
  have ES: "field_tower_locale E ?S addition multiplication zero unit"
    by (rule field_tower_locale.intro [OF FE FS])
      (unfold_locales; use ESsub in blast)
  interpret D: field_tower_chain_locale K E ?S
    addition multiplication zero unit
    by (rule field_tower_chain_locale.intro [OF KE ES])
  have SSpan: "?S \<subseteq> Module.span E addition zero ?S multiplication Cset"
    using SSpanL V.sub_span_eq [OF CS] by simp
  have ESpan': "E \<subseteq> Module.span K addition zero E multiplication B"
    using ESpan C.middle_span_eq [OF BE] by simp
  obtain H where finH: "finite H" and HS: "H \<subseteq> ?S"
    and HSpan: "?S \<subseteq> Module.span K addition zero ?S multiplication H"
    using D.finite_spanning_tower [OF finB BE ESpan' finC CS SSpan]
    by blast
  have SL: "field_tower_locale ?S L addition multiplication zero unit"
    by (rule field_tower_locale.intro [OF FS ext.Field_axioms])
      (unfold_locales; use SLsub in blast)
  interpret T: field_tower_chain_locale K ?S L
    addition multiplication zero unit
    by (rule field_tower_chain_locale.intro [OF D.KL_field_tower SL])
  have finalSpan: "?S \<subseteq> vs.span H"
    using HSpan T.middle_span_eq [OF HS] by simp
  have KS: "K \<subseteq> ?S" using KEsub ESsub by blast
  have AS: "insert a F \<subseteq> ?S"
    using aS Fsub ESsub by blast
  show ?case
    by (rule exI [where x="?S"], rule exI [where x=H])
      (use FS KS SLsub AS finH HS finalSpan in auto)
qed

lemma finite_intermediate_elements_algebraic:
  assumes FE: "Field E addition multiplication zero unit"
    and KEsub: "K \<subseteq> E" and ELsub: "E \<subseteq> L"
    and finB: "finite B" and BE: "B \<subseteq> E"
    and ESpan: "E \<subseteq> vs.span B" and xE: "x \<in> E"
  shows "algebraic_over_base x"
proof -
  have KE: "field_tower_locale K E addition multiplication zero unit"
    by (rule field_tower_locale.intro [OF base.Field_axioms FE])
      (unfold_locales; use KEsub in blast)
  have EL: "field_tower_locale E L addition multiplication zero unit"
    by (rule field_tower_locale.intro [OF FE ext.Field_axioms])
      (unfold_locales; use ELsub in blast)
  interpret C: field_tower_chain_locale K E L
    addition multiplication zero unit
    by (rule field_tower_chain_locale.intro [OF KE EL])
  have ESpan': "E \<subseteq> Module.span K addition zero E multiplication B"
    using ESpan C.middle_span_eq [OF BE] by simp
  have algE: "C.KE.algebraic_over_base x"
    by (rule C.KE.finite_spanning_implies_algebraic
        [OF finB BE ESpan' xE])
  show ?thesis
    by (rule C.algebraic_over_ambient_mono [OF algE])
qed

theorem finite_algebraic_set_field_hull:
  assumes fin: "finite A"
    and alg: "\<forall>x\<in>A. algebraic_over_base x"
  shows "\<exists>E. Field E addition multiplication zero unit \<and>
    E \<subseteq> L \<and> A \<subseteq> E \<and>
    (\<forall>x\<in>E. algebraic_over_base x)"
proof -
  obtain E B where FE: "Field E addition multiplication zero unit"
    and KEsub: "K \<subseteq> E" and ELsub: "E \<subseteq> L"
    and AE: "A \<subseteq> E" and finB: "finite B" and BE: "B \<subseteq> E"
    and ESpan: "E \<subseteq> vs.span B"
    using finite_algebraic_set_in_finite_extension [OF fin alg] by blast
  have all: "\<forall>x\<in>E. algebraic_over_base x"
    using finite_intermediate_elements_algebraic
      [OF FE KEsub ELsub finB BE ESpan] by blast
  show ?thesis
    by (rule exI [where x=E]) (use FE ELsub AE all in auto)
qed

definition algebraic_carrier :: "'a set"
  where "algebraic_carrier = {x. algebraic_over_base x}"

lemma algebraic_carrier_subset:
  "algebraic_carrier \<subseteq> L"
  by (auto simp: algebraic_carrier_def algebraic_over_base_def)

lemma base_subset_algebraic_carrier:
  "K \<subseteq> algebraic_carrier"
  using base_elements_algebraic by (auto simp: algebraic_carrier_def)

lemma algebraic_carrier_add:
  assumes a: "a \<in> algebraic_carrier"
    and b: "b \<in> algebraic_carrier"
  shows "addition a b \<in> algebraic_carrier"
proof -
  obtain E where FE: "Field E addition multiplication zero unit"
    and AE: "{a,b} \<subseteq> E"
    and all: "\<forall>x\<in>E. algebraic_over_base x"
    using finite_algebraic_set_field_hull [of "{a,b}"] a b
    by (auto simp: algebraic_carrier_def)
  interpret E: Field E addition multiplication zero unit by (rule FE)
  have "addition a b \<in> E"
    using AE by (blast intro: E.additive.composition_closed)
  then show ?thesis using all by (simp add: algebraic_carrier_def)
qed

lemma algebraic_carrier_mult:
  assumes a: "a \<in> algebraic_carrier"
    and b: "b \<in> algebraic_carrier"
  shows "multiplication a b \<in> algebraic_carrier"
proof -
  obtain E where FE: "Field E addition multiplication zero unit"
    and AE: "{a,b} \<subseteq> E"
    and all: "\<forall>x\<in>E. algebraic_over_base x"
    using finite_algebraic_set_field_hull [of "{a,b}"] a b
    by (auto simp: algebraic_carrier_def)
  interpret E: Field E addition multiplication zero unit by (rule FE)
  have "multiplication a b \<in> E"
    using AE by (blast intro: E.multiplicative.composition_closed)
  then show ?thesis using all by (simp add: algebraic_carrier_def)
qed

lemma algebraic_carrier_neg:
  assumes a: "a \<in> algebraic_carrier"
  shows "ext.additive.inverse a \<in> algebraic_carrier"
proof -
  obtain E where FE: "Field E addition multiplication zero unit"
    and EL: "E \<subseteq> L" and aE: "a \<in> E"
    and all: "\<forall>x\<in>E. algebraic_over_base x"
    using finite_algebraic_set_field_hull [of "{a}"] a
    by (auto simp: algebraic_carrier_def)
  interpret E: Field E addition multiplication zero unit by (rule FE)
  have inv_eq: "ext.additive.inverse a = E.additive.inverse a"
  proof -
    have S: "Subgroup E L addition zero"
      by unfold_locales
        (use EL in
          \<open>blast intro: E.additive.composition_closed E.additive.unit_closed\<close>)+
    interpret S: Subgroup E L addition zero by (rule S)
    show ?thesis using S.subgroup_inverse_equality [OF aE] by simp
  qed
  have "E.additive.inverse a \<in> E"
    using aE by simp
  then show ?thesis using all by (simp add: algebraic_carrier_def inv_eq)
qed

lemma algebraic_carrier_inverse:
  assumes a: "a \<in> algebraic_carrier" and anz: "a \<noteq> zero"
  shows "ext.multiplicative.inverse a \<in> algebraic_carrier"
proof -
  obtain E where FE: "Field E addition multiplication zero unit"
    and EL: "E \<subseteq> L" and aE: "a \<in> E"
    and all: "\<forall>x\<in>E. algebraic_over_base x"
    using finite_algebraic_set_field_hull [of "{a}"] a
    by (auto simp: algebraic_carrier_def)
  interpret E: Field E addition multiplication zero unit by (rule FE)
  have inv_eq: "ext.multiplicative.inverse a = E.multiplicative.inverse a"
  proof -
    have aiE: "E.multiplicative.invertible a"
      by (rule E.field_inverse [OF aE anz])
    have bE: "E.multiplicative.inverse a \<in> E"
      by (rule E.multiplicative.invertible_inverse_closed [OF aiE aE])
    have aL: "a \<in> L" and bL: "E.multiplicative.inverse a \<in> L"
      using EL aE bE by blast+
    show ?thesis
      by (rule ext.multiplicative.inverse_equality
        [OF E.multiplicative.invertible_right_inverse [OF aiE aE]
            E.multiplicative.invertible_left_inverse [OF aiE aE] aL bL])
  qed
  have "E.multiplicative.inverse a \<in> E"
    using E.field_inverse [OF aE anz] aE by simp
  then show ?thesis using all by (simp add: algebraic_carrier_def inv_eq)
qed

theorem algebraic_carrier_field:
  "Field algebraic_carrier addition multiplication zero unit"
proof -
  let ?S = algebraic_carrier
  have SL: "?S \<subseteq> L" by (rule algebraic_carrier_subset)
  have KS: "K \<subseteq> ?S" by (rule base_subset_algebraic_carrier)
  have submodule: "vs.mod.submodule ?S"
  proof (rule vs.mod.submoduleI)
    show "?S \<subseteq> L" by (rule SL)
    show "zero \<in> ?S" using KS base.additive.unit_closed by blast
    fix a b assume "a \<in> ?S" "b \<in> ?S"
    then show "addition a b \<in> ?S"
      by (rule algebraic_carrier_add)
  next
    fix a v assume a: "a \<in> K" and v: "v \<in> ?S"
    have "a \<in> ?S" using a KS by blast
    then show "multiplication a v \<in> ?S"
      by (rule algebraic_carrier_mult [OF _ v])
  qed
  interpret V: vector_subspace K addition multiplication zero unit
    addition zero L multiplication ?S
    by unfold_locales (rule submodule)
  have submon: "Submonoid ?S L multiplication unit"
  proof (intro Submonoid.intro ext.multiplicative.Monoid_axioms
      Submonoid_axioms.intro)
    show "?S \<subseteq> L" by (rule SL)
    show "\<And>a b. \<lbrakk>a \<in> ?S; b \<in> ?S\<rbrakk> \<Longrightarrow> multiplication a b \<in> ?S"
      by (rule algebraic_carrier_mult)
    show "unit \<in> ?S"
      using KS base.multiplicative.unit_closed by blast
  qed
  interpret M: Submonoid ?S L multiplication unit by (rule submon)
  have ring: "Ring ?S addition multiplication zero unit"
  proof (intro Ring.intro V.sub.vadd.Abelian_Group_axioms M.sub.Monoid_axioms
      Ring_axioms.intro)
    fix a b c
    assume a: "a \<in> ?S" and b: "b \<in> ?S" and c: "c \<in> ?S"
    have aL: "a \<in> L" and bL: "b \<in> L" and cL: "c \<in> L"
      using SL a b c by blast+
    show "multiplication a (addition b c) =
      addition (multiplication a b) (multiplication a c)"
      by (rule ext.distributive(1) [OF aL bL cL])
    show "multiplication (addition b c) a =
      addition (multiplication b a) (multiplication c a)"
      by (rule ext.distributive(2) [OF aL bL cL])
  qed
  have cmon: "commutative_monoid ?S multiplication unit"
  proof (intro commutative_monoid.intro M.sub.Monoid_axioms
      commutative_monoid_axioms.intro)
    fix a b assume a: "a \<in> ?S" and b: "b \<in> ?S"
    show "multiplication a b = multiplication b a"
      using SL a b by (blast intro: ext.multiplicative.commutative)
  qed
  have cring: "commutative_ring ?S addition multiplication zero unit"
    by (rule commutative_ring.intro [OF ring cmon])
  have nontrivial: "nontrivial_ring ?S addition multiplication zero unit"
    by (intro nontrivial_ring.intro [OF ring]
        nontrivial_ring_axioms.intro base.nontrivial)
  show ?thesis
  proof (intro Field.intro cring nontrivial Field_axioms.intro)
    fix a assume a: "a \<in> ?S" and anz: "a \<noteq> zero"
    have aL: "a \<in> L" using a SL by blast
    have ai: "ext.multiplicative.invertible a"
      by (rule ext.field_inverse [OF aL anz])
    have bS: "ext.multiplicative.inverse a \<in> ?S"
      by (rule algebraic_carrier_inverse [OF a anz])
    show "M.sub.invertible a"
      by (rule M.sub.invertibleI [OF
          ext.multiplicative.invertible_right_inverse [OF ai aL]
          ext.multiplicative.invertible_left_inverse [OF ai aL] bS])
  qed
qed

end

end
