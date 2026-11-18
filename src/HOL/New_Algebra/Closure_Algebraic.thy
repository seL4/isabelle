section \<open>Algebraic Closures of Carrier-Set and Type-Class Fields\<close>

theory Closure_Algebraic
  imports Closure_Extension Field_Tower_Locale Poly_Divisibility
    Poly_Typeclass Algebraic_Transitivity Extension_Properties
    Finite_Generated_Extension Linear_System
    "HOL-Computational_Algebra.Polynomial_Factorial"
    "HOL-Computational_Algebra.Field_as_Ring"
begin

text \<open>An algebraic closure in the sense of HOL-Algebra's
  \<open>algebraic_closure\<close> locale: an algebraic field extension in which
  every polynomial over the base field splits.\<close>
locale carrier_algebraic_closure = field_tower_locale K L
  addition multiplication zero unit
  for K L :: "'a set"
    and addition multiplication :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and zero unit :: 'a +
  assumes algebraic_extension:
    "\<And>x. x \<in> L \<Longrightarrow> algebraic_over_base x"
    and base_polynomials_split:
    "\<And>p. p \<in> base.poly_carrier \<Longrightarrow> ext.splits p"

locale carrier_algebraically_closed = Field L addition multiplication zero unit
  for L :: "'a set"
    and addition multiplication :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and zero unit :: 'a +
  assumes polynomials_split:
    "\<And>p. p \<in> poly_carrier \<Longrightarrow> splits p"

lemma (in Field) splits_if_roots:
  assumes roots: "\<And>p. \<lbrakk>p \<in> poly_carrier; 0 < degree p\<rbrakk>
      \<Longrightarrow> \<exists>x\<in>R. eval x p = zero"
    and p: "p \<in> poly_carrier"
  shows "splits p"
  using p
proof (induction "degree p" arbitrary: p rule: less_induct)
  case (less p)
  show ?case
  proof (cases "degree p = 0")
    case True
    then have "p = poly_const (p 0)"
      using degree_zero_imp_const [OF less.prems] by simp
    moreover have "p 0 \<in> R"
      by (rule poly_carrier_coeff_closed [OF less.prems])
    ultimately show ?thesis by (metis splits_const)
  next
    case False
    then have pos: "0 < degree p" by simp
    obtain x where x: "x \<in> R" and root: "eval x p = zero"
      using roots [OF less.prems pos] by blast
    obtain q where q: "q \<in> poly_carrier"
      and peq: "p = poly_mult (root_factor x) q"
      using factor_theorem [OF less.prems x] root by blast
    have rf: "root_factor x \<in> poly_carrier"
      by (rule root_factor_closed [OF x])
    have pnz: "p \<noteq> poly_zero"
    proof
      assume "p = poly_zero"
      then have "degree p = 0" by simp
      then show False using pos by simp
    qed
    have qnz: "q \<noteq> poly_zero"
      using peq pnz poly_mult_zero_right [OF rf] by blast
    have dq: "degree q < degree p"
      using peq degree_mult [OF rf q
        root_factor_nonzero [OF x] qnz] degree_root_factor [OF x] by simp
    have "splits q" by (rule less.hyps [OF dq q])
    then show ?thesis
      using peq splits_mult splits_root_factor [OF x] by blast
  qed
qed

context carrier_algebraic_closure
begin

theorem roots_over_carrier:
  assumes p: "p \<in> ext.poly_carrier" and pos: "0 < ext.degree p"
  obtains x where "x \<in> L" and "ext.eval x p = zero"
proof -
  let ?C = "p ` {..ext.degree p}"
  have finC: "finite ?C" by simp
  have CL: "?C \<subseteq> L"
    using p ext.poly_carrier_coeff_closed by blast
  have algC: "\<forall>x\<in>?C. algebraic_over_base x"
    using CL algebraic_extension by blast
  obtain E B where FE: "Field E addition multiplication zero unit"
    and KEsub: "K \<subseteq> E" and ELsub: "E \<subseteq> L"
    and CE: "?C \<subseteq> E"
    and finB: "finite B" and BE: "B \<subseteq> E"
    and ESpan: "E \<subseteq> vs.span B"
    using finite_algebraic_set_in_finite_extension [OF finC algC] by blast
  interpret F: Field E addition multiplication zero unit by (rule FE)
  interpret KE: field_tower_locale K E addition multiplication zero unit
    by (intro field_tower_locale.intro field_tower_locale_axioms.intro
        base.Field_axioms FE KEsub)
  interpret EL: field_tower_locale E L addition multiplication zero unit
    by (intro field_tower_locale.intro field_tower_locale_axioms.intro
        FE ext.Field_axioms ELsub)
  interpret Chain: field_tower_chain_locale K E L addition multiplication zero unit
    by (rule field_tower_chain_locale.intro [OF KE.field_tower_locale_axioms
      EL.field_tower_locale_axioms])
  have ESpanKE: "E \<subseteq> KE.vs.span B"
    using ESpan Chain.middle_span_eq [OF BE] by simp
  have pE: "p \<in> F.poly_carrier"
  proof (rule F.poly_carrierI)
    show "finite {i. p i \<noteq> zero}"
      by (rule ext.poly_carrier_finite [OF p])
    fix i
    show "p i \<in> E"
    proof (cases "i \<le> ext.degree p")
      case True
      then show ?thesis using CE by blast
    next
      case False
      have "p i = zero"
        by (rule ext.coeff_gt_degree [OF p]) (use False in simp)
      then show ?thesis by simp
    qed
  qed
  have degreeE: "F.degree p = ext.degree p"
    by (simp add: F.degree_def ext.degree_def)
  obtain Q where QK: "Q \<in> base.poly_carrier"
    and Qnz: "Q \<noteq> base.poly_zero"
    and modE: "F.pmod Q p = F.poly_zero"
    using KE.finite_spanning_polynomial_multiple
      [OF finB BE ESpanKE pE] pos degreeE by auto
  have QE: "Q \<in> F.poly_carrier"
    using KE.base_poly_carrier_subset_ext QK by blast
  have pEnz: "p \<noteq> F.poly_zero"
    using pos degreeE by auto
  have dvdE: "F.poly_dvd p Q"
    using F.poly_dvd_iff_pmod_zero [OF pE pEnz QE] modE by blast
  obtain q where qE: "q \<in> F.poly_carrier"
    and Qeq: "Q = F.poly_mult q p"
    using dvdE unfolding F.poly_dvd_def by blast
  have qL: "q \<in> ext.poly_carrier"
    using EL.base_poly_carrier_subset_ext qE by blast
  have QeqL: "Q = ext.poly_mult q p"
    using Qeq EL.poly_mult_agrees [OF qE pE] by simp
  have dvdL: "ext.poly_dvd p Q"
    using qL QeqL unfolding ext.poly_dvd_def by blast
  have QL: "Q \<in> ext.poly_carrier"
    using base_poly_carrier_subset_ext QK by blast
  have QLn: "Q \<noteq> ext.poly_zero"
    using Qnz by (simp add: base.poly_zero_def ext.poly_zero_def)
  have split: "ext.splits Q"
    by (rule base_polynomials_split [OF QK])
  obtain x where x: "x \<in> L" and root: "ext.eval x p = zero"
    using ext.split_multiple_has_root [OF p pos QL QLn split dvdL] by blast
  show thesis by (rule that [OF x root])
qed

end

sublocale carrier_algebraic_closure \<subseteq>
  carrier_algebraically_closed L addition multiplication zero unit
proof (intro carrier_algebraically_closed.intro ext.Field_axioms
    carrier_algebraically_closed_axioms.intro)
  fix p assume p: "p \<in> ext.poly_carrier"
  show "ext.splits p"
  proof (rule ext.splits_if_roots [OF _ p])
    fix q assume q: "q \<in> ext.poly_carrier" and pos: "0 < ext.degree q"
    obtain x where "x \<in> L" "ext.eval x q = zero"
      by (rule roots_over_carrier [OF q pos])
    then show "\<exists>x\<in>L. ext.eval x q = zero" by blast
  qed
qed

subsection \<open>Algebraic elements of a splitting extension\<close>

text \<open>For a locale field, algebraicity is expressed directly in the fixed splitting extension:
  a nonzero polynomial over the base field annihilates the element after its coefficients are
  embedded as indexed-polynomial constants.  This formulation uses only carrier-set fields.\<close>

context Field
begin

lemma splits_pos_degree_has_root:
  assumes sp: "splits p" and deg: "0 < degree p"
  obtains x where "x \<in> R" and "eval x p = \<zero>"
proof -
  obtain c as where c: "c \<in> R" and as: "set as \<subseteq> R"
    and peq: "p = poly_const c \<otimes>\<^sub>P poly_prod (List.map root_factor as)"
    using sp by (rule splitsE)
  have ne: "as \<noteq> []"
  proof
    assume "as = []"
    then have "p = poly_const c"
      using peq c by (simp add: poly_mult_one_right poly_const_closed)
    then show False using deg degree_const_le by simp
  qed
  obtain x bs where xbs: "as = x # bs"
    using ne by (cases as) auto
  have x: "x \<in> R" and bs: "set bs \<subseteq> R"
    using as xbs by auto
  have pc: "poly_prod (List.map root_factor bs) \<in> poly_carrier"
    using bs by (intro poly_prod_closed) (auto intro: root_factor_closed)
  have pa: "poly_prod (List.map root_factor as) \<in> poly_carrier"
    using as by (intro poly_prod_closed) (auto intro: root_factor_closed)
  have ev: "eval x (poly_prod (List.map root_factor as)) = \<zero>"
    unfolding xbs
    using x pc by (simp add: eval_mult root_factor_closed)
  have "eval x p = \<zero>"
    unfolding peq
    using c x pa ev by (simp add: eval_mult poly_const_closed)
  then show thesis using that x by blast
qed

definition algebraic_in_split :: "'a ipoly set"
  where "algebraic_in_split =
    {x \<in> ecarrier splitting_extension.
       \<exists>P \<in> poly_carrier.
         P \<noteq> \<zero>\<^sub>P \<and> eeval splitting_extension x (lift_poly P) = \<zero>\<^sub>I}"

lemma algebraic_in_splitI:
  assumes "x \<in> ecarrier splitting_extension"
    and "P \<in> poly_carrier" and "P \<noteq> \<zero>\<^sub>P"
    and "eeval splitting_extension x (lift_poly P) = \<zero>\<^sub>I"
  shows "x \<in> algebraic_in_split"
  using assms unfolding algebraic_in_split_def by blast

lemma algebraic_in_splitD:
  assumes "x \<in> algebraic_in_split"
  obtains P where "x \<in> ecarrier splitting_extension"
    and "P \<in> poly_carrier" and "P \<noteq> \<zero>\<^sub>P"
    and "eeval splitting_extension x (lift_poly P) = \<zero>\<^sub>I"
  using assms unfolding algebraic_in_split_def by blast

lemma algebraic_in_split_subset:
  "algebraic_in_split \<subseteq> ecarrier splitting_extension"
  by (auto simp: algebraic_in_split_def)

lemma base_mem_splitting_extension:
  assumes "a \<in> R"
  shows "ipoly_const a \<in> ecarrier splitting_extension"
  using assms splitting_extension_spec is_extension_const_mem by blast

lemma base_image_field:
  "Field (ipoly_const ` R) (eadd splitting_extension) (emult splitting_extension)
    \<zero>\<^sub>I \<one>\<^sub>I"
proof -
  have ext: "is_extension splitting_extension"
    using splitting_extension_spec by blast
  have "Field (ipoly_const ` R) (eadd splitting_extension) (emult splitting_extension)
    (ipoly_const \<zero>) (ipoly_const \<one>)"
    apply (rule field_image_transport [OF ipoly_const_inj_on])
    by (auto simp: is_extension_const_add [OF ext] is_extension_const_mult [OF ext])
  then show ?thesis by simp
qed

lemma splitting_field_tower:
  "field_tower_locale (ipoly_const ` R) (ecarrier splitting_extension)
    (eadd splitting_extension) (emult splitting_extension) \<zero>\<^sub>I \<one>\<^sub>I"
  by (intro field_tower_locale.intro field_tower_locale_axioms.intro
      base_image_field splitting_extension_field)
    (use base_mem_splitting_extension in blast)


theorem algebraic_in_split_field:
  "Field algebraic_in_split (eadd splitting_extension)
    (emult splitting_extension) \<zero>\<^sub>I \<one>\<^sub>I"
proof -
  interpret T: field_tower_locale "ipoly_const ` R"
    "ecarrier splitting_extension" "eadd splitting_extension"
    "emult splitting_extension" "\<zero>\<^sub>I" "\<one>\<^sub>I"
    by (rule splitting_field_tower)
  have zero_lift: "lift_poly \<zero>\<^sub>P = T.base.poly_zero"
    by (simp add: lift_poly_def poly_zero_def T.base.poly_zero_def)
  have nzlift: "lift_poly P \<noteq> T.base.poly_zero"
    if Pnz: "P \<noteq> \<zero>\<^sub>P" for P
  proof -
    obtain k where k: "P k \<noteq> \<zero>"
      using Pnz by (auto simp: poly_zero_def fun_eq_iff)
    then have "ipoly_const (P k) \<noteq> \<zero>\<^sub>I"
      by (metis ipoly_const_coeff ipoly_zero_def)
    then show ?thesis
      by (auto simp: lift_poly_def T.base.poly_zero_def fun_eq_iff)
  qed
  have lift_base: "lift_poly P \<in> T.base.poly_carrier"
    if P: "P \<in> poly_carrier" for P
  proof (rule T.base.poly_carrierI)
    have "{i. lift_poly P i \<noteq> \<zero>\<^sub>I} \<subseteq> {i. P i \<noteq> \<zero>}"
      by (auto simp: lift_poly_def ipoly_const_def ipoly_zero_def)
    then show "finite {i. lift_poly P i \<noteq> \<zero>\<^sub>I}"
      using poly_carrier_finite [OF P] by (rule finite_subset)
    show "\<And>i. lift_poly P i \<in> ipoly_const ` R"
      using P by (auto simp: lift_poly_def poly_carrier_coeff_closed)
  qed
  have unlift: "p \<in> T.base.poly_carrier \<Longrightarrow>
    \<exists>P\<in>poly_carrier. lift_poly P = p" for p
  proof -
    assume p: "p \<in> T.base.poly_carrier"
    define P where "P = (\<lambda>i. SOME z. z \<in> R \<and> ipoly_const z = p i)"
    have coeff: "P i \<in> R \<and> ipoly_const (P i) = p i" for i
    proof -
      have im: "p i \<in> ipoly_const ` R"
        by (rule T.base.poly_carrier_coeff_closed [OF p])
      obtain z where z: "z \<in> R" "p i = ipoly_const z"
        using im by (rule imageE)
      have "\<exists>z. z \<in> R \<and> ipoly_const z = p i"
        by (rule exI [of _ z]) (simp add: z)
      then show ?thesis unfolding P_def
        by (rule someI_ex)
    qed
    have zero_coeff: "p i = \<zero>\<^sub>I \<longleftrightarrow> P i = \<zero>" for i
    proof
      assume "p i = \<zero>\<^sub>I"
      then show "P i = \<zero>"
        using coeff [of i] by (metis ipoly_const_coeff ipoly_const_zero)
    next
      assume "P i = \<zero>"
      then show "p i = \<zero>\<^sub>I" using coeff [of i] by simp
    qed
    have supp: "{i. P i \<noteq> \<zero>} = {i. p i \<noteq> \<zero>\<^sub>I}"
      using zero_coeff by blast
    have Pc: "P \<in> poly_carrier"
    proof (rule poly_carrierI)
      show "finite {i. P i \<noteq> \<zero>}"
        using T.base.poly_carrier_finite [OF p] by (simp add: supp)
      show "\<And>i. P i \<in> R" using coeff by blast
    qed
    have "lift_poly P = p"
    proof (rule ext)
      fix i
      show "lift_poly P i = p i"
        using coeff [of i] by simp
    qed
    then show ?thesis using Pc by blast
  qed
  have eq: "algebraic_in_split = T.algebraic_carrier"
  proof
    show "algebraic_in_split \<subseteq> T.algebraic_carrier"
    proof
      fix x assume "x \<in> algebraic_in_split"
      then obtain P where x: "x \<in> ecarrier splitting_extension"
        and P: "P \<in> poly_carrier" and nz: "P \<noteq> \<zero>\<^sub>P"
        and ev: "eeval splitting_extension x (lift_poly P) = \<zero>\<^sub>I"
        by (rule algebraic_in_splitD)
      have "T.algebraic_over_base x"
        by (rule T.algebraic_over_baseI [OF x lift_base [OF P] nzlift [OF nz] ev])
      then show "x \<in> T.algebraic_carrier"
        by (simp add: T.algebraic_carrier_def)
    qed
    show "T.algebraic_carrier \<subseteq> algebraic_in_split"
    proof
      fix x assume "x \<in> T.algebraic_carrier"
      then have ax: "T.algebraic_over_base x"
        by (simp add: T.algebraic_carrier_def)
      obtain p where x: "x \<in> ecarrier splitting_extension"
        and p: "p \<in> T.base.poly_carrier"
        and nz: "p \<noteq> T.base.poly_zero"
        and ev: "eeval splitting_extension x p = \<zero>\<^sub>I"
        using ax by (rule T.algebraic_over_baseD)
      obtain P where P: "P \<in> poly_carrier" and lift: "lift_poly P = p"
        using unlift [OF p] by blast
      have Pnz: "P \<noteq> \<zero>\<^sub>P"
        using nz lift zero_lift by blast
      have evP: "eeval splitting_extension x (lift_poly P) = \<zero>\<^sub>I"
        using ev lift by simp
      show "x \<in> algebraic_in_split"
        by (rule algebraic_in_splitI [OF x P Pnz evP])
    qed
  qed
  show ?thesis using T.algebraic_carrier_field by (simp add: eq)
qed


lemma unlift_base_polynomial:
  assumes p: "p \<in> Ring.poly_carrier (ipoly_const ` R) \<zero>\<^sub>I"
  obtains P where "P \<in> poly_carrier" and "lift_poly P = p"
proof -
  interpret T: field_tower_locale "ipoly_const ` R"
    "ecarrier splitting_extension" "eadd splitting_extension"
    "emult splitting_extension" "\<zero>\<^sub>I" "\<one>\<^sub>I"
    by (rule splitting_field_tower)
  have pT: "p \<in> T.base.poly_carrier" using p by simp
  define P where "P = (\<lambda>i. SOME z. z \<in> R \<and> ipoly_const z = p i)"
  have coeff: "P i \<in> R \<and> ipoly_const (P i) = p i" for i
  proof -
    have im: "p i \<in> ipoly_const ` R"
      by (rule T.base.poly_carrier_coeff_closed [OF pT])
    obtain z where z: "z \<in> R" "p i = ipoly_const z"
      using im by (rule imageE)
    have "\<exists>z. z \<in> R \<and> ipoly_const z = p i"
      by (rule exI [of _ z]) (simp add: z)
    then show ?thesis unfolding P_def by (rule someI_ex)
  qed
  have zero_coeff: "p i = \<zero>\<^sub>I \<longleftrightarrow> P i = \<zero>" for i
  proof
    assume "p i = \<zero>\<^sub>I"
    then show "P i = \<zero>"
      using coeff [of i] by (metis ipoly_const_coeff ipoly_const_zero)
  next
    assume "P i = \<zero>"
    then show "p i = \<zero>\<^sub>I" using coeff [of i] by simp
  qed
  have supp: "{i. P i \<noteq> \<zero>} = {i. p i \<noteq> \<zero>\<^sub>I}"
    using zero_coeff by blast
  have Pc: "P \<in> poly_carrier"
  proof (rule poly_carrierI)
    show "finite {i. P i \<noteq> \<zero>}"
      using T.base.poly_carrier_finite [OF pT] by (simp add: supp)
    show "\<And>i. P i \<in> R" using coeff by blast
  qed
  have "lift_poly P = p"
  proof (rule ext)
    fix i
    show "lift_poly P i = p i"
      using coeff [of i] by simp
  qed
  then show thesis by (rule that [OF Pc])
qed

lemma lift_poly_base_carrier:
  assumes P: "P \<in> poly_carrier"
  shows "lift_poly P \<in> Ring.poly_carrier (ipoly_const ` R) \<zero>\<^sub>I"
proof -
  interpret T: field_tower_locale "ipoly_const ` R"
    "ecarrier splitting_extension" "eadd splitting_extension"
    "emult splitting_extension" "\<zero>\<^sub>I" "\<one>\<^sub>I"
    by (rule splitting_field_tower)
  show ?thesis
  proof (rule T.base.poly_carrierI)
  have "{i. lift_poly P i \<noteq> \<zero>\<^sub>I} \<subseteq> {i. P i \<noteq> \<zero>}"
    by (auto simp: lift_poly_def ipoly_const_def ipoly_zero_def)
  then show "finite {i. lift_poly P i \<noteq> \<zero>\<^sub>I}"
    using poly_carrier_finite [OF P] by (rule finite_subset)
  show "\<And>i. lift_poly P i \<in> ipoly_const ` R"
    using P by (auto simp: lift_poly_def poly_carrier_coeff_closed)
  qed
qed

lemma lift_poly_base_nonzero:
  assumes Pnz: "P \<noteq> \<zero>\<^sub>P"
  shows "lift_poly P \<noteq> Ring.poly_zero \<zero>\<^sub>I"
proof -
  interpret T: field_tower_locale "ipoly_const ` R"
    "ecarrier splitting_extension" "eadd splitting_extension"
    "emult splitting_extension" "\<zero>\<^sub>I" "\<one>\<^sub>I"
    by (rule splitting_field_tower)
  obtain k where k: "P k \<noteq> \<zero>"
    using Pnz by (auto simp: poly_zero_def fun_eq_iff)
  then have "ipoly_const (P k) \<noteq> \<zero>\<^sub>I"
    by (metis ipoly_const_coeff ipoly_zero_def)
  then show ?thesis
    by (auto simp: lift_poly_def T.base.poly_zero_def fun_eq_iff)
qed

lemma algebraic_in_split_iff_base_algebraic:
  "x \<in> algebraic_in_split \<longleftrightarrow>
    x \<in> ecarrier splitting_extension \<and>
    (\<exists>p \<in> Ring.poly_carrier (ipoly_const ` R) \<zero>\<^sub>I.
      p \<noteq> Ring.poly_zero \<zero>\<^sub>I \<and>
      eeval splitting_extension x p = \<zero>\<^sub>I)"
proof -
  interpret T: field_tower_locale "ipoly_const ` R"
    "ecarrier splitting_extension" "eadd splitting_extension"
    "emult splitting_extension" "\<zero>\<^sub>I" "\<one>\<^sub>I"
    by (rule splitting_field_tower)
  have eq: "x \<in> algebraic_in_split \<longleftrightarrow> T.algebraic_over_base x"
  proof
  assume "x \<in> algebraic_in_split"
  then obtain P where x: "x \<in> ecarrier splitting_extension"
    and P: "P \<in> poly_carrier" and nz: "P \<noteq> \<zero>\<^sub>P"
    and ev: "eeval splitting_extension x (lift_poly P) = \<zero>\<^sub>I"
    by (rule algebraic_in_splitD)
  show "T.algebraic_over_base x"
    by (rule T.algebraic_over_baseI
      [OF x lift_poly_base_carrier [OF P] lift_poly_base_nonzero [OF nz] ev])
next
  assume ax: "T.algebraic_over_base x"
  obtain p where x: "x \<in> ecarrier splitting_extension"
    and p: "p \<in> T.base.poly_carrier"
    and nz: "p \<noteq> T.base.poly_zero"
    and ev: "eeval splitting_extension x p = \<zero>\<^sub>I"
    using ax by (rule T.algebraic_over_baseD)
  obtain P where P: "P \<in> poly_carrier" and lift: "lift_poly P = p"
    using unlift_base_polynomial [OF p] by blast
  have Pnz: "P \<noteq> \<zero>\<^sub>P"
    using nz lift by (auto simp: lift_poly_def poly_zero_def T.base.poly_zero_def)
  show "x \<in> algebraic_in_split"
    by (rule algebraic_in_splitI [OF x P Pnz]) (use ev lift in simp)
  qed
  show ?thesis using eq by (simp add: T.algebraic_over_base_def)
qed

lemma base_algebraic_in_split:
  assumes a: "a \<in> R"
  shows "ipoly_const a \<in> algebraic_in_split"
proof -
  have ext: "is_extension splitting_extension"
    using splitting_extension_spec by blast
  interpret W: Field "ecarrier splitting_extension" "eadd splitting_extension"
    "emult splitting_extension" "\<zero>\<^sub>I" "\<one>\<^sub>I"
    by (rule splitting_extension_field)
  have rf: "lift_poly (root_factor a) = W.root_factor (ipoly_const a)"
    unfolding lift_poly_def
    apply (rule root_factor_hom [where mult=multiplication
          and bmult="emult splitting_extension"])
    using a
    by (auto intro: base_mem_splitting_extension Ring_axioms W.Ring_axioms
          commutative_ring_axioms W.commutative_ring_axioms
        simp: is_extension_const_add [OF ext] is_extension_const_mult [OF ext])
  have ev: "eeval splitting_extension (ipoly_const a) (lift_poly (root_factor a)) = \<zero>\<^sub>I"
    using rf W.eval_root_factor [OF base_mem_splitting_extension [OF a]] by simp
  show ?thesis
    by (rule algebraic_in_splitI [OF base_mem_splitting_extension [OF a]
          root_factor_closed [OF a] root_factor_nonzero [OF a] ev])
qed

lemma base_subset_algebraic_in_split:
  "ipoly_const ` R \<subseteq> algebraic_in_split"
  using base_algebraic_in_split by blast

lemma lift_poly_degree:
  "Ring.degree \<zero>\<^sub>I (lift_poly P) = degree P"
proof -
  have "{i. lift_poly P i \<noteq> \<zero>\<^sub>I} = {i. P i \<noteq> \<zero>}"
    by (auto simp: lift_poly_def ipoly_const_def ipoly_zero_def fun_eq_iff)
  then show ?thesis
    by (simp add: Ring.degree_def [OF ipoly_ring] degree_def)
qed

lemma splitting_root_algebraic:
  assumes "P \<in> poly_carrier" and "P \<noteq> \<zero>\<^sub>P"
    and "x \<in> ecarrier splitting_extension"
    and "eeval splitting_extension x (lift_poly P) = \<zero>\<^sub>I"
  shows "x \<in> algebraic_in_split"
  by (rule algebraic_in_splitI [OF assms(3) assms(1) assms(2) assms(4)])

theorem splitting_extension_has_algebraic_root:
  assumes P: "P \<in> poly_carrier" and pos: "0 < degree P"
  obtains x where "x \<in> algebraic_in_split"
    and "eeval splitting_extension x (lift_poly P) = \<zero>\<^sub>I"
proof -
  interpret W: Field "ecarrier splitting_extension" "eadd splitting_extension"
    "emult splitting_extension" "\<zero>\<^sub>I" "\<one>\<^sub>I"
    by (rule splitting_extension_field)
  have sp: "W.splits (lift_poly P)"
    by (rule splitting_extension_splits [OF P])
  have deg: "0 < W.degree (lift_poly P)"
    using pos by (simp add: lift_poly_degree)
  obtain x where x: "x \<in> ecarrier splitting_extension"
    and ev: "eeval splitting_extension x (lift_poly P) = \<zero>\<^sub>I"
    using W.splits_pos_degree_has_root [OF sp deg] by blast
  have nz: "P \<noteq> \<zero>\<^sub>P" using pos by auto
  show thesis
    by (rule that [OF splitting_root_algebraic [OF P nz x ev] ev])
qed

theorem algebraic_in_split_splits:
  assumes P: "P \<in> poly_carrier"
  shows "Field.splits algebraic_in_split (eadd splitting_extension)
    (emult splitting_extension) \<zero>\<^sub>I \<one>\<^sub>I (lift_poly P)"
proof -
  interpret A: Field algebraic_in_split "eadd splitting_extension"
    "emult splitting_extension" "\<zero>\<^sub>I" "\<one>\<^sub>I"
    by (rule algebraic_in_split_field)
  interpret T: field_tower_locale algebraic_in_split
    "ecarrier splitting_extension" "eadd splitting_extension"
    "emult splitting_extension" "\<zero>\<^sub>I" "\<one>\<^sub>I"
    by (intro field_tower_locale.intro field_tower_locale_axioms.intro
        A.Field_axioms splitting_extension_field algebraic_in_split_subset)
  have liftA: "lift_poly P \<in> A.poly_carrier"
  proof (rule A.poly_carrierI)
    have "{i. lift_poly P i \<noteq> \<zero>\<^sub>I} \<subseteq> {i. P i \<noteq> \<zero>}"
      by (auto simp: lift_poly_def ipoly_const_def ipoly_zero_def)
    then show "finite {i. lift_poly P i \<noteq> \<zero>\<^sub>I}"
      using poly_carrier_finite [OF P] by (rule finite_subset)
    show "\<And>i. lift_poly P i \<in> algebraic_in_split"
      using P by (simp add: base_algebraic_in_split poly_carrier_coeff_closed)
  qed
  show ?thesis
  proof (cases "P = \<zero>\<^sub>P")
    case True
    have "lift_poly P = A.poly_zero"
      using True by (simp add: lift_poly_def poly_zero_def A.poly_zero_def)
    then show ?thesis by simp
  next
    case False
    show ?thesis
    proof (rule T.splits_descends [OF liftA splitting_extension_splits [OF P]])
      fix x
      assume x: "x \<in> ecarrier splitting_extension"
        and ev: "eeval splitting_extension x (lift_poly P) = \<zero>\<^sub>I"
      show "x \<in> algebraic_in_split"
        by (rule splitting_root_algebraic [OF P False x ev])
    qed
  qed
qed

theorem algebraic_in_split_is_algebraic_closure:
  "carrier_algebraic_closure (ipoly_const ` R) algebraic_in_split
    (eadd splitting_extension) (emult splitting_extension)
    \<zero>\<^sub>I \<one>\<^sub>I"
proof -
  interpret T: field_tower_locale "ipoly_const ` R" algebraic_in_split
    "eadd splitting_extension" "emult splitting_extension"
    "\<zero>\<^sub>I" "\<one>\<^sub>I"
    by (intro field_tower_locale.intro field_tower_locale_axioms.intro
        base_image_field algebraic_in_split_field base_subset_algebraic_in_split)
  interpret AL: field_tower_locale algebraic_in_split
    "ecarrier splitting_extension" "eadd splitting_extension"
    "emult splitting_extension" "\<zero>\<^sub>I" "\<one>\<^sub>I"
    by (intro field_tower_locale.intro field_tower_locale_axioms.intro
        algebraic_in_split_field splitting_extension_field algebraic_in_split_subset)
  show ?thesis
  proof (intro carrier_algebraic_closure.intro T.field_tower_locale_axioms
      carrier_algebraic_closure_axioms.intro)
    fix x assume x: "x \<in> algebraic_in_split"
    show "T.algebraic_over_base x"
    proof -
      obtain q where q: "q \<in> T.base.poly_carrier"
        and qnz: "q \<noteq> T.base.poly_zero"
        and ev: "eeval splitting_extension x q = \<zero>\<^sub>I"
        using x algebraic_in_split_iff_base_algebraic by blast
      have qA: "q \<in> T.ext.poly_carrier"
        using T.base_poly_carrier_subset_ext q by blast
      have "T.ext.eval x q = \<zero>\<^sub>I"
        using ev AL.eval_agrees_on_base [OF x qA] by simp
      then show ?thesis by (rule T.algebraic_over_baseI [OF x q qnz])
    qed
  next
    fix q assume q: "q \<in> T.base.poly_carrier"
    obtain P where P: "P \<in> poly_carrier" and lift: "lift_poly P = q"
      using unlift_base_polynomial [OF q] by blast
    show "T.ext.splits q"
      using algebraic_in_split_splits [OF P] by (simp add: lift)
  qed
qed

text \<open>Every positive-degree polynomial over the algebraic part of the
  splitting extension has a root there.  Its finitely many coefficients lie
  in a finite extension of the base field.  The remainder-space argument
  supplies a nonzero base polynomial divisible by it; that base polynomial
  splits in the algebraic carrier.\<close>
theorem algebraic_in_split_algebraically_closed:
  assumes p: "p \<in> Ring.poly_carrier algebraic_in_split \<zero>\<^sub>I"
    and pos: "0 < Ring.degree \<zero>\<^sub>I p"
  obtains x where "x \<in> algebraic_in_split"
    and "eeval splitting_extension x p = \<zero>\<^sub>I"
proof -
  interpret C: carrier_algebraic_closure "ipoly_const ` R" algebraic_in_split
    "eadd splitting_extension" "emult splitting_extension"
    "\<zero>\<^sub>I" "\<one>\<^sub>I"
    by (rule algebraic_in_split_is_algebraic_closure)
  interpret AL: field_tower_locale algebraic_in_split
    "ecarrier splitting_extension" "eadd splitting_extension"
    "emult splitting_extension" "\<zero>\<^sub>I" "\<one>\<^sub>I"
    by (intro field_tower_locale.intro field_tower_locale_axioms.intro
        algebraic_in_split_field splitting_extension_field algebraic_in_split_subset)
  obtain x where x: "x \<in> algebraic_in_split"
    and ev: "C.ext.eval x p = \<zero>\<^sub>I"
    using C.roots_over_carrier [OF p pos] by blast
  have "eeval splitting_extension x p = \<zero>\<^sub>I"
    using ev AL.eval_agrees_on_base [OF x p] by simp
  then show thesis by (rule that [OF x])
qed

end

section \<open>The Algebraic Closure as a Field Type\<close>

text \<open>
  \<open>Closure_Extension\<close> produces, for any field, an extension inside the indexed
  polynomial ring in which every polynomial over the base field splits.  That extension is not yet an
  algebraic closure: it is far too big, being generated by one indeterminate for every polynomial and
  root index, and it is not algebraic over the base.  The closure is cut out of it as the set of
  elements algebraic over the base.

  The closure theorem in this theory transports the extension onto a type.  The development's
  field-extension and Galois theory already works with an ambient type-class field and subfields as
  carrier sets, and once the extension is a type all of it applies --- in particular
  @{thm [source] subfield_algebraic_elements}, which says that the algebraic elements form a subfield.
  The preceding part proves algebraic closure directly for carrier-set fields.  The development
  below also transports the splitting extension onto a type, providing the type-class field used
  by the field-extension and Galois theories.
\<close>

subsection \<open>An extension of the whole type in which every polynomial splits\<close>

context poly_TC
begin

text \<open>A definite choice among the extensions supplied by @{thm [source] exists_extension_with_roots},
  so that the type constructed from it below depends on nothing but @{typ 'a}.\<close>

definition wide_extension where "wide_extension = splitting_extension"

lemma wide_extension_spec:
  "is_extension wide_extension
   \<and> (\<forall>P \<in> poly_carrier.
        Field.splits (ecarrier wide_extension) (eadd wide_extension) (emult wide_extension)
                     ipoly_zero ipoly_one (lift_poly P))"
  unfolding wide_extension_def
  by (rule splitting_extension_spec)

lemmas is_extension_wide_extension = wide_extension_spec [THEN conjunct1]

lemma wide_extension_splits:
  "P \<in> poly_carrier
   \<Longrightarrow> Field.splits (ecarrier wide_extension) (eadd wide_extension) (emult wide_extension)
                    ipoly_zero ipoly_one (lift_poly P)"
  using wide_extension_spec by blast

text \<open>The field structure of the chosen extension, named once for the transport below.\<close>
lemma field_wide_extension:
  "Field (ecarrier wide_extension) (eadd wide_extension) (emult wide_extension)
         ipoly_zero ipoly_one"
  by (rule is_extension_field [OF is_extension_wide_extension])

lemma wide_extension_nonempty: "ipoly_zero \<in> ecarrier wide_extension"
proof -
  interpret W: Field "ecarrier wide_extension" "eadd wide_extension" "emult wide_extension"
                    ipoly_zero ipoly_one
    by (rule field_wide_extension)
  show ?thesis by (rule W.additive.unit_closed)
qed

text \<open>How the base field sits inside the extension.  These are restatements of the extension
  conditions at the chosen extension: only facts proved \<^emph>\<open>in this locale\<close> are available once it is
  left, and the type constructed below can only be spoken of outside it.\<close>

lemma wide_const_mem: "ipoly_const a \<in> ecarrier wide_extension"
  by (simp add: is_extension_const_mem [OF is_extension_wide_extension])

lemma wide_const_add:
  "eadd wide_extension (ipoly_const a) (ipoly_const b) = ipoly_const (a + b)"
  by (simp add: is_extension_const_add [OF is_extension_wide_extension])

lemma wide_const_mult:
  "emult wide_extension (ipoly_const a) (ipoly_const b) = ipoly_const (a * b)"
  by (simp add: is_extension_const_mult [OF is_extension_wide_extension])

lemmas wide_const_inj = ipoly_const_inj_on
lemmas wide_lift_poly_apply = lift_poly_apply
lemmas wide_const_zero = ipoly_const_zero
lemmas wide_const_one = ipoly_const_one

end


subsection \<open>The extension as a type\<close>

text \<open>The extension is a field, but a locale one, on a carrier set inside the indexed polynomial
  ring.  Carving that carrier out as a type and transporting the operations onto it makes it a
  type-class field, which is what the rest of the development can use.\<close>

typedef (overloaded) 'a :: field wide = "ecarrier (poly_TC.wide_extension :: 'a iext)"
  using wide_extension_nonempty by blast

setup_lifting type_definition_wide

text \<open>Names for the transported structure.  The locale's constants must be spelled out here because
  @{locale poly_TC} fixes no parameters, so its abbreviations do not reach outside it; each takes
  only the parameters occurring in its definition.\<close>

abbreviation wcarrier :: "'a :: field ipoly set"
  where "wcarrier \<equiv> ecarrier (poly_TC.wide_extension :: 'a iext)"

abbreviation wadd :: "'a :: field ipoly \<Rightarrow> 'a ipoly \<Rightarrow> 'a ipoly"
  where "wadd \<equiv> eadd (poly_TC.wide_extension :: 'a iext)"

abbreviation wmult :: "'a :: field ipoly \<Rightarrow> 'a ipoly \<Rightarrow> 'a ipoly"
  where "wmult \<equiv> emult (poly_TC.wide_extension :: 'a iext)"

abbreviation wzero :: "'a :: field ipoly"
  where "wzero \<equiv> Ring.ipoly_zero 0"

abbreviation wone :: "'a :: field ipoly"
  where "wone \<equiv> Ring.ipoly_one 0 1"

abbreviation wneg :: "'a :: field ipoly \<Rightarrow> 'a ipoly"
  where "wneg \<equiv> Monoid.inverse wcarrier wadd wzero"

abbreviation winv :: "'a :: field ipoly \<Rightarrow> 'a ipoly"
  where "winv \<equiv> Monoid.inverse wcarrier wmult wone"

interpretation W: Field wcarrier wadd wmult wzero wone
  by (rule field_wide_extension)

instantiation wide :: (field) field
begin

lift_definition zero_wide :: "'a wide" is "wzero :: 'a ipoly"
  by (rule W.additive.unit_closed)

lift_definition one_wide :: "'a wide" is "wone :: 'a ipoly"
  by (rule W.multiplicative.unit_closed)

lift_definition plus_wide :: "'a wide \<Rightarrow> 'a wide \<Rightarrow> 'a wide" is "wadd :: 'a ipoly \<Rightarrow> _"
  by (rule W.additive.composition_closed)

lift_definition times_wide :: "'a wide \<Rightarrow> 'a wide \<Rightarrow> 'a wide" is "wmult :: 'a ipoly \<Rightarrow> _"
  by (rule W.multiplicative.composition_closed)

lift_definition uminus_wide :: "'a wide \<Rightarrow> 'a wide" is "wneg :: 'a ipoly \<Rightarrow> _"
  by simp

lift_definition minus_wide :: "'a wide \<Rightarrow> 'a wide \<Rightarrow> 'a wide"
  is "\<lambda>x y. wadd x (wneg y) :: 'a ipoly"
  by simp

text \<open>HOL's field class requires @{term "inverse 0 = 0"}, where the locale leaves the inverse of
  @{term wzero} unspecified; the two are reconciled by the case split.\<close>
lift_definition inverse_wide :: "'a wide \<Rightarrow> 'a wide"
  is "\<lambda>x. if x = wzero then wzero else winv x :: 'a ipoly"
  by (auto intro: W.multiplicative.invertible_inverse_closed W.field_inverse)

lift_definition divide_wide :: "'a wide \<Rightarrow> 'a wide \<Rightarrow> 'a wide"
  is "\<lambda>x y. if y = wzero then wzero else wmult x (winv y) :: 'a ipoly"
  by (auto intro: W.multiplicative.invertible_inverse_closed W.field_inverse)

instance
proof (standard, goal_cases)
  case 1 show ?case by transfer (rule W.multiplicative.associative)
next
  case 2 show ?case by transfer (rule W.multiplicative.commutative)
next
  case 3 show ?case by transfer (rule W.multiplicative.left_unit)
next
  case 4 show ?case by transfer (rule W.additive.associative)
next
  case 5 show ?case by transfer (rule W.additive.commutative)
next
  case 6 show ?case by transfer (rule W.additive.left_unit)
next
  case 7 show ?case by transfer simp
next
  case 8 show ?case by transfer simp
next
  case 9 show ?case by transfer (rule W.distributive)
next
  case 10 show ?case by transfer (rule not_sym [OF W.nontrivial])
next
  case 11 then show ?case
    by transfer (auto intro: W.field_inverse W.multiplicative.invertible_left_inverse)
next
  case 12 then show ?case by transfer auto
next
  case 13 then show ?case by transfer auto
qed

end

text \<open>A field is a Euclidean ring in a trivial way.  Spelling that out for @{typ "'a wide"} --- as
  HOL-Algebra's \<open>Algebraic_Closure_Type\<close> does for its own closure type --- is what puts
  @{typ "'a wide poly"} in @{class factorial_semiring}, and so makes HOL's factorisation machinery,
  in particular the primality of a monic linear polynomial, available over the extension.\<close>

instantiation wide :: (field)
  "{unique_euclidean_ring, normalization_euclidean_semiring, normalization_semidom_multiplicative}"
begin

definition [simp]: "normalize_wide = (normalize_field :: 'a wide \<Rightarrow> _)"
definition [simp]: "unit_factor_wide = (unit_factor_field :: 'a wide \<Rightarrow> _)"
definition [simp]: "modulo_wide = (mod_field :: 'a wide \<Rightarrow> _)"
definition [simp]: "euclidean_size_wide = (euclidean_size_field :: 'a wide \<Rightarrow> _)"
definition [simp]: "division_segment (x :: 'a wide) = 1"

instance
  by standard (simp_all add: dvd_field_iff field_split_simps split: if_splits)

end

instantiation wide :: (field) euclidean_ring_gcd
begin

definition gcd_wide :: "'a wide \<Rightarrow> 'a wide \<Rightarrow> 'a wide"
  where "gcd_wide = Euclidean_Algorithm.gcd"
definition lcm_wide :: "'a wide \<Rightarrow> 'a wide \<Rightarrow> 'a wide"
  where "lcm_wide = Euclidean_Algorithm.lcm"
definition Gcd_wide :: "'a wide set \<Rightarrow> 'a wide"
  where "Gcd_wide = Euclidean_Algorithm.Gcd"
definition Lcm_wide :: "'a wide set \<Rightarrow> 'a wide"
  where "Lcm_wide = Euclidean_Algorithm.Lcm"

instance
  by standard (simp_all add: gcd_wide_def lcm_wide_def Gcd_wide_def Lcm_wide_def)

end

instance wide :: (field) semiring_gcd_mult_normalize ..

text \<open>The four instances above are exactly @{class field_gcd}, which is the sort under which HOL states
  the primality of a monic linear polynomial.\<close>
instance wide :: (field) field_gcd ..


subsection \<open>The base field inside the extension\<close>

text \<open>The base field sits in the extension as the constants.  This is the embedding along which the
  algebraic closure will be described: a subfield of @{typ "'a wide"} isomorphic to @{typ 'a}.\<close>

lift_definition to_wide :: "'a :: field \<Rightarrow> 'a wide" is "Ring.ipoly_const 0 :: 'a \<Rightarrow> 'a ipoly"
  by (rule wide_const_mem)

lemma to_wide_zero [simp]: "to_wide 0 = 0"
  by transfer (rule wide_const_zero)

lemma to_wide_one [simp]: "to_wide 1 = 1"
  by transfer (rule wide_const_one)

lemma to_wide_add [simp]: "to_wide (x + y) = to_wide x + to_wide y"
  by transfer (rule wide_const_add [symmetric])

lemma to_wide_mult [simp]: "to_wide (x * y) = to_wide x * to_wide y"
  by transfer (rule wide_const_mult [symmetric])

lemma inj_to_wide: "inj (to_wide :: 'a :: field \<Rightarrow> 'a wide)"
  by (metis UNIV_I injI inj_on_eq_iff to_wide.rep_eq wide_const_inj)

lemma to_wide_eq_iff [simp]: "to_wide x = to_wide y \<longleftrightarrow> x = y"
  using inj_to_wide by (auto dest: injD)

text \<open>Being a ring homomorphism between fields, the embedding automatically respects negation and
  inversion: each is pinned by the equation it solves.\<close>

lemma to_wide_uminus [simp]: "to_wide (- x) = - to_wide x"    
  using to_wide_add [of "- x" x] eq_neg_iff_add_eq_0 by auto

lemma to_wide_inverse [simp]: "to_wide (inverse x) = inverse (to_wide x)"
  using to_wide_mult [of x "inverse x"] inverse_unique right_inverse[of x] by fastforce

lemma to_wide_diff [simp]: "to_wide (x - y) = to_wide x - to_wide y"
  using to_wide_add [of x "- y"] by simp

theorem subfield_range_to_wide: "Subfield (range (to_wide :: 'a :: field \<Rightarrow> 'a wide))"
proof
  show "(0 :: 'a wide) \<in> range to_wide" using rangeI [of to_wide 0] by simp
  show "(1 :: 'a wide) \<in> range to_wide" using rangeI [of to_wide 1] by simp
qed (auto simp flip: to_wide_add to_wide_uminus to_wide_mult to_wide_inverse)

text \<open>The inverse of the embedding, so that a polynomial over the base subfield can be read back as
  a polynomial over @{typ 'a}.\<close>

definition of_wide :: "'a :: field wide \<Rightarrow> 'a"
  where "of_wide = inv to_wide"

lemma of_wide_to_wide [simp]: "of_wide (to_wide x) = x"
  by (simp add: of_wide_def inj_to_wide)

lemma to_wide_of_wide [simp]: "x \<in> range to_wide \<Longrightarrow> to_wide (of_wide x) = x"
  by (auto simp: of_wide_def f_inv_into_f)

lemma of_wide_zero [simp]: "of_wide 0 = 0"
  by (metis of_wide_to_wide to_wide_zero)


subsection \<open>Every polynomial over the base subfield splits\<close>

text \<open>@{const Abs_wide} is a field isomorphism from the carrier onto the type, so
  @{thm [source] splits_hom} carries the splitting of a base polynomial across.  Each equation below
  is read off from the corresponding \<open>rep_eq\<close> of the transported operation.\<close>

lemma Abs_wide_zero [simp]: "Abs_wide wzero = 0"
  using Rep_wide_inverse [of 0] by (simp add: zero_wide.rep_eq)

lemma Abs_wide_one [simp]: "Abs_wide wone = 1"
  using Rep_wide_inverse [of 1] by (simp add: one_wide.rep_eq)

lemma Abs_wide_add:
  assumes "x \<in> wcarrier" and "y \<in> wcarrier"
  shows "Abs_wide (wadd x y) = Abs_wide x + Abs_wide y"
  using Rep_wide_inverse [of "Abs_wide x + Abs_wide y"]
  by (simp add: plus_wide.rep_eq Abs_wide_inverse assms)

lemma Abs_wide_mult:
  assumes "x \<in> wcarrier" and "y \<in> wcarrier"
  shows "Abs_wide (wmult x y) = Abs_wide x * Abs_wide y"
  using Rep_wide_inverse [of "Abs_wide x * Abs_wide y"]
  by (simp add: times_wide.rep_eq Abs_wide_inverse assms)

lemma Abs_wide_const [simp]: "Abs_wide (Ring.ipoly_const 0 a) = to_wide a"
  by (simp add: to_wide.abs_eq)

text \<open>A polynomial whose coefficients lie in the base subfield, read back as a polynomial over the
  base field itself.\<close>

definition wide_pull :: "'a :: field wide poly \<Rightarrow> nat \<Rightarrow> 'a"
  where "wide_pull p \<equiv> (\<lambda>k. of_wide (Polynomial.coeff p k))"

lemma wide_pull_carrier: "wide_pull p \<in> Ring.poly_carrier (UNIV :: 'a :: field set) 0"
proof -
  have "{k. wide_pull p k \<noteq> 0} \<subseteq> {k. Polynomial.coeff p k \<noteq> 0}"
    by (auto simp: wide_pull_def)
  then have "finite {k. wide_pull p k \<noteq> (0 :: 'a)}"
    by (rule finite_subset) simp
  then show ?thesis by (simp add: poly_carrier_iff)
qed

lemma to_wide_wide_pull:
  assumes p: "p \<in> poly_over (range (to_wide :: 'a :: field \<Rightarrow> 'a wide))"
  shows "to_wide (wide_pull p k) = Polynomial.coeff p k"
  by (simp add: Subfield.poly_over_coeff p subfield_range_to_wide wide_pull_def)

theorem wide_splits:
  fixes p :: "'a :: field wide poly"
  assumes p: "p \<in> poly_over (range to_wide)"
  obtains c as where "p = [:c:] * (\<Prod>a\<leftarrow>as. [:uminus a, 1:])"
proof -
  have RA: "Ring wcarrier wadd wmult (wzero :: 'a ipoly) wone"
    using W.Ring_axioms by simp
  have RB: "Ring (UNIV :: 'a wide set) (+) (*) 0 1"
    using field_TC.Ring_axioms by simp
  have lift: "Ring.lift_poly 0 (wide_pull p) k \<in> wcarrier" for k
    by (simp add: wide_lift_poly_apply wide_const_mem)
  have spB: "Field.splits (UNIV :: 'a wide set) (+) (*) 0 1
               (\<lambda>k. Abs_wide (Ring.lift_poly 0 (wide_pull p) k))"
  proof (intro splits_hom [OF RA RB])
    show "\<And>y y'. \<lbrakk> y \<in> wcarrier; y' \<in> wcarrier \<rbrakk> \<Longrightarrow> Abs_wide (wadd y y') = Abs_wide y + Abs_wide y'"
      by (rule Abs_wide_add)
    show "\<And>y y'. \<lbrakk> y \<in> wcarrier; y' \<in> wcarrier \<rbrakk> \<Longrightarrow> Abs_wide (wmult y y') = Abs_wide y * Abs_wide y'"
      by (rule Abs_wide_mult)
    show "Field wcarrier wadd wmult (wzero :: 'a ipoly) wone"
      by (rule field_wide_extension)
    show "Field (UNIV :: 'a wide set) (+) (*) 0 1"
      by (rule field_TC.Field_axioms)
    show "Field.splits wcarrier wadd wmult wzero wone (Ring.lift_poly 0 (wide_pull p))"
      by (rule wide_extension_splits [OF wide_pull_carrier])
  qed auto
  have "(\<lambda>k. Abs_wide (Ring.lift_poly 0 (wide_pull p) k)) = Polynomial.coeff p"
    by (simp add: wide_lift_poly_apply to_wide_wide_pull [OF p])
  with spB have "Field.splits (UNIV :: 'a wide set) (+) (*) 0 1 (Polynomial.coeff p)"
    by simp
  then show thesis 
    using splits_coeff_iff that by blast
qed


subsection \<open>The algebraic closure\<close>

text \<open>The splitting extension is far larger than an algebraic closure --- it has an indeterminate
  for every polynomial and root index, and is not algebraic over the base.  Cutting it down to the
  elements algebraic over the base gives the closure.  Nothing has to be proved about that set here:
  @{thm [source] subfield_algebraic_elements} already says it is a subfield, which is exactly what
  transporting the extension onto a type bought.\<close>

definition alg_closure :: "'a :: field wide set"
  where "alg_closure = algebraic_elements (range to_wide)"

theorem subfield_alg_closure: "Subfield (alg_closure :: 'a :: field wide set)"
  unfolding alg_closure_def by (rule subfield_algebraic_elements [OF subfield_range_to_wide])

lemma alg_closure_iff: "x \<in> alg_closure \<longleftrightarrow> algebraic_over (range to_wide) x"
  by (simp add: alg_closure_def algebraic_elements_def)

theorem base_subset_alg_closure: "range (to_wide :: 'a :: field \<Rightarrow> 'a wide) \<subseteq> alg_closure"
    using Subfield.algebraic_over_self [OF subfield_range_to_wide] alg_closure_iff by blast

theorem algebraic_extension_alg_closure:
  "algebraic_extension (alg_closure :: 'a :: field wide set) (range to_wide)"
  by (simp add: algebraic_extension_def alg_closure_iff)

text \<open>Two facts about a product of linear factors: it is monic, and its roots are exactly the
  elements of the list.\<close>

lemma lead_coeff_linear_prod: "lead_coeff (\<Prod>a\<leftarrow>as. [:uminus a, 1:]) = (1 :: 'b :: idom)"
proof (induct as)
  case Nil
  show ?case by simp
next
  case (Cons a as)
  have "lead_coeff ([:uminus a, 1:] * (\<Prod>b\<leftarrow>as. [:uminus b, 1:]))
        = lead_coeff [:uminus a, 1:] * lead_coeff (\<Prod>b\<leftarrow>as. [:uminus b, 1:])"
    by (rule lead_coeff_mult)
  with Cons show ?case by simp
qed

lemma poly_linear_prod_eq_0_iff:
  "poly (\<Prod>a\<leftarrow>as. [:uminus a, 1:]) z = (0 :: 'b :: idom) \<longleftrightarrow> z \<in> set as"
  by (induct as) auto

text \<open>A root of a nonzero polynomial over the base is algebraic over it, so lies in the closure ---
  that polynomial is its own witness.\<close>
lemma alg_closure_root:
  fixes p :: "'a :: field wide poly"
  assumes "p \<in> poly_over (range to_wide)" and "p \<noteq> 0" and "poly p z = 0"
  shows "z \<in> alg_closure"
  using assms by (auto simp: alg_closure_iff algebraic_over_def)

text \<open>Every nonzero polynomial over the base splits, with all of its roots and its leading
  coefficient inside the closure.  Because \<open>splits\<close> carries an explicit list of roots, the
  descent from the splitting extension to the closure is immediate: the very same product works,
  every factor being a root of a base polynomial and hence algebraic.\<close>
theorem alg_closure_splits:
  fixes p :: "'a :: field wide poly"
  assumes p: "p \<in> poly_over (range to_wide)" and nz: "p \<noteq> 0"
  obtains c as where "c \<in> alg_closure" and "set as \<subseteq> alg_closure"
    and "p = [:c:] * (\<Prod>a\<leftarrow>as. [:uminus a, 1:])"
proof -
  obtain c as where peq: "p = [:c:] * (\<Prod>a\<leftarrow>as. [:uminus a, 1:])"
    using wide_splits [OF p] by blast
  have "c = lead_coeff p"
    by (simp add: peq lead_coeff_mult lead_coeff_linear_prod)
  then have "c \<in> range to_wide"
    using Subfield.lead_coeff_closed [OF subfield_range_to_wide p] by simp
  then have cA: "c \<in> alg_closure"
    using base_subset_alg_closure by blast
  have "a \<in> alg_closure" if "a \<in> set as" for a
    using that alg_closure_root [OF p nz] by (simp add: peq poly_linear_prod_eq_0_iff)
  then have asA: "set as \<subseteq> alg_closure" by blast
  show thesis by (rule that [OF cA asA peq])
qed

corollary poly_root_set_subset_alg_closure:
  fixes p :: "'a :: field wide poly"
  assumes "p \<in> poly_over (range to_wide)" and "p \<noteq> 0"
  shows "poly_root_set p \<subseteq> alg_closure"
  using alg_closure_root [OF assms] by (auto simp: poly_root_set_def)

text \<open>The existence statement, in the shape of HOL-Algebra's \<open>exists_closure\<close>: every field has an
  algebraic extension in which each of its polynomials splits.\<close>
theorem exists_closure:
  obtains L :: "'a :: field wide set"
  where "Subfield L" and "range to_wide \<subseteq> L" and "algebraic_extension L (range to_wide)"
    and "\<And>p. \<lbrakk> p \<in> poly_over (range to_wide); p \<noteq> 0 \<rbrakk>
              \<Longrightarrow> \<exists>c as. c \<in> L \<and> set as \<subseteq> L \<and> p = [:c:] * (\<Prod>a\<leftarrow>as. [:uminus a, 1:])"
  by (metis alg_closure_splits algebraic_extension_alg_closure base_subset_alg_closure
      subfield_alg_closure)


subsection \<open>The closure is algebraically closed\<close>

text \<open>A divisor of a split polynomial of positive degree has a root among its factors.  Peeling one
  factor at a time: either it is a root of the divisor, or the divisor is coprime to it (linear
  monic polynomials are prime) and the factor can be cancelled.\<close>

lemma dvd_split_imp_root:
  fixes q :: "'b :: field_gcd poly"
  assumes "q dvd [:\<gamma>:] * (\<Prod>a\<leftarrow>as. [:uminus a, 1:])" and "\<gamma> \<noteq> 0" and "0 < degree q"
  shows "\<exists>a \<in> set as. poly q a = 0"
  using assms
proof (induct as arbitrary: \<gamma>)
  case Nil
  then have "[:\<gamma>:] \<noteq> 0" by simp
  with Nil have "degree q \<le> degree [:\<gamma>:]"
    by (metis dvd_imp_degree_le list.map(1) mult_cancel_left1 prod_list.Nil)
  with Nil.prems(3) show ?case by simp
next
  case (Cons a as)
  then have dvd1: "q dvd [:uminus a, 1:] * ([:\<gamma>:] * (\<Prod>b\<leftarrow>as. [:uminus b, 1:]))"
    by simp
  show ?case
  proof (cases "poly q a = 0")
    case True
    then show ?thesis by auto
  next
    case False
    then have nd: "\<not> [:uminus a, 1:] dvd q"
      by (simp add: poly_eq_0_iff_dvd)
    have pe: "prime_elem [:uminus a, 1 :: 'b:]"
      by (rule prime_elem_linear_poly) simp_all
    have copq: "coprime q [:uminus a, 1 :: 'b:]"
      using coprime_commute prime_elem_imp_coprime [OF pe nd] by blast
    have "q dvd [:\<gamma>:] * (\<Prod>b\<leftarrow>as. [:uminus b, 1:])"
      using dvd1 coprime_dvd_mult_right_iff [OF copq] by blast
    then show ?thesis
      using Cons by auto
  qed
qed

text \<open>
  Every polynomial over the closure of positive degree has a root there, so the closure is
  algebraically closed.

  This is the one step of the construction that needs a dimension count, and it is HOL-Algebra's
  rupture argument in elementary form.  Normalise the polynomial to be monic and let \<open>L\<close> be a finite
  extension of the base containing its coefficients, which exists because those coefficients are
  algebraic (@{thm [source] exists_finite_subfield_tower}).  Divide \<open>X\<^sup>i\<close> by the polynomial for
  \<open>i \<le> n * card B\<close>, where \<open>B\<close> is a basis of \<open>L\<close>: each remainder has degree below \<open>n\<close> and coefficients
  in \<open>L\<close>, so it is described by \<open>n * card B\<close> scalars from the base field, while there are
  \<open>n * card B + 1\<close> of them.  @{thm [source] Subfield.underdetermined_solution} therefore supplies a
  nontrivial vanishing combination, whose coefficients assemble into a nonzero polynomial \<^emph>\<open>over the
  base\<close> that the given polynomial divides.  That one splits in the closure, and a divisor of a split
  polynomial has a root.

  Where HOL-Algebra forms the quotient \<open>A[X]/(P)\<close> and compares its dimension with that of \<open>K[X]\<close>, the
  linear system does the same counting directly, so no quotient (which would change the type) is
  ever constructed.
\<close>
theorem alg_closure_alg_closed:
  fixes p :: "'a :: field wide poly"
  assumes p: "p \<in> poly_over alg_closure" and dp: "0 < degree p"
  obtains z where "z \<in> alg_closure" and "poly p z = 0"
proof -
  interpret K: Subfield "range (to_wide :: 'a \<Rightarrow> 'a wide)" by (rule subfield_range_to_wide)
  interpret A: Subfield "alg_closure :: 'a wide set" by (rule subfield_alg_closure)

  \<comment> \<open>Normalise to a monic polynomial with the same roots.\<close>
  define q where "q \<equiv> smult (inverse (lead_coeff p)) p"
  have pnz: "p \<noteq> 0" using dp by auto
  then have lc: "lead_coeff p \<noteq> 0" by simp
  have lcA: "lead_coeff p \<in> alg_closure" by (rule A.lead_coeff_closed [OF p])
  have qA: "q \<in> poly_over alg_closure"
    unfolding q_def using p lcA by (auto intro: A.poly_over_smult A.inverse_closed)
  have dq: "degree q = degree p" by (simp add: q_def lc)
  have monic: "lead_coeff q = 1" by (simp add: q_def lc pnz)
  have roots: "poly q z = 0 \<longleftrightarrow> poly p z = 0" for z
    using lc by (auto simp: q_def)
  define n where "n \<equiv> degree q"
  have npos: "0 < n" using dp dq by (simp add: n_def)

  \<comment> \<open>A finite extension of the base containing the coefficients.\<close>
  define S where "S \<equiv> (\<lambda>i. coeff q i) ` {..n}"
  have finS: "finite S" by (simp add: S_def)
  have SA: "S \<subseteq> alg_closure" using qA by (auto simp: S_def A.poly_over_coeff)
  then have algS: "algebraic_over (range to_wide) x" if "x \<in> S" for x
    using that by (auto simp: alg_closure_iff)
  obtain L where L: "finite_subfield_tower (range (to_wide :: 'a \<Rightarrow> 'a wide)) L"
    and KL: "range to_wide \<subseteq> L" and SL: "S \<subseteq> L"
    using exists_finite_subfield_tower [OF subfield_range_to_wide finS algS] by blast
  interpret T: finite_subfield_tower "range (to_wide :: 'a \<Rightarrow> 'a wide)" L by (rule L)
  have sfL: "Subfield L" by (rule T.ext.Subfield_axioms)
  have qL: "q \<in> poly_over L"
  proof (rule Subfield.poly_overI [OF sfL])
    fix i
    show "coeff q i \<in> L"
    proof (cases "i \<le> n")
      case True then show ?thesis using SL by (auto simp: S_def)
    next
      case False
      then show ?thesis using Subfield.zero_closed [OF sfL] by (simp add: coeff_eq_0 n_def)
    qed
  qed

  \<comment> \<open>Coordinates with respect to a basis of \<open>L\<close> over the base.\<close>
  obtain B coord where finB: "finite B" and BL: "B \<subseteq> L"
    and coordK: "\<And>x. x \<in> L \<Longrightarrow> (\<forall>b\<in>B. coord x b \<in> range to_wide)"
    and coordS: "\<And>x. x \<in> L \<Longrightarrow> x = (\<Sum>b\<in>B. coord x b * b)"
    using T.exists_coordinates by blast

  \<comment> \<open>Divide each power of the indeterminate by \<open>q\<close>.\<close>
  define N where "N \<equiv> n * card B"
  have "\<exists>s r. s \<in> poly_over L \<and> r \<in> poly_over L \<and> monom 1 i = s * q + r \<and> degree r < n" for i
    using T.ext.one_closed T.ext.poly_over_divmod_exists T.ext.poly_over_monom monic n_def npos qL
    by presburger
  then obtain s r where sr: "\<And>i. s i \<in> poly_over L \<and> r i \<in> poly_over L
                                  \<and> monom 1 i = s i * q + r i \<and> degree (r i) < n"
    by metis
  have rL: "r i \<in> poly_over L" and rdeg: "degree (r i) < n"
    and divid: "monom (1 :: 'a wide) i = s i * q + r i" for i
    using sr by blast+
  have rcoeffL: "coeff (r i) j \<in> L" for i j
    using rL by (simp add: Subfield.poly_over_coeff [OF sfL])

  \<comment> \<open>More unknowns than equations, so a nontrivial vanishing combination exists.\<close>
  define I where "I \<equiv> {..<n} \<times> B"
  define Amat where "Amat \<equiv> (\<lambda>(j, b) i. coord (coeff (r i) j) b)"
  have finI: "finite I" by (simp add: I_def finB)
  have cardI: "card I = N" by (simp add: I_def N_def card_cartesian_product)
  have "card I < card {..N}" by (simp add: cardI)
  moreover have "Amat e i \<in> range to_wide" if "e \<in> I" for e i
    using that coordK [OF rcoeffL] by (auto simp: Amat_def I_def)
  ultimately obtain c where cKall: "\<forall>j. c j \<in> range (to_wide :: 'a \<Rightarrow> 'a wide)"
    and cnz: "\<exists>j \<in> {..N}. c j \<noteq> 0"
    and sysall: "\<forall>e \<in> I. (\<Sum>i \<le> N. Amat e i * c i) = 0"
    using K.underdetermined_solution [OF finI, of "{..N}" Amat] by blast
  have cK: "c i \<in> range (to_wide :: 'a \<Rightarrow> 'a wide)" for i using cKall by blast
  have sys: "(\<Sum>i \<le> N. Amat e i * c i) = 0" if "e \<in> I" for e using sysall that by blast

  \<comment> \<open>The combination of remainders vanishes identically.\<close>
  define R where "R = (\<Sum>i \<le> N. smult (c i) (r i))"
  have Rdeg: "degree R < n"
    using rdeg R_def by (simp add: degree_sum_less npos)
  have Rcoeff: "coeff R j = 0" if j: "j < n" for j
  proof -
    have "coeff R j = (\<Sum>i \<le> N. c i * (\<Sum>b\<in>B. coord (coeff (r i) j) b * b))"
      using coordS [OF rcoeffL] by (simp add: R_def coeff_sum)
    also have "\<dots> = (\<Sum>i \<le> N. \<Sum>b\<in>B. c i * (coord (coeff (r i) j) b * b))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>b\<in>B. \<Sum>i \<le> N. c i * (coord (coeff (r i) j) b * b))"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>b\<in>B. (\<Sum>i \<le> N. Amat (j, b) i * c i) * b)"
    proof (rule sum.cong [OF refl])
      fix b assume "b \<in> B"
      have "(\<Sum>i \<le> N. c i * (coord (coeff (r i) j) b * b)) = (\<Sum>i \<le> N. Amat (j, b) i * c i * b)"
        by (simp add: Amat_def ac_simps)
      also have "\<dots> = (\<Sum>i \<le> N. Amat (j, b) i * c i) * b"
        by (simp add: sum_distrib_right)
      finally show "(\<Sum>i \<le> N. c i * (coord (coeff (r i) j) b * b))
                    = (\<Sum>i \<le> N. Amat (j, b) i * c i) * b" .
    qed
    also have "\<dots> = 0"
      using sys j by (intro sum.neutral) (simp add: I_def)
    finally show ?thesis .
  qed
  have "R = 0"
    using Rcoeff Rdeg by fastforce

  \<comment> \<open>Hence \<open>q\<close> divides a nonzero polynomial over the base field.\<close>
  define Q where "Q \<equiv> (\<Sum>i \<le> N. monom (c i) i)"
  have QK: "Q \<in> poly_over (range (to_wide :: 'a \<Rightarrow> 'a wide))"
    unfolding Q_def using cK by (auto intro!: K.poly_over_sum K.poly_over_monom)
  have coeffQ: "coeff Q i = c i" if "i \<le> N" for i
    using that by (simp add: Q_def coeff_sum)
  have Qnz: "Q \<noteq> 0" using cnz coeffQ by force
  have Qsplit: "Q = (\<Sum>i \<le> N. smult (c i) (s i)) * q + R"
  proof -
    have "monom (c i) i = smult (c i) (s i) * q + smult (c i) (r i)" for i
    proof -
      have "monom (c i) i = smult (c i) (monom 1 i)" by (simp add: smult_monom)
      also have "\<dots> = smult (c i) (s i) * q + smult (c i) (r i)"
        by (simp add: smult_monom divid [of i] smult_add_right mult_smult_left)
      finally show ?thesis .
    qed
    then have "Q = (\<Sum>i \<le> N. smult (c i) (s i) * q + smult (c i) (r i))"
      by (simp add: Q_def)
    also have "\<dots> = (\<Sum>i \<le> N. smult (c i) (s i)) * q + R"
      by (simp add: R_def sum.distrib sum_distrib_right)
    finally show ?thesis .
  qed
  with \<open>R = 0\<close> have qdvd: "q dvd Q" by auto

  \<comment> \<open>That polynomial splits in the closure, so \<open>q\<close> has a root there.\<close>
  obtain \<gamma> as where \<gamma>: "\<gamma> \<in> alg_closure" and as: "set as \<subseteq> alg_closure"
    and Qeq: "Q = [:\<gamma>:] * (\<Prod>a\<leftarrow>as. [:uminus a, 1:])"
    using alg_closure_splits [OF QK Qnz] by blast
  have "\<gamma> \<noteq> 0" using Qnz Qeq by auto
  then obtain z where z: "z \<in> set as" and "poly q z = 0"
    using dvd_split_imp_root [OF qdvd [unfolded Qeq]] npos by (auto simp: n_def)
  then show thesis
    using as roots by (blast intro: that)
qed

end
