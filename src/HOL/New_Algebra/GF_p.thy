section \<open>The prime fields \<open>GF(p) = \<int>/p\<int>\<close>\<close>

theory GF_p
  imports ZFact Ring_Theory Poly_Ring Poly_Ideal "HOL-Computational_Algebra.Primes"
begin

text \<open>For a prime @{term p}, the residue ring \<open>ZFact\<close> becomes a field:
  the only extra step over the general @{term "n > 0"} case is that every nonzero residue has a
  multiplicative inverse, which follows from Bézout's identity since @{term p} is prime.

  Carrier @{term "{0..<p}"} of @{typ nat}, arithmetic modulo @{term p}, arithmetic operations
  @{const gfp_add} and @{const gfp_mult} shared with the ring-level development in @{text ZFact}.\<close>

context
  fixes p :: nat
  assumes prime_p: "prime p"
begin

lemma p_gt_1: "p > 1" using prime_p by (simp add: prime_nat_iff)
lemma p_gt_0: "p > 0" using p_gt_1 by simp

text \<open>\<^emph>\<open>Inverses.\<close>  For @{term "a \<in> {1..<p}"}, @{term a} is coprime to the prime @{term p}, so
  Bézout gives integers with @{text "u\<cdot>a + v\<cdot>p = 1"}; reducing @{text "u"} modulo @{term p}
  yields a multiplicative inverse of @{term a}.\<close>
lemma gfp_inverse_exists:
  assumes a: "a \<in> {0..<p}" and anz: "a \<noteq> 0"
  shows "\<exists>b\<in>{0..<p}. gfp_mult p a b = 1"
proof -
  have ap: "a < p" and a1: "a \<ge> 1" using a anz by auto
  \<comment> \<open>@{term p} prime and @{term "a < p"}, @{term "a \<noteq> 0"}, so @{term p} does not divide @{term a}.\<close>
  have ndvd: "\<not> p dvd a" using ap anz by (simp add: nat_dvd_not_less)
  then have "gcd a p = 1"
    by (metis gcd_unique prime_nat_iff prime_p)
  then have cop: "coprime (int a) (int p)" by (simp add: coprime_iff_gcd_eq_1)
  \<comment> \<open>Bézout: @{text "u\<cdot>a + v\<cdot>p = 1"} for some integers @{text u}, @{text v}.\<close>
  obtain u v :: int where uv: "u * int a + v * int p = 1"
    using cop bezout_int by (metis coprime_imp_gcd_eq_1)
  define b where "b = nat (u mod int p)"
  have brange: "b \<in> {0..<p}" using p_gt_0 by (simp add: b_def) (simp add: nat_less_iff)
  \<comment> \<open>Then @{text "a\<cdot>b \<equiv> a\<cdot>u \<equiv> 1 (mod p)"}.\<close>
  have "int (gfp_mult p a b) = (int a * u) mod int p"
    by (simp add: b_def gfp_mult_def mod_mult_right_eq of_nat_mod p_gt_0)
  also have "\<dots> = (1 - v * int p + v * int p) mod int p"
    by (metis diff_add_cancel mod_mult_self1 mult.commute uv)
  also have "\<dots> = 1" using p_gt_1 by simp
  finally show ?thesis using brange
    using of_nat_eq_1_iff by blast
qed

lemma gfp_field: "Field {0..<p} (gfp_add p) (gfp_mult p) 0 1"
proof -
  interpret R: commutative_ring "{0..<p}" "gfp_add p" "gfp_mult p" 0 1
    using zfact_commutative_ring[OF p_gt_1] .
  show ?thesis
  proof
    show "(1::nat) \<noteq> 0" using p_gt_1 by simp
    show "\<And>a. a \<in> {0..<p} \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> R.multiplicative.invertible a"
      by (metis R.multiplicative.invertibleI gfp_inverse_exists gfp_mult_def mult.commute)
  qed
qed

text \<open>The prime field has exactly @{term p} elements.\<close>
lemma card_gfp: "card {0..<p} = p" by simp

end

text \<open>Hence prime fields of every prime order exist --- in particular the @{locale Field} locale is
  non-vacuous for every prime cardinality.\<close>

subsection \<open>The two-element field as a non-vacuity witness\<close>

text \<open>
  A concrete field with two elements, witnessing that the @{locale Field} and
  @{locale integral_domain} locales (and hence the abstract @{typ "'a ring"} type as a
  field) are non-vacuous.  Carrier @{term "{0, 1}"} of @{typ nat}.
\<close>

definition gf2_add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "gf2_add x y \<equiv> (x + y) mod 2"

definition gf2_mult :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "gf2_mult x y \<equiv> (x * y) mod 2"

text \<open>Enumeration helper: membership in the two-element carrier.\<close>
lemma gf2_cases: "x \<in> {0, 1::nat} \<Longrightarrow> x = 0 \<or> x = 1" by auto

lemma gf2_add_simps [simp]:
  "gf2_add 0 0 = 0" "gf2_add 0 1 = 1" "gf2_add 1 0 = 1" "gf2_add 1 1 = 0"
  by (simp_all add: gf2_add_def)

lemma gf2_mult_simps [simp]:
  "gf2_mult 0 0 = 0" "gf2_mult 0 1 = 0" "gf2_mult 1 0 = 0" "gf2_mult 1 1 = 1"
  by (simp_all add: gf2_mult_def)

lemma gf2_add_closed [simp]: "\<lbrakk> x \<in> {0,1::nat}; y \<in> {0,1} \<rbrakk> \<Longrightarrow> gf2_add x y \<in> {0,1}"
  by (auto simp: gf2_add_def)

lemma gf2_mult_closed [simp]: "\<lbrakk> x \<in> {0,1::nat}; y \<in> {0,1} \<rbrakk> \<Longrightarrow> gf2_mult x y \<in> {0,1}"
  by (auto simp: gf2_mult_def)

text \<open>The additive part is a group (each element is its own inverse), via @{thm [source] GroupI}.\<close>
lemma gf2_add_group: "Group {0, 1::nat} gf2_add 0"
proof (rule GroupI)
  fix u :: nat assume u: "u \<in> {0,1}"
  then have "gf2_add u u = 0" by (auto simp: gf2_add_def)
  with u show "\<exists>v \<in> {0,1::nat}. gf2_add u v = 0 \<and> gf2_add v u = 0" by blast
qed (auto simp: gf2_add_def)

lemma gf2_add_commutative_monoid: "commutative_monoid {0, 1::nat} gf2_add 0"
  by unfold_locales (auto simp: gf2_add_def)

text \<open>The additive part is therefore an abelian group.\<close>
lemma gf2_additive: "Abelian_Group {0, 1::nat} gf2_add 0"
  by (rule Abelian_Group.intro [OF gf2_add_group gf2_add_commutative_monoid])

text \<open>The multiplicative part is a commutative monoid.\<close>
lemma gf2_multiplicative: "commutative_monoid {0, 1::nat} gf2_mult 1"
  by unfold_locales (auto simp: gf2_mult_def)

lemma gf2_ring: "Ring {0, 1::nat} gf2_add gf2_mult 0 1"
proof (rule Ring.intro)
  show "Abelian_Group {0,1::nat} gf2_add 0" by (rule gf2_additive)
  show "Monoid {0,1::nat} gf2_mult 1" by (rule commutative_monoid.axioms(1) [OF gf2_multiplicative])
  show "Ring_axioms {0,1::nat} gf2_add gf2_mult" by unfold_locales (auto simp: gf2_add_def gf2_mult_def)
qed

lemma gf2_commutative_ring: "commutative_ring {0, 1::nat} gf2_add gf2_mult 0 1"
  by (rule commutative_ring.intro [OF gf2_ring gf2_multiplicative])

text \<open>The two-element field.  This is the single witness the downstream constructions consume (via
  \<open>interpretation \<dots> by (rule gf2_field)\<close> in \<open>GF4\<close> and \<open>GF8\<close>); it also witnesses non-vacuity of the
  @{locale Field}, @{locale integral_domain} and @{locale commutative_ring} locales, the last two by
  the locale hierarchy (a @{locale Field} is in particular an @{locale integral_domain}).\<close>
lemma gf2_field: "Field {0, 1::nat} gf2_add gf2_mult 0 1"
proof -
  interpret R: commutative_ring "{0,1::nat}" gf2_add gf2_mult 0 1 by (rule gf2_commutative_ring)
  show ?thesis
  proof 
    show "(1::nat) \<noteq> 0" by simp
  next
    fix a :: nat assume a: "a \<in> {0,1}" "a \<noteq> 0"
    then have a1: "a = 1" by auto
    then have "gf2_mult a a = 1" by (simp add: gf2_mult_def)
    then show "R.multiplicative.invertible a"
      using a1 by (intro R.multiplicative.invertibleI [where v = a]) auto
  qed
qed

subsection \<open>The two-element field with polynomial machinery\<close>

interpretation GF2: Field "{0, 1::nat}" gf2_add gf2_mult 0 1
  by (rule gf2_field)

lemma GF2_poly_const_carrier [simp, intro]: "GF2.poly_const 1 \<in> GF2.poly_carrier"
  by (rule GF2.poly_const_closed) simp

lemma GF2_monom_carrier [simp, intro]: "GF2.monom 1 n \<in> GF2.poly_carrier"
  by (rule GF2.monom_closed) simp


subsection \<open>The 3-element prime field with polynomial machinery\<close>

text \<open>A single, canonical interpretation of the @{locale Field} locale on \<open>GF(3)\<close>.\<close>

interpretation GF3: Field "{0..<3::nat}" "gfp_add 3" "gfp_mult 3" 0 1
  using gfp_field[of 3] by simp

lemma GF3_poly_const_carrier [simp, intro]: "GF3.poly_const 1 \<in> GF3.poly_carrier"
  by (rule GF3.poly_const_closed) simp

lemma GF3_monom_carrier [simp, intro]: "GF3.monom 1 n \<in> GF3.poly_carrier"
  by (rule GF3.monom_closed) simp

text \<open>An end-to-end witness for the carrier-set field machinery, over a non-binary prime
  field: the polynomial \<open>X\<^sup>2 + 1\<close> is irreducible over \<open>GF(3)\<close> (it has no root there, as \<open>-1\<close> is not
  a square modulo 3), so by Kronecker's theorem the quotient \<open>GF(3)[X] / (X\<^sup>2 + 1)\<close> is a field, and
  by @{thm [source] Field.card_poly_quotient} it has \<open>3\<^sup>2 = 9\<close> elements --- the field \<open>GF(9)\<close>.\<close>

text \<open>The witness polynomial \<open>\<Psi> = X\<^sup>2 + 1\<close> over \<open>GF(3)\<close>.\<close>
definition Psi :: "nat \<Rightarrow> nat"
  where "Psi \<equiv> GF3.poly_add (GF3.monom 1 2) (GF3.poly_const 1)"

lemma Psi_coeff: "Psi i = (if i = 0 \<or> i = 2 then 1 else 0)"
  by (simp add: Psi_def GF3.poly_add_def GF3.monom_def GF3.poly_const_def gfp_add_def)

lemma Psi_closed: "Psi \<in> GF3.poly_carrier"
  unfolding Psi_def by (intro GF3.poly_add_closed GF3_monom_carrier GF3_poly_const_carrier)

text \<open>@{term Psi} has degree exactly @{text 2}.\<close>
lemma degree_Psi: "GF3.degree Psi = 2"
proof (rule antisym)
  show "GF3.degree Psi \<le> 2"
    by (rule GF3.degree_leI[OF Psi_closed]) (simp add: Psi_coeff)
  have "Psi 2 \<noteq> 0" by (simp add: Psi_coeff)
  moreover have "finite {i. Psi i \<noteq> 0}" using Psi_closed by (rule GF3.poly_carrier_finite)
  ultimately show "2 \<le> GF3.degree Psi"
    by (simp add: GF3.degree_def) (metis (mono_tags, lifting) Max_ge empty_iff mem_Collect_eq)
qed

text \<open>@{term Psi} has no root in @{term "{0..<3::nat}"}: \<open>\<alpha>\<^sup>2 + 1\<close> is @{text 1}, @{text 2}, @{text 2}
  at \<open>\<alpha> = 0, 1, 2\<close> respectively --- never @{text 0}.\<close>
lemma Psi_no_root: "\<alpha> \<in> {0..<3::nat} \<Longrightarrow> GF3.eval \<alpha> Psi \<noteq> 0"
proof -
  assume a: "\<alpha> \<in> {0..<3::nat}"
  \<comment> \<open>Evaluate term by term.\<close>
  have "GF3.eval \<alpha> Psi = gfp_add 3 (GF3.eval \<alpha> (GF3.monom 1 2)) (GF3.eval \<alpha> (GF3.poly_const 1))"
    unfolding Psi_def by (rule GF3.eval_add[OF GF3_monom_carrier GF3_poly_const_carrier a])
  also have "GF3.eval \<alpha> (GF3.monom 1 2) = gfp_mult 3 1 (GF3.rpow \<alpha> 2)"
    using GF3.eval_monom a by blast
  also have "GF3.eval \<alpha> (GF3.poly_const 1) = 1"
    using GF3.eval_const a by blast
  finally have ev: "GF3.eval \<alpha> Psi = gfp_add 3 (gfp_mult 3 1 (GF3.rpow \<alpha> 2)) 1" .
  \<comment> \<open>Compute the square: @{text "\<alpha>\<^sup>2 = \<alpha>\<cdot>\<alpha>"}.\<close>
  have r2: "GF3.rpow \<alpha> 2 = gfp_mult 3 \<alpha> (gfp_mult 3 \<alpha> 1)"
    unfolding GF3.rpow_def by (simp add: eval_nat_numeral)
  have val: "GF3.eval \<alpha> Psi = Suc (\<alpha> * \<alpha> mod 3) mod 3"
    using ev r2 by (simp add: gfp_add_def gfp_mult_def mod_mult_right_eq mod_mult_left_eq)
  \<comment> \<open>Check the three residues @{text "\<alpha> = 0, 1, 2"} explicitly.\<close>
  have "\<alpha> = 0 \<or> \<alpha> = 1 \<or> \<alpha> = 2" using a by auto
  then show "GF3.eval \<alpha> Psi \<noteq> 0" using val by auto
qed

text \<open>Therefore @{term Psi} is irreducible over @{text "GF(3)"}.\<close>
theorem Psi_irreducible: "GF3.poly_irreducible Psi"
  using GF3.degree23_no_root_irreducible[OF Psi_closed] degree_Psi Psi_no_root by blast

subsection \<open>The four-element field \<open>GF(4)\<close> via Kronecker's construction\<close>

text \<open>The polynomial \<open>X\<^sup>2 + X + 1\<close> is irreducible over the two-element field \<open>GF(2)\<close> (it has no root there), 
  so by Kronecker's theorem (@{thm [source] Field.poly_quotient_field}) the quotient
  \<open>GF(2)[X] / (X\<^sup>2 + X + 1)\<close> is a field --- the four-element field \<open>GF(4)\<close>.\<close>

text \<open>The witness polynomial \<open>\<Phi> = X\<^sup>2 + X + 1\<close> over \<open>GF(2)\<close>.\<close>
definition Phi :: "nat \<Rightarrow> nat"
  where "Phi \<equiv> GF2.poly_add (GF2.poly_add (GF2.monom 1 2) (GF2.monom 1 1)) (GF2.poly_const 1)"

text \<open>Its coefficients: @{text 1} at degrees @{text 0}, @{text 1}, @{text 2}, and @{text 0} above.\<close>
lemma Phi_coeff: "Phi i = (if i \<le> 2 then 1 else 0)"
  by (simp add: Phi_def GF2.poly_add_def GF2.monom_def GF2.poly_const_def gf2_add_def)

lemma Phi_closed: "Phi \<in> GF2.poly_carrier"
  unfolding Phi_def by (intro GF2.poly_add_closed GF2_monom_carrier GF2_poly_const_carrier)

text \<open>@{term Phi} has degree exactly @{text 2}.\<close>
lemma degree_Phi: "GF2.degree Phi = 2"
proof (rule antisym)
  show "GF2.degree Phi \<le> 2"
    using GF2.degree_le_iff Phi_closed Phi_coeff by auto
  have "finite {i. Phi i \<noteq> 0}" using Phi_closed by (rule GF2.poly_carrier_finite)
  then show "2 \<le> GF2.degree Phi"
    using GF2.coeff_gt_degree Phi_closed Phi_coeff linorder_not_le by fastforce
qed

text \<open>@{term Phi} has no root in @{term "{0, 1::nat}"}: both candidate values evaluate to
  @{text 1}, since \<open>X\<^sup>2 + X + 1\<close> at @{text 0} is @{text 1} and at @{text 1} is
  \<open>1 + 1 + 1 = 1\<close> modulo 2.\<close>
lemma Phi_no_root:
  assumes a: "\<alpha> \<in> {0, 1::nat}"
  shows "GF2.eval \<alpha> Phi \<noteq> 0"
proof -
  have sum2: "GF2.poly_add (GF2.monom 1 2) (GF2.monom 1 1) \<in> GF2.poly_carrier"
    by (intro GF2.poly_add_closed GF2_monom_carrier)
  \<comment> \<open>Evaluate term by term, using additivity and @{thm [source] GF2.eval_monom}.\<close>
  have "GF2.eval \<alpha> Phi
        = gf2_add (GF2.eval \<alpha> (GF2.poly_add (GF2.monom 1 2) (GF2.monom 1 1))) (GF2.eval \<alpha> (GF2.poly_const 1))"
    unfolding Phi_def using GF2.eval_add[OF sum2 GF2_poly_const_carrier assms] .
  also have "\<dots> = gf2_add (gf2_add (gf2_mult 1 (GF2.rpow \<alpha> 2)) (gf2_mult 1 (GF2.rpow \<alpha> 1))) 1"
    using GF2.eval_add[OF GF2_monom_carrier GF2_monom_carrier assms]
          GF2.eval_const[OF assms] GF2.eval_monom[OF _ assms] by simp
  finally have "GF2.eval \<alpha> Phi
        = gf2_add (gf2_add (gf2_mult 1 (GF2.rpow \<alpha> 2)) (gf2_mult 1 (GF2.rpow \<alpha> 1))) 1" .
  \<comment> \<open>Compute the powers: @{text "\<alpha>\<^sup>2 = \<alpha>\<cdot>\<alpha>"}, @{text "\<alpha>\<^sup>1 = \<alpha>"}.\<close>
  then show "GF2.eval \<alpha> Phi \<noteq> 0"
    using gf2_cases[OF a] gf2_add_simps(4) gf2_mult_simps(4) 
    unfolding GF2.rpow_def by (fastforce simp add: eval_nat_numeral)
qed

text \<open>Therefore @{term Phi} is irreducible over @{text "GF(2)"}.\<close>
theorem Phi_irreducible: "GF2.poly_irreducible Phi"
  using GF2.degree23_no_root_irreducible[OF Phi_closed] degree_Phi Phi_no_root by blast

text \<open>\<^emph>\<open>Kronecker.\<close>  The principal ideal @{text "(\<Phi>)"} is maximal in @{text "GF(2)[X]"}, so the
  quotient @{text "GF(2)[X]/(\<Phi>)"} is a field --- a four-element field, @{text "GF(4)"}.\<close>
theorem GF4_is_field:
  "ideal_in_comm_ring (GF2.poly_pideal Phi) GF2.poly_carrier GF2.poly_add GF2.poly_mult GF2.poly_zero GF2.poly_one
   \<and> Ideal.maximal_ideal (GF2.poly_pideal Phi) GF2.poly_carrier GF2.poly_add GF2.poly_mult GF2.poly_zero GF2.poly_one"
  using GF2.poly_quotient_field[OF Phi_irreducible] .

subsection \<open>The eight-element field \<open>GF(8)\<close> via Kronecker's construction\<close>

text \<open>A cubic witness for the carrier-set field machinery: the polynomial \<open>X\<^sup>3 + X + 1\<close> is
  irreducible over \<open>GF(2)\<close> (degree 3 with no root), so by Kronecker's theorem the quotient
  \<open>GF(2)[X] / (X\<^sup>3 + X + 1)\<close> is a field, and by @{thm [source] Field.card_poly_quotient} it has
  \<open>2\<^sup>3 = 8\<close> elements --- the field \<open>GF(8)\<close>.\<close>

text \<open>The witness polynomial \<open>\<Theta> = X\<^sup>3 + X + 1\<close> over \<open>GF(2)\<close>.\<close>
definition Theta :: "nat \<Rightarrow> nat"
  where "Theta = GF2.poly_add (GF2.poly_add (GF2.monom 1 3) (GF2.monom 1 1)) (GF2.poly_const 1)"

lemma Theta_coeff: "Theta i = (if i = 0 \<or> i = 1 \<or> i = 3 then 1 else 0)"
  by (simp add: Theta_def GF2.poly_add_def GF2.monom_def GF2.poly_const_def gf2_add_def)

lemma Theta_closed: "Theta \<in> GF2.poly_carrier"
  unfolding Theta_def by (intro GF2.poly_add_closed GF2_monom_carrier GF2_poly_const_carrier)

text \<open>@{term Theta} has degree exactly @{text 3}.\<close>
lemma degree_Theta: "GF2.degree Theta = 3"
proof (rule antisym)
  show "GF2.degree Theta \<le> 3"
    by (rule GF2.degree_leI[OF Theta_closed]) (simp add: Theta_coeff)
  have "Theta 3 \<noteq> 0" by (simp add: Theta_coeff)
  moreover have "finite {i. Theta i \<noteq> 0}" using Theta_closed by (rule GF2.poly_carrier_finite)
  ultimately show "3 \<le> GF2.degree Theta"
    by (simp add: GF2.degree_def) (metis (mono_tags, lifting) Max_ge empty_iff mem_Collect_eq)
qed

text \<open>@{term Theta} has no root in @{term "{0, 1::nat}"}: \<open>\<alpha>\<^sup>3 + \<alpha> + 1\<close> is @{text 1} at both
  @{text 0} and @{text 1} (modulo 2).\<close>
lemma Theta_no_root: "\<alpha> \<in> {0, 1::nat} \<Longrightarrow> GF2.eval \<alpha> Theta \<noteq> 0"
proof -
  assume a: "\<alpha> \<in> {0, 1::nat}"
  have sum2: "GF2.poly_add (GF2.monom 1 3) (GF2.monom 1 1) \<in> GF2.poly_carrier"
    by (intro GF2.poly_add_closed GF2_monom_carrier)
  \<comment> \<open>Evaluate term by term.\<close>
  have "GF2.eval \<alpha> Theta
        = gf2_add (GF2.eval \<alpha> (GF2.poly_add (GF2.monom 1 3) (GF2.monom 1 1))) (GF2.eval \<alpha> (GF2.poly_const 1))"
    unfolding Theta_def
    using GF2.eval_add[OF sum2 GF2_poly_const_carrier a] .
  also have "GF2.eval \<alpha> (GF2.poly_add (GF2.monom 1 3) (GF2.monom 1 1))
             = gf2_add (GF2.eval \<alpha> (GF2.monom 1 3)) (GF2.eval \<alpha> (GF2.monom 1 1))"
    using GF2.eval_add a by blast
  also have "GF2.eval \<alpha> (GF2.monom 1 3) = gf2_mult 1 (GF2.rpow \<alpha> 3)"
    using GF2.eval_monom a by blast
  also have "GF2.eval \<alpha> (GF2.monom 1 1) = gf2_mult 1 (GF2.rpow \<alpha> 1)"
    using GF2.eval_monom a by blast
  also have "GF2.eval \<alpha> (GF2.poly_const 1) = 1"
    using GF2.eval_const a by blast
  finally have ev: "GF2.eval \<alpha> Theta
        = gf2_add (gf2_add (gf2_mult 1 (GF2.rpow \<alpha> 3)) (gf2_mult 1 (GF2.rpow \<alpha> 1))) 1" .
  then have "GF2.eval \<alpha> Theta = gf2_add (gf2_add (gf2_mult 1 (gf2_mult \<alpha> (gf2_mult \<alpha> (gf2_mult \<alpha> 1))))
                                          (gf2_mult 1 (gf2_mult \<alpha> 1))) 1"
    unfolding GF2.rpow_def by (simp add: eval_nat_numeral)
  then show "GF2.eval \<alpha> Theta \<noteq> 0"
    using gf2_cases[OF a] by (auto simp: gf2_add_def gf2_mult_def)
qed

text \<open>Therefore @{term Theta} is irreducible over @{text "GF(2)"}.\<close>
theorem Theta_irreducible: "GF2.poly_irreducible Theta"
  using GF2.degree23_no_root_irreducible[OF Theta_closed] degree_Theta Theta_no_root
  by blast

text \<open>\<^emph>\<open>Kronecker.\<close>  The quotient @{text "GF(2)[X]/(\<Theta>)"} is a field with \<open>2\<^sup>3 = 8\<close> elements.\<close>
theorem GF8_is_field:
  "ideal_in_comm_ring (GF2.poly_pideal Theta) GF2.poly_carrier (GF2.poly_add) (GF2.poly_mult) GF2.poly_zero GF2.poly_one
   \<and> Ideal.maximal_ideal (GF2.poly_pideal Theta) GF2.poly_carrier (GF2.poly_add) (GF2.poly_mult) GF2.poly_zero GF2.poly_one"
  using GF2.poly_quotient_field[OF Theta_irreducible] .

theorem card_GF8:
  "card (Ideal.quotient_set (GF2.poly_pideal Theta) GF2.poly_carrier (GF2.poly_add) GF2.poly_zero) = 8"
proof -
  have pnz: "Theta \<noteq> GF2.poly_zero"
    using degree_Theta by (metis GF2.degree_zero zero_neq_numeral)
  have "card (Ideal.quotient_set (GF2.poly_pideal Theta) GF2.poly_carrier (GF2.poly_add) GF2.poly_zero)
        = card {0, 1::nat} ^ GF2.degree Theta"
    by (rule GF2.card_poly_quotient[OF _ Theta_closed pnz]) simp
  also have "\<dots> = 8" by (simp add: degree_Theta eval_nat_numeral)
  finally show ?thesis .
qed

subsection \<open>The nine-element field \<open>GF(9)\<close> via Kronecker's construction\<close>

text \<open>\<^emph>\<open>Kronecker.\<close>  The quotient @{text "GF(3)[X]/(\<Psi>)"} is a field with \<open>3\<^sup>2 = 9\<close> elements.\<close>
theorem GF9_is_field:
  "ideal_in_comm_ring (GF3.poly_pideal Psi) GF3.poly_carrier (GF3.poly_add) (GF3.poly_mult) GF3.poly_zero GF3.poly_one
   \<and> Ideal.maximal_ideal (GF3.poly_pideal Psi) GF3.poly_carrier (GF3.poly_add) (GF3.poly_mult) GF3.poly_zero GF3.poly_one"
  using GF3.poly_quotient_field[OF Psi_irreducible] .

theorem card_GF9:
  "card (Ideal.quotient_set (GF3.poly_pideal Psi) GF3.poly_carrier (GF3.poly_add) GF3.poly_zero) = 9"
proof -
  have pnz: "Psi \<noteq> GF3.poly_zero"
    using degree_Psi by (metis GF3.degree_zero zero_neq_numeral)
  have "card (Ideal.quotient_set (GF3.poly_pideal Psi) GF3.poly_carrier (GF3.poly_add) GF3.poly_zero)
        = card {0..<3::nat} ^ GF3.degree Psi"
    by (rule GF3.card_poly_quotient[OF _ Psi_closed pnz]) simp
  also have "\<dots> = 9" by (simp add: degree_Psi)
  finally show ?thesis .
qed

end
