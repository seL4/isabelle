section \<open>Linking the carrier-set polynomial ring to Isabelle's polynomial type\<close>

theory Poly_Typeclass
  imports Poly_Ring Field_Typeclass "HOL-Computational_Algebra.Polynomial"
begin

text \<open>
  \<open>Poly_Ring\<close> represents a polynomial as a finite-support function
  @{typ "nat \<Rightarrow> 'a"} with coefficients in a carrier @{term R}, which is exactly the representing
  set of HOL's @{typ "'a poly"} once the carrier is the whole type.  So for a type-class field the
  two developments describe the same objects, and the dictionary between them is little more than
  @{const Abs_poly}: this theory writes it out, so that the ring-theoretic results proved for
  @{term poly_carrier} --- irreducibility, division, unique factorisation --- become available to
  the extension and Galois theory, which is phrased throughout in terms of @{typ "'a poly"}.
\<close>

subsection \<open>Finite composites are sums and products\<close>

text \<open>The carrier-set @{const commutative_monoid.fincomp} at the whole type is HOL's
  @{const sum} or @{const prod}; the guard @{term commutative_monoid.M_ify} in its definition is
  vacuous there.\<close>

lemma fincomp_TC_sum:
  "commutative_monoid.fincomp (UNIV :: 'a :: comm_monoid_add set) (+) 0 f A = sum f A"
proof -
  interpret M: commutative_monoid "UNIV :: 'a set" "(+)" 0
    by unfold_locales (auto simp: ac_simps)
  show ?thesis
    by (induct A rule: infinite_finite_induct) auto
qed

lemma fincomp_TC_prod:
  "commutative_monoid.fincomp (UNIV :: 'a :: comm_monoid_mult set) (*) 1 f A = prod f A"
proof -
  interpret M: commutative_monoid "UNIV :: 'a set" "(*)" 1
    by unfold_locales (auto simp: ac_simps)
  show ?thesis
    by (induct A rule: infinite_finite_induct) auto
qed


subsection \<open>The two representations of a polynomial\<close>

text \<open>A finite-support function read as a polynomial.  Off the finite-support functions the value
  is arbitrary; @{term 0} is chosen so that the map is total.\<close>

definition poly_of_fun :: "(nat \<Rightarrow> 'a :: zero) \<Rightarrow> 'a poly"
  where "poly_of_fun p = (if finite {i. p i \<noteq> 0} then Abs_poly p else 0)"

lemma coeff_poly_of_fun [simp]:
  "finite {i. p i \<noteq> 0} \<Longrightarrow> Polynomial.coeff (poly_of_fun p) = p"
  by (simp add: poly_of_fun_def Abs_poly_inverse MOST_iff_cofinite)

lemma finite_support_coeff [simp, intro]: "finite {i. Polynomial.coeff p i \<noteq> 0}"
  using MOST_coeff_eq_0 [of p] by (simp add: MOST_iff_cofinite)

lemma poly_of_fun_coeff [simp]: "poly_of_fun (Polynomial.coeff p) = p"
  by (simp add: poly_of_fun_def coeff_inverse)

lemma inj_on_poly_of_fun: "inj_on poly_of_fun {p. finite {i. p i \<noteq> 0}}"
  by (rule inj_onI) (metis coeff_poly_of_fun mem_Collect_eq)


subsection \<open>The dictionary at a type-class field\<close>

text \<open>Fixing the carrier to be the whole type turns every constant of \<open>Poly_Ring\<close>
  into an operation on finite-support functions over a type-class field; the locale below exists only
  to make those constants available unqualified.\<close>

locale poly_TC = Field "UNIV :: 'a :: field set" "(+)" "(*)" "0" "1"

interpretation poly_TC
  by (simp add: poly_TC_def field_TC.Field_axioms)

context poly_TC
begin

text \<open>Membership of the carrier is finite support alone: every coefficient lies in the carrier
  because the carrier is everything.\<close>
lemma poly_carrier_TC: "poly_carrier = {p :: nat \<Rightarrow> 'a. finite {i. p i \<noteq> 0}}"
  by (auto simp: poly_carrier_def)

lemma poly_carrier_iff: "p \<in> poly_carrier \<longleftrightarrow> finite {i. p i \<noteq> 0}"
  by (simp add: poly_carrier_TC)

lemma coeff_in_poly_carrier [simp, intro]: "Polynomial.coeff q \<in> poly_carrier"
  by (simp add: poly_carrier_iff)

lemma coeff_poly_of_fun_carrier [simp]:
  "p \<in> poly_carrier \<Longrightarrow> Polynomial.coeff (poly_of_fun p) = p"
  by (simp add: poly_carrier_iff)

text \<open>The additive inverse supplied by the group structure is HOL's, though the two are distinct
  constants and print alike; without this the coefficientwise proofs below cannot close.\<close>
lemma additive_inverse_TC [simp]: "additive.inverse a = uminus a"
  by (intro additive.inverse_equality) simp_all

text \<open>On the carrier the dictionary is injective, so an identity between carrier-set polynomials
  may be checked in @{typ "'a poly"} and conversely.\<close>
lemma poly_of_fun_eq_iff [simp]:
  "\<lbrakk> p \<in> poly_carrier; q \<in> poly_carrier \<rbrakk> \<Longrightarrow> poly_of_fun p = poly_of_fun q \<longleftrightarrow> p = q"
  by (metis coeff_poly_of_fun_carrier)


subsection \<open>The ring operations correspond\<close>

lemma poly_of_fun_zero [simp]: "poly_of_fun poly_zero = 0"
  by (simp add: poly_zero_def poly_of_fun_def zero_poly_def)

lemma poly_of_fun_one [simp]: "poly_of_fun poly_one = 1"
proof -
  have "finite {i. poly_one i \<noteq> (0::'a)}"
    using poly_one_closed by (simp add: poly_carrier_iff)
  then show ?thesis
    by (intro poly_eqI) (simp add: poly_one_def)
qed

lemma poly_of_fun_add [simp]:
  assumes "p \<in> poly_carrier" and "q \<in> poly_carrier"
  shows "poly_of_fun (poly_add p q) = poly_of_fun p + poly_of_fun q"
proof -
  have "poly_add p q \<in> poly_carrier"
    using assms by (rule poly_add_closed)
  with assms show ?thesis
    by (intro poly_eqI) (simp add: poly_add_def)
qed

lemma poly_of_fun_neg [simp]:
  assumes "p \<in> poly_carrier"
  shows "poly_of_fun (poly_neg p) = - poly_of_fun p"
proof -
  have "poly_neg p \<in> poly_carrier"
    using assms by (rule poly_neg_closed)
  with assms show ?thesis
    by (intro poly_eqI) (simp add: poly_neg_def)
qed

text \<open>The convolution defining @{const poly_mult} is literally HOL's @{thm [source] coeff_mult},
  once the finite composite is read as a sum.\<close>
lemma poly_of_fun_mult [simp]:
  assumes "p \<in> poly_carrier" and "q \<in> poly_carrier"
  shows "poly_of_fun (poly_mult p q) = poly_of_fun p * poly_of_fun q"
proof -
  have "poly_mult p q \<in> poly_carrier"
    using assms by (rule poly_mult_closed)
  with assms show ?thesis
    by (intro poly_eqI) (simp add: poly_mult_def coeff_mult fincomp_TC_sum)
qed


subsection \<open>Constants, the indeterminate, degree and evaluation\<close>

lemma poly_of_fun_const [simp]: "poly_of_fun (poly_const c) = [:c:]"
proof -
  have "poly_const c \<in> poly_carrier"
    by (rule poly_const_closed) simp
  then show ?thesis
    by (intro poly_eqI) (auto simp: poly_const_def poly_carrier_iff coeff_pCons split: nat.split)
qed

lemma poly_of_fun_monom [simp]: "poly_of_fun (monom c k) = Polynomial.monom c k"
proof -
  have "monom c k \<in> poly_carrier"
    by (rule monom_closed) simp
  then show ?thesis
    by (intro poly_eqI) (simp add: monom_def poly_carrier_iff)
qed

lemma poly_of_fun_var [simp]: "poly_of_fun var = [:0, 1:]"
proof -
  have "var \<in> poly_carrier"
    by (rule var_closed)
  then show ?thesis
    by (simp add: var_def monom_altdef)
qed

text \<open>Both notions of degree are pinned by the same two inequalities: no coefficient above the
  degree, and a nonzero coefficient at it.\<close>
lemma degree_poly_of_fun [simp]:
  assumes p: "p \<in> poly_carrier"
  shows "Polynomial.degree (poly_of_fun p) = degree p"
proof (cases "p = poly_zero")
  case True then show ?thesis by simp
next
  case False
  then have ne: "{i. p i \<noteq> 0} \<noteq> {}" by (auto simp: poly_zero_def)
  have fin: "finite {i. p i \<noteq> 0}" using p by (simp add: poly_carrier_iff)
  have c: "Polynomial.coeff (poly_of_fun p) = p" using p by simp
  have "Polynomial.degree (poly_of_fun p) \<le> degree p"
    using p c by (intro degree_le) (auto dest: coeff_gt_degree)
  moreover
  have "p (degree p) \<noteq> 0"
    using Max_in [OF fin ne] ne by (simp add: degree_def)
  then have "degree p \<le> Polynomial.degree (poly_of_fun p)"
    using c by (metis le_degree)
  ultimately show ?thesis by simp
qed

text \<open>Powers in the multiplicative monoid of the type are ordinary powers.\<close>
lemma rpow_TC [simp]: "rpow a n = a ^ n"
  by (induct n) simp_all

text \<open>Evaluation matches @{thm [source] poly_altdef}, the coefficientwise form of @{const poly}.\<close>
lemma poly_poly_of_fun [simp]:
  assumes "p \<in> poly_carrier"
  shows "Polynomial.poly (poly_of_fun p) x = eval x p"
  using assms by (simp add: poly_altdef eval_def fincomp_TC_sum)


subsection \<open>Splitting into linear factors\<close>

lemma poly_of_fun_root_factor [simp]: "poly_of_fun (root_factor a) = [:uminus a, 1:]"
proof -
  have "poly_of_fun (root_factor a) = poly_of_fun var + (- poly_of_fun (poly_const a))"
    unfolding root_factor_def
    by (simp add: var_closed poly_const_closed poly_neg_closed)
  also have "\<dots> = [:uminus a, 1:]" by simp
  finally show ?thesis .
qed

lemma poly_of_fun_poly_prod:
  assumes "\<And>f. f \<in> set fs \<Longrightarrow> f \<in> poly_carrier"
  shows "poly_of_fun (poly_prod fs) = (\<Prod>f\<leftarrow>fs. poly_of_fun f)"
  using assms by (induct fs) (auto simp: poly_prod_closed)

text \<open>The witnessing product, translated once for both directions of the theorem below.\<close>
lemma poly_of_fun_split_form:
  "poly_of_fun (poly_mult (poly_const c) (poly_prod (List.map root_factor as)))
     = [:c:] * (\<Prod>a\<leftarrow>as. [:uminus a, 1:])"
proof -
  have cc: "poly_const c \<in> poly_carrier"
    by (rule poly_const_closed) simp
  have rf: "\<And>f. f \<in> set (List.map root_factor as) \<Longrightarrow> f \<in> poly_carrier"
    by (auto intro: root_factor_closed)
  then have pc: "poly_prod (List.map root_factor as) \<in> poly_carrier"
    by (rule poly_prod_closed)
  have "poly_of_fun (poly_mult (poly_const c) (poly_prod (List.map root_factor as)))
        = [:c:] * poly_of_fun (poly_prod (List.map root_factor as))"
    using poly_of_fun_mult [OF cc pc] by simp
  also have "poly_of_fun (poly_prod (List.map root_factor as)) = (\<Prod>a\<leftarrow>as. [:uminus a, 1:])"
  proof -
    have "poly_of_fun (poly_prod (List.map root_factor as))
          = (\<Prod>f\<leftarrow>List.map root_factor as. poly_of_fun f)"
      using rf by (rule poly_of_fun_poly_prod)
    also have "\<dots> = (\<Prod>a\<leftarrow>as. [:uminus a, 1:])"
      by (induct as) simp_all
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma poly_mult_const_prod_carrier:
  "poly_mult (poly_const c) (poly_prod (List.map root_factor as)) \<in> poly_carrier"
proof (intro poly_mult_closed poly_prod_closed)
  show "poly_const c \<in> poly_carrier" by (rule poly_const_closed) simp
qed (auto intro: root_factor_closed)

text \<open>@{const splits} says exactly that the corresponding polynomial of @{typ "'a poly"} is a
  constant times a product of linear factors.  Both directions are the dictionary applied to the
  defining equation, the reverse using injectivity on the carrier --- which is also why the carrier
  hypothesis cannot be dropped: an infinite-support function is sent to @{term 0}, so the right-hand
  side would hold of it vacuously.\<close>
theorem splits_iff_linear_factors:
  assumes p: "p \<in> poly_carrier"
  shows "splits p \<longleftrightarrow> (\<exists>c as. poly_of_fun p = [:c:] * (\<Prod>a\<leftarrow>as. [:uminus a, 1:]))"
proof
  assume "splits p"
  then obtain c as where "p = poly_mult (poly_const c) (poly_prod (List.map root_factor as))"
    by (auto simp: splits_def)
  then have "poly_of_fun p = [:c:] * (\<Prod>a\<leftarrow>as. [:uminus a, 1:])"
    by (simp add: poly_of_fun_split_form)
  then show "\<exists>c as. poly_of_fun p = [:c:] * (\<Prod>a\<leftarrow>as. [:uminus a, 1:])" by blast
next
  assume "\<exists>c as. poly_of_fun p = [:c:] * (\<Prod>a\<leftarrow>as. [:uminus a, 1:])"
  then obtain c as where q: "poly_of_fun p = [:c:] * (\<Prod>a\<leftarrow>as. [:uminus a, 1:])" by blast
  have "poly_of_fun p
        = poly_of_fun (poly_mult (poly_const c) (poly_prod (List.map root_factor as)))"
    by (simp add: q poly_of_fun_split_form)
  with p poly_mult_const_prod_carrier
  have "p = poly_mult (poly_const c) (poly_prod (List.map root_factor as))"
    by simp
  then show "splits p"
    unfolding splits_def by blast
qed

text \<open>A splitting polynomial of positive degree has a root: the factor list cannot be empty.\<close>
theorem splits_imp_root:
  assumes p: "p \<in> poly_carrier" and sp: "splits p" and d: "0 < degree p"
  obtains a where "eval a p = 0"
proof -
  from sp obtain c as where q: "poly_of_fun p = [:c:] * (\<Prod>a\<leftarrow>as. [:uminus a, 1:])"
    using splits_iff_linear_factors [OF p] by blast
  have "as \<noteq> []"
  proof
    assume "as = []"
    with q have "poly_of_fun p = [:c:]" by simp
    then have "Polynomial.degree (poly_of_fun p) = 0" by simp
    with p d show False by simp
  qed
  then obtain a bs where as: "as = a # bs" by (cases as) auto
  have "Polynomial.poly (poly_of_fun p) a = 0"
    unfolding q as by simp
  with p have "eval a p = 0" by simp
  then show thesis ..
qed


subsection \<open>The dictionary read backwards\<close>

text \<open>Every polynomial of @{typ "'a poly"} is the reading of its own coefficient function, so each
  correspondence above serves in the other direction too.\<close>

lemma eval_coeff [simp]: "eval x (Polynomial.coeff q) = Polynomial.poly q x"
  by (metis coeff_in_poly_carrier poly_of_fun_coeff poly_poly_of_fun)

lemma splits_coeff_iff:
  "splits (Polynomial.coeff q) \<longleftrightarrow> (\<exists>c as. q = [:c:] * (\<Prod>a\<leftarrow>as. [:uminus a, 1:]))"
  using splits_iff_linear_factors [OF coeff_in_poly_carrier] by simp

corollary splits_coeff_imp_root:
  assumes "splits (Polynomial.coeff q)" and "0 < Polynomial.degree q"
  obtains a where "Polynomial.poly q a = 0"
  by (metis assms coeff_in_poly_carrier degree_poly_of_fun eval_coeff poly_of_fun_coeff
      splits_imp_root)

end

text \<open>Outside the locale the carrier-set degree must be named in full, its only parameter being the
  zero of the ring; that also makes it usable as a simplification rule on ordinary polynomials.\<close>
lemma degree_coeff [simp]:
  fixes q :: "'a :: field poly"
  shows "Ring.degree 0 (Polynomial.coeff q) = Polynomial.degree q"
  by (metis coeff_in_poly_carrier degree_poly_of_fun poly_of_fun_coeff)

end
