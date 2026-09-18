section \<open>Polynomials in an Indexed Family of Indeterminates\<close>

theory Indexed_Poly
  imports Poly_Ring "HOL-Library.Multiset"
begin

text \<open>
  \<open>Poly_Ring\<close> builds \<open>R[X]\<close> from finite-support functions @{typ "nat \<Rightarrow> 'a"}, the exponent of the
  single indeterminate being the index.  Here the indeterminates form an arbitrary family, indexed by
  a type @{typ 'i}, and a monomial is therefore not a single exponent but a \<^emph>\<open>multiset\<close> over
  @{typ 'i}: the monomial \<open>X\<^sub>i\<^sup>2 X\<^sub>j\<close> is @{term "{# i, i, j #}"}.  A polynomial is a finite-support
  function @{typ "'i multiset \<Rightarrow> 'a"} with coefficients in the carrier, so the representation choice
  is the same one \<open>Poly_Ring\<close> makes, with the exponent @{typ nat} replaced by a monomial.  Addition
  is pointwise and multiplication is the convolution
  \<open>(p \<otimes> q) m = (\<Sum>n \<subseteq># m. p n \<cdot> q (m - n))\<close>, the sum running over the submultisets of \<open>m\<close> --- the
  monomial factorisations \<open>m = n + (m - n)\<close> --- exactly as the univariate convolution runs over
  \<open>{..k}\<close>, the factorisations \<open>k = i + (k - i)\<close>.

  \<^bold>\<open>Why an indexed family, rather than iterating \<open>Poly_Ring\<close>.\<close>  Iteration gives \<open>R[X][Y]\<close> and so on,
  which is \<^emph>\<open>finitely\<close> many indeterminates.  The construction of an algebraic closure needs one
  indeterminate for every polynomial over the base ring, all present at once, so that a maximal
  extension has room for a root of each.  That is what this theory supplies.

  Three facts used below --- \<open>fincomp_Sigma\<close>, \<open>fincomp_mult_distrib_left\<close> and
  \<open>fincomp_mult_distrib_right\<close> --- live in \<open>Poly_Ring\<close> but are generic in the index type and say
  nothing about polynomials.
\<close>

subsection \<open>Submultisets\<close>

text \<open>The convolution sums over the submultisets of a monomial, so that index set must be finite.
  Each submultiset of @{term "add_mset x m"} either omits @{term x}, and is a submultiset of
  @{term m}, or contains it, and is @{term x} added to one.\<close>
lemma finite_submultisets: "finite {n. n \<subseteq># (m :: 'i multiset)}"
proof (induct m rule: multiset_induct)
  case empty
  have "{n. n \<subseteq># {#}} = {{#}}" by auto
  then show ?case by simp
next
  case (add x m)
  have "{n. n \<subseteq># add_mset x m} \<subseteq> {n. n \<subseteq># m} \<union> add_mset x ` {n. n \<subseteq># m}"
  proof
    fix n assume "n \<in> {n. n \<subseteq># add_mset x m}"
    then have n: "\<And>y. count n y \<le> count (add_mset x m) y"
      by (simp add: subseteq_mset_def)
    show "n \<in> {n. n \<subseteq># m} \<union> add_mset x ` {n. n \<subseteq># m}"
    proof (cases "x \<in># n")
      case True
      have "count (n - {#x#}) y \<le> count m y" for y
        using n [of y] True by (cases "y = x") auto
      moreover from True have "n = add_mset x (n - {#x#})" by simp
      ultimately show ?thesis by (auto simp: subseteq_mset_def)
    next
      case False
      have "count n y \<le> count m y" for y
        using n [of y] False by (cases "y = x") (auto simp: not_in_iff)
      then show ?thesis by (simp add: subseteq_mset_def)
    qed
  qed
  moreover have "finite ({n. n \<subseteq># m} \<union> add_mset x ` {n. n \<subseteq># m})"
    using add by blast
  ultimately show ?case by (rule finite_subset)
qed

text \<open>Monomial arithmetic for the convolution, all at the level of coefficient counts.  The last
  two are the identities that make the associativity reindexing below a bijection.\<close>

lemma msub_diff_mono: "\<lbrakk> a \<subseteq># b; b \<subseteq># m \<rbrakk> \<Longrightarrow> b - a \<subseteq># m - a"
  using subset_eq_diff_conv by fastforce

lemma msub_add_closed: "\<lbrakk> a \<subseteq># m; b \<subseteq># m - a \<rbrakk> \<Longrightarrow> a + b \<subseteq># m"
  by (simp add: add.commute subset_mset.le_diff_conv2)

lemma msub_diff_diff: "\<lbrakk> a \<subseteq># b; b \<subseteq># m \<rbrakk> \<Longrightarrow> m - a - (b - a) = m - b"
  by (simp add: subseteq_mset_def multiset_eq_iff)

text \<open>Complementation is an involution of the submultisets of a monomial; this is what makes the
  convolution symmetric when the coefficients commute.\<close>
lemma msub_double_diff: "n \<subseteq># m \<Longrightarrow> m - (m - n) = n"
  by (simp add: subseteq_mset_def multiset_eq_iff)


context Ring
begin

subsection \<open>Carrier and coefficients\<close>

text \<open>The polynomials over @{term R} in the indeterminates indexed by @{typ 'i}: finite support on
  monomials, coefficients in the carrier.\<close>
definition ipoly_carrier :: "('i multiset \<Rightarrow> 'a) set"
  where "ipoly_carrier \<equiv> {p. finite {m. p m \<noteq> \<zero>} \<and> (\<forall>m. p m \<in> R)}"

lemma ipoly_carrierI:
  "\<lbrakk> finite {m. p m \<noteq> \<zero>}; \<And>m. p m \<in> R \<rbrakk> \<Longrightarrow> p \<in> ipoly_carrier"
  unfolding ipoly_carrier_def by blast

lemma ipoly_carrier_finite: "p \<in> ipoly_carrier \<Longrightarrow> finite {m. p m \<noteq> \<zero>}"
  unfolding ipoly_carrier_def by blast

lemma ipoly_carrier_coeff_closed: "p \<in> ipoly_carrier \<Longrightarrow> p m \<in> R"
  unfolding ipoly_carrier_def by blast


subsection \<open>Operations\<close>

definition ipoly_zero :: "'i multiset \<Rightarrow> 'a"  (\<open>\<zero>\<^sub>I\<close>)
  where "ipoly_zero \<equiv> (\<lambda>m. \<zero>)"

text \<open>The unit is the constant @{term \<one>}, carried by the empty monomial.\<close>
definition ipoly_one :: "'i multiset \<Rightarrow> 'a"  (\<open>\<one>\<^sub>I\<close>)
  where "ipoly_one \<equiv> (\<lambda>m. if m = {#} then \<one> else \<zero>)"

definition ipoly_add :: "('i multiset \<Rightarrow> 'a) \<Rightarrow> ('i multiset \<Rightarrow> 'a) \<Rightarrow> ('i multiset \<Rightarrow> 'a)"
    (infixl \<open>\<oplus>\<^sub>I\<close> 65)
  where "ipoly_add p q \<equiv> (\<lambda>m. p m + q m)"

definition ipoly_neg :: "('i multiset \<Rightarrow> 'a) \<Rightarrow> ('i multiset \<Rightarrow> 'a)"  (\<open>\<ominus>\<^sub>I _\<close> [66] 65)
  where "ipoly_neg p \<equiv> (\<lambda>m. - p m)"

text \<open>The convolution: a coefficient of the product sums over the factorisations
  \<open>m = n + (m - n)\<close> of the monomial.\<close>
definition ipoly_mult :: "('i multiset \<Rightarrow> 'a) \<Rightarrow> ('i multiset \<Rightarrow> 'a) \<Rightarrow> ('i multiset \<Rightarrow> 'a)"
    (infixl \<open>\<otimes>\<^sub>I\<close> 70)
  where "ipoly_mult p q \<equiv> (\<lambda>m. additive.fincomp (\<lambda>n. p n \<cdot> q (m - n)) {n. n \<subseteq># m})"


subsection \<open>Closure under the operations\<close>

lemma ipoly_zero_closed: "\<zero>\<^sub>I \<in> ipoly_carrier"
  by (rule ipoly_carrierI) (auto simp: ipoly_zero_def)

lemma ipoly_one_closed: "\<one>\<^sub>I \<in> ipoly_carrier"
  by (intro ipoly_carrierI) (auto simp: ipoly_one_def)

lemma ipoly_add_closed:
  assumes "p \<in> ipoly_carrier" "q \<in> ipoly_carrier"
  shows "p \<oplus>\<^sub>I q \<in> ipoly_carrier"
proof (rule ipoly_carrierI)
  have "{m. (p \<oplus>\<^sub>I q) m \<noteq> \<zero>} \<subseteq> {m. p m \<noteq> \<zero>} \<union> {m. q m \<noteq> \<zero>}"
    using additive.left_unit by (fastforce simp: additive.right_unit additive.unit_closed ipoly_add_def)
  moreover have "finite ({m. p m \<noteq> \<zero>} \<union> {m. q m \<noteq> \<zero>})"
    using assms by (simp add: ipoly_carrier_finite)
  ultimately show "finite {m. (p \<oplus>\<^sub>I q) m \<noteq> \<zero>}" by (rule finite_subset)
  show "\<And>m. (p \<oplus>\<^sub>I q) m \<in> R"
    using assms by (simp add: ipoly_add_def ipoly_carrier_coeff_closed)
qed

lemma ipoly_neg_closed:
  assumes p: "p \<in> ipoly_carrier" shows "\<ominus>\<^sub>I p \<in> ipoly_carrier"
proof (rule ipoly_carrierI)
  have "{m. (\<ominus>\<^sub>I p) m \<noteq> \<zero>} \<subseteq> {m. p m \<noteq> \<zero>}"
    unfolding ipoly_neg_def using additive.inverse_unit by force
  then show "finite {m. (\<ominus>\<^sub>I p) m \<noteq> \<zero>}"
    using p ipoly_carrier_finite finite_subset by blast
  show "\<And>m. (\<ominus>\<^sub>I p) m \<in> R"
    using p by (simp add: ipoly_neg_def ipoly_carrier_coeff_closed)
qed

lemma ipoly_mult_coeff_closed:
  assumes "p \<in> ipoly_carrier" "q \<in> ipoly_carrier"
  shows "(p \<otimes>\<^sub>I q) m \<in> R"
  by (simp add: assms ipoly_carrier_coeff_closed ipoly_mult_def)

text \<open>A product coefficient can be nonzero only at a monomial that factors as a support monomial of
  @{term p} times one of @{term q}, and there are finitely many such products.  This replaces the
  degree bound used in the univariate case, where the support is bounded by a single number.\<close>
lemma ipoly_mult_support_bound:
  assumes p: "p \<in> ipoly_carrier" and q: "q \<in> ipoly_carrier"
  shows "{m. (p \<otimes>\<^sub>I q) m \<noteq> \<zero>} \<subseteq> (\<lambda>(a, b). a + b) ` ({m. p m \<noteq> \<zero>} \<times> {m. q m \<noteq> \<zero>})"
proof
  fix m assume "m \<in> {m. (p \<otimes>\<^sub>I q) m \<noteq> \<zero>}"
  then have nz: "(p \<otimes>\<^sub>I q) m \<noteq> \<zero>" by simp
  show "m \<in> (\<lambda>(a, b). a + b) ` ({m. p m \<noteq> \<zero>} \<times> {m. q m \<noteq> \<zero>})"
  proof (rule ccontr)
    assume "m \<notin> (\<lambda>(a, b). a + b) ` ({m. p m \<noteq> \<zero>} \<times> {m. q m \<noteq> \<zero>})"
    then have "p n \<cdot> q (m - n) = \<zero>" if "n \<in> {n. n \<subseteq># m}" for n
      using that assms
      apply (simp add: image_iff ipoly_carrier_coeff_closed)
      by (metis ipoly_carrier_coeff_closed left_zero right_zero subset_mset.add_diff_inverse)
    then have "(p \<otimes>\<^sub>I q) m = \<zero>"
      unfolding ipoly_mult_def by (rule additive.fincomp_unit_eqI)
    with nz show False by simp
  qed
qed

lemma ipoly_mult_closed:
  assumes "p \<in> ipoly_carrier" and "q \<in> ipoly_carrier"
  shows "p \<otimes>\<^sub>I q \<in> ipoly_carrier"
proof (rule ipoly_carrierI)
  have "finite ({m. p m \<noteq> \<zero>} \<times> {m. q m \<noteq> \<zero>})"
    using assms by (simp add: ipoly_carrier_finite)
  then show "finite {m. (p \<otimes>\<^sub>I q) m \<noteq> \<zero>}"
    using ipoly_mult_support_bound [OF assms] by (blast intro: finite_subset)
qed (simp add: ipoly_mult_coeff_closed assms)


subsection \<open>Additive structure\<close>

text \<open>Addition is pointwise, so the abelian-group laws are those of @{term R} coefficientwise.\<close>

lemma ipoly_add_assoc:
  "\<lbrakk> p \<in> ipoly_carrier; q \<in> ipoly_carrier; r \<in> ipoly_carrier \<rbrakk>
     \<Longrightarrow> (p \<oplus>\<^sub>I q) \<oplus>\<^sub>I r = p \<oplus>\<^sub>I (q \<oplus>\<^sub>I r)"
  by (auto simp: ipoly_add_def additive.associative ipoly_carrier_coeff_closed)

lemma ipoly_add_comm:
  "\<lbrakk> p \<in> ipoly_carrier; q \<in> ipoly_carrier \<rbrakk> \<Longrightarrow> p \<oplus>\<^sub>I q = q \<oplus>\<^sub>I p"
  by (auto simp: ipoly_add_def additive.commutative ipoly_carrier_coeff_closed)

lemma ipoly_add_zero: "p \<in> ipoly_carrier \<Longrightarrow> \<zero>\<^sub>I \<oplus>\<^sub>I p = p"
  by (auto simp: ipoly_add_def ipoly_zero_def ipoly_carrier_coeff_closed)

lemma ipoly_add_neg: "p \<in> ipoly_carrier \<Longrightarrow> (\<ominus>\<^sub>I p) \<oplus>\<^sub>I p = \<zero>\<^sub>I"
  by (auto simp: ipoly_add_def ipoly_neg_def ipoly_zero_def ipoly_carrier_coeff_closed)

lemma ipoly_add_neg_right: "p \<in> ipoly_carrier \<Longrightarrow> p \<oplus>\<^sub>I (\<ominus>\<^sub>I p) = \<zero>\<^sub>I"
  using ipoly_add_comm ipoly_add_neg ipoly_neg_closed by force


subsection \<open>Multiplicative unit\<close>

text \<open>Only the empty monomial contributes to a product with the unit.\<close>

lemma ipoly_mult_one_left:
  assumes p: "p \<in> ipoly_carrier"
  shows "\<one>\<^sub>I \<otimes>\<^sub>I p = p"
proof
  fix m
  have "(\<one>\<^sub>I \<otimes>\<^sub>I p) m = additive.fincomp (\<lambda>n. \<one>\<^sub>I n \<cdot> p (m - n)) {n. n \<subseteq># m}"
    by (simp add: ipoly_mult_def)
  also have "\<dots> = additive.fincomp (\<lambda>n. if n = {#} then (\<lambda>_. p m) n else \<zero>) {n. n \<subseteq># m}"
    using p by (intro additive.fincomp_cong')
               (auto simp: ipoly_one_def ipoly_carrier_coeff_closed)
  also have "\<dots> = p m"
    by (intro additive.fincomp_singleton_swap) (auto simp: finite_submultisets ipoly_carrier_coeff_closed p)
  finally show "(\<one>\<^sub>I \<otimes>\<^sub>I p) m = p m" .
qed

lemma ipoly_mult_one_right:
  assumes p: "p \<in> ipoly_carrier"
  shows "p \<otimes>\<^sub>I \<one>\<^sub>I = p"
proof
  fix m
  have "(p \<otimes>\<^sub>I \<one>\<^sub>I) m = additive.fincomp (\<lambda>n. p n \<cdot> \<one>\<^sub>I (m - n)) {n. n \<subseteq># m}"
    by (simp add: ipoly_mult_def)
  also have "\<dots> = additive.fincomp (\<lambda>n. if n = m then (\<lambda>_. p m) n else \<zero>) {n. n \<subseteq># m}"
    using p
    by (intro additive.fincomp_cong')
       (auto simp: ipoly_one_def ipoly_carrier_coeff_closed Diff_eq_empty_iff_mset)
  also have "\<dots> = p m"
    by (intro additive.fincomp_singleton_swap) (auto simp: finite_submultisets ipoly_carrier_coeff_closed p)
  finally show "(p \<otimes>\<^sub>I \<one>\<^sub>I) m = p m" .
qed


subsection \<open>Distributivity\<close>

lemma ipoly_mult_add_distrib_left:
  assumes p: "p \<in> ipoly_carrier" and q: "q \<in> ipoly_carrier" and r: "r \<in> ipoly_carrier"
  shows "p \<otimes>\<^sub>I (q \<oplus>\<^sub>I r) = (p \<otimes>\<^sub>I q) \<oplus>\<^sub>I (p \<otimes>\<^sub>I r)"
proof
  fix m
  have pi: "\<And>n. p n \<in> R" and qi: "\<And>n. q n \<in> R" and ri: "\<And>n. r n \<in> R"
    using p q r by (auto simp: ipoly_carrier_coeff_closed)
  have "(p \<otimes>\<^sub>I (q \<oplus>\<^sub>I r)) m
        = additive.fincomp (\<lambda>n. p n \<cdot> (q (m - n) + r (m - n))) {n. n \<subseteq># m}"
    by (simp add: ipoly_mult_def ipoly_add_def)
  also have "\<dots> = additive.fincomp (\<lambda>n. p n \<cdot> q (m - n) + p n \<cdot> r (m - n)) {n. n \<subseteq># m}"
    using distributive(1) pi qi ri by presburger
  also have "\<dots> = additive.fincomp (\<lambda>n. p n \<cdot> q (m - n)) {n. n \<subseteq># m}
                  + additive.fincomp (\<lambda>n. p n \<cdot> r (m - n)) {n. n \<subseteq># m}"
    by (rule additive.fincomp_comp) (use pi qi ri in auto)
  also have "\<dots> = ((p \<otimes>\<^sub>I q) \<oplus>\<^sub>I (p \<otimes>\<^sub>I r)) m"
    by (simp add: ipoly_mult_def ipoly_add_def)
  finally show "(p \<otimes>\<^sub>I (q \<oplus>\<^sub>I r)) m = ((p \<otimes>\<^sub>I q) \<oplus>\<^sub>I (p \<otimes>\<^sub>I r)) m" .
qed

lemma ipoly_mult_add_distrib_right:
  assumes p: "p \<in> ipoly_carrier" and q: "q \<in> ipoly_carrier" and r: "r \<in> ipoly_carrier"
  shows "(q \<oplus>\<^sub>I r) \<otimes>\<^sub>I p = (q \<otimes>\<^sub>I p) \<oplus>\<^sub>I (r \<otimes>\<^sub>I p)"
proof
  fix m
  have pi: "\<And>n. p n \<in> R" and qi: "\<And>n. q n \<in> R" and ri: "\<And>n. r n \<in> R"
    using p q r by (auto simp: ipoly_carrier_coeff_closed)
  have "((q \<oplus>\<^sub>I r) \<otimes>\<^sub>I p) m = additive.fincomp (\<lambda>n. (q n + r n) \<cdot> p (m - n)) {n. n \<subseteq># m}"
    by (simp add: ipoly_mult_def ipoly_add_def)
  also have "\<dots> = additive.fincomp (\<lambda>n. q n \<cdot> p (m - n) + r n \<cdot> p (m - n)) {n. n \<subseteq># m}"
    using distributive(2) pi qi ri by presburger
  also have "\<dots> = additive.fincomp (\<lambda>n. q n \<cdot> p (m - n)) {n. n \<subseteq># m}
                  + additive.fincomp (\<lambda>n. r n \<cdot> p (m - n)) {n. n \<subseteq># m}"
    by (rule additive.fincomp_comp) (use pi qi ri in auto)
  also have "\<dots> = ((q \<otimes>\<^sub>I p) \<oplus>\<^sub>I (r \<otimes>\<^sub>I p)) m"
    by (simp add: ipoly_mult_def ipoly_add_def)
  finally show "((q \<oplus>\<^sub>I r) \<otimes>\<^sub>I p) m = ((q \<otimes>\<^sub>I p) \<oplus>\<^sub>I (r \<otimes>\<^sub>I p)) m" .
qed


subsection \<open>Associativity of the convolution\<close>

text \<open>Both sides are the sum of \<open>p a \<cdot> q b \<cdot> r c\<close> over the factorisations \<open>m = a + b + c\<close>.  The two
  nested sums present that set differently --- as pairs \<open>(b + a, a)\<close> on the left and \<open>(a, b)\<close> on the
  right --- so the proof is a reindexing along \<open>(b, a) \<mapsto> (a, b - a)\<close>, exactly as in the
  univariate case, with monomial arithmetic in place of arithmetic on degrees.\<close>
lemma ipoly_mult_assoc:
  fixes p q r :: "'i multiset \<Rightarrow> 'a"
  assumes p: "p \<in> ipoly_carrier" and q: "q \<in> ipoly_carrier" and r: "r \<in> ipoly_carrier"
  shows "(p \<otimes>\<^sub>I q) \<otimes>\<^sub>I r = p \<otimes>\<^sub>I (q \<otimes>\<^sub>I r)"
proof (rule ext)
  fix m :: "'i multiset"
  have pi: "\<And>n. p n \<in> R" and qi: "\<And>n. q n \<in> R" and ri: "\<And>n. r n \<in> R"
    using p q r by (auto simp: ipoly_carrier_coeff_closed)
  let ?S1 = "Sigma {b. b \<subseteq># m} (\<lambda>b :: 'i multiset. {a. a \<subseteq># b})"
  let ?S2 = "Sigma {a. a \<subseteq># m} (\<lambda>a :: 'i multiset. {b. b \<subseteq># m - a})"
  \<comment> \<open>The left side, as a sum over pairs \<open>(b, a)\<close> with \<open>a \<subseteq># b \<subseteq># m\<close>.\<close>
  have "((p \<otimes>\<^sub>I q) \<otimes>\<^sub>I r) m
        = additive.fincomp
            (\<lambda>b. additive.fincomp (\<lambda>a. p a \<cdot> q (b - a)) {a. a \<subseteq># b} \<cdot> r (m - b))
            {b. b \<subseteq># m}"
    by (simp add: ipoly_mult_def)
  also have "\<dots> = additive.fincomp
                    (\<lambda>b. additive.fincomp (\<lambda>a. (p a \<cdot> q (b - a)) \<cdot> r (m - b)) {a. a \<subseteq># b})
                    {b. b \<subseteq># m}"
    using pi qi ri
    by (intro additive.fincomp_cong' fincomp_mult_distrib_right) auto
  also have "\<dots> = additive.fincomp
                    (\<lambda>x. (p (snd x) \<cdot> q (fst x - snd x)) \<cdot> r (m - fst x)) ?S1"
    by (rule fincomp_Sigma) (use pi qi ri finite_submultisets in auto)
  finally have LHS: "((p \<otimes>\<^sub>I q) \<otimes>\<^sub>I r) m
        = additive.fincomp (\<lambda>x. (p (snd x) \<cdot> q (fst x - snd x)) \<cdot> r (m - fst x)) ?S1" .
  \<comment> \<open>The right side, as a sum over pairs \<open>(a, b)\<close> with \<open>a \<subseteq># m\<close> and \<open>b \<subseteq># m - a\<close>.\<close>
  have "(p \<otimes>\<^sub>I (q \<otimes>\<^sub>I r)) m
        = additive.fincomp
            (\<lambda>a. p a \<cdot> additive.fincomp (\<lambda>b. q b \<cdot> r (m - a - b)) {b. b \<subseteq># m - a})
            {a. a \<subseteq># m}"
    by (simp add: ipoly_mult_def)
  also have "\<dots> = additive.fincomp
                    (\<lambda>a. additive.fincomp (\<lambda>b. p a \<cdot> (q b \<cdot> r (m - a - b))) {b. b \<subseteq># m - a})
                    {a. a \<subseteq># m}"
    using pi qi ri
    by (intro additive.fincomp_cong' fincomp_mult_distrib_left) auto
  also have "\<dots> = additive.fincomp
                    (\<lambda>x. p (fst x) \<cdot> (q (snd x) \<cdot> r (m - fst x - snd x))) ?S2"
    by (rule fincomp_Sigma) (use pi qi ri finite_submultisets in auto)
  finally have RHS: "(p \<otimes>\<^sub>I (q \<otimes>\<^sub>I r)) m
        = additive.fincomp (\<lambda>x. p (fst x) \<cdot> (q (snd x) \<cdot> r (m - fst x - snd x))) ?S2" .
  \<comment> \<open>Reindex: \<open>(b, a) \<mapsto> (a, b - a)\<close>, with inverse \<open>(a, b) \<mapsto> (a + b, a)\<close>.\<close>
  let ?h = "\<lambda>x :: 'i multiset \<times> 'i multiset. (snd x, fst x - snd x)"
  let ?h' = "\<lambda>x :: 'i multiset \<times> 'i multiset. (fst x + snd x, fst x)"
  have bij: "bij_betw ?h ?S1 ?S2"
  proof (rule bij_betw_byWitness [where f' = ?h'])
    show "?h ` ?S1 \<subseteq> ?S2"
      by (auto simp: msub_diff_mono intro: subset_mset.order_trans)
  qed (auto simp: subset_mset.add_diff_inverse msub_add_closed)
  let ?F = "\<lambda>x. p (fst x) \<cdot> (q (snd x) \<cdot> r (m - fst x - snd x))"
  have "additive.fincomp ?F ?S2 = additive.fincomp ?F (?h ` ?S1)"
    using bij bij_betw_imp_surj_on by fastforce
  also have "\<dots> = additive.fincomp (\<lambda>x. ?F (?h x)) ?S1"
  proof (rule additive.fincomp_reindex)
    show "?F \<in> ?h ` ?S1 \<rightarrow> R" using pi qi ri by auto
    show "inj_on ?h ?S1" using bij bij_betw_imp_inj_on by blast
  qed
  also have "\<dots> = additive.fincomp (\<lambda>x. (p (snd x) \<cdot> q (fst x - snd x)) \<cdot> r (m - fst x)) ?S1"
    using pi qi ri multiplicative.associative
    by (intro additive.fincomp_cong') (auto simp: msub_diff_diff)
  finally show "((p \<otimes>\<^sub>I q) \<otimes>\<^sub>I r) m = (p \<otimes>\<^sub>I (q \<otimes>\<^sub>I r)) m"
    using LHS RHS by simp
qed


subsection \<open>The indexed polynomial ring\<close>

theorem ipoly_ring: "Ring ipoly_carrier (\<oplus>\<^sub>I) (\<otimes>\<^sub>I) \<zero>\<^sub>I \<one>\<^sub>I"
proof -
  have add_grp: "Group ipoly_carrier (\<oplus>\<^sub>I) \<zero>\<^sub>I"
  proof (rule GroupI)
    show "\<And>p. p \<in> ipoly_carrier \<Longrightarrow> p \<oplus>\<^sub>I \<zero>\<^sub>I = p"
      by (metis ipoly_add_comm ipoly_add_zero ipoly_zero_closed)
    show "\<And>p. p \<in> ipoly_carrier \<Longrightarrow> \<exists>q\<in>ipoly_carrier. p \<oplus>\<^sub>I q = \<zero>\<^sub>I \<and> q \<oplus>\<^sub>I p = \<zero>\<^sub>I"
      using ipoly_add_neg ipoly_add_neg_right ipoly_neg_closed by blast
  qed (auto simp: ipoly_add_closed ipoly_zero_closed ipoly_add_assoc ipoly_add_zero)
  interpret add: Group ipoly_carrier "(\<oplus>\<^sub>I)" "\<zero>\<^sub>I" by (rule add_grp)
  interpret add: Abelian_Group ipoly_carrier "(\<oplus>\<^sub>I)" "\<zero>\<^sub>I"
    by unfold_locales (rule ipoly_add_comm)
  interpret mult: Monoid ipoly_carrier "(\<otimes>\<^sub>I)" "\<one>\<^sub>I"
    by (simp add: Monoid.intro ipoly_mult_assoc ipoly_mult_closed ipoly_mult_one_left
        ipoly_mult_one_right ipoly_one_closed)
  show ?thesis
  proof qed (use ipoly_mult_add_distrib_left ipoly_mult_add_distrib_right in auto)
qed

subsection \<open>Constants and indeterminates\<close>

text \<open>A constant carries its value on the empty monomial.  This is the embedding of the coefficient
  ring, and it is what lets an extension of @{term R} be built inside this ring.\<close>
definition ipoly_const :: "'a \<Rightarrow> ('i multiset \<Rightarrow> 'a)"
  where "ipoly_const a \<equiv> (\<lambda>m. if m = {#} then a else \<zero>)"

lemma ipoly_const_coeff [simp]: "ipoly_const a {#} = a"
  by (simp add: ipoly_const_def)

lemma ipoly_const_closed: "a \<in> R \<Longrightarrow> ipoly_const a \<in> ipoly_carrier"
    by (auto simp: ipoly_mult_def ipoly_const_def ipoly_carrierI)

lemma ipoly_const_zero [simp]: "ipoly_const \<zero> = \<zero>\<^sub>I"
  by (simp add: ipoly_const_def ipoly_zero_def fun_eq_iff)

lemma ipoly_const_one [simp]: "ipoly_const \<one> = \<one>\<^sub>I"
  by (simp add: ipoly_const_def ipoly_one_def fun_eq_iff)

lemma ipoly_const_add:
  assumes "a \<in> R" and "b \<in> R"
  shows "ipoly_const (a + b) = (ipoly_const a :: 'i multiset \<Rightarrow> 'a) \<oplus>\<^sub>I ipoly_const b"
  using assms by (auto simp: ipoly_const_def ipoly_add_def fun_eq_iff additive.right_unit)

lemma ipoly_const_mult:
  assumes "a \<in> R" "b \<in> R"
  shows "ipoly_const (a \<cdot> b) = (ipoly_const a :: 'i multiset \<Rightarrow> 'a) \<otimes>\<^sub>I ipoly_const b"
    using assms by (auto simp: ipoly_mult_def ipoly_const_def additive.fincomp_unit_eqI)

lemma ipoly_const_inj_on: "inj_on (ipoly_const :: 'a \<Rightarrow> 'i multiset \<Rightarrow> 'a) R"
  using ipoly_const_coeff by (metis inj_on_def)

text \<open>The indeterminate @{text "X\<^sub>i"} is the monomial @{term "{#i#}"} with coefficient @{term \<one>}.
  Distinct indices give distinct indeterminates whenever the ring is nontrivial: note that
  @{locale Ring} does not itself assume @{term "\<one> \<noteq> \<zero>"}.\<close>
definition ivar :: "'i \<Rightarrow> ('i multiset \<Rightarrow> 'a)"
  where "ivar i \<equiv> (\<lambda>m. if m = {#i#} then \<one> else \<zero>)"

lemma ivar_closed: "ivar i \<in> ipoly_carrier"
  by (rule ipoly_carrierI) (auto simp: ivar_def)

lemma ivar_inj:
  assumes "\<one> \<noteq> \<zero>"
  shows "inj (ivar :: 'i \<Rightarrow> 'i multiset \<Rightarrow> 'a)"
  using assms by (auto simp: ivar_def inj_on_def fun_eq_iff)


subsection \<open>Indeterminates a polynomial does not involve\<close>

text \<open>@{term \<P>} does not involve the indeterminate @{term j} when no monomial containing @{term j}
  carries a nonzero coefficient.  An index that \<^emph>\<open>no\<close> element of an extension involves is what
  supplies room for a new root: adjoining one is then guaranteed not to disturb what is there
  already.  This replaces the cardinality argument that a construction over an abstract type of
  labels would need, and is the reason for choosing indexed polynomials as the ambient type.\<close>
definition index_free :: "('i multiset \<Rightarrow> 'a) \<Rightarrow> 'i \<Rightarrow> bool"
  where "index_free \<P> j \<equiv> (\<forall>m. j \<in># m \<longrightarrow> \<P> m = \<zero>)"

lemma index_freeI: "(\<And>m. j \<in># m \<Longrightarrow> \<P> m = \<zero>) \<Longrightarrow> index_free \<P> j"
  by (simp add: index_free_def)

lemma index_freeD: "\<lbrakk> index_free \<P> j; j \<in># m \<rbrakk> \<Longrightarrow> \<P> m = \<zero>"
  by (simp add: index_free_def)

text \<open>Constants involve no indeterminate at all.\<close>
lemma index_free_const [simp]: "index_free (ipoly_const a) j"
  by (rule index_freeI) (auto simp: ipoly_const_def)

lemma index_free_zero [simp]: "index_free \<zero>\<^sub>I j"
  by (rule index_freeI) (simp add: ipoly_zero_def)

text \<open>The indeterminate @{term "ivar j"} does involve @{term j}, provided the coefficient ring is
  nontrivial --- @{locale Ring} does not itself assume @{term "\<one> \<noteq> \<zero>"}.\<close>
lemma not_index_free_ivar:
  assumes "\<one> \<noteq> \<zero>" shows "\<not> index_free (ivar j) j"
  using assms index_freeD ivar_def by (metis multi_member_last)


subsection \<open>Monomials\<close>

text \<open>The monomial @{term "imonom a n"} carries the coefficient @{term a} on the monomial @{term n}.
  Constants and indeterminates are the special cases @{term "n = {#}"} and @{term "a = \<one>"} with
  @{term n} a singleton.\<close>
definition imonom :: "'a \<Rightarrow> 'i multiset \<Rightarrow> ('i multiset \<Rightarrow> 'a)"
  where "imonom a n \<equiv> (\<lambda>m. if m = n then a else \<zero>)"

lemma imonom_apply [simp]: "imonom a n n = a"
  by (simp add: imonom_def)

lemma imonom_closed: "a \<in> R \<Longrightarrow> imonom a n \<in> ipoly_carrier"
proof (rule ipoly_carrierI)
  show "finite {m. imonom a n m \<noteq> \<zero>}"
    by (rule finite_subset [where B = "{n}"]) (auto simp: imonom_def)
qed (simp add: imonom_def)

lemma ipoly_const_eq_imonom: "ipoly_const a = imonom a {#}"
  by (simp add: ipoly_const_def imonom_def)

lemma ivar_eq_imonom: "ivar j = imonom \<one> {#j#}"
  by (simp add: ivar_def imonom_def)

lemma imonom_mult:
  fixes n n' :: "'i multiset"
  assumes a: "a \<in> R" and b: "b \<in> R"
  shows "imonom a n \<otimes>\<^sub>I imonom b n' = imonom (a \<cdot> b) (n + n')"
proof 
  fix m
  show "(imonom a n \<otimes>\<^sub>I imonom b n') m = imonom (a \<cdot> b) (n + n') m"
  proof (cases "m = n + n'")
    case True
    have nsub: "n \<subseteq># m" using True by simp
    have "(imonom a n \<otimes>\<^sub>I imonom b n') m
          = additive.fincomp (\<lambda>p. if p = n then (\<lambda>_. a \<cdot> b) p else \<zero>) {p. p \<subseteq># m}"
      unfolding ipoly_mult_def
      using a b True by (intro additive.fincomp_cong') (auto simp: imonom_def)
    also have "\<dots> = a \<cdot> b"
      using nsub a b
      by (intro finite_submultisets additive.fincomp_singleton_swap) auto
    finally show ?thesis using True by simp
  next
    case False
    with a b have "imonom a n p \<cdot> imonom b n' (m - p) = \<zero>" if "p \<in> {p. p \<subseteq># m}" for p
      using that a b by (auto simp: imonom_def subset_mset.add_diff_inverse)
    then have "(imonom a n \<otimes>\<^sub>I imonom b n') m = \<zero>"
      unfolding ipoly_mult_def by (rule additive.fincomp_unit_eqI)
    then show ?thesis using False by (simp add: imonom_def)
  qed
qed

lemma imonom_shift:
  fixes n m :: "'i multiset"
  assumes c: "c \<in> ipoly_carrier"
  shows "(c \<otimes>\<^sub>I imonom \<one> n) m = (if n \<subseteq># m then c (m - n) else \<zero>)"
proof (cases "n \<subseteq># m")
  case True
  \<comment> \<open>For @{term "p \<subseteq># m"} the second factor is @{term \<one>} exactly at @{term "p = m - n"}.\<close>
  then have unique: "(m - p = n) = (p = m - n)" if "p \<subseteq># m" for p
    using that by (auto simp: msub_double_diff)
  have \<section>: "\<forall>m. c m \<in> R"
    by (meson Ring.ipoly_carrier_coeff_closed Ring_axioms c)
  have "(c \<otimes>\<^sub>I imonom \<one> n) m = additive.fincomp (\<lambda>p. if p = m - n then (\<lambda>p. c p) p else \<zero>) {p. p \<subseteq># m}"
    unfolding ipoly_mult_def
    using c by (intro additive.fincomp_cong')
               (auto simp: imonom_def unique ipoly_carrier_coeff_closed)
  also have "\<dots> = c (m - n)"
    using \<section> by (simp add: additive.fincomp_singleton_swap finite_submultisets)
  finally show ?thesis using True by simp
next
  case False
  then have "c p \<cdot> imonom \<one> n (m - p) = \<zero>" if "p \<in> {p. p \<subseteq># m}" for p
    by (metis c imonom_def ipoly_carrier_coeff_closed right_zero diff_subset_eq_self)
  then have "(c \<otimes>\<^sub>I imonom \<one> n) m = \<zero>"
    unfolding ipoly_mult_def by (rule additive.fincomp_unit_eqI)
  then show ?thesis using False by simp
qed

text \<open>A power of an indeterminate is the monomial with that exponent.\<close>
lemma ivar_pow:
  fixes j :: 'i
  shows "Ring.rpow (\<otimes>\<^sub>I) \<one>\<^sub>I (ivar j) k = imonom \<one> (replicate_mset k j)"
proof (induct k)
  case 0
  have "Ring.rpow (\<otimes>\<^sub>I) \<one>\<^sub>I (ivar j) 0 = \<one>\<^sub>I"
    by (rule Ring.rpow_0 [OF ipoly_ring])
  then show ?case
    by (simp add: ipoly_one_def imonom_def)
next
  case (Suc k) 
  have "Ring.rpow (\<otimes>\<^sub>I) \<one>\<^sub>I (ivar j) (Suc k) = ivar j \<otimes>\<^sub>I Ring.rpow (\<otimes>\<^sub>I) \<one>\<^sub>I (ivar j) k"
    by (rule Ring.rpow_Suc [OF ipoly_ring])
  then show ?case
    using Suc by (simp add: ivar_eq_imonom imonom_mult)
qed


subsection \<open>Reading a polynomial off its value at an indeterminate\<close>

text \<open>The point of the monomial lemmas above.  A sum \<open>\<Sum>\<^sub>k c\<^sub>k X\<^sub>j\<^sup>k\<close> whose coefficients do not involve
  \<open>X\<^sub>j\<close> determines those coefficients: its value on a monomial \<open>m\<close> is the coefficient indexed by the
  multiplicity of \<open>j\<close> in \<open>m\<close>, evaluated at what remains of \<open>m\<close>.  So such a sum is injective in the
  coefficients, which is what makes the realisation of a quotient \<open>M[X]/(Q)\<close> inside this ring
  faithful.\<close>

lemma ipoly_add_cmonoid: "commutative_monoid ipoly_carrier (\<oplus>\<^sub>I) \<zero>\<^sub>I"
  using ipoly_ring by (meson Abelian_Group_def Ring_def)

text \<open>Addition is pointwise, so a finite sum may be evaluated coefficientwise.\<close>
lemma ipoly_fincomp_apply:
  fixes m :: "'i multiset"
  assumes f: "\<And>k. f k \<in> ipoly_carrier"
  shows "commutative_monoid.fincomp ipoly_carrier (\<oplus>\<^sub>I) \<zero>\<^sub>I f A m = additive.fincomp (\<lambda>k. f k m) A"
proof (induction A rule: infinite_finite_induct)
  case empty
  have "commutative_monoid.fincomp ipoly_carrier (\<oplus>\<^sub>I) \<zero>\<^sub>I f {} = \<zero>\<^sub>I"
    by (rule commutative_monoid.fincomp_empty [OF ipoly_add_cmonoid])
  then show ?case by (simp add: ipoly_zero_def)
next
  case (insert a A)
  have "f \<in> A \<rightarrow> ipoly_carrier" "f a \<in> ipoly_carrier" using f by auto
  then have "commutative_monoid.fincomp ipoly_carrier (\<oplus>\<^sub>I) \<zero>\<^sub>I f (insert a A) m
               = f a m + commutative_monoid.fincomp ipoly_carrier (\<oplus>\<^sub>I) \<zero>\<^sub>I f A m"
    using commutative_monoid.fincomp_insert [OF ipoly_add_cmonoid] insert.hyps 
    by (smt (verit) ipoly_add_def)
  also have "\<dots> = additive.fincomp (\<lambda>k. f k m) (insert a A)"
    using insert.IH by (simp add: f insert.hyps ipoly_carrier_coeff_closed)
  finally show ?case .
next
  case infinite
  then show ?case
    using additive.commutative_monoid_axioms ipoly_add_cmonoid ipoly_zero_def
    by (metis commutative_monoid.fincomp_def)
qed

lemma replicate_mset_subseteq_count: "replicate_mset k j \<subseteq># m \<longleftrightarrow> k \<le> count m j"
  by (auto simp: subseteq_mset_def split: if_split_asm)

text \<open>The closed form: only the term whose exponent matches the multiplicity of @{term j} in
  @{term m} survives, because every earlier coefficient is evaluated at a monomial that still
  involves @{term j}, where it vanishes.\<close>
theorem ieval_ivar:
  fixes j :: 'i and m :: "'i multiset"
  assumes c: "\<And>k. c k \<in> ipoly_carrier" and free: "\<And>k. index_free (c k) j"
  shows "commutative_monoid.fincomp ipoly_carrier (\<oplus>\<^sub>I) \<zero>\<^sub>I
           (\<lambda>k. c k \<otimes>\<^sub>I Ring.rpow (\<otimes>\<^sub>I) \<one>\<^sub>I (ivar j) k) {..d} m
         = (if count m j \<le> d then c (count m j) (m - replicate_mset (count m j) j) else \<zero>)"
proof -
  have cl: "c k \<otimes>\<^sub>I Ring.rpow (\<otimes>\<^sub>I) \<one>\<^sub>I (ivar j) k \<in> ipoly_carrier" for k
    using c by (simp add: ivar_pow ipoly_mult_closed imonom_closed)
  have term_eq: "(c k \<otimes>\<^sub>I Ring.rpow (\<otimes>\<^sub>I) \<one>\<^sub>I (ivar j) k) m
                 = (if k = count m j
                    then c (count m j) (m - replicate_mset (count m j) j) else \<zero>)" for k
  proof -
    have "(c k \<otimes>\<^sub>I Ring.rpow (\<otimes>\<^sub>I) \<one>\<^sub>I (ivar j) k) m
          = (if replicate_mset k j \<subseteq># m then c k (m - replicate_mset k j) else \<zero>)"
      by (simp add: ivar_pow imonom_shift [OF c])
    also have "\<dots> = (if k = count m j then c (count m j) (m - replicate_mset (count m j) j) else \<zero>)"
      using index_freeD [OF free] 
      by (cases "k < count m j") (auto simp: in_diff_count replicate_mset_subseteq_count)
    finally show ?thesis .
  qed
  have "commutative_monoid.fincomp ipoly_carrier (\<oplus>\<^sub>I) \<zero>\<^sub>I
          (\<lambda>k. c k \<otimes>\<^sub>I Ring.rpow (\<otimes>\<^sub>I) \<one>\<^sub>I (ivar j) k) {..d} m
        = additive.fincomp (\<lambda>k. (c k \<otimes>\<^sub>I Ring.rpow (\<otimes>\<^sub>I) \<one>\<^sub>I (ivar j) k) m) {..d}"
    by (rule ipoly_fincomp_apply [OF cl])
  also have "\<dots> = additive.fincomp
                    (\<lambda>k. if k = count m j
                         then (\<lambda>_. c (count m j) (m - replicate_mset (count m j) j)) k
                         else \<zero>) {..d}"
    using term_eq by simp
  also have "\<dots> = (if count m j \<le> d
                   then c (count m j) (m - replicate_mset (count m j) j) else \<zero>)"
  proof (cases "count m j \<le> d")
    case True
    then show ?thesis
      using assms(1) 
      by (auto intro!: ipoly_carrier_coeff_closed additive.fincomp_singleton_swap)
  next
    case False then show ?thesis
      by (force intro!: additive.fincomp_unit_eqI)
  qed
  finally show ?thesis .
qed

text \<open>What the closed form is for: the coefficients can be recovered, so a polynomial in
  @{term "ivar j"} with index-free coefficients determines them.  Reading @{thm [source] ieval_ivar}
  at the monomial @{term "n + replicate_mset k j"} isolates the @{term k}th coefficient at
  @{term n} --- provided @{term n} itself avoids @{term j}, and where it does not, both coefficients
  vanish anyway.  This is the injectivity that lets a quotient be realised by normal forms: distinct
  remainders go to distinct elements of the ambient ring.\<close>
lemma ieval_ivar_inj:
  fixes j :: 'i and D k :: nat
  assumes c: "\<And>k. c k \<in> ipoly_carrier" and cfree: "\<And>k. index_free (c k) j"
    and d: "\<And>k. d k \<in> ipoly_carrier" and dfree: "\<And>k. index_free (d k) j"
    and eq: "commutative_monoid.fincomp ipoly_carrier (\<oplus>\<^sub>I) \<zero>\<^sub>I
               (\<lambda>k. c k \<otimes>\<^sub>I Ring.rpow (\<otimes>\<^sub>I) \<one>\<^sub>I (ivar j) k) {..D}
             = commutative_monoid.fincomp ipoly_carrier (\<oplus>\<^sub>I) \<zero>\<^sub>I
               (\<lambda>k. d k \<otimes>\<^sub>I Ring.rpow (\<otimes>\<^sub>I) \<one>\<^sub>I (ivar j) k) {..D}"
    and k: "k \<le> D"
  shows "c k = d k"
proof (rule ext)
  fix n :: "'i multiset"
  show "c k n = d k n"
  proof (cases "j \<in># n")
    case True
    \<comment> \<open>Both coefficients are index-free at @{term j}, so both vanish here.\<close>
    show ?thesis
      using index_freeD [OF cfree True] index_freeD [OF dfree True] by simp
  next
    case False
    define m where "m \<equiv> n + replicate_mset k j"
    have cm: "count m j = k" using False by (simp add: m_def not_in_iff)
    have mn: "m - replicate_mset k j = n" by (simp add: m_def)
    have ceq: "commutative_monoid.fincomp ipoly_carrier (\<oplus>\<^sub>I) \<zero>\<^sub>I
                 (\<lambda>k. c k \<otimes>\<^sub>I Ring.rpow (\<otimes>\<^sub>I) \<one>\<^sub>I (ivar j) k) {..D} m
               = (if count m j \<le> D
                  then c (count m j) (m - replicate_mset (count m j) j) else \<zero>)"
      by (rule ieval_ivar [OF c cfree])
    have deq: "commutative_monoid.fincomp ipoly_carrier (\<oplus>\<^sub>I) \<zero>\<^sub>I
                 (\<lambda>k. d k \<otimes>\<^sub>I Ring.rpow (\<otimes>\<^sub>I) \<one>\<^sub>I (ivar j) k) {..D} m
               = (if count m j \<le> D
                  then d (count m j) (m - replicate_mset (count m j) j) else \<zero>)"
      by (rule ieval_ivar [OF d dfree])
    from ceq deq eq cm mn k show ?thesis by simp
  qed
qed

end (* Ring *)


section \<open>Polynomials over a Commutative Ring\<close>

context commutative_ring
begin

text \<open>When the coefficients commute so do the polynomials: the convolution is symmetric under the
  involution @{text "n \<mapsto> m - n"} of the submultisets of @{text m}.\<close>
lemma ipoly_mult_comm:
  fixes p q :: "'i multiset \<Rightarrow> 'a"
  assumes p: "p \<in> ipoly_carrier" and q: "q \<in> ipoly_carrier"
  shows "p \<otimes>\<^sub>I q = q \<otimes>\<^sub>I p"
proof 
  fix m :: "'i multiset"
  have pi: "\<And>n. p n \<in> R" and qi: "\<And>n. q n \<in> R"
    using p q by (auto simp: ipoly_carrier_coeff_closed)
  have bij: "bij_betw (\<lambda>n :: 'i multiset. m - n) {n. n \<subseteq># m} {n. n \<subseteq># m}"
    by (rule bij_betw_byWitness [where f' = "\<lambda>n :: 'i multiset. m - n"])
       (auto simp: msub_double_diff diff_subset_eq_self)
  have "(p \<otimes>\<^sub>I q) m = additive.fincomp (\<lambda>n. q (m - n) \<cdot> p n) {n. n \<subseteq># m}"
    by (simp add: ipoly_mult_def multiplicative.commutative pi qi)
  also have "\<dots> = additive.fincomp (\<lambda>n. q (m - n) \<cdot> p n)
                    ((\<lambda>n :: 'i multiset. m - n) ` {n. n \<subseteq># m})"
    using bij bij_betw_imp_surj_on by fastforce
  also have "\<dots> = additive.fincomp (\<lambda>n. q (m - (m - n)) \<cdot> p (m - n)) {n. n \<subseteq># m}"
    by (rule additive.fincomp_reindex)
       (use pi qi bij bij_betw_imp_inj_on in auto)
  also have "\<dots> = additive.fincomp (\<lambda>n. q n \<cdot> p (m - n)) {n. n \<subseteq># m}"
    using pi qi by (intro additive.fincomp_cong') (auto simp: msub_double_diff)
  also have "\<dots> = (q \<otimes>\<^sub>I p) m" by (simp add: ipoly_mult_def)
  finally show "(p \<otimes>\<^sub>I q) m = (q \<otimes>\<^sub>I p) m" .
qed

theorem ipoly_commutative_ring:
  "commutative_ring (ipoly_carrier :: ('i multiset \<Rightarrow> 'a) set) (\<oplus>\<^sub>I) (\<otimes>\<^sub>I) \<zero>\<^sub>I \<one>\<^sub>I"
proof -
  interpret P: Ring "ipoly_carrier :: ('i multiset \<Rightarrow> 'a) set" "(\<oplus>\<^sub>I)" "(\<otimes>\<^sub>I)" "\<zero>\<^sub>I" "\<one>\<^sub>I"
    by (rule ipoly_ring)
  show ?thesis
  proof qed (simp add: ipoly_mult_comm)
qed

end (* commutative_ring *)


section \<open>The Univariate Case, as a Check on the Convolution\<close>

text \<open>With a single indeterminate --- index type @{typ unit} --- a monomial is determined by its
  size, so the submultisets of @{text "X\<^sup>k"} are exactly @{text "X\<^sup>i"} for @{text "i \<le> k"}, and the
  indexed convolution must reduce to the univariate one of \<open>Poly_Ring\<close>.  This is an independent
  check on both the index set of the convolution and the placement of @{text "m - n"} within it: a
  sum over the wrong factorisations of a monomial would still build a ring, and would still satisfy
  every law proved above, but it would not agree with \<open>Poly_Ring\<close> here.\<close>

lemma unit_mset_eq_replicate: "(n :: unit multiset) = replicate_mset (count n ()) ()"
  by (simp add: multiset_eq_iff)

lemma submultisets_replicate_unit:
  "{n :: unit multiset. n \<subseteq># replicate_mset k ()} = (\<lambda>i. replicate_mset i ()) ` {..k}"
  using unit_mset_eq_replicate
  by (auto simp: subseteq_mset_def image_iff)

lemma replicate_unit_diff:
  "replicate_mset k () - replicate_mset i () = replicate_mset (k - i) ()"
  by (simp add: multiset_eq_iff)

lemma inj_on_replicate_unit: "inj_on (\<lambda>i. replicate_mset i ()) {..k}"
  by (rule inj_on_inverseI [where g = "\<lambda>n. count n ()"]) simp

context Ring
begin

theorem ipoly_mult_unit_index:
  fixes p q :: "unit multiset \<Rightarrow> 'a"
  assumes p: "p \<in> ipoly_carrier" and q: "q \<in> ipoly_carrier"
  shows "(p \<otimes>\<^sub>I q) (replicate_mset k ())
         = ((\<lambda>i. p (replicate_mset i ())) \<otimes>\<^sub>P (\<lambda>i. q (replicate_mset i ()))) k"
proof -
  have pi: "\<And>n. p n \<in> R" and qi: "\<And>n. q n \<in> R"
    using p q by (auto simp: ipoly_carrier_coeff_closed)
  have "(p \<otimes>\<^sub>I q) (replicate_mset k ())
        = additive.fincomp (\<lambda>n. p n \<cdot> q (replicate_mset k () - n))
            ((\<lambda>i. replicate_mset i ()) ` {..k})"
    by (simp add: ipoly_mult_def submultisets_replicate_unit)
  also have "\<dots> = additive.fincomp
                    (\<lambda>i. p (replicate_mset i ())
                           \<cdot> q (replicate_mset k () - replicate_mset i ())) {..k}"
    by (rule additive.fincomp_reindex) (use pi qi inj_on_replicate_unit in auto)
  also have "\<dots> = ((\<lambda>i. p (replicate_mset i ())) \<otimes>\<^sub>P (\<lambda>i. q (replicate_mset i ()))) k"
    by (simp add: replicate_unit_diff poly_mult_def)
  finally show ?thesis .
qed

end (* Ring *)

end
