section \<open>The Polynomial Ring \<open>R[X]\<close> (Carrier-Set Construction)\<close>

theory Poly_Ring
  imports Ring_Theory Finite_Composite
begin

text \<open>\<^bold>\<open>Note on notation.\<close> \<open>Ring_Theory\<close> frees \<open>+\<close>/\<open>-\<close> for the ring operations, while
  \<open>FiniteProduct\<close> (via \<open>Main\<close>) keeps HOL's arithmetic notation; the theory merge admits
  \<^emph>\<open>both\<close>.  This is exactly what the convolution needs --- ring operations on coefficients
  (type \<open>'a\<close>) and ordinary arithmetic on the \<open>nat\<close> indices \<open>k - i\<close> --- and the parser
  disambiguates by type.\<close>

text \<open>
  We construct the polynomial ring over a carrier-set ring \<open>R\<close> using the
  \<^emph>\<open>finite-support function\<close> representation: a polynomial is a function
  @{typ "nat \<Rightarrow> 'a"} that is eventually zero, with all coefficients drawn from the
  carrier \<open>R\<close>.  This mirrors HOL's own \<open>'a poly\<close> type (which is \<open>Abs_poly\<close>
  over a finite-support function), so the bridge to the type-class world is near
  definitional, and there is no leading-zero normalisation invariant to maintain.

  Coefficient \<open>i\<close> of a polynomial \<open>p\<close> is simply \<open>p i\<close>.  Addition is
  pointwise; multiplication is the convolution \<open>(p \<otimes> q) k = (\<Sum>i\<le>k. p i \<cdot> q (k - i))\<close>,
  computed with the additive \<open>fincomp\<close> operator of \<open>R\<close>.
\<close>

context Ring
begin

subsection \<open>Carrier, coefficients, and support\<close>

text \<open>The set of polynomials over @{term R}: finite support, coefficients in @{term R}.\<close>
definition poly_carrier :: "(nat \<Rightarrow> 'a) set"
  where "poly_carrier = {p. finite {i. p i \<noteq> \<zero>} \<and> (\<forall>i. p i \<in> R)}"

lemma poly_carrierI:
  "\<lbrakk> finite {i. p i \<noteq> \<zero>}; \<And>i. p i \<in> R \<rbrakk> \<Longrightarrow> p \<in> poly_carrier"
  unfolding poly_carrier_def by blast

lemma poly_carrier_finite: "p \<in> poly_carrier \<Longrightarrow> finite {i. p i \<noteq> \<zero>}"
  unfolding poly_carrier_def by blast

lemma poly_carrier_coeff_closed: "p \<in> poly_carrier \<Longrightarrow> p i \<in> R"
  unfolding poly_carrier_def by blast


subsection \<open>Zero and one\<close>

definition poly_zero :: "nat \<Rightarrow> 'a"  (\<open>\<zero>\<^sub>P\<close>)
  where "poly_zero = (\<lambda>i. \<zero>)"

definition poly_one :: "nat \<Rightarrow> 'a"  (\<open>\<one>\<^sub>P\<close>)
  where "poly_one = (\<lambda>i. if i = 0 then \<one> else \<zero>)"


subsection \<open>Addition\<close>

definition poly_add :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"  (infixl \<open>\<oplus>\<^sub>P\<close> 65)
  where "poly_add p q = (\<lambda>i. p i + q i)"

definition poly_neg :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"  (\<open>\<ominus>\<^sub>P _\<close> [66] 65)
  where "poly_neg p = (\<lambda>i. - p i)"


subsection \<open>Multiplication (convolution)\<close>

definition poly_mult :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"  (infixl \<open>\<otimes>\<^sub>P\<close> 70)
  where "poly_mult p q = (\<lambda>k. additive.fincomp (\<lambda>i. p i \<cdot> q (k - i)) {..k})"

text \<open>A polynomial is a \<^emph>\<open>unit\<close> when it has a two-sided multiplicative inverse in the
  polynomial ring.  (Stated directly on the carrier-set operations, since the ambient
  @{text multiplicative} monoid acts on the coefficient type, not on polynomials.)\<close>
definition poly_unit :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "poly_unit p \<longleftrightarrow> p \<in> poly_carrier
            \<and> (\<exists>q. q \<in> poly_carrier \<and> p \<otimes>\<^sub>P q = \<one>\<^sub>P \<and> q \<otimes>\<^sub>P p = \<one>\<^sub>P)"

lemma poly_unitI:
  "\<lbrakk> p \<in> poly_carrier; q \<in> poly_carrier; p \<otimes>\<^sub>P q = \<one>\<^sub>P; q \<otimes>\<^sub>P p = \<one>\<^sub>P \<rbrakk> \<Longrightarrow> poly_unit p"
  unfolding poly_unit_def by blast

lemma poly_unit_closed: "poly_unit p \<Longrightarrow> p \<in> poly_carrier"
  unfolding poly_unit_def by blast


subsection \<open>Closure under the operations\<close>

lemma poly_zero_closed: "\<zero>\<^sub>P \<in> poly_carrier"
  by (rule poly_carrierI) (auto simp: poly_zero_def)

lemma poly_one_closed: "\<one>\<^sub>P \<in> poly_carrier"
  by (simp add: poly_carrierI poly_one_def)

lemma poly_add_closed:
  assumes "p \<in> poly_carrier" "q \<in> poly_carrier"
  shows "p \<oplus>\<^sub>P q \<in> poly_carrier"
proof (rule poly_carrierI)
  have "{i. (p \<oplus>\<^sub>P q) i \<noteq> \<zero>} \<subseteq> {i. p i \<noteq> \<zero>} \<union> {i. q i \<noteq> \<zero>}"
    using additive.right_unit poly_add_def by force
  moreover have "finite ({i. p i \<noteq> \<zero>} \<union> {i. q i \<noteq> \<zero>})"
    using assms by (simp add: poly_carrier_finite)
  ultimately show "finite {i. (p \<oplus>\<^sub>P q) i \<noteq> \<zero>}" by (rule finite_subset)
  show "\<And>i. (p \<oplus>\<^sub>P q) i \<in> R"
    using assms by (simp add: poly_add_def poly_carrier_coeff_closed)
qed

text \<open>Each coefficient of a product is a finite sum of products of carrier elements.\<close>
lemma poly_mult_coeff_closed:
  assumes "p \<in> poly_carrier" "q \<in> poly_carrier"
  shows "(p \<otimes>\<^sub>P q) k \<in> R"
  by (simp add: assms(1,2) poly_carrier_coeff_closed poly_mult_def)

text \<open>A product coefficient vanishes beyond the sum of the two top degrees, so the product has
  finite support.\<close>
lemma poly_mult_support_bound:
  assumes p: "p \<in> poly_carrier" and q: "q \<in> poly_carrier"
    and k: "k > (if {i. p i \<noteq> \<zero>} = {} then 0 else Max {i. p i \<noteq> \<zero>})
              + (if {i. q i \<noteq> \<zero>} = {} then 0 else Max {i. q i \<noteq> \<zero>})"
  shows "(p \<otimes>\<^sub>P q) k = \<zero>"
proof -
  define Np where "Np = (if {i. p i \<noteq> \<zero>} = {} then 0 else Max {i. p i \<noteq> \<zero>})"
  define Nq where "Nq = (if {i. q i \<noteq> \<zero>} = {} then 0 else Max {i. q i \<noteq> \<zero>})"
  have finP: "finite {i. p i \<noteq> \<zero>}" using p by (rule poly_carrier_finite)
  have finQ: "finite {i. q i \<noteq> \<zero>}" using q by (rule poly_carrier_finite)
  have pNp: "\<And>i. p i \<noteq> \<zero> \<Longrightarrow> i \<le> Np"
    using finP unfolding Np_def by (auto simp: Max_ge)
  have qNq: "\<And>i. q i \<noteq> \<zero> \<Longrightarrow> i \<le> Nq"
    using finQ unfolding Nq_def by (auto simp: Max_ge)
  have kgt: "k > Np + Nq" using k unfolding Np_def Nq_def by simp
  have "p i \<cdot> q (k - i) = \<zero>" if "i \<in> {..k}" for i
  proof (cases "p i = \<zero>")
    case True then show ?thesis using p q by (simp add: poly_carrier_coeff_closed)
  next
    case False 
    then have "q (k - i) = \<zero>" using qNq
      using kgt pNp by fastforce
    then show ?thesis using p q by (simp add: poly_carrier_coeff_closed)
  qed
  then show ?thesis
    unfolding poly_mult_def by (rule additive.fincomp_unit_eqI)
qed

lemma poly_mult_closed:
  assumes "p \<in> poly_carrier" "q \<in> poly_carrier"
  shows "p \<otimes>\<^sub>P q \<in> poly_carrier"
proof (rule poly_carrierI)
  let ?B = "(if {i. p i \<noteq> \<zero>} = {} then 0 else Max {i. p i \<noteq> \<zero>})
          + (if {i. q i \<noteq> \<zero>} = {} then 0 else Max {i. q i \<noteq> \<zero>})"
  have "{i. (p \<otimes>\<^sub>P q) i \<noteq> \<zero>} \<subseteq> {..?B}"
    by (fastforce simp: intro: poly_mult_support_bound[OF assms])
  then show "finite {i. (p \<otimes>\<^sub>P q) i \<noteq> \<zero>}" by (rule finite_subset) simp
  show "\<And>i. (p \<otimes>\<^sub>P q) i \<in> R" using assms by (rule poly_mult_coeff_closed)
qed

subsection \<open>Distribution of multiplication over finite additive sums\<close>

text \<open>A fixed factor distributes over an additive finite sum (left and right versions).\<close>
lemma fincomp_mult_distrib_left:
  assumes "a \<in> R" and "g \<in> A \<rightarrow> R"
  shows "a \<cdot> additive.fincomp g A = additive.fincomp (\<lambda>i. a \<cdot> g i) A"
proof (cases "finite A")
  case True
  then show ?thesis using assms
  proof (induct A rule: finite_induct)
    case empty then show ?case by simp
  next
    case (insert x A)
    then have "a \<cdot> additive.fincomp g (insert x A) = a \<cdot> g x + additive.fincomp (\<lambda>i. a \<cdot> g i) A"
      by (simp add: distributive)
    also have "\<dots> = additive.fincomp (\<lambda>i. a \<cdot> g i) (insert x A)"
    proof -
      have "(\<lambda>i. a \<cdot> g i) \<in> A \<rightarrow> R" using insert assms by auto
      then show ?thesis using insert assms by (simp add: additive.fincomp_insert)
    qed
    finally show ?case .
  qed
next
  case False
  then show ?thesis using assms by (simp add: additive.fincomp_infinite)
qed

lemma fincomp_mult_distrib_right:
  assumes "a \<in> R" and "g \<in> A \<rightarrow> R"
  shows "additive.fincomp g A \<cdot> a = additive.fincomp (\<lambda>i. g i \<cdot> a) A"
proof (cases "finite A")
  case True
  then show ?thesis using assms
  proof (induct A rule: finite_induct)
    case empty then show ?case by simp
  next
    case (insert x A)
    then have "additive.fincomp g (insert x A) \<cdot> a = g x \<cdot> a + additive.fincomp (\<lambda>i. g i \<cdot> a) A"
      by (simp add: distributive)
    also have "\<dots> = additive.fincomp (\<lambda>i. g i \<cdot> a) (insert x A)"
    proof -
      have "(\<lambda>i. g i \<cdot> a) \<in> A \<rightarrow> R" using insert assms by auto
      then show ?thesis using insert assms by (simp add: additive.fincomp_insert)
    qed
    finally show ?case .
  qed
next
  case False
  then show ?thesis using assms by (simp add: additive.fincomp_infinite)
qed


subsection \<open>Pointwise additive structure\<close>

lemma poly_add_assoc:
  "\<lbrakk> p \<in> poly_carrier; q \<in> poly_carrier; r \<in> poly_carrier \<rbrakk>
     \<Longrightarrow> (p \<oplus>\<^sub>P q) \<oplus>\<^sub>P r = p \<oplus>\<^sub>P (q \<oplus>\<^sub>P r)"
  by (auto simp: poly_add_def additive.associative poly_carrier_coeff_closed)

lemma poly_add_comm:
  "\<lbrakk> p \<in> poly_carrier; q \<in> poly_carrier \<rbrakk> \<Longrightarrow> p \<oplus>\<^sub>P q = q \<oplus>\<^sub>P p"
  by (auto simp: poly_add_def additive.commutative poly_carrier_coeff_closed)

lemma poly_add_zero: "p \<in> poly_carrier \<Longrightarrow> \<zero>\<^sub>P \<oplus>\<^sub>P p = p"
  by (auto simp: poly_add_def poly_zero_def poly_carrier_coeff_closed)

lemma poly_neg_closed: "p \<in> poly_carrier \<Longrightarrow> \<ominus>\<^sub>P p \<in> poly_carrier"
proof (rule poly_carrierI)
  assume p: "p \<in> poly_carrier"
  have "{i. (\<ominus>\<^sub>P p) i \<noteq> \<zero>} \<subseteq> {i. p i \<noteq> \<zero>}"
    using additive.inverse_unit poly_neg_def by force
  then show "finite {i. (\<ominus>\<^sub>P p) i \<noteq> \<zero>}"
    using p poly_carrier_finite finite_subset by blast 
  show "\<And>i. (\<ominus>\<^sub>P p) i \<in> R" using p by (simp add: poly_neg_def poly_carrier_coeff_closed)
qed

lemma poly_add_neg: "p \<in> poly_carrier \<Longrightarrow> (\<ominus>\<^sub>P p) \<oplus>\<^sub>P p = \<zero>\<^sub>P"
  by (auto simp: poly_add_def poly_neg_def poly_zero_def poly_carrier_coeff_closed)

lemma poly_add_neg_right: "p \<in> poly_carrier \<Longrightarrow> p \<oplus>\<^sub>P (\<ominus>\<^sub>P p) = \<zero>\<^sub>P"
  using poly_add_comm poly_add_neg poly_neg_closed by force

text \<open>Additive cancellation: @{text "x \<oplus> (a \<oplus> \<ominus>x) = a"} for carrier polynomials.\<close>
lemma poly_add_minus_cancel:
  assumes "x \<in> poly_carrier" "a \<in> poly_carrier"
  shows "x \<oplus>\<^sub>P (a \<oplus>\<^sub>P (\<ominus>\<^sub>P x)) = a"
  by (metis assms poly_add_assoc poly_add_comm poly_add_neg_right poly_add_zero poly_neg_closed)

text \<open>Left cancellation for polynomial addition.\<close>
lemma poly_add_left_cancel:
  assumes x: "x \<in> poly_carrier" and a: "a \<in> poly_carrier" and b: "b \<in> poly_carrier"
    and eq: "x \<oplus>\<^sub>P a = x \<oplus>\<^sub>P b"
  shows "a = b"
  by (metis a b eq poly_add_assoc poly_add_minus_cancel poly_neg_closed x)

text \<open>The negation is the unique additive inverse.\<close>
lemma poly_minus_unique:
  assumes x: "x \<in> poly_carrier" and y: "y \<in> poly_carrier" and z: "x \<oplus>\<^sub>P y = \<zero>\<^sub>P"
  shows "y = \<ominus>\<^sub>P x"
  using poly_add_left_cancel poly_add_neg_right poly_neg_closed x y z by presburger

text \<open>Double negation.\<close>
lemma poly_neg_neg:
  assumes x: "x \<in> poly_carrier" shows "\<ominus>\<^sub>P (\<ominus>\<^sub>P x) = x"
  using poly_add_neg poly_minus_unique poly_neg_closed x by presburger

text \<open>Reassociation: \<open>(u \<oplus> a) \<oplus> c = (u \<oplus> c) \<oplus> a\<close> in the abelian group.\<close>
lemma poly_add_swap_right:
  assumes u: "u \<in> poly_carrier" and a: "a \<in> poly_carrier" and c: "c \<in> poly_carrier"
  shows "(u \<oplus>\<^sub>P a) \<oplus>\<^sub>P c = (u \<oplus>\<^sub>P c) \<oplus>\<^sub>P a"
  by (metis a c poly_add_assoc poly_add_comm u)

text \<open>Subtracting one equation from another: if \<open>u \<oplus> a = v \<oplus> b\<close> then
  \<open>u \<oplus> \<ominus>v = b \<oplus> \<ominus>a\<close>.\<close>
lemma poly_sub_shift:
  assumes u: "u \<in> poly_carrier" and v: "v \<in> poly_carrier"
    and a: "a \<in> poly_carrier" and b: "b \<in> poly_carrier"
    and eq: "u \<oplus>\<^sub>P a = v \<oplus>\<^sub>P b"
  shows "u \<oplus>\<^sub>P (\<ominus>\<^sub>P v) = b \<oplus>\<^sub>P (\<ominus>\<^sub>P a)"
proof -
  have nv: "\<ominus>\<^sub>P v \<in> poly_carrier" and na: "\<ominus>\<^sub>P a \<in> poly_carrier"
    using u v a b by (auto simp: poly_neg_closed)
  \<comment> \<open>Add \<open>\<ominus>v\<close> and \<open>\<ominus>a\<close> to both sides of \<open>u \<oplus> a = v \<oplus> b\<close>.\<close>
  have "(u \<oplus>\<^sub>P a) \<oplus>\<^sub>P ((\<ominus>\<^sub>P v) \<oplus>\<^sub>P (\<ominus>\<^sub>P a)) = (v \<oplus>\<^sub>P b) \<oplus>\<^sub>P ((\<ominus>\<^sub>P v) \<oplus>\<^sub>P (\<ominus>\<^sub>P a))"
    using eq by simp
  \<comment> \<open>LHS reduces to \<open>u \<oplus> \<ominus>v\<close>, RHS to \<open>b \<oplus> \<ominus>a\<close>.\<close>
  moreover have "(u \<oplus>\<^sub>P a) \<oplus>\<^sub>P ((\<ominus>\<^sub>P v) \<oplus>\<^sub>P (\<ominus>\<^sub>P a)) = u \<oplus>\<^sub>P (\<ominus>\<^sub>P v)"
    by (simp add: a na nv poly_add_assoc poly_add_closed poly_add_minus_cancel u)
  moreover have "(v \<oplus>\<^sub>P b) \<oplus>\<^sub>P ((\<ominus>\<^sub>P v) \<oplus>\<^sub>P (\<ominus>\<^sub>P a)) = b \<oplus>\<^sub>P (\<ominus>\<^sub>P a)"
    by (metis b na nv poly_add_assoc poly_add_closed poly_add_minus_cancel v)
  ultimately show ?thesis by simp
qed

text \<open>If \<open>x \<oplus> \<ominus>y = \<zero>\<close> then @{term "x = y"}.\<close>
lemma poly_diff_zero_eq:
  assumes "x \<in> poly_carrier" and "y \<in> poly_carrier" and "x \<oplus>\<^sub>P (\<ominus>\<^sub>P y) = \<zero>\<^sub>P"
  shows "x = y"
  by (metis poly_add_comm poly_add_minus_cancel poly_add_zero poly_zero_closed assms)


subsection \<open>Multiplicative unit\<close>

lemma poly_mult_one_left:
  assumes p: "p \<in> poly_carrier"
  shows "\<one>\<^sub>P \<otimes>\<^sub>P p = p"
proof
  fix k
  have "(\<one>\<^sub>P \<otimes>\<^sub>P p) k = additive.fincomp (\<lambda>i. \<one>\<^sub>P i \<cdot> p (k - i)) {..k}"
    by (simp add: poly_mult_def)
  also have "\<dots> = additive.fincomp (\<lambda>j. if j = 0 then (\<lambda>_. p k) j else \<zero>) {..k}"
    using p by (intro additive.fincomp_cong') (auto simp: poly_one_def poly_carrier_coeff_closed)
  also have "\<dots> = p k"
    using p by (simp add: additive.fincomp_singleton_swap poly_carrier_coeff_closed)
  finally show "(\<one>\<^sub>P \<otimes>\<^sub>P p) k = p k" .
qed

lemma poly_mult_one_right:
  assumes p: "p \<in> poly_carrier"
  shows "p \<otimes>\<^sub>P \<one>\<^sub>P = p"
proof
  fix k
  have "(p \<otimes>\<^sub>P \<one>\<^sub>P) k = additive.fincomp (\<lambda>i. p i \<cdot> \<one>\<^sub>P (k - i)) {..k}"
    by (simp add: poly_mult_def)
  also have "\<dots> = additive.fincomp (\<lambda>j. if j = k then (\<lambda>_. p k) j else \<zero>) {..k}"
    using p by (intro additive.fincomp_cong') (auto simp: poly_one_def poly_carrier_coeff_closed)
  also have "\<dots> = p k"
    using p by (simp add: additive.fincomp_singleton_swap poly_carrier_coeff_closed)
  finally show "(p \<otimes>\<^sub>P \<one>\<^sub>P) k = p k" .
qed


subsection \<open>Distributivity\<close>

lemma poly_mult_add_distrib_left:
  assumes p: "p \<in> poly_carrier" and q: "q \<in> poly_carrier" and r: "r \<in> poly_carrier"
  shows "p \<otimes>\<^sub>P (q \<oplus>\<^sub>P r) = (p \<otimes>\<^sub>P q) \<oplus>\<^sub>P (p \<otimes>\<^sub>P r)"
proof
  fix k
  have pi: "\<And>i. p i \<in> R" and qi: "\<And>i. q i \<in> R" and ri: "\<And>i. r i \<in> R"
    using p q r by (auto simp: poly_carrier_coeff_closed)
  have "(p \<otimes>\<^sub>P (q \<oplus>\<^sub>P r)) k = additive.fincomp (\<lambda>i. p i \<cdot> (q (k - i) + r (k - i))) {..k}"
    by (simp add: poly_mult_def poly_add_def)
  also have "\<dots> = additive.fincomp (\<lambda>i. p i \<cdot> q (k - i) + p i \<cdot> r (k - i)) {..k}"
    using distributive(1) pi qi ri by presburger
  also have "\<dots> = additive.fincomp (\<lambda>i. p i \<cdot> q (k - i)) {..k}
                  + additive.fincomp (\<lambda>i. p i \<cdot> r (k - i)) {..k}"
    by (rule additive.fincomp_comp) (use pi qi ri in auto)
  also have "\<dots> = ((p \<otimes>\<^sub>P q) \<oplus>\<^sub>P (p \<otimes>\<^sub>P r)) k"
    by (simp add: poly_mult_def poly_add_def)
  finally show "(p \<otimes>\<^sub>P (q \<oplus>\<^sub>P r)) k = ((p \<otimes>\<^sub>P q) \<oplus>\<^sub>P (p \<otimes>\<^sub>P r)) k" .
qed

lemma poly_mult_add_distrib_right:
  assumes p: "p \<in> poly_carrier" and q: "q \<in> poly_carrier" and r: "r \<in> poly_carrier"
  shows "(q \<oplus>\<^sub>P r) \<otimes>\<^sub>P p = (q \<otimes>\<^sub>P p) \<oplus>\<^sub>P (r \<otimes>\<^sub>P p)"
proof
  fix k
  have pi: "\<And>i. p i \<in> R" and qi: "\<And>i. q i \<in> R" and ri: "\<And>i. r i \<in> R"
    using p q r by (auto simp: poly_carrier_coeff_closed)
  have "((q \<oplus>\<^sub>P r) \<otimes>\<^sub>P p) k = additive.fincomp (\<lambda>i. (q i + r i) \<cdot> p (k - i)) {..k}"
    by (simp add: poly_mult_def poly_add_def)
  also have "\<dots> = additive.fincomp (\<lambda>i. q i \<cdot> p (k - i) + r i \<cdot> p (k - i)) {..k}"
    using distributive(2) pi qi ri by presburger
  also have "\<dots> = additive.fincomp (\<lambda>i. q i \<cdot> p (k - i)) {..k}
                  + additive.fincomp (\<lambda>i. r i \<cdot> p (k - i)) {..k}"
    by (rule additive.fincomp_comp) (use pi qi ri in auto)
  also have "\<dots> = ((q \<otimes>\<^sub>P p) \<oplus>\<^sub>P (r \<otimes>\<^sub>P p)) k"
    by (simp add: poly_mult_def poly_add_def)
  finally show "((q \<oplus>\<^sub>P r) \<otimes>\<^sub>P p) k = ((q \<otimes>\<^sub>P p) \<oplus>\<^sub>P (r \<otimes>\<^sub>P p)) k" .
qed


subsection \<open>A Fubini law for the additive finite sum\<close>

text \<open>A nested additive sum equals the sum over the dependent product (Sigma) of the index
  sets: \<open>\<Sum>i\<in>I. \<Sum>j\<in>A i. g i j  =  \<Sum>(i,j)\<in>Sigma I A. g i j\<close>.\<close>
lemma fincomp_Sigma:
  assumes I: "finite I" and A: "\<And>i. i \<in> I \<Longrightarrow> finite (A i)"
    and g: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> A i \<Longrightarrow> g i j \<in> R"
  shows "additive.fincomp (\<lambda>i. additive.fincomp (g i) (A i)) I
         = additive.fincomp (\<lambda>p. g (fst p) (snd p)) (Sigma I A)"
proof -
  have disj: "pairwise (\<lambda>i j. disjnt ({i} \<times> A i) ({j} \<times> A j)) I"
    by (auto simp: pairwise_def disjnt_def)
  have "additive.fincomp (\<lambda>p. g (fst p) (snd p)) (Sigma I A)
        = additive.fincomp (\<lambda>p. g (fst p) (snd p)) (\<Union>i\<in>I. {i} \<times> A i)"
    by (simp add: Sigma_def)
  also have "\<dots> = additive.fincomp (\<lambda>i. additive.fincomp (\<lambda>p. g (fst p) (snd p)) ({i} \<times> A i)) I"
    using A I by (intro additive.fincomp_UN_disjoint disj g) auto
  also have "\<dots> = additive.fincomp (\<lambda>i. additive.fincomp (g i) (A i)) I"
  proof (rule additive.fincomp_cong')
    fix i assume i: "i \<in> I"
    have "{i} \<times> A i = Pair i ` A i" by auto
    then have "additive.fincomp (\<lambda>p. g (fst p) (snd p)) ({i} \<times> A i)
          = additive.fincomp (\<lambda>p. g (fst p) (snd p)) (Pair i ` A i)"
      by simp
    also have "\<dots> = additive.fincomp (\<lambda>j. g (fst (Pair i j)) (snd (Pair i j))) (A i)"
    proof (rule additive.fincomp_reindex)
      show "(\<lambda>p. g (fst p) (snd p)) \<in> Pair i ` A i \<rightarrow> R" using i g by auto
      show "inj_on (Pair i) (A i)" by (simp add: inj_on_def)
    qed
    also have "\<dots> = additive.fincomp (g i) (A i)" by simp
    finally show "additive.fincomp (\<lambda>p. g (fst p) (snd p)) ({i} \<times> A i)
                    = additive.fincomp (g i) (A i)" .
  qed (use I A g additive.fincomp_closed in auto)
  finally show ?thesis ..
qed


subsection \<open>Associativity of convolution\<close>

lemma poly_mult_assoc:
  assumes p: "p \<in> poly_carrier" and q: "q \<in> poly_carrier" and r: "r \<in> poly_carrier"
  shows "(p \<otimes>\<^sub>P q) \<otimes>\<^sub>P r = p \<otimes>\<^sub>P (q \<otimes>\<^sub>P r)"
proof
  fix n
  have pi: "\<And>i. p i \<in> R" and qi: "\<And>i. q i \<in> R" and ri: "\<And>i. r i \<in> R"
    using p q r by (auto simp: poly_carrier_coeff_closed)
  \<comment> \<open>LHS as a sum over the triangle @{text "{(j,i). i \<le> j \<le> n}"}.\<close>
  have "((p \<otimes>\<^sub>P q) \<otimes>\<^sub>P r) n
        = additive.fincomp (\<lambda>j. additive.fincomp (\<lambda>i. p i \<cdot> q (j - i)) {..j} \<cdot> r (n - j)) {..n}"
    by (simp add: poly_mult_def)
  also have "\<dots> = additive.fincomp
                    (\<lambda>j. additive.fincomp (\<lambda>i. (p i \<cdot> q (j - i)) \<cdot> r (n - j)) {..j}) {..n}"
    using pi qi ri
    by (intro additive.fincomp_cong' fincomp_mult_distrib_right) auto
  also have "\<dots> = additive.fincomp (\<lambda>x. (p (snd x) \<cdot> q (fst x - snd x)) \<cdot> r (n - fst x))
                    (Sigma {..n} (\<lambda>j. {..j}))"
    by (rule fincomp_Sigma) (use pi qi ri in auto)
  finally have LHS: "((p \<otimes>\<^sub>P q) \<otimes>\<^sub>P r) n
        = additive.fincomp (\<lambda>x. (p (snd x) \<cdot> q (fst x - snd x)) \<cdot> r (n - fst x))
            (Sigma {..n} (\<lambda>j. {..j}))" .
  \<comment> \<open>RHS as a sum over the triangle @{text "{(i,j). j \<le> n - i}"}.\<close>
  have "(p \<otimes>\<^sub>P (q \<otimes>\<^sub>P r)) n
        = additive.fincomp (\<lambda>i. p i \<cdot> additive.fincomp (\<lambda>j. q j \<cdot> r (n - i - j)) {..n - i}) {..n}"
    by (simp add: poly_mult_def)
  also have "\<dots> = additive.fincomp
                    (\<lambda>i. additive.fincomp (\<lambda>j. p i \<cdot> (q j \<cdot> r (n - i - j))) {..n - i}) {..n}"
    using pi qi ri
    by (intro additive.fincomp_cong' fincomp_mult_distrib_left) auto
  also have "\<dots> = additive.fincomp (\<lambda>x. p (fst x) \<cdot> (q (snd x) \<cdot> r (n - fst x - snd x)))
                    (Sigma {..n} (\<lambda>i. {..n - i}))"
    by (rule fincomp_Sigma) (use pi qi ri in auto)
  finally have RHS: "(p \<otimes>\<^sub>P (q \<otimes>\<^sub>P r)) n
        = additive.fincomp (\<lambda>x. p (fst x) \<cdot> (q (snd x) \<cdot> r (n - fst x - snd x)))
            (Sigma {..n} (\<lambda>i. {..n - i}))" .
  \<comment> \<open>Reindex the LHS triangle to the RHS triangle by @{text "(j,i) \<mapsto> (i, j - i)"}.\<close>
  let ?h = "\<lambda>x::nat\<times>nat. (snd x, fst x - snd x)"
  let ?h' = "\<lambda>x::nat\<times>nat. (fst x + snd x, fst x)"
  have bij: "bij_betw ?h (Sigma {..n} (\<lambda>j. {..j})) (Sigma {..n} (\<lambda>i. {..n - i}))"
    by (rule bij_betw_byWitness[where f' = ?h']) auto
  let ?F = "\<lambda>x. p (fst x) \<cdot> (q (snd x) \<cdot> r (n - fst x - snd x))"
  have "additive.fincomp ?F (Sigma {..n} (\<lambda>i. {..n - i}))
        = additive.fincomp ?F (?h ` Sigma {..n} (\<lambda>j. {..j}))"
    using bij bij_betw_imp_surj_on by fastforce
  also have "\<dots> = additive.fincomp (\<lambda>x. ?F (?h x)) (Sigma {..n} (\<lambda>j. {..j}))"
  proof (rule additive.fincomp_reindex)
    show "?F \<in> ?h ` Sigma {..n} (\<lambda>j. {..j}) \<rightarrow> R" using pi qi ri by auto
    show "inj_on ?h (Sigma {..n} (\<lambda>j. {..j}))"
      using bij bij_betw_imp_inj_on by blast
  qed
  also have "\<dots> = additive.fincomp (\<lambda>x. (p (snd x) \<cdot> q (fst x - snd x)) \<cdot> r (n - fst x))
                    (Sigma {..n} (\<lambda>j. {..j}))"
    using pi qi ri multiplicative.associative
    by (intro additive.fincomp_cong') auto
  finally show "((p \<otimes>\<^sub>P q) \<otimes>\<^sub>P r) n = (p \<otimes>\<^sub>P (q \<otimes>\<^sub>P r)) n"
    using LHS RHS by simp
qed


subsection \<open>Coefficients, degree, monomials, constants, and the variable\<close>

text \<open>The coefficient map is just function application (kept as a named operation to mirror
  the HOL-Algebra polynomial interface).\<close>
definition coeff :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"
  where "coeff p = p"

lemma coeff_eq [simp]: "coeff p i = p i"
  by (simp add: coeff_def)

text \<open>The degree is the greatest index with a nonzero coefficient (and @{term 0} for the zero
  polynomial, as is conventional here).\<close>
definition degree :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat"
  where "degree p = (if {i. p i \<noteq> \<zero>} = {} then 0 else Max {i. p i \<noteq> \<zero>})"

lemma degree_zero [simp]: "degree \<zero>\<^sub>P = 0"
  by (simp add: degree_def poly_zero_def)

lemma coeff_gt_degree:
  assumes "p \<in> poly_carrier" and "degree p < i"
  shows "p i = \<zero>"
proof (rule ccontr)
  assume "p i \<noteq> \<zero>"
  then have \<section>: "{i. p i \<noteq> \<zero>} \<noteq> {}" by blast
  moreover have "finite {i. p i \<noteq> \<zero>}" using assms(1) by (rule poly_carrier_finite)
  ultimately have "i \<le> Max {i. p i \<noteq> \<zero>}" using \<open>p i \<noteq> \<zero>\<close> by simp
  then show False using assms(2)
    by (metis \<section> degree_def linorder_not_le)
qed

text \<open>A degree bound: @{term "degree p \<le> n"} exactly when all coefficients above @{term n}
  vanish (for a polynomial, whose support is finite).\<close>
lemma degree_le_iff:
  assumes "p \<in> poly_carrier"
  shows "degree p \<le> n \<longleftrightarrow> (\<forall>i>n. p i = \<zero>)"
proof
  assume "degree p \<le> n"
  then show "\<forall>i>n. p i = \<zero>" using coeff_gt_degree[OF assms] by force
next
  assume *: "\<forall>i>n. p i = \<zero>"
  show "degree p \<le> n"
    using "*" assms degree_def linorder_le_less_linear poly_carrier_finite by force
qed

lemma degree_leI:
  "\<lbrakk> p \<in> poly_carrier; \<And>i. i > n \<Longrightarrow> p i = \<zero> \<rbrakk> \<Longrightarrow> degree p \<le> n"
  by (simp add: degree_le_iff)

text \<open>Negation preserves the support, hence the degree (for carrier polynomials).\<close>
lemma degree_neg:
  assumes p: "p \<in> poly_carrier" shows "degree (\<ominus>\<^sub>P p) = degree p"
proof -
  have "\<And>x. (\<ominus>\<^sub>P p) x = \<zero> \<Longrightarrow> p x = \<zero>"
    by (metis additive.inverse_unit p poly_neg_def poly_neg_neg)
  then have "{i. (\<ominus>\<^sub>P p) i \<noteq> \<zero>} = {i. p i \<noteq> \<zero>}"
    by (metis additive.inverse_unit poly_neg_def)
  then show ?thesis by (simp add: degree_def)
qed


subsection \<open>Polynomials of bounded degree\<close>

text \<open>The polynomials supported on @{text "{..<n}"} --- those of degree below @{term n}, together
  with the zero polynomial.  These are exactly the carrier polynomials whose coefficients vanish
  from index @{term n} on.  When the coefficient ring is finite, there are @{text "\<bar>R\<bar>\<^sup>n"} of them;
  they serve as the canonical representatives of @{text "F[X]/(b)"} for @{term b} of degree
  @{term n}.\<close>
definition low_poly :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) set"
  where "low_poly n = {p. p \<in> poly_carrier \<and> (\<forall>i\<ge>n. p i = \<zero>)}"

lemma low_polyI:
  "\<lbrakk> p \<in> poly_carrier; \<And>i. i \<ge> n \<Longrightarrow> p i = \<zero> \<rbrakk> \<Longrightarrow> p \<in> low_poly n"
  unfolding low_poly_def by blast

lemma low_poly_closed: "p \<in> low_poly n \<Longrightarrow> p \<in> poly_carrier"
  unfolding low_poly_def by blast

lemma low_poly_coeff: "\<lbrakk> p \<in> low_poly n; i \<ge> n \<rbrakk> \<Longrightarrow> p i = \<zero>"
  unfolding low_poly_def by blast

text \<open>The low-degree polynomials form a subgroup of the additive group, and this is immediate
  \<^emph>\<open>coefficientwise\<close>: the operations are pointwise, so no reasoning about degrees is needed.\<close>

\<comment> \<open>@{thm [source] low_poly_coeff} and @{thm [source] low_poly_closed} must \<^emph>\<open>not\<close> go into a simp
    set: both leave @{term n} schematic, so simp searches for a bound rather than using one, and does
    not terminate.  These proofs therefore name their instances.\<close>

lemma low_poly_zero [simp]: "\<zero>\<^sub>P \<in> low_poly n"
proof (rule low_polyI)
  show "\<zero>\<^sub>P \<in> poly_carrier" by (rule poly_zero_closed)
  show "\<And>i. n \<le> i \<Longrightarrow> \<zero>\<^sub>P i = \<zero>" by (simp add: poly_zero_def)
qed

lemma low_poly_add_closed:
  assumes p: "p \<in> low_poly n" and q: "q \<in> low_poly n" shows "p \<oplus>\<^sub>P q \<in> low_poly n"
proof (rule low_polyI)
  have pc: "p \<in> poly_carrier" and qc: "q \<in> poly_carrier"
    using p q by (blast intro: low_poly_closed)+
  show "p \<oplus>\<^sub>P q \<in> poly_carrier" using pc qc by (rule poly_add_closed)
next
  fix i assume i: "n \<le> i"
  have "p i = \<zero>" and "q i = \<zero>"
    using low_poly_coeff [OF p i] low_poly_coeff [OF q i] by blast+
  then show "(p \<oplus>\<^sub>P q) i = \<zero>"
    by (simp add: poly_add_def additive.left_unit)
qed

lemma low_poly_neg_closed:
  assumes p: "p \<in> low_poly n" shows "\<ominus>\<^sub>P p \<in> low_poly n"
proof (rule low_polyI)
  show "\<ominus>\<^sub>P p \<in> poly_carrier" using low_poly_closed [OF p] by (rule poly_neg_closed)
next
  fix i assume i: "n \<le> i"
  have "p i = \<zero>" using low_poly_coeff [OF p i] .
  then show "(\<ominus>\<^sub>P p) i = \<zero>" by (simp add: poly_neg_def additive.inverse_unit)
qed

lemma low_poly_one:
  assumes n: "0 < n" shows "\<one>\<^sub>P \<in> low_poly n"
proof (rule low_polyI)
  show "\<one>\<^sub>P \<in> poly_carrier" by (rule poly_one_closed)
next
  fix i assume "n \<le> i"
  with n show "\<one>\<^sub>P i = \<zero>" by (simp add: poly_one_def)
qed

text \<open>Membership of @{const low_poly} in terms of degree: a carrier polynomial lies in
  @{term "low_poly n"} iff it is zero or has degree below @{term n}.\<close>
lemma low_poly_iff_degree:
  assumes p: "p \<in> poly_carrier"
  shows "p \<in> low_poly n \<longleftrightarrow> (p = \<zero>\<^sub>P \<or> degree p < n)"
proof
  assume "p \<in> low_poly n"
  then have z: "\<And>i. i \<ge> n \<Longrightarrow> p i = \<zero>" unfolding low_poly_def by blast
  show "p = \<zero>\<^sub>P \<or> degree p < n"
  proof (cases "p = \<zero>\<^sub>P")
    case False
    \<comment> \<open>The support is finite and nonempty, so its maximum @{term "degree p"} lies in it.\<close>
    have fin: "finite {i. p i \<noteq> \<zero>}" using p by (rule poly_carrier_finite)
    have ne: "{i. p i \<noteq> \<zero>} \<noteq> {}" using False by (auto simp: poly_zero_def fun_eq_iff)
    then show ?thesis
      by (metis (mono_tags, lifting) Max_in degree_def fin leI mem_Collect_eq z)
  qed simp
next
  assume "p = \<zero>\<^sub>P \<or> degree p < n"
  then show "p \<in> low_poly n"
    using coeff_gt_degree low_polyI poly_zero_def p by auto
qed

text \<open>Restricting a low-degree polynomial to @{text "{..<n}"} is a bijection onto the coefficient
  vectors @{text "{..<n} \<rightarrow>\<^sub>E R"}; the inverse extends a vector by zero.\<close>
lemma bij_low_poly_PiE:
  "bij_betw (\<lambda>p. restrict p {..<n}) (low_poly n) ({..<n} \<rightarrow>\<^sub>E R)"
proof (rule bij_betw_byWitness[where f' = "\<lambda>f i. if i < n then f i else \<zero>"])
  show "\<forall>p\<in>low_poly n. (\<lambda>i. if i < n then restrict p {..<n} i else \<zero>) = p"
    by (auto simp: low_poly_def not_less)
  show "\<forall>f\<in>{..<n} \<rightarrow>\<^sub>E R. restrict (\<lambda>i. if i < n then f i else \<zero>) {..<n} = f"
    by (auto simp: restrict_def PiE_def extensional_def fun_eq_iff)
  show "(\<lambda>p. restrict p {..<n}) ` low_poly n \<subseteq> {..<n} \<rightarrow>\<^sub>E R"
    using low_poly_closed poly_carrier_coeff_closed by force
  show "(\<lambda>f i. if i < n then f i else \<zero>) ` ({..<n} \<rightarrow>\<^sub>E R) \<subseteq> low_poly n"
  proof
    fix p assume "p \<in> (\<lambda>f i. if i < n then f i else \<zero>) ` ({..<n} \<rightarrow>\<^sub>E R)"
    then obtain f where f: "f \<in> {..<n} \<rightarrow>\<^sub>E R" and pf: "p = (\<lambda>i. if i < n then f i else \<zero>)" by blast
    have "p \<in> poly_carrier"
      using f by (intro poly_carrierI) (auto simp: pf)
    then show "p \<in> low_poly n" using pf by (auto intro!: low_polyI)
  qed
qed

text \<open>Hence, over a finite coefficient ring, there are exactly @{text "\<bar>R\<bar>\<^sup>n"} polynomials of
  degree below @{term n}.\<close>
theorem card_low_poly:
  assumes "finite R" shows "card (low_poly n) = card R ^ n"
  using bij_betw_same_card [OF bij_low_poly_PiE] by (simp add: card_PiE)

text \<open>The constant polynomial with value @{term a}.\<close>
definition poly_const :: "'a \<Rightarrow> (nat \<Rightarrow> 'a)"
  where "poly_const a = (\<lambda>i. if i = 0 then a else \<zero>)"

lemma poly_const_closed: "a \<in> R \<Longrightarrow> poly_const a \<in> poly_carrier"
  by (simp add: poly_carrier_def poly_const_def)

lemma poly_const_zero [simp]: "poly_const \<zero> = \<zero>\<^sub>P"
  by (simp add: poly_const_def poly_zero_def)

lemma poly_const_one [simp]: "poly_const \<one> = \<one>\<^sub>P"
  by (simp add: poly_const_def poly_one_def)

text \<open>The monomial @{text "a X\<^sup>n"}: the coefficient @{term a} at degree @{term n}.\<close>
definition monom :: "'a \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a)"
  where "monom a n = (\<lambda>i. if i = n then a else \<zero>)"

lemma monom_closed: "a \<in> R \<Longrightarrow> monom a n \<in> poly_carrier"
  by (simp add: monom_def poly_carrier_def)

lemma monom_0_eq_const: "monom a 0 = poly_const a"
  by (simp add: monom_def poly_const_def)

text \<open>The variable @{text X} is the monomial @{text "\<one> X\<^sup>1"}.\<close>
definition var :: "nat \<Rightarrow> 'a"  (\<open>X\<^sub>P\<close>)
  where "var = monom \<one> 1"

lemma var_closed: "X\<^sub>P \<in> poly_carrier"
  by (simp add: var_def monom_closed)

lemma coeff_var: "X\<^sub>P i = (if i = 1 then \<one> else \<zero>)"
  by (simp add: var_def monom_def)

text \<open>Multiplying by a monomial @{text "monom c k"} shifts coefficients up by @{term k} and
  scales by @{term c}: @{text "(monom c k \<otimes> b) j = (if k \<le> j then c \<cdot> b (j - k) else \<zero>)"}.\<close>
lemma coeff_monom_mult:
  assumes c: "c \<in> R" and b: "b \<in> poly_carrier"
  shows "(monom c k \<otimes>\<^sub>P b) j = (if k \<le> j then c \<cdot> b (j - k) else \<zero>)"
proof -
  have bi: "\<And>i. b i \<in> R" using b by (simp add: poly_carrier_coeff_closed)
  have "(monom c k \<otimes>\<^sub>P b) j = additive.fincomp (\<lambda>i. monom c k i \<cdot> b (j - i)) {..j}"
    by (simp add: poly_mult_def)
  also have "\<dots> = additive.fincomp (\<lambda>i. if i = k then c \<cdot> b (j - k) else \<zero>) {..j}"
    by (rule additive.fincomp_cong') (use c bi in \<open>auto simp: monom_def\<close>)
  finally have eq: "(monom c k \<otimes>\<^sub>P b) j
                    = additive.fincomp (\<lambda>i. if i = k then c \<cdot> b (j - k) else \<zero>) {..j}" .
  show ?thesis
  proof (cases "k \<le> j")
    case True
    then have "k \<in> {..j}" by simp
    have "additive.fincomp (\<lambda>i. if i = k then (\<lambda>_. c \<cdot> b (j - k)) i else \<zero>) {..j}
            = (\<lambda>_. c \<cdot> b (j - k)) k"
      by (rule additive.fincomp_singleton_swap[OF \<open>k \<in> {..j}\<close>]) (use c bi in auto)
    then show ?thesis using eq True by simp
  next
    case False
    then have "\<And>i. i \<in> {..j} \<Longrightarrow> (if i = k then c \<cdot> b (j - k) else \<zero>) = \<zero>" by auto
    then show ?thesis using eq False
      by (smt (verit) additive.fincomp_unit_eqI)
  qed
qed

text \<open>Degrees of the basic polynomials (support-based, so no carrier hypothesis needed).\<close>
text \<open>Multiplying a monomial by the variable raises its exponent, and multiplying by a constant
  scales its coefficient.  \<^emph>\<open>Stated with @{const Suc} and at exponent zero deliberately:\<close> the general
  law @{text "monom a k \<otimes> monom b l = monom (a \<cdot> b) (k + l)"} cannot be written here, because \<open>+\<close> on
  two free variables is ambiguous between @{const Groups.plus} and the ring's own addition and
  Isabelle finds both readings type correct.  These two instances are all that is needed.\<close>

lemma var_mult_monom:
  assumes a: "a \<in> R" shows "X\<^sub>P \<otimes>\<^sub>P monom a k = monom a (Suc k)"
proof
  fix j
  have one: "\<one> \<in> R" by simp
  have step: "(monom \<one> (Suc 0) \<otimes>\<^sub>P monom a k) j
              = (if Suc 0 \<le> j then \<one> \<cdot> monom a k (j - Suc 0) else \<zero>)"
    by (rule coeff_monom_mult [OF one monom_closed [OF a]])
  have "(X\<^sub>P \<otimes>\<^sub>P monom a k) j
        = (if Suc 0 \<le> j then \<one> \<cdot> monom a k (j - Suc 0) else \<zero>)"
    using step by (simp add: var_def)
  also have "\<dots> = monom a (Suc k) j" using a by (auto simp: monom_def)
  finally show "(X\<^sub>P \<otimes>\<^sub>P monom a k) j = monom a (Suc k) j" .
qed

lemma degree_monom_le: "degree (monom a n) \<le> n"
proof -
  have sub: "{i. monom a n i \<noteq> \<zero>} \<subseteq> {n}" by (auto simp: monom_def)
  show ?thesis
    by (metis Max_singleton degree_def le0 order_refl sub subset_singleton_iff)
qed

text \<open>A monomial is zero exactly when its coefficient is zero.  In particular, a nonzero
  monomial has the advertised degree, not merely the upper bound above.\<close>
lemma monom_eq_zero_iff [simp]:
  "monom a n = \<zero>\<^sub>P \<longleftrightarrow> a = \<zero>"
proof
  assume "monom a n = \<zero>\<^sub>P"
  then have h: "\<forall>i. monom a n i = \<zero>\<^sub>P i"
    by (simp add: fun_eq_iff)
  have hn: "monom a n n = \<zero>\<^sub>P n" using h by blast
  then show "a = \<zero>"
    by (simp add: monom_def poly_zero_def)
next
  assume "a = \<zero>"
  then show "monom a n = \<zero>\<^sub>P"
    by (simp add: monom_def poly_zero_def)
qed

lemma degree_monom:
  assumes "a \<noteq> \<zero>"
  shows "degree (monom a n) = n"
proof -
  have support: "{i. monom a n i \<noteq> \<zero>} = {n}"
    using assms by (auto simp: monom_def)
  then show ?thesis by (simp add: degree_def)
qed

lemma degree_poly_const:
  assumes "a \<noteq> \<zero>"
  shows "degree (poly_const a) = 0"
  using degree_monom[OF assms, of 0] by (simp add: monom_0_eq_const)

lemma degree_const_le: "degree (poly_const a) \<le> 0"
  using degree_monom_le[of a 0] by (simp add: monom_0_eq_const)

lemma degree_one [simp]: "degree \<one>\<^sub>P = 0"
  using degree_const_le[of \<one>] by simp

text \<open>In a nontrivial coefficient ring, the variable has degree one.  The explicit hypothesis
  keeps this lemma available in the more general @{locale Ring} context above.\<close>
lemma degree_var:
  assumes "\<one> \<noteq> \<zero>"
  shows "degree X\<^sub>P = 1"
proof -
  have h: "degree (monom \<one> 1) = 1"
  proof (rule degree_monom)
    show "\<one> \<noteq> \<zero>" using assms .
  qed
  then show ?thesis by (simp add: var_def)
qed

text \<open>The product of two constants is the constant of the product.\<close>
lemma poly_const_add:
  assumes a: "a \<in> R" and b: "b \<in> R"
  shows "poly_const a \<oplus>\<^sub>P poly_const b = poly_const (a + b)"
proof
  fix j
  show "(poly_const a \<oplus>\<^sub>P poly_const b) j = poly_const (a + b) j"
    by (cases "j = 0") (simp_all add: poly_add_def poly_const_def additive.left_unit)
qed

lemma poly_const_mult:
  assumes a: "a \<in> R" and b: "b \<in> R"
  shows "poly_const a \<otimes>\<^sub>P poly_const b = poly_const (a \<cdot> b)"
proof
  fix j
  have "(poly_const a \<otimes>\<^sub>P poly_const b) j = a \<cdot> poly_const b j"
    using coeff_monom_mult[OF a poly_const_closed[OF b], of 0 j]
    by (simp add: monom_0_eq_const)
  also have "\<dots> = poly_const (a \<cdot> b) j" using a by (simp add: poly_const_def)
  finally show "(poly_const a \<otimes>\<^sub>P poly_const b) j = poly_const (a \<cdot> b) j" .
qed

text \<open>A polynomial of degree @{text 0} is the constant given by its zeroth coefficient.\<close>
lemma degree_zero_imp_const:
  assumes "p \<in> poly_carrier" "degree p = 0"
  shows "p = poly_const (p 0)"
  using assms coeff_gt_degree poly_const_def by auto

lemma degree_add_le:
  assumes "p \<in> poly_carrier" "q \<in> poly_carrier"
  shows "degree (p \<oplus>\<^sub>P q) \<le> max (degree p) (degree q)"
proof (intro degree_leI poly_add_closed assms)
qed (simp add: assms coeff_gt_degree poly_add_def)


text \<open>Multiplication by the zero polynomial.\<close>
lemma
  assumes "p \<in> poly_carrier" 
  shows poly_mult_zero_right: "p \<otimes>\<^sub>P \<zero>\<^sub>P = \<zero>\<^sub>P"
    and poly_mult_zero_left: "\<zero>\<^sub>P \<otimes>\<^sub>P p = \<zero>\<^sub>P"
  using assms by (simp_all add: poly_mult_def poly_zero_def poly_carrier_coeff_closed)

text \<open>The leading coefficient.\<close>
definition lead_coeff :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "lead_coeff p = p (degree p)"

text \<open>The coefficient at the degree is nonzero for a nonzero polynomial.\<close>
lemma coeff_degree_nonzero:
  assumes "p \<in> poly_carrier" and "p \<noteq> \<zero>\<^sub>P"
  shows "p (degree p) \<noteq> \<zero>"
  by (metis antisym assms coeff_gt_degree less_not_refl linorder_not_le low_polyI
      low_poly_iff_degree)

lemma lead_coeff_nonzero:
  "\<lbrakk> p \<in> poly_carrier; p \<noteq> \<zero>\<^sub>P \<rbrakk> \<Longrightarrow> lead_coeff p \<noteq> \<zero>"
  unfolding lead_coeff_def by (rule coeff_degree_nonzero)

text \<open>The coefficient of a product at the sum of the two degrees is the product of the leading
  coefficients: every other term of the convolution vanishes for degree reasons.\<close>
lemma coeff_mult_degree_add:
  assumes p: "p \<in> poly_carrier" and q: "q \<in> poly_carrier"
  shows "(p \<otimes>\<^sub>P q) (degree p + degree q) = p (degree p) \<cdot> q (degree q)"
proof -
  let ?m = "degree p" and ?n = "degree q"
  have pi: "\<And>i. p i \<in> R" and qi: "\<And>i. q i \<in> R"
    using p q by (auto simp: poly_carrier_coeff_closed)
  have "(p \<otimes>\<^sub>P q) (?m + ?n) = additive.fincomp (\<lambda>i. p i \<cdot> q (?m + ?n - i)) {..?m + ?n}"
    by (simp add: poly_mult_def)
  also have "\<dots> = additive.fincomp (\<lambda>i. if i = ?m then p ?m \<cdot> q ?n else \<zero>) {..?m + ?n}"
  proof (rule additive.fincomp_cong')
    fix i assume "i \<in> {..?m + ?n}"
    show "p i \<cdot> q (?m + ?n - i) = (if i = ?m then p ?m \<cdot> q ?n else \<zero>)"
    proof (cases "i = ?m")
      case False
      have "p i \<cdot> q (?m + ?n - i) = \<zero>"
      proof (cases "i > ?m")
        case False
        with pi coeff_gt_degree[OF q] \<open>i \<noteq> ?m\<close> show ?thesis by simp
      qed (simp add: coeff_gt_degree p qi)
      then show ?thesis using False by simp
    qed auto
  qed (use pi qi in auto)
  also have "\<dots> = p ?m \<cdot> q ?n"
    using additive.fincomp_singleton_swap[of ?m "{..?m + ?n}" "\<lambda>_. p ?m \<cdot> q ?n"]
    using pi qi by simp
  finally show ?thesis .
qed

text \<open>The degree of a product is at most the sum of the degrees.\<close>
lemma degree_mult_le:
  assumes p: "p \<in> poly_carrier" and q: "q \<in> poly_carrier"
  shows "degree (p \<otimes>\<^sub>P q) \<le> degree p + degree q"
proof (rule degree_leI)
  show "p \<otimes>\<^sub>P q \<in> poly_carrier" using assms by (rule poly_mult_closed)
  fix i assume i: "i > degree p + degree q"
  \<comment> \<open>Each convolution term @{text "p j \<cdot> q (i - j)"} vanishes: either @{text "j > degree p"}
      or @{text "i - j > degree q"}.\<close>
  have "p j \<cdot> q (i - j) = \<zero>" if "j \<in> {..i}" for j
  proof (cases "j > degree p")
    case True
    then show ?thesis using q coeff_gt_degree[OF p]
      by (simp add: poly_carrier_coeff_closed)
  next
    case False
    then show ?thesis using p i coeff_gt_degree[OF q]
      by (simp add: poly_carrier_coeff_closed)
  qed
  then show "(p \<otimes>\<^sub>P q) i = \<zero>"
    unfolding poly_mult_def by (rule additive.fincomp_unit_eqI)
qed


subsection \<open>The ring structure\<close>

theorem poly_ring: "Ring poly_carrier (\<oplus>\<^sub>P) (\<otimes>\<^sub>P) \<zero>\<^sub>P \<one>\<^sub>P"
proof -
  have add_grp: "Group poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P"
  proof (rule GroupI)
    show "\<And>p. p \<in> poly_carrier \<Longrightarrow> p \<oplus>\<^sub>P \<zero>\<^sub>P = p"
      using poly_add_comm poly_add_zero poly_zero_closed by simp
    show "\<And>p. p \<in> poly_carrier \<Longrightarrow> \<exists>q\<in>poly_carrier. p \<oplus>\<^sub>P q = \<zero>\<^sub>P \<and> q \<oplus>\<^sub>P p = \<zero>\<^sub>P"
      using poly_add_neg poly_add_neg_right poly_neg_closed by blast
  qed (auto simp: poly_add_closed poly_zero_closed poly_add_assoc poly_add_zero)
  interpret add: Group poly_carrier "(\<oplus>\<^sub>P)" "\<zero>\<^sub>P" by (rule add_grp)
  interpret add: Abelian_Group poly_carrier "(\<oplus>\<^sub>P)" "\<zero>\<^sub>P"
    by unfold_locales (rule poly_add_comm)
  interpret mult: Monoid poly_carrier "(\<otimes>\<^sub>P)" "\<one>\<^sub>P"
  proof 
  qed (auto simp: poly_mult_one_left poly_mult_one_right poly_mult_assoc poly_one_closed poly_mult_closed)
  show ?thesis
  proof qed (use poly_mult_add_distrib_left poly_mult_add_distrib_right in auto)
qed


subsection \<open>Evaluation at a point\<close>

text \<open>Powers in the (multiplicative monoid of the) ring.  We define them locally rather than
  importing \<open>Group_Action\<close>'s \<open>Monoid.power\<close>, to keep the polynomial theory's
  dependencies minimal.\<close>
definition rpow :: "'a \<Rightarrow> nat \<Rightarrow> 'a"
  where "rpow a n = (((\<cdot>) a) ^^ n) \<one>"

lemma rpow_0 [simp]: "rpow a 0 = \<one>"
  by (simp add: rpow_def)

lemma rpow_Suc [simp]: "rpow a (Suc n) = a \<cdot> rpow a n"
  by (simp add: rpow_def)

lemma rpow_closed [simp]: "a \<in> R \<Longrightarrow> rpow a n \<in> R"
  by (induct n) auto

text \<open>Evaluation of a polynomial at a point @{term a}: the finite sum
  @{text "\<Sum>\<^bsub>i\<le>degree p\<^esub> p i \<cdot> a\<^sup>i"}.\<close>
definition eval :: "'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "eval a p = additive.fincomp (\<lambda>i. p i \<cdot> rpow a i) {..degree p}"

text \<open>Each summand lies in @{term R}, and the sum is closed.\<close>
lemma eval_summand_closed: "\<lbrakk> p \<in> poly_carrier; a \<in> R \<rbrakk> \<Longrightarrow> p i \<cdot> rpow a i \<in> R"
  by (simp add: poly_carrier_coeff_closed)

lemma eval_closed [simp]:
  assumes p: "p \<in> poly_carrier" and a: "a \<in> R" shows "eval a p \<in> R"
  unfolding eval_def using p a by (auto intro!: additive.fincomp_closed eval_summand_closed)

text \<open>The summation range may be enlarged past the degree: the extra coefficients vanish.\<close>
lemma eval_fincomp_le:
  assumes p: "p \<in> poly_carrier" and a: "a \<in> R" and n: "degree p \<le> n"
  shows "eval a p = additive.fincomp (\<lambda>i. p i \<cdot> rpow a i) {..n}"
proof -
  have fin: "\<And>i. p i \<cdot> rpow a i \<in> R" using p a by (rule eval_summand_closed)
  have split: "{..n} = {..degree p} \<union> {Suc (degree p)..n}" using n by auto
  have disj: "{..degree p} \<inter> {Suc (degree p)..n} = {}" by auto
  have "additive.fincomp (\<lambda>i. p i \<cdot> rpow a i) {..n}
        = additive.fincomp (\<lambda>i. p i \<cdot> rpow a i) {..degree p}
          + additive.fincomp (\<lambda>i. p i \<cdot> rpow a i) {Suc (degree p)..n}"
    using fin by (simp add: split additive.fincomp_Un_disjoint[OF _ _ disj])
  also have "additive.fincomp (\<lambda>i. p i \<cdot> rpow a i) {Suc (degree p)..n} = \<zero>"
    using a coeff_gt_degree[OF p] by (auto intro: additive.fincomp_unit_eqI)
  finally show ?thesis
    unfolding eval_def using fin by (simp add: additive.fincomp_closed)
qed

text \<open>Evaluation of the basic polynomials.\<close>
lemma eval_zero [simp]: "a \<in> R \<Longrightarrow> eval a \<zero>\<^sub>P = \<zero>"
  by (simp add: eval_def poly_zero_def)

lemma eval_const [simp]:
  assumes a: "a \<in> R" and c: "c \<in> R" shows "eval a (poly_const c) = c"
  unfolding eval_def
  by (simp add: degree_def poly_const_def) (use c in \<open>simp add: poly_const_def\<close>)

lemma eval_one [simp]: "a \<in> R \<Longrightarrow> eval a \<one>\<^sub>P = \<one>"
  using eval_const[of a \<one>] by simp

text \<open>Evaluation is additive.\<close>
lemma eval_add:
  assumes p: "p \<in> poly_carrier" and q: "q \<in> poly_carrier" and a: "a \<in> R"
  shows "eval a (p \<oplus>\<^sub>P q) = eval a p + eval a q"
proof -
  define n where "n = max (degree p) (degree q)"
  have pq: "p \<oplus>\<^sub>P q \<in> poly_carrier" using p q by (rule poly_add_closed)
  have dpq: "degree (p \<oplus>\<^sub>P q) \<le> n" unfolding n_def using degree_add_le[OF p q] .
  have pi: "\<And>i. p i \<in> R" and qi: "\<And>i. q i \<in> R" using p q by (auto simp: poly_carrier_coeff_closed)
  have "eval a (p \<oplus>\<^sub>P q) = additive.fincomp (\<lambda>i. (p i + q i) \<cdot> rpow a i) {..n}"
    using eval_fincomp_le[OF pq a dpq] by (simp add: poly_add_def)
  also have "\<dots> = additive.fincomp (\<lambda>i. p i \<cdot> rpow a i) {..n}
                  + additive.fincomp (\<lambda>i. q i \<cdot> rpow a i) {..n}"
    by (simp add: a additive.fincomp_comp distributive(2) pi qi)
  also have "\<dots> = eval a p + eval a q"
    by (metis (lifting) a eval_fincomp_le max.cobounded1 max.cobounded2 n_def p q)
  finally show ?thesis .
qed

text \<open>Evaluation of a monomial @{term "monom c k"} is @{text "c \<cdot> a\<^sup>k"}.\<close>
lemma eval_monom:
  assumes c: "c \<in> R" and a: "a \<in> R"
  shows "eval a (monom c k) = c \<cdot> rpow a k"
proof -
  have "eval a (monom c k) = additive.fincomp (\<lambda>i. monom c k i \<cdot> rpow a i) {..k}"
    using a c degree_monom_le eval_fincomp_le monom_closed by blast
  also have "\<dots> = additive.fincomp (\<lambda>i. if i = k then c \<cdot> rpow a k else \<zero>) {..k}"
    by (rule additive.fincomp_cong') (use c a in \<open>auto simp: monom_def\<close>)
  also have "\<dots> = c \<cdot> rpow a k"
    using additive.fincomp_singleton_swap[of k "{..k}" "\<lambda>i. c \<cdot> rpow a k"] c a by simp
  finally show ?thesis .
qed

text \<open>Evaluation of the variable @{term "X\<^sub>P"} returns the point itself.\<close>
text \<open>Powers of the variable are the monic monomials, and a constant times a monic monomial is the
  monomial with that coefficient.  These are the two computations behind expanding a polynomial into
  its monomials.\<close>

lemma poly_rpow_var: "Ring.rpow (\<otimes>\<^sub>P) \<one>\<^sub>P X\<^sub>P k = monom \<one> k"
proof (induct k)
  case 0
  show ?case
    using Ring.rpow_0 [OF poly_ring, of X\<^sub>P] monom_0_eq_const [of \<one>] by simp
next
  case (Suc k)
  have "Ring.rpow (\<otimes>\<^sub>P) \<one>\<^sub>P X\<^sub>P (Suc k)
        = X\<^sub>P \<otimes>\<^sub>P Ring.rpow (\<otimes>\<^sub>P) \<one>\<^sub>P X\<^sub>P k"
    by (rule Ring.rpow_Suc [OF poly_ring])
  also have "\<dots> = X\<^sub>P \<otimes>\<^sub>P monom \<one> k" using Suc by simp
  also have "\<dots> = monom \<one> (Suc k)" by (rule var_mult_monom) simp
  finally show ?case .
qed

lemma poly_const_mult_monom:
  assumes c: "c \<in> R" shows "poly_const c \<otimes>\<^sub>P monom \<one> k = monom c k"
proof
  fix j
  have one: "\<one> \<in> R" by simp
  have step: "(monom c 0 \<otimes>\<^sub>P monom \<one> k) j
              = (if 0 \<le> j then c \<cdot> monom \<one> k (j - 0) else \<zero>)"
    by (rule coeff_monom_mult [OF c monom_closed [OF one]])
  have "(poly_const c \<otimes>\<^sub>P monom \<one> k) j = c \<cdot> monom \<one> k j"
    using step by (simp add: monom_0_eq_const)
  also have "\<dots> = monom c k j" using c by (simp add: monom_def)
  finally show "(poly_const c \<otimes>\<^sub>P monom \<one> k) j = monom c k j" .
qed

text \<open>\<^emph>\<open>Expanding a polynomial into its monomials.\<close>  Sums in the polynomial ring are pointwise, so
  a finite composite may be read coefficientwise, and then only the monomial whose exponent matches
  the coefficient index survives.  This is the univariate counterpart of the closed form
  \<open>ieval_ivar\<close> in \<open>Indexed_Poly\<close>, and it is what identifies evaluation of a polynomial's
  constant lift at the variable with the polynomial itself.\<close>

lemma poly_add_cmonoid: "commutative_monoid poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P"
proof -
  have "Abelian_Group poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P"
    using poly_ring unfolding Ring_def by blast
  then show ?thesis unfolding Abelian_Group_def by blast
qed

lemma poly_fincomp_apply:
  assumes f: "\<And>k. f k \<in> poly_carrier"
  shows "commutative_monoid.fincomp poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P f A j
       = additive.fincomp (\<lambda>k. f k j) A"
proof (cases "finite A")
  case False
  then have "commutative_monoid.fincomp poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P f A = \<zero>\<^sub>P"
    by (rule commutative_monoid.fincomp_infinite [OF poly_add_cmonoid])
  moreover from False have "additive.fincomp (\<lambda>k. f k j) A = \<zero>" by simp
  ultimately show ?thesis by (simp add: poly_zero_def)
next
  case True
  then show ?thesis
  proof (induction A rule: finite_induct)
    case empty
    have "commutative_monoid.fincomp poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P f {} = \<zero>\<^sub>P"
      by (rule commutative_monoid.fincomp_empty [OF poly_add_cmonoid])
    then show ?case by (simp add: poly_zero_def)
  next
    case (insert a A)
    have fA: "f \<in> A \<rightarrow> poly_carrier" and fa: "f a \<in> poly_carrier" using f by auto
    have "commutative_monoid.fincomp poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P f (insert a A)
          = f a \<oplus>\<^sub>P commutative_monoid.fincomp poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P f A"
      by (rule commutative_monoid.fincomp_insert
                 [OF poly_add_cmonoid insert.hyps(1) insert.hyps(2) fA fa])
    then have "commutative_monoid.fincomp poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P f (insert a A) j
               = f a j + commutative_monoid.fincomp poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P f A j"
      by (simp add: poly_add_def)
    also have "\<dots> = f a j + additive.fincomp (\<lambda>k. f k j) A" using insert.IH by simp
    also have "\<dots> = additive.fincomp (\<lambda>k. f k j) (insert a A)"
    proof (rule additive.fincomp_insert [OF insert.hyps(1) insert.hyps(2), symmetric])
      show "(\<lambda>k. f k j) \<in> A \<rightarrow> R" using f by (simp add: poly_carrier_coeff_closed)
      show "f a j \<in> R" using f by (simp add: poly_carrier_coeff_closed)
    qed
    finally show ?case .
  qed
qed

lemma poly_sum_monom:
  assumes q: "q \<in> poly_carrier" and n: "degree q \<le> n"
  shows "commutative_monoid.fincomp poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P (\<lambda>k. monom (q k) k) {..n} = q"
proof (rule ext)
  fix j
  have cl: "monom (q k) k \<in> poly_carrier" for k
    using q by (simp add: monom_closed poly_carrier_coeff_closed)
  have qjR: "q j \<in> R" by (rule poly_carrier_coeff_closed [OF q])
  have "commutative_monoid.fincomp poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P (\<lambda>k. monom (q k) k) {..n} j
        = additive.fincomp (\<lambda>k. monom (q k) k j) {..n}"
    by (rule poly_fincomp_apply [OF cl])
  also have "\<dots> = additive.fincomp (\<lambda>k. if k = j then (\<lambda>_. q j) k else \<zero>) {..n}"
  proof (rule additive.fincomp_cong')
    show "{..n} = {..n}" by rule
    show "(\<lambda>k. if k = j then (\<lambda>_. q j) k else \<zero>) \<in> {..n} \<rightarrow> R"
      using qjR by auto
    show "\<And>i. i \<in> {..n} \<Longrightarrow> monom (q i) i j
                = (if i = j then (\<lambda>_. q j) i else \<zero>)"
      by (auto simp: monom_def)
  qed
  also have "\<dots> = q j"
  proof (cases "j \<le> n")
    case True
    show ?thesis
    proof (rule additive.fincomp_singleton_swap)
      show "j \<in> {..n}" using True by simp
      show "finite {..n}" by simp
      show "(\<lambda>_. q j) \<in> {..n} \<rightarrow> R" using qjR by blast
    qed
  next
    case False
    have "(if k = j then (\<lambda>_. q j) k else \<zero>) = \<zero>" if "k \<in> {..n}" for k
      using False that by auto
    then have "additive.fincomp (\<lambda>k. if k = j then (\<lambda>_. q j) k else \<zero>) {..n} = \<zero>"
      by (rule additive.fincomp_unit_eqI)
    moreover have "q j = \<zero>" using False n by (intro coeff_gt_degree [OF q]) simp
    ultimately show ?thesis by simp
  qed
  finally show "commutative_monoid.fincomp poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P (\<lambda>k. monom (q k) k) {..n} j
                = q j" .
qed

text \<open>\<^emph>\<open>A polynomial is the value of its own constant lift at the variable.\<close>  Evaluating in the
  polynomial ring itself, with each coefficient embedded as a constant and the point taken to be
  @{term "X\<^sub>P"}, returns the polynomial.  Composing this with the reduction homomorphism is what
  identifies the class of @{term q} with the value of @{term q} at the adjoined root.\<close>
lemma eval_const_lift_at_var:
  assumes q: "q \<in> poly_carrier"
  shows "Ring.eval poly_carrier (\<oplus>\<^sub>P) (\<otimes>\<^sub>P) \<zero>\<^sub>P \<one>\<^sub>P X\<^sub>P (\<lambda>k. poly_const (q k)) = q"
proof -
  have coeffR: "q k \<in> R" for k using q by (rule poly_carrier_coeff_closed)
  have supp: "{k. poly_const (q k) \<noteq> \<zero>\<^sub>P} = {k. q k \<noteq> \<zero>}"
    by (auto simp: poly_const_def poly_zero_def fun_eq_iff)
  have lift: "(\<lambda>k. poly_const (q k)) \<in> Ring.poly_carrier poly_carrier \<zero>\<^sub>P"
  proof (rule Ring.poly_carrierI [OF poly_ring])
    show "finite {i. poly_const (q i) \<noteq> \<zero>\<^sub>P}"
      using poly_carrier_finite [OF q] supp by simp
    show "\<And>i. poly_const (q i) \<in> poly_carrier" using coeffR by (blast intro: poly_const_closed)
  qed
  have deg: "Ring.degree \<zero>\<^sub>P (\<lambda>k. poly_const (q k)) = degree q"
    using Ring.degree_def [OF poly_ring, of "\<lambda>k. poly_const (q k)"] supp
    by (simp add: degree_def)
  have summand: "poly_const (q k) \<otimes>\<^sub>P Ring.rpow (\<otimes>\<^sub>P) \<one>\<^sub>P X\<^sub>P k = monom (q k) k" for k
    using poly_rpow_var [of k] poly_const_mult_monom [OF coeffR, of k] by simp
  have "Ring.eval poly_carrier (\<oplus>\<^sub>P) (\<otimes>\<^sub>P) \<zero>\<^sub>P \<one>\<^sub>P X\<^sub>P (\<lambda>k. poly_const (q k))
        = commutative_monoid.fincomp poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P
            (\<lambda>k. poly_const (q k) \<otimes>\<^sub>P Ring.rpow (\<otimes>\<^sub>P) \<one>\<^sub>P X\<^sub>P k)
            {..Ring.degree \<zero>\<^sub>P (\<lambda>k. poly_const (q k))}"
    by (rule Ring.eval_def [OF poly_ring])
  also have "\<dots> = commutative_monoid.fincomp poly_carrier (\<oplus>\<^sub>P) \<zero>\<^sub>P
                    (\<lambda>k. monom (q k) k) {..degree q}"
    using summand deg by simp
  also have "\<dots> = q" by (rule poly_sum_monom [OF q order_refl])
  finally show ?thesis .
qed

lemma eval_var [simp]: "a \<in> R \<Longrightarrow> eval a X\<^sub>P = a"
  using eval_monom[of \<one> a 1] by (simp add: var_def)

text \<open>Powers add exponents.\<close>
lemma rpow_add: "a \<in> R \<Longrightarrow> rpow a (i + j) = rpow a i \<cdot> rpow a j"
  by (induct i) (auto simp: multiplicative.associative)

end

subsection \<open>Evaluation along a ring homomorphism\<close>

text \<open>Evaluating in the target, at the image of the point and with the images of the coefficients,
  gives the image of the evaluation.  Powers transport by induction on the exponent and the sum by
  @{thm [source] fincomp_hom}; the summation range is the only thing that does not come for free, so
  the equality of the two degrees is taken as a hypothesis.  This is the fact HOL-Algebra obtains from
  \<open>ring_hom_ring.eval_hom'\<close>.\<close>
lemma eval_hom:
  fixes A :: "'b set" and add mult :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" and z u :: 'b
    and B :: "'c set" and badd bmult :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" and bz bu :: 'c
    and h :: "'b \<Rightarrow> 'c"
  assumes RA: "Ring A add mult z u" and RB: "Ring B badd bmult bz bu"
    and hB: "\<And>y. y \<in> A \<Longrightarrow> h y \<in> B"
    and hz: "h z = bz" and hu: "h u = bu"
    and hadd: "\<And>y y'. \<lbrakk> y \<in> A; y' \<in> A \<rbrakk> \<Longrightarrow> h (add y y') = badd (h y) (h y')"
    and hmult: "\<And>y y'. \<lbrakk> y \<in> A; y' \<in> A \<rbrakk> \<Longrightarrow> h (mult y y') = bmult (h y) (h y')"
    and x: "x \<in> A" and p: "\<And>k. p k \<in> A"
    and deg: "Ring.degree bz (\<lambda>k. h (p k)) = Ring.degree z p"
  shows "Ring.eval B badd bmult bz bu (h x) (\<lambda>k. h (p k)) = h (Ring.eval A add mult z u x p)"
proof -
  have cmA: "commutative_monoid A add z" using RA by (simp add: Ring_def Abelian_Group_def)
  have cmB: "commutative_monoid B badd bz" using RB by (simp add: Ring_def Abelian_Group_def)
  have MonM: "Monoid A mult u" using RA by (simp add: Ring_def)
  have rp: "Ring.rpow bmult bu (h x) n = h (Ring.rpow mult u x n)" for n
  proof (induct n)
    case 0
    show ?case using hu by (simp add: Ring.rpow_0 [OF RA] Ring.rpow_0 [OF RB])
  next
    case (Suc n)
    have cl: "Ring.rpow mult u x n \<in> A" by (rule Ring.rpow_closed [OF RA x])
    have "Ring.rpow bmult bu (h x) (Suc n) = bmult (h x) (Ring.rpow bmult bu (h x) n)"
      by (rule Ring.rpow_Suc [OF RB])
    also have "\<dots> = bmult (h x) (h (Ring.rpow mult u x n))" using Suc by simp
    also have "\<dots> = h (mult x (Ring.rpow mult u x n))" by (rule hmult [OF x cl, symmetric])
    also have "\<dots> = h (Ring.rpow mult u x (Suc n))"
      using Ring.rpow_Suc [OF RA, of x n] by simp
    finally show ?case .
  qed
  define kf where "kf = (\<lambda>i. mult (p i) (Ring.rpow mult u x i))"
  have kA: "kf i \<in> A" for i
    unfolding kf_def
    using p Ring.rpow_closed [OF RA x] Monoid.composition_closed [OF MonM] by blast
  have summand: "bmult (h (p i)) (Ring.rpow bmult bu (h x) i) = h (kf i)" for i
    unfolding kf_def using rp hmult [OF p Ring.rpow_closed [OF RA x]] by simp
  have "Ring.eval B badd bmult bz bu (h x) (\<lambda>k. h (p k))
        = commutative_monoid.fincomp B badd bz
            (\<lambda>i. bmult (h (p i)) (Ring.rpow bmult bu (h x) i))
            {..Ring.degree bz (\<lambda>k. h (p k))}"
    by (rule Ring.eval_def [OF RB])
  also have "\<dots> = commutative_monoid.fincomp B badd bz (\<lambda>i. h (kf i)) {..Ring.degree z p}"
    using summand deg by simp
  also have "\<dots> = h (commutative_monoid.fincomp A add z kf {..Ring.degree z p})"
  proof (rule fincomp_hom [OF cmA cmB, symmetric])
    show "\<And>y. y \<in> A \<Longrightarrow> h y \<in> B" by (rule hB)
    show "h z = bz" by (rule hz)
    show "\<And>y y'. \<lbrakk> y \<in> A; y' \<in> A \<rbrakk> \<Longrightarrow> h (add y y') = badd (h y) (h y')" by (rule hadd)
    show "kf \<in> {..Ring.degree z p} \<rightarrow> A" using kA by blast
  qed
  also have "\<dots> = h (Ring.eval A add mult z u x p)"
    unfolding kf_def by (simp add: Ring.eval_def [OF RA, symmetric])
  finally show ?thesis .
qed

text \<open>When the map is injective on the source and the target is exactly the image, the degree
  hypothesis is automatic: an injection sends the zero to the zero and nothing else there, so the two
  coefficient supports are the same set.\<close>
corollary eval_transport:
  fixes A :: "'b set" and add mult :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" and z u :: 'b
    and h :: "'b \<Rightarrow> 'c" and hadd hmult :: "'c \<Rightarrow> 'c \<Rightarrow> 'c"
  assumes RA: "Ring A add mult z u"
    and RK: "Ring (h ` A) hadd hmult (h z) (h u)"
    and ha: "\<And>y y'. \<lbrakk> y \<in> A; y' \<in> A \<rbrakk> \<Longrightarrow> h (add y y') = hadd (h y) (h y')"
    and hm: "\<And>y y'. \<lbrakk> y \<in> A; y' \<in> A \<rbrakk> \<Longrightarrow> h (mult y y') = hmult (h y) (h y')"
    and inj: "inj_on h A"
    and x: "x \<in> A" and p: "\<And>k. p k \<in> A"
  shows "Ring.eval (h ` A) hadd hmult (h z) (h u) (h x) (\<lambda>k. h (p k))
       = h (Ring.eval A add mult z u x p)"
proof (rule eval_hom [OF RA RK])
  show "\<And>y. y \<in> A \<Longrightarrow> h y \<in> h ` A" by blast
  show "h z = h z" by rule
  show "h u = h u" by rule
  show "\<And>y y'. \<lbrakk> y \<in> A; y' \<in> A \<rbrakk> \<Longrightarrow> h (add y y') = hadd (h y) (h y')" by (rule ha)
  show "\<And>y y'. \<lbrakk> y \<in> A; y' \<in> A \<rbrakk> \<Longrightarrow> h (mult y y') = hmult (h y) (h y')" by (rule hm)
  show "x \<in> A" by (rule x)
  show "\<And>k. p k \<in> A" by (rule p)
  have cmA: "commutative_monoid A add z" using RA by (simp add: Ring_def Abelian_Group_def)
  have MonA: "Monoid A add z" using cmA by (simp add: commutative_monoid_def)
  have zA: "z \<in> A" by (rule Monoid.unit_closed [OF MonA])
  have supp: "{i. h (p i) \<noteq> h z} = {i. p i \<noteq> z}"
    using inj_on_eq_iff [OF inj p zA] by blast
  show "Ring.degree (h z) (\<lambda>k. h (p k)) = Ring.degree z p"
    using Ring.degree_def [OF RK, of "\<lambda>k. h (p k)"] Ring.degree_def [OF RA, of p] supp
    by simp
qed




section \<open>Polynomials over a Commutative Ring (continued): evaluation is multiplicative\<close>

context commutative_ring
begin

text \<open>\<^emph>\<open>Evaluation is multiplicative.\<close>  This needs commutativity (the point and the coefficients
  must commute), so it lives here rather than in the bare @{locale Ring}.  The proof mirrors
  @{thm [source] poly_mult_assoc}: expand both sides to sums over a triangle of index pairs and
  reindex by @{text "(k,i) \<mapsto> (i, k - i)"}.\<close>
lemma eval_mult:
  assumes p: "p \<in> poly_carrier" and q: "q \<in> poly_carrier" and a: "a \<in> R"
  shows "eval a (p \<otimes>\<^sub>P q) = eval a p \<cdot> eval a q"
proof -
  have pi: "\<And>i. p i \<in> R" and qi: "\<And>i. q i \<in> R" using p q by (auto simp: poly_carrier_coeff_closed)
  have pq: "p \<otimes>\<^sub>P q \<in> poly_carrier" using p q by (rule poly_mult_closed)
  define N where "N = degree p + degree q"
  have dpq: "degree (p \<otimes>\<^sub>P q) \<le> N" unfolding N_def using degree_mult_le[OF p q] .
  \<comment> \<open>LHS: distribute @{text "a\<^sup>k"} into the convolution and view it over the triangle.\<close>
  have "eval a (p \<otimes>\<^sub>P q) = additive.fincomp (\<lambda>k. (p \<otimes>\<^sub>P q) k \<cdot> rpow a k) {..N}"
    using eval_fincomp_le[OF pq a dpq] .
  also have "\<dots> = additive.fincomp
                    (\<lambda>k. additive.fincomp (\<lambda>i. (p i \<cdot> q (k - i)) \<cdot> rpow a k) {..k}) {..N}"
  proof (rule additive.fincomp_cong')
    fix k assume "k \<in> {..N}"
    have "(p \<otimes>\<^sub>P q) k \<cdot> rpow a k = additive.fincomp (\<lambda>i. p i \<cdot> q (k - i)) {..k} \<cdot> rpow a k"
      by (simp add: poly_mult_def)
    also have "\<dots> = additive.fincomp (\<lambda>i. (p i \<cdot> q (k - i)) \<cdot> rpow a k) {..k}"
      by (rule fincomp_mult_distrib_right) (use pi qi a in auto)
    finally show "(p \<otimes>\<^sub>P q) k \<cdot> rpow a k = additive.fincomp (\<lambda>i. (p i \<cdot> q (k - i)) \<cdot> rpow a k) {..k}" .
  qed (use pi qi a additive.fincomp_closed in auto)
  also have "\<dots> = additive.fincomp (\<lambda>x. (p (snd x) \<cdot> q (fst x - snd x)) \<cdot> rpow a (fst x))
                    (Sigma {..N} (\<lambda>k. {..k}))"
    by (rule fincomp_Sigma) (use pi qi a in auto)
  finally have LHS: "eval a (p \<otimes>\<^sub>P q)
        = additive.fincomp (\<lambda>x. (p (snd x) \<cdot> q (fst x - snd x)) \<cdot> rpow a (fst x))
            (Sigma {..N} (\<lambda>k. {..k}))" .
  \<comment> \<open>RHS: expand the product of the two evaluation sums into a double sum.\<close>
  have "eval a q \<in> R" using q a by (rule eval_closed)
  then have "eval a p \<cdot> eval a q = additive.fincomp (\<lambda>i. (p i \<cdot> rpow a i) \<cdot> eval a q) {..degree p}"
    using pi a unfolding eval_def by (intro fincomp_mult_distrib_right) auto
  also have "\<dots> = additive.fincomp
                    (\<lambda>i. additive.fincomp (\<lambda>j. (p i \<cdot> rpow a i) \<cdot> (q j \<cdot> rpow a j)) {..degree q})
                    {..degree p}"
  proof (rule additive.fincomp_cong')
    fix i assume "i \<in> {..degree p}"
    show "(p i \<cdot> rpow a i) \<cdot> eval a q
            = additive.fincomp (\<lambda>j. (p i \<cdot> rpow a i) \<cdot> (q j \<cdot> rpow a j)) {..degree q}"
      unfolding eval_def by (rule fincomp_mult_distrib_left) (use pi qi a in auto)
  qed (use pi qi a additive.fincomp_closed in auto)
  also have "\<dots> = additive.fincomp
                    (\<lambda>x. (p (fst x) \<cdot> rpow a (fst x)) \<cdot> (q (snd x) \<cdot> rpow a (snd x)))
                    (Sigma {..degree p} (\<lambda>i. {..degree q}))"
    by (rule fincomp_Sigma) (use pi qi a in auto)
  finally have RHS: "eval a p \<cdot> eval a q
        = additive.fincomp (\<lambda>x. (p (fst x) \<cdot> rpow a (fst x)) \<cdot> (q (snd x) \<cdot> rpow a (snd x)))
            (Sigma {..degree p} (\<lambda>i. {..degree q}))" .
  \<comment> \<open>Both sides are sums of @{text "p i \<cdot> q j \<cdot> a\<^bsup>i+j\<^esup>"}; identify the index sets.\<close>
  let ?T = "Sigma {..N} (\<lambda>k. {..k})"
  let ?S = "Sigma {..degree p} (\<lambda>i. {..degree q})"
  let ?G = "\<lambda>i j. (p i \<cdot> q j) \<cdot> rpow a (i + j)"
  \<comment> \<open>Rewrite the LHS summand into the symmetric form @{text "?G i j"} with @{text "(i,j) = (snd x, fst x - snd x)"}.\<close>
  have LHS': "additive.fincomp (\<lambda>x. (p (snd x) \<cdot> q (fst x - snd x)) \<cdot> rpow a (fst x)) ?T
             = additive.fincomp (\<lambda>x. ?G (snd x) (fst x - snd x)) ?T"
    by (intro additive.fincomp_cong') (auto simp: a pi qi)
  \<comment> \<open>And the RHS summand likewise, with @{text "(i,j) = (fst x, snd x)"}.\<close>
  have RHS': "additive.fincomp (\<lambda>x. (p (fst x) \<cdot> rpow a (fst x)) \<cdot> (q (snd x) \<cdot> rpow a (snd x))) ?S
             = additive.fincomp (\<lambda>x. ?G (fst x) (snd x)) ?S"
  proof (rule additive.fincomp_cong')
    fix x assume "x \<in> ?S"
    define P A1 Q A2 where "P = p (fst x)" and "A1 = rpow a (fst x)"
      and "Q = q (snd x)" and "A2 = rpow a (snd x)"
    have PR: "P \<in> R" and A1R: "A1 \<in> R" and QR: "Q \<in> R" and A2R: "A2 \<in> R"
      using pi qi a by (auto simp: P_def A1_def Q_def A2_def)
    \<comment> \<open>@{text "(P\<cdot>A1)\<cdot>(Q\<cdot>A2) = (P\<cdot>Q)\<cdot>(A1\<cdot>A2)"} by associativity and commuting @{text "A1"} past @{text "Q"}.\<close>
    have "(P \<cdot> A1) \<cdot> (Q \<cdot> A2) = (P \<cdot> Q) \<cdot> (A1 \<cdot> A2)"
      by (simp add: A1R A2R PR QR multiplicative.associative multiplicative.left_commute)
    then have "(p (fst x) \<cdot> rpow a (fst x)) \<cdot> (q (snd x) \<cdot> rpow a (snd x))
                 = (p (fst x) \<cdot> q (snd x)) \<cdot> (rpow a (fst x) \<cdot> rpow a (snd x))"
      by (simp add: P_def A1_def Q_def A2_def)
    also have "\<dots> = ?G (fst x) (snd x)" using a by (simp add: rpow_add)
    finally show "(p (fst x) \<cdot> rpow a (fst x)) \<cdot> (q (snd x) \<cdot> rpow a (snd x))
                    = ?G (fst x) (snd x)" .
  qed (use pi qi a in auto)
  \<comment> \<open>The rectangle \<open>?S\<close> sits inside the larger triangle \<open>?U\<close>; the extra summands of \<open>?U\<close>
      vanish, since \<open>p i = \<zero>\<close> for \<open>i > degree p\<close> and likewise \<open>q\<close>.  So the sum over \<open>?S\<close>
      equals the sum over \<open>?U\<close>.\<close>
  let ?U = "Sigma {..N} (\<lambda>i. {..N - i})"
  have GR: "\<And>i j. ?G i j \<in> R" using pi qi a by simp
  have G_eq_S: "additive.fincomp (\<lambda>x. ?G (fst x) (snd x)) ?S
                = additive.fincomp (\<lambda>x. ?G (fst x) (snd x)) ?U"
  proof -
    have Ssub: "?S \<subseteq> ?U" unfolding N_def by (auto simp del: split_paired_All)
    have finU: "finite ?U" by simp
    have vanish: "?G (fst x) (snd x) = \<zero>" if "x \<in> ?U - ?S" for x
    proof -
      from that have "x \<notin> ?S" by simp
      then have "p (fst x) = \<zero> \<or> q (snd x) = \<zero>"
        using coeff_gt_degree[OF p] coeff_gt_degree[OF q] by (auto simp: mem_Times_iff)
      then show ?thesis
        using a left_zero pi qi right_zero rpow_closed by presburger
    qed
    have "additive.fincomp (\<lambda>x. ?G (fst x) (snd x)) ?U
          = additive.fincomp (\<lambda>x. ?G (fst x) (snd x)) ?S"
      by (rule additive.fincomp_mono_neutral_cong_right[OF finU Ssub])
         (use vanish GR in auto)
    then show ?thesis ..
  qed
  \<comment> \<open>Reindex the LHS triangle @{term ?T} to @{term ?U} by @{text "(k,i) \<mapsto> (i, k - i)"} --- the
      same bijection used for associativity of convolution.\<close>
  let ?h = "\<lambda>x::nat\<times>nat. (snd x, fst x - snd x)"
  let ?h' = "\<lambda>x::nat\<times>nat. (fst x + snd x, fst x)"
  have bij: "bij_betw ?h ?T ?U"
    by (rule bij_betw_byWitness[where f' = ?h']) (auto simp: N_def)
  have "additive.fincomp (\<lambda>x. ?G (fst x) (snd x)) ?U
        = additive.fincomp (\<lambda>x. ?G (fst x) (snd x)) (?h ` ?T)"
    using bij bij_betw_imp_surj_on by fastforce
  also have "\<dots> = additive.fincomp (\<lambda>x. ?G (fst (?h x)) (snd (?h x))) ?T"
    using bij bij_betw_def GR by (intro additive.fincomp_reindex) auto
  also have "\<dots> = additive.fincomp (\<lambda>x. ?G (snd x) (fst x - snd x)) ?T" by simp
  finally have "additive.fincomp (\<lambda>x. ?G (fst x) (snd x)) ?S
                = additive.fincomp (\<lambda>x. ?G (snd x) (fst x - snd x)) ?T"
    using G_eq_S by simp
  then show ?thesis using LHS RHS LHS' RHS' by simp
qed

text \<open>Evaluation respects negation, hence is a ring homomorphism @{text "F[X] \<rightarrow> F"}.\<close>
lemma eval_neg:
  assumes "p \<in> poly_carrier" and "a \<in> R"
  shows "eval a (\<ominus>\<^sub>P p) = - eval a p"
proof -
  have "eval a p + eval a (\<ominus>\<^sub>P p) = \<zero>"
    using assms eval_add poly_add_neg_right poly_neg_closed by fastforce 
  then show ?thesis
    by (simp add: assms additive.commutative additive.inverse_equality poly_neg_closed)
qed

text \<open>The linear polynomial @{text "X - a"} (a root factor).\<close>
definition root_factor :: "'a \<Rightarrow> (nat \<Rightarrow> 'a)"
  where "root_factor a = X\<^sub>P \<oplus>\<^sub>P (\<ominus>\<^sub>P poly_const a)"

lemma root_factor_closed: "a \<in> R \<Longrightarrow> root_factor a \<in> poly_carrier"
  unfolding root_factor_def using var_closed poly_const_closed poly_neg_closed by (simp add: poly_add_closed)

text \<open>@{term "root_factor a"} evaluates to @{text 0} at @{term a}.\<close>
lemma eval_root_factor [simp]:
  assumes a: "a \<in> R" shows "eval a (root_factor a) = \<zero>"
  using a poly_const_closed poly_neg_closed
  by (simp add: eval_add eval_neg poly_const_closed root_factor_def var_closed)

end


section \<open>Polynomials over a Commutative Ring\<close>

context commutative_ring
begin

text \<open>When the coefficient ring is commutative, so is the polynomial ring: the convolution
  @{text "\<Sum>i\<le>k. p i \<cdot> q (k - i)"} is symmetric under the reindexing @{text "i \<mapsto> k - i"}.\<close>
lemma poly_mult_comm:
  assumes p: "p \<in> poly_carrier" and q: "q \<in> poly_carrier"
  shows "p \<otimes>\<^sub>P q = q \<otimes>\<^sub>P p"
proof
  fix k
  have inj: "inj_on (\<lambda>i. k - i) {..k::nat}"
    by (metis atMost_iff diff_diff_cancel inj_on_inverseI)
  have img: "(\<lambda>i. k - i) ` {..k} = {..k::nat}"
    by (auto simp: image_def) (metis atMost_iff diff_diff_cancel diff_le_self)
  have pi: "\<And>i. p i \<in> R" and qi: "\<And>i. q i \<in> R"
    using p q by (auto simp: poly_carrier_coeff_closed)
  have "(p \<otimes>\<^sub>P q) k = additive.fincomp (\<lambda>i. q (k - i) \<cdot> p i) ((\<lambda>i. k - i) ` {..k})"
    using img multiplicative.commutative pi poly_mult_def qi by presburger
  also have "\<dots> = additive.fincomp (\<lambda>i. q (k - (k - i)) \<cdot> p (k - i)) {..k}"
    by (rule additive.fincomp_reindex[where h = "\<lambda>i. k - i" and A = "{..k}"])
      (use pi qi inj in auto)
  also have "\<dots> = additive.fincomp (\<lambda>i. q i \<cdot> p (k - i)) {..k}"
    by (rule additive.fincomp_cong') (use pi qi in auto)
  also have "\<dots> = (q \<otimes>\<^sub>P p) k" by (simp add: poly_mult_def)
  finally show "(p \<otimes>\<^sub>P q) k = (q \<otimes>\<^sub>P p) k" .
qed

text \<open>Hence the polynomial ring over a commutative ring is itself commutative.\<close>
theorem poly_commutative_ring:
  "commutative_ring poly_carrier (\<oplus>\<^sub>P) (\<otimes>\<^sub>P) \<zero>\<^sub>P \<one>\<^sub>P"
proof -
  interpret R: Ring poly_carrier "(\<oplus>\<^sub>P)" "(\<otimes>\<^sub>P)" "\<zero>\<^sub>P" "\<one>\<^sub>P" by (rule poly_ring)
  show ?thesis
  proof qed (simp add: poly_mult_comm)
qed

end


section \<open>Polynomials over an Integral Domain\<close>

context integral_domain
begin

lemma degree_mult:
  assumes p: "p \<in> poly_carrier" and q: "q \<in> poly_carrier"
    and pnz: "p \<noteq> \<zero>\<^sub>P" and qnz: "q \<noteq> \<zero>\<^sub>P"
  shows "degree (p \<otimes>\<^sub>P q) = degree p + degree q"
proof (rule antisym)
  show "degree (p \<otimes>\<^sub>P q) \<le> degree p + degree q" using p q by (rule degree_mult_le)
next
  \<comment> \<open>The leading coefficients are nonzero, and a domain has no zero divisors, so the
      product's coefficient at @{text "degree p + degree q"} is nonzero.\<close>
  have "p (degree p) \<cdot> q (degree q) \<noteq> \<zero>"
    by (metis coeff_degree_nonzero local.no_zero_divisors poly_carrier_coeff_closed assms)
  then have "(p \<otimes>\<^sub>P q) (degree p + degree q) \<noteq> \<zero>"
    using coeff_mult_degree_add[OF p q] by simp
  then show "degree p + degree q \<le> degree (p \<otimes>\<^sub>P q)"
    by (meson coeff_gt_degree linorder_not_le p poly_mult_closed q)
qed

text \<open>Multiplication by a nonzero monomial shifts the degree by its exponent.\<close>
lemma degree_monom_mult:
  assumes c: "c \<in> R" and b: "b \<in> poly_carrier"
    and cnz: "c \<noteq> \<zero>" and bnz: "b \<noteq> \<zero>\<^sub>P"
  shows "degree (monom c n \<otimes>\<^sub>P b) = n + degree b"
proof -
  have mc: "monom c n \<in> poly_carrier" using c by (rule monom_closed)
  have mnz: "monom c n \<noteq> \<zero>\<^sub>P" using cnz by simp
  have "degree (monom c n \<otimes>\<^sub>P b) = degree (monom c n) + degree b"
    using degree_mult[OF mc b mnz bnz] .
  then show ?thesis using degree_monom[OF cnz] by simp
qed

text \<open>Hence the polynomial ring over an integral domain has no zero divisors.\<close>
lemma poly_no_zero_divisors:
  assumes "p \<in> poly_carrier" and "q \<in> poly_carrier" and "p \<otimes>\<^sub>P q = \<zero>\<^sub>P"
  shows "p = \<zero>\<^sub>P \<or> q = \<zero>\<^sub>P"
proof (rule ccontr)
  assume "\<not> (p = \<zero>\<^sub>P \<or> q = \<zero>\<^sub>P)"
  then obtain "p (degree p) \<noteq> \<zero>" and "q (degree q) \<noteq> \<zero>" 
    using assms coeff_degree_nonzero by blast
  then have "(p \<otimes>\<^sub>P q) (degree p + degree q) \<noteq> \<zero>"
    by (metis coeff_mult_degree_add no_zero_divisors poly_carrier_coeff_closed assms) 
  then show False using \<open>p \<otimes>\<^sub>P q = \<zero>\<^sub>P\<close> by (simp add: poly_zero_def)
qed


text \<open>Hence @{text "R[X]"} is itself an integral domain.  Stated here, in the
  @{locale integral_domain} context, rather than for a field base: the proof needs only
  @{thm [source] nontrivial} and @{thm [source] poly_no_zero_divisors}, both available already.
  That matters for iterating the construction --- @{text "R[X][Y]"} is a domain whenever
  @{term R} is --- which is what a multivariate polynomial ring over a domain amounts to on
  this representation.\<close>
theorem poly_integral_domain:
  "integral_domain poly_carrier (\<oplus>\<^sub>P) (\<otimes>\<^sub>P) \<zero>\<^sub>P \<one>\<^sub>P"
proof -
  interpret comm: commutative_ring poly_carrier "(\<oplus>\<^sub>P)" "(\<otimes>\<^sub>P)" "\<zero>\<^sub>P" "\<one>\<^sub>P"
    by (rule poly_commutative_ring)
  have nt: "\<one>\<^sub>P \<noteq> \<zero>\<^sub>P"
    by (metis nontrivial poly_one_def poly_zero_def)
  then show ?thesis
    by unfold_locales (use nt poly_no_zero_divisors in blast)+
qed

end


section \<open>Polynomial Division over a Field\<close>

context Field
begin

subsection \<open>Units of \<open>F[X]\<close>\<close>

text \<open>Over a field, multiplication of nonzero polynomials adds degrees, so a polynomial can
  only be a multiplicative unit if it has degree @{text 0}: the units of @{text "F[X]"} are
  exactly the nonzero constants.  This pins down what it means for an irreducible polynomial
  to admit only trivial factorisations.\<close>

text \<open>A nonzero constant is a unit, with the constant of the inverse coefficient as inverse.\<close>
lemma poly_const_unit:
  assumes a: "a \<in> R" and anz: "a \<noteq> \<zero>"
  shows "poly_unit (poly_const a)"
  by (metis poly_unitI field_inverse poly_const_mult assms multiplicative.invertibleE 
      poly_const_closed poly_const_one)

text \<open>Conversely, every unit of @{text "F[X]"} is a nonzero constant.  An invertible
  polynomial is nonzero and has degree @{text 0} (degrees add under multiplication), so it is
  the constant of its own (nonzero) leading coefficient.\<close>
lemma poly_unit_imp_const:
  assumes inv: "poly_unit p"
  shows "p \<noteq> \<zero>\<^sub>P \<and> degree p = 0 \<and> p = poly_const (p 0) \<and> p 0 \<noteq> \<zero>"
proof -
  have p: "p \<in> poly_carrier" using inv by (rule poly_unit_closed)
  obtain q where q: "q \<in> poly_carrier" and pq: "p \<otimes>\<^sub>P q = \<one>\<^sub>P"
    using inv unfolding poly_unit_def by blast
  have pnz: "p \<noteq> \<zero>\<^sub>P"
    using q poly_mult_zero_left pq eval_zero nontrivial by force
  have qnz: "q \<noteq> \<zero>\<^sub>P"
    using p pnz poly_mult_one_right poly_mult_zero_right pq by force
  \<comment> \<open>Degrees add and the product has degree @{text 0}, so @{term p} has degree @{text 0}.\<close>
  have d0: "degree p = 0"
    by (metis add_eq_0_iff_both_eq_0 degree_mult degree_one p pnz pq q qnz)
  then show ?thesis using pnz d0
    by (metis coeff_degree_nonzero degree_zero_imp_const p)
qed

text \<open>A polynomial is \<^emph>\<open>irreducible\<close> when it is a non-unit, nonzero, and every factorisation
  has a unit factor.  Over a field this excludes the units (the nonzero constants) and the
  zero polynomial, matching the usual notion for @{text "F[X]"}.\<close>
definition poly_irreducible :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "poly_irreducible p \<longleftrightarrow> p \<in> poly_carrier \<and> p \<noteq> \<zero>\<^sub>P \<and> \<not> poly_unit p
            \<and> (\<forall>a b. a \<in> poly_carrier \<longrightarrow> b \<in> poly_carrier \<longrightarrow> p = a \<otimes>\<^sub>P b
                    \<longrightarrow> poly_unit a \<or> poly_unit b)"

lemma poly_irreducibleD_carrier: "poly_irreducible p \<Longrightarrow> p \<in> poly_carrier"
  unfolding poly_irreducible_def by blast

lemma poly_irreducibleD_nonzero: "poly_irreducible p \<Longrightarrow> p \<noteq> \<zero>\<^sub>P"
  unfolding poly_irreducible_def by blast

lemma poly_irreducibleD_nonunit: "poly_irreducible p \<Longrightarrow> \<not> poly_unit p"
  unfolding poly_irreducible_def by blast

lemma poly_irreducibleD_factor:
  "\<lbrakk> poly_irreducible p; a \<in> poly_carrier; b \<in> poly_carrier; p = a \<otimes>\<^sub>P b \<rbrakk>
     \<Longrightarrow> poly_unit a \<or> poly_unit b"
  unfolding poly_irreducible_def by blast

text \<open>An irreducible polynomial is nonconstant: a nonzero constant is a unit, and the zero
  polynomial is excluded outright.  Needed because the remainders modulo @{term p} contain
  @{term "\<one>\<^sub>P"} only when @{term p} is nonconstant.\<close>
lemma poly_irreducible_degree_pos:
  assumes irr: "poly_irreducible p" shows "0 < degree p"
proof (rule ccontr)
  assume "\<not> 0 < degree p"
  then have d0: "degree p = 0" by simp
  have pc: "p \<in> poly_carrier" using irr by (rule poly_irreducibleD_carrier)
  have pnz: "p \<noteq> \<zero>\<^sub>P" using irr by (rule poly_irreducibleD_nonzero)
  have low: "p \<in> low_poly 1" using pc d0 by (simp add: low_poly_iff_degree)
  have const: "p = poly_const (p 0)"
  proof (rule ext)
    fix i show "p i = poly_const (p 0) i"
      using low_poly_coeff [OF low] by (cases i) (simp_all add: poly_const_def)
  qed
  have nz: "p 0 \<noteq> \<zero>"
  proof
    assume "p 0 = \<zero>"
    with const have "p = \<zero>\<^sub>P" by (simp add: poly_const_def poly_zero_def)
    with pnz show False ..
  qed
  have "poly_unit p"
    using const poly_const_unit [OF poly_carrier_coeff_closed [OF pc] nz] by simp
  with poly_irreducibleD_nonunit [OF irr] show False ..
qed

text \<open>The reduction step of the division algorithm: when @{term "degree b \<le> degree a"} and both
  are nonzero, subtracting the appropriate monomial multiple of @{term b} cancels the leading
  term of @{term a}, strictly decreasing its degree.\<close>
lemma div_step:
  assumes a: "a \<in> poly_carrier" and b: "b \<in> poly_carrier"
    and anz: "a \<noteq> \<zero>\<^sub>P" and bnz: "b \<noteq> \<zero>\<^sub>P" and ge: "degree b \<le> degree a"
  obtains m where "m \<in> poly_carrier" "degree m = degree a - degree b"
    and "a \<oplus>\<^sub>P (\<ominus>\<^sub>P (m \<otimes>\<^sub>P b)) = \<zero>\<^sub>P \<or> degree (a \<oplus>\<^sub>P (\<ominus>\<^sub>P (m \<otimes>\<^sub>P b))) < degree a"
proof -
  define c where "c = lead_coeff a \<cdot> multiplicative.inverse (lead_coeff b)"
  define k where "k = degree a - degree b"
  have la: "lead_coeff a \<noteq> \<zero>" using a anz by (rule lead_coeff_nonzero)
  have lb: "lead_coeff b \<noteq> \<zero>" using b bnz by (rule lead_coeff_nonzero)
  have laR: "lead_coeff a \<in> R" using a by (simp add: lead_coeff_def poly_carrier_coeff_closed)
  have lbR: "lead_coeff b \<in> R" using b by (simp add: lead_coeff_def poly_carrier_coeff_closed)
  have invb: "multiplicative.invertible (lead_coeff b)" using lbR lb by (rule field_inverse)
  have ibR: "multiplicative.inverse (lead_coeff b) \<in> R" using lbR invb by simp
  have cR: "c \<in> R" unfolding c_def using laR ibR by simp
  have ib_nz: "multiplicative.inverse (lead_coeff b) \<noteq> \<zero>"
    using invb lbR multiplicative.invertible_right_inverse nontrivial right_zero by moura
  have cnz: "c \<noteq> \<zero>"
    using c_def ibR ib_nz la laR local.no_zero_divisors by auto
  define m where "m = monom c k"
  have mc: "m \<in> poly_carrier" unfolding m_def using cR by (rule monom_closed)
  have mk: "m k \<noteq> \<zero>" unfolding m_def monom_def using cnz by simp
  \<comment> \<open>@{term m} has degree exactly @{term k}.\<close>
  have degm: "degree m = k"
    using coeff_gt_degree degree_monom_le le_neq_implies_less m_def mc mk by blast
  have mnz: "m \<noteq> \<zero>\<^sub>P" using mk by (auto simp: poly_zero_def)
  have mbc: "m \<otimes>\<^sub>P b \<in> poly_carrier" using mc b by (rule poly_mult_closed)
  \<comment> \<open>The product @{term "m \<otimes>\<^sub>P b"} has degree @{term "degree a"} and matching leading term.\<close>
  have degmb: "degree (m \<otimes>\<^sub>P b) = degree a"
    using degree_mult[OF mc b mnz bnz] degm ge by (simp add: k_def)
  have lead_mb: "(m \<otimes>\<^sub>P b) (degree a) = lead_coeff a"
    using coeff_mult_degree_add[OF mc b] invb degm ge k_def laR lbR m_def 
    by (force simp: c_def multiplicative.associative lead_coeff_def monom_def)
  define d where "d = a \<oplus>\<^sub>P (\<ominus>\<^sub>P (m \<otimes>\<^sub>P b))"
  have dc: "d \<in> poly_carrier" unfolding d_def using a mbc poly_neg_closed poly_add_closed by simp
  \<comment> \<open>The difference is zero or has strictly smaller degree, since its top coefficient cancels.\<close>
  have "d = \<zero>\<^sub>P \<or> degree d < degree a"
  proof (cases "d = \<zero>\<^sub>P")
    case True then show ?thesis ..
  next
    case False
    have "degree d \<le> degree a"
      by (intro degree_leI[OF dc]) (simp add: a d_def poly_add_def poly_neg_def coeff_gt_degree degmb mbc)
    moreover have "d (degree a) = \<zero>"
      using Ring.lead_coeff_def Ring_axioms d_def laR lead_mb poly_add_def poly_neg_def
      by fastforce
    ultimately show ?thesis
      using False by (metis coeff_degree_nonzero dc le_neq_implies_less)
  qed
  then show ?thesis using mc degm d_def by (metis k_def that)
qed

text \<open>\<^emph>\<open>The division algorithm.\<close>  For any dividend @{term a} and nonzero divisor @{term b}
  there exist a quotient @{term q} and remainder @{term r} with @{text "a = b \<otimes> q \<oplus> r"} and
  the remainder either zero or of degree below that of @{term b}.  Proved by strong induction
  on @{term "degree a"}, repeatedly applying @{thm [source] div_step}.\<close>
theorem poly_divide:
  assumes a: "a \<in> poly_carrier" and b: "b \<in> poly_carrier" and bnz: "b \<noteq> \<zero>\<^sub>P"
  shows "\<exists>q r. q \<in> poly_carrier \<and> r \<in> poly_carrier \<and> a = (b \<otimes>\<^sub>P q) \<oplus>\<^sub>P r
              \<and> (r = \<zero>\<^sub>P \<or> degree r < degree b)"
  using a
proof (induct "degree a" arbitrary: a rule: less_induct)
  case (less a)
  show ?case
  proof (cases "a = \<zero>\<^sub>P \<or> degree a < degree b")
    case True then show ?thesis
    \<comment> \<open>Base case: the quotient is zero and @{term a} is the remainder.\<close>
      by (metis b less.prems poly_zero_closed poly_add_zero poly_mult_zero_right)
  next
    case False
    then have anz: "a \<noteq> \<zero>\<^sub>P" and ge: "degree b \<le> degree a" by auto
    \<comment> \<open>Reduce the leading term, then divide the smaller remainder by the induction hypothesis.\<close>
    obtain m where m: "m \<in> poly_carrier"
      and d: "a \<oplus>\<^sub>P (\<ominus>\<^sub>P (m \<otimes>\<^sub>P b)) = \<zero>\<^sub>P \<or> degree (a \<oplus>\<^sub>P (\<ominus>\<^sub>P (m \<otimes>\<^sub>P b))) < degree a"
      using div_step[OF less.prems b anz bnz ge] by blast
    define dd where "dd = a \<oplus>\<^sub>P (\<ominus>\<^sub>P (m \<otimes>\<^sub>P b))"
    have ddc: "dd \<in> poly_carrier"
      unfolding dd_def using less.prems b m poly_neg_closed poly_mult_closed poly_add_closed
      by simp
    \<comment> \<open>@{term a} is recovered: @{text "a = (m \<otimes> b) \<oplus> dd"}, by additive-group cancellation.\<close>
    have mbc: "m \<otimes>\<^sub>P b \<in> poly_carrier" using m b by (rule poly_mult_closed)
    have a_eq: "a = (m \<otimes>\<^sub>P b) \<oplus>\<^sub>P dd"
      unfolding dd_def using poly_add_minus_cancel[OF mbc less.prems] by simp
    have dd_div: "\<exists>q r. q \<in> poly_carrier \<and> r \<in> poly_carrier \<and> dd = (b \<otimes>\<^sub>P q) \<oplus>\<^sub>P r
                       \<and> (r = \<zero>\<^sub>P \<or> degree r < degree b)"
      by (metis b d dd_def ddc less.hyps poly_add_zero poly_mult_zero_right)
    then obtain q r where q: "q \<in> poly_carrier" and r: "r \<in> poly_carrier"
      and dd_eq: "dd = (b \<otimes>\<^sub>P q) \<oplus>\<^sub>P r" and rdeg: "r = \<zero>\<^sub>P \<or> degree r < degree b" by blast
    \<comment> \<open>Assemble: @{text "a = (m \<otimes> b) \<oplus> (b \<otimes> q) \<oplus> r = b \<otimes> (m \<oplus> q) \<oplus> r"}.\<close>
    have "a = (m \<otimes>\<^sub>P b) \<oplus>\<^sub>P ((b \<otimes>\<^sub>P q) \<oplus>\<^sub>P r)" using a_eq dd_eq by simp
    also have "\<dots> = (b \<otimes>\<^sub>P (m \<oplus>\<^sub>P q)) \<oplus>\<^sub>P r"
      using poly_mult_add_distrib_left[OF b m q]
      by (simp add: b m poly_add_assoc poly_mult_closed poly_mult_comm q r)
    finally have "a = (b \<otimes>\<^sub>P (m \<oplus>\<^sub>P q)) \<oplus>\<^sub>P r" .
    then show ?thesis 
      by (metis r rdeg m poly_add_closed q)
  qed
qed

text \<open>\<^emph>\<open>Uniqueness of quotient and remainder.\<close>  If @{term b} is nonzero and two quotient/remainder
  pairs both work --- each remainder of degree below @{term b} --- then they coincide.  For if the
  quotients differed, \<open>b \<otimes> (q\<^sub>1 \<oplus> \<ominus>q\<^sub>2)\<close> would have degree \<open>\<ge> degree b\<close> (degrees
  add over a domain), yet it equals \<open>r\<^sub>2 \<oplus> \<ominus>r\<^sub>1\<close>, of degree below @{term b}.\<close>
text \<open>Left cancellation of a nonzero factor: @{text "a \<otimes> x = a \<otimes> y \<Longrightarrow> x = y"} (the ring of
  polynomials over a field is a domain).\<close>
lemma poly_mult_left_cancel:
  assumes a: "a \<in> poly_carrier" and anz: "a \<noteq> \<zero>\<^sub>P"
    and x: "x \<in> poly_carrier" and y: "y \<in> poly_carrier"
    and eq: "a \<otimes>\<^sub>P x = a \<otimes>\<^sub>P y"
  shows "x = y"
proof -
  have ny: "\<ominus>\<^sub>P y \<in> poly_carrier" using y by (rule poly_neg_closed)
  have dxyc: "x \<oplus>\<^sub>P (\<ominus>\<^sub>P y) \<in> poly_carrier" using x ny by (rule poly_add_closed)
  \<comment> \<open>@{text "a \<otimes> \<ominus>y = \<ominus>(a \<otimes> y)"}: the two sum to @{text "a \<otimes> (y \<oplus> \<ominus>y) = \<zero>"}.\<close>
  have "(a \<otimes>\<^sub>P y) \<oplus>\<^sub>P (a \<otimes>\<^sub>P (\<ominus>\<^sub>P y)) = a \<otimes>\<^sub>P (y \<oplus>\<^sub>P (\<ominus>\<^sub>P y))"
    using poly_mult_add_distrib_left[OF a y ny] by simp
  also have "\<dots> = \<zero>\<^sub>P" using a
    by (simp add: poly_add_neg_right poly_mult_zero_right y)
  finally have "(a \<otimes>\<^sub>P y) \<oplus>\<^sub>P (a \<otimes>\<^sub>P (\<ominus>\<^sub>P y)) = \<zero>\<^sub>P" .
  then have "a \<otimes>\<^sub>P (x \<oplus>\<^sub>P (\<ominus>\<^sub>P y)) = \<zero>\<^sub>P" 
  \<comment> \<open>No zero divisors and @{term "a \<noteq> \<zero>\<^sub>P"} force \<open>x \<oplus> \<ominus>y = \<zero>\<^sub>P\<close>, i.e. @{term "x = y"}.\<close>
    by (simp add: a eq ny poly_mult_add_distrib_left x)
  then show ?thesis
    by (meson a anz dxyc poly_diff_zero_eq poly_no_zero_divisors x y)
qed

theorem poly_divide_unique:
  assumes b: "b \<in> poly_carrier" and bnz: "b \<noteq> \<zero>\<^sub>P"
    and q1: "q1 \<in> poly_carrier" and r1: "r1 \<in> poly_carrier"
    and q2: "q2 \<in> poly_carrier" and r2: "r2 \<in> poly_carrier"
    and e1: "a = (b \<otimes>\<^sub>P q1) \<oplus>\<^sub>P r1" and d1: "r1 = \<zero>\<^sub>P \<or> degree r1 < degree b"
    and e2: "a = (b \<otimes>\<^sub>P q2) \<oplus>\<^sub>P r2" and d2: "r2 = \<zero>\<^sub>P \<or> degree r2 < degree b"
  shows "q1 = q2 \<and> r1 = r2"
proof 
  have bq1: "b \<otimes>\<^sub>P q1 \<in> poly_carrier" using b q1 by (rule poly_mult_closed)
  have bq2: "b \<otimes>\<^sub>P q2 \<in> poly_carrier" using b q2 by (rule poly_mult_closed)
  define dq where "dq = q1 \<oplus>\<^sub>P (\<ominus>\<^sub>P q2)"
  define dr where "dr = r2 \<oplus>\<^sub>P (\<ominus>\<^sub>P r1)"
  have dqc: "dq \<in> poly_carrier" unfolding dq_def using q1 q2 poly_neg_closed by (simp add: poly_add_closed)
  have drc: "dr \<in> poly_carrier" unfolding dr_def using r1 r2 poly_neg_closed by (simp add: poly_add_closed)
  \<comment> \<open>The two equations give @{term "b \<otimes>\<^sub>P dq = dr"}.\<close>
  have key: "b \<otimes>\<^sub>P dq = dr"
  proof -
    have "b \<otimes>\<^sub>P dq = (b \<otimes>\<^sub>P q1) \<oplus>\<^sub>P (b \<otimes>\<^sub>P (\<ominus>\<^sub>P q2))"
      unfolding dq_def using poly_mult_add_distrib_left[OF b q1 poly_neg_closed[OF q2]] .
    also have "b \<otimes>\<^sub>P (\<ominus>\<^sub>P q2) = \<ominus>\<^sub>P (b \<otimes>\<^sub>P q2)"
      using poly_mult_add_distrib_left[OF b q2 poly_neg_closed[OF q2]]
      by (simp add: b poly_add_neg_right poly_minus_unique poly_mult_closed poly_mult_zero_right
          poly_neg_closed q2) 
    finally have "b \<otimes>\<^sub>P dq = (b \<otimes>\<^sub>P q1) \<oplus>\<^sub>P (\<ominus>\<^sub>P (b \<otimes>\<^sub>P q2))" .
    \<comment> \<open>And \<open>(b \<otimes> q1) \<oplus> \<ominus>(b \<otimes> q2) = r2 \<oplus> \<ominus>r1 = dr\<close> from the two division equations.\<close>
    then show ?thesis
      using bq1 bq2 dr_def e1 e2 poly_sub_shift r1 r2 by force
  qed
  \<comment> \<open>If @{term dq} were nonzero, @{term "b \<otimes>\<^sub>P dq"} would have degree @{text "\<ge> degree b"}.\<close>
  have dqz: "dq = \<zero>\<^sub>P"
  proof (rule ccontr)
    assume dqnz: "dq \<noteq> \<zero>\<^sub>P"
    have ge: "degree b \<le> degree dr" using key
      using b bnz degree_mult dqc dqnz by force
    \<comment> \<open>But @{term dr} has degree below @{term b}.\<close>
    have "dr = \<zero>\<^sub>P \<or> degree dr < degree b"
    proof (cases "dr = \<zero>\<^sub>P")
      case True then show ?thesis ..
    next
      case False
      \<comment> \<open>@{term dr} is nonzero, so @{term "degree b > 0"} (else both remainders vanish).\<close>
      have bpos: "degree b > 0"
        using False assms(10,8) dr_def poly_add_neg_right r2 by force
      have r1b: "degree r1 < degree b" using d1 bpos by auto
      have r2b: "degree r2 < degree b" using d2 bpos by auto
      have "degree dr \<le> max (degree r2) (degree (\<ominus>\<^sub>P r1))"
        unfolding dr_def by (rule degree_add_le[OF r2 poly_neg_closed[OF r1]])
      then show ?thesis
        using degree_neg r1 r1b r2b by fastforce
    qed
    then show False
      using b bnz dqc dqnz ge key poly_no_zero_divisors by fastforce
  qed
  \<comment> \<open>So @{term "q1 = q2"}, and then @{term "r1 = r2"} from either equation.\<close>
  show qeq: "q1 = q2"
    using dq_def dqz poly_diff_zero_eq q1 q2 by blast
  show "r1 = r2"
    using bq1 e1 e2 poly_add_left_cancel qeq r1 r2 by blast 
qed


subsection \<open>Remainder modulo a polynomial\<close>

text \<open>The remainder of @{term a} on division by @{term b}: the canonical representative of
  @{term a} modulo @{term b}, of degree below that of @{term b}.  Defined by choice from the
  division algorithm, and pinned down uniquely by @{thm [source] poly_divide_unique}.\<close>
definition pmod :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"
  where "pmod a b = (SOME r. \<exists>q. q \<in> poly_carrier \<and> r \<in> poly_carrier
                                  \<and> a = (b \<otimes>\<^sub>P q) \<oplus>\<^sub>P r \<and> (r = \<zero>\<^sub>P \<or> degree r < degree b))"

text \<open>The defining property of @{const pmod}: there is a quotient realising it.\<close>
lemma pmod_spec:
  assumes a: "a \<in> poly_carrier" and b: "b \<in> poly_carrier" and bnz: "b \<noteq> \<zero>\<^sub>P"
  shows "\<exists>q. q \<in> poly_carrier \<and> pmod a b \<in> poly_carrier
             \<and> a = (b \<otimes>\<^sub>P q) \<oplus>\<^sub>P pmod a b \<and> (pmod a b = \<zero>\<^sub>P \<or> degree (pmod a b) < degree b)"
proof -
  let ?P = "\<lambda>r. \<exists>q. q \<in> poly_carrier \<and> r \<in> poly_carrier
                     \<and> a = (b \<otimes>\<^sub>P q) \<oplus>\<^sub>P r \<and> (r = \<zero>\<^sub>P \<or> degree r < degree b)"
  have "\<exists>r. ?P r" using poly_divide[OF a b bnz] by blast
  then have "?P (SOME r. ?P r)" by (rule someI_ex)
  then show ?thesis unfolding pmod_def .
qed

lemma pmod_closed:
  "\<lbrakk> a \<in> poly_carrier; b \<in> poly_carrier; b \<noteq> \<zero>\<^sub>P \<rbrakk> \<Longrightarrow> pmod a b \<in> poly_carrier"
  using pmod_spec by blast

lemma pmod_degree:
  "\<lbrakk> a \<in> poly_carrier; b \<in> poly_carrier; b \<noteq> \<zero>\<^sub>P \<rbrakk>
     \<Longrightarrow> pmod a b = \<zero>\<^sub>P \<or> degree (pmod a b) < degree b"
  using pmod_spec by blast

text \<open>@{const pmod} is the unique remainder: any low-degree @{term r} congruent to @{term a}
  modulo @{term b} equals @{term "pmod a b"}.\<close>
lemma pmod_unique:
  assumes a: "a \<in> poly_carrier" and b: "b \<in> poly_carrier" and bnz: "b \<noteq> \<zero>\<^sub>P"
    and q: "q \<in> poly_carrier" and r: "r \<in> poly_carrier"
    and eq: "a = (b \<otimes>\<^sub>P q) \<oplus>\<^sub>P r" and rd: "r = \<zero>\<^sub>P \<or> degree r < degree b"
  shows "pmod a b = r"
  using pmod_spec[OF a b bnz] poly_divide_unique[OF b bnz]
  by (metis eq q r rd)

text \<open>A remainder is a low-degree polynomial --- the form in which the remainders are used as a
  carrier.\<close>
lemma pmod_low_poly:
  assumes a: "a \<in> poly_carrier" and b: "b \<in> poly_carrier" and bnz: "b \<noteq> \<zero>\<^sub>P"
  shows "pmod a b \<in> low_poly (degree b)"
  using pmod_closed [OF a b bnz] pmod_degree [OF a b bnz]
  by (simp add: low_poly_iff_degree)

text \<open>A polynomial of degree below @{term b} is its own remainder.\<close>
lemma pmod_small:
  assumes b: "b \<in> poly_carrier" and bnz: "b \<noteq> \<zero>\<^sub>P"
    and r: "r \<in> poly_carrier" and rd: "r = \<zero>\<^sub>P \<or> degree r < degree b"
  shows "pmod r b = r"
  using pmod_unique[OF r b bnz poly_zero_closed r _ rd]
  using b poly_add_zero poly_mult_zero_right r by force

text \<open>Changing @{term a} by a multiple of @{term b} does not change the remainder.  Everything below
  is a consequence of this and @{thm [source] pmod_unique}.\<close>
lemma pmod_shift:
  assumes y: "y \<in> poly_carrier" and c: "c \<in> poly_carrier"
    and b: "b \<in> poly_carrier" and bnz: "b \<noteq> \<zero>\<^sub>P"
  shows "pmod ((b \<otimes>\<^sub>P c) \<oplus>\<^sub>P y) b = pmod y b"
proof -
  obtain q where q: "q \<in> poly_carrier" and yeq: "y = (b \<otimes>\<^sub>P q) \<oplus>\<^sub>P pmod y b"
    using pmod_spec [OF y b bnz] by blast
  have r: "pmod y b \<in> poly_carrier" by (rule pmod_closed [OF y b bnz])
  have "(b \<otimes>\<^sub>P c) \<oplus>\<^sub>P y = (b \<otimes>\<^sub>P (c \<oplus>\<^sub>P q)) \<oplus>\<^sub>P pmod y b"
    using yeq b c q r
    by (simp add: poly_mult_add_distrib_left poly_add_assoc poly_mult_closed)
  moreover have "(b \<otimes>\<^sub>P c) \<oplus>\<^sub>P y \<in> poly_carrier"
    using b c y by (simp add: poly_add_closed poly_mult_closed)
  ultimately show ?thesis
    using pmod_unique [OF _ b bnz _ r _ pmod_degree [OF y b bnz]] c q
    by (simp add: poly_add_closed)
qed

text \<open>The remainder is additive outright: a sum of two low-degree remainders is already low-degree,
  so no second reduction is needed.\<close>
lemma pmod_add:
  assumes a: "a \<in> poly_carrier" and a': "a' \<in> poly_carrier"
    and b: "b \<in> poly_carrier" and bnz: "b \<noteq> \<zero>\<^sub>P"
  shows "pmod (a \<oplus>\<^sub>P a') b = pmod a b \<oplus>\<^sub>P pmod a' b"
proof -
  obtain q where q: "q \<in> poly_carrier" and aeq: "a = (b \<otimes>\<^sub>P q) \<oplus>\<^sub>P pmod a b"
    using pmod_spec [OF a b bnz] by blast
  obtain q' where q': "q' \<in> poly_carrier" and a'eq: "a' = (b \<otimes>\<^sub>P q') \<oplus>\<^sub>P pmod a' b"
    using pmod_spec [OF a' b bnz] by blast
  have r: "pmod a b \<in> poly_carrier" and r': "pmod a' b \<in> poly_carrier"
    using pmod_closed [OF a b bnz] pmod_closed [OF a' b bnz] by blast+
  have rr': "pmod a b \<oplus>\<^sub>P pmod a' b \<in> poly_carrier" using r r' by (rule poly_add_closed)
  \<comment> \<open>The sum of the two remainders is itself low-degree.\<close>
  have low: "pmod a b \<oplus>\<^sub>P pmod a' b = \<zero>\<^sub>P \<or> degree (pmod a b \<oplus>\<^sub>P pmod a' b) < degree b"
  proof (cases "pmod a b \<oplus>\<^sub>P pmod a' b = \<zero>\<^sub>P")
    case False
    \<comment> \<open>Not both remainders vanish, so @{term b} has positive degree, and then a vanishing
        remainder has degree below it as well.\<close>
    have dpos: "0 < degree b"
    proof (cases "pmod a b = \<zero>\<^sub>P")
      case True
      then have "pmod a' b \<noteq> \<zero>\<^sub>P" using False r' by (simp add: poly_add_zero)
      then show ?thesis using pmod_degree [OF a' b bnz] by auto
    next
      case False
      then show ?thesis using pmod_degree [OF a b bnz] by auto
    qed
    have dr: "degree (pmod a b) < degree b" and dr': "degree (pmod a' b) < degree b"
      using pmod_degree [OF a b bnz] pmod_degree [OF a' b bnz] dpos by auto
    have "degree (pmod a b \<oplus>\<^sub>P pmod a' b) \<le> max (degree (pmod a b)) (degree (pmod a' b))"
      by (rule degree_add_le [OF r r'])
    with dr dr' have "degree (pmod a b \<oplus>\<^sub>P pmod a' b) < degree b" by simp
    then show ?thesis by blast
  qed simp
  \<comment> \<open>Reduce the left summand, then the right, as \<open>pmod_mult\<close> below does for a product; each step
      only moves a multiple of @{term b}.  The sum of the remainders is then its own remainder.\<close>
  have step1: "a \<oplus>\<^sub>P a' = (b \<otimes>\<^sub>P q) \<oplus>\<^sub>P (pmod a b \<oplus>\<^sub>P a')"
    using aeq poly_add_assoc [OF poly_mult_closed [OF b q] r a'] by simp
  have step2: "pmod a b \<oplus>\<^sub>P a' = (b \<otimes>\<^sub>P q') \<oplus>\<^sub>P (pmod a b \<oplus>\<^sub>P pmod a' b)"
  proof -
    have bq': "b \<otimes>\<^sub>P q' \<in> poly_carrier" using b q' by (rule poly_mult_closed)
    have "pmod a b \<oplus>\<^sub>P a' = pmod a b \<oplus>\<^sub>P ((b \<otimes>\<^sub>P q') \<oplus>\<^sub>P pmod a' b)"
      using a'eq by simp
    also have "\<dots> = (pmod a b \<oplus>\<^sub>P (b \<otimes>\<^sub>P q')) \<oplus>\<^sub>P pmod a' b"
      by (rule poly_add_assoc [OF r bq' r', symmetric])
    also have "\<dots> = ((b \<otimes>\<^sub>P q') \<oplus>\<^sub>P pmod a b) \<oplus>\<^sub>P pmod a' b"
      using poly_add_comm [OF r bq'] by simp
    also have "\<dots> = (b \<otimes>\<^sub>P q') \<oplus>\<^sub>P (pmod a b \<oplus>\<^sub>P pmod a' b)"
      by (rule poly_add_assoc [OF bq' r r'])
    finally show ?thesis .
  qed
  have "pmod (a \<oplus>\<^sub>P a') b = pmod (pmod a b \<oplus>\<^sub>P a') b"
    using step1 pmod_shift [OF poly_add_closed [OF r a'] q b bnz] by simp
  also have "\<dots> = pmod (pmod a b \<oplus>\<^sub>P pmod a' b) b"
    using step2 pmod_shift [OF rr' q' b bnz] by simp
  also have "\<dots> = pmod a b \<oplus>\<^sub>P pmod a' b" by (rule pmod_small [OF b bnz rr' low])
  finally show ?thesis .
qed

text \<open>The remainder is multiplicative \<^emph>\<open>after a further reduction\<close>: a product of two low-degree
  remainders need not be low-degree, so the outer @{const pmod} cannot be dropped here as it was for
  the sum.  This is the congruence that makes the remainders a ring.\<close>
lemma pmod_mult:
  assumes a: "a \<in> poly_carrier" and a': "a' \<in> poly_carrier"
    and b: "b \<in> poly_carrier" and bnz: "b \<noteq> \<zero>\<^sub>P"
  shows "pmod (a \<otimes>\<^sub>P a') b = pmod (pmod a b \<otimes>\<^sub>P pmod a' b) b"
proof -
  obtain q where q: "q \<in> poly_carrier" and aeq: "a = (b \<otimes>\<^sub>P q) \<oplus>\<^sub>P pmod a b"
    using pmod_spec [OF a b bnz] by blast
  obtain q' where q': "q' \<in> poly_carrier" and a'eq: "a' = (b \<otimes>\<^sub>P q') \<oplus>\<^sub>P pmod a' b"
    using pmod_spec [OF a' b bnz] by blast
  have r: "pmod a b \<in> poly_carrier" and r': "pmod a' b \<in> poly_carrier"
    using pmod_closed [OF a b bnz] pmod_closed [OF a' b bnz] by blast+
  \<comment> \<open>Reduce the left factor, then the right; each step only moves a multiple of @{term b}.\<close>
  have step1: "a \<otimes>\<^sub>P a' = (b \<otimes>\<^sub>P (q \<otimes>\<^sub>P a')) \<oplus>\<^sub>P (pmod a b \<otimes>\<^sub>P a')"
  proof -
    have "a \<otimes>\<^sub>P a' = ((b \<otimes>\<^sub>P q) \<otimes>\<^sub>P a') \<oplus>\<^sub>P (pmod a b \<otimes>\<^sub>P a')"
      using aeq poly_mult_add_distrib_right [OF a' poly_mult_closed [OF b q] r] by simp
    also have "\<dots> = (b \<otimes>\<^sub>P (q \<otimes>\<^sub>P a')) \<oplus>\<^sub>P (pmod a b \<otimes>\<^sub>P a')"
      using poly_mult_assoc [OF b q a'] by simp
    finally show ?thesis .
  qed
  have step2: "pmod a b \<otimes>\<^sub>P a' = (b \<otimes>\<^sub>P (pmod a b \<otimes>\<^sub>P q')) \<oplus>\<^sub>P (pmod a b \<otimes>\<^sub>P pmod a' b)"
  proof -
    have "pmod a b \<otimes>\<^sub>P a' = (pmod a b \<otimes>\<^sub>P (b \<otimes>\<^sub>P q')) \<oplus>\<^sub>P (pmod a b \<otimes>\<^sub>P pmod a' b)"
      using a'eq poly_mult_add_distrib_left [OF r poly_mult_closed [OF b q'] r'] by simp
    also have "pmod a b \<otimes>\<^sub>P (b \<otimes>\<^sub>P q') = b \<otimes>\<^sub>P (pmod a b \<otimes>\<^sub>P q')"
      using b q' r by (metis poly_mult_assoc poly_mult_comm)
    finally show ?thesis .
  qed
  have "pmod (a \<otimes>\<^sub>P a') b = pmod (pmod a b \<otimes>\<^sub>P a') b"
    using step1 pmod_shift [OF poly_mult_closed [OF r a'] poly_mult_closed [OF q a'] b bnz] by simp
  also have "\<dots> = pmod (pmod a b \<otimes>\<^sub>P pmod a' b) b"
    using step2 pmod_shift [OF poly_mult_closed [OF r r'] poly_mult_closed [OF r q'] b bnz] by simp
  finally show ?thesis .
qed

subsection \<open>The factor theorem\<close>

text \<open>The root factor @{term "root_factor a"} has degree exactly @{text 1}: its degree-1
  coefficient is @{term \<one>}, which is nonzero in a (nontrivial) field.\<close>
lemma degree_root_factor:
  assumes a: "a \<in> R" shows "degree (root_factor a) = 1"
proof (rule antisym)
  have rf: "root_factor a \<in> poly_carrier" using a by (rule root_factor_closed)
  \<comment> \<open>Coefficients above @{text 1} vanish.\<close>
  show "degree (root_factor a) \<le> 1"
    using a rf unfolding root_factor_def poly_const_def
    by (intro degree_leI) (auto simp: poly_add_def poly_neg_def coeff_var poly_const_def)
  \<comment> \<open>The degree-1 coefficient is @{term \<one>}, which is nonzero.\<close>
  have "root_factor a 1 = \<one>"
    using a poly_const_def coeff_var poly_add_def poly_neg_def root_factor_def by fastforce
  then show "1 \<le> degree (root_factor a)"
    using degree_le_iff nontrivial rf by fastforce
qed

lemma root_factor_nonzero:
  assumes a: "a \<in> R" shows "root_factor a \<noteq> \<zero>\<^sub>P"
  using assms degree_root_factor by force

text \<open>\<^emph>\<open>The factor theorem.\<close>  A field element @{term a} is a root of @{term p} 
     iff the linear polynomial @{term "root_factor a"} divides @{term p}.\<close>
theorem factor_theorem:
  assumes p: "p \<in> poly_carrier" and a: "a \<in> R"
  shows "eval a p = \<zero> \<longleftrightarrow> (\<exists>q. q \<in> poly_carrier \<and> p = root_factor a \<otimes>\<^sub>P q)"
proof
  assume "\<exists>q. q \<in> poly_carrier \<and> p = root_factor a \<otimes>\<^sub>P q" then show "eval a p = \<zero>"
    using a eval_mult root_factor_closed by force
next
  assume root: "eval a p = \<zero>"
  have rf: "root_factor a \<in> poly_carrier" using a by (rule root_factor_closed)
  have rfnz: "root_factor a \<noteq> \<zero>\<^sub>P" using a by (rule root_factor_nonzero)
  \<comment> \<open>Divide by the degree-1 factor; the remainder has degree @{text "< 1"}, so is a constant.\<close>
  obtain q r where q: "q \<in> poly_carrier" and r: "r \<in> poly_carrier"
    and peq: "p = (root_factor a \<otimes>\<^sub>P q) \<oplus>\<^sub>P r"
    and rdeg: "r = \<zero>\<^sub>P \<or> degree r < degree (root_factor a)"
    using poly_divide[OF p rf rfnz] by blast
  have rconst: "r = poly_const (r 0)"
    using a degree_root_factor degree_zero_imp_const r rdeg by fastforce
  \<comment> \<open>Evaluate at @{term a}: the @{term "root_factor a"} term vanishes, leaving the constant.\<close>
  have rqc: "root_factor a \<otimes>\<^sub>P q \<in> poly_carrier" using rf q by (rule poly_mult_closed)
  have r0: "r 0 \<in> R" using r by (simp add: poly_carrier_coeff_closed)
  have "\<zero> = \<zero> + r 0"
    using Ring.eval_const Ring_axioms a eval_add eval_mult peq q r r0 rconst rf root rqc
    by fastforce
  then have rz: "r = \<zero>\<^sub>P" using rconst
    using poly_const_zero r0 by force
  \<comment> \<open>So @{term p} is exactly the multiple @{term "root_factor a \<otimes>\<^sub>P q"}.\<close>
  have "p = (root_factor a \<otimes>\<^sub>P q) \<oplus>\<^sub>P \<zero>\<^sub>P" using peq rz by simp
  also have "\<dots> = root_factor a \<otimes>\<^sub>P q" 
    using rqc poly_add_comm[OF rqc poly_zero_closed] poly_add_zero by force
  finally have "p = root_factor a \<otimes>\<^sub>P q" .
  then show "\<exists>q. q \<in> poly_carrier \<and> p = root_factor a \<otimes>\<^sub>P q" using q by blast
qed

subsection \<open>A nonzero polynomial has at most \<open>degree\<close> roots\<close>

text \<open>Evaluation of the linear factor @{term "root_factor a"} at an arbitrary point @{term b} is
  \<open>b - a\<close>; in particular it is nonzero unless @{term "b = a"}.\<close>
lemma eval_root_factor_apply:
  assumes a: "a \<in> R" and b: "b \<in> R" shows "eval b (root_factor a) = b - a"
proof -
  have nc: "\<ominus>\<^sub>P poly_const a \<in> poly_carrier" 
    using a poly_const_closed poly_neg_closed by simp
  have "eval b (root_factor a) = eval b X\<^sub>P + eval b (\<ominus>\<^sub>P poly_const a)"
    unfolding root_factor_def using var_closed nc b by (rule eval_add)
  also have "\<dots> = b - a"
    by (simp add: a b eval_neg poly_const_closed)
  finally show ?thesis .
qed

text \<open>The root set @{term "{a \<in> R. eval a p = \<zero>}"} of a nonzero polynomial over a field is finite and
  has at most @{term "degree p"} elements.  By induction on the degree: a root @{term a} lets the factor
  theorem write @{term "p = root_factor a \<otimes>\<^sub>P q"} with @{term "degree q = degree p - 1"}
  (@{thm [source] degree_mult}, @{thm [source] degree_root_factor}); as a field has no zero divisors,
  every root of @{term p} is @{term a} or a root of @{term q}.\<close>
theorem card_roots_le_degree:
  "p \<in> poly_carrier \<Longrightarrow> p \<noteq> \<zero>\<^sub>P
     \<Longrightarrow> finite {a \<in> R. eval a p = \<zero>} \<and> card {a \<in> R. eval a p = \<zero>} \<le> degree p"
proof (induct "degree p" arbitrary: p rule: less_induct)
  case less
  note p = \<open>p \<in> poly_carrier\<close> and pnz = \<open>p \<noteq> \<zero>\<^sub>P\<close>
  show ?case
  proof (cases "\<exists>a \<in> R. eval a p = \<zero>")
    case False
    then have e: "{a \<in> R. eval a p = \<zero>} = {}" by blast
    show ?thesis
      unfolding e by simp
  next
    case True
    then obtain a where aR: "a \<in> R" and aroot: "eval a p = \<zero>" by blast
    obtain q where q: "q \<in> poly_carrier" and peq: "p = root_factor a \<otimes>\<^sub>P q" and qnz: "q \<noteq> \<zero>\<^sub>P"
      using factor_theorem[OF p] aroot
      using aR pnz poly_mult_zero_right root_factor_closed by metis
    have rf: "root_factor a \<in> poly_carrier" using aR by (rule root_factor_closed)
    have qnz: "q \<noteq> \<zero>\<^sub>P" using peq pnz by (metis poly_mult_zero_right rf)
    have degp: "degree p = 1 + degree q"
      by (simp add: aR degree_mult degree_root_factor peq q qnz root_factor_closed
          root_factor_nonzero)
    have IH: "finite {b \<in> R. eval b q = \<zero>} \<and> card {b \<in> R. eval b q = \<zero>} \<le> degree q"
      using degp q qnz by (intro less) simp
    \<comment> \<open>Every root of @{term p} is @{term a} or a root of @{term q}.\<close>
    have subset: "{b \<in> R. eval b p = \<zero>} \<subseteq> insert a {b \<in> R. eval b q = \<zero>}"
    proof
      fix b assume "b \<in> {b \<in> R. eval b p = \<zero>}"
      then have bR: "b \<in> R" and broot: "eval b p = \<zero>" by auto
      have "eval b (root_factor a) \<cdot> eval b q = \<zero>"
        using peq eval_mult[OF rf q bR] broot by simp
      then have "eval b (root_factor a) = \<zero> \<or> eval b q = \<zero>"
        using eval_closed[OF rf bR] by (simp add: bR local.no_zero_divisors q)
      then show "b \<in> insert a {b \<in> R. eval b q = \<zero>}"
      proof
        assume "eval b (root_factor a) = \<zero>"
        then have z: "b + (- a) = \<zero>" using eval_root_factor_apply[OF aR bR] by simp
        then show ?thesis
          using aR additive.inverse_unique additive.invertible_left_inverse bR by blast
      qed (auto simp: bR)
    qed
    have "card {a \<in> R. eval a p = \<zero>} \<le> card (insert a {b \<in> R. eval b q = \<zero>})"
      by (simp add: IH card_mono subset)
    also have "\<dots> \<le> degree p"
      using IH degp by (intro card_insert_le_m1) auto
    finally show ?thesis
      using IH finite_subset subset by auto
  qed
qed


subsection \<open>Low-degree irreducibility\<close>

text \<open>Evaluation of a polynomial of degree @{text "\<le> 1"}: @{text "eval \<alpha> c = c 0 + c 1 \<cdot> \<alpha>"}.\<close>
lemma eval_le1:
  assumes c: "c \<in> poly_carrier" and al: "\<alpha> \<in> R" and d: "degree c \<le> 1"
  shows "eval \<alpha> c = c 0 + c 1 \<cdot> \<alpha>"
proof -
  have ci: "\<And>i. c i \<in> R" using c by (simp add: poly_carrier_coeff_closed)
  have "additive.fincomp (\<lambda>i. c i \<cdot> rpow \<alpha> i) {0, 1} = c 0 \<cdot> rpow \<alpha> 0 + c 1 \<cdot> rpow \<alpha> 1"
    using ci al by simp
  then show ?thesis 
    unfolding eval_fincomp_le[OF c al d]
    by (simp add: al atMost_Suc ci insert_commute)
qed

text \<open>Every polynomial of degree @{text 1} over a field has a root, namely
  @{text "-(c 0) \<cdot> (c 1)\<inverse>"}.\<close>
lemma degree1_has_root:
  assumes c: "c \<in> poly_carrier" and d: "degree c = 1"
  shows "\<exists>\<alpha>\<in>R. eval \<alpha> c = \<zero>"
proof -
  have ci: "\<And>i. c i \<in> R" using c by (simp add: poly_carrier_coeff_closed)
  have inv: "multiplicative.invertible (c 1)"
    using c ci coeff_degree_nonzero d field_inverse by force
  then have i1: "multiplicative.inverse (c 1) \<in> R" using ci by simp
  have nc0: "- c 0 \<in> R" using ci by simp
  define \<alpha> where "\<alpha> = (- c 0) \<cdot> multiplicative.inverse (c 1)"
  have aR: "\<alpha> \<in> R" unfolding \<alpha>_def using nc0 i1 by simp
  have "c 1 \<cdot> \<alpha> = (c 1 \<cdot> multiplicative.inverse (c 1)) \<cdot> (- c 0)"
    using \<alpha>_def ci i1 multiplicative.associative multiplicative.commutative by auto
  then have "eval \<alpha> c = \<zero>"
    using aR c ci d eval_le1 inv by force
  then show ?thesis using aR by blast
qed

lemma degree_nz: 
  assumes a: "a \<in> poly_carrier" and nua: "\<not> poly_unit a" and anz: "a \<noteq> \<zero>\<^sub>P"
  shows "degree a \<noteq> 0"
  using degree_zero_imp_const[OF a] coeff_degree_nonzero[OF a anz]
  by (metis a nua poly_carrier_coeff_closed poly_const_unit)


text \<open>\<^emph>\<open>Degree-2 irreducibility criterion.\<close>  A degree-2 polynomial over a field is irreducible
  iff it has no root.  Only the ``no root @{text "\<Rightarrow>"} irreducible'' direction is proved here,
  which is what irreducibility witnesses need.\<close>
theorem degree2_no_root_irreducible:
  assumes p: "p \<in> poly_carrier" and d: "degree p = 2"
    and noroot: "\<And>\<alpha>. \<alpha> \<in> R \<Longrightarrow> eval \<alpha> p \<noteq> \<zero>"
  shows "poly_irreducible p"
proof -
  have pnz: "p \<noteq> \<zero>\<^sub>P" using d by auto
  have pnu: "\<not> poly_unit p"
    using d poly_unit_imp_const by force
  have "poly_unit a \<or> poly_unit b"
    if a: "a \<in> poly_carrier" and b: "b \<in> poly_carrier" and pab: "p = a \<otimes>\<^sub>P b" for a b
  proof (rule ccontr)
    assume non: "\<not> (poly_unit a \<or> poly_unit b)"
    have anz: "a \<noteq> \<zero>\<^sub>P" and bnz: "b \<noteq> \<zero>\<^sub>P"
      using pab pnz a b poly_mult_zero_left poly_mult_zero_right by auto
    \<comment> \<open>Degrees add to @{text 2}; neither factor is a unit, so neither has degree @{text 0}.\<close>
    have dsum: "degree a + degree b = 2" using degree_mult[OF a b anz bnz] pab d by simp
    obtain "degree a \<noteq> 0" and "degree b \<noteq> 0"
      using non a anz b bnz degree_nz by blast
    then have da1: "degree a = 1" using dsum by auto
    obtain \<alpha> where al: "\<alpha> \<in> R" and ra: "eval \<alpha> a = \<zero>" using degree1_has_root[OF a da1] by blast
    have "eval \<alpha> p = eval \<alpha> a \<cdot> eval \<alpha> b" using pab eval_mult[OF a b al] by simp
    also have "\<dots> = \<zero>" using ra eval_closed[OF b al] by (simp add: left_zero)
    finally have "eval \<alpha> p = \<zero>" .
    with noroot[OF al] show False ..
  qed
  then show ?thesis unfolding poly_irreducible_def using p pnz pnu by blast
qed

text \<open>A degree-1 factor of @{term p} supplies a root of @{term p}: if @{term "p = a \<otimes>\<^sub>P b"} with
  @{term a} (or @{term b}) of degree @{text 1}, evaluation at the factor's root kills @{term p}.\<close>
lemma degree1_factor_root:
  assumes a: "a \<in> poly_carrier" and b: "b \<in> poly_carrier" and pab: "p = a \<otimes>\<^sub>P b"
    and da1: "degree a = 1"
  shows "\<exists>\<alpha>\<in>R. eval \<alpha> p = \<zero>"
proof -
  obtain \<alpha> where al: "\<alpha> \<in> R" and ra: "eval \<alpha> a = \<zero>" using degree1_has_root[OF a da1] by blast
  then show ?thesis
    using a b eval_mult pab by force
qed

text \<open>\<^emph>\<open>Degree-3 irreducibility criterion.\<close>  A cubic with no root is irreducible: a nontrivial
  factorisation @{term "p = a \<otimes>\<^sub>P b"} has @{term "degree a + degree b = 3"} with both factors of
  degree @{text "\<ge> 1"}, so one of them has degree @{text 1} and hence furnishes a root of
  @{term p}.\<close>
theorem degree3_no_root_irreducible:
  assumes p: "p \<in> poly_carrier" and d: "degree p = 3"
    and noroot: "\<And>\<alpha>. \<alpha> \<in> R \<Longrightarrow> eval \<alpha> p \<noteq> \<zero>"
  shows "poly_irreducible p"
proof -
  have pnz: "p \<noteq> \<zero>\<^sub>P" using d by auto
  have pnu: "\<not> poly_unit p"
    using assms(2) poly_unit_imp_const by fastforce
  have "poly_unit a \<or> poly_unit b"
    if a: "a \<in> poly_carrier" and b: "b \<in> poly_carrier" and pab: "p = a \<otimes>\<^sub>P b" for a b
  proof (rule ccontr)
    assume non: "\<not> (poly_unit a \<or> poly_unit b)"
    have anz: "a \<noteq> \<zero>\<^sub>P" and bnz: "b \<noteq> \<zero>\<^sub>P"
      using pab pnz a b poly_mult_zero_left poly_mult_zero_right by auto
    \<comment> \<open>Degrees add to @{text 3}; neither factor is a unit, so neither has degree @{text 0}.\<close>
    have dsum: "degree a + degree b = 3" using degree_mult[OF a b anz bnz] pab d by simp
    \<comment> \<open>So one factor has degree @{text 1} (the splits of @{text 3} are @{text "1+2"} and
        @{text "2+1"}), giving a root of @{term p}.\<close>
    obtain "degree a \<noteq> 0" and "degree b \<noteq> 0"
      using non a anz b bnz degree_nz by blast
    then have "degree a = 1 \<or> degree b = 1" using dsum by auto
    then have "\<exists>\<alpha>\<in>R. eval \<alpha> p = \<zero>"
      by (metis a b degree1_factor_root pab poly_mult_comm)
    with noroot show False by blast
  qed
  then show ?thesis unfolding poly_irreducible_def using p pnz pnu by blast
qed


subsection \<open>Factorisation into irreducibles\<close>

text \<open>The product of a list of polynomials (right fold, empty list giving @{term "\<one>\<^sub>P"}).\<close>
definition poly_prod :: "(nat \<Rightarrow> 'a) list \<Rightarrow> (nat \<Rightarrow> 'a)"
  where "poly_prod fs = foldr (\<otimes>\<^sub>P) fs \<one>\<^sub>P"

lemma poly_prod_Nil [simp]: "poly_prod [] = \<one>\<^sub>P"
  by (simp add: poly_prod_def)

lemma poly_prod_Cons [simp]: "poly_prod (f # fs) = f \<otimes>\<^sub>P poly_prod fs"
  by (simp add: poly_prod_def)

lemma poly_prod_closed:
  "(\<And>f. f \<in> set fs \<Longrightarrow> f \<in> poly_carrier) \<Longrightarrow> poly_prod fs \<in> poly_carrier"
  by (induct fs) (auto simp: poly_one_closed poly_mult_closed)

lemma poly_prod_append:
  assumes fs: "\<And>f. f \<in> set fs \<Longrightarrow> f \<in> poly_carrier"
    and gs: "\<And>g. g \<in> set gs \<Longrightarrow> g \<in> poly_carrier"
  shows "poly_prod (fs @ gs) = poly_prod fs \<otimes>\<^sub>P poly_prod gs"
  using fs
proof (induct fs)
  case Nil
  show ?case using poly_mult_one_left [OF poly_prod_closed [OF gs]] by simp
next
  case (Cons f fs)
  have f: "f \<in> poly_carrier" and rest: "\<And>h. h \<in> set fs \<Longrightarrow> h \<in> poly_carrier"
    using Cons.prems by auto
  have Pf: "poly_prod fs \<in> poly_carrier" by (rule poly_prod_closed [OF rest])
  have Pg: "poly_prod gs \<in> poly_carrier" by (rule poly_prod_closed [OF gs])
  have "poly_prod ((f # fs) @ gs) = f \<otimes>\<^sub>P poly_prod (fs @ gs)" by simp
  also have "\<dots> = f \<otimes>\<^sub>P (poly_prod fs \<otimes>\<^sub>P poly_prod gs)"
    using Cons.hyps [OF rest] by simp
  also have "\<dots> = (f \<otimes>\<^sub>P poly_prod fs) \<otimes>\<^sub>P poly_prod gs"
    by (rule poly_mult_assoc [OF f Pf Pg, symmetric])
  finally show ?case by simp
qed

subsection \<open>Splitting into linear factors\<close>

text \<open>A polynomial \<^emph>\<open>splits\<close> when it is a constant times a product of root factors, all of whose roots
  lie in the field.  Equivalently it is a product of linear factors: the constant carries the leading
  coefficient.  Taking that constant to range over the whole field, rather than the nonzero elements,
  lets @{term "\<zero>\<^sub>P"} split as well (empty list, zero constant), so no polynomial is excluded.

  This is the carrier-set counterpart of HOL-Algebra's \<open>splitted\<close>, which counts a root multiset
  instead.  A list of roots is the lighter encoding here, since @{const poly_prod} already exists and
  no multiset machinery is needed.  It is what the algebraic-closure development consumes: the
  property of an extension that every polynomial over the base field splits in it, which is strictly
  stronger than every such polynomial having a \<^emph>\<open>root\<close> --- a root of a polynomial over a subfield
  leaves a cofactor over the larger field, so root existence does not induct.\<close>
definition splits :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "splits p \<longleftrightarrow> (\<exists>c as. c \<in> R \<and> set as \<subseteq> R
                            \<and> p = poly_const c \<otimes>\<^sub>P poly_prod (List.map root_factor as))"

lemma splitsI:
  "\<lbrakk> c \<in> R; set as \<subseteq> R; p = poly_const c \<otimes>\<^sub>P poly_prod (List.map root_factor as) \<rbrakk>
     \<Longrightarrow> splits p"
  unfolding splits_def by blast

lemma splitsE:
  assumes "splits p"
  obtains c as where "c \<in> R" "set as \<subseteq> R"
    and "p = poly_const c \<otimes>\<^sub>P poly_prod (List.map root_factor as)"
  using assms unfolding splits_def by blast

lemma splits_closed: "splits p \<Longrightarrow> p \<in> poly_carrier"
proof (elim splitsE)
  fix c as assume c: "c \<in> R" and as: "set as \<subseteq> R"
    and peq: "p = poly_const c \<otimes>\<^sub>P poly_prod (List.map root_factor as)"
  have "poly_prod (List.map root_factor as) \<in> poly_carrier"
    using as by (intro poly_prod_closed) (auto intro: root_factor_closed)
  then show "p \<in> poly_carrier" using peq poly_const_closed [OF c] by (simp add: poly_mult_closed)
qed

lemma splits_const:
  assumes c: "c \<in> R" shows "splits (poly_const c)"
proof (rule splitsI [where c = c and as = "[]"])
  show "c \<in> R" by (rule c)
  show "set [] \<subseteq> R" by simp
  show "poly_const c = poly_const c \<otimes>\<^sub>P poly_prod (List.map root_factor [])"
    using poly_mult_one_right [OF poly_const_closed [OF c]] by simp
qed

lemma splits_zero [simp]: "splits \<zero>\<^sub>P"
  using splits_const [of \<zero>] by simp

lemma splits_root_factor:
  assumes a: "a \<in> R" shows "splits (root_factor a)"
proof (rule splitsI [where c = \<one> and as = "[a]"])
  show "\<one> \<in> R" by simp
  show "set [a] \<subseteq> R" using a by simp
  have rf: "root_factor a \<in> poly_carrier" using a by (rule root_factor_closed)
  show "root_factor a = poly_const \<one> \<otimes>\<^sub>P poly_prod (List.map root_factor [a])"
    using poly_mult_one_right [OF rf] poly_mult_one_left [OF rf] by simp
qed

text \<open>Splitting is multiplicative: concatenate the root lists and multiply the constants.\<close>
lemma splits_mult:
  assumes p: "splits p" and q: "splits q" shows "splits (p \<otimes>\<^sub>P q)"
proof -
  obtain c as where c: "c \<in> R" and as: "set as \<subseteq> R"
    and peq: "p = poly_const c \<otimes>\<^sub>P poly_prod (List.map root_factor as)"
    using p by (rule splitsE)
  obtain d bs where d: "d \<in> R" and bs: "set bs \<subseteq> R"
    and qeq: "q = poly_const d \<otimes>\<^sub>P poly_prod (List.map root_factor bs)"
    using q by (rule splitsE)
  have pa: "poly_prod (List.map root_factor as) \<in> poly_carrier"
    using as by (intro poly_prod_closed) (auto intro: root_factor_closed)
  have pb: "poly_prod (List.map root_factor bs) \<in> poly_carrier"
    using bs by (intro poly_prod_closed) (auto intro: root_factor_closed)
  have prod_app: "poly_prod (List.map root_factor (as @ bs))
                  = poly_prod (List.map root_factor as) \<otimes>\<^sub>P poly_prod (List.map root_factor bs)"
    unfolding List.map_append
  proof (rule poly_prod_append)
    show "\<And>f. f \<in> set (List.map root_factor as) \<Longrightarrow> f \<in> poly_carrier"
      using as by (auto intro: root_factor_closed)
    show "\<And>g. g \<in> set (List.map root_factor bs) \<Longrightarrow> g \<in> poly_carrier"
      using bs by (auto intro: root_factor_closed)
  qed
  show ?thesis
  proof (rule splitsI [where c = "c \<cdot> d" and as = "as @ bs"])
    show "c \<cdot> d \<in> R" using c d by simp
    show "set (as @ bs) \<subseteq> R" using as bs by simp
    show "p \<otimes>\<^sub>P q = poly_const (c \<cdot> d) \<otimes>\<^sub>P poly_prod (List.map root_factor (as @ bs))"
    proof -
      have cc: "poly_const c \<in> poly_carrier" using c by (rule poly_const_closed)
      have dc: "poly_const d \<in> poly_carrier" using d by (rule poly_const_closed)
      have "p \<otimes>\<^sub>P q
            = (poly_const c \<otimes>\<^sub>P poly_prod (List.map root_factor as))
              \<otimes>\<^sub>P (poly_const d \<otimes>\<^sub>P poly_prod (List.map root_factor bs))"
        using peq qeq by simp
      also have "\<dots> = (poly_const c \<otimes>\<^sub>P poly_const d)
                       \<otimes>\<^sub>P (poly_prod (List.map root_factor as)
                            \<otimes>\<^sub>P poly_prod (List.map root_factor bs))"
      proof -
        \<comment> \<open>Pure rearrangement: swap the middle two factors.\<close>
        have "(poly_const c \<otimes>\<^sub>P pa') \<otimes>\<^sub>P (poly_const d \<otimes>\<^sub>P pb')
              = (poly_const c \<otimes>\<^sub>P poly_const d) \<otimes>\<^sub>P (pa' \<otimes>\<^sub>P pb')"
          if A: "pa' \<in> poly_carrier" and B: "pb' \<in> poly_carrier" for pa' pb'
        proof -
          have "(poly_const c \<otimes>\<^sub>P pa') \<otimes>\<^sub>P (poly_const d \<otimes>\<^sub>P pb')
                = poly_const c \<otimes>\<^sub>P (pa' \<otimes>\<^sub>P (poly_const d \<otimes>\<^sub>P pb'))"
            by (rule poly_mult_assoc [OF cc A poly_mult_closed [OF dc B]])
          also have "pa' \<otimes>\<^sub>P (poly_const d \<otimes>\<^sub>P pb') = (pa' \<otimes>\<^sub>P poly_const d) \<otimes>\<^sub>P pb'"
            by (rule poly_mult_assoc [OF A dc B, symmetric])
          also have "pa' \<otimes>\<^sub>P poly_const d = poly_const d \<otimes>\<^sub>P pa'"
            by (rule poly_mult_comm [OF A dc])
          also have "(poly_const d \<otimes>\<^sub>P pa') \<otimes>\<^sub>P pb' = poly_const d \<otimes>\<^sub>P (pa' \<otimes>\<^sub>P pb')"
            by (rule poly_mult_assoc [OF dc A B])
          also have "poly_const c \<otimes>\<^sub>P (poly_const d \<otimes>\<^sub>P (pa' \<otimes>\<^sub>P pb'))
                     = (poly_const c \<otimes>\<^sub>P poly_const d) \<otimes>\<^sub>P (pa' \<otimes>\<^sub>P pb')"
            by (rule poly_mult_assoc [OF cc dc poly_mult_closed [OF A B], symmetric])
          finally show ?thesis .
        qed
        from this [OF pa pb] show ?thesis .
      qed
      also have "\<dots> = poly_const (c \<cdot> d)
                       \<otimes>\<^sub>P poly_prod (List.map root_factor (as @ bs))"
        using poly_const_mult [OF c d] prod_app by simp
      finally show ?thesis .
    qed
  qed
qed

text \<open>\<^emph>\<open>A polynomial of degree one splits.\<close>  Divide by the leading coefficient: the result is
  @{term "root_factor a"} for @{term a} the negated ratio of the two coefficients.  This is the base
  case that makes a factorisation into linear factors out of a factorisation into irreducibles all of
  whose factors have degree one.\<close>
lemma degree_one_splits:
  assumes q: "q \<in> poly_carrier" and d: "degree q = 1"
  shows "splits q"
proof -
  have qnz: "q \<noteq> \<zero>\<^sub>P" using d by auto
  have c: "q 1 \<in> R" and q0: "q 0 \<in> R" using q by (blast intro: poly_carrier_coeff_closed)+
  have cnz: "q 1 \<noteq> \<zero>"
    using lead_coeff_nonzero [OF q qnz] d by (simp add: lead_coeff_def)
  have inv: "multiplicative.invertible (q 1)" by (rule field_inverse [OF c cnz])
  define e where "e = multiplicative.inverse (q 1)"
  have eR: "e \<in> R"
    unfolding e_def by (rule multiplicative.invertible_inverse_closed [OF inv c])
  have ce: "q 1 \<cdot> e = \<one>"
    unfolding e_def by (rule multiplicative.invertible_right_inverse [OF inv c])
  define a where "a = - (e \<cdot> q 0)"
  have eq0: "e \<cdot> q 0 \<in> R" using eR q0 by simp
  have aR: "a \<in> R" unfolding a_def using eq0 by (simp add: additive.invertible_inverse_closed)
  have nega: "- a = e \<cdot> q 0" unfolding a_def using eq0 by simp
  have rf: "root_factor a \<in> poly_carrier" using aR by (rule root_factor_closed)
  \<comment> \<open>Multiplying by a constant scales each coefficient.\<close>
  have scale: "(poly_const (q 1) \<otimes>\<^sub>P root_factor a) j = q 1 \<cdot> root_factor a j" for j
    using coeff_monom_mult [OF c rf, of 0 j] by (simp add: monom_0_eq_const)
  \<comment> \<open>The three coefficients of @{term "root_factor a"}.\<close>
  have rf0: "root_factor a 0 = - a"
    using aR by (simp add: root_factor_def var_def monom_def poly_const_def poly_add_def
                           poly_neg_def additive.invertible_inverse_closed)
  have rf1: "root_factor a 1 = \<one>"
    by (simp add: root_factor_def var_def monom_def poly_const_def poly_add_def poly_neg_def)
  have rfj: "root_factor a j = \<zero>" if "j \<noteq> 0" "j \<noteq> 1" for j
    using that by (simp add: root_factor_def var_def monom_def poly_const_def poly_add_def
                             poly_neg_def)
  have qeq: "q = poly_const (q 1) \<otimes>\<^sub>P root_factor a"
  proof (rule ext)
    fix j
    show "q j = (poly_const (q 1) \<otimes>\<^sub>P root_factor a) j"
    proof (cases "j = 0")
      case True
      have "q 1 \<cdot> (- a) = (q 1 \<cdot> e) \<cdot> q 0"
        using nega c eR q0 by (simp add: multiplicative.associative)
      also have "\<dots> = q 0" using ce q0 by simp
      finally show ?thesis using True scale rf0 by simp
    next
      case False
      show ?thesis
      proof (cases "j = 1")
        case True
        then show ?thesis using scale rf1 c by simp
      next
        case False
        with \<open>j \<noteq> 0\<close> have "degree q < j" using d by simp
        then show ?thesis
          using scale rfj [OF \<open>j \<noteq> 0\<close> False] coeff_gt_degree [OF q] c by simp
      qed
    qed
  qed
  show ?thesis
  proof (rule splitsI [where c = "q 1" and as = "[a]"])
    show "q 1 \<in> R" by (rule c)
    show "set [a] \<subseteq> R" using aR by simp
    show "q = poly_const (q 1) \<otimes>\<^sub>P poly_prod (List.map root_factor [a])"
      using qeq poly_mult_one_right [OF rf] by simp
  qed
qed

lemma splits_poly_prod:
  assumes "\<And>f. f \<in> set fs \<Longrightarrow> splits f" shows "splits (poly_prod fs)"
  using assms
proof (induct fs)
  case Nil
  have "splits (poly_const \<one>)" by (rule splits_const) simp
  then show ?case by simp
next
  case (Cons f fs)
  have "splits f" using Cons.prems by simp
  moreover have "splits (poly_prod fs)" using Cons.prems by (intro Cons.hyps) simp
  ultimately show ?case by (simp add: splits_mult)
qed


text \<open>\<^emph>\<open>Existence of an irreducible factorisation.\<close>  Every nonzero non-unit polynomial over a field
  is a product of a nonempty list of irreducibles.  By strong induction on the degree: an
  irreducible @{term p} is its own singleton factorisation; otherwise @{term "p = a \<otimes>\<^sub>P b"} with
  both factors non-units --- hence, over a field, of strictly smaller degree --- and the induction
  hypothesis factors each.\<close>
theorem factorization_into_irreducibles:
  assumes "p \<in> poly_carrier" and "p \<noteq> \<zero>\<^sub>P" and "\<not> poly_unit p"
  shows "\<exists>fs. fs \<noteq> [] \<and> (\<forall>f\<in>set fs. poly_irreducible f) \<and> p = poly_prod fs"
  using assms
proof (induct "degree p" arbitrary: p rule: less_induct)
  case (less p)
  show ?case
  proof (cases "poly_irreducible p")
    case True
    \<comment> \<open>@{term p} is its own factorisation.\<close>
    have "p = poly_prod [p]" using less.prems by (simp add: poly_mult_one_right)
    moreover have "[p] \<noteq> [] \<and> (\<forall>f\<in>set [p]. poly_irreducible f)" using True by simp
    ultimately show ?thesis by blast
  next
    case False
    \<comment> \<open>A nontrivial factorisation into non-units @{term a}, @{term b}.\<close>
    from less.prems False obtain a b where a: "a \<in> poly_carrier" and b: "b \<in> poly_carrier"
      and pab: "p = a \<otimes>\<^sub>P b" and nua: "\<not> poly_unit a" and nub: "\<not> poly_unit b"
      unfolding poly_irreducible_def by blast
    have anz: "a \<noteq> \<zero>\<^sub>P" and bnz: "b \<noteq> \<zero>\<^sub>P"
      using pab less.prems(2) a b poly_mult_zero_left poly_mult_zero_right by auto
    have dsum: "degree a + degree b = degree p"
      using degree_mult[OF a b anz bnz] pab by simp
    \<comment> \<open>Neither factor has degree @{text 0} (that would make it a unit), so each has degree
        strictly below @{term "degree p"}.\<close>
    obtain "degree a \<noteq> 0" and "degree b \<noteq> 0"
      using a anz b bnz degree_nz nua nub by blast
    then have da: "degree a < degree p" and db: "degree b < degree p" using dsum by auto
    \<comment> \<open>Factor each smaller factor by the induction hypothesis, then concatenate.\<close>
    obtain fa where fa: "fa \<noteq> []" "\<forall>f\<in>set fa. poly_irreducible f" "a = poly_prod fa"
      using less.hyps[OF da a anz nua] by blast
    obtain fb where fb: "fb \<noteq> []" "\<forall>f\<in>set fb. poly_irreducible f" "b = poly_prod fb"
      using less.hyps[OF db b bnz nub] by blast
    have "p = poly_prod (fa @ fb)"
    proof -
      have "poly_prod (fa @ fb) = poly_prod fa \<otimes>\<^sub>P poly_prod fb"
        using fa(2) fb(2)
      proof (induct fa)
        case Nil
        then show ?case
          using b fb(3) poly_mult_one_left by auto
      next
        case (Cons g gs)
        have gc: "g \<in> poly_carrier" using Cons.prems by (simp add: poly_irreducibleD_carrier)
        have gsc: "poly_prod gs \<in> poly_carrier"
          by (simp add: Cons.prems(1) poly_irreducibleD_carrier poly_prod_closed)
        have "poly_prod fb \<in> poly_carrier"
          using b fb(3) by auto
        then show ?case
          by (simp add: Cons.hyps Cons.prems gc gsc poly_mult_assoc)
      qed
      then show ?thesis using pab fa(3) fb(3) by simp
    qed
    moreover have "\<forall>f\<in>set (fa @ fb). poly_irreducible f" using fa(2) fb(2) by auto
    ultimately show ?thesis
      using fa(1) by blast
  qed
qed


subsection \<open>Monic polynomials and normalisation\<close>

text \<open>A polynomial is \<^emph>\<open>monic\<close> when it is nonzero with leading coefficient @{term \<one>}.\<close>
definition poly_monic :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "poly_monic p \<longleftrightarrow> p \<noteq> \<zero>\<^sub>P \<and> lead_coeff p = \<one>"

text \<open>Scaling a nonzero polynomial by a nonzero constant preserves its degree and scales its
  leading coefficient.\<close>
lemma degree_poly_const_mult:
  assumes c: "c \<in> R" and cnz: "c \<noteq> \<zero>" and p: "p \<in> poly_carrier" and pnz: "p \<noteq> \<zero>\<^sub>P"
  shows "degree (poly_const c \<otimes>\<^sub>P p) = degree p"
  by (simp add: c cnz degree_mult p pnz poly_const_closed poly_const_unit poly_unit_imp_const)

lemma lead_coeff_poly_const_mult:
  assumes c: "c \<in> R" and cnz: "c \<noteq> \<zero>" and p: "p \<in> poly_carrier" and pnz: "p \<noteq> \<zero>\<^sub>P"
  shows "lead_coeff (poly_const c \<otimes>\<^sub>P p) = c \<cdot> lead_coeff p"
proof -
  have cc: "poly_const c \<in> poly_carrier" using c by (rule poly_const_closed)
  have dc0: "degree (poly_const c) = 0" using degree_const_le by (simp add: le_zero_eq)
  have deg: "degree (poly_const c \<otimes>\<^sub>P p) = degree p" using degree_poly_const_mult[OF c cnz p pnz] .
  have "lead_coeff (poly_const c \<otimes>\<^sub>P p) = poly_const c (degree (poly_const c)) \<cdot> p (degree p)"
    using coeff_mult_degree_add[OF cc p] by (simp add: dc0 deg lead_coeff_def)
  also have "\<dots> = c \<cdot> p (degree p)"
    using dc0 poly_const_def by auto
  finally show ?thesis by (simp add: lead_coeff_def)
qed

text \<open>Every nonzero polynomial has a monic associate, obtained by scaling by the inverse of its
  leading coefficient.\<close>
theorem monic_associate_exists:
  assumes p: "p \<in> poly_carrier" and pnz: "p \<noteq> \<zero>\<^sub>P"
  shows "\<exists>u m. u \<in> R \<and> u \<noteq> \<zero> \<and> m \<in> poly_carrier \<and> poly_monic m \<and> p = poly_const u \<otimes>\<^sub>P m"
proof -
  have lc: "lead_coeff p \<in> R" 
    using p by (simp add: lead_coeff_def poly_carrier_coeff_closed)
  have lcnz: "lead_coeff p \<noteq> \<zero>" 
    using p pnz by (rule lead_coeff_nonzero)
  define c where "c = multiplicative.inverse (lead_coeff p)"
  have inv: "multiplicative.invertible (lead_coeff p)" using lc lcnz by (rule field_inverse)
  have cR: "c \<in> R" unfolding c_def using lc inv by simp
  have cnz: "c \<noteq> \<zero>"
    using c_def inv lc multiplicative.invertible_inverse_invertible nontrivial
    by fastforce
  define m where "m = poly_const c \<otimes>\<^sub>P p"
  have cc: "poly_const c \<in> poly_carrier" using cR by (rule poly_const_closed)
  have mc: "m \<in> poly_carrier" unfolding m_def using cc p by (rule poly_mult_closed)
  \<comment> \<open>@{term m} is monic: its leading coefficient is @{text "c \<cdot> lead_coeff p = \<one>"}.\<close>
  have cnzp: "poly_const c \<noteq> \<zero>\<^sub>P" using cnz by (auto simp: poly_const_def poly_zero_def fun_eq_iff)
  have mnz: "m \<noteq> \<zero>\<^sub>P" unfolding m_def
    using poly_no_zero_divisors[OF cc p] cnzp pnz by auto
  have eq1: "multiplicative.inverse (lead_coeff p) \<cdot> lead_coeff p = \<one>"
    using inv lc by simp
  have "lead_coeff m = \<one>"
    by (metis cR c_def cnz eq1 lead_coeff_poly_const_mult m_def p pnz)
  then have monic_m: "poly_monic m" 
    using mnz by (simp add: poly_monic_def)
  \<comment> \<open>Recover @{term p} by scaling @{term m} by @{term "lead_coeff p"}.\<close>
  have "poly_const (lead_coeff p) \<otimes>\<^sub>P m = poly_const (lead_coeff p) \<otimes>\<^sub>P (poly_const c \<otimes>\<^sub>P p)"
    unfolding m_def ..
  also have "\<dots> = poly_const \<one> \<otimes>\<^sub>P p"
    using cR unfolding c_def
    by (metis eq1 lc multiplicative.commutative p poly_const_closed poly_const_mult poly_mult_assoc)
   also have "\<dots> = p" 
    using p by (simp add: poly_mult_one_left)
  finally have "p = poly_const (lead_coeff p) \<otimes>\<^sub>P m" ..
  then show ?thesis using lc lcnz mc monic_m by blast
qed


subsection \<open>The polynomial ring over a field is a principal ideal domain\<close>

text \<open>\<^emph>\<open>Every ideal of \<open>F[X]\<close> is principal.\<close>  Given an ideal @{term J}, the zero ideal is
  generated by @{term "\<zero>\<^sub>P"}; otherwise pick a nonzero @{term b} of \<^emph>\<open>least degree\<close> in @{term J}.
  Dividing any @{term "a \<in> J"} by @{term b} (the division algorithm @{thm [source] poly_divide})
  leaves a remainder that again lies in @{term J} but has degree below that of @{term b}, so by
  minimality it must be zero: hence @{term a} is a multiple of @{term b}.  This is the structural
  fact behind Kronecker's construction --- it makes \<open>(p)\<close> maximal for irreducible @{term p}, and
  so @{text "F[X]/(p)"} a field.\<close>
theorem poly_PID:
  assumes J: "Ideal J poly_carrier (\<oplus>\<^sub>P) (\<otimes>\<^sub>P) \<zero>\<^sub>P \<one>\<^sub>P"
  shows "\<exists>b. b \<in> poly_carrier \<and> J = {r \<otimes>\<^sub>P b | r. r \<in> poly_carrier}"
proof -
  interpret J: Ideal J poly_carrier "(\<oplus>\<^sub>P)" "(\<otimes>\<^sub>P)" "\<zero>\<^sub>P" "\<one>\<^sub>P" by (rule J)
  show ?thesis
  proof (cases "J = {\<zero>\<^sub>P}")
    case True
    then show ?thesis using poly_zero_closed by force
  next
    case False
    \<comment> \<open>Otherwise @{term J} contains a nonzero element, hence one of least degree.\<close>
    have ex: "\<exists>a. a \<in> J \<and> a \<noteq> \<zero>\<^sub>P"
      using False by blast
    define hasdeg where "hasdeg n \<longleftrightarrow> (\<exists>a. a \<in> J \<and> a \<noteq> \<zero>\<^sub>P \<and> degree a = n)" for n
    have "\<exists>n. hasdeg n" using ex unfolding hasdeg_def by blast
    then have "hasdeg (LEAST n. hasdeg n)" by (rule LeastI_ex)
    then obtain b where bJ: "b \<in> J" and bnz: "b \<noteq> \<zero>\<^sub>P"
      and bLeast: "degree b = (LEAST n. hasdeg n)"
      unfolding hasdeg_def by blast
    have bP: "b \<in> poly_carrier" using bJ J.additive.subset by blast
    \<comment> \<open>@{term b} has least degree among the nonzero elements of @{term J}.\<close>
    have minimal: "degree b \<le> degree c" if "c \<in> J" "c \<noteq> \<zero>\<^sub>P" for c
      by (metis Least_le bLeast hasdeg_def that)
    \<comment> \<open>@{term J} is exactly the principal ideal generated by @{term b}.\<close>
    have "J = {r \<otimes>\<^sub>P b | r. r \<in> poly_carrier}"
    proof
      show "J \<subseteq> {r \<otimes>\<^sub>P b | r. r \<in> poly_carrier}"
      proof
        fix a assume aJ: "a \<in> J"
        have aP: "a \<in> poly_carrier" using aJ J.additive.subset by blast
        obtain q rem where q: "q \<in> poly_carrier" and rem: "rem \<in> poly_carrier"
          and aeq: "a = (b \<otimes>\<^sub>P q) \<oplus>\<^sub>P rem"
          and remd: "rem = \<zero>\<^sub>P \<or> degree rem < degree b"
          using poly_divide[OF aP bP bnz] by blast
        have bqc: "b \<otimes>\<^sub>P q \<in> poly_carrier" using bP q by (rule poly_mult_closed)
        \<comment> \<open>The multiple @{term "b \<otimes>\<^sub>P q"} and its negative both lie in @{term J}.\<close>
        have bqJ: "b \<otimes>\<^sub>P q \<in> J" using q bJ by (rule J.Ideal(2))
        have "J.additive.inverse (b \<otimes>\<^sub>P q) \<in> J" using bqJ by simp
        have negbqJ: "\<ominus>\<^sub>P (b \<otimes>\<^sub>P q) \<in> J"
        proof -
          have "J.additive.inverse (b \<otimes>\<^sub>P q) \<in> J" using bqJ by simp
          moreover have "J.additive.inverse (b \<otimes>\<^sub>P q) = \<ominus>\<^sub>P (b \<otimes>\<^sub>P q)"
            by (simp add: bqc poly_minus_unique)
          ultimately show ?thesis by simp
        qed
        \<comment> \<open>So the remainder @{text "rem = \<ominus>(b \<otimes> q) \<oplus> a"} lies in @{term J} too.\<close>
        have rem_eq: "rem = (\<ominus>\<^sub>P (b \<otimes>\<^sub>P q)) \<oplus>\<^sub>P a"
          by (metis aeq bqc poly_add_comm poly_add_minus_cancel poly_neg_closed poly_neg_neg rem)
        have remJ: "rem \<in> J"
          unfolding rem_eq using negbqJ aJ by (rule J.additive.sub_composition_closed)
        have "rem = \<zero>\<^sub>P"
          using leD minimal remJ remd by auto
        then have "a = q \<otimes>\<^sub>P b"
          by (simp add: aeq bP poly_mult_comm q)
        then show "a \<in> {r \<otimes>\<^sub>P b | r. r \<in> poly_carrier}" using q by blast
      qed
    next
      show "{r \<otimes>\<^sub>P b | r. r \<in> poly_carrier} \<subseteq> J"
        by (auto simp: J.Ideal(1) bJ)
    qed
    then show ?thesis using bP by blast
  qed
qed

end


section \<open>Pushing a Polynomial along a Ring Homomorphism\<close>

text \<open>Coefficientwise application of a ring homomorphism commutes with every operation of the
  polynomial ring.  HOL-Algebra obtains the corresponding facts from \<open>map_poly\<close> and
  \<open>ring_hom_ring.subfield_polynomial_hom\<close>; the carrier-set layer has no homomorphism apparatus at
  this level, so they are proved here directly, in the style of \<open>eval_hom\<close>.\<close>

context
  fixes A :: "'b set" and add mult :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" and z u :: 'b
    and B :: "'c set" and badd bmult :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" and bz bu :: 'c
    and h :: "'b \<Rightarrow> 'c"
  assumes RA: "Ring A add mult z u" and RB: "Ring B badd bmult bz bu"
    and hB: "\<And>y. y \<in> A \<Longrightarrow> h y \<in> B"
    and hz: "h z = bz" and hu: "h u = bu"
    and hadd: "\<And>y y'. \<lbrakk> y \<in> A; y' \<in> A \<rbrakk> \<Longrightarrow> h (add y y') = badd (h y) (h y')"
    and hmult: "\<And>y y'. \<lbrakk> y \<in> A; y' \<in> A \<rbrakk> \<Longrightarrow> h (mult y y') = bmult (h y) (h y')"
begin

lemma cmA: "commutative_monoid A add z"
  using RA by (simp add: Ring_def Abelian_Group_def)

lemma cmB: "commutative_monoid B badd bz"
  using RB by (simp add: Ring_def Abelian_Group_def)

lemma gpA: "Abelian_Group A add z"
  using RA by (simp add: Ring_def)

lemma gpB: "Abelian_Group B badd bz"
  using RB by (simp add: Ring_def)

lemma monA: "Monoid A mult u"
  using RA by (simp add: Ring_def)

lemma poly_zero_hom: "(\<lambda>k. h (Ring.poly_zero z k)) = Ring.poly_zero bz"
  by (simp add: Ring.poly_zero_def [OF RA] Ring.poly_zero_def [OF RB] hz)

lemma poly_one_hom: "(\<lambda>k. h (Ring.poly_one z u k)) = Ring.poly_one bz bu"
  by (rule ext) (simp add: Ring.poly_one_def [OF RA] Ring.poly_one_def [OF RB] hz hu)

lemma poly_const_hom: "(\<lambda>k. h (Ring.poly_const z c k)) = Ring.poly_const bz (h c)"
  by (rule ext) (simp add: Ring.poly_const_def [OF RA] Ring.poly_const_def [OF RB] hz)

lemma var_hom: "(\<lambda>k. h (Ring.var z u k)) = Ring.var bz bu"
  by (rule ext) (simp add: Ring.var_def [OF RA] Ring.var_def [OF RB]
                           Ring.monom_def [OF RA] Ring.monom_def [OF RB] hz hu)

text \<open>Coefficients of the polynomials named above, needed as closure side conditions below.\<close>

lemma zA: "z \<in> A"
proof -
  interpret GA: Abelian_Group A add z by (rule gpA)
  show ?thesis by simp
qed

lemma uA: "u \<in> A"
proof -
  interpret MA: Monoid A mult u by (rule monA)
  show ?thesis by simp
qed

lemma poly_const_coeff_closed: "c \<in> A \<Longrightarrow> Ring.poly_const z c k \<in> A"
  using zA by (simp add: Ring.poly_const_def [OF RA])

lemma var_coeff_closed: "Ring.var z u k \<in> A"
  using zA uA by (simp add: Ring.var_def [OF RA] Ring.monom_def [OF RA])

lemma poly_add_hom:
  assumes p: "\<And>k. p k \<in> A" and q: "\<And>k. q k \<in> A"
  shows "(\<lambda>k. h (Ring.poly_add add p q k))
       = Ring.poly_add badd (\<lambda>k. h (p k)) (\<lambda>k. h (q k))"
  by (rule ext) (simp add: Ring.poly_add_def [OF RA] Ring.poly_add_def [OF RB] hadd p q)

text \<open>The additive inverse is pinned by the equation it solves, so a homomorphism of the additive
  groups carries it along.\<close>
lemma inverse_hom:
  assumes y: "y \<in> A"
  shows "h (Monoid.inverse A add z y) = Monoid.inverse B badd bz (h y)"
proof -
  interpret GA: Abelian_Group A add z by (rule gpA)
  interpret GB: Abelian_Group B badd bz by (rule gpB)
  have inv: "Monoid.inverse A add z y \<in> A" using y by simp
  have "badd (h y) (h (Monoid.inverse A add z y)) = h (add y (Monoid.inverse A add z y))"
    by (rule hadd [OF y inv, symmetric])
  also have "\<dots> = h z" using y by simp
  finally have 1: "badd (h y) (h (Monoid.inverse A add z y)) = bz" by (simp add: hz)
  have "badd (h (Monoid.inverse A add z y)) (h y) = h (add (Monoid.inverse A add z y) y)"
    by (rule hadd [OF inv y, symmetric])
  also have "\<dots> = h z" using y by simp
  finally have 2: "badd (h (Monoid.inverse A add z y)) (h y) = bz" by (simp add: hz)
  show ?thesis
    using 1 2 hB [OF y] hB [OF inv] by (intro GB.inverse_equality [symmetric]) auto
qed

lemma poly_neg_hom:
  assumes p: "\<And>k. p k \<in> A"
  shows "(\<lambda>k. h (Ring.poly_neg A add z p k)) = Ring.poly_neg B badd bz (\<lambda>k. h (p k))"
  by (rule ext) (simp add: Ring.poly_neg_def [OF RA] Ring.poly_neg_def [OF RB] inverse_hom p)

lemma poly_neg_coeff_closed:
  assumes p: "\<And>k. p k \<in> A"
  shows "Ring.poly_neg A add z p k \<in> A"
proof -
  interpret GA: Abelian_Group A add z by (rule gpA)
  show ?thesis using p by (simp add: Ring.poly_neg_def [OF RA])
qed

text \<open>Convolution is a finite composite of products, so it pushes along by @{thm [source] fincomp_hom}.
  Only the two monoid premises are supplied: resolving the homomorphism premise inside \<open>OF\<close> sends
  unification into higher-order search, as the corresponding step of \<open>eval_hom\<close> also avoids.\<close>
lemma poly_mult_hom:
  assumes p: "\<And>k. p k \<in> A" and q: "\<And>k. q k \<in> A"
  shows "(\<lambda>k. h (Ring.poly_mult A add mult z p q k))
       = Ring.poly_mult B badd bmult bz (\<lambda>k. h (p k)) (\<lambda>k. h (q k))"
proof (rule ext)
  fix k
  have cl: "(\<lambda>i. mult (p i) (q (k - i))) \<in> {..k} \<rightarrow> A"
  proof (rule Pi_I)
    fix i
    show "mult (p i) (q (k - i)) \<in> A"
      by (rule Monoid.composition_closed [OF monA p q])
  qed
  have fe: "(\<lambda>i. h (mult (p i) (q (k - i)))) = (\<lambda>i. bmult (h (p i)) (h (q (k - i))))"
    by (rule ext) (simp add: hmult p q)
  have "h (Ring.poly_mult A add mult z p q k)
        = h (commutative_monoid.fincomp A add z (\<lambda>i. mult (p i) (q (k - i))) {..k})"
    by (simp add: Ring.poly_mult_def [OF RA])
  also have "\<dots> = commutative_monoid.fincomp B badd bz (\<lambda>i. h (mult (p i) (q (k - i)))) {..k}"
    by (rule fincomp_hom [OF cmA cmB]) (auto simp: hB hz hadd cl)
  also have "\<dots> = commutative_monoid.fincomp B badd bz (\<lambda>i. bmult (h (p i)) (h (q (k - i)))) {..k}"
    by (simp add: fe)
  also have "\<dots> = Ring.poly_mult B badd bmult bz (\<lambda>k. h (p k)) (\<lambda>k. h (q k)) k"
    by (simp add: Ring.poly_mult_def [OF RB])
  finally show "h (Ring.poly_mult A add mult z p q k)
              = Ring.poly_mult B badd bmult bz (\<lambda>k. h (p k)) (\<lambda>k. h (q k)) k" .
qed

lemma poly_mult_coeff_closed:
  assumes p: "\<And>k. p k \<in> A" and q: "\<And>k. q k \<in> A"
  shows "Ring.poly_mult A add mult z p q k \<in> A"
proof -
  have "(\<lambda>i. mult (p i) (q (k - i))) \<in> {..k} \<rightarrow> A"
    by (rule Pi_I) (rule Monoid.composition_closed [OF monA p q])
  then show ?thesis
    by (simp add: Ring.poly_mult_def [OF RA] commutative_monoid.fincomp_closed [OF cmA])
qed

lemma poly_one_coeff_closed: "Ring.poly_one z u k \<in> A"
  using zA uA by (simp add: Ring.poly_one_def [OF RA])

text \<open>The linear factor \<open>X - a\<close>, the list product, and hence the property of splitting.  The
  stronger structure is taken as an ordinary assumption of each lemma, so that the ring-level facts
  above keep their generality.\<close>

lemma root_factor_coeff_closed:
  assumes CA: "commutative_ring A add mult z u" and a: "a \<in> A"
  shows "commutative_ring.root_factor A add z u a k \<in> A"
proof -
  interpret GA: Abelian_Group A add z by (rule gpA)
  have cn: "\<And>k. Ring.poly_const z a k \<in> A"
    using a by (rule poly_const_coeff_closed)
  have "Ring.poly_neg A add z (Ring.poly_const z a) k \<in> A"
    by (rule poly_neg_coeff_closed [OF cn])
  then show ?thesis
    unfolding commutative_ring.root_factor_def [OF CA] Ring.poly_add_def [OF RA]
    using var_coeff_closed by simp
qed

lemma root_factor_hom:
  assumes CA: "commutative_ring A add mult z u" and CB: "commutative_ring B badd bmult bz bu"
    and a: "a \<in> A"
  shows "(\<lambda>k. h (commutative_ring.root_factor A add z u a k))
       = commutative_ring.root_factor B badd bz bu (h a)"
proof -
  have cn: "\<And>k. Ring.poly_const z a k \<in> A"
    using a by (rule poly_const_coeff_closed)
  have "(\<lambda>k. h (commutative_ring.root_factor A add z u a k))
        = (\<lambda>k. h (Ring.poly_add add (Ring.var z u)
                     (Ring.poly_neg A add z (Ring.poly_const z a)) k))"
    by (simp add: commutative_ring.root_factor_def [OF CA])
  also have "\<dots> = Ring.poly_add badd (\<lambda>k. h (Ring.var z u k))
                    (\<lambda>k. h (Ring.poly_neg A add z (Ring.poly_const z a) k))"
    by (rule poly_add_hom) (auto simp: var_coeff_closed poly_neg_coeff_closed cn)
  also have "\<dots> = Ring.poly_add badd (Ring.var bz bu)
                    (Ring.poly_neg B badd bz (Ring.poly_const bz (h a)))"
    by (simp add: var_hom poly_neg_hom [OF cn] poly_const_hom)
  also have "\<dots> = commutative_ring.root_factor B badd bz bu (h a)"
    by (simp add: commutative_ring.root_factor_def [OF CB])
  finally show ?thesis .
qed

lemma poly_prod_coeff_closed:
  assumes FA: "Field A add mult z u"
    and fs: "\<And>f. f \<in> set fs \<Longrightarrow> (\<forall>k. f k \<in> A)"
  shows "Field.poly_prod A add mult z u fs k \<in> A"
  using fs
proof (induct fs arbitrary: k)
  case Nil
  show ?case
    using poly_one_coeff_closed by (simp add: Field.poly_prod_Nil [OF FA])
next
  case (Cons g gs)
  have g: "\<And>k. g k \<in> A" and gs: "\<And>f. f \<in> set gs \<Longrightarrow> (\<forall>k. f k \<in> A)"
    using Cons.prems by auto
  have pp: "\<And>k. Field.poly_prod A add mult z u gs k \<in> A"
    using Cons.hyps [OF gs] by blast
  show ?case
    by (simp add: Field.poly_prod_Cons [OF FA] poly_mult_coeff_closed [OF g pp])
qed

lemma poly_prod_hom:
  assumes FA: "Field A add mult z u" and FB: "Field B badd bmult bz bu"
    and fs: "\<And>f. f \<in> set fs \<Longrightarrow> (\<forall>k. f k \<in> A)"
  shows "(\<lambda>k. h (Field.poly_prod A add mult z u fs k))
       = Field.poly_prod B badd bmult bz bu (List.map (\<lambda>f k. h (f k)) fs)"
  using fs
proof (induct fs)
  case Nil
  show ?case
    by (simp add: Field.poly_prod_Nil [OF FA] Field.poly_prod_Nil [OF FB] poly_one_hom)
next
  case (Cons g gs)
  have g: "\<And>k. g k \<in> A" and gs: "\<And>f. f \<in> set gs \<Longrightarrow> (\<forall>k. f k \<in> A)"
    using Cons.prems by auto
  have pp: "\<And>k. Field.poly_prod A add mult z u gs k \<in> A"
    by (rule poly_prod_coeff_closed [OF FA]) (rule gs)
  have "(\<lambda>k. h (Field.poly_prod A add mult z u (g # gs) k))
        = (\<lambda>k. h (Ring.poly_mult A add mult z g (Field.poly_prod A add mult z u gs) k))"
    by (simp add: Field.poly_prod_Cons [OF FA])
  also have "\<dots> = Ring.poly_mult B badd bmult bz (\<lambda>k. h (g k))
                    (\<lambda>k. h (Field.poly_prod A add mult z u gs k))"
    by (rule poly_mult_hom [OF g pp])
  also have "\<dots> = Ring.poly_mult B badd bmult bz (\<lambda>k. h (g k))
                    (Field.poly_prod B badd bmult bz bu (List.map (\<lambda>f k. h (f k)) gs))"
    by (simp add: Cons.hyps [OF gs])
  also have "\<dots> = Field.poly_prod B badd bmult bz bu (List.map (\<lambda>f k. h (f k)) (g # gs))"
    by (simp add: Field.poly_prod_Cons [OF FB])
  finally show ?case .
qed

text \<open>Splitting is preserved: the witnessing constant and root list are simply carried across.
  The steps use \<open>simp only\<close> throughout, to keep @{thm [source] map_map} from rewriting the two lists
  into composed form and so out of reach of the transport equations.\<close>
theorem splits_hom:
  assumes FA: "Field A add mult z u" and FB: "Field B badd bmult bz bu"
    and sp: "Field.splits A add mult z u p"
  shows "Field.splits B badd bmult bz bu (\<lambda>k. h (p k))"
proof -
  have CA: "commutative_ring A add mult z u" using FA by (simp add: Field_def)
  have CB: "commutative_ring B badd bmult bz bu" using FB by (simp add: Field_def)
  from sp obtain c as where c: "c \<in> A" and as: "set as \<subseteq> A"
    and peq: "p = Ring.poly_mult A add mult z
                   (Ring.poly_const z c)
                   (Field.poly_prod A add mult z u
                      (List.map (commutative_ring.root_factor A add z u) as))"
    using Field.splits_def [OF FA] by blast
  define bs where "bs = List.map h as"
  have cn: "\<And>k. Ring.poly_const z c k \<in> A"
    using c by (rule poly_const_coeff_closed)
  have rf: "\<And>f. f \<in> set (List.map (commutative_ring.root_factor A add z u) as)
                 \<Longrightarrow> (\<forall>k. f k \<in> A)"
    using as by (auto simp: root_factor_coeff_closed [OF CA])
  have pp: "\<And>k. Field.poly_prod A add mult z u
                  (List.map (commutative_ring.root_factor A add z u) as) k \<in> A"
    by (rule poly_prod_coeff_closed [OF FA]) (rule rf)
  have mm: "List.map (\<lambda>f k. h (f k)) (List.map (commutative_ring.root_factor A add z u) as)
            = List.map (commutative_ring.root_factor B badd bz bu) bs"
    unfolding bs_def using as by (induct as) (simp_all add: root_factor_hom [OF CA CB])
  have step1: "(\<lambda>k. h (p k))
        = Ring.poly_mult B badd bmult bz (Ring.poly_const bz (h c))
            (Field.poly_prod B badd bmult bz bu
               (List.map (\<lambda>f k. h (f k))
                  (List.map (commutative_ring.root_factor A add z u) as)))"
  proof -
    have "(\<lambda>k. h (p k))
          = Ring.poly_mult B badd bmult bz (\<lambda>k. h (Ring.poly_const z c k))
              (\<lambda>k. h (Field.poly_prod A add mult z u
                        (List.map (commutative_ring.root_factor A add z u) as) k))"
      unfolding peq by (rule poly_mult_hom [OF cn pp])
    then show ?thesis
      by (simp only: poly_const_hom poly_prod_hom [OF FA FB rf])
  qed
  have "(\<lambda>k. h (p k))
        = Ring.poly_mult B badd bmult bz (Ring.poly_const bz (h c))
            (Field.poly_prod B badd bmult bz bu
               (List.map (commutative_ring.root_factor B badd bz bu) bs))"
    using step1 by (simp only: mm)
  moreover have "h c \<in> B" using c by (rule hB)
  moreover have "set bs \<subseteq> B" unfolding bs_def using as hB by auto
  ultimately show ?thesis
    using Field.splits_def [OF FB] by blast
qed

end

end
