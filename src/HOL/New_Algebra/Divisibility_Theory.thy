section \<open>Divisibility in commutative rings: units, associates, irreducibles, primes\<close>

theory Divisibility_Theory
  imports Ideal_Theory
begin

text \<open>Elementary multiplicative divisibility theory for a commutative ring, in the locale idiom of
  \<open>Ring_Theory\<close>. We work directly with ring elements rather than lifting the
  multiplicative monoid, which keeps the statements close to textbook divisibility.\<close>

context commutative_ring
begin

subsection \<open>Divisibility and units\<close>

text \<open>@{term "divides a b"}: \<open>a\<close> divides \<open>b\<close>, i.e.\ \<open>b = a \<cdot> c\<close> for some ring element \<open>c\<close>.\<close>
definition divides :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "divides a b \<equiv> (\<exists>c\<in>R. b = a \<cdot> c)"

lemma dividesI [intro]: "\<lbrakk> c \<in> R; b = a \<cdot> c \<rbrakk> \<Longrightarrow> divides a b"
  unfolding divides_def by blast

lemma dividesE [elim]:
  assumes "divides a b" obtains c where "c \<in> R" "b = a \<cdot> c"
  using assms unfolding divides_def by blast

lemma divides_refl [simp]: "a \<in> R \<Longrightarrow> divides a a"
  using Monoid.unit_closed multiplicative.Monoid_axioms by fastforce

lemma divides_trans [trans]:
  assumes "divides a b" "divides b c" and a: "a \<in> R"
  shows "divides a c"
  using a assms divides_def by auto

lemma divides_zero [simp]: "a \<in> R \<Longrightarrow> divides a \<zero>"
  by (rule dividesI[of \<zero>]) simp_all

lemma one_divides [simp]: "a \<in> R \<Longrightarrow> divides \<one> a"
  by (simp add: divides_def)

lemma divides_mult_right:
  assumes "b \<in> R" shows "divides a (a \<cdot> b)"
  using assms by blast

text \<open>A unit is an invertible element of the multiplicative monoid.\<close>
abbreviation is_unit :: "'a \<Rightarrow> bool"
  where "is_unit u \<equiv> multiplicative.invertible u"

lemma is_unitI [intro]: "\<lbrakk> u \<cdot> v = \<one>; v \<cdot> u = \<one>; v \<in> R \<rbrakk> \<Longrightarrow> is_unit u"
  by (rule multiplicative.invertibleI)

lemma unit_divides_one:
  assumes "is_unit u" shows "divides u \<one>"
  using assms by auto

lemma one_divides_unit_iff:
  assumes u: "u \<in> R" shows "divides u \<one> \<longleftrightarrow> is_unit u"
  using is_unitI multiplicative.commutative u by blast

lemma unit_divides_all:
  assumes "is_unit u" "u \<in> R" "a \<in> R" shows "divides u a"
  using assms divides_trans one_divides one_divides_unit_iff by meson


subsection \<open>Associated elements\<close>

text \<open>Two elements are associated if each divides the other.\<close>
definition associated :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "associated a b \<longleftrightarrow> divides a b \<and> divides b a"

lemma associatedI [intro]: "\<lbrakk> divides a b; divides b a \<rbrakk> \<Longrightarrow> associated a b"
  unfolding associated_def by blast

lemma associatedD1: "associated a b \<Longrightarrow> divides a b"
  unfolding associated_def by blast

lemma associatedD2: "associated a b \<Longrightarrow> divides b a"
  unfolding associated_def by blast

lemma associated_refl [simp]: "a \<in> R \<Longrightarrow> associated a a"
  by (simp add: associated_def)

lemma associated_sym: "associated a b \<Longrightarrow> associated b a"
  unfolding associated_def by blast

lemma associated_trans [trans]:
  assumes "associated a b" "associated b c" "a \<in> R" "b \<in> R" "c \<in> R"
  shows "associated a c"
  using assms unfolding associated_def by (meson divides_trans)


subsection \<open>Greatest common divisors and least common multiples\<close>

text \<open>@{term "is_gcd d a b"}: \<open>d\<close> is a common divisor of \<open>a\<close> and \<open>b\<close> that every common divisor
  divides.  Gcds need not exist in a general ring, but when they do they are unique up to
  association; existence is established in a principal ideal domain (Bezout) below.\<close>
definition is_gcd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_gcd d a b \<longleftrightarrow>
    d \<in> R \<and> divides d a \<and> divides d b \<and> (\<forall>c\<in>R. divides c a \<and> divides c b \<longrightarrow> divides c d)"

text \<open>@{term "is_lcm m a b"}: \<open>m\<close> is a common multiple of \<open>a\<close> and \<open>b\<close> dividing every common
  multiple.\<close>
definition is_lcm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_lcm m a b \<longleftrightarrow>
    m \<in> R \<and> divides a m \<and> divides b m \<and> (\<forall>c\<in>R. divides a c \<and> divides b c \<longrightarrow> divides m c)"

lemma is_gcdI:
  "\<lbrakk> d \<in> R; divides d a; divides d b;
     \<And>c. \<lbrakk> c \<in> R; divides c a; divides c b \<rbrakk> \<Longrightarrow> divides c d \<rbrakk> \<Longrightarrow> is_gcd d a b"
  unfolding is_gcd_def by blast

lemma is_gcdD:
  assumes "is_gcd d a b"
  shows "d \<in> R" "divides d a" "divides d b"
    and "\<And>c. \<lbrakk> c \<in> R; divides c a; divides c b \<rbrakk> \<Longrightarrow> divides c d"
  using assms unfolding is_gcd_def by blast+

lemma is_gcd_sym: "is_gcd d a b \<Longrightarrow> is_gcd d b a"
  unfolding is_gcd_def by blast

lemma is_lcm_sym: "is_lcm m a b \<Longrightarrow> is_lcm m b a"
  unfolding is_lcm_def by blast

text \<open>Any two gcds of the same pair are associated.\<close>
lemma is_gcd_unique:
  assumes "is_gcd d a b" and "is_gcd d' a b"
  shows "associated d d'"
  using assms associated_def is_gcd_def by force

text \<open>Dually, any two lcms are associated.\<close>
lemma is_lcm_unique:
  assumes "is_lcm m a b" and "is_lcm m' a b"
  shows "associated m m'"
  using assms associated_def is_lcm_def by force

end


subsection \<open>Irreducible and prime elements\<close>

context commutative_ring
begin

text \<open>An irreducible element is a nonzero non-unit whose only factorisations are trivial.\<close>
definition irreducible_elem :: "'a \<Rightarrow> bool"
  where "irreducible_elem p \<longleftrightarrow>
    p \<in> R \<and> p \<noteq> \<zero> \<and> \<not> is_unit p \<and>
    (\<forall>a\<in>R. \<forall>b\<in>R. p = a \<cdot> b \<longrightarrow> is_unit a \<or> is_unit b)"

lemma irreducible_elemI:
  assumes "p \<in> R" "p \<noteq> \<zero>" "\<not> is_unit p"
    and "\<And>a b. \<lbrakk> a \<in> R; b \<in> R; p = a \<cdot> b \<rbrakk> \<Longrightarrow> is_unit a \<or> is_unit b"
  shows "irreducible_elem p"
  using assms unfolding irreducible_elem_def by blast

lemma irreducible_elemD:
  assumes "irreducible_elem p"
  shows "p \<in> R" "p \<noteq> \<zero>" "\<not> is_unit p"
    and "\<And>a b. \<lbrakk> a \<in> R; b \<in> R; p = a \<cdot> b \<rbrakk> \<Longrightarrow> is_unit a \<or> is_unit b"
  using assms unfolding irreducible_elem_def by blast+

text \<open>A prime element is a nonzero non-unit that, when dividing a product, divides a factor.\<close>
definition prime_elem :: "'a \<Rightarrow> bool"
  where "prime_elem p \<longleftrightarrow>
    p \<in> R \<and> p \<noteq> \<zero> \<and> \<not> is_unit p \<and>
    (\<forall>a\<in>R. \<forall>b\<in>R. divides p (a \<cdot> b) \<longrightarrow> divides p a \<or> divides p b)"

lemma prime_elemI:
  assumes "p \<in> R" "p \<noteq> \<zero>" "\<not> is_unit p"
    and "\<And>a b. \<lbrakk> a \<in> R; b \<in> R; divides p (a \<cdot> b) \<rbrakk> \<Longrightarrow> divides p a \<or> divides p b"
  shows "prime_elem p"
  using assms unfolding prime_elem_def by blast

lemma prime_elemD:
  assumes "prime_elem p"
  shows "p \<in> R" "p \<noteq> \<zero>" "\<not> is_unit p"
    and "\<And>a b. \<lbrakk> a \<in> R; b \<in> R; divides p (a \<cdot> b) \<rbrakk> \<Longrightarrow> divides p a \<or> divides p b"
  using assms unfolding prime_elem_def by blast+

end


subsection \<open>In an integral domain, prime elements are irreducible\<close>

context integral_domain
begin

text \<open>Cancellation of a nonzero factor: the defining property that separates domains from general
  commutative rings.  From \<open>c \<cdot> a = c \<cdot> b\<close> with \<open>c \<noteq> \<zero>\<close> we get \<open>c \<cdot> (a - b) = \<zero>\<close>, and absence of
  zero divisors forces \<open>a - b = \<zero>\<close>.\<close>
lemma mult_cancel_left:
  assumes c: "c \<in> R" and a: "a \<in> R" and b: "b \<in> R" and cnz: "c \<noteq> \<zero>" and eq: "c \<cdot> a = c \<cdot> b"
  shows "a = b"
proof -
  have "c \<cdot> (a - b) = c \<cdot> a + c \<cdot> (- b)" using c a b by (simp add: distributive)
  then have "c \<cdot> (a - b) = \<zero>"
    by (simp add: b c eq local.right_minus) 
  then have "c = \<zero> \<or> a - b = \<zero>" 
    using c no_zero_divisors by (simp add: a b)
  then have z: "a - b = \<zero>" using cnz by blast
  then show ?thesis
    using a additive.commutative additive.inverse_equality b by fastforce
qed

text \<open>The classical characterization of association in a domain: \<open>a\<close> and \<open>b\<close> are associated iff
  they differ by a unit factor, \<open>b = u \<cdot> a\<close>.  (The right-to-left direction holds in any commutative
  ring; the forward direction is where cancellation --- hence the domain hypothesis --- is used.)\<close>
lemma associated_iff_unit_multiple:
  assumes a: "a \<in> R" and b: "b \<in> R"
  shows "associated a b \<longleftrightarrow> (\<exists>u. is_unit u \<and> u \<in> R \<and> b = u \<cdot> a)"
proof
  assume "associated a b"
  then have ab: "divides a b" and ba: "divides b a"
    by (auto dest: associatedD1 associatedD2)
  obtain s where s: "s \<in> R" "b = a \<cdot> s" using ab by blast
  obtain t where t: "t \<in> R" "a = b \<cdot> t" using ba by blast
  show "\<exists>u. is_unit u \<and> u \<in> R \<and> b = u \<cdot> a"
  proof (cases "a = \<zero>")
    case True
    then show ?thesis using s a by force
  next
    case False
    have eq1: "a \<cdot> \<one> = a \<cdot> (s \<cdot> t)"
      using multiplicative.associative a s t by force
    have stR: "s \<cdot> t \<in> R" using s t by simp
    have one_st: "\<one> = s \<cdot> t"
      by (rule mult_cancel_left[OF a multiplicative.unit_closed stR False eq1])
    then show ?thesis using s(1)
      using a is_unitI multiplicative.commutative s(2) t(1) by blast
  qed
next
  assume "\<exists>u. is_unit u \<and> u \<in> R \<and> b = u \<cdot> a"
  then obtain u where u: "is_unit u" "u \<in> R" and beq: "b = u \<cdot> a" and iuR: "multiplicative.inverse u \<in> R" 
    by blast
  show "associated a b"
  proof (rule associatedI)
    \<comment> \<open>\<open>divides a b\<close> since \<open>b = u \<cdot> a = a \<cdot> u\<close>.\<close>
    show "divides a b"
      using a beq multiplicative.commutative u(2) by blast
        \<comment> \<open>\<open>divides b a\<close> since \<open>a = u\<inverse> \<cdot> b\<close>.\<close>
    show "divides b a"
      unfolding divides_def
      using a b beq iuR multiplicative.commutative multiplicative.invertible_left_inverse2 u
      by metis
  qed
qed

lemma prime_imp_irreducible:
  assumes p: "prime_elem p"
  shows "irreducible_elem p"
proof (rule irreducible_elemI)
  show pR: "p \<in> R" and pnz: "p \<noteq> \<zero>" and pnu: "\<not> is_unit p"
    using p by (auto dest: prime_elemD)
  fix a b assume a: "a \<in> R" and b: "b \<in> R" and eq: "p = a \<cdot> b"
  \<comment> \<open>\<open>p\<close> divides \<open>a \<cdot> b\<close>, so it divides one factor; say \<open>p\<close> divides \<open>a\<close>, giving \<open>a = p \<cdot> d\<close>.\<close>
  then have "divides p a \<or> divides p b" using a b p by (auto simp: prime_elem_def)
  then show "is_unit a \<or> is_unit b"
  proof
    assume "divides p a"
    then obtain d where d: "d \<in> R" "a = p \<cdot> d" by blast
    have "p \<cdot> \<one> = p \<cdot> (d \<cdot> b)"
      using eq d a b pR by (simp add: multiplicative.associative)
    then have db: "d \<cdot> b = \<one>" using mult_cancel_left[OF pR _ _ pnz] d b pR by simp
    then show ?thesis
      using b d(1) is_unitI multiplicative.commutative by blast
  next
    assume "divides p b"
    then obtain d where d: "d \<in> R" "b = p \<cdot> d" by blast
    then have "p \<cdot> \<one> = p \<cdot> (d \<cdot> a)"
      using a eq multiplicative.commutative multiplicative.left_commutative pR by force 
    then have da: "d \<cdot> a = \<one>" using mult_cancel_left[OF pR _ _ pnz] d a pR by simp
    then show ?thesis
      using a d(1) is_unitI multiplicative.commutative by blast 
  qed
qed

end


subsection \<open>Divisibility via principal ideals\<close>

text \<open>Divisibility is containment of principal ideals the other way round: \<open>a\<close> divides \<open>b\<close> iff
  \<open>(b) \<subseteq> (a)\<close> iff \<open>b \<in> (a)\<close>.  This is the bridge that turns the ideal-theoretic PID argument into
  statements about ring elements.\<close>

context commutative_ring
begin

lemma divides_iff_mem_principal:
  assumes a: "a \<in> R" and b: "b \<in> R"
  shows "divides a b \<longleftrightarrow> b \<in> principal_ideal a"
  using a divides_def multiplicative.commutative principal_ideal_def by auto

lemma divides_iff_principal_subset:
  assumes a: "a \<in> R" and b: "b \<in> R"
  shows "divides a b \<longleftrightarrow> principal_ideal b \<subseteq> principal_ideal a"
proof
  assume dvd: "divides a b"
  show "principal_ideal b \<subseteq> principal_ideal a"
  proof
    fix x assume "x \<in> principal_ideal b"
    then obtain r c where "r \<in> R" "x = r \<cdot> b" and "c \<in> R" "b = a \<cdot> c"
      unfolding principal_ideal_def using dvd by blast
    then show "x \<in> principal_ideal a" using principal_ideal_memI[of "r \<cdot> c" a]
      using a multiplicative.associative multiplicative.commutative by auto
  qed
next
  assume "principal_ideal b \<subseteq> principal_ideal a"
  moreover have "b \<in> principal_ideal b" using b by (simp add: principal_ideal_contains)
  ultimately have "b \<in> principal_ideal a" by blast
  then show "divides a b" using divides_iff_mem_principal[OF a b] by simp
qed

text \<open>Associated elements generate the same principal ideal.\<close>
lemma associated_iff_same_principal:
  assumes a: "a \<in> R" and b: "b \<in> R"
  shows "associated a b \<longleftrightarrow> principal_ideal a = principal_ideal b"
  unfolding associated_def
  using divides_iff_principal_subset[OF a b] divides_iff_principal_subset[OF b a] by blast

text \<open>An ideal containing @{term \<one>} is the whole ring.\<close>
lemma ideal_contains_one_eq_whole:
  assumes I: "Ideal I R (+) (\<cdot>) \<zero> \<one>" and one: "\<one> \<in> I"
  shows "I = R"
proof -
  interpret I: Ideal I R "(+)" "(\<cdot>)" \<zero> \<one> by (rule I)
  show ?thesis using one I.additive.subset
    by (metis I.Ideal(1) multiplicative.right_unit subsetI subset_antisym)
qed

text \<open>A principal ideal is the whole ring exactly when its generator is a unit.\<close>
lemma principal_ideal_eq_whole_iff_unit:
  assumes a: "a \<in> R"
  shows "principal_ideal a = R \<longleftrightarrow> is_unit a"
proof
  assume "principal_ideal a = R"
  then have "\<one> \<in> principal_ideal a" by simp
  then obtain r where r: "r \<in> R" "r \<cdot> a = \<one>" "a \<cdot> r = \<one>" 
    unfolding principal_ideal_def
    using assms multiplicative.commutative by auto
  then show "is_unit a"
    using is_unitI by blast
next
  assume u: "is_unit a"
  have "\<one> \<in> principal_ideal a"
    using multiplicative.invertibleE principal_ideal_memI u by metis
  then show "principal_ideal a = R"
    using assms ideal_proper_iff_one_notin principal_ideal_is_ideal by blast
qed

end


subsection \<open>Noetherian rings\<close>

text \<open>A (two-sided) noetherian ring is one in which every ascending chain of ideals
  eventually stabilises.  This is the ascending-chain formulation of noetherianity, and is the
  form used by the factorisation arguments below.\<close>
locale Noetherian_Ring = Ring +
  assumes ideal_chain_stabilises:
    "\<lbrakk> \<And>n. Ideal (A n) R (+) (\<cdot>) \<zero> \<one>; \<And>n. A n \<subseteq> A (Suc n) \<rbrakk> \<Longrightarrow>
     \<exists>N. \<forall>n. N \<le> n \<longrightarrow> A n = A N"

text \<open>A noetherian domain is both noetherian and an integral domain.\<close>
locale Noetherian_Domain = Noetherian_Ring + integral_domain

subsection \<open>Principal ideal domains\<close>

text \<open>A principal ideal domain (PID) is an integral domain in which every ideal is principal.\<close>
locale principal_ideal_domain = integral_domain +
  assumes principal: "Ideal I R (+) (\<cdot>) \<zero> \<one> \<Longrightarrow> \<exists>a\<in>R. I = principal_ideal a"

context principal_ideal_domain
begin

text \<open>In a PID an irreducible element generates a maximal ideal.  We use the maximality criterion of
  @{locale Ideal}: any ideal \<open>J\<close> containing \<open>(p)\<close> is principal, \<open>J = (q)\<close>, so \<open>q\<close> divides \<open>p\<close>; by
  irreducibility one factor is a unit, giving \<open>J = (p)\<close> or \<open>J = R\<close>.\<close>
theorem irreducible_imp_maximal_ideal:
  assumes p: "irreducible_elem p"
  shows "Ideal.maximal_ideal (principal_ideal p) R (+) (\<cdot>) \<zero> \<one>"
proof -
  have pR: "p \<in> R" and pnu: "\<not> is_unit p" using p by (auto dest: irreducible_elemD)
  interpret P: Ideal "principal_ideal p" R "(+)" "(\<cdot>)" \<zero> \<one>
    by (rule principal_ideal_is_ideal[OF pR])
  show ?thesis
    unfolding P.maximal_ideal_def
  proof (intro conjI allI impI)
    show "principal_ideal p \<noteq> R" using principal_ideal_eq_whole_iff_unit[OF pR] pnu by blast
  next
    fix J assume J: "Ideal J R (+) (\<cdot>) \<zero> \<one>" and sub: "principal_ideal p \<subseteq> J"
    obtain q where q: "q \<in> R" "J = principal_ideal q" using principal[OF J] by blast
    \<comment> \<open>\<open>(p) \<subseteq> (q)\<close> means \<open>q\<close> divides \<open>p\<close>, so \<open>p = q \<cdot> r\<close>.\<close>
    have "principal_ideal p \<subseteq> principal_ideal q" using sub q by simp
    then have "divides q p" using divides_iff_principal_subset[OF q(1) pR] by simp
    then obtain r where r: "r \<in> R" "p = q \<cdot> r" by blast
    have "is_unit q \<or> is_unit r" using p q(1) r by (auto dest: irreducible_elemD)
    then show "J = principal_ideal p \<or> J = R"
    proof
      assume "is_unit q"
      then show ?thesis using principal_ideal_eq_whole_iff_unit q by blast
    next
      assume ur: "is_unit r"
      have "p \<cdot> multiplicative.inverse r = q"
        by (simp add: multiplicative.associative q(1) r ur)
      then have "divides p q"
        using r(1) ur by auto 
      then show ?thesis using q(2)
        using divides_iff_principal_subset pR q(1) sub by blast 
    qed
  qed
qed

text \<open>Hence in a PID every irreducible element is prime (the converse of
  @{thm integral_domain.prime_imp_irreducible}).\<close>
theorem irreducible_imp_prime:
  assumes p: "irreducible_elem p"
  shows "prime_elem p"
proof -
  have pR: "p \<in> R" and pnz: "p \<noteq> \<zero>" and pnu: "\<not> is_unit p"
    using p by (auto dest: irreducible_elemD)
  interpret P: ideal_in_comm_ring "principal_ideal p" R "(+)" "(\<cdot>)" \<zero> \<one>
    by (intro ideal_in_comm_ring.intro principal_ideal_is_ideal[OF pR] commutative_ring_axioms)
  have prime: "P.prime_ideal"
    using P.maximal_imp_prime_ideal irreducible_imp_maximal_ideal p by blast
  show ?thesis
    using P.prime_ideal_def divides_iff_mem_principal pR pnu pnz prime prime_elemI by auto
qed


subsubsection \<open>The ascending chain condition on principal ideals\<close>

text \<open>The union of a countable ascending chain of ideals is an ideal.\<close>
lemma Union_chain_ideal:
  assumes I: "\<And>n. Ideal (A n) R (+) (\<cdot>) \<zero> \<one>"
    and mono: "\<And>n. A n \<subseteq> A (Suc n)"
  shows "Ideal (\<Union>n. A n) R (+) (\<cdot>) \<zero> \<one>"
proof -
  have mono_le: "A m \<subseteq> A n" if "m \<le> n" for m n
    using that by (induct n) (simp_all add: lift_Suc_mono_le mono)
  have dir: "\<And>x y. x \<in> (\<Union>n. A n) \<Longrightarrow> y \<in> (\<Union>n. A n) \<Longrightarrow> \<exists>k. x \<in> A k \<and> y \<in> A k"
    using mono mono_le by (metis UN_E not_less_eq_eq subset_eq)
  interpret A0: Ideal "A 0" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule I)
  have sub: "Subgroup (\<Union>n. A n) R (+) \<zero>"
  proof (rule additive.subgroupI)
    show "(\<Union>n. A n) \<subseteq> R"
    proof
      fix x assume "x \<in> (\<Union>n. A n)"
      then obtain n where "x \<in> A n" by blast
      interpret An: Ideal "A n" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule I)
      show "x \<in> R" using \<open>x \<in> A n\<close> An.additive.subset by blast
    qed
  next
    show "\<zero> \<in> (\<Union>n. A n)" using A0.additive.sub_unit_closed by blast
  next
    fix g h assume "g \<in> (\<Union>n. A n)" "h \<in> (\<Union>n. A n)"
    then obtain k where gh: "g \<in> A k" "h \<in> A k" using dir by blast
    interpret Ak: Ideal "A k" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule I)
    show "g + h \<in> (\<Union>n. A n)" using gh Ak.additive.sub_composition_closed by blast
  next
    fix g assume "g \<in> (\<Union>n. A n)"
    then obtain n where "g \<in> A n" by blast
    interpret An: Ideal "A n" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule I)
    show "additive.invertible g" using \<open>g \<in> A n\<close> An.additive.subset by auto
    show "additive.inverse g \<in> (\<Union>n. A n)"
      using \<open>g \<in> A n\<close> An.additive.submonoid_inverse_closed An.additive.sub.invertible by blast
  qed
  interpret U: Subgroup "\<Union>n. A n" R "(+)" \<zero> by (rule sub)
  show ?thesis
  proof 
    fix a x assume a: "a \<in> R" and x: "x \<in> (\<Union>n. A n)"
    obtain n where "x \<in> A n" using x by blast
    interpret An: Ideal "A n" R "(+)" "(\<cdot>)" \<zero> \<one> by (rule I)
    show "a \<cdot> x \<in> (\<Union>n. A n)" "x \<cdot> a \<in> (\<Union>n. A n)" 
      using a \<open>x \<in> A n\<close> An.Ideal by blast+
  qed
qed

text \<open>\<^emph>\<open>Ascending chain condition\<close>: every ascending chain of (principal) ideals in a PID
  stabilises.  Proof: the union is an ideal, hence principal \<open>= (c)\<close>; the generator \<open>c\<close> lies in
  some \<open>A N\<close>, and from there on the chain cannot grow beyond \<open>A N\<close>.\<close>
theorem ascending_chain_stabilises:
  assumes I: "\<And>n. Ideal (A n) R (+) (\<cdot>) \<zero> \<one>"
    and mono: "\<And>n. A n \<subseteq> A (Suc n)"
  obtains N where "\<And>n. N \<le> n \<Longrightarrow> A n = A N"
proof -
  have mono_le: "A m \<subseteq> A n" if "m \<le> n" for m n
    using that
    by (induct n) (simp_all add: lift_Suc_mono_le mono)
  have Uideal: "Ideal (\<Union>n. A n) R (+) (\<cdot>) \<zero> \<one>"
    using I mono by (rule Union_chain_ideal)
  obtain c where c: "c \<in> R" and Uc: "(\<Union>n. A n) = principal_ideal c"
    using principal[OF Union_chain_ideal] I mono by metis
  then obtain N where cN: "c \<in> A N"
    using Uc c principal_ideal_contains by auto
  have "A n = A N" if "N \<le> n" for n
  proof
    show "A N \<subseteq> A n" using mono_le that .
    show "A n \<subseteq> A N"
    proof
      fix x assume "x \<in> A n"
      then have "x \<in> principal_ideal c" using Uc by blast
      then obtain r where r: "r \<in> R" "x = r \<cdot> c" unfolding principal_ideal_def by blast
      interpret AN: Ideal "A N" R "(+)" "(\<cdot>)" \<zero> \<one> 
        by (rule I)
      show "x \<in> A N" using r cN AN.Ideal(1) by blast 
    qed
  qed
  then show ?thesis using that by blast
qed


subsubsection \<open>Bezout: existence of greatest common divisors\<close>

text \<open>The ideal generated by two elements, \<open>(a, b) = {x \<cdot> a + y \<cdot> b}\<close>.\<close>
definition bezout_ideal :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "bezout_ideal a b \<equiv> {x \<cdot> a + y \<cdot> b | x y. x \<in> R \<and> y \<in> R}"

lemma bezout_ideal_memI:
  "\<lbrakk> x \<in> R; y \<in> R \<rbrakk> \<Longrightarrow> x \<cdot> a + y \<cdot> b \<in> bezout_ideal a b"
  unfolding bezout_ideal_def by blast

lemma bezout_ideal_is_ideal:
  assumes a: "a \<in> R" and b: "b \<in> R"
  shows "Ideal (bezout_ideal a b) R (+) (\<cdot>) \<zero> \<one>"
proof -
  have sg: "Subgroup (bezout_ideal a b) R (+) \<zero>"
  proof (rule additive.subgroupI)
    show "bezout_ideal a b \<subseteq> R"
      using a b principal_ideal_domain.bezout_ideal_def principal_ideal_domain_axioms by fastforce
    show "\<zero> \<in> bezout_ideal a b" using a b
      using additive.left_unit additive.unit_closed bezout_ideal_memI left_zero by metis
  next
    fix g h assume "g \<in> bezout_ideal a b" "h \<in> bezout_ideal a b"
    then obtain x1 y1 x2 y2 where
      g: "x1 \<in> R" "y1 \<in> R" "g = x1 \<cdot> a + y1 \<cdot> b" and h: "x2 \<in> R" "y2 \<in> R" "h = x2 \<cdot> a + y2 \<cdot> b" 
      unfolding bezout_ideal_def by blast
    have "g + h = (x1 + x2) \<cdot> a + (y1 + y2) \<cdot> b"
      by (simp add: a additive.commutative additive.left_commutative b distributive(2) g h)
    then show "g + h \<in> bezout_ideal a b" 
      using g h bezout_ideal_memI[of "x1+x2" "y1+y2" a b] by simp
  next
    fix g assume "g \<in> bezout_ideal a b"
    then obtain x y where xy: "x \<in> R" "y \<in> R" "g = x \<cdot> a + y \<cdot> b" 
      unfolding bezout_ideal_def by blast
    show "additive.invertible g" 
      using xy a b by simp
    show "additive.inverse g \<in> bezout_ideal a b" 
      using xy a b bezout_ideal_memI[of "- x" "- y" a b] 
      by (simp add: left_minus additive.inverse_composition_commute additive.commutative)
  qed
  interpret S: Subgroup "bezout_ideal a b" R "(+)" \<zero> by (rule sg)
  show ?thesis
  proof 
    fix r z assume r: "r \<in> R" and "z \<in> bezout_ideal a b"
    then obtain x y where z: "x \<in> R" "y \<in> R" "z = x \<cdot> a + y \<cdot> b"
      unfolding bezout_ideal_def by blast
    have "r \<cdot> z = (r \<cdot> x) \<cdot> a + (r \<cdot> y) \<cdot> b"
      using r z a b by (simp add: distributive multiplicative.associative)
    then show "r \<cdot> z \<in> bezout_ideal a b"
      using r z bezout_ideal_memI[of "r \<cdot> x" "r \<cdot> y" a b] by simp
    then show "z \<cdot> r \<in> bezout_ideal a b" 
      using r z a b by (simp add: multiplicative.commutative)
  qed
qed

text \<open>@{term a} and @{term b} both lie in \<open>(a, b)\<close>.\<close>
lemma a_in_bezout_ideal: "\<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> a \<in> bezout_ideal a b"
  using bezout_ideal_memI[of \<one> \<zero> a b] by simp

lemma b_in_bezout_ideal: "\<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> b \<in> bezout_ideal a b"
  using bezout_ideal_memI[of \<zero> \<one> a b] by simp

text \<open>\<^emph>\<open>Bezout's theorem.\<close>  The gcd generates the ideal \<open>(a, b)\<close>: divisibility of \<open>a\<close> and \<open>b\<close> 
  is membership, and any common divisor divides every element of \<open>(a, b)\<close>, in particular \<open>d\<close>.\<close>
theorem bezout:
  assumes a: "a \<in> R" and b: "b \<in> R"
  obtains d x y where "is_gcd d a b" "x \<in> R" "y \<in> R" "d = x \<cdot> a + y \<cdot> b"
proof -
  have I: "Ideal (bezout_ideal a b) R (+) (\<cdot>) \<zero> \<one>" by (rule bezout_ideal_is_ideal[OF a b])
  obtain d where d: "d \<in> R" and gen: "bezout_ideal a b = principal_ideal d"
    using principal[OF I] by blast
  have "d \<in> bezout_ideal a b" using gen d by (simp add: principal_ideal_contains)
  then obtain x y where xy: "x \<in> R" "y \<in> R" "d = x \<cdot> a + y \<cdot> b"
    unfolding bezout_ideal_def by blast
  obtain dda: "divides d a" and ddb: "divides d b"
    using a_in_bezout_ideal b_in_bezout_ideal gen divides_iff_mem_principal[OF d] a b by metis
  \<comment> \<open>Any common divisor \<open>c\<close> divides \<open>d = x \<cdot> a + y \<cdot> b\<close>.\<close>
  have "is_gcd d a b"
  proof (rule is_gcdI[OF d dda ddb])
    fix c assume c: "c \<in> R" and ca: "divides c a" and cb: "divides c b"
    obtain s t where s: "s \<in> R" "a = c \<cdot> s" and t: "t \<in> R" "b = c \<cdot> t" using ca cb by blast
    then have "d = c \<cdot> (x \<cdot> s + y \<cdot> t)"
      by (simp add: c distributive(1) multiplicative.left_commutative xy)
    moreover have "x \<cdot> s + y \<cdot> t \<in> R" using xy s t by simp
    ultimately show "divides c d" by (blast intro: dividesI)
  qed
  then show ?thesis using xy that by blast
qed

text \<open>Consequently a greatest common divisor exists for every pair.\<close>
corollary gcd_exists:
  assumes "a \<in> R" "b \<in> R" shows "\<exists>d. is_gcd d a b"
  using bezout[OF assms] by blast


end


text \<open>Principal ideal domains satisfy the noetherian ascending-chain condition.\<close>
sublocale principal_ideal_domain \<subseteq> Noetherian_Domain
proof unfold_locales
  fix A
  assume I: "\<And>n. Ideal (A n) R (+) (\<cdot>) \<zero> \<one>"
    and mono: "\<And>n. A n \<subseteq> A (Suc n)"
  show "\<exists>N. \<forall>n. N \<le> n \<longrightarrow> A n = A N"
    using I ascending_chain_stabilises mono by meson
qed


subsection \<open>Euclidean domains\<close>

text \<open>A Euclidean domain is an integral domain equipped with a degree function \<open>\<phi>\<close> into the naturals
  admitting division with remainder: for \<open>a, b\<close> nonzero there are \<open>q, r\<close> with \<open>a = b \<cdot> q + r\<close> and
  either \<open>r = \<zero>\<close> or \<open>\<phi> r < \<phi> b\<close>.\<close>
locale Euclidean_Domain = integral_domain +
  fixes \<phi> :: "'a \<Rightarrow> nat"
  assumes euclidean_division:
    "\<lbrakk> a \<in> R; b \<in> R; a \<noteq> \<zero>; b \<noteq> \<zero> \<rbrakk> \<Longrightarrow>
       \<exists>q\<in>R. \<exists>r\<in>R. a = b \<cdot> q + r \<and> (r = \<zero> \<or> \<phi> r < \<phi> b)"
begin

text \<open>Every Euclidean domain is a principal ideal domain: an ideal is generated by any nonzero
  element of least \<open>\<phi>\<close>-value, since division with remainder against it lands back in the ideal and
  minimality forces a zero remainder.\<close>
sublocale principal_ideal_domain
proof unfold_locales
  fix I assume I: "Ideal I R (+) (\<cdot>) \<zero> \<one>"
  interpret I: Ideal I R "(+)" "(\<cdot>)" \<zero> \<one> by (rule I)
  show "\<exists>a\<in>R. I = principal_ideal a"
  proof (cases "I = {\<zero>}")
    case True
    have "principal_ideal \<zero> = {\<zero>}"
      using principal_ideal_memI[of \<zero> \<zero>] by (force simp: principal_ideal_def)
    then show ?thesis using True by auto
  next
    case False
    \<comment> \<open>Choose \<open>a\<close> in the nonzero part of \<open>I\<close> minimising \<open>\<phi>\<close>.\<close>
    define Inz where "Inz \<equiv> {x \<in> I. x \<noteq> \<zero>}"
    have ne: "Inz \<noteq> {}" using False I.additive.sub_unit_closed Inz_def by blast
    define \<phi>img where "\<phi>img \<equiv> \<phi> ` Inz"
    have "\<phi>img \<noteq> {}" using ne \<phi>img_def by simp
    then obtain a where a: "a \<in> Inz" and amin: "\<And>b. b \<in> Inz \<Longrightarrow> \<phi> a \<le> \<phi> b"
      using exists_least_iff[of "\<lambda>n. n \<in> \<phi>img"] unfolding \<phi>img_def image_def mem_Collect_eq
      by (metis ne all_not_in_conv linorder_not_le)
    have aI: "a \<in> I" using a Inz_def by blast
    have aR: "a \<in> R" using aI I.additive.subset by blast
    have anz: "a \<noteq> \<zero>" using a Inz_def by blast
    have "I = principal_ideal a"
    proof
      \<comment> \<open>\<open>(a) \<subseteq> I\<close> since \<open>a \<in> I\<close> and \<open>I\<close> absorbs products.\<close>
      show "principal_ideal a \<subseteq> I"
        using I.Ideal(1) aI principal_ideal_def by auto
    next
      \<comment> \<open>\<open>I \<subseteq> (a)\<close> by Euclidean division against \<open>a\<close>.\<close>
      show "I \<subseteq> principal_ideal a"
      proof
        fix b assume bI: "b \<in> I"
        have bR: "b \<in> R" using bI I.additive.subset by blast
        show "b \<in> principal_ideal a"
        proof (cases "b = \<zero>")
          case True then show ?thesis using principal_ideal_memI[of \<zero> a] aR by simp
        next
          case bnz: False
          obtain q r where q: "q \<in> R" and rR: "r \<in> R" and beq: "b = a \<cdot> q + r"
            and rem: "r = \<zero> \<or> \<phi> r < \<phi> a"
            using euclidean_division[OF bR aR bnz anz] by blast
          have aqI: "a \<cdot> q \<in> I" using I.Ideal(2)[OF q aI] .
          then have req: "r = b - a \<cdot> q"
            using I.additive.sub additive.commutative additive.commute_iff_inverse beq rR by metis
          have "- (a \<cdot> q) \<in> I" using aqI by simp
          then have "b + (- (a \<cdot> q)) \<in> I"
            using bI I.additive.sub_composition_closed by blast
          then have rI: "r \<in> I" using req by simp
          \<comment> \<open>Minimality of \<open>\<phi> a\<close> rules out \<open>\<phi> r < \<phi> a\<close>, so \<open>r = \<zero>\<close> and \<open>a\<close> divides \<open>b\<close>.\<close>
          have "r = \<zero>"
            using rI rem Inz_def amin linorder_not_less by blast
          then show ?thesis using q principal_ideal_memI[of q a]
            using aR beq multiplicative.commutative by auto
        qed
      qed
    qed
    then show ?thesis using aR by blast
  qed
qed

end

text \<open>A field is a Euclidean domain with the constant degree function (division with remainder is
  exact: \<open>a = b \<cdot> (b\<inverse> \<cdot> a) + \<zero>\<close>).\<close>
sublocale Field \<subseteq> Euclidean_Domain R "(+)" "(\<cdot>)" \<zero> \<one> "\<lambda>_. 0"
proof 
  fix a b assume a: "a \<in> R" and b: "b \<in> R" and bnz: "b \<noteq> \<zero>"
  have "a = b \<cdot> (multiplicative.inverse b \<cdot> a) + \<zero>"
    by (simp add: a b bnz field_inverse multiplicative.invertible_right_inverse2)
  then show "\<exists>q\<in>R. \<exists>r\<in>R. a = b \<cdot> q + r \<and> (r = \<zero> \<or> (0::nat) < 0)"
    using a b bnz field_inverse by auto
qed


subsection \<open>Factorizations into irreducibles\<close>

text \<open>The product of a list of ring elements.\<close>
context commutative_ring
begin

definition list_prod :: "'a list \<Rightarrow> 'a"
  where "list_prod xs = foldr (\<cdot>) xs \<one>"

lemma list_prod_Nil [simp]: "list_prod [] = \<one>"
  by (simp add: list_prod_def)

lemma list_prod_Cons [simp]: "list_prod (x # xs) = x \<cdot> list_prod xs"
  by (simp add: list_prod_def)

lemma list_prod_closed [intro, simp]:
  "set xs \<subseteq> R \<Longrightarrow> list_prod xs \<in> R"
  by (induct xs) auto

text \<open>A factorization of \<open>a\<close> is a list of irreducible ring elements whose product is \<open>a\<close>.\<close>
definition factorization :: "'a list \<Rightarrow> 'a \<Rightarrow> bool"
  where "factorization fs a \<equiv> (\<forall>p\<in>set fs. irreducible_elem p) \<and> list_prod fs = a"

lemma factorizationI:
  "\<lbrakk> \<And>p. p \<in> set fs \<Longrightarrow> irreducible_elem p; list_prod fs = a \<rbrakk> \<Longrightarrow> factorization fs a"
  unfolding factorization_def by blast

lemma factorization_irreducible: "\<lbrakk> factorization fs a; p \<in> set fs \<rbrakk> \<Longrightarrow> irreducible_elem p"
  unfolding factorization_def by blast

lemma factorization_prod: "factorization fs a \<Longrightarrow> list_prod fs = a"
  unfolding factorization_def by blast

lemma factorization_set_R: "factorization fs a \<Longrightarrow> set fs \<subseteq> R"
  unfolding factorization_def using irreducible_elemD(1) by blast

lemma list_prod_append [simp]:
  assumes "set xs \<subseteq> R" "set ys \<subseteq> R"
  shows "list_prod (xs @ ys) = list_prod xs \<cdot> list_prod ys"
  using assms
  by (induct xs) (simp_all add: multiplicative.associative)

text \<open>An irreducible element has the one-item factorization \<open>[p]\<close>.\<close>
lemma factorization_single: "irreducible_elem p \<Longrightarrow> factorization [p] p"
  by (simp add: factorization_def irreducible_elemD)

text \<open>Concatenating factorizations multiplies the factored elements.\<close>
lemma factorization_append:
  assumes "factorization fs a" "factorization gs b"
  shows "factorization (fs @ gs) (a \<cdot> b)"
  using assms factorization_def factorization_set_R by auto

end


subsection \<open>Uniqueness of factorization\<close>

context integral_domain
begin

text \<open>A prime element dividing a list-product divides one of the factors.\<close>
lemma prime_divides_list_prod:
  assumes p: "prime_elem p" and fs: "set fs \<subseteq> R" and dvd: "divides p (list_prod fs)"
  shows "\<exists>f\<in>set fs. divides p f"
  using fs dvd
proof (induct fs)
  case Nil with one_divides_unit_iff p prime_elem_def show ?case 
    by force
next
  case (Cons f fs)
  then have "divides p f \<or> divides p (list_prod fs)"
    using p prime_elem_def by auto
  then show ?case
    using Cons by force
qed

text \<open>If an irreducible \<open>q\<close> divides an irreducible \<open>p\<close> then they are associated.\<close>
lemma irreducible_dvd_irreducible_assoc:
  assumes q: "irreducible_elem q" and p: "irreducible_elem p" and dvd: "divides q p"
  shows "associated q p"
proof -
  have qR: "q \<in> R" and pR: "p \<in> R" using q p by (auto dest: irreducible_elemD)
  obtain c where c: "c \<in> R" "p = q \<cdot> c" using dvd by blast
  \<comment> \<open>\<open>p = q \<cdot> c\<close> irreducible: \<open>q\<close> or \<open>c\<close> is a unit; \<open>q\<close> is not, so \<open>c\<close> is, giving \<open>q \<sim> p\<close>.\<close>
  have "is_unit q \<or> is_unit c" using irreducible_elemD(4)[OF p qR c(1) c(2)] .
  then have cu: "is_unit c" using irreducible_elemD(3)[OF q] by blast
  have "divides p q"
    using associated_iff_unit_multiple c cu local.associatedD2 multiplicative.commutative pR qR
    by metis
  then show ?thesis using dvd
    by blast
qed

text \<open>Cancellation for association: a common nonzero factor may be dropped.\<close>
lemma associated_cancel:
  assumes c: "c \<in> R" and x: "x \<in> R" and y: "y \<in> R" and cnz: "c \<noteq> \<zero>"
    and as: "associated (c \<cdot> x) (c \<cdot> y)"
  shows "associated x y"
proof (rule associatedI)
  have d1: "divides (c \<cdot> x) (c \<cdot> y)" and d2: "divides (c \<cdot> y) (c \<cdot> x)"
    using as by (auto dest: associatedD1 associatedD2)
  show "divides x y"
  proof -
    obtain d where d: "d \<in> R" "c \<cdot> y = (c \<cdot> x) \<cdot> d" using d1 by blast
    then have "y = x \<cdot> d" 
      using mult_cancel_left[OF c y _ cnz] x d c by auto
    then show ?thesis using d by blast
  qed
  show "divides y x"
  proof -
    obtain d where d: "d \<in> R" "c \<cdot> x = (c \<cdot> y) \<cdot> d" using d2 by blast
    then show ?thesis using d
      using \<open>divides x y\<close> c cnz divides_def local.mult_cancel_left multiplicative.associative
        multiplicative.composition_closed x by metis
  qed
qed

text \<open>Multiplying by a unit yields an associate.\<close>
lemma associated_unit_mult:
  assumes u: "is_unit u" "u \<in> R" and b: "b \<in> R"
  shows "associated (u \<cdot> b) b"
proof (rule associatedI)
  show "divides (u \<cdot> b) b"
    using associated_iff_unit_multiple b local.associatedD2 u by blast
  show "divides b (u \<cdot> b)" using u b by (metis dividesI multiplicative.commutative)
qed

text \<open>Product of a list is unchanged by removing then re-multiplying a member (commutativity).\<close>
lemma list_prod_remove1:
  assumes "set gs \<subseteq> R" and "g \<in> set gs"
  shows "list_prod gs = g \<cdot> list_prod (remove1 g gs)"
  using assms
proof (induct gs)
  case (Cons h hs)
  have hR: "h \<in> R" and hsR: "set hs \<subseteq> R" using Cons.prems(1) by auto
  show ?case
  proof (cases "g = h")
    case False
    have tR: "list_prod (remove1 g hs) \<in> R"
      using hsR set_remove1_subset by fastforce
    have "list_prod (h # hs) = h \<cdot> (g \<cdot> list_prod (remove1 g hs))"
      using Cons.hyps Cons.prems(2) False hsR by force 
    also have "\<dots> = g \<cdot> list_prod (h # remove1 g hs)"      
      using Cons.prems tR by (auto simp: mult_ac)
    also have "h # remove1 g hs = remove1 g (h # hs)" using False by simp
    finally show ?thesis .
  qed auto
qed auto

text \<open>\<^emph>\<open>Uniqueness of factorization\<close> (length form): any two prime factorizations of associated
  products have the same number of factors.  This is the well-definedness of the number of
  irreducible factors --- the core uniqueness statement of unique factorization.\<close>
theorem prime_factorization_length_unique:
  assumes "\<And>f. f \<in> set fs \<Longrightarrow> prime_elem f" and "\<And>g. g \<in> set gs \<Longrightarrow> prime_elem g"
    and "associated (list_prod fs) (list_prod gs)"
  shows "length fs = length gs"
  using assms
proof (induct fs arbitrary: gs)
  case Nil
  \<comment> \<open>Empty on the left: the right product is a unit, so it too must be empty.\<close>
  have "associated \<one> (list_prod gs)" using Nil.prems(3) by simp
  then have 1: "divides (list_prod gs) \<one>" by (auto dest: associatedD2)
  have "gs = []"
  proof (rule ccontr)
    assume "gs \<noteq> []" 
    then obtain g gs' where gs: "gs = g # gs'" using list.exhaust by blast
    have gp: "prime_elem g" using Nil.prems(2) gs by simp
    have gR: "g \<in> R" and gsR: "set gs' \<subseteq> R"
      using gp gs Nil.prems(2) by (auto dest: prime_elemD(1))
    have "divides g (list_prod gs)" using gs gR gsR by (auto intro: dividesI)
    then show False using prime_elemD(3)[OF gp]
      using 1 divides_trans gR one_divides_unit_iff by blast
  qed
  then show ?case by simp
next
  case (Cons f fs')
  have fp: "prime_elem f" using Cons.prems(1) by simp
  then have fR: "f \<in> R" and fnz: "f \<noteq> \<zero>" by (auto dest: prime_elemD)
  have fs'p: "\<And>x. x \<in> set fs' \<Longrightarrow> prime_elem x" using Cons.prems(1) by simp
  have fsR: "set fs' \<subseteq> R" using fs'p prime_elemD(1) by blast
  have gsR: "set gs \<subseteq> R" using Cons.prems(2) prime_elemD(1) by blast
  \<comment> \<open>\<open>f\<close> divides the right product, so divides some \<open>g \<in> gs\<close>; they are associated.\<close>
  have "divides f (list_prod (f # fs'))" using fR fsR by (auto intro: dividesI)
  then have "divides f (list_prod gs)"
    using Cons.prems(3) fR list_prod_closed[OF gsR] by (meson associatedD1 divides_trans)
  then obtain g where g: "g \<in> set gs" and fg: "divides f g"
    using Cons.prems(1) prime_divides_list_prod[OF _ gsR] by auto
  have gp: "prime_elem g" using Cons.prems(2) g by simp
  have gR: "g \<in> R" and gnz: "g \<noteq> \<zero>" using gp by (auto dest: prime_elemD)
  have assoc_fg: "associated f g"
    by (simp add: Cons.prems(1) fg gp irreducible_dvd_irreducible_assoc prime_imp_irreducible)
  define rest where "rest \<equiv> remove1 g gs"
  have restR: "set rest \<subseteq> R"
    using gsR rest_def by force
  have restp: "\<And>x. x \<in> set rest \<Longrightarrow> prime_elem x"
    unfolding rest_def using Cons.prems(2) set_remove1_subset by (meson subset_iff)
  have gs_split: "list_prod gs = g \<cdot> list_prod rest"
    using list_prod_remove1[OF gsR g] rest_def by simp
  \<comment> \<open>\<open>g = f \<cdot> u\<close> for a unit \<open>u\<close>; substitute and cancel \<open>f\<close>.\<close>
  obtain u where u: "u \<in> R" "g = f \<cdot> u"
    using assoc_fg by (auto dest: associatedD1)
  then have uu: "is_unit u"
    using fp gp irreducible_elem_def prime_imp_irreducible by metis
  have "associated (f \<cdot> list_prod fs') (g \<cdot> list_prod rest)"
    using Cons.prems(3) gs_split by simp
  then have "associated (f \<cdot> list_prod fs') (f \<cdot> (u \<cdot> list_prod rest))"
    using u by (simp add: multiplicative.associative fR u(1) restR)
  then have "associated (list_prod fs') (u \<cdot> list_prod rest)"
    using associated_cancel[OF fR list_prod_closed[OF fsR]] fnz u(1) restR by simp
  moreover have "associated (u \<cdot> list_prod rest) (list_prod rest)"
    using associated_unit_mult[OF uu u(1) list_prod_closed[OF restR]] .
  ultimately have "associated (list_prod fs') (list_prod rest)"
    using fsR restR u(1) associated_trans by (meson associated_def divides_trans list_prod_closed)
  then have eqlen: "length fs' = length rest" using Cons.hyps[OF fs'p restp] by simp
  have "0 < length gs" using g by (cases gs) auto
  then show ?case using eqlen
    using g rest_def by (simp add: length_remove1)
qed

end


subsection \<open>Factorial domains (unique factorization domains)\<close>

context principal_ideal_domain
begin

subsubsection \<open>Existence of factorizations\<close>

text \<open>Every nonzero non-unit of a PID admits a factorization into irreducibles.  If not, the
  set of ``bad'' elements (nonzero non-units without a factorization) is nonempty; a bad element
  is not irreducible, so it factors into two non-units, at least one of which is bad and is a
  \<^emph>\<open>proper\<close> divisor.  Iterating (dependent choice) yields a strictly ascending chain of principal
  ideals, contradicting the ascending chain condition.\<close>
theorem factorization_exists:
  assumes a: "a \<in> R" and anz: "a \<noteq> \<zero>" and anu: "\<not> is_unit a"
  shows "\<exists>fs. factorization fs a"
proof (rule ccontr)
  define bad where "bad x \<equiv> x \<in> R \<and> x \<noteq> \<zero> \<and> \<not> is_unit x \<and> \<not> (\<exists>fs. factorization fs x)" for x
  assume non: "\<not> (\<exists>fs. factorization fs a)"
  \<comment> \<open>\<open>bad x\<close>: nonzero non-unit with no factorization.\<close>
  then have bad_a: "bad a" using assms bad_def by simp
  \<comment> \<open>Every bad element has a bad proper divisor.\<close>
  have step: "\<exists>y. bad y \<and> divides y x \<and> \<not> divides x y" if bx: "bad x" for x
  proof -
    have xR: "x \<in> R" and xnz: "x \<noteq> \<zero>" and xnu: "\<not> is_unit x"
      and xnf: "\<not> (\<exists>fs. factorization fs x)" using bx bad_def by auto
    have "\<not> irreducible_elem x" using xnf factorization_single by blast
    then obtain p q where pq: "p \<in> R" "q \<in> R" "x = p \<cdot> q" "\<not> is_unit p" "\<not> is_unit q"
      using irreducible_elemI[OF xR xnz xnu] by blast
    have pnz: "p \<noteq> \<zero>" and qnz: "q \<noteq> \<zero>" using pq(3) xnz pq(1,2) by auto
    \<comment> \<open>If both \<open>p\<close> and \<open>q\<close> had factorizations, so would \<open>x = p \<cdot> q\<close>; hence one is bad.\<close>
    have "\<not> (\<exists>fs. factorization fs p) \<or> \<not> (\<exists>fs. factorization fs q)"
      using factorization_append pq(3) xnf by blast
    then show ?thesis
    proof
      assume npf: "\<not> (\<exists>fs. factorization fs p)"
      have "bad p" using pq(1) pnz pq(4) npf bad_def by simp
      moreover have "\<not> divides x p"
      proof
        assume "divides x p"
        \<comment> \<open>\<open>x | p\<close> and \<open>x = p \<cdot> q\<close> force \<open>q\<close> to be a unit, contradiction.\<close>
        then obtain d where d: "d \<in> R" "p = x \<cdot> d" by blast
        then have "x \<cdot> \<one> = x \<cdot> (q \<cdot> d)"
          using d multiplicative.associative multiplicative.commutative pq(2,3) xR by force 
        then have qd: "q \<cdot> d = \<one>" using mult_cancel_left[OF xR _ _ xnz] pq(2) d by simp
        have "d \<cdot> q = \<one>" using qd pq(2) d(1) by (simp add: multiplicative.commutative)
        then show False
          using d is_unitI pq(5) qd by blast
      qed
      ultimately show ?thesis using pq by blast
    next
      assume nqf: "\<not> (\<exists>fs. factorization fs q)"
      have "bad q" using pq(2) qnz pq(5) nqf bad_def by simp
      moreover have "divides q x"
        using multiplicative.commutative pq by blast
      moreover have "\<not> divides x q"
      proof
        assume "divides x q"
        then obtain d where d: "d \<in> R" "q = x \<cdot> d" by blast
        then have "x \<cdot> \<one> = x \<cdot> (p \<cdot> d)"
          using multiplicative.left_commutative pq xR by auto
        then have pd: "p \<cdot> d = \<one>" using mult_cancel_left[OF xR _ _ xnz] pq(1) d by simp
        have "d \<cdot> p = \<one>" using pd pq(1) d(1) by (simp add: multiplicative.commutative)
        then show False
          using d(1) is_unitI pd pq(4) by presburger
      qed
      ultimately show ?thesis by blast
    qed
  qed
  \<comment> \<open>Build an infinite bad proper-divisor chain by dependent choice.\<close>
  have "\<exists>f. \<forall>n. bad (f n) \<and> (divides (f (Suc n)) (f n) \<and> \<not> divides (f n) (f (Suc n)))"
    by (rule dependent_nat_choice) (use bad_a step in blast)+
  then obtain f where fbad: "\<And>n. bad (f n)"
    and fdvd: "\<And>n. divides (f (Suc n)) (f n)" and fndvd: "\<And>n. \<not> divides (f n) (f (Suc n))"
    by blast
  have fR: "\<And>n. f n \<in> R" using fbad bad_def by simp
  \<comment> \<open>The principal ideals \<open>(f n)\<close> ascend strictly.\<close>
  define A where "A n \<equiv> principal_ideal (f n)" for n
  have "\<And>n. A n \<subseteq> A (Suc n)"
    using A_def fdvd divides_iff_principal_subset[OF fR fR] by simp
  then obtain N where stab: "\<And>n. N \<le> n \<Longrightarrow> A n = A N"
    using A_def principal_ideal_is_ideal[OF fR] ideal_chain_stabilises by force
  \<comment> \<open>\<open>A N = A (Suc N)\<close> makes \<open>f N\<close> and \<open>f (Suc N)\<close> mutually divide.\<close>
  have "A (Suc N) = A N" using stab[of "Suc N"] by simp
  then show False using fndvd
    unfolding A_def using divides_iff_mem_principal fR principal_ideal_contains by metis
qed

end

text \<open>A factorial domain (UFD) is an integral domain in which every nonzero non-unit factors into
  irreducibles, uniquely up to the number of factors (and, via
  @{thm integral_domain.prime_factorization_length_unique}, up to associates and order once the
  factors are prime).\<close>
locale Factorial_Domain = integral_domain +
  assumes factors_exist: "\<lbrakk> a \<in> R; a \<noteq> \<zero>; \<not> is_unit a \<rbrakk> \<Longrightarrow> \<exists>fs. factorization fs a"

text \<open>Every principal ideal domain is a factorial domain: existence of factorizations is
  @{thm principal_ideal_domain.factorization_exists}, established via the ascending chain condition.\<close>
sublocale principal_ideal_domain \<subseteq> Factorial_Domain
  by unfold_locales (rule factorization_exists)

end
