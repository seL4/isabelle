section \<open>Linking the locale-based field theory to Isabelle's type classes\<close>

theory Field_Typeclass
  imports Ring_Theory
begin

text \<open>\<open>Ring_Theory\<close> suppresses the HOL arithmetic notation; restore it locally so the
  type-class operations below read normally.\<close>
notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax

text \<open>
  Following the \<open>Met_TC\<close> pattern of \<open>HOL-Analysis.Abstract_Metric_Spaces\<close>
  (where \<open>interpretation Met_TC: Metric_space UNIV dist\<close> feeds the type-class operations
  into the locale), we interpret the locale-based @{locale Field} at an arbitrary
  type-class field, with the whole type as carrier.  This lets the locale-based
  constructions to come (polynomials, splitting fields, Galois groups) be applied to
  concrete type-class fields such as \<open>real\<close> and \<open>complex\<close>.
\<close>

text \<open>Built bottom-up, exactly as for the @{text GF2} witness: the additive abelian group,
  the multiplicative commutative monoid, then the ring, commutative ring and field.\<close>

text \<open>The additive-group, multiplicative-monoid and ring bridge lemmas need only the ring axioms,
  so we state them at the weakest suitable type class @{class comm_ring_1} rather than @{class field}.
  This lets the same bridge serve integral domains (e.g.\ \<open>int\<close>, in theory \<open>IntRing\<close>), not just fields.\<close>

lemma add_group_TC: "Group (UNIV :: 'a :: group_add set) (+) 0"
proof (rule GroupI)
  fix u :: 'a
  show "\<exists>v \<in> UNIV. u + v = 0 \<and> v + u = 0" by (rule bexI [where x = "- u"]) simp_all
qed (auto simp: algebra_simps)

lemma add_abelian_TC: "Abelian_Group (UNIV :: 'a :: ab_group_add set) (+) 0"
proof (rule Abelian_Group.intro [OF add_group_TC])
  show "commutative_monoid UNIV (+) (0::'a)"
    by unfold_locales (simp_all add: ac_simps)
qed

lemma mult_monoid_TC: "Monoid (UNIV :: 'a :: monoid_mult set) (*) 1"
  by unfold_locales (auto simp: ac_simps)

lemma mult_cmonoid_TC: "commutative_monoid (UNIV :: 'a :: comm_monoid_mult set) (*) 1"
  by unfold_locales (auto simp: ac_simps)

lemma ring_TC: "Ring (UNIV :: 'a :: ring_1 set) (+) (*) 0 1"
proof (intro Ring.intro add_abelian_TC)
  show "Monoid (UNIV::'a set) (*) 1"
    using mult_monoid_TC by blast
  show "Ring_axioms (UNIV::'a set) (+) (*)" by unfold_locales (auto simp: algebra_simps)
qed

lemma comm_ring_TC: "commutative_ring (UNIV :: 'a :: comm_ring_1 set) (+) (*) 0 1"
  by (rule commutative_ring.intro [OF ring_TC mult_cmonoid_TC])

text \<open>At an integral domain, the locale @{locale integral_domain} holds: the type class provides
  nontriviality (@{thm zero_neq_one}) and the absence of zero divisors (@{thm mult_eq_0_iff}).\<close>
lemma idom_TC: "integral_domain (UNIV :: 'a :: idom set) (+) (*) 0 1"
proof -
  interpret R: commutative_ring "UNIV :: 'a set" "(+)" "(*)" "0" "1" by (rule comm_ring_TC)
  show ?thesis
  proof (unfold_locales)
    show "(1::'a) \<noteq> 0" by simp
  next
    fix a b :: 'a assume "a * b = 0" then show "a = 0 \<or> b = 0" by simp
  qed
qed

interpretation field_TC: Field "UNIV :: 'a :: field set" "(+)" "(*)" "0" "1"
proof -
  interpret R: commutative_ring "UNIV :: 'a set" "(+)" "(*)" "0" "1" by (rule comm_ring_TC)
  show "Field (UNIV :: 'a set) (+) (*) 0 1"
  proof
    fix a :: 'a assume "a \<noteq> 0"
    then have "a * inverse a = 1" "inverse a * a = 1" by simp_all
    then show "R.multiplicative.invertible a"
      by (intro R.multiplicative.invertibleI [where v = "inverse a"]) auto
  qed auto
qed

text \<open>The interpretation gives, for every type-class field, the locale-based field
  structure on the whole type; e.g. its multiplicative inverse coincides with @{const inverse}
  on nonzero elements.\<close>
lemma TC_inverse_eq:
  fixes a :: "'a :: field"
  assumes "a \<noteq> 0"
  shows "field_TC.multiplicative.inverse a = inverse a"
  using assms by (intro field_TC.multiplicative.inverse_equality) simp_all

end
