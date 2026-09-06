section \<open>The two-element field as a non-vacuity witness\<close>

theory GF2
  imports Ring_Theory
begin

text \<open>\<open>Ring_Theory\<close> suppresses the HOL arithmetic notation; restore it locally so that the
  modular arithmetic below reads normally.\<close>
notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax

text \<open>
  A concrete field with two elements, witnessing that the @{locale Field} and
  @{locale integral_domain} locales (and hence the abstract @{typ "'a ring"} type as a
  field) are non-vacuous.  Carrier @{term "{0, 1}"} of @{typ nat}, arithmetic modulo 2.
\<close>

definition gf2_add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "gf2_add x y = (x + y) mod 2"
definition gf2_mult :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "gf2_mult x y = (x * y) mod 2"

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

end
