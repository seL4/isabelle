section \<open>The residue rings \<open>\<int>/n\<int>\<close>\<close>

theory ZFact
  imports Ring_Theory
begin

text \<open>\<open>Ring_Theory\<close> suppresses HOL's arithmetic notation; restore it locally for the modular
  arithmetic below.\<close>
notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax

text \<open>For any @{term "n > 1"}, the integers modulo @{term n} form a commutative ring: carrier
  @{term "{0..<n}"} of @{typ nat}, arithmetic modulo @{term n}.  This is the abstract residue ring
  \<open>\<int>/n\<int>\<close>; when @{term n} is prime it is in fact a field, developed in \<open>GF_p\<close>.  The bound
  @{term "n > 1"} ensures both @{term 0} and @{term 1} lie in @{term "{0..<n}"} and are distinct
  in @{typ nat}; the trivial ring case @{term "n = 1"} is not modelled by this carrier.\<close>

definition gfp_add :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "gfp_add n x y = (x + y) mod n"

definition gfp_mult :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "gfp_mult n x y = (x * y) mod n"

context
  fixes n :: nat
  assumes n_gt_1: "n > 1"
begin

lemma n_gt_0: "n > 0" using n_gt_1 by simp

text \<open>Closure: results of modular arithmetic land in @{term "{0..<n}"}.\<close>
lemma gfp_add_closed [simp]: "gfp_add n x y \<in> {0..<n}"
  using n_gt_0 by (simp add: gfp_add_def)

lemma gfp_mult_closed [simp]: "gfp_mult n x y \<in> {0..<n}"
  using n_gt_0 by (simp add: gfp_mult_def)

lemma zero_mem: "(0::nat) \<in> {0..<n}" and one_mem: "(1::nat) \<in> {0..<n}"
  using n_gt_1 by auto

text \<open>The additive part is an abelian group: associative and commutative modular addition, with
  @{term "n - x"} (reduced) as the inverse of @{term x}.\<close>
lemma gfp_add_group: "Group {0..<n} (gfp_add n) 0"
proof (rule GroupI)
  show "\<And>x y z. \<lbrakk> x \<in> {0..<n}; y \<in> {0..<n}; z \<in> {0..<n} \<rbrakk>
          \<Longrightarrow> gfp_add n (gfp_add n x y) z = gfp_add n x (gfp_add n y z)"
    by (simp add: gfp_add_def mod_add_left_eq mod_add_right_eq add.assoc)
next
  fix x assume x: "x \<in> {0..<n}"
  then have key: "(x + (n - x) mod n) mod n = 0"
    by (simp_all add: mod_add_right_eq)
  then show "\<exists>y\<in>{0..<n}. gfp_add n x y = 0 \<and> gfp_add n y x = 0"
    by (metis add.commute add.right_neutral gfp_add_closed gfp_add_def)
qed (use zero_mem n_gt_0 in \<open>simp_all add: add.commute gfp_add_def\<close>)

lemma gfp_add_commutative_monoid: "commutative_monoid {0..<n} (gfp_add n) 0"
  unfolding commutative_monoid_def
  by (metis Group_def add.commute commutative_monoid_axioms.intro gfp_add_def gfp_add_group)

lemma gfp_additive: "Abelian_Group {0..<n} (gfp_add n) 0"
  by (rule Abelian_Group.intro [OF gfp_add_group gfp_add_commutative_monoid])

text \<open>The multiplicative part is a commutative monoid with unit @{term 1}.\<close>
lemma gfp_multiplicative: "commutative_monoid {0..<n} (gfp_mult n) 1"
proof
  show "\<And>x y z. \<lbrakk> x \<in> {0..<n}; y \<in> {0..<n}; z \<in> {0..<n} \<rbrakk>
          \<Longrightarrow> gfp_mult n (gfp_mult n x y) z = gfp_mult n x (gfp_mult n y z)"
    by (simp add: gfp_mult_def mod_mult_left_eq mod_mult_right_eq mult.assoc)
qed (use one_mem n_gt_1 in \<open>simp_all add: mult.commute gfp_mult_def\<close>)

lemma zfact_ring: "Ring {0..<n} (gfp_add n) (gfp_mult n) 0 1"
proof (intro Ring.intro gfp_additive)
  show "Monoid {0..<n} (gfp_mult n) 1"
    by (rule commutative_monoid.axioms(1) [OF gfp_multiplicative])
  show "Ring_axioms {0..<n} (gfp_add n) (gfp_mult n)"
    by unfold_locales
       (simp_all add: gfp_add_def gfp_mult_def mod_mult_left_eq mod_mult_right_eq
                      add_mult_distrib add_mult_distrib2 mod_add_left_eq mod_add_right_eq)
qed

lemma zfact_commutative_ring: "commutative_ring {0..<n} (gfp_add n) (gfp_mult n) 0 1"
  by (rule commutative_ring.intro [OF zfact_ring gfp_multiplicative])

text \<open>The residue ring @{text "\<int>/n\<int>"} has exactly @{term n} elements.\<close>
lemma card_zfact: "card {0..<n} = n" by simp

end

text \<open>Hence, for every @{term "n > 1"}, the locale @{locale commutative_ring} is non-vacuous with
  a witness of cardinality @{term n}.\<close>

end
