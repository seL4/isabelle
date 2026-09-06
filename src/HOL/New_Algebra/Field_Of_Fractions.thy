section \<open>The field of fractions of an integral domain\<close>

theory Field_Of_Fractions
  imports Divisibility_Theory
begin

text \<open>Given an integral domain \<open>R\<close> we construct its field of fractions as a carrier-set object,
  mirroring the elementary construction of \<open>\<rat>\<close> from \<open>\<int>\<close>: fractions are pairs \<open>(a, b)\<close> with
  \<open>b \<noteq> \<zero>\<close>, identified when they cross-multiply equal, and the field operations are the usual ones
  on numerators and denominators.  We reuse the @{locale Equivalence} machinery of
  \<open>Set_Theory\<close> for the quotient, then interpret @{locale Field} on it.  The
  canonical map \<open>a \<mapsto> a / \<one>\<close> is an injective ring homomorphism, giving the universal embedding
  of the domain into a field.\<close>

context integral_domain
begin

subsection \<open>Fractions and their equivalence\<close>

text \<open>A fraction is a pair of ring elements with nonzero denominator.\<close>
definition frac_set :: "('a \<times> 'a) set"
  where "frac_set = {(a, b). a \<in> R \<and> b \<in> R \<and> b \<noteq> \<zero>}"

lemma frac_setI [intro]: "\<lbrakk> a \<in> R; b \<in> R; b \<noteq> \<zero> \<rbrakk> \<Longrightarrow> (a, b) \<in> frac_set"
  unfolding frac_set_def by blast

lemma frac_setD [dest]: "(a, b) \<in> frac_set \<Longrightarrow> a \<in> R \<and> b \<in> R \<and> b \<noteq> \<zero>"
  unfolding frac_set_def by blast

text \<open>The denominator of a fraction is a nonzero ring element; the product of two nonzero
  denominators is again nonzero (no zero divisors).\<close>
lemma frac_mult_denom_nonzero [intro]:
  "\<lbrakk> b \<in> R; d \<in> R; b \<noteq> \<zero>; d \<noteq> \<zero> \<rbrakk> \<Longrightarrow> b \<cdot> d \<noteq> \<zero>"
  using no_zero_divisors by blast

text \<open>Cross-multiplication equivalence: \<open>(a, b) \<sim> (c, d)\<close> iff \<open>a \<cdot> d = c \<cdot> b\<close>.\<close>
definition frac_rel :: "(('a \<times> 'a) \<times> ('a \<times> 'a)) set"
  where "frac_rel = {((a, b), (c, d)). (a, b) \<in> frac_set \<and> (c, d) \<in> frac_set \<and> a \<cdot> d = c \<cdot> b}"

lemma frac_relI [intro]:
  "\<lbrakk> (a, b) \<in> frac_set; (c, d) \<in> frac_set; a \<cdot> d = c \<cdot> b \<rbrakk> \<Longrightarrow> ((a, b), (c, d)) \<in> frac_rel"
  unfolding frac_rel_def by blast

lemma frac_relE:
  assumes "((a, b), (c, d)) \<in> frac_rel"
  obtains "(a, b) \<in> frac_set" "(c, d) \<in> frac_set" "a \<cdot> d = c \<cdot> b"
  using assms unfolding frac_rel_def by blast

text \<open>Transitivity is where cancellation --- hence the domain hypothesis --- is used.\<close>
lemma frac_rel_trans:
  assumes 1: "((a, b), (c, d)) \<in> frac_rel" and 2: "((c, d), (e, f)) \<in> frac_rel"
  shows "((a, b), (e, f)) \<in> frac_rel"
proof -
  from 1 obtain ab: "(a, b) \<in> frac_set" and cd: "(c, d) \<in> frac_set" and e1: "a \<cdot> d = c \<cdot> b"
    by (rule frac_relE)
  from 2 obtain ef: "(e, f) \<in> frac_set" and e2: "c \<cdot> f = e \<cdot> d" by (rule frac_relE)
  from ab cd ef have [simp]: "a \<in> R" "b \<in> R" "c \<in> R" "d \<in> R" "e \<in> R" "f \<in> R"
    and dnz: "d \<noteq> \<zero>" by auto
  \<comment> \<open>From \<open>a d = c b\<close> and \<open>c f = e d\<close>: multiply and cancel \<open>d\<close> to reach \<open>a f = e b\<close>.\<close>
  have "d \<cdot> (a \<cdot> f) = (a \<cdot> d) \<cdot> f" by (simp add: mult_ac)
  also have "\<dots> = (c \<cdot> b) \<cdot> f" by (simp add: e1)
  also have "\<dots> = (c \<cdot> f) \<cdot> b" by (simp add: mult_ac)
  also have "\<dots> = (e \<cdot> d) \<cdot> b" by (simp add: e2)
  also have "\<dots> = d \<cdot> (e \<cdot> b)" by (simp add: mult_ac)
  finally have eq: "d \<cdot> (a \<cdot> f) = d \<cdot> (e \<cdot> b)" .
  have "a \<cdot> f = e \<cdot> b"
    by (rule mult_cancel_left[where c = d]) (use dnz eq in simp_all)
  with ab ef show ?thesis by (rule frac_relI)
qed

text \<open>The relation is an equivalence on the set of fractions.\<close>
interpretation frac: Equivalence frac_set frac_rel
proof (rule equivalenceI)
  show "frac_rel \<subseteq> frac_set \<times> frac_set" by (auto simp: frac_rel_def)
next
  fix x assume "x \<in> frac_set"
  then show "(x, x) \<in> frac_rel" by (cases x) (auto simp: frac_rel_def)
next
  fix x y assume "(x, y) \<in> frac_rel"
  then show "(y, x) \<in> frac_rel" by (cases x; cases y) (auto simp: frac_rel_def)
next
  fix x y z assume "(x, y) \<in> frac_rel" "(y, z) \<in> frac_rel"
  then show "(x, z) \<in> frac_rel"
    by (cases x; cases y; cases z) (blast intro: frac_rel_trans)
qed

subsection \<open>The carrier and class equality\<close>

text \<open>The carrier of the field of fractions: the set of equivalence classes.\<close>
abbreviation Fractions :: "('a \<times> 'a) set set"
  where "Fractions \<equiv> frac_set / frac_rel"

text \<open>Class equality is cross-multiplication.\<close>
lemma frac_eqI:
  assumes "(a, b) \<in> frac_set" "(c, d) \<in> frac_set" "a \<cdot> d = c \<cdot> b"
  shows "frac.Class (a, b) = frac.Class (c, d)"
  using assms by (intro frac.Class_eq frac_relI)

lemma frac_eqD:
  assumes "(a, b) \<in> frac_set" "(c, d) \<in> frac_set" "frac.Class (a, b) = frac.Class (c, d)"
  shows "a \<cdot> d = c \<cdot> b"
  using assms frac.Class_equivalence by (blast elim: frac_relE)

text \<open>A class lies in the carrier exactly when it is the class of a fraction.\<close>
lemma Class_in_Fractions [intro, simp]: "(a, b) \<in> frac_set \<Longrightarrow> frac.Class (a, b) \<in> Fractions"
  by (rule frac.Class_in_Partition)

lemma Fractions_cases:
  assumes "A \<in> Fractions" obtains a b where "(a, b) \<in> frac_set" "A = frac.Class (a, b)"
  using assms frac.representant_exists by (metis surj_pair)

text \<open>A class equals the zero-class \<open>Class (\<zero>, \<one>)\<close> iff any (equivalently every) numerator is zero.
  Later, we take \<open>Class (\<zero>, \<one>)\<close> as the additive unit and \<open>Class (\<one>, \<one>)\<close> as the multiplicative unit
  of \<open>Fractions\<close>.\<close>
lemma frac_Class_zero_iff:
  assumes ab: "(a, b) \<in> frac_set"
  shows "frac.Class (a, b) = frac.Class (\<zero>, \<one>) \<longleftrightarrow> a = \<zero>"
proof
  from ab have aR: "a \<in> R" and bR: "b \<in> R" by auto
  have zero_in: "(\<zero>, \<one>) \<in> frac_set" by (auto intro!: frac_setI simp: nontrivial)
  assume "frac.Class (a, b) = frac.Class (\<zero>, \<one>)"
  from frac_eqD[OF ab zero_in this] show "a = \<zero>" using aR bR by simp
next
  assume "a = \<zero>"
  with ab show "frac.Class (a, b) = frac.Class (\<zero>, \<one>)"
    by (intro frac_eqI) (auto intro!: frac_setI simp: nontrivial)
qed


subsection \<open>The operations on classes\<close>

text \<open>We define addition, multiplication, negation, and inversion on classes by picking any
  representative and applying the elementary fraction formulas.  For each operation we prove a
  congruence lemma (well-definedness under the equivalence) and a \<open>Class\<close>-formula giving the
  computation on a canonical representative.\<close>

definition frac_add :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
    (infixl \<open>[+]\<close> 65)
  where "A [+] B =
    (let (a, b) = SOME p. p \<in> A \<and> p \<in> frac_set;
         (c, d) = SOME p. p \<in> B \<and> p \<in> frac_set
     in frac.Class (a \<cdot> d + c \<cdot> b, b \<cdot> d))"

definition frac_mult :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
    (infixl \<open>[\<cdot>]\<close> 70)
  where "A [\<cdot>] B =
    (let (a, b) = SOME p. p \<in> A \<and> p \<in> frac_set;
         (c, d) = SOME p. p \<in> B \<and> p \<in> frac_set
     in frac.Class (a \<cdot> c, b \<cdot> d))"

definition frac_neg :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"  (\<open>[-] _\<close> [80] 80)
  where "[-] A = (let (a, b) = SOME p. p \<in> A \<and> p \<in> frac_set in frac.Class (- a, b))"

text \<open>Inversion is only used on nonzero classes.\<close>
definition frac_inv :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
  where "frac_inv A = (let (a, b) = SOME p. p \<in> A \<and> p \<in> frac_set in frac.Class (b, a))"

text \<open>The zero and unit of the fraction field.\<close>
abbreviation frac_zero :: "('a \<times> 'a) set"  (\<open>[\<zero>]\<close>)
  where "[\<zero>] \<equiv> frac.Class (\<zero>, \<one>)"

abbreviation frac_one :: "('a \<times> 'a) set"  (\<open>[\<one>]\<close>)
  where "[\<one>] \<equiv> frac.Class (\<one>, \<one>)"

lemma one_in_frac_set: "(\<one>, \<one>) \<in> frac_set"
  by (rule frac_setI) (auto simp: nontrivial)

lemma zero_in_frac_set: "(\<zero>, \<one>) \<in> frac_set"
  by (rule frac_setI) (auto simp: nontrivial)

lemma frac_zero_in [intro, simp]: "[\<zero>] \<in> Fractions"
  using zero_in_frac_set by (rule Class_in_Fractions)

lemma frac_one_in [intro, simp]: "[\<one>] \<in> Fractions"
  using one_in_frac_set by (rule Class_in_Fractions)

lemma frac_one_neq_zero: "[\<one>] \<noteq> [\<zero>]"
proof
  assume eq: "[\<one>] = [\<zero>]"
  from frac_eqD[OF one_in_frac_set zero_in_frac_set eq] show False using nontrivial by simp
qed


subsubsection \<open>Representative selection\<close>

text \<open>Any class of a fraction contains that fraction.\<close>
lemma rep_in_frac_set:
  assumes "(a, b) \<in> frac_set"
  shows "(SOME p. p \<in> frac.Class (a, b) \<and> p \<in> frac_set) \<in> frac.Class (a, b) \<and>
         (SOME p. p \<in> frac.Class (a, b) \<and> p \<in> frac_set) \<in> frac_set"
proof (rule someI_ex)
  from assms have "(a, b) \<in> frac.Class (a, b)" by (intro frac.Class_self)
  with assms show "\<exists>p. p \<in> frac.Class (a, b) \<and> p \<in> frac_set" by blast
qed


subsubsection \<open>Congruence: well-definedness under the equivalence\<close>

lemma frac_add_cong:
  assumes r1: "((a, b), (a', b')) \<in> frac_rel" and r2: "((c, d), (c', d')) \<in> frac_rel"
  shows "((a \<cdot> d + c \<cdot> b, b \<cdot> d), (a' \<cdot> d' + c' \<cdot> b', b' \<cdot> d')) \<in> frac_rel"
proof -
  from r1 obtain ab: "(a, b) \<in> frac_set" and ab': "(a', b') \<in> frac_set" and e1: "a \<cdot> b' = a' \<cdot> b"
    by (rule frac_relE)
  from r2 obtain cd: "(c, d) \<in> frac_set" and cd': "(c', d') \<in> frac_set" and e2: "c \<cdot> d' = c' \<cdot> d"
    by (rule frac_relE)
  from ab ab' cd cd' have [simp]:
    "a \<in> R" "b \<in> R" "a' \<in> R" "b' \<in> R" "c \<in> R" "d \<in> R" "c' \<in> R" "d' \<in> R"
    and bnz: "b \<noteq> \<zero>" and b'nz: "b' \<noteq> \<zero>" and dnz: "d \<noteq> \<zero>" and d'nz: "d' \<noteq> \<zero>" by auto
  have step1: "(a \<cdot> d + c \<cdot> b) \<cdot> (b' \<cdot> d') = (a \<cdot> b') \<cdot> (d \<cdot> d') + (c \<cdot> d') \<cdot> (b \<cdot> b')"
  proof -
    have "(a \<cdot> d + c \<cdot> b) \<cdot> (b' \<cdot> d') = (a \<cdot> d) \<cdot> (b' \<cdot> d') + (c \<cdot> b) \<cdot> (b' \<cdot> d')"
      by (simp add: distributive)
    also have "(a \<cdot> d) \<cdot> (b' \<cdot> d') = (a \<cdot> b') \<cdot> (d \<cdot> d')" by (simp add: mult_ac)
    also have "(c \<cdot> b) \<cdot> (b' \<cdot> d') = (c \<cdot> d') \<cdot> (b \<cdot> b')" by (simp add: mult_ac)
    finally show ?thesis .
  qed
  also have "(a \<cdot> b') \<cdot> (d \<cdot> d') + (c \<cdot> d') \<cdot> (b \<cdot> b') = (a' \<cdot> b) \<cdot> (d \<cdot> d') + (c' \<cdot> d) \<cdot> (b \<cdot> b')"
    by (simp add: e1 e2)
  also have "\<dots> = (a' \<cdot> d' + c' \<cdot> b') \<cdot> (b \<cdot> d)"
  proof -
    have "(a' \<cdot> d' + c' \<cdot> b') \<cdot> (b \<cdot> d) = (a' \<cdot> d') \<cdot> (b \<cdot> d) + (c' \<cdot> b') \<cdot> (b \<cdot> d)"
      by (simp add: distributive)
    also have "(a' \<cdot> d') \<cdot> (b \<cdot> d) = (a' \<cdot> b) \<cdot> (d \<cdot> d')" by (simp add: mult_ac)
    also have "(c' \<cdot> b') \<cdot> (b \<cdot> d) = (c' \<cdot> d) \<cdot> (b \<cdot> b')" by (simp add: mult_ac)
    finally show ?thesis by simp
  qed
  finally have eq: "(a \<cdot> d + c \<cdot> b) \<cdot> (b' \<cdot> d') = (a' \<cdot> d' + c' \<cdot> b') \<cdot> (b \<cdot> d)" .
  have s1: "(a \<cdot> d + c \<cdot> b, b \<cdot> d) \<in> frac_set"
    using bnz dnz frac_mult_denom_nonzero[of b d] by (auto intro!: frac_setI)
  have s2: "(a' \<cdot> d' + c' \<cdot> b', b' \<cdot> d') \<in> frac_set"
    using b'nz d'nz frac_mult_denom_nonzero[of b' d'] by (auto intro!: frac_setI)
  from s1 s2 eq show ?thesis by (rule frac_relI)
qed

lemma frac_mult_cong:
  assumes r1: "((a, b), (a', b')) \<in> frac_rel" and r2: "((c, d), (c', d')) \<in> frac_rel"
  shows "((a \<cdot> c, b \<cdot> d), (a' \<cdot> c', b' \<cdot> d')) \<in> frac_rel"
proof -
  from r1 obtain ab: "(a, b) \<in> frac_set" and ab': "(a', b') \<in> frac_set" and e1: "a \<cdot> b' = a' \<cdot> b"
    by (rule frac_relE)
  from r2 obtain cd: "(c, d) \<in> frac_set" and cd': "(c', d') \<in> frac_set" and e2: "c \<cdot> d' = c' \<cdot> d"
    by (rule frac_relE)
  from ab ab' cd cd' have [simp]:
    "a \<in> R" "b \<in> R" "a' \<in> R" "b' \<in> R" "c \<in> R" "d \<in> R" "c' \<in> R" "d' \<in> R"
    and bnz: "b \<noteq> \<zero>" and b'nz: "b' \<noteq> \<zero>" and dnz: "d \<noteq> \<zero>" and d'nz: "d' \<noteq> \<zero>" by auto
  have "(a \<cdot> c) \<cdot> (b' \<cdot> d') = (a \<cdot> b') \<cdot> (c \<cdot> d')" by (simp add: mult_ac)
  also have "\<dots> = (a' \<cdot> b) \<cdot> (c' \<cdot> d)" by (simp add: e1 e2)
  also have "\<dots> = (a' \<cdot> c') \<cdot> (b \<cdot> d)" by (simp add: mult_ac)
  finally have eq: "(a \<cdot> c) \<cdot> (b' \<cdot> d') = (a' \<cdot> c') \<cdot> (b \<cdot> d)" .
  have s1: "(a \<cdot> c, b \<cdot> d) \<in> frac_set"
    using bnz dnz frac_mult_denom_nonzero[of b d] by (auto intro!: frac_setI)
  have s2: "(a' \<cdot> c', b' \<cdot> d') \<in> frac_set"
    using b'nz d'nz frac_mult_denom_nonzero[of b' d'] by (auto intro!: frac_setI)
  from s1 s2 eq show ?thesis by (rule frac_relI)
qed

lemma frac_neg_cong:
  assumes r: "((a, b), (a', b')) \<in> frac_rel"
  shows "((- a, b), (- a', b')) \<in> frac_rel"
proof -
  from r obtain ab: "(a, b) \<in> frac_set" and ab': "(a', b') \<in> frac_set" and e: "a \<cdot> b' = a' \<cdot> b"
    by (rule frac_relE)
  from ab ab' have [simp]: "a \<in> R" "b \<in> R" "a' \<in> R" "b' \<in> R"
    and bnz: "b \<noteq> \<zero>" and b'nz: "b' \<noteq> \<zero>" by auto
  have "(- a) \<cdot> b' = - (a \<cdot> b')" by (simp add: left_minus)
  also have "\<dots> = - (a' \<cdot> b)" by (simp add: e)
  also have "\<dots> = (- a') \<cdot> b" by (simp add: left_minus)
  finally have eq: "(- a) \<cdot> b' = (- a') \<cdot> b" .
  have s1: "(- a, b) \<in> frac_set" using bnz by (auto intro!: frac_setI)
  have s2: "(- a', b') \<in> frac_set" using b'nz by (auto intro!: frac_setI)
  from s1 s2 eq show ?thesis by (rule frac_relI)
qed

text \<open>Inversion: well-defined provided the numerators are nonzero (i.e.\ the class is nonzero).\<close>
lemma frac_inv_cong:
  assumes r: "((a, b), (a', b')) \<in> frac_rel" and anz: "a \<noteq> \<zero>"
  shows "((b, a), (b', a')) \<in> frac_rel"
proof -
  from r obtain ab: "(a, b) \<in> frac_set" and ab': "(a', b') \<in> frac_set" and e: "a \<cdot> b' = a' \<cdot> b"
    by (rule frac_relE)
  from ab ab' have [simp]: "a \<in> R" "b \<in> R" "a' \<in> R" "b' \<in> R"
    and bnz: "b \<noteq> \<zero>" and b'nz: "b' \<noteq> \<zero>" by auto
  have a'nz: "a' \<noteq> \<zero>"
  proof
    assume "a' = \<zero>"
    with e have "a \<cdot> b' = \<zero>" by simp
    then have "a = \<zero> \<or> b' = \<zero>" using no_zero_divisors by simp
    with anz b'nz show False by auto
  qed
  have s1: "(b, a) \<in> frac_set" using anz by (auto intro!: frac_setI)
  have s2: "(b', a') \<in> frac_set" using a'nz by (auto intro!: frac_setI)
  have "b \<cdot> a' = a' \<cdot> b" by (simp add: mult_ac)
  also have "\<dots> = a \<cdot> b'" by (simp add: e)
  also have "\<dots> = b' \<cdot> a" by (simp add: mult_ac)
  finally have "b \<cdot> a' = b' \<cdot> a" .
  with s1 s2 show ?thesis by (rule frac_relI)
qed


subsubsection \<open>The \<open>Class\<close>-formulas\<close>

text \<open>Key auxiliary: if a class is chosen from a fraction, the SOME-representative is equivalent
  to the given fraction.\<close>
lemma some_rep_equiv:
  assumes ab: "(a, b) \<in> frac_set"
  defines "p \<equiv> SOME p. p \<in> frac.Class (a, b) \<and> p \<in> frac_set"
  shows "(p, (a, b)) \<in> frac_rel" and "p \<in> frac_set"
proof -
  have rep_prop: "p \<in> frac.Class (a, b) \<and> p \<in> frac_set"
    unfolding p_def using rep_in_frac_set[OF ab] by simp
  then have "p \<in> frac.Class (a, b)" and "p \<in> frac_set" by auto
  from frac.ClassD[OF this(1) ab] show "(p, (a, b)) \<in> frac_rel" .
  from rep_prop show "p \<in> frac_set" by simp
qed

lemma frac_add_Class:
  assumes ab: "(a, b) \<in> frac_set" and cd: "(c, d) \<in> frac_set"
  shows "frac.Class (a, b) [+] frac.Class (c, d) = frac.Class (a \<cdot> d + c \<cdot> b, b \<cdot> d)"
proof -
  let ?p = "SOME p. p \<in> frac.Class (a, b) \<and> p \<in> frac_set"
  let ?q = "SOME p. p \<in> frac.Class (c, d) \<and> p \<in> frac_set"
  have p_equiv: "(?p, (a, b)) \<in> frac_rel" using some_rep_equiv(1)[OF ab] .
  have q_equiv: "(?q, (c, d)) \<in> frac_rel" using some_rep_equiv(1)[OF cd] .
  obtain a1 b1 where p_eq: "?p = (a1, b1)" by force
  obtain c1 d1 where q_eq: "?q = (c1, d1)" by force
  from p_eq p_equiv have "((a1, b1), (a, b)) \<in> frac_rel" by simp
  moreover from q_eq q_equiv have "((c1, d1), (c, d)) \<in> frac_rel" by simp
  ultimately have "((a1 \<cdot> d1 + c1 \<cdot> b1, b1 \<cdot> d1), (a \<cdot> d + c \<cdot> b, b \<cdot> d)) \<in> frac_rel"
    by (rule frac_add_cong)
  then have "frac.Class (a1 \<cdot> d1 + c1 \<cdot> b1, b1 \<cdot> d1) = frac.Class (a \<cdot> d + c \<cdot> b, b \<cdot> d)"
    by (rule frac.Class_eq)
  then show ?thesis
    unfolding frac_add_def by (simp add: p_eq q_eq)
qed

lemma frac_mult_Class:
  assumes ab: "(a, b) \<in> frac_set" and cd: "(c, d) \<in> frac_set"
  shows "frac.Class (a, b) [\<cdot>] frac.Class (c, d) = frac.Class (a \<cdot> c, b \<cdot> d)"
proof -
  let ?p = "SOME p. p \<in> frac.Class (a, b) \<and> p \<in> frac_set"
  let ?q = "SOME p. p \<in> frac.Class (c, d) \<and> p \<in> frac_set"
  have p_equiv: "(?p, (a, b)) \<in> frac_rel" using some_rep_equiv(1)[OF ab] .
  have q_equiv: "(?q, (c, d)) \<in> frac_rel" using some_rep_equiv(1)[OF cd] .
  obtain a1 b1 where p_eq: "?p = (a1, b1)" by force
  obtain c1 d1 where q_eq: "?q = (c1, d1)" by force
  from p_eq p_equiv have "((a1, b1), (a, b)) \<in> frac_rel" by simp
  moreover from q_eq q_equiv have "((c1, d1), (c, d)) \<in> frac_rel" by simp
  ultimately have "((a1 \<cdot> c1, b1 \<cdot> d1), (a \<cdot> c, b \<cdot> d)) \<in> frac_rel"
    by (rule frac_mult_cong)
  then have "frac.Class (a1 \<cdot> c1, b1 \<cdot> d1) = frac.Class (a \<cdot> c, b \<cdot> d)"
    by (rule frac.Class_eq)
  then show ?thesis
    unfolding frac_mult_def by (simp add: p_eq q_eq)
qed

lemma frac_neg_Class:
  assumes ab: "(a, b) \<in> frac_set"
  shows "[-] frac.Class (a, b) = frac.Class (- a, b)"
proof -
  let ?p = "SOME p. p \<in> frac.Class (a, b) \<and> p \<in> frac_set"
  have p_equiv: "(?p, (a, b)) \<in> frac_rel" using some_rep_equiv(1)[OF ab] .
  obtain a1 b1 where p_eq: "?p = (a1, b1)" by force
  from p_eq p_equiv have "((a1, b1), (a, b)) \<in> frac_rel" by simp
  then have "((- a1, b1), (- a, b)) \<in> frac_rel" by (rule frac_neg_cong)
  then have "frac.Class (- a1, b1) = frac.Class (- a, b)" by (rule frac.Class_eq)
  then show ?thesis unfolding frac_neg_def by (simp add: p_eq)
qed

lemma frac_inv_Class:
  assumes ab: "(a, b) \<in> frac_set" and anz: "a \<noteq> \<zero>"
  shows "frac_inv (frac.Class (a, b)) = frac.Class (b, a)"
proof -
  let ?p = "SOME p. p \<in> frac.Class (a, b) \<and> p \<in> frac_set"
  have p_equiv: "(?p, (a, b)) \<in> frac_rel" using some_rep_equiv(1)[OF ab] .
  obtain a1 b1 where p_eq: "?p = (a1, b1)" by force
  from p_eq p_equiv have r: "((a1, b1), (a, b)) \<in> frac_rel" by simp
  \<comment> \<open>Symmetry gives us \<open>((a,b),(a1,b1)) \<in> frac_rel\<close>, whose inversion congruence needs \<open>a \<noteq> \<zero>\<close>.\<close>
  from r have r': "((a, b), (a1, b1)) \<in> frac_rel" by (rule frac.symmetric)
  then have "((b, a), (b1, a1)) \<in> frac_rel" using anz by (rule frac_inv_cong)
  then have "((b1, a1), (b, a)) \<in> frac_rel" by (rule frac.symmetric)
  then have "frac.Class (b1, a1) = frac.Class (b, a)" by (rule frac.Class_eq)
  then show ?thesis unfolding frac_inv_def by (simp add: p_eq)
qed


subsubsection \<open>Closure under the operations\<close>

lemma frac_add_closed [intro, simp]:
  "A \<in> Fractions \<Longrightarrow> B \<in> Fractions \<Longrightarrow> A [+] B \<in> Fractions"
proof -
  assume "A \<in> Fractions" "B \<in> Fractions"
  then obtain a b c d
    where A: "A = frac.Class (a, b)" "(a, b) \<in> frac_set"
      and B: "B = frac.Class (c, d)" "(c, d) \<in> frac_set"
    by (metis Fractions_cases)
  then have [simp]: "b \<in> R" "d \<in> R" "b \<noteq> \<zero>" "d \<noteq> \<zero>" and abR: "a \<in> R" "c \<in> R" by auto
  have "(a \<cdot> d + c \<cdot> b, b \<cdot> d) \<in> frac_set" using abR frac_mult_denom_nonzero[of b d] by (auto intro!: frac_setI)
  then show "A [+] B \<in> Fractions" using A B frac_add_Class[OF A(2) B(2)] by auto
qed

lemma frac_mult_closed [intro, simp]:
  "A \<in> Fractions \<Longrightarrow> B \<in> Fractions \<Longrightarrow> A [\<cdot>] B \<in> Fractions"
proof -
  assume "A \<in> Fractions" "B \<in> Fractions"
  then obtain a b c d
    where A: "A = frac.Class (a, b)" "(a, b) \<in> frac_set"
      and B: "B = frac.Class (c, d)" "(c, d) \<in> frac_set"
    by (metis Fractions_cases)
  then have [simp]: "b \<in> R" "d \<in> R" "b \<noteq> \<zero>" "d \<noteq> \<zero>" and abR: "a \<in> R" "c \<in> R" by auto
  have "(a \<cdot> c, b \<cdot> d) \<in> frac_set" using abR frac_mult_denom_nonzero[of b d] by (auto intro!: frac_setI)
  then show "A [\<cdot>] B \<in> Fractions" using A B frac_mult_Class[OF A(2) B(2)] by auto
qed

lemma frac_neg_closed [intro, simp]: "A \<in> Fractions \<Longrightarrow> [-] A \<in> Fractions"
proof -
  assume "A \<in> Fractions"
  then obtain a b where A: "A = frac.Class (a, b)" "(a, b) \<in> frac_set" by (metis Fractions_cases)
  then have "(- a, b) \<in> frac_set" by (auto intro!: frac_setI)
  then show "[-] A \<in> Fractions" using A frac_neg_Class[OF A(2)] by auto
qed


subsection \<open>The field of fractions\<close>

text \<open>We assemble the additive abelian group and the multiplicative monoid as separate top-level
  lemmas, then compose them via @{thm [source] Ring.intro} to obtain the ring structure.  This
  avoids taking on the (locale-qualified) @{term Monoid.invertible} obligation mid-interpretation:
  we discharge it once, at the level of @{thm [source] GroupI}, which takes the raw
  \<open>\<exists>v \<in> G. u \<cdot> v = \<one> \<and> v \<cdot> u = \<one>\<close> form directly.\<close>

subsubsection \<open>The additive abelian group of \<open>Fractions\<close>\<close>

text \<open>The additive group.  Associativity, unit, invertibility, and commutativity are established
  on fraction representatives.  Invertibility supplies the explicit inverse \<open>Class(- a, b)\<close> of
  \<open>Class(a, b)\<close>.\<close>
lemma Frac_add_group: "Group Fractions ([+]) [\<zero>]"
proof (rule GroupI)
  \<comment> \<open>Closure.\<close>
  fix A B assume "A \<in> Fractions" "B \<in> Fractions"
  then show "A [+] B \<in> Fractions" by simp
next
  show "[\<zero>] \<in> Fractions" by simp
next
  \<comment> \<open>Associativity of \<open>[+]\<close>, on representatives.\<close>
  fix A B C assume A: "A \<in> Fractions" and B: "B \<in> Fractions" and C: "C \<in> Fractions"
  obtain a b where A': "A = frac.Class (a, b)" "(a, b) \<in> frac_set" using A by (metis Fractions_cases)
  obtain c d where B': "B = frac.Class (c, d)" "(c, d) \<in> frac_set" using B by (metis Fractions_cases)
  obtain e f where C': "C = frac.Class (e, f)" "(e, f) \<in> frac_set" using C by (metis Fractions_cases)
  from A' B' C' have [simp]:
    "a \<in> R" "b \<in> R" "c \<in> R" "d \<in> R" "e \<in> R" "f \<in> R"
    "b \<noteq> \<zero>" "d \<noteq> \<zero>" "f \<noteq> \<zero>" by auto
  have s1: "(a \<cdot> d + c \<cdot> b, b \<cdot> d) \<in> frac_set"
    using frac_mult_denom_nonzero[of b d] by (auto intro!: frac_setI)
  have s2: "(c \<cdot> f + e \<cdot> d, d \<cdot> f) \<in> frac_set"
    using frac_mult_denom_nonzero[of d f] by (auto intro!: frac_setI)
  have "(A [+] B) [+] C = frac.Class ((a \<cdot> d + c \<cdot> b) \<cdot> f + e \<cdot> (b \<cdot> d), (b \<cdot> d) \<cdot> f)"
    using A' B' C' by (simp add: frac_add_Class[OF A'(2) B'(2)] frac_add_Class[OF s1 C'(2)])
  moreover have "A [+] (B [+] C) = frac.Class (a \<cdot> (d \<cdot> f) + (c \<cdot> f + e \<cdot> d) \<cdot> b, b \<cdot> (d \<cdot> f))"
    using A' B' C' by (simp add: frac_add_Class[OF B'(2) C'(2)] frac_add_Class[OF A'(2) s2])
  moreover have "(a \<cdot> d + c \<cdot> b) \<cdot> f + e \<cdot> (b \<cdot> d) = a \<cdot> (d \<cdot> f) + (c \<cdot> f + e \<cdot> d) \<cdot> b"
  proof -
    have LHS: "(a \<cdot> d + c \<cdot> b) \<cdot> f + e \<cdot> (b \<cdot> d) = a \<cdot> (d \<cdot> f) + c \<cdot> f \<cdot> b + e \<cdot> d \<cdot> b"
      by (simp add: distributive mult_ac add_ac)
    have RHS: "a \<cdot> (d \<cdot> f) + (c \<cdot> f + e \<cdot> d) \<cdot> b = a \<cdot> (d \<cdot> f) + c \<cdot> f \<cdot> b + e \<cdot> d \<cdot> b"
      by (simp add: distributive mult_ac add_ac)
    from LHS RHS show ?thesis by simp
  qed
  moreover have "(b \<cdot> d) \<cdot> f = b \<cdot> (d \<cdot> f)" by (simp add: mult_ac)
  ultimately show "(A [+] B) [+] C = A [+] (B [+] C)" by simp
next
  \<comment> \<open>Left unit of \<open>[+]\<close> is \<open>[\<zero>]\<close>.\<close>
  fix A assume A: "A \<in> Fractions"
  obtain a b where A': "A = frac.Class (a, b)" "(a, b) \<in> frac_set" using A by (metis Fractions_cases)
  from A' have [simp]: "a \<in> R" "b \<in> R" "b \<noteq> \<zero>" by auto
  have "[\<zero>] [+] A = frac.Class (\<zero> \<cdot> b + a \<cdot> \<one>, \<one> \<cdot> b)"
    using A' by (simp add: frac_add_Class[OF zero_in_frac_set A'(2)])
  also have "\<dots> = frac.Class (a, b)" by simp
  finally show "[\<zero>] [+] A = A" using A' by simp
next
  \<comment> \<open>Right unit of \<open>[+]\<close>.\<close>
  fix A assume A: "A \<in> Fractions"
  obtain a b where A': "A = frac.Class (a, b)" "(a, b) \<in> frac_set" using A by (metis Fractions_cases)
  from A' have [simp]: "a \<in> R" "b \<in> R" "b \<noteq> \<zero>" by auto
  have "A [+] [\<zero>] = frac.Class (a \<cdot> \<one> + \<zero> \<cdot> b, b \<cdot> \<one>)"
    using A' by (simp add: frac_add_Class[OF A'(2) zero_in_frac_set])
  also have "\<dots> = frac.Class (a, b)" by simp
  finally show "A [+] [\<zero>] = A" using A' by simp
next
  \<comment> \<open>Invertibility for \<open>[+]\<close>: supply the explicit two-sided inverse \<open>[-] A\<close>.  This is the pinch
    point that motivates the whole refactor --- @{thm [source] GroupI} takes the raw
    \<open>\<exists>v \<in> G. u \<cdot> v = \<one> \<and> v \<cdot> u = \<one>\<close> form, avoiding the locale-qualified @{term Monoid.invertible}
    obligation that would otherwise be raised inside a bare @{command interpretation} of \<open>Ring\<close>.\<close>
  fix A assume A: "A \<in> Fractions"
  obtain a b where A': "A = frac.Class (a, b)" "(a, b) \<in> frac_set" using A by (metis Fractions_cases)
  from A' have abR: "a \<in> R" "b \<in> R" and bnz: "b \<noteq> \<zero>" by auto
  have bbR: "b \<cdot> b \<in> R" and bbnz: "b \<cdot> b \<noteq> \<zero>"
    using abR bnz frac_mult_denom_nonzero[of b b] by auto
  have negA_in_frac_set: "(- a, b) \<in> frac_set" using abR bnz by (auto intro!: frac_setI)
  have negA: "[-] A = frac.Class (- a, b)" using A' by (simp add: frac_neg_Class[OF A'(2)])
  have zero_bb_in: "(\<zero>, b \<cdot> b) \<in> frac_set" using bbR bbnz by (auto intro!: frac_setI)
  have zero_bb_eq_zero: "frac.Class (\<zero>, b \<cdot> b) = frac.Class (\<zero>, \<one>)"
    using bbR by (intro frac_eqI[OF zero_bb_in zero_in_frac_set]) simp
  have right: "A [+] ([-] A) = [\<zero>]"
  proof -
    have "A [+] ([-] A) = frac.Class (a \<cdot> b + (- a) \<cdot> b, b \<cdot> b)"
      using A' negA by (simp add: frac_add_Class[OF A'(2) negA_in_frac_set])
    also have "a \<cdot> b + (- a) \<cdot> b = \<zero>" using abR by (simp add: left_minus)
    finally have "A [+] ([-] A) = frac.Class (\<zero>, b \<cdot> b)" .
    then show ?thesis using zero_bb_eq_zero by simp
  qed
  have left: "[-] A [+] A = [\<zero>]"
  proof -
    have "[-] A [+] A = frac.Class ((- a) \<cdot> b + a \<cdot> b, b \<cdot> b)"
      using A' negA by (simp add: frac_add_Class[OF negA_in_frac_set A'(2)])
    also have "(- a) \<cdot> b + a \<cdot> b = \<zero>" using abR by (simp add: left_minus)
    finally have "[-] A [+] A = frac.Class (\<zero>, b \<cdot> b)" .
    then show ?thesis using zero_bb_eq_zero by simp
  qed
  have negA_class: "[-] A \<in> Fractions" using A by simp
  from right left negA_class show "\<exists>v\<in>Fractions. A [+] v = [\<zero>] \<and> v [+] A = [\<zero>]" by blast
qed

lemma Frac_add_commutative: "\<lbrakk> A \<in> Fractions; B \<in> Fractions \<rbrakk> \<Longrightarrow> A [+] B = B [+] A"
proof -
  fix A B assume A: "A \<in> Fractions" and B: "B \<in> Fractions"
  obtain a b where A': "A = frac.Class (a, b)" "(a, b) \<in> frac_set" using A by (metis Fractions_cases)
  obtain c d where B': "B = frac.Class (c, d)" "(c, d) \<in> frac_set" using B by (metis Fractions_cases)
  from A' B' have [simp]: "a \<in> R" "b \<in> R" "c \<in> R" "d \<in> R" "b \<noteq> \<zero>" "d \<noteq> \<zero>" by auto
  have "A [+] B = frac.Class (a \<cdot> d + c \<cdot> b, b \<cdot> d)"
    using A' B' by (simp add: frac_add_Class[OF A'(2) B'(2)])
  moreover have "B [+] A = frac.Class (c \<cdot> b + a \<cdot> d, d \<cdot> b)"
    using A' B' by (simp add: frac_add_Class[OF B'(2) A'(2)])
  moreover have "a \<cdot> d + c \<cdot> b = c \<cdot> b + a \<cdot> d" by (simp add: add_ac)
  moreover have "b \<cdot> d = d \<cdot> b" by (simp add: mult_ac)
  ultimately show "A [+] B = B [+] A" by simp
qed

lemma Frac_add_commutative_monoid: "commutative_monoid Fractions ([+]) [\<zero>]"
proof -
  interpret G: Group Fractions "([+])" "[\<zero>]" by (rule Frac_add_group)
  show ?thesis
    by unfold_locales (simp_all add: Frac_add_commutative)
qed

lemma Frac_abelian_group: "Abelian_Group Fractions ([+]) [\<zero>]"
  by (rule Abelian_Group.intro[OF Frac_add_group Frac_add_commutative_monoid])


subsubsection \<open>The multiplicative monoid of \<open>Fractions\<close>\<close>

lemma Frac_mult_monoid: "Monoid Fractions ([\<cdot>]) [\<one>]"
proof
  fix A B assume "A \<in> Fractions" "B \<in> Fractions"
  then show "A [\<cdot>] B \<in> Fractions" by simp
next
  show "[\<one>] \<in> Fractions" by simp
next
  \<comment> \<open>Associativity of \<open>[\<cdot>]\<close>, on representatives.\<close>
  fix A B C assume A: "A \<in> Fractions" and B: "B \<in> Fractions" and C: "C \<in> Fractions"
  obtain a b where A': "A = frac.Class (a, b)" "(a, b) \<in> frac_set" using A by (metis Fractions_cases)
  obtain c d where B': "B = frac.Class (c, d)" "(c, d) \<in> frac_set" using B by (metis Fractions_cases)
  obtain e f where C': "C = frac.Class (e, f)" "(e, f) \<in> frac_set" using C by (metis Fractions_cases)
  from A' B' C' have [simp]:
    "a \<in> R" "b \<in> R" "c \<in> R" "d \<in> R" "e \<in> R" "f \<in> R"
    "b \<noteq> \<zero>" "d \<noteq> \<zero>" "f \<noteq> \<zero>" by auto
  have s1: "(a \<cdot> c, b \<cdot> d) \<in> frac_set"
    using frac_mult_denom_nonzero[of b d] by (auto intro!: frac_setI)
  have s2: "(c \<cdot> e, d \<cdot> f) \<in> frac_set"
    using frac_mult_denom_nonzero[of d f] by (auto intro!: frac_setI)
  have "(A [\<cdot>] B) [\<cdot>] C = frac.Class ((a \<cdot> c) \<cdot> e, (b \<cdot> d) \<cdot> f)"
    using A' B' C' by (simp add: frac_mult_Class[OF A'(2) B'(2)] frac_mult_Class[OF s1 C'(2)])
  moreover have "A [\<cdot>] (B [\<cdot>] C) = frac.Class (a \<cdot> (c \<cdot> e), b \<cdot> (d \<cdot> f))"
    using A' B' C' by (simp add: frac_mult_Class[OF B'(2) C'(2)] frac_mult_Class[OF A'(2) s2])
  moreover have "(a \<cdot> c) \<cdot> e = a \<cdot> (c \<cdot> e)" by (simp add: mult_ac)
  moreover have "(b \<cdot> d) \<cdot> f = b \<cdot> (d \<cdot> f)" by (simp add: mult_ac)
  ultimately show "(A [\<cdot>] B) [\<cdot>] C = A [\<cdot>] (B [\<cdot>] C)" by simp
next
  \<comment> \<open>Left unit.\<close>
  fix A assume A: "A \<in> Fractions"
  obtain a b where A': "A = frac.Class (a, b)" "(a, b) \<in> frac_set" using A by (metis Fractions_cases)
  from A' have [simp]: "a \<in> R" "b \<in> R" "b \<noteq> \<zero>" by auto
  have "[\<one>] [\<cdot>] A = frac.Class (\<one> \<cdot> a, \<one> \<cdot> b)"
    using A' by (simp add: frac_mult_Class[OF one_in_frac_set A'(2)])
  also have "\<dots> = frac.Class (a, b)" by simp
  finally show "[\<one>] [\<cdot>] A = A" using A' by simp
next
  \<comment> \<open>Right unit.\<close>
  fix A assume A: "A \<in> Fractions"
  obtain a b where A': "A = frac.Class (a, b)" "(a, b) \<in> frac_set" using A by (metis Fractions_cases)
  from A' have [simp]: "a \<in> R" "b \<in> R" "b \<noteq> \<zero>" by auto
  have "A [\<cdot>] [\<one>] = frac.Class (a \<cdot> \<one>, b \<cdot> \<one>)"
    using A' by (simp add: frac_mult_Class[OF A'(2) one_in_frac_set])
  also have "\<dots> = frac.Class (a, b)" by simp
  finally show "A [\<cdot>] [\<one>] = A" using A' by simp
qed


subsubsection \<open>Distributivity and the ring axiom\<close>

lemma Frac_Ring_axioms: "Ring_axioms Fractions ([+]) ([\<cdot>])"
proof
  \<comment> \<open>Left distributivity.\<close>
  fix A B C assume A: "A \<in> Fractions" and B: "B \<in> Fractions" and C: "C \<in> Fractions"
  obtain a b where A': "A = frac.Class (a, b)" "(a, b) \<in> frac_set" using A by (metis Fractions_cases)
  obtain c d where B': "B = frac.Class (c, d)" "(c, d) \<in> frac_set" using B by (metis Fractions_cases)
  obtain e f where C': "C = frac.Class (e, f)" "(e, f) \<in> frac_set" using C by (metis Fractions_cases)
  from A' B' C' have [simp]:
    "a \<in> R" "b \<in> R" "c \<in> R" "d \<in> R" "e \<in> R" "f \<in> R"
    "b \<noteq> \<zero>" "d \<noteq> \<zero>" "f \<noteq> \<zero>" by auto
  have BC_in: "(c \<cdot> f + e \<cdot> d, d \<cdot> f) \<in> frac_set"
    using frac_mult_denom_nonzero[of d f] by (auto intro!: frac_setI)
  have AB_in: "(a \<cdot> c, b \<cdot> d) \<in> frac_set"
    using frac_mult_denom_nonzero[of b d] by (auto intro!: frac_setI)
  have AC_in: "(a \<cdot> e, b \<cdot> f) \<in> frac_set"
    using frac_mult_denom_nonzero[of b f] by (auto intro!: frac_setI)
  have "A [\<cdot>] (B [+] C) = frac.Class (a \<cdot> (c \<cdot> f + e \<cdot> d), b \<cdot> (d \<cdot> f))"
    using A' B' C' by (simp add: frac_add_Class[OF B'(2) C'(2)] frac_mult_Class[OF A'(2) BC_in])
  moreover have "A [\<cdot>] B [+] A [\<cdot>] C =
                   frac.Class ((a \<cdot> c) \<cdot> (b \<cdot> f) + (a \<cdot> e) \<cdot> (b \<cdot> d), (b \<cdot> d) \<cdot> (b \<cdot> f))"
    using A' B' C'
    by (simp add: frac_mult_Class[OF A'(2) B'(2)] frac_mult_Class[OF A'(2) C'(2)]
                  frac_add_Class[OF AB_in AC_in])
  moreover have
    "(a \<cdot> (c \<cdot> f + e \<cdot> d)) \<cdot> ((b \<cdot> d) \<cdot> (b \<cdot> f)) =
     ((a \<cdot> c) \<cdot> (b \<cdot> f) + (a \<cdot> e) \<cdot> (b \<cdot> d)) \<cdot> (b \<cdot> (d \<cdot> f))"
  proof -
    have "a \<cdot> (c \<cdot> f + e \<cdot> d) = a \<cdot> (c \<cdot> f) + a \<cdot> (e \<cdot> d)" by (simp add: distributive)
    then have L: "(a \<cdot> (c \<cdot> f + e \<cdot> d)) \<cdot> ((b \<cdot> d) \<cdot> (b \<cdot> f))
                   = a \<cdot> (c \<cdot> f) \<cdot> ((b \<cdot> d) \<cdot> (b \<cdot> f)) + a \<cdot> (e \<cdot> d) \<cdot> ((b \<cdot> d) \<cdot> (b \<cdot> f))"
      by (simp add: distributive)
    have "((a \<cdot> c) \<cdot> (b \<cdot> f) + (a \<cdot> e) \<cdot> (b \<cdot> d)) \<cdot> (b \<cdot> (d \<cdot> f))
            = (a \<cdot> c) \<cdot> (b \<cdot> f) \<cdot> (b \<cdot> (d \<cdot> f)) + (a \<cdot> e) \<cdot> (b \<cdot> d) \<cdot> (b \<cdot> (d \<cdot> f))"
      by (simp add: distributive)
    also have "(a \<cdot> c) \<cdot> (b \<cdot> f) \<cdot> (b \<cdot> (d \<cdot> f)) = a \<cdot> (c \<cdot> f) \<cdot> ((b \<cdot> d) \<cdot> (b \<cdot> f))"
      by (simp add: mult_ac)
    also have "(a \<cdot> e) \<cdot> (b \<cdot> d) \<cdot> (b \<cdot> (d \<cdot> f)) = a \<cdot> (e \<cdot> d) \<cdot> ((b \<cdot> d) \<cdot> (b \<cdot> f))"
      by (simp add: mult_ac)
    finally show ?thesis using L by simp
  qed
  moreover have "(a \<cdot> (c \<cdot> f + e \<cdot> d), b \<cdot> (d \<cdot> f)) \<in> frac_set"
    using frac_mult_denom_nonzero[of d f] frac_mult_denom_nonzero[of b "d \<cdot> f"]
    by (auto intro!: frac_setI)
  moreover have "((a \<cdot> c) \<cdot> (b \<cdot> f) + (a \<cdot> e) \<cdot> (b \<cdot> d), (b \<cdot> d) \<cdot> (b \<cdot> f)) \<in> frac_set"
    using frac_mult_denom_nonzero[of b d] frac_mult_denom_nonzero[of b f]
          frac_mult_denom_nonzero[of "b \<cdot> d" "b \<cdot> f"]
    by (auto intro!: frac_setI)
  ultimately show "A [\<cdot>] (B [+] C) = A [\<cdot>] B [+] A [\<cdot>] C"
    by (metis frac_eqI)
next
  \<comment> \<open>Right distributivity.\<close>
  fix A B C assume A: "A \<in> Fractions" and B: "B \<in> Fractions" and C: "C \<in> Fractions"
  obtain a b where A': "A = frac.Class (a, b)" "(a, b) \<in> frac_set" using A by (metis Fractions_cases)
  obtain c d where B': "B = frac.Class (c, d)" "(c, d) \<in> frac_set" using B by (metis Fractions_cases)
  obtain e f where C': "C = frac.Class (e, f)" "(e, f) \<in> frac_set" using C by (metis Fractions_cases)
  from A' B' C' have [simp]:
    "a \<in> R" "b \<in> R" "c \<in> R" "d \<in> R" "e \<in> R" "f \<in> R"
    "b \<noteq> \<zero>" "d \<noteq> \<zero>" "f \<noteq> \<zero>" by auto
  have BC_in: "(c \<cdot> f + e \<cdot> d, d \<cdot> f) \<in> frac_set"
    using frac_mult_denom_nonzero[of d f] by (auto intro!: frac_setI)
  have BA_in: "(c \<cdot> a, d \<cdot> b) \<in> frac_set"
    using frac_mult_denom_nonzero[of d b] by (auto intro!: frac_setI)
  have CA_in: "(e \<cdot> a, f \<cdot> b) \<in> frac_set"
    using frac_mult_denom_nonzero[of f b] by (auto intro!: frac_setI)
  have "(B [+] C) [\<cdot>] A = frac.Class ((c \<cdot> f + e \<cdot> d) \<cdot> a, (d \<cdot> f) \<cdot> b)"
    using A' B' C' by (simp add: frac_add_Class[OF B'(2) C'(2)] frac_mult_Class[OF BC_in A'(2)])
  moreover have "B [\<cdot>] A [+] C [\<cdot>] A =
                   frac.Class ((c \<cdot> a) \<cdot> (f \<cdot> b) + (e \<cdot> a) \<cdot> (d \<cdot> b), (d \<cdot> b) \<cdot> (f \<cdot> b))"
    using A' B' C'
    by (simp add: frac_mult_Class[OF B'(2) A'(2)] frac_mult_Class[OF C'(2) A'(2)]
                  frac_add_Class[OF BA_in CA_in])
  moreover have
    "((c \<cdot> f + e \<cdot> d) \<cdot> a) \<cdot> ((d \<cdot> b) \<cdot> (f \<cdot> b)) =
     ((c \<cdot> a) \<cdot> (f \<cdot> b) + (e \<cdot> a) \<cdot> (d \<cdot> b)) \<cdot> ((d \<cdot> f) \<cdot> b)"
  proof -
    have "(c \<cdot> f + e \<cdot> d) \<cdot> a = (c \<cdot> f) \<cdot> a + (e \<cdot> d) \<cdot> a" by (simp add: distributive)
    then have L: "((c \<cdot> f + e \<cdot> d) \<cdot> a) \<cdot> ((d \<cdot> b) \<cdot> (f \<cdot> b))
                   = ((c \<cdot> f) \<cdot> a) \<cdot> ((d \<cdot> b) \<cdot> (f \<cdot> b)) + ((e \<cdot> d) \<cdot> a) \<cdot> ((d \<cdot> b) \<cdot> (f \<cdot> b))"
      by (simp add: distributive)
    have "((c \<cdot> a) \<cdot> (f \<cdot> b) + (e \<cdot> a) \<cdot> (d \<cdot> b)) \<cdot> ((d \<cdot> f) \<cdot> b)
            = (c \<cdot> a) \<cdot> (f \<cdot> b) \<cdot> ((d \<cdot> f) \<cdot> b) + (e \<cdot> a) \<cdot> (d \<cdot> b) \<cdot> ((d \<cdot> f) \<cdot> b)"
      by (simp add: distributive)
    also have "(c \<cdot> a) \<cdot> (f \<cdot> b) \<cdot> ((d \<cdot> f) \<cdot> b) = ((c \<cdot> f) \<cdot> a) \<cdot> ((d \<cdot> b) \<cdot> (f \<cdot> b))"
      by (simp add: mult_ac)
    also have "(e \<cdot> a) \<cdot> (d \<cdot> b) \<cdot> ((d \<cdot> f) \<cdot> b) = ((e \<cdot> d) \<cdot> a) \<cdot> ((d \<cdot> b) \<cdot> (f \<cdot> b))"
      by (simp add: mult_ac)
    finally show ?thesis using L by simp
  qed
  moreover have "((c \<cdot> f + e \<cdot> d) \<cdot> a, (d \<cdot> f) \<cdot> b) \<in> frac_set"
    using frac_mult_denom_nonzero[of d f] frac_mult_denom_nonzero[of "d \<cdot> f" b]
    by (auto intro!: frac_setI)
  moreover have "((c \<cdot> a) \<cdot> (f \<cdot> b) + (e \<cdot> a) \<cdot> (d \<cdot> b), (d \<cdot> b) \<cdot> (f \<cdot> b)) \<in> frac_set"
    using frac_mult_denom_nonzero[of d b] frac_mult_denom_nonzero[of f b]
          frac_mult_denom_nonzero[of "d \<cdot> b" "f \<cdot> b"]
    by (auto intro!: frac_setI)
  ultimately show "(B [+] C) [\<cdot>] A = B [\<cdot>] A [+] C [\<cdot>] A"
    by (metis frac_eqI)
qed


text \<open>Assemble the additive abelian group, multiplicative monoid, and the distributive laws into
  the @{locale Ring} interpretation.\<close>
interpretation Frac: Ring Fractions "([+])" "([\<cdot>])" "[\<zero>]" "[\<one>]"
  by (rule Ring.intro[OF Frac_abelian_group Frac_mult_monoid Frac_Ring_axioms])


interpretation Frac: commutative_ring Fractions "([+])" "([\<cdot>])" "[\<zero>]" "[\<one>]"
proof
  fix A B assume A: "A \<in> Fractions" and B: "B \<in> Fractions"
  obtain a b where A': "A = frac.Class (a, b)" "(a, b) \<in> frac_set" using A by (metis Fractions_cases)
  obtain c d where B': "B = frac.Class (c, d)" "(c, d) \<in> frac_set" using B by (metis Fractions_cases)
  from A' B' have [simp]: "a \<in> R" "b \<in> R" "c \<in> R" "d \<in> R" "b \<noteq> \<zero>" "d \<noteq> \<zero>" by auto
  have "A [\<cdot>] B = frac.Class (a \<cdot> c, b \<cdot> d)"
    using A' B' by (simp add: frac_mult_Class[OF A'(2) B'(2)])
  moreover have "B [\<cdot>] A = frac.Class (c \<cdot> a, d \<cdot> b)"
    using A' B' by (simp add: frac_mult_Class[OF B'(2) A'(2)])
  moreover have "a \<cdot> c = c \<cdot> a" by (simp add: mult_ac)
  moreover have "b \<cdot> d = d \<cdot> b" by (simp add: mult_ac)
  ultimately show "A [\<cdot>] B = B [\<cdot>] A" by simp
qed


interpretation Frac: Field Fractions "([+])" "([\<cdot>])" "[\<zero>]" "[\<one>]"
proof
  \<comment> \<open>Nontrivial.\<close>
  show "[\<one>] \<noteq> [\<zero>]" using frac_one_neq_zero .
next
  \<comment> \<open>Every nonzero class is invertible.\<close>
  fix A assume A: "A \<in> Fractions" and Anz: "A \<noteq> [\<zero>]"
  obtain a b where A': "A = frac.Class (a, b)" "(a, b) \<in> frac_set" using A by (metis Fractions_cases)
  from A' have abR: "a \<in> R" "b \<in> R" and bnz: "b \<noteq> \<zero>" by auto
  have anz: "a \<noteq> \<zero>" using Anz A' frac_Class_zero_iff[OF A'(2)] by blast
  have inv_in: "(b, a) \<in> frac_set" using abR anz by (auto intro!: frac_setI)
  have inv_class: "frac_inv A = frac.Class (b, a)"
    using A' by (simp add: frac_inv_Class[OF A'(2) anz])
  have "A [\<cdot>] frac_inv A = frac.Class (a \<cdot> b, b \<cdot> a)"
    using A' inv_class by (simp add: frac_mult_Class[OF A'(2) inv_in])
  moreover have "frac.Class (a \<cdot> b, b \<cdot> a) = [\<one>]"
  proof -
    have "(a \<cdot> b, b \<cdot> a) \<in> frac_set"
      using abR anz bnz frac_mult_denom_nonzero[of b a] by (auto intro!: frac_setI)
    moreover have "(\<one>, \<one>) \<in> frac_set" by (auto simp: nontrivial)
    moreover have "(a \<cdot> b) \<cdot> \<one> = \<one> \<cdot> (b \<cdot> a)" using abR by (simp add: mult_ac)
    ultimately show ?thesis by (rule frac_eqI)
  qed
  ultimately have right_inv: "A [\<cdot>] frac_inv A = [\<one>]" by simp

  have "frac_inv A [\<cdot>] A = frac.Class (b \<cdot> a, a \<cdot> b)"
    using A' inv_class by (simp add: frac_mult_Class[OF inv_in A'(2)])
  moreover have "frac.Class (b \<cdot> a, a \<cdot> b) = [\<one>]"
  proof -
    have "(b \<cdot> a, a \<cdot> b) \<in> frac_set"
      using abR anz bnz frac_mult_denom_nonzero[of a b] by (auto intro!: frac_setI)
    moreover have "(\<one>, \<one>) \<in> frac_set" by (auto simp: nontrivial)
    moreover have "(b \<cdot> a) \<cdot> \<one> = \<one> \<cdot> (a \<cdot> b)" using abR by (simp add: mult_ac)
    ultimately show ?thesis by (rule frac_eqI)
  qed
  ultimately have left_inv: "frac_inv A [\<cdot>] A = [\<one>]" by simp

  have inv_in_carrier: "frac_inv A \<in> Fractions" using inv_class inv_in by simp
  show "Frac.multiplicative.invertible A" using right_inv left_inv A inv_in_carrier
    by (blast intro: Frac.multiplicative.invertibleI)
qed


subsection \<open>The canonical embedding \<open>R \<rightarrow> Fractions\<close>\<close>

text \<open>The canonical map \<open>a \<mapsto> \<open>Class(a, \<one>)\<close>\<close> embeds \<open>R\<close> into its field of fractions.  It is an
  injective ring homomorphism.  Together with the field structure, this is the universal
  embedding of an integral domain into a field: every nonzero element of \<open>R\<close> acquires a
  multiplicative inverse in \<open>Fractions\<close>.\<close>

definition to_frac :: "'a \<Rightarrow> ('a \<times> 'a) set"
  where "to_frac = (\<lambda>a \<in> R. frac.Class (a, \<one>))"

lemma to_frac_apply [simp]: "a \<in> R \<Longrightarrow> to_frac a = frac.Class (a, \<one>)"
  unfolding to_frac_def by simp

lemma to_frac_undefined [simp]: "a \<notin> R \<Longrightarrow> to_frac a = undefined"
  unfolding to_frac_def by simp

lemma to_frac_pair: "a \<in> R \<Longrightarrow> (a, \<one>) \<in> frac_set"
  by (auto intro!: frac_setI simp: nontrivial)

lemma to_frac_in_Fractions [intro, simp]: "a \<in> R \<Longrightarrow> to_frac a \<in> Fractions"
  using to_frac_pair by (simp add: to_frac_apply)

lemma to_frac_zero: "to_frac \<zero> = [\<zero>]"  by simp
lemma to_frac_one:  "to_frac \<one> = [\<one>]"   by simp

lemma to_frac_add:
  assumes a: "a \<in> R" and b: "b \<in> R"
  shows "to_frac (a + b) = to_frac a [+] to_frac b"
proof -
  have "to_frac a [+] to_frac b = frac.Class (a \<cdot> \<one> + b \<cdot> \<one>, \<one> \<cdot> \<one>)"
    using a b by (simp add: frac_add_Class[OF to_frac_pair[OF a] to_frac_pair[OF b]])
  also have "\<dots> = frac.Class (a + b, \<one>)" using a b by simp
  finally show ?thesis using a b by simp
qed

lemma to_frac_mult:
  assumes a: "a \<in> R" and b: "b \<in> R"
  shows "to_frac (a \<cdot> b) = to_frac a [\<cdot>] to_frac b"
proof -
  have "to_frac a [\<cdot>] to_frac b = frac.Class (a \<cdot> b, \<one> \<cdot> \<one>)"
    using a b by (simp add: frac_mult_Class[OF to_frac_pair[OF a] to_frac_pair[OF b]])
  also have "\<dots> = frac.Class (a \<cdot> b, \<one>)" by simp
  finally show ?thesis using a b by simp
qed

lemma to_frac_inj:
  assumes a: "a \<in> R" and b: "b \<in> R" and eq: "to_frac a = to_frac b"
  shows "a = b"
proof -
  have "a \<cdot> \<one> = b \<cdot> \<one>"
    by (rule frac_eqD[OF to_frac_pair[OF a] to_frac_pair[OF b]]) (use eq a b in simp)
  with a b show ?thesis by simp
qed

interpretation to_frac: ring_homomorphism to_frac R "(+)" "(\<cdot>)" \<zero> \<one>
                                                Fractions "([+])" "([\<cdot>])" "[\<zero>]" "[\<one>]"
proof
  have "\<And>x. x \<in> R \<Longrightarrow> to_frac x \<in> Fractions" by (rule to_frac_in_Fractions)
  moreover have "\<And>x. x \<notin> R \<Longrightarrow> to_frac x = undefined" by (rule to_frac_undefined)
  ultimately show "to_frac \<in> R \<rightarrow>\<^sub>E Fractions"
    unfolding PiE_def extensional_def by blast
next
  fix a b assume "a \<in> R" "b \<in> R"
  then show "to_frac (a + b) = to_frac a [+] to_frac b" by (rule to_frac_add)
  from \<open>a \<in> R\<close> \<open>b \<in> R\<close> show "to_frac (a \<cdot> b) = to_frac a [\<cdot>] to_frac b" by (rule to_frac_mult)
next
  show "to_frac \<zero> = [\<zero>]" by (rule to_frac_zero)
  show "to_frac \<one> = [\<one>]" by (rule to_frac_one)
qed

end

end
