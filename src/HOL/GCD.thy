(*  Title:      HOL/GCD.thy
    Author:     Christophe Tabacznyj
    Author:     Lawrence C. Paulson
    Author:     Amine Chaieb
    Author:     Thomas M. Rasmussen
    Author:     Jeremy Avigad
    Author:     Tobias Nipkow

This file deals with the functions gcd and lcm.  Definitions and
lemmas are proved uniformly for the natural numbers and integers.

This file combines and revises a number of prior developments.

The original theories "GCD" and "Primes" were by Christophe Tabacznyj
and Lawrence C. Paulson, based on @{cite davenport92}. They introduced
gcd, lcm, and prime for the natural numbers.

The original theory "IntPrimes" was by Thomas M. Rasmussen, and
extended gcd, lcm, primes to the integers. Amine Chaieb provided
another extension of the notions to the integers, and added a number
of results to "Primes" and "GCD". IntPrimes also defined and developed
the congruence relations on the integers. The notion was extended to
the natural numbers by Chaieb.

Jeremy Avigad combined all of these, made everything uniform for the
natural numbers and the integers, and added a number of new theorems.

Tobias Nipkow cleaned up a lot.
*)

section \<open>Greatest common divisor and least common multiple\<close>

theory GCD
  imports Groups_List 
begin

subsection \<open>Abstract bounded quasi semilattices as common foundation\<close>

locale bounded_quasi_semilattice = abel_semigroup +
  fixes top :: 'a  ("\<^bold>\<top>") and bot :: 'a  ("\<^bold>\<bottom>")
    and normalize :: "'a \<Rightarrow> 'a"
  assumes idem_normalize [simp]: "a \<^bold>* a = normalize a"
    and normalize_left_idem [simp]: "normalize a \<^bold>* b = a \<^bold>* b"
    and normalize_idem [simp]: "normalize (a \<^bold>* b) = a \<^bold>* b"
    and normalize_top [simp]: "normalize \<^bold>\<top> = \<^bold>\<top>"
    and normalize_bottom [simp]: "normalize \<^bold>\<bottom> = \<^bold>\<bottom>"
    and top_left_normalize [simp]: "\<^bold>\<top> \<^bold>* a = normalize a"
    and bottom_left_bottom [simp]: "\<^bold>\<bottom> \<^bold>* a = \<^bold>\<bottom>"
begin

lemma left_idem [simp]:
  "a \<^bold>* (a \<^bold>* b) = a \<^bold>* b"
  using assoc [of a a b, symmetric] by simp

lemma right_idem [simp]:
  "(a \<^bold>* b) \<^bold>* b = a \<^bold>* b"
  using left_idem [of b a] by (simp add: ac_simps)

lemma comp_fun_idem: "comp_fun_idem f"
  by standard (simp_all add: fun_eq_iff ac_simps)

interpretation comp_fun_idem f
  by (fact comp_fun_idem)

lemma top_right_normalize [simp]:
  "a \<^bold>* \<^bold>\<top> = normalize a"
  using top_left_normalize [of a] by (simp add: ac_simps)

lemma bottom_right_bottom [simp]:
  "a \<^bold>* \<^bold>\<bottom> = \<^bold>\<bottom>"
  using bottom_left_bottom [of a] by (simp add: ac_simps)

lemma normalize_right_idem [simp]:
  "a \<^bold>* normalize b = a \<^bold>* b"
  using normalize_left_idem [of b a] by (simp add: ac_simps)

end

locale bounded_quasi_semilattice_set = bounded_quasi_semilattice
begin

interpretation comp_fun_idem f
  by (fact comp_fun_idem)

definition F :: "'a set \<Rightarrow> 'a"
where
  eq_fold: "F A = (if finite A then Finite_Set.fold f \<^bold>\<top> A else \<^bold>\<bottom>)"

lemma infinite [simp]:
  "infinite A \<Longrightarrow> F A = \<^bold>\<bottom>"
  by (simp add: eq_fold)

lemma set_eq_fold [code]:
  "F (set xs) = fold f xs \<^bold>\<top>"
  by (simp add: eq_fold fold_set_fold)

lemma empty [simp]:
  "F {} = \<^bold>\<top>"
  by (simp add: eq_fold)

lemma insert [simp]:
  "F (insert a A) = a \<^bold>* F A"
  by (cases "finite A") (simp_all add: eq_fold)

lemma normalize [simp]:
  "normalize (F A) = F A"
  by (induct A rule: infinite_finite_induct) simp_all

lemma in_idem:
  assumes "a \<in> A"
  shows "a \<^bold>* F A = F A"
  using assms by (induct A rule: infinite_finite_induct)
    (auto simp: left_commute [of a])

lemma union:
  "F (A \<union> B) = F A \<^bold>* F B"
  by (induct A rule: infinite_finite_induct)
    (simp_all add: ac_simps)

lemma remove:
  assumes "a \<in> A"
  shows "F A = a \<^bold>* F (A - {a})"
proof -
  from assms obtain B where "A = insert a B" and "a \<notin> B"
    by (blast dest: mk_disjoint_insert)
  with assms show ?thesis by simp
qed

lemma insert_remove:
  "F (insert a A) = a \<^bold>* F (A - {a})"
  by (cases "a \<in> A") (simp_all add: insert_absorb remove)

lemma subset:
  assumes "B \<subseteq> A"
  shows "F B \<^bold>* F A = F A"
  using assms by (simp add: union [symmetric] Un_absorb1)

end

subsection \<open>Abstract GCD and LCM\<close>

class gcd = zero + one + dvd +
  fixes gcd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and lcm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

class Gcd = gcd +
  fixes Gcd :: "'a set \<Rightarrow> 'a"
    and Lcm :: "'a set \<Rightarrow> 'a"

syntax
  "_GCD1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3GCD _./ _)" [0, 10] 10)
  "_GCD"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3GCD _\<in>_./ _)" [0, 0, 10] 10)
  "_LCM1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3LCM _./ _)" [0, 10] 10)
  "_LCM"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3LCM _\<in>_./ _)" [0, 0, 10] 10)

translations
  "GCD x y. f"   \<rightleftharpoons> "GCD x. GCD y. f"
  "GCD x. f"     \<rightleftharpoons> "CONST Gcd (CONST range (\<lambda>x. f))"
  "GCD x\<in>A. f"   \<rightleftharpoons> "CONST Gcd ((\<lambda>x. f) ` A)"
  "LCM x y. f"   \<rightleftharpoons> "LCM x. LCM y. f"
  "LCM x. f"     \<rightleftharpoons> "CONST Lcm (CONST range (\<lambda>x. f))"
  "LCM x\<in>A. f"   \<rightleftharpoons> "CONST Lcm ((\<lambda>x. f) ` A)"

class semiring_gcd = normalization_semidom + gcd +
  assumes gcd_dvd1 [iff]: "gcd a b dvd a"
    and gcd_dvd2 [iff]: "gcd a b dvd b"
    and gcd_greatest: "c dvd a \<Longrightarrow> c dvd b \<Longrightarrow> c dvd gcd a b"
    and normalize_gcd [simp]: "normalize (gcd a b) = gcd a b"
    and lcm_gcd: "lcm a b = normalize (a * b div gcd a b)"
begin

lemma gcd_greatest_iff [simp]: "a dvd gcd b c \<longleftrightarrow> a dvd b \<and> a dvd c"
  by (blast intro!: gcd_greatest intro: dvd_trans)

lemma gcd_dvdI1: "a dvd c \<Longrightarrow> gcd a b dvd c"
  by (rule dvd_trans) (rule gcd_dvd1)

lemma gcd_dvdI2: "b dvd c \<Longrightarrow> gcd a b dvd c"
  by (rule dvd_trans) (rule gcd_dvd2)

lemma dvd_gcdD1: "a dvd gcd b c \<Longrightarrow> a dvd b"
  using gcd_dvd1 [of b c] by (blast intro: dvd_trans)

lemma dvd_gcdD2: "a dvd gcd b c \<Longrightarrow> a dvd c"
  using gcd_dvd2 [of b c] by (blast intro: dvd_trans)

lemma gcd_0_left [simp]: "gcd 0 a = normalize a"
  by (rule associated_eqI) simp_all

lemma gcd_0_right [simp]: "gcd a 0 = normalize a"
  by (rule associated_eqI) simp_all

lemma gcd_eq_0_iff [simp]: "gcd a b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  then have "0 dvd gcd a b"
    by simp
  then have "0 dvd a" and "0 dvd b"
    by (blast intro: dvd_trans)+
  then show ?Q
    by simp
next
  assume ?Q
  then show ?P
    by simp
qed

lemma unit_factor_gcd: "unit_factor (gcd a b) = (if a = 0 \<and> b = 0 then 0 else 1)"
proof (cases "gcd a b = 0")
  case True
  then show ?thesis by simp
next
  case False
  have "unit_factor (gcd a b) * normalize (gcd a b) = gcd a b"
    by (rule unit_factor_mult_normalize)
  then have "unit_factor (gcd a b) * gcd a b = gcd a b"
    by simp
  then have "unit_factor (gcd a b) * gcd a b div gcd a b = gcd a b div gcd a b"
    by simp
  with False show ?thesis
    by simp
qed

lemma is_unit_gcd_iff [simp]:
  "is_unit (gcd a b) \<longleftrightarrow> gcd a b = 1"
  by (cases "a = 0 \<and> b = 0") (auto simp: unit_factor_gcd dest: is_unit_unit_factor)

sublocale gcd: abel_semigroup gcd
proof
  fix a b c
  show "gcd a b = gcd b a"
    by (rule associated_eqI) simp_all
  from gcd_dvd1 have "gcd (gcd a b) c dvd a"
    by (rule dvd_trans) simp
  moreover from gcd_dvd1 have "gcd (gcd a b) c dvd b"
    by (rule dvd_trans) simp
  ultimately have P1: "gcd (gcd a b) c dvd gcd a (gcd b c)"
    by (auto intro!: gcd_greatest)
  from gcd_dvd2 have "gcd a (gcd b c) dvd b"
    by (rule dvd_trans) simp
  moreover from gcd_dvd2 have "gcd a (gcd b c) dvd c"
    by (rule dvd_trans) simp
  ultimately have P2: "gcd a (gcd b c) dvd gcd (gcd a b) c"
    by (auto intro!: gcd_greatest)
  from P1 P2 show "gcd (gcd a b) c = gcd a (gcd b c)"
    by (rule associated_eqI) simp_all
qed

sublocale gcd: bounded_quasi_semilattice gcd 0 1 normalize
proof
  show "gcd a a = normalize a" for a
  proof -
    have "a dvd gcd a a"
      by (rule gcd_greatest) simp_all
    then show ?thesis
      by (auto intro: associated_eqI)
  qed
  show "gcd (normalize a) b = gcd a b" for a b
    using gcd_dvd1 [of "normalize a" b]
    by (auto intro: associated_eqI)
  show "gcd 1 a = 1" for a
    by (rule associated_eqI) simp_all
qed simp_all

lemma gcd_self: "gcd a a = normalize a"
  by (fact gcd.idem_normalize)

lemma gcd_left_idem: "gcd a (gcd a b) = gcd a b"
  by (fact gcd.left_idem)

lemma gcd_right_idem: "gcd (gcd a b) b = gcd a b"
  by (fact gcd.right_idem)

lemma gcdI:
  assumes "c dvd a" and "c dvd b"
    and greatest: "\<And>d. d dvd a \<Longrightarrow> d dvd b \<Longrightarrow> d dvd c"
    and "normalize c = c"
  shows "c = gcd a b"
  by (rule associated_eqI) (auto simp: assms intro: gcd_greatest)

lemma gcd_unique:
  "d dvd a \<and> d dvd b \<and> normalize d = d \<and> (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  by rule (auto intro: gcdI simp: gcd_greatest)

lemma gcd_dvd_prod: "gcd a b dvd k * b"
  using mult_dvd_mono [of 1] by auto

lemma gcd_proj2_if_dvd: "b dvd a \<Longrightarrow> gcd a b = normalize b"
  by (rule gcdI [symmetric]) simp_all

lemma gcd_proj1_if_dvd: "a dvd b \<Longrightarrow> gcd a b = normalize a"
  by (rule gcdI [symmetric]) simp_all

lemma gcd_proj1_iff: "gcd m n = normalize m \<longleftrightarrow> m dvd n"
proof
  assume *: "gcd m n = normalize m"
  show "m dvd n"
  proof (cases "m = 0")
    case True
    with * show ?thesis by simp
  next
    case [simp]: False
    from * have **: "m = gcd m n * unit_factor m"
      by (simp add: unit_eq_div2)
    show ?thesis
      by (subst **) (simp add: mult_unit_dvd_iff)
  qed
next
  assume "m dvd n"
  then show "gcd m n = normalize m"
    by (rule gcd_proj1_if_dvd)
qed

lemma gcd_proj2_iff: "gcd m n = normalize n \<longleftrightarrow> n dvd m"
  using gcd_proj1_iff [of n m] by (simp add: ac_simps)

lemma gcd_mult_left: "gcd (c * a) (c * b) = normalize (c * gcd a b)"
proof (cases "c = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have *: "c * gcd a b dvd gcd (c * a) (c * b)"
    by (auto intro: gcd_greatest)
  moreover from False * have "gcd (c * a) (c * b) dvd c * gcd a b"
    by (metis div_dvd_iff_mult dvd_mult_left gcd_dvd1 gcd_dvd2 gcd_greatest mult_commute)
  ultimately have "normalize (gcd (c * a) (c * b)) = normalize (c * gcd a b)"
    by (auto intro: associated_eqI)
  then show ?thesis
    by (simp add: normalize_mult)
qed

lemma gcd_mult_right: "gcd (a * c) (b * c) = normalize (gcd b a * c)"
  using gcd_mult_left [of c a b] by (simp add: ac_simps)

lemma dvd_lcm1 [iff]: "a dvd lcm a b"
  by (metis div_mult_swap dvd_mult2 dvd_normalize_iff dvd_refl gcd_dvd2 lcm_gcd)

lemma dvd_lcm2 [iff]: "b dvd lcm a b"
  by (metis dvd_div_mult dvd_mult dvd_normalize_iff dvd_refl gcd_dvd1 lcm_gcd)

lemma dvd_lcmI1: "a dvd b \<Longrightarrow> a dvd lcm b c"
  by (rule dvd_trans) (assumption, blast)

lemma dvd_lcmI2: "a dvd c \<Longrightarrow> a dvd lcm b c"
  by (rule dvd_trans) (assumption, blast)

lemma lcm_dvdD1: "lcm a b dvd c \<Longrightarrow> a dvd c"
  using dvd_lcm1 [of a b] by (blast intro: dvd_trans)

lemma lcm_dvdD2: "lcm a b dvd c \<Longrightarrow> b dvd c"
  using dvd_lcm2 [of a b] by (blast intro: dvd_trans)

lemma lcm_least:
  assumes "a dvd c" and "b dvd c"
  shows "lcm a b dvd c"
proof (cases "c = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have *: "is_unit (unit_factor c)"
    by simp
  show ?thesis
  proof (cases "gcd a b = 0")
    case True
    with assms show ?thesis by simp
  next
    case False
    have "a * b dvd normalize (c * gcd a b)"
      using assms by (subst gcd_mult_left [symmetric]) (auto intro!: gcd_greatest simp: mult_ac)
    with False have "(a * b div gcd a b) dvd c"
      by (subst div_dvd_iff_mult) auto
    thus ?thesis by (simp add: lcm_gcd)
  qed
qed

lemma lcm_least_iff [simp]: "lcm a b dvd c \<longleftrightarrow> a dvd c \<and> b dvd c"
  by (blast intro!: lcm_least intro: dvd_trans)

lemma normalize_lcm [simp]: "normalize (lcm a b) = lcm a b"
  by (simp add: lcm_gcd dvd_normalize_div)

lemma lcm_0_left [simp]: "lcm 0 a = 0"
  by (simp add: lcm_gcd)

lemma lcm_0_right [simp]: "lcm a 0 = 0"
  by (simp add: lcm_gcd)

lemma lcm_eq_0_iff: "lcm a b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
  (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  then have "0 dvd lcm a b"
    by simp
  also have "lcm a b dvd (a * b)"
    by simp
  finally show ?Q
    by auto
next
  assume ?Q
  then show ?P
    by auto
qed

lemma zero_eq_lcm_iff: "0 = lcm a b \<longleftrightarrow> a = 0 \<or> b = 0"
  using lcm_eq_0_iff[of a b] by auto

lemma lcm_eq_1_iff [simp]: "lcm a b = 1 \<longleftrightarrow> is_unit a \<and> is_unit b"
  by (auto intro: associated_eqI)

lemma unit_factor_lcm: "unit_factor (lcm a b) = (if a = 0 \<or> b = 0 then 0 else 1)"
  using lcm_eq_0_iff[of a b] by (cases "lcm a b = 0") (auto simp: lcm_gcd)

sublocale lcm: abel_semigroup lcm
proof
  fix a b c
  show "lcm a b = lcm b a"
    by (simp add: lcm_gcd ac_simps normalize_mult dvd_normalize_div)
  have "lcm (lcm a b) c dvd lcm a (lcm b c)"
    and "lcm a (lcm b c) dvd lcm (lcm a b) c"
    by (auto intro: lcm_least
      dvd_trans [of b "lcm b c" "lcm a (lcm b c)"]
      dvd_trans [of c "lcm b c" "lcm a (lcm b c)"]
      dvd_trans [of a "lcm a b" "lcm (lcm a b) c"]
      dvd_trans [of b "lcm a b" "lcm (lcm a b) c"])
  then show "lcm (lcm a b) c = lcm a (lcm b c)"
    by (rule associated_eqI) simp_all
qed

sublocale lcm: bounded_quasi_semilattice lcm 1 0 normalize
proof
  show "lcm a a = normalize a" for a
  proof -
    have "lcm a a dvd a"
      by (rule lcm_least) simp_all
    then show ?thesis
      by (auto intro: associated_eqI)
  qed
  show "lcm (normalize a) b = lcm a b" for a b
    using dvd_lcm1 [of "normalize a" b] unfolding normalize_dvd_iff
    by (auto intro: associated_eqI)
  show "lcm 1 a = normalize a" for a
    by (rule associated_eqI) simp_all
qed simp_all

lemma lcm_self: "lcm a a = normalize a"
  by (fact lcm.idem_normalize)

lemma lcm_left_idem: "lcm a (lcm a b) = lcm a b"
  by (fact lcm.left_idem)

lemma lcm_right_idem: "lcm (lcm a b) b = lcm a b"
  by (fact lcm.right_idem)

lemma gcd_lcm:
  assumes "a \<noteq> 0" and "b \<noteq> 0"
  shows "gcd a b = normalize (a * b div lcm a b)"
proof -
  from assms have [simp]: "a * b div gcd a b \<noteq> 0"
    by (subst dvd_div_eq_0_iff) auto
  let ?u = "unit_factor (a * b div gcd a b)"
  have "gcd a b * normalize (a * b div gcd a b) =
          gcd a b * ((a * b div gcd a b) * (1 div ?u))"
    by simp
  also have "\<dots> = a * b div ?u"
    by (subst mult.assoc [symmetric]) auto
  also have "\<dots> dvd a * b"
    by (subst div_unit_dvd_iff) auto
  finally have "gcd a b dvd ((a * b) div lcm a b)"
    by (intro dvd_mult_imp_div) (auto simp: lcm_gcd)
  moreover have "a * b div lcm a b dvd a" and "a * b div lcm a b dvd b"
    using assms by (subst div_dvd_iff_mult; simp add: lcm_eq_0_iff mult.commute[of b "lcm a b"])+
  ultimately have "normalize (gcd a b) = normalize (a * b div lcm a b)"
    apply -
    apply (rule associated_eqI)
    using assms
    apply (auto simp: div_dvd_iff_mult zero_eq_lcm_iff)
    done
  thus ?thesis by simp
qed

lemma lcm_1_left: "lcm 1 a = normalize a"
  by (fact lcm.top_left_normalize)

lemma lcm_1_right: "lcm a 1 = normalize a"
  by (fact lcm.top_right_normalize)

lemma lcm_mult_left: "lcm (c * a) (c * b) = normalize (c * lcm a b)"
proof (cases "c = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have *: "lcm (c * a) (c * b) dvd c * lcm a b"
    by (auto intro: lcm_least)
  moreover have "lcm a b dvd lcm (c * a) (c * b) div c"
    by (intro lcm_least) (auto intro!: dvd_mult_imp_div simp: mult_ac)
  hence "c * lcm a b dvd lcm (c * a) (c * b)"
    using False by (subst (asm) dvd_div_iff_mult) (auto simp: mult_ac intro: dvd_lcmI1)
  ultimately have "normalize (lcm (c * a) (c * b)) = normalize (c * lcm a b)"
    by (auto intro: associated_eqI)
  then show ?thesis
    by (simp add: normalize_mult)
qed

lemma lcm_mult_right: "lcm (a * c) (b * c) = normalize (lcm b a * c)"
  using lcm_mult_left [of c a b] by (simp add: ac_simps)

lemma lcm_mult_unit1: "is_unit a \<Longrightarrow> lcm (b * a) c = lcm b c"
  by (rule associated_eqI) (simp_all add: mult_unit_dvd_iff dvd_lcmI1)

lemma lcm_mult_unit2: "is_unit a \<Longrightarrow> lcm b (c * a) = lcm b c"
  using lcm_mult_unit1 [of a c b] by (simp add: ac_simps)

lemma lcm_div_unit1:
  "is_unit a \<Longrightarrow> lcm (b div a) c = lcm b c"
  by (erule is_unitE [of _ b]) (simp add: lcm_mult_unit1)

lemma lcm_div_unit2: "is_unit a \<Longrightarrow> lcm b (c div a) = lcm b c"
  by (erule is_unitE [of _ c]) (simp add: lcm_mult_unit2)

lemma normalize_lcm_left: "lcm (normalize a) b = lcm a b"
  by (fact lcm.normalize_left_idem)

lemma normalize_lcm_right: "lcm a (normalize b) = lcm a b"
  by (fact lcm.normalize_right_idem)

lemma comp_fun_idem_gcd: "comp_fun_idem gcd"
  by standard (simp_all add: fun_eq_iff ac_simps)

lemma comp_fun_idem_lcm: "comp_fun_idem lcm"
  by standard (simp_all add: fun_eq_iff ac_simps)

lemma gcd_dvd_antisym: "gcd a b dvd gcd c d \<Longrightarrow> gcd c d dvd gcd a b \<Longrightarrow> gcd a b = gcd c d"
proof (rule gcdI)
  assume *: "gcd a b dvd gcd c d"
    and **: "gcd c d dvd gcd a b"
  have "gcd c d dvd c"
    by simp
  with * show "gcd a b dvd c"
    by (rule dvd_trans)
  have "gcd c d dvd d"
    by simp
  with * show "gcd a b dvd d"
    by (rule dvd_trans)
  show "normalize (gcd a b) = gcd a b"
    by simp
  fix l assume "l dvd c" and "l dvd d"
  then have "l dvd gcd c d"
    by (rule gcd_greatest)
  from this and ** show "l dvd gcd a b"
    by (rule dvd_trans)
qed

declare unit_factor_lcm [simp]

lemma lcmI:
  assumes "a dvd c" and "b dvd c" and "\<And>d. a dvd d \<Longrightarrow> b dvd d \<Longrightarrow> c dvd d"
    and "normalize c = c"
  shows "c = lcm a b"
  by (rule associated_eqI) (auto simp: assms intro: lcm_least)

lemma gcd_dvd_lcm [simp]: "gcd a b dvd lcm a b"
  using gcd_dvd2 by (rule dvd_lcmI2)

lemmas lcm_0 = lcm_0_right

lemma lcm_unique:
  "a dvd d \<and> b dvd d \<and> normalize d = d \<and> (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  by rule (auto intro: lcmI simp: lcm_least lcm_eq_0_iff)

lemma lcm_proj1_if_dvd:
  assumes "b dvd a" shows "lcm a b = normalize a"
proof -
  have "normalize (lcm a b) = normalize a"
    by (rule associatedI) (use assms in auto)
  thus ?thesis by simp
qed

lemma lcm_proj2_if_dvd: "a dvd b \<Longrightarrow> lcm a b = normalize b"
  using lcm_proj1_if_dvd [of a b] by (simp add: ac_simps)

lemma lcm_proj1_iff: "lcm m n = normalize m \<longleftrightarrow> n dvd m"
proof
  assume *: "lcm m n = normalize m"
  show "n dvd m"
  proof (cases "m = 0")
    case True
    then show ?thesis by simp
  next
    case [simp]: False
    from * have **: "m = lcm m n * unit_factor m"
      by (simp add: unit_eq_div2)
    show ?thesis by (subst **) simp
  qed
next
  assume "n dvd m"
  then show "lcm m n = normalize m"
    by (rule lcm_proj1_if_dvd)
qed

lemma lcm_proj2_iff: "lcm m n = normalize n \<longleftrightarrow> m dvd n"
  using lcm_proj1_iff [of n m] by (simp add: ac_simps)

lemma gcd_mono: "a dvd c \<Longrightarrow> b dvd d \<Longrightarrow> gcd a b dvd gcd c d"
  by (simp add: gcd_dvdI1 gcd_dvdI2)

lemma lcm_mono: "a dvd c \<Longrightarrow> b dvd d \<Longrightarrow> lcm a b dvd lcm c d"
  by (simp add: dvd_lcmI1 dvd_lcmI2)

lemma dvd_productE:
  assumes "p dvd a * b"
  obtains x y where "p = x * y" "x dvd a" "y dvd b"
proof (cases "a = 0")
  case True
  thus ?thesis by (intro that[of p 1]) simp_all
next
  case False
  define x y where "x = gcd a p" and "y = p div x"
  have "p = x * y" by (simp add: x_def y_def)
  moreover have "x dvd a" by (simp add: x_def)
  moreover from assms have "p dvd gcd (b * a) (b * p)"
    by (intro gcd_greatest) (simp_all add: mult.commute)
  hence "p dvd b * gcd a p" by (subst (asm) gcd_mult_left) auto
  with False have "y dvd b"
    by (simp add: x_def y_def div_dvd_iff_mult assms)
  ultimately show ?thesis by (rule that)
qed

lemma gcd_mult_unit1: 
  assumes "is_unit a" shows "gcd (b * a) c = gcd b c"
proof -
  have "gcd (b * a) c dvd b"
    using assms dvd_mult_unit_iff by blast
  then show ?thesis
    by (rule gcdI) simp_all
qed

lemma gcd_mult_unit2: "is_unit a \<Longrightarrow> gcd b (c * a) = gcd b c"
  using gcd.commute gcd_mult_unit1 by auto

lemma gcd_div_unit1: "is_unit a \<Longrightarrow> gcd (b div a) c = gcd b c"
  by (erule is_unitE [of _ b]) (simp add: gcd_mult_unit1)

lemma gcd_div_unit2: "is_unit a \<Longrightarrow> gcd b (c div a) = gcd b c"
  by (erule is_unitE [of _ c]) (simp add: gcd_mult_unit2)

lemma normalize_gcd_left: "gcd (normalize a) b = gcd a b"
  by (fact gcd.normalize_left_idem)

lemma normalize_gcd_right: "gcd a (normalize b) = gcd a b"
  by (fact gcd.normalize_right_idem)

lemma gcd_add1 [simp]: "gcd (m + n) n = gcd m n"
  by (rule gcdI [symmetric]) (simp_all add: dvd_add_left_iff)

lemma gcd_add2 [simp]: "gcd m (m + n) = gcd m n"
  using gcd_add1 [of n m] by (simp add: ac_simps)

lemma gcd_add_mult: "gcd m (k * m + n) = gcd m n"
  by (rule gcdI [symmetric]) (simp_all add: dvd_add_right_iff)

end

class ring_gcd = comm_ring_1 + semiring_gcd
begin

lemma gcd_neg1 [simp]: "gcd (-a) b = gcd a b"
  by (rule sym, rule gcdI) (simp_all add: gcd_greatest)

lemma gcd_neg2 [simp]: "gcd a (-b) = gcd a b"
  by (rule sym, rule gcdI) (simp_all add: gcd_greatest)

lemma gcd_neg_numeral_1 [simp]: "gcd (- numeral n) a = gcd (numeral n) a"
  by (fact gcd_neg1)

lemma gcd_neg_numeral_2 [simp]: "gcd a (- numeral n) = gcd a (numeral n)"
  by (fact gcd_neg2)

lemma gcd_diff1: "gcd (m - n) n = gcd m n"
  by (subst diff_conv_add_uminus, subst gcd_neg2[symmetric], subst gcd_add1, simp)

lemma gcd_diff2: "gcd (n - m) n = gcd m n"
  by (subst gcd_neg1[symmetric]) (simp only: minus_diff_eq gcd_diff1)

lemma lcm_neg1 [simp]: "lcm (-a) b = lcm a b"
  by (rule sym, rule lcmI) (simp_all add: lcm_least lcm_eq_0_iff)

lemma lcm_neg2 [simp]: "lcm a (-b) = lcm a b"
  by (rule sym, rule lcmI) (simp_all add: lcm_least lcm_eq_0_iff)

lemma lcm_neg_numeral_1 [simp]: "lcm (- numeral n) a = lcm (numeral n) a"
  by (fact lcm_neg1)

lemma lcm_neg_numeral_2 [simp]: "lcm a (- numeral n) = lcm a (numeral n)"
  by (fact lcm_neg2)

end

class semiring_Gcd = semiring_gcd + Gcd +
  assumes Gcd_dvd: "a \<in> A \<Longrightarrow> Gcd A dvd a"
    and Gcd_greatest: "(\<And>b. b \<in> A \<Longrightarrow> a dvd b) \<Longrightarrow> a dvd Gcd A"
    and normalize_Gcd [simp]: "normalize (Gcd A) = Gcd A"
  assumes dvd_Lcm: "a \<in> A \<Longrightarrow> a dvd Lcm A"
    and Lcm_least: "(\<And>b. b \<in> A \<Longrightarrow> b dvd a) \<Longrightarrow> Lcm A dvd a"
    and normalize_Lcm [simp]: "normalize (Lcm A) = Lcm A"
begin

lemma Lcm_Gcd: "Lcm A = Gcd {b. \<forall>a\<in>A. a dvd b}"
  by (rule associated_eqI) (auto intro: Gcd_dvd dvd_Lcm Gcd_greatest Lcm_least)

lemma Gcd_Lcm: "Gcd A = Lcm {b. \<forall>a\<in>A. b dvd a}"
  by (rule associated_eqI) (auto intro: Gcd_dvd dvd_Lcm Gcd_greatest Lcm_least)

lemma Gcd_empty [simp]: "Gcd {} = 0"
  by (rule dvd_0_left, rule Gcd_greatest) simp

lemma Lcm_empty [simp]: "Lcm {} = 1"
  by (auto intro: associated_eqI Lcm_least)

lemma Gcd_insert [simp]: "Gcd (insert a A) = gcd a (Gcd A)"
proof -
  have "Gcd (insert a A) dvd gcd a (Gcd A)"
    by (auto intro: Gcd_dvd Gcd_greatest)
  moreover have "gcd a (Gcd A) dvd Gcd (insert a A)"
  proof (rule Gcd_greatest)
    fix b
    assume "b \<in> insert a A"
    then show "gcd a (Gcd A) dvd b"
    proof
      assume "b = a"
      then show ?thesis
        by simp
    next
      assume "b \<in> A"
      then have "Gcd A dvd b"
        by (rule Gcd_dvd)
      moreover have "gcd a (Gcd A) dvd Gcd A"
        by simp
      ultimately show ?thesis
        by (blast intro: dvd_trans)
    qed
  qed
  ultimately show ?thesis
    by (auto intro: associated_eqI)
qed

lemma Lcm_insert [simp]: "Lcm (insert a A) = lcm a (Lcm A)"
proof (rule sym)
  have "lcm a (Lcm A) dvd Lcm (insert a A)"
    by (auto intro: dvd_Lcm Lcm_least)
  moreover have "Lcm (insert a A) dvd lcm a (Lcm A)"
  proof (rule Lcm_least)
    fix b
    assume "b \<in> insert a A"
    then show "b dvd lcm a (Lcm A)"
    proof
      assume "b = a"
      then show ?thesis by simp
    next
      assume "b \<in> A"
      then have "b dvd Lcm A"
        by (rule dvd_Lcm)
      moreover have "Lcm A dvd lcm a (Lcm A)"
        by simp
      ultimately show ?thesis
        by (blast intro: dvd_trans)
    qed
  qed
  ultimately show "lcm a (Lcm A) = Lcm (insert a A)"
    by (rule associated_eqI) (simp_all add: lcm_eq_0_iff)
qed

lemma LcmI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> a dvd b"
    and "\<And>c. (\<And>a. a \<in> A \<Longrightarrow> a dvd c) \<Longrightarrow> b dvd c"
    and "normalize b = b"
  shows "b = Lcm A"
  by (rule associated_eqI) (auto simp: assms dvd_Lcm intro: Lcm_least)

lemma Lcm_subset: "A \<subseteq> B \<Longrightarrow> Lcm A dvd Lcm B"
  by (blast intro: Lcm_least dvd_Lcm)

lemma Lcm_Un: "Lcm (A \<union> B) = lcm (Lcm A) (Lcm B)"
proof -
  have "\<And>d. \<lbrakk>Lcm A dvd d; Lcm B dvd d\<rbrakk> \<Longrightarrow> Lcm (A \<union> B) dvd d"
    by (meson UnE Lcm_least dvd_Lcm dvd_trans)
  then show ?thesis
    by (meson Lcm_subset lcm_unique normalize_Lcm sup.cobounded1 sup.cobounded2)
qed

lemma Gcd_0_iff [simp]: "Gcd A = 0 \<longleftrightarrow> A \<subseteq> {0}"
  (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  show ?Q
  proof
    fix a
    assume "a \<in> A"
    then have "Gcd A dvd a"
      by (rule Gcd_dvd)
    with \<open>?P\<close> have "a = 0"
      by simp
    then show "a \<in> {0}"
      by simp
  qed
next
  assume ?Q
  have "0 dvd Gcd A"
  proof (rule Gcd_greatest)
    fix a
    assume "a \<in> A"
    with \<open>?Q\<close> have "a = 0"
      by auto
    then show "0 dvd a"
      by simp
  qed
  then show ?P
    by simp
qed

lemma Lcm_1_iff [simp]: "Lcm A = 1 \<longleftrightarrow> (\<forall>a\<in>A. is_unit a)"
  (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  show ?Q
  proof
    fix a
    assume "a \<in> A"
    then have "a dvd Lcm A"
      by (rule dvd_Lcm)
    with \<open>?P\<close> show "is_unit a"
      by simp
  qed
next
  assume ?Q
  then have "is_unit (Lcm A)"
    by (blast intro: Lcm_least)
  then have "normalize (Lcm A) = 1"
    by (rule is_unit_normalize)
  then show ?P
    by simp
qed

lemma unit_factor_Lcm: "unit_factor (Lcm A) = (if Lcm A = 0 then 0 else 1)"
proof (cases "Lcm A = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  with unit_factor_normalize have "unit_factor (normalize (Lcm A)) = 1"
    by blast
  with False show ?thesis
    by simp
qed

lemma unit_factor_Gcd: "unit_factor (Gcd A) = (if Gcd A = 0 then 0 else 1)"
  by (simp add: Gcd_Lcm unit_factor_Lcm)

lemma GcdI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> b dvd a"
    and "\<And>c. (\<And>a. a \<in> A \<Longrightarrow> c dvd a) \<Longrightarrow> c dvd b"
    and "normalize b = b"
  shows "b = Gcd A"
  by (rule associated_eqI) (auto simp: assms Gcd_dvd intro: Gcd_greatest)

lemma Gcd_eq_1_I:
  assumes "is_unit a" and "a \<in> A"
  shows "Gcd A = 1"
proof -
  from assms have "is_unit (Gcd A)"
    by (blast intro: Gcd_dvd dvd_unit_imp_unit)
  then have "normalize (Gcd A) = 1"
    by (rule is_unit_normalize)
  then show ?thesis
    by simp
qed

lemma Lcm_eq_0_I:
  assumes "0 \<in> A"
  shows "Lcm A = 0"
proof -
  from assms have "0 dvd Lcm A"
    by (rule dvd_Lcm)
  then show ?thesis
    by simp
qed

lemma Gcd_UNIV [simp]: "Gcd UNIV = 1"
  using dvd_refl by (rule Gcd_eq_1_I) simp

lemma Lcm_UNIV [simp]: "Lcm UNIV = 0"
  by (rule Lcm_eq_0_I) simp

lemma Lcm_0_iff:
  assumes "finite A"
  shows "Lcm A = 0 \<longleftrightarrow> 0 \<in> A"
proof (cases "A = {}")
  case True
  then show ?thesis by simp
next
  case False
  with assms show ?thesis
    by (induct A rule: finite_ne_induct) (auto simp: lcm_eq_0_iff)
qed

lemma Gcd_image_normalize [simp]: "Gcd (normalize ` A) = Gcd A"
proof -
  have "Gcd (normalize ` A) dvd a" if "a \<in> A" for a
  proof -
    from that obtain B where "A = insert a B"
      by blast
    moreover have "gcd (normalize a) (Gcd (normalize ` B)) dvd normalize a"
      by (rule gcd_dvd1)
    ultimately show "Gcd (normalize ` A) dvd a"
      by simp
  qed
  then have "Gcd (normalize ` A) dvd Gcd A" and "Gcd A dvd Gcd (normalize ` A)"
    by (auto intro!: Gcd_greatest intro: Gcd_dvd)
  then show ?thesis
    by (auto intro: associated_eqI)
qed

lemma Gcd_eqI:
  assumes "normalize a = a"
  assumes "\<And>b. b \<in> A \<Longrightarrow> a dvd b"
    and "\<And>c. (\<And>b. b \<in> A \<Longrightarrow> c dvd b) \<Longrightarrow> c dvd a"
  shows "Gcd A = a"
  using assms by (blast intro: associated_eqI Gcd_greatest Gcd_dvd normalize_Gcd)

lemma dvd_GcdD: "x dvd Gcd A \<Longrightarrow> y \<in> A \<Longrightarrow> x dvd y"
  using Gcd_dvd dvd_trans by blast

lemma dvd_Gcd_iff: "x dvd Gcd A \<longleftrightarrow> (\<forall>y\<in>A. x dvd y)"
  by (blast dest: dvd_GcdD intro: Gcd_greatest)

lemma Gcd_mult: "Gcd ((*) c ` A) = normalize (c * Gcd A)"
proof (cases "c = 0")
  case True
  then show ?thesis by auto
next
  case [simp]: False
  have "Gcd ((*) c ` A) div c dvd Gcd A"
    by (intro Gcd_greatest, subst div_dvd_iff_mult)
       (auto intro!: Gcd_greatest Gcd_dvd simp: mult.commute[of _ c])
  then have "Gcd ((*) c ` A) dvd c * Gcd A"
    by (subst (asm) div_dvd_iff_mult) (auto intro: Gcd_greatest simp: mult_ac)
  moreover have "c * Gcd A dvd Gcd ((*) c ` A)"
    by (intro Gcd_greatest) (auto intro: mult_dvd_mono Gcd_dvd)
  ultimately have "normalize (Gcd ((*) c ` A)) = normalize (c * Gcd A)"
    by (rule associatedI)
  then show ?thesis by simp    
qed

lemma Lcm_eqI:
  assumes "normalize a = a"
    and "\<And>b. b \<in> A \<Longrightarrow> b dvd a"
    and "\<And>c. (\<And>b. b \<in> A \<Longrightarrow> b dvd c) \<Longrightarrow> a dvd c"
  shows "Lcm A = a"
  using assms by (blast intro: associated_eqI Lcm_least dvd_Lcm normalize_Lcm)

lemma Lcm_dvdD: "Lcm A dvd x \<Longrightarrow> y \<in> A \<Longrightarrow> y dvd x"
  using dvd_Lcm dvd_trans by blast

lemma Lcm_dvd_iff: "Lcm A dvd x \<longleftrightarrow> (\<forall>y\<in>A. y dvd x)"
  by (blast dest: Lcm_dvdD intro: Lcm_least)

lemma Lcm_mult:
  assumes "A \<noteq> {}"
  shows "Lcm ((*) c ` A) = normalize (c * Lcm A)"
proof (cases "c = 0")
  case True
  with assms have "(*) c ` A = {0}"
    by auto
  with True show ?thesis by auto
next
  case [simp]: False
  from assms obtain x where x: "x \<in> A"
    by blast
  have "c dvd c * x"
    by simp
  also from x have "c * x dvd Lcm ((*) c ` A)"
    by (intro dvd_Lcm) auto
  finally have dvd: "c dvd Lcm ((*) c ` A)" .
  moreover have "Lcm A dvd Lcm ((*) c ` A) div c"
    by (intro Lcm_least dvd_mult_imp_div)
      (auto intro!: Lcm_least dvd_Lcm simp: mult.commute[of _ c])
  ultimately have "c * Lcm A dvd Lcm ((*) c ` A)"
    by auto
  moreover have "Lcm ((*) c ` A) dvd c * Lcm A"
    by (intro Lcm_least) (auto intro: mult_dvd_mono dvd_Lcm)
  ultimately have "normalize (c * Lcm A) = normalize (Lcm ((*) c ` A))"
    by (rule associatedI)
  then show ?thesis by simp
qed

lemma Lcm_no_units: "Lcm A = Lcm (A - {a. is_unit a})"
proof -
  have "(A - {a. is_unit a}) \<union> {a\<in>A. is_unit a} = A"
    by blast
  then have "Lcm A = lcm (Lcm (A - {a. is_unit a})) (Lcm {a\<in>A. is_unit a})"
    by (simp add: Lcm_Un [symmetric])
  also have "Lcm {a\<in>A. is_unit a} = 1"
    by simp
  finally show ?thesis
    by simp
qed

lemma Lcm_0_iff': "Lcm A = 0 \<longleftrightarrow> (\<nexists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l))"
  by (metis Lcm_least dvd_0_left dvd_Lcm)

lemma Lcm_no_multiple: "(\<forall>m. m \<noteq> 0 \<longrightarrow> (\<exists>a\<in>A. \<not> a dvd m)) \<Longrightarrow> Lcm A = 0"
  by (auto simp: Lcm_0_iff')

lemma Lcm_singleton [simp]: "Lcm {a} = normalize a"
  by simp

lemma Lcm_2 [simp]: "Lcm {a, b} = lcm a b"
  by simp

lemma Gcd_1: "1 \<in> A \<Longrightarrow> Gcd A = 1"
  by (auto intro!: Gcd_eq_1_I)

lemma Gcd_singleton [simp]: "Gcd {a} = normalize a"
  by simp

lemma Gcd_2 [simp]: "Gcd {a, b} = gcd a b"
  by simp

lemma Gcd_mono:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x dvd g x"
  shows   "(GCD x\<in>A. f x) dvd (GCD x\<in>A. g x)"
proof (intro Gcd_greatest, safe)
  fix x assume "x \<in> A"
  hence "(GCD x\<in>A. f x) dvd f x"
    by (intro Gcd_dvd) auto
  also have "f x dvd g x"
    using \<open>x \<in> A\<close> assms by blast
  finally show "(GCD x\<in>A. f x) dvd \<dots>" .
qed

lemma Lcm_mono:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x dvd g x"
  shows   "(LCM x\<in>A. f x) dvd (LCM x\<in>A. g x)"
proof (intro Lcm_least, safe)
  fix x assume "x \<in> A"
  hence "f x dvd g x" by (rule assms)
  also have "g x dvd (LCM x\<in>A. g x)"
    using \<open>x \<in> A\<close> by (intro dvd_Lcm) auto
  finally show "f x dvd \<dots>" .
qed

end


subsection \<open>An aside: GCD and LCM on finite sets for incomplete gcd rings\<close>

context semiring_gcd
begin

sublocale Gcd_fin: bounded_quasi_semilattice_set gcd 0 1 normalize
defines
  Gcd_fin ("Gcd\<^sub>f\<^sub>i\<^sub>n") = "Gcd_fin.F :: 'a set \<Rightarrow> 'a" ..

abbreviation gcd_list :: "'a list \<Rightarrow> 'a"
  where "gcd_list xs \<equiv> Gcd\<^sub>f\<^sub>i\<^sub>n (set xs)"

sublocale Lcm_fin: bounded_quasi_semilattice_set lcm 1 0 normalize
defines
  Lcm_fin ("Lcm\<^sub>f\<^sub>i\<^sub>n") = Lcm_fin.F ..

abbreviation lcm_list :: "'a list \<Rightarrow> 'a"
  where "lcm_list xs \<equiv> Lcm\<^sub>f\<^sub>i\<^sub>n (set xs)"

lemma Gcd_fin_dvd:
  "a \<in> A \<Longrightarrow> Gcd\<^sub>f\<^sub>i\<^sub>n A dvd a"
  by (induct A rule: infinite_finite_induct)
    (auto intro: dvd_trans)

lemma dvd_Lcm_fin:
  "a \<in> A \<Longrightarrow> a dvd Lcm\<^sub>f\<^sub>i\<^sub>n A"
  by (induct A rule: infinite_finite_induct)
    (auto intro: dvd_trans)

lemma Gcd_fin_greatest:
  "a dvd Gcd\<^sub>f\<^sub>i\<^sub>n A" if "finite A" and "\<And>b. b \<in> A \<Longrightarrow> a dvd b"
  using that by (induct A) simp_all

lemma Lcm_fin_least:
  "Lcm\<^sub>f\<^sub>i\<^sub>n A dvd a" if "finite A" and "\<And>b. b \<in> A \<Longrightarrow> b dvd a"
  using that by (induct A) simp_all

lemma gcd_list_greatest:
  "a dvd gcd_list bs" if "\<And>b. b \<in> set bs \<Longrightarrow> a dvd b"
  by (rule Gcd_fin_greatest) (simp_all add: that)

lemma lcm_list_least:
  "lcm_list bs dvd a" if "\<And>b. b \<in> set bs \<Longrightarrow> b dvd a"
  by (rule Lcm_fin_least) (simp_all add: that)

lemma dvd_Gcd_fin_iff:
  "b dvd Gcd\<^sub>f\<^sub>i\<^sub>n A \<longleftrightarrow> (\<forall>a\<in>A. b dvd a)" if "finite A"
  using that by (auto intro: Gcd_fin_greatest Gcd_fin_dvd dvd_trans [of b "Gcd\<^sub>f\<^sub>i\<^sub>n A"])

lemma dvd_gcd_list_iff:
  "b dvd gcd_list xs \<longleftrightarrow> (\<forall>a\<in>set xs. b dvd a)"
  by (simp add: dvd_Gcd_fin_iff)

lemma Lcm_fin_dvd_iff:
  "Lcm\<^sub>f\<^sub>i\<^sub>n A dvd b  \<longleftrightarrow> (\<forall>a\<in>A. a dvd b)" if "finite A"
  using that by (auto intro: Lcm_fin_least dvd_Lcm_fin dvd_trans [of _ "Lcm\<^sub>f\<^sub>i\<^sub>n A" b])

lemma lcm_list_dvd_iff:
  "lcm_list xs dvd b  \<longleftrightarrow> (\<forall>a\<in>set xs. a dvd b)"
  by (simp add: Lcm_fin_dvd_iff)

lemma Gcd_fin_mult:
  "Gcd\<^sub>f\<^sub>i\<^sub>n (image (times b) A) = normalize (b * Gcd\<^sub>f\<^sub>i\<^sub>n A)" if "finite A"
  using that by induction (auto simp: gcd_mult_left)

lemma Lcm_fin_mult:
  "Lcm\<^sub>f\<^sub>i\<^sub>n (image (times b) A) = normalize (b * Lcm\<^sub>f\<^sub>i\<^sub>n A)" if "A \<noteq> {}"
proof (cases "b = 0")
  case True
  moreover from that have "times 0 ` A = {0}"
    by auto
  ultimately show ?thesis
    by simp
next
  case False
  show ?thesis proof (cases "finite A")
    case False
    moreover have "inj_on (times b) A"
      using \<open>b \<noteq> 0\<close> by (rule inj_on_mult)
    ultimately have "infinite (times b ` A)"
      by (simp add: finite_image_iff)
    with False show ?thesis
      by simp
  next
    case True
    then show ?thesis using that
      by (induct A rule: finite_ne_induct) (auto simp: lcm_mult_left)
  qed
qed

lemma unit_factor_Gcd_fin:
  "unit_factor (Gcd\<^sub>f\<^sub>i\<^sub>n A) = of_bool (Gcd\<^sub>f\<^sub>i\<^sub>n A \<noteq> 0)"
  by (rule normalize_idem_imp_unit_factor_eq) simp

lemma unit_factor_Lcm_fin:
  "unit_factor (Lcm\<^sub>f\<^sub>i\<^sub>n A) = of_bool (Lcm\<^sub>f\<^sub>i\<^sub>n A \<noteq> 0)"
  by (rule normalize_idem_imp_unit_factor_eq) simp

lemma is_unit_Gcd_fin_iff [simp]:
  "is_unit (Gcd\<^sub>f\<^sub>i\<^sub>n A) \<longleftrightarrow> Gcd\<^sub>f\<^sub>i\<^sub>n A = 1"
  by (rule normalize_idem_imp_is_unit_iff) simp

lemma is_unit_Lcm_fin_iff [simp]:
  "is_unit (Lcm\<^sub>f\<^sub>i\<^sub>n A) \<longleftrightarrow> Lcm\<^sub>f\<^sub>i\<^sub>n A = 1"
  by (rule normalize_idem_imp_is_unit_iff) simp
 
lemma Gcd_fin_0_iff:
  "Gcd\<^sub>f\<^sub>i\<^sub>n A = 0 \<longleftrightarrow> A \<subseteq> {0} \<and> finite A"
  by (induct A rule: infinite_finite_induct) simp_all

lemma Lcm_fin_0_iff:
  "Lcm\<^sub>f\<^sub>i\<^sub>n A = 0 \<longleftrightarrow> 0 \<in> A" if "finite A"
  using that by (induct A) (auto simp: lcm_eq_0_iff)

lemma Lcm_fin_1_iff:
  "Lcm\<^sub>f\<^sub>i\<^sub>n A = 1 \<longleftrightarrow> (\<forall>a\<in>A. is_unit a) \<and> finite A"
  by (induct A rule: infinite_finite_induct) simp_all

end

context semiring_Gcd
begin

lemma Gcd_fin_eq_Gcd [simp]:
  "Gcd\<^sub>f\<^sub>i\<^sub>n A = Gcd A" if "finite A" for A :: "'a set"
  using that by induct simp_all

lemma Gcd_set_eq_fold [code_unfold]:
  "Gcd (set xs) = fold gcd xs 0"
  by (simp add: Gcd_fin.set_eq_fold [symmetric])

lemma Lcm_fin_eq_Lcm [simp]:
  "Lcm\<^sub>f\<^sub>i\<^sub>n A = Lcm A" if "finite A" for A :: "'a set"
  using that by induct simp_all

lemma Lcm_set_eq_fold [code_unfold]:
  "Lcm (set xs) = fold lcm xs 1"
  by (simp add: Lcm_fin.set_eq_fold [symmetric])

end


subsection \<open>Coprimality\<close>

context semiring_gcd
begin

lemma coprime_imp_gcd_eq_1 [simp]:
  "gcd a b = 1" if "coprime a b"
proof -
  define t r s where "t = gcd a b" and "r = a div t" and "s = b div t"
  then have "a = t * r" and "b = t * s"
    by simp_all
  with that have "coprime (t * r) (t * s)"
    by simp
  then show ?thesis
    by (simp add: t_def)
qed

lemma gcd_eq_1_imp_coprime [dest!]:
  "coprime a b" if "gcd a b = 1"
proof (rule coprimeI)
  fix c
  assume "c dvd a" and "c dvd b"
  then have "c dvd gcd a b"
    by (rule gcd_greatest)
  with that show "is_unit c"
    by simp
qed

lemma coprime_iff_gcd_eq_1 [presburger, code]:
  "coprime a b \<longleftrightarrow> gcd a b = 1"
  by rule (simp_all add: gcd_eq_1_imp_coprime)

lemma is_unit_gcd [simp]:
  "is_unit (gcd a b) \<longleftrightarrow> coprime a b"
  by (simp add: coprime_iff_gcd_eq_1)

lemma coprime_add_one_left [simp]: "coprime (a + 1) a"
  by (simp add: gcd_eq_1_imp_coprime ac_simps)

lemma coprime_add_one_right [simp]: "coprime a (a + 1)"
  using coprime_add_one_left [of a] by (simp add: ac_simps)

lemma coprime_mult_left_iff [simp]:
  "coprime (a * b) c \<longleftrightarrow> coprime a c \<and> coprime b c"
proof
  assume "coprime (a * b) c"
  with coprime_common_divisor [of "a * b" c]
  have *: "is_unit d" if "d dvd a * b" and "d dvd c" for d
    using that by blast
  have "coprime a c"
    by (rule coprimeI, rule *) simp_all
  moreover have "coprime b c"
    by (rule coprimeI, rule *) simp_all
  ultimately show "coprime a c \<and> coprime b c" ..
next
  assume "coprime a c \<and> coprime b c"
  then have "coprime a c" "coprime b c"
    by simp_all
  show "coprime (a * b) c"
  proof (rule coprimeI)
    fix d
    assume "d dvd a * b"
    then obtain r s where d: "d = r * s" "r dvd a" "s dvd b"
      by (rule dvd_productE)
    assume "d dvd c"
    with d have "r * s dvd c"
      by simp
    then have "r dvd c" "s dvd c"
      by (auto intro: dvd_mult_left dvd_mult_right)
    from \<open>coprime a c\<close> \<open>r dvd a\<close> \<open>r dvd c\<close>
    have "is_unit r"
      by (rule coprime_common_divisor)
    moreover from \<open>coprime b c\<close> \<open>s dvd b\<close> \<open>s dvd c\<close>
    have "is_unit s"
      by (rule coprime_common_divisor)
    ultimately show "is_unit d"
      by (simp add: d is_unit_mult_iff)
  qed
qed

lemma coprime_mult_right_iff [simp]:
  "coprime c (a * b) \<longleftrightarrow> coprime c a \<and> coprime c b"
  using coprime_mult_left_iff [of a b c] by (simp add: ac_simps)

lemma coprime_power_left_iff [simp]:
  "coprime (a ^ n) b \<longleftrightarrow> coprime a b \<or> n = 0"
proof (cases "n = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  then have "n > 0"
    by simp
  then show ?thesis
    by (induction n rule: nat_induct_non_zero) simp_all
qed

lemma coprime_power_right_iff [simp]:
  "coprime a (b ^ n) \<longleftrightarrow> coprime a b \<or> n = 0"
  using coprime_power_left_iff [of b n a] by (simp add: ac_simps)

lemma prod_coprime_left:
  "coprime (\<Prod>i\<in>A. f i) a" if "\<And>i. i \<in> A \<Longrightarrow> coprime (f i) a"
  using that by (induct A rule: infinite_finite_induct) simp_all

lemma prod_coprime_right:
  "coprime a (\<Prod>i\<in>A. f i)" if "\<And>i. i \<in> A \<Longrightarrow> coprime a (f i)"
  using that prod_coprime_left [of A f a] by (simp add: ac_simps)

lemma prod_list_coprime_left:
  "coprime (prod_list xs) a" if "\<And>x. x \<in> set xs \<Longrightarrow> coprime x a"
  using that by (induct xs) simp_all

lemma prod_list_coprime_right:
  "coprime a (prod_list xs)" if "\<And>x. x \<in> set xs \<Longrightarrow> coprime a x"
  using that prod_list_coprime_left [of xs a] by (simp add: ac_simps)

lemma coprime_dvd_mult_left_iff:
  "a dvd b * c \<longleftrightarrow> a dvd b" if "coprime a c"
proof
  assume "a dvd b"
  then show "a dvd b * c"
    by simp
next
  assume "a dvd b * c"
  show "a dvd b"
  proof (cases "b = 0")
    case True
    then show ?thesis
      by simp
  next
    case False
    then have unit: "is_unit (unit_factor b)"
      by simp
    from \<open>coprime a c\<close>
    have "gcd (b * a) (b * c) * unit_factor b = b"
      by (subst gcd_mult_left) (simp add: ac_simps)
    moreover from \<open>a dvd b * c\<close>
    have "a dvd gcd (b * a) (b * c) * unit_factor b"
      by (simp add: dvd_mult_unit_iff unit)
    ultimately show ?thesis
      by simp
  qed
qed

lemma coprime_dvd_mult_right_iff:
  "a dvd c * b \<longleftrightarrow> a dvd b" if "coprime a c"
  using that coprime_dvd_mult_left_iff [of a c b] by (simp add: ac_simps)

lemma divides_mult:
  "a * b dvd c" if "a dvd c" and "b dvd c" and "coprime a b"
proof -
  from \<open>b dvd c\<close> obtain b' where "c = b * b'" ..
  with \<open>a dvd c\<close> have "a dvd b' * b"
    by (simp add: ac_simps)
  with \<open>coprime a b\<close> have "a dvd b'"
    by (simp add: coprime_dvd_mult_left_iff)
  then obtain a' where "b' = a * a'" ..
  with \<open>c = b * b'\<close> have "c = (a * b) * a'"
    by (simp add: ac_simps)
  then show ?thesis ..
qed

lemma div_gcd_coprime:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
  shows "coprime (a div gcd a b) (b div gcd a b)"
proof -
  let ?g = "gcd a b"
  let ?a' = "a div ?g"
  let ?b' = "b div ?g"
  let ?g' = "gcd ?a' ?b'"
  have dvdg: "?g dvd a" "?g dvd b"
    by simp_all
  have dvdg': "?g' dvd ?a'" "?g' dvd ?b'"
    by simp_all
  from dvdg dvdg' obtain ka kb ka' kb' where
    kab: "a = ?g * ka" "b = ?g * kb" "?a' = ?g' * ka'" "?b' = ?g' * kb'"
    unfolding dvd_def by blast
  from this [symmetric] have "?g * ?a' = (?g * ?g') * ka'" "?g * ?b' = (?g * ?g') * kb'"
    by (simp_all add: mult.assoc mult.left_commute [of "gcd a b"])
  then have dvdgg':"?g * ?g' dvd a" "?g* ?g' dvd b"
    by (auto simp: dvd_mult_div_cancel [OF dvdg(1)] dvd_mult_div_cancel [OF dvdg(2)] dvd_def)
  have "?g \<noteq> 0"
    using assms by simp
  moreover from gcd_greatest [OF dvdgg'] have "?g * ?g' dvd ?g" .
  ultimately show ?thesis
    using dvd_times_left_cancel_iff [of "gcd a b" _ 1]
    by simp (simp only: coprime_iff_gcd_eq_1)
qed

lemma gcd_coprime:
  assumes c: "gcd a b \<noteq> 0"
    and a: "a = a' * gcd a b"
    and b: "b = b' * gcd a b"
  shows "coprime a' b'"
proof -
  from c have "a \<noteq> 0 \<or> b \<noteq> 0"
    by simp
  with div_gcd_coprime have "coprime (a div gcd a b) (b div gcd a b)" .
  also from assms have "a div gcd a b = a'"
    using dvd_div_eq_mult gcd_dvd1 by blast
  also from assms have "b div gcd a b = b'"
    using dvd_div_eq_mult gcd_dvd1 by blast
  finally show ?thesis .
qed

lemma gcd_coprime_exists:
  assumes "gcd a b \<noteq> 0"
  shows "\<exists>a' b'. a = a' * gcd a b \<and> b = b' * gcd a b \<and> coprime a' b'"
proof -
  have "coprime (a div gcd a b) (b div gcd a b)"
    using assms div_gcd_coprime by auto
  then show ?thesis
    by force
qed

lemma pow_divides_pow_iff [simp]:
  "a ^ n dvd b ^ n \<longleftrightarrow> a dvd b" if "n > 0"
proof (cases "gcd a b = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  show ?thesis
  proof
    let ?d = "gcd a b"
    from \<open>n > 0\<close> obtain m where m: "n = Suc m"
      by (cases n) simp_all
    from False have zn: "?d ^ n \<noteq> 0"
      by (rule power_not_zero)
    from gcd_coprime_exists [OF False]
    obtain a' b' where ab': "a = a' * ?d" "b = b' * ?d" "coprime a' b'"
      by blast
    assume "a ^ n dvd b ^ n"
    then have "(a' * ?d) ^ n dvd (b' * ?d) ^ n"
      by (simp add: ab'(1,2)[symmetric])
    then have "?d^n * a'^n dvd ?d^n * b'^n"
      by (simp only: power_mult_distrib ac_simps)
    with zn have "a' ^ n dvd b' ^ n"
      by simp
    then have "a' dvd b' ^ n"
      using dvd_trans[of a' "a'^n" "b'^n"] by (simp add: m)
    then have "a' dvd b' ^ m * b'"
      by (simp add: m ac_simps)
    moreover have "coprime a' (b' ^ n)"
      using \<open>coprime a' b'\<close> by simp
    then have "a' dvd b'"
      using \<open>a' dvd b' ^ n\<close> coprime_dvd_mult_left_iff dvd_mult by blast
    then have "a' * ?d dvd b' * ?d"
      by (rule mult_dvd_mono) simp
    with ab'(1,2) show "a dvd b"
      by simp
  next
    assume "a dvd b"
    with \<open>n > 0\<close> show "a ^ n dvd b ^ n"
      by (induction rule: nat_induct_non_zero)
        (simp_all add: mult_dvd_mono)
  qed
qed

lemma coprime_crossproduct:
  fixes a b c d :: 'a
  assumes "coprime a d" and "coprime b c"
  shows "normalize a * normalize c = normalize b * normalize d \<longleftrightarrow>
    normalize a = normalize b \<and> normalize c = normalize d"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then show ?lhs by simp
next
  assume ?lhs
  from \<open>?lhs\<close> have "normalize a dvd normalize b * normalize d"
    by (auto intro: dvdI dest: sym)
  with \<open>coprime a d\<close> have "a dvd b"
    by (simp add: coprime_dvd_mult_left_iff normalize_mult [symmetric])
  from \<open>?lhs\<close> have "normalize b dvd normalize a * normalize c"
    by (auto intro: dvdI dest: sym)
  with \<open>coprime b c\<close> have "b dvd a"
    by (simp add: coprime_dvd_mult_left_iff normalize_mult [symmetric])
  from \<open>?lhs\<close> have "normalize c dvd normalize d * normalize b"
    by (auto intro: dvdI dest: sym simp add: mult.commute)
  with \<open>coprime b c\<close> have "c dvd d"
    by (simp add: coprime_dvd_mult_left_iff coprime_commute normalize_mult [symmetric])
  from \<open>?lhs\<close> have "normalize d dvd normalize c * normalize a"
    by (auto intro: dvdI dest: sym simp add: mult.commute)
  with \<open>coprime a d\<close> have "d dvd c"
    by (simp add: coprime_dvd_mult_left_iff coprime_commute normalize_mult [symmetric])
  from \<open>a dvd b\<close> \<open>b dvd a\<close> have "normalize a = normalize b"
    by (rule associatedI)
  moreover from \<open>c dvd d\<close> \<open>d dvd c\<close> have "normalize c = normalize d"
    by (rule associatedI)
  ultimately show ?rhs ..
qed

lemma gcd_mult_left_left_cancel:
  "gcd (c * a) b = gcd a b" if "coprime b c"
proof -
  have "coprime (gcd b (a * c)) c"
    by (rule coprimeI) (auto intro: that coprime_common_divisor)
  then have "gcd b (a * c) dvd a"
    using coprime_dvd_mult_left_iff [of "gcd b (a * c)" c a]
    by simp
  then show ?thesis
    by (auto intro: associated_eqI simp add: ac_simps)
qed

lemma gcd_mult_left_right_cancel:
  "gcd (a * c) b = gcd a b" if "coprime b c"
  using that gcd_mult_left_left_cancel [of b c a]
  by (simp add: ac_simps)

lemma gcd_mult_right_left_cancel:
  "gcd a (c * b) = gcd a b" if "coprime a c"
  using that gcd_mult_left_left_cancel [of a c b]
  by (simp add: ac_simps)

lemma gcd_mult_right_right_cancel:
  "gcd a (b * c) = gcd a b" if "coprime a c"
  using that gcd_mult_right_left_cancel [of a c b]
  by (simp add: ac_simps)

lemma gcd_exp_weak:
  "gcd (a ^ n) (b ^ n) = normalize (gcd a b ^ n)"
proof (cases "a = 0 \<and> b = 0 \<or> n = 0")
  case True
  then show ?thesis
    by (cases n) simp_all
next
  case False
  then have "coprime (a div gcd a b) (b div gcd a b)" and "n > 0"
    by (auto intro: div_gcd_coprime)
  then have "coprime ((a div gcd a b) ^ n) ((b div gcd a b) ^ n)"
    by simp
  then have "1 = gcd ((a div gcd a b) ^ n) ((b div gcd a b) ^ n)"
    by simp
  then have "normalize (gcd a b ^ n) = normalize (gcd a b ^ n * \<dots>)"
    by simp
  also have "\<dots> = gcd (gcd a b ^ n * (a div gcd a b) ^ n) (gcd a b ^ n * (b div gcd a b) ^ n)"
    by (rule gcd_mult_left [symmetric])
  also have "(gcd a b) ^ n * (a div gcd a b) ^ n = a ^ n"
    by (simp add: ac_simps div_power dvd_power_same)
  also have "(gcd a b) ^ n * (b div gcd a b) ^ n = b ^ n"
    by (simp add: ac_simps div_power dvd_power_same)
  finally show ?thesis by simp
qed

lemma division_decomp:
  assumes "a dvd b * c"
  shows "\<exists>b' c'. a = b' * c' \<and> b' dvd b \<and> c' dvd c"
proof (cases "gcd a b = 0")
  case True
  then have "a = 0 \<and> b = 0"
    by simp
  then have "a = 0 * c \<and> 0 dvd b \<and> c dvd c"
    by simp
  then show ?thesis by blast
next
  case False
  let ?d = "gcd a b"
  from gcd_coprime_exists [OF False]
    obtain a' b' where ab': "a = a' * ?d" "b = b' * ?d" "coprime a' b'"
    by blast
  from ab'(1) have "a' dvd a" ..
  with assms have "a' dvd b * c"
    using dvd_trans [of a' a "b * c"] by simp
  from assms ab'(1,2) have "a' * ?d dvd (b' * ?d) * c"
    by simp
  then have "?d * a' dvd ?d * (b' * c)"
    by (simp add: mult_ac)
  with \<open>?d \<noteq> 0\<close> have "a' dvd b' * c"
    by simp
  then have "a' dvd c"
    using \<open>coprime a' b'\<close> by (simp add: coprime_dvd_mult_right_iff)
  with ab'(1) have "a = ?d * a' \<and> ?d dvd b \<and> a' dvd c"
    by (simp add: ac_simps)
  then show ?thesis by blast
qed

lemma lcm_coprime: "coprime a b \<Longrightarrow> lcm a b = normalize (a * b)"
  by (subst lcm_gcd) simp

end

context ring_gcd
begin

lemma coprime_minus_left_iff [simp]:
  "coprime (- a) b \<longleftrightarrow> coprime a b"
  by (rule; rule coprimeI) (auto intro: coprime_common_divisor)

lemma coprime_minus_right_iff [simp]:
  "coprime a (- b) \<longleftrightarrow> coprime a b"
  using coprime_minus_left_iff [of b a] by (simp add: ac_simps)

lemma coprime_diff_one_left [simp]: "coprime (a - 1) a"
  using coprime_add_one_right [of "a - 1"] by simp

lemma coprime_doff_one_right [simp]: "coprime a (a - 1)"
  using coprime_diff_one_left [of a] by (simp add: ac_simps)

end

context semiring_Gcd
begin

lemma Lcm_coprime:
  assumes "finite A"
    and "A \<noteq> {}"
    and "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> coprime a b"
  shows "Lcm A = normalize (\<Prod>A)"
  using assms
proof (induct rule: finite_ne_induct)
  case singleton
  then show ?case by simp
next
  case (insert a A)
  have "Lcm (insert a A) = lcm a (Lcm A)"
    by simp
  also from insert have "Lcm A = normalize (\<Prod>A)"
    by blast
  also have "lcm a \<dots> = lcm a (\<Prod>A)"
    by (cases "\<Prod>A = 0") (simp_all add: lcm_div_unit2)
  also from insert have "coprime a (\<Prod>A)"
    by (subst coprime_commute, intro prod_coprime_left) auto
  with insert have "lcm a (\<Prod>A) = normalize (\<Prod>(insert a A))"
    by (simp add: lcm_coprime)
  finally show ?case .
qed

lemma Lcm_coprime':
  "card A \<noteq> 0 \<Longrightarrow>
    (\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> coprime a b) \<Longrightarrow>
    Lcm A = normalize (\<Prod>A)"
  by (rule Lcm_coprime) (simp_all add: card_eq_0_iff)

end


subsection \<open>GCD and LCM for multiplicative normalisation functions\<close>

class semiring_gcd_mult_normalize = semiring_gcd + normalization_semidom_multiplicative
begin

lemma mult_gcd_left: "c * gcd a b = unit_factor c * gcd (c * a) (c * b)"
  by (simp add: gcd_mult_left normalize_mult mult.assoc [symmetric])

lemma mult_gcd_right: "gcd a b * c = gcd (a * c) (b * c) * unit_factor c"
  using mult_gcd_left [of c a b] by (simp add: ac_simps)

lemma gcd_mult_distrib': "normalize c * gcd a b = gcd (c * a) (c * b)"
  by (subst gcd_mult_left) (simp_all add: normalize_mult)

lemma gcd_mult_distrib: "k * gcd a b = gcd (k * a) (k * b) * unit_factor k"
proof-
  have "normalize k * gcd a b = gcd (k * a) (k * b)"
    by (simp add: gcd_mult_distrib')
  then have "normalize k * gcd a b * unit_factor k = gcd (k * a) (k * b) * unit_factor k"
    by simp
  then have "normalize k * unit_factor k * gcd a b  = gcd (k * a) (k * b) * unit_factor k"
    by (simp only: ac_simps)
  then show ?thesis
    by simp
qed

lemma gcd_mult_lcm [simp]: "gcd a b * lcm a b = normalize a * normalize b"
  by (simp add: lcm_gcd normalize_mult dvd_normalize_div)

lemma lcm_mult_gcd [simp]: "lcm a b * gcd a b = normalize a * normalize b"
  using gcd_mult_lcm [of a b] by (simp add: ac_simps)

lemma mult_lcm_left: "c * lcm a b = unit_factor c * lcm (c * a) (c * b)"
  by (simp add: lcm_mult_left mult.assoc [symmetric] normalize_mult)

lemma mult_lcm_right: "lcm a b * c = lcm (a * c) (b * c) * unit_factor c"
  using mult_lcm_left [of c a b] by (simp add: ac_simps)

lemma lcm_gcd_prod: "lcm a b * gcd a b = normalize (a * b)"
  by (simp add: lcm_gcd dvd_normalize_div normalize_mult)

lemma lcm_mult_distrib': "normalize c * lcm a b = lcm (c * a) (c * b)"
  by (subst lcm_mult_left) (simp add: normalize_mult)

lemma lcm_mult_distrib: "k * lcm a b = lcm (k * a) (k * b) * unit_factor k"
proof-
  have "normalize k * lcm a b = lcm (k * a) (k * b)"
    by (simp add: lcm_mult_distrib')
  then have "normalize k * lcm a b * unit_factor k = lcm (k * a) (k * b) * unit_factor k"
    by simp
  then have "normalize k * unit_factor k * lcm a b  = lcm (k * a) (k * b) * unit_factor k"
    by (simp only: ac_simps)
  then show ?thesis
    by simp
qed

lemma coprime_crossproduct':
  fixes a b c d
  assumes "b \<noteq> 0"
  assumes unit_factors: "unit_factor b = unit_factor d"
  assumes coprime: "coprime a b" "coprime c d"
  shows "a * d = b * c \<longleftrightarrow> a = c \<and> b = d"
proof safe
  assume eq: "a * d = b * c"
  hence "normalize a * normalize d = normalize c * normalize b"
    by (simp only: normalize_mult [symmetric] mult_ac)
  with coprime have "normalize b = normalize d"
    by (subst (asm) coprime_crossproduct) simp_all
  from this and unit_factors show "b = d"
    by (rule normalize_unit_factor_eqI)
  from eq have "a * d = c * d" by (simp only: \<open>b = d\<close> mult_ac)
  with \<open>b \<noteq> 0\<close> \<open>b = d\<close> show "a = c" by simp
qed (simp_all add: mult_ac)

lemma gcd_exp [simp]:
  "gcd (a ^ n) (b ^ n) = gcd a b ^ n"
  using gcd_exp_weak[of a n b] by (simp add: normalize_power)

end


subsection \<open>GCD and LCM on \<^typ>\<open>nat\<close> and \<^typ>\<open>int\<close>\<close>

instantiation nat :: gcd
begin

fun gcd_nat  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "gcd_nat x y = (if y = 0 then x else gcd y (x mod y))"

definition lcm_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "lcm_nat x y = x * y div (gcd x y)"

instance ..

end

instantiation int :: gcd
begin

definition gcd_int  :: "int \<Rightarrow> int \<Rightarrow> int"
  where "gcd_int x y = int (gcd (nat \<bar>x\<bar>) (nat \<bar>y\<bar>))"

definition lcm_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where "lcm_int x y = int (lcm (nat \<bar>x\<bar>) (nat \<bar>y\<bar>))"

instance ..

end

lemma gcd_int_int_eq [simp]:
  "gcd (int m) (int n) = int (gcd m n)"
  by (simp add: gcd_int_def)

lemma gcd_nat_abs_left_eq [simp]:
  "gcd (nat \<bar>k\<bar>) n = nat (gcd k (int n))"
  by (simp add: gcd_int_def)

lemma gcd_nat_abs_right_eq [simp]:
  "gcd n (nat \<bar>k\<bar>) = nat (gcd (int n) k)"
  by (simp add: gcd_int_def)

lemma abs_gcd_int [simp]:
  "\<bar>gcd x y\<bar> = gcd x y"
  for x y :: int
  by (simp only: gcd_int_def)

lemma gcd_abs1_int [simp]:
  "gcd \<bar>x\<bar> y = gcd x y"
  for x y :: int
  by (simp only: gcd_int_def) simp

lemma gcd_abs2_int [simp]:
  "gcd x \<bar>y\<bar> = gcd x y"
  for x y :: int
  by (simp only: gcd_int_def) simp

lemma lcm_int_int_eq [simp]:
  "lcm (int m) (int n) = int (lcm m n)"
  by (simp add: lcm_int_def)

lemma lcm_nat_abs_left_eq [simp]:
  "lcm (nat \<bar>k\<bar>) n = nat (lcm k (int n))"
  by (simp add: lcm_int_def)

lemma lcm_nat_abs_right_eq [simp]:
  "lcm n (nat \<bar>k\<bar>) = nat (lcm (int n) k)"
  by (simp add: lcm_int_def)

lemma lcm_abs1_int [simp]:
  "lcm \<bar>x\<bar> y = lcm x y"
  for x y :: int
  by (simp only: lcm_int_def) simp

lemma lcm_abs2_int [simp]:
  "lcm x \<bar>y\<bar> = lcm x y"
  for x y :: int
  by (simp only: lcm_int_def) simp

lemma abs_lcm_int [simp]: "\<bar>lcm i j\<bar> = lcm i j"
  for i j :: int
  by (simp only: lcm_int_def)

lemma gcd_nat_induct [case_names base step]:
  fixes m n :: nat
  assumes "\<And>m. P m 0"
    and "\<And>m n. 0 < n \<Longrightarrow> P n (m mod n) \<Longrightarrow> P m n"
  shows "P m n"
proof (induction m n rule: gcd_nat.induct)
  case (1 x y)
  then show ?case
    using assms neq0_conv by blast
qed

lemma gcd_neg1_int [simp]: "gcd (- x) y = gcd x y"
  for x y :: int
  by (simp only: gcd_int_def) simp

lemma gcd_neg2_int [simp]: "gcd x (- y) = gcd x y"
  for x y :: int
  by (simp only: gcd_int_def) simp

lemma gcd_cases_int:
  fixes x y :: int
  assumes "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> P (gcd x y)"
    and "x \<ge> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> P (gcd x (- y))"
    and "x \<le> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> P (gcd (- x) y)"
    and "x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> P (gcd (- x) (- y))"
  shows "P (gcd x y)"
  using assms by auto arith

lemma gcd_ge_0_int [simp]: "gcd (x::int) y >= 0"
  for x y :: int
  by (simp add: gcd_int_def)

lemma lcm_neg1_int: "lcm (- x) y = lcm x y"
  for x y :: int
  by (simp only: lcm_int_def) simp

lemma lcm_neg2_int: "lcm x (- y) = lcm x y"
  for x y :: int
  by (simp only: lcm_int_def) simp

lemma lcm_cases_int:
  fixes x y :: int
  assumes "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> P (lcm x y)"
    and "x \<ge> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> P (lcm x (- y))"
    and "x \<le> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> P (lcm (- x) y)"
    and "x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> P (lcm (- x) (- y))"
  shows "P (lcm x y)"
  using assms by (auto simp: lcm_neg1_int lcm_neg2_int) arith

lemma lcm_ge_0_int [simp]: "lcm x y \<ge> 0"
  for x y :: int
  by (simp only: lcm_int_def)

lemma gcd_0_nat: "gcd x 0 = x"
  for x :: nat
  by simp

lemma gcd_0_int [simp]: "gcd x 0 = \<bar>x\<bar>"
  for x :: int
  by (auto simp: gcd_int_def)

lemma gcd_0_left_nat: "gcd 0 x = x"
  for x :: nat
  by simp

lemma gcd_0_left_int [simp]: "gcd 0 x = \<bar>x\<bar>"
  for x :: int
  by (auto simp: gcd_int_def)

lemma gcd_red_nat: "gcd x y = gcd y (x mod y)"
  for x y :: nat
  by (cases "y = 0") auto


text \<open>Weaker, but useful for the simplifier.\<close>

lemma gcd_non_0_nat: "y \<noteq> 0 \<Longrightarrow> gcd x y = gcd y (x mod y)"
  for x y :: nat
  by simp

lemma gcd_1_nat [simp]: "gcd m 1 = 1"
  for m :: nat
  by simp

lemma gcd_Suc_0 [simp]: "gcd m (Suc 0) = Suc 0"
  for m :: nat
  by simp

lemma gcd_1_int [simp]: "gcd m 1 = 1"
  for m :: int
  by (simp add: gcd_int_def)

lemma gcd_idem_nat: "gcd x x = x"
  for x :: nat
  by simp

lemma gcd_idem_int: "gcd x x = \<bar>x\<bar>"
  for x :: int
  by (auto simp: gcd_int_def)

declare gcd_nat.simps [simp del]

text \<open>
  \<^medskip> \<^term>\<open>gcd m n\<close> divides \<open>m\<close> and \<open>n\<close>.
  The conjunctions don't seem provable separately.
\<close>

instance nat :: semiring_gcd
proof
  fix m n :: nat
  show "gcd m n dvd m" and "gcd m n dvd n"
  proof (induct m n rule: gcd_nat_induct)
    case (step m n)
    then have "gcd n (m mod n) dvd m"
      by (metis dvd_mod_imp_dvd)
    with step show "gcd m n dvd m"
      by (simp add: gcd_non_0_nat)
  qed (simp_all add: gcd_0_nat gcd_non_0_nat)
next
  fix m n k :: nat
  assume "k dvd m" and "k dvd n"
  then show "k dvd gcd m n"
    by (induct m n rule: gcd_nat_induct) (simp_all add: gcd_non_0_nat dvd_mod gcd_0_nat)
qed (simp_all add: lcm_nat_def)

instance int :: ring_gcd
proof
  fix k l r :: int
  show [simp]: "gcd k l dvd k" "gcd k l dvd l"
    using gcd_dvd1 [of "nat \<bar>k\<bar>" "nat \<bar>l\<bar>"]
      gcd_dvd2 [of "nat \<bar>k\<bar>" "nat \<bar>l\<bar>"]
    by simp_all
  show "lcm k l = normalize (k * l div gcd k l)"
    using lcm_gcd [of "nat \<bar>k\<bar>" "nat \<bar>l\<bar>"]
    by (simp add: nat_eq_iff of_nat_div abs_mult abs_div)
  assume "r dvd k" "r dvd l"
  then show "r dvd gcd k l"
    using gcd_greatest [of "nat \<bar>r\<bar>" "nat \<bar>k\<bar>" "nat \<bar>l\<bar>"]
    by simp
qed simp

lemma gcd_le1_nat [simp]: "a \<noteq> 0 \<Longrightarrow> gcd a b \<le> a"
  for a b :: nat
  by (rule dvd_imp_le) auto

lemma gcd_le2_nat [simp]: "b \<noteq> 0 \<Longrightarrow> gcd a b \<le> b"
  for a b :: nat
  by (rule dvd_imp_le) auto

lemma gcd_le1_int [simp]: "a > 0 \<Longrightarrow> gcd a b \<le> a"
  for a b :: int
  by (rule zdvd_imp_le) auto

lemma gcd_le2_int [simp]: "b > 0 \<Longrightarrow> gcd a b \<le> b"
  for a b :: int
  by (rule zdvd_imp_le) auto

lemma gcd_pos_nat [simp]: "gcd m n > 0 \<longleftrightarrow> m \<noteq> 0 \<or> n \<noteq> 0"
  for m n :: nat
  using gcd_eq_0_iff [of m n] by arith

lemma gcd_pos_int [simp]: "gcd m n > 0 \<longleftrightarrow> m \<noteq> 0 \<or> n \<noteq> 0"
  for m n :: int
  using gcd_eq_0_iff [of m n] gcd_ge_0_int [of m n] by arith

lemma gcd_unique_nat: "d dvd a \<and> d dvd b \<and> (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  for d a :: nat
  using gcd_unique by fastforce

lemma gcd_unique_int:
  "d \<ge> 0 \<and> d dvd a \<and> d dvd b \<and> (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  for d a :: int
  using zdvd_antisym_nonneg by auto

interpretation gcd_nat:
  semilattice_neutr_order gcd "0::nat" Rings.dvd "\<lambda>m n. m dvd n \<and> m \<noteq> n"
  by standard (auto simp: gcd_unique_nat [symmetric] intro: dvd_antisym dvd_trans)

lemma gcd_proj1_if_dvd_int [simp]: "x dvd y \<Longrightarrow> gcd x y = \<bar>x\<bar>"
  for x y :: int
  by (metis abs_dvd_iff gcd_0_left_int gcd_unique_int)

lemma gcd_proj2_if_dvd_int [simp]: "y dvd x \<Longrightarrow> gcd x y = \<bar>y\<bar>"
  for x y :: int
  by (metis gcd_proj1_if_dvd_int gcd.commute)


text \<open>\<^medskip> Multiplication laws.\<close>

lemma gcd_mult_distrib_nat: "k * gcd m n = gcd (k * m) (k * n)"
  for k m n :: nat
  \<comment> \<open>@{cite \<open>page 27\<close> davenport92}\<close>
  by (simp add: gcd_mult_left)

lemma gcd_mult_distrib_int: "\<bar>k\<bar> * gcd m n = gcd (k * m) (k * n)"
  for k m n :: int
  by (simp add: gcd_mult_left abs_mult)

text \<open>\medskip Addition laws.\<close>

(* TODO: add the other variations? *)

lemma gcd_diff1_nat: "m \<ge> n \<Longrightarrow> gcd (m - n) n = gcd m n"
  for m n :: nat
  by (subst gcd_add1 [symmetric]) auto

lemma gcd_diff2_nat: "n \<ge> m \<Longrightarrow> gcd (n - m) n = gcd m n"
  for m n :: nat
  by (metis gcd.commute gcd_add2 gcd_diff1_nat le_add_diff_inverse2)

lemma gcd_non_0_int: 
  fixes x y :: int
  assumes "y > 0" shows "gcd x y = gcd y (x mod y)"
proof (cases "x mod y = 0")
  case False
  then have neg: "x mod y = y - (- x) mod y"
    by (simp add: zmod_zminus1_eq_if)
  have xy: "0 \<le> x mod y" 
    by (simp add: assms)
  show ?thesis
  proof (cases "x < 0")
    case True
    have "nat (- x mod y) \<le> nat y"
      by (simp add: assms dual_order.order_iff_strict)
    moreover have "gcd (nat (- x)) (nat y) = gcd (nat (- x mod y)) (nat y)"
      using True assms gcd_non_0_nat nat_mod_distrib by auto
    ultimately have "gcd (nat (- x)) (nat y) = gcd (nat y) (nat (x mod y))"
      using assms 
      by (simp add: neg nat_diff_distrib') (metis gcd.commute gcd_diff2_nat)
    with assms \<open>0 \<le> x mod y\<close> show ?thesis
      by (simp add: True dual_order.order_iff_strict gcd_int_def)
  next
    case False
    with assms xy have "gcd (nat x) (nat y) = gcd (nat y) (nat x mod nat y)"
      using gcd_red_nat by blast
    with False assms show ?thesis
      by (simp add: gcd_int_def nat_mod_distrib)
  qed
qed (use assms in auto)

lemma gcd_red_int: "gcd x y = gcd y (x mod y)"
  for x y :: int
proof (cases y "0::int" rule: linorder_cases)
  case less
  with gcd_non_0_int [of "- y" "- x"] show ?thesis
    by auto
next
  case greater
  with gcd_non_0_int [of y x] show ?thesis
    by auto
qed auto

(* TODO: differences, and all variations of addition rules
    as simplification rules for nat and int *)

(* TODO: add the three variations of these, and for ints? *)

lemma finite_divisors_nat [simp]: (* FIXME move *)
  fixes m :: nat
  assumes "m > 0"
  shows "finite {d. d dvd m}"
proof-
  from assms have "{d. d dvd m} \<subseteq> {d. d \<le> m}"
    by (auto dest: dvd_imp_le)
  then show ?thesis
    using finite_Collect_le_nat by (rule finite_subset)
qed

lemma finite_divisors_int [simp]:
  fixes i :: int
  assumes "i \<noteq> 0"
  shows "finite {d. d dvd i}"
proof -
  have "{d. \<bar>d\<bar> \<le> \<bar>i\<bar>} = {- \<bar>i\<bar>..\<bar>i\<bar>}"
    by (auto simp: abs_if)
  then have "finite {d. \<bar>d\<bar> \<le> \<bar>i\<bar>}"
    by simp
  from finite_subset [OF _ this] show ?thesis
    using assms by (simp add: dvd_imp_le_int subset_iff)
qed

lemma Max_divisors_self_nat [simp]: "n \<noteq> 0 \<Longrightarrow> Max {d::nat. d dvd n} = n"
  by (fastforce intro: antisym Max_le_iff[THEN iffD2] simp: dvd_imp_le)

lemma Max_divisors_self_int [simp]: 
  assumes "n \<noteq> 0" shows "Max {d::int. d dvd n} = \<bar>n\<bar>"
proof (rule antisym)
  show "Max {d. d dvd n} \<le> \<bar>n\<bar>"
    using assms by (auto intro: abs_le_D1 dvd_imp_le_int intro!: Max_le_iff [THEN iffD2])
qed (simp add: assms)

lemma gcd_is_Max_divisors_nat:
  fixes m n :: nat
  assumes "n > 0" shows "gcd m n = Max {d. d dvd m \<and> d dvd n}"
proof (rule Max_eqI[THEN sym], simp_all)
  show "finite {d. d dvd m \<and> d dvd n}"
    by (simp add: \<open>n > 0\<close>)
  show "\<And>y. y dvd m \<and> y dvd n \<Longrightarrow> y \<le> gcd m n"
    by (simp add: \<open>n > 0\<close> dvd_imp_le)
qed

lemma gcd_is_Max_divisors_int:
  fixes m n :: int
  assumes "n \<noteq> 0" shows "gcd m n = Max {d. d dvd m \<and> d dvd n}"
proof (rule Max_eqI[THEN sym], simp_all)
  show "finite {d. d dvd m \<and> d dvd n}"
    by (simp add: \<open>n \<noteq> 0\<close>)
  show "\<And>y. y dvd m \<and> y dvd n \<Longrightarrow> y \<le> gcd m n"
    by (simp add: \<open>n \<noteq> 0\<close> zdvd_imp_le)
qed

lemma gcd_code_int [code]: "gcd k l = \<bar>if l = 0 then k else gcd l (\<bar>k\<bar> mod \<bar>l\<bar>)\<bar>"
  for k l :: int
  using gcd_red_int [of "\<bar>k\<bar>" "\<bar>l\<bar>"] by simp

lemma coprime_Suc_left_nat [simp]:
  "coprime (Suc n) n"
  using coprime_add_one_left [of n] by simp

lemma coprime_Suc_right_nat [simp]:
  "coprime n (Suc n)"
  using coprime_Suc_left_nat [of n] by (simp add: ac_simps)

lemma coprime_diff_one_left_nat [simp]:
  "coprime (n - 1) n" if "n > 0" for n :: nat
  using that coprime_Suc_right_nat [of "n - 1"] by simp

lemma coprime_diff_one_right_nat [simp]:
  "coprime n (n - 1)" if "n > 0" for n :: nat
  using that coprime_diff_one_left_nat [of n] by (simp add: ac_simps)

lemma coprime_crossproduct_nat:
  fixes a b c d :: nat
  assumes "coprime a d" and "coprime b c"
  shows "a * c = b * d \<longleftrightarrow> a = b \<and> c = d"
  using assms coprime_crossproduct [of a d b c] by simp

lemma coprime_crossproduct_int:
  fixes a b c d :: int
  assumes "coprime a d" and "coprime b c"
  shows "\<bar>a\<bar> * \<bar>c\<bar> = \<bar>b\<bar> * \<bar>d\<bar> \<longleftrightarrow> \<bar>a\<bar> = \<bar>b\<bar> \<and> \<bar>c\<bar> = \<bar>d\<bar>"
  using assms coprime_crossproduct [of a d b c] by simp


subsection \<open>Bezout's theorem\<close>

text \<open>
  Function \<open>bezw\<close> returns a pair of witnesses to Bezout's theorem --
  see the theorems that follow the definition.
\<close>

fun bezw :: "nat \<Rightarrow> nat \<Rightarrow> int * int"
  where "bezw x y =
    (if y = 0 then (1, 0)
     else
      (snd (bezw y (x mod y)),
       fst (bezw y (x mod y)) - snd (bezw y (x mod y)) * int(x div y)))"

lemma bezw_0 [simp]: "bezw x 0 = (1, 0)"
  by simp

lemma bezw_non_0:
  "y > 0 \<Longrightarrow> bezw x y =
    (snd (bezw y (x mod y)), fst (bezw y (x mod y)) - snd (bezw y (x mod y)) * int(x div y))"
  by simp

declare bezw.simps [simp del]


lemma bezw_aux: "int (gcd x y) = fst (bezw x y) * int x + snd (bezw x y) * int y"
proof (induct x y rule: gcd_nat_induct)
  case (step m n)
  then have "fst (bezw m n) * int m + snd (bezw m n) * int n - int (gcd m n) 
             = int m * snd (bezw n (m mod n)) -
               (int (m mod n) * snd (bezw n (m mod n)) + int n * (int (m div n) * snd (bezw n (m mod n))))"
    by (simp add: bezw_non_0 gcd_non_0_nat field_simps)
  also have "\<dots> = int m * snd (bezw n (m mod n)) - (int (m mod n) + int (n * (m div n))) * snd (bezw n (m mod n))"
    by (simp add: distrib_right)
  also have "\<dots> = 0"
    by (metis cancel_comm_monoid_add_class.diff_cancel mod_mult_div_eq of_nat_add)
  finally show ?case
    by simp
qed auto


lemma bezout_int: "\<exists>u v. u * x + v * y = gcd x y"
  for x y :: int
proof -
  have aux: "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> \<exists>u v. u * x + v * y = gcd x y" for x y :: int
    apply (rule_tac x = "fst (bezw (nat x) (nat y))" in exI)
    apply (rule_tac x = "snd (bezw (nat x) (nat y))" in exI)
    by (simp add: bezw_aux gcd_int_def)
  consider "x \<ge> 0" "y \<ge> 0" | "x \<ge> 0" "y \<le> 0" | "x \<le> 0" "y \<ge> 0" | "x \<le> 0" "y \<le> 0"
    using linear by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (rule aux)
  next
    case 2
    then show ?thesis
      using aux [of x "-y"]
      by (metis gcd_neg2_int mult.commute mult_minus_right neg_0_le_iff_le)
  next
    case 3
    then show ?thesis
      using aux [of "-x" y]
      by (metis gcd.commute gcd_neg2_int mult.commute mult_minus_right neg_0_le_iff_le)
  next
    case 4
    then show ?thesis
      using aux [of "-x" "-y"]
      by (metis diff_0 diff_ge_0_iff_ge gcd_neg1_int gcd_neg2_int mult.commute mult_minus_right)
  qed
qed


text \<open>Versions of Bezout for \<open>nat\<close>, by Amine Chaieb.\<close>

lemma Euclid_induct [case_names swap zero add]:
  fixes P :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  assumes c: "\<And>a b. P a b \<longleftrightarrow> P b a"
    and z: "\<And>a. P a 0"
    and add: "\<And>a b. P a b \<longrightarrow> P a (a + b)"
  shows "P a b"
proof (induct "a + b" arbitrary: a b rule: less_induct)
  case less
  consider (eq) "a = b" | (lt) "a < b" "a + b - a < a + b" | "b = 0" | "b + a - b < a + b"
    by arith
  show ?case
  proof (cases a b rule: linorder_cases)
    case equal
    with add [rule_format, OF z [rule_format, of a]] show ?thesis by simp
  next
    case lt: less
    then consider "a = 0" | "a + b - a < a + b" by arith
    then show ?thesis
    proof cases
      case 1
      with z c show ?thesis by blast
    next
      case 2
      also have *: "a + b - a = a + (b - a)" using lt by arith
      finally have "a + (b - a) < a + b" .
      then have "P a (a + (b - a))" by (rule add [rule_format, OF less])
      then show ?thesis by (simp add: *[symmetric])
    qed
  next
    case gt: greater
    then consider "b = 0" | "b + a - b < a + b" by arith
    then show ?thesis
    proof cases
      case 1
      with z c show ?thesis by blast
    next
      case 2
      also have *: "b + a - b = b + (a - b)" using gt by arith
      finally have "b + (a - b) < a + b" .
      then have "P b (b + (a - b))" by (rule add [rule_format, OF less])
      then have "P b a" by (simp add: *[symmetric])
      with c show ?thesis by blast
    qed
  qed
qed

lemma bezout_lemma_nat:
  fixes d::nat
  shows "\<lbrakk>d dvd a; d dvd b; a * x = b * y + d \<or> b * x = a * y + d\<rbrakk>
    \<Longrightarrow> \<exists>x y. d dvd a \<and> d dvd a + b \<and> (a * x = (a + b) * y + d \<or> (a + b) * x = a * y + d)"
  apply auto
  apply (metis add_mult_distrib2 left_add_mult_distrib)
  apply (rule_tac x=x in exI)
  by (metis add_mult_distrib2 mult.commute add.assoc)

lemma bezout_add_nat: 
  "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and> (a * x = b * y + d \<or> b * x = a * y + d)"
proof (induct a b rule: Euclid_induct)
  case (swap a b)
  then show ?case
    by blast
next
  case (zero a)
  then show ?case
    by fastforce    
next
  case (add a b)
  then show ?case
    by (meson bezout_lemma_nat)
qed

lemma bezout1_nat: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and> (a * x - b * y = d \<or> b * x - a * y = d)"
  using bezout_add_nat[of a b]  by (metis add_diff_cancel_left')

lemma bezout_add_strong_nat:
  fixes a b :: nat
  assumes a: "a \<noteq> 0"
  shows "\<exists>d x y. d dvd a \<and> d dvd b \<and> a * x = b * y + d"
proof -
  consider d x y where "d dvd a" "d dvd b" "a * x = b * y + d"
         | d x y where "d dvd a" "d dvd b" "b * x = a * y + d"
    using bezout_add_nat [of a b] by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by blast
  next
    case H: 2
    show ?thesis
    proof (cases "b = 0")
      case True
      with H show ?thesis by simp
    next
      case False
      then have bp: "b > 0" by simp
      with dvd_imp_le [OF H(2)] consider "d = b" | "d < b"
        by atomize_elim auto
      then show ?thesis
      proof cases
        case 1
        with a H show ?thesis
          by (metis Suc_pred add.commute mult.commute mult_Suc_right neq0_conv)
      next
        case 2
        show ?thesis
        proof (cases "x = 0")
          case True
          with a H show ?thesis by simp
        next
          case x0: False
          then have xp: "x > 0" by simp
          from \<open>d < b\<close> have "d \<le> b - 1" by simp
          then have "d * b \<le> b * (b - 1)" by simp
          with xp mult_mono[of "1" "x" "d * b" "b * (b - 1)"]
          have dble: "d * b \<le> x * b * (b - 1)" using bp by simp
          from H(3) have "d + (b - 1) * (b * x) = d + (b - 1) * (a * y + d)"
            by simp
          then have "d + (b - 1) * a * y + (b - 1) * d = d + (b - 1) * b * x"
            by (simp only: mult.assoc distrib_left)
          then have "a * ((b - 1) * y) + d * (b - 1 + 1) = d + x * b * (b - 1)"
            by algebra
          then have "a * ((b - 1) * y) = d + x * b * (b - 1) - d * b"
            using bp by simp
          then have "a * ((b - 1) * y) = d + (x * b * (b - 1) - d * b)"
            by (simp only: diff_add_assoc[OF dble, of d, symmetric])
          then have "a * ((b - 1) * y) = b * (x * (b - 1) - d) + d"
            by (simp only: diff_mult_distrib2 ac_simps)
          with H(1,2) show ?thesis
            by blast
        qed
      qed
    qed
  qed
qed

lemma bezout_nat:
  fixes a :: nat
  assumes a: "a \<noteq> 0"
  shows "\<exists>x y. a * x = b * y + gcd a b"
proof -
  obtain d x y where d: "d dvd a" "d dvd b" and eq: "a * x = b * y + d"
    using bezout_add_strong_nat [OF a, of b] by blast
  from d have "d dvd gcd a b"
    by simp
  then obtain k where k: "gcd a b = d * k"
    unfolding dvd_def by blast
  from eq have "a * x * k = (b * y + d) * k"
    by auto
  then have "a * (x * k) = b * (y * k) + gcd a b"
    by (algebra add: k)
  then show ?thesis
    by blast
qed


subsection \<open>LCM properties on \<^typ>\<open>nat\<close> and \<^typ>\<open>int\<close>\<close>

lemma lcm_altdef_int [code]: "lcm a b = \<bar>a\<bar> * \<bar>b\<bar> div gcd a b"
  for a b :: int
  by (simp add: abs_mult lcm_gcd abs_div)
  
lemma prod_gcd_lcm_nat: "m * n = gcd m n * lcm m n"
  for m n :: nat
  by (simp add: lcm_gcd)

lemma prod_gcd_lcm_int: "\<bar>m\<bar> * \<bar>n\<bar> = gcd m n * lcm m n"
  for m n :: int
  by (simp add: lcm_gcd abs_div abs_mult)

lemma lcm_pos_nat: "m > 0 \<Longrightarrow> n > 0 \<Longrightarrow> lcm m n > 0"
  for m n :: nat
  using lcm_eq_0_iff [of m n] by auto

lemma lcm_pos_int: "m \<noteq> 0 \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> lcm m n > 0"
  for m n :: int
  by (simp add: less_le lcm_eq_0_iff)

lemma dvd_pos_nat: "n > 0 \<Longrightarrow> m dvd n \<Longrightarrow> m > 0"  (* FIXME move *)
  for m n :: nat
  by auto

lemma lcm_unique_nat:
  "a dvd d \<and> b dvd d \<and> (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  for a b d :: nat
  by (auto intro: dvd_antisym lcm_least)

lemma lcm_unique_int:
  "d \<ge> 0 \<and> a dvd d \<and> b dvd d \<and> (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  for a b d :: int
  using lcm_least zdvd_antisym_nonneg by auto

lemma lcm_proj2_if_dvd_nat [simp]: "x dvd y \<Longrightarrow> lcm x y = y"
  for x y :: nat
  by (simp add: lcm_proj2_if_dvd)

lemma lcm_proj2_if_dvd_int [simp]: "x dvd y \<Longrightarrow> lcm x y = \<bar>y\<bar>"
  for x y :: int
  by (simp add: lcm_proj2_if_dvd)

lemma lcm_proj1_if_dvd_nat [simp]: "x dvd y \<Longrightarrow> lcm y x = y"
  for x y :: nat
  by (subst lcm.commute) (erule lcm_proj2_if_dvd_nat)

lemma lcm_proj1_if_dvd_int [simp]: "x dvd y \<Longrightarrow> lcm y x = \<bar>y\<bar>"
  for x y :: int
  by (subst lcm.commute) (erule lcm_proj2_if_dvd_int)

lemma lcm_proj1_iff_nat [simp]: "lcm m n = m \<longleftrightarrow> n dvd m"
  for m n :: nat
  by (metis lcm_proj1_if_dvd_nat lcm_unique_nat)

lemma lcm_proj2_iff_nat [simp]: "lcm m n = n \<longleftrightarrow> m dvd n"
  for m n :: nat
  by (metis lcm_proj2_if_dvd_nat lcm_unique_nat)

lemma lcm_proj1_iff_int [simp]: "lcm m n = \<bar>m\<bar> \<longleftrightarrow> n dvd m"
  for m n :: int
  by (metis dvd_abs_iff lcm_proj1_if_dvd_int lcm_unique_int)

lemma lcm_proj2_iff_int [simp]: "lcm m n = \<bar>n\<bar> \<longleftrightarrow> m dvd n"
  for m n :: int
  by (metis dvd_abs_iff lcm_proj2_if_dvd_int lcm_unique_int)

lemma lcm_1_iff_nat [simp]: "lcm m n = Suc 0 \<longleftrightarrow> m = Suc 0 \<and> n = Suc 0"
  for m n :: nat
  using lcm_eq_1_iff [of m n] by simp

lemma lcm_1_iff_int [simp]: "lcm m n = 1 \<longleftrightarrow> (m = 1 \<or> m = -1) \<and> (n = 1 \<or> n = -1)"
  for m n :: int
  by auto


subsection \<open>The complete divisibility lattice on \<^typ>\<open>nat\<close> and \<^typ>\<open>int\<close>\<close>

text \<open>
  Lifting \<open>gcd\<close> and \<open>lcm\<close> to sets (\<open>Gcd\<close> / \<open>Lcm\<close>).
  \<open>Gcd\<close> is defined via \<open>Lcm\<close> to facilitate the proof that we have a complete lattice.
\<close>

instantiation nat :: semiring_Gcd
begin

interpretation semilattice_neutr_set lcm "1::nat"
  by standard simp_all

definition "Lcm M = (if finite M then F M else 0)" for M :: "nat set"

lemma Lcm_nat_empty: "Lcm {} = (1::nat)"
  by (simp add: Lcm_nat_def del: One_nat_def)

lemma Lcm_nat_insert: "Lcm (insert n M) = lcm n (Lcm M)" for n :: nat
  by (cases "finite M") (auto simp: Lcm_nat_def simp del: One_nat_def)

lemma Lcm_nat_infinite: "infinite M \<Longrightarrow> Lcm M = 0" for M :: "nat set"
  by (simp add: Lcm_nat_def)

lemma dvd_Lcm_nat [simp]:
  fixes M :: "nat set"
  assumes "m \<in> M"
  shows "m dvd Lcm M"
proof -
  from assms have "insert m M = M"
    by auto
  moreover have "m dvd Lcm (insert m M)"
    by (simp add: Lcm_nat_insert)
  ultimately show ?thesis
    by simp
qed

lemma Lcm_dvd_nat [simp]:
  fixes M :: "nat set"
  assumes "\<forall>m\<in>M. m dvd n"
  shows "Lcm M dvd n"
proof (cases "n > 0")
  case False
  then show ?thesis by simp
next
  case True
  then have "finite {d. d dvd n}"
    by (rule finite_divisors_nat)
  moreover have "M \<subseteq> {d. d dvd n}"
    using assms by fast
  ultimately have "finite M"
    by (rule rev_finite_subset)
  then show ?thesis
    using assms by (induct M) (simp_all add: Lcm_nat_empty Lcm_nat_insert)
qed

definition "Gcd M = Lcm {d. \<forall>m\<in>M. d dvd m}" for M :: "nat set"

instance
proof
  fix N :: "nat set"
  fix n :: nat
  show "Gcd N dvd n" if "n \<in> N"
    using that by (induct N rule: infinite_finite_induct) (auto simp: Gcd_nat_def)
  show "n dvd Gcd N" if "\<And>m. m \<in> N \<Longrightarrow> n dvd m"
    using that by (induct N rule: infinite_finite_induct) (auto simp: Gcd_nat_def)
  show "n dvd Lcm N" if "n \<in> N"
    using that by (induct N rule: infinite_finite_induct) auto
  show "Lcm N dvd n" if "\<And>m. m \<in> N \<Longrightarrow> m dvd n"
    using that by (induct N rule: infinite_finite_induct) auto
  show "normalize (Gcd N) = Gcd N" and "normalize (Lcm N) = Lcm N"
    by simp_all
qed

end

lemma Gcd_nat_eq_one: "1 \<in> N \<Longrightarrow> Gcd N = 1"
  for N :: "nat set"
  by (rule Gcd_eq_1_I) auto

instance nat :: semiring_gcd_mult_normalize
  by intro_classes (auto simp: unit_factor_nat_def)


text \<open>Alternative characterizations of Gcd:\<close>

lemma Gcd_eq_Max:
  fixes M :: "nat set"
  assumes "finite (M::nat set)" and "M \<noteq> {}" and "0 \<notin> M"
  shows "Gcd M = Max (\<Inter>m\<in>M. {d. d dvd m})"
proof (rule antisym)
  from assms obtain m where "m \<in> M" and "m > 0"
    by auto
  from \<open>m > 0\<close> have "finite {d. d dvd m}"
    by (blast intro: finite_divisors_nat)
  with \<open>m \<in> M\<close> have fin: "finite (\<Inter>m\<in>M. {d. d dvd m})"
    by blast
  from fin show "Gcd M \<le> Max (\<Inter>m\<in>M. {d. d dvd m})"
    by (auto intro: Max_ge Gcd_dvd)
  from fin show "Max (\<Inter>m\<in>M. {d. d dvd m}) \<le> Gcd M"
  proof (rule Max.boundedI, simp_all)
    show "(\<Inter>m\<in>M. {d. d dvd m}) \<noteq> {}"
      by auto
    show "\<And>a. \<forall>x\<in>M. a dvd x \<Longrightarrow> a \<le> Gcd M"
      by (meson Gcd_dvd Gcd_greatest \<open>0 < m\<close> \<open>m \<in> M\<close> dvd_imp_le dvd_pos_nat)
  qed
qed

lemma Gcd_remove0_nat: "finite M \<Longrightarrow> Gcd M = Gcd (M - {0})"
  for M :: "nat set"
proof (induct pred: finite)
  case (insert x M)
  then show ?case
    by (simp add: insert_Diff_if)
qed auto

lemma Lcm_in_lcm_closed_set_nat:
  fixes M :: "nat set" 
  assumes "finite M" "M \<noteq> {}" "\<And>m n. \<lbrakk>m \<in> M; n \<in> M\<rbrakk> \<Longrightarrow> lcm m n \<in> M"
  shows "Lcm M \<in> M"
  using assms
proof (induction M rule: finite_linorder_min_induct)
  case (insert x M)
  then have "\<And>m n. m \<in> M \<Longrightarrow> n \<in> M \<Longrightarrow> lcm m n \<in> M"
    by (metis dvd_lcm1 gr0I insert_iff lcm_pos_nat nat_dvd_not_less)
  with insert show ?case
    by simp (metis Lcm_nat_empty One_nat_def dvd_1_left dvd_lcm2)
qed auto

lemma Lcm_eq_Max_nat:
  fixes M :: "nat set" 
  assumes M: "finite M" "M \<noteq> {}" "0 \<notin> M" and lcm: "\<And>m n. \<lbrakk>m \<in> M; n \<in> M\<rbrakk> \<Longrightarrow> lcm m n \<in> M"
  shows "Lcm M = Max M"
proof (rule antisym)
  show "Lcm M \<le> Max M"
    by (simp add: Lcm_in_lcm_closed_set_nat \<open>finite M\<close> \<open>M \<noteq> {}\<close> lcm)
  show "Max M \<le> Lcm M"
    by (meson Lcm_0_iff Max_in M dvd_Lcm dvd_imp_le le_0_eq not_le)
qed

lemma mult_inj_if_coprime_nat:
  "inj_on f A \<Longrightarrow> inj_on g B \<Longrightarrow> (\<And>a b. \<lbrakk>a\<in>A; b\<in>B\<rbrakk> \<Longrightarrow> coprime (f a) (g b)) \<Longrightarrow>
    inj_on (\<lambda>(a, b). f a * g b) (A \<times> B)"
  for f :: "'a \<Rightarrow> nat" and g :: "'b \<Rightarrow> nat"
  by (auto simp: inj_on_def coprime_crossproduct_nat simp del: One_nat_def)


subsubsection \<open>Setwise GCD and LCM for integers\<close>

instantiation int :: Gcd
begin

definition Gcd_int :: "int set \<Rightarrow> int"
  where "Gcd K = int (GCD k\<in>K. (nat \<circ> abs) k)"

definition Lcm_int :: "int set \<Rightarrow> int"
  where "Lcm K = int (LCM k\<in>K. (nat \<circ> abs) k)"

instance ..

end

lemma Gcd_int_eq [simp]:
  "(GCD n\<in>N. int n) = int (Gcd N)"
  by (simp add: Gcd_int_def image_image)

lemma Gcd_nat_abs_eq [simp]:
  "(GCD k\<in>K. nat \<bar>k\<bar>) = nat (Gcd K)"
  by (simp add: Gcd_int_def)

lemma abs_Gcd_eq [simp]:
  "\<bar>Gcd K\<bar> = Gcd K" for K :: "int set"
  by (simp only: Gcd_int_def)

lemma Gcd_int_greater_eq_0 [simp]:
  "Gcd K \<ge> 0"
  for K :: "int set"
  using abs_ge_zero [of "Gcd K"] by simp

lemma Gcd_abs_eq [simp]:
  "(GCD k\<in>K. \<bar>k\<bar>) = Gcd K"
  for K :: "int set"
  by (simp only: Gcd_int_def image_image) simp

lemma Lcm_int_eq [simp]:
  "(LCM n\<in>N. int n) = int (Lcm N)"
  by (simp add: Lcm_int_def image_image)

lemma Lcm_nat_abs_eq [simp]:
  "(LCM k\<in>K. nat \<bar>k\<bar>) = nat (Lcm K)"
  by (simp add: Lcm_int_def)

lemma abs_Lcm_eq [simp]:
  "\<bar>Lcm K\<bar> = Lcm K" for K :: "int set"
  by (simp only: Lcm_int_def)

lemma Lcm_int_greater_eq_0 [simp]:
  "Lcm K \<ge> 0"
  for K :: "int set"
  using abs_ge_zero [of "Lcm K"] by simp

lemma Lcm_abs_eq [simp]:
  "(LCM k\<in>K. \<bar>k\<bar>) = Lcm K"
  for K :: "int set"
  by (simp only: Lcm_int_def image_image) simp

instance int :: semiring_Gcd
proof
  fix K :: "int set" and k :: int
  show "Gcd K dvd k" and "k dvd Lcm K" if "k \<in> K"
    using that Gcd_dvd [of "nat \<bar>k\<bar>" "(nat \<circ> abs) ` K"]
      dvd_Lcm [of "nat \<bar>k\<bar>" "(nat \<circ> abs) ` K"]
    by (simp_all add: comp_def)
  show "k dvd Gcd K" if "\<And>l. l \<in> K \<Longrightarrow> k dvd l"
  proof -
    have "nat \<bar>k\<bar> dvd (GCD k\<in>K. nat \<bar>k\<bar>)"
      by (rule Gcd_greatest) (use that in auto)
    then show ?thesis by simp
  qed
  show "Lcm K dvd k" if "\<And>l. l \<in> K \<Longrightarrow> l dvd k"
  proof -
    have "(LCM k\<in>K. nat \<bar>k\<bar>) dvd nat \<bar>k\<bar>"
      by (rule Lcm_least) (use that in auto)
    then show ?thesis by simp
  qed
qed (simp_all add: sgn_mult)

instance int :: semiring_gcd_mult_normalize
  by intro_classes (auto simp: sgn_mult)


subsection \<open>GCD and LCM on \<^typ>\<open>integer\<close>\<close>

instantiation integer :: gcd
begin

context
  includes integer.lifting
begin

lift_definition gcd_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" is gcd .

lift_definition lcm_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" is lcm .

end

instance ..

end

lifting_update integer.lifting
lifting_forget integer.lifting

context
  includes integer.lifting
begin

lemma gcd_code_integer [code]: "gcd k l = \<bar>if l = (0::integer) then k else gcd l (\<bar>k\<bar> mod \<bar>l\<bar>)\<bar>"
  by transfer (fact gcd_code_int)

lemma lcm_code_integer [code]: "lcm a b = \<bar>a\<bar> * \<bar>b\<bar> div gcd a b"
  for a b :: integer
  by transfer (fact lcm_altdef_int)

end

code_printing
  constant "gcd :: integer \<Rightarrow> _" \<rightharpoonup>
    (OCaml) "!(fun k l -> if Z.equal k Z.zero then/ Z.abs l else if Z.equal/ l Z.zero then Z.abs k else Z.gcd k l)"
  and (Haskell) "Prelude.gcd"
  and (Scala) "_.gcd'((_)')"
  \<comment> \<open>There is no gcd operation in the SML standard library, so no code setup for SML\<close>

text \<open>Some code equations\<close>

lemmas Gcd_nat_set_eq_fold [code] = Gcd_set_eq_fold [where ?'a = nat]
lemmas Lcm_nat_set_eq_fold [code] = Lcm_set_eq_fold [where ?'a = nat]
lemmas Gcd_int_set_eq_fold [code] = Gcd_set_eq_fold [where ?'a = int]
lemmas Lcm_int_set_eq_fold [code] = Lcm_set_eq_fold [where ?'a = int]

text \<open>Fact aliases.\<close>

lemma lcm_0_iff_nat [simp]: "lcm m n = 0 \<longleftrightarrow> m = 0 \<or> n = 0"
  for m n :: nat
  by (fact lcm_eq_0_iff)

lemma lcm_0_iff_int [simp]: "lcm m n = 0 \<longleftrightarrow> m = 0 \<or> n = 0"
  for m n :: int
  by (fact lcm_eq_0_iff)

lemma dvd_lcm_I1_nat [simp]: "k dvd m \<Longrightarrow> k dvd lcm m n"
  for k m n :: nat
  by (fact dvd_lcmI1)

lemma dvd_lcm_I2_nat [simp]: "k dvd n \<Longrightarrow> k dvd lcm m n"
  for k m n :: nat
  by (fact dvd_lcmI2)

lemma dvd_lcm_I1_int [simp]: "i dvd m \<Longrightarrow> i dvd lcm m n"
  for i m n :: int
  by (fact dvd_lcmI1)

lemma dvd_lcm_I2_int [simp]: "i dvd n \<Longrightarrow> i dvd lcm m n"
  for i m n :: int
  by (fact dvd_lcmI2)

lemmas Gcd_dvd_nat [simp] = Gcd_dvd [where ?'a = nat]
lemmas Gcd_dvd_int [simp] = Gcd_dvd [where ?'a = int]
lemmas Gcd_greatest_nat [simp] = Gcd_greatest [where ?'a = nat]
lemmas Gcd_greatest_int [simp] = Gcd_greatest [where ?'a = int]

lemma dvd_Lcm_int [simp]: "m \<in> M \<Longrightarrow> m dvd Lcm M"
  for M :: "int set"
  by (fact dvd_Lcm)

lemma gcd_neg_numeral_1_int [simp]: "gcd (- numeral n :: int) x = gcd (numeral n) x"
  by (fact gcd_neg1_int)

lemma gcd_neg_numeral_2_int [simp]: "gcd x (- numeral n :: int) = gcd x (numeral n)"
  by (fact gcd_neg2_int)

lemma gcd_proj1_if_dvd_nat [simp]: "x dvd y \<Longrightarrow> gcd x y = x"
  for x y :: nat
  by (fact gcd_nat.absorb1)

lemma gcd_proj2_if_dvd_nat [simp]: "y dvd x \<Longrightarrow> gcd x y = y"
  for x y :: nat
  by (fact gcd_nat.absorb2)

lemma Gcd_in:
  fixes A :: "nat set"
  assumes "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> gcd a b \<in> A"
  assumes "A \<noteq> {}"
  shows   "Gcd A \<in> A"
proof (cases "A = {0}")
  case False
  with assms obtain x where "x \<in> A" "x > 0"
    by auto
  thus "Gcd A \<in> A"
  proof (induction x rule: less_induct)
    case (less x)
    show ?case
    proof (cases "x = Gcd A")
      case False
      have "\<exists>y\<in>A. \<not>x dvd y"
        using False less.prems by (metis Gcd_dvd Gcd_greatest_nat gcd_nat.asym)
      then obtain y where y: "y \<in> A" "\<not>x dvd y"
        by blast
      have "gcd x y \<in> A"
        by (rule assms(1)) (use \<open>x \<in> A\<close> y in auto)
      moreover have "gcd x y < x"
        using \<open>x > 0\<close> y by (metis gcd_dvd1 gcd_dvd2 nat_dvd_not_less nat_neq_iff)
      moreover have "gcd x y > 0"
        using \<open>x > 0\<close> by auto
      ultimately show ?thesis using less.IH by blast
    qed (use less in auto)
  qed
qed auto

lemma bezout_gcd_nat':
  fixes a b :: nat
  shows "\<exists>x y. b * y \<le> a * x \<and> a * x - b * y = gcd a b \<or> a * y \<le> b * x \<and> b * x - a * y = gcd a b"
  using bezout_nat[of a b]
  by (metis add_diff_cancel_left' diff_zero gcd.commute gcd_0_nat
            le_add_same_cancel1 mult.right_neutral zero_le)

lemmas Lcm_eq_0_I_nat [simp] = Lcm_eq_0_I [where ?'a = nat]
lemmas Lcm_0_iff_nat [simp] = Lcm_0_iff [where ?'a = nat]
lemmas Lcm_least_int [simp] = Lcm_least [where ?'a = int]


subsection \<open>Characteristic of a semiring\<close>

definition (in semiring_1) semiring_char :: "'a itself \<Rightarrow> nat" 
  where "semiring_char _ = Gcd {n. of_nat n = (0 :: 'a)}"

context semiring_1
begin

context
  fixes CHAR :: nat
  defines "CHAR \<equiv> semiring_char (Pure.type :: 'a itself)"
begin

lemma of_nat_CHAR [simp]: "of_nat CHAR = (0 :: 'a)"
proof -
  have "CHAR \<in> {n. of_nat n = (0::'a)}"
    unfolding CHAR_def semiring_char_def
  proof (rule Gcd_in, clarify)
    fix a b :: nat
    assume *: "of_nat a = (0 :: 'a)" "of_nat b = (0 :: 'a)"
    show "of_nat (gcd a b) = (0 :: 'a)"
    proof (cases "a = 0")
      case False
      with bezout_nat obtain x y where "a * x = b * y + gcd a b"
        by blast
      hence "of_nat (a * x) = (of_nat (b * y + gcd a b) :: 'a)"
        by (rule arg_cong)
      thus "of_nat (gcd a b) = (0 :: 'a)"
        using * by simp
    qed (use * in auto)
  next
    have "of_nat 0 = (0 :: 'a)"
      by simp
    thus "{n. of_nat n = (0 :: 'a)} \<noteq> {}"
      by blast
  qed
  thus ?thesis
    by simp
qed

lemma of_nat_eq_0_iff_char_dvd: "of_nat n = (0 :: 'a) \<longleftrightarrow> CHAR dvd n"
proof
  assume "of_nat n = (0 :: 'a)"
  thus "CHAR dvd n"
    unfolding CHAR_def semiring_char_def by (intro Gcd_dvd) auto
next
  assume "CHAR dvd n"
  then obtain m where "n = CHAR * m"
    by auto
  thus "of_nat n = (0 :: 'a)"
    by simp
qed

lemma CHAR_eqI:
  assumes "of_nat c = (0 :: 'a)"
  assumes "\<And>x. of_nat x = (0 :: 'a) \<Longrightarrow> c dvd x"
  shows   "CHAR = c"
  using assms by (intro dvd_antisym) (auto simp: of_nat_eq_0_iff_char_dvd)

lemma CHAR_eq0_iff: "CHAR = 0 \<longleftrightarrow> (\<forall>n>0. of_nat n \<noteq> (0::'a))"
  by (auto simp: of_nat_eq_0_iff_char_dvd)

lemma CHAR_pos_iff: "CHAR > 0 \<longleftrightarrow> (\<exists>n>0. of_nat n = (0::'a))"
  using CHAR_eq0_iff neq0_conv by blast

lemma CHAR_eq_posI:
  assumes "c > 0" "of_nat c = (0 :: 'a)" "\<And>x. x > 0 \<Longrightarrow> x < c \<Longrightarrow> of_nat x \<noteq> (0 :: 'a)"
  shows   "CHAR = c"
proof (rule antisym)
  from assms have "CHAR > 0"
    by (auto simp: CHAR_pos_iff)
  from assms(3)[OF this] show "CHAR \<ge> c"
    by force
next
  have "CHAR dvd c"
    using assms by (auto simp: of_nat_eq_0_iff_char_dvd)
  thus "CHAR \<le> c"
    using \<open>c > 0\<close> by (intro dvd_imp_le) auto
qed

end
end

lemma (in semiring_char_0) CHAR_eq_0 [simp]: "semiring_char (Pure.type :: 'a itself) = 0"
  by (simp add: CHAR_eq0_iff)


(* nicer notation *)

syntax "_type_char" :: "type => nat" ("(1CHAR/(1'(_')))")

translations "CHAR('t)" => "CONST semiring_char (CONST Pure.type :: 't itself)"

print_translation \<open>
  let
    fun char_type_tr' ctxt [Const (\<^const_syntax>\<open>Pure.type\<close>, Type (_, [T]))] =
      Syntax.const \<^syntax_const>\<open>_type_char\<close> $ Syntax_Phases.term_of_typ ctxt T
  in [(\<^const_syntax>\<open>semiring_char\<close>, char_type_tr')] end
\<close>

end
