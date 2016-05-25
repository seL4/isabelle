(*  Authors:    Christophe Tabacznyj, Lawrence C. Paulson, Amine Chaieb,
                Thomas M. Rasmussen, Jeremy Avigad, Tobias Nipkow


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
imports Main
begin

subsection \<open>Abstract GCD and LCM\<close>

class gcd = zero + one + dvd +
  fixes gcd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and lcm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

abbreviation coprime :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "coprime x y \<equiv> gcd x y = 1"

end

class Gcd = gcd +
  fixes Gcd :: "'a set \<Rightarrow> 'a"
    and Lcm :: "'a set \<Rightarrow> 'a"
begin

abbreviation GREATEST_COMMON_DIVISOR :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "GREATEST_COMMON_DIVISOR A f \<equiv> Gcd (f ` A)"

abbreviation LEAST_COMMON_MULTIPLE :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "LEAST_COMMON_MULTIPLE A f \<equiv> Lcm (f ` A)"

end

syntax
  "_GCD1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3GCD _./ _)" [0, 10] 10)
  "_GCD"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3GCD _\<in>_./ _)" [0, 0, 10] 10)
  "_LCM1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3LCM _./ _)" [0, 10] 10)
  "_LCM"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3LCM _\<in>_./ _)" [0, 0, 10] 10)

translations
  "GCD x y. B"   \<rightleftharpoons> "GCD x. GCD y. B"
  "GCD x. B"     \<rightleftharpoons> "CONST GREATEST_COMMON_DIVISOR CONST UNIV (\<lambda>x. B)"
  "GCD x. B"     \<rightleftharpoons> "GCD x \<in> CONST UNIV. B"
  "GCD x\<in>A. B"   \<rightleftharpoons> "CONST GREATEST_COMMON_DIVISOR A (\<lambda>x. B)"
  "LCM x y. B"   \<rightleftharpoons> "LCM x. LCM y. B"
  "LCM x. B"     \<rightleftharpoons> "CONST LEAST_COMMON_MULTIPLE CONST UNIV (\<lambda>x. B)"
  "LCM x. B"     \<rightleftharpoons> "LCM x \<in> CONST UNIV. B"
  "LCM x\<in>A. B"   \<rightleftharpoons> "CONST LEAST_COMMON_MULTIPLE A (\<lambda>x. B)"

print_translation \<open>
  [Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax GREATEST_COMMON_DIVISOR} @{syntax_const "_GCD"},
    Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax LEAST_COMMON_MULTIPLE} @{syntax_const "_LCM"}]
\<close> \<comment> \<open>to avoid eta-contraction of body\<close>

class semiring_gcd = normalization_semidom + gcd +
  assumes gcd_dvd1 [iff]: "gcd a b dvd a"
    and gcd_dvd2 [iff]: "gcd a b dvd b"
    and gcd_greatest: "c dvd a \<Longrightarrow> c dvd b \<Longrightarrow> c dvd gcd a b"
    and normalize_gcd [simp]: "normalize (gcd a b) = gcd a b"
    and lcm_gcd: "lcm a b = normalize (a * b) div gcd a b"
begin    

lemma gcd_greatest_iff [simp]:
  "a dvd gcd b c \<longleftrightarrow> a dvd b \<and> a dvd c"
  by (blast intro!: gcd_greatest intro: dvd_trans)

lemma gcd_dvdI1:
  "a dvd c \<Longrightarrow> gcd a b dvd c"
  by (rule dvd_trans) (rule gcd_dvd1)

lemma gcd_dvdI2:
  "b dvd c \<Longrightarrow> gcd a b dvd c"
  by (rule dvd_trans) (rule gcd_dvd2)

lemma dvd_gcdD1:
  "a dvd gcd b c \<Longrightarrow> a dvd b"
  using gcd_dvd1 [of b c] by (blast intro: dvd_trans)

lemma dvd_gcdD2:
  "a dvd gcd b c \<Longrightarrow> a dvd c"
  using gcd_dvd2 [of b c] by (blast intro: dvd_trans)

lemma gcd_0_left [simp]:
  "gcd 0 a = normalize a"
  by (rule associated_eqI) simp_all

lemma gcd_0_right [simp]:
  "gcd a 0 = normalize a"
  by (rule associated_eqI) simp_all
  
lemma gcd_eq_0_iff [simp]:
  "gcd a b = 0 \<longleftrightarrow> a = 0 \<and> b = 0" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P then have "0 dvd gcd a b" by simp
  then have "0 dvd a" and "0 dvd b" by (blast intro: dvd_trans)+
  then show ?Q by simp
next
  assume ?Q then show ?P by simp
qed

lemma unit_factor_gcd:
  "unit_factor (gcd a b) = (if a = 0 \<and> b = 0 then 0 else 1)"
proof (cases "gcd a b = 0")
  case True then show ?thesis by simp
next
  case False
  have "unit_factor (gcd a b) * normalize (gcd a b) = gcd a b"
    by (rule unit_factor_mult_normalize)
  then have "unit_factor (gcd a b) * gcd a b = gcd a b"
    by simp
  then have "unit_factor (gcd a b) * gcd a b div gcd a b = gcd a b div gcd a b"
    by simp
  with False show ?thesis by simp
qed

lemma is_unit_gcd [simp]:
  "is_unit (gcd a b) \<longleftrightarrow> coprime a b"
  by (cases "a = 0 \<and> b = 0") (auto simp add: unit_factor_gcd dest: is_unit_unit_factor)

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

lemma gcd_self [simp]:
  "gcd a a = normalize a"
proof -
  have "a dvd gcd a a"
    by (rule gcd_greatest) simp_all
  then show ?thesis
    by (auto intro: associated_eqI)
qed

lemma gcd_left_idem [simp]:
  "gcd a (gcd a b) = gcd a b"
  by (auto intro: associated_eqI)

lemma gcd_right_idem [simp]:
  "gcd (gcd a b) b = gcd a b"
  unfolding gcd.commute [of a] gcd.commute [of "gcd b a"] by simp

lemma coprime_1_left [simp]:
  "coprime 1 a"
  by (rule associated_eqI) simp_all

lemma coprime_1_right [simp]:
  "coprime a 1"
  using coprime_1_left [of a] by (simp add: ac_simps)

lemma gcd_mult_left:
  "gcd (c * a) (c * b) = normalize c * gcd a b"
proof (cases "c = 0")
  case True then show ?thesis by simp
next
  case False
  then have "c * gcd a b dvd gcd (c * a) (c * b)"
    by (auto intro: gcd_greatest)
  moreover from calculation False have "gcd (c * a) (c * b) dvd c * gcd a b"
    by (metis div_dvd_iff_mult dvd_mult_left gcd_dvd1 gcd_dvd2 gcd_greatest mult_commute)
  ultimately have "normalize (gcd (c * a) (c * b)) = normalize (c * gcd a b)"
    by (auto intro: associated_eqI)
  then show ?thesis by (simp add: normalize_mult)
qed

lemma gcd_mult_right:
  "gcd (a * c) (b * c) = gcd b a * normalize c"
  using gcd_mult_left [of c a b] by (simp add: ac_simps)

lemma mult_gcd_left:
  "c * gcd a b = unit_factor c * gcd (c * a) (c * b)"
  by (simp add: gcd_mult_left mult.assoc [symmetric])

lemma mult_gcd_right:
  "gcd a b * c = gcd (a * c) (b * c) * unit_factor c"
  using mult_gcd_left [of c a b] by (simp add: ac_simps)

lemma dvd_lcm1 [iff]:
  "a dvd lcm a b"
proof -
  have "normalize (a * b) div gcd a b = normalize a * (normalize b div gcd a b)"
    by (simp add: lcm_gcd normalize_mult div_mult_swap)
  then show ?thesis
    by (simp add: lcm_gcd)
qed
  
lemma dvd_lcm2 [iff]:
  "b dvd lcm a b"
proof -
  have "normalize (a * b) div gcd a b = normalize b * (normalize a div gcd a b)"
    by (simp add: lcm_gcd normalize_mult div_mult_swap ac_simps)
  then show ?thesis
    by (simp add: lcm_gcd)
qed

lemma dvd_lcmI1:
  "a dvd b \<Longrightarrow> a dvd lcm b c"
  by (rule dvd_trans) (assumption, blast) 

lemma dvd_lcmI2:
  "a dvd c \<Longrightarrow> a dvd lcm b c"
  by (rule dvd_trans) (assumption, blast)

lemma lcm_dvdD1:
  "lcm a b dvd c \<Longrightarrow> a dvd c"
  using dvd_lcm1 [of a b] by (blast intro: dvd_trans)

lemma lcm_dvdD2:
  "lcm a b dvd c \<Longrightarrow> b dvd c"
  using dvd_lcm2 [of a b] by (blast intro: dvd_trans)

lemma lcm_least:
  assumes "a dvd c" and "b dvd c"
  shows "lcm a b dvd c"
proof (cases "c = 0")
  case True then show ?thesis by simp
next
  case False then have U: "is_unit (unit_factor c)" by simp
  show ?thesis
  proof (cases "gcd a b = 0")
    case True with assms show ?thesis by simp
  next
    case False then have "a \<noteq> 0 \<or> b \<noteq> 0" by simp
    with \<open>c \<noteq> 0\<close> assms have "a * b dvd a * c" "a * b dvd c * b"
      by (simp_all add: mult_dvd_mono)
    then have "normalize (a * b) dvd gcd (a * c) (b * c)"
      by (auto intro: gcd_greatest simp add: ac_simps)
    then have "normalize (a * b) dvd gcd (a * c) (b * c) * unit_factor c"
      using U by (simp add: dvd_mult_unit_iff)
    then have "normalize (a * b) dvd gcd a b * c"
      by (simp add: mult_gcd_right [of a b c])
    then have "normalize (a * b) div gcd a b dvd c"
      using False by (simp add: div_dvd_iff_mult ac_simps)
    then show ?thesis by (simp add: lcm_gcd)
  qed
qed

lemma lcm_least_iff [simp]:
  "lcm a b dvd c \<longleftrightarrow> a dvd c \<and> b dvd c"
  by (blast intro!: lcm_least intro: dvd_trans)

lemma normalize_lcm [simp]:
  "normalize (lcm a b) = lcm a b"
  by (simp add: lcm_gcd dvd_normalize_div)

lemma lcm_0_left [simp]:
  "lcm 0 a = 0"
  by (simp add: lcm_gcd)
  
lemma lcm_0_right [simp]:
  "lcm a 0 = 0"
  by (simp add: lcm_gcd)

lemma lcm_eq_0_iff:
  "lcm a b = 0 \<longleftrightarrow> a = 0 \<or> b = 0" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P then have "0 dvd lcm a b" by simp
  then have "0 dvd normalize (a * b) div gcd a b"
    by (simp add: lcm_gcd)
  then have "0 * gcd a b dvd normalize (a * b)"
    using dvd_div_iff_mult [of "gcd a b" _ 0] by (cases "gcd a b = 0") simp_all
  then have "normalize (a * b) = 0"
    by simp
  then show ?Q by simp
next
  assume ?Q then show ?P by auto
qed

lemma lcm_eq_1_iff [simp]:
  "lcm a b = 1 \<longleftrightarrow> is_unit a \<and> is_unit b"
  by (auto intro: associated_eqI)

lemma unit_factor_lcm :
  "unit_factor (lcm a b) = (if a = 0 \<or> b = 0 then 0 else 1)"
  by (simp add: unit_factor_gcd dvd_unit_factor_div lcm_gcd)

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

lemma lcm_self [simp]:
  "lcm a a = normalize a"
proof -
  have "lcm a a dvd a"
    by (rule lcm_least) simp_all
  then show ?thesis
    by (auto intro: associated_eqI)
qed

lemma lcm_left_idem [simp]:
  "lcm a (lcm a b) = lcm a b"
  by (auto intro: associated_eqI)

lemma lcm_right_idem [simp]:
  "lcm (lcm a b) b = lcm a b"
  unfolding lcm.commute [of a] lcm.commute [of "lcm b a"] by simp

lemma gcd_mult_lcm [simp]:
  "gcd a b * lcm a b = normalize a * normalize b"
  by (simp add: lcm_gcd normalize_mult)

lemma lcm_mult_gcd [simp]:
  "lcm a b * gcd a b = normalize a * normalize b"
  using gcd_mult_lcm [of a b] by (simp add: ac_simps) 

lemma gcd_lcm:
  assumes "a \<noteq> 0" and "b \<noteq> 0"
  shows "gcd a b = normalize (a * b) div lcm a b"
proof -
  from assms have "lcm a b \<noteq> 0"
    by (simp add: lcm_eq_0_iff)
  have "gcd a b * lcm a b = normalize a * normalize b" by simp
  then have "gcd a b * lcm a b div lcm a b = normalize (a * b) div lcm a b"
    by (simp_all add: normalize_mult)
  with \<open>lcm a b \<noteq> 0\<close> show ?thesis
    using nonzero_mult_divide_cancel_right [of "lcm a b" "gcd a b"] by simp
qed

lemma lcm_1_left [simp]:
  "lcm 1 a = normalize a"
  by (simp add: lcm_gcd)

lemma lcm_1_right [simp]:
  "lcm a 1 = normalize a"
  by (simp add: lcm_gcd)
  
lemma lcm_mult_left:
  "lcm (c * a) (c * b) = normalize c * lcm a b"
  by (cases "c = 0")
    (simp_all add: gcd_mult_right lcm_gcd div_mult_swap normalize_mult ac_simps,
      simp add: dvd_div_mult2_eq mult.left_commute [of "normalize c", symmetric])

lemma lcm_mult_right:
  "lcm (a * c) (b * c) = lcm b a * normalize c"
  using lcm_mult_left [of c a b] by (simp add: ac_simps)

lemma mult_lcm_left:
  "c * lcm a b = unit_factor c * lcm (c * a) (c * b)"
  by (simp add: lcm_mult_left mult.assoc [symmetric])

lemma mult_lcm_right:
  "lcm a b * c = lcm (a * c) (b * c) * unit_factor c"
  using mult_lcm_left [of c a b] by (simp add: ac_simps)

lemma gcdI:
  assumes "c dvd a" and "c dvd b" and greatest: "\<And>d. d dvd a \<Longrightarrow> d dvd b \<Longrightarrow> d dvd c"
    and "normalize c = c"
  shows "c = gcd a b"
  by (rule associated_eqI) (auto simp: assms intro: gcd_greatest)

lemma gcd_unique: "d dvd a \<and> d dvd b \<and> 
    normalize d = d \<and>
    (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  by rule (auto intro: gcdI simp: gcd_greatest)

lemma gcd_dvd_prod: "gcd a b dvd k * b"
  using mult_dvd_mono [of 1] by auto

lemma gcd_proj2_if_dvd: "b dvd a \<Longrightarrow> gcd a b = normalize b"
  by (rule gcdI [symmetric]) simp_all

lemma gcd_proj1_if_dvd: "a dvd b \<Longrightarrow> gcd a b = normalize a"
  by (rule gcdI [symmetric]) simp_all

lemma gcd_proj1_iff: "gcd m n = normalize m \<longleftrightarrow> m dvd n"
proof
  assume A: "gcd m n = normalize m"
  show "m dvd n"
  proof (cases "m = 0")
    assume [simp]: "m \<noteq> 0"
    from A have B: "m = gcd m n * unit_factor m"
      by (simp add: unit_eq_div2)
    show ?thesis by (subst B, simp add: mult_unit_dvd_iff)
  qed (insert A, simp)
next
  assume "m dvd n"
  then show "gcd m n = normalize m" by (rule gcd_proj1_if_dvd)
qed
  
lemma gcd_proj2_iff: "gcd m n = normalize n \<longleftrightarrow> n dvd m"
  using gcd_proj1_iff [of n m] by (simp add: ac_simps)

lemma gcd_mult_distrib': "normalize c * gcd a b = gcd (c * a) (c * b)"
  by (rule gcdI) (auto simp: normalize_mult gcd_greatest mult_dvd_mono gcd_mult_left[symmetric])

lemma gcd_mult_distrib:
  "k * gcd a b = gcd (k * a) (k * b) * unit_factor k"
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

lemma lcm_mult_unit1:
  "is_unit a \<Longrightarrow> lcm (b * a) c = lcm b c"
  by (rule associated_eqI) (simp_all add: mult_unit_dvd_iff dvd_lcmI1)

lemma lcm_mult_unit2:
  "is_unit a \<Longrightarrow> lcm b (c * a) = lcm b c"
  using lcm_mult_unit1 [of a c b] by (simp add: ac_simps)

lemma lcm_div_unit1:
  "is_unit a \<Longrightarrow> lcm (b div a) c = lcm b c"
  by (erule is_unitE [of _ b]) (simp add: lcm_mult_unit1) 

lemma lcm_div_unit2:
  "is_unit a \<Longrightarrow> lcm b (c div a) = lcm b c"
  by (erule is_unitE [of _ c]) (simp add: lcm_mult_unit2)

lemma normalize_lcm_left [simp]:
  "lcm (normalize a) b = lcm a b"
proof (cases "a = 0")
  case True then show ?thesis
    by simp
next
  case False then have "is_unit (unit_factor a)"
    by simp
  moreover have "normalize a = a div unit_factor a"
    by simp
  ultimately show ?thesis
    by (simp only: lcm_div_unit1)
qed

lemma normalize_lcm_right [simp]:
  "lcm a (normalize b) = lcm a b"
  using normalize_lcm_left [of b a] by (simp add: ac_simps)

lemma gcd_mult_unit1: "is_unit a \<Longrightarrow> gcd (b * a) c = gcd b c"
  apply (rule gcdI)
  apply simp_all
  apply (rule dvd_trans, rule gcd_dvd1, simp add: unit_simps)
  done

lemma gcd_mult_unit2: "is_unit a \<Longrightarrow> gcd b (c * a) = gcd b c"
  by (subst gcd.commute, subst gcd_mult_unit1, assumption, rule gcd.commute)

lemma gcd_div_unit1: "is_unit a \<Longrightarrow> gcd (b div a) c = gcd b c"
  by (erule is_unitE [of _ b]) (simp add: gcd_mult_unit1)

lemma gcd_div_unit2: "is_unit a \<Longrightarrow> gcd b (c div a) = gcd b c"
  by (erule is_unitE [of _ c]) (simp add: gcd_mult_unit2)

lemma normalize_gcd_left [simp]:
  "gcd (normalize a) b = gcd a b"
proof (cases "a = 0")
  case True then show ?thesis
    by simp
next
  case False then have "is_unit (unit_factor a)"
    by simp
  moreover have "normalize a = a div unit_factor a"
    by simp
  ultimately show ?thesis
    by (simp only: gcd_div_unit1)
qed

lemma normalize_gcd_right [simp]:
  "gcd a (normalize b) = gcd a b"
  using normalize_gcd_left [of b a] by (simp add: ac_simps)

lemma comp_fun_idem_gcd: "comp_fun_idem gcd"
  by standard (simp_all add: fun_eq_iff ac_simps)

lemma comp_fun_idem_lcm: "comp_fun_idem lcm"
  by standard (simp_all add: fun_eq_iff ac_simps)

lemma gcd_dvd_antisym:
  "gcd a b dvd gcd c d \<Longrightarrow> gcd c d dvd gcd a b \<Longrightarrow> gcd a b = gcd c d"
proof (rule gcdI)
  assume A: "gcd a b dvd gcd c d" and B: "gcd c d dvd gcd a b"
  have "gcd c d dvd c" by simp
  with A show "gcd a b dvd c" by (rule dvd_trans)
  have "gcd c d dvd d" by simp
  with A show "gcd a b dvd d" by (rule dvd_trans)
  show "normalize (gcd a b) = gcd a b"
    by simp
  fix l assume "l dvd c" and "l dvd d"
  hence "l dvd gcd c d" by (rule gcd_greatest)
  from this and B show "l dvd gcd a b" by (rule dvd_trans)
qed

lemma coprime_dvd_mult:
  assumes "coprime a b" and "a dvd c * b"
  shows "a dvd c"
proof (cases "c = 0")
  case True then show ?thesis by simp
next
  case False
  then have unit: "is_unit (unit_factor c)" by simp
  from \<open>coprime a b\<close> mult_gcd_left [of c a b]
  have "gcd (c * a) (c * b) * unit_factor c = c"
    by (simp add: ac_simps)
  moreover from \<open>a dvd c * b\<close> have "a dvd gcd (c * a) (c * b) * unit_factor c"
    by (simp add: dvd_mult_unit_iff unit)
  ultimately show ?thesis by simp
qed

lemma coprime_dvd_mult_iff:
  assumes "coprime a c"
  shows "a dvd b * c \<longleftrightarrow> a dvd b"
  using assms by (auto intro: coprime_dvd_mult)

lemma gcd_mult_cancel:
  "coprime c b \<Longrightarrow> gcd (c * a) b = gcd a b"
  apply (rule associated_eqI)
  apply (rule gcd_greatest)
  apply (rule_tac b = c in coprime_dvd_mult)
  apply (simp add: gcd.assoc)
  apply (simp_all add: ac_simps)
  done

lemma coprime_crossproduct:
  fixes a b c d
  assumes "coprime a d" and "coprime b c"
  shows "normalize a * normalize c = normalize b * normalize d
    \<longleftrightarrow> normalize a = normalize b \<and> normalize c = normalize d" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs then show ?lhs by simp
next
  assume ?lhs
  from \<open>?lhs\<close> have "normalize a dvd normalize b * normalize d"
    by (auto intro: dvdI dest: sym)
  with \<open>coprime a d\<close> have "a dvd b"
    by (simp add: coprime_dvd_mult_iff normalize_mult [symmetric])
  from \<open>?lhs\<close> have "normalize b dvd normalize a * normalize c"
    by (auto intro: dvdI dest: sym)
  with \<open>coprime b c\<close> have "b dvd a"
    by (simp add: coprime_dvd_mult_iff normalize_mult [symmetric])
  from \<open>?lhs\<close> have "normalize c dvd normalize d * normalize b"
    by (auto intro: dvdI dest: sym simp add: mult.commute)
  with \<open>coprime b c\<close> have "c dvd d"
    by (simp add: coprime_dvd_mult_iff gcd.commute normalize_mult [symmetric])
  from \<open>?lhs\<close> have "normalize d dvd normalize c * normalize a"
    by (auto intro: dvdI dest: sym simp add: mult.commute)
  with \<open>coprime a d\<close> have "d dvd c"
    by (simp add: coprime_dvd_mult_iff gcd.commute normalize_mult [symmetric])
  from \<open>a dvd b\<close> \<open>b dvd a\<close> have "normalize a = normalize b"
    by (rule associatedI)
  moreover from \<open>c dvd d\<close> \<open>d dvd c\<close> have "normalize c = normalize d"
    by (rule associatedI)
  ultimately show ?rhs ..
qed

lemma gcd_add1 [simp]: "gcd (m + n) n = gcd m n"
  by (rule gcdI [symmetric]) (simp_all add: dvd_add_left_iff)

lemma gcd_add2 [simp]: "gcd m (m + n) = gcd m n"
  using gcd_add1 [of n m] by (simp add: ac_simps)

lemma gcd_add_mult: "gcd m (k * m + n) = gcd m n"
  by (rule gcdI [symmetric]) (simp_all add: dvd_add_right_iff)

lemma coprimeI: "(\<And>l. \<lbrakk>l dvd a; l dvd b\<rbrakk> \<Longrightarrow> l dvd 1) \<Longrightarrow> gcd a b = 1"
  by (rule sym, rule gcdI, simp_all)

lemma coprime: "gcd a b = 1 \<longleftrightarrow> (\<forall>d. d dvd a \<and> d dvd b \<longleftrightarrow> is_unit d)"
  by (auto intro: coprimeI gcd_greatest dvd_gcdD1 dvd_gcdD2)

lemma div_gcd_coprime:
  assumes nz: "a \<noteq> 0 \<or> b \<noteq> 0"
  shows "coprime (a div gcd a b) (b div gcd a b)"
proof -
  let ?g = "gcd a b"
  let ?a' = "a div ?g"
  let ?b' = "b div ?g"
  let ?g' = "gcd ?a' ?b'"
  have dvdg: "?g dvd a" "?g dvd b" by simp_all
  have dvdg': "?g' dvd ?a'" "?g' dvd ?b'" by simp_all
  from dvdg dvdg' obtain ka kb ka' kb' where
      kab: "a = ?g * ka" "b = ?g * kb" "?a' = ?g' * ka'" "?b' = ?g' * kb'"
    unfolding dvd_def by blast
  from this [symmetric] have "?g * ?a' = (?g * ?g') * ka'" "?g * ?b' = (?g * ?g') * kb'"
    by (simp_all add: mult.assoc mult.left_commute [of "gcd a b"])
  then have dvdgg':"?g * ?g' dvd a" "?g* ?g' dvd b"
    by (auto simp add: dvd_mult_div_cancel [OF dvdg(1)]
      dvd_mult_div_cancel [OF dvdg(2)] dvd_def)
  have "?g \<noteq> 0" using nz by simp
  moreover from gcd_greatest [OF dvdgg'] have "?g * ?g' dvd ?g" .
  thm dvd_mult_cancel_left
  ultimately show ?thesis using dvd_times_left_cancel_iff [of "gcd a b" _ 1] by simp
qed


lemma divides_mult:
  assumes "a dvd c" and nr: "b dvd c" and "coprime a b"
  shows "a * b dvd c"
proof-
  from \<open>b dvd c\<close> obtain b' where"c = b * b'" ..
  with \<open>a dvd c\<close> have "a dvd b' * b"
    by (simp add: ac_simps)
  with \<open>coprime a b\<close> have "a dvd b'"
    by (simp add: coprime_dvd_mult_iff)
  then obtain a' where "b' = a * a'" ..
  with \<open>c = b * b'\<close> have "c = (a * b) * a'"
    by (simp add: ac_simps)
  then show ?thesis ..
qed

lemma coprime_lmult:
  assumes dab: "gcd d (a * b) = 1" 
  shows "gcd d a = 1"
proof (rule coprimeI)
  fix l assume "l dvd d" and "l dvd a"
  hence "l dvd a * b" by simp
  with \<open>l dvd d\<close> and dab show "l dvd 1" by (auto intro: gcd_greatest)
qed

lemma coprime_rmult:
  assumes dab: "gcd d (a * b) = 1"
  shows "gcd d b = 1"
proof (rule coprimeI)
  fix l assume "l dvd d" and "l dvd b"
  hence "l dvd a * b" by simp
  with \<open>l dvd d\<close> and dab show "l dvd 1" by (auto intro: gcd_greatest)
qed

lemma coprime_mult:
  assumes da: "coprime d a" and db: "coprime d b"
  shows "coprime d (a * b)"
  apply (subst gcd.commute)
  using da apply (subst gcd_mult_cancel)
  apply (subst gcd.commute, assumption)
  apply (subst gcd.commute, rule db)
  done

lemma coprime_mul_eq: "gcd d (a * b) = 1 \<longleftrightarrow> gcd d a = 1 \<and> gcd d b = 1"
  using coprime_rmult[of d a b] coprime_lmult[of d a b] coprime_mult[of d a b] by blast

lemma gcd_coprime:
  assumes c: "gcd a b \<noteq> 0" and a: "a = a' * gcd a b" and b: "b = b' * gcd a b"
  shows "gcd a' b' = 1"
proof -
  from c have "a \<noteq> 0 \<or> b \<noteq> 0" by simp
  with div_gcd_coprime have "gcd (a div gcd a b) (b div gcd a b) = 1" .
  also from assms have "a div gcd a b = a'" using dvd_div_eq_mult local.gcd_dvd1 by blast
  also from assms have "b div gcd a b = b'" using dvd_div_eq_mult local.gcd_dvd1 by blast
  finally show ?thesis .
qed

lemma coprime_power:
  assumes "0 < n"
  shows "gcd a (b ^ n) = 1 \<longleftrightarrow> gcd a b = 1"
using assms proof (induct n)
  case (Suc n) then show ?case
    by (cases n) (simp_all add: coprime_mul_eq)
qed simp

lemma gcd_coprime_exists:
  assumes nz: "gcd a b \<noteq> 0"
  shows "\<exists>a' b'. a = a' * gcd a b \<and> b = b' * gcd a b \<and> gcd a' b' = 1"
  apply (rule_tac x = "a div gcd a b" in exI)
  apply (rule_tac x = "b div gcd a b" in exI)
  apply (insert nz, auto intro: div_gcd_coprime)
  done

lemma coprime_exp:
  "gcd d a = 1 \<Longrightarrow> gcd d (a^n) = 1"
  by (induct n, simp_all add: coprime_mult)

lemma coprime_exp_left:
  assumes "coprime a b"
  shows "coprime (a ^ n) b"
  using assms by (induct n) (simp_all add: gcd_mult_cancel)

lemma coprime_exp2:
  assumes "coprime a b"
  shows "coprime (a ^ n) (b ^ m)"
proof (rule coprime_exp_left)
  from assms show "coprime a (b ^ m)"
    by (induct m) (simp_all add: gcd_mult_cancel gcd.commute [of a])
qed

lemma gcd_exp:
  "gcd (a ^ n) (b ^ n) = gcd a b ^ n"
proof (cases "a = 0 \<and> b = 0")
  case True
  then show ?thesis by (cases n) simp_all
next
  case False
  then have "1 = gcd ((a div gcd a b) ^ n) ((b div gcd a b) ^ n)"
    using coprime_exp2[OF div_gcd_coprime[of a b], of n n, symmetric] by simp
  then have "gcd a b ^ n = gcd a b ^ n * ..." by simp
  also note gcd_mult_distrib
  also have "unit_factor (gcd a b ^ n) = 1"
    using False by (auto simp add: unit_factor_power unit_factor_gcd)
  also have "(gcd a b)^n * (a div gcd a b)^n = a^n"
    by (subst ac_simps, subst div_power, simp, rule dvd_div_mult_self, rule dvd_power_same, simp)
  also have "(gcd a b)^n * (b div gcd a b)^n = b^n"
    by (subst ac_simps, subst div_power, simp, rule dvd_div_mult_self, rule dvd_power_same, simp)
  finally show ?thesis by simp
qed

lemma coprime_common_divisor: 
  "gcd a b = 1 \<Longrightarrow> a dvd a \<Longrightarrow> a dvd b \<Longrightarrow> is_unit a"
  apply (subgoal_tac "a dvd gcd a b")
  apply simp
  apply (erule (1) gcd_greatest)
  done

lemma division_decomp: 
  assumes dc: "a dvd b * c"
  shows "\<exists>b' c'. a = b' * c' \<and> b' dvd b \<and> c' dvd c"
proof (cases "gcd a b = 0")
  assume "gcd a b = 0"
  hence "a = 0 \<and> b = 0" by simp
  hence "a = 0 * c \<and> 0 dvd b \<and> c dvd c" by simp
  then show ?thesis by blast
next
  let ?d = "gcd a b"
  assume "?d \<noteq> 0"
  from gcd_coprime_exists[OF this]
    obtain a' b' where ab': "a = a' * ?d" "b = b' * ?d" "gcd a' b' = 1"
    by blast
  from ab'(1) have "a' dvd a" unfolding dvd_def by blast
  with dc have "a' dvd b*c" using dvd_trans[of a' a "b*c"] by simp
  from dc ab'(1,2) have "a'*?d dvd (b'*?d) * c" by simp
  hence "?d * a' dvd ?d * (b' * c)" by (simp add: mult_ac)
  with \<open>?d \<noteq> 0\<close> have "a' dvd b' * c" by simp
  with coprime_dvd_mult[OF ab'(3)] 
    have "a' dvd c" by (subst (asm) ac_simps, blast)
  with ab'(1) have "a = ?d * a' \<and> ?d dvd b \<and> a' dvd c" by (simp add: mult_ac)
  then show ?thesis by blast
qed

lemma pow_divs_pow:
  assumes ab: "a ^ n dvd b ^ n" and n: "n \<noteq> 0"
  shows "a dvd b"
proof (cases "gcd a b = 0")
  assume "gcd a b = 0"
  then show ?thesis by simp
next
  let ?d = "gcd a b"
  assume "?d \<noteq> 0"
  from n obtain m where m: "n = Suc m" by (cases n, simp_all)
  from \<open>?d \<noteq> 0\<close> have zn: "?d ^ n \<noteq> 0" by (rule power_not_zero)
  from gcd_coprime_exists[OF \<open>?d \<noteq> 0\<close>]
    obtain a' b' where ab': "a = a' * ?d" "b = b' * ?d" "gcd a' b' = 1"
    by blast
  from ab have "(a' * ?d) ^ n dvd (b' * ?d) ^ n"
    by (simp add: ab'(1,2)[symmetric])
  hence "?d^n * a'^n dvd ?d^n * b'^n"
    by (simp only: power_mult_distrib ac_simps)
  with zn have "a'^n dvd b'^n" by simp
  hence "a' dvd b'^n" using dvd_trans[of a' "a'^n" "b'^n"] by (simp add: m)
  hence "a' dvd b'^m * b'" by (simp add: m ac_simps)
  with coprime_dvd_mult[OF coprime_exp[OF ab'(3), of m]]
    have "a' dvd b'" by (subst (asm) ac_simps, blast)
  hence "a'*?d dvd b'*?d" by (rule mult_dvd_mono, simp)
  with ab'(1,2) show ?thesis by simp
qed

lemma pow_divs_eq [simp]:
  "n \<noteq> 0 \<Longrightarrow> a ^ n dvd b ^ n \<longleftrightarrow> a dvd b"
  by (auto intro: pow_divs_pow dvd_power_same)

lemma coprime_plus_one [simp]: "gcd (n + 1) n = 1"
  by (subst add_commute, simp)

lemma setprod_coprime [rule_format]:
  "(\<forall>i\<in>A. gcd (f i) a = 1) \<longrightarrow> gcd (\<Prod>i\<in>A. f i) a = 1"
  apply (cases "finite A")
  apply (induct set: finite)
  apply (auto simp add: gcd_mult_cancel)
  done
  
lemma listprod_coprime:
  "(\<And>x. x \<in> set xs \<Longrightarrow> coprime x y) \<Longrightarrow> coprime (listprod xs) y" 
  by (induction xs) (simp_all add: gcd_mult_cancel)

lemma coprime_divisors: 
  assumes "d dvd a" "e dvd b" "gcd a b = 1"
  shows "gcd d e = 1" 
proof -
  from assms obtain k l where "a = d * k" "b = e * l"
    unfolding dvd_def by blast
  with assms have "gcd (d * k) (e * l) = 1" by simp
  hence "gcd (d * k) e = 1" by (rule coprime_lmult)
  also have "gcd (d * k) e = gcd e (d * k)" by (simp add: ac_simps)
  finally have "gcd e d = 1" by (rule coprime_lmult)
  then show ?thesis by (simp add: ac_simps)
qed

lemma lcm_gcd_prod:
  "lcm a b * gcd a b = normalize (a * b)"
  by (simp add: lcm_gcd)

declare unit_factor_lcm [simp]

lemma lcmI:
  assumes "a dvd c" and "b dvd c" and "\<And>d. a dvd d \<Longrightarrow> b dvd d \<Longrightarrow> c dvd d"
    and "normalize c = c"
  shows "c = lcm a b"
  by (rule associated_eqI) (auto simp: assms intro: lcm_least)

lemma gcd_dvd_lcm [simp]:
  "gcd a b dvd lcm a b"
  using gcd_dvd2 by (rule dvd_lcmI2)

lemmas lcm_0 = lcm_0_right

lemma lcm_unique:
  "a dvd d \<and> b dvd d \<and> 
  normalize d = d \<and>
  (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  by rule (auto intro: lcmI simp: lcm_least lcm_eq_0_iff)

lemma lcm_coprime:
  "gcd a b = 1 \<Longrightarrow> lcm a b = normalize (a * b)"
  by (subst lcm_gcd) simp

lemma lcm_proj1_if_dvd: 
  "b dvd a \<Longrightarrow> lcm a b = normalize a"
  by (cases "a = 0") (simp, rule sym, rule lcmI, simp_all)

lemma lcm_proj2_if_dvd: 
  "a dvd b \<Longrightarrow> lcm a b = normalize b"
  using lcm_proj1_if_dvd [of a b] by (simp add: ac_simps)

lemma lcm_proj1_iff:
  "lcm m n = normalize m \<longleftrightarrow> n dvd m"
proof
  assume A: "lcm m n = normalize m"
  show "n dvd m"
  proof (cases "m = 0")
    assume [simp]: "m \<noteq> 0"
    from A have B: "m = lcm m n * unit_factor m"
      by (simp add: unit_eq_div2)
    show ?thesis by (subst B, simp)
  qed simp
next
  assume "n dvd m"
  then show "lcm m n = normalize m" by (rule lcm_proj1_if_dvd)
qed

lemma lcm_proj2_iff:
  "lcm m n = normalize n \<longleftrightarrow> m dvd n"
  using lcm_proj1_iff [of n m] by (simp add: ac_simps)

end

class ring_gcd = comm_ring_1 + semiring_gcd
begin

lemma coprime_minus_one: "coprime (n - 1) n"
  using coprime_plus_one[of "n - 1"] by (simp add: gcd.commute)

lemma gcd_neg1 [simp]:
  "gcd (-a) b = gcd a b"
  by (rule sym, rule gcdI, simp_all add: gcd_greatest)

lemma gcd_neg2 [simp]:
  "gcd a (-b) = gcd a b"
  by (rule sym, rule gcdI, simp_all add: gcd_greatest)

lemma gcd_neg_numeral_1 [simp]:
  "gcd (- numeral n) a = gcd (numeral n) a"
  by (fact gcd_neg1)

lemma gcd_neg_numeral_2 [simp]:
  "gcd a (- numeral n) = gcd a (numeral n)"
  by (fact gcd_neg2)

lemma gcd_diff1: "gcd (m - n) n = gcd m n"
  by (subst diff_conv_add_uminus, subst gcd_neg2[symmetric],  subst gcd_add1, simp)

lemma gcd_diff2: "gcd (n - m) n = gcd m n"
  by (subst gcd_neg1[symmetric], simp only: minus_diff_eq gcd_diff1)

lemma lcm_neg1 [simp]: "lcm (-a) b = lcm a b"
  by (rule sym, rule lcmI, simp_all add: lcm_least lcm_eq_0_iff)

lemma lcm_neg2 [simp]: "lcm a (-b) = lcm a b"
  by (rule sym, rule lcmI, simp_all add: lcm_least lcm_eq_0_iff)

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

lemma Lcm_Gcd:
  "Lcm A = Gcd {b. \<forall>a\<in>A. a dvd b}"
  by (rule associated_eqI) (auto intro: Gcd_dvd dvd_Lcm Gcd_greatest Lcm_least)

lemma Gcd_Lcm:
  "Gcd A = Lcm {b. \<forall>a\<in>A. b dvd a}"
  by (rule associated_eqI) (auto intro: Gcd_dvd dvd_Lcm Gcd_greatest Lcm_least)

lemma Gcd_empty [simp]:
  "Gcd {} = 0"
  by (rule dvd_0_left, rule Gcd_greatest) simp

lemma Lcm_empty [simp]:
  "Lcm {} = 1"
  by (auto intro: associated_eqI Lcm_least)

lemma Gcd_insert [simp]:
  "Gcd (insert a A) = gcd a (Gcd A)"
proof -
  have "Gcd (insert a A) dvd gcd a (Gcd A)"
    by (auto intro: Gcd_dvd Gcd_greatest)
  moreover have "gcd a (Gcd A) dvd Gcd (insert a A)"
  proof (rule Gcd_greatest)
    fix b
    assume "b \<in> insert a A"
    then show "gcd a (Gcd A) dvd b"
    proof
      assume "b = a" then show ?thesis by simp
    next
      assume "b \<in> A"
      then have "Gcd A dvd b" by (rule Gcd_dvd)
      moreover have "gcd a (Gcd A) dvd Gcd A" by simp
      ultimately show ?thesis by (blast intro: dvd_trans)
    qed
  qed
  ultimately show ?thesis
    by (auto intro: associated_eqI)
qed

lemma Lcm_insert [simp]:
  "Lcm (insert a A) = lcm a (Lcm A)"
proof (rule sym)
  have "lcm a (Lcm A) dvd Lcm (insert a A)"
    by (auto intro: dvd_Lcm Lcm_least)
  moreover have "Lcm (insert a A) dvd lcm a (Lcm A)"
  proof (rule Lcm_least)
    fix b
    assume "b \<in> insert a A"
    then show "b dvd lcm a (Lcm A)"
    proof
      assume "b = a" then show ?thesis by simp
    next
      assume "b \<in> A"
      then have "b dvd Lcm A" by (rule dvd_Lcm)
      moreover have "Lcm A dvd lcm a (Lcm A)" by simp
      ultimately show ?thesis by (blast intro: dvd_trans)
    qed
  qed
  ultimately show "lcm a (Lcm A) = Lcm (insert a A)"
    by (rule associated_eqI) (simp_all add: lcm_eq_0_iff)
qed

lemma LcmI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> a dvd b" and "\<And>c. (\<And>a. a \<in> A \<Longrightarrow> a dvd c) \<Longrightarrow> b dvd c"
    and "normalize b = b" shows "b = Lcm A"
  by (rule associated_eqI) (auto simp: assms dvd_Lcm intro: Lcm_least)

lemma Lcm_subset:
  "A \<subseteq> B \<Longrightarrow> Lcm A dvd Lcm B"
  by (blast intro: Lcm_least dvd_Lcm)

lemma Lcm_Un:
  "Lcm (A \<union> B) = lcm (Lcm A) (Lcm B)"
  apply (rule lcmI)
  apply (blast intro: Lcm_subset)
  apply (blast intro: Lcm_subset)
  apply (intro Lcm_least ballI, elim UnE)
  apply (rule dvd_trans, erule dvd_Lcm, assumption)
  apply (rule dvd_trans, erule dvd_Lcm, assumption)
  apply simp
  done
  

lemma Gcd_0_iff [simp]:
  "Gcd A = 0 \<longleftrightarrow> A \<subseteq> {0}" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  show ?Q
  proof
    fix a
    assume "a \<in> A"
    then have "Gcd A dvd a" by (rule Gcd_dvd)
    with \<open>?P\<close> have "a = 0" by simp
    then show "a \<in> {0}" by simp
  qed
next
  assume ?Q
  have "0 dvd Gcd A"
  proof (rule Gcd_greatest)
    fix a
    assume "a \<in> A"
    with \<open>?Q\<close> have "a = 0" by auto
    then show "0 dvd a" by simp
  qed
  then show ?P by simp
qed

lemma Lcm_1_iff [simp]:
  "Lcm A = 1 \<longleftrightarrow> (\<forall>a\<in>A. is_unit a)" (is "?P \<longleftrightarrow> ?Q")
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

lemma unit_factor_Lcm:
  "unit_factor (Lcm A) = (if Lcm A = 0 then 0 else 1)"
proof (cases "Lcm A = 0")
  case True then show ?thesis by simp
next
  case False
  with unit_factor_normalize have "unit_factor (normalize (Lcm A)) = 1"
    by blast
  with False show ?thesis
    by simp
qed

lemma unit_factor_Gcd: "unit_factor (Gcd A) = (if Gcd A = 0 then 0 else 1)"
proof -
  show "unit_factor (Gcd A) = (if Gcd A = 0 then 0 else 1)"
    by (simp add: Gcd_Lcm unit_factor_Lcm)
qed

lemma GcdI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> b dvd a" and "\<And>c. (\<And>a. a \<in> A \<Longrightarrow> c dvd a) \<Longrightarrow> c dvd b"
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

lemma Gcd_UNIV [simp]:
  "Gcd UNIV = 1"
  using dvd_refl by (rule Gcd_eq_1_I) simp

lemma Lcm_UNIV [simp]:
  "Lcm UNIV = 0"
  by (rule Lcm_eq_0_I) simp

lemma Lcm_0_iff:
  assumes "finite A"
  shows "Lcm A = 0 \<longleftrightarrow> 0 \<in> A"
proof (cases "A = {}")
  case True then show ?thesis by simp
next
  case False with assms show ?thesis
    by (induct A rule: finite_ne_induct)
      (auto simp add: lcm_eq_0_iff)
qed

lemma Gcd_finite:
  assumes "finite A"
  shows "Gcd A = Finite_Set.fold gcd 0 A"
  by (induct rule: finite.induct[OF \<open>finite A\<close>])
     (simp_all add: comp_fun_idem.fold_insert_idem[OF comp_fun_idem_gcd])

lemma Gcd_set [code_unfold]: "Gcd (set as) = foldl gcd 0 as"
  by (simp add: Gcd_finite comp_fun_idem.fold_set_fold[OF comp_fun_idem_gcd] 
                foldl_conv_fold gcd.commute)

lemma Lcm_finite:
  assumes "finite A"
  shows "Lcm A = Finite_Set.fold lcm 1 A"
  by (induct rule: finite.induct[OF \<open>finite A\<close>])
     (simp_all add: comp_fun_idem.fold_insert_idem[OF comp_fun_idem_lcm])

lemma Lcm_set [code_unfold]:
  "Lcm (set as) = foldl lcm 1 as"
  by (simp add: Lcm_finite comp_fun_idem.fold_set_fold[OF comp_fun_idem_lcm] 
                foldl_conv_fold lcm.commute)

lemma Gcd_image_normalize [simp]:
  "Gcd (normalize ` A) = Gcd A"
proof -
  have "Gcd (normalize ` A) dvd a" if "a \<in> A" for a
  proof -
    from that obtain B where "A = insert a B" by blast
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

lemma Lcm_eqI:
  assumes "normalize a = a"
  assumes "\<And>b. b \<in> A \<Longrightarrow> b dvd a"
    and "\<And>c. (\<And>b. b \<in> A \<Longrightarrow> b dvd c) \<Longrightarrow> a dvd c"
  shows "Lcm A = a"
  using assms by (blast intro: associated_eqI Lcm_least dvd_Lcm normalize_Lcm)


lemma Lcm_no_units:
  "Lcm A = Lcm (A - {a. is_unit a})"
proof -
  have "(A - {a. is_unit a}) \<union> {a\<in>A. is_unit a} = A" by blast
  hence "Lcm A = lcm (Lcm (A - {a. is_unit a})) (Lcm {a\<in>A. is_unit a})"
    by (simp add: Lcm_Un [symmetric])
  also have "Lcm {a\<in>A. is_unit a} = 1" by (simp add: Lcm_1_iff)
  finally show ?thesis by simp
qed

lemma Lcm_0_iff': "Lcm A = 0 \<longleftrightarrow> \<not>(\<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l))"
  by (metis Lcm_least dvd_0_left dvd_Lcm)

lemma Lcm_no_multiple: "(\<forall>m. m \<noteq> 0 \<longrightarrow> (\<exists>a\<in>A. \<not>a dvd m)) \<Longrightarrow> Lcm A = 0"
  by (auto simp: Lcm_0_iff')

lemma Lcm_singleton [simp]:
  "Lcm {a} = normalize a"
  by simp

lemma Lcm_2 [simp]:
  "Lcm {a,b} = lcm a b"
  by simp

lemma Lcm_coprime:
  assumes "finite A" and "A \<noteq> {}" 
  assumes "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> gcd a b = 1"
  shows "Lcm A = normalize (\<Prod>A)"
using assms proof (induct rule: finite_ne_induct)
  case (insert a A)
  have "Lcm (insert a A) = lcm a (Lcm A)" by simp
  also from insert have "Lcm A = normalize (\<Prod>A)" by blast
  also have "lcm a \<dots> = lcm a (\<Prod>A)" by (cases "\<Prod>A = 0") (simp_all add: lcm_div_unit2)
  also from insert have "gcd a (\<Prod>A) = 1" by (subst gcd.commute, intro setprod_coprime) auto
  with insert have "lcm a (\<Prod>A) = normalize (\<Prod>(insert a A))"
    by (simp add: lcm_coprime)
  finally show ?case .
qed simp
      
lemma Lcm_coprime':
  "card A \<noteq> 0 \<Longrightarrow> (\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> gcd a b = 1)
    \<Longrightarrow> Lcm A = normalize (\<Prod>A)"
  by (rule Lcm_coprime) (simp_all add: card_eq_0_iff)

lemma Gcd_1:
  "1 \<in> A \<Longrightarrow> Gcd A = 1"
  by (auto intro!: Gcd_eq_1_I)

lemma Gcd_singleton [simp]: "Gcd {a} = normalize a"
  by simp

lemma Gcd_2 [simp]: "Gcd {a,b} = gcd a b"
  by simp


definition pairwise_coprime where
  "pairwise_coprime A = (\<forall>x y. x \<in> A \<and> y \<in> A \<and> x \<noteq> y \<longrightarrow> coprime x y)"

lemma pairwise_coprimeI [intro?]:
  "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> coprime x y) \<Longrightarrow> pairwise_coprime A"
  by (simp add: pairwise_coprime_def)

lemma pairwise_coprimeD:
  "pairwise_coprime A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> coprime x y"
  by (simp add: pairwise_coprime_def)

lemma pairwise_coprime_subset: "pairwise_coprime A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> pairwise_coprime B"
  by (force simp: pairwise_coprime_def)

end

subsection \<open>GCD and LCM on @{typ nat} and @{typ int}\<close>

instantiation nat :: gcd
begin

fun gcd_nat  :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where "gcd_nat x y =
  (if y = 0 then x else gcd y (x mod y))"

definition lcm_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "lcm_nat x y = x * y div (gcd x y)"

instance proof qed

end

instantiation int :: gcd
begin

definition gcd_int  :: "int \<Rightarrow> int \<Rightarrow> int"
  where "gcd_int x y = int (gcd (nat \<bar>x\<bar>) (nat \<bar>y\<bar>))"

definition lcm_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where "lcm_int x y = int (lcm (nat \<bar>x\<bar>) (nat \<bar>y\<bar>))"

instance ..

end

text \<open>Transfer setup\<close>

lemma transfer_nat_int_gcd:
  "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> gcd (nat x) (nat y) = nat (gcd x y)"
  "(x::int) >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> lcm (nat x) (nat y) = nat (lcm x y)"
  unfolding gcd_int_def lcm_int_def
  by auto

lemma transfer_nat_int_gcd_closures:
  "x >= (0::int) \<Longrightarrow> y >= 0 \<Longrightarrow> gcd x y >= 0"
  "x >= (0::int) \<Longrightarrow> y >= 0 \<Longrightarrow> lcm x y >= 0"
  by (auto simp add: gcd_int_def lcm_int_def)

declare transfer_morphism_nat_int[transfer add return:
    transfer_nat_int_gcd transfer_nat_int_gcd_closures]

lemma transfer_int_nat_gcd:
  "gcd (int x) (int y) = int (gcd x y)"
  "lcm (int x) (int y) = int (lcm x y)"
  by (unfold gcd_int_def lcm_int_def, auto)

lemma transfer_int_nat_gcd_closures:
  "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> gcd x y >= 0"
  "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> lcm x y >= 0"
  by (auto simp add: gcd_int_def lcm_int_def)

declare transfer_morphism_int_nat[transfer add return:
    transfer_int_nat_gcd transfer_int_nat_gcd_closures]

lemma gcd_nat_induct:
  fixes m n :: nat
  assumes "\<And>m. P m 0"
    and "\<And>m n. 0 < n \<Longrightarrow> P n (m mod n) \<Longrightarrow> P m n"
  shows "P m n"
  apply (rule gcd_nat.induct)
  apply (case_tac "y = 0")
  using assms apply simp_all
done

(* specific to int *)

lemma gcd_eq_int_iff:
  "gcd k l = int n \<longleftrightarrow> gcd (nat \<bar>k\<bar>) (nat \<bar>l\<bar>) = n"
  by (simp add: gcd_int_def)

lemma lcm_eq_int_iff:
  "lcm k l = int n \<longleftrightarrow> lcm (nat \<bar>k\<bar>) (nat \<bar>l\<bar>) = n"
  by (simp add: lcm_int_def)

lemma gcd_neg1_int [simp]: "gcd (-x::int) y = gcd x y"
  by (simp add: gcd_int_def)

lemma gcd_neg2_int [simp]: "gcd (x::int) (-y) = gcd x y"
  by (simp add: gcd_int_def)

lemma abs_gcd_int [simp]: "\<bar>gcd (x::int) y\<bar> = gcd x y"
by(simp add: gcd_int_def)

lemma gcd_abs_int: "gcd (x::int) y = gcd \<bar>x\<bar> \<bar>y\<bar>"
by (simp add: gcd_int_def)

lemma gcd_abs1_int [simp]: "gcd \<bar>x\<bar> (y::int) = gcd x y"
by (metis abs_idempotent gcd_abs_int)

lemma gcd_abs2_int [simp]: "gcd x \<bar>y::int\<bar> = gcd x y"
by (metis abs_idempotent gcd_abs_int)

lemma gcd_cases_int:
  fixes x :: int and y
  assumes "x >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> P (gcd x y)"
      and "x >= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> P (gcd x (-y))"
      and "x <= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> P (gcd (-x) y)"
      and "x <= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> P (gcd (-x) (-y))"
  shows "P (gcd x y)"
  by (insert assms, auto, arith)

lemma gcd_ge_0_int [simp]: "gcd (x::int) y >= 0"
  by (simp add: gcd_int_def)

lemma lcm_neg1_int: "lcm (-x::int) y = lcm x y"
  by (simp add: lcm_int_def)

lemma lcm_neg2_int: "lcm (x::int) (-y) = lcm x y"
  by (simp add: lcm_int_def)

lemma lcm_abs_int: "lcm (x::int) y = lcm \<bar>x\<bar> \<bar>y\<bar>"
  by (simp add: lcm_int_def)

lemma abs_lcm_int [simp]: "\<bar>lcm i j::int\<bar> = lcm i j"
  by (simp add:lcm_int_def)

lemma lcm_abs1_int [simp]: "lcm \<bar>x\<bar> (y::int) = lcm x y"
  by (metis abs_idempotent lcm_int_def)

lemma lcm_abs2_int [simp]: "lcm x \<bar>y::int\<bar> = lcm x y"
  by (metis abs_idempotent lcm_int_def)

lemma lcm_cases_int:
  fixes x :: int and y
  assumes "x >= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> P (lcm x y)"
      and "x >= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> P (lcm x (-y))"
      and "x <= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> P (lcm (-x) y)"
      and "x <= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> P (lcm (-x) (-y))"
  shows "P (lcm x y)"
  using assms by (auto simp add: lcm_neg1_int lcm_neg2_int) arith

lemma lcm_ge_0_int [simp]: "lcm (x::int) y >= 0"
  by (simp add: lcm_int_def)

lemma gcd_0_nat: "gcd (x::nat) 0 = x"
  by simp

lemma gcd_0_int [simp]: "gcd (x::int) 0 = \<bar>x\<bar>"
  by (unfold gcd_int_def, auto)

lemma gcd_0_left_nat: "gcd 0 (x::nat) = x"
  by simp

lemma gcd_0_left_int [simp]: "gcd 0 (x::int) = \<bar>x\<bar>"
  by (unfold gcd_int_def, auto)

lemma gcd_red_nat: "gcd (x::nat) y = gcd y (x mod y)"
  by (case_tac "y = 0", auto)

(* weaker, but useful for the simplifier *)

lemma gcd_non_0_nat: "y \<noteq> (0::nat) \<Longrightarrow> gcd (x::nat) y = gcd y (x mod y)"
  by simp

lemma gcd_1_nat [simp]: "gcd (m::nat) 1 = 1"
  by simp

lemma gcd_Suc_0 [simp]: "gcd (m::nat) (Suc 0) = Suc 0"
  by simp

lemma gcd_1_int [simp]: "gcd (m::int) 1 = 1"
  by (simp add: gcd_int_def)

lemma gcd_idem_nat: "gcd (x::nat) x = x"
by simp

lemma gcd_idem_int: "gcd (x::int) x = \<bar>x\<bar>"
by (auto simp add: gcd_int_def)

declare gcd_nat.simps [simp del]

text \<open>
  \medskip @{term "gcd m n"} divides \<open>m\<close> and \<open>n\<close>.  The
  conjunctions don't seem provable separately.
\<close>

instance nat :: semiring_gcd
proof
  fix m n :: nat
  show "gcd m n dvd m" and "gcd m n dvd n"
  proof (induct m n rule: gcd_nat_induct)
    fix m n :: nat
    assume "gcd n (m mod n) dvd m mod n" and "gcd n (m mod n) dvd n"
    then have "gcd n (m mod n) dvd m"
      by (rule dvd_mod_imp_dvd)
    moreover assume "0 < n"
    ultimately show "gcd m n dvd m"
      by (simp add: gcd_non_0_nat)
  qed (simp_all add: gcd_0_nat gcd_non_0_nat)
next
  fix m n k :: nat
  assume "k dvd m" and "k dvd n"
  then show "k dvd gcd m n"
    by (induct m n rule: gcd_nat_induct) (simp_all add: gcd_non_0_nat dvd_mod gcd_0_nat)
qed (simp_all add: lcm_nat_def)

instance int :: ring_gcd
  by standard
    (simp_all add: dvd_int_unfold_dvd_nat gcd_int_def lcm_int_def zdiv_int nat_abs_mult_distrib [symmetric] lcm_gcd gcd_greatest)

lemma gcd_le1_nat [simp]: "a \<noteq> 0 \<Longrightarrow> gcd (a::nat) b \<le> a"
  by (rule dvd_imp_le, auto)

lemma gcd_le2_nat [simp]: "b \<noteq> 0 \<Longrightarrow> gcd (a::nat) b \<le> b"
  by (rule dvd_imp_le, auto)

lemma gcd_le1_int [simp]: "a > 0 \<Longrightarrow> gcd (a::int) b \<le> a"
  by (rule zdvd_imp_le, auto)

lemma gcd_le2_int [simp]: "b > 0 \<Longrightarrow> gcd (a::int) b \<le> b"
  by (rule zdvd_imp_le, auto)

lemma gcd_pos_nat [simp]: "(gcd (m::nat) n > 0) = (m ~= 0 | n ~= 0)"
  by (insert gcd_eq_0_iff [of m n], arith)

lemma gcd_pos_int [simp]: "(gcd (m::int) n > 0) = (m ~= 0 | n ~= 0)"
  by (insert gcd_eq_0_iff [of m n], insert gcd_ge_0_int [of m n], arith)

lemma gcd_unique_nat: "(d::nat) dvd a \<and> d dvd b \<and>
    (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  apply auto
  apply (rule dvd_antisym)
  apply (erule (1) gcd_greatest)
  apply auto
done

lemma gcd_unique_int: "d >= 0 & (d::int) dvd a \<and> d dvd b \<and>
    (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
apply (case_tac "d = 0")
 apply simp
apply (rule iffI)
 apply (rule zdvd_antisym_nonneg)
 apply (auto intro: gcd_greatest)
done

interpretation gcd_nat:
  semilattice_neutr_order gcd "0::nat" Rings.dvd "\<lambda>m n. m dvd n \<and> m \<noteq> n"
  by standard (auto simp add: gcd_unique_nat [symmetric] intro: dvd_antisym dvd_trans)

lemma gcd_proj1_if_dvd_int [simp]: "x dvd y \<Longrightarrow> gcd (x::int) y = \<bar>x\<bar>"
  by (metis abs_dvd_iff gcd_0_left_int gcd_abs_int gcd_unique_int)

lemma gcd_proj2_if_dvd_int [simp]: "y dvd x \<Longrightarrow> gcd (x::int) y = \<bar>y\<bar>"
  by (metis gcd_proj1_if_dvd_int gcd.commute)

text \<open>
  \medskip Multiplication laws
\<close>

lemma gcd_mult_distrib_nat: "(k::nat) * gcd m n = gcd (k * m) (k * n)"
    \<comment> \<open>@{cite \<open>page 27\<close> davenport92}\<close>
  apply (induct m n rule: gcd_nat_induct)
  apply simp
  apply (case_tac "k = 0")
  apply (simp_all add: gcd_non_0_nat)
done

lemma gcd_mult_distrib_int: "\<bar>k::int\<bar> * gcd m n = gcd (k * m) (k * n)"
  apply (subst (1 2) gcd_abs_int)
  apply (subst (1 2) abs_mult)
  apply (rule gcd_mult_distrib_nat [transferred])
  apply auto
done

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

text \<open>\medskip Addition laws\<close>

(* to do: add the other variations? *)

lemma gcd_diff1_nat: "(m::nat) >= n \<Longrightarrow> gcd (m - n) n = gcd m n"
  by (subst gcd_add1 [symmetric]) auto

lemma gcd_diff2_nat: "(n::nat) >= m \<Longrightarrow> gcd (n - m) n = gcd m n"
  apply (subst gcd.commute)
  apply (subst gcd_diff1_nat [symmetric])
  apply auto
  apply (subst gcd.commute)
  apply (subst gcd_diff1_nat)
  apply assumption
  apply (rule gcd.commute)
  done

lemma gcd_non_0_int: "(y::int) > 0 \<Longrightarrow> gcd x y = gcd y (x mod y)"
  apply (frule_tac b = y and a = x in pos_mod_sign)
  apply (simp del: pos_mod_sign add: gcd_int_def abs_if nat_mod_distrib)
  apply (auto simp add: gcd_non_0_nat nat_mod_distrib [symmetric]
    zmod_zminus1_eq_if)
  apply (frule_tac a = x in pos_mod_bound)
  apply (subst (1 2) gcd.commute)
  apply (simp del: pos_mod_bound add: nat_diff_distrib gcd_diff2_nat
    nat_le_eq_zle)
  done

lemma gcd_red_int: "gcd (x::int) y = gcd y (x mod y)"
  apply (case_tac "y = 0")
  apply force
  apply (case_tac "y > 0")
  apply (subst gcd_non_0_int, auto)
  apply (insert gcd_non_0_int [of "-y" "-x"])
  apply auto
done

(* to do: differences, and all variations of addition rules
    as simplification rules for nat and int *)

(* to do: add the three variations of these, and for ints? *)

lemma finite_divisors_nat [simp]: \<comment> \<open>FIXME move\<close>
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
  then have "finite {d. \<bar>d\<bar> <= \<bar>i\<bar>}"
    by simp
  from finite_subset [OF _ this] show ?thesis using assms
    by (simp add: dvd_imp_le_int subset_iff)
qed

lemma Max_divisors_self_nat [simp]: "n\<noteq>0 \<Longrightarrow> Max{d::nat. d dvd n} = n"
apply(rule antisym)
 apply (fastforce intro: Max_le_iff[THEN iffD2] simp: dvd_imp_le)
apply simp
done

lemma Max_divisors_self_int [simp]: "n\<noteq>0 \<Longrightarrow> Max{d::int. d dvd n} = \<bar>n\<bar>"
apply(rule antisym)
 apply(rule Max_le_iff [THEN iffD2])
  apply (auto intro: abs_le_D1 dvd_imp_le_int)
done

lemma gcd_is_Max_divisors_nat:
  "m > 0 \<Longrightarrow> n > 0 \<Longrightarrow> gcd (m::nat) n = Max {d. d dvd m \<and> d dvd n}"
apply(rule Max_eqI[THEN sym])
  apply (metis finite_Collect_conjI finite_divisors_nat)
 apply simp
 apply(metis Suc_diff_1 Suc_neq_Zero dvd_imp_le gcd_greatest_iff gcd_pos_nat)
apply simp
done

lemma gcd_is_Max_divisors_int:
  "m ~= 0 ==> n ~= 0 ==> gcd (m::int) n = (Max {d. d dvd m & d dvd n})"
apply(rule Max_eqI[THEN sym])
  apply (metis finite_Collect_conjI finite_divisors_int)
 apply simp
 apply (metis gcd_greatest_iff gcd_pos_int zdvd_imp_le)
apply simp
done

lemma gcd_code_int [code]:
  "gcd k l = \<bar>if l = (0::int) then k else gcd l (\<bar>k\<bar> mod \<bar>l\<bar>)\<bar>"
  by (simp add: gcd_int_def nat_mod_distrib gcd_non_0_nat)


subsection \<open>Coprimality\<close>

lemma coprime_nat:
  "coprime (a::nat) b \<longleftrightarrow> (\<forall>d. d dvd a \<and> d dvd b \<longleftrightarrow> d = 1)"
  using coprime [of a b] by simp

lemma coprime_Suc_0_nat:
  "coprime (a::nat) b \<longleftrightarrow> (\<forall>d. d dvd a \<and> d dvd b \<longleftrightarrow> d = Suc 0)"
  using coprime_nat by simp

lemma coprime_int:
  "coprime (a::int) b \<longleftrightarrow> (\<forall>d. d \<ge> 0 \<and> d dvd a \<and> d dvd b \<longleftrightarrow> d = 1)"
  using gcd_unique_int [of 1 a b]
  apply clarsimp
  apply (erule subst)
  apply (rule iffI)
  apply force
  using abs_dvd_iff abs_ge_zero apply blast
  done

lemma pow_divides_eq_nat [simp]:
  "n > 0 \<Longrightarrow> (a::nat) ^ n dvd b ^ n \<longleftrightarrow> a dvd b"
  using pow_divs_eq[of n] by simp

lemma coprime_Suc_nat [simp]: "coprime (Suc n) n"
  using coprime_plus_one[of n] by simp

lemma coprime_minus_one_nat: "(n::nat) \<noteq> 0 \<Longrightarrow> coprime (n - 1) n"
  using coprime_Suc_nat [of "n - 1"] gcd.commute [of "n - 1" n] by auto

lemma coprime_common_divisor_nat: 
  "coprime (a::nat) b \<Longrightarrow> x dvd a \<Longrightarrow> x dvd b \<Longrightarrow> x = 1"
  by (metis gcd_greatest_iff nat_dvd_1_iff_1)

lemma coprime_common_divisor_int:
  "coprime (a::int) b \<Longrightarrow> x dvd a \<Longrightarrow> x dvd b \<Longrightarrow> \<bar>x\<bar> = 1"
  using gcd_greatest_iff [of x a b] by auto

lemma invertible_coprime_nat: "(x::nat) * y mod m = 1 \<Longrightarrow> coprime x m"
by (metis coprime_lmult gcd_1_nat gcd.commute gcd_red_nat)

lemma invertible_coprime_int: "(x::int) * y mod m = 1 \<Longrightarrow> coprime x m"
by (metis coprime_lmult gcd_1_int gcd.commute gcd_red_int)


subsection \<open>Bezout's theorem\<close>

(* Function bezw returns a pair of witnesses to Bezout's theorem --
   see the theorems that follow the definition. *)
fun
  bezw  :: "nat \<Rightarrow> nat \<Rightarrow> int * int"
where
  "bezw x y =
  (if y = 0 then (1, 0) else
      (snd (bezw y (x mod y)),
       fst (bezw y (x mod y)) - snd (bezw y (x mod y)) * int(x div y)))"

lemma bezw_0 [simp]: "bezw x 0 = (1, 0)" by simp

lemma bezw_non_0: "y > 0 \<Longrightarrow> bezw x y = (snd (bezw y (x mod y)),
       fst (bezw y (x mod y)) - snd (bezw y (x mod y)) * int(x div y))"
  by simp

declare bezw.simps [simp del]

lemma bezw_aux [rule_format]:
    "fst (bezw x y) * int x + snd (bezw x y) * int y = int (gcd x y)"
proof (induct x y rule: gcd_nat_induct)
  fix m :: nat
  show "fst (bezw m 0) * int m + snd (bezw m 0) * int 0 = int (gcd m 0)"
    by auto
  next fix m :: nat and n
    assume ngt0: "n > 0" and
      ih: "fst (bezw n (m mod n)) * int n +
        snd (bezw n (m mod n)) * int (m mod n) =
        int (gcd n (m mod n))"
    thus "fst (bezw m n) * int m + snd (bezw m n) * int n = int (gcd m n)"
      apply (simp add: bezw_non_0 gcd_non_0_nat)
      apply (erule subst)
      apply (simp add: field_simps)
      apply (subst mod_div_equality [of m n, symmetric])
      (* applying simp here undoes the last substitution!
         what is procedure cancel_div_mod? *)
      apply (simp only: NO_MATCH_def field_simps of_nat_add of_nat_mult)
      done
qed

lemma bezout_int:
  fixes x y
  shows "EX u v. u * (x::int) + v * y = gcd x y"
proof -
  have bezout_aux: "!!x y. x \<ge> (0::int) \<Longrightarrow> y \<ge> 0 \<Longrightarrow>
      EX u v. u * x + v * y = gcd x y"
    apply (rule_tac x = "fst (bezw (nat x) (nat y))" in exI)
    apply (rule_tac x = "snd (bezw (nat x) (nat y))" in exI)
    apply (unfold gcd_int_def)
    apply simp
    apply (subst bezw_aux [symmetric])
    apply auto
    done
  have "(x \<ge> 0 \<and> y \<ge> 0) | (x \<ge> 0 \<and> y \<le> 0) | (x \<le> 0 \<and> y \<ge> 0) |
      (x \<le> 0 \<and> y \<le> 0)"
    by auto
  moreover have "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> ?thesis"
    by (erule (1) bezout_aux)
  moreover have "x >= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> ?thesis"
    apply (insert bezout_aux [of x "-y"])
    apply auto
    apply (rule_tac x = u in exI)
    apply (rule_tac x = "-v" in exI)
    apply (subst gcd_neg2_int [symmetric])
    apply auto
    done
  moreover have "x <= 0 \<Longrightarrow> y >= 0 \<Longrightarrow> ?thesis"
    apply (insert bezout_aux [of "-x" y])
    apply auto
    apply (rule_tac x = "-u" in exI)
    apply (rule_tac x = v in exI)
    apply (subst gcd_neg1_int [symmetric])
    apply auto
    done
  moreover have "x <= 0 \<Longrightarrow> y <= 0 \<Longrightarrow> ?thesis"
    apply (insert bezout_aux [of "-x" "-y"])
    apply auto
    apply (rule_tac x = "-u" in exI)
    apply (rule_tac x = "-v" in exI)
    apply (subst gcd_neg1_int [symmetric])
    apply (subst gcd_neg2_int [symmetric])
    apply auto
    done
  ultimately show ?thesis by blast
qed

text \<open>versions of Bezout for nat, by Amine Chaieb\<close>

lemma ind_euclid:
  assumes c: " \<forall>a b. P (a::nat) b \<longleftrightarrow> P b a" and z: "\<forall>a. P a 0"
  and add: "\<forall>a b. P a b \<longrightarrow> P a (a + b)"
  shows "P a b"
proof(induct "a + b" arbitrary: a b rule: less_induct)
  case less
  have "a = b \<or> a < b \<or> b < a" by arith
  moreover {assume eq: "a= b"
    from add[rule_format, OF z[rule_format, of a]] have "P a b" using eq
    by simp}
  moreover
  {assume lt: "a < b"
    hence "a + b - a < a + b \<or> a = 0" by arith
    moreover
    {assume "a =0" with z c have "P a b" by blast }
    moreover
    {assume "a + b - a < a + b"
      also have th0: "a + b - a = a + (b - a)" using lt by arith
      finally have "a + (b - a) < a + b" .
      then have "P a (a + (b - a))" by (rule add[rule_format, OF less])
      then have "P a b" by (simp add: th0[symmetric])}
    ultimately have "P a b" by blast}
  moreover
  {assume lt: "a > b"
    hence "b + a - b < a + b \<or> b = 0" by arith
    moreover
    {assume "b =0" with z c have "P a b" by blast }
    moreover
    {assume "b + a - b < a + b"
      also have th0: "b + a - b = b + (a - b)" using lt by arith
      finally have "b + (a - b) < a + b" .
      then have "P b (b + (a - b))" by (rule add[rule_format, OF less])
      then have "P b a" by (simp add: th0[symmetric])
      hence "P a b" using c by blast }
    ultimately have "P a b" by blast}
ultimately  show "P a b" by blast
qed

lemma bezout_lemma_nat:
  assumes ex: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and>
    (a * x = b * y + d \<or> b * x = a * y + d)"
  shows "\<exists>d x y. d dvd a \<and> d dvd a + b \<and>
    (a * x = (a + b) * y + d \<or> (a + b) * x = a * y + d)"
  using ex
  apply clarsimp
  apply (rule_tac x="d" in exI, simp)
  apply (case_tac "a * x = b * y + d" , simp_all)
  apply (rule_tac x="x + y" in exI)
  apply (rule_tac x="y" in exI)
  apply algebra
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="x + y" in exI)
  apply algebra
done

lemma bezout_add_nat: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and>
    (a * x = b * y + d \<or> b * x = a * y + d)"
  apply(induct a b rule: ind_euclid)
  apply blast
  apply clarify
  apply (rule_tac x="a" in exI, simp)
  apply clarsimp
  apply (rule_tac x="d" in exI)
  apply (case_tac "a * x = b * y + d", simp_all)
  apply (rule_tac x="x+y" in exI)
  apply (rule_tac x="y" in exI)
  apply algebra
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="x+y" in exI)
  apply algebra
done

lemma bezout1_nat: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and>
    (a * x - b * y = d \<or> b * x - a * y = d)"
  using bezout_add_nat[of a b]
  apply clarsimp
  apply (rule_tac x="d" in exI, simp)
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="y" in exI)
  apply auto
done

lemma bezout_add_strong_nat: assumes nz: "a \<noteq> (0::nat)"
  shows "\<exists>d x y. d dvd a \<and> d dvd b \<and> a * x = b * y + d"
proof-
 from nz have ap: "a > 0" by simp
 from bezout_add_nat[of a b]
 have "(\<exists>d x y. d dvd a \<and> d dvd b \<and> a * x = b * y + d) \<or>
   (\<exists>d x y. d dvd a \<and> d dvd b \<and> b * x = a * y + d)" by blast
 moreover
    {fix d x y assume H: "d dvd a" "d dvd b" "a * x = b * y + d"
     from H have ?thesis by blast }
 moreover
 {fix d x y assume H: "d dvd a" "d dvd b" "b * x = a * y + d"
   {assume b0: "b = 0" with H  have ?thesis by simp}
   moreover
   {assume b: "b \<noteq> 0" hence bp: "b > 0" by simp
     from b dvd_imp_le [OF H(2)] have "d < b \<or> d = b"
       by auto
     moreover
     {assume db: "d=b"
       with nz H have ?thesis apply simp
         apply (rule exI[where x = b], simp)
         apply (rule exI[where x = b])
        by (rule exI[where x = "a - 1"], simp add: diff_mult_distrib2)}
    moreover
    {assume db: "d < b"
        {assume "x=0" hence ?thesis using nz H by simp }
        moreover
        {assume x0: "x \<noteq> 0" hence xp: "x > 0" by simp
          from db have "d \<le> b - 1" by simp
          hence "d*b \<le> b*(b - 1)" by simp
          with xp mult_mono[of "1" "x" "d*b" "b*(b - 1)"]
          have dble: "d*b \<le> x*b*(b - 1)" using bp by simp
          from H (3) have "d + (b - 1) * (b*x) = d + (b - 1) * (a*y + d)"
            by simp
          hence "d + (b - 1) * a * y + (b - 1) * d = d + (b - 1) * b * x"
            by (simp only: mult.assoc distrib_left)
          hence "a * ((b - 1) * y) + d * (b - 1 + 1) = d + x*b*(b - 1)"
            by algebra
          hence "a * ((b - 1) * y) = d + x*b*(b - 1) - d*b" using bp by simp
          hence "a * ((b - 1) * y) = d + (x*b*(b - 1) - d*b)"
            by (simp only: diff_add_assoc[OF dble, of d, symmetric])
          hence "a * ((b - 1) * y) = b*(x*(b - 1) - d) + d"
            by (simp only: diff_mult_distrib2 ac_simps)
          hence ?thesis using H(1,2)
            apply -
            apply (rule exI[where x=d], simp)
            apply (rule exI[where x="(b - 1) * y"])
            by (rule exI[where x="x*(b - 1) - d"], simp)}
        ultimately have ?thesis by blast}
    ultimately have ?thesis by blast}
  ultimately have ?thesis by blast}
 ultimately show ?thesis by blast
qed

lemma bezout_nat: assumes a: "(a::nat) \<noteq> 0"
  shows "\<exists>x y. a * x = b * y + gcd a b"
proof-
  let ?g = "gcd a b"
  from bezout_add_strong_nat[OF a, of b]
  obtain d x y where d: "d dvd a" "d dvd b" "a * x = b * y + d" by blast
  from d(1,2) have "d dvd ?g" by simp
  then obtain k where k: "?g = d*k" unfolding dvd_def by blast
  from d(3) have "a * x * k = (b * y + d) *k " by auto
  hence "a * (x * k) = b * (y*k) + ?g" by (algebra add: k)
  thus ?thesis by blast
qed


subsection \<open>LCM properties  on @{typ nat} and @{typ int}\<close>

lemma lcm_altdef_int [code]: "lcm (a::int) b = \<bar>a\<bar> * \<bar>b\<bar> div gcd a b"
  by (simp add: lcm_int_def lcm_nat_def zdiv_int gcd_int_def)

lemma prod_gcd_lcm_nat: "(m::nat) * n = gcd m n * lcm m n"
  unfolding lcm_nat_def
  by (simp add: dvd_mult_div_cancel [OF gcd_dvd_prod])

lemma prod_gcd_lcm_int: "\<bar>m::int\<bar> * \<bar>n\<bar> = gcd m n * lcm m n"
  unfolding lcm_int_def gcd_int_def
  apply (subst of_nat_mult [symmetric])
  apply (subst prod_gcd_lcm_nat [symmetric])
  apply (subst nat_abs_mult_distrib [symmetric])
  apply (simp, simp add: abs_mult)
done

lemma lcm_pos_nat:
  "(m::nat) > 0 \<Longrightarrow> n>0 \<Longrightarrow> lcm m n > 0"
by (metis gr0I mult_is_0 prod_gcd_lcm_nat)

lemma lcm_pos_int:
  "(m::int) ~= 0 \<Longrightarrow> n ~= 0 \<Longrightarrow> lcm m n > 0"
  apply (subst lcm_abs_int)
  apply (rule lcm_pos_nat [transferred])
  apply auto
  done

lemma dvd_pos_nat: \<comment> \<open>FIXME move\<close>
  fixes n m :: nat
  assumes "n > 0" and "m dvd n"
  shows "m > 0"
  using assms by (cases m) auto

lemma lcm_unique_nat: "(a::nat) dvd d \<and> b dvd d \<and>
    (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  by (auto intro: dvd_antisym lcm_least)

lemma lcm_unique_int: "d >= 0 \<and> (a::int) dvd d \<and> b dvd d \<and>
    (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  using lcm_least zdvd_antisym_nonneg by auto

lemma lcm_proj2_if_dvd_nat [simp]: "(x::nat) dvd y \<Longrightarrow> lcm x y = y"
  apply (rule sym)
  apply (subst lcm_unique_nat [symmetric])
  apply auto
done

lemma lcm_proj2_if_dvd_int [simp]: "(x::int) dvd y \<Longrightarrow> lcm x y = \<bar>y\<bar>"
  apply (rule sym)
  apply (subst lcm_unique_int [symmetric])
  apply auto
done

lemma lcm_proj1_if_dvd_nat [simp]: "(x::nat) dvd y \<Longrightarrow> lcm y x = y"
by (subst lcm.commute, erule lcm_proj2_if_dvd_nat)

lemma lcm_proj1_if_dvd_int [simp]: "(x::int) dvd y \<Longrightarrow> lcm y x = \<bar>y\<bar>"
by (subst lcm.commute, erule lcm_proj2_if_dvd_int)

lemma lcm_proj1_iff_nat [simp]: "lcm m n = (m::nat) \<longleftrightarrow> n dvd m"
by (metis lcm_proj1_if_dvd_nat lcm_unique_nat)

lemma lcm_proj2_iff_nat [simp]: "lcm m n = (n::nat) \<longleftrightarrow> m dvd n"
by (metis lcm_proj2_if_dvd_nat lcm_unique_nat)

lemma lcm_proj1_iff_int [simp]: "lcm m n = \<bar>m::int\<bar> \<longleftrightarrow> n dvd m"
by (metis dvd_abs_iff lcm_proj1_if_dvd_int lcm_unique_int)

lemma lcm_proj2_iff_int [simp]: "lcm m n = \<bar>n::int\<bar> \<longleftrightarrow> m dvd n"
by (metis dvd_abs_iff lcm_proj2_if_dvd_int lcm_unique_int)

lemma lcm_1_iff_nat [simp]:
  "lcm (m::nat) n = Suc 0 \<longleftrightarrow> m = Suc 0 \<and> n = Suc 0"
  using lcm_eq_1_iff [of m n] by simp
  
lemma lcm_1_iff_int [simp]:
  "lcm (m::int) n = 1 \<longleftrightarrow> (m=1 \<or> m = -1) \<and> (n=1 \<or> n = -1)"
  by auto


subsection \<open>The complete divisibility lattice on @{typ nat} and @{typ int}\<close>

text\<open>Lifting gcd and lcm to sets (Gcd/Lcm).
Gcd is defined via Lcm to facilitate the proof that we have a complete lattice.
\<close>

instantiation nat :: semiring_Gcd
begin

interpretation semilattice_neutr_set lcm "1::nat"
  by standard simp_all

definition
  "Lcm (M::nat set) = (if finite M then F M else 0)"

lemma Lcm_nat_empty:
  "Lcm {} = (1::nat)"
  by (simp add: Lcm_nat_def del: One_nat_def)

lemma Lcm_nat_insert:
  "Lcm (insert n M) = lcm (n::nat) (Lcm M)"
  by (cases "finite M") (auto simp add: Lcm_nat_def simp del: One_nat_def)

lemma Lcm_nat_infinite:
  "infinite M \<Longrightarrow> Lcm M = (0::nat)"
  by (simp add: Lcm_nat_def)

lemma dvd_Lcm_nat [simp]:
  fixes M :: "nat set"
  assumes "m \<in> M"
  shows "m dvd Lcm M"
proof -
  from assms have "insert m M = M" by auto
  moreover have "m dvd Lcm (insert m M)"
    by (simp add: Lcm_nat_insert)
  ultimately show ?thesis by simp
qed

lemma Lcm_dvd_nat [simp]:
  fixes M :: "nat set"
  assumes "\<forall>m\<in>M. m dvd n"
  shows "Lcm M dvd n"
proof (cases "n > 0")
  case False then show ?thesis by simp
next
  case True
  then have "finite {d. d dvd n}" by (rule finite_divisors_nat)
  moreover have "M \<subseteq> {d. d dvd n}" using assms by fast
  ultimately have "finite M" by (rule rev_finite_subset)
  then show ?thesis using assms
    by (induct M) (simp_all add: Lcm_nat_empty Lcm_nat_insert)
qed

definition
  "Gcd (M::nat set) = Lcm {d. \<forall>m\<in>M. d dvd m}"

instance proof
  show "Gcd N dvd n" if "n \<in> N" for N and n :: nat
  using that by (induct N rule: infinite_finite_induct)
    (auto simp add: Gcd_nat_def)
  show "n dvd Gcd N" if "\<And>m. m \<in> N \<Longrightarrow> n dvd m" for N and n :: nat
  using that by (induct N rule: infinite_finite_induct)
    (auto simp add: Gcd_nat_def)
  show "n dvd Lcm N" if "n \<in> N" for N and n ::nat
  using that by (induct N rule: infinite_finite_induct)
    auto
  show "Lcm N dvd n" if "\<And>m. m \<in> N \<Longrightarrow> m dvd n" for N and n ::nat
  using that by (induct N rule: infinite_finite_induct)
    auto
qed simp_all

end

lemma Gcd_nat_eq_one:
  "1 \<in> N \<Longrightarrow> Gcd N = (1::nat)"
  by (rule Gcd_eq_1_I) auto

text\<open>Alternative characterizations of Gcd:\<close>

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
    apply (rule Max.boundedI)
    apply auto
    apply (meson Gcd_dvd Gcd_greatest \<open>0 < m\<close> \<open>m \<in> M\<close> dvd_imp_le dvd_pos_nat)
    done
qed

lemma Gcd_remove0_nat: "finite M \<Longrightarrow> Gcd M = Gcd (M - {0::nat})"
apply(induct pred:finite)
 apply simp
apply(case_tac "x=0")
 apply simp
apply(subgoal_tac "insert x F - {0} = insert x (F - {0})")
 apply simp
apply blast
done

lemma Lcm_in_lcm_closed_set_nat:
  "finite M \<Longrightarrow> M \<noteq> {} \<Longrightarrow> ALL m n :: nat. m:M \<longrightarrow> n:M \<longrightarrow> lcm m n : M \<Longrightarrow> Lcm M : M"
apply(induct rule:finite_linorder_min_induct)
 apply simp
apply simp
apply(subgoal_tac "ALL m n :: nat. m:A \<longrightarrow> n:A \<longrightarrow> lcm m n : A")
 apply simp
 apply(case_tac "A={}")
  apply simp
 apply simp
apply (metis lcm_pos_nat lcm_unique_nat linorder_neq_iff nat_dvd_not_less not_less0)
done

lemma Lcm_eq_Max_nat:
  "finite M \<Longrightarrow> M \<noteq> {} \<Longrightarrow> 0 \<notin> M \<Longrightarrow> ALL m n :: nat. m:M \<longrightarrow> n:M \<longrightarrow> lcm m n : M \<Longrightarrow> Lcm M = Max M"
apply(rule antisym)
 apply(rule Max_ge, assumption)
 apply(erule (2) Lcm_in_lcm_closed_set_nat)
apply (auto simp add: not_le Lcm_0_iff dvd_imp_le leD le_neq_trans)
done

lemma mult_inj_if_coprime_nat:
  "inj_on f A \<Longrightarrow> inj_on g B \<Longrightarrow> ALL a:A. ALL b:B. coprime (f a) (g b)
   \<Longrightarrow> inj_on (%(a,b). f a * g b::nat) (A \<times> B)"
  by (auto simp add: inj_on_def coprime_crossproduct_nat simp del: One_nat_def)

text\<open>Nitpick:\<close>

lemma gcd_eq_nitpick_gcd [nitpick_unfold]: "gcd x y = Nitpick.nat_gcd x y"
by (induct x y rule: nat_gcd.induct)
   (simp add: gcd_nat.simps Nitpick.nat_gcd.simps)

lemma lcm_eq_nitpick_lcm [nitpick_unfold]: "lcm x y = Nitpick.nat_lcm x y"
by (simp only: lcm_nat_def Nitpick.nat_lcm_def gcd_eq_nitpick_gcd)


subsubsection \<open>Setwise gcd and lcm for integers\<close>

instantiation int :: semiring_Gcd
begin

definition
  "Lcm M = int (LCM m\<in>M. (nat \<circ> abs) m)"

definition
  "Gcd M = int (GCD m\<in>M. (nat \<circ> abs) m)"

instance by standard
  (auto intro!: Gcd_dvd Gcd_greatest simp add: Gcd_int_def
    Lcm_int_def int_dvd_iff dvd_int_iff dvd_int_unfold_dvd_nat [symmetric])

end

lemma abs_Gcd [simp]:
  fixes K :: "int set"
  shows "\<bar>Gcd K\<bar> = Gcd K"
  using normalize_Gcd [of K] by simp

lemma abs_Lcm [simp]:
  fixes K :: "int set"
  shows "\<bar>Lcm K\<bar> = Lcm K"
  using normalize_Lcm [of K] by simp

lemma Gcm_eq_int_iff:
  "Gcd K = int n \<longleftrightarrow> Gcd ((nat \<circ> abs) ` K) = n"
  by (simp add: Gcd_int_def comp_def image_image)

lemma Lcm_eq_int_iff:
  "Lcm K = int n \<longleftrightarrow> Lcm ((nat \<circ> abs) ` K) = n"
  by (simp add: Lcm_int_def comp_def image_image)


subsection \<open>GCD and LCM on @{typ integer}\<close>

instantiation integer :: gcd
begin

context
  includes integer.lifting
begin

lift_definition gcd_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer"
  is gcd .
lift_definition lcm_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer"
  is lcm .

end
instance ..

end

lifting_update integer.lifting
lifting_forget integer.lifting

context
  includes integer.lifting
begin

lemma gcd_code_integer [code]:
  "gcd k l = \<bar>if l = (0::integer) then k else gcd l (\<bar>k\<bar> mod \<bar>l\<bar>)\<bar>"
  by transfer (fact gcd_code_int)

lemma lcm_code_integer [code]: "lcm (a::integer) b = \<bar>a\<bar> * \<bar>b\<bar> div gcd a b"
  by transfer (fact lcm_altdef_int)

end

code_printing constant "gcd :: integer \<Rightarrow> _"
  \<rightharpoonup> (OCaml) "Big'_int.gcd'_big'_int"
  and (Haskell) "Prelude.gcd"
  and (Scala) "_.gcd'((_)')"
  \<comment> \<open>There is no gcd operation in the SML standard library, so no code setup for SML\<close>

text \<open>Some code equations\<close>

lemmas Lcm_set_nat [code, code_unfold] = Lcm_set[where ?'a = nat]
lemmas Gcd_set_nat [code] = Gcd_set[where ?'a = nat]
lemmas Lcm_set_int [code, code_unfold] = Lcm_set[where ?'a = int]
lemmas Gcd_set_int [code] = Gcd_set[where ?'a = int]


text \<open>Fact aliasses\<close>

lemma lcm_0_iff_nat [simp]: "lcm (m::nat) n = 0 \<longleftrightarrow> m = 0 \<or> n = 0"
  by (fact lcm_eq_0_iff)

lemma lcm_0_iff_int [simp]: "lcm (m::int) n = 0 \<longleftrightarrow> m = 0 \<or> n = 0"
  by (fact lcm_eq_0_iff)

lemma dvd_lcm_I1_nat [simp]: "(k::nat) dvd m \<Longrightarrow> k dvd lcm m n"
  by (fact dvd_lcmI1)

lemma dvd_lcm_I2_nat [simp]: "(k::nat) dvd n \<Longrightarrow> k dvd lcm m n"
  by (fact dvd_lcmI2)

lemma dvd_lcm_I1_int [simp]: "(i::int) dvd m \<Longrightarrow> i dvd lcm m n"
  by (fact dvd_lcmI1)

lemma dvd_lcm_I2_int [simp]: "(i::int) dvd n \<Longrightarrow> i dvd lcm m n"
  by (fact dvd_lcmI2)

lemma coprime_exp2_nat [intro]: "coprime (a::nat) b \<Longrightarrow> coprime (a^n) (b^m)"
  by (fact coprime_exp2)

lemma coprime_exp2_int [intro]: "coprime (a::int) b \<Longrightarrow> coprime (a^n) (b^m)"
  by (fact coprime_exp2)

lemmas Gcd_dvd_nat [simp] = Gcd_dvd [where ?'a = nat]
lemmas Gcd_dvd_int [simp] = Gcd_dvd [where ?'a = int]
lemmas Gcd_greatest_nat [simp] = Gcd_greatest [where ?'a = nat]
lemmas Gcd_greatest_int [simp] = Gcd_greatest [where ?'a = int]

lemma dvd_Lcm_int [simp]:
  fixes M :: "int set" assumes "m \<in> M" shows "m dvd Lcm M"
  using assms by (fact dvd_Lcm)

lemma gcd_neg_numeral_1_int [simp]:
  "gcd (- numeral n :: int) x = gcd (numeral n) x"
  by (fact gcd_neg1_int)

lemma gcd_neg_numeral_2_int [simp]:
  "gcd x (- numeral n :: int) = gcd x (numeral n)"
  by (fact gcd_neg2_int)

lemma gcd_proj1_if_dvd_nat [simp]: "(x::nat) dvd y \<Longrightarrow> gcd x y = x"
  by (fact gcd_nat.absorb1)

lemma gcd_proj2_if_dvd_nat [simp]: "(y::nat) dvd x \<Longrightarrow> gcd x y = y"
  by (fact gcd_nat.absorb2)

lemmas Lcm_eq_0_I_nat [simp] = Lcm_eq_0_I [where ?'a = nat]
lemmas Lcm_0_iff_nat [simp] = Lcm_0_iff [where ?'a = nat]
lemmas Lcm_least_int [simp] = Lcm_least [where ?'a = int]

end
