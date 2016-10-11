(* Author: Manuel Eberl *)

section \<open>Abstract euclidean algorithm\<close>

theory Euclidean_Algorithm
imports "~~/src/HOL/GCD" Factorial_Ring
begin

class divide_modulo = semidom_divide + modulo +
  assumes div_mod_equality: "((a div b) * b + a mod b) + c = a + c"
begin

lemma zero_mod_left [simp]: "0 mod a = 0"
  using div_mod_equality[of 0 a 0] by simp

lemma dvd_mod_iff [simp]: 
  assumes "k dvd n"
  shows   "(k dvd m mod n) = (k dvd m)"
proof -
  thm div_mod_equality
  from assms have "(k dvd m mod n) \<longleftrightarrow> (k dvd ((m div n) * n + m mod n))" 
    by (simp add: dvd_add_right_iff)
  also have "(m div n) * n + m mod n = m"
    using div_mod_equality[of m n 0] by simp
  finally show ?thesis .
qed

lemma mod_0_imp_dvd: 
  assumes "a mod b = 0"
  shows   "b dvd a"
proof -
  have "b dvd ((a div b) * b)" by simp
  also have "(a div b) * b = a"
    using div_mod_equality[of a b 0] by (simp add: assms)
  finally show ?thesis .
qed

end



text \<open>
  A Euclidean semiring is a semiring upon which the Euclidean algorithm can be
  implemented. It must provide:
  \begin{itemize}
  \item division with remainder
  \item a size function such that @{term "size (a mod b) < size b"} 
        for any @{term "b \<noteq> 0"}
  \end{itemize}
  The existence of these functions makes it possible to derive gcd and lcm functions 
  for any Euclidean semiring.
\<close> 
class euclidean_semiring = divide_modulo + normalization_semidom + 
  fixes euclidean_size :: "'a \<Rightarrow> nat"
  assumes size_0 [simp]: "euclidean_size 0 = 0"
  assumes mod_size_less: 
    "b \<noteq> 0 \<Longrightarrow> euclidean_size (a mod b) < euclidean_size b"
  assumes size_mult_mono:
    "b \<noteq> 0 \<Longrightarrow> euclidean_size a \<le> euclidean_size (a * b)"
begin

lemma euclidean_size_normalize [simp]:
  "euclidean_size (normalize a) = euclidean_size a"
proof (cases "a = 0")
  case True
  then show ?thesis
    by simp
next
  case [simp]: False
  have "euclidean_size (normalize a) \<le> euclidean_size (normalize a * unit_factor a)"
    by (rule size_mult_mono) simp
  moreover have "euclidean_size a \<le> euclidean_size (a * (1 div unit_factor a))"
    by (rule size_mult_mono) simp
  ultimately show ?thesis
    by simp
qed

lemma euclidean_division:
  fixes a :: 'a and b :: 'a
  assumes "b \<noteq> 0"
  obtains s and t where "a = s * b + t" 
    and "euclidean_size t < euclidean_size b"
proof -
  from div_mod_equality [of a b 0] 
     have "a = a div b * b + a mod b" by simp
  with that and assms show ?thesis by (auto simp add: mod_size_less)
qed

lemma zero_mod_left [simp]: "0 mod a = 0"
  using div_mod_equality[of 0 a 0] by simp

lemma dvd_mod_iff [simp]: 
  assumes "k dvd n"
  shows   "(k dvd m mod n) = (k dvd m)"
proof -
  thm div_mod_equality
  from assms have "(k dvd m mod n) \<longleftrightarrow> (k dvd ((m div n) * n + m mod n))" 
    by (simp add: dvd_add_right_iff)
  also have "(m div n) * n + m mod n = m"
    using div_mod_equality[of m n 0] by simp
  finally show ?thesis .
qed

lemma mod_0_imp_dvd: 
  assumes "a mod b = 0"
  shows   "b dvd a"
proof -
  have "b dvd ((a div b) * b)" by simp
  also have "(a div b) * b = a"
    using div_mod_equality[of a b 0] by (simp add: assms)
  finally show ?thesis .
qed

lemma dvd_euclidean_size_eq_imp_dvd:
  assumes "a \<noteq> 0" and b_dvd_a: "b dvd a" and size_eq: "euclidean_size a = euclidean_size b"
  shows "a dvd b"
proof (rule ccontr)
  assume "\<not> a dvd b"
  hence "b mod a \<noteq> 0" using mod_0_imp_dvd[of b a] by blast
  then have "b mod a \<noteq> 0" by (simp add: mod_eq_0_iff_dvd)
  from b_dvd_a have b_dvd_mod: "b dvd b mod a" by simp
  from b_dvd_mod obtain c where "b mod a = b * c" unfolding dvd_def by blast
    with \<open>b mod a \<noteq> 0\<close> have "c \<noteq> 0" by auto
  with \<open>b mod a = b * c\<close> have "euclidean_size (b mod a) \<ge> euclidean_size b"
      using size_mult_mono by force
  moreover from \<open>\<not> a dvd b\<close> and \<open>a \<noteq> 0\<close>
  have "euclidean_size (b mod a) < euclidean_size a"
      using mod_size_less by blast
  ultimately show False using size_eq by simp
qed

lemma size_mult_mono': "b \<noteq> 0 \<Longrightarrow> euclidean_size a \<le> euclidean_size (b * a)"
  by (subst mult.commute) (rule size_mult_mono)

lemma euclidean_size_times_unit:
  assumes "is_unit a"
  shows   "euclidean_size (a * b) = euclidean_size b"
proof (rule antisym)
  from assms have [simp]: "a \<noteq> 0" by auto
  thus "euclidean_size (a * b) \<ge> euclidean_size b" by (rule size_mult_mono')
  from assms have "is_unit (1 div a)" by simp
  hence "1 div a \<noteq> 0" by (intro notI) simp_all
  hence "euclidean_size (a * b) \<le> euclidean_size ((1 div a) * (a * b))"
    by (rule size_mult_mono')
  also from assms have "(1 div a) * (a * b) = b"
    by (simp add: algebra_simps unit_div_mult_swap)
  finally show "euclidean_size (a * b) \<le> euclidean_size b" .
qed

lemma euclidean_size_unit: "is_unit x \<Longrightarrow> euclidean_size x = euclidean_size 1"
  using euclidean_size_times_unit[of x 1] by simp

lemma unit_iff_euclidean_size: 
  "is_unit x \<longleftrightarrow> euclidean_size x = euclidean_size 1 \<and> x \<noteq> 0"
proof safe
  assume A: "x \<noteq> 0" and B: "euclidean_size x = euclidean_size 1"
  show "is_unit x" by (rule dvd_euclidean_size_eq_imp_dvd[OF A _ B]) simp_all
qed (auto intro: euclidean_size_unit)

lemma euclidean_size_times_nonunit:
  assumes "a \<noteq> 0" "b \<noteq> 0" "\<not>is_unit a"
  shows   "euclidean_size b < euclidean_size (a * b)"
proof (rule ccontr)
  assume "\<not>euclidean_size b < euclidean_size (a * b)"
  with size_mult_mono'[OF assms(1), of b] 
    have eq: "euclidean_size (a * b) = euclidean_size b" by simp
  have "a * b dvd b"
    by (rule dvd_euclidean_size_eq_imp_dvd[OF _ _ eq]) (insert assms, simp_all)
  hence "a * b dvd 1 * b" by simp
  with \<open>b \<noteq> 0\<close> have "is_unit a" by (subst (asm) dvd_times_right_cancel_iff)
  with assms(3) show False by contradiction
qed

lemma dvd_imp_size_le:
  assumes "x dvd y" "y \<noteq> 0" 
  shows   "euclidean_size x \<le> euclidean_size y"
  using assms by (auto elim!: dvdE simp: size_mult_mono)

lemma dvd_proper_imp_size_less:
  assumes "x dvd y" "\<not>y dvd x" "y \<noteq> 0" 
  shows   "euclidean_size x < euclidean_size y"
proof -
  from assms(1) obtain z where "y = x * z" by (erule dvdE)
  hence z: "y = z * x" by (simp add: mult.commute)
  from z assms have "\<not>is_unit z" by (auto simp: mult.commute mult_unit_dvd_iff)
  with z assms show ?thesis
    by (auto intro!: euclidean_size_times_nonunit simp: )
qed

function gcd_eucl :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "gcd_eucl a b = (if b = 0 then normalize a else gcd_eucl b (a mod b))"
  by pat_completeness simp
termination
  by (relation "measure (euclidean_size \<circ> snd)") (simp_all add: mod_size_less)

declare gcd_eucl.simps [simp del]

lemma gcd_eucl_induct [case_names zero mod]:
  assumes H1: "\<And>b. P b 0"
  and H2: "\<And>a b. b \<noteq> 0 \<Longrightarrow> P b (a mod b) \<Longrightarrow> P a b"
  shows "P a b"
proof (induct a b rule: gcd_eucl.induct)
  case ("1" a b)
  show ?case
  proof (cases "b = 0")
    case True then show "P a b" by simp (rule H1)
  next
    case False
    then have "P b (a mod b)"
      by (rule "1.hyps")
    with \<open>b \<noteq> 0\<close> show "P a b"
      by (blast intro: H2)
  qed
qed

definition lcm_eucl :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "lcm_eucl a b = normalize (a * b) div gcd_eucl a b"

definition Lcm_eucl :: "'a set \<Rightarrow> 'a" \<comment> \<open>
  Somewhat complicated definition of Lcm that has the advantage of working
  for infinite sets as well\<close>
where
  "Lcm_eucl A = (if \<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) then
     let l = SOME l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l =
       (LEAST n. \<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n)
       in normalize l 
      else 0)"

definition Gcd_eucl :: "'a set \<Rightarrow> 'a"
where
  "Gcd_eucl A = Lcm_eucl {d. \<forall>a\<in>A. d dvd a}"

declare Lcm_eucl_def Gcd_eucl_def [code del]

lemma gcd_eucl_0:
  "gcd_eucl a 0 = normalize a"
  by (simp add: gcd_eucl.simps [of a 0])

lemma gcd_eucl_0_left:
  "gcd_eucl 0 a = normalize a"
  by (simp_all add: gcd_eucl_0 gcd_eucl.simps [of 0 a])

lemma gcd_eucl_non_0:
  "b \<noteq> 0 \<Longrightarrow> gcd_eucl a b = gcd_eucl b (a mod b)"
  by (simp add: gcd_eucl.simps [of a b] gcd_eucl.simps [of b 0])

lemma gcd_eucl_dvd1 [iff]: "gcd_eucl a b dvd a"
  and gcd_eucl_dvd2 [iff]: "gcd_eucl a b dvd b"
  by (induct a b rule: gcd_eucl_induct)
     (simp_all add: gcd_eucl_0 gcd_eucl_non_0 dvd_mod_iff)

lemma normalize_gcd_eucl [simp]:
  "normalize (gcd_eucl a b) = gcd_eucl a b"
  by (induct a b rule: gcd_eucl_induct) (simp_all add: gcd_eucl_0 gcd_eucl_non_0)
     
lemma gcd_eucl_greatest:
  fixes k a b :: 'a
  shows "k dvd a \<Longrightarrow> k dvd b \<Longrightarrow> k dvd gcd_eucl a b"
proof (induct a b rule: gcd_eucl_induct)
  case (zero a) from zero(1) show ?case by (rule dvd_trans) (simp add: gcd_eucl_0)
next
  case (mod a b)
  then show ?case
    by (simp add: gcd_eucl_non_0 dvd_mod_iff)
qed

lemma gcd_euclI:
  fixes gcd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes "d dvd a" "d dvd b" "normalize d = d"
          "\<And>k. k dvd a \<Longrightarrow> k dvd b \<Longrightarrow> k dvd d"
  shows   "gcd_eucl a b = d"
  by (rule associated_eqI) (simp_all add: gcd_eucl_greatest assms)

lemma eq_gcd_euclI:
  fixes gcd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes "\<And>a b. gcd a b dvd a" "\<And>a b. gcd a b dvd b" "\<And>a b. normalize (gcd a b) = gcd a b"
          "\<And>a b k. k dvd a \<Longrightarrow> k dvd b \<Longrightarrow> k dvd gcd a b"
  shows   "gcd = gcd_eucl"
  by (intro ext, rule associated_eqI) (simp_all add: gcd_eucl_greatest assms)

lemma gcd_eucl_zero [simp]:
  "gcd_eucl a b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  by (metis dvd_0_left dvd_refl gcd_eucl_dvd1 gcd_eucl_dvd2 gcd_eucl_greatest)+

  
lemma dvd_Lcm_eucl [simp]: "a \<in> A \<Longrightarrow> a dvd Lcm_eucl A"
  and Lcm_eucl_least: "(\<And>a. a \<in> A \<Longrightarrow> a dvd b) \<Longrightarrow> Lcm_eucl A dvd b"
  and unit_factor_Lcm_eucl [simp]: 
          "unit_factor (Lcm_eucl A) = (if Lcm_eucl A = 0 then 0 else 1)"
proof -
  have "(\<forall>a\<in>A. a dvd Lcm_eucl A) \<and> (\<forall>l'. (\<forall>a\<in>A. a dvd l') \<longrightarrow> Lcm_eucl A dvd l') \<and>
    unit_factor (Lcm_eucl A) = (if Lcm_eucl A = 0 then 0 else 1)" (is ?thesis)
  proof (cases "\<exists>l. l \<noteq>  0 \<and> (\<forall>a\<in>A. a dvd l)")
    case False
    hence "Lcm_eucl A = 0" by (auto simp: Lcm_eucl_def)
    with False show ?thesis by auto
  next
    case True
    then obtain l\<^sub>0 where l\<^sub>0_props: "l\<^sub>0 \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l\<^sub>0)" by blast
    define n where "n = (LEAST n. \<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n)"
    define l where "l = (SOME l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n)"
    have "\<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n"
      apply (subst n_def)
      apply (rule LeastI[of _ "euclidean_size l\<^sub>0"])
      apply (rule exI[of _ l\<^sub>0])
      apply (simp add: l\<^sub>0_props)
      done
    from someI_ex[OF this] have "l \<noteq> 0" and "\<forall>a\<in>A. a dvd l" and "euclidean_size l = n" 
      unfolding l_def by simp_all
    {
      fix l' assume "\<forall>a\<in>A. a dvd l'"
      with \<open>\<forall>a\<in>A. a dvd l\<close> have "\<forall>a\<in>A. a dvd gcd_eucl l l'" by (auto intro: gcd_eucl_greatest)
      moreover from \<open>l \<noteq> 0\<close> have "gcd_eucl l l' \<noteq> 0" by simp
      ultimately have "\<exists>b. b \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd b) \<and> 
                          euclidean_size b = euclidean_size (gcd_eucl l l')"
        by (intro exI[of _ "gcd_eucl l l'"], auto)
      hence "euclidean_size (gcd_eucl l l') \<ge> n" by (subst n_def) (rule Least_le)
      moreover have "euclidean_size (gcd_eucl l l') \<le> n"
      proof -
        have "gcd_eucl l l' dvd l" by simp
        then obtain a where "l = gcd_eucl l l' * a" unfolding dvd_def by blast
        with \<open>l \<noteq> 0\<close> have "a \<noteq> 0" by auto
        hence "euclidean_size (gcd_eucl l l') \<le> euclidean_size (gcd_eucl l l' * a)"
          by (rule size_mult_mono)
        also have "gcd_eucl l l' * a = l" using \<open>l = gcd_eucl l l' * a\<close> ..
        also note \<open>euclidean_size l = n\<close>
        finally show "euclidean_size (gcd_eucl l l') \<le> n" .
      qed
      ultimately have *: "euclidean_size l = euclidean_size (gcd_eucl l l')" 
        by (intro le_antisym, simp_all add: \<open>euclidean_size l = n\<close>)
      from \<open>l \<noteq> 0\<close> have "l dvd gcd_eucl l l'"
        by (rule dvd_euclidean_size_eq_imp_dvd) (auto simp add: *)
      hence "l dvd l'" by (rule dvd_trans[OF _ gcd_eucl_dvd2])
    }

    with \<open>(\<forall>a\<in>A. a dvd l)\<close> and unit_factor_is_unit[OF \<open>l \<noteq> 0\<close>] and \<open>l \<noteq> 0\<close>
      have "(\<forall>a\<in>A. a dvd normalize l) \<and> 
        (\<forall>l'. (\<forall>a\<in>A. a dvd l') \<longrightarrow> normalize l dvd l') \<and>
        unit_factor (normalize l) = 
        (if normalize l = 0 then 0 else 1)"
      by (auto simp: unit_simps)
    also from True have "normalize l = Lcm_eucl A"
      by (simp add: Lcm_eucl_def Let_def n_def l_def)
    finally show ?thesis .
  qed
  note A = this

  {fix a assume "a \<in> A" then show "a dvd Lcm_eucl A" using A by blast}
  {fix b assume "\<And>a. a \<in> A \<Longrightarrow> a dvd b" then show "Lcm_eucl A dvd b" using A by blast}
  from A show "unit_factor (Lcm_eucl A) = (if Lcm_eucl A = 0 then 0 else 1)" by blast
qed

lemma normalize_Lcm_eucl [simp]:
  "normalize (Lcm_eucl A) = Lcm_eucl A"
proof (cases "Lcm_eucl A = 0")
  case True then show ?thesis by simp
next
  case False
  have "unit_factor (Lcm_eucl A) * normalize (Lcm_eucl A) = Lcm_eucl A"
    by (fact unit_factor_mult_normalize)
  with False show ?thesis by simp
qed

lemma eq_Lcm_euclI:
  fixes lcm :: "'a set \<Rightarrow> 'a"
  assumes "\<And>A a. a \<in> A \<Longrightarrow> a dvd lcm A" and "\<And>A c. (\<And>a. a \<in> A \<Longrightarrow> a dvd c) \<Longrightarrow> lcm A dvd c"
          "\<And>A. normalize (lcm A) = lcm A" shows "lcm = Lcm_eucl"
  by (intro ext, rule associated_eqI) (auto simp: assms intro: Lcm_eucl_least)  

lemma Gcd_eucl_dvd: "x \<in> A \<Longrightarrow> Gcd_eucl A dvd x"
  unfolding Gcd_eucl_def by (auto intro: Lcm_eucl_least)

lemma Gcd_eucl_greatest: "(\<And>x. x \<in> A \<Longrightarrow> d dvd x) \<Longrightarrow> d dvd Gcd_eucl A"
  unfolding Gcd_eucl_def by auto

lemma normalize_Gcd_eucl [simp]: "normalize (Gcd_eucl A) = Gcd_eucl A"
  by (simp add: Gcd_eucl_def)

lemma Lcm_euclI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> x dvd d" "\<And>d'. (\<And>x. x \<in> A \<Longrightarrow> x dvd d') \<Longrightarrow> d dvd d'" "normalize d = d"
  shows   "Lcm_eucl A = d"
proof -
  have "normalize (Lcm_eucl A) = normalize d"
    by (intro associatedI) (auto intro: dvd_Lcm_eucl Lcm_eucl_least assms)
  thus ?thesis by (simp add: assms)
qed

lemma Gcd_euclI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> d dvd x" "\<And>d'. (\<And>x. x \<in> A \<Longrightarrow> d' dvd x) \<Longrightarrow> d' dvd d" "normalize d = d"
  shows   "Gcd_eucl A = d"
proof -
  have "normalize (Gcd_eucl A) = normalize d"
    by (intro associatedI) (auto intro: Gcd_eucl_dvd Gcd_eucl_greatest assms)
  thus ?thesis by (simp add: assms)
qed
  
lemmas lcm_gcd_eucl_facts = 
  gcd_eucl_dvd1 gcd_eucl_dvd2 gcd_eucl_greatest normalize_gcd_eucl lcm_eucl_def
  Gcd_eucl_def Gcd_eucl_dvd Gcd_eucl_greatest normalize_Gcd_eucl
  dvd_Lcm_eucl Lcm_eucl_least normalize_Lcm_eucl

lemma normalized_factors_product:
  "{p. p dvd a * b \<and> normalize p = p} = 
     (\<lambda>(x,y). x * y) ` ({p. p dvd a \<and> normalize p = p} \<times> {p. p dvd b \<and> normalize p = p})"
proof safe
  fix p assume p: "p dvd a * b" "normalize p = p"
  interpret semiring_gcd 1 0 "op *" gcd_eucl lcm_eucl "op div" "op +" "op -" normalize unit_factor
    by standard (rule lcm_gcd_eucl_facts; assumption)+
  from dvd_productE[OF p(1)] guess x y . note xy = this
  define x' y' where "x' = normalize x" and "y' = normalize y"
  have "p = x' * y'"
    by (subst p(2) [symmetric]) (simp add: xy x'_def y'_def normalize_mult)
  moreover from xy have "normalize x' = x'" "normalize y' = y'" "x' dvd a" "y' dvd b" 
    by (simp_all add: x'_def y'_def)
  ultimately show "p \<in> (\<lambda>(x, y). x * y) ` 
                     ({p. p dvd a \<and> normalize p = p} \<times> {p. p dvd b \<and> normalize p = p})"
    by blast
qed (auto simp: normalize_mult mult_dvd_mono)


subclass factorial_semiring
proof (standard, rule factorial_semiring_altI_aux)
  fix x assume "x \<noteq> 0"
  thus "finite {p. p dvd x \<and> normalize p = p}"
  proof (induction "euclidean_size x" arbitrary: x rule: less_induct)
    case (less x)
    show ?case
    proof (cases "\<exists>y. y dvd x \<and> \<not>x dvd y \<and> \<not>is_unit y")
      case False
      have "{p. p dvd x \<and> normalize p = p} \<subseteq> {1, normalize x}"
      proof
        fix p assume p: "p \<in> {p. p dvd x \<and> normalize p = p}"
        with False have "is_unit p \<or> x dvd p" by blast
        thus "p \<in> {1, normalize x}"
        proof (elim disjE)
          assume "is_unit p"
          hence "normalize p = 1" by (simp add: is_unit_normalize)
          with p show ?thesis by simp
        next
          assume "x dvd p"
          with p have "normalize p = normalize x" by (intro associatedI) simp_all
          with p show ?thesis by simp
        qed
      qed
      moreover have "finite \<dots>" by simp
      ultimately show ?thesis by (rule finite_subset)
      
    next
      case True
      then obtain y where y: "y dvd x" "\<not>x dvd y" "\<not>is_unit y" by blast
      define z where "z = x div y"
      let ?fctrs = "\<lambda>x. {p. p dvd x \<and> normalize p = p}"
      from y have x: "x = y * z" by (simp add: z_def)
      with less.prems have "y \<noteq> 0" "z \<noteq> 0" by auto
      from x y have "\<not>is_unit z" by (auto simp: mult_unit_dvd_iff)
      have "?fctrs x = (\<lambda>(p,p'). p * p') ` (?fctrs y \<times> ?fctrs z)"
        by (subst x) (rule normalized_factors_product)
      also have "\<not>y * z dvd y * 1" "\<not>y * z dvd 1 * z"
        by (subst dvd_times_left_cancel_iff dvd_times_right_cancel_iff; fact)+
      hence "finite ((\<lambda>(p,p'). p * p') ` (?fctrs y \<times> ?fctrs z))"
        by (intro finite_imageI finite_cartesian_product less dvd_proper_imp_size_less)
           (auto simp: x)
      finally show ?thesis .
    qed
  qed
next
  interpret semiring_gcd 1 0 "op *" gcd_eucl lcm_eucl "op div" "op +" "op -" normalize unit_factor
    by standard (rule lcm_gcd_eucl_facts; assumption)+
  fix p assume p: "irreducible p"
  thus "prime_elem p" by (rule irreducible_imp_prime_elem_gcd)
qed

lemma gcd_eucl_eq_gcd_factorial: "gcd_eucl = gcd_factorial"
  by (intro ext gcd_euclI gcd_lcm_factorial)

lemma lcm_eucl_eq_lcm_factorial: "lcm_eucl = lcm_factorial"
  by (intro ext) (simp add: lcm_eucl_def lcm_factorial_gcd_factorial gcd_eucl_eq_gcd_factorial)

lemma Gcd_eucl_eq_Gcd_factorial: "Gcd_eucl = Gcd_factorial"
  by (intro ext Gcd_euclI gcd_lcm_factorial)

lemma Lcm_eucl_eq_Lcm_factorial: "Lcm_eucl = Lcm_factorial"
  by (intro ext Lcm_euclI gcd_lcm_factorial)

lemmas eucl_eq_factorial = 
  gcd_eucl_eq_gcd_factorial lcm_eucl_eq_lcm_factorial 
  Gcd_eucl_eq_Gcd_factorial Lcm_eucl_eq_Lcm_factorial
  
end

class euclidean_ring = euclidean_semiring + idom
begin

function euclid_ext_aux :: "'a \<Rightarrow> _" where
  "euclid_ext_aux r' r s' s t' t = (
     if r = 0 then let c = 1 div unit_factor r' in (s' * c, t' * c, normalize r')
     else let q = r' div r
          in  euclid_ext_aux r (r' mod r) s (s' - q * s) t (t' - q * t))"
by auto
termination by (relation "measure (\<lambda>(_,b,_,_,_,_). euclidean_size b)") (simp_all add: mod_size_less)

declare euclid_ext_aux.simps [simp del]

lemma euclid_ext_aux_correct:
  assumes "gcd_eucl r' r = gcd_eucl x y"
  assumes "s' * x + t' * y = r'"
  assumes "s * x + t * y = r"
  shows   "case euclid_ext_aux r' r s' s t' t of (a,b,c) \<Rightarrow>
             a * x + b * y = c \<and> c = gcd_eucl x y" (is "?P (euclid_ext_aux r' r s' s t' t)")
using assms
proof (induction r' r s' s t' t rule: euclid_ext_aux.induct)
  case (1 r' r s' s t' t)
  show ?case
  proof (cases "r = 0")
    case True
    hence "euclid_ext_aux r' r s' s t' t = 
             (s' div unit_factor r', t' div unit_factor r', normalize r')"
      by (subst euclid_ext_aux.simps) (simp add: Let_def)
    also have "?P \<dots>"
    proof safe
      have "s' div unit_factor r' * x + t' div unit_factor r' * y = 
                (s' * x + t' * y) div unit_factor r'"
        by (cases "r' = 0") (simp_all add: unit_div_commute)
      also have "s' * x + t' * y = r'" by fact
      also have "\<dots> div unit_factor r' = normalize r'" by simp
      finally show "s' div unit_factor r' * x + t' div unit_factor r' * y = normalize r'" .
    next
      from "1.prems" True show "normalize r' = gcd_eucl x y" by (simp add: gcd_eucl_0)
    qed
    finally show ?thesis .
  next
    case False
    hence "euclid_ext_aux r' r s' s t' t = 
             euclid_ext_aux r (r' mod r) s (s' - r' div r * s) t (t' - r' div r * t)"
      by (subst euclid_ext_aux.simps) (simp add: Let_def)
    also from "1.prems" False have "?P \<dots>"
    proof (intro "1.IH")
      have "(s' - r' div r * s) * x + (t' - r' div r * t) * y =
              (s' * x + t' * y) - r' div r * (s * x + t * y)" by (simp add: algebra_simps)
      also have "s' * x + t' * y = r'" by fact
      also have "s * x + t * y = r" by fact
      also have "r' - r' div r * r = r' mod r" using div_mod_equality[of r' r]
        by (simp add: algebra_simps)
      finally show "(s' - r' div r * s) * x + (t' - r' div r * t) * y = r' mod r" .
    qed (auto simp: gcd_eucl_non_0 algebra_simps div_mod_equality')
    finally show ?thesis .
  qed
qed

definition euclid_ext where
  "euclid_ext a b = euclid_ext_aux a b 1 0 0 1"

lemma euclid_ext_0: 
  "euclid_ext a 0 = (1 div unit_factor a, 0, normalize a)"
  by (simp add: euclid_ext_def euclid_ext_aux.simps)

lemma euclid_ext_left_0: 
  "euclid_ext 0 a = (0, 1 div unit_factor a, normalize a)"
  by (simp add: euclid_ext_def euclid_ext_aux.simps)

lemma euclid_ext_correct':
  "case euclid_ext x y of (a,b,c) \<Rightarrow> a * x + b * y = c \<and> c = gcd_eucl x y"
  unfolding euclid_ext_def by (rule euclid_ext_aux_correct) simp_all

lemma euclid_ext_gcd_eucl:
  "(case euclid_ext x y of (a,b,c) \<Rightarrow> c) = gcd_eucl x y"
  using euclid_ext_correct'[of x y] by (simp add: case_prod_unfold)

definition euclid_ext' where
  "euclid_ext' x y = (case euclid_ext x y of (a, b, _) \<Rightarrow> (a, b))"

lemma euclid_ext'_correct':
  "case euclid_ext' x y of (a,b) \<Rightarrow> a * x + b * y = gcd_eucl x y"
  using euclid_ext_correct'[of x y] by (simp add: case_prod_unfold euclid_ext'_def)

lemma euclid_ext'_0: "euclid_ext' a 0 = (1 div unit_factor a, 0)" 
  by (simp add: euclid_ext'_def euclid_ext_0)

lemma euclid_ext'_left_0: "euclid_ext' 0 a = (0, 1 div unit_factor a)" 
  by (simp add: euclid_ext'_def euclid_ext_left_0)

end

class euclidean_semiring_gcd = euclidean_semiring + gcd + Gcd +
  assumes gcd_gcd_eucl: "gcd = gcd_eucl" and lcm_lcm_eucl: "lcm = lcm_eucl"
  assumes Gcd_Gcd_eucl: "Gcd = Gcd_eucl" and Lcm_Lcm_eucl: "Lcm = Lcm_eucl"
begin

subclass semiring_gcd
  by standard (simp_all add: gcd_gcd_eucl gcd_eucl_greatest lcm_lcm_eucl lcm_eucl_def)

subclass semiring_Gcd
  by standard (auto simp: Gcd_Gcd_eucl Lcm_Lcm_eucl Gcd_eucl_def intro: Lcm_eucl_least)

subclass factorial_semiring_gcd
proof
  fix a b
  show "gcd a b = gcd_factorial a b"
    by (rule sym, rule gcdI) (rule gcd_lcm_factorial; assumption)+
  thus "lcm a b = lcm_factorial a b"
    by (simp add: lcm_factorial_gcd_factorial lcm_gcd)
next
  fix A 
  show "Gcd A = Gcd_factorial A"
    by (rule sym, rule GcdI) (rule gcd_lcm_factorial; assumption)+
  show "Lcm A = Lcm_factorial A"
    by (rule sym, rule LcmI) (rule gcd_lcm_factorial; assumption)+
qed

lemma gcd_non_0:
  "b \<noteq> 0 \<Longrightarrow> gcd a b = gcd b (a mod b)"
  unfolding gcd_gcd_eucl by (fact gcd_eucl_non_0)

lemmas gcd_0 = gcd_0_right
lemmas dvd_gcd_iff = gcd_greatest_iff
lemmas gcd_greatest_iff = dvd_gcd_iff

lemma gcd_mod1 [simp]:
  "gcd (a mod b) b = gcd a b"
  by (rule gcdI, metis dvd_mod_iff gcd_dvd1 gcd_dvd2, simp_all add: gcd_greatest dvd_mod_iff)

lemma gcd_mod2 [simp]:
  "gcd a (b mod a) = gcd a b"
  by (rule gcdI, simp, metis dvd_mod_iff gcd_dvd1 gcd_dvd2, simp_all add: gcd_greatest dvd_mod_iff)
         
lemma euclidean_size_gcd_le1 [simp]:
  assumes "a \<noteq> 0"
  shows "euclidean_size (gcd a b) \<le> euclidean_size a"
proof -
   have "gcd a b dvd a" by (rule gcd_dvd1)
   then obtain c where A: "a = gcd a b * c" unfolding dvd_def by blast
   with \<open>a \<noteq> 0\<close> show ?thesis by (subst (2) A, intro size_mult_mono) auto
qed

lemma euclidean_size_gcd_le2 [simp]:
  "b \<noteq> 0 \<Longrightarrow> euclidean_size (gcd a b) \<le> euclidean_size b"
  by (subst gcd.commute, rule euclidean_size_gcd_le1)

lemma euclidean_size_gcd_less1:
  assumes "a \<noteq> 0" and "\<not>a dvd b"
  shows "euclidean_size (gcd a b) < euclidean_size a"
proof (rule ccontr)
  assume "\<not>euclidean_size (gcd a b) < euclidean_size a"
  with \<open>a \<noteq> 0\<close> have A: "euclidean_size (gcd a b) = euclidean_size a"
    by (intro le_antisym, simp_all)
  have "a dvd gcd a b"
    by (rule dvd_euclidean_size_eq_imp_dvd) (simp_all add: assms A)
  hence "a dvd b" using dvd_gcdD2 by blast
  with \<open>\<not>a dvd b\<close> show False by contradiction
qed

lemma euclidean_size_gcd_less2:
  assumes "b \<noteq> 0" and "\<not>b dvd a"
  shows "euclidean_size (gcd a b) < euclidean_size b"
  using assms by (subst gcd.commute, rule euclidean_size_gcd_less1)

lemma euclidean_size_lcm_le1: 
  assumes "a \<noteq> 0" and "b \<noteq> 0"
  shows "euclidean_size a \<le> euclidean_size (lcm a b)"
proof -
  have "a dvd lcm a b" by (rule dvd_lcm1)
  then obtain c where A: "lcm a b = a * c" ..
  with \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close> have "c \<noteq> 0" by (auto simp: lcm_eq_0_iff)
  then show ?thesis by (subst A, intro size_mult_mono)
qed

lemma euclidean_size_lcm_le2:
  "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> euclidean_size b \<le> euclidean_size (lcm a b)"
  using euclidean_size_lcm_le1 [of b a] by (simp add: ac_simps)

lemma euclidean_size_lcm_less1:
  assumes "b \<noteq> 0" and "\<not>b dvd a"
  shows "euclidean_size a < euclidean_size (lcm a b)"
proof (rule ccontr)
  from assms have "a \<noteq> 0" by auto
  assume "\<not>euclidean_size a < euclidean_size (lcm a b)"
  with \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close> have "euclidean_size (lcm a b) = euclidean_size a"
    by (intro le_antisym, simp, intro euclidean_size_lcm_le1)
  with assms have "lcm a b dvd a" 
    by (rule_tac dvd_euclidean_size_eq_imp_dvd) (auto simp: lcm_eq_0_iff)
  hence "b dvd a" by (rule lcm_dvdD2)
  with \<open>\<not>b dvd a\<close> show False by contradiction
qed

lemma euclidean_size_lcm_less2:
  assumes "a \<noteq> 0" and "\<not>a dvd b"
  shows "euclidean_size b < euclidean_size (lcm a b)"
  using assms euclidean_size_lcm_less1 [of a b] by (simp add: ac_simps)

lemma Lcm_eucl_set [code]:
  "Lcm_eucl (set xs) = foldl lcm_eucl 1 xs"
  by (simp add: Lcm_Lcm_eucl [symmetric] lcm_lcm_eucl Lcm_set)

lemma Gcd_eucl_set [code]:
  "Gcd_eucl (set xs) = foldl gcd_eucl 0 xs"
  by (simp add: Gcd_Gcd_eucl [symmetric] gcd_gcd_eucl Gcd_set)

end


text \<open>
  A Euclidean ring is a Euclidean semiring with additive inverses. It provides a 
  few more lemmas; in particular, Bezout's lemma holds for any Euclidean ring.
\<close>

class euclidean_ring_gcd = euclidean_semiring_gcd + idom
begin

subclass euclidean_ring ..
subclass ring_gcd ..
subclass factorial_ring_gcd ..

lemma euclid_ext_gcd [simp]:
  "(case euclid_ext a b of (_, _ , t) \<Rightarrow> t) = gcd a b"
  using euclid_ext_correct'[of a b] by (simp add: case_prod_unfold Let_def gcd_gcd_eucl)

lemma euclid_ext_gcd' [simp]:
  "euclid_ext a b = (r, s, t) \<Longrightarrow> t = gcd a b"
  by (insert euclid_ext_gcd[of a b], drule (1) subst, simp)

lemma euclid_ext_correct:
  "case euclid_ext x y of (a,b,c) \<Rightarrow> a * x + b * y = c \<and> c = gcd x y"
  using euclid_ext_correct'[of x y]
  by (simp add: gcd_gcd_eucl case_prod_unfold)
  
lemma euclid_ext'_correct:
  "fst (euclid_ext' a b) * a + snd (euclid_ext' a b) * b = gcd a b"
  using euclid_ext_correct'[of a b]
  by (simp add: gcd_gcd_eucl case_prod_unfold euclid_ext'_def)

lemma bezout: "\<exists>s t. s * a + t * b = gcd a b"
  using euclid_ext'_correct by blast

end


subsection \<open>Typical instances\<close>

instantiation nat :: euclidean_semiring
begin

definition [simp]:
  "euclidean_size_nat = (id :: nat \<Rightarrow> nat)"

instance by standard simp_all

end


instantiation int :: euclidean_ring
begin

definition [simp]:
  "euclidean_size_int = (nat \<circ> abs :: int \<Rightarrow> nat)"

instance by standard (auto simp add: abs_mult nat_mult_distrib split: abs_split)

end

instance nat :: euclidean_semiring_gcd
proof
  show [simp]: "gcd = (gcd_eucl :: nat \<Rightarrow> _)" "Lcm = (Lcm_eucl :: nat set \<Rightarrow> _)"
    by (simp_all add: eq_gcd_euclI eq_Lcm_euclI)
  show "lcm = (lcm_eucl :: nat \<Rightarrow> _)" "Gcd = (Gcd_eucl :: nat set \<Rightarrow> _)"
    by (intro ext, simp add: lcm_eucl_def lcm_nat_def Gcd_nat_def Gcd_eucl_def)+
qed

instance int :: euclidean_ring_gcd
proof
  show [simp]: "gcd = (gcd_eucl :: int \<Rightarrow> _)" "Lcm = (Lcm_eucl :: int set \<Rightarrow> _)"
    by (simp_all add: eq_gcd_euclI eq_Lcm_euclI)
  show "lcm = (lcm_eucl :: int \<Rightarrow> _)" "Gcd = (Gcd_eucl :: int set \<Rightarrow> _)"
    by (intro ext, simp add: lcm_eucl_def lcm_altdef_int 
          semiring_Gcd_class.Gcd_Lcm Gcd_eucl_def abs_mult)+
qed

end
