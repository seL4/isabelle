(*  Title:      HOL/Computational_Algebra/Euclidean_Algorithm.thy
    Author:     Manuel Eberl, TU Muenchen
*)

section \<open>Abstract euclidean algorithm in euclidean (semi)rings\<close>

theory Euclidean_Algorithm
  imports Factorial_Ring
begin

subsection \<open>Generic construction of the (simple) euclidean algorithm\<close>

class normalization_euclidean_semiring = euclidean_semiring + normalization_semidom
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

context
begin

qualified function gcd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "gcd a b = (if b = 0 then normalize a else gcd b (a mod b))"
  by pat_completeness simp
termination
  by (relation "measure (euclidean_size \<circ> snd)") (simp_all add: mod_size_less)

declare gcd.simps [simp del]

lemma eucl_induct [case_names zero mod]:
  assumes H1: "\<And>b. P b 0"
  and H2: "\<And>a b. b \<noteq> 0 \<Longrightarrow> P b (a mod b) \<Longrightarrow> P a b"
  shows "P a b"
proof (induct a b rule: gcd.induct)
  case (1 a b)
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
  
qualified lemma gcd_0:
  "gcd a 0 = normalize a"
  by (simp add: gcd.simps [of a 0])
  
qualified lemma gcd_mod:
  "a \<noteq> 0 \<Longrightarrow> gcd a (b mod a) = gcd b a"
  by (simp add: gcd.simps [of b 0] gcd.simps [of b a])

qualified definition lcm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "lcm a b = normalize (a * b div gcd a b)"

qualified definition Lcm :: "'a set \<Rightarrow> 'a" \<comment> \<open>Somewhat complicated definition of Lcm that has the advantage of working
    for infinite sets as well\<close>
  where
  [code del]: "Lcm A = (if \<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) then
     let l = SOME l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l =
       (LEAST n. \<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n)
       in normalize l 
      else 0)"

qualified definition Gcd :: "'a set \<Rightarrow> 'a"
  where [code del]: "Gcd A = Lcm {d. \<forall>a\<in>A. d dvd a}"

end    

lemma semiring_gcd:
  "class.semiring_gcd one zero times gcd lcm
    divide plus minus unit_factor normalize"
proof
  show "gcd a b dvd a"
    and "gcd a b dvd b" for a b
    by (induct a b rule: eucl_induct)
      (simp_all add: local.gcd_0 local.gcd_mod dvd_mod_iff)
next
  show "c dvd a \<Longrightarrow> c dvd b \<Longrightarrow> c dvd gcd a b" for a b c
  proof (induct a b rule: eucl_induct)
    case (zero a) from \<open>c dvd a\<close> show ?case
      by (rule dvd_trans) (simp add: local.gcd_0)
  next
    case (mod a b)
    then show ?case
      by (simp add: local.gcd_mod dvd_mod_iff)
  qed
next
  show "normalize (gcd a b) = gcd a b" for a b
    by (induct a b rule: eucl_induct)
      (simp_all add: local.gcd_0 local.gcd_mod)
next
  show "lcm a b = normalize (a * b div gcd a b)" for a b
    by (fact local.lcm_def)
qed

interpretation semiring_gcd one zero times gcd lcm
  divide plus minus unit_factor normalize
  by (fact semiring_gcd)
  
lemma semiring_Gcd:
  "class.semiring_Gcd one zero times gcd lcm Gcd Lcm
    divide plus minus unit_factor normalize"
proof -
  show ?thesis
  proof
    have "(\<forall>a\<in>A. a dvd Lcm A) \<and> (\<forall>b. (\<forall>a\<in>A. a dvd b) \<longrightarrow> Lcm A dvd b)" for A
    proof (cases "\<exists>l. l \<noteq>  0 \<and> (\<forall>a\<in>A. a dvd l)")
      case False
      then have "Lcm A = 0"
        by (auto simp add: local.Lcm_def)
      with False show ?thesis
        by auto
    next
      case True
      then obtain l\<^sub>0 where l\<^sub>0_props: "l\<^sub>0 \<noteq> 0" "\<forall>a\<in>A. a dvd l\<^sub>0" by blast
      define n where "n = (LEAST n. \<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n)"
      define l where "l = (SOME l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n)"
      have "\<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n"
        apply (subst n_def)
        apply (rule LeastI [of _ "euclidean_size l\<^sub>0"])
        apply (rule exI [of _ l\<^sub>0])
        apply (simp add: l\<^sub>0_props)
        done
      from someI_ex [OF this] have "l \<noteq> 0" and "\<forall>a\<in>A. a dvd l"
        and "euclidean_size l = n" 
        unfolding l_def by simp_all
      {
        fix l' assume "\<forall>a\<in>A. a dvd l'"
        with \<open>\<forall>a\<in>A. a dvd l\<close> have "\<forall>a\<in>A. a dvd gcd l l'"
          by (auto intro: gcd_greatest)
        moreover from \<open>l \<noteq> 0\<close> have "gcd l l' \<noteq> 0"
          by simp
        ultimately have "\<exists>b. b \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd b) \<and> 
          euclidean_size b = euclidean_size (gcd l l')"
          by (intro exI [of _ "gcd l l'"], auto)
        then have "euclidean_size (gcd l l') \<ge> n"
          by (subst n_def) (rule Least_le)
        moreover have "euclidean_size (gcd l l') \<le> n"
        proof -
          have "gcd l l' dvd l"
            by simp
          then obtain a where "l = gcd l l' * a" ..
          with \<open>l \<noteq> 0\<close> have "a \<noteq> 0"
            by auto
          hence "euclidean_size (gcd l l') \<le> euclidean_size (gcd l l' * a)"
            by (rule size_mult_mono)
          also have "gcd l l' * a = l" using \<open>l = gcd l l' * a\<close> ..
          also note \<open>euclidean_size l = n\<close>
          finally show "euclidean_size (gcd l l') \<le> n" .
        qed
        ultimately have *: "euclidean_size l = euclidean_size (gcd l l')" 
          by (intro le_antisym, simp_all add: \<open>euclidean_size l = n\<close>)
        from \<open>l \<noteq> 0\<close> have "l dvd gcd l l'"
          by (rule dvd_euclidean_size_eq_imp_dvd) (auto simp add: *)
        hence "l dvd l'" by (rule dvd_trans [OF _ gcd_dvd2])
      }
      with \<open>\<forall>a\<in>A. a dvd l\<close> and \<open>l \<noteq> 0\<close>
        have "(\<forall>a\<in>A. a dvd normalize l) \<and> 
          (\<forall>l'. (\<forall>a\<in>A. a dvd l') \<longrightarrow> normalize l dvd l')"
        by auto
      also from True have "normalize l = Lcm A"
        by (simp add: local.Lcm_def Let_def n_def l_def)
      finally show ?thesis .
    qed
    then show dvd_Lcm: "a \<in> A \<Longrightarrow> a dvd Lcm A"
      and Lcm_least: "(\<And>a. a \<in> A \<Longrightarrow> a dvd b) \<Longrightarrow> Lcm A dvd b" for A and a b
      by auto
    show "a \<in> A \<Longrightarrow> Gcd A dvd a" for A and a
      by (auto simp add: local.Gcd_def intro: Lcm_least)
    show "(\<And>a. a \<in> A \<Longrightarrow> b dvd a) \<Longrightarrow> b dvd Gcd A" for A and b
      by (auto simp add: local.Gcd_def intro: dvd_Lcm)
    show [simp]: "normalize (Lcm A) = Lcm A" for A
      by (simp add: local.Lcm_def)
    show "normalize (Gcd A) = Gcd A" for A
      by (simp add: local.Gcd_def)
  qed
qed

interpretation semiring_Gcd one zero times gcd lcm Gcd Lcm
    divide plus minus unit_factor normalize
  by (fact semiring_Gcd)

subclass factorial_semiring
proof -
  show "class.factorial_semiring divide plus minus zero times one
     unit_factor normalize"
  proof (standard, rule factorial_semiring_altI_aux) \<comment> \<open>FIXME rule\<close>
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
        have normalized_factors_product:
          "{p. p dvd a * b \<and> normalize p = p} \<subseteq>
             (\<lambda>(x,y). normalize (x * y)) ` ({p. p dvd a \<and> normalize p = p} \<times> {p. p dvd b \<and> normalize p = p})"
          for a b
        proof safe
          fix p assume p: "p dvd a * b" "normalize p = p"
          from p(1) obtain x y where xy: "p = x * y" "x dvd a" "y dvd b"
            by (rule dvd_productE)
          define x' y' where "x' = normalize x" and "y' = normalize y"
          have "p = normalize (x' * y')"
            using p by (simp add: xy x'_def y'_def)
          moreover have "x' dvd a \<and> normalize x' = x'" and "y' dvd b \<and> normalize y' = y'"
            using xy by (auto simp: x'_def y'_def)
          ultimately show "p \<in> (\<lambda>(x, y). normalize (x * y)) `
              ({p. p dvd a \<and> normalize p = p} \<times> {p. p dvd b \<and> normalize p = p})" by fast
        qed
        from x y have "\<not>is_unit z" by (auto simp: mult_unit_dvd_iff)
        have "?fctrs x \<subseteq> (\<lambda>(p,p'). normalize (p * p')) ` (?fctrs y \<times> ?fctrs z)"
          by (subst x) (rule normalized_factors_product)
        moreover have "\<not>y * z dvd y * 1" "\<not>y * z dvd 1 * z"
          by (subst dvd_times_left_cancel_iff dvd_times_right_cancel_iff; fact)+
        hence "finite ((\<lambda>(p,p'). normalize (p * p')) ` (?fctrs y \<times> ?fctrs z))"
          by (intro finite_imageI finite_cartesian_product less dvd_proper_imp_size_less)
             (auto simp: x)
        ultimately show ?thesis by (rule finite_subset)
      qed
    qed
  next
    fix p
    assume "irreducible p"
    then show "prime_elem p"
      by (rule irreducible_imp_prime_elem_gcd)
  qed
qed

lemma Gcd_eucl_set [code]:
  "Gcd (set xs) = fold gcd xs 0"
  by (fact Gcd_set_eq_fold)

lemma Lcm_eucl_set [code]:
  "Lcm (set xs) = fold lcm xs 1"
  by (fact Lcm_set_eq_fold)
 
end

hide_const (open) gcd lcm Gcd Lcm

lemma prime_elem_int_abs_iff [simp]:
  fixes p :: int
  shows "prime_elem \<bar>p\<bar> \<longleftrightarrow> prime_elem p"
  using prime_elem_normalize_iff [of p] by simp
  
lemma prime_elem_int_minus_iff [simp]:
  fixes p :: int
  shows "prime_elem (- p) \<longleftrightarrow> prime_elem p"
  using prime_elem_normalize_iff [of "- p"] by simp

lemma prime_int_iff:
  fixes p :: int
  shows "prime p \<longleftrightarrow> p > 0 \<and> prime_elem p"
  by (auto simp add: prime_def dest: prime_elem_not_zeroI)
  
  
subsection \<open>The (simple) euclidean algorithm as gcd computation\<close>
  
class euclidean_semiring_gcd = normalization_euclidean_semiring + gcd + Gcd +
  assumes gcd_eucl: "Euclidean_Algorithm.gcd = GCD.gcd"
    and lcm_eucl: "Euclidean_Algorithm.lcm = GCD.lcm"
  assumes Gcd_eucl: "Euclidean_Algorithm.Gcd = GCD.Gcd"
    and Lcm_eucl: "Euclidean_Algorithm.Lcm = GCD.Lcm"
begin

subclass semiring_gcd
  unfolding gcd_eucl [symmetric] lcm_eucl [symmetric]
  by (fact semiring_gcd)

subclass semiring_Gcd
  unfolding  gcd_eucl [symmetric] lcm_eucl [symmetric]
    Gcd_eucl [symmetric] Lcm_eucl [symmetric]
  by (fact semiring_Gcd)

subclass factorial_semiring_gcd
proof
  show "gcd a b = gcd_factorial a b" for a b
    apply (rule sym)
    apply (rule gcdI)
       apply (fact gcd_lcm_factorial)+
    done
  then show "lcm a b = lcm_factorial a b" for a b
    by (simp add: lcm_factorial_gcd_factorial lcm_gcd)
  show "Gcd A = Gcd_factorial A" for A
    apply (rule sym)
    apply (rule GcdI)
       apply (fact gcd_lcm_factorial)+
    done
  show "Lcm A = Lcm_factorial A" for A
    apply (rule sym)
    apply (rule LcmI)
       apply (fact gcd_lcm_factorial)+
    done
qed

lemma gcd_mod_right [simp]:
  "a \<noteq> 0 \<Longrightarrow> gcd a (b mod a) = gcd a b"
  unfolding gcd.commute [of a b]
  by (simp add: gcd_eucl [symmetric] local.gcd_mod)

lemma gcd_mod_left [simp]:
  "b \<noteq> 0 \<Longrightarrow> gcd (a mod b) b = gcd a b"
  by (drule gcd_mod_right [of _ a]) (simp add: gcd.commute)

lemma euclidean_size_gcd_le1 [simp]:
  assumes "a \<noteq> 0"
  shows "euclidean_size (gcd a b) \<le> euclidean_size a"
proof -
  from gcd_dvd1 obtain c where A: "a = gcd a b * c" ..
  with assms have "c \<noteq> 0"
    by auto
  moreover from this
  have "euclidean_size (gcd a b) \<le> euclidean_size (gcd a b * c)"
    by (rule size_mult_mono)
  with A show ?thesis
    by simp
qed

lemma euclidean_size_gcd_le2 [simp]:
  "b \<noteq> 0 \<Longrightarrow> euclidean_size (gcd a b) \<le> euclidean_size b"
  by (subst gcd.commute, rule euclidean_size_gcd_le1)

lemma euclidean_size_gcd_less1:
  assumes "a \<noteq> 0" and "\<not> a dvd b"
  shows "euclidean_size (gcd a b) < euclidean_size a"
proof (rule ccontr)
  assume "\<not>euclidean_size (gcd a b) < euclidean_size a"
  with \<open>a \<noteq> 0\<close> have A: "euclidean_size (gcd a b) = euclidean_size a"
    by (intro le_antisym, simp_all)
  have "a dvd gcd a b"
    by (rule dvd_euclidean_size_eq_imp_dvd) (simp_all add: assms A)
  hence "a dvd b" using dvd_gcdD2 by blast
  with \<open>\<not> a dvd b\<close> show False by contradiction
qed

lemma euclidean_size_gcd_less2:
  assumes "b \<noteq> 0" and "\<not> b dvd a"
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
  assumes "b \<noteq> 0" and "\<not> b dvd a"
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
  assumes "a \<noteq> 0" and "\<not> a dvd b"
  shows "euclidean_size b < euclidean_size (lcm a b)"
  using assms euclidean_size_lcm_less1 [of a b] by (simp add: ac_simps)

end

lemma factorial_euclidean_semiring_gcdI:
  "OFCLASS('a::{factorial_semiring_gcd, normalization_euclidean_semiring}, euclidean_semiring_gcd_class)"
proof
  interpret semiring_Gcd 1 0 times
    Euclidean_Algorithm.gcd Euclidean_Algorithm.lcm
    Euclidean_Algorithm.Gcd Euclidean_Algorithm.Lcm
    divide plus minus unit_factor normalize
    rewrites "dvd.dvd (*) = Rings.dvd"
    by (fact semiring_Gcd) (simp add: dvd.dvd_def dvd_def fun_eq_iff)
  show [simp]: "Euclidean_Algorithm.gcd = (gcd :: 'a \<Rightarrow> _)"
  proof (rule ext)+
    fix a b :: 'a
    show "Euclidean_Algorithm.gcd a b = gcd a b"
    proof (induct a b rule: eucl_induct)
      case zero
      then show ?case
        by simp
    next
      case (mod a b)
      moreover have "gcd b (a mod b) = gcd b a"
        using GCD.gcd_add_mult [of b "a div b" "a mod b", symmetric]
          by (simp add: div_mult_mod_eq)
      ultimately show ?case
        by (simp add: Euclidean_Algorithm.gcd_mod ac_simps)
    qed
  qed
  show [simp]: "Euclidean_Algorithm.Lcm = (Lcm :: 'a set \<Rightarrow> _)"
    by (auto intro!: Lcm_eqI GCD.dvd_Lcm GCD.Lcm_least)
  show "Euclidean_Algorithm.lcm = (lcm :: 'a \<Rightarrow> _)"
    by (simp add: fun_eq_iff Euclidean_Algorithm.lcm_def semiring_gcd_class.lcm_gcd)
  show "Euclidean_Algorithm.Gcd = (Gcd :: 'a set \<Rightarrow> _)"
    by (simp add: fun_eq_iff Euclidean_Algorithm.Gcd_def semiring_Gcd_class.Gcd_Lcm)
qed


subsection \<open>The extended euclidean algorithm\<close>
  
class euclidean_ring_gcd = euclidean_semiring_gcd + idom
begin

subclass euclidean_ring ..
subclass ring_gcd ..
subclass factorial_ring_gcd ..

function euclid_ext_aux :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) \<times> 'a"
  where "euclid_ext_aux s' s t' t r' r = (
     if r = 0 then let c = 1 div unit_factor r' in ((s' * c, t' * c), normalize r')
     else let q = r' div r
          in euclid_ext_aux s (s' - q * s) t (t' - q * t) r (r' mod r))"
  by auto
termination
  by (relation "measure (\<lambda>(_, _, _, _, _, b). euclidean_size b)")
    (simp_all add: mod_size_less)

abbreviation (input) euclid_ext :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) \<times> 'a"
  where "euclid_ext \<equiv> euclid_ext_aux 1 0 0 1"
    
lemma
  assumes "gcd r' r = gcd a b"
  assumes "s' * a + t' * b = r'"
  assumes "s * a + t * b = r"
  assumes "euclid_ext_aux s' s t' t r' r = ((x, y), c)"
  shows euclid_ext_aux_eq_gcd: "c = gcd a b"
    and euclid_ext_aux_bezout: "x * a + y * b = gcd a b"
proof -
  have "case euclid_ext_aux s' s t' t r' r of ((x, y), c) \<Rightarrow> 
    x * a + y * b = c \<and> c = gcd a b" (is "?P (euclid_ext_aux s' s t' t r' r)")
    using assms(1-3)
  proof (induction s' s t' t r' r rule: euclid_ext_aux.induct)
    case (1 s' s t' t r' r)
    show ?case
    proof (cases "r = 0")
      case True
      hence "euclid_ext_aux s' s t' t r' r = 
               ((s' div unit_factor r', t' div unit_factor r'), normalize r')"
        by (subst euclid_ext_aux.simps) (simp add: Let_def)
      also have "?P \<dots>"
      proof safe
        have "s' div unit_factor r' * a + t' div unit_factor r' * b = 
                (s' * a + t' * b) div unit_factor r'"
          by (cases "r' = 0") (simp_all add: unit_div_commute)
        also have "s' * a + t' * b = r'" by fact
        also have "\<dots> div unit_factor r' = normalize r'" by simp
        finally show "s' div unit_factor r' * a + t' div unit_factor r' * b = normalize r'" .
      next
        from "1.prems" True show "normalize r' = gcd a b"
          by simp
      qed
      finally show ?thesis .
    next
      case False
      hence "euclid_ext_aux s' s t' t r' r = 
             euclid_ext_aux s (s' - r' div r * s) t (t' - r' div r * t) r (r' mod r)"
        by (subst euclid_ext_aux.simps) (simp add: Let_def)
      also from "1.prems" False have "?P \<dots>"
      proof (intro "1.IH")
        have "(s' - r' div r * s) * a + (t' - r' div r * t) * b =
              (s' * a + t' * b) - r' div r * (s * a + t * b)" by (simp add: algebra_simps)
        also have "s' * a + t' * b = r'" by fact
        also have "s * a + t * b = r" by fact
        also have "r' - r' div r * r = r' mod r" using div_mult_mod_eq [of r' r]
          by (simp add: algebra_simps)
        finally show "(s' - r' div r * s) * a + (t' - r' div r * t) * b = r' mod r" .
      qed (auto simp: algebra_simps minus_mod_eq_div_mult [symmetric] gcd.commute)
      finally show ?thesis .
    qed
  qed
  with assms(4) show "c = gcd a b" "x * a + y * b = gcd a b"
    by simp_all
qed

declare euclid_ext_aux.simps [simp del]

definition bezout_coefficients :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a"
  where [code]: "bezout_coefficients a b = fst (euclid_ext a b)"

lemma bezout_coefficients_0: 
  "bezout_coefficients a 0 = (1 div unit_factor a, 0)"
  by (simp add: bezout_coefficients_def euclid_ext_aux.simps)

lemma bezout_coefficients_left_0: 
  "bezout_coefficients 0 a = (0, 1 div unit_factor a)"
  by (simp add: bezout_coefficients_def euclid_ext_aux.simps)

lemma bezout_coefficients:
  assumes "bezout_coefficients a b = (x, y)"
  shows "x * a + y * b = gcd a b"
  using assms by (simp add: bezout_coefficients_def
    euclid_ext_aux_bezout [of a b a b 1 0 0 1 x y] prod_eq_iff)

lemma bezout_coefficients_fst_snd:
  "fst (bezout_coefficients a b) * a + snd (bezout_coefficients a b) * b = gcd a b"
  by (rule bezout_coefficients) simp

lemma euclid_ext_eq [simp]:
  "euclid_ext a b = (bezout_coefficients a b, gcd a b)" (is "?p = ?q")
proof
  show "fst ?p = fst ?q"
    by (simp add: bezout_coefficients_def)
  have "snd (euclid_ext_aux 1 0 0 1 a b) = gcd a b"
    by (rule euclid_ext_aux_eq_gcd [of a b a b 1 0 0 1])
      (simp_all add: prod_eq_iff)
  then show "snd ?p = snd ?q"
    by simp
qed

declare euclid_ext_eq [symmetric, code_unfold]

end

class normalization_euclidean_semiring_multiplicative =
  normalization_euclidean_semiring + normalization_semidom_multiplicative
begin

subclass factorial_semiring_multiplicative ..

end

class field_gcd =
  field + unique_euclidean_ring + euclidean_ring_gcd + normalization_semidom_multiplicative
begin

subclass normalization_euclidean_semiring_multiplicative ..

subclass normalization_euclidean_semiring ..

subclass semiring_gcd_mult_normalize ..

end


subsection \<open>Typical instances\<close>

instance nat :: normalization_euclidean_semiring ..

instance nat :: euclidean_semiring_gcd
proof
  interpret semiring_Gcd 1 0 times
    "Euclidean_Algorithm.gcd" "Euclidean_Algorithm.lcm"
    "Euclidean_Algorithm.Gcd" "Euclidean_Algorithm.Lcm"
    divide plus minus unit_factor normalize
    rewrites "dvd.dvd (*) = Rings.dvd"
    by (fact semiring_Gcd) (simp add: dvd.dvd_def dvd_def fun_eq_iff)
  show [simp]: "(Euclidean_Algorithm.gcd :: nat \<Rightarrow> _) = gcd"
  proof (rule ext)+
    fix m n :: nat
    show "Euclidean_Algorithm.gcd m n = gcd m n"
    proof (induct m n rule: eucl_induct)
      case zero
      then show ?case
        by simp
    next
      case (mod m n)
      then have "gcd n (m mod n) = gcd n m"
        using gcd_nat.simps [of m n] by (simp add: ac_simps)
      with mod show ?case
        by (simp add: Euclidean_Algorithm.gcd_mod ac_simps)
    qed
  qed
  show [simp]: "(Euclidean_Algorithm.Lcm :: nat set \<Rightarrow> _) = Lcm"
    by (auto intro!: ext Lcm_eqI)
  show "(Euclidean_Algorithm.lcm :: nat \<Rightarrow> _) = lcm"
    by (simp add: fun_eq_iff Euclidean_Algorithm.lcm_def semiring_gcd_class.lcm_gcd)
  show "(Euclidean_Algorithm.Gcd :: nat set \<Rightarrow> _) = Gcd"
    by (simp add: fun_eq_iff Euclidean_Algorithm.Gcd_def semiring_Gcd_class.Gcd_Lcm)
qed

instance nat :: normalization_euclidean_semiring_multiplicative ..

lemma prime_factorization_Suc_0 [simp]: "prime_factorization (Suc 0) = {#}"
  unfolding One_nat_def [symmetric] using prime_factorization_1 .

instance int :: normalization_euclidean_semiring ..

instance int :: euclidean_ring_gcd
proof
  interpret semiring_Gcd 1 0 times
    "Euclidean_Algorithm.gcd" "Euclidean_Algorithm.lcm"
    "Euclidean_Algorithm.Gcd" "Euclidean_Algorithm.Lcm"
    divide plus minus unit_factor normalize
    rewrites "dvd.dvd (*) = Rings.dvd"
    by (fact semiring_Gcd) (simp add: dvd.dvd_def dvd_def fun_eq_iff)
  show [simp]: "(Euclidean_Algorithm.gcd :: int \<Rightarrow> _) = gcd"
  proof (rule ext)+
    fix k l :: int
    show "Euclidean_Algorithm.gcd k l = gcd k l"
    proof (induct k l rule: eucl_induct)
      case zero
      then show ?case
        by simp
    next
      case (mod k l)
      have "gcd l (k mod l) = gcd l k"
      proof (cases l "0::int" rule: linorder_cases)
        case less
        then show ?thesis
          using gcd_non_0_int [of "- l" "- k"] by (simp add: ac_simps)
      next
        case equal
        with mod show ?thesis
          by simp
      next
        case greater
        then show ?thesis
          using gcd_non_0_int [of l k] by (simp add: ac_simps)
      qed
      with mod show ?case
        by (simp add: Euclidean_Algorithm.gcd_mod ac_simps)
    qed
  qed
  show [simp]: "(Euclidean_Algorithm.Lcm :: int set \<Rightarrow> _) = Lcm"
    by (auto intro!: ext Lcm_eqI)
  show "(Euclidean_Algorithm.lcm :: int \<Rightarrow> _) = lcm"
    by (simp add: fun_eq_iff Euclidean_Algorithm.lcm_def semiring_gcd_class.lcm_gcd)
  show "(Euclidean_Algorithm.Gcd :: int set \<Rightarrow> _) = Gcd"
    by (simp add: fun_eq_iff Euclidean_Algorithm.Gcd_def semiring_Gcd_class.Gcd_Lcm)
qed

instance int :: normalization_euclidean_semiring_multiplicative ..

lemma (in idom) prime_CHAR_semidom:
  assumes "CHAR('a) > 0"
  shows   "prime CHAR('a)"
proof -
  have False if ab: "a \<noteq> 1" "b \<noteq> 1" "CHAR('a) = a * b" for a b
  proof -
    from assms ab have "a > 0" "b > 0"
      by (auto intro!: Nat.gr0I)    
    have "of_nat (a * b) = (0 :: 'a)"
      using ab by (metis of_nat_CHAR)
    also have "of_nat (a * b) = (of_nat a :: 'a) * of_nat b"
      by simp
    finally have "of_nat a * of_nat b = (0 :: 'a)" .
    moreover have "of_nat a * of_nat b \<noteq> (0 :: 'a)"
      using ab \<open>a > 0\<close> \<open>b > 0\<close>
      by (intro no_zero_divisors) (auto simp: of_nat_eq_0_iff_char_dvd)
    ultimately show False
      by contradiction
  qed
  moreover have "CHAR('a) > 1"
    using assms CHAR_not_1' by linarith
  ultimately have "prime_elem CHAR('a)"
    by (intro irreducible_imp_prime_elem) (auto simp: Factorial_Ring.irreducible_def)
  thus ?thesis
    by (auto simp: prime_def)
qed

end
