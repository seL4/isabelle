(* Author: Manuel Eberl *)

section \<open>Abstract euclidean algorithm\<close>

theory Euclidean_Algorithm
imports "~~/src/HOL/GCD" "~~/src/HOL/Library/Polynomial"
begin

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
class euclidean_semiring = semiring_div + normalization_semidom + 
  fixes euclidean_size :: "'a \<Rightarrow> nat"
  assumes size_0 [simp]: "euclidean_size 0 = 0"
  assumes mod_size_less: 
    "b \<noteq> 0 \<Longrightarrow> euclidean_size (a mod b) < euclidean_size b"
  assumes size_mult_mono:
    "b \<noteq> 0 \<Longrightarrow> euclidean_size a \<le> euclidean_size (a * b)"
begin

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

lemma dvd_euclidean_size_eq_imp_dvd:
  assumes "a \<noteq> 0" and b_dvd_a: "b dvd a" and size_eq: "euclidean_size a = euclidean_size b"
  shows "a dvd b"
proof (rule ccontr)
  assume "\<not> a dvd b"
  then have "b mod a \<noteq> 0" by (simp add: mod_eq_0_iff_dvd)
  from b_dvd_a have b_dvd_mod: "b dvd b mod a" by (simp add: dvd_mod_iff)
  from b_dvd_mod obtain c where "b mod a = b * c" unfolding dvd_def by blast
    with \<open>b mod a \<noteq> 0\<close> have "c \<noteq> 0" by auto
  with \<open>b mod a = b * c\<close> have "euclidean_size (b mod a) \<ge> euclidean_size b"
      using size_mult_mono by force
  moreover from \<open>\<not> a dvd b\<close> and \<open>a \<noteq> 0\<close>
  have "euclidean_size (b mod a) < euclidean_size a"
      using mod_size_less by blast
  ultimately show False using size_eq by simp
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

end

class euclidean_ring = euclidean_semiring + idom
begin

subclass ring_div ..

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
      also have "r' - r' div r * r = r' mod r" using mod_div_equality[of r' r]
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

instance proof
qed simp_all

end


instantiation int :: euclidean_ring
begin

definition [simp]:
  "euclidean_size_int = (nat \<circ> abs :: int \<Rightarrow> nat)"

instance
by standard (auto simp add: abs_mult nat_mult_distrib split: abs_split)

end


instantiation poly :: (field) euclidean_ring
begin

definition euclidean_size_poly :: "'a poly \<Rightarrow> nat"
  where "euclidean_size p = (if p = 0 then 0 else 2 ^ degree p)"

lemma euclidean_size_poly_0 [simp]:
  "euclidean_size (0::'a poly) = 0"
  by (simp add: euclidean_size_poly_def)

lemma euclidean_size_poly_not_0 [simp]:
  "p \<noteq> 0 \<Longrightarrow> euclidean_size p = 2 ^ degree p"
  by (simp add: euclidean_size_poly_def)

instance
proof
  fix p q :: "'a poly"
  assume "q \<noteq> 0"
  then have "p mod q = 0 \<or> degree (p mod q) < degree q"
    by (rule degree_mod_less [of q p])  
  with \<open>q \<noteq> 0\<close> show "euclidean_size (p mod q) < euclidean_size q"
    by (cases "p mod q = 0") simp_all
next
  fix p q :: "'a poly"
  assume "q \<noteq> 0"
  from \<open>q \<noteq> 0\<close> have "degree p \<le> degree (p * q)"
    by (rule degree_mult_right_le)
  with \<open>q \<noteq> 0\<close> show "euclidean_size p \<le> euclidean_size (p * q)"
    by (cases "p = 0") simp_all
qed simp

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


instantiation poly :: (field) euclidean_ring_gcd
begin

definition gcd_poly :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "gcd_poly = gcd_eucl"
  
definition lcm_poly :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "lcm_poly = lcm_eucl"
  
definition Gcd_poly :: "'a poly set \<Rightarrow> 'a poly" where
  "Gcd_poly = Gcd_eucl"
  
definition Lcm_poly :: "'a poly set \<Rightarrow> 'a poly" where
  "Lcm_poly = Lcm_eucl"

instance by standard (simp_all only: gcd_poly_def lcm_poly_def Gcd_poly_def Lcm_poly_def)
end

lemma poly_gcd_monic:
  "lead_coeff (gcd x y) = (if x = 0 \<and> y = 0 then 0 else 1)"
  using unit_factor_gcd[of x y]
  by (simp add: unit_factor_poly_def monom_0 one_poly_def lead_coeff_def split: if_split_asm)

lemma poly_dvd_antisym:
  fixes p q :: "'a::idom poly"
  assumes coeff: "coeff p (degree p) = coeff q (degree q)"
  assumes dvd1: "p dvd q" and dvd2: "q dvd p" shows "p = q"
proof (cases "p = 0")
  case True with coeff show "p = q" by simp
next
  case False with coeff have "q \<noteq> 0" by auto
  have degree: "degree p = degree q"
    using \<open>p dvd q\<close> \<open>q dvd p\<close> \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close>
    by (intro order_antisym dvd_imp_degree_le)

  from \<open>p dvd q\<close> obtain a where a: "q = p * a" ..
  with \<open>q \<noteq> 0\<close> have "a \<noteq> 0" by auto
  with degree a \<open>p \<noteq> 0\<close> have "degree a = 0"
    by (simp add: degree_mult_eq)
  with coeff a show "p = q"
    by (cases a, auto split: if_splits)
qed

lemma poly_gcd_unique:
  fixes d x y :: "_ poly"
  assumes dvd1: "d dvd x" and dvd2: "d dvd y"
    and greatest: "\<And>k. k dvd x \<Longrightarrow> k dvd y \<Longrightarrow> k dvd d"
    and monic: "coeff d (degree d) = (if x = 0 \<and> y = 0 then 0 else 1)"
  shows "d = gcd x y"
  using assms by (intro gcdI) (auto simp: normalize_poly_def split: if_split_asm)

lemma poly_gcd_code [code]:
  "gcd x y = (if y = 0 then normalize x else gcd y (x mod (y :: _ poly)))"
  by (simp add: gcd_0 gcd_non_0)

end
