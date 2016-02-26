(* Author: Manuel Eberl *)

section \<open>Abstract euclidean algorithm\<close>

theory Euclidean_Algorithm
imports Main "~~/src/HOL/GCD" "~~/src/HOL/Library/Polynomial"
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

definition Lcm_eucl :: "'a set \<Rightarrow> 'a" -- \<open>
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
    def n \<equiv> "LEAST n. \<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n"
    def l \<equiv> "SOME l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n"
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

function euclid_ext :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a" where
  "euclid_ext a b = 
     (if b = 0 then 
        (1 div unit_factor a, 0, normalize a)
      else
        case euclid_ext b (a mod b) of
            (s, t, c) \<Rightarrow> (t, s - t * (a div b), c))"
  by pat_completeness simp
termination
  by (relation "measure (euclidean_size \<circ> snd)") (simp_all add: mod_size_less)

declare euclid_ext.simps [simp del]

lemma euclid_ext_0: 
  "euclid_ext a 0 = (1 div unit_factor a, 0, normalize a)"
  by (simp add: euclid_ext.simps [of a 0])

lemma euclid_ext_left_0: 
  "euclid_ext 0 a = (0, 1 div unit_factor a, normalize a)"
  by (simp add: euclid_ext_0 euclid_ext.simps [of 0 a])

lemma euclid_ext_non_0: 
  "b \<noteq> 0 \<Longrightarrow> euclid_ext a b = (case euclid_ext b (a mod b) of
    (s, t, c) \<Rightarrow> (t, s - t * (a div b), c))"
  by (simp add: euclid_ext.simps [of a b] euclid_ext.simps [of b 0])

lemma euclid_ext_code [code]:
  "euclid_ext a b = (if b = 0 then (1 div unit_factor a, 0, normalize a)
    else let (s, t, c) = euclid_ext b (a mod b) in  (t, s - t * (a div b), c))"
  by (simp add: euclid_ext.simps [of a b] euclid_ext.simps [of b 0])

lemma euclid_ext_correct:
  "case euclid_ext a b of (s, t, c) \<Rightarrow> s * a + t * b = c"
proof (induct a b rule: gcd_eucl_induct)
  case (zero a) then show ?case
    by (simp add: euclid_ext_0 ac_simps)
next
  case (mod a b)
  obtain s t c where stc: "euclid_ext b (a mod b) = (s,t,c)"
    by (cases "euclid_ext b (a mod b)") blast
  with mod have "c = s * b + t * (a mod b)" by simp
  also have "... = t * ((a div b) * b + a mod b) + (s - t * (a div b)) * b"
    by (simp add: algebra_simps) 
  also have "(a div b) * b + a mod b = a" using mod_div_equality .
  finally show ?case
    by (subst euclid_ext.simps) (simp add: stc mod ac_simps)
qed

definition euclid_ext' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a"
where
  "euclid_ext' a b = (case euclid_ext a b of (s, t, _) \<Rightarrow> (s, t))"

lemma euclid_ext'_0: "euclid_ext' a 0 = (1 div unit_factor a, 0)" 
  by (simp add: euclid_ext'_def euclid_ext_0)

lemma euclid_ext'_left_0: "euclid_ext' 0 a = (0, 1 div unit_factor a)" 
  by (simp add: euclid_ext'_def euclid_ext_left_0)
  
lemma euclid_ext'_non_0: "b \<noteq> 0 \<Longrightarrow> euclid_ext' a b = (snd (euclid_ext' b (a mod b)),
  fst (euclid_ext' b (a mod b)) - snd (euclid_ext' b (a mod b)) * (a div b))"
  by (simp add: euclid_ext'_def euclid_ext_non_0 split_def)

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

lemma gcd_proj2_if_dvd: 
  "b dvd a \<Longrightarrow> gcd a b = normalize b"
  by (cases "b = 0", simp_all add: dvd_eq_mod_eq_0 gcd_non_0)

lemma gcd_proj1_if_dvd: 
  "a dvd b \<Longrightarrow> gcd a b = normalize a"
  by (subst gcd.commute, simp add: gcd_proj2_if_dvd)

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

lemma gcd_mod1 [simp]:
  "gcd (a mod b) b = gcd a b"
  by (rule gcdI, metis dvd_mod_iff gcd_dvd1 gcd_dvd2, simp_all add: gcd_greatest dvd_mod_iff)

lemma gcd_mod2 [simp]:
  "gcd a (b mod a) = gcd a b"
  by (rule gcdI, simp, metis dvd_mod_iff gcd_dvd1 gcd_dvd2, simp_all add: gcd_greatest dvd_mod_iff)
         
lemma gcd_mult_distrib': 
  "normalize c * gcd a b = gcd (c * a) (c * b)"
proof (cases "c = 0")
  case True then show ?thesis by simp_all
next
  case False then have [simp]: "is_unit (unit_factor c)" by simp
  show ?thesis
  proof (induct a b rule: gcd_eucl_induct)
    case (zero a) show ?case
    proof (cases "a = 0")
      case True then show ?thesis by simp
    next
      case False
      then show ?thesis by (simp add: normalize_mult)
    qed
    case (mod a b)
    then show ?case by (simp add: mult_mod_right gcd.commute)
  qed
qed

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

lemma gcd_idem: "gcd a a = normalize a"
  by (cases "a = 0") (simp, rule sym, rule gcdI, simp_all)

lemma gcd_right_idem: "gcd (gcd a b) b = gcd a b"
  apply (rule gcdI)
  apply (simp add: ac_simps)
  apply (rule gcd_dvd2)
  apply (rule gcd_greatest, erule (1) gcd_greatest, assumption)
  apply simp
  done

lemma gcd_left_idem: "gcd a (gcd a b) = gcd a b"
  apply (rule gcdI)
  apply simp
  apply (rule dvd_trans, rule gcd_dvd2, rule gcd_dvd2)
  apply (rule gcd_greatest, assumption, erule gcd_greatest, assumption)
  apply simp
  done

lemma comp_fun_idem_gcd: "comp_fun_idem gcd"
proof
  fix a b show "gcd a \<circ> gcd b = gcd b \<circ> gcd a"
    by (simp add: fun_eq_iff ac_simps)
next
  fix a show "gcd a \<circ> gcd a = gcd a"
    by (simp add: fun_eq_iff gcd_left_idem)
qed

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

lemma coprime_crossproduct:
  assumes [simp]: "gcd a d = 1" "gcd b c = 1"
  shows "normalize (a * c) = normalize (b * d) \<longleftrightarrow> normalize a  = normalize b \<and> normalize c = normalize d"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then have "a dvd b" "b dvd a" "c dvd d" "d dvd c" by (simp_all add: associated_iff_dvd)
  then have "a * c dvd b * d" "b * d dvd a * c" by (fast intro: mult_dvd_mono)+
  then show ?lhs by (simp add: associated_iff_dvd)
next
  assume ?lhs
  then have dvd: "a * c dvd b * d" "b * d dvd a * c" by (simp_all add: associated_iff_dvd)
  then have "a dvd b * d" by (metis dvd_mult_left) 
  hence "a dvd b" by (simp add: coprime_dvd_mult_iff)
  moreover from dvd have "b dvd a * c" by (metis dvd_mult_left) 
  hence "b dvd a" by (simp add: coprime_dvd_mult_iff)
  moreover from dvd have "c dvd d * b" 
    by (auto dest: dvd_mult_right simp add: ac_simps)
  hence "c dvd d" by (simp add: coprime_dvd_mult_iff gcd.commute)
  moreover from dvd have "d dvd c * a"
    by (auto dest: dvd_mult_right simp add: ac_simps)
  hence "d dvd c" by (simp add: coprime_dvd_mult_iff gcd.commute)
  ultimately show ?rhs by (simp add: associated_iff_dvd)
qed

lemma gcd_add1 [simp]:
  "gcd (m + n) n = gcd m n"
  by (cases "n = 0", simp_all add: gcd_non_0)

lemma gcd_add2 [simp]:
  "gcd m (m + n) = gcd m n"
  using gcd_add1 [of n m] by (simp add: ac_simps)

lemma gcd_add_mult:
  "gcd m (k * m + n) = gcd m n"
proof -
  have "gcd m ((k * m + n) mod m) = gcd m (k * m + n)"
    by (fact gcd_mod2)
  then show ?thesis by simp 
qed

lemma coprimeI: "(\<And>l. \<lbrakk>l dvd a; l dvd b\<rbrakk> \<Longrightarrow> l dvd 1) \<Longrightarrow> gcd a b = 1"
  by (rule sym, rule gcdI, simp_all)

lemma coprime: "gcd a b = 1 \<longleftrightarrow> (\<forall>d. d dvd a \<and> d dvd b \<longleftrightarrow> is_unit d)"
  by (auto intro: coprimeI gcd_greatest dvd_gcdD1 dvd_gcdD2)

lemma div_gcd_coprime:
  assumes nz: "a \<noteq> 0 \<or> b \<noteq> 0"
  defines [simp]: "d \<equiv> gcd a b"
  defines [simp]: "a' \<equiv> a div d" and [simp]: "b' \<equiv> b div d"
  shows "gcd a' b' = 1"
proof (rule coprimeI)
  fix l assume "l dvd a'" "l dvd b'"
  then obtain s t where "a' = l * s" "b' = l * t" unfolding dvd_def by blast
  moreover have "a = a' * d" "b = b' * d" by simp_all
  ultimately have "a = (l * d) * s" "b = (l * d) * t"
    by (simp_all only: ac_simps)
  hence "l*d dvd a" and "l*d dvd b" by (simp_all only: dvd_triv_left)
  hence "l*d dvd d" by (simp add: gcd_greatest)
  then obtain u where "d = l * d * u" ..
  then have "d * (l * u) = d" by (simp add: ac_simps)
  moreover from nz have "d \<noteq> 0" by simp
  with div_mult_self1_is_id have "d * (l * u) div d = l * u" . 
  ultimately have "1 = l * u"
    using \<open>d \<noteq> 0\<close> by simp
  then show "l dvd 1" ..
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

lemma coprime_mul_eq: "gcd d (a * b) = 1 \<longleftrightarrow> gcd d a = 1 \<and> gcd d b = 1"
  using coprime_rmult[of d a b] coprime_lmult[of d a b] coprime_mult[of d a b] by blast

lemma gcd_coprime:
  assumes c: "gcd a b \<noteq> 0" and a: "a = a' * gcd a b" and b: "b = b' * gcd a b"
  shows "gcd a' b' = 1"
proof -
  from c have "a \<noteq> 0 \<or> b \<noteq> 0" by simp
  with div_gcd_coprime have "gcd (a div gcd a b) (b div gcd a b) = 1" .
  also from assms have "a div gcd a b = a'" by (metis div_mult_self2_is_id)+
  also from assms have "b div gcd a b = b'" by (metis div_mult_self2_is_id)+
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

lemmas divs_mult = divides_mult

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

lemma invertible_coprime:
  assumes "a * b mod m = 1"
  shows "coprime a m"
proof -
  from assms have "coprime m (a * b mod m)"
    by simp
  then have "coprime m (a * b)"
    by simp
  then have "coprime m a"
    by (rule coprime_lmult)
  then show ?thesis
    by (simp add: ac_simps)
qed

lemma lcm_gcd_prod:
  "lcm a b * gcd a b = normalize (a * b)"
  by (simp add: lcm_gcd)

lemma lcm_zero:
  "lcm a b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
  by (fact lcm_eq_0_iff)

lemmas lcm_0_iff = lcm_zero

lemma gcd_lcm: 
  assumes "lcm a b \<noteq> 0"
  shows "gcd a b = normalize (a * b) div lcm a b"
proof -
  have "lcm a b * gcd a b = normalize (a * b)"
    by (fact lcm_gcd_prod)
  with assms show ?thesis
    by (metis nonzero_mult_divide_cancel_left)
qed

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
  by rule (auto intro: lcmI simp: lcm_least lcm_zero)

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

lemma euclidean_size_lcm_le1: 
  assumes "a \<noteq> 0" and "b \<noteq> 0"
  shows "euclidean_size a \<le> euclidean_size (lcm a b)"
proof -
  have "a dvd lcm a b" by (rule dvd_lcm1)
  then obtain c where A: "lcm a b = a * c" ..
  with \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close> have "c \<noteq> 0" by (auto simp: lcm_zero)
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
    by (rule_tac dvd_euclidean_size_eq_imp_dvd) (auto simp: lcm_zero)
  hence "b dvd a" by (rule lcm_dvdD2)
  with \<open>\<not>b dvd a\<close> show False by contradiction
qed

lemma euclidean_size_lcm_less2:
  assumes "a \<noteq> 0" and "\<not>a dvd b"
  shows "euclidean_size b < euclidean_size (lcm a b)"
  using assms euclidean_size_lcm_less1 [of a b] by (simp add: ac_simps)

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

lemma Lcm_no_units:
  "Lcm A = Lcm (A - {a. is_unit a})"
proof -
  have "(A - {a. is_unit a}) \<union> {a\<in>A. is_unit a} = A" by blast
  hence "Lcm A = lcm (Lcm (A - {a. is_unit a})) (Lcm {a\<in>A. is_unit a})"
    by (simp add: Lcm_Un [symmetric])
  also have "Lcm {a\<in>A. is_unit a} = 1" by (simp add: Lcm_1_iff)
  finally show ?thesis by simp
qed

lemma Lcm_0_iff':
  "Lcm A = 0 \<longleftrightarrow> \<not>(\<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l))"
proof
  assume "Lcm A = 0"
  show "\<not>(\<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l))"
  proof
    assume ex: "\<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l)"
    then obtain l\<^sub>0 where l\<^sub>0_props: "l\<^sub>0 \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l\<^sub>0)" by blast
    def n \<equiv> "LEAST n. \<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n"
    def l \<equiv> "SOME l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n"
    have "\<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n"
      apply (subst n_def)
      apply (rule LeastI[of _ "euclidean_size l\<^sub>0"])
      apply (rule exI[of _ l\<^sub>0])
      apply (simp add: l\<^sub>0_props)
      done
    from someI_ex[OF this] have "l \<noteq> 0" unfolding l_def by simp_all
    hence "normalize l \<noteq> 0" by simp
    also from ex have "normalize l = Lcm A"
       by (simp only: Lcm_Lcm_eucl Lcm_eucl_def n_def l_def if_True Let_def)
    finally show False using \<open>Lcm A = 0\<close> by contradiction
  qed
qed (simp only: Lcm_Lcm_eucl Lcm_eucl_def if_False)

lemma Lcm_no_multiple:
  "(\<forall>m. m \<noteq> 0 \<longrightarrow> (\<exists>a\<in>A. \<not>a dvd m)) \<Longrightarrow> Lcm A = 0"
proof -
  assume "\<forall>m. m \<noteq> 0 \<longrightarrow> (\<exists>a\<in>A. \<not>a dvd m)"
  hence "\<not>(\<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l))" by blast
  then show "Lcm A = 0" by (simp only: Lcm_Lcm_eucl Lcm_eucl_def if_False)
qed

lemma Lcm_finite:
  assumes "finite A"
  shows "Lcm A = Finite_Set.fold lcm 1 A"
  by (induct rule: finite.induct[OF \<open>finite A\<close>])
    (simp_all add: comp_fun_idem.fold_insert_idem[OF comp_fun_idem_lcm])

lemma Lcm_set:
  "Lcm (set xs) = foldl lcm 1 xs"
  using comp_fun_idem.fold_set_fold[OF comp_fun_idem_lcm] Lcm_finite
  by (simp add: foldl_conv_fold lcm.commute)

lemma Lcm_eucl_set [code]:
  "Lcm_eucl (set xs) = foldl lcm_eucl 1 xs"
  by (simp add: Lcm_Lcm_eucl [symmetric] lcm_lcm_eucl Lcm_set)

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

lemma unit_factor_Gcd [simp]: "unit_factor (Gcd A) = (if Gcd A = 0 then 0 else 1)"
proof -
  show "unit_factor (Gcd A) = (if Gcd A = 0 then 0 else 1)"
    by (simp add: Gcd_Lcm unit_factor_Lcm)
qed

lemma GcdI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> b dvd a" and "\<And>c. (\<And>a. a \<in> A \<Longrightarrow> c dvd a) \<Longrightarrow> c dvd b"
    and "normalize b = b"
  shows "b = Gcd A"
  by (rule associated_eqI) (auto simp: assms Gcd_dvd intro: Gcd_greatest)

lemma Gcd_1:
  "1 \<in> A \<Longrightarrow> Gcd A = 1"
  by (auto intro!: Gcd_eq_1_I)

lemma Gcd_finite:
  assumes "finite A"
  shows "Gcd A = Finite_Set.fold gcd 0 A"
  by (induct rule: finite.induct[OF \<open>finite A\<close>])
    (simp_all add: comp_fun_idem.fold_insert_idem[OF comp_fun_idem_gcd])

lemma Gcd_set:
  "Gcd (set xs) = foldl gcd 0 xs"
  using comp_fun_idem.fold_set_fold[OF comp_fun_idem_gcd] Gcd_finite
  by (simp add: foldl_conv_fold gcd.commute)

lemma Gcd_eucl_set [code]:
  "Gcd_eucl (set xs) = foldl gcd_eucl 0 xs"
  by (simp add: Gcd_Gcd_eucl [symmetric] gcd_gcd_eucl Gcd_set)

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
  by (induct a b rule: gcd_eucl_induct)
    (simp_all add: euclid_ext_0 euclid_ext_non_0 ac_simps split: prod.split prod.split_asm)

lemma euclid_ext_gcd' [simp]:
  "euclid_ext a b = (r, s, t) \<Longrightarrow> t = gcd a b"
  by (insert euclid_ext_gcd[of a b], drule (1) subst, simp)
  
lemma euclid_ext'_correct:
  "fst (euclid_ext' a b) * a + snd (euclid_ext' a b) * b = gcd a b"
proof-
  obtain s t c where "euclid_ext a b = (s,t,c)"
    by (cases "euclid_ext a b", blast)
  with euclid_ext_correct[of a b] euclid_ext_gcd[of a b]
    show ?thesis unfolding euclid_ext'_def by simp
qed

lemma bezout: "\<exists>s t. s * a + t * b = gcd a b"
  using euclid_ext'_correct by blast

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

lemma coprime_minus_one [simp]: "gcd (n - 1) n = 1"
proof -
  have "gcd (n - 1) n = gcd n (n - 1)" by (fact gcd.commute)
  also have "\<dots> = gcd ((n - 1) + 1) (n - 1)" by simp
  also have "\<dots> = 1" by (rule coprime_plus_one)
  finally show ?thesis .
qed

lemma lcm_neg1 [simp]: "lcm (-a) b = lcm a b"
  by (rule sym, rule lcmI, simp_all add: lcm_least lcm_zero)

lemma lcm_neg2 [simp]: "lcm a (-b) = lcm a b"
  by (rule sym, rule lcmI, simp_all add: lcm_least lcm_zero)

lemma lcm_neg_numeral_1 [simp]: "lcm (- numeral n) a = lcm (numeral n) a"
  by (fact lcm_neg1)

lemma lcm_neg_numeral_2 [simp]: "lcm a (- numeral n) = lcm a (numeral n)"
  by (fact lcm_neg2)

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
