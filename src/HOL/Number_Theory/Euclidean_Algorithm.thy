(* Author: Manuel Eberl *)

section \<open>Abstract euclidean algorithm\<close>

theory Euclidean_Algorithm
imports Complex_Main "~~/src/HOL/Library/Polynomial"
begin
  
text \<open>
  A Euclidean semiring is a semiring upon which the Euclidean algorithm can be
  implemented. It must provide:
  \begin{itemize}
  \item division with remainder
  \item a size function such that @{term "size (a mod b) < size b"} 
        for any @{term "b \<noteq> 0"}
  \item a normalization factor such that two associated numbers are equal iff 
        they are the same when divd by their normalization factors.
  \end{itemize}
  The existence of these functions makes it possible to derive gcd and lcm functions 
  for any Euclidean semiring.
\<close> 
class euclidean_semiring = semiring_div + 
  fixes euclidean_size :: "'a \<Rightarrow> nat"
  fixes normalization_factor :: "'a \<Rightarrow> 'a"
  assumes mod_size_less: 
    "b \<noteq> 0 \<Longrightarrow> euclidean_size (a mod b) < euclidean_size b"
  assumes size_mult_mono:
    "b \<noteq> 0 \<Longrightarrow> euclidean_size (a * b) \<ge> euclidean_size a"
  assumes normalization_factor_is_unit [intro,simp]: 
    "a \<noteq> 0 \<Longrightarrow> is_unit (normalization_factor a)"
  assumes normalization_factor_mult: "normalization_factor (a * b) = 
    normalization_factor a * normalization_factor b"
  assumes normalization_factor_unit: "is_unit a \<Longrightarrow> normalization_factor a = a"
  assumes normalization_factor_0 [simp]: "normalization_factor 0 = 0"
begin

lemma normalization_factor_dvd [simp]:
  "a \<noteq> 0 \<Longrightarrow> normalization_factor a dvd b"
  by (rule unit_imp_dvd, simp)
    
lemma normalization_factor_1 [simp]:
  "normalization_factor 1 = 1"
  by (simp add: normalization_factor_unit)

lemma normalization_factor_0_iff [simp]:
  "normalization_factor a = 0 \<longleftrightarrow> a = 0"
proof
  assume "normalization_factor a = 0"
  hence "\<not> is_unit (normalization_factor a)"
    by simp
  then show "a = 0" by auto
qed simp

lemma normalization_factor_pow:
  "normalization_factor (a ^ n) = normalization_factor a ^ n"
  by (induct n) (simp_all add: normalization_factor_mult power_Suc2)

lemma normalization_correct [simp]:
  "normalization_factor (a div normalization_factor a) = (if a = 0 then 0 else 1)"
proof (cases "a = 0", simp)
  assume "a \<noteq> 0"
  let ?nf = "normalization_factor"
  from normalization_factor_is_unit[OF \<open>a \<noteq> 0\<close>] have "?nf a \<noteq> 0"
    by auto
  have "?nf (a div ?nf a) * ?nf (?nf a) = ?nf (a div ?nf a * ?nf a)" 
    by (simp add: normalization_factor_mult)
  also have "a div ?nf a * ?nf a = a" using \<open>a \<noteq> 0\<close>
    by simp
  also have "?nf (?nf a) = ?nf a" using \<open>a \<noteq> 0\<close> 
    normalization_factor_is_unit normalization_factor_unit by simp
  finally have "normalization_factor (a div normalization_factor a) = 1"  
    using \<open>?nf a \<noteq> 0\<close> by (metis div_mult_self2_is_id div_self)
  with \<open>a \<noteq> 0\<close> show ?thesis by simp
qed

lemma normalization_0_iff [simp]:
  "a div normalization_factor a = 0 \<longleftrightarrow> a = 0"
  by (cases "a = 0", simp, subst unit_eq_div1, blast, simp)

lemma mult_div_normalization [simp]:
  "b * (1 div normalization_factor a) = b div normalization_factor a"
  by (cases "a = 0") simp_all

lemma associated_iff_normed_eq:
  "associated a b \<longleftrightarrow> a div normalization_factor a = b div normalization_factor b" (is "?P \<longleftrightarrow> ?Q")
proof (cases "a = 0 \<or> b = 0")
  case True then show ?thesis by (auto dest: sym)
next
  case False then have "a \<noteq> 0" and "b \<noteq> 0" by auto
  show ?thesis
  proof
    assume ?Q
    from \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close>
    have "is_unit (normalization_factor a div normalization_factor b)"
      by auto
    moreover from \<open>?Q\<close> \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close>
    have "a = (normalization_factor a div normalization_factor b) * b"
      by (simp add: ac_simps div_mult_swap unit_eq_div1)
    ultimately show "associated a b" by (rule is_unit_associatedI) 
  next
    assume ?P
    then obtain c where "is_unit c" and "a = c * b"
      by (blast elim: associated_is_unitE)
    then show ?Q
      by (auto simp add: normalization_factor_mult normalization_factor_unit)
  qed
qed

lemma normed_associated_imp_eq:
  "associated a b \<Longrightarrow> normalization_factor a \<in> {0, 1} \<Longrightarrow> normalization_factor b \<in> {0, 1} \<Longrightarrow> a = b"
  by (simp add: associated_iff_normed_eq, elim disjE, simp_all)

lemma normed_dvd [iff]:
  "a div normalization_factor a dvd a"
proof (cases "a = 0")
  case True then show ?thesis by simp
next
  case False
  then have "a = a div normalization_factor a * normalization_factor a"
    by (auto intro: unit_div_mult_self)
  then show ?thesis ..
qed

lemma dvd_normed [iff]:
  "a dvd a div normalization_factor a"
proof (cases "a = 0")
  case True then show ?thesis by simp
next
  case False
  then have "a div normalization_factor a = a * (1 div normalization_factor a)"
    by (auto intro: unit_mult_div_div)
  then show ?thesis ..
qed

lemma associated_normed:
  "associated (a div normalization_factor a) a"
  by (rule associatedI) simp_all

lemma normalization_factor_dvd' [simp]:
  "normalization_factor a dvd a"
  by (cases "a = 0", simp_all)

lemmas normalization_factor_dvd_iff [simp] =
  unit_dvd_iff [OF normalization_factor_is_unit]

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
  "gcd_eucl a b = (if b = 0 then a div normalization_factor a
    else gcd_eucl b (a mod b))"
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
  "lcm_eucl a b = a * b div (gcd_eucl a b * normalization_factor (a * b))"

definition Lcm_eucl :: "'a set \<Rightarrow> 'a" -- \<open>
  Somewhat complicated definition of Lcm that has the advantage of working
  for infinite sets as well\<close>
where
  "Lcm_eucl A = (if \<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) then
     let l = SOME l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l =
       (LEAST n. \<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n)
       in l div normalization_factor l
      else 0)"

definition Gcd_eucl :: "'a set \<Rightarrow> 'a"
where
  "Gcd_eucl A = Lcm_eucl {d. \<forall>a\<in>A. d dvd a}"

lemma gcd_eucl_0:
  "gcd_eucl a 0 = a div normalization_factor a"
  by (simp add: gcd_eucl.simps [of a 0])

lemma gcd_eucl_0_left:
  "gcd_eucl 0 a = a div normalization_factor a"
  by (simp_all add: gcd_eucl_0 gcd_eucl.simps [of 0 a])

lemma gcd_eucl_non_0:
  "b \<noteq> 0 \<Longrightarrow> gcd_eucl a b = gcd_eucl b (a mod b)"
  by (simp add: gcd_eucl.simps [of a b] gcd_eucl.simps [of b 0])

end

class euclidean_ring = euclidean_semiring + idom
begin

function euclid_ext :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a" where
  "euclid_ext a b = 
     (if b = 0 then 
        let c = 1 div normalization_factor a in (c, 0, a * c)
      else
        case euclid_ext b (a mod b) of
            (s, t, c) \<Rightarrow> (t, s - t * (a div b), c))"
  by pat_completeness simp
termination
  by (relation "measure (euclidean_size \<circ> snd)") (simp_all add: mod_size_less)

declare euclid_ext.simps [simp del]

lemma euclid_ext_0: 
  "euclid_ext a 0 = (1 div normalization_factor a, 0, a div normalization_factor a)"
  by (simp add: euclid_ext.simps [of a 0])

lemma euclid_ext_left_0: 
  "euclid_ext 0 a = (0, 1 div normalization_factor a, a div normalization_factor a)"
  by (simp add: euclid_ext_0 euclid_ext.simps [of 0 a])

lemma euclid_ext_non_0: 
  "b \<noteq> 0 \<Longrightarrow> euclid_ext a b = (case euclid_ext b (a mod b) of
    (s, t, c) \<Rightarrow> (t, s - t * (a div b), c))"
  by (simp add: euclid_ext.simps [of a b] euclid_ext.simps [of b 0])

lemma euclid_ext_code [code]:
  "euclid_ext a b = (if b = 0 then (1 div normalization_factor a, 0, a div normalization_factor a)
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

lemma euclid_ext'_0: "euclid_ext' a 0 = (1 div normalization_factor a, 0)" 
  by (simp add: euclid_ext'_def euclid_ext_0)

lemma euclid_ext'_left_0: "euclid_ext' 0 a = (0, 1 div normalization_factor a)" 
  by (simp add: euclid_ext'_def euclid_ext_left_0)
  
lemma euclid_ext'_non_0: "b \<noteq> 0 \<Longrightarrow> euclid_ext' a b = (snd (euclid_ext' b (a mod b)),
  fst (euclid_ext' b (a mod b)) - snd (euclid_ext' b (a mod b)) * (a div b))"
  by (simp add: euclid_ext'_def euclid_ext_non_0 split_def)

end

class euclidean_semiring_gcd = euclidean_semiring + gcd + Gcd +
  assumes gcd_gcd_eucl: "gcd = gcd_eucl" and lcm_lcm_eucl: "lcm = lcm_eucl"
  assumes Gcd_Gcd_eucl: "Gcd = Gcd_eucl" and Lcm_Lcm_eucl: "Lcm = Lcm_eucl"
begin

lemma gcd_0_left:
  "gcd 0 a = a div normalization_factor a"
  unfolding gcd_gcd_eucl by (fact gcd_eucl_0_left)

lemma gcd_0:
  "gcd a 0 = a div normalization_factor a"
  unfolding gcd_gcd_eucl by (fact gcd_eucl_0)

lemma gcd_non_0:
  "b \<noteq> 0 \<Longrightarrow> gcd a b = gcd b (a mod b)"
  unfolding gcd_gcd_eucl by (fact gcd_eucl_non_0)

lemma gcd_dvd1 [iff]: "gcd a b dvd a"
  and gcd_dvd2 [iff]: "gcd a b dvd b"
  by (induct a b rule: gcd_eucl_induct)
    (simp_all add: gcd_0 gcd_non_0 dvd_mod_iff)
    
lemma dvd_gcd_D1: "k dvd gcd m n \<Longrightarrow> k dvd m"
  by (rule dvd_trans, assumption, rule gcd_dvd1)

lemma dvd_gcd_D2: "k dvd gcd m n \<Longrightarrow> k dvd n"
  by (rule dvd_trans, assumption, rule gcd_dvd2)

lemma gcd_greatest:
  fixes k a b :: 'a
  shows "k dvd a \<Longrightarrow> k dvd b \<Longrightarrow> k dvd gcd a b"
proof (induct a b rule: gcd_eucl_induct)
  case (zero a) from zero(1) show ?case by (rule dvd_trans) (simp add: gcd_0)
next
  case (mod a b)
  then show ?case
    by (simp add: gcd_non_0 dvd_mod_iff)
qed

lemma dvd_gcd_iff:
  "k dvd gcd a b \<longleftrightarrow> k dvd a \<and> k dvd b"
  by (blast intro!: gcd_greatest intro: dvd_trans)

lemmas gcd_greatest_iff = dvd_gcd_iff

lemma gcd_zero [simp]:
  "gcd a b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  by (metis dvd_0_left dvd_refl gcd_dvd1 gcd_dvd2 gcd_greatest)+

lemma normalization_factor_gcd [simp]:
  "normalization_factor (gcd a b) = (if a = 0 \<and> b = 0 then 0 else 1)" (is "?f a b = ?g a b")
  by (induct a b rule: gcd_eucl_induct)
    (auto simp add: gcd_0 gcd_non_0)

lemma gcdI:
  "k dvd a \<Longrightarrow> k dvd b \<Longrightarrow> (\<And>l. l dvd a \<Longrightarrow> l dvd b \<Longrightarrow> l dvd k)
    \<Longrightarrow> normalization_factor k = (if k = 0 then 0 else 1) \<Longrightarrow> k = gcd a b"
  by (intro normed_associated_imp_eq) (auto simp: associated_def intro: gcd_greatest)

sublocale gcd!: abel_semigroup gcd
proof
  fix a b c 
  show "gcd (gcd a b) c = gcd a (gcd b c)"
  proof (rule gcdI)
    have "gcd (gcd a b) c dvd gcd a b" "gcd a b dvd a" by simp_all
    then show "gcd (gcd a b) c dvd a" by (rule dvd_trans)
    have "gcd (gcd a b) c dvd gcd a b" "gcd a b dvd b" by simp_all
    hence "gcd (gcd a b) c dvd b" by (rule dvd_trans)
    moreover have "gcd (gcd a b) c dvd c" by simp
    ultimately show "gcd (gcd a b) c dvd gcd b c"
      by (rule gcd_greatest)
    show "normalization_factor (gcd (gcd a b) c) =  (if gcd (gcd a b) c = 0 then 0 else 1)"
      by auto
    fix l assume "l dvd a" and "l dvd gcd b c"
    with dvd_trans[OF _ gcd_dvd1] and dvd_trans[OF _ gcd_dvd2]
      have "l dvd b" and "l dvd c" by blast+
    with \<open>l dvd a\<close> show "l dvd gcd (gcd a b) c"
      by (intro gcd_greatest)
  qed
next
  fix a b
  show "gcd a b = gcd b a"
    by (rule gcdI) (simp_all add: gcd_greatest)
qed

lemma gcd_unique: "d dvd a \<and> d dvd b \<and> 
    normalization_factor d = (if d = 0 then 0 else 1) \<and>
    (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  by (rule, auto intro: gcdI simp: gcd_greatest)

lemma gcd_dvd_prod: "gcd a b dvd k * b"
  using mult_dvd_mono [of 1] by auto

lemma gcd_1_left [simp]: "gcd 1 a = 1"
  by (rule sym, rule gcdI, simp_all)

lemma gcd_1 [simp]: "gcd a 1 = 1"
  by (rule sym, rule gcdI, simp_all)

lemma gcd_proj2_if_dvd: 
  "b dvd a \<Longrightarrow> gcd a b = b div normalization_factor b"
  by (cases "b = 0", simp_all add: dvd_eq_mod_eq_0 gcd_non_0 gcd_0)

lemma gcd_proj1_if_dvd: 
  "a dvd b \<Longrightarrow> gcd a b = a div normalization_factor a"
  by (subst gcd.commute, simp add: gcd_proj2_if_dvd)

lemma gcd_proj1_iff: "gcd m n = m div normalization_factor m \<longleftrightarrow> m dvd n"
proof
  assume A: "gcd m n = m div normalization_factor m"
  show "m dvd n"
  proof (cases "m = 0")
    assume [simp]: "m \<noteq> 0"
    from A have B: "m = gcd m n * normalization_factor m"
      by (simp add: unit_eq_div2)
    show ?thesis by (subst B, simp add: mult_unit_dvd_iff)
  qed (insert A, simp)
next
  assume "m dvd n"
  then show "gcd m n = m div normalization_factor m" by (rule gcd_proj1_if_dvd)
qed
  
lemma gcd_proj2_iff: "gcd m n = n div normalization_factor n \<longleftrightarrow> n dvd m"
  by (subst gcd.commute, simp add: gcd_proj1_iff)

lemma gcd_mod1 [simp]:
  "gcd (a mod b) b = gcd a b"
  by (rule gcdI, metis dvd_mod_iff gcd_dvd1 gcd_dvd2, simp_all add: gcd_greatest dvd_mod_iff)

lemma gcd_mod2 [simp]:
  "gcd a (b mod a) = gcd a b"
  by (rule gcdI, simp, metis dvd_mod_iff gcd_dvd1 gcd_dvd2, simp_all add: gcd_greatest dvd_mod_iff)
         
lemma gcd_mult_distrib': 
  "c div normalization_factor c * gcd a b = gcd (c * a) (c * b)"
proof (cases "c = 0")
  case True then show ?thesis by (simp_all add: gcd_0)
next
  case False then have [simp]: "is_unit (normalization_factor c)" by simp
  show ?thesis
  proof (induct a b rule: gcd_eucl_induct)
    case (zero a) show ?case
    proof (cases "a = 0")
      case True then show ?thesis by (simp add: gcd_0)
    next
      case False then have "is_unit (normalization_factor a)" by simp
      then show ?thesis
        by (simp add: gcd_0 unit_div_commute unit_div_mult_swap normalization_factor_mult is_unit_div_mult2_eq)
    qed
    case (mod a b)
    then show ?case by (simp add: mult_mod_right gcd.commute)
  qed
qed

lemma gcd_mult_distrib:
  "k * gcd a b = gcd (k*a) (k*b) * normalization_factor k"
proof-
  let ?nf = "normalization_factor"
  from gcd_mult_distrib' 
    have "gcd (k*a) (k*b) = k div ?nf k * gcd a b" ..
  also have "... = k * gcd a b div ?nf k"
    by (metis dvd_div_mult dvd_eq_mod_eq_0 mod_0 normalization_factor_dvd)
  finally show ?thesis
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
  with \<open>a \<noteq> 0\<close> have "euclidean_size (gcd a b) = euclidean_size a"
    by (intro le_antisym, simp_all)
  with assms have "a dvd gcd a b" by (auto intro: dvd_euclidean_size_eq_imp_dvd)
  hence "a dvd b" using dvd_gcd_D2 by blast
  with \<open>\<not>a dvd b\<close> show False by contradiction
qed

lemma euclidean_size_gcd_less2:
  assumes "b \<noteq> 0" and "\<not>b dvd a"
  shows "euclidean_size (gcd a b) < euclidean_size b"
  using assms by (subst gcd.commute, rule euclidean_size_gcd_less1)

lemma gcd_mult_unit1: "is_unit a \<Longrightarrow> gcd (b * a) c = gcd b c"
  apply (rule gcdI)
  apply (rule dvd_trans, rule gcd_dvd1, simp add: unit_simps)
  apply (rule gcd_dvd2)
  apply (rule gcd_greatest, simp add: unit_simps, assumption)
  apply (subst normalization_factor_gcd, simp add: gcd_0)
  done

lemma gcd_mult_unit2: "is_unit a \<Longrightarrow> gcd b (c * a) = gcd b c"
  by (subst gcd.commute, subst gcd_mult_unit1, assumption, rule gcd.commute)

lemma gcd_div_unit1: "is_unit a \<Longrightarrow> gcd (b div a) c = gcd b c"
  by (erule is_unitE [of _ b]) (simp add: gcd_mult_unit1)

lemma gcd_div_unit2: "is_unit a \<Longrightarrow> gcd b (c div a) = gcd b c"
  by (erule is_unitE [of _ c]) (simp add: gcd_mult_unit2)

lemma gcd_idem: "gcd a a = a div normalization_factor a"
  by (cases "a = 0") (simp add: gcd_0_left, rule sym, rule gcdI, simp_all)

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

lemma coprime_dvd_mult:
  assumes "gcd c b = 1" and "c dvd a * b"
  shows "c dvd a"
proof -
  let ?nf = "normalization_factor"
  from assms gcd_mult_distrib [of a c b] 
    have A: "a = gcd (a * c) (a * b) * ?nf a" by simp
  from \<open>c dvd a * b\<close> show ?thesis by (subst A, simp_all add: gcd_greatest)
qed

lemma coprime_dvd_mult_iff:
  "gcd c b = 1 \<Longrightarrow> (c dvd a * b) = (c dvd a)"
  by (rule, rule coprime_dvd_mult, simp_all)

lemma gcd_dvd_antisym:
  "gcd a b dvd gcd c d \<Longrightarrow> gcd c d dvd gcd a b \<Longrightarrow> gcd a b = gcd c d"
proof (rule gcdI)
  assume A: "gcd a b dvd gcd c d" and B: "gcd c d dvd gcd a b"
  have "gcd c d dvd c" by simp
  with A show "gcd a b dvd c" by (rule dvd_trans)
  have "gcd c d dvd d" by simp
  with A show "gcd a b dvd d" by (rule dvd_trans)
  show "normalization_factor (gcd a b) = (if gcd a b = 0 then 0 else 1)"
    by simp
  fix l assume "l dvd c" and "l dvd d"
  hence "l dvd gcd c d" by (rule gcd_greatest)
  from this and B show "l dvd gcd a b" by (rule dvd_trans)
qed

lemma gcd_mult_cancel:
  assumes "gcd k n = 1"
  shows "gcd (k * m) n = gcd m n"
proof (rule gcd_dvd_antisym)
  have "gcd (gcd (k * m) n) k = gcd (gcd k n) (k * m)" by (simp add: ac_simps)
  also note \<open>gcd k n = 1\<close>
  finally have "gcd (gcd (k * m) n) k = 1" by simp
  hence "gcd (k * m) n dvd m" by (rule coprime_dvd_mult, simp add: ac_simps)
  moreover have "gcd (k * m) n dvd n" by simp
  ultimately show "gcd (k * m) n dvd gcd m n" by (rule gcd_greatest)
  have "gcd m n dvd (k * m)" and "gcd m n dvd n" by simp_all
  then show "gcd m n dvd gcd (k * m) n" by (rule gcd_greatest)
qed

lemma coprime_crossproduct:
  assumes [simp]: "gcd a d = 1" "gcd b c = 1"
  shows "associated (a * c) (b * d) \<longleftrightarrow> associated a b \<and> associated c d" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs then show ?lhs unfolding associated_def by (fast intro: mult_dvd_mono)
next
  assume ?lhs
  from \<open>?lhs\<close> have "a dvd b * d" unfolding associated_def by (metis dvd_mult_left) 
  hence "a dvd b" by (simp add: coprime_dvd_mult_iff)
  moreover from \<open>?lhs\<close> have "b dvd a * c" unfolding associated_def by (metis dvd_mult_left) 
  hence "b dvd a" by (simp add: coprime_dvd_mult_iff)
  moreover from \<open>?lhs\<close> have "c dvd d * b" 
    unfolding associated_def by (auto dest: dvd_mult_right simp add: ac_simps)
  hence "c dvd d" by (simp add: coprime_dvd_mult_iff gcd.commute)
  moreover from \<open>?lhs\<close> have "d dvd c * a"
    unfolding associated_def by (auto dest: dvd_mult_right simp add: ac_simps)
  hence "d dvd c" by (simp add: coprime_dvd_mult_iff gcd.commute)
  ultimately show ?rhs unfolding associated_def by simp
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
  by (auto intro: coprimeI gcd_greatest dvd_gcd_D1 dvd_gcd_D2)

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

lemma coprime_mult: 
  assumes da: "gcd d a = 1" and db: "gcd d b = 1"
  shows "gcd d (a * b) = 1"
  apply (subst gcd.commute)
  using da apply (subst gcd_mult_cancel)
  apply (subst gcd.commute, assumption)
  apply (subst gcd.commute, rule db)
  done

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

lemma coprime_exp2 [intro]:
  "gcd a b = 1 \<Longrightarrow> gcd (a^n) (b^m) = 1"
  apply (rule coprime_exp)
  apply (subst gcd.commute)
  apply (rule coprime_exp)
  apply (subst gcd.commute)
  apply assumption
  done

lemma gcd_exp:
  "gcd (a^n) (b^n) = (gcd a b) ^ n"
proof (cases "a = 0 \<and> b = 0")
  assume "a = 0 \<and> b = 0"
  then show ?thesis by (cases n, simp_all add: gcd_0_left)
next
  assume A: "\<not>(a = 0 \<and> b = 0)"
  hence "1 = gcd ((a div gcd a b)^n) ((b div gcd a b)^n)"
    using div_gcd_coprime by (subst sym, auto simp: div_gcd_coprime)
  hence "(gcd a b) ^ n = (gcd a b) ^ n * ..." by simp
  also note gcd_mult_distrib
  also have "normalization_factor ((gcd a b)^n) = 1"
    by (simp add: normalization_factor_pow A)
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

lemma divs_mult:
  assumes mr: "m dvd r" and nr: "n dvd r" and mn: "gcd m n = 1"
  shows "m * n dvd r"
proof -
  from mr nr obtain m' n' where m': "r = m*m'" and n': "r = n*n'"
    unfolding dvd_def by blast
  from mr n' have "m dvd n'*n" by (simp add: ac_simps)
  hence "m dvd n'" using coprime_dvd_mult_iff[OF mn] by simp
  then obtain k where k: "n' = m*k" unfolding dvd_def by blast
  with n' have "r = m * n * k" by (simp add: mult_ac)
  then show ?thesis unfolding dvd_def by blast
qed

lemma coprime_plus_one [simp]: "gcd (n + 1) n = 1"
  by (subst add_commute, simp)

lemma setprod_coprime [rule_format]:
  "(\<forall>i\<in>A. gcd (f i) a = 1) \<longrightarrow> gcd (\<Prod>i\<in>A. f i) a = 1"
  apply (cases "finite A")
  apply (induct set: finite)
  apply (auto simp add: gcd_mult_cancel)
  done

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

lemma lcm_gcd:
  "lcm a b = a * b div (gcd a b * normalization_factor (a*b))"
  by (simp only: lcm_lcm_eucl gcd_gcd_eucl lcm_eucl_def)

lemma lcm_gcd_prod:
  "lcm a b * gcd a b = a * b div normalization_factor (a*b)"
proof (cases "a * b = 0")
  let ?nf = normalization_factor
  assume "a * b \<noteq> 0"
  hence "gcd a b \<noteq> 0" by simp
  from lcm_gcd have "lcm a b * gcd a b = gcd a b * (a * b div (?nf (a*b) * gcd a b))" 
    by (simp add: mult_ac)
  also from \<open>a * b \<noteq> 0\<close> have "... = a * b div ?nf (a*b)"
    by (simp add: div_mult_swap mult.commute)
  finally show ?thesis .
qed (auto simp add: lcm_gcd)

lemma lcm_dvd1 [iff]:
  "a dvd lcm a b"
proof (cases "a*b = 0")
  assume "a * b \<noteq> 0"
  hence "gcd a b \<noteq> 0" by simp
  let ?c = "1 div normalization_factor (a * b)"
  from \<open>a * b \<noteq> 0\<close> have [simp]: "is_unit (normalization_factor (a * b))" by simp
  from lcm_gcd_prod[of a b] have "lcm a b * gcd a b = a * ?c * b"
    by (simp add: div_mult_swap unit_div_commute)
  hence "lcm a b * gcd a b div gcd a b = a * ?c * b div gcd a b" by simp
  with \<open>gcd a b \<noteq> 0\<close> have "lcm a b = a * ?c * b div gcd a b"
    by (subst (asm) div_mult_self2_is_id, simp_all)
  also have "... = a * (?c * b div gcd a b)"
    by (metis div_mult_swap gcd_dvd2 mult_assoc)
  finally show ?thesis by (rule dvdI)
qed (auto simp add: lcm_gcd)

lemma lcm_least:
  "\<lbrakk>a dvd k; b dvd k\<rbrakk> \<Longrightarrow> lcm a b dvd k"
proof (cases "k = 0")
  let ?nf = normalization_factor
  assume "k \<noteq> 0"
  hence "is_unit (?nf k)" by simp
  hence "?nf k \<noteq> 0" by (metis not_is_unit_0)
  assume A: "a dvd k" "b dvd k"
  hence "gcd a b \<noteq> 0" using \<open>k \<noteq> 0\<close> by auto
  from A obtain r s where ar: "k = a * r" and bs: "k = b * s" 
    unfolding dvd_def by blast
  with \<open>k \<noteq> 0\<close> have "r * s \<noteq> 0"
    by auto (drule sym [of 0], simp)
  hence "is_unit (?nf (r * s))" by simp
  let ?c = "?nf k div ?nf (r*s)"
  from \<open>is_unit (?nf k)\<close> and \<open>is_unit (?nf (r * s))\<close> have "is_unit ?c" by (rule unit_div)
  hence "?c \<noteq> 0" using not_is_unit_0 by fast 
  from ar bs have "k * k * gcd s r = ?nf k * k * gcd (k * s) (k * r)"
    by (subst mult_assoc, subst gcd_mult_distrib[of k s r], simp only: ac_simps)
  also have "... = ?nf k * k * gcd ((r*s) * a) ((r*s) * b)"
    by (subst (3) \<open>k = a * r\<close>, subst (3) \<open>k = b * s\<close>, simp add: algebra_simps)
  also have "... = ?c * r*s * k * gcd a b" using \<open>r * s \<noteq> 0\<close>
    by (subst gcd_mult_distrib'[symmetric], simp add: algebra_simps unit_simps)
  finally have "(a*r) * (b*s) * gcd s r = ?c * k * r * s * gcd a b"
    by (subst ar[symmetric], subst bs[symmetric], simp add: mult_ac)
  hence "a * b * gcd s r * (r * s) = ?c * k * gcd a b * (r * s)"
    by (simp add: algebra_simps)
  hence "?c * k * gcd a b = a * b * gcd s r" using \<open>r * s \<noteq> 0\<close>
    by (metis div_mult_self2_is_id)
  also have "... = lcm a b * gcd a b * gcd s r * ?nf (a*b)"
    by (subst lcm_gcd_prod[of a b], metis gcd_mult_distrib gcd_mult_distrib') 
  also have "... = lcm a b * gcd s r * ?nf (a*b) * gcd a b"
    by (simp add: algebra_simps)
  finally have "k * ?c = lcm a b * gcd s r * ?nf (a*b)" using \<open>gcd a b \<noteq> 0\<close>
    by (metis mult.commute div_mult_self2_is_id)
  hence "k = lcm a b * (gcd s r * ?nf (a*b)) div ?c" using \<open>?c \<noteq> 0\<close>
    by (metis div_mult_self2_is_id mult_assoc) 
  also have "... = lcm a b * (gcd s r * ?nf (a*b) div ?c)" using \<open>is_unit ?c\<close>
    by (simp add: unit_simps)
  finally show ?thesis by (rule dvdI)
qed simp

lemma lcm_zero:
  "lcm a b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
proof -
  let ?nf = normalization_factor
  {
    assume "a \<noteq> 0" "b \<noteq> 0"
    hence "a * b div ?nf (a * b) \<noteq> 0" by (simp add: no_zero_divisors)
    moreover from \<open>a \<noteq> 0\<close> and \<open>b \<noteq> 0\<close> have "gcd a b \<noteq> 0" by simp
    ultimately have "lcm a b \<noteq> 0" using lcm_gcd_prod[of a b] by (intro notI, simp)
  } moreover {
    assume "a = 0 \<or> b = 0"
    hence "lcm a b = 0" by (elim disjE, simp_all add: lcm_gcd)
  }
  ultimately show ?thesis by blast
qed

lemmas lcm_0_iff = lcm_zero

lemma gcd_lcm: 
  assumes "lcm a b \<noteq> 0"
  shows "gcd a b = a * b div (lcm a b * normalization_factor (a * b))"
proof-
  from assms have "gcd a b \<noteq> 0" by (simp add: lcm_zero)
  let ?c = "normalization_factor (a * b)"
  from \<open>lcm a b \<noteq> 0\<close> have "?c \<noteq> 0" by (intro notI, simp add: lcm_zero no_zero_divisors)
  hence "is_unit ?c" by simp
  from lcm_gcd_prod [of a b] have "gcd a b = a * b div ?c div lcm a b"
    by (subst (2) div_mult_self2_is_id[OF \<open>lcm a b \<noteq> 0\<close>, symmetric], simp add: mult_ac)
  also from \<open>is_unit ?c\<close> have "... = a * b div (lcm a b * ?c)"
    by (metis \<open>?c \<noteq> 0\<close> div_mult_mult1 dvd_mult_div_cancel mult_commute normalization_factor_dvd')
  finally show ?thesis .
qed

lemma normalization_factor_lcm [simp]:
  "normalization_factor (lcm a b) = (if a = 0 \<or> b = 0 then 0 else 1)"
proof (cases "a = 0 \<or> b = 0")
  case True then show ?thesis
    by (auto simp add: lcm_gcd) 
next
  case False
  let ?nf = normalization_factor
  from lcm_gcd_prod[of a b] 
    have "?nf (lcm a b) * ?nf (gcd a b) = ?nf (a*b) div ?nf (a*b)"
    by (metis div_by_0 div_self normalization_correct normalization_factor_0 normalization_factor_mult)
  also have "... = (if a*b = 0 then 0 else 1)"
    by simp
  finally show ?thesis using False by simp
qed

lemma lcm_dvd2 [iff]: "b dvd lcm a b"
  using lcm_dvd1 [of b a] by (simp add: lcm_gcd ac_simps)

lemma lcmI:
  "\<lbrakk>a dvd k; b dvd k; \<And>l. a dvd l \<Longrightarrow> b dvd l \<Longrightarrow> k dvd l;
    normalization_factor k = (if k = 0 then 0 else 1)\<rbrakk> \<Longrightarrow> k = lcm a b"
  by (intro normed_associated_imp_eq) (auto simp: associated_def intro: lcm_least)

sublocale lcm!: abel_semigroup lcm
proof
  fix a b c
  show "lcm (lcm a b) c = lcm a (lcm b c)"
  proof (rule lcmI)
    have "a dvd lcm a b" and "lcm a b dvd lcm (lcm a b) c" by simp_all
    then show "a dvd lcm (lcm a b) c" by (rule dvd_trans)
    
    have "b dvd lcm a b" and "lcm a b dvd lcm (lcm a b) c" by simp_all
    hence "b dvd lcm (lcm a b) c" by (rule dvd_trans)
    moreover have "c dvd lcm (lcm a b) c" by simp
    ultimately show "lcm b c dvd lcm (lcm a b) c" by (rule lcm_least)

    fix l assume "a dvd l" and "lcm b c dvd l"
    have "b dvd lcm b c" by simp
    from this and \<open>lcm b c dvd l\<close> have "b dvd l" by (rule dvd_trans)
    have "c dvd lcm b c" by simp
    from this and \<open>lcm b c dvd l\<close> have "c dvd l" by (rule dvd_trans)
    from \<open>a dvd l\<close> and \<open>b dvd l\<close> have "lcm a b dvd l" by (rule lcm_least)
    from this and \<open>c dvd l\<close> show "lcm (lcm a b) c dvd l" by (rule lcm_least)
  qed (simp add: lcm_zero)
next
  fix a b
  show "lcm a b = lcm b a"
    by (simp add: lcm_gcd ac_simps)
qed

lemma dvd_lcm_D1:
  "lcm m n dvd k \<Longrightarrow> m dvd k"
  by (rule dvd_trans, rule lcm_dvd1, assumption)

lemma dvd_lcm_D2:
  "lcm m n dvd k \<Longrightarrow> n dvd k"
  by (rule dvd_trans, rule lcm_dvd2, assumption)

lemma gcd_dvd_lcm [simp]:
  "gcd a b dvd lcm a b"
  by (metis dvd_trans gcd_dvd2 lcm_dvd2)

lemma lcm_1_iff:
  "lcm a b = 1 \<longleftrightarrow> is_unit a \<and> is_unit b"
proof
  assume "lcm a b = 1"
  then show "is_unit a \<and> is_unit b" by auto
next
  assume "is_unit a \<and> is_unit b"
  hence "a dvd 1" and "b dvd 1" by simp_all
  hence "is_unit (lcm a b)" by (rule lcm_least)
  hence "lcm a b = normalization_factor (lcm a b)"
    by (subst normalization_factor_unit, simp_all)
  also have "\<dots> = 1" using \<open>is_unit a \<and> is_unit b\<close>
    by auto
  finally show "lcm a b = 1" .
qed

lemma lcm_0_left [simp]:
  "lcm 0 a = 0"
  by (rule sym, rule lcmI, simp_all)

lemma lcm_0 [simp]:
  "lcm a 0 = 0"
  by (rule sym, rule lcmI, simp_all)

lemma lcm_unique:
  "a dvd d \<and> b dvd d \<and> 
  normalization_factor d = (if d = 0 then 0 else 1) \<and>
  (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  by (rule, auto intro: lcmI simp: lcm_least lcm_zero)

lemma dvd_lcm_I1 [simp]:
  "k dvd m \<Longrightarrow> k dvd lcm m n"
  by (metis lcm_dvd1 dvd_trans)

lemma dvd_lcm_I2 [simp]:
  "k dvd n \<Longrightarrow> k dvd lcm m n"
  by (metis lcm_dvd2 dvd_trans)

lemma lcm_1_left [simp]:
  "lcm 1 a = a div normalization_factor a"
  by (cases "a = 0") (simp, rule sym, rule lcmI, simp_all)

lemma lcm_1_right [simp]:
  "lcm a 1 = a div normalization_factor a"
  using lcm_1_left [of a] by (simp add: ac_simps)

lemma lcm_coprime:
  "gcd a b = 1 \<Longrightarrow> lcm a b = a * b div normalization_factor (a*b)"
  by (subst lcm_gcd) simp

lemma lcm_proj1_if_dvd: 
  "b dvd a \<Longrightarrow> lcm a b = a div normalization_factor a"
  by (cases "a = 0") (simp, rule sym, rule lcmI, simp_all)

lemma lcm_proj2_if_dvd: 
  "a dvd b \<Longrightarrow> lcm a b = b div normalization_factor b"
  using lcm_proj1_if_dvd [of a b] by (simp add: ac_simps)

lemma lcm_proj1_iff:
  "lcm m n = m div normalization_factor m \<longleftrightarrow> n dvd m"
proof
  assume A: "lcm m n = m div normalization_factor m"
  show "n dvd m"
  proof (cases "m = 0")
    assume [simp]: "m \<noteq> 0"
    from A have B: "m = lcm m n * normalization_factor m"
      by (simp add: unit_eq_div2)
    show ?thesis by (subst B, simp)
  qed simp
next
  assume "n dvd m"
  then show "lcm m n = m div normalization_factor m" by (rule lcm_proj1_if_dvd)
qed

lemma lcm_proj2_iff:
  "lcm m n = n div normalization_factor n \<longleftrightarrow> m dvd n"
  using lcm_proj1_iff [of n m] by (simp add: ac_simps)

lemma euclidean_size_lcm_le1: 
  assumes "a \<noteq> 0" and "b \<noteq> 0"
  shows "euclidean_size a \<le> euclidean_size (lcm a b)"
proof -
  have "a dvd lcm a b" by (rule lcm_dvd1)
  then obtain c where A: "lcm a b = a * c" unfolding dvd_def by blast
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
  hence "b dvd a" by (rule dvd_lcm_D2)
  with \<open>\<not>b dvd a\<close> show False by contradiction
qed

lemma euclidean_size_lcm_less2:
  assumes "a \<noteq> 0" and "\<not>a dvd b"
  shows "euclidean_size b < euclidean_size (lcm a b)"
  using assms euclidean_size_lcm_less1 [of a b] by (simp add: ac_simps)

lemma lcm_mult_unit1:
  "is_unit a \<Longrightarrow> lcm (b * a) c = lcm b c"
  apply (rule lcmI)
  apply (rule dvd_trans[of _ "b * a"], simp, rule lcm_dvd1)
  apply (rule lcm_dvd2)
  apply (rule lcm_least, simp add: unit_simps, assumption)
  apply (subst normalization_factor_lcm, simp add: lcm_zero)
  done

lemma lcm_mult_unit2:
  "is_unit a \<Longrightarrow> lcm b (c * a) = lcm b c"
  using lcm_mult_unit1 [of a c b] by (simp add: ac_simps)

lemma lcm_div_unit1:
  "is_unit a \<Longrightarrow> lcm (b div a) c = lcm b c"
  by (erule is_unitE [of _ b]) (simp add: lcm_mult_unit1) 

lemma lcm_div_unit2:
  "is_unit a \<Longrightarrow> lcm b (c div a) = lcm b c"
  by (erule is_unitE [of _ c]) (simp add: lcm_mult_unit2)

lemma lcm_left_idem:
  "lcm a (lcm a b) = lcm a b"
  apply (rule lcmI)
  apply simp
  apply (subst lcm.assoc [symmetric], rule lcm_dvd2)
  apply (rule lcm_least, assumption)
  apply (erule (1) lcm_least)
  apply (auto simp: lcm_zero)
  done

lemma lcm_right_idem:
  "lcm (lcm a b) b = lcm a b"
  apply (rule lcmI)
  apply (subst lcm.assoc, rule lcm_dvd1)
  apply (rule lcm_dvd2)
  apply (rule lcm_least, erule (1) lcm_least, assumption)
  apply (auto simp: lcm_zero)
  done

lemma comp_fun_idem_lcm: "comp_fun_idem lcm"
proof
  fix a b show "lcm a \<circ> lcm b = lcm b \<circ> lcm a"
    by (simp add: fun_eq_iff ac_simps)
next
  fix a show "lcm a \<circ> lcm a = lcm a" unfolding o_def
    by (intro ext, simp add: lcm_left_idem)
qed

lemma dvd_Lcm [simp]: "a \<in> A \<Longrightarrow> a dvd Lcm A"
  and Lcm_dvd [simp]: "(\<forall>a\<in>A. a dvd l') \<Longrightarrow> Lcm A dvd l'"
  and normalization_factor_Lcm [simp]: 
          "normalization_factor (Lcm A) = (if Lcm A = 0 then 0 else 1)"
proof -
  have "(\<forall>a\<in>A. a dvd Lcm A) \<and> (\<forall>l'. (\<forall>a\<in>A. a dvd l') \<longrightarrow> Lcm A dvd l') \<and>
    normalization_factor (Lcm A) = (if Lcm A = 0 then 0 else 1)" (is ?thesis)
  proof (cases "\<exists>l. l \<noteq>  0 \<and> (\<forall>a\<in>A. a dvd l)")
    case False
    hence "Lcm A = 0" by (auto simp: Lcm_Lcm_eucl Lcm_eucl_def)
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
      with \<open>\<forall>a\<in>A. a dvd l\<close> have "\<forall>a\<in>A. a dvd gcd l l'" by (auto intro: gcd_greatest)
      moreover from \<open>l \<noteq> 0\<close> have "gcd l l' \<noteq> 0" by simp
      ultimately have "\<exists>b. b \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd b) \<and> euclidean_size b = euclidean_size (gcd l l')"
        by (intro exI[of _ "gcd l l'"], auto)
      hence "euclidean_size (gcd l l') \<ge> n" by (subst n_def) (rule Least_le)
      moreover have "euclidean_size (gcd l l') \<le> n"
      proof -
        have "gcd l l' dvd l" by simp
        then obtain a where "l = gcd l l' * a" unfolding dvd_def by blast
        with \<open>l \<noteq> 0\<close> have "a \<noteq> 0" by auto
        hence "euclidean_size (gcd l l') \<le> euclidean_size (gcd l l' * a)"
          by (rule size_mult_mono)
        also have "gcd l l' * a = l" using \<open>l = gcd l l' * a\<close> ..
        also note \<open>euclidean_size l = n\<close>
        finally show "euclidean_size (gcd l l') \<le> n" .
      qed
      ultimately have "euclidean_size l = euclidean_size (gcd l l')" 
        by (intro le_antisym, simp_all add: \<open>euclidean_size l = n\<close>)
      with \<open>l \<noteq> 0\<close> have "l dvd gcd l l'" by (blast intro: dvd_euclidean_size_eq_imp_dvd)
      hence "l dvd l'" by (blast dest: dvd_gcd_D2)
    }

    with \<open>(\<forall>a\<in>A. a dvd l)\<close> and normalization_factor_is_unit[OF \<open>l \<noteq> 0\<close>] and \<open>l \<noteq> 0\<close>
      have "(\<forall>a\<in>A. a dvd l div normalization_factor l) \<and> 
        (\<forall>l'. (\<forall>a\<in>A. a dvd l') \<longrightarrow> l div normalization_factor l dvd l') \<and>
        normalization_factor (l div normalization_factor l) = 
        (if l div normalization_factor l = 0 then 0 else 1)"
      by (auto simp: unit_simps)
    also from True have "l div normalization_factor l = Lcm A"
      by (simp add: Lcm_Lcm_eucl Lcm_eucl_def Let_def n_def l_def)
    finally show ?thesis .
  qed
  note A = this

  {fix a assume "a \<in> A" then show "a dvd Lcm A" using A by blast}
  {fix l' assume "\<forall>a\<in>A. a dvd l'" then show "Lcm A dvd l'" using A by blast}
  from A show "normalization_factor (Lcm A) = (if Lcm A = 0 then 0 else 1)" by blast
qed
    
lemma LcmI:
  "(\<And>a. a\<in>A \<Longrightarrow> a dvd l) \<Longrightarrow> (\<And>l'. (\<forall>a\<in>A. a dvd l') \<Longrightarrow> l dvd l') \<Longrightarrow>
      normalization_factor l = (if l = 0 then 0 else 1) \<Longrightarrow> l = Lcm A"
  by (intro normed_associated_imp_eq)
    (auto intro: Lcm_dvd dvd_Lcm simp: associated_def)

lemma Lcm_subset:
  "A \<subseteq> B \<Longrightarrow> Lcm A dvd Lcm B"
  by (blast intro: Lcm_dvd dvd_Lcm)

lemma Lcm_Un:
  "Lcm (A \<union> B) = lcm (Lcm A) (Lcm B)"
  apply (rule lcmI)
  apply (blast intro: Lcm_subset)
  apply (blast intro: Lcm_subset)
  apply (intro Lcm_dvd ballI, elim UnE)
  apply (rule dvd_trans, erule dvd_Lcm, assumption)
  apply (rule dvd_trans, erule dvd_Lcm, assumption)
  apply simp
  done

lemma Lcm_1_iff:
  "Lcm A = 1 \<longleftrightarrow> (\<forall>a\<in>A. is_unit a)"
proof
  assume "Lcm A = 1"
  then show "\<forall>a\<in>A. is_unit a" by auto
qed (rule LcmI [symmetric], auto)

lemma Lcm_no_units:
  "Lcm A = Lcm (A - {a. is_unit a})"
proof -
  have "(A - {a. is_unit a}) \<union> {a\<in>A. is_unit a} = A" by blast
  hence "Lcm A = lcm (Lcm (A - {a. is_unit a})) (Lcm {a\<in>A. is_unit a})"
    by (simp add: Lcm_Un[symmetric])
  also have "Lcm {a\<in>A. is_unit a} = 1" by (simp add: Lcm_1_iff)
  finally show ?thesis by simp
qed

lemma Lcm_empty [simp]:
  "Lcm {} = 1"
  by (simp add: Lcm_1_iff)

lemma Lcm_eq_0 [simp]:
  "0 \<in> A \<Longrightarrow> Lcm A = 0"
  by (drule dvd_Lcm) simp

lemma Lcm0_iff':
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
    hence "l div normalization_factor l \<noteq> 0" by simp
    also from ex have "l div normalization_factor l = Lcm A"
       by (simp only: Lcm_Lcm_eucl Lcm_eucl_def n_def l_def if_True Let_def)
    finally show False using \<open>Lcm A = 0\<close> by contradiction
  qed
qed (simp only: Lcm_Lcm_eucl Lcm_eucl_def if_False)

lemma Lcm0_iff [simp]:
  "finite A \<Longrightarrow> Lcm A = 0 \<longleftrightarrow> 0 \<in> A"
proof -
  assume "finite A"
  have "0 \<in> A \<Longrightarrow> Lcm A = 0"  by (intro dvd_0_left dvd_Lcm)
  moreover {
    assume "0 \<notin> A"
    hence "\<Prod>A \<noteq> 0" 
      apply (induct rule: finite_induct[OF \<open>finite A\<close>]) 
      apply simp
      apply (subst setprod.insert, assumption, assumption)
      apply (rule no_zero_divisors)
      apply blast+
      done
    moreover from \<open>finite A\<close> have "\<forall>a\<in>A. a dvd \<Prod>A" by blast
    ultimately have "\<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l)" by blast
    with Lcm0_iff' have "Lcm A \<noteq> 0" by simp
  }
  ultimately show "Lcm A = 0 \<longleftrightarrow> 0 \<in> A" by blast
qed

lemma Lcm_no_multiple:
  "(\<forall>m. m \<noteq> 0 \<longrightarrow> (\<exists>a\<in>A. \<not>a dvd m)) \<Longrightarrow> Lcm A = 0"
proof -
  assume "\<forall>m. m \<noteq> 0 \<longrightarrow> (\<exists>a\<in>A. \<not>a dvd m)"
  hence "\<not>(\<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l))" by blast
  then show "Lcm A = 0" by (simp only: Lcm_Lcm_eucl Lcm_eucl_def if_False)
qed

lemma Lcm_insert [simp]:
  "Lcm (insert a A) = lcm a (Lcm A)"
proof (rule lcmI)
  fix l assume "a dvd l" and "Lcm A dvd l"
  hence "\<forall>a\<in>A. a dvd l" by (blast intro: dvd_trans dvd_Lcm)
  with \<open>a dvd l\<close> show "Lcm (insert a A) dvd l" by (force intro: Lcm_dvd)
qed (auto intro: Lcm_dvd dvd_Lcm)
 
lemma Lcm_finite:
  assumes "finite A"
  shows "Lcm A = Finite_Set.fold lcm 1 A"
  by (induct rule: finite.induct[OF \<open>finite A\<close>])
    (simp_all add: comp_fun_idem.fold_insert_idem[OF comp_fun_idem_lcm])

lemma Lcm_set [code_unfold]:
  "Lcm (set xs) = fold lcm xs 1"
  using comp_fun_idem.fold_set_fold[OF comp_fun_idem_lcm] Lcm_finite by (simp add: ac_simps)

lemma Lcm_singleton [simp]:
  "Lcm {a} = a div normalization_factor a"
  by simp

lemma Lcm_2 [simp]:
  "Lcm {a,b} = lcm a b"
  by (simp only: Lcm_insert Lcm_empty lcm_1_right)
    (cases "b = 0", simp, rule lcm_div_unit2, simp)

lemma Lcm_coprime:
  assumes "finite A" and "A \<noteq> {}" 
  assumes "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> gcd a b = 1"
  shows "Lcm A = \<Prod>A div normalization_factor (\<Prod>A)"
using assms proof (induct rule: finite_ne_induct)
  case (insert a A)
  have "Lcm (insert a A) = lcm a (Lcm A)" by simp
  also from insert have "Lcm A = \<Prod>A div normalization_factor (\<Prod>A)" by blast
  also have "lcm a \<dots> = lcm a (\<Prod>A)" by (cases "\<Prod>A = 0") (simp_all add: lcm_div_unit2)
  also from insert have "gcd a (\<Prod>A) = 1" by (subst gcd.commute, intro setprod_coprime) auto
  with insert have "lcm a (\<Prod>A) = \<Prod>(insert a A) div normalization_factor (\<Prod>(insert a A))"
    by (simp add: lcm_coprime)
  finally show ?case .
qed simp
      
lemma Lcm_coprime':
  "card A \<noteq> 0 \<Longrightarrow> (\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> gcd a b = 1)
    \<Longrightarrow> Lcm A = \<Prod>A div normalization_factor (\<Prod>A)"
  by (rule Lcm_coprime) (simp_all add: card_eq_0_iff)

lemma Gcd_Lcm:
  "Gcd A = Lcm {d. \<forall>a\<in>A. d dvd a}"
  by (simp add: Gcd_Gcd_eucl Lcm_Lcm_eucl Gcd_eucl_def)

lemma Gcd_dvd [simp]: "a \<in> A \<Longrightarrow> Gcd A dvd a"
  and dvd_Gcd [simp]: "(\<forall>a\<in>A. g' dvd a) \<Longrightarrow> g' dvd Gcd A"
  and normalization_factor_Gcd [simp]: 
    "normalization_factor (Gcd A) = (if Gcd A = 0 then 0 else 1)"
proof -
  fix a assume "a \<in> A"
  hence "Lcm {d. \<forall>a\<in>A. d dvd a} dvd a" by (intro Lcm_dvd) blast
  then show "Gcd A dvd a" by (simp add: Gcd_Lcm)
next
  fix g' assume "\<forall>a\<in>A. g' dvd a"
  hence "g' dvd Lcm {d. \<forall>a\<in>A. d dvd a}" by (intro dvd_Lcm) blast
  then show "g' dvd Gcd A" by (simp add: Gcd_Lcm)
next
  show "normalization_factor (Gcd A) = (if Gcd A = 0 then 0 else 1)"
    by (simp add: Gcd_Lcm)
qed

lemma GcdI:
  "(\<And>a. a\<in>A \<Longrightarrow> l dvd a) \<Longrightarrow> (\<And>l'. (\<forall>a\<in>A. l' dvd a) \<Longrightarrow> l' dvd l) \<Longrightarrow>
    normalization_factor l = (if l = 0 then 0 else 1) \<Longrightarrow> l = Gcd A"
  by (intro normed_associated_imp_eq)
    (auto intro: Gcd_dvd dvd_Gcd simp: associated_def)

lemma Lcm_Gcd:
  "Lcm A = Gcd {m. \<forall>a\<in>A. a dvd m}"
  by (rule LcmI[symmetric]) (auto intro: dvd_Gcd Gcd_dvd)

lemma Gcd_0_iff:
  "Gcd A = 0 \<longleftrightarrow> A \<subseteq> {0}"
  apply (rule iffI)
  apply (rule subsetI, drule Gcd_dvd, simp)
  apply (auto intro: GcdI[symmetric])
  done

lemma Gcd_empty [simp]:
  "Gcd {} = 0"
  by (simp add: Gcd_0_iff)

lemma Gcd_1:
  "1 \<in> A \<Longrightarrow> Gcd A = 1"
  by (intro GcdI[symmetric]) (auto intro: Gcd_dvd dvd_Gcd)

lemma Gcd_insert [simp]:
  "Gcd (insert a A) = gcd a (Gcd A)"
proof (rule gcdI)
  fix l assume "l dvd a" and "l dvd Gcd A"
  hence "\<forall>a\<in>A. l dvd a" by (blast intro: dvd_trans Gcd_dvd)
  with \<open>l dvd a\<close> show "l dvd Gcd (insert a A)" by (force intro: Gcd_dvd)
qed auto

lemma Gcd_finite:
  assumes "finite A"
  shows "Gcd A = Finite_Set.fold gcd 0 A"
  by (induct rule: finite.induct[OF \<open>finite A\<close>])
    (simp_all add: comp_fun_idem.fold_insert_idem[OF comp_fun_idem_gcd])

lemma Gcd_set [code_unfold]:
  "Gcd (set xs) = fold gcd xs 0"
  using comp_fun_idem.fold_set_fold[OF comp_fun_idem_gcd] Gcd_finite by (simp add: ac_simps)

lemma Gcd_singleton [simp]: "Gcd {a} = a div normalization_factor a"
  by (simp add: gcd_0)

lemma Gcd_2 [simp]: "Gcd {a,b} = gcd a b"
  by (simp only: Gcd_insert Gcd_empty gcd_0) (cases "b = 0", simp, rule gcd_div_unit2, simp)

subclass semiring_gcd
  by unfold_locales (simp_all add: gcd_greatest_iff)
  
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
    (simp_all add: euclid_ext_0 gcd_0 euclid_ext_non_0 ac_simps split: prod.split prod.split_asm)

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

definition [simp]:
  "normalization_factor_nat (n::nat) = (if n = 0 then 0 else 1 :: nat)"

instance proof
qed simp_all

end

instantiation int :: euclidean_ring
begin

definition [simp]:
  "euclidean_size_int = (nat \<circ> abs :: int \<Rightarrow> nat)"

definition [simp]:
  "normalization_factor_int = (sgn :: int \<Rightarrow> int)"

instance
proof (default, goals)
  case 2
  then show ?case by (auto simp add: abs_mult nat_mult_distrib)
next
  case 3
  then show ?case by (simp add: zsgn_def)
next
  case 5
  then show ?case by (auto simp: zsgn_def)
next
  case 6
  then show ?case by (auto split: abs_split simp: zsgn_def)
qed (auto simp: sgn_times split: abs_split)

end

instantiation poly :: (field) euclidean_ring
begin

definition euclidean_size_poly :: "'a poly \<Rightarrow> nat"
  where "euclidean_size p = (if p = 0 then 0 else Suc (degree p))"

definition normalization_factor_poly :: "'a poly \<Rightarrow> 'a poly"
  where "normalization_factor p = monom (coeff p (degree p)) 0"

lemma euclidean_size_poly_0 [simp]:
  "euclidean_size (0::'a poly) = 0"
  by (simp add: euclidean_size_poly_def)

lemma euclidean_size_poly_not_0 [simp]:
  "p \<noteq> 0 \<Longrightarrow> euclidean_size p = Suc (degree p)"
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
  from \<open>q \<noteq> 0\<close> have "is_unit (monom (coeff q (degree q)) 0)"
    by (auto intro: is_unit_monom_0)
  then show "is_unit (normalization_factor q)"
    by (simp add: normalization_factor_poly_def)
next
  fix p :: "'a poly"
  assume "is_unit p"
  then have "monom (coeff p (degree p)) 0 = p"
    by (fact is_unit_monom_trival)
  then show "normalization_factor p = p"
    by (simp add: normalization_factor_poly_def)
next
  fix p q :: "'a poly"
  have "monom (coeff (p * q) (degree (p * q))) 0 =
    monom (coeff p (degree p)) 0 * monom (coeff q (degree q)) 0"
    by (simp add: monom_0 coeff_degree_mult)
  then show "normalization_factor (p * q) =
    normalization_factor p * normalization_factor q"
    by (simp add: normalization_factor_poly_def)
next
  have "monom (coeff 0 (degree 0)) 0 = 0"
    by simp
  then show "normalization_factor 0 = (0::'a poly)"
    by (simp add: normalization_factor_poly_def)
qed

end

end
