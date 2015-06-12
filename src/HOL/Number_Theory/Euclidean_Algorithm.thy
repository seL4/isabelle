(* Author: Manuel Eberl *)

section {* Abstract euclidean algorithm *}

theory Euclidean_Algorithm
imports Complex_Main
begin

context semiring_div
begin 

text \<open>Units: invertible elements in a ring\<close>

abbreviation is_unit :: "'a \<Rightarrow> bool"
where
  "is_unit a \<equiv> a dvd 1"

lemma not_is_unit_0 [simp]:
  "\<not> is_unit 0"
  by simp

lemma unit_imp_dvd [dest]: 
  "is_unit b \<Longrightarrow> b dvd a"
  by (rule dvd_trans [of _ 1]) simp_all

lemma unit_dvdE:
  assumes "is_unit a"
  obtains c where "a \<noteq> 0" and "b = a * c"
proof -
  from assms have "a dvd b" by auto
  then obtain c where "b = a * c" ..
  moreover from assms have "a \<noteq> 0" by auto
  ultimately show thesis using that by blast
qed

lemma dvd_unit_imp_unit:
  "a dvd b \<Longrightarrow> is_unit b \<Longrightarrow> is_unit a"
  by (rule dvd_trans)

lemma unit_div_1_unit [simp, intro]:
  assumes "is_unit a"
  shows "is_unit (1 div a)"
proof -
  from assms have "1 = 1 div a * a" by simp
  then show "is_unit (1 div a)" by (rule dvdI)
qed

lemma is_unitE [elim?]:
  assumes "is_unit a"
  obtains b where "a \<noteq> 0" and "b \<noteq> 0"
    and "is_unit b" and "1 div a = b" and "1 div b = a"
    and "a * b = 1" and "c div a = c * b"
proof (rule that)
  def b \<equiv> "1 div a"
  then show "1 div a = b" by simp
  from b_def `is_unit a` show "is_unit b" by simp
  from `is_unit a` and `is_unit b` show "a \<noteq> 0" and "b \<noteq> 0" by auto
  from b_def `is_unit a` show "a * b = 1" by simp
  then have "1 = a * b" ..
  with b_def `b \<noteq> 0` show "1 div b = a" by simp
  from `is_unit a` have "a dvd c" ..
  then obtain d where "c = a * d" ..
  with `a \<noteq> 0` `a * b = 1` show "c div a = c * b"
    by (simp add: mult.assoc mult.left_commute [of a])
qed

lemma unit_prod [intro]:
  "is_unit a \<Longrightarrow> is_unit b \<Longrightarrow> is_unit (a * b)"
  by (subst mult_1_left [of 1, symmetric]) (rule mult_dvd_mono) 
  
lemma unit_div [intro]:
  "is_unit a \<Longrightarrow> is_unit b \<Longrightarrow> is_unit (a div b)"
  by (erule is_unitE [of b a]) (simp add: ac_simps unit_prod)

lemma mult_unit_dvd_iff:
  assumes "is_unit b"
  shows "a * b dvd c \<longleftrightarrow> a dvd c"
proof
  assume "a * b dvd c"
  with assms show "a dvd c"
    by (simp add: dvd_mult_left)
next
  assume "a dvd c"
  then obtain k where "c = a * k" ..
  with assms have "c = (a * b) * (1 div b * k)"
    by (simp add: mult_ac)
  then show "a * b dvd c" by (rule dvdI)
qed

lemma dvd_mult_unit_iff:
  assumes "is_unit b"
  shows "a dvd c * b \<longleftrightarrow> a dvd c"
proof
  assume "a dvd c * b"
  with assms have "c * b dvd c * (b * (1 div b))"
    by (subst mult_assoc [symmetric]) simp
  also from `is_unit b` have "b * (1 div b) = 1" by (rule is_unitE) simp
  finally have "c * b dvd c" by simp
  with `a dvd c * b` show "a dvd c" by (rule dvd_trans)
next
  assume "a dvd c"
  then show "a dvd c * b" by simp
qed

lemma div_unit_dvd_iff:
  "is_unit b \<Longrightarrow> a div b dvd c \<longleftrightarrow> a dvd c"
  by (erule is_unitE [of _ a]) (auto simp add: mult_unit_dvd_iff)

lemma dvd_div_unit_iff:
  "is_unit b \<Longrightarrow> a dvd c div b \<longleftrightarrow> a dvd c"
  by (erule is_unitE [of _ c]) (simp add: dvd_mult_unit_iff)

lemmas unit_dvd_iff = mult_unit_dvd_iff div_unit_dvd_iff
  dvd_mult_unit_iff dvd_div_unit_iff -- \<open>FIXME consider fact collection\<close>

lemma unit_mult_div_div [simp]:
  "is_unit a \<Longrightarrow> b * (1 div a) = b div a"
  by (erule is_unitE [of _ b]) simp

lemma unit_div_mult_self [simp]:
  "is_unit a \<Longrightarrow> b div a * a = b"
  by (rule dvd_div_mult_self) auto

lemma unit_div_1_div_1 [simp]:
  "is_unit a \<Longrightarrow> 1 div (1 div a) = a"
  by (erule is_unitE) simp

lemma unit_div_mult_swap:
  "is_unit c \<Longrightarrow> a * (b div c) = (a * b) div c"
  by (erule unit_dvdE [of _ b]) (simp add: mult.left_commute [of _ c])

lemma unit_div_commute:
  "is_unit b \<Longrightarrow> (a div b) * c = (a * c) div b"
  using unit_div_mult_swap [of b c a] by (simp add: ac_simps)

lemma unit_eq_div1:
  "is_unit b \<Longrightarrow> a div b = c \<longleftrightarrow> a = c * b"
  by (auto elim: is_unitE)

lemma unit_eq_div2:
  "is_unit b \<Longrightarrow> a = c div b \<longleftrightarrow> a * b = c"
  using unit_eq_div1 [of b c a] by auto

lemma unit_mult_left_cancel:
  assumes "is_unit a"
  shows "a * b = a * c \<longleftrightarrow> b = c" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?Q then show ?P by simp
next
  assume ?P then have "a * b div a = a * c div a" by simp
  moreover from assms have "a \<noteq> 0" by auto
  ultimately show ?Q by simp
qed

lemma unit_mult_right_cancel:
  "is_unit a \<Longrightarrow> b * a = c * a \<longleftrightarrow> b = c"
  using unit_mult_left_cancel [of a b c] by (auto simp add: ac_simps)

lemma unit_div_cancel:
  assumes "is_unit a"
  shows "b div a = c div a \<longleftrightarrow> b = c"
proof -
  from assms have "is_unit (1 div a)" by simp
  then have "b * (1 div a) = c * (1 div a) \<longleftrightarrow> b = c"
    by (rule unit_mult_right_cancel)
  with assms show ?thesis by simp
qed
  

text \<open>Associated elements in a ring – an equivalence relation induced by the quasi-order divisibility \<close>

definition associated :: "'a \<Rightarrow> 'a \<Rightarrow> bool" 
where
  "associated a b \<longleftrightarrow> a dvd b \<and> b dvd a"

lemma associatedI:
  "a dvd b \<Longrightarrow> b dvd a \<Longrightarrow> associated a b"
  by (simp add: associated_def)

lemma associatedD1:
  "associated a b \<Longrightarrow> a dvd b"
  by (simp add: associated_def)

lemma associatedD2:
  "associated a b \<Longrightarrow> b dvd a"
  by (simp add: associated_def)

lemma associated_refl [simp]:
  "associated a a"
  by (auto intro: associatedI)

lemma associated_sym:
  "associated b a \<longleftrightarrow> associated a b"
  by (auto intro: associatedI dest: associatedD1 associatedD2)

lemma associated_trans:
  "associated a b \<Longrightarrow> associated b c \<Longrightarrow> associated a c"
  by (auto intro: associatedI dvd_trans dest: associatedD1 associatedD2)

lemma equivp_associated:
  "equivp associated"
proof (rule equivpI)
  show "reflp associated"
    by (rule reflpI) simp
  show "symp associated"
    by (rule sympI) (simp add: associated_sym)
  show "transp associated"
    by (rule transpI) (fact associated_trans)
qed

lemma associated_0 [simp]:
  "associated 0 b \<longleftrightarrow> b = 0"
  "associated a 0 \<longleftrightarrow> a = 0"
  by (auto dest: associatedD1 associatedD2)

lemma associated_unit:
  "associated a b \<Longrightarrow> is_unit a \<Longrightarrow> is_unit b"
  using dvd_unit_imp_unit by (auto dest!: associatedD1 associatedD2)

lemma associated_iff_div_unit:
  "associated a b \<longleftrightarrow> (\<exists>c. is_unit c \<and> a = c * b)"
proof
  assume "associated a b"
  show "\<exists>c. is_unit c \<and> a = c * b"
  proof (cases "a = 0")
    assume "a = 0"
    then show "\<exists>c. is_unit c \<and> a = c * b" using `associated a b`
        by (intro exI[of _ 1], simp add: associated_def)
  next
    assume [simp]: "a \<noteq> 0"
    hence [simp]: "a dvd b" "b dvd a" using `associated a b`
        unfolding associated_def by simp_all
    hence "1 = a div b * (b div a)"
      by (simp add: div_mult_swap)
    hence "is_unit (a div b)" ..
    moreover have "a = (a div b) * b" by simp
    ultimately show ?thesis by blast
  qed
next
  assume "\<exists>c. is_unit c \<and> a = c * b"
  then obtain c where "is_unit c" and "a = c * b" by blast
  hence "b = a * (1 div c)" by (simp add: algebra_simps)
  hence "a dvd b" by simp
  moreover from `a = c * b` have "b dvd a" by simp
  ultimately show "associated a b" unfolding associated_def by simp
qed

lemmas unit_simps = mult_unit_dvd_iff div_unit_dvd_iff dvd_mult_unit_iff 
  dvd_div_unit_iff unit_div_mult_swap unit_div_commute
  unit_mult_left_cancel unit_mult_right_cancel unit_div_cancel 
  unit_eq_div1 unit_eq_div2

end

lemma is_unit_int:
  "is_unit (k::int) \<longleftrightarrow> k = 1 \<or> k = - 1"
  by auto

  
text {*
  A Euclidean semiring is a semiring upon which the Euclidean algorithm can be
  implemented. It must provide:
  \begin{itemize}
  \item division with remainder
  \item a size function such that @{term "size (a mod b) < size b"} 
        for any @{term "b \<noteq> 0"}
  \item a normalisation factor such that two associated numbers are equal iff 
        they are the same when divd by their normalisation factors.
  \end{itemize}
  The existence of these functions makes it possible to derive gcd and lcm functions 
  for any Euclidean semiring.
*} 
class euclidean_semiring = semiring_div + 
  fixes euclidean_size :: "'a \<Rightarrow> nat"
  fixes normalisation_factor :: "'a \<Rightarrow> 'a"
  assumes mod_size_less [simp]: 
    "b \<noteq> 0 \<Longrightarrow> euclidean_size (a mod b) < euclidean_size b"
  assumes size_mult_mono:
    "b \<noteq> 0 \<Longrightarrow> euclidean_size (a * b) \<ge> euclidean_size a"
  assumes normalisation_factor_is_unit [intro,simp]: 
    "a \<noteq> 0 \<Longrightarrow> is_unit (normalisation_factor a)"
  assumes normalisation_factor_mult: "normalisation_factor (a * b) = 
    normalisation_factor a * normalisation_factor b"
  assumes normalisation_factor_unit: "is_unit a \<Longrightarrow> normalisation_factor a = a"
  assumes normalisation_factor_0 [simp]: "normalisation_factor 0 = 0"
begin

lemma normalisation_factor_dvd [simp]:
  "a \<noteq> 0 \<Longrightarrow> normalisation_factor a dvd b"
  by (rule unit_imp_dvd, simp)
    
lemma normalisation_factor_1 [simp]:
  "normalisation_factor 1 = 1"
  by (simp add: normalisation_factor_unit)

lemma normalisation_factor_0_iff [simp]:
  "normalisation_factor a = 0 \<longleftrightarrow> a = 0"
proof
  assume "normalisation_factor a = 0"
  hence "\<not> is_unit (normalisation_factor a)"
    by simp
  then show "a = 0" by auto
qed simp

lemma normalisation_factor_pow:
  "normalisation_factor (a ^ n) = normalisation_factor a ^ n"
  by (induct n) (simp_all add: normalisation_factor_mult power_Suc2)

lemma normalisation_correct [simp]:
  "normalisation_factor (a div normalisation_factor a) = (if a = 0 then 0 else 1)"
proof (cases "a = 0", simp)
  assume "a \<noteq> 0"
  let ?nf = "normalisation_factor"
  from normalisation_factor_is_unit[OF `a \<noteq> 0`] have "?nf a \<noteq> 0"
    by auto
  have "?nf (a div ?nf a) * ?nf (?nf a) = ?nf (a div ?nf a * ?nf a)" 
    by (simp add: normalisation_factor_mult)
  also have "a div ?nf a * ?nf a = a" using `a \<noteq> 0`
    by simp
  also have "?nf (?nf a) = ?nf a" using `a \<noteq> 0` 
    normalisation_factor_is_unit normalisation_factor_unit by simp
  finally have "normalisation_factor (a div normalisation_factor a) = 1"  
    using `?nf a \<noteq> 0` by (metis div_mult_self2_is_id div_self)
  with `a \<noteq> 0` show ?thesis by simp
qed

lemma normalisation_0_iff [simp]:
  "a div normalisation_factor a = 0 \<longleftrightarrow> a = 0"
  by (cases "a = 0", simp, subst unit_eq_div1, blast, simp)

lemma mult_div_normalisation [simp]:
  "b * (1 div normalisation_factor a) = b div normalisation_factor a"
  by (cases "a = 0") simp_all

lemma associated_iff_normed_eq:
  "associated a b \<longleftrightarrow> a div normalisation_factor a = b div normalisation_factor b"
proof (cases "b = 0", simp, cases "a = 0", metis associated_0(1) normalisation_0_iff, rule iffI)
  let ?nf = normalisation_factor
  assume "a \<noteq> 0" "b \<noteq> 0" "a div ?nf a = b div ?nf b"
  hence "a = b * (?nf a div ?nf b)"
    apply (subst (asm) unit_eq_div1, blast, subst (asm) unit_div_commute, blast)
    apply (subst div_mult_swap, simp, simp)
    done
  with `a \<noteq> 0` `b \<noteq> 0` have "\<exists>c. is_unit c \<and> a = c * b"
    by (intro exI[of _ "?nf a div ?nf b"], force simp: mult_ac)
  with associated_iff_div_unit show "associated a b" by simp
next
  let ?nf = normalisation_factor
  assume "a \<noteq> 0" "b \<noteq> 0" "associated a b"
  with associated_iff_div_unit obtain c where "is_unit c" and "a = c * b" by blast
  then show "a div ?nf a = b div ?nf b"
    apply (simp only: `a = c * b` normalisation_factor_mult normalisation_factor_unit)
    apply (rule div_mult_mult1, force)
    done
  qed

lemma normed_associated_imp_eq:
  "associated a b \<Longrightarrow> normalisation_factor a \<in> {0, 1} \<Longrightarrow> normalisation_factor b \<in> {0, 1} \<Longrightarrow> a = b"
  by (simp add: associated_iff_normed_eq, elim disjE, simp_all)
    
lemmas normalisation_factor_dvd_iff [simp] =
  unit_dvd_iff [OF normalisation_factor_is_unit]

lemma euclidean_division:
  fixes a :: 'a and b :: 'a
  assumes "b \<noteq> 0"
  obtains s and t where "a = s * b + t" 
    and "euclidean_size t < euclidean_size b"
proof -
  from div_mod_equality[of a b 0] 
     have "a = a div b * b + a mod b" by simp
  with that and assms show ?thesis by force
qed

lemma dvd_euclidean_size_eq_imp_dvd:
  assumes "a \<noteq> 0" and b_dvd_a: "b dvd a" and size_eq: "euclidean_size a = euclidean_size b"
  shows "a dvd b"
proof (subst dvd_eq_mod_eq_0, rule ccontr)
  assume "b mod a \<noteq> 0"
  from b_dvd_a have b_dvd_mod: "b dvd b mod a" by (simp add: dvd_mod_iff)
  from b_dvd_mod obtain c where "b mod a = b * c" unfolding dvd_def by blast
    with `b mod a \<noteq> 0` have "c \<noteq> 0" by auto
  with `b mod a = b * c` have "euclidean_size (b mod a) \<ge> euclidean_size b"
      using size_mult_mono by force
  moreover from `a \<noteq> 0` have "euclidean_size (b mod a) < euclidean_size a"
      using mod_size_less by blast
  ultimately show False using size_eq by simp
qed

function gcd_eucl :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "gcd_eucl a b = (if b = 0 then a div normalisation_factor a else gcd_eucl b (a mod b))"
  by (pat_completeness, simp)
termination by (relation "measure (euclidean_size \<circ> snd)", simp_all)

declare gcd_eucl.simps [simp del]

lemma gcd_induct: "\<lbrakk>\<And>b. P b 0; \<And>a b. 0 \<noteq> b \<Longrightarrow> P b (a mod b) \<Longrightarrow> P a b\<rbrakk> \<Longrightarrow> P a b"
proof (induct a b rule: gcd_eucl.induct)
  case ("1" m n)
    then show ?case by (cases "n = 0") auto
qed

definition lcm_eucl :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "lcm_eucl a b = a * b div (gcd_eucl a b * normalisation_factor (a * b))"

  (* Somewhat complicated definition of Lcm that has the advantage of working
     for infinite sets as well *)

definition Lcm_eucl :: "'a set \<Rightarrow> 'a"
where
  "Lcm_eucl A = (if \<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) then
     let l = SOME l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l =
       (LEAST n. \<exists>l. l \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd l) \<and> euclidean_size l = n)
       in l div normalisation_factor l
      else 0)"

definition Gcd_eucl :: "'a set \<Rightarrow> 'a"
where
  "Gcd_eucl A = Lcm_eucl {d. \<forall>a\<in>A. d dvd a}"

end

class euclidean_semiring_gcd = euclidean_semiring + gcd + Gcd +
  assumes gcd_gcd_eucl: "gcd = gcd_eucl" and lcm_lcm_eucl: "lcm = lcm_eucl"
  assumes Gcd_Gcd_eucl: "Gcd = Gcd_eucl" and Lcm_Lcm_eucl: "Lcm = Lcm_eucl"
begin

lemma gcd_red:
  "gcd a b = gcd b (a mod b)"
  by (metis gcd_eucl.simps mod_0 mod_by_0 gcd_gcd_eucl)

lemma gcd_non_0:
  "b \<noteq> 0 \<Longrightarrow> gcd a b = gcd b (a mod b)"
  by (rule gcd_red)

lemma gcd_0_left:
  "gcd 0 a = a div normalisation_factor a"
   by (simp only: gcd_gcd_eucl, subst gcd_eucl.simps, subst gcd_eucl.simps, simp add: Let_def)

lemma gcd_0:
  "gcd a 0 = a div normalisation_factor a"
  by (simp only: gcd_gcd_eucl, subst gcd_eucl.simps, simp add: Let_def)

lemma gcd_dvd1 [iff]: "gcd a b dvd a"
  and gcd_dvd2 [iff]: "gcd a b dvd b"
proof (induct a b rule: gcd_eucl.induct)
  fix a b :: 'a
  assume IH1: "b \<noteq> 0 \<Longrightarrow> gcd b (a mod b) dvd b"
  assume IH2: "b \<noteq> 0 \<Longrightarrow> gcd b (a mod b) dvd (a mod b)"
  
  have "gcd a b dvd a \<and> gcd a b dvd b"
  proof (cases "b = 0")
    case True
      then show ?thesis by (cases "a = 0", simp_all add: gcd_0)
  next
    case False
      with IH1 and IH2 show ?thesis by (simp add: gcd_non_0 dvd_mod_iff)
  qed
  then show "gcd a b dvd a" "gcd a b dvd b" by simp_all
qed

lemma dvd_gcd_D1: "k dvd gcd m n \<Longrightarrow> k dvd m"
  by (rule dvd_trans, assumption, rule gcd_dvd1)

lemma dvd_gcd_D2: "k dvd gcd m n \<Longrightarrow> k dvd n"
  by (rule dvd_trans, assumption, rule gcd_dvd2)

lemma gcd_greatest:
  fixes k a b :: 'a
  shows "k dvd a \<Longrightarrow> k dvd b \<Longrightarrow> k dvd gcd a b"
proof (induct a b rule: gcd_eucl.induct)
  case (1 a b)
  show ?case
    proof (cases "b = 0")
      assume "b = 0"
      with 1 show ?thesis by (cases "a = 0", simp_all add: gcd_0)
    next
      assume "b \<noteq> 0"
      with 1 show ?thesis by (simp add: gcd_non_0 dvd_mod_iff) 
    qed
qed

lemma dvd_gcd_iff:
  "k dvd gcd a b \<longleftrightarrow> k dvd a \<and> k dvd b"
  by (blast intro!: gcd_greatest intro: dvd_trans)

lemmas gcd_greatest_iff = dvd_gcd_iff

lemma gcd_zero [simp]:
  "gcd a b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  by (metis dvd_0_left dvd_refl gcd_dvd1 gcd_dvd2 gcd_greatest)+

lemma normalisation_factor_gcd [simp]:
  "normalisation_factor (gcd a b) = (if a = 0 \<and> b = 0 then 0 else 1)" (is "?f a b = ?g a b")
proof (induct a b rule: gcd_eucl.induct)
  fix a b :: 'a
  assume IH: "b \<noteq> 0 \<Longrightarrow> ?f b (a mod b) = ?g b (a mod b)"
  then show "?f a b = ?g a b" by (cases "b = 0", auto simp: gcd_non_0 gcd_0)
qed

lemma gcdI:
  "k dvd a \<Longrightarrow> k dvd b \<Longrightarrow> (\<And>l. l dvd a \<Longrightarrow> l dvd b \<Longrightarrow> l dvd k)
    \<Longrightarrow> normalisation_factor k = (if k = 0 then 0 else 1) \<Longrightarrow> k = gcd a b"
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
    show "normalisation_factor (gcd (gcd a b) c) =  (if gcd (gcd a b) c = 0 then 0 else 1)"
      by auto
    fix l assume "l dvd a" and "l dvd gcd b c"
    with dvd_trans[OF _ gcd_dvd1] and dvd_trans[OF _ gcd_dvd2]
      have "l dvd b" and "l dvd c" by blast+
    with `l dvd a` show "l dvd gcd (gcd a b) c"
      by (intro gcd_greatest)
  qed
next
  fix a b
  show "gcd a b = gcd b a"
    by (rule gcdI) (simp_all add: gcd_greatest)
qed

lemma gcd_unique: "d dvd a \<and> d dvd b \<and> 
    normalisation_factor d = (if d = 0 then 0 else 1) \<and>
    (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  by (rule, auto intro: gcdI simp: gcd_greatest)

lemma gcd_dvd_prod: "gcd a b dvd k * b"
  using mult_dvd_mono [of 1] by auto

lemma gcd_1_left [simp]: "gcd 1 a = 1"
  by (rule sym, rule gcdI, simp_all)

lemma gcd_1 [simp]: "gcd a 1 = 1"
  by (rule sym, rule gcdI, simp_all)

lemma gcd_proj2_if_dvd: 
  "b dvd a \<Longrightarrow> gcd a b = b div normalisation_factor b"
  by (cases "b = 0", simp_all add: dvd_eq_mod_eq_0 gcd_non_0 gcd_0)

lemma gcd_proj1_if_dvd: 
  "a dvd b \<Longrightarrow> gcd a b = a div normalisation_factor a"
  by (subst gcd.commute, simp add: gcd_proj2_if_dvd)

lemma gcd_proj1_iff: "gcd m n = m div normalisation_factor m \<longleftrightarrow> m dvd n"
proof
  assume A: "gcd m n = m div normalisation_factor m"
  show "m dvd n"
  proof (cases "m = 0")
    assume [simp]: "m \<noteq> 0"
    from A have B: "m = gcd m n * normalisation_factor m"
      by (simp add: unit_eq_div2)
    show ?thesis by (subst B, simp add: mult_unit_dvd_iff)
  qed (insert A, simp)
next
  assume "m dvd n"
  then show "gcd m n = m div normalisation_factor m" by (rule gcd_proj1_if_dvd)
qed
  
lemma gcd_proj2_iff: "gcd m n = n div normalisation_factor n \<longleftrightarrow> n dvd m"
  by (subst gcd.commute, simp add: gcd_proj1_iff)

lemma gcd_mod1 [simp]:
  "gcd (a mod b) b = gcd a b"
  by (rule gcdI, metis dvd_mod_iff gcd_dvd1 gcd_dvd2, simp_all add: gcd_greatest dvd_mod_iff)

lemma gcd_mod2 [simp]:
  "gcd a (b mod a) = gcd a b"
  by (rule gcdI, simp, metis dvd_mod_iff gcd_dvd1 gcd_dvd2, simp_all add: gcd_greatest dvd_mod_iff)
         
lemma normalisation_factor_dvd' [simp]:
  "normalisation_factor a dvd a"
  by (cases "a = 0", simp_all)

lemma gcd_mult_distrib': 
  "k div normalisation_factor k * gcd a b = gcd (k*a) (k*b)"
proof (induct a b rule: gcd_eucl.induct)
  case (1 a b)
  show ?case
  proof (cases "b = 0")
    case True
    then show ?thesis by (simp add: normalisation_factor_mult gcd_0 algebra_simps div_mult_div_if_dvd)
  next
    case False
    hence "k div normalisation_factor k * gcd a b =  gcd (k * b) (k * (a mod b))" 
      using 1 by (subst gcd_red, simp)
    also have "... = gcd (k * a) (k * b)"
      by (simp add: mult_mod_right gcd.commute)
    finally show ?thesis .
  qed
qed

lemma gcd_mult_distrib:
  "k * gcd a b = gcd (k*a) (k*b) * normalisation_factor k"
proof-
  let ?nf = "normalisation_factor"
  from gcd_mult_distrib' 
    have "gcd (k*a) (k*b) = k div ?nf k * gcd a b" ..
  also have "... = k * gcd a b div ?nf k"
    by (metis dvd_div_mult dvd_eq_mod_eq_0 mod_0 normalisation_factor_dvd)
  finally show ?thesis
    by simp
qed

lemma euclidean_size_gcd_le1 [simp]:
  assumes "a \<noteq> 0"
  shows "euclidean_size (gcd a b) \<le> euclidean_size a"
proof -
   have "gcd a b dvd a" by (rule gcd_dvd1)
   then obtain c where A: "a = gcd a b * c" unfolding dvd_def by blast
   with `a \<noteq> 0` show ?thesis by (subst (2) A, intro size_mult_mono) auto
qed

lemma euclidean_size_gcd_le2 [simp]:
  "b \<noteq> 0 \<Longrightarrow> euclidean_size (gcd a b) \<le> euclidean_size b"
  by (subst gcd.commute, rule euclidean_size_gcd_le1)

lemma euclidean_size_gcd_less1:
  assumes "a \<noteq> 0" and "\<not>a dvd b"
  shows "euclidean_size (gcd a b) < euclidean_size a"
proof (rule ccontr)
  assume "\<not>euclidean_size (gcd a b) < euclidean_size a"
  with `a \<noteq> 0` have "euclidean_size (gcd a b) = euclidean_size a"
    by (intro le_antisym, simp_all)
  with assms have "a dvd gcd a b" by (auto intro: dvd_euclidean_size_eq_imp_dvd)
  hence "a dvd b" using dvd_gcd_D2 by blast
  with `\<not>a dvd b` show False by contradiction
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
  apply (subst normalisation_factor_gcd, simp add: gcd_0)
  done

lemma gcd_mult_unit2: "is_unit a \<Longrightarrow> gcd b (c * a) = gcd b c"
  by (subst gcd.commute, subst gcd_mult_unit1, assumption, rule gcd.commute)

lemma gcd_div_unit1: "is_unit a \<Longrightarrow> gcd (b div a) c = gcd b c"
  by (erule is_unitE [of _ b]) (simp add: gcd_mult_unit1)

lemma gcd_div_unit2: "is_unit a \<Longrightarrow> gcd b (c div a) = gcd b c"
  by (erule is_unitE [of _ c]) (simp add: gcd_mult_unit2)

lemma gcd_idem: "gcd a a = a div normalisation_factor a"
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
  let ?nf = "normalisation_factor"
  from assms gcd_mult_distrib [of a c b] 
    have A: "a = gcd (a * c) (a * b) * ?nf a" by simp
  from `c dvd a * b` show ?thesis by (subst A, simp_all add: gcd_greatest)
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
  show "normalisation_factor (gcd a b) = (if gcd a b = 0 then 0 else 1)"
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
  also note `gcd k n = 1`
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
  from `?lhs` have "a dvd b * d" unfolding associated_def by (metis dvd_mult_left) 
  hence "a dvd b" by (simp add: coprime_dvd_mult_iff)
  moreover from `?lhs` have "b dvd a * c" unfolding associated_def by (metis dvd_mult_left) 
  hence "b dvd a" by (simp add: coprime_dvd_mult_iff)
  moreover from `?lhs` have "c dvd d * b" 
    unfolding associated_def by (auto dest: dvd_mult_right simp add: ac_simps)
  hence "c dvd d" by (simp add: coprime_dvd_mult_iff gcd.commute)
  moreover from `?lhs` have "d dvd c * a"
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

lemma gcd_add_mult: "gcd m (k * m + n) = gcd m n"
  by (subst gcd.commute, subst gcd_red, simp)

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
    using `d \<noteq> 0` by simp
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
  with `l dvd d` and dab show "l dvd 1" by (auto intro: gcd_greatest)
qed

lemma coprime_rmult:
  assumes dab: "gcd d (a * b) = 1"
  shows "gcd d b = 1"
proof (rule coprimeI)
  fix l assume "l dvd d" and "l dvd b"
  hence "l dvd a * b" by simp
  with `l dvd d` and dab show "l dvd 1" by (auto intro: gcd_greatest)
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
  also have "normalisation_factor ((gcd a b)^n) = 1"
    by (simp add: normalisation_factor_pow A)
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
  with `?d \<noteq> 0` have "a' dvd b' * c" by simp
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
  from `?d \<noteq> 0` have zn: "?d ^ n \<noteq> 0" by (rule power_not_zero)
  from gcd_coprime_exists[OF `?d \<noteq> 0`]
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
  "lcm a b = a * b div (gcd a b * normalisation_factor (a*b))"
  by (simp only: lcm_lcm_eucl gcd_gcd_eucl lcm_eucl_def)

lemma lcm_gcd_prod:
  "lcm a b * gcd a b = a * b div normalisation_factor (a*b)"
proof (cases "a * b = 0")
  let ?nf = normalisation_factor
  assume "a * b \<noteq> 0"
  hence "gcd a b \<noteq> 0" by simp
  from lcm_gcd have "lcm a b * gcd a b = gcd a b * (a * b div (?nf (a*b) * gcd a b))" 
    by (simp add: mult_ac)
  also from `a * b \<noteq> 0` have "... = a * b div ?nf (a*b)"
    by (simp add: div_mult_swap mult.commute)
  finally show ?thesis .
qed (auto simp add: lcm_gcd)

lemma lcm_dvd1 [iff]:
  "a dvd lcm a b"
proof (cases "a*b = 0")
  assume "a * b \<noteq> 0"
  hence "gcd a b \<noteq> 0" by simp
  let ?c = "1 div normalisation_factor (a * b)"
  from `a * b \<noteq> 0` have [simp]: "is_unit (normalisation_factor (a * b))" by simp
  from lcm_gcd_prod[of a b] have "lcm a b * gcd a b = a * ?c * b"
    by (simp add: div_mult_swap unit_div_commute)
  hence "lcm a b * gcd a b div gcd a b = a * ?c * b div gcd a b" by simp
  with `gcd a b \<noteq> 0` have "lcm a b = a * ?c * b div gcd a b"
    by (subst (asm) div_mult_self2_is_id, simp_all)
  also have "... = a * (?c * b div gcd a b)"
    by (metis div_mult_swap gcd_dvd2 mult_assoc)
  finally show ?thesis by (rule dvdI)
qed (auto simp add: lcm_gcd)

lemma lcm_least:
  "\<lbrakk>a dvd k; b dvd k\<rbrakk> \<Longrightarrow> lcm a b dvd k"
proof (cases "k = 0")
  let ?nf = normalisation_factor
  assume "k \<noteq> 0"
  hence "is_unit (?nf k)" by simp
  hence "?nf k \<noteq> 0" by (metis not_is_unit_0)
  assume A: "a dvd k" "b dvd k"
  hence "gcd a b \<noteq> 0" using `k \<noteq> 0` by auto
  from A obtain r s where ar: "k = a * r" and bs: "k = b * s" 
    unfolding dvd_def by blast
  with `k \<noteq> 0` have "r * s \<noteq> 0"
    by auto (drule sym [of 0], simp)
  hence "is_unit (?nf (r * s))" by simp
  let ?c = "?nf k div ?nf (r*s)"
  from `is_unit (?nf k)` and `is_unit (?nf (r * s))` have "is_unit ?c" by (rule unit_div)
  hence "?c \<noteq> 0" using not_is_unit_0 by fast 
  from ar bs have "k * k * gcd s r = ?nf k * k * gcd (k * s) (k * r)"
    by (subst mult_assoc, subst gcd_mult_distrib[of k s r], simp only: ac_simps)
  also have "... = ?nf k * k * gcd ((r*s) * a) ((r*s) * b)"
    by (subst (3) `k = a * r`, subst (3) `k = b * s`, simp add: algebra_simps)
  also have "... = ?c * r*s * k * gcd a b" using `r * s \<noteq> 0`
    by (subst gcd_mult_distrib'[symmetric], simp add: algebra_simps unit_simps)
  finally have "(a*r) * (b*s) * gcd s r = ?c * k * r * s * gcd a b"
    by (subst ar[symmetric], subst bs[symmetric], simp add: mult_ac)
  hence "a * b * gcd s r * (r * s) = ?c * k * gcd a b * (r * s)"
    by (simp add: algebra_simps)
  hence "?c * k * gcd a b = a * b * gcd s r" using `r * s \<noteq> 0`
    by (metis div_mult_self2_is_id)
  also have "... = lcm a b * gcd a b * gcd s r * ?nf (a*b)"
    by (subst lcm_gcd_prod[of a b], metis gcd_mult_distrib gcd_mult_distrib') 
  also have "... = lcm a b * gcd s r * ?nf (a*b) * gcd a b"
    by (simp add: algebra_simps)
  finally have "k * ?c = lcm a b * gcd s r * ?nf (a*b)" using `gcd a b \<noteq> 0`
    by (metis mult.commute div_mult_self2_is_id)
  hence "k = lcm a b * (gcd s r * ?nf (a*b)) div ?c" using `?c \<noteq> 0`
    by (metis div_mult_self2_is_id mult_assoc) 
  also have "... = lcm a b * (gcd s r * ?nf (a*b) div ?c)" using `is_unit ?c`
    by (simp add: unit_simps)
  finally show ?thesis by (rule dvdI)
qed simp

lemma lcm_zero:
  "lcm a b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
proof -
  let ?nf = normalisation_factor
  {
    assume "a \<noteq> 0" "b \<noteq> 0"
    hence "a * b div ?nf (a * b) \<noteq> 0" by (simp add: no_zero_divisors)
    moreover from `a \<noteq> 0` and `b \<noteq> 0` have "gcd a b \<noteq> 0" by simp
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
  shows "gcd a b = a * b div (lcm a b * normalisation_factor (a * b))"
proof-
  from assms have "gcd a b \<noteq> 0" by (simp add: lcm_zero)
  let ?c = "normalisation_factor (a * b)"
  from `lcm a b \<noteq> 0` have "?c \<noteq> 0" by (intro notI, simp add: lcm_zero no_zero_divisors)
  hence "is_unit ?c" by simp
  from lcm_gcd_prod [of a b] have "gcd a b = a * b div ?c div lcm a b"
    by (subst (2) div_mult_self2_is_id[OF `lcm a b \<noteq> 0`, symmetric], simp add: mult_ac)
  also from `is_unit ?c` have "... = a * b div (lcm a b * ?c)"
    by (metis `?c \<noteq> 0` div_mult_mult1 dvd_mult_div_cancel mult_commute normalisation_factor_dvd')
  finally show ?thesis .
qed

lemma normalisation_factor_lcm [simp]:
  "normalisation_factor (lcm a b) = (if a = 0 \<or> b = 0 then 0 else 1)"
proof (cases "a = 0 \<or> b = 0")
  case True then show ?thesis
    by (auto simp add: lcm_gcd) 
next
  case False
  let ?nf = normalisation_factor
  from lcm_gcd_prod[of a b] 
    have "?nf (lcm a b) * ?nf (gcd a b) = ?nf (a*b) div ?nf (a*b)"
    by (metis div_by_0 div_self normalisation_correct normalisation_factor_0 normalisation_factor_mult)
  also have "... = (if a*b = 0 then 0 else 1)"
    by simp
  finally show ?thesis using False by simp
qed

lemma lcm_dvd2 [iff]: "b dvd lcm a b"
  using lcm_dvd1 [of b a] by (simp add: lcm_gcd ac_simps)

lemma lcmI:
  "\<lbrakk>a dvd k; b dvd k; \<And>l. a dvd l \<Longrightarrow> b dvd l \<Longrightarrow> k dvd l;
    normalisation_factor k = (if k = 0 then 0 else 1)\<rbrakk> \<Longrightarrow> k = lcm a b"
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
    from this and `lcm b c dvd l` have "b dvd l" by (rule dvd_trans)
    have "c dvd lcm b c" by simp
    from this and `lcm b c dvd l` have "c dvd l" by (rule dvd_trans)
    from `a dvd l` and `b dvd l` have "lcm a b dvd l" by (rule lcm_least)
    from this and `c dvd l` show "lcm (lcm a b) c dvd l" by (rule lcm_least)
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
  hence "lcm a b = normalisation_factor (lcm a b)"
    by (subst normalisation_factor_unit, simp_all)
  also have "\<dots> = 1" using `is_unit a \<and> is_unit b`
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
  normalisation_factor d = (if d = 0 then 0 else 1) \<and>
  (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  by (rule, auto intro: lcmI simp: lcm_least lcm_zero)

lemma dvd_lcm_I1 [simp]:
  "k dvd m \<Longrightarrow> k dvd lcm m n"
  by (metis lcm_dvd1 dvd_trans)

lemma dvd_lcm_I2 [simp]:
  "k dvd n \<Longrightarrow> k dvd lcm m n"
  by (metis lcm_dvd2 dvd_trans)

lemma lcm_1_left [simp]:
  "lcm 1 a = a div normalisation_factor a"
  by (cases "a = 0") (simp, rule sym, rule lcmI, simp_all)

lemma lcm_1_right [simp]:
  "lcm a 1 = a div normalisation_factor a"
  using lcm_1_left [of a] by (simp add: ac_simps)

lemma lcm_coprime:
  "gcd a b = 1 \<Longrightarrow> lcm a b = a * b div normalisation_factor (a*b)"
  by (subst lcm_gcd) simp

lemma lcm_proj1_if_dvd: 
  "b dvd a \<Longrightarrow> lcm a b = a div normalisation_factor a"
  by (cases "a = 0") (simp, rule sym, rule lcmI, simp_all)

lemma lcm_proj2_if_dvd: 
  "a dvd b \<Longrightarrow> lcm a b = b div normalisation_factor b"
  using lcm_proj1_if_dvd [of a b] by (simp add: ac_simps)

lemma lcm_proj1_iff:
  "lcm m n = m div normalisation_factor m \<longleftrightarrow> n dvd m"
proof
  assume A: "lcm m n = m div normalisation_factor m"
  show "n dvd m"
  proof (cases "m = 0")
    assume [simp]: "m \<noteq> 0"
    from A have B: "m = lcm m n * normalisation_factor m"
      by (simp add: unit_eq_div2)
    show ?thesis by (subst B, simp)
  qed simp
next
  assume "n dvd m"
  then show "lcm m n = m div normalisation_factor m" by (rule lcm_proj1_if_dvd)
qed

lemma lcm_proj2_iff:
  "lcm m n = n div normalisation_factor n \<longleftrightarrow> m dvd n"
  using lcm_proj1_iff [of n m] by (simp add: ac_simps)

lemma euclidean_size_lcm_le1: 
  assumes "a \<noteq> 0" and "b \<noteq> 0"
  shows "euclidean_size a \<le> euclidean_size (lcm a b)"
proof -
  have "a dvd lcm a b" by (rule lcm_dvd1)
  then obtain c where A: "lcm a b = a * c" unfolding dvd_def by blast
  with `a \<noteq> 0` and `b \<noteq> 0` have "c \<noteq> 0" by (auto simp: lcm_zero)
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
  with `a \<noteq> 0` and `b \<noteq> 0` have "euclidean_size (lcm a b) = euclidean_size a"
    by (intro le_antisym, simp, intro euclidean_size_lcm_le1)
  with assms have "lcm a b dvd a" 
    by (rule_tac dvd_euclidean_size_eq_imp_dvd) (auto simp: lcm_zero)
  hence "b dvd a" by (rule dvd_lcm_D2)
  with `\<not>b dvd a` show False by contradiction
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
  apply (subst normalisation_factor_lcm, simp add: lcm_zero)
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
  and normalisation_factor_Lcm [simp]: 
          "normalisation_factor (Lcm A) = (if Lcm A = 0 then 0 else 1)"
proof -
  have "(\<forall>a\<in>A. a dvd Lcm A) \<and> (\<forall>l'. (\<forall>a\<in>A. a dvd l') \<longrightarrow> Lcm A dvd l') \<and>
    normalisation_factor (Lcm A) = (if Lcm A = 0 then 0 else 1)" (is ?thesis)
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
      with `\<forall>a\<in>A. a dvd l` have "\<forall>a\<in>A. a dvd gcd l l'" by (auto intro: gcd_greatest)
      moreover from `l \<noteq> 0` have "gcd l l' \<noteq> 0" by simp
      ultimately have "\<exists>b. b \<noteq> 0 \<and> (\<forall>a\<in>A. a dvd b) \<and> euclidean_size b = euclidean_size (gcd l l')"
        by (intro exI[of _ "gcd l l'"], auto)
      hence "euclidean_size (gcd l l') \<ge> n" by (subst n_def) (rule Least_le)
      moreover have "euclidean_size (gcd l l') \<le> n"
      proof -
        have "gcd l l' dvd l" by simp
        then obtain a where "l = gcd l l' * a" unfolding dvd_def by blast
        with `l \<noteq> 0` have "a \<noteq> 0" by auto
        hence "euclidean_size (gcd l l') \<le> euclidean_size (gcd l l' * a)"
          by (rule size_mult_mono)
        also have "gcd l l' * a = l" using `l = gcd l l' * a` ..
        also note `euclidean_size l = n`
        finally show "euclidean_size (gcd l l') \<le> n" .
      qed
      ultimately have "euclidean_size l = euclidean_size (gcd l l')" 
        by (intro le_antisym, simp_all add: `euclidean_size l = n`)
      with `l \<noteq> 0` have "l dvd gcd l l'" by (blast intro: dvd_euclidean_size_eq_imp_dvd)
      hence "l dvd l'" by (blast dest: dvd_gcd_D2)
    }

    with `(\<forall>a\<in>A. a dvd l)` and normalisation_factor_is_unit[OF `l \<noteq> 0`] and `l \<noteq> 0`
      have "(\<forall>a\<in>A. a dvd l div normalisation_factor l) \<and> 
        (\<forall>l'. (\<forall>a\<in>A. a dvd l') \<longrightarrow> l div normalisation_factor l dvd l') \<and>
        normalisation_factor (l div normalisation_factor l) = 
        (if l div normalisation_factor l = 0 then 0 else 1)"
      by (auto simp: unit_simps)
    also from True have "l div normalisation_factor l = Lcm A"
      by (simp add: Lcm_Lcm_eucl Lcm_eucl_def Let_def n_def l_def)
    finally show ?thesis .
  qed
  note A = this

  {fix a assume "a \<in> A" then show "a dvd Lcm A" using A by blast}
  {fix l' assume "\<forall>a\<in>A. a dvd l'" then show "Lcm A dvd l'" using A by blast}
  from A show "normalisation_factor (Lcm A) = (if Lcm A = 0 then 0 else 1)" by blast
qed
    
lemma LcmI:
  "(\<And>a. a\<in>A \<Longrightarrow> a dvd l) \<Longrightarrow> (\<And>l'. (\<forall>a\<in>A. a dvd l') \<Longrightarrow> l dvd l') \<Longrightarrow>
      normalisation_factor l = (if l = 0 then 0 else 1) \<Longrightarrow> l = Lcm A"
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
    hence "l div normalisation_factor l \<noteq> 0" by simp
    also from ex have "l div normalisation_factor l = Lcm A"
       by (simp only: Lcm_Lcm_eucl Lcm_eucl_def n_def l_def if_True Let_def)
    finally show False using `Lcm A = 0` by contradiction
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
      apply (induct rule: finite_induct[OF `finite A`]) 
      apply simp
      apply (subst setprod.insert, assumption, assumption)
      apply (rule no_zero_divisors)
      apply blast+
      done
    moreover from `finite A` have "\<forall>a\<in>A. a dvd \<Prod>A" by blast
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
  with `a dvd l` show "Lcm (insert a A) dvd l" by (force intro: Lcm_dvd)
qed (auto intro: Lcm_dvd dvd_Lcm)
 
lemma Lcm_finite:
  assumes "finite A"
  shows "Lcm A = Finite_Set.fold lcm 1 A"
  by (induct rule: finite.induct[OF `finite A`])
    (simp_all add: comp_fun_idem.fold_insert_idem[OF comp_fun_idem_lcm])

lemma Lcm_set [code_unfold]:
  "Lcm (set xs) = fold lcm xs 1"
  using comp_fun_idem.fold_set_fold[OF comp_fun_idem_lcm] Lcm_finite by (simp add: ac_simps)

lemma Lcm_singleton [simp]:
  "Lcm {a} = a div normalisation_factor a"
  by simp

lemma Lcm_2 [simp]:
  "Lcm {a,b} = lcm a b"
  by (simp only: Lcm_insert Lcm_empty lcm_1_right)
    (cases "b = 0", simp, rule lcm_div_unit2, simp)

lemma Lcm_coprime:
  assumes "finite A" and "A \<noteq> {}" 
  assumes "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> gcd a b = 1"
  shows "Lcm A = \<Prod>A div normalisation_factor (\<Prod>A)"
using assms proof (induct rule: finite_ne_induct)
  case (insert a A)
  have "Lcm (insert a A) = lcm a (Lcm A)" by simp
  also from insert have "Lcm A = \<Prod>A div normalisation_factor (\<Prod>A)" by blast
  also have "lcm a \<dots> = lcm a (\<Prod>A)" by (cases "\<Prod>A = 0") (simp_all add: lcm_div_unit2)
  also from insert have "gcd a (\<Prod>A) = 1" by (subst gcd.commute, intro setprod_coprime) auto
  with insert have "lcm a (\<Prod>A) = \<Prod>(insert a A) div normalisation_factor (\<Prod>(insert a A))"
    by (simp add: lcm_coprime)
  finally show ?case .
qed simp
      
lemma Lcm_coprime':
  "card A \<noteq> 0 \<Longrightarrow> (\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> gcd a b = 1)
    \<Longrightarrow> Lcm A = \<Prod>A div normalisation_factor (\<Prod>A)"
  by (rule Lcm_coprime) (simp_all add: card_eq_0_iff)

lemma Gcd_Lcm:
  "Gcd A = Lcm {d. \<forall>a\<in>A. d dvd a}"
  by (simp add: Gcd_Gcd_eucl Lcm_Lcm_eucl Gcd_eucl_def)

lemma Gcd_dvd [simp]: "a \<in> A \<Longrightarrow> Gcd A dvd a"
  and dvd_Gcd [simp]: "(\<forall>a\<in>A. g' dvd a) \<Longrightarrow> g' dvd Gcd A"
  and normalisation_factor_Gcd [simp]: 
    "normalisation_factor (Gcd A) = (if Gcd A = 0 then 0 else 1)"
proof -
  fix a assume "a \<in> A"
  hence "Lcm {d. \<forall>a\<in>A. d dvd a} dvd a" by (intro Lcm_dvd) blast
  then show "Gcd A dvd a" by (simp add: Gcd_Lcm)
next
  fix g' assume "\<forall>a\<in>A. g' dvd a"
  hence "g' dvd Lcm {d. \<forall>a\<in>A. d dvd a}" by (intro dvd_Lcm) blast
  then show "g' dvd Gcd A" by (simp add: Gcd_Lcm)
next
  show "normalisation_factor (Gcd A) = (if Gcd A = 0 then 0 else 1)"
    by (simp add: Gcd_Lcm)
qed

lemma GcdI:
  "(\<And>a. a\<in>A \<Longrightarrow> l dvd a) \<Longrightarrow> (\<And>l'. (\<forall>a\<in>A. l' dvd a) \<Longrightarrow> l' dvd l) \<Longrightarrow>
    normalisation_factor l = (if l = 0 then 0 else 1) \<Longrightarrow> l = Gcd A"
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
  with `l dvd a` show "l dvd Gcd (insert a A)" by (force intro: Gcd_dvd)
qed auto

lemma Gcd_finite:
  assumes "finite A"
  shows "Gcd A = Finite_Set.fold gcd 0 A"
  by (induct rule: finite.induct[OF `finite A`])
    (simp_all add: comp_fun_idem.fold_insert_idem[OF comp_fun_idem_gcd])

lemma Gcd_set [code_unfold]:
  "Gcd (set xs) = fold gcd xs 0"
  using comp_fun_idem.fold_set_fold[OF comp_fun_idem_gcd] Gcd_finite by (simp add: ac_simps)

lemma Gcd_singleton [simp]: "Gcd {a} = a div normalisation_factor a"
  by (simp add: gcd_0)

lemma Gcd_2 [simp]: "Gcd {a,b} = gcd a b"
  by (simp only: Gcd_insert Gcd_empty gcd_0) (cases "b = 0", simp, rule gcd_div_unit2, simp)

end

text {*
  A Euclidean ring is a Euclidean semiring with additive inverses. It provides a 
  few more lemmas; in particular, Bezout's lemma holds for any Euclidean ring.
*}

class euclidean_ring = euclidean_semiring + idom

class euclidean_ring_gcd = euclidean_semiring_gcd + idom
begin

subclass euclidean_ring ..

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

function euclid_ext :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a" where
  "euclid_ext a b = 
     (if b = 0 then 
        let c = 1 div normalisation_factor a in (c, 0, a * c)
      else 
        case euclid_ext b (a mod b) of
            (s,t,c) \<Rightarrow> (t, s - t * (a div b), c))"
  by (pat_completeness, simp)
  termination by (relation "measure (euclidean_size \<circ> snd)", simp_all)

declare euclid_ext.simps [simp del]

lemma euclid_ext_0: 
  "euclid_ext a 0 = (1 div normalisation_factor a, 0, a div normalisation_factor a)"
  by (subst euclid_ext.simps) (simp add: Let_def)

lemma euclid_ext_non_0:
  "b \<noteq> 0 \<Longrightarrow> euclid_ext a b = (case euclid_ext b (a mod b) of 
    (s,t,c) \<Rightarrow> (t, s - t * (a div b), c))"
  by (subst euclid_ext.simps) simp

definition euclid_ext' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a"
where
  "euclid_ext' a b = (case euclid_ext a b of (s, t, _) \<Rightarrow> (s, t))"

lemma euclid_ext_gcd [simp]:
  "(case euclid_ext a b of (_,_,t) \<Rightarrow> t) = gcd a b"
proof (induct a b rule: euclid_ext.induct)
  case (1 a b)
  then show ?case
  proof (cases "b = 0")
    case True
      then show ?thesis by  
        (simp add: euclid_ext_0 unit_div mult_ac unit_simps gcd_0)
    next
    case False with 1 show ?thesis
      by (simp add: euclid_ext_non_0 ac_simps split: prod.split prod.split_asm)
    qed
qed

lemma euclid_ext_gcd' [simp]:
  "euclid_ext a b = (r, s, t) \<Longrightarrow> t = gcd a b"
  by (insert euclid_ext_gcd[of a b], drule (1) subst, simp)

lemma euclid_ext_correct:
  "case euclid_ext a b of (s,t,c) \<Rightarrow> s*a + t*b = c"
proof (induct a b rule: euclid_ext.induct)
  case (1 a b)
  show ?case
  proof (cases "b = 0")
    case True
    then show ?thesis by (simp add: euclid_ext_0 mult_ac)
  next
    case False
    obtain s t c where stc: "euclid_ext b (a mod b) = (s,t,c)"
      by (cases "euclid_ext b (a mod b)", blast)
    from 1 have "c = s * b + t * (a mod b)" by (simp add: stc False)
    also have "... = t*((a div b)*b + a mod b) + (s - t * (a div b))*b"
      by (simp add: algebra_simps) 
    also have "(a div b)*b + a mod b = a" using mod_div_equality .
    finally show ?thesis
      by (subst euclid_ext.simps, simp add: False stc)
    qed
qed

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

lemma euclid_ext'_0 [simp]: "euclid_ext' a 0 = (1 div normalisation_factor a, 0)" 
  by (simp add: bezw_def euclid_ext'_def euclid_ext_0)

lemma euclid_ext'_non_0: "b \<noteq> 0 \<Longrightarrow> euclid_ext' a b = (snd (euclid_ext' b (a mod b)),
  fst (euclid_ext' b (a mod b)) - snd (euclid_ext' b (a mod b)) * (a div b))"
  by (cases "euclid_ext b (a mod b)") 
    (simp add: euclid_ext'_def euclid_ext_non_0)
  
end

instantiation nat :: euclidean_semiring
begin

definition [simp]:
  "euclidean_size_nat = (id :: nat \<Rightarrow> nat)"

definition [simp]:
  "normalisation_factor_nat (n::nat) = (if n = 0 then 0 else 1 :: nat)"

instance proof
qed simp_all

end

instantiation int :: euclidean_ring
begin

definition [simp]:
  "euclidean_size_int = (nat \<circ> abs :: int \<Rightarrow> nat)"

definition [simp]:
  "normalisation_factor_int = (sgn :: int \<Rightarrow> int)"

instance proof
  case goal2 then show ?case by (auto simp add: abs_mult nat_mult_distrib)
next
  case goal3 then show ?case by (simp add: zsgn_def)
next
  case goal5 then show ?case by (auto simp: zsgn_def)
next
  case goal6 then show ?case by (auto split: abs_split simp: zsgn_def)
qed (auto simp: sgn_times split: abs_split)

end

end
