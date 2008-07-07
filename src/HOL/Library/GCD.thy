(*  Title:      HOL/GCD.thy
    ID:         $Id$
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge
*)

header {* The Greatest Common Divisor *}

theory GCD
imports Plain "~~/src/HOL/Presburger"
begin

text {*
  See \cite{davenport92}. \bigskip
*}

subsection {* Specification of GCD on nats *}

definition
  is_gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where -- {* @{term gcd} as a relation *}
  [code func del]: "is_gcd p m n \<longleftrightarrow> p dvd m \<and> p dvd n \<and>
    (\<forall>d. d dvd m \<longrightarrow> d dvd n \<longrightarrow> d dvd p)"

text {* Uniqueness *}

lemma is_gcd_unique: "is_gcd m a b \<Longrightarrow> is_gcd n a b \<Longrightarrow> m = n"
  by (simp add: is_gcd_def) (blast intro: dvd_anti_sym)

text {* Connection to divides relation *}

lemma is_gcd_dvd: "is_gcd m a b \<Longrightarrow> k dvd a \<Longrightarrow> k dvd b \<Longrightarrow> k dvd m"
  by (auto simp add: is_gcd_def)

text {* Commutativity *}

lemma is_gcd_commute: "is_gcd k m n = is_gcd k n m"
  by (auto simp add: is_gcd_def)


subsection {* GCD on nat by Euclid's algorithm *}

fun
  gcd  :: "nat \<times> nat => nat"
where
  "gcd (m, n) = (if n = 0 then m else gcd (n, m mod n))"

lemma gcd_induct:
  fixes m n :: nat
  assumes "\<And>m. P m 0"
    and "\<And>m n. 0 < n \<Longrightarrow> P n (m mod n) \<Longrightarrow> P m n"
  shows "P m n"
apply (rule gcd.induct [of "split P" "(m, n)", unfolded Product_Type.split])
apply (case_tac "n = 0")
apply simp_all
using assms apply simp_all
done

lemma gcd_0 [simp]: "gcd (m, 0) = m"
  by simp

lemma gcd_0_left [simp]: "gcd (0, m) = m"
  by simp

lemma gcd_non_0: "n > 0 \<Longrightarrow> gcd (m, n) = gcd (n, m mod n)"
  by simp

lemma gcd_1 [simp]: "gcd (m, Suc 0) = 1"
  by simp

declare gcd.simps [simp del]

text {*
  \medskip @{term "gcd (m, n)"} divides @{text m} and @{text n}.  The
  conjunctions don't seem provable separately.
*}

lemma gcd_dvd1 [iff]: "gcd (m, n) dvd m"
  and gcd_dvd2 [iff]: "gcd (m, n) dvd n"
  apply (induct m n rule: gcd_induct)
     apply (simp_all add: gcd_non_0)
  apply (blast dest: dvd_mod_imp_dvd)
  done

text {*
  \medskip Maximality: for all @{term m}, @{term n}, @{term k}
  naturals, if @{term k} divides @{term m} and @{term k} divides
  @{term n} then @{term k} divides @{term "gcd (m, n)"}.
*}

lemma gcd_greatest: "k dvd m \<Longrightarrow> k dvd n \<Longrightarrow> k dvd gcd (m, n)"
  by (induct m n rule: gcd_induct) (simp_all add: gcd_non_0 dvd_mod)

text {*
  \medskip Function gcd yields the Greatest Common Divisor.
*}

lemma is_gcd: "is_gcd (gcd (m, n)) m n"
  by (simp add: is_gcd_def gcd_greatest)


subsection {* Derived laws for GCD *}

lemma gcd_greatest_iff [iff]: "k dvd gcd (m, n) \<longleftrightarrow> k dvd m \<and> k dvd n"
  by (blast intro!: gcd_greatest intro: dvd_trans)

lemma gcd_zero: "gcd (m, n) = 0 \<longleftrightarrow> m = 0 \<and> n = 0"
  by (simp only: dvd_0_left_iff [symmetric] gcd_greatest_iff)

lemma gcd_commute: "gcd (m, n) = gcd (n, m)"
  apply (rule is_gcd_unique)
   apply (rule is_gcd)
  apply (subst is_gcd_commute)
  apply (simp add: is_gcd)
  done

lemma gcd_assoc: "gcd (gcd (k, m), n) = gcd (k, gcd (m, n))"
  apply (rule is_gcd_unique)
   apply (rule is_gcd)
  apply (simp add: is_gcd_def)
  apply (blast intro: dvd_trans)
  done

lemma gcd_1_left [simp]: "gcd (Suc 0, m) = 1"
  by (simp add: gcd_commute)

text {*
  \medskip Multiplication laws
*}

lemma gcd_mult_distrib2: "k * gcd (m, n) = gcd (k * m, k * n)"
    -- {* \cite[page 27]{davenport92} *}
  apply (induct m n rule: gcd_induct)
   apply simp
  apply (case_tac "k = 0")
   apply (simp_all add: mod_geq gcd_non_0 mod_mult_distrib2)
  done

lemma gcd_mult [simp]: "gcd (k, k * n) = k"
  apply (rule gcd_mult_distrib2 [of k 1 n, simplified, symmetric])
  done

lemma gcd_self [simp]: "gcd (k, k) = k"
  apply (rule gcd_mult [of k 1, simplified])
  done

lemma relprime_dvd_mult: "gcd (k, n) = 1 ==> k dvd m * n ==> k dvd m"
  apply (insert gcd_mult_distrib2 [of m k n])
  apply simp
  apply (erule_tac t = m in ssubst)
  apply simp
  done

lemma relprime_dvd_mult_iff: "gcd (k, n) = 1 ==> (k dvd m * n) = (k dvd m)"
  apply (blast intro: relprime_dvd_mult dvd_trans)
  done

lemma gcd_mult_cancel: "gcd (k, n) = 1 ==> gcd (k * m, n) = gcd (m, n)"
  apply (rule dvd_anti_sym)
   apply (rule gcd_greatest)
    apply (rule_tac n = k in relprime_dvd_mult)
     apply (simp add: gcd_assoc)
     apply (simp add: gcd_commute)
    apply (simp_all add: mult_commute)
  apply (blast intro: dvd_trans)
  done


text {* \medskip Addition laws *}

lemma gcd_add1 [simp]: "gcd (m + n, n) = gcd (m, n)"
  apply (case_tac "n = 0")
   apply (simp_all add: gcd_non_0)
  done

lemma gcd_add2 [simp]: "gcd (m, m + n) = gcd (m, n)"
proof -
  have "gcd (m, m + n) = gcd (m + n, m)" by (rule gcd_commute)
  also have "... = gcd (n + m, m)" by (simp add: add_commute)
  also have "... = gcd (n, m)" by simp
  also have  "... = gcd (m, n)" by (rule gcd_commute)
  finally show ?thesis .
qed

lemma gcd_add2' [simp]: "gcd (m, n + m) = gcd (m, n)"
  apply (subst add_commute)
  apply (rule gcd_add2)
  done

lemma gcd_add_mult: "gcd (m, k * m + n) = gcd (m, n)"
  by (induct k) (simp_all add: add_assoc)

lemma gcd_dvd_prod: "gcd (m, n) dvd m * n"
  using mult_dvd_mono [of 1] by auto

text {*
  \medskip Division by gcd yields rrelatively primes.
*}

lemma div_gcd_relprime:
  assumes nz: "a \<noteq> 0 \<or> b \<noteq> 0"
  shows "gcd (a div gcd(a,b), b div gcd(a,b)) = 1"
proof -
  let ?g = "gcd (a, b)"
  let ?a' = "a div ?g"
  let ?b' = "b div ?g"
  let ?g' = "gcd (?a', ?b')"
  have dvdg: "?g dvd a" "?g dvd b" by simp_all
  have dvdg': "?g' dvd ?a'" "?g' dvd ?b'" by simp_all
  from dvdg dvdg' obtain ka kb ka' kb' where
      kab: "a = ?g * ka" "b = ?g * kb" "?a' = ?g' * ka'" "?b' = ?g' * kb'"
    unfolding dvd_def by blast
  then have "?g * ?a' = (?g * ?g') * ka'" "?g * ?b' = (?g * ?g') * kb'" by simp_all
  then have dvdgg':"?g * ?g' dvd a" "?g* ?g' dvd b"
    by (auto simp add: dvd_mult_div_cancel [OF dvdg(1)]
      dvd_mult_div_cancel [OF dvdg(2)] dvd_def)
  have "?g \<noteq> 0" using nz by (simp add: gcd_zero)
  then have gp: "?g > 0" by simp
  from gcd_greatest [OF dvdgg'] have "?g * ?g' dvd ?g" .
  with dvd_mult_cancel1 [OF gp] show "?g' = 1" by simp
qed

subsection {* LCM defined by GCD *}

definition
  lcm :: "nat \<times> nat \<Rightarrow> nat"
where
  lcm_prim_def: "lcm = (\<lambda>(m, n). m * n div gcd (m, n))"

lemma lcm_def:
  "lcm (m, n) = m * n div gcd (m, n)"
  unfolding lcm_prim_def by simp

lemma prod_gcd_lcm:
  "m * n = gcd (m, n) * lcm (m, n)"
  unfolding lcm_def by (simp add: dvd_mult_div_cancel [OF gcd_dvd_prod])

lemma lcm_0 [simp]: "lcm (m, 0) = 0"
  unfolding lcm_def by simp

lemma lcm_1 [simp]: "lcm (m, 1) = m"
  unfolding lcm_def by simp

lemma lcm_0_left [simp]: "lcm (0, n) = 0"
  unfolding lcm_def by simp

lemma lcm_1_left [simp]: "lcm (1, m) = m"
  unfolding lcm_def by simp

lemma dvd_pos:
  fixes n m :: nat
  assumes "n > 0" and "m dvd n"
  shows "m > 0"
using assms by (cases m) auto

lemma lcm_least:
  assumes "m dvd k" and "n dvd k"
  shows "lcm (m, n) dvd k"
proof (cases k)
  case 0 then show ?thesis by auto
next
  case (Suc _) then have pos_k: "k > 0" by auto
  from assms dvd_pos [OF this] have pos_mn: "m > 0" "n > 0" by auto
  with gcd_zero [of m n] have pos_gcd: "gcd (m, n) > 0" by simp
  from assms obtain p where k_m: "k = m * p" using dvd_def by blast
  from assms obtain q where k_n: "k = n * q" using dvd_def by blast
  from pos_k k_m have pos_p: "p > 0" by auto
  from pos_k k_n have pos_q: "q > 0" by auto
  have "k * k * gcd (q, p) = k * gcd (k * q, k * p)"
    by (simp add: mult_ac gcd_mult_distrib2)
  also have "\<dots> = k * gcd (m * p * q, n * q * p)"
    by (simp add: k_m [symmetric] k_n [symmetric])
  also have "\<dots> = k * p * q * gcd (m, n)"
    by (simp add: mult_ac gcd_mult_distrib2)
  finally have "(m * p) * (n * q) * gcd (q, p) = k * p * q * gcd (m, n)"
    by (simp only: k_m [symmetric] k_n [symmetric])
  then have "p * q * m * n * gcd (q, p) = p * q * k * gcd (m, n)"
    by (simp add: mult_ac)
  with pos_p pos_q have "m * n * gcd (q, p) = k * gcd (m, n)"
    by simp
  with prod_gcd_lcm [of m n]
  have "lcm (m, n) * gcd (q, p) * gcd (m, n) = k * gcd (m, n)"
    by (simp add: mult_ac)
  with pos_gcd have "lcm (m, n) * gcd (q, p) = k" by simp
  then show ?thesis using dvd_def by auto
qed

lemma lcm_dvd1 [iff]:
  "m dvd lcm (m, n)"
proof (cases m)
  case 0 then show ?thesis by simp
next
  case (Suc _)
  then have mpos: "m > 0" by simp
  show ?thesis
  proof (cases n)
    case 0 then show ?thesis by simp
  next
    case (Suc _)
    then have npos: "n > 0" by simp
    have "gcd (m, n) dvd n" by simp
    then obtain k where "n = gcd (m, n) * k" using dvd_def by auto
    then have "m * n div gcd (m, n) = m * (gcd (m, n) * k) div gcd (m, n)" by (simp add: mult_ac)
    also have "\<dots> = m * k" using mpos npos gcd_zero by simp
    finally show ?thesis by (simp add: lcm_def)
  qed
qed

lemma lcm_dvd2 [iff]: 
  "n dvd lcm (m, n)"
proof (cases n)
  case 0 then show ?thesis by simp
next
  case (Suc _)
  then have npos: "n > 0" by simp
  show ?thesis
  proof (cases m)
    case 0 then show ?thesis by simp
  next
    case (Suc _)
    then have mpos: "m > 0" by simp
    have "gcd (m, n) dvd m" by simp
    then obtain k where "m = gcd (m, n) * k" using dvd_def by auto
    then have "m * n div gcd (m, n) = (gcd (m, n) * k) * n div gcd (m, n)" by (simp add: mult_ac)
    also have "\<dots> = n * k" using mpos npos gcd_zero by simp
    finally show ?thesis by (simp add: lcm_def)
  qed
qed


subsection {* GCD and LCM on integers *}

definition
  igcd :: "int \<Rightarrow> int \<Rightarrow> int" where
  "igcd i j = int (gcd (nat (abs i), nat (abs j)))"

lemma igcd_dvd1 [simp]: "igcd i j dvd i"
  by (simp add: igcd_def int_dvd_iff)

lemma igcd_dvd2 [simp]: "igcd i j dvd j"
  by (simp add: igcd_def int_dvd_iff)

lemma igcd_pos: "igcd i j \<ge> 0"
  by (simp add: igcd_def)

lemma igcd0 [simp]: "(igcd i j = 0) = (i = 0 \<and> j = 0)"
  by (simp add: igcd_def gcd_zero) arith

lemma igcd_commute: "igcd i j = igcd j i"
  unfolding igcd_def by (simp add: gcd_commute)

lemma igcd_neg1 [simp]: "igcd (- i) j = igcd i j"
  unfolding igcd_def by simp

lemma igcd_neg2 [simp]: "igcd i (- j) = igcd i j"
  unfolding igcd_def by simp

lemma zrelprime_dvd_mult: "igcd i j = 1 \<Longrightarrow> i dvd k * j \<Longrightarrow> i dvd k"
  unfolding igcd_def
proof -
  assume "int (gcd (nat \<bar>i\<bar>, nat \<bar>j\<bar>)) = 1" "i dvd k * j"
  then have g: "gcd (nat \<bar>i\<bar>, nat \<bar>j\<bar>) = 1" by simp
  from `i dvd k * j` obtain h where h: "k*j = i*h" unfolding dvd_def by blast
  have th: "nat \<bar>i\<bar> dvd nat \<bar>k\<bar> * nat \<bar>j\<bar>"
    unfolding dvd_def
    by (rule_tac x= "nat \<bar>h\<bar>" in exI, simp add: h nat_abs_mult_distrib [symmetric])
  from relprime_dvd_mult [OF g th] obtain h' where h': "nat \<bar>k\<bar> = nat \<bar>i\<bar> * h'"
    unfolding dvd_def by blast
  from h' have "int (nat \<bar>k\<bar>) = int (nat \<bar>i\<bar> * h')" by simp
  then have "\<bar>k\<bar> = \<bar>i\<bar> * int h'" by (simp add: int_mult)
  then show ?thesis
    apply (subst zdvd_abs1 [symmetric])
    apply (subst zdvd_abs2 [symmetric])
    apply (unfold dvd_def)
    apply (rule_tac x = "int h'" in exI, simp)
    done
qed

lemma int_nat_abs: "int (nat (abs x)) = abs x"  by arith

lemma igcd_greatest:
  assumes "k dvd m" and "k dvd n"
  shows "k dvd igcd m n"
proof -
  let ?k' = "nat \<bar>k\<bar>"
  let ?m' = "nat \<bar>m\<bar>"
  let ?n' = "nat \<bar>n\<bar>"
  from `k dvd m` and `k dvd n` have dvd': "?k' dvd ?m'" "?k' dvd ?n'"
    unfolding zdvd_int by (simp_all only: int_nat_abs zdvd_abs1 zdvd_abs2)
  from gcd_greatest [OF dvd'] have "int (nat \<bar>k\<bar>) dvd igcd m n"
    unfolding igcd_def by (simp only: zdvd_int)
  then have "\<bar>k\<bar> dvd igcd m n" by (simp only: int_nat_abs)
  then show "k dvd igcd m n" by (simp add: zdvd_abs1)
qed

lemma div_igcd_relprime:
  assumes nz: "a \<noteq> 0 \<or> b \<noteq> 0"
  shows "igcd (a div (igcd a b)) (b div (igcd a b)) = 1"
proof -
  from nz have nz': "nat \<bar>a\<bar> \<noteq> 0 \<or> nat \<bar>b\<bar> \<noteq> 0" by arith 
  let ?g = "igcd a b"
  let ?a' = "a div ?g"
  let ?b' = "b div ?g"
  let ?g' = "igcd ?a' ?b'"
  have dvdg: "?g dvd a" "?g dvd b" by (simp_all add: igcd_dvd1 igcd_dvd2)
  have dvdg': "?g' dvd ?a'" "?g' dvd ?b'" by (simp_all add: igcd_dvd1 igcd_dvd2)
  from dvdg dvdg' obtain ka kb ka' kb' where
   kab: "a = ?g*ka" "b = ?g*kb" "?a' = ?g'*ka'" "?b' = ?g' * kb'"
    unfolding dvd_def by blast
  then have "?g* ?a' = (?g * ?g') * ka'" "?g* ?b' = (?g * ?g') * kb'" by simp_all
  then have dvdgg':"?g * ?g' dvd a" "?g* ?g' dvd b"
    by (auto simp add: zdvd_mult_div_cancel [OF dvdg(1)]
      zdvd_mult_div_cancel [OF dvdg(2)] dvd_def)
  have "?g \<noteq> 0" using nz by simp
  then have gp: "?g \<noteq> 0" using igcd_pos[where i="a" and j="b"] by arith
  from igcd_greatest [OF dvdgg'] have "?g * ?g' dvd ?g" .
  with zdvd_mult_cancel1 [OF gp] have "\<bar>?g'\<bar> = 1" by simp
  with igcd_pos show "?g' = 1" by simp
qed

definition "ilcm = (\<lambda>i j. int (lcm(nat(abs i),nat(abs j))))"

lemma dvd_ilcm_self1[simp]: "i dvd ilcm i j"
by(simp add:ilcm_def dvd_int_iff)

lemma dvd_ilcm_self2[simp]: "j dvd ilcm i j"
by(simp add:ilcm_def dvd_int_iff)


lemma dvd_imp_dvd_ilcm1:
  assumes "k dvd i" shows "k dvd (ilcm i j)"
proof -
  have "nat(abs k) dvd nat(abs i)" using `k dvd i`
    by(simp add:int_dvd_iff[symmetric] dvd_int_iff[symmetric] zdvd_abs1)
  thus ?thesis by(simp add:ilcm_def dvd_int_iff)(blast intro: dvd_trans)
qed

lemma dvd_imp_dvd_ilcm2:
  assumes "k dvd j" shows "k dvd (ilcm i j)"
proof -
  have "nat(abs k) dvd nat(abs j)" using `k dvd j`
    by(simp add:int_dvd_iff[symmetric] dvd_int_iff[symmetric] zdvd_abs1)
  thus ?thesis by(simp add:ilcm_def dvd_int_iff)(blast intro: dvd_trans)
qed


lemma zdvd_self_abs1: "(d::int) dvd (abs d)"
by (case_tac "d <0", simp_all)

lemma zdvd_self_abs2: "(abs (d::int)) dvd d"
by (case_tac "d<0", simp_all)

(* lcm a b is positive for positive a and b *)

lemma lcm_pos: 
  assumes mpos: "m > 0"
  and npos: "n>0"
  shows "lcm (m,n) > 0"
proof(rule ccontr, simp add: lcm_def gcd_zero)
assume h:"m*n div gcd(m,n) = 0"
from mpos npos have "gcd (m,n) \<noteq> 0" using gcd_zero by simp
hence gcdp: "gcd(m,n) > 0" by simp
with h
have "m*n < gcd(m,n)"
  by (cases "m * n < gcd (m, n)") (auto simp add: div_if[OF gcdp, where m="m*n"])
moreover 
have "gcd(m,n) dvd m" by simp
 with mpos dvd_imp_le have t1:"gcd(m,n) \<le> m" by simp
 with npos have t1:"gcd(m,n)*n \<le> m*n" by simp
 have "gcd(m,n) \<le> gcd(m,n)*n" using npos by simp
 with t1 have "gcd(m,n) \<le> m*n" by arith
ultimately show "False" by simp
qed

lemma ilcm_pos: 
  assumes anz: "a \<noteq> 0"
  and bnz: "b \<noteq> 0" 
  shows "0 < ilcm a b"
proof-
  let ?na = "nat (abs a)"
  let ?nb = "nat (abs b)"
  have nap: "?na >0" using anz by simp
  have nbp: "?nb >0" using bnz by simp
  have "0 < lcm (?na,?nb)" by (rule lcm_pos[OF nap nbp])
  thus ?thesis by (simp add: ilcm_def)
qed

end
