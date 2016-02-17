(*  Title:      HOL/Library/Polynomial_GCD_euclidean.thy
    Author:     Brian Huffman
    Author:     Clemens Ballarin
    Author:     Amine Chaieb
    Author:     Florian Haftmann
*)

section \<open>GCD and LCM on polynomials over a field\<close>

theory Polynomial_GCD_euclidean
imports Main "~~/src/HOL/GCD" "~~/src/HOL/Library/Polynomial"
begin

subsection \<open>GCD of polynomials\<close>

instantiation poly :: (field) gcd
begin

function gcd_poly :: "'a::field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
where
  "gcd (x::'a poly) 0 = smult (inverse (coeff x (degree x))) x"
| "y \<noteq> 0 \<Longrightarrow> gcd (x::'a poly) y = gcd y (x mod y)"
by auto

termination "gcd :: _ poly \<Rightarrow> _"
by (relation "measure (\<lambda>(x, y). if y = 0 then 0 else Suc (degree y))")
   (auto dest: degree_mod_less)

declare gcd_poly.simps [simp del]

definition lcm_poly :: "'a::field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
where
  "lcm_poly a b = a * b div smult (coeff a (degree a) * coeff b (degree b)) (gcd a b)"

instance ..

end

lemma
  fixes x y :: "_ poly"
  shows poly_gcd_dvd1 [iff]: "gcd x y dvd x"
    and poly_gcd_dvd2 [iff]: "gcd x y dvd y"
  apply (induct x y rule: gcd_poly.induct)
  apply (simp_all add: gcd_poly.simps)
  apply (fastforce simp add: smult_dvd_iff dest: inverse_zero_imp_zero)
  apply (blast dest: dvd_mod_imp_dvd)
  done

lemma poly_gcd_greatest:
  fixes k x y :: "_ poly"
  shows "k dvd x \<Longrightarrow> k dvd y \<Longrightarrow> k dvd gcd x y"
  by (induct x y rule: gcd_poly.induct)
     (simp_all add: gcd_poly.simps dvd_mod dvd_smult)

lemma dvd_poly_gcd_iff [iff]:
  fixes k x y :: "_ poly"
  shows "k dvd gcd x y \<longleftrightarrow> k dvd x \<and> k dvd y"
  by (auto intro!: poly_gcd_greatest intro: dvd_trans [of _ "gcd x y"])

lemma poly_gcd_monic:
  fixes x y :: "_ poly"
  shows "coeff (gcd x y) (degree (gcd x y)) =
    (if x = 0 \<and> y = 0 then 0 else 1)"
  by (induct x y rule: gcd_poly.induct)
     (simp_all add: gcd_poly.simps nonzero_imp_inverse_nonzero)

lemma poly_gcd_zero_iff [simp]:
  fixes x y :: "_ poly"
  shows "gcd x y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  by (simp only: dvd_0_left_iff [symmetric] dvd_poly_gcd_iff)

lemma poly_gcd_0_0 [simp]:
  "gcd (0::_ poly) 0 = 0"
  by simp

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
  shows "gcd x y = d"
proof -
  have "coeff (gcd x y) (degree (gcd x y)) = coeff d (degree d)"
    by (simp_all add: poly_gcd_monic monic)
  moreover have "gcd x y dvd d"
    using poly_gcd_dvd1 poly_gcd_dvd2 by (rule greatest)
  moreover have "d dvd gcd x y"
    using dvd1 dvd2 by (rule poly_gcd_greatest)
  ultimately show ?thesis
    by (rule poly_dvd_antisym)
qed

instance poly :: (field) semiring_gcd
proof
  fix p q :: "'a::field poly"
  show "normalize (gcd p q) = gcd p q"
    by (induct p q rule: gcd_poly.induct)
      (simp_all add: gcd_poly.simps normalize_poly_def)
  show "lcm p q = normalize (p * q) div gcd p q"
    by (simp add: coeff_degree_mult div_smult_left div_smult_right lcm_poly_def normalize_poly_def)
      (metis (no_types, lifting) div_smult_right inverse_mult_distrib inverse_zero mult.commute pdivmod_rel pdivmod_rel_def smult_eq_0_iff)
qed simp_all

lemma poly_gcd_1_left [simp]: "gcd 1 y = (1 :: _ poly)"
by (rule poly_gcd_unique) simp_all

lemma poly_gcd_1_right [simp]: "gcd x 1 = (1 :: _ poly)"
by (rule poly_gcd_unique) simp_all

lemma poly_gcd_minus_left [simp]: "gcd (- x) y = gcd x (y :: _ poly)"
by (rule poly_gcd_unique) (simp_all add: poly_gcd_monic)

lemma poly_gcd_minus_right [simp]: "gcd x (- y) = gcd x (y :: _ poly)"
by (rule poly_gcd_unique) (simp_all add: poly_gcd_monic)

lemma poly_gcd_code [code]:
  "gcd x y = (if y = 0 then normalize x else gcd y (x mod (y :: _ poly)))"
  by (simp add: gcd_poly.simps)

end
