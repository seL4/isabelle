(*  Title:      HOL/Polynomial.thy
    Author:     Brian Huffman
                Based on an earlier development by Clemens Ballarin
*)

header {* Univariate Polynomials *}

theory Polynomial
imports Plain SetInterval Main
begin

subsection {* Definition of type @{text poly} *}

typedef (Poly) 'a poly = "{f::nat \<Rightarrow> 'a::zero. \<exists>n. \<forall>i>n. f i = 0}"
  morphisms coeff Abs_poly
  by auto

lemma expand_poly_eq: "p = q \<longleftrightarrow> (\<forall>n. coeff p n = coeff q n)"
by (simp add: coeff_inject [symmetric] expand_fun_eq)

lemma poly_ext: "(\<And>n. coeff p n = coeff q n) \<Longrightarrow> p = q"
by (simp add: expand_poly_eq)


subsection {* Degree of a polynomial *}

definition
  degree :: "'a::zero poly \<Rightarrow> nat" where
  "degree p = (LEAST n. \<forall>i>n. coeff p i = 0)"

lemma coeff_eq_0: "degree p < n \<Longrightarrow> coeff p n = 0"
proof -
  have "coeff p \<in> Poly"
    by (rule coeff)
  hence "\<exists>n. \<forall>i>n. coeff p i = 0"
    unfolding Poly_def by simp
  hence "\<forall>i>degree p. coeff p i = 0"
    unfolding degree_def by (rule LeastI_ex)
  moreover assume "degree p < n"
  ultimately show ?thesis by simp
qed

lemma le_degree: "coeff p n \<noteq> 0 \<Longrightarrow> n \<le> degree p"
  by (erule contrapos_np, rule coeff_eq_0, simp)

lemma degree_le: "\<forall>i>n. coeff p i = 0 \<Longrightarrow> degree p \<le> n"
  unfolding degree_def by (erule Least_le)

lemma less_degree_imp: "n < degree p \<Longrightarrow> \<exists>i>n. coeff p i \<noteq> 0"
  unfolding degree_def by (drule not_less_Least, simp)


subsection {* The zero polynomial *}

instantiation poly :: (zero) zero
begin

definition
  zero_poly_def: "0 = Abs_poly (\<lambda>n. 0)"

instance ..
end

lemma coeff_0 [simp]: "coeff 0 n = 0"
  unfolding zero_poly_def
  by (simp add: Abs_poly_inverse Poly_def)

lemma degree_0 [simp]: "degree 0 = 0"
  by (rule order_antisym [OF degree_le le0]) simp

lemma leading_coeff_neq_0:
  assumes "p \<noteq> 0" shows "coeff p (degree p) \<noteq> 0"
proof (cases "degree p")
  case 0
  from `p \<noteq> 0` have "\<exists>n. coeff p n \<noteq> 0"
    by (simp add: expand_poly_eq)
  then obtain n where "coeff p n \<noteq> 0" ..
  hence "n \<le> degree p" by (rule le_degree)
  with `coeff p n \<noteq> 0` and `degree p = 0`
  show "coeff p (degree p) \<noteq> 0" by simp
next
  case (Suc n)
  from `degree p = Suc n` have "n < degree p" by simp
  hence "\<exists>i>n. coeff p i \<noteq> 0" by (rule less_degree_imp)
  then obtain i where "n < i" and "coeff p i \<noteq> 0" by fast
  from `degree p = Suc n` and `n < i` have "degree p \<le> i" by simp
  also from `coeff p i \<noteq> 0` have "i \<le> degree p" by (rule le_degree)
  finally have "degree p = i" .
  with `coeff p i \<noteq> 0` show "coeff p (degree p) \<noteq> 0" by simp
qed

lemma leading_coeff_0_iff [simp]: "coeff p (degree p) = 0 \<longleftrightarrow> p = 0"
  by (cases "p = 0", simp, simp add: leading_coeff_neq_0)


subsection {* List-style constructor for polynomials *}

definition
  pCons :: "'a::zero \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
where
  [code del]: "pCons a p = Abs_poly (nat_case a (coeff p))"

syntax
  "_poly" :: "args \<Rightarrow> 'a poly"  ("[:(_):]")

translations
  "[:x, xs:]" == "CONST pCons x [:xs:]"
  "[:x:]" == "CONST pCons x 0"

lemma Poly_nat_case: "f \<in> Poly \<Longrightarrow> nat_case a f \<in> Poly"
  unfolding Poly_def by (auto split: nat.split)

lemma coeff_pCons:
  "coeff (pCons a p) = nat_case a (coeff p)"
  unfolding pCons_def
  by (simp add: Abs_poly_inverse Poly_nat_case coeff)

lemma coeff_pCons_0 [simp]: "coeff (pCons a p) 0 = a"
  by (simp add: coeff_pCons)

lemma coeff_pCons_Suc [simp]: "coeff (pCons a p) (Suc n) = coeff p n"
  by (simp add: coeff_pCons)

lemma degree_pCons_le: "degree (pCons a p) \<le> Suc (degree p)"
by (rule degree_le, simp add: coeff_eq_0 coeff_pCons split: nat.split)

lemma degree_pCons_eq:
  "p \<noteq> 0 \<Longrightarrow> degree (pCons a p) = Suc (degree p)"
apply (rule order_antisym [OF degree_pCons_le])
apply (rule le_degree, simp)
done

lemma degree_pCons_0: "degree (pCons a 0) = 0"
apply (rule order_antisym [OF _ le0])
apply (rule degree_le, simp add: coeff_pCons split: nat.split)
done

lemma degree_pCons_eq_if [simp]:
  "degree (pCons a p) = (if p = 0 then 0 else Suc (degree p))"
apply (cases "p = 0", simp_all)
apply (rule order_antisym [OF _ le0])
apply (rule degree_le, simp add: coeff_pCons split: nat.split)
apply (rule order_antisym [OF degree_pCons_le])
apply (rule le_degree, simp)
done

lemma pCons_0_0 [simp]: "pCons 0 0 = 0"
by (rule poly_ext, simp add: coeff_pCons split: nat.split)

lemma pCons_eq_iff [simp]:
  "pCons a p = pCons b q \<longleftrightarrow> a = b \<and> p = q"
proof (safe)
  assume "pCons a p = pCons b q"
  then have "coeff (pCons a p) 0 = coeff (pCons b q) 0" by simp
  then show "a = b" by simp
next
  assume "pCons a p = pCons b q"
  then have "\<forall>n. coeff (pCons a p) (Suc n) =
                 coeff (pCons b q) (Suc n)" by simp
  then show "p = q" by (simp add: expand_poly_eq)
qed

lemma pCons_eq_0_iff [simp]: "pCons a p = 0 \<longleftrightarrow> a = 0 \<and> p = 0"
  using pCons_eq_iff [of a p 0 0] by simp

lemma Poly_Suc: "f \<in> Poly \<Longrightarrow> (\<lambda>n. f (Suc n)) \<in> Poly"
  unfolding Poly_def
  by (clarify, rule_tac x=n in exI, simp)

lemma pCons_cases [cases type: poly]:
  obtains (pCons) a q where "p = pCons a q"
proof
  show "p = pCons (coeff p 0) (Abs_poly (\<lambda>n. coeff p (Suc n)))"
    by (rule poly_ext)
       (simp add: Abs_poly_inverse Poly_Suc coeff coeff_pCons
             split: nat.split)
qed

lemma pCons_induct [case_names 0 pCons, induct type: poly]:
  assumes zero: "P 0"
  assumes pCons: "\<And>a p. P p \<Longrightarrow> P (pCons a p)"
  shows "P p"
proof (induct p rule: measure_induct_rule [where f=degree])
  case (less p)
  obtain a q where "p = pCons a q" by (rule pCons_cases)
  have "P q"
  proof (cases "q = 0")
    case True
    then show "P q" by (simp add: zero)
  next
    case False
    then have "degree (pCons a q) = Suc (degree q)"
      by (rule degree_pCons_eq)
    then have "degree q < degree p"
      using `p = pCons a q` by simp
    then show "P q"
      by (rule less.hyps)
  qed
  then have "P (pCons a q)"
    by (rule pCons)
  then show ?case
    using `p = pCons a q` by simp
qed


subsection {* Recursion combinator for polynomials *}

function
  poly_rec :: "'b \<Rightarrow> ('a::zero \<Rightarrow> 'a poly \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a poly \<Rightarrow> 'b"
where
  poly_rec_pCons_eq_if [simp del, code del]:
    "poly_rec z f (pCons a p) = f a p (if p = 0 then z else poly_rec z f p)"
by (case_tac x, rename_tac q, case_tac q, auto)

termination poly_rec
by (relation "measure (degree \<circ> snd \<circ> snd)", simp)
   (simp add: degree_pCons_eq)

lemma poly_rec_0:
  "f 0 0 z = z \<Longrightarrow> poly_rec z f 0 = z"
  using poly_rec_pCons_eq_if [of z f 0 0] by simp

lemma poly_rec_pCons:
  "f 0 0 z = z \<Longrightarrow> poly_rec z f (pCons a p) = f a p (poly_rec z f p)"
  by (simp add: poly_rec_pCons_eq_if poly_rec_0)


subsection {* Monomials *}

definition
  monom :: "'a \<Rightarrow> nat \<Rightarrow> 'a::zero poly" where
  "monom a m = Abs_poly (\<lambda>n. if m = n then a else 0)"

lemma coeff_monom [simp]: "coeff (monom a m) n = (if m=n then a else 0)"
  unfolding monom_def
  by (subst Abs_poly_inverse, auto simp add: Poly_def)

lemma monom_0: "monom a 0 = pCons a 0"
  by (rule poly_ext, simp add: coeff_pCons split: nat.split)

lemma monom_Suc: "monom a (Suc n) = pCons 0 (monom a n)"
  by (rule poly_ext, simp add: coeff_pCons split: nat.split)

lemma monom_eq_0 [simp]: "monom 0 n = 0"
  by (rule poly_ext) simp

lemma monom_eq_0_iff [simp]: "monom a n = 0 \<longleftrightarrow> a = 0"
  by (simp add: expand_poly_eq)

lemma monom_eq_iff [simp]: "monom a n = monom b n \<longleftrightarrow> a = b"
  by (simp add: expand_poly_eq)

lemma degree_monom_le: "degree (monom a n) \<le> n"
  by (rule degree_le, simp)

lemma degree_monom_eq: "a \<noteq> 0 \<Longrightarrow> degree (monom a n) = n"
  apply (rule order_antisym [OF degree_monom_le])
  apply (rule le_degree, simp)
  done


subsection {* Addition and subtraction *}

instantiation poly :: (comm_monoid_add) comm_monoid_add
begin

definition
  plus_poly_def [code del]:
    "p + q = Abs_poly (\<lambda>n. coeff p n + coeff q n)"

lemma Poly_add:
  fixes f g :: "nat \<Rightarrow> 'a"
  shows "\<lbrakk>f \<in> Poly; g \<in> Poly\<rbrakk> \<Longrightarrow> (\<lambda>n. f n + g n) \<in> Poly"
  unfolding Poly_def
  apply (clarify, rename_tac m n)
  apply (rule_tac x="max m n" in exI, simp)
  done

lemma coeff_add [simp]:
  "coeff (p + q) n = coeff p n + coeff q n"
  unfolding plus_poly_def
  by (simp add: Abs_poly_inverse coeff Poly_add)

instance proof
  fix p q r :: "'a poly"
  show "(p + q) + r = p + (q + r)"
    by (simp add: expand_poly_eq add_assoc)
  show "p + q = q + p"
    by (simp add: expand_poly_eq add_commute)
  show "0 + p = p"
    by (simp add: expand_poly_eq)
qed

end

instance poly ::
  ("{cancel_ab_semigroup_add,comm_monoid_add}") cancel_ab_semigroup_add
proof
  fix p q r :: "'a poly"
  assume "p + q = p + r" thus "q = r"
    by (simp add: expand_poly_eq)
qed

instantiation poly :: (ab_group_add) ab_group_add
begin

definition
  uminus_poly_def [code del]:
    "- p = Abs_poly (\<lambda>n. - coeff p n)"

definition
  minus_poly_def [code del]:
    "p - q = Abs_poly (\<lambda>n. coeff p n - coeff q n)"

lemma Poly_minus:
  fixes f :: "nat \<Rightarrow> 'a"
  shows "f \<in> Poly \<Longrightarrow> (\<lambda>n. - f n) \<in> Poly"
  unfolding Poly_def by simp

lemma Poly_diff:
  fixes f g :: "nat \<Rightarrow> 'a"
  shows "\<lbrakk>f \<in> Poly; g \<in> Poly\<rbrakk> \<Longrightarrow> (\<lambda>n. f n - g n) \<in> Poly"
  unfolding diff_minus by (simp add: Poly_add Poly_minus)

lemma coeff_minus [simp]: "coeff (- p) n = - coeff p n"
  unfolding uminus_poly_def
  by (simp add: Abs_poly_inverse coeff Poly_minus)

lemma coeff_diff [simp]:
  "coeff (p - q) n = coeff p n - coeff q n"
  unfolding minus_poly_def
  by (simp add: Abs_poly_inverse coeff Poly_diff)

instance proof
  fix p q :: "'a poly"
  show "- p + p = 0"
    by (simp add: expand_poly_eq)
  show "p - q = p + - q"
    by (simp add: expand_poly_eq diff_minus)
qed

end

lemma add_pCons [simp]:
  "pCons a p + pCons b q = pCons (a + b) (p + q)"
  by (rule poly_ext, simp add: coeff_pCons split: nat.split)

lemma minus_pCons [simp]:
  "- pCons a p = pCons (- a) (- p)"
  by (rule poly_ext, simp add: coeff_pCons split: nat.split)

lemma diff_pCons [simp]:
  "pCons a p - pCons b q = pCons (a - b) (p - q)"
  by (rule poly_ext, simp add: coeff_pCons split: nat.split)

lemma degree_add_le_max: "degree (p + q) \<le> max (degree p) (degree q)"
  by (rule degree_le, auto simp add: coeff_eq_0)

lemma degree_add_le:
  "\<lbrakk>degree p \<le> n; degree q \<le> n\<rbrakk> \<Longrightarrow> degree (p + q) \<le> n"
  by (auto intro: order_trans degree_add_le_max)

lemma degree_add_less:
  "\<lbrakk>degree p < n; degree q < n\<rbrakk> \<Longrightarrow> degree (p + q) < n"
  by (auto intro: le_less_trans degree_add_le_max)

lemma degree_add_eq_right:
  "degree p < degree q \<Longrightarrow> degree (p + q) = degree q"
  apply (cases "q = 0", simp)
  apply (rule order_antisym)
  apply (simp add: degree_add_le)
  apply (rule le_degree)
  apply (simp add: coeff_eq_0)
  done

lemma degree_add_eq_left:
  "degree q < degree p \<Longrightarrow> degree (p + q) = degree p"
  using degree_add_eq_right [of q p]
  by (simp add: add_commute)

lemma degree_minus [simp]: "degree (- p) = degree p"
  unfolding degree_def by simp

lemma degree_diff_le_max: "degree (p - q) \<le> max (degree p) (degree q)"
  using degree_add_le [where p=p and q="-q"]
  by (simp add: diff_minus)

lemma degree_diff_le:
  "\<lbrakk>degree p \<le> n; degree q \<le> n\<rbrakk> \<Longrightarrow> degree (p - q) \<le> n"
  by (simp add: diff_minus degree_add_le)

lemma degree_diff_less:
  "\<lbrakk>degree p < n; degree q < n\<rbrakk> \<Longrightarrow> degree (p - q) < n"
  by (simp add: diff_minus degree_add_less)

lemma add_monom: "monom a n + monom b n = monom (a + b) n"
  by (rule poly_ext) simp

lemma diff_monom: "monom a n - monom b n = monom (a - b) n"
  by (rule poly_ext) simp

lemma minus_monom: "- monom a n = monom (-a) n"
  by (rule poly_ext) simp

lemma coeff_setsum: "coeff (\<Sum>x\<in>A. p x) i = (\<Sum>x\<in>A. coeff (p x) i)"
  by (cases "finite A", induct set: finite, simp_all)

lemma monom_setsum: "monom (\<Sum>x\<in>A. a x) n = (\<Sum>x\<in>A. monom (a x) n)"
  by (rule poly_ext) (simp add: coeff_setsum)


subsection {* Multiplication by a constant *}

definition
  smult :: "'a::comm_semiring_0 \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "smult a p = Abs_poly (\<lambda>n. a * coeff p n)"

lemma Poly_smult:
  fixes f :: "nat \<Rightarrow> 'a::comm_semiring_0"
  shows "f \<in> Poly \<Longrightarrow> (\<lambda>n. a * f n) \<in> Poly"
  unfolding Poly_def
  by (clarify, rule_tac x=n in exI, simp)

lemma coeff_smult [simp]: "coeff (smult a p) n = a * coeff p n"
  unfolding smult_def
  by (simp add: Abs_poly_inverse Poly_smult coeff)

lemma degree_smult_le: "degree (smult a p) \<le> degree p"
  by (rule degree_le, simp add: coeff_eq_0)

lemma smult_smult [simp]: "smult a (smult b p) = smult (a * b) p"
  by (rule poly_ext, simp add: mult_assoc)

lemma smult_0_right [simp]: "smult a 0 = 0"
  by (rule poly_ext, simp)

lemma smult_0_left [simp]: "smult 0 p = 0"
  by (rule poly_ext, simp)

lemma smult_1_left [simp]: "smult (1::'a::comm_semiring_1) p = p"
  by (rule poly_ext, simp)

lemma smult_add_right:
  "smult a (p + q) = smult a p + smult a q"
  by (rule poly_ext, simp add: algebra_simps)

lemma smult_add_left:
  "smult (a + b) p = smult a p + smult b p"
  by (rule poly_ext, simp add: algebra_simps)

lemma smult_minus_right [simp]:
  "smult (a::'a::comm_ring) (- p) = - smult a p"
  by (rule poly_ext, simp)

lemma smult_minus_left [simp]:
  "smult (- a::'a::comm_ring) p = - smult a p"
  by (rule poly_ext, simp)

lemma smult_diff_right:
  "smult (a::'a::comm_ring) (p - q) = smult a p - smult a q"
  by (rule poly_ext, simp add: algebra_simps)

lemma smult_diff_left:
  "smult (a - b::'a::comm_ring) p = smult a p - smult b p"
  by (rule poly_ext, simp add: algebra_simps)

lemmas smult_distribs =
  smult_add_left smult_add_right
  smult_diff_left smult_diff_right

lemma smult_pCons [simp]:
  "smult a (pCons b p) = pCons (a * b) (smult a p)"
  by (rule poly_ext, simp add: coeff_pCons split: nat.split)

lemma smult_monom: "smult a (monom b n) = monom (a * b) n"
  by (induct n, simp add: monom_0, simp add: monom_Suc)

lemma degree_smult_eq [simp]:
  fixes a :: "'a::idom"
  shows "degree (smult a p) = (if a = 0 then 0 else degree p)"
  by (cases "a = 0", simp, simp add: degree_def)

lemma smult_eq_0_iff [simp]:
  fixes a :: "'a::idom"
  shows "smult a p = 0 \<longleftrightarrow> a = 0 \<or> p = 0"
  by (simp add: expand_poly_eq)


subsection {* Multiplication of polynomials *}

text {* TODO: move to SetInterval.thy *}
lemma setsum_atMost_Suc_shift:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>i\<le>Suc n. f i) = f 0 + (\<Sum>i\<le>n. f (Suc i))"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n) note IH = this
  have "(\<Sum>i\<le>Suc (Suc n). f i) = (\<Sum>i\<le>Suc n. f i) + f (Suc (Suc n))"
    by (rule setsum_atMost_Suc)
  also have "(\<Sum>i\<le>Suc n. f i) = f 0 + (\<Sum>i\<le>n. f (Suc i))"
    by (rule IH)
  also have "f 0 + (\<Sum>i\<le>n. f (Suc i)) + f (Suc (Suc n)) =
             f 0 + ((\<Sum>i\<le>n. f (Suc i)) + f (Suc (Suc n)))"
    by (rule add_assoc)
  also have "(\<Sum>i\<le>n. f (Suc i)) + f (Suc (Suc n)) = (\<Sum>i\<le>Suc n. f (Suc i))"
    by (rule setsum_atMost_Suc [symmetric])
  finally show ?case .
qed

instantiation poly :: (comm_semiring_0) comm_semiring_0
begin

definition
  times_poly_def [code del]:
    "p * q = poly_rec 0 (\<lambda>a p pq. smult a q + pCons 0 pq) p"

lemma mult_poly_0_left: "(0::'a poly) * q = 0"
  unfolding times_poly_def by (simp add: poly_rec_0)

lemma mult_pCons_left [simp]:
  "pCons a p * q = smult a q + pCons 0 (p * q)"
  unfolding times_poly_def by (simp add: poly_rec_pCons)

lemma mult_poly_0_right: "p * (0::'a poly) = 0"
  by (induct p, simp add: mult_poly_0_left, simp)

lemma mult_pCons_right [simp]:
  "p * pCons a q = smult a p + pCons 0 (p * q)"
  by (induct p, simp add: mult_poly_0_left, simp add: algebra_simps)

lemmas mult_poly_0 = mult_poly_0_left mult_poly_0_right

lemma mult_smult_left [simp]: "smult a p * q = smult a (p * q)"
  by (induct p, simp add: mult_poly_0, simp add: smult_add_right)

lemma mult_smult_right [simp]: "p * smult a q = smult a (p * q)"
  by (induct q, simp add: mult_poly_0, simp add: smult_add_right)

lemma mult_poly_add_left:
  fixes p q r :: "'a poly"
  shows "(p + q) * r = p * r + q * r"
  by (induct r, simp add: mult_poly_0,
                simp add: smult_distribs algebra_simps)

instance proof
  fix p q r :: "'a poly"
  show 0: "0 * p = 0"
    by (rule mult_poly_0_left)
  show "p * 0 = 0"
    by (rule mult_poly_0_right)
  show "(p + q) * r = p * r + q * r"
    by (rule mult_poly_add_left)
  show "(p * q) * r = p * (q * r)"
    by (induct p, simp add: mult_poly_0, simp add: mult_poly_add_left)
  show "p * q = q * p"
    by (induct p, simp add: mult_poly_0, simp)
qed

end

instance poly :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

lemma coeff_mult:
  "coeff (p * q) n = (\<Sum>i\<le>n. coeff p i * coeff q (n-i))"
proof (induct p arbitrary: n)
  case 0 show ?case by simp
next
  case (pCons a p n) thus ?case
    by (cases n, simp, simp add: setsum_atMost_Suc_shift
                            del: setsum_atMost_Suc)
qed

lemma degree_mult_le: "degree (p * q) \<le> degree p + degree q"
apply (rule degree_le)
apply (induct p)
apply simp
apply (simp add: coeff_eq_0 coeff_pCons split: nat.split)
done

lemma mult_monom: "monom a m * monom b n = monom (a * b) (m + n)"
  by (induct m, simp add: monom_0 smult_monom, simp add: monom_Suc)


subsection {* The unit polynomial and exponentiation *}

instantiation poly :: (comm_semiring_1) comm_semiring_1
begin

definition
  one_poly_def:
    "1 = pCons 1 0"

instance proof
  fix p :: "'a poly" show "1 * p = p"
    unfolding one_poly_def
    by simp
next
  show "0 \<noteq> (1::'a poly)"
    unfolding one_poly_def by simp
qed

end

instance poly :: (comm_semiring_1_cancel) comm_semiring_1_cancel ..

lemma coeff_1 [simp]: "coeff 1 n = (if n = 0 then 1 else 0)"
  unfolding one_poly_def
  by (simp add: coeff_pCons split: nat.split)

lemma degree_1 [simp]: "degree 1 = 0"
  unfolding one_poly_def
  by (rule degree_pCons_0)

instantiation poly :: (comm_semiring_1) recpower
begin

primrec power_poly where
  power_poly_0: "(p::'a poly) ^ 0 = 1"
| power_poly_Suc: "(p::'a poly) ^ (Suc n) = p * p ^ n"

instance
  by default simp_all

end

instance poly :: (comm_ring) comm_ring ..

instance poly :: (comm_ring_1) comm_ring_1 ..

instantiation poly :: (comm_ring_1) number_ring
begin

definition
  "number_of k = (of_int k :: 'a poly)"

instance
  by default (rule number_of_poly_def)

end


subsection {* Polynomials form an integral domain *}

lemma coeff_mult_degree_sum:
  "coeff (p * q) (degree p + degree q) =
   coeff p (degree p) * coeff q (degree q)"
  by (induct p, simp, simp add: coeff_eq_0)

instance poly :: (idom) idom
proof
  fix p q :: "'a poly"
  assume "p \<noteq> 0" and "q \<noteq> 0"
  have "coeff (p * q) (degree p + degree q) =
        coeff p (degree p) * coeff q (degree q)"
    by (rule coeff_mult_degree_sum)
  also have "coeff p (degree p) * coeff q (degree q) \<noteq> 0"
    using `p \<noteq> 0` and `q \<noteq> 0` by simp
  finally have "\<exists>n. coeff (p * q) n \<noteq> 0" ..
  thus "p * q \<noteq> 0" by (simp add: expand_poly_eq)
qed

lemma degree_mult_eq:
  fixes p q :: "'a::idom poly"
  shows "\<lbrakk>p \<noteq> 0; q \<noteq> 0\<rbrakk> \<Longrightarrow> degree (p * q) = degree p + degree q"
apply (rule order_antisym [OF degree_mult_le le_degree])
apply (simp add: coeff_mult_degree_sum)
done

lemma dvd_imp_degree_le:
  fixes p q :: "'a::idom poly"
  shows "\<lbrakk>p dvd q; q \<noteq> 0\<rbrakk> \<Longrightarrow> degree p \<le> degree q"
  by (erule dvdE, simp add: degree_mult_eq)


subsection {* Polynomials form an ordered integral domain *}

definition
  pos_poly :: "'a::ordered_idom poly \<Rightarrow> bool"
where
  "pos_poly p \<longleftrightarrow> 0 < coeff p (degree p)"

lemma pos_poly_pCons:
  "pos_poly (pCons a p) \<longleftrightarrow> pos_poly p \<or> (p = 0 \<and> 0 < a)"
  unfolding pos_poly_def by simp

lemma not_pos_poly_0 [simp]: "\<not> pos_poly 0"
  unfolding pos_poly_def by simp

lemma pos_poly_add: "\<lbrakk>pos_poly p; pos_poly q\<rbrakk> \<Longrightarrow> pos_poly (p + q)"
  apply (induct p arbitrary: q, simp)
  apply (case_tac q, force simp add: pos_poly_pCons add_pos_pos)
  done

lemma pos_poly_mult: "\<lbrakk>pos_poly p; pos_poly q\<rbrakk> \<Longrightarrow> pos_poly (p * q)"
  unfolding pos_poly_def
  apply (subgoal_tac "p \<noteq> 0 \<and> q \<noteq> 0")
  apply (simp add: degree_mult_eq coeff_mult_degree_sum mult_pos_pos)
  apply auto
  done

lemma pos_poly_total: "p = 0 \<or> pos_poly p \<or> pos_poly (- p)"
by (induct p) (auto simp add: pos_poly_pCons)

instantiation poly :: (ordered_idom) ordered_idom
begin

definition
  [code del]:
    "x < y \<longleftrightarrow> pos_poly (y - x)"

definition
  [code del]:
    "x \<le> y \<longleftrightarrow> x = y \<or> pos_poly (y - x)"

definition
  [code del]:
    "abs (x::'a poly) = (if x < 0 then - x else x)"

definition
  [code del]:
    "sgn (x::'a poly) = (if x = 0 then 0 else if 0 < x then 1 else - 1)"

instance proof
  fix x y :: "'a poly"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    unfolding less_eq_poly_def less_poly_def
    apply safe
    apply simp
    apply (drule (1) pos_poly_add)
    apply simp
    done
next
  fix x :: "'a poly" show "x \<le> x"
    unfolding less_eq_poly_def by simp
next
  fix x y z :: "'a poly"
  assume "x \<le> y" and "y \<le> z" thus "x \<le> z"
    unfolding less_eq_poly_def
    apply safe
    apply (drule (1) pos_poly_add)
    apply (simp add: algebra_simps)
    done
next
  fix x y :: "'a poly"
  assume "x \<le> y" and "y \<le> x" thus "x = y"
    unfolding less_eq_poly_def
    apply safe
    apply (drule (1) pos_poly_add)
    apply simp
    done
next
  fix x y z :: "'a poly"
  assume "x \<le> y" thus "z + x \<le> z + y"
    unfolding less_eq_poly_def
    apply safe
    apply (simp add: algebra_simps)
    done
next
  fix x y :: "'a poly"
  show "x \<le> y \<or> y \<le> x"
    unfolding less_eq_poly_def
    using pos_poly_total [of "x - y"]
    by auto
next
  fix x y z :: "'a poly"
  assume "x < y" and "0 < z"
  thus "z * x < z * y"
    unfolding less_poly_def
    by (simp add: right_diff_distrib [symmetric] pos_poly_mult)
next
  fix x :: "'a poly"
  show "\<bar>x\<bar> = (if x < 0 then - x else x)"
    by (rule abs_poly_def)
next
  fix x :: "'a poly"
  show "sgn x = (if x = 0 then 0 else if 0 < x then 1 else - 1)"
    by (rule sgn_poly_def)
qed

end

text {* TODO: Simplification rules for comparisons *}


subsection {* Long division of polynomials *}

definition
  pdivmod_rel :: "'a::field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> bool"
where
  [code del]:
  "pdivmod_rel x y q r \<longleftrightarrow>
    x = q * y + r \<and> (if y = 0 then q = 0 else r = 0 \<or> degree r < degree y)"

lemma pdivmod_rel_0:
  "pdivmod_rel 0 y 0 0"
  unfolding pdivmod_rel_def by simp

lemma pdivmod_rel_by_0:
  "pdivmod_rel x 0 0 x"
  unfolding pdivmod_rel_def by simp

lemma eq_zero_or_degree_less:
  assumes "degree p \<le> n" and "coeff p n = 0"
  shows "p = 0 \<or> degree p < n"
proof (cases n)
  case 0
  with `degree p \<le> n` and `coeff p n = 0`
  have "coeff p (degree p) = 0" by simp
  then have "p = 0" by simp
  then show ?thesis ..
next
  case (Suc m)
  have "\<forall>i>n. coeff p i = 0"
    using `degree p \<le> n` by (simp add: coeff_eq_0)
  then have "\<forall>i\<ge>n. coeff p i = 0"
    using `coeff p n = 0` by (simp add: le_less)
  then have "\<forall>i>m. coeff p i = 0"
    using `n = Suc m` by (simp add: less_eq_Suc_le)
  then have "degree p \<le> m"
    by (rule degree_le)
  then have "degree p < n"
    using `n = Suc m` by (simp add: less_Suc_eq_le)
  then show ?thesis ..
qed

lemma pdivmod_rel_pCons:
  assumes rel: "pdivmod_rel x y q r"
  assumes y: "y \<noteq> 0"
  assumes b: "b = coeff (pCons a r) (degree y) / coeff y (degree y)"
  shows "pdivmod_rel (pCons a x) y (pCons b q) (pCons a r - smult b y)"
    (is "pdivmod_rel ?x y ?q ?r")
proof -
  have x: "x = q * y + r" and r: "r = 0 \<or> degree r < degree y"
    using assms unfolding pdivmod_rel_def by simp_all

  have 1: "?x = ?q * y + ?r"
    using b x by simp

  have 2: "?r = 0 \<or> degree ?r < degree y"
  proof (rule eq_zero_or_degree_less)
    show "degree ?r \<le> degree y"
    proof (rule degree_diff_le)
      show "degree (pCons a r) \<le> degree y"
        using r by auto
      show "degree (smult b y) \<le> degree y"
        by (rule degree_smult_le)
    qed
  next
    show "coeff ?r (degree y) = 0"
      using `y \<noteq> 0` unfolding b by simp
  qed

  from 1 2 show ?thesis
    unfolding pdivmod_rel_def
    using `y \<noteq> 0` by simp
qed

lemma pdivmod_rel_exists: "\<exists>q r. pdivmod_rel x y q r"
apply (cases "y = 0")
apply (fast intro!: pdivmod_rel_by_0)
apply (induct x)
apply (fast intro!: pdivmod_rel_0)
apply (fast intro!: pdivmod_rel_pCons)
done

lemma pdivmod_rel_unique:
  assumes 1: "pdivmod_rel x y q1 r1"
  assumes 2: "pdivmod_rel x y q2 r2"
  shows "q1 = q2 \<and> r1 = r2"
proof (cases "y = 0")
  assume "y = 0" with assms show ?thesis
    by (simp add: pdivmod_rel_def)
next
  assume [simp]: "y \<noteq> 0"
  from 1 have q1: "x = q1 * y + r1" and r1: "r1 = 0 \<or> degree r1 < degree y"
    unfolding pdivmod_rel_def by simp_all
  from 2 have q2: "x = q2 * y + r2" and r2: "r2 = 0 \<or> degree r2 < degree y"
    unfolding pdivmod_rel_def by simp_all
  from q1 q2 have q3: "(q1 - q2) * y = r2 - r1"
    by (simp add: algebra_simps)
  from r1 r2 have r3: "(r2 - r1) = 0 \<or> degree (r2 - r1) < degree y"
    by (auto intro: degree_diff_less)

  show "q1 = q2 \<and> r1 = r2"
  proof (rule ccontr)
    assume "\<not> (q1 = q2 \<and> r1 = r2)"
    with q3 have "q1 \<noteq> q2" and "r1 \<noteq> r2" by auto
    with r3 have "degree (r2 - r1) < degree y" by simp
    also have "degree y \<le> degree (q1 - q2) + degree y" by simp
    also have "\<dots> = degree ((q1 - q2) * y)"
      using `q1 \<noteq> q2` by (simp add: degree_mult_eq)
    also have "\<dots> = degree (r2 - r1)"
      using q3 by simp
    finally have "degree (r2 - r1) < degree (r2 - r1)" .
    then show "False" by simp
  qed
qed

lemma pdivmod_rel_0_iff: "pdivmod_rel 0 y q r \<longleftrightarrow> q = 0 \<and> r = 0"
by (auto dest: pdivmod_rel_unique intro: pdivmod_rel_0)

lemma pdivmod_rel_by_0_iff: "pdivmod_rel x 0 q r \<longleftrightarrow> q = 0 \<and> r = x"
by (auto dest: pdivmod_rel_unique intro: pdivmod_rel_by_0)

lemmas pdivmod_rel_unique_div =
  pdivmod_rel_unique [THEN conjunct1, standard]

lemmas pdivmod_rel_unique_mod =
  pdivmod_rel_unique [THEN conjunct2, standard]

instantiation poly :: (field) ring_div
begin

definition div_poly where
  [code del]: "x div y = (THE q. \<exists>r. pdivmod_rel x y q r)"

definition mod_poly where
  [code del]: "x mod y = (THE r. \<exists>q. pdivmod_rel x y q r)"

lemma div_poly_eq:
  "pdivmod_rel x y q r \<Longrightarrow> x div y = q"
unfolding div_poly_def
by (fast elim: pdivmod_rel_unique_div)

lemma mod_poly_eq:
  "pdivmod_rel x y q r \<Longrightarrow> x mod y = r"
unfolding mod_poly_def
by (fast elim: pdivmod_rel_unique_mod)

lemma pdivmod_rel:
  "pdivmod_rel x y (x div y) (x mod y)"
proof -
  from pdivmod_rel_exists
    obtain q r where "pdivmod_rel x y q r" by fast
  thus ?thesis
    by (simp add: div_poly_eq mod_poly_eq)
qed

instance proof
  fix x y :: "'a poly"
  show "x div y * y + x mod y = x"
    using pdivmod_rel [of x y]
    by (simp add: pdivmod_rel_def)
next
  fix x :: "'a poly"
  have "pdivmod_rel x 0 0 x"
    by (rule pdivmod_rel_by_0)
  thus "x div 0 = 0"
    by (rule div_poly_eq)
next
  fix y :: "'a poly"
  have "pdivmod_rel 0 y 0 0"
    by (rule pdivmod_rel_0)
  thus "0 div y = 0"
    by (rule div_poly_eq)
next
  fix x y z :: "'a poly"
  assume "y \<noteq> 0"
  hence "pdivmod_rel (x + z * y) y (z + x div y) (x mod y)"
    using pdivmod_rel [of x y]
    by (simp add: pdivmod_rel_def left_distrib)
  thus "(x + z * y) div y = z + x div y"
    by (rule div_poly_eq)
qed

end

lemma degree_mod_less:
  "y \<noteq> 0 \<Longrightarrow> x mod y = 0 \<or> degree (x mod y) < degree y"
  using pdivmod_rel [of x y]
  unfolding pdivmod_rel_def by simp

lemma div_poly_less: "degree x < degree y \<Longrightarrow> x div y = 0"
proof -
  assume "degree x < degree y"
  hence "pdivmod_rel x y 0 x"
    by (simp add: pdivmod_rel_def)
  thus "x div y = 0" by (rule div_poly_eq)
qed

lemma mod_poly_less: "degree x < degree y \<Longrightarrow> x mod y = x"
proof -
  assume "degree x < degree y"
  hence "pdivmod_rel x y 0 x"
    by (simp add: pdivmod_rel_def)
  thus "x mod y = x" by (rule mod_poly_eq)
qed

lemma pdivmod_rel_smult_left:
  "pdivmod_rel x y q r
    \<Longrightarrow> pdivmod_rel (smult a x) y (smult a q) (smult a r)"
  unfolding pdivmod_rel_def by (simp add: smult_add_right)

lemma div_smult_left: "(smult a x) div y = smult a (x div y)"
  by (rule div_poly_eq, rule pdivmod_rel_smult_left, rule pdivmod_rel)

lemma mod_smult_left: "(smult a x) mod y = smult a (x mod y)"
  by (rule mod_poly_eq, rule pdivmod_rel_smult_left, rule pdivmod_rel)

lemma pdivmod_rel_smult_right:
  "\<lbrakk>a \<noteq> 0; pdivmod_rel x y q r\<rbrakk>
    \<Longrightarrow> pdivmod_rel x (smult a y) (smult (inverse a) q) r"
  unfolding pdivmod_rel_def by simp

lemma div_smult_right:
  "a \<noteq> 0 \<Longrightarrow> x div (smult a y) = smult (inverse a) (x div y)"
  by (rule div_poly_eq, erule pdivmod_rel_smult_right, rule pdivmod_rel)

lemma mod_smult_right: "a \<noteq> 0 \<Longrightarrow> x mod (smult a y) = x mod y"
  by (rule mod_poly_eq, erule pdivmod_rel_smult_right, rule pdivmod_rel)

lemma pdivmod_rel_mult:
  "\<lbrakk>pdivmod_rel x y q r; pdivmod_rel q z q' r'\<rbrakk>
    \<Longrightarrow> pdivmod_rel x (y * z) q' (y * r' + r)"
apply (cases "z = 0", simp add: pdivmod_rel_def)
apply (cases "y = 0", simp add: pdivmod_rel_by_0_iff pdivmod_rel_0_iff)
apply (cases "r = 0")
apply (cases "r' = 0")
apply (simp add: pdivmod_rel_def)
apply (simp add: pdivmod_rel_def ring_simps degree_mult_eq)
apply (cases "r' = 0")
apply (simp add: pdivmod_rel_def degree_mult_eq)
apply (simp add: pdivmod_rel_def ring_simps)
apply (simp add: degree_mult_eq degree_add_less)
done

lemma poly_div_mult_right:
  fixes x y z :: "'a::field poly"
  shows "x div (y * z) = (x div y) div z"
  by (rule div_poly_eq, rule pdivmod_rel_mult, (rule pdivmod_rel)+)

lemma poly_mod_mult_right:
  fixes x y z :: "'a::field poly"
  shows "x mod (y * z) = y * (x div y mod z) + x mod y"
  by (rule mod_poly_eq, rule pdivmod_rel_mult, (rule pdivmod_rel)+)

lemma mod_pCons:
  fixes a and x
  assumes y: "y \<noteq> 0"
  defines b: "b \<equiv> coeff (pCons a (x mod y)) (degree y) / coeff y (degree y)"
  shows "(pCons a x) mod y = (pCons a (x mod y) - smult b y)"
unfolding b
apply (rule mod_poly_eq)
apply (rule pdivmod_rel_pCons [OF pdivmod_rel y refl])
done


subsection {* Evaluation of polynomials *}

definition
  poly :: "'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a" where
  "poly = poly_rec (\<lambda>x. 0) (\<lambda>a p f x. a + x * f x)"

lemma poly_0 [simp]: "poly 0 x = 0"
  unfolding poly_def by (simp add: poly_rec_0)

lemma poly_pCons [simp]: "poly (pCons a p) x = a + x * poly p x"
  unfolding poly_def by (simp add: poly_rec_pCons)

lemma poly_1 [simp]: "poly 1 x = 1"
  unfolding one_poly_def by simp

lemma poly_monom:
  fixes a x :: "'a::{comm_semiring_1,recpower}"
  shows "poly (monom a n) x = a * x ^ n"
  by (induct n, simp add: monom_0, simp add: monom_Suc power_Suc mult_ac)

lemma poly_add [simp]: "poly (p + q) x = poly p x + poly q x"
  apply (induct p arbitrary: q, simp)
  apply (case_tac q, simp, simp add: algebra_simps)
  done

lemma poly_minus [simp]:
  fixes x :: "'a::comm_ring"
  shows "poly (- p) x = - poly p x"
  by (induct p, simp_all)

lemma poly_diff [simp]:
  fixes x :: "'a::comm_ring"
  shows "poly (p - q) x = poly p x - poly q x"
  by (simp add: diff_minus)

lemma poly_setsum: "poly (\<Sum>k\<in>A. p k) x = (\<Sum>k\<in>A. poly (p k) x)"
  by (cases "finite A", induct set: finite, simp_all)

lemma poly_smult [simp]: "poly (smult a p) x = a * poly p x"
  by (induct p, simp, simp add: algebra_simps)

lemma poly_mult [simp]: "poly (p * q) x = poly p x * poly q x"
  by (induct p, simp_all, simp add: algebra_simps)

lemma poly_power [simp]:
  fixes p :: "'a::{comm_semiring_1,recpower} poly"
  shows "poly (p ^ n) x = poly p x ^ n"
  by (induct n, simp, simp add: power_Suc)


subsection {* Synthetic division *}

definition
  synthetic_divmod :: "'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a poly \<times> 'a"
where [code del]:
  "synthetic_divmod p c =
    poly_rec (0, 0) (\<lambda>a p (q, r). (pCons r q, a + c * r)) p"

definition
  synthetic_div :: "'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a poly"
where
  "synthetic_div p c = fst (synthetic_divmod p c)"

lemma synthetic_divmod_0 [simp]:
  "synthetic_divmod 0 c = (0, 0)"
  unfolding synthetic_divmod_def
  by (simp add: poly_rec_0)

lemma synthetic_divmod_pCons [simp]:
  "synthetic_divmod (pCons a p) c =
    (\<lambda>(q, r). (pCons r q, a + c * r)) (synthetic_divmod p c)"
  unfolding synthetic_divmod_def
  by (simp add: poly_rec_pCons)

lemma snd_synthetic_divmod: "snd (synthetic_divmod p c) = poly p c"
  by (induct p, simp, simp add: split_def)

lemma synthetic_div_0 [simp]: "synthetic_div 0 c = 0"
  unfolding synthetic_div_def by simp

lemma synthetic_div_pCons [simp]:
  "synthetic_div (pCons a p) c = pCons (poly p c) (synthetic_div p c)"
  unfolding synthetic_div_def
  by (simp add: split_def snd_synthetic_divmod)

lemma synthetic_div_eq_0_iff:
  "synthetic_div p c = 0 \<longleftrightarrow> degree p = 0"
  by (induct p, simp, case_tac p, simp)

lemma degree_synthetic_div:
  "degree (synthetic_div p c) = degree p - 1"
  by (induct p, simp, simp add: synthetic_div_eq_0_iff)

lemma synthetic_div_correct:
  "p + smult c (synthetic_div p c) = pCons (poly p c) (synthetic_div p c)"
  by (induct p) simp_all

lemma synthetic_div_unique_lemma: "smult c p = pCons a p \<Longrightarrow> p = 0"
by (induct p arbitrary: a) simp_all

lemma synthetic_div_unique:
  "p + smult c q = pCons r q \<Longrightarrow> r = poly p c \<and> q = synthetic_div p c"
apply (induct p arbitrary: q r)
apply (simp, frule synthetic_div_unique_lemma, simp)
apply (case_tac q, force)
done

lemma synthetic_div_correct':
  fixes c :: "'a::comm_ring_1"
  shows "[:-c, 1:] * synthetic_div p c + [:poly p c:] = p"
  using synthetic_div_correct [of p c]
  by (simp add: algebra_simps)

lemma poly_eq_0_iff_dvd:
  fixes c :: "'a::idom"
  shows "poly p c = 0 \<longleftrightarrow> [:-c, 1:] dvd p"
proof
  assume "poly p c = 0"
  with synthetic_div_correct' [of c p]
  have "p = [:-c, 1:] * synthetic_div p c" by simp
  then show "[:-c, 1:] dvd p" ..
next
  assume "[:-c, 1:] dvd p"
  then obtain k where "p = [:-c, 1:] * k" by (rule dvdE)
  then show "poly p c = 0" by simp
qed

lemma dvd_iff_poly_eq_0:
  fixes c :: "'a::idom"
  shows "[:c, 1:] dvd p \<longleftrightarrow> poly p (-c) = 0"
  by (simp add: poly_eq_0_iff_dvd)

lemma poly_roots_finite:
  fixes p :: "'a::idom poly"
  shows "p \<noteq> 0 \<Longrightarrow> finite {x. poly p x = 0}"
proof (induct n \<equiv> "degree p" arbitrary: p)
  case (0 p)
  then obtain a where "a \<noteq> 0" and "p = [:a:]"
    by (cases p, simp split: if_splits)
  then show "finite {x. poly p x = 0}" by simp
next
  case (Suc n p)
  show "finite {x. poly p x = 0}"
  proof (cases "\<exists>x. poly p x = 0")
    case False
    then show "finite {x. poly p x = 0}" by simp
  next
    case True
    then obtain a where "poly p a = 0" ..
    then have "[:-a, 1:] dvd p" by (simp only: poly_eq_0_iff_dvd)
    then obtain k where k: "p = [:-a, 1:] * k" ..
    with `p \<noteq> 0` have "k \<noteq> 0" by auto
    with k have "degree p = Suc (degree k)"
      by (simp add: degree_mult_eq del: mult_pCons_left)
    with `Suc n = degree p` have "n = degree k" by simp
    with `k \<noteq> 0` have "finite {x. poly k x = 0}" by (rule Suc.hyps)
    then have "finite (insert a {x. poly k x = 0})" by simp
    then show "finite {x. poly p x = 0}"
      by (simp add: k uminus_add_conv_diff Collect_disj_eq
               del: mult_pCons_left)
  qed
qed


subsection {* Configuration of the code generator *}

code_datatype "0::'a::zero poly" pCons

declare pCons_0_0 [code post]

instantiation poly :: ("{zero,eq}") eq
begin

definition [code del]:
  "eq_class.eq (p::'a poly) q \<longleftrightarrow> p = q"

instance
  by default (rule eq_poly_def)

end

lemma eq_poly_code [code]:
  "eq_class.eq (0::_ poly) (0::_ poly) \<longleftrightarrow> True"
  "eq_class.eq (0::_ poly) (pCons b q) \<longleftrightarrow> eq_class.eq 0 b \<and> eq_class.eq 0 q"
  "eq_class.eq (pCons a p) (0::_ poly) \<longleftrightarrow> eq_class.eq a 0 \<and> eq_class.eq p 0"
  "eq_class.eq (pCons a p) (pCons b q) \<longleftrightarrow> eq_class.eq a b \<and> eq_class.eq p q"
unfolding eq by simp_all

lemmas coeff_code [code] =
  coeff_0 coeff_pCons_0 coeff_pCons_Suc

lemmas degree_code [code] =
  degree_0 degree_pCons_eq_if

lemmas monom_poly_code [code] =
  monom_0 monom_Suc

lemma add_poly_code [code]:
  "0 + q = (q :: _ poly)"
  "p + 0 = (p :: _ poly)"
  "pCons a p + pCons b q = pCons (a + b) (p + q)"
by simp_all

lemma minus_poly_code [code]:
  "- 0 = (0 :: _ poly)"
  "- pCons a p = pCons (- a) (- p)"
by simp_all

lemma diff_poly_code [code]:
  "0 - q = (- q :: _ poly)"
  "p - 0 = (p :: _ poly)"
  "pCons a p - pCons b q = pCons (a - b) (p - q)"
by simp_all

lemmas smult_poly_code [code] =
  smult_0_right smult_pCons

lemma mult_poly_code [code]:
  "0 * q = (0 :: _ poly)"
  "pCons a p * q = smult a q + pCons 0 (p * q)"
by simp_all

lemmas poly_code [code] =
  poly_0 poly_pCons

lemmas synthetic_divmod_code [code] =
  synthetic_divmod_0 synthetic_divmod_pCons

text {* code generator setup for div and mod *}

definition
  pdivmod :: "'a::field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<times> 'a poly"
where
  [code del]: "pdivmod x y = (x div y, x mod y)"

lemma div_poly_code [code]: "x div y = fst (pdivmod x y)"
  unfolding pdivmod_def by simp

lemma mod_poly_code [code]: "x mod y = snd (pdivmod x y)"
  unfolding pdivmod_def by simp

lemma pdivmod_0 [code]: "pdivmod 0 y = (0, 0)"
  unfolding pdivmod_def by simp

lemma pdivmod_pCons [code]:
  "pdivmod (pCons a x) y =
    (if y = 0 then (0, pCons a x) else
      (let (q, r) = pdivmod x y;
           b = coeff (pCons a r) (degree y) / coeff y (degree y)
        in (pCons b q, pCons a r - smult b y)))"
apply (simp add: pdivmod_def Let_def, safe)
apply (rule div_poly_eq)
apply (erule pdivmod_rel_pCons [OF pdivmod_rel _ refl])
apply (rule mod_poly_eq)
apply (erule pdivmod_rel_pCons [OF pdivmod_rel _ refl])
done

end
