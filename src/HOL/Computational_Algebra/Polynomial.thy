(*  Title:      HOL/Computational_Algebra/Polynomial.thy
    Author:     Brian Huffman
    Author:     Clemens Ballarin
    Author:     Amine Chaieb
    Author:     Florian Haftmann
*)

section \<open>Polynomials as type over a ring structure\<close>

theory Polynomial
imports
  Complex_Main
  "HOL-Library.More_List"
  "HOL-Library.Infinite_Set"
  Factorial_Ring
begin

subsection \<open>Auxiliary: operations for lists (later) representing coefficients\<close>

definition cCons :: "'a::zero \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixr "##" 65)
  where "x ## xs = (if xs = [] \<and> x = 0 then [] else x # xs)"

lemma cCons_0_Nil_eq [simp]: "0 ## [] = []"
  by (simp add: cCons_def)

lemma cCons_Cons_eq [simp]: "x ## y # ys = x # y # ys"
  by (simp add: cCons_def)

lemma cCons_append_Cons_eq [simp]: "x ## xs @ y # ys = x # xs @ y # ys"
  by (simp add: cCons_def)

lemma cCons_not_0_eq [simp]: "x \<noteq> 0 \<Longrightarrow> x ## xs = x # xs"
  by (simp add: cCons_def)

lemma strip_while_not_0_Cons_eq [simp]:
  "strip_while (\<lambda>x. x = 0) (x # xs) = x ## strip_while (\<lambda>x. x = 0) xs"
proof (cases "x = 0")
  case False
  then show ?thesis by simp
next
  case True
  show ?thesis
  proof (induct xs rule: rev_induct)
    case Nil
    with True show ?case by simp
  next
    case (snoc y ys)
    then show ?case
      by (cases "y = 0") (simp_all add: append_Cons [symmetric] del: append_Cons)
  qed
qed

lemma tl_cCons [simp]: "tl (x ## xs) = xs"
  by (simp add: cCons_def)


subsection \<open>Definition of type \<open>poly\<close>\<close>

typedef (overloaded) 'a poly = "{f :: nat \<Rightarrow> 'a::zero. \<forall>\<^sub>\<infinity> n. f n = 0}"
  morphisms coeff Abs_poly
  by (auto intro!: ALL_MOST)

setup_lifting type_definition_poly

lemma poly_eq_iff: "p = q \<longleftrightarrow> (\<forall>n. coeff p n = coeff q n)"
  by (simp add: coeff_inject [symmetric] fun_eq_iff)

lemma poly_eqI: "(\<And>n. coeff p n = coeff q n) \<Longrightarrow> p = q"
  by (simp add: poly_eq_iff)

lemma MOST_coeff_eq_0: "\<forall>\<^sub>\<infinity> n. coeff p n = 0"
  using coeff [of p] by simp


subsection \<open>Degree of a polynomial\<close>

definition degree :: "'a::zero poly \<Rightarrow> nat"
  where "degree p = (LEAST n. \<forall>i>n. coeff p i = 0)"

lemma coeff_eq_0:
  assumes "degree p < n"
  shows "coeff p n = 0"
proof -
  have "\<exists>n. \<forall>i>n. coeff p i = 0"
    using MOST_coeff_eq_0 by (simp add: MOST_nat)
  then have "\<forall>i>degree p. coeff p i = 0"
    unfolding degree_def by (rule LeastI_ex)
  with assms show ?thesis by simp
qed

lemma le_degree: "coeff p n \<noteq> 0 \<Longrightarrow> n \<le> degree p"
  by (erule contrapos_np, rule coeff_eq_0, simp)

lemma degree_le: "\<forall>i>n. coeff p i = 0 \<Longrightarrow> degree p \<le> n"
  unfolding degree_def by (erule Least_le)

lemma less_degree_imp: "n < degree p \<Longrightarrow> \<exists>i>n. coeff p i \<noteq> 0"
  unfolding degree_def by (drule not_less_Least, simp)


subsection \<open>The zero polynomial\<close>

instantiation poly :: (zero) zero
begin

lift_definition zero_poly :: "'a poly"
  is "\<lambda>_. 0"
  by (rule MOST_I) simp

instance ..

end

lemma coeff_0 [simp]: "coeff 0 n = 0"
  by transfer rule

lemma degree_0 [simp]: "degree 0 = 0"
  by (rule order_antisym [OF degree_le le0]) simp

lemma leading_coeff_neq_0:
  assumes "p \<noteq> 0"
  shows "coeff p (degree p) \<noteq> 0"
proof (cases "degree p")
  case 0
  from \<open>p \<noteq> 0\<close> obtain n where "coeff p n \<noteq> 0"
    by (auto simp add: poly_eq_iff)
  then have "n \<le> degree p"
    by (rule le_degree)
  with \<open>coeff p n \<noteq> 0\<close> and \<open>degree p = 0\<close> show "coeff p (degree p) \<noteq> 0"
    by simp
next
  case (Suc n)
  from \<open>degree p = Suc n\<close> have "n < degree p"
    by simp
  then have "\<exists>i>n. coeff p i \<noteq> 0"
    by (rule less_degree_imp)
  then obtain i where "n < i" and "coeff p i \<noteq> 0"
    by blast
  from \<open>degree p = Suc n\<close> and \<open>n < i\<close> have "degree p \<le> i"
    by simp
  also from \<open>coeff p i \<noteq> 0\<close> have "i \<le> degree p"
    by (rule le_degree)
  finally have "degree p = i" .
  with \<open>coeff p i \<noteq> 0\<close> show "coeff p (degree p) \<noteq> 0" by simp
qed

lemma leading_coeff_0_iff [simp]: "coeff p (degree p) = 0 \<longleftrightarrow> p = 0"
  by (cases "p = 0") (simp_all add: leading_coeff_neq_0)

lemma eq_zero_or_degree_less:
  assumes "degree p \<le> n" and "coeff p n = 0"
  shows "p = 0 \<or> degree p < n"
proof (cases n)
  case 0
  with \<open>degree p \<le> n\<close> and \<open>coeff p n = 0\<close> have "coeff p (degree p) = 0"
    by simp
  then have "p = 0" by simp
  then show ?thesis ..
next
  case (Suc m)
  from \<open>degree p \<le> n\<close> have "\<forall>i>n. coeff p i = 0"
    by (simp add: coeff_eq_0)
  with \<open>coeff p n = 0\<close> have "\<forall>i\<ge>n. coeff p i = 0"
    by (simp add: le_less)
  with \<open>n = Suc m\<close> have "\<forall>i>m. coeff p i = 0"
    by (simp add: less_eq_Suc_le)
  then have "degree p \<le> m"
    by (rule degree_le)
  with \<open>n = Suc m\<close> have "degree p < n"
    by (simp add: less_Suc_eq_le)
  then show ?thesis ..
qed

lemma coeff_0_degree_minus_1: "coeff rrr dr = 0 \<Longrightarrow> degree rrr \<le> dr \<Longrightarrow> degree rrr \<le> dr - 1"
  using eq_zero_or_degree_less by fastforce


subsection \<open>List-style constructor for polynomials\<close>

lift_definition pCons :: "'a::zero \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>a p. case_nat a (coeff p)"
  by (rule MOST_SucD) (simp add: MOST_coeff_eq_0)

lemmas coeff_pCons = pCons.rep_eq

lemma coeff_pCons_0 [simp]: "coeff (pCons a p) 0 = a"
  by transfer simp

lemma coeff_pCons_Suc [simp]: "coeff (pCons a p) (Suc n) = coeff p n"
  by (simp add: coeff_pCons)

lemma degree_pCons_le: "degree (pCons a p) \<le> Suc (degree p)"
  by (rule degree_le) (simp add: coeff_eq_0 coeff_pCons split: nat.split)

lemma degree_pCons_eq: "p \<noteq> 0 \<Longrightarrow> degree (pCons a p) = Suc (degree p)"
  by (simp add: degree_pCons_le le_antisym le_degree)

lemma degree_pCons_0: "degree (pCons a 0) = 0"
proof -
  have "degree (pCons a 0) \<le> Suc 0"
    by (metis (no_types) degree_0 degree_pCons_le)
  then show ?thesis
    by (metis coeff_0 coeff_pCons_Suc degree_0 eq_zero_or_degree_less less_Suc0)
qed

lemma degree_pCons_eq_if [simp]: "degree (pCons a p) = (if p = 0 then 0 else Suc (degree p))"
  by (simp add: degree_pCons_0 degree_pCons_eq)

lemma pCons_0_0 [simp]: "pCons 0 0 = 0"
  by (rule poly_eqI) (simp add: coeff_pCons split: nat.split)

lemma pCons_eq_iff [simp]: "pCons a p = pCons b q \<longleftrightarrow> a = b \<and> p = q"
proof safe
  assume "pCons a p = pCons b q"
  then have "coeff (pCons a p) 0 = coeff (pCons b q) 0"
    by simp
  then show "a = b"
    by simp
next
  assume "pCons a p = pCons b q"
  then have "coeff (pCons a p) (Suc n) = coeff (pCons b q) (Suc n)" for n
    by simp
  then show "p = q"
    by (simp add: poly_eq_iff)
qed

lemma pCons_eq_0_iff [simp]: "pCons a p = 0 \<longleftrightarrow> a = 0 \<and> p = 0"
  using pCons_eq_iff [of a p 0 0] by simp

lemma pCons_cases [cases type: poly]:
  obtains (pCons) a q where "p = pCons a q"
proof
  show "p = pCons (coeff p 0) (Abs_poly (\<lambda>n. coeff p (Suc n)))"
    by transfer
      (simp_all add: MOST_inj[where f=Suc and P="\<lambda>n. p n = 0" for p] fun_eq_iff Abs_poly_inverse
        split: nat.split)
qed

lemma pCons_induct [case_names 0 pCons, induct type: poly]:
  assumes zero: "P 0"
  assumes pCons: "\<And>a p. a \<noteq> 0 \<or> p \<noteq> 0 \<Longrightarrow> P p \<Longrightarrow> P (pCons a p)"
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
    with \<open>p = pCons a q\<close> have "degree q < degree p"
      by simp
    then show "P q"
      by (rule less.hyps)
  qed
  have "P (pCons a q)"
  proof (cases "a \<noteq> 0 \<or> q \<noteq> 0")
    case True
    with \<open>P q\<close> show ?thesis by (auto intro: pCons)
  next
    case False
    with zero show ?thesis by simp
  qed
  with \<open>p = pCons a q\<close> show ?case
    by simp
qed

lemma degree_eq_zeroE:
  fixes p :: "'a::zero poly"
  assumes "degree p = 0"
  obtains a where "p = pCons a 0"
proof -
  obtain a q where p: "p = pCons a q"
    by (cases p)
  with assms have "q = 0"
    by (cases "q = 0") simp_all
  with p have "p = pCons a 0"
    by simp
  then show thesis ..
qed


subsection \<open>Quickcheck generator for polynomials\<close>

quickcheck_generator poly constructors: "0 :: _ poly", pCons


subsection \<open>List-style syntax for polynomials\<close>

syntax "_poly" :: "args \<Rightarrow> 'a poly"  ("[:(_):]")
translations
  "[:x, xs:]" \<rightleftharpoons> "CONST pCons x [:xs:]"
  "[:x:]" \<rightleftharpoons> "CONST pCons x 0"
  "[:x:]" \<leftharpoondown> "CONST pCons x (_constrain 0 t)"


subsection \<open>Representation of polynomials by lists of coefficients\<close>

primrec Poly :: "'a::zero list \<Rightarrow> 'a poly"
  where
    [code_post]: "Poly [] = 0"
  | [code_post]: "Poly (a # as) = pCons a (Poly as)"

lemma Poly_replicate_0 [simp]: "Poly (replicate n 0) = 0"
  by (induct n) simp_all

lemma Poly_eq_0: "Poly as = 0 \<longleftrightarrow> (\<exists>n. as = replicate n 0)"
  by (induct as) (auto simp add: Cons_replicate_eq)

lemma Poly_append_replicate_zero [simp]: "Poly (as @ replicate n 0) = Poly as"
  by (induct as) simp_all

lemma Poly_snoc_zero [simp]: "Poly (as @ [0]) = Poly as"
  using Poly_append_replicate_zero [of as 1] by simp

lemma Poly_cCons_eq_pCons_Poly [simp]: "Poly (a ## p) = pCons a (Poly p)"
  by (simp add: cCons_def)

lemma Poly_on_rev_starting_with_0 [simp]: "hd as = 0 \<Longrightarrow> Poly (rev (tl as)) = Poly (rev as)"
  by (cases as) simp_all

lemma degree_Poly: "degree (Poly xs) \<le> length xs"
  by (induct xs) simp_all

lemma coeff_Poly_eq [simp]: "coeff (Poly xs) = nth_default 0 xs"
  by (induct xs) (simp_all add: fun_eq_iff coeff_pCons split: nat.splits)

definition coeffs :: "'a poly \<Rightarrow> 'a::zero list"
  where "coeffs p = (if p = 0 then [] else map (\<lambda>i. coeff p i) [0 ..< Suc (degree p)])"

lemma coeffs_eq_Nil [simp]: "coeffs p = [] \<longleftrightarrow> p = 0"
  by (simp add: coeffs_def)

lemma not_0_coeffs_not_Nil: "p \<noteq> 0 \<Longrightarrow> coeffs p \<noteq> []"
  by simp

lemma coeffs_0_eq_Nil [simp]: "coeffs 0 = []"
  by simp

lemma coeffs_pCons_eq_cCons [simp]: "coeffs (pCons a p) = a ## coeffs p"
proof -
  have *: "\<forall>m\<in>set ms. m > 0 \<Longrightarrow> map (case_nat x f) ms = map f (map (\<lambda>n. n - 1) ms)"
    for ms :: "nat list" and f :: "nat \<Rightarrow> 'a" and x :: "'a"
    by (induct ms) (auto split: nat.split)
  show ?thesis
    by (simp add: * coeffs_def upt_conv_Cons coeff_pCons map_decr_upt del: upt_Suc)
qed

lemma length_coeffs: "p \<noteq> 0 \<Longrightarrow> length (coeffs p) = degree p + 1"
  by (simp add: coeffs_def)

lemma coeffs_nth: "p \<noteq> 0 \<Longrightarrow> n \<le> degree p \<Longrightarrow> coeffs p ! n = coeff p n"
  by (auto simp: coeffs_def simp del: upt_Suc)

lemma coeff_in_coeffs: "p \<noteq> 0 \<Longrightarrow> n \<le> degree p \<Longrightarrow> coeff p n \<in> set (coeffs p)"
  using coeffs_nth [of p n, symmetric] by (simp add: length_coeffs)

lemma not_0_cCons_eq [simp]: "p \<noteq> 0 \<Longrightarrow> a ## coeffs p = a # coeffs p"
  by (simp add: cCons_def)

lemma Poly_coeffs [simp, code abstype]: "Poly (coeffs p) = p"
  by (induct p) auto

lemma coeffs_Poly [simp]: "coeffs (Poly as) = strip_while (HOL.eq 0) as"
proof (induct as)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  from replicate_length_same [of as 0] have "(\<forall>n. as \<noteq> replicate n 0) \<longleftrightarrow> (\<exists>a\<in>set as. a \<noteq> 0)"
    by (auto dest: sym [of _ as])
  with Cons show ?case by auto
qed

lemma no_trailing_coeffs [simp]:
  "no_trailing (HOL.eq 0) (coeffs p)"
  by (induct p)  auto

lemma strip_while_coeffs [simp]:
  "strip_while (HOL.eq 0) (coeffs p) = coeffs p"
  by simp

lemma coeffs_eq_iff: "p = q \<longleftrightarrow> coeffs p = coeffs q"
  (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  then show ?Q by simp
next
  assume ?Q
  then have "Poly (coeffs p) = Poly (coeffs q)" by simp
  then show ?P by simp
qed

lemma nth_default_coeffs_eq: "nth_default 0 (coeffs p) = coeff p"
  by (simp add: fun_eq_iff coeff_Poly_eq [symmetric])

lemma [code]: "coeff p = nth_default 0 (coeffs p)"
  by (simp add: nth_default_coeffs_eq)

lemma coeffs_eqI:
  assumes coeff: "\<And>n. coeff p n = nth_default 0 xs n"
  assumes zero: "no_trailing (HOL.eq 0) xs"
  shows "coeffs p = xs"
proof -
  from coeff have "p = Poly xs"
    by (simp add: poly_eq_iff)
  with zero show ?thesis by simp
qed

lemma degree_eq_length_coeffs [code]: "degree p = length (coeffs p) - 1"
  by (simp add: coeffs_def)

lemma length_coeffs_degree: "p \<noteq> 0 \<Longrightarrow> length (coeffs p) = Suc (degree p)"
  by (induct p) (auto simp: cCons_def)

lemma [code abstract]: "coeffs 0 = []"
  by (fact coeffs_0_eq_Nil)

lemma [code abstract]: "coeffs (pCons a p) = a ## coeffs p"
  by (fact coeffs_pCons_eq_cCons)

lemma set_coeffs_subset_singleton_0_iff [simp]:
  "set (coeffs p) \<subseteq> {0} \<longleftrightarrow> p = 0"
  by (auto simp add: coeffs_def intro: classical)

lemma set_coeffs_not_only_0 [simp]:
  "set (coeffs p) \<noteq> {0}"
  by (auto simp add: set_eq_subset)

lemma forall_coeffs_conv:
  "(\<forall>n. P (coeff p n)) \<longleftrightarrow> (\<forall>c \<in> set (coeffs p). P c)" if "P 0"
  using that by (auto simp add: coeffs_def)
    (metis atLeastLessThan_iff coeff_eq_0 not_less_iff_gr_or_eq zero_le)

instantiation poly :: ("{zero, equal}") equal
begin

definition [code]: "HOL.equal (p::'a poly) q \<longleftrightarrow> HOL.equal (coeffs p) (coeffs q)"

instance
  by standard (simp add: equal equal_poly_def coeffs_eq_iff)

end

lemma [code nbe]: "HOL.equal (p :: _ poly) p \<longleftrightarrow> True"
  by (fact equal_refl)

definition is_zero :: "'a::zero poly \<Rightarrow> bool"
  where [code]: "is_zero p \<longleftrightarrow> List.null (coeffs p)"

lemma is_zero_null [code_abbrev]: "is_zero p \<longleftrightarrow> p = 0"
  by (simp add: is_zero_def null_def)


subsubsection \<open>Reconstructing the polynomial from the list\<close>
  \<comment> \<open>contributed by Sebastiaan J.C. Joosten and René Thiemann\<close>

definition poly_of_list :: "'a::comm_monoid_add list \<Rightarrow> 'a poly"
  where [simp]: "poly_of_list = Poly"

lemma poly_of_list_impl [code abstract]: "coeffs (poly_of_list as) = strip_while (HOL.eq 0) as"
  by simp


subsection \<open>Fold combinator for polynomials\<close>

definition fold_coeffs :: "('a::zero \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a poly \<Rightarrow> 'b \<Rightarrow> 'b"
  where "fold_coeffs f p = foldr f (coeffs p)"

lemma fold_coeffs_0_eq [simp]: "fold_coeffs f 0 = id"
  by (simp add: fold_coeffs_def)

lemma fold_coeffs_pCons_eq [simp]: "f 0 = id \<Longrightarrow> fold_coeffs f (pCons a p) = f a \<circ> fold_coeffs f p"
  by (simp add: fold_coeffs_def cCons_def fun_eq_iff)

lemma fold_coeffs_pCons_0_0_eq [simp]: "fold_coeffs f (pCons 0 0) = id"
  by (simp add: fold_coeffs_def)

lemma fold_coeffs_pCons_coeff_not_0_eq [simp]:
  "a \<noteq> 0 \<Longrightarrow> fold_coeffs f (pCons a p) = f a \<circ> fold_coeffs f p"
  by (simp add: fold_coeffs_def)

lemma fold_coeffs_pCons_not_0_0_eq [simp]:
  "p \<noteq> 0 \<Longrightarrow> fold_coeffs f (pCons a p) = f a \<circ> fold_coeffs f p"
  by (simp add: fold_coeffs_def)


subsection \<open>Canonical morphism on polynomials -- evaluation\<close>

definition poly :: \<open>'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>poly p a = horner_sum id a (coeffs p)\<close>

lemma poly_eq_fold_coeffs:
  \<open>poly p = fold_coeffs (\<lambda>a f x. a + x * f x) p (\<lambda>x. 0)\<close>
  by (induction p) (auto simp add: fun_eq_iff poly_def)

lemma poly_0 [simp]: "poly 0 x = 0"
  by (simp add: poly_def)

lemma poly_pCons [simp]: "poly (pCons a p) x = a + x * poly p x"
  by (cases "p = 0 \<and> a = 0") (auto simp add: poly_def)

lemma poly_altdef: "poly p x = (\<Sum>i\<le>degree p. coeff p i * x ^ i)"
  for x :: "'a::{comm_semiring_0,semiring_1}"
proof (induction p rule: pCons_induct)
  case 0
  then show ?case
    by simp
next
  case (pCons a p)
  show ?case
  proof (cases "p = 0")
    case True
    then show ?thesis by simp
  next
    case False
    let ?p' = "pCons a p"
    note poly_pCons[of a p x]
    also note pCons.IH
    also have "a + x * (\<Sum>i\<le>degree p. coeff p i * x ^ i) =
        coeff ?p' 0 * x^0 + (\<Sum>i\<le>degree p. coeff ?p' (Suc i) * x^Suc i)"
      by (simp add: field_simps sum_distrib_left coeff_pCons)
    also note sum.atMost_Suc_shift[symmetric]
    also note degree_pCons_eq[OF \<open>p \<noteq> 0\<close>, of a, symmetric]
    finally show ?thesis .
  qed
qed

lemma poly_0_coeff_0: "poly p 0 = coeff p 0"
  by (cases p) (auto simp: poly_altdef)


subsection \<open>Monomials\<close>

lift_definition monom :: "'a \<Rightarrow> nat \<Rightarrow> 'a::zero poly"
  is "\<lambda>a m n. if m = n then a else 0"
  by (simp add: MOST_iff_cofinite)

lemma coeff_monom [simp]: "coeff (monom a m) n = (if m = n then a else 0)"
  by transfer rule

lemma monom_0: "monom a 0 = pCons a 0"
  by (rule poly_eqI) (simp add: coeff_pCons split: nat.split)

lemma monom_Suc: "monom a (Suc n) = pCons 0 (monom a n)"
  by (rule poly_eqI) (simp add: coeff_pCons split: nat.split)

lemma monom_eq_0 [simp]: "monom 0 n = 0"
  by (rule poly_eqI) simp

lemma monom_eq_0_iff [simp]: "monom a n = 0 \<longleftrightarrow> a = 0"
  by (simp add: poly_eq_iff)

lemma monom_eq_iff [simp]: "monom a n = monom b n \<longleftrightarrow> a = b"
  by (simp add: poly_eq_iff)

lemma degree_monom_le: "degree (monom a n) \<le> n"
  by (rule degree_le, simp)

lemma degree_monom_eq: "a \<noteq> 0 \<Longrightarrow> degree (monom a n) = n"
  by (metis coeff_monom leading_coeff_0_iff)

lemma coeffs_monom [code abstract]:
  "coeffs (monom a n) = (if a = 0 then [] else replicate n 0 @ [a])"
  by (induct n) (simp_all add: monom_0 monom_Suc)

lemma fold_coeffs_monom [simp]: "a \<noteq> 0 \<Longrightarrow> fold_coeffs f (monom a n) = f 0 ^^ n \<circ> f a"
  by (simp add: fold_coeffs_def coeffs_monom fun_eq_iff)

lemma poly_monom: "poly (monom a n) x = a * x ^ n"
  for a x :: "'a::comm_semiring_1"
  by (cases "a = 0", simp_all) (induct n, simp_all add: mult.left_commute poly_eq_fold_coeffs)

lemma monom_eq_iff': "monom c n = monom d m \<longleftrightarrow>  c = d \<and> (c = 0 \<or> n = m)"
  by (auto simp: poly_eq_iff)

lemma monom_eq_const_iff: "monom c n = [:d:] \<longleftrightarrow> c = d \<and> (c = 0 \<or> n = 0)"
  using monom_eq_iff'[of c n d 0] by (simp add: monom_0)


subsection \<open>Leading coefficient\<close>

abbreviation lead_coeff:: "'a::zero poly \<Rightarrow> 'a"
  where "lead_coeff p \<equiv> coeff p (degree p)"

lemma lead_coeff_pCons[simp]:
  "p \<noteq> 0 \<Longrightarrow> lead_coeff (pCons a p) = lead_coeff p"
  "p = 0 \<Longrightarrow> lead_coeff (pCons a p) = a"
  by auto

lemma lead_coeff_monom [simp]: "lead_coeff (monom c n) = c"
  by (cases "c = 0") (simp_all add: degree_monom_eq)

lemma last_coeffs_eq_coeff_degree:
  "last (coeffs p) = lead_coeff p" if "p \<noteq> 0"
  using that by (simp add: coeffs_def)


subsection \<open>Addition and subtraction\<close>

instantiation poly :: (comm_monoid_add) comm_monoid_add
begin

lift_definition plus_poly :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>p q n. coeff p n + coeff q n"
proof -
  fix q p :: "'a poly"
  show "\<forall>\<^sub>\<infinity>n. coeff p n + coeff q n = 0"
    using MOST_coeff_eq_0[of p] MOST_coeff_eq_0[of q] by eventually_elim simp
qed

lemma coeff_add [simp]: "coeff (p + q) n = coeff p n + coeff q n"
  by (simp add: plus_poly.rep_eq)

instance
proof
  fix p q r :: "'a poly"
  show "(p + q) + r = p + (q + r)"
    by (simp add: poly_eq_iff add.assoc)
  show "p + q = q + p"
    by (simp add: poly_eq_iff add.commute)
  show "0 + p = p"
    by (simp add: poly_eq_iff)
qed

end

instantiation poly :: (cancel_comm_monoid_add) cancel_comm_monoid_add
begin

lift_definition minus_poly :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>p q n. coeff p n - coeff q n"
proof -
  fix q p :: "'a poly"
  show "\<forall>\<^sub>\<infinity>n. coeff p n - coeff q n = 0"
    using MOST_coeff_eq_0[of p] MOST_coeff_eq_0[of q] by eventually_elim simp
qed

lemma coeff_diff [simp]: "coeff (p - q) n = coeff p n - coeff q n"
  by (simp add: minus_poly.rep_eq)

instance
proof
  fix p q r :: "'a poly"
  show "p + q - p = q"
    by (simp add: poly_eq_iff)
  show "p - q - r = p - (q + r)"
    by (simp add: poly_eq_iff diff_diff_eq)
qed

end

instantiation poly :: (ab_group_add) ab_group_add
begin

lift_definition uminus_poly :: "'a poly \<Rightarrow> 'a poly"
  is "\<lambda>p n. - coeff p n"
proof -
  fix p :: "'a poly"
  show "\<forall>\<^sub>\<infinity>n. - coeff p n = 0"
    using MOST_coeff_eq_0 by simp
qed

lemma coeff_minus [simp]: "coeff (- p) n = - coeff p n"
  by (simp add: uminus_poly.rep_eq)

instance
proof
  fix p q :: "'a poly"
  show "- p + p = 0"
    by (simp add: poly_eq_iff)
  show "p - q = p + - q"
    by (simp add: poly_eq_iff)
qed

end

lemma add_pCons [simp]: "pCons a p + pCons b q = pCons (a + b) (p + q)"
  by (rule poly_eqI) (simp add: coeff_pCons split: nat.split)

lemma minus_pCons [simp]: "- pCons a p = pCons (- a) (- p)"
  by (rule poly_eqI) (simp add: coeff_pCons split: nat.split)

lemma diff_pCons [simp]: "pCons a p - pCons b q = pCons (a - b) (p - q)"
  by (rule poly_eqI) (simp add: coeff_pCons split: nat.split)

lemma degree_add_le_max: "degree (p + q) \<le> max (degree p) (degree q)"
  by (rule degree_le) (auto simp add: coeff_eq_0)

lemma degree_add_le: "degree p \<le> n \<Longrightarrow> degree q \<le> n \<Longrightarrow> degree (p + q) \<le> n"
  by (auto intro: order_trans degree_add_le_max)

lemma degree_add_less: "degree p < n \<Longrightarrow> degree q < n \<Longrightarrow> degree (p + q) < n"
  by (auto intro: le_less_trans degree_add_le_max)

lemma degree_add_eq_right: assumes "degree p < degree q" shows "degree (p + q) = degree q"
proof (cases "q = 0")
  case False
  show ?thesis
  proof (rule order_antisym)
    show "degree (p + q) \<le> degree q"
      by (simp add: assms degree_add_le order.strict_implies_order)
    show "degree q \<le> degree (p + q)"
      by (simp add: False assms coeff_eq_0 le_degree)
  qed
qed (use assms in auto)

lemma degree_add_eq_left: "degree q < degree p \<Longrightarrow> degree (p + q) = degree p"
  using degree_add_eq_right [of q p] by (simp add: add.commute)

lemma degree_minus [simp]: "degree (- p) = degree p"
  by (simp add: degree_def)

lemma lead_coeff_add_le: "degree p < degree q \<Longrightarrow> lead_coeff (p + q) = lead_coeff q"
  by (metis coeff_add coeff_eq_0 monoid_add_class.add.left_neutral degree_add_eq_right)

lemma lead_coeff_minus: "lead_coeff (- p) = - lead_coeff p"
  by (metis coeff_minus degree_minus)

lemma degree_diff_le_max: "degree (p - q) \<le> max (degree p) (degree q)"
  for p q :: "'a::ab_group_add poly"
  using degree_add_le [where p=p and q="-q"] by simp

lemma degree_diff_le: "degree p \<le> n \<Longrightarrow> degree q \<le> n \<Longrightarrow> degree (p - q) \<le> n"
  for p q :: "'a::ab_group_add poly"
  using degree_add_le [of p n "- q"] by simp

lemma degree_diff_less: "degree p < n \<Longrightarrow> degree q < n \<Longrightarrow> degree (p - q) < n"
  for p q :: "'a::ab_group_add poly"
  using degree_add_less [of p n "- q"] by simp

lemma add_monom: "monom a n + monom b n = monom (a + b) n"
  by (rule poly_eqI) simp

lemma diff_monom: "monom a n - monom b n = monom (a - b) n"
  by (rule poly_eqI) simp

lemma minus_monom: "- monom a n = monom (- a) n"
  by (rule poly_eqI) simp

lemma coeff_sum: "coeff (\<Sum>x\<in>A. p x) i = (\<Sum>x\<in>A. coeff (p x) i)"
  by (induct A rule: infinite_finite_induct) simp_all

lemma monom_sum: "monom (\<Sum>x\<in>A. a x) n = (\<Sum>x\<in>A. monom (a x) n)"
  by (rule poly_eqI) (simp add: coeff_sum)

fun plus_coeffs :: "'a::comm_monoid_add list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "plus_coeffs xs [] = xs"
  | "plus_coeffs [] ys = ys"
  | "plus_coeffs (x # xs) (y # ys) = (x + y) ## plus_coeffs xs ys"

lemma coeffs_plus_eq_plus_coeffs [code abstract]:
  "coeffs (p + q) = plus_coeffs (coeffs p) (coeffs q)"
proof -
  have *: "nth_default 0 (plus_coeffs xs ys) n = nth_default 0 xs n + nth_default 0 ys n"
    for xs ys :: "'a list" and n
  proof (induct xs ys arbitrary: n rule: plus_coeffs.induct)
    case (3 x xs y ys n)
    then show ?case
      by (cases n) (auto simp add: cCons_def)
  qed simp_all
  have **: "no_trailing (HOL.eq 0) (plus_coeffs xs ys)"
    if "no_trailing (HOL.eq 0) xs" and "no_trailing (HOL.eq 0) ys"
    for xs ys :: "'a list"
    using that by (induct xs ys rule: plus_coeffs.induct) (simp_all add: cCons_def)
  show ?thesis
    by (rule coeffs_eqI) (auto simp add: * nth_default_coeffs_eq intro: **)
qed

lemma coeffs_uminus [code abstract]:
  "coeffs (- p) = map uminus (coeffs p)"
proof -
  have eq_0: "HOL.eq 0 \<circ> uminus = HOL.eq (0::'a)"
    by (simp add: fun_eq_iff)
  show ?thesis
    by (rule coeffs_eqI) (simp_all add: nth_default_map_eq nth_default_coeffs_eq no_trailing_map eq_0)
qed

lemma [code]: "p - q = p + - q"
  for p q :: "'a::ab_group_add poly"
  by (fact diff_conv_add_uminus)

lemma poly_add [simp]: "poly (p + q) x = poly p x + poly q x"
proof (induction p arbitrary: q)
  case (pCons a p)
  then show ?case
    by (cases q) (simp add: algebra_simps)
qed auto

lemma poly_minus [simp]: "poly (- p) x = - poly p x"
  for x :: "'a::comm_ring"
  by (induct p) simp_all

lemma poly_diff [simp]: "poly (p - q) x = poly p x - poly q x"
  for x :: "'a::comm_ring"
  using poly_add [of p "- q" x] by simp

lemma poly_sum: "poly (\<Sum>k\<in>A. p k) x = (\<Sum>k\<in>A. poly (p k) x)"
  by (induct A rule: infinite_finite_induct) simp_all

lemma degree_sum_le: "finite S \<Longrightarrow> (\<And>p. p \<in> S \<Longrightarrow> degree (f p) \<le> n) \<Longrightarrow> degree (sum f S) \<le> n"
proof (induct S rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert p S)
  then have "degree (sum f S) \<le> n" "degree (f p) \<le> n"
    by auto
  then show ?case
    unfolding sum.insert[OF insert(1-2)] by (metis degree_add_le)
qed

lemma poly_as_sum_of_monoms':
  assumes "degree p \<le> n"
  shows "(\<Sum>i\<le>n. monom (coeff p i) i) = p"
proof -
  have eq: "\<And>i. {..n} \<inter> {i} = (if i \<le> n then {i} else {})"
    by auto
  from assms show ?thesis
    by (simp add: poly_eq_iff coeff_sum coeff_eq_0 sum.If_cases eq
        if_distrib[where f="\<lambda>x. x * a" for a])
qed

lemma poly_as_sum_of_monoms: "(\<Sum>i\<le>degree p. monom (coeff p i) i) = p"
  by (intro poly_as_sum_of_monoms' order_refl)

lemma Poly_snoc: "Poly (xs @ [x]) = Poly xs + monom x (length xs)"
  by (induct xs) (simp_all add: monom_0 monom_Suc)


subsection \<open>Multiplication by a constant, polynomial multiplication and the unit polynomial\<close>

lift_definition smult :: "'a::comm_semiring_0 \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>a p n. a * coeff p n"
proof -
  fix a :: 'a and p :: "'a poly"
  show "\<forall>\<^sub>\<infinity> i. a * coeff p i = 0"
    using MOST_coeff_eq_0[of p] by eventually_elim simp
qed

lemma coeff_smult [simp]: "coeff (smult a p) n = a * coeff p n"
  by (simp add: smult.rep_eq)

lemma degree_smult_le: "degree (smult a p) \<le> degree p"
  by (rule degree_le) (simp add: coeff_eq_0)

lemma smult_smult [simp]: "smult a (smult b p) = smult (a * b) p"
  by (rule poly_eqI) (simp add: mult.assoc)

lemma smult_0_right [simp]: "smult a 0 = 0"
  by (rule poly_eqI) simp

lemma smult_0_left [simp]: "smult 0 p = 0"
  by (rule poly_eqI) simp

lemma smult_1_left [simp]: "smult (1::'a::comm_semiring_1) p = p"
  by (rule poly_eqI) simp

lemma smult_add_right: "smult a (p + q) = smult a p + smult a q"
  by (rule poly_eqI) (simp add: algebra_simps)

lemma smult_add_left: "smult (a + b) p = smult a p + smult b p"
  by (rule poly_eqI) (simp add: algebra_simps)

lemma smult_minus_right [simp]: "smult a (- p) = - smult a p"
  for a :: "'a::comm_ring"
  by (rule poly_eqI) simp

lemma smult_minus_left [simp]: "smult (- a) p = - smult a p"
  for a :: "'a::comm_ring"
  by (rule poly_eqI) simp

lemma smult_diff_right: "smult a (p - q) = smult a p - smult a q"
  for a :: "'a::comm_ring"
  by (rule poly_eqI) (simp add: algebra_simps)

lemma smult_diff_left: "smult (a - b) p = smult a p - smult b p"
  for a b :: "'a::comm_ring"
  by (rule poly_eqI) (simp add: algebra_simps)

lemmas smult_distribs =
  smult_add_left smult_add_right
  smult_diff_left smult_diff_right

lemma smult_pCons [simp]: "smult a (pCons b p) = pCons (a * b) (smult a p)"
  by (rule poly_eqI) (simp add: coeff_pCons split: nat.split)

lemma smult_monom: "smult a (monom b n) = monom (a * b) n"
  by (induct n) (simp_all add: monom_0 monom_Suc)

lemma smult_Poly: "smult c (Poly xs) = Poly (map ((*) c) xs)"
  by (auto simp: poly_eq_iff nth_default_def)

lemma degree_smult_eq [simp]: "degree (smult a p) = (if a = 0 then 0 else degree p)"
  for a :: "'a::{comm_semiring_0,semiring_no_zero_divisors}"
  by (cases "a = 0") (simp_all add: degree_def)

lemma smult_eq_0_iff [simp]: "smult a p = 0 \<longleftrightarrow> a = 0 \<or> p = 0"
  for a :: "'a::{comm_semiring_0,semiring_no_zero_divisors}"
  by (simp add: poly_eq_iff)

lemma coeffs_smult [code abstract]:
  "coeffs (smult a p) = (if a = 0 then [] else map (Groups.times a) (coeffs p))"
  for p :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
proof -
  have eq_0: "HOL.eq 0 \<circ> times a = HOL.eq (0::'a)" if "a \<noteq> 0"
    using that by (simp add: fun_eq_iff)
  show ?thesis
    by (rule coeffs_eqI) (auto simp add: no_trailing_map nth_default_map_eq nth_default_coeffs_eq eq_0)
qed

lemma smult_eq_iff:
  fixes b :: "'a :: field"
  assumes "b \<noteq> 0"
  shows "smult a p = smult b q \<longleftrightarrow> smult (a / b) p = q"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  also from assms have "smult (inverse b) \<dots> = q"
    by simp
  finally show ?rhs
    by (simp add: field_simps)
next
  assume ?rhs
  with assms show ?lhs by auto
qed

instantiation poly :: (comm_semiring_0) comm_semiring_0
begin

definition "p * q = fold_coeffs (\<lambda>a p. smult a q + pCons 0 p) p 0"

lemma mult_poly_0_left: "(0::'a poly) * q = 0"
  by (simp add: times_poly_def)

lemma mult_pCons_left [simp]: "pCons a p * q = smult a q + pCons 0 (p * q)"
  by (cases "p = 0 \<and> a = 0") (auto simp add: times_poly_def)

lemma mult_poly_0_right: "p * (0::'a poly) = 0"
  by (induct p) (simp_all add: mult_poly_0_left)

lemma mult_pCons_right [simp]: "p * pCons a q = smult a p + pCons 0 (p * q)"
  by (induct p) (simp_all add: mult_poly_0_left algebra_simps)

lemmas mult_poly_0 = mult_poly_0_left mult_poly_0_right

lemma mult_smult_left [simp]: "smult a p * q = smult a (p * q)"
  by (induct p) (simp_all add: mult_poly_0 smult_add_right)

lemma mult_smult_right [simp]: "p * smult a q = smult a (p * q)"
  by (induct q) (simp_all add: mult_poly_0 smult_add_right)

lemma mult_poly_add_left: "(p + q) * r = p * r + q * r"
  for p q r :: "'a poly"
  by (induct r) (simp_all add: mult_poly_0 smult_distribs algebra_simps)

instance
proof
  fix p q r :: "'a poly"
  show 0: "0 * p = 0"
    by (rule mult_poly_0_left)
  show "p * 0 = 0"
    by (rule mult_poly_0_right)
  show "(p + q) * r = p * r + q * r"
    by (rule mult_poly_add_left)
  show "(p * q) * r = p * (q * r)"
    by (induct p) (simp_all add: mult_poly_0 mult_poly_add_left)
  show "p * q = q * p"
    by (induct p) (simp_all add: mult_poly_0)
qed

end

lemma coeff_mult_degree_sum:
  "coeff (p * q) (degree p + degree q) = coeff p (degree p) * coeff q (degree q)"
  by (induct p) (simp_all add: coeff_eq_0)

instance poly :: ("{comm_semiring_0,semiring_no_zero_divisors}") semiring_no_zero_divisors
proof
  fix p q :: "'a poly"
  assume "p \<noteq> 0" and "q \<noteq> 0"
  have "coeff (p * q) (degree p + degree q) = coeff p (degree p) * coeff q (degree q)"
    by (rule coeff_mult_degree_sum)
  also from \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> have "coeff p (degree p) * coeff q (degree q) \<noteq> 0"
    by simp
  finally have "\<exists>n. coeff (p * q) n \<noteq> 0" ..
  then show "p * q \<noteq> 0"
    by (simp add: poly_eq_iff)
qed

instance poly :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

lemma coeff_mult: "coeff (p * q) n = (\<Sum>i\<le>n. coeff p i * coeff q (n-i))"
proof (induct p arbitrary: n)
  case 0
  show ?case by simp
next
  case (pCons a p n)
  then show ?case
    by (cases n) (simp_all add: sum.atMost_Suc_shift del: sum.atMost_Suc)
qed

lemma degree_mult_le: "degree (p * q) \<le> degree p + degree q"
proof (rule degree_le)
  show "\<forall>i>degree p + degree q. coeff (p * q) i = 0"
    by (induct p) (simp_all add: coeff_eq_0 coeff_pCons split: nat.split)
qed

lemma mult_monom: "monom a m * monom b n = monom (a * b) (m + n)"
  by (induct m) (simp add: monom_0 smult_monom, simp add: monom_Suc)

instantiation poly :: (comm_semiring_1) comm_semiring_1
begin

lift_definition one_poly :: "'a poly"
  is "\<lambda>n. of_bool (n = 0)"
  by (rule MOST_SucD) simp

lemma coeff_1 [simp]:
  "coeff 1 n = of_bool (n = 0)"
  by (simp add: one_poly.rep_eq)

lemma one_pCons:
  "1 = [:1:]"
  by (simp add: poly_eq_iff coeff_pCons split: nat.splits)

lemma pCons_one:
  "[:1:] = 1"
  by (simp add: one_pCons)

instance
  by standard (simp_all add: one_pCons)

end

lemma poly_1 [simp]:
  "poly 1 x = 1"
  by (simp add: one_pCons)

lemma one_poly_eq_simps [simp]:
  "1 = [:1:] \<longleftrightarrow> True"
  "[:1:] = 1 \<longleftrightarrow> True"
  by (simp_all add: one_pCons)

lemma degree_1 [simp]:
  "degree 1 = 0"
  by (simp add: one_pCons)

lemma coeffs_1_eq [simp, code abstract]:
  "coeffs 1 = [1]"
  by (simp add: one_pCons)

lemma smult_one [simp]:
  "smult c 1 = [:c:]"
  by (simp add: one_pCons)

lemma monom_eq_1 [simp]:
  "monom 1 0 = 1"
  by (simp add: monom_0 one_pCons)

lemma monom_eq_1_iff:
  "monom c n = 1 \<longleftrightarrow> c = 1 \<and> n = 0"
  using monom_eq_const_iff [of c n 1] by auto

lemma monom_altdef:
  "monom c n = smult c ([:0, 1:] ^ n)"
  by (induct n) (simp_all add: monom_0 monom_Suc)

instance poly :: ("{comm_semiring_1,semiring_1_no_zero_divisors}") semiring_1_no_zero_divisors ..
instance poly :: (comm_ring) comm_ring ..
instance poly :: (comm_ring_1) comm_ring_1 ..
instance poly :: (comm_ring_1) comm_semiring_1_cancel ..

lemma degree_power_le: "degree (p ^ n) \<le> degree p * n"
  by (induct n) (auto intro: order_trans degree_mult_le)

lemma coeff_0_power: "coeff (p ^ n) 0 = coeff p 0 ^ n"
  by (induct n) (simp_all add: coeff_mult)

lemma poly_smult [simp]: "poly (smult a p) x = a * poly p x"
  by (induct p) (simp_all add: algebra_simps)

lemma poly_mult [simp]: "poly (p * q) x = poly p x * poly q x"
  by (induct p) (simp_all add: algebra_simps)

lemma poly_power [simp]: "poly (p ^ n) x = poly p x ^ n"
  for p :: "'a::comm_semiring_1 poly"
  by (induct n) simp_all

lemma poly_prod: "poly (\<Prod>k\<in>A. p k) x = (\<Prod>k\<in>A. poly (p k) x)"
  by (induct A rule: infinite_finite_induct) simp_all

lemma degree_prod_sum_le: "finite S \<Longrightarrow> degree (prod f S) \<le> sum (degree \<circ> f) S"
proof (induct S rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a S)
  show ?case
    unfolding prod.insert[OF insert(1-2)] sum.insert[OF insert(1-2)]
    by (rule le_trans[OF degree_mult_le]) (use insert in auto)
qed

lemma coeff_0_prod_list: "coeff (prod_list xs) 0 = prod_list (map (\<lambda>p. coeff p 0) xs)"
  by (induct xs) (simp_all add: coeff_mult)

lemma coeff_monom_mult: "coeff (monom c n * p) k = (if k < n then 0 else c * coeff p (k - n))"
proof -
  have "coeff (monom c n * p) k = (\<Sum>i\<le>k. (if n = i then c else 0) * coeff p (k - i))"
    by (simp add: coeff_mult)
  also have "\<dots> = (\<Sum>i\<le>k. (if n = i then c * coeff p (k - i) else 0))"
    by (intro sum.cong) simp_all
  also have "\<dots> = (if k < n then 0 else c * coeff p (k - n))"
    by simp
  finally show ?thesis .
qed

lemma monom_1_dvd_iff': "monom 1 n dvd p \<longleftrightarrow> (\<forall>k<n. coeff p k = 0)"
proof
  assume "monom 1 n dvd p"
  then obtain r where "p = monom 1 n * r"
    by (rule dvdE)
  then show "\<forall>k<n. coeff p k = 0"
    by (simp add: coeff_mult)
next
  assume zero: "(\<forall>k<n. coeff p k = 0)"
  define r where "r = Abs_poly (\<lambda>k. coeff p (k + n))"
  have "\<forall>\<^sub>\<infinity>k. coeff p (k + n) = 0"
    by (subst cofinite_eq_sequentially, subst eventually_sequentially_seg,
        subst cofinite_eq_sequentially [symmetric]) transfer
  then have coeff_r [simp]: "coeff r k = coeff p (k + n)" for k
    unfolding r_def by (subst poly.Abs_poly_inverse) simp_all
  have "p = monom 1 n * r"
    by (rule poly_eqI, subst coeff_monom_mult) (simp_all add: zero)
  then show "monom 1 n dvd p" by simp
qed


subsection \<open>Mapping polynomials\<close>

definition map_poly :: "('a :: zero \<Rightarrow> 'b :: zero) \<Rightarrow> 'a poly \<Rightarrow> 'b poly"
  where "map_poly f p = Poly (map f (coeffs p))"

lemma map_poly_0 [simp]: "map_poly f 0 = 0"
  by (simp add: map_poly_def)

lemma map_poly_1: "map_poly f 1 = [:f 1:]"
  by (simp add: map_poly_def)

lemma map_poly_1' [simp]: "f 1 = 1 \<Longrightarrow> map_poly f 1 = 1"
  by (simp add: map_poly_def one_pCons)

lemma coeff_map_poly:
  assumes "f 0 = 0"
  shows "coeff (map_poly f p) n = f (coeff p n)"
  by (auto simp: assms map_poly_def nth_default_def coeffs_def not_less Suc_le_eq coeff_eq_0
      simp del: upt_Suc)

lemma coeffs_map_poly [code abstract]:
  "coeffs (map_poly f p) = strip_while ((=) 0) (map f (coeffs p))"
  by (simp add: map_poly_def)

lemma coeffs_map_poly':
  assumes "\<And>x. x \<noteq> 0 \<Longrightarrow> f x \<noteq> 0"
  shows "coeffs (map_poly f p) = map f (coeffs p)"
  using assms
  by (auto simp add: coeffs_map_poly strip_while_idem_iff
    last_coeffs_eq_coeff_degree no_trailing_unfold last_map)

lemma set_coeffs_map_poly:
  "(\<And>x. f x = 0 \<longleftrightarrow> x = 0) \<Longrightarrow> set (coeffs (map_poly f p)) = f ` set (coeffs p)"
  by (simp add: coeffs_map_poly')

lemma degree_map_poly:
  assumes "\<And>x. x \<noteq> 0 \<Longrightarrow> f x \<noteq> 0"
  shows "degree (map_poly f p) = degree p"
  by (simp add: degree_eq_length_coeffs coeffs_map_poly' assms)

lemma map_poly_eq_0_iff:
  assumes "f 0 = 0" "\<And>x. x \<in> set (coeffs p) \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> f x \<noteq> 0"
  shows "map_poly f p = 0 \<longleftrightarrow> p = 0"
proof -
  have "(coeff (map_poly f p) n = 0) = (coeff p n = 0)" for n
  proof -
    have "coeff (map_poly f p) n = f (coeff p n)"
      by (simp add: coeff_map_poly assms)
    also have "\<dots> = 0 \<longleftrightarrow> coeff p n = 0"
    proof (cases "n < length (coeffs p)")
      case True
      then have "coeff p n \<in> set (coeffs p)"
        by (auto simp: coeffs_def simp del: upt_Suc)
      with assms show "f (coeff p n) = 0 \<longleftrightarrow> coeff p n = 0"
        by auto
    next
      case False
      then show ?thesis
        by (auto simp: assms length_coeffs nth_default_coeffs_eq [symmetric] nth_default_def)
    qed
    finally show ?thesis .
  qed
  then show ?thesis by (auto simp: poly_eq_iff)
qed

lemma map_poly_smult:
  assumes "f 0 = 0""\<And>c x. f (c * x) = f c * f x"
  shows "map_poly f (smult c p) = smult (f c) (map_poly f p)"
  by (intro poly_eqI) (simp_all add: assms coeff_map_poly)

lemma map_poly_pCons:
  assumes "f 0 = 0"
  shows "map_poly f (pCons c p) = pCons (f c) (map_poly f p)"
  by (intro poly_eqI) (simp_all add: assms coeff_map_poly coeff_pCons split: nat.splits)

lemma map_poly_map_poly:
  assumes "f 0 = 0" "g 0 = 0"
  shows "map_poly f (map_poly g p) = map_poly (f \<circ> g) p"
  by (intro poly_eqI) (simp add: coeff_map_poly assms)

lemma map_poly_id [simp]: "map_poly id p = p"
  by (simp add: map_poly_def)

lemma map_poly_id' [simp]: "map_poly (\<lambda>x. x) p = p"
  by (simp add: map_poly_def)

lemma map_poly_cong:
  assumes "(\<And>x. x \<in> set (coeffs p) \<Longrightarrow> f x = g x)"
  shows "map_poly f p = map_poly g p"
proof -
  from assms have "map f (coeffs p) = map g (coeffs p)"
    by (intro map_cong) simp_all
  then show ?thesis
    by (simp only: coeffs_eq_iff coeffs_map_poly)
qed

lemma map_poly_monom: "f 0 = 0 \<Longrightarrow> map_poly f (monom c n) = monom (f c) n"
  by (intro poly_eqI) (simp_all add: coeff_map_poly)

lemma map_poly_idI:
  assumes "\<And>x. x \<in> set (coeffs p) \<Longrightarrow> f x = x"
  shows "map_poly f p = p"
  using map_poly_cong[OF assms, of _ id] by simp

lemma map_poly_idI':
  assumes "\<And>x. x \<in> set (coeffs p) \<Longrightarrow> f x = x"
  shows "p = map_poly f p"
  using map_poly_cong[OF assms, of _ id] by simp

lemma smult_conv_map_poly: "smult c p = map_poly (\<lambda>x. c * x) p"
  by (intro poly_eqI) (simp_all add: coeff_map_poly)


subsection \<open>Conversions\<close>

lemma of_nat_poly:
  "of_nat n = [:of_nat n:]"
  by (induct n) (simp_all add: one_pCons)

lemma of_nat_monom:
  "of_nat n = monom (of_nat n) 0"
  by (simp add: of_nat_poly monom_0)

lemma degree_of_nat [simp]:
  "degree (of_nat n) = 0"
  by (simp add: of_nat_poly)

lemma lead_coeff_of_nat [simp]:
  "lead_coeff (of_nat n) = of_nat n"
  by (simp add: of_nat_poly)

lemma of_int_poly:
  "of_int k = [:of_int k:]"
  by (simp only: of_int_of_nat of_nat_poly) simp

lemma of_int_monom:
  "of_int k = monom (of_int k) 0"
  by (simp add: of_int_poly monom_0)

lemma degree_of_int [simp]:
  "degree (of_int k) = 0"
  by (simp add: of_int_poly)

lemma lead_coeff_of_int [simp]:
  "lead_coeff (of_int k) = of_int k"
  by (simp add: of_int_poly)

lemma numeral_poly: "numeral n = [:numeral n:]"
proof -
  have "numeral n = of_nat (numeral n)"
    by simp
  also have "\<dots> = [:of_nat (numeral n):]"
    by (simp add: of_nat_poly)
  finally show ?thesis
    by simp
qed

lemma numeral_monom:
  "numeral n = monom (numeral n) 0"
  by (simp add: numeral_poly monom_0)

lemma degree_numeral [simp]:
  "degree (numeral n) = 0"
  by (simp add: numeral_poly)

lemma lead_coeff_numeral [simp]:
  "lead_coeff (numeral n) = numeral n"
  by (simp add: numeral_poly)


subsection \<open>Lemmas about divisibility\<close>

lemma dvd_smult:
  assumes "p dvd q"
  shows "p dvd smult a q"
proof -
  from assms obtain k where "q = p * k" ..
  then have "smult a q = p * smult a k" by simp
  then show "p dvd smult a q" ..
qed

lemma dvd_smult_cancel: "p dvd smult a q \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> p dvd q"
  for a :: "'a::field"
  by (drule dvd_smult [where a="inverse a"]) simp

lemma dvd_smult_iff: "a \<noteq> 0 \<Longrightarrow> p dvd smult a q \<longleftrightarrow> p dvd q"
  for a :: "'a::field"
  by (safe elim!: dvd_smult dvd_smult_cancel)

lemma smult_dvd_cancel:
  assumes "smult a p dvd q"
  shows "p dvd q"
proof -
  from assms obtain k where "q = smult a p * k" ..
  then have "q = p * smult a k" by simp
  then show "p dvd q" ..
qed

lemma smult_dvd: "p dvd q \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> smult a p dvd q"
  for a :: "'a::field"
  by (rule smult_dvd_cancel [where a="inverse a"]) simp

lemma smult_dvd_iff: "smult a p dvd q \<longleftrightarrow> (if a = 0 then q = 0 else p dvd q)"
  for a :: "'a::field"
  by (auto elim: smult_dvd smult_dvd_cancel)

lemma is_unit_smult_iff: "smult c p dvd 1 \<longleftrightarrow> c dvd 1 \<and> p dvd 1"
proof -
  have "smult c p = [:c:] * p" by simp
  also have "\<dots> dvd 1 \<longleftrightarrow> c dvd 1 \<and> p dvd 1"
  proof safe
    assume *: "[:c:] * p dvd 1"
    then show "p dvd 1"
      by (rule dvd_mult_right)
    from * obtain q where q: "1 = [:c:] * p * q"
      by (rule dvdE)
    have "c dvd c * (coeff p 0 * coeff q 0)"
      by simp
    also have "\<dots> = coeff ([:c:] * p * q) 0"
      by (simp add: mult.assoc coeff_mult)
    also note q [symmetric]
    finally have "c dvd coeff 1 0" .
    then show "c dvd 1" by simp
  next
    assume "c dvd 1" "p dvd 1"
    from this(1) obtain d where "1 = c * d"
      by (rule dvdE)
    then have "1 = [:c:] * [:d:]"
      by (simp add: one_pCons ac_simps)
    then have "[:c:] dvd 1"
      by (rule dvdI)
    from mult_dvd_mono[OF this \<open>p dvd 1\<close>] show "[:c:] * p dvd 1"
      by simp
  qed
  finally show ?thesis .
qed


subsection \<open>Polynomials form an integral domain\<close>

instance poly :: (idom) idom ..

instance poly :: ("{ring_char_0, comm_ring_1}") ring_char_0
  by standard (auto simp add: of_nat_poly intro: injI)

lemma degree_mult_eq: "p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> degree (p * q) = degree p + degree q"
  for p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  by (rule order_antisym [OF degree_mult_le le_degree]) (simp add: coeff_mult_degree_sum)

lemma degree_prod_eq_sum_degree:
  fixes A :: "'a set"
  and f :: "'a \<Rightarrow> 'b::idom poly"
  assumes f0: "\<forall>i\<in>A. f i \<noteq> 0"
  shows "degree (\<Prod>i\<in>A. (f i)) = (\<Sum>i\<in>A. degree (f i))"
  using assms
  by (induction A rule: infinite_finite_induct) (auto simp: degree_mult_eq)

lemma degree_mult_eq_0:
  "degree (p * q) = 0 \<longleftrightarrow> p = 0 \<or> q = 0 \<or> (p \<noteq> 0 \<and> q \<noteq> 0 \<and> degree p = 0 \<and> degree q = 0)"
  for p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  by (auto simp: degree_mult_eq)

lemma degree_power_eq: "p \<noteq> 0 \<Longrightarrow> degree ((p :: 'a :: idom poly) ^ n) = n * degree p"
  by (induction n) (simp_all add: degree_mult_eq)

lemma degree_mult_right_le:
  fixes p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  assumes "q \<noteq> 0"
  shows "degree p \<le> degree (p * q)"
  using assms by (cases "p = 0") (simp_all add: degree_mult_eq)

lemma coeff_degree_mult: "coeff (p * q) (degree (p * q)) = coeff q (degree q) * coeff p (degree p)"
  for p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  by (cases "p = 0 \<or> q = 0") (auto simp: degree_mult_eq coeff_mult_degree_sum mult_ac)

lemma dvd_imp_degree_le: "p dvd q \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> degree p \<le> degree q"
  for p q :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  by (erule dvdE, hypsubst, subst degree_mult_eq) auto

lemma divides_degree:
  fixes p q :: "'a ::{comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "p dvd q"
  shows "degree p \<le> degree q \<or> q = 0"
  by (metis dvd_imp_degree_le assms)

lemma const_poly_dvd_iff:
  fixes c :: "'a::{comm_semiring_1,semiring_no_zero_divisors}"
  shows "[:c:] dvd p \<longleftrightarrow> (\<forall>n. c dvd coeff p n)"
proof (cases "c = 0 \<or> p = 0")
  case True
  then show ?thesis
    by (auto intro!: poly_eqI)
next
  case False
  show ?thesis
  proof
    assume "[:c:] dvd p"
    then show "\<forall>n. c dvd coeff p n"
      by (auto elim!: dvdE simp: coeffs_def)
  next
    assume *: "\<forall>n. c dvd coeff p n"
    define mydiv where "mydiv x y = (SOME z. x = y * z)" for x y :: 'a
    have mydiv: "x = y * mydiv x y" if "y dvd x" for x y
      using that unfolding mydiv_def dvd_def by (rule someI_ex)
    define q where "q = Poly (map (\<lambda>a. mydiv a c) (coeffs p))"
    from False * have "p = q * [:c:]"
      by (intro poly_eqI)
        (auto simp: q_def nth_default_def not_less length_coeffs_degree coeffs_nth
          intro!: coeff_eq_0 mydiv)
    then show "[:c:] dvd p"
      by (simp only: dvd_triv_right)
  qed
qed

lemma const_poly_dvd_const_poly_iff [simp]: "[:a:] dvd [:b:] \<longleftrightarrow> a dvd b"
  for a b :: "'a::{comm_semiring_1,semiring_no_zero_divisors}"
  by (subst const_poly_dvd_iff) (auto simp: coeff_pCons split: nat.splits)

lemma lead_coeff_mult: "lead_coeff (p * q) = lead_coeff p * lead_coeff q"
  for p q :: "'a::{comm_semiring_0, semiring_no_zero_divisors} poly"
  by (cases "p = 0 \<or> q = 0") (auto simp: coeff_mult_degree_sum degree_mult_eq)

lemma lead_coeff_prod: "lead_coeff (prod f A) = (\<Prod>x\<in>A. lead_coeff (f x))"
  for f :: "'a \<Rightarrow> 'b::{comm_semiring_1, semiring_no_zero_divisors} poly"
  by (induction A rule: infinite_finite_induct) (auto simp: lead_coeff_mult)

lemma lead_coeff_smult: "lead_coeff (smult c p) = c * lead_coeff p"
  for p :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
proof -
  have "smult c p = [:c:] * p" by simp
  also have "lead_coeff \<dots> = c * lead_coeff p"
    by (subst lead_coeff_mult) simp_all
  finally show ?thesis .
qed

lemma lead_coeff_1 [simp]: "lead_coeff 1 = 1"
  by simp

lemma lead_coeff_power: "lead_coeff (p ^ n) = lead_coeff p ^ n"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  by (induct n) (simp_all add: lead_coeff_mult)


subsection \<open>Polynomials form an ordered integral domain\<close>

definition pos_poly :: "'a::linordered_semidom poly \<Rightarrow> bool"
  where "pos_poly p \<longleftrightarrow> 0 < coeff p (degree p)"

lemma pos_poly_pCons: "pos_poly (pCons a p) \<longleftrightarrow> pos_poly p \<or> (p = 0 \<and> 0 < a)"
  by (simp add: pos_poly_def)

lemma not_pos_poly_0 [simp]: "\<not> pos_poly 0"
  by (simp add: pos_poly_def)

lemma pos_poly_add: "pos_poly p \<Longrightarrow> pos_poly q \<Longrightarrow> pos_poly (p + q)"
proof (induction p arbitrary: q)
  case (pCons a p)
  then show ?case
    by (cases q; force simp add: pos_poly_pCons add_pos_pos)
qed auto

lemma pos_poly_mult: "pos_poly p \<Longrightarrow> pos_poly q \<Longrightarrow> pos_poly (p * q)"
  by (simp add: pos_poly_def coeff_degree_mult)

lemma pos_poly_total: "p = 0 \<or> pos_poly p \<or> pos_poly (- p)"
  for p :: "'a::linordered_idom poly"
  by (induct p) (auto simp: pos_poly_pCons)

lemma pos_poly_coeffs [code]: "pos_poly p \<longleftrightarrow> (let as = coeffs p in as \<noteq> [] \<and> last as > 0)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then show ?lhs
    by (auto simp add: pos_poly_def last_coeffs_eq_coeff_degree)
next
  assume ?lhs
  then have *: "0 < coeff p (degree p)"
    by (simp add: pos_poly_def)
  then have "p \<noteq> 0"
    by auto
  with * show ?rhs
    by (simp add: last_coeffs_eq_coeff_degree)
qed

instantiation poly :: (linordered_idom) linordered_idom
begin

definition "x < y \<longleftrightarrow> pos_poly (y - x)"

definition "x \<le> y \<longleftrightarrow> x = y \<or> pos_poly (y - x)"

definition "\<bar>x::'a poly\<bar> = (if x < 0 then - x else x)"

definition "sgn (x::'a poly) = (if x = 0 then 0 else if 0 < x then 1 else - 1)"

instance
proof
  fix x y z :: "'a poly"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    unfolding less_eq_poly_def less_poly_def
    using pos_poly_add by force
  then show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    using less_eq_poly_def less_poly_def by force
  show "x \<le> x"
    by (simp add: less_eq_poly_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    using less_eq_poly_def pos_poly_add by fastforce
  show "x \<le> y \<Longrightarrow> z + x \<le> z + y"
    by (simp add: less_eq_poly_def)
  show "x \<le> y \<or> y \<le> x"
    unfolding less_eq_poly_def
    using pos_poly_total [of "x - y"]
    by auto
  show "x < y \<Longrightarrow> 0 < z \<Longrightarrow> z * x < z * y"
    by (simp add: less_poly_def right_diff_distrib [symmetric] pos_poly_mult)
  show "\<bar>x\<bar> = (if x < 0 then - x else x)"
    by (rule abs_poly_def)
  show "sgn x = (if x = 0 then 0 else if 0 < x then 1 else - 1)"
    by (rule sgn_poly_def)
qed

end

text \<open>TODO: Simplification rules for comparisons\<close>


subsection \<open>Synthetic division and polynomial roots\<close>

subsubsection \<open>Synthetic division\<close>

text \<open>Synthetic division is simply division by the linear polynomial \<^term>\<open>x - c\<close>.\<close>

definition synthetic_divmod :: "'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a poly \<times> 'a"
  where "synthetic_divmod p c = fold_coeffs (\<lambda>a (q, r). (pCons r q, a + c * r)) p (0, 0)"

definition synthetic_div :: "'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a poly"
  where "synthetic_div p c = fst (synthetic_divmod p c)"

lemma synthetic_divmod_0 [simp]: "synthetic_divmod 0 c = (0, 0)"
  by (simp add: synthetic_divmod_def)

lemma synthetic_divmod_pCons [simp]:
  "synthetic_divmod (pCons a p) c = (\<lambda>(q, r). (pCons r q, a + c * r)) (synthetic_divmod p c)"
  by (cases "p = 0 \<and> a = 0") (auto simp add: synthetic_divmod_def)

lemma synthetic_div_0 [simp]: "synthetic_div 0 c = 0"
  by (simp add: synthetic_div_def)

lemma synthetic_div_unique_lemma: "smult c p = pCons a p \<Longrightarrow> p = 0"
  by (induct p arbitrary: a) simp_all

lemma snd_synthetic_divmod: "snd (synthetic_divmod p c) = poly p c"
  by (induct p) (simp_all add: split_def)

lemma synthetic_div_pCons [simp]:
  "synthetic_div (pCons a p) c = pCons (poly p c) (synthetic_div p c)"
  by (simp add: synthetic_div_def split_def snd_synthetic_divmod)

lemma synthetic_div_eq_0_iff: "synthetic_div p c = 0 \<longleftrightarrow> degree p = 0"
proof (induct p)
  case 0
  then show ?case by simp
next
  case (pCons a p)
  then show ?case by (cases p) simp
qed

lemma degree_synthetic_div: "degree (synthetic_div p c) = degree p - 1"
  by (induct p) (simp_all add: synthetic_div_eq_0_iff)

lemma synthetic_div_correct:
  "p + smult c (synthetic_div p c) = pCons (poly p c) (synthetic_div p c)"
  by (induct p) simp_all

lemma synthetic_div_unique: "p + smult c q = pCons r q \<Longrightarrow> r = poly p c \<and> q = synthetic_div p c"
proof (induction p arbitrary: q r)
  case 0
  then show ?case
    using synthetic_div_unique_lemma by fastforce
next
  case (pCons a p)
  then show ?case
    by (cases q; force)
qed

lemma synthetic_div_correct': "[:-c, 1:] * synthetic_div p c + [:poly p c:] = p"
  for c :: "'a::comm_ring_1"
  using synthetic_div_correct [of p c] by (simp add: algebra_simps)


subsubsection \<open>Polynomial roots\<close>

lemma poly_eq_0_iff_dvd: "poly p c = 0 \<longleftrightarrow> [:- c, 1:] dvd p"
  (is "?lhs \<longleftrightarrow> ?rhs")
  for c :: "'a::comm_ring_1"
proof
  assume ?lhs
  with synthetic_div_correct' [of c p] have "p = [:-c, 1:] * synthetic_div p c" by simp
  then show ?rhs ..
next
  assume ?rhs
  then obtain k where "p = [:-c, 1:] * k" by (rule dvdE)
  then show ?lhs by simp
qed

lemma dvd_iff_poly_eq_0: "[:c, 1:] dvd p \<longleftrightarrow> poly p (- c) = 0"
  for c :: "'a::comm_ring_1"
  by (simp add: poly_eq_0_iff_dvd)

lemma poly_roots_finite: "p \<noteq> 0 \<Longrightarrow> finite {x. poly p x = 0}"
  for p :: "'a::{comm_ring_1,ring_no_zero_divisors} poly"
proof (induct n \<equiv> "degree p" arbitrary: p)
  case 0
  then obtain a where "a \<noteq> 0" and "p = [:a:]"
    by (cases p) (simp split: if_splits)
  then show "finite {x. poly p x = 0}"
    by simp
next
  case (Suc n)
  show "finite {x. poly p x = 0}"
  proof (cases "\<exists>x. poly p x = 0")
    case False
    then show "finite {x. poly p x = 0}" by simp
  next
    case True
    then obtain a where "poly p a = 0" ..
    then have "[:-a, 1:] dvd p"
      by (simp only: poly_eq_0_iff_dvd)
    then obtain k where k: "p = [:-a, 1:] * k" ..
    with \<open>p \<noteq> 0\<close> have "k \<noteq> 0"
      by auto
    with k have "degree p = Suc (degree k)"
      by (simp add: degree_mult_eq del: mult_pCons_left)
    with \<open>Suc n = degree p\<close> have "n = degree k"
      by simp
    from this \<open>k \<noteq> 0\<close> have "finite {x. poly k x = 0}"
      by (rule Suc.hyps)
    then have "finite (insert a {x. poly k x = 0})"
      by simp
    then show "finite {x. poly p x = 0}"
      by (simp add: k Collect_disj_eq del: mult_pCons_left)
  qed
qed

lemma poly_eq_poly_eq_iff: "poly p = poly q \<longleftrightarrow> p = q"
  (is "?lhs \<longleftrightarrow> ?rhs")
  for p q :: "'a::{comm_ring_1,ring_no_zero_divisors,ring_char_0} poly"
proof
  assume ?rhs
  then show ?lhs by simp
next
  assume ?lhs
  have "poly p = poly 0 \<longleftrightarrow> p = 0" for p :: "'a poly"
  proof (cases "p = 0")
    case False
    then show ?thesis
      by (auto simp add: infinite_UNIV_char_0 dest: poly_roots_finite)
  qed auto
  from \<open>?lhs\<close> and this [of "p - q"] show ?rhs
    by auto
qed

lemma poly_all_0_iff_0: "(\<forall>x. poly p x = 0) \<longleftrightarrow> p = 0"
  for p :: "'a::{ring_char_0,comm_ring_1,ring_no_zero_divisors} poly"
  by (auto simp add: poly_eq_poly_eq_iff [symmetric])


subsubsection \<open>Order of polynomial roots\<close>

definition order :: "'a::idom \<Rightarrow> 'a poly \<Rightarrow> nat"
  where "order a p = (LEAST n. \<not> [:-a, 1:] ^ Suc n dvd p)"

lemma coeff_linear_power: "coeff ([:a, 1:] ^ n) n = 1"
  for a :: "'a::comm_semiring_1"
proof (induct n)
  case (Suc n)
  have "degree ([:a, 1:] ^ n) \<le> 1 * n"
    by (metis One_nat_def degree_pCons_eq_if degree_power_le one_neq_zero one_pCons)
  then have "coeff ([:a, 1:] ^ n) (Suc n) = 0"
    by (simp add: coeff_eq_0)
  then show ?case
    using Suc.hyps by fastforce
qed auto

lemma degree_linear_power: "degree ([:a, 1:] ^ n) = n"
  for a :: "'a::comm_semiring_1"
proof (rule order_antisym)
  show "degree ([:a, 1:] ^ n) \<le> n"
    by (metis One_nat_def degree_pCons_eq_if degree_power_le mult.left_neutral one_neq_zero one_pCons)
qed (simp add: coeff_linear_power le_degree)

lemma order_1: "[:-a, 1:] ^ order a p dvd p"
proof (cases "p = 0")
  case False
  show ?thesis
  proof (cases "order a p")
    case (Suc n)
    then show ?thesis
      by (metis lessI not_less_Least order_def)
  qed auto
qed auto

lemma order_2:
  assumes "p \<noteq> 0"
  shows "\<not> [:-a, 1:] ^ Suc (order a p) dvd p"
proof -
  have False if "[:- a, 1:] ^ Suc (degree p) dvd p"
    using dvd_imp_degree_le [OF that]
    by (metis Suc_n_not_le_n assms degree_linear_power)
  then show ?thesis
    unfolding order_def
    by (metis (no_types, lifting) LeastI)
qed

lemma order: "p \<noteq> 0 \<Longrightarrow> [:-a, 1:] ^ order a p dvd p \<and> \<not> [:-a, 1:] ^ Suc (order a p) dvd p"
  by (rule conjI [OF order_1 order_2])

lemma order_degree:
  assumes p: "p \<noteq> 0"
  shows "order a p \<le> degree p"
proof -
  have "order a p = degree ([:-a, 1:] ^ order a p)"
    by (simp only: degree_linear_power)
  also from order_1 p have "\<dots> \<le> degree p"
    by (rule dvd_imp_degree_le)
  finally show ?thesis .
qed

lemma order_root: "poly p a = 0 \<longleftrightarrow> p = 0 \<or> order a p \<noteq> 0" (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (metis One_nat_def order_2 poly_eq_0_iff_dvd power_one_right)
  show "?rhs \<Longrightarrow> ?lhs"
    by (meson dvd_power dvd_trans neq0_conv order_1 poly_0 poly_eq_0_iff_dvd)
qed

lemma order_0I: "poly p a \<noteq> 0 \<Longrightarrow> order a p = 0"
  by (subst (asm) order_root) auto

lemma order_unique_lemma:
  fixes p :: "'a::idom poly"
  assumes "[:-a, 1:] ^ n dvd p" "\<not> [:-a, 1:] ^ Suc n dvd p"
  shows "order a p = n"
  unfolding Polynomial.order_def
  by (metis (mono_tags, lifting) Least_equality assms not_less_eq_eq power_le_dvd)

lemma order_mult:
  assumes "p * q \<noteq> 0" shows "order a (p * q) = order a p + order a q"
proof -
  define i where "i \<equiv> order a p"
  define j where "j \<equiv> order a q"
  define t where "t \<equiv> [:-a, 1:]"
  have t_dvd_iff: "\<And>u. t dvd u \<longleftrightarrow> poly u a = 0"
    by (simp add: t_def dvd_iff_poly_eq_0)
  have dvd: "t ^ i dvd p" "t ^ j dvd q" and "\<not> t ^ Suc i dvd p" "\<not> t ^ Suc j dvd q"
    using assms i_def j_def order_1 order_2 t_def by auto
  then have "\<not> t ^ Suc(i + j) dvd p * q"
    by (elim dvdE) (simp add: power_add t_dvd_iff)
  moreover have "t ^ (i + j) dvd p * q"
    using dvd by (simp add: mult_dvd_mono power_add)
  ultimately show "order a (p * q) = i + j"
    using order_unique_lemma t_def by blast
qed


lemma order_smult:
  assumes "c \<noteq> 0"
  shows "order x (smult c p) = order x p"
proof (cases "p = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  have "smult c p = [:c:] * p" by simp
  also from assms False have "order x \<dots> = order x [:c:] + order x p"
    by (subst order_mult) simp_all
  also have "order x [:c:] = 0"
    by (rule order_0I) (use assms in auto)
  finally show ?thesis
    by simp
qed

text \<open>Next three lemmas contributed by Wenda Li\<close>
lemma order_1_eq_0 [simp]:"order x 1 = 0"
  by (metis order_root poly_1 zero_neq_one)

lemma order_uminus[simp]: "order x (-p) = order x p"
  by (metis neg_equal_0_iff_equal order_smult smult_1_left smult_minus_left)

lemma order_power_n_n: "order a ([:-a,1:]^n)=n"
proof (induct n) (*might be proved more concisely using nat_less_induct*)
  case 0
  then show ?case
    by (metis order_root poly_1 power_0 zero_neq_one)
next
  case (Suc n)
  have "order a ([:- a, 1:] ^ Suc n) = order a ([:- a, 1:] ^ n) + order a [:-a,1:]"
    by (metis (no_types, opaque_lifting) One_nat_def add_Suc_right monoid_add_class.add.right_neutral
      one_neq_zero order_mult pCons_eq_0_iff power_add power_eq_0_iff power_one_right)
  moreover have "order a [:-a,1:] = 1"
    unfolding order_def
  proof (rule Least_equality, rule notI)
    assume "[:- a, 1:] ^ Suc 1 dvd [:- a, 1:]"
    then have "degree ([:- a, 1:] ^ Suc 1) \<le> degree ([:- a, 1:])"
      by (rule dvd_imp_degree_le) auto
    then show False
      by auto
  next
    fix y
    assume *: "\<not> [:- a, 1:] ^ Suc y dvd [:- a, 1:]"
    show "1 \<le> y"
    proof (rule ccontr)
      assume "\<not> 1 \<le> y"
      then have "y = 0" by auto
      then have "[:- a, 1:] ^ Suc y dvd [:- a, 1:]" by auto
      with * show False by auto
    qed
  qed
  ultimately show ?case
    using Suc by auto
qed

lemma order_0_monom [simp]: "c \<noteq> 0 \<Longrightarrow> order 0 (monom c n) = n"
  using order_power_n_n[of 0 n] by (simp add: monom_altdef order_smult)

lemma dvd_imp_order_le: "q \<noteq> 0 \<Longrightarrow> p dvd q \<Longrightarrow> Polynomial.order a p \<le> Polynomial.order a q"
  by (auto simp: order_mult elim: dvdE)

text \<open>Now justify the standard squarefree decomposition, i.e. \<open>f / gcd f f'\<close>.\<close>

lemma order_divides: "[:-a, 1:] ^ n dvd p \<longleftrightarrow> p = 0 \<or> n \<le> order a p"
  by (meson dvd_0_right not_less_eq_eq order_1 order_2 power_le_dvd)

lemma order_decomp:
  assumes "p \<noteq> 0"
  shows "\<exists>q. p = [:- a, 1:] ^ order a p * q \<and> \<not> [:- a, 1:] dvd q"
proof -
  from assms have *: "[:- a, 1:] ^ order a p dvd p"
    and **: "\<not> [:- a, 1:] ^ Suc (order a p) dvd p"
    by (auto dest: order)
  from * obtain q where q: "p = [:- a, 1:] ^ order a p * q" ..
  with ** have "\<not> [:- a, 1:] ^ Suc (order a p) dvd [:- a, 1:] ^ order a p * q"
    by simp
  then have "\<not> [:- a, 1:] ^ order a p * [:- a, 1:] dvd [:- a, 1:] ^ order a p * q"
    by simp
  with idom_class.dvd_mult_cancel_left [of "[:- a, 1:] ^ order a p" "[:- a, 1:]" q]
  have "\<not> [:- a, 1:] dvd q" by auto
  with q show ?thesis by blast
qed

lemma monom_1_dvd_iff: "p \<noteq> 0 \<Longrightarrow> monom 1 n dvd p \<longleftrightarrow> n \<le> order 0 p"
  using order_divides[of 0 n p] by (simp add: monom_altdef)


subsection \<open>Additional induction rules on polynomials\<close>

text \<open>
  An induction rule for induction over the roots of a polynomial with a certain property.
  (e.g. all positive roots)
\<close>
lemma poly_root_induct [case_names 0 no_roots root]:
  fixes p :: "'a :: idom poly"
  assumes "Q 0"
    and "\<And>p. (\<And>a. P a \<Longrightarrow> poly p a \<noteq> 0) \<Longrightarrow> Q p"
    and "\<And>a p. P a \<Longrightarrow> Q p \<Longrightarrow> Q ([:a, -1:] * p)"
  shows "Q p"
proof (induction "degree p" arbitrary: p rule: less_induct)
  case (less p)
  show ?case
  proof (cases "p = 0")
    case True
    with assms(1) show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "\<exists>a. P a \<and> poly p a = 0")
      case False
      then show ?thesis by (intro assms(2)) blast
    next
      case True
      then obtain a where a: "P a" "poly p a = 0"
        by blast
      then have "-[:-a, 1:] dvd p"
        by (subst minus_dvd_iff) (simp add: poly_eq_0_iff_dvd)
      then obtain q where q: "p = [:a, -1:] * q" by (elim dvdE) simp
      with False have "q \<noteq> 0" by auto
      have "degree p = Suc (degree q)"
        by (subst q, subst degree_mult_eq) (simp_all add: \<open>q \<noteq> 0\<close>)
      then have "Q q" by (intro less) simp
      with a(1) have "Q ([:a, -1:] * q)"
        by (rule assms(3))
      with q show ?thesis by simp
    qed
  qed
qed

lemma dropWhile_replicate_append:
  "dropWhile ((=) a) (replicate n a @ ys) = dropWhile ((=) a) ys"
  by (induct n) simp_all

lemma Poly_append_replicate_0: "Poly (xs @ replicate n 0) = Poly xs"
  by (subst coeffs_eq_iff) (simp_all add: strip_while_def dropWhile_replicate_append)

text \<open>
  An induction rule for simultaneous induction over two polynomials,
  prepending one coefficient in each step.
\<close>
lemma poly_induct2 [case_names 0 pCons]:
  assumes "P 0 0" "\<And>a p b q. P p q \<Longrightarrow> P (pCons a p) (pCons b q)"
  shows "P p q"
proof -
  define n where "n = max (length (coeffs p)) (length (coeffs q))"
  define xs where "xs = coeffs p @ (replicate (n - length (coeffs p)) 0)"
  define ys where "ys = coeffs q @ (replicate (n - length (coeffs q)) 0)"
  have "length xs = length ys"
    by (simp add: xs_def ys_def n_def)
  then have "P (Poly xs) (Poly ys)"
    by (induct rule: list_induct2) (simp_all add: assms)
  also have "Poly xs = p"
    by (simp add: xs_def Poly_append_replicate_0)
  also have "Poly ys = q"
    by (simp add: ys_def Poly_append_replicate_0)
  finally show ?thesis .
qed


subsection \<open>Composition of polynomials\<close>

(* Several lemmas contributed by René Thiemann and Akihisa Yamada *)

definition pcompose :: "'a::comm_semiring_0 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  where "pcompose p q = fold_coeffs (\<lambda>a c. [:a:] + q * c) p 0"

notation pcompose (infixl "\<circ>\<^sub>p" 71)

lemma pcompose_0 [simp]: "pcompose 0 q = 0"
  by (simp add: pcompose_def)

lemma pcompose_pCons: "pcompose (pCons a p) q = [:a:] + q * pcompose p q"
  by (cases "p = 0 \<and> a = 0") (auto simp add: pcompose_def)

lemma pcompose_1: "pcompose 1 p = 1"
  for p :: "'a::comm_semiring_1 poly"
  by (auto simp: one_pCons pcompose_pCons)

lemma poly_pcompose: "poly (pcompose p q) x = poly p (poly q x)"
  by (induct p) (simp_all add: pcompose_pCons)

lemma degree_pcompose_le: "degree (pcompose p q) \<le> degree p * degree q"
proof (induction p)
  case (pCons a p)
  then show ?case
  proof (clarsimp simp add: pcompose_pCons)
    assume "degree (p \<circ>\<^sub>p q) \<le> degree p * degree q" "p \<noteq> 0"
    then have "degree (q * p \<circ>\<^sub>p q) \<le> degree q + degree p * degree q"
      by (meson add_le_cancel_left degree_mult_le dual_order.trans pCons.IH)
    then show "degree ([:a:] + q * p \<circ>\<^sub>p q) \<le> degree q + degree p * degree q"
      by (simp add: degree_add_le)
  qed
qed auto

lemma pcompose_add: "pcompose (p + q) r = pcompose p r + pcompose q r"
  for p q r :: "'a::{comm_semiring_0, ab_semigroup_add} poly"
proof (induction p q rule: poly_induct2)
  case 0
  then show ?case by simp
next
  case (pCons a p b q)
  have "pcompose (pCons a p + pCons b q) r = [:a + b:] + r * pcompose p r + r * pcompose q r"
    by (simp_all add: pcompose_pCons pCons.IH algebra_simps)
  also have "[:a + b:] = [:a:] + [:b:]" by simp
  also have "\<dots> + r * pcompose p r + r * pcompose q r = pcompose (pCons a p) r + pcompose (pCons b q) r"
    by (simp only: pcompose_pCons add_ac)
  finally show ?case .
qed

lemma pcompose_uminus: "pcompose (-p) r = -pcompose p r"
  for p r :: "'a::comm_ring poly"
  by (induct p) (simp_all add: pcompose_pCons)

lemma pcompose_diff: "pcompose (p - q) r = pcompose p r - pcompose q r"
  for p q r :: "'a::comm_ring poly"
  using pcompose_add[of p "-q"] by (simp add: pcompose_uminus)

lemma pcompose_smult: "pcompose (smult a p) r = smult a (pcompose p r)"
  for p r :: "'a::comm_semiring_0 poly"
  by (induct p) (simp_all add: pcompose_pCons pcompose_add smult_add_right)

lemma pcompose_mult: "pcompose (p * q) r = pcompose p r * pcompose q r"
  for p q r :: "'a::comm_semiring_0 poly"
  by (induct p arbitrary: q) (simp_all add: pcompose_add pcompose_smult pcompose_pCons algebra_simps)

lemma pcompose_assoc: "pcompose p (pcompose q r) = pcompose (pcompose p q) r"
  for p q r :: "'a::comm_semiring_0 poly"
  by (induct p arbitrary: q) (simp_all add: pcompose_pCons pcompose_add pcompose_mult)

lemma pcompose_idR[simp]: "pcompose p [: 0, 1 :] = p"
  for p :: "'a::comm_semiring_1 poly"
  by (induct p) (simp_all add: pcompose_pCons)

lemma pcompose_sum: "pcompose (sum f A) p = sum (\<lambda>i. pcompose (f i) p) A"
  by (induct A rule: infinite_finite_induct) (simp_all add: pcompose_1 pcompose_add)

lemma pcompose_prod: "pcompose (prod f A) p = prod (\<lambda>i. pcompose (f i) p) A"
  by (induct A rule: infinite_finite_induct) (simp_all add: pcompose_1 pcompose_mult)

lemma pcompose_const [simp]: "pcompose [:a:] q = [:a:]"
  by (subst pcompose_pCons) simp

lemma pcompose_0': "pcompose p 0 = [:coeff p 0:]"
  by (induct p) (auto simp add: pcompose_pCons)

lemma degree_pcompose: "degree (pcompose p q) = degree p * degree q"
  for p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
proof (induct p)
  case 0
  then show ?case by auto
next
  case (pCons a p)
  consider "degree (q * pcompose p q) = 0" | "degree (q * pcompose p q) > 0"
    by blast
  then show ?case
  proof cases
    case prems: 1
    show ?thesis
    proof (cases "p = 0")
      case True
      then show ?thesis by auto
    next
      case False
      from prems have "degree q = 0 \<or> pcompose p q = 0"
        by (auto simp add: degree_mult_eq_0)
      moreover have False if "pcompose p q = 0" "degree q \<noteq> 0"
      proof -
        from pCons.hyps(2) that have "degree p = 0"
          by auto
        then obtain a1 where "p = [:a1:]"
          by (metis degree_pCons_eq_if old.nat.distinct(2) pCons_cases)
        with \<open>pcompose p q = 0\<close> \<open>p \<noteq> 0\<close> show False
          by auto
      qed
      ultimately have "degree (pCons a p) * degree q = 0"
        by auto
      moreover have "degree (pcompose (pCons a p) q) = 0"
      proof -
        from prems have "0 = max (degree [:a:]) (degree (q * pcompose p q))"
          by simp
        also have "\<dots> \<ge> degree ([:a:] + q * pcompose p q)"
          by (rule degree_add_le_max)
        finally show ?thesis
          by (auto simp add: pcompose_pCons)
      qed
      ultimately show ?thesis by simp
    qed
  next
    case prems: 2
    then have "p \<noteq> 0" "q \<noteq> 0" "pcompose p q \<noteq> 0"
      by auto
    from prems degree_add_eq_right [of "[:a:]"]
    have "degree (pcompose (pCons a p) q) = degree (q * pcompose p q)"
      by (auto simp: pcompose_pCons)
    with pCons.hyps(2) degree_mult_eq[OF \<open>q\<noteq>0\<close> \<open>pcompose p q\<noteq>0\<close>] show ?thesis
      by auto
  qed
qed

lemma pcompose_eq_0:
  fixes p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  assumes "pcompose p q = 0" "degree q > 0"
  shows "p = 0"
proof -
  from assms degree_pcompose [of p q] have "degree p = 0"
    by auto
  then obtain a where "p = [:a:]"
    by (metis degree_pCons_eq_if gr0_conv_Suc neq0_conv pCons_cases)
  with assms(1) have "a = 0"
    by auto
  with \<open>p = [:a:]\<close> show ?thesis
    by simp
qed

lemma lead_coeff_comp:
  fixes p q :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "degree q > 0"
  shows "lead_coeff (pcompose p q) = lead_coeff p * lead_coeff q ^ (degree p)"
proof (induct p)
  case 0
  then show ?case by auto
next
  case (pCons a p)
  consider "degree (q * pcompose p q) = 0" | "degree (q * pcompose p q) > 0"
    by blast
  then show ?case
  proof cases
    case prems: 1
    then have "pcompose p q = 0"
      by (metis assms degree_0 degree_mult_eq_0 neq0_conv)
    with pcompose_eq_0[OF _ \<open>degree q > 0\<close>] have "p = 0"
      by simp
    then show ?thesis
      by auto
  next
    case prems: 2
    then have "degree [:a:] < degree (q * pcompose p q)"
      by simp
    then have "lead_coeff ([:a:] + q * p \<circ>\<^sub>p q) = lead_coeff (q * p \<circ>\<^sub>p q)"
      by (rule lead_coeff_add_le)
    then have "lead_coeff (pcompose (pCons a p) q) = lead_coeff (q * pcompose p q)"
      by (simp add: pcompose_pCons)
    also have "\<dots> = lead_coeff q * (lead_coeff p * lead_coeff q ^ degree p)"
      using pCons.hyps(2) lead_coeff_mult[of q "pcompose p q"] by simp
    also have "\<dots> = lead_coeff p * lead_coeff q ^ (degree p + 1)"
      by (auto simp: mult_ac)
    finally show ?thesis by auto
  qed
qed


subsection \<open>Closure properties of coefficients\<close>


context
  fixes R :: "'a :: comm_semiring_1 set"
  assumes R_0: "0 \<in> R"
  assumes R_plus: "\<And>x y. x \<in> R \<Longrightarrow> y \<in> R \<Longrightarrow> x + y \<in> R"
  assumes R_mult: "\<And>x y. x \<in> R \<Longrightarrow> y \<in> R \<Longrightarrow> x * y \<in> R"
begin

lemma coeff_mult_semiring_closed:
  assumes "\<And>i. coeff p i \<in> R" "\<And>i. coeff q i \<in> R"
  shows   "coeff (p * q) i \<in> R"
proof -
  have R_sum: "sum f A \<in> R" if "\<And>x. x \<in> A \<Longrightarrow> f x \<in> R" for A and f :: "nat \<Rightarrow> 'a"
    using that by (induction A rule: infinite_finite_induct) (auto intro: R_0 R_plus)
  show ?thesis
    unfolding coeff_mult by (auto intro!: R_sum R_mult assms)
qed

lemma coeff_pcompose_semiring_closed:
  assumes "\<And>i. coeff p i \<in> R" "\<And>i. coeff q i \<in> R"
  shows   "coeff (pcompose p q) i \<in> R"
  using assms(1)
proof (induction p arbitrary: i)
  case (pCons a p i)
  have [simp]: "a \<in> R"
    using pCons.prems[of 0] by auto
  have "coeff p i \<in> R" for i
    using pCons.prems[of "Suc i"] by auto
  hence "coeff (p \<circ>\<^sub>p q) i \<in> R" for i
    using pCons.prems by (intro pCons.IH)
  thus ?case
    by (auto simp: pcompose_pCons coeff_pCons split: nat.splits
             intro!: assms R_plus coeff_mult_semiring_closed)
qed auto

end


subsection \<open>Shifting polynomials\<close>

definition poly_shift :: "nat \<Rightarrow> 'a::zero poly \<Rightarrow> 'a poly"
  where "poly_shift n p = Abs_poly (\<lambda>i. coeff p (i + n))"

lemma nth_default_drop: "nth_default x (drop n xs) m = nth_default x xs (m + n)"
  by (auto simp add: nth_default_def add_ac)

lemma nth_default_take: "nth_default x (take n xs) m = (if m < n then nth_default x xs m else x)"
  by (auto simp add: nth_default_def add_ac)

lemma coeff_poly_shift: "coeff (poly_shift n p) i = coeff p (i + n)"
proof -
  from MOST_coeff_eq_0[of p] obtain m where "\<forall>k>m. coeff p k = 0"
    by (auto simp: MOST_nat)
  then have "\<forall>k>m. coeff p (k + n) = 0"
    by auto
  then have "\<forall>\<^sub>\<infinity>k. coeff p (k + n) = 0"
    by (auto simp: MOST_nat)
  then show ?thesis
    by (simp add: poly_shift_def poly.Abs_poly_inverse)
qed

lemma poly_shift_id [simp]: "poly_shift 0 = (\<lambda>x. x)"
  by (simp add: poly_eq_iff fun_eq_iff coeff_poly_shift)

lemma poly_shift_0 [simp]: "poly_shift n 0 = 0"
  by (simp add: poly_eq_iff coeff_poly_shift)

lemma poly_shift_1: "poly_shift n 1 = (if n = 0 then 1 else 0)"
  by (simp add: poly_eq_iff coeff_poly_shift)

lemma poly_shift_monom: "poly_shift n (monom c m) = (if m \<ge> n then monom c (m - n) else 0)"
  by (auto simp add: poly_eq_iff coeff_poly_shift)

lemma coeffs_shift_poly [code abstract]:
  "coeffs (poly_shift n p) = drop n (coeffs p)"
proof (cases "p = 0")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis
    by (intro coeffs_eqI)
      (simp_all add: coeff_poly_shift nth_default_drop nth_default_coeffs_eq)
qed


subsection \<open>Truncating polynomials\<close>

definition poly_cutoff
  where "poly_cutoff n p = Abs_poly (\<lambda>k. if k < n then coeff p k else 0)"

lemma coeff_poly_cutoff: "coeff (poly_cutoff n p) k = (if k < n then coeff p k else 0)"
  unfolding poly_cutoff_def
  by (subst poly.Abs_poly_inverse) (auto simp: MOST_nat intro: exI[of _ n])

lemma poly_cutoff_0 [simp]: "poly_cutoff n 0 = 0"
  by (simp add: poly_eq_iff coeff_poly_cutoff)

lemma poly_cutoff_1 [simp]: "poly_cutoff n 1 = (if n = 0 then 0 else 1)"
  by (simp add: poly_eq_iff coeff_poly_cutoff)

lemma coeffs_poly_cutoff [code abstract]:
  "coeffs (poly_cutoff n p) = strip_while ((=) 0) (take n (coeffs p))"
proof (cases "strip_while ((=) 0) (take n (coeffs p)) = []")
  case True
  then have "coeff (poly_cutoff n p) k = 0" for k
    unfolding coeff_poly_cutoff
    by (auto simp: nth_default_coeffs_eq [symmetric] nth_default_def set_conv_nth)
  then have "poly_cutoff n p = 0"
    by (simp add: poly_eq_iff)
  then show ?thesis
    by (subst True) simp_all
next
  case False
  have "no_trailing ((=) 0) (strip_while ((=) 0) (take n (coeffs p)))"
    by simp
  with False have "last (strip_while ((=) 0) (take n (coeffs p))) \<noteq> 0"
    unfolding no_trailing_unfold by auto
  then show ?thesis
    by (intro coeffs_eqI)
      (simp_all add: coeff_poly_cutoff nth_default_take nth_default_coeffs_eq)
qed


subsection \<open>Reflecting polynomials\<close>

definition reflect_poly :: "'a::zero poly \<Rightarrow> 'a poly"
  where "reflect_poly p = Poly (rev (coeffs p))"

lemma coeffs_reflect_poly [code abstract]:
  "coeffs (reflect_poly p) = rev (dropWhile ((=) 0) (coeffs p))"
  by (simp add: reflect_poly_def)

lemma reflect_poly_0 [simp]: "reflect_poly 0 = 0"
  by (simp add: reflect_poly_def)

lemma reflect_poly_1 [simp]: "reflect_poly 1 = 1"
  by (simp add: reflect_poly_def one_pCons)

lemma coeff_reflect_poly:
  "coeff (reflect_poly p) n = (if n > degree p then 0 else coeff p (degree p - n))"
  by (cases "p = 0")
    (auto simp add: reflect_poly_def nth_default_def
      rev_nth degree_eq_length_coeffs coeffs_nth not_less
      dest: le_imp_less_Suc)

lemma coeff_0_reflect_poly_0_iff [simp]: "coeff (reflect_poly p) 0 = 0 \<longleftrightarrow> p = 0"
  by (simp add: coeff_reflect_poly)

lemma reflect_poly_at_0_eq_0_iff [simp]: "poly (reflect_poly p) 0 = 0 \<longleftrightarrow> p = 0"
  by (simp add: coeff_reflect_poly poly_0_coeff_0)

lemma reflect_poly_pCons':
  "p \<noteq> 0 \<Longrightarrow> reflect_poly (pCons c p) = reflect_poly p + monom c (Suc (degree p))"
  by (intro poly_eqI)
    (auto simp: coeff_reflect_poly coeff_pCons not_less Suc_diff_le split: nat.split)

lemma reflect_poly_const [simp]: "reflect_poly [:a:] = [:a:]"
  by (cases "a = 0") (simp_all add: reflect_poly_def)

lemma poly_reflect_poly_nz:
  "x \<noteq> 0 \<Longrightarrow> poly (reflect_poly p) x = x ^ degree p * poly p (inverse x)"
  for x :: "'a::field"
  by (induct rule: pCons_induct) (simp_all add: field_simps reflect_poly_pCons' poly_monom)

lemma coeff_0_reflect_poly [simp]: "coeff (reflect_poly p) 0 = lead_coeff p"
  by (simp add: coeff_reflect_poly)

lemma poly_reflect_poly_0 [simp]: "poly (reflect_poly p) 0 = lead_coeff p"
  by (simp add: poly_0_coeff_0)

lemma reflect_poly_reflect_poly [simp]: "coeff p 0 \<noteq> 0 \<Longrightarrow> reflect_poly (reflect_poly p) = p"
  by (cases p rule: pCons_cases) (simp add: reflect_poly_def )

lemma degree_reflect_poly_le: "degree (reflect_poly p) \<le> degree p"
  by (simp add: degree_eq_length_coeffs coeffs_reflect_poly length_dropWhile_le diff_le_mono)

lemma reflect_poly_pCons: "a \<noteq> 0 \<Longrightarrow> reflect_poly (pCons a p) = Poly (rev (a # coeffs p))"
  by (subst coeffs_eq_iff) (simp add: coeffs_reflect_poly)

lemma degree_reflect_poly_eq [simp]: "coeff p 0 \<noteq> 0 \<Longrightarrow> degree (reflect_poly p) = degree p"
  by (cases p rule: pCons_cases) (simp add: reflect_poly_pCons degree_eq_length_coeffs)

(* TODO: does this work with zero divisors as well? Probably not. *)
lemma reflect_poly_mult: "reflect_poly (p * q) = reflect_poly p * reflect_poly q"
  for p q :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
proof (cases "p = 0 \<or> q = 0")
  case False
  then have [simp]: "p \<noteq> 0" "q \<noteq> 0" by auto
  show ?thesis
  proof (rule poly_eqI)
    show "coeff (reflect_poly (p * q)) i = coeff (reflect_poly p * reflect_poly q) i" for i
    proof (cases "i \<le> degree (p * q)")
      case True
      define A where "A = {..i} \<inter> {i - degree q..degree p}"
      define B where "B = {..degree p} \<inter> {degree p - i..degree (p*q) - i}"
      let ?f = "\<lambda>j. degree p - j"

      from True have "coeff (reflect_poly (p * q)) i = coeff (p * q) (degree (p * q) - i)"
        by (simp add: coeff_reflect_poly)
      also have "\<dots> = (\<Sum>j\<le>degree (p * q) - i. coeff p j * coeff q (degree (p * q) - i - j))"
        by (simp add: coeff_mult)
      also have "\<dots> = (\<Sum>j\<in>B. coeff p j * coeff q (degree (p * q) - i - j))"
        by (intro sum.mono_neutral_right) (auto simp: B_def degree_mult_eq not_le coeff_eq_0)
      also from True have "\<dots> = (\<Sum>j\<in>A. coeff p (degree p - j) * coeff q (degree q - (i - j)))"
        by (intro sum.reindex_bij_witness[of _ ?f ?f])
          (auto simp: A_def B_def degree_mult_eq add_ac)
      also have "\<dots> =
        (\<Sum>j\<le>i.
          if j \<in> {i - degree q..degree p}
          then coeff p (degree p - j) * coeff q (degree q - (i - j))
          else 0)"
        by (subst sum.inter_restrict [symmetric]) (simp_all add: A_def)
      also have "\<dots> = coeff (reflect_poly p * reflect_poly q) i"
        by (fastforce simp: coeff_mult coeff_reflect_poly intro!: sum.cong)
      finally show ?thesis .
    qed (auto simp: coeff_mult coeff_reflect_poly coeff_eq_0 degree_mult_eq intro!: sum.neutral)
  qed
qed auto

lemma reflect_poly_smult: "reflect_poly (smult c p) = smult c (reflect_poly p)"
  for p :: "'a::{comm_semiring_0,semiring_no_zero_divisors} poly"
  using reflect_poly_mult[of "[:c:]" p] by simp

lemma reflect_poly_power: "reflect_poly (p ^ n) = reflect_poly p ^ n"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  by (induct n) (simp_all add: reflect_poly_mult)

lemma reflect_poly_prod: "reflect_poly (prod f A) = prod (\<lambda>x. reflect_poly (f x)) A"
  for f :: "_ \<Rightarrow> _::{comm_semiring_0,semiring_no_zero_divisors} poly"
  by (induct A rule: infinite_finite_induct) (simp_all add: reflect_poly_mult)

lemma reflect_poly_prod_list: "reflect_poly (prod_list xs) = prod_list (map reflect_poly xs)"
  for xs :: "_::{comm_semiring_0,semiring_no_zero_divisors} poly list"
  by (induct xs) (simp_all add: reflect_poly_mult)

lemma reflect_poly_Poly_nz:
  "no_trailing (HOL.eq 0) xs \<Longrightarrow> reflect_poly (Poly xs) = Poly (rev xs)"
  by (simp add: reflect_poly_def)

lemmas reflect_poly_simps =
  reflect_poly_0 reflect_poly_1 reflect_poly_const reflect_poly_smult reflect_poly_mult
  reflect_poly_power reflect_poly_prod reflect_poly_prod_list


subsection \<open>Derivatives\<close>

function pderiv :: "('a :: {comm_semiring_1,semiring_no_zero_divisors}) poly \<Rightarrow> 'a poly"
  where "pderiv (pCons a p) = (if p = 0 then 0 else p + pCons 0 (pderiv p))"
  by (auto intro: pCons_cases)

termination pderiv
  by (relation "measure degree") simp_all

declare pderiv.simps[simp del]

lemma pderiv_0 [simp]: "pderiv 0 = 0"
  using pderiv.simps [of 0 0] by simp

lemma pderiv_pCons: "pderiv (pCons a p) = p + pCons 0 (pderiv p)"
  by (simp add: pderiv.simps)

lemma pderiv_1 [simp]: "pderiv 1 = 0"
  by (simp add: one_pCons pderiv_pCons)

lemma pderiv_of_nat [simp]: "pderiv (of_nat n) = 0"
  and pderiv_numeral [simp]: "pderiv (numeral m) = 0"
  by (simp_all add: of_nat_poly numeral_poly pderiv_pCons)

lemma coeff_pderiv: "coeff (pderiv p) n = of_nat (Suc n) * coeff p (Suc n)"
  by (induct p arbitrary: n)
    (auto simp add: pderiv_pCons coeff_pCons algebra_simps split: nat.split)

fun pderiv_coeffs_code :: "'a::{comm_semiring_1,semiring_no_zero_divisors} \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "pderiv_coeffs_code f (x # xs) = cCons (f * x) (pderiv_coeffs_code (f+1) xs)"
  | "pderiv_coeffs_code f [] = []"

definition pderiv_coeffs :: "'a::{comm_semiring_1,semiring_no_zero_divisors} list \<Rightarrow> 'a list"
  where "pderiv_coeffs xs = pderiv_coeffs_code 1 (tl xs)"

(* Efficient code for pderiv contributed by René Thiemann and Akihisa Yamada *)
lemma pderiv_coeffs_code:
  "nth_default 0 (pderiv_coeffs_code f xs) n = (f + of_nat n) * nth_default 0 xs n"
proof (induct xs arbitrary: f n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis
      by (cases "pderiv_coeffs_code (f + 1) xs = [] \<and> f * x = 0") (auto simp: cCons_def)
  next
    case n: (Suc m)
    show ?thesis
    proof (cases "pderiv_coeffs_code (f + 1) xs = [] \<and> f * x = 0")
      case False
      then have "nth_default 0 (pderiv_coeffs_code f (x # xs)) n =
          nth_default 0 (pderiv_coeffs_code (f + 1) xs) m"
        by (auto simp: cCons_def n)
      also have "\<dots> = (f + of_nat n) * nth_default 0 xs m"
        by (simp add: Cons n add_ac)
      finally show ?thesis
        by (simp add: n)
    next
      case True
      have empty: "pderiv_coeffs_code g xs = [] \<Longrightarrow> g + of_nat m = 0 \<or> nth_default 0 xs m = 0" for g
      proof (induct xs arbitrary: g m)
        case Nil
        then show ?case by simp
      next
        case (Cons x xs)
        from Cons(2) have empty: "pderiv_coeffs_code (g + 1) xs = []" and g: "g = 0 \<or> x = 0"
          by (auto simp: cCons_def split: if_splits)
        note IH = Cons(1)[OF empty]
        from IH[of m] IH[of "m - 1"] g show ?case
          by (cases m) (auto simp: field_simps)
      qed
      from True have "nth_default 0 (pderiv_coeffs_code f (x # xs)) n = 0"
        by (auto simp: cCons_def n)
      moreover from True have "(f + of_nat n) * nth_default 0 (x # xs) n = 0"
        by (simp add: n) (use empty[of "f+1"] in \<open>auto simp: field_simps\<close>)
      ultimately show ?thesis by simp
    qed
  qed
qed

lemma coeffs_pderiv_code [code abstract]: "coeffs (pderiv p) = pderiv_coeffs (coeffs p)"
  unfolding pderiv_coeffs_def
proof (rule coeffs_eqI, unfold pderiv_coeffs_code coeff_pderiv, goal_cases)
  case (1 n)
  have id: "coeff p (Suc n) = nth_default 0 (map (\<lambda>i. coeff p (Suc i)) [0..<degree p]) n"
    by (cases "n < degree p") (auto simp: nth_default_def coeff_eq_0)
  show ?case
    unfolding coeffs_def map_upt_Suc by (auto simp: id)
next
  case 2
  obtain n :: 'a and xs where defs: "tl (coeffs p) = xs" "1 = n"
    by simp
  from 2 show ?case
    unfolding defs by (induct xs arbitrary: n) (auto simp: cCons_def)
qed

lemma pderiv_eq_0_iff: "pderiv p = 0 \<longleftrightarrow> degree p = 0"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
proof (cases "degree p")
  case 0
  then show ?thesis
    by (metis degree_eq_zeroE pderiv.simps)
next
  case (Suc n)
  then show ?thesis
    using coeff_0 coeff_pderiv degree_0 leading_coeff_0_iff mult_eq_0_iff nat.distinct(1) of_nat_eq_0_iff
    by (metis coeff_0 coeff_pderiv degree_0 leading_coeff_0_iff mult_eq_0_iff nat.distinct(1) of_nat_eq_0_iff)
qed

lemma degree_pderiv: "degree (pderiv p) = degree p - 1"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
proof -
  have "degree p - 1 \<le> degree (pderiv p)"
  proof (cases "degree p")
    case (Suc n)
    then show ?thesis
      by (metis coeff_pderiv degree_0 diff_Suc_1 le_degree leading_coeff_0_iff mult_eq_0_iff nat.distinct(1) of_nat_eq_0_iff)
  qed auto
  moreover have "\<forall>i>degree p - 1. coeff (pderiv p) i = 0"
    by (simp add: coeff_eq_0 coeff_pderiv)
  ultimately show ?thesis
    using order_antisym [OF degree_le] by blast
qed

lemma not_dvd_pderiv:
  fixes p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
  assumes "degree p \<noteq> 0"
  shows "\<not> p dvd pderiv p"
proof
  assume dvd: "p dvd pderiv p"
  then obtain q where p: "pderiv p = p * q"
    unfolding dvd_def by auto
  from dvd have le: "degree p \<le> degree (pderiv p)"
    by (simp add: assms dvd_imp_degree_le pderiv_eq_0_iff)
  from assms and this [unfolded degree_pderiv]
    show False by auto
qed

lemma dvd_pderiv_iff [simp]: "p dvd pderiv p \<longleftrightarrow> degree p = 0"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
  using not_dvd_pderiv[of p] by (auto simp: pderiv_eq_0_iff [symmetric])

lemma pderiv_singleton [simp]: "pderiv [:a:] = 0"
  by (simp add: pderiv_pCons)

lemma pderiv_add: "pderiv (p + q) = pderiv p + pderiv q"
  by (rule poly_eqI) (simp add: coeff_pderiv algebra_simps)

lemma pderiv_minus: "pderiv (- p :: 'a :: idom poly) = - pderiv p"
  by (rule poly_eqI) (simp add: coeff_pderiv algebra_simps)

lemma pderiv_diff: "pderiv ((p :: _ :: idom poly) - q) = pderiv p - pderiv q"
  by (rule poly_eqI) (simp add: coeff_pderiv algebra_simps)

lemma pderiv_smult: "pderiv (smult a p) = smult a (pderiv p)"
  by (rule poly_eqI) (simp add: coeff_pderiv algebra_simps)

lemma pderiv_mult: "pderiv (p * q) = p * pderiv q + q * pderiv p"
  by (induct p) (auto simp: pderiv_add pderiv_smult pderiv_pCons algebra_simps)

lemma pderiv_power_Suc: "pderiv (p ^ Suc n) = smult (of_nat (Suc n)) (p ^ n) * pderiv p"
proof (induction n)
  case (Suc n)
  then show ?case
    by (simp add: pderiv_mult smult_add_left algebra_simps)
qed auto

lemma pderiv_pcompose: "pderiv (pcompose p q) = pcompose (pderiv p) q * pderiv q"
  by (induction p rule: pCons_induct)
     (auto simp: pcompose_pCons pderiv_add pderiv_mult pderiv_pCons pcompose_add algebra_simps)

lemma pderiv_prod: "pderiv (prod f (as)) = (\<Sum>a\<in>as. prod f (as - {a}) * pderiv (f a))"
proof (induct as rule: infinite_finite_induct)
  case (insert a as)
  then have id: "prod f (insert a as) = f a * prod f as"
    "\<And>g. sum g (insert a as) = g a + sum g as"
    "insert a as - {a} = as"
    by auto
  have "prod f (insert a as - {b}) = f a * prod f (as - {b})" if "b \<in> as" for b
  proof -
    from \<open>a \<notin> as\<close> that have *: "insert a as - {b} = insert a (as - {b})"
      by auto
    show ?thesis
      unfolding * by (subst prod.insert) (use insert in auto)
  qed
  then show ?case
    unfolding id pderiv_mult insert(3) sum_distrib_left
    by (auto simp add: ac_simps intro!: sum.cong)
qed auto

lemma DERIV_pow2: "DERIV (\<lambda>x. x ^ Suc n) x :> real (Suc n) * (x ^ n)"
  by (rule DERIV_cong, rule DERIV_pow) simp
declare DERIV_pow2 [simp] DERIV_pow [simp]

lemma DERIV_add_const: "DERIV f x :> D \<Longrightarrow> DERIV (\<lambda>x. a + f x :: 'a::real_normed_field) x :> D"
  by (rule DERIV_cong, rule DERIV_add) auto

lemma poly_DERIV [simp]: "DERIV (\<lambda>x. poly p x) x :> poly (pderiv p) x"
  by (induct p) (auto intro!: derivative_eq_intros simp add: pderiv_pCons)

lemma poly_isCont[simp]:
  fixes x::"'a::real_normed_field"
  shows "isCont (\<lambda>x. poly p x) x"
by (rule poly_DERIV [THEN DERIV_isCont])

lemma tendsto_poly [tendsto_intros]: "(f \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. poly p (f x)) \<longlongrightarrow> poly p a) F"
  for f :: "_ \<Rightarrow> 'a::real_normed_field"
  by (rule isCont_tendsto_compose [OF poly_isCont])

lemma continuous_within_poly: "continuous (at z within s) (poly p)"
  for z :: "'a::{real_normed_field}"
  by (simp add: continuous_within tendsto_poly)

lemma continuous_poly [continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. poly p (f x))"
  for f :: "_ \<Rightarrow> 'a::real_normed_field"
  unfolding continuous_def by (rule tendsto_poly)

lemma continuous_on_poly [continuous_intros]:
  fixes p :: "'a :: {real_normed_field} poly"
  assumes "continuous_on A f"
  shows "continuous_on A (\<lambda>x. poly p (f x))"
  by (metis DERIV_continuous_on assms continuous_on_compose2 poly_DERIV subset_UNIV)

text \<open>Consequences of the derivative theorem above.\<close>

lemma poly_differentiable[simp]: "(\<lambda>x. poly p x) differentiable (at x)"
  for x :: real
  by (simp add: real_differentiable_def) (blast intro: poly_DERIV)

lemma poly_IVT_pos: "a < b \<Longrightarrow> poly p a < 0 \<Longrightarrow> 0 < poly p b \<Longrightarrow> \<exists>x. a < x \<and> x < b \<and> poly p x = 0"
  for a b :: real
  using IVT [of "poly p" a 0 b] by (auto simp add: order_le_less)

lemma poly_IVT_neg: "a < b \<Longrightarrow> 0 < poly p a \<Longrightarrow> poly p b < 0 \<Longrightarrow> \<exists>x. a < x \<and> x < b \<and> poly p x = 0"
  for a b :: real
  using poly_IVT_pos [where p = "- p"] by simp

lemma poly_IVT: "a < b \<Longrightarrow> poly p a * poly p b < 0 \<Longrightarrow> \<exists>x>a. x < b \<and> poly p x = 0"
  for p :: "real poly"
  by (metis less_not_sym mult_less_0_iff poly_IVT_neg poly_IVT_pos)

lemma poly_MVT: "a < b \<Longrightarrow> \<exists>x. a < x \<and> x < b \<and> poly p b - poly p a = (b - a) * poly (pderiv p) x"
  for a b :: real
  by (simp add: MVT2)

lemma poly_MVT':
  fixes a b :: real
  assumes "{min a b..max a b} \<subseteq> A"
  shows "\<exists>x\<in>A. poly p b - poly p a = (b - a) * poly (pderiv p) x"
proof (cases a b rule: linorder_cases)
  case less
  from poly_MVT[OF less, of p] obtain x
    where "a < x" "x < b" "poly p b - poly p a = (b - a) * poly (pderiv p) x"
    by auto
  then show ?thesis by (intro bexI[of _ x]) (auto intro!: subsetD[OF assms])
next
  case greater
  from poly_MVT[OF greater, of p] obtain x
    where "b < x" "x < a" "poly p a - poly p b = (a - b) * poly (pderiv p) x" by auto
  then show ?thesis by (intro bexI[of _ x]) (auto simp: algebra_simps intro!: subsetD[OF assms])
qed (use assms in auto)

lemma poly_pinfty_gt_lc:
  fixes p :: "real poly"
  assumes "lead_coeff p > 0"
  shows "\<exists>n. \<forall> x \<ge> n. poly p x \<ge> lead_coeff p"
  using assms
proof (induct p)
  case 0
  then show ?case by auto
next
  case (pCons a p)
  from this(1) consider "a \<noteq> 0" "p = 0" | "p \<noteq> 0" by auto
  then show ?case
  proof cases
    case 1
    then show ?thesis by auto
  next
    case 2
    with pCons obtain n1 where gte_lcoeff: "\<forall>x\<ge>n1. lead_coeff p \<le> poly p x"
      by auto
    from pCons(3) \<open>p \<noteq> 0\<close> have gt_0: "lead_coeff p > 0" by auto
    define n where "n = max n1 (1 + \<bar>a\<bar> / lead_coeff p)"
    have "lead_coeff (pCons a p) \<le> poly (pCons a p) x" if "n \<le> x" for x
    proof -
      from gte_lcoeff that have "lead_coeff p \<le> poly p x"
        by (auto simp: n_def)
      with gt_0 have "\<bar>a\<bar> / lead_coeff p \<ge> \<bar>a\<bar> / poly p x" and "poly p x > 0"
        by (auto intro: frac_le)
      with \<open>n \<le> x\<close>[unfolded n_def] have "x \<ge> 1 + \<bar>a\<bar> / poly p x"
        by auto
      with \<open>lead_coeff p \<le> poly p x\<close> \<open>poly p x > 0\<close> \<open>p \<noteq> 0\<close>
      show "lead_coeff (pCons a p) \<le> poly (pCons a p) x"
        by (auto simp: field_simps)
    qed
    then show ?thesis by blast
  qed
qed

lemma lemma_order_pderiv1:
  "pderiv ([:- a, 1:] ^ Suc n * q) = [:- a, 1:] ^ Suc n * pderiv q +
    smult (of_nat (Suc n)) (q * [:- a, 1:] ^ n)"
  by (simp only: pderiv_mult pderiv_power_Suc) (simp del: power_Suc of_nat_Suc add: pderiv_pCons)

lemma lemma_order_pderiv:
  fixes p :: "'a :: field_char_0 poly"
  assumes n: "0 < n"
    and pd: "pderiv p \<noteq> 0"
    and pe: "p = [:- a, 1:] ^ n * q"
    and nd: "\<not> [:- a, 1:] dvd q"
  shows "n = Suc (order a (pderiv p))"
proof -
  from assms have "pderiv ([:- a, 1:] ^ n * q) \<noteq> 0"
    by auto
  from assms obtain n' where "n = Suc n'" "0 < Suc n'" "pderiv ([:- a, 1:] ^ Suc n' * q) \<noteq> 0"
    by (cases n) auto
  have "order a (pderiv ([:- a, 1:] ^ Suc n' * q)) = n'"
  proof (rule order_unique_lemma)
    show "[:- a, 1:] ^ n' dvd pderiv ([:- a, 1:] ^ Suc n' * q)"
      unfolding lemma_order_pderiv1
    proof (rule dvd_add)
      show "[:- a, 1:] ^ n' dvd [:- a, 1:] ^ Suc n' * pderiv q"
        by (metis dvdI dvd_mult2 power_Suc2)
      show "[:- a, 1:] ^ n' dvd smult (of_nat (Suc n')) (q * [:- a, 1:] ^ n')"
        by (metis dvd_smult dvd_triv_right)
    qed
    have "k dvd k * pderiv q + smult (of_nat (Suc n')) l \<Longrightarrow> k dvd l" for k l
      by (auto simp del: of_nat_Suc simp: dvd_add_right_iff dvd_smult_iff)
    then show "\<not> [:- a, 1:] ^ Suc n' dvd pderiv ([:- a, 1:] ^ Suc n' * q)"
      unfolding lemma_order_pderiv1
      by (metis nd dvd_mult_cancel_right power_not_zero pCons_eq_0_iff power_Suc zero_neq_one)
  qed
  then show ?thesis
    by (metis \<open>n = Suc n'\<close> pe)
qed

lemma order_pderiv: "order a p = Suc (order a (pderiv p))"
  if "pderiv p \<noteq> 0" "order a p \<noteq> 0"
  for p :: "'a::field_char_0 poly"
proof (cases "p = 0")
  case False
  obtain q where "p = [:- a, 1:] ^ order a p * q \<and> \<not> [:- a, 1:] dvd q"
    using False order_decomp by blast
  then show ?thesis
    using lemma_order_pderiv that by blast
qed (use that in auto)

lemma poly_squarefree_decomp_order:
  fixes p :: "'a::field_char_0 poly"
  assumes "pderiv p \<noteq> 0"
    and p: "p = q * d"
    and p': "pderiv p = e * d"
    and d: "d = r * p + s * pderiv p"
  shows "order a q = (if order a p = 0 then 0 else 1)"
proof (rule classical)
  assume 1: "\<not> ?thesis"
  from \<open>pderiv p \<noteq> 0\<close> have "p \<noteq> 0" by auto
  with p have "order a p = order a q + order a d"
    by (simp add: order_mult)
  with 1 have "order a p \<noteq> 0"
    by (auto split: if_splits)
  from \<open>pderiv p \<noteq> 0\<close> \<open>pderiv p = e * d\<close> have oapp: "order a (pderiv p) = order a e + order a d"
    by (simp add: order_mult)
  from \<open>pderiv p \<noteq> 0\<close> \<open>order a p \<noteq> 0\<close> have oap: "order a p = Suc (order a (pderiv p))"
    by (rule order_pderiv)
  from \<open>p \<noteq> 0\<close> \<open>p = q * d\<close> have "d \<noteq> 0"
    by simp
  have "[:- a, 1:] ^ order a (pderiv p) dvd r * p"
    by (metis dvd_trans dvd_triv_right oap order_1 power_Suc)
  then have "([:-a, 1:] ^ (order a (pderiv p))) dvd d"
    by (simp add: d order_1)
  with \<open>d \<noteq> 0\<close> have "order a (pderiv p) \<le> order a d"
    by (simp add: order_divides)
  show ?thesis
    using \<open>order a p = order a q + order a d\<close>
      and oapp oap
      and \<open>order a (pderiv p) \<le> order a d\<close>
    by auto
qed

lemma poly_squarefree_decomp_order2:
  "pderiv p \<noteq> 0 \<Longrightarrow> p = q * d \<Longrightarrow> pderiv p = e * d \<Longrightarrow>
    d = r * p + s * pderiv p \<Longrightarrow> \<forall>a. order a q = (if order a p = 0 then 0 else 1)"
  for p :: "'a::field_char_0 poly"
  by (blast intro: poly_squarefree_decomp_order)

lemma order_pderiv2:
  "pderiv p \<noteq> 0 \<Longrightarrow> order a p \<noteq> 0 \<Longrightarrow> order a (pderiv p) = n \<longleftrightarrow> order a p = Suc n"
  for p :: "'a::field_char_0 poly"
  by (auto dest: order_pderiv)

definition rsquarefree :: "'a::idom poly \<Rightarrow> bool"
  where "rsquarefree p \<longleftrightarrow> p \<noteq> 0 \<and> (\<forall>a. order a p = 0 \<or> order a p = 1)"

lemma pderiv_iszero: "pderiv p = 0 \<Longrightarrow> \<exists>h. p = [:h:]"
  for p :: "'a::{semidom,semiring_char_0} poly"
  by (cases p) (auto simp: pderiv_eq_0_iff split: if_splits)

lemma rsquarefree_roots: "rsquarefree p \<longleftrightarrow> (\<forall>a. \<not> (poly p a = 0 \<and> poly (pderiv p) a = 0))"
  for p :: "'a::field_char_0 poly"
proof (cases "p = 0")
  case False
  show ?thesis
  proof (cases "pderiv p = 0")
    case True
    with \<open>p \<noteq> 0\<close> pderiv_iszero show ?thesis
      by (force simp add: order_0I rsquarefree_def)
  next
    case False
    with \<open>p \<noteq> 0\<close> order_pderiv2 show ?thesis
      by (force simp add: rsquarefree_def order_root)
  qed
qed (simp add: rsquarefree_def)

lemma poly_squarefree_decomp:
  fixes p :: "'a::field_char_0 poly"
  assumes "pderiv p \<noteq> 0"
    and "p = q * d"
    and "pderiv p = e * d"
    and "d = r * p + s * pderiv p"
  shows "rsquarefree q \<and> (\<forall>a. poly q a = 0 \<longleftrightarrow> poly p a = 0)"
proof -
  from \<open>pderiv p \<noteq> 0\<close> have "p \<noteq> 0" by auto
  with \<open>p = q * d\<close> have "q \<noteq> 0" by simp
  from assms have "\<forall>a. order a q = (if order a p = 0 then 0 else 1)"
    by (rule poly_squarefree_decomp_order2)
  with \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> show ?thesis
    by (simp add: rsquarefree_def order_root)
qed


subsection \<open>Algebraic numbers\<close>

text \<open>
  Algebraic numbers can be defined in two equivalent ways: all real numbers that are
  roots of rational polynomials or of integer polynomials. The Algebraic-Numbers AFP entry
  uses the rational definition, but we need the integer definition.

  The equivalence is obvious since any rational polynomial can be multiplied with the
  LCM of its coefficients, yielding an integer polynomial with the same roots.
\<close>

definition algebraic :: "'a :: field_char_0 \<Rightarrow> bool"
  where "algebraic x \<longleftrightarrow> (\<exists>p. (\<forall>i. coeff p i \<in> \<int>) \<and> p \<noteq> 0 \<and> poly p x = 0)"

lemma algebraicI: "(\<And>i. coeff p i \<in> \<int>) \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> poly p x = 0 \<Longrightarrow> algebraic x"
  unfolding algebraic_def by blast

lemma algebraicE:
  assumes "algebraic x"
  obtains p where "\<And>i. coeff p i \<in> \<int>" "p \<noteq> 0" "poly p x = 0"
  using assms unfolding algebraic_def by blast

lemma algebraic_altdef: "algebraic x \<longleftrightarrow> (\<exists>p. (\<forall>i. coeff p i \<in> \<rat>) \<and> p \<noteq> 0 \<and> poly p x = 0)"
  for p :: "'a::field_char_0 poly"
proof safe
  fix p
  assume rat: "\<forall>i. coeff p i \<in> \<rat>" and root: "poly p x = 0" and nz: "p \<noteq> 0"
  define cs where "cs = coeffs p"
  from rat have "\<forall>c\<in>range (coeff p). \<exists>c'. c = of_rat c'"
    unfolding Rats_def by blast
  then obtain f where f: "coeff p i = of_rat (f (coeff p i))" for i
    by (subst (asm) bchoice_iff) blast
  define cs' where "cs' = map (quotient_of \<circ> f) (coeffs p)"
  define d where "d = Lcm (set (map snd cs'))"
  define p' where "p' = smult (of_int d) p"

  have "coeff p' n \<in> \<int>" for n
  proof (cases "n \<le> degree p")
    case True
    define c where "c = coeff p n"
    define a where "a = fst (quotient_of (f (coeff p n)))"
    define b where "b = snd (quotient_of (f (coeff p n)))"
    have b_pos: "b > 0"
      unfolding b_def using quotient_of_denom_pos' by simp
    have "coeff p' n = of_int d * coeff p n"
      by (simp add: p'_def)
    also have "coeff p n = of_rat (of_int a / of_int b)"
      unfolding a_def b_def
      by (subst quotient_of_div [of "f (coeff p n)", symmetric]) (simp_all add: f [symmetric])
    also have "of_int d * \<dots> = of_rat (of_int (a*d) / of_int b)"
      by (simp add: of_rat_mult of_rat_divide)
    also from nz True have "b \<in> snd ` set cs'"
      by (force simp: cs'_def o_def b_def coeffs_def simp del: upt_Suc)
    then have "b dvd (a * d)"
      by (simp add: d_def)
    then have "of_int (a * d) / of_int b \<in> (\<int> :: rat set)"
      by (rule of_int_divide_in_Ints)
    then have "of_rat (of_int (a * d) / of_int b) \<in> \<int>" by (elim Ints_cases) auto
    finally show ?thesis .
  next
    case False
    then show ?thesis
      by (auto simp: p'_def not_le coeff_eq_0)
  qed
  moreover have "set (map snd cs') \<subseteq> {0<..}"
    unfolding cs'_def using quotient_of_denom_pos' by (auto simp: coeffs_def simp del: upt_Suc)
  then have "d \<noteq> 0"
    unfolding d_def by (induct cs') simp_all
  with nz have "p' \<noteq> 0" by (simp add: p'_def)
  moreover from root have "poly p' x = 0"
    by (simp add: p'_def)
  ultimately show "algebraic x"
    unfolding algebraic_def by blast
next
  assume "algebraic x"
  then obtain p where p: "coeff p i \<in> \<int>" "poly p x = 0" "p \<noteq> 0" for i
    by (force simp: algebraic_def)
  moreover have "coeff p i \<in> \<int> \<Longrightarrow> coeff p i \<in> \<rat>" for i
    by (elim Ints_cases) simp
  ultimately show "\<exists>p. (\<forall>i. coeff p i \<in> \<rat>) \<and> p \<noteq> 0 \<and> poly p x = 0" by auto
qed


subsection \<open>Algebraic integers\<close>

inductive algebraic_int :: "'a :: field \<Rightarrow> bool" where
  "\<lbrakk>lead_coeff p = 1; \<forall>i. coeff p i \<in> \<int>; poly p x = 0\<rbrakk> \<Longrightarrow> algebraic_int x"

lemma algebraic_int_altdef_ipoly:
  fixes x :: "'a :: field_char_0"
  shows "algebraic_int x \<longleftrightarrow> (\<exists>p. poly (map_poly of_int p) x = 0 \<and> lead_coeff p = 1)"
proof
  assume "algebraic_int x"
  then obtain p where p: "lead_coeff p = 1" "\<forall>i. coeff p i \<in> \<int>" "poly p x = 0"
    by (auto elim: algebraic_int.cases)
  define the_int where "the_int = (\<lambda>x::'a. THE r. x = of_int r)"
  define p' where "p' = map_poly the_int p"
  have of_int_the_int: "of_int (the_int x) = x" if "x \<in> \<int>" for x
    unfolding the_int_def by (rule sym, rule theI') (insert that, auto simp: Ints_def)
  have the_int_0_iff: "the_int x = 0 \<longleftrightarrow> x = 0" if "x \<in> \<int>" for x
    using of_int_the_int[OF that] by auto
  have [simp]: "the_int 0 = 0"
    by (subst the_int_0_iff) auto
  have "map_poly of_int p' = map_poly (of_int \<circ> the_int) p"
    by (simp add: p'_def map_poly_map_poly)
  also from p of_int_the_int have "\<dots> = p"
    by (subst poly_eq_iff) (auto simp: coeff_map_poly)
  finally have p_p': "map_poly of_int p' = p" .

  show "(\<exists>p. poly (map_poly of_int p) x = 0 \<and> lead_coeff p = 1)"
  proof (intro exI conjI notI)
    from p show "poly (map_poly of_int p') x = 0" by (simp add: p_p')
  next
    show "lead_coeff p' = 1"
      using p by (simp flip: p_p' add: degree_map_poly coeff_map_poly)
  qed
next
  assume "\<exists>p. poly (map_poly of_int p) x = 0 \<and> lead_coeff p = 1"
  then obtain p where p: "poly (map_poly of_int p) x = 0" "lead_coeff p = 1"
    by auto
  define p' where "p' = (map_poly of_int p :: 'a poly)"
  from p have "lead_coeff p' = 1" "poly p' x = 0" "\<forall>i. coeff p' i \<in> \<int>"
    by (auto simp: p'_def coeff_map_poly degree_map_poly)
  thus "algebraic_int x"
    by (intro algebraic_int.intros)
qed

theorem rational_algebraic_int_is_int:
  assumes "algebraic_int x" and "x \<in> \<rat>"
  shows   "x \<in> \<int>"
proof -
  from assms(2) obtain a b where ab: "b > 0" "Rings.coprime a b" and x_eq: "x = of_int a / of_int b"
    by (auto elim: Rats_cases')
  from \<open>b > 0\<close> have [simp]: "b \<noteq> 0"
    by auto
  from assms(1) obtain p
    where p: "lead_coeff p = 1" "\<forall>i. coeff p i \<in> \<int>" "poly p x = 0"
    by (auto simp: algebraic_int.simps)

  define q :: "'a poly" where "q = [:-of_int a, of_int b:]"
  have "poly q x = 0" "q \<noteq> 0" "\<forall>i. coeff q i \<in> \<int>"
    by (auto simp: x_eq q_def coeff_pCons split: nat.splits)
  define n where "n = degree p"
  have "n > 0"
    using p by (intro Nat.gr0I) (auto simp: n_def elim!: degree_eq_zeroE)
  have "(\<Sum>i<n. coeff p i * of_int (a ^ i * b ^ (n - i - 1))) \<in> \<int>"
    using p by auto
  then obtain R where R: "of_int R = (\<Sum>i<n. coeff p i * of_int (a ^ i * b ^ (n - i - 1)))"
    by (auto simp: Ints_def)
  have [simp]: "coeff p n = 1"
    using p by (auto simp: n_def)

  have "0 = poly p x * of_int b ^ n"
    using p by simp
  also have "\<dots> = (\<Sum>i\<le>n. coeff p i * x ^ i * of_int b ^ n)"
    by (simp add: poly_altdef n_def sum_distrib_right)
  also have "\<dots> = (\<Sum>i\<le>n. coeff p i * of_int (a ^ i * b ^ (n - i)))"
    by (intro sum.cong) (auto simp: x_eq field_simps simp flip: power_add)
  also have "{..n} = insert n {..<n}"
    using \<open>n > 0\<close> by auto
  also have "(\<Sum>i\<in>\<dots>. coeff p i * of_int (a ^ i * b ^ (n - i))) =
               coeff p n * of_int (a ^ n) + (\<Sum>i<n. coeff p i * of_int (a ^ i * b ^ (n - i)))"
    by (subst sum.insert) auto
  also have "(\<Sum>i<n. coeff p i * of_int (a ^ i * b ^ (n - i))) =
             (\<Sum>i<n. coeff p i * of_int (a ^ i * b * b ^ (n - i - 1)))"
    by (intro sum.cong) (auto simp flip: power_add power_Suc simp: Suc_diff_Suc)
  also have "\<dots> = of_int (b * R)"
    by (simp add: R sum_distrib_left sum_distrib_right mult_ac)
  finally have "of_int (a ^ n) = (-of_int (b * R) :: 'a)"
    by (auto simp: add_eq_0_iff)
  hence "a ^ n = -b * R"
    by (simp flip: of_int_mult of_int_power of_int_minus)
  hence "b dvd a ^ n"
    by simp
  with \<open>Rings.coprime a b\<close> have "b dvd 1"
    by (meson coprime_power_left_iff dvd_refl not_coprimeI)
  with x_eq and \<open>b > 0\<close> show ?thesis
    by auto
qed

lemma algebraic_int_imp_algebraic [dest]: "algebraic_int x \<Longrightarrow> algebraic x"
  by (auto simp: algebraic_int.simps algebraic_def)

lemma int_imp_algebraic_int:
  assumes "x \<in> \<int>"
  shows   "algebraic_int x"
proof
  show "\<forall>i. coeff [:-x, 1:] i \<in> \<int>"
    using assms by (auto simp: coeff_pCons split: nat.splits)
qed auto

lemma algebraic_int_0 [simp, intro]: "algebraic_int 0"
  and algebraic_int_1 [simp, intro]: "algebraic_int 1"
  and algebraic_int_numeral [simp, intro]: "algebraic_int (numeral n)"
  and algebraic_int_of_nat [simp, intro]: "algebraic_int (of_nat k)"
  and algebraic_int_of_int [simp, intro]: "algebraic_int (of_int m)"
  by (simp_all add: int_imp_algebraic_int)

lemma algebraic_int_ii [simp, intro]: "algebraic_int \<i>"
proof
  show "poly [:1, 0, 1:] \<i> = 0"
    by simp
qed (auto simp: coeff_pCons split: nat.splits)

lemma algebraic_int_minus [intro]:
  assumes "algebraic_int x"
  shows   "algebraic_int (-x)"
proof -
  from assms obtain p where p: "lead_coeff p = 1" "\<forall>i. coeff p i \<in> \<int>" "poly p x = 0"
    by (auto simp: algebraic_int.simps)
  define s where "s = (if even (degree p) then 1 else -1 :: 'a)"

  define q where "q = Polynomial.smult s (pcompose p [:0, -1:])"
  have "lead_coeff q = s * lead_coeff (pcompose p [:0, -1:])"
    by (simp add: q_def)
  also have "lead_coeff (pcompose p [:0, -1:]) = lead_coeff p * (- 1) ^ degree p"
    by (subst lead_coeff_comp) auto
  finally have "poly q (-x) = 0" and "lead_coeff q = 1"
    using p by (auto simp: q_def poly_pcompose s_def)
  moreover have "coeff q i \<in> \<int>" for i
  proof -
    have "coeff (pcompose p [:0, -1:]) i \<in> \<int>"
      using p by (intro coeff_pcompose_semiring_closed) (auto simp: coeff_pCons split: nat.splits)
    thus ?thesis by (simp add: q_def s_def)
  qed
  ultimately show ?thesis
    by (auto simp: algebraic_int.simps)
qed

lemma algebraic_int_minus_iff [simp]:
  "algebraic_int (-x) \<longleftrightarrow> algebraic_int (x :: 'a :: field_char_0)"
  using algebraic_int_minus[of x] algebraic_int_minus[of "-x"] by auto

lemma algebraic_int_inverse [intro]:
  assumes "poly p x = 0" and "\<forall>i. coeff p i \<in> \<int>" and "coeff p 0 = 1"
  shows   "algebraic_int (inverse x)"
proof
  from assms have [simp]: "x \<noteq> 0"
    by (auto simp: poly_0_coeff_0)
  show "poly (reflect_poly p) (inverse x) = 0"
    using assms by (simp add: poly_reflect_poly_nz)
qed (use assms in \<open>auto simp: coeff_reflect_poly\<close>)

lemma algebraic_int_root:
  assumes "algebraic_int y"
      and "poly p x = y" and "\<forall>i. coeff p i \<in> \<int>" and "lead_coeff p = 1" and "degree p > 0"
  shows   "algebraic_int x"
proof -
  from assms obtain q where q: "poly q y = 0" "\<forall>i. coeff q i \<in> \<int>" "lead_coeff q = 1"
    by (auto simp: algebraic_int.simps)
  show ?thesis
  proof
    from assms q show "lead_coeff (pcompose q p) = 1"
      by (subst lead_coeff_comp) auto
    from assms q show "\<forall>i. coeff (pcompose q p) i \<in> \<int>"
      by (intro allI coeff_pcompose_semiring_closed) auto
    show "poly (pcompose q p) x = 0"
      using assms q by (simp add: poly_pcompose)
  qed
qed

lemma algebraic_int_abs_real [simp]:
  "algebraic_int \<bar>x :: real\<bar> \<longleftrightarrow> algebraic_int x"
  by (auto simp: abs_if)

lemma algebraic_int_nth_root_real [intro]:
  assumes "algebraic_int x"
  shows   "algebraic_int (root n x)"
proof (cases "n = 0")
  case False
  show ?thesis
  proof (rule algebraic_int_root)
    show "poly (monom 1 n) (root n x) = (if even n then \<bar>x\<bar> else x)"
      using sgn_power_root[of n x] False
      by (auto simp add: poly_monom sgn_if split: if_splits)
  qed (use False assms in \<open>auto simp: degree_monom_eq\<close>)
qed auto

lemma algebraic_int_sqrt [intro]: "algebraic_int x \<Longrightarrow> algebraic_int (sqrt x)"
  by (auto simp: sqrt_def)

lemma algebraic_int_csqrt [intro]: "algebraic_int x \<Longrightarrow> algebraic_int (csqrt x)"
  by (rule algebraic_int_root[where p = "monom 1 2"])
     (auto simp: poly_monom degree_monom_eq)

lemma poly_map_poly_cnj [simp]: "poly (map_poly cnj p) x = cnj (poly p (cnj x))"
  by (induction p) (auto simp: map_poly_pCons)

lemma algebraic_int_cnj [intro]:
  assumes "algebraic_int x"
  shows   "algebraic_int (cnj x)"
proof -
  from assms obtain p where p: "lead_coeff p = 1" "\<forall>i. coeff p i \<in> \<int>" "poly p x = 0"
    by (auto simp: algebraic_int.simps)
  show ?thesis
  proof
    show "poly (map_poly cnj p) (cnj x) = 0"
      using p by simp
    show "lead_coeff (map_poly cnj p) = 1"
      using p by (simp add: coeff_map_poly degree_map_poly)
    show "\<forall>i. coeff (map_poly cnj p) i \<in> \<int>"
      using p by (auto simp: coeff_map_poly)
  qed
qed

lemma algebraic_int_cnj_iff [simp]: "algebraic_int (cnj x) \<longleftrightarrow> algebraic_int x"
  using algebraic_int_cnj[of x] algebraic_int_cnj[of "cnj x"] by auto

lemma algebraic_int_of_real [intro]:
  assumes "algebraic_int x"
  shows   "algebraic_int (of_real x)"
proof -
  from assms obtain p where p: "poly p x = 0" "\<forall>i. coeff p i \<in> \<int>" "lead_coeff p = 1"
    by (auto simp: algebraic_int.simps)
  show "algebraic_int (of_real x :: 'a)"
  proof
    have "poly (map_poly of_real p) (of_real x) = (of_real (poly p x) :: 'a)"
      by (induction p) (auto simp: map_poly_pCons)
    thus "poly (map_poly of_real p) (of_real x) = (0 :: 'a)"
      using p by simp
  qed (use p in \<open>auto simp: coeff_map_poly degree_map_poly\<close>)
qed

lemma algebraic_int_of_real_iff [simp]:
  "algebraic_int (of_real x :: 'a :: {field_char_0, real_algebra_1}) \<longleftrightarrow> algebraic_int x"
proof
  assume "algebraic_int (of_real x :: 'a)"
  then obtain p
    where p: "poly (map_poly of_int p) (of_real x :: 'a) = 0" "lead_coeff p = 1"
    by (auto simp: algebraic_int_altdef_ipoly)
  show "algebraic_int x"
    unfolding algebraic_int_altdef_ipoly
  proof (intro exI[of _ p] conjI)
    have "of_real (poly (map_poly real_of_int p) x) = poly (map_poly of_int p) (of_real x :: 'a)"
      by (induction p) (auto simp: map_poly_pCons)
    also note p(1)
    finally show "poly (map_poly real_of_int p) x = 0" by simp
  qed (use p in auto)
qed auto


subsection \<open>Division of polynomials\<close>

subsubsection \<open>Division in general\<close>

instantiation poly :: (idom_divide) idom_divide
begin

fun divide_poly_main :: "'a \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a poly"
  where
    "divide_poly_main lc q r d dr (Suc n) =
      (let cr = coeff r dr; a = cr div lc; mon = monom a n in
        if False \<or> a * lc = cr then \<comment> \<open>\<open>False \<or>\<close> is only because of problem in function-package\<close>
          divide_poly_main
            lc
            (q + mon)
            (r - mon * d)
            d (dr - 1) n else 0)"
  | "divide_poly_main lc q r d dr 0 = q"

definition divide_poly :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  where "divide_poly f g =
    (if g = 0 then 0
     else
      divide_poly_main (coeff g (degree g)) 0 f g (degree f)
        (1 + length (coeffs f) - length (coeffs g)))"

lemma divide_poly_main:
  assumes d: "d \<noteq> 0" "lc = coeff d (degree d)"
    and "degree (d * r) \<le> dr" "divide_poly_main lc q (d * r) d dr n = q'"
    and "n = 1 + dr - degree d \<or> dr = 0 \<and> n = 0 \<and> d * r = 0"
  shows "q' = q + r"
  using assms(3-)
proof (induct n arbitrary: q r dr)
  case (Suc n)
  let ?rr = "d * r"
  let ?a = "coeff ?rr dr"
  let ?qq = "?a div lc"
  define b where [simp]: "b = monom ?qq n"
  let ?rrr =  "d * (r - b)"
  let ?qqq = "q + b"
  note res = Suc(3)
  from Suc(4) have dr: "dr = n + degree d" by auto
  from d have lc: "lc \<noteq> 0" by auto
  have "coeff (b * d) dr = coeff b n * coeff d (degree d)"
  proof (cases "?qq = 0")
    case True
    then show ?thesis by simp
  next
    case False
    then have n: "n = degree b"
      by (simp add: degree_monom_eq)
    show ?thesis
      unfolding n dr by (simp add: coeff_mult_degree_sum)
  qed
  also have "\<dots> = lc * coeff b n"
    by (simp add: d)
  finally have c2: "coeff (b * d) dr = lc * coeff b n" .
  have rrr: "?rrr = ?rr - b * d"
    by (simp add: field_simps)
  have c1: "coeff (d * r) dr = lc * coeff r n"
  proof (cases "degree r = n")
    case True
    with Suc(2) show ?thesis
      unfolding dr using coeff_mult_degree_sum[of d r] d by (auto simp: ac_simps)
  next
    case False
    from dr Suc(2) have "degree r \<le> n"
      by auto
        (metis add.commute add_le_cancel_left d(1) degree_0 degree_mult_eq
          diff_is_0_eq diff_zero le_cases)
    with False have r_n: "degree r < n"
      by auto
    then have right: "lc * coeff r n = 0"
      by (simp add: coeff_eq_0)
    have "coeff (d * r) dr = coeff (d * r) (degree d + n)"
      by (simp add: dr ac_simps)
    also from r_n have "\<dots> = 0"
      by (metis False Suc.prems(1) add.commute add_left_imp_eq coeff_degree_mult coeff_eq_0
        coeff_mult_degree_sum degree_mult_le dr le_eq_less_or_eq)
    finally show ?thesis
      by (simp only: right)
  qed
  have c0: "coeff ?rrr dr = 0"
    and id: "lc * (coeff (d * r) dr div lc) = coeff (d * r) dr"
    unfolding rrr coeff_diff c2
    unfolding b_def coeff_monom coeff_smult c1 using lc by auto
  from res[unfolded divide_poly_main.simps[of lc q] Let_def] id
  have res: "divide_poly_main lc ?qqq ?rrr d (dr - 1) n = q'"
    by (simp del: divide_poly_main.simps add: field_simps)
  note IH = Suc(1)[OF _ res]
  from Suc(4) have dr: "dr = n + degree d" by auto
  from Suc(2) have deg_rr: "degree ?rr \<le> dr" by auto
  have deg_bd: "degree (b * d) \<le> dr"
    unfolding dr b_def by (rule order.trans[OF degree_mult_le]) (auto simp: degree_monom_le)
  have "degree ?rrr \<le> dr"
    unfolding rrr by (rule degree_diff_le[OF deg_rr deg_bd])
  with c0 have deg_rrr: "degree ?rrr \<le> (dr - 1)"
    by (rule coeff_0_degree_minus_1)
  have "n = 1 + (dr - 1) - degree d \<or> dr - 1 = 0 \<and> n = 0 \<and> ?rrr = 0"
  proof (cases dr)
    case 0
    with Suc(4) have 0: "dr = 0" "n = 0" "degree d = 0"
      by auto
    with deg_rrr have "degree ?rrr = 0"
      by simp
    from degree_eq_zeroE[OF this] obtain a where rrr: "?rrr = [:a:]"
      by metis
    show ?thesis
      unfolding 0 using c0 unfolding rrr 0 by simp
  next
    case _: Suc
    with Suc(4) show ?thesis by auto
  qed
  from IH[OF deg_rrr this] show ?case
    by simp
next
  case 0
  show ?case
  proof (cases "r = 0")
    case True
    with 0 show ?thesis by auto
  next
    case False
    from d False have "degree (d * r) = degree d + degree r"
      by (subst degree_mult_eq) auto
    with 0 d show ?thesis by auto
  qed
qed

lemma divide_poly_main_0: "divide_poly_main 0 0 r d dr n = 0"
proof (induct n arbitrary: r d dr)
  case 0
  then show ?case by simp
next
  case Suc
  show ?case
    unfolding divide_poly_main.simps[of _ _ r] Let_def
    by (simp add: Suc del: divide_poly_main.simps)
qed

lemma divide_poly:
  assumes g: "g \<noteq> 0"
  shows "(f * g) div g = (f :: 'a poly)"
proof -
  have len: "length (coeffs f) = Suc (degree f)" if "f \<noteq> 0" for f :: "'a poly"
    using that unfolding degree_eq_length_coeffs by auto
  have "divide_poly_main (coeff g (degree g)) 0 (g * f) g (degree (g * f))
    (1 + length (coeffs (g * f)) - length (coeffs  g)) = (f * g) div g"
    by (simp add: divide_poly_def Let_def ac_simps)
  note main = divide_poly_main[OF g refl le_refl this]
  have "(f * g) div g = 0 + f"
  proof (rule main, goal_cases)
    case 1
    show ?case
    proof (cases "f = 0")
      case True
      with g show ?thesis
        by (auto simp: degree_eq_length_coeffs)
    next
      case False
      with g have fg: "g * f \<noteq> 0" by auto
      show ?thesis
        unfolding len[OF fg] len[OF g] by auto
    qed
  qed
  then show ?thesis by simp
qed

lemma divide_poly_0: "f div 0 = 0"
  for f :: "'a poly"
  by (simp add: divide_poly_def Let_def divide_poly_main_0)

instance
  by standard (auto simp: divide_poly divide_poly_0)

end

instance poly :: (idom_divide) algebraic_semidom ..

lemma div_const_poly_conv_map_poly:
  assumes "[:c:] dvd p"
  shows "p div [:c:] = map_poly (\<lambda>x. x div c) p"
proof (cases "c = 0")
  case True
  then show ?thesis
    by (auto intro!: poly_eqI simp: coeff_map_poly)
next
  case False
  from assms obtain q where p: "p = [:c:] * q" by (rule dvdE)
  moreover {
    have "smult c q = [:c:] * q"
      by simp
    also have "\<dots> div [:c:] = q"
      by (rule nonzero_mult_div_cancel_left) (use False in auto)
    finally have "smult c q div [:c:] = q" .
  }
  ultimately show ?thesis by (intro poly_eqI) (auto simp: coeff_map_poly False)
qed

lemma is_unit_monom_0:
  fixes a :: "'a::field"
  assumes "a \<noteq> 0"
  shows "is_unit (monom a 0)"
proof
  from assms show "1 = monom a 0 * monom (inverse a) 0"
    by (simp add: mult_monom)
qed

lemma is_unit_triv: "a \<noteq> 0 \<Longrightarrow> is_unit [:a:]"
  for a :: "'a::field"
  by (simp add: is_unit_monom_0 monom_0 [symmetric])

lemma is_unit_iff_degree:
  fixes p :: "'a::field poly"
  assumes "p \<noteq> 0"
  shows "is_unit p \<longleftrightarrow> degree p = 0"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then obtain a where "p = [:a:]"
    by (rule degree_eq_zeroE)
  with assms show ?lhs
    by (simp add: is_unit_triv)
next
  assume ?lhs
  then obtain q where "q \<noteq> 0" "p * q = 1" ..
  then have "degree (p * q) = degree 1"
    by simp
  with \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> have "degree p + degree q = 0"
    by (simp add: degree_mult_eq)
  then show ?rhs by simp
qed

lemma is_unit_pCons_iff: "is_unit (pCons a p) \<longleftrightarrow> p = 0 \<and> a \<noteq> 0"
  for p :: "'a::field poly"
  by (cases "p = 0") (auto simp: is_unit_triv is_unit_iff_degree)

lemma is_unit_monom_trivial: "is_unit p \<Longrightarrow> monom (coeff p (degree p)) 0 = p"
  for p :: "'a::field poly"
  by (cases p) (simp_all add: monom_0 is_unit_pCons_iff)

lemma is_unit_const_poly_iff: "[:c:] dvd 1 \<longleftrightarrow> c dvd 1"
  for c :: "'a::{comm_semiring_1,semiring_no_zero_divisors}"
  by (auto simp: one_pCons)

lemma is_unit_polyE:
  fixes p :: "'a :: {comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "p dvd 1"
  obtains c where "p = [:c:]" "c dvd 1"
proof -
  from assms obtain q where "1 = p * q"
    by (rule dvdE)
  then have "p \<noteq> 0" and "q \<noteq> 0"
    by auto
  from \<open>1 = p * q\<close> have "degree 1 = degree (p * q)"
    by simp
  also from \<open>p \<noteq> 0\<close> and \<open>q \<noteq> 0\<close> have "\<dots> = degree p + degree q"
    by (simp add: degree_mult_eq)
  finally have "degree p = 0" by simp
  with degree_eq_zeroE obtain c where c: "p = [:c:]" .
  with \<open>p dvd 1\<close> have "c dvd 1"
    by (simp add: is_unit_const_poly_iff)
  with c show thesis ..
qed

lemma is_unit_polyE':
  fixes p :: "'a::field poly"
  assumes "is_unit p"
  obtains a where "p = monom a 0" and "a \<noteq> 0"
proof -
  obtain a q where "p = pCons a q"
    by (cases p)
  with assms have "p = [:a:]" and "a \<noteq> 0"
    by (simp_all add: is_unit_pCons_iff)
  with that show thesis by (simp add: monom_0)
qed

lemma is_unit_poly_iff: "p dvd 1 \<longleftrightarrow> (\<exists>c. p = [:c:] \<and> c dvd 1)"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  by (auto elim: is_unit_polyE simp add: is_unit_const_poly_iff)


subsubsection \<open>Pseudo-Division\<close>

text \<open>This part is by René Thiemann and Akihisa Yamada.\<close>

fun pseudo_divmod_main ::
  "'a :: comm_ring_1  \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a poly \<times> 'a poly"
  where
    "pseudo_divmod_main lc q r d dr (Suc n) =
      (let
        rr = smult lc r;
        qq = coeff r dr;
        rrr = rr - monom qq n * d;
        qqq = smult lc q + monom qq n
       in pseudo_divmod_main lc qqq rrr d (dr - 1) n)"
  | "pseudo_divmod_main lc q r d dr 0 = (q,r)"

definition pseudo_divmod :: "'a :: comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<times> 'a poly"
  where "pseudo_divmod p q \<equiv>
    if q = 0 then (0, p)
    else
      pseudo_divmod_main (coeff q (degree q)) 0 p q (degree p)
        (1 + length (coeffs p) - length (coeffs q))"

lemma pseudo_divmod_main:
  assumes d: "d \<noteq> 0" "lc = coeff d (degree d)"
    and "degree r \<le> dr" "pseudo_divmod_main lc q r d dr n = (q',r')"
    and "n = 1 + dr - degree d \<or> dr = 0 \<and> n = 0 \<and> r = 0"
  shows "(r' = 0 \<or> degree r' < degree d) \<and> smult (lc^n) (d * q + r) = d * q' + r'"
  using assms(3-)
proof (induct n arbitrary: q r dr)
  case 0
  then show ?case by auto
next
  case (Suc n)
  let ?rr = "smult lc r"
  let ?qq = "coeff r dr"
  define b where [simp]: "b = monom ?qq n"
  let ?rrr = "?rr - b * d"
  let ?qqq = "smult lc q + b"
  note res = Suc(3)
  from res[unfolded pseudo_divmod_main.simps[of lc q] Let_def]
  have res: "pseudo_divmod_main lc ?qqq ?rrr d (dr - 1) n = (q',r')"
    by (simp del: pseudo_divmod_main.simps)
  from Suc(4) have dr: "dr = n + degree d" by auto
  have "coeff (b * d) dr = coeff b n * coeff d (degree d)"
  proof (cases "?qq = 0")
    case True
    then show ?thesis by auto
  next
    case False
    then have n: "n = degree b"
      by (simp add: degree_monom_eq)
    show ?thesis
      unfolding n dr by (simp add: coeff_mult_degree_sum)
  qed
  also have "\<dots> = lc * coeff b n" by (simp add: d)
  finally have "coeff (b * d) dr = lc * coeff b n" .
  moreover have "coeff ?rr dr = lc * coeff r dr"
    by simp
  ultimately have c0: "coeff ?rrr dr = 0"
    by auto
  from Suc(4) have dr: "dr = n + degree d" by auto
  have deg_rr: "degree ?rr \<le> dr"
    using Suc(2) degree_smult_le dual_order.trans by blast
  have deg_bd: "degree (b * d) \<le> dr"
    unfolding dr by (rule order.trans[OF degree_mult_le]) (auto simp: degree_monom_le)
  have "degree ?rrr \<le> dr"
    using degree_diff_le[OF deg_rr deg_bd] by auto
  with c0 have deg_rrr: "degree ?rrr \<le> (dr - 1)"
    by (rule coeff_0_degree_minus_1)
  have "n = 1 + (dr - 1) - degree d \<or> dr - 1 = 0 \<and> n = 0 \<and> ?rrr = 0"
  proof (cases dr)
    case 0
    with Suc(4) have 0: "dr = 0" "n = 0" "degree d = 0" by auto
    with deg_rrr have "degree ?rrr = 0" by simp
    then have "\<exists>a. ?rrr = [:a:]"
      by (metis degree_pCons_eq_if old.nat.distinct(2) pCons_cases)
    from this obtain a where rrr: "?rrr = [:a:]"
      by auto
    show ?thesis
      unfolding 0 using c0 unfolding rrr 0 by simp
  next
    case _: Suc
    with Suc(4) show ?thesis by auto
  qed
  note IH = Suc(1)[OF deg_rrr res this]
  show ?case
  proof (intro conjI)
    from IH show "r' = 0 \<or> degree r' < degree d"
      by blast
    show "smult (lc ^ Suc n) (d * q + r) = d * q' + r'"
      unfolding IH[THEN conjunct2,symmetric]
      by (simp add: field_simps smult_add_right)
  qed
qed

lemma pseudo_divmod:
  assumes g: "g \<noteq> 0"
    and *: "pseudo_divmod f g = (q,r)"
  shows "smult (coeff g (degree g) ^ (Suc (degree f) - degree g)) f = g * q + r"  (is ?A)
    and "r = 0 \<or> degree r < degree g"  (is ?B)
proof -
  from *[unfolded pseudo_divmod_def Let_def]
  have "pseudo_divmod_main (coeff g (degree g)) 0 f g (degree f)
      (1 + length (coeffs f) - length (coeffs g)) = (q, r)"
    by (auto simp: g)
  note main = pseudo_divmod_main[OF _ _ _ this, OF g refl le_refl]
  from g have "1 + length (coeffs f) - length (coeffs g) = 1 + degree f - degree g \<or>
    degree f = 0 \<and> 1 + length (coeffs f) - length (coeffs g) = 0 \<and> f = 0"
    by (cases "f = 0"; cases "coeffs g") (auto simp: degree_eq_length_coeffs)
  note main' = main[OF this]
  then show "r = 0 \<or> degree r < degree g" by auto
  show "smult (coeff g (degree g) ^ (Suc (degree f) - degree g)) f = g * q + r"
    by (subst main'[THEN conjunct2, symmetric], simp add: degree_eq_length_coeffs,
        cases "f = 0"; cases "coeffs g", use g in auto)
qed

definition "pseudo_mod_main lc r d dr n = snd (pseudo_divmod_main lc 0 r d dr n)"

lemma snd_pseudo_divmod_main:
  "snd (pseudo_divmod_main lc q r d dr n) = snd (pseudo_divmod_main lc q' r d dr n)"
  by (induct n arbitrary: q q' lc r d dr) (simp_all add: Let_def)

definition pseudo_mod :: "'a::{comm_ring_1,semiring_1_no_zero_divisors} poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  where "pseudo_mod f g = snd (pseudo_divmod f g)"

lemma pseudo_mod:
  fixes f g :: "'a::{comm_ring_1,semiring_1_no_zero_divisors} poly"
  defines "r \<equiv> pseudo_mod f g"
  assumes g: "g \<noteq> 0"
  shows "\<exists>a q. a \<noteq> 0 \<and> smult a f = g * q + r" "r = 0 \<or> degree r < degree g"
proof -
  let ?cg = "coeff g (degree g)"
  let ?cge = "?cg ^ (Suc (degree f) - degree g)"
  define a where "a = ?cge"
  from r_def[unfolded pseudo_mod_def] obtain q where pdm: "pseudo_divmod f g = (q, r)"
    by (cases "pseudo_divmod f g") auto
  from pseudo_divmod[OF g pdm] have id: "smult a f = g * q + r" and "r = 0 \<or> degree r < degree g"
    by (auto simp: a_def)
  show "r = 0 \<or> degree r < degree g" by fact
  from g have "a \<noteq> 0"
    by (auto simp: a_def)
  with id show "\<exists>a q. a \<noteq> 0 \<and> smult a f = g * q + r"
    by auto
qed

lemma fst_pseudo_divmod_main_as_divide_poly_main:
  assumes d: "d \<noteq> 0"
  defines lc: "lc \<equiv> coeff d (degree d)"
  shows "fst (pseudo_divmod_main lc q r d dr n) =
    divide_poly_main lc (smult (lc^n) q) (smult (lc^n) r) d dr n"
proof (induct n arbitrary: q r dr)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note lc0 = leading_coeff_neq_0[OF d, folded lc]
  then have "pseudo_divmod_main lc q r d dr (Suc n) =
    pseudo_divmod_main lc (smult lc q + monom (coeff r dr) n)
      (smult lc r - monom (coeff r dr) n * d) d (dr - 1) n"
    by (simp add: Let_def ac_simps)
  also have "fst \<dots> = divide_poly_main lc
     (smult (lc^n) (smult lc q + monom (coeff r dr) n))
     (smult (lc^n) (smult lc r - monom (coeff r dr) n * d))
     d (dr - 1) n"
    by (simp only: Suc[unfolded divide_poly_main.simps Let_def])
  also have "\<dots> = divide_poly_main lc (smult (lc ^ Suc n) q) (smult (lc ^ Suc n) r) d dr (Suc n)"
    unfolding smult_monom smult_distribs mult_smult_left[symmetric]
    using lc0 by (simp add: Let_def ac_simps)
  finally show ?case .
qed


subsubsection \<open>Division in polynomials over fields\<close>

lemma pseudo_divmod_field:
  fixes g :: "'a::field poly"
  assumes g: "g \<noteq> 0"
    and *: "pseudo_divmod f g = (q,r)"
  defines "c \<equiv> coeff g (degree g) ^ (Suc (degree f) - degree g)"
  shows "f = g * smult (1/c) q + smult (1/c) r"
proof -
  from leading_coeff_neq_0[OF g] have c0: "c \<noteq> 0"
    by (auto simp: c_def)
  from pseudo_divmod(1)[OF g *, folded c_def] have "smult c f = g * q + r"
    by auto
  also have "smult (1 / c) \<dots> = g * smult (1 / c) q + smult (1 / c) r"
    by (simp add: smult_add_right)
  finally show ?thesis
    using c0 by auto
qed

lemma divide_poly_main_field:
  fixes d :: "'a::field poly"
  assumes d: "d \<noteq> 0"
  defines lc: "lc \<equiv> coeff d (degree d)"
  shows "divide_poly_main lc q r d dr n =
    fst (pseudo_divmod_main lc (smult ((1 / lc)^n) q) (smult ((1 / lc)^n) r) d dr n)"
  unfolding lc by (subst fst_pseudo_divmod_main_as_divide_poly_main) (auto simp: d power_one_over)

lemma divide_poly_field:
  fixes f g :: "'a::field poly"
  defines "f' \<equiv> smult ((1 / coeff g (degree g)) ^ (Suc (degree f) - degree g)) f"
  shows "f div g = fst (pseudo_divmod f' g)"
proof (cases "g = 0")
  case True
  show ?thesis
    unfolding divide_poly_def pseudo_divmod_def Let_def f'_def True
    by (simp add: divide_poly_main_0)
next
  case False
  from leading_coeff_neq_0[OF False] have "degree f' = degree f"
    by (auto simp: f'_def)
  then show ?thesis
    using length_coeffs_degree[of f'] length_coeffs_degree[of f]
    unfolding divide_poly_def pseudo_divmod_def Let_def
      divide_poly_main_field[OF False]
      length_coeffs_degree[OF False]
      f'_def
    by force
qed

instantiation poly :: ("{semidom_divide_unit_factor,idom_divide}") normalization_semidom
begin

definition unit_factor_poly :: "'a poly \<Rightarrow> 'a poly"
  where "unit_factor_poly p = [:unit_factor (lead_coeff p):]"

definition normalize_poly :: "'a poly \<Rightarrow> 'a poly"
  where "normalize p = p div [:unit_factor (lead_coeff p):]"

instance
proof
  fix p :: "'a poly"
  show "unit_factor p * normalize p = p"
  proof (cases "p = 0")
    case True
    then show ?thesis
      by (simp add: unit_factor_poly_def normalize_poly_def)
  next
    case False
    then have "lead_coeff p \<noteq> 0"
      by simp
    then have *: "unit_factor (lead_coeff p) \<noteq> 0"
      using unit_factor_is_unit [of "lead_coeff p"] by auto
    then have "unit_factor (lead_coeff p) dvd 1"
      by (auto intro: unit_factor_is_unit)
    then have **: "unit_factor (lead_coeff p) dvd c" for c
      by (rule dvd_trans) simp
    have ***: "unit_factor (lead_coeff p) * (c div unit_factor (lead_coeff p)) = c" for c
    proof -
      from ** obtain b where "c = unit_factor (lead_coeff p) * b" ..
      with False * show ?thesis by simp
    qed
    have "p div [:unit_factor (lead_coeff p):] =
      map_poly (\<lambda>c. c div unit_factor (lead_coeff p)) p"
      by (simp add: const_poly_dvd_iff div_const_poly_conv_map_poly **)
    then show ?thesis
      by (simp add: normalize_poly_def unit_factor_poly_def
        smult_conv_map_poly map_poly_map_poly o_def ***)
  qed
next
  fix p :: "'a poly"
  assume "is_unit p"
  then obtain c where p: "p = [:c:]" "c dvd 1"
    by (auto simp: is_unit_poly_iff)
  then show "unit_factor p = p"
    by (simp add: unit_factor_poly_def monom_0 is_unit_unit_factor)
next
  fix p :: "'a poly"
  assume "p \<noteq> 0"
  then show "is_unit (unit_factor p)"
    by (simp add: unit_factor_poly_def monom_0 is_unit_poly_iff unit_factor_is_unit)
next
  fix a b :: "'a poly" assume "is_unit a"
  thus "unit_factor (a * b) = a * unit_factor b"
    by (auto simp: unit_factor_poly_def lead_coeff_mult unit_factor_mult elim!: is_unit_polyE)
qed (simp_all add: normalize_poly_def unit_factor_poly_def monom_0 lead_coeff_mult unit_factor_mult)

end

instance poly :: ("{semidom_divide_unit_factor,idom_divide,normalization_semidom_multiplicative}")
  normalization_semidom_multiplicative
  by intro_classes (auto simp: unit_factor_poly_def lead_coeff_mult unit_factor_mult)

lemma normalize_poly_eq_map_poly: "normalize p = map_poly (\<lambda>x. x div unit_factor (lead_coeff p)) p"
proof -
  have "[:unit_factor (lead_coeff p):] dvd p"
    by (metis unit_factor_poly_def unit_factor_self)
  then show ?thesis
    by (simp add: normalize_poly_def div_const_poly_conv_map_poly)
qed

lemma coeff_normalize [simp]:
  "coeff (normalize p) n = coeff p n div unit_factor (lead_coeff p)"
  by (simp add: normalize_poly_eq_map_poly coeff_map_poly)

class field_unit_factor = field + unit_factor +
  assumes unit_factor_field [simp]: "unit_factor = id"
begin

subclass semidom_divide_unit_factor
proof
  fix a
  assume "a \<noteq> 0"
  then have "1 = a * inverse a" by simp
  then have "a dvd 1" ..
  then show "unit_factor a dvd 1" by simp
qed simp_all

end

lemma unit_factor_pCons:
  "unit_factor (pCons a p) = (if p = 0 then [:unit_factor a:] else unit_factor p)"
  by (simp add: unit_factor_poly_def)

lemma normalize_monom [simp]: "normalize (monom a n) = monom (normalize a) n"
  by (cases "a = 0") (simp_all add: map_poly_monom normalize_poly_eq_map_poly degree_monom_eq)

lemma unit_factor_monom [simp]: "unit_factor (monom a n) = [:unit_factor a:]"
  by (cases "a = 0") (simp_all add: unit_factor_poly_def degree_monom_eq)

lemma normalize_const_poly: "normalize [:c:] = [:normalize c:]"
  by (simp add: normalize_poly_eq_map_poly map_poly_pCons)

lemma normalize_smult:
  fixes c :: "'a :: {normalization_semidom_multiplicative, idom_divide}"
  shows "normalize (smult c p) = smult (normalize c) (normalize p)"
proof -
  have "smult c p = [:c:] * p" by simp
  also have "normalize \<dots> = smult (normalize c) (normalize p)"
    by (subst normalize_mult) (simp add: normalize_const_poly)
  finally show ?thesis .
qed

inductive eucl_rel_poly :: "'a::field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<times> 'a poly \<Rightarrow> bool"
  where
    eucl_rel_poly_by0: "eucl_rel_poly x 0 (0, x)"
  | eucl_rel_poly_dividesI: "y \<noteq> 0 \<Longrightarrow> x = q * y \<Longrightarrow> eucl_rel_poly x y (q, 0)"
  | eucl_rel_poly_remainderI:
      "y \<noteq> 0 \<Longrightarrow> degree r < degree y \<Longrightarrow> x = q * y + r \<Longrightarrow> eucl_rel_poly x y (q, r)"

lemma eucl_rel_poly_iff:
  "eucl_rel_poly x y (q, r) \<longleftrightarrow>
    x = q * y + r \<and> (if y = 0 then q = 0 else r = 0 \<or> degree r < degree y)"
  by (auto elim: eucl_rel_poly.cases
      intro: eucl_rel_poly_by0 eucl_rel_poly_dividesI eucl_rel_poly_remainderI)

lemma eucl_rel_poly_0: "eucl_rel_poly 0 y (0, 0)"
  by (simp add: eucl_rel_poly_iff)

lemma eucl_rel_poly_by_0: "eucl_rel_poly x 0 (0, x)"
  by (simp add: eucl_rel_poly_iff)

lemma eucl_rel_poly_pCons:
  assumes rel: "eucl_rel_poly x y (q, r)"
  assumes y: "y \<noteq> 0"
  assumes b: "b = coeff (pCons a r) (degree y) / coeff y (degree y)"
  shows "eucl_rel_poly (pCons a x) y (pCons b q, pCons a r - smult b y)"
    (is "eucl_rel_poly ?x y (?q, ?r)")
proof -
  from assms have x: "x = q * y + r" and r: "r = 0 \<or> degree r < degree y"
    by (simp_all add: eucl_rel_poly_iff)
  from b x have "?x = ?q * y + ?r" by simp
  moreover
  have "?r = 0 \<or> degree ?r < degree y"
  proof (rule eq_zero_or_degree_less)
    show "degree ?r \<le> degree y"
    proof (rule degree_diff_le)
      from r show "degree (pCons a r) \<le> degree y"
        by auto
      show "degree (smult b y) \<le> degree y"
        by (rule degree_smult_le)
    qed
    from \<open>y \<noteq> 0\<close> show "coeff ?r (degree y) = 0"
      by (simp add: b)
  qed
  ultimately show ?thesis
    unfolding eucl_rel_poly_iff using \<open>y \<noteq> 0\<close> by simp
qed

lemma eucl_rel_poly_exists: "\<exists>q r. eucl_rel_poly x y (q, r)"
proof (cases "y = 0")
  case False
  show ?thesis
  proof (induction x)
    case 0
    then show ?case
      using eucl_rel_poly_0 by blast
  next
    case (pCons a x)
    then show ?case
      using False eucl_rel_poly_pCons by blast
  qed
qed (use eucl_rel_poly_by0 in blast)

lemma eucl_rel_poly_unique:
  assumes 1: "eucl_rel_poly x y (q1, r1)"
  assumes 2: "eucl_rel_poly x y (q2, r2)"
  shows "q1 = q2 \<and> r1 = r2"
proof (cases "y = 0")
  assume "y = 0"
  with assms show ?thesis
    by (simp add: eucl_rel_poly_iff)
next
  assume [simp]: "y \<noteq> 0"
  from 1 have q1: "x = q1 * y + r1" and r1: "r1 = 0 \<or> degree r1 < degree y"
    unfolding eucl_rel_poly_iff by simp_all
  from 2 have q2: "x = q2 * y + r2" and r2: "r2 = 0 \<or> degree r2 < degree y"
    unfolding eucl_rel_poly_iff by simp_all
  from q1 q2 have q3: "(q1 - q2) * y = r2 - r1"
    by (simp add: algebra_simps)
  from r1 r2 have r3: "(r2 - r1) = 0 \<or> degree (r2 - r1) < degree y"
    by (auto intro: degree_diff_less)
  show "q1 = q2 \<and> r1 = r2"
  proof (rule classical)
    assume "\<not> ?thesis"
    with q3 have "q1 \<noteq> q2" and "r1 \<noteq> r2" by auto
    with r3 have "degree (r2 - r1) < degree y" by simp
    also have "degree y \<le> degree (q1 - q2) + degree y" by simp
    also from \<open>q1 \<noteq> q2\<close> have "\<dots> = degree ((q1 - q2) * y)"
      by (simp add: degree_mult_eq)
    also from q3 have "\<dots> = degree (r2 - r1)"
      by simp
    finally have "degree (r2 - r1) < degree (r2 - r1)" .
    then show ?thesis by simp
  qed
qed

lemma eucl_rel_poly_0_iff: "eucl_rel_poly 0 y (q, r) \<longleftrightarrow> q = 0 \<and> r = 0"
  by (auto dest: eucl_rel_poly_unique intro: eucl_rel_poly_0)

lemma eucl_rel_poly_by_0_iff: "eucl_rel_poly x 0 (q, r) \<longleftrightarrow> q = 0 \<and> r = x"
  by (auto dest: eucl_rel_poly_unique intro: eucl_rel_poly_by_0)

lemmas eucl_rel_poly_unique_div = eucl_rel_poly_unique [THEN conjunct1]

lemmas eucl_rel_poly_unique_mod = eucl_rel_poly_unique [THEN conjunct2]

instantiation poly :: (field) semidom_modulo
begin

definition modulo_poly :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  where mod_poly_def: "f mod g =
    (if g = 0 then f else pseudo_mod (smult ((1 / lead_coeff g) ^ (Suc (degree f) - degree g)) f) g)"

instance
proof
  fix x y :: "'a poly"
  show "x div y * y + x mod y = x"
  proof (cases "y = 0")
    case True
    then show ?thesis
      by (simp add: divide_poly_0 mod_poly_def)
  next
    case False
    then have "pseudo_divmod (smult ((1 / lead_coeff y) ^ (Suc (degree x) - degree y)) x) y =
        (x div y, x mod y)"
      by (simp add: divide_poly_field mod_poly_def pseudo_mod_def)
    with False pseudo_divmod [OF False this] show ?thesis
      by (simp add: power_mult_distrib [symmetric] ac_simps)
  qed
qed

end

lemma eucl_rel_poly: "eucl_rel_poly x y (x div y, x mod y)"
  unfolding eucl_rel_poly_iff
proof
  show "x = x div y * y + x mod y"
    by (simp add: div_mult_mod_eq)
  show "if y = 0 then x div y = 0 else x mod y = 0 \<or> degree (x mod y) < degree y"
  proof (cases "y = 0")
    case True
    then show ?thesis by auto
  next
    case False
    with pseudo_mod[OF this] show ?thesis
      by (simp add: mod_poly_def)
  qed
qed

lemma div_poly_eq: "eucl_rel_poly x y (q, r) \<Longrightarrow> x div y = q"
  for x :: "'a::field poly"
  by (rule eucl_rel_poly_unique_div [OF eucl_rel_poly])

lemma mod_poly_eq: "eucl_rel_poly x y (q, r) \<Longrightarrow> x mod y = r"
  for x :: "'a::field poly"
  by (rule eucl_rel_poly_unique_mod [OF eucl_rel_poly])

instance poly :: (field) idom_modulo ..

lemma div_pCons_eq:
  "pCons a p div q =
    (if q = 0 then 0
     else pCons (coeff (pCons a (p mod q)) (degree q) / lead_coeff q) (p div q))"
  using eucl_rel_poly_pCons [OF eucl_rel_poly _ refl, of q a p]
  by (auto intro: div_poly_eq)

lemma mod_pCons_eq:
  "pCons a p mod q =
    (if q = 0 then pCons a p
     else pCons a (p mod q) - smult (coeff (pCons a (p mod q)) (degree q) / lead_coeff q) q)"
  using eucl_rel_poly_pCons [OF eucl_rel_poly _ refl, of q a p]
  by (auto intro: mod_poly_eq)

lemma div_mod_fold_coeffs:
  "(p div q, p mod q) =
    (if q = 0 then (0, p)
     else
      fold_coeffs
        (\<lambda>a (s, r).
          let b = coeff (pCons a r) (degree q) / coeff q (degree q)
          in (pCons b s, pCons a r - smult b q)) p (0, 0))"
  by (rule sym, induct p) (auto simp: div_pCons_eq mod_pCons_eq Let_def)

lemma degree_mod_less: "y \<noteq> 0 \<Longrightarrow> x mod y = 0 \<or> degree (x mod y) < degree y"
  using eucl_rel_poly [of x y] unfolding eucl_rel_poly_iff by simp

lemma degree_mod_less': "b \<noteq> 0 \<Longrightarrow> a mod b \<noteq> 0 \<Longrightarrow> degree (a mod b) < degree b"
  using degree_mod_less[of b a] by auto

lemma div_poly_less:
  fixes x :: "'a::field poly"
  assumes "degree x < degree y"
  shows "x div y = 0"
proof -
  from assms have "eucl_rel_poly x y (0, x)"
    by (simp add: eucl_rel_poly_iff)
  then show "x div y = 0"
    by (rule div_poly_eq)
qed

lemma mod_poly_less:
  assumes "degree x < degree y"
  shows "x mod y = x"
proof -
  from assms have "eucl_rel_poly x y (0, x)"
    by (simp add: eucl_rel_poly_iff)
  then show "x mod y = x"
    by (rule mod_poly_eq)
qed

lemma eucl_rel_poly_smult_left:
  "eucl_rel_poly x y (q, r) \<Longrightarrow> eucl_rel_poly (smult a x) y (smult a q, smult a r)"
  by (simp add: eucl_rel_poly_iff smult_add_right)

lemma div_smult_left: "(smult a x) div y = smult a (x div y)"
  for x y :: "'a::field poly"
  by (rule div_poly_eq, rule eucl_rel_poly_smult_left, rule eucl_rel_poly)

lemma mod_smult_left: "(smult a x) mod y = smult a (x mod y)"
  by (rule mod_poly_eq, rule eucl_rel_poly_smult_left, rule eucl_rel_poly)

lemma poly_div_minus_left [simp]: "(- x) div y = - (x div y)"
  for x y :: "'a::field poly"
  using div_smult_left [of "- 1::'a"] by simp

lemma poly_mod_minus_left [simp]: "(- x) mod y = - (x mod y)"
  for x y :: "'a::field poly"
  using mod_smult_left [of "- 1::'a"] by simp

lemma eucl_rel_poly_add_left:
  assumes "eucl_rel_poly x y (q, r)"
  assumes "eucl_rel_poly x' y (q', r')"
  shows "eucl_rel_poly (x + x') y (q + q', r + r')"
  using assms unfolding eucl_rel_poly_iff
  by (auto simp: algebra_simps degree_add_less)

lemma poly_div_add_left: "(x + y) div z = x div z + y div z"
  for x y z :: "'a::field poly"
  using eucl_rel_poly_add_left [OF eucl_rel_poly eucl_rel_poly]
  by (rule div_poly_eq)

lemma poly_mod_add_left: "(x + y) mod z = x mod z + y mod z"
  for x y z :: "'a::field poly"
  using eucl_rel_poly_add_left [OF eucl_rel_poly eucl_rel_poly]
  by (rule mod_poly_eq)

lemma poly_div_diff_left: "(x - y) div z = x div z - y div z"
  for x y z :: "'a::field poly"
  by (simp only: diff_conv_add_uminus poly_div_add_left poly_div_minus_left)

lemma poly_mod_diff_left: "(x - y) mod z = x mod z - y mod z"
  for x y z :: "'a::field poly"
  by (simp only: diff_conv_add_uminus poly_mod_add_left poly_mod_minus_left)

lemma eucl_rel_poly_smult_right:
  "a \<noteq> 0 \<Longrightarrow> eucl_rel_poly x y (q, r) \<Longrightarrow> eucl_rel_poly x (smult a y) (smult (inverse a) q, r)"
  by (simp add: eucl_rel_poly_iff)

lemma div_smult_right: "a \<noteq> 0 \<Longrightarrow> x div (smult a y) = smult (inverse a) (x div y)"
  for x y :: "'a::field poly"
  by (rule div_poly_eq, erule eucl_rel_poly_smult_right, rule eucl_rel_poly)

lemma mod_smult_right: "a \<noteq> 0 \<Longrightarrow> x mod (smult a y) = x mod y"
  by (rule mod_poly_eq, erule eucl_rel_poly_smult_right, rule eucl_rel_poly)

lemma poly_div_minus_right [simp]: "x div (- y) = - (x div y)"
  for x y :: "'a::field poly"
  using div_smult_right [of "- 1::'a"] by (simp add: nonzero_inverse_minus_eq)

lemma poly_mod_minus_right [simp]: "x mod (- y) = x mod y"
  for x y :: "'a::field poly"
  using mod_smult_right [of "- 1::'a"] by simp

lemma eucl_rel_poly_mult:
  assumes "eucl_rel_poly x y (q, r)" "eucl_rel_poly q z (q', r')"
  shows "eucl_rel_poly x (y * z) (q', y * r' + r)"
proof (cases "y = 0")
  case True
  with assms eucl_rel_poly_0_iff show ?thesis
    by (force simp add: eucl_rel_poly_iff)
next
  case False
  show ?thesis
  proof (cases "r' = 0")
    case True
    with assms show ?thesis
      by (auto simp add: eucl_rel_poly_iff degree_mult_eq)
  next
    case False
    with assms \<open>y \<noteq> 0\<close> show ?thesis
      by (auto simp add: eucl_rel_poly_iff degree_add_less degree_mult_eq field_simps)
  qed
qed

lemma poly_div_mult_right: "x div (y * z) = (x div y) div z"
  for x y z :: "'a::field poly"
  by (rule div_poly_eq, rule eucl_rel_poly_mult, (rule eucl_rel_poly)+)

lemma poly_mod_mult_right: "x mod (y * z) = y * (x div y mod z) + x mod y"
  for x y z :: "'a::field poly"
  by (rule mod_poly_eq, rule eucl_rel_poly_mult, (rule eucl_rel_poly)+)

lemma mod_pCons:
  fixes a :: "'a::field"
    and x y :: "'a::field poly"
  assumes y: "y \<noteq> 0"
  defines "b \<equiv> coeff (pCons a (x mod y)) (degree y) / coeff y (degree y)"
  shows "(pCons a x) mod y = pCons a (x mod y) - smult b y"
  unfolding b_def
  by (rule mod_poly_eq, rule eucl_rel_poly_pCons [OF eucl_rel_poly y refl])


subsubsection \<open>List-based versions for fast implementation\<close>
(* Subsection by:
      Sebastiaan Joosten
      René Thiemann
      Akihisa Yamada
    *)
fun minus_poly_rev_list :: "'a :: group_add list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "minus_poly_rev_list (x # xs) (y # ys) = (x - y) # (minus_poly_rev_list xs ys)"
  | "minus_poly_rev_list xs [] = xs"
  | "minus_poly_rev_list [] (y # ys) = []"

fun pseudo_divmod_main_list ::
  "'a::comm_ring_1 \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list \<times> 'a list"
  where
    "pseudo_divmod_main_list lc q r d (Suc n) =
      (let
        rr = map ((*) lc) r;
        a = hd r;
        qqq = cCons a (map ((*) lc) q);
        rrr = tl (if a = 0 then rr else minus_poly_rev_list rr (map ((*) a) d))
       in pseudo_divmod_main_list lc qqq rrr d n)"
  | "pseudo_divmod_main_list lc q r d 0 = (q, r)"

fun pseudo_mod_main_list :: "'a::comm_ring_1 \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list"
  where
    "pseudo_mod_main_list lc r d (Suc n) =
      (let
        rr = map ((*) lc) r;
        a = hd r;
        rrr = tl (if a = 0 then rr else minus_poly_rev_list rr (map ((*) a) d))
       in pseudo_mod_main_list lc rrr d n)"
  | "pseudo_mod_main_list lc r d 0 = r"


fun divmod_poly_one_main_list ::
    "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list \<times> 'a list"
  where
    "divmod_poly_one_main_list q r d (Suc n) =
      (let
        a = hd r;
        qqq = cCons a q;
        rr = tl (if a = 0 then r else minus_poly_rev_list r (map ((*) a) d))
       in divmod_poly_one_main_list qqq rr d n)"
  | "divmod_poly_one_main_list q r d 0 = (q, r)"

fun mod_poly_one_main_list :: "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list"
  where
    "mod_poly_one_main_list r d (Suc n) =
      (let
        a = hd r;
        rr = tl (if a = 0 then r else minus_poly_rev_list r (map ((*) a) d))
       in mod_poly_one_main_list rr d n)"
  | "mod_poly_one_main_list r d 0 = r"

definition pseudo_divmod_list :: "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list"
  where "pseudo_divmod_list p q =
    (if q = [] then ([], p)
     else
      (let rq = rev q;
        (qu,re) = pseudo_divmod_main_list (hd rq) [] (rev p) rq (1 + length p - length q)
       in (qu, rev re)))"

definition pseudo_mod_list :: "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "pseudo_mod_list p q =
    (if q = [] then p
     else
      (let
        rq = rev q;
        re = pseudo_mod_main_list (hd rq) (rev p) rq (1 + length p - length q)
       in rev re))"

lemma minus_zero_does_nothing: "minus_poly_rev_list x (map ((*) 0) y) = x"
  for x :: "'a::ring list"
  by (induct x y rule: minus_poly_rev_list.induct) auto

lemma length_minus_poly_rev_list [simp]: "length (minus_poly_rev_list xs ys) = length xs"
  by (induct xs ys rule: minus_poly_rev_list.induct) auto

lemma if_0_minus_poly_rev_list:
  "(if a = 0 then x else minus_poly_rev_list x (map ((*) a) y)) =
    minus_poly_rev_list x (map ((*) a) y)"
  for a :: "'a::ring"
  by(cases "a = 0") (simp_all add: minus_zero_does_nothing)

lemma Poly_append: "Poly (a @ b) = Poly a + monom 1 (length a) * Poly b"
  for a :: "'a::comm_semiring_1 list"
  by (induct a) (auto simp: monom_0 monom_Suc)

lemma minus_poly_rev_list: "length p \<ge> length q \<Longrightarrow>
  Poly (rev (minus_poly_rev_list (rev p) (rev q))) =
    Poly p - monom 1 (length p - length q) * Poly q"
  for p q :: "'a :: comm_ring_1 list"
proof (induct "rev p" "rev q" arbitrary: p q rule: minus_poly_rev_list.induct)
  case (1 x xs y ys)
  then have "length (rev q) \<le> length (rev p)"
    by simp
  from this[folded 1(2,3)] have ys_xs: "length ys \<le> length xs"
    by simp
  then have *: "Poly (rev (minus_poly_rev_list xs ys)) =
      Poly (rev xs) - monom 1 (length xs - length ys) * Poly (rev ys)"
    by (subst "1.hyps"(1)[of "rev xs" "rev ys", unfolded rev_rev_ident length_rev]) auto
  have "Poly p - monom 1 (length p - length q) * Poly q =
    Poly (rev (rev p)) - monom 1 (length (rev (rev p)) - length (rev (rev q))) * Poly (rev (rev q))"
    by simp
  also have "\<dots> =
      Poly (rev (x # xs)) - monom 1 (length (x # xs) - length (y # ys)) * Poly (rev (y # ys))"
    unfolding 1(2,3) by simp
  also from ys_xs have "\<dots> =
    Poly (rev xs) + monom x (length xs) -
      (monom 1 (length xs - length ys) * Poly (rev ys) + monom y (length xs))"
    by (simp add: Poly_append distrib_left mult_monom smult_monom)
  also have "\<dots> = Poly (rev (minus_poly_rev_list xs ys)) + monom (x - y) (length xs)"
    unfolding * diff_monom[symmetric] by simp
  finally show ?case
    by (simp add: 1(2,3)[symmetric] smult_monom Poly_append)
qed auto

lemma smult_monom_mult: "smult a (monom b n * f) = monom (a * b) n * f"
  using smult_monom [of a _ n] by (metis mult_smult_left)

lemma head_minus_poly_rev_list:
  "length d \<le> length r \<Longrightarrow> d \<noteq> [] \<Longrightarrow>
    hd (minus_poly_rev_list (map ((*) (last d)) r) (map ((*) (hd r)) (rev d))) = 0"
  for d r :: "'a::comm_ring list"
proof (induct r)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  then show ?case by (cases "rev d") (simp_all add: ac_simps)
qed

lemma Poly_map: "Poly (map ((*) a) p) = smult a (Poly p)"
proof (induct p)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases "Poly xs = 0") auto
qed

lemma last_coeff_is_hd: "xs \<noteq> [] \<Longrightarrow> coeff (Poly xs) (length xs - 1) = hd (rev xs)"
  by (simp_all add: hd_conv_nth rev_nth nth_default_nth nth_append)

lemma pseudo_divmod_main_list_invar:
  assumes leading_nonzero: "last d \<noteq> 0"
    and lc: "last d = lc"
    and "d \<noteq> []"
    and "pseudo_divmod_main_list lc q (rev r) (rev d) n = (q', rev r')"
    and "n = 1 + length r - length d"
  shows "pseudo_divmod_main lc (monom 1 n * Poly q) (Poly r) (Poly d) (length r - 1) n =
    (Poly q', Poly r')"
  using assms(4-)
proof (induct n arbitrary: r q)
  case (Suc n)
  from Suc.prems have *: "\<not> Suc (length r) \<le> length d"
    by simp
  with \<open>d \<noteq> []\<close> have "r \<noteq> []"
    using Suc_leI length_greater_0_conv list.size(3) by fastforce
  let ?a = "(hd (rev r))"
  let ?rr = "map ((*) lc) (rev r)"
  let ?rrr = "rev (tl (minus_poly_rev_list ?rr (map ((*) ?a) (rev d))))"
  let ?qq = "cCons ?a (map ((*) lc) q)"
  from * Suc(3) have n: "n = (1 + length r - length d - 1)"
    by simp
  from * have rr_val:"(length ?rrr) = (length r - 1)"
    by auto
  with \<open>r \<noteq> []\<close> * have rr_smaller: "(1 + length r - length d - 1) = (1 + length ?rrr - length d)"
    by auto
  from * have id: "Suc (length r) - length d = Suc (length r - length d)"
    by auto
  from Suc.prems *
  have "pseudo_divmod_main_list lc ?qq (rev ?rrr) (rev d) (1 + length r - length d - 1) = (q', rev r')"
    by (simp add: Let_def if_0_minus_poly_rev_list id)
  with n have v: "pseudo_divmod_main_list lc ?qq (rev ?rrr) (rev d) n = (q', rev r')"
    by auto
  from * have sucrr:"Suc (length r) - length d = Suc (length r - length d)"
    using Suc_diff_le not_less_eq_eq by blast
  from Suc(3) \<open>r \<noteq> []\<close> have n_ok : "n = 1 + (length ?rrr) - length d"
    by simp
  have cong: "\<And>x1 x2 x3 x4 y1 y2 y3 y4. x1 = y1 \<Longrightarrow> x2 = y2 \<Longrightarrow> x3 = y3 \<Longrightarrow> x4 = y4 \<Longrightarrow>
      pseudo_divmod_main lc x1 x2 x3 x4 n = pseudo_divmod_main lc y1 y2 y3 y4 n"
    by simp
  have hd_rev: "coeff (Poly r) (length r - Suc 0) = hd (rev r)"
    using last_coeff_is_hd[OF \<open>r \<noteq> []\<close>] by simp
  show ?case
    unfolding Suc.hyps(1)[OF v n_ok, symmetric] pseudo_divmod_main.simps Let_def
  proof (rule cong[OF _ _ refl], goal_cases)
    case 1
    show ?case
      by (simp add: monom_Suc hd_rev[symmetric] smult_monom Poly_map)
  next
    case 2
    show ?case
    proof (subst Poly_on_rev_starting_with_0, goal_cases)
      show "hd (minus_poly_rev_list (map ((*) lc) (rev r)) (map ((*) (hd (rev r))) (rev d))) = 0"
        by (fold lc, subst head_minus_poly_rev_list, insert * \<open>d \<noteq> []\<close>, auto)
      from * have "length d \<le> length r"
        by simp
      then show "smult lc (Poly r) - monom (coeff (Poly r) (length r - 1)) n * Poly d =
          Poly (rev (minus_poly_rev_list (map ((*) lc) (rev r)) (map ((*) (hd (rev r))) (rev d))))"
        by (fold rev_map) (auto simp add: n smult_monom_mult Poly_map hd_rev [symmetric]
            minus_poly_rev_list)
    qed
  qed simp
qed simp

lemma pseudo_divmod_impl [code]:
  "pseudo_divmod f g = map_prod poly_of_list poly_of_list (pseudo_divmod_list (coeffs f) (coeffs g))"
    for f g :: "'a::comm_ring_1 poly"
proof (cases "g = 0")
  case False
  then have "last (coeffs g) \<noteq> 0"
    and "last (coeffs g) = lead_coeff g"
    and "coeffs g \<noteq> []"
    by (simp_all add: last_coeffs_eq_coeff_degree)
  moreover obtain q r where qr: "pseudo_divmod_main_list
    (last (coeffs g)) (rev [])
    (rev (coeffs f)) (rev (coeffs g))
    (1 + length (coeffs f) -
    length (coeffs g)) = (q, rev (rev r))"
    by force
  ultimately have "(Poly q, Poly (rev r)) = pseudo_divmod_main (lead_coeff g) 0 f g
    (length (coeffs f) - Suc 0) (Suc (length (coeffs f)) - length (coeffs g))"
    by (subst pseudo_divmod_main_list_invar [symmetric]) auto
  moreover have "pseudo_divmod_main_list
    (hd (rev (coeffs g))) []
    (rev (coeffs f)) (rev (coeffs g))
    (1 + length (coeffs f) -
    length (coeffs g)) = (q, r)"
    by (metis hd_rev qr rev.simps(1) rev_swap)
  ultimately show ?thesis
    by (simp add: degree_eq_length_coeffs pseudo_divmod_def pseudo_divmod_list_def)
next
  case True
  then show ?thesis
    by (auto simp add: pseudo_divmod_def pseudo_divmod_list_def)
qed

lemma pseudo_mod_main_list:
  "snd (pseudo_divmod_main_list l q xs ys n) = pseudo_mod_main_list l xs ys n"
  by (induct n arbitrary: l q xs ys) (auto simp: Let_def)

lemma pseudo_mod_impl[code]: "pseudo_mod f g = poly_of_list (pseudo_mod_list (coeffs f) (coeffs g))"
proof -
  have snd_case: "\<And>f g p. snd ((\<lambda>(x,y). (f x, g y)) p) = g (snd p)"
    by auto
  show ?thesis
    unfolding pseudo_mod_def pseudo_divmod_impl pseudo_divmod_list_def
      pseudo_mod_list_def Let_def
    by (simp add: snd_case pseudo_mod_main_list)
qed


subsubsection \<open>Improved Code-Equations for Polynomial (Pseudo) Division\<close>

lemma pdivmod_pdivmodrel: "eucl_rel_poly p q (r, s) \<longleftrightarrow> (p div q, p mod q) = (r, s)"
  by (metis eucl_rel_poly eucl_rel_poly_unique)

lemma pdivmod_via_pseudo_divmod:
  "(f div g, f mod g) =
    (if g = 0 then (0, f)
     else
      let
        ilc = inverse (coeff g (degree g));
        h = smult ilc g;
        (q,r) = pseudo_divmod f h
      in (smult ilc q, r))"
  (is "?l = ?r")
proof (cases "g = 0")
  case True
  then show ?thesis by simp
next
  case False
  define lc where "lc = inverse (coeff g (degree g))"
  define h where "h = smult lc g"
  from False have h1: "coeff h (degree h) = 1" and lc: "lc \<noteq> 0"
    by (auto simp: h_def lc_def)
  then have h0: "h \<noteq> 0"
    by auto
  obtain q r where p: "pseudo_divmod f h = (q, r)"
    by force
  from False have id: "?r = (smult lc q, r)"
    by (auto simp: Let_def h_def[symmetric] lc_def[symmetric] p)
  from pseudo_divmod[OF h0 p, unfolded h1]
  have f: "f = h * q + r" and r: "r = 0 \<or> degree r < degree h"
    by auto
  from f r h0 have "eucl_rel_poly f h (q, r)"
    by (auto simp: eucl_rel_poly_iff)
  then have "(f div h, f mod h) = (q, r)"
    by (simp add: pdivmod_pdivmodrel)
  with lc have "(f div g, f mod g) = (smult lc q, r)"
    by (auto simp: h_def div_smult_right[OF lc] mod_smult_right[OF lc])
  with id show ?thesis
    by auto
qed

lemma pdivmod_via_pseudo_divmod_list:
  "(f div g, f mod g) =
    (let cg = coeffs g in
      if cg = [] then (0, f)
      else
        let
          cf = coeffs f;
          ilc = inverse (last cg);
          ch = map ((*) ilc) cg;
          (q, r) = pseudo_divmod_main_list 1 [] (rev cf) (rev ch) (1 + length cf - length cg)
        in (poly_of_list (map ((*) ilc) q), poly_of_list (rev r)))"
proof -
  note d = pdivmod_via_pseudo_divmod pseudo_divmod_impl pseudo_divmod_list_def
  show ?thesis
  proof (cases "g = 0")
    case True
    with d show ?thesis by auto
  next
    case False
    define ilc where "ilc = inverse (coeff g (degree g))"
    from False have ilc: "ilc \<noteq> 0"
      by (auto simp: ilc_def)
    with False have id: "g = 0 \<longleftrightarrow> False" "coeffs g = [] \<longleftrightarrow> False"
      "last (coeffs g) = coeff g (degree g)"
      "coeffs (smult ilc g) = [] \<longleftrightarrow> False"
      by (auto simp: last_coeffs_eq_coeff_degree)
    have id2: "hd (rev (coeffs (smult ilc g))) = 1"
      by (subst hd_rev, insert id ilc, auto simp: coeffs_smult, subst last_map, auto simp: id ilc_def)
    have id3: "length (coeffs (smult ilc g)) = length (coeffs g)"
      "rev (coeffs (smult ilc g)) = rev (map ((*) ilc) (coeffs g))"
      unfolding coeffs_smult using ilc by auto
    obtain q r where pair:
      "pseudo_divmod_main_list 1 [] (rev (coeffs f)) (rev (map ((*) ilc) (coeffs g)))
        (1 + length (coeffs f) - length (coeffs g)) = (q, r)"
      by force
    show ?thesis
      unfolding d Let_def id if_False ilc_def[symmetric] map_prod_def[symmetric] id2
      unfolding id3 pair map_prod_def split
      by (auto simp: Poly_map)
  qed
qed

lemma pseudo_divmod_main_list_1: "pseudo_divmod_main_list 1 = divmod_poly_one_main_list"
proof (intro ext, goal_cases)
  case (1 q r d n)
  have *: "map ((*) 1) xs = xs" for xs :: "'a list"
    by (induct xs) auto
  show ?case
    by (induct n arbitrary: q r d) (auto simp: * Let_def)
qed

fun divide_poly_main_list :: "'a::idom_divide \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list"
  where
    "divide_poly_main_list lc q r d (Suc n) =
      (let
        cr = hd r
        in if cr = 0 then divide_poly_main_list lc (cCons cr q) (tl r) d n else let
        a = cr div lc;
        qq = cCons a q;
        rr = minus_poly_rev_list r (map ((*) a) d)
       in if hd rr = 0 then divide_poly_main_list lc qq (tl rr) d n else [])"
  | "divide_poly_main_list lc q r d 0 = q"

lemma divide_poly_main_list_simp [simp]:
  "divide_poly_main_list lc q r d (Suc n) =
    (let
      cr = hd r;
      a = cr div lc;
      qq = cCons a q;
      rr = minus_poly_rev_list r (map ((*) a) d)
     in if hd rr = 0 then divide_poly_main_list lc qq (tl rr) d n else [])"
  by (simp add: Let_def minus_zero_does_nothing)

declare divide_poly_main_list.simps(1)[simp del]

definition divide_poly_list :: "'a::idom_divide poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  where "divide_poly_list f g =
    (let cg = coeffs g in
      if cg = [] then g
      else
        let
          cf = coeffs f;
          cgr = rev cg
        in poly_of_list (divide_poly_main_list (hd cgr) [] (rev cf) cgr (1 + length cf - length cg)))"

lemmas pdivmod_via_divmod_list = pdivmod_via_pseudo_divmod_list[unfolded pseudo_divmod_main_list_1]

lemma mod_poly_one_main_list: "snd (divmod_poly_one_main_list q r d n) = mod_poly_one_main_list r d n"
  by (induct n arbitrary: q r d) (auto simp: Let_def)

lemma mod_poly_code [code]:
  "f mod g =
    (let cg = coeffs g in
      if cg = [] then f
      else
        let
          cf = coeffs f;
          ilc = inverse (last cg);
          ch = map ((*) ilc) cg;
          r = mod_poly_one_main_list (rev cf) (rev ch) (1 + length cf - length cg)
        in poly_of_list (rev r))"
  (is "_ = ?rhs")
proof -
  have "snd (f div g, f mod g) = ?rhs"
    unfolding pdivmod_via_divmod_list Let_def mod_poly_one_main_list [symmetric, of _ _ _ Nil]
    by (auto split: prod.splits)
  then show ?thesis by simp
qed

definition div_field_poly_impl :: "'a :: field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  where "div_field_poly_impl f g =
    (let cg = coeffs g in
      if cg = [] then 0
      else
        let
          cf = coeffs f;
          ilc = inverse (last cg);
          ch = map ((*) ilc) cg;
          q = fst (divmod_poly_one_main_list [] (rev cf) (rev ch) (1 + length cf - length cg))
        in poly_of_list ((map ((*) ilc) q)))"

text \<open>We do not declare the following lemma as code equation, since then polynomial division
  on non-fields will no longer be executable. However, a code-unfold is possible, since
  \<open>div_field_poly_impl\<close> is a bit more efficient than the generic polynomial division.\<close>
lemma div_field_poly_impl[code_unfold]: "(div) = div_field_poly_impl"
proof (intro ext)
  fix f g :: "'a poly"
  have "fst (f div g, f mod g) = div_field_poly_impl f g"
    unfolding div_field_poly_impl_def pdivmod_via_divmod_list Let_def
    by (auto split: prod.splits)
  then show "f div g =  div_field_poly_impl f g"
    by simp
qed

lemma divide_poly_main_list:
  assumes lc0: "lc \<noteq> 0"
    and lc: "last d = lc"
    and d: "d \<noteq> []"
    and "n = (1 + length r - length d)"
  shows "Poly (divide_poly_main_list lc q (rev r) (rev d) n) =
    divide_poly_main lc (monom 1 n * Poly q) (Poly r) (Poly d) (length r - 1) n"
  using assms(4-)
proof (induct "n" arbitrary: r q)
  case (Suc n)
  from Suc.prems have ifCond: "\<not> Suc (length r) \<le> length d"
    by simp
  with d have r: "r \<noteq> []"
    using Suc_leI length_greater_0_conv list.size(3) by fastforce
  then obtain rr lcr where r: "r = rr @ [lcr]"
    by (cases r rule: rev_cases) auto
  from d lc obtain dd where d: "d = dd @ [lc]"
    by (cases d rule: rev_cases) auto
  from Suc(2) ifCond have n: "n = 1 + length rr - length d"
    by (auto simp: r)
  from ifCond have len: "length dd \<le> length rr"
    by (simp add: r d)
  show ?case
  proof (cases "lcr div lc * lc = lcr")
    case False
    with r d show ?thesis
      unfolding Suc(2)[symmetric]
      by (auto simp add: Let_def nth_default_append)
  next
    case True
    with r d have id:
      "?thesis \<longleftrightarrow>
        Poly (divide_poly_main_list lc (cCons (lcr div lc) q)
          (rev (rev (minus_poly_rev_list (rev rr) (rev (map ((*) (lcr div lc)) dd))))) (rev d) n) =
          divide_poly_main lc
            (monom 1 (Suc n) * Poly q + monom (lcr div lc) n)
            (Poly r - monom (lcr div lc) n * Poly d)
            (Poly d) (length rr - 1) n"
      by (cases r rule: rev_cases; cases "d" rule: rev_cases)
        (auto simp add: Let_def rev_map nth_default_append)
    have cong: "\<And>x1 x2 x3 x4 y1 y2 y3 y4. x1 = y1 \<Longrightarrow> x2 = y2 \<Longrightarrow> x3 = y3 \<Longrightarrow> x4 = y4 \<Longrightarrow>
        divide_poly_main lc x1 x2 x3 x4 n = divide_poly_main lc y1 y2 y3 y4 n"
      by simp
    show ?thesis
      unfolding id
    proof (subst Suc(1), simp add: n,
        subst minus_poly_rev_list, force simp: len, rule cong[OF _ _ refl], goal_cases)
      case 2
      have "monom lcr (length rr) = monom (lcr div lc) (length rr - length dd) * monom lc (length dd)"
        by (simp add: mult_monom len True)
      then show ?case unfolding r d Poly_append n ring_distribs
        by (auto simp: Poly_map smult_monom smult_monom_mult)
    qed (auto simp: len monom_Suc smult_monom)
  qed
qed simp

lemma divide_poly_list[code]: "f div g = divide_poly_list f g"
proof -
  note d = divide_poly_def divide_poly_list_def
  show ?thesis
  proof (cases "g = 0")
    case True
    show ?thesis by (auto simp: d True)
  next
    case False
    then obtain cg lcg where cg: "coeffs g = cg @ [lcg]"
      by (cases "coeffs g" rule: rev_cases) auto
    with False have id: "(g = 0) = False" "(cg @ [lcg] = []) = False"
      by auto
    from cg False have lcg: "coeff g (degree g) = lcg"
      using last_coeffs_eq_coeff_degree last_snoc by force
    with False have "lcg \<noteq> 0" by auto
    from cg Poly_coeffs [of g] have ltp: "Poly (cg @ [lcg]) = g"
      by auto
    show ?thesis
      unfolding d cg Let_def id if_False poly_of_list_def
      by (subst divide_poly_main_list, insert False cg \<open>lcg \<noteq> 0\<close>)
        (auto simp: lcg ltp, simp add: degree_eq_length_coeffs)
  qed
qed


subsection \<open>Primality and irreducibility in polynomial rings\<close>

lemma prod_mset_const_poly: "(\<Prod>x\<in>#A. [:f x:]) = [:prod_mset (image_mset f A):]"
  by (induct A) (simp_all add: ac_simps)

lemma irreducible_const_poly_iff:
  fixes c :: "'a :: {comm_semiring_1,semiring_no_zero_divisors}"
  shows "irreducible [:c:] \<longleftrightarrow> irreducible c"
proof
  assume A: "irreducible c"
  show "irreducible [:c:]"
  proof (rule irreducibleI)
    fix a b assume ab: "[:c:] = a * b"
    hence "degree [:c:] = degree (a * b)" by (simp only: )
    also from A ab have "a \<noteq> 0" "b \<noteq> 0" by auto
    hence "degree (a * b) = degree a + degree b" by (simp add: degree_mult_eq)
    finally have "degree a = 0" "degree b = 0" by auto
    then obtain a' b' where ab': "a = [:a':]" "b = [:b':]" by (auto elim!: degree_eq_zeroE)
    from ab have "coeff [:c:] 0 = coeff (a * b) 0" by (simp only: )
    hence "c = a' * b'" by (simp add: ab' mult_ac)
    from A and this have "a' dvd 1 \<or> b' dvd 1" by (rule irreducibleD)
    with ab' show "a dvd 1 \<or> b dvd 1"
      by (auto simp add: is_unit_const_poly_iff)
  qed (insert A, auto simp: irreducible_def is_unit_poly_iff)
next
  assume A: "irreducible [:c:]"
  then have "c \<noteq> 0" and "\<not> c dvd 1"
    by (auto simp add: irreducible_def is_unit_const_poly_iff)
  then show "irreducible c"
  proof (rule irreducibleI)
    fix a b assume ab: "c = a * b"
    hence "[:c:] = [:a:] * [:b:]" by (simp add: mult_ac)
    from A and this have "[:a:] dvd 1 \<or> [:b:] dvd 1" by (rule irreducibleD)
    then show "a dvd 1 \<or> b dvd 1"
      by (auto simp add: is_unit_const_poly_iff)
  qed
qed

lemma lift_prime_elem_poly:
  assumes "prime_elem (c :: 'a :: semidom)"
  shows   "prime_elem [:c:]"
proof (rule prime_elemI)
  fix a b assume *: "[:c:] dvd a * b"
  from * have dvd: "c dvd coeff (a * b) n" for n
    by (subst (asm) const_poly_dvd_iff) blast
  {
    define m where "m = (GREATEST m. \<not>c dvd coeff b m)"
    assume "\<not>[:c:] dvd b"
    hence A: "\<exists>i. \<not>c dvd coeff b i" by (subst (asm) const_poly_dvd_iff) blast
    have B: "\<And>i. \<not>c dvd coeff b i \<Longrightarrow> i \<le> degree b"
      by (auto intro: le_degree)
    have coeff_m: "\<not>c dvd coeff b m" unfolding m_def by (rule GreatestI_ex_nat[OF A B])
    have "i \<le> m" if "\<not>c dvd coeff b i" for i
      unfolding m_def by (metis (mono_tags, lifting) B Greatest_le_nat that)
    hence dvd_b: "c dvd coeff b i" if "i > m" for i using that by force

    have "c dvd coeff a i" for i
    proof (induction i rule: nat_descend_induct[of "degree a"])
      case (base i)
      thus ?case by (simp add: coeff_eq_0)
    next
      case (descend i)
      let ?A = "{..i+m} - {i}"
      have "c dvd coeff (a * b) (i + m)" by (rule dvd)
      also have "coeff (a * b) (i + m) = (\<Sum>k\<le>i + m. coeff a k * coeff b (i + m - k))"
        by (simp add: coeff_mult)
      also have "{..i+m} = insert i ?A" by auto
      also have "(\<Sum>k\<in>\<dots>. coeff a k * coeff b (i + m - k)) =
                   coeff a i * coeff b m + (\<Sum>k\<in>?A. coeff a k * coeff b (i + m - k))"
        (is "_ = _ + ?S")
        by (subst sum.insert) simp_all
      finally have eq: "c dvd coeff a i * coeff b m + ?S" .
      moreover have "c dvd ?S"
      proof (rule dvd_sum)
        fix k assume k: "k \<in> {..i+m} - {i}"
        show "c dvd coeff a k * coeff b (i + m - k)"
        proof (cases "k < i")
          case False
          with k have "c dvd coeff a k" by (intro descend.IH) simp
          thus ?thesis by simp
        next
          case True
          hence "c dvd coeff b (i + m - k)" by (intro dvd_b) simp
          thus ?thesis by simp
        qed
      qed
      ultimately have "c dvd coeff a i * coeff b m"
        by (simp add: dvd_add_left_iff)
      with assms coeff_m show "c dvd coeff a i"
        by (simp add: prime_elem_dvd_mult_iff)
    qed
    hence "[:c:] dvd a" by (subst const_poly_dvd_iff) blast
  }
  then show "[:c:] dvd a \<or> [:c:] dvd b" by blast
next
  from assms show "[:c:] \<noteq> 0" and "\<not> [:c:] dvd 1"
    by (simp_all add: prime_elem_def is_unit_const_poly_iff)
qed

lemma prime_elem_const_poly_iff:
  fixes c :: "'a :: semidom"
  shows   "prime_elem [:c:] \<longleftrightarrow> prime_elem c"
proof
  assume A: "prime_elem [:c:]"
  show "prime_elem c"
  proof (rule prime_elemI)
    fix a b assume "c dvd a * b"
    hence "[:c:] dvd [:a:] * [:b:]" by (simp add: mult_ac)
    from A and this have "[:c:] dvd [:a:] \<or> [:c:] dvd [:b:]" by (rule prime_elem_dvd_multD)
    thus "c dvd a \<or> c dvd b" by simp
  qed (insert A, auto simp: prime_elem_def is_unit_poly_iff)
qed (auto intro: lift_prime_elem_poly)


subsection \<open>Content and primitive part of a polynomial\<close>

definition content :: "'a::semiring_gcd poly \<Rightarrow> 'a"
  where "content p = gcd_list (coeffs p)"

lemma content_eq_fold_coeffs [code]: "content p = fold_coeffs gcd p 0"
  by (simp add: content_def Gcd_fin.set_eq_fold fold_coeffs_def foldr_fold fun_eq_iff ac_simps)

lemma content_0 [simp]: "content 0 = 0"
  by (simp add: content_def)

lemma content_1 [simp]: "content 1 = 1"
  by (simp add: content_def)

lemma content_const [simp]: "content [:c:] = normalize c"
  by (simp add: content_def cCons_def)

lemma const_poly_dvd_iff_dvd_content: "[:c:] dvd p \<longleftrightarrow> c dvd content p"
  for c :: "'a::semiring_gcd"
proof (cases "p = 0")
  case True
  then show ?thesis by simp
next
  case False
  have "[:c:] dvd p \<longleftrightarrow> (\<forall>n. c dvd coeff p n)"
    by (rule const_poly_dvd_iff)
  also have "\<dots> \<longleftrightarrow> (\<forall>a\<in>set (coeffs p). c dvd a)"
  proof safe
    fix n :: nat
    assume "\<forall>a\<in>set (coeffs p). c dvd a"
    then show "c dvd coeff p n"
      by (cases "n \<le> degree p") (auto simp: coeff_eq_0 coeffs_def split: if_splits)
  qed (auto simp: coeffs_def simp del: upt_Suc split: if_splits)
  also have "\<dots> \<longleftrightarrow> c dvd content p"
    by (simp add: content_def dvd_Gcd_fin_iff dvd_mult_unit_iff)
  finally show ?thesis .
qed

lemma content_dvd [simp]: "[:content p:] dvd p"
  by (subst const_poly_dvd_iff_dvd_content) simp_all

lemma content_dvd_coeff [simp]: "content p dvd coeff p n"
proof (cases "p = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  then show ?thesis
    by (cases "n \<le> degree p")
      (auto simp add: content_def not_le coeff_eq_0 coeff_in_coeffs intro: Gcd_fin_dvd)
qed

lemma content_dvd_coeffs: "c \<in> set (coeffs p) \<Longrightarrow> content p dvd c"
  by (simp add: content_def Gcd_fin_dvd)

lemma normalize_content [simp]: "normalize (content p) = content p"
  by (simp add: content_def)

lemma is_unit_content_iff [simp]: "is_unit (content p) \<longleftrightarrow> content p = 1"
proof
  assume "is_unit (content p)"
  then have "normalize (content p) = 1" by (simp add: is_unit_normalize del: normalize_content)
  then show "content p = 1" by simp
qed auto

lemma content_smult [simp]:
  fixes c :: "'a :: {normalization_semidom_multiplicative, semiring_gcd}"
  shows "content (smult c p) = normalize c * content p"
  by (simp add: content_def coeffs_smult Gcd_fin_mult normalize_mult)

lemma content_eq_zero_iff [simp]: "content p = 0 \<longleftrightarrow> p = 0"
  by (auto simp: content_def simp: poly_eq_iff coeffs_def)

definition primitive_part :: "'a :: semiring_gcd poly \<Rightarrow> 'a poly"
  where "primitive_part p = map_poly (\<lambda>x. x div content p) p"

lemma primitive_part_0 [simp]: "primitive_part 0 = 0"
  by (simp add: primitive_part_def)

lemma content_times_primitive_part [simp]: "smult (content p) (primitive_part p) = p"
  for p :: "'a :: semiring_gcd poly"
proof (cases "p = 0")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis
  unfolding primitive_part_def
  by (auto simp: smult_conv_map_poly map_poly_map_poly o_def content_dvd_coeffs
      intro: map_poly_idI)
qed

lemma primitive_part_eq_0_iff [simp]: "primitive_part p = 0 \<longleftrightarrow> p = 0"
proof (cases "p = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have "primitive_part p = map_poly (\<lambda>x. x div content p) p"
    by (simp add:  primitive_part_def)
  also from False have "\<dots> = 0 \<longleftrightarrow> p = 0"
    by (intro map_poly_eq_0_iff) (auto simp: dvd_div_eq_0_iff content_dvd_coeffs)
  finally show ?thesis
    using False by simp
qed

lemma content_primitive_part [simp]:
  fixes p :: "'a :: {normalization_semidom_multiplicative, semiring_gcd} poly"
  assumes "p \<noteq> 0"
  shows "content (primitive_part p) = 1"
proof -
  have "p = smult (content p) (primitive_part p)"
    by simp
  also have "content \<dots> = content (primitive_part p) * content p"
    by (simp del: content_times_primitive_part add: ac_simps)
  finally have "1 * content p = content (primitive_part p) * content p"
    by simp
  then have "1 * content p div content p = content (primitive_part p) * content p div content p"
    by simp
  with assms show ?thesis
    by simp
qed

lemma content_decompose:
  obtains p' :: "'a :: {normalization_semidom_multiplicative, semiring_gcd} poly"
  where "p = smult (content p) p'" "content p' = 1"
proof (cases "p = 0")
  case True
  then have "p = smult (content p) 1" "content 1 = 1"
    by simp_all
  then show ?thesis ..
next
  case False
  then have "p = smult (content p) (primitive_part p)" "content (primitive_part p) = 1"
    by simp_all
  then show ?thesis ..
qed

lemma content_dvd_contentI [intro]: "p dvd q \<Longrightarrow> content p dvd content q"
  using const_poly_dvd_iff_dvd_content content_dvd dvd_trans by blast

lemma primitive_part_const_poly [simp]: "primitive_part [:x:] = [:unit_factor x:]"
  by (simp add: primitive_part_def map_poly_pCons)

lemma primitive_part_prim: "content p = 1 \<Longrightarrow> primitive_part p = p"
  by (auto simp: primitive_part_def)

lemma degree_primitive_part [simp]: "degree (primitive_part p) = degree p"
proof (cases "p = 0")
  case True
  then show ?thesis by simp
next
  case False
  have "p = smult (content p) (primitive_part p)"
    by simp
  also from False have "degree \<dots> = degree (primitive_part p)"
    by (subst degree_smult_eq) simp_all
  finally show ?thesis ..
qed

lemma smult_content_normalize_primitive_part [simp]:
  fixes p :: "'a :: {normalization_semidom_multiplicative, semiring_gcd, idom_divide} poly"
  shows "smult (content p) (normalize (primitive_part p)) = normalize p"
proof -
  have "smult (content p) (normalize (primitive_part p)) =
      normalize ([:content p:] * primitive_part p)"
    by (subst normalize_mult) (simp_all add: normalize_const_poly)
  also have "[:content p:] * primitive_part p = p" by simp
  finally show ?thesis .
qed

context
begin

private

lemma content_1_mult:
  fixes f g :: "'a :: {semiring_gcd, factorial_semiring} poly"
  assumes "content f = 1" "content g = 1"
  shows   "content (f * g) = 1"
proof (cases "f * g = 0")
  case False
  from assms have "f \<noteq> 0" "g \<noteq> 0" by auto

  hence "f * g \<noteq> 0" by auto
  {
    assume "\<not>is_unit (content (f * g))"
    with False have "\<exists>p. p dvd content (f * g) \<and> prime p"
      by (intro prime_divisor_exists) simp_all
    then obtain p where "p dvd content (f * g)" "prime p" by blast
    from \<open>p dvd content (f * g)\<close> have "[:p:] dvd f * g"
      by (simp add: const_poly_dvd_iff_dvd_content)
    moreover from \<open>prime p\<close> have "prime_elem [:p:]" by (simp add: lift_prime_elem_poly)
    ultimately have "[:p:] dvd f \<or> [:p:] dvd g"
      by (simp add: prime_elem_dvd_mult_iff)
    with assms have "is_unit p" by (simp add: const_poly_dvd_iff_dvd_content)
    with \<open>prime p\<close> have False by simp
  }
  hence "is_unit (content (f * g))" by blast
  hence "normalize (content (f * g)) = 1" by (simp add: is_unit_normalize del: normalize_content)
  thus ?thesis by simp
qed (insert assms, auto)

lemma content_mult:
  fixes p q :: "'a :: {factorial_semiring, semiring_gcd, normalization_semidom_multiplicative} poly"
  shows "content (p * q) = content p * content q"
proof (cases "p * q = 0")
  case False
  then have "p \<noteq> 0" and "q \<noteq> 0"
    by simp_all
  then have *: "content (primitive_part p * primitive_part q) = 1"
    by (auto intro: content_1_mult)
  have "p * q = smult (content p) (primitive_part p) * smult (content q) (primitive_part q)"
    by simp
  also have "\<dots> = smult (content p * content q) (primitive_part p * primitive_part q)"
    by (metis mult.commute mult_smult_right smult_smult)
  with * show ?thesis
  by (simp add: normalize_mult)
next
  case True
  then show ?thesis
    by auto
qed

end

lemma primitive_part_mult:
  fixes p q :: "'a :: {factorial_semiring, semiring_Gcd, ring_gcd, idom_divide,
                       normalization_semidom_multiplicative} poly"
  shows "primitive_part (p * q) = primitive_part p * primitive_part q"
proof -
  have "primitive_part (p * q) = p * q div [:content (p * q):]"
    by (simp add: primitive_part_def div_const_poly_conv_map_poly)
  also have "\<dots> = (p div [:content p:]) * (q div [:content q:])"
    by (subst div_mult_div_if_dvd) (simp_all add: content_mult mult_ac)
  also have "\<dots> = primitive_part p * primitive_part q"
    by (simp add: primitive_part_def div_const_poly_conv_map_poly)
  finally show ?thesis .
qed

lemma primitive_part_smult:
  fixes p :: "'a :: {factorial_semiring, semiring_Gcd, ring_gcd, idom_divide,
                     normalization_semidom_multiplicative} poly"
  shows "primitive_part (smult a p) = smult (unit_factor a) (primitive_part p)"
proof -
  have "smult a p = [:a:] * p" by simp
  also have "primitive_part \<dots> = smult (unit_factor a) (primitive_part p)"
    by (subst primitive_part_mult) simp_all
  finally show ?thesis .
qed

lemma primitive_part_dvd_primitive_partI [intro]:
  fixes p q :: "'a :: {factorial_semiring, semiring_Gcd, ring_gcd, idom_divide,
                       normalization_semidom_multiplicative} poly"
  shows "p dvd q \<Longrightarrow> primitive_part p dvd primitive_part q"
  by (auto elim!: dvdE simp: primitive_part_mult)

lemma content_prod_mset:
  fixes A :: "'a :: {factorial_semiring, semiring_Gcd, normalization_semidom_multiplicative}
      poly multiset"
  shows "content (prod_mset A) = prod_mset (image_mset content A)"
  by (induction A) (simp_all add: content_mult mult_ac)

lemma content_prod_eq_1_iff:
  fixes p q :: "'a :: {factorial_semiring, semiring_Gcd, normalization_semidom_multiplicative} poly"
  shows "content (p * q) = 1 \<longleftrightarrow> content p = 1 \<and> content q = 1"
proof safe
  assume A: "content (p * q) = 1"
  {
    fix p q :: "'a poly" assume "content p * content q = 1"
    hence "1 = content p * content q" by simp
    hence "content p dvd 1" by (rule dvdI)
    hence "content p = 1" by simp
  } note B = this
  from A B[of p q] B [of q p] show "content p = 1" "content q = 1"
    by (simp_all add: content_mult mult_ac)
qed (auto simp: content_mult)


no_notation cCons (infixr "##" 65)

end
