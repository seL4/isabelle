(*  Title:      HOL/Library/Polynomial.thy
    Author:     Brian Huffman
    Author:     Clemens Ballarin
    Author:     Amine Chaieb
    Author:     Florian Haftmann
*)

section \<open>Polynomials as type over a ring structure\<close>

theory Polynomial
imports Main "~~/src/HOL/Deriv" "~~/src/HOL/Library/More_List"
  "~~/src/HOL/Library/Infinite_Set"
begin

subsection \<open>Auxiliary: operations for lists (later) representing coefficients\<close>

definition cCons :: "'a::zero \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixr "##" 65)
where
  "x ## xs = (if xs = [] \<and> x = 0 then [] else x # xs)"

lemma cCons_0_Nil_eq [simp]:
  "0 ## [] = []"
  by (simp add: cCons_def)

lemma cCons_Cons_eq [simp]:
  "x ## y # ys = x # y # ys"
  by (simp add: cCons_def)

lemma cCons_append_Cons_eq [simp]:
  "x ## xs @ y # ys = x # xs @ y # ys"
  by (simp add: cCons_def)

lemma cCons_not_0_eq [simp]:
  "x \<noteq> 0 \<Longrightarrow> x ## xs = x # xs"
  by (simp add: cCons_def)

lemma strip_while_not_0_Cons_eq [simp]:
  "strip_while (\<lambda>x. x = 0) (x # xs) = x ## strip_while (\<lambda>x. x = 0) xs"
proof (cases "x = 0")
  case False then show ?thesis by simp
next
  case True show ?thesis
  proof (induct xs rule: rev_induct)
    case Nil with True show ?case by simp
  next
    case (snoc y ys) then show ?case
      by (cases "y = 0") (simp_all add: append_Cons [symmetric] del: append_Cons)
  qed
qed

lemma tl_cCons [simp]:
  "tl (x ## xs) = xs"
  by (simp add: cCons_def)

subsection \<open>Definition of type \<open>poly\<close>\<close>

typedef (overloaded) 'a poly = "{f :: nat \<Rightarrow> 'a::zero. \<forall>\<^sub>\<infinity> n. f n = 0}"
  morphisms coeff Abs_poly by (auto intro!: ALL_MOST)

setup_lifting type_definition_poly

lemma poly_eq_iff: "p = q \<longleftrightarrow> (\<forall>n. coeff p n = coeff q n)"
  by (simp add: coeff_inject [symmetric] fun_eq_iff)

lemma poly_eqI: "(\<And>n. coeff p n = coeff q n) \<Longrightarrow> p = q"
  by (simp add: poly_eq_iff)

lemma MOST_coeff_eq_0: "\<forall>\<^sub>\<infinity> n. coeff p n = 0"
  using coeff [of p] by simp


subsection \<open>Degree of a polynomial\<close>

definition degree :: "'a::zero poly \<Rightarrow> nat"
where
  "degree p = (LEAST n. \<forall>i>n. coeff p i = 0)"

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
  is "\<lambda>_. 0" by (rule MOST_I) simp

instance ..

end

lemma coeff_0 [simp]:
  "coeff 0 n = 0"
  by transfer rule

lemma degree_0 [simp]:
  "degree 0 = 0"
  by (rule order_antisym [OF degree_le le0]) simp

lemma leading_coeff_neq_0:
  assumes "p \<noteq> 0"
  shows "coeff p (degree p) \<noteq> 0"
proof (cases "degree p")
  case 0
  from \<open>p \<noteq> 0\<close> have "\<exists>n. coeff p n \<noteq> 0"
    by (simp add: poly_eq_iff)
  then obtain n where "coeff p n \<noteq> 0" ..
  hence "n \<le> degree p" by (rule le_degree)
  with \<open>coeff p n \<noteq> 0\<close> and \<open>degree p = 0\<close>
  show "coeff p (degree p) \<noteq> 0" by simp
next
  case (Suc n)
  from \<open>degree p = Suc n\<close> have "n < degree p" by simp
  hence "\<exists>i>n. coeff p i \<noteq> 0" by (rule less_degree_imp)
  then obtain i where "n < i" and "coeff p i \<noteq> 0" by fast
  from \<open>degree p = Suc n\<close> and \<open>n < i\<close> have "degree p \<le> i" by simp
  also from \<open>coeff p i \<noteq> 0\<close> have "i \<le> degree p" by (rule le_degree)
  finally have "degree p = i" .
  with \<open>coeff p i \<noteq> 0\<close> show "coeff p (degree p) \<noteq> 0" by simp
qed

lemma leading_coeff_0_iff [simp]:
  "coeff p (degree p) = 0 \<longleftrightarrow> p = 0"
  by (cases "p = 0", simp, simp add: leading_coeff_neq_0)


subsection \<open>List-style constructor for polynomials\<close>

lift_definition pCons :: "'a::zero \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>a p. case_nat a (coeff p)"
  by (rule MOST_SucD) (simp add: MOST_coeff_eq_0)

lemmas coeff_pCons = pCons.rep_eq

lemma coeff_pCons_0 [simp]:
  "coeff (pCons a p) 0 = a"
  by transfer simp

lemma coeff_pCons_Suc [simp]:
  "coeff (pCons a p) (Suc n) = coeff p n"
  by (simp add: coeff_pCons)

lemma degree_pCons_le:
  "degree (pCons a p) \<le> Suc (degree p)"
  by (rule degree_le) (simp add: coeff_eq_0 coeff_pCons split: nat.split)

lemma degree_pCons_eq:
  "p \<noteq> 0 \<Longrightarrow> degree (pCons a p) = Suc (degree p)"
  apply (rule order_antisym [OF degree_pCons_le])
  apply (rule le_degree, simp)
  done

lemma degree_pCons_0:
  "degree (pCons a 0) = 0"
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

lemma pCons_0_0 [simp]:
  "pCons 0 0 = 0"
  by (rule poly_eqI) (simp add: coeff_pCons split: nat.split)

lemma pCons_eq_iff [simp]:
  "pCons a p = pCons b q \<longleftrightarrow> a = b \<and> p = q"
proof safe
  assume "pCons a p = pCons b q"
  then have "coeff (pCons a p) 0 = coeff (pCons b q) 0" by simp
  then show "a = b" by simp
next
  assume "pCons a p = pCons b q"
  then have "\<forall>n. coeff (pCons a p) (Suc n) =
                 coeff (pCons b q) (Suc n)" by simp
  then show "p = q" by (simp add: poly_eq_iff)
qed

lemma pCons_eq_0_iff [simp]:
  "pCons a p = 0 \<longleftrightarrow> a = 0 \<and> p = 0"
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
    then have "degree q < degree p"
      using \<open>p = pCons a q\<close> by simp
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
  then show ?case
    using \<open>p = pCons a q\<close> by simp
qed

lemma degree_eq_zeroE:
  fixes p :: "'a::zero poly"
  assumes "degree p = 0"
  obtains a where "p = pCons a 0"
proof -
  obtain a q where p: "p = pCons a q" by (cases p)
  with assms have "q = 0" by (cases "q = 0") simp_all
  with p have "p = pCons a 0" by simp
  with that show thesis .
qed


subsection \<open>Quickcheck generator for polynomials\<close>

quickcheck_generator poly constructors: "0 :: _ poly", pCons


subsection \<open>List-style syntax for polynomials\<close>

syntax
  "_poly" :: "args \<Rightarrow> 'a poly"  ("[:(_):]")

translations
  "[:x, xs:]" == "CONST pCons x [:xs:]"
  "[:x:]" == "CONST pCons x 0"
  "[:x:]" <= "CONST pCons x (_constrain 0 t)"


subsection \<open>Representation of polynomials by lists of coefficients\<close>

primrec Poly :: "'a::zero list \<Rightarrow> 'a poly"
where
  [code_post]: "Poly [] = 0"
| [code_post]: "Poly (a # as) = pCons a (Poly as)"

lemma Poly_replicate_0 [simp]:
  "Poly (replicate n 0) = 0"
  by (induct n) simp_all

lemma Poly_eq_0:
  "Poly as = 0 \<longleftrightarrow> (\<exists>n. as = replicate n 0)"
  by (induct as) (auto simp add: Cons_replicate_eq)

lemma Poly_append_replicate_zero [simp]:
  "Poly (as @ replicate n 0) = Poly as"
  by (induct as) simp_all

lemma Poly_snoc_zero [simp]:
  "Poly (as @ [0]) = Poly as"
  using Poly_append_replicate_zero [of as 1] by simp

lemma Poly_cCons_eq_pCons_Poly [simp]:
  "Poly (a ## p) = pCons a (Poly p)"
  by (simp add: cCons_def)

lemma Poly_on_rev_starting_with_0 [simp]:
  assumes "hd as = 0"
  shows "Poly (rev (tl as)) = Poly (rev as)"
  using assms by (cases as) simp_all

lemma degree_Poly: "degree (Poly xs) \<le> length xs"
  by (induction xs) simp_all

lemma coeff_Poly_eq [simp]:
  "coeff (Poly xs) = nth_default 0 xs"
  by (induct xs) (simp_all add: fun_eq_iff coeff_pCons split: nat.splits)

definition coeffs :: "'a poly \<Rightarrow> 'a::zero list"
where
  "coeffs p = (if p = 0 then [] else map (\<lambda>i. coeff p i) [0 ..< Suc (degree p)])"

lemma coeffs_eq_Nil [simp]:
  "coeffs p = [] \<longleftrightarrow> p = 0"
  by (simp add: coeffs_def)

lemma not_0_coeffs_not_Nil:
  "p \<noteq> 0 \<Longrightarrow> coeffs p \<noteq> []"
  by simp

lemma coeffs_0_eq_Nil [simp]:
  "coeffs 0 = []"
  by simp

lemma coeffs_pCons_eq_cCons [simp]:
  "coeffs (pCons a p) = a ## coeffs p"
proof -
  { fix ms :: "nat list" and f :: "nat \<Rightarrow> 'a" and x :: "'a"
    assume "\<forall>m\<in>set ms. m > 0"
    then have "map (case_nat x f) ms = map f (map (\<lambda>n. n - 1) ms)"
      by (induct ms) (auto split: nat.split)
  }
  note * = this
  show ?thesis
    by (simp add: coeffs_def * upt_conv_Cons coeff_pCons map_decr_upt del: upt_Suc)
qed

lemma length_coeffs: "p \<noteq> 0 \<Longrightarrow> length (coeffs p) = degree p + 1"
  by (simp add: coeffs_def)
  
lemma coeffs_nth:
  assumes "p \<noteq> 0" "n \<le> degree p"
  shows   "coeffs p ! n = coeff p n"
  using assms unfolding coeffs_def by (auto simp del: upt_Suc)

lemma not_0_cCons_eq [simp]:
  "p \<noteq> 0 \<Longrightarrow> a ## coeffs p = a # coeffs p"
  by (simp add: cCons_def)

lemma Poly_coeffs [simp, code abstype]:
  "Poly (coeffs p) = p"
  by (induct p) auto

lemma coeffs_Poly [simp]:
  "coeffs (Poly as) = strip_while (HOL.eq 0) as"
proof (induct as)
  case Nil then show ?case by simp
next
  case (Cons a as)
  have "(\<forall>n. as \<noteq> replicate n 0) \<longleftrightarrow> (\<exists>a\<in>set as. a \<noteq> 0)"
    using replicate_length_same [of as 0] by (auto dest: sym [of _ as])
  with Cons show ?case by auto
qed

lemma last_coeffs_not_0:
  "p \<noteq> 0 \<Longrightarrow> last (coeffs p) \<noteq> 0"
  by (induct p) (auto simp add: cCons_def)

lemma strip_while_coeffs [simp]:
  "strip_while (HOL.eq 0) (coeffs p) = coeffs p"
  by (cases "p = 0") (auto dest: last_coeffs_not_0 intro: strip_while_not_last)

lemma coeffs_eq_iff:
  "p = q \<longleftrightarrow> coeffs p = coeffs q" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P then show ?Q by simp
next
  assume ?Q
  then have "Poly (coeffs p) = Poly (coeffs q)" by simp
  then show ?P by simp
qed

lemma nth_default_coeffs_eq:
  "nth_default 0 (coeffs p) = coeff p"
  by (simp add: fun_eq_iff coeff_Poly_eq [symmetric])

lemma [code]:
  "coeff p = nth_default 0 (coeffs p)"
  by (simp add: nth_default_coeffs_eq)

lemma coeffs_eqI:
  assumes coeff: "\<And>n. coeff p n = nth_default 0 xs n"
  assumes zero: "xs \<noteq> [] \<Longrightarrow> last xs \<noteq> 0"
  shows "coeffs p = xs"
proof -
  from coeff have "p = Poly xs" by (simp add: poly_eq_iff)
  with zero show ?thesis by simp (cases xs, simp_all)
qed

lemma degree_eq_length_coeffs [code]:
  "degree p = length (coeffs p) - 1"
  by (simp add: coeffs_def)

lemma length_coeffs_degree:
  "p \<noteq> 0 \<Longrightarrow> length (coeffs p) = Suc (degree p)"
  by (induct p) (auto simp add: cCons_def)

lemma [code abstract]:
  "coeffs 0 = []"
  by (fact coeffs_0_eq_Nil)

lemma [code abstract]:
  "coeffs (pCons a p) = a ## coeffs p"
  by (fact coeffs_pCons_eq_cCons)

instantiation poly :: ("{zero, equal}") equal
begin

definition
  [code]: "HOL.equal (p::'a poly) q \<longleftrightarrow> HOL.equal (coeffs p) (coeffs q)"

instance
  by standard (simp add: equal equal_poly_def coeffs_eq_iff)

end

lemma [code nbe]: "HOL.equal (p :: _ poly) p \<longleftrightarrow> True"
  by (fact equal_refl)

definition is_zero :: "'a::zero poly \<Rightarrow> bool"
where
  [code]: "is_zero p \<longleftrightarrow> List.null (coeffs p)"

lemma is_zero_null [code_abbrev]:
  "is_zero p \<longleftrightarrow> p = 0"
  by (simp add: is_zero_def null_def)

subsubsection \<open>Reconstructing the polynomial from the list\<close>
  -- \<open>contributed by Sebastiaan J.C. Joosten and René Thiemann\<close>

definition poly_of_list :: "'a::comm_monoid_add list \<Rightarrow> 'a poly"
where
  [simp]: "poly_of_list = Poly"

lemma poly_of_list_impl [code abstract]:
  "coeffs (poly_of_list as) = strip_while (HOL.eq 0) as"
  by simp


subsection \<open>Fold combinator for polynomials\<close>

definition fold_coeffs :: "('a::zero \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a poly \<Rightarrow> 'b \<Rightarrow> 'b"
where
  "fold_coeffs f p = foldr f (coeffs p)"

lemma fold_coeffs_0_eq [simp]:
  "fold_coeffs f 0 = id"
  by (simp add: fold_coeffs_def)

lemma fold_coeffs_pCons_eq [simp]:
  "f 0 = id \<Longrightarrow> fold_coeffs f (pCons a p) = f a \<circ> fold_coeffs f p"
  by (simp add: fold_coeffs_def cCons_def fun_eq_iff)

lemma fold_coeffs_pCons_0_0_eq [simp]:
  "fold_coeffs f (pCons 0 0) = id"
  by (simp add: fold_coeffs_def)

lemma fold_coeffs_pCons_coeff_not_0_eq [simp]:
  "a \<noteq> 0 \<Longrightarrow> fold_coeffs f (pCons a p) = f a \<circ> fold_coeffs f p"
  by (simp add: fold_coeffs_def)

lemma fold_coeffs_pCons_not_0_0_eq [simp]:
  "p \<noteq> 0 \<Longrightarrow> fold_coeffs f (pCons a p) = f a \<circ> fold_coeffs f p"
  by (simp add: fold_coeffs_def)

subsection \<open>Canonical morphism on polynomials -- evaluation\<close>

definition poly :: "'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "poly p = fold_coeffs (\<lambda>a f x. a + x * f x) p (\<lambda>x. 0)" \<comment> \<open>The Horner Schema\<close>

lemma poly_0 [simp]:
  "poly 0 x = 0"
  by (simp add: poly_def)
  
lemma poly_pCons [simp]:
  "poly (pCons a p) x = a + x * poly p x"
  by (cases "p = 0 \<and> a = 0") (auto simp add: poly_def)

lemma poly_altdef: 
  "poly p (x :: 'a :: {comm_semiring_0, semiring_1}) = (\<Sum>i\<le>degree p. coeff p i * x ^ i)"
proof (induction p rule: pCons_induct)
  case (pCons a p)
    show ?case
    proof (cases "p = 0")
      case False
      let ?p' = "pCons a p"
      note poly_pCons[of a p x]
      also note pCons.IH
      also have "a + x * (\<Sum>i\<le>degree p. coeff p i * x ^ i) =
                 coeff ?p' 0 * x^0 + (\<Sum>i\<le>degree p. coeff ?p' (Suc i) * x^Suc i)"
          by (simp add: field_simps setsum_right_distrib coeff_pCons)
      also note setsum_atMost_Suc_shift[symmetric]
      also note degree_pCons_eq[OF \<open>p \<noteq> 0\<close>, of a, symmetric]
      finally show ?thesis .
   qed simp
qed simp

lemma poly_0_coeff_0: "poly p 0 = coeff p 0"
  by (cases p) (auto simp: poly_altdef)


subsection \<open>Monomials\<close>

lift_definition monom :: "'a \<Rightarrow> nat \<Rightarrow> 'a::zero poly"
  is "\<lambda>a m n. if m = n then a else 0"
  by (simp add: MOST_iff_cofinite)

lemma coeff_monom [simp]:
  "coeff (monom a m) n = (if m = n then a else 0)"
  by transfer rule

lemma monom_0:
  "monom a 0 = pCons a 0"
  by (rule poly_eqI) (simp add: coeff_pCons split: nat.split)

lemma monom_Suc:
  "monom a (Suc n) = pCons 0 (monom a n)"
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
  apply (rule order_antisym [OF degree_monom_le])
  apply (rule le_degree, simp)
  done

lemma coeffs_monom [code abstract]:
  "coeffs (monom a n) = (if a = 0 then [] else replicate n 0 @ [a])"
  by (induct n) (simp_all add: monom_0 monom_Suc)

lemma fold_coeffs_monom [simp]:
  "a \<noteq> 0 \<Longrightarrow> fold_coeffs f (monom a n) = f 0 ^^ n \<circ> f a"
  by (simp add: fold_coeffs_def coeffs_monom fun_eq_iff)

lemma poly_monom:
  fixes a x :: "'a::{comm_semiring_1}"
  shows "poly (monom a n) x = a * x ^ n"
  by (cases "a = 0", simp_all)
    (induct n, simp_all add: mult.left_commute poly_def)

    
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

lemma add_pCons [simp]:
  "pCons a p + pCons b q = pCons (a + b) (p + q)"
  by (rule poly_eqI, simp add: coeff_pCons split: nat.split)

lemma minus_pCons [simp]:
  "- pCons a p = pCons (- a) (- p)"
  by (rule poly_eqI, simp add: coeff_pCons split: nat.split)

lemma diff_pCons [simp]:
  "pCons a p - pCons b q = pCons (a - b) (p - q)"
  by (rule poly_eqI, simp add: coeff_pCons split: nat.split)

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
  by (simp add: add.commute)

lemma degree_minus [simp]:
  "degree (- p) = degree p"
  unfolding degree_def by simp

lemma degree_diff_le_max:
  fixes p q :: "'a :: ab_group_add poly"
  shows "degree (p - q) \<le> max (degree p) (degree q)"
  using degree_add_le [where p=p and q="-q"]
  by simp

lemma degree_diff_le:
  fixes p q :: "'a :: ab_group_add poly"
  assumes "degree p \<le> n" and "degree q \<le> n"
  shows "degree (p - q) \<le> n"
  using assms degree_add_le [of p n "- q"] by simp

lemma degree_diff_less:
  fixes p q :: "'a :: ab_group_add poly"
  assumes "degree p < n" and "degree q < n"
  shows "degree (p - q) < n"
  using assms degree_add_less [of p n "- q"] by simp

lemma add_monom: "monom a n + monom b n = monom (a + b) n"
  by (rule poly_eqI) simp

lemma diff_monom: "monom a n - monom b n = monom (a - b) n"
  by (rule poly_eqI) simp

lemma minus_monom: "- monom a n = monom (-a) n"
  by (rule poly_eqI) simp

lemma coeff_setsum: "coeff (\<Sum>x\<in>A. p x) i = (\<Sum>x\<in>A. coeff (p x) i)"
  by (cases "finite A", induct set: finite, simp_all)

lemma monom_setsum: "monom (\<Sum>x\<in>A. a x) n = (\<Sum>x\<in>A. monom (a x) n)"
  by (rule poly_eqI) (simp add: coeff_setsum)

fun plus_coeffs :: "'a::comm_monoid_add list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "plus_coeffs xs [] = xs"
| "plus_coeffs [] ys = ys"
| "plus_coeffs (x # xs) (y # ys) = (x + y) ## plus_coeffs xs ys"

lemma coeffs_plus_eq_plus_coeffs [code abstract]:
  "coeffs (p + q) = plus_coeffs (coeffs p) (coeffs q)"
proof -
  { fix xs ys :: "'a list" and n
    have "nth_default 0 (plus_coeffs xs ys) n = nth_default 0 xs n + nth_default 0 ys n"
    proof (induct xs ys arbitrary: n rule: plus_coeffs.induct)
      case (3 x xs y ys n)
      then show ?case by (cases n) (auto simp add: cCons_def)
    qed simp_all }
  note * = this
  { fix xs ys :: "'a list"
    assume "xs \<noteq> [] \<Longrightarrow> last xs \<noteq> 0" and "ys \<noteq> [] \<Longrightarrow> last ys \<noteq> 0"
    moreover assume "plus_coeffs xs ys \<noteq> []"
    ultimately have "last (plus_coeffs xs ys) \<noteq> 0"
    proof (induct xs ys rule: plus_coeffs.induct)
      case (3 x xs y ys) then show ?case by (auto simp add: cCons_def) metis
    qed simp_all }
  note ** = this
  show ?thesis
    apply (rule coeffs_eqI)
    apply (simp add: * nth_default_coeffs_eq)
    apply (rule **)
    apply (auto dest: last_coeffs_not_0)
    done
qed

lemma coeffs_uminus [code abstract]:
  "coeffs (- p) = map (\<lambda>a. - a) (coeffs p)"
  by (rule coeffs_eqI)
    (simp_all add: not_0_coeffs_not_Nil last_map last_coeffs_not_0 nth_default_map_eq nth_default_coeffs_eq)

lemma [code]:
  fixes p q :: "'a::ab_group_add poly"
  shows "p - q = p + - q"
  by (fact diff_conv_add_uminus)

lemma poly_add [simp]: "poly (p + q) x = poly p x + poly q x"
  apply (induct p arbitrary: q, simp)
  apply (case_tac q, simp, simp add: algebra_simps)
  done

lemma poly_minus [simp]:
  fixes x :: "'a::comm_ring"
  shows "poly (- p) x = - poly p x"
  by (induct p) simp_all

lemma poly_diff [simp]:
  fixes x :: "'a::comm_ring"
  shows "poly (p - q) x = poly p x - poly q x"
  using poly_add [of p "- q" x] by simp

lemma poly_setsum: "poly (\<Sum>k\<in>A. p k) x = (\<Sum>k\<in>A. poly (p k) x)"
  by (induct A rule: infinite_finite_induct) simp_all

lemma degree_setsum_le: "finite S \<Longrightarrow> (\<And> p . p \<in> S \<Longrightarrow> degree (f p) \<le> n)
  \<Longrightarrow> degree (setsum f S) \<le> n"
proof (induct S rule: finite_induct)
  case (insert p S)
  hence "degree (setsum f S) \<le> n" "degree (f p) \<le> n" by auto
  thus ?case unfolding setsum.insert[OF insert(1-2)] by (metis degree_add_le)
qed simp

lemma poly_as_sum_of_monoms': 
  assumes n: "degree p \<le> n" 
  shows "(\<Sum>i\<le>n. monom (coeff p i) i) = p"
proof -
  have eq: "\<And>i. {..n} \<inter> {i} = (if i \<le> n then {i} else {})"
    by auto
  show ?thesis
    using n by (simp add: poly_eq_iff coeff_setsum coeff_eq_0 setsum.If_cases eq 
                  if_distrib[where f="\<lambda>x. x * a" for a])
qed

lemma poly_as_sum_of_monoms: "(\<Sum>i\<le>degree p. monom (coeff p i) i) = p"
  by (intro poly_as_sum_of_monoms' order_refl)

lemma Poly_snoc: "Poly (xs @ [x]) = Poly xs + monom x (length xs)"
  by (induction xs) (simp_all add: monom_0 monom_Suc)


subsection \<open>Multiplication by a constant, polynomial multiplication and the unit polynomial\<close>

lift_definition smult :: "'a::comm_semiring_0 \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  is "\<lambda>a p n. a * coeff p n"
proof -
  fix a :: 'a and p :: "'a poly" show "\<forall>\<^sub>\<infinity> i. a * coeff p i = 0"
    using MOST_coeff_eq_0[of p] by eventually_elim simp
qed

lemma coeff_smult [simp]:
  "coeff (smult a p) n = a * coeff p n"
  by (simp add: smult.rep_eq)

lemma degree_smult_le: "degree (smult a p) \<le> degree p"
  by (rule degree_le, simp add: coeff_eq_0)

lemma smult_smult [simp]: "smult a (smult b p) = smult (a * b) p"
  by (rule poly_eqI, simp add: mult.assoc)

lemma smult_0_right [simp]: "smult a 0 = 0"
  by (rule poly_eqI, simp)

lemma smult_0_left [simp]: "smult 0 p = 0"
  by (rule poly_eqI, simp)

lemma smult_1_left [simp]: "smult (1::'a::comm_semiring_1) p = p"
  by (rule poly_eqI, simp)

lemma smult_add_right:
  "smult a (p + q) = smult a p + smult a q"
  by (rule poly_eqI, simp add: algebra_simps)

lemma smult_add_left:
  "smult (a + b) p = smult a p + smult b p"
  by (rule poly_eqI, simp add: algebra_simps)

lemma smult_minus_right [simp]:
  "smult (a::'a::comm_ring) (- p) = - smult a p"
  by (rule poly_eqI, simp)

lemma smult_minus_left [simp]:
  "smult (- a::'a::comm_ring) p = - smult a p"
  by (rule poly_eqI, simp)

lemma smult_diff_right:
  "smult (a::'a::comm_ring) (p - q) = smult a p - smult a q"
  by (rule poly_eqI, simp add: algebra_simps)

lemma smult_diff_left:
  "smult (a - b::'a::comm_ring) p = smult a p - smult b p"
  by (rule poly_eqI, simp add: algebra_simps)

lemmas smult_distribs =
  smult_add_left smult_add_right
  smult_diff_left smult_diff_right

lemma smult_pCons [simp]:
  "smult a (pCons b p) = pCons (a * b) (smult a p)"
  by (rule poly_eqI, simp add: coeff_pCons split: nat.split)

lemma smult_monom: "smult a (monom b n) = monom (a * b) n"
  by (induct n, simp add: monom_0, simp add: monom_Suc)

lemma degree_smult_eq [simp]:
  fixes a :: "'a::idom"
  shows "degree (smult a p) = (if a = 0 then 0 else degree p)"
  by (cases "a = 0", simp, simp add: degree_def)

lemma smult_eq_0_iff [simp]:
  fixes a :: "'a::idom"
  shows "smult a p = 0 \<longleftrightarrow> a = 0 \<or> p = 0"
  by (simp add: poly_eq_iff)

lemma coeffs_smult [code abstract]:
  fixes p :: "'a::idom poly"
  shows "coeffs (smult a p) = (if a = 0 then [] else map (Groups.times a) (coeffs p))"
  by (rule coeffs_eqI)
    (auto simp add: not_0_coeffs_not_Nil last_map last_coeffs_not_0 nth_default_map_eq nth_default_coeffs_eq)

instantiation poly :: (comm_semiring_0) comm_semiring_0
begin

definition
  "p * q = fold_coeffs (\<lambda>a p. smult a q + pCons 0 p) p 0"

lemma mult_poly_0_left: "(0::'a poly) * q = 0"
  by (simp add: times_poly_def)

lemma mult_pCons_left [simp]:
  "pCons a p * q = smult a q + pCons 0 (p * q)"
  by (cases "p = 0 \<and> a = 0") (auto simp add: times_poly_def)

lemma mult_poly_0_right: "p * (0::'a poly) = 0"
  by (induct p) (simp add: mult_poly_0_left, simp)

lemma mult_pCons_right [simp]:
  "p * pCons a q = smult a p + pCons 0 (p * q)"
  by (induct p) (simp add: mult_poly_0_left, simp add: algebra_simps)

lemmas mult_poly_0 = mult_poly_0_left mult_poly_0_right

lemma mult_smult_left [simp]:
  "smult a p * q = smult a (p * q)"
  by (induct p) (simp add: mult_poly_0, simp add: smult_add_right)

lemma mult_smult_right [simp]:
  "p * smult a q = smult a (p * q)"
  by (induct q) (simp add: mult_poly_0, simp add: smult_add_right)

lemma mult_poly_add_left:
  fixes p q r :: "'a poly"
  shows "(p + q) * r = p * r + q * r"
  by (induct r) (simp add: mult_poly_0, simp add: smult_distribs algebra_simps)

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
  by (induct m) (simp add: monom_0 smult_monom, simp add: monom_Suc)

instantiation poly :: (comm_semiring_1) comm_semiring_1
begin

definition one_poly_def: "1 = pCons 1 0"

instance
proof
  show "1 * p = p" for p :: "'a poly"
    unfolding one_poly_def by simp
  show "0 \<noteq> (1::'a poly)"
    unfolding one_poly_def by simp
qed

end

instance poly :: (comm_ring) comm_ring ..

instance poly :: (comm_ring_1) comm_ring_1 ..

lemma coeff_1 [simp]: "coeff 1 n = (if n = 0 then 1 else 0)"
  unfolding one_poly_def
  by (simp add: coeff_pCons split: nat.split)

lemma monom_eq_1 [simp]:
  "monom 1 0 = 1"
  by (simp add: monom_0 one_poly_def)
  
lemma degree_1 [simp]: "degree 1 = 0"
  unfolding one_poly_def
  by (rule degree_pCons_0)

lemma coeffs_1_eq [simp, code abstract]:
  "coeffs 1 = [1]"
  by (simp add: one_poly_def)

lemma degree_power_le:
  "degree (p ^ n) \<le> degree p * n"
  by (induct n) (auto intro: order_trans degree_mult_le)

lemma poly_smult [simp]:
  "poly (smult a p) x = a * poly p x"
  by (induct p, simp, simp add: algebra_simps)

lemma poly_mult [simp]:
  "poly (p * q) x = poly p x * poly q x"
  by (induct p, simp_all, simp add: algebra_simps)

lemma poly_1 [simp]:
  "poly 1 x = 1"
  by (simp add: one_poly_def)

lemma poly_power [simp]:
  fixes p :: "'a::{comm_semiring_1} poly"
  shows "poly (p ^ n) x = poly p x ^ n"
  by (induct n) simp_all

lemma poly_setprod: "poly (\<Prod>k\<in>A. p k) x = (\<Prod>k\<in>A. poly (p k) x)"
  by (induct A rule: infinite_finite_induct) simp_all

lemma degree_setprod_setsum_le: "finite S \<Longrightarrow> degree (setprod f S) \<le> setsum (degree o f) S"
proof (induct S rule: finite_induct)
  case (insert a S)
  show ?case unfolding setprod.insert[OF insert(1-2)] setsum.insert[OF insert(1-2)]
    by (rule le_trans[OF degree_mult_le], insert insert, auto)
qed simp

subsection \<open>Conversions from natural numbers\<close>

lemma of_nat_poly: "of_nat n = [:of_nat n :: 'a :: comm_semiring_1:]"
proof (induction n)
  case (Suc n)
  hence "of_nat (Suc n) = 1 + (of_nat n :: 'a poly)" 
    by simp
  also have "(of_nat n :: 'a poly) = [: of_nat n :]" 
    by (subst Suc) (rule refl)
  also have "1 = [:1:]" by (simp add: one_poly_def)
  finally show ?case by (subst (asm) add_pCons) simp
qed simp

lemma degree_of_nat [simp]: "degree (of_nat n) = 0"
  by (simp add: of_nat_poly)

lemma degree_numeral [simp]: "degree (numeral n) = 0"
  by (subst of_nat_numeral [symmetric], subst of_nat_poly) simp

lemma numeral_poly: "numeral n = [:numeral n:]"
  by (subst of_nat_numeral [symmetric], subst of_nat_poly) simp

subsection \<open>Lemmas about divisibility\<close>

lemma dvd_smult: "p dvd q \<Longrightarrow> p dvd smult a q"
proof -
  assume "p dvd q"
  then obtain k where "q = p * k" ..
  then have "smult a q = p * smult a k" by simp
  then show "p dvd smult a q" ..
qed

lemma dvd_smult_cancel:
  fixes a :: "'a :: field"
  shows "p dvd smult a q \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> p dvd q"
  by (drule dvd_smult [where a="inverse a"]) simp

lemma dvd_smult_iff:
  fixes a :: "'a::field"
  shows "a \<noteq> 0 \<Longrightarrow> p dvd smult a q \<longleftrightarrow> p dvd q"
  by (safe elim!: dvd_smult dvd_smult_cancel)

lemma smult_dvd_cancel:
  "smult a p dvd q \<Longrightarrow> p dvd q"
proof -
  assume "smult a p dvd q"
  then obtain k where "q = smult a p * k" ..
  then have "q = p * smult a k" by simp
  then show "p dvd q" ..
qed

lemma smult_dvd:
  fixes a :: "'a::field"
  shows "p dvd q \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> smult a p dvd q"
  by (rule smult_dvd_cancel [where a="inverse a"]) simp

lemma smult_dvd_iff:
  fixes a :: "'a::field"
  shows "smult a p dvd q \<longleftrightarrow> (if a = 0 then q = 0 else p dvd q)"
  by (auto elim: smult_dvd smult_dvd_cancel)


subsection \<open>Polynomials form an integral domain\<close>

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
    using \<open>p \<noteq> 0\<close> and \<open>q \<noteq> 0\<close> by simp
  finally have "\<exists>n. coeff (p * q) n \<noteq> 0" ..
  thus "p * q \<noteq> 0" by (simp add: poly_eq_iff)
qed

lemma degree_mult_eq:
  fixes p q :: "'a::semidom poly"
  shows "\<lbrakk>p \<noteq> 0; q \<noteq> 0\<rbrakk> \<Longrightarrow> degree (p * q) = degree p + degree q"
apply (rule order_antisym [OF degree_mult_le le_degree])
apply (simp add: coeff_mult_degree_sum)
done

lemma degree_mult_right_le:
  fixes p q :: "'a::semidom poly"
  assumes "q \<noteq> 0"
  shows "degree p \<le> degree (p * q)"
  using assms by (cases "p = 0") (simp_all add: degree_mult_eq)

lemma coeff_degree_mult:
  fixes p q :: "'a::semidom poly"
  shows "coeff (p * q) (degree (p * q)) =
    coeff q (degree q) * coeff p (degree p)"
  by (cases "p = 0 \<or> q = 0") (auto simp add: degree_mult_eq coeff_mult_degree_sum mult_ac)

lemma dvd_imp_degree_le:
  fixes p q :: "'a::semidom poly"
  shows "\<lbrakk>p dvd q; q \<noteq> 0\<rbrakk> \<Longrightarrow> degree p \<le> degree q"
  by (erule dvdE, hypsubst, subst degree_mult_eq) auto

lemma divides_degree:
  assumes pq: "p dvd (q :: 'a :: semidom poly)"
  shows "degree p \<le> degree q \<or> q = 0"
  by (metis dvd_imp_degree_le pq)

subsection \<open>Polynomials form an ordered integral domain\<close>

definition pos_poly :: "'a::linordered_idom poly \<Rightarrow> bool"
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
  apply (simp add: degree_mult_eq coeff_mult_degree_sum)
  apply auto
  done

lemma pos_poly_total: "p = 0 \<or> pos_poly p \<or> pos_poly (- p)"
by (induct p) (auto simp add: pos_poly_pCons)

lemma last_coeffs_eq_coeff_degree:
  "p \<noteq> 0 \<Longrightarrow> last (coeffs p) = coeff p (degree p)"
  by (simp add: coeffs_def)

lemma pos_poly_coeffs [code]:
  "pos_poly p \<longleftrightarrow> (let as = coeffs p in as \<noteq> [] \<and> last as > 0)" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?Q then show ?P by (auto simp add: pos_poly_def last_coeffs_eq_coeff_degree)
next
  assume ?P then have *: "0 < coeff p (degree p)" by (simp add: pos_poly_def)
  then have "p \<noteq> 0" by auto
  with * show ?Q by (simp add: last_coeffs_eq_coeff_degree)
qed

instantiation poly :: (linordered_idom) linordered_idom
begin

definition
  "x < y \<longleftrightarrow> pos_poly (y - x)"

definition
  "x \<le> y \<longleftrightarrow> x = y \<or> pos_poly (y - x)"

definition
  "\<bar>x::'a poly\<bar> = (if x < 0 then - x else x)"

definition
  "sgn (x::'a poly) = (if x = 0 then 0 else if 0 < x then 1 else - 1)"

instance
proof
  fix x y z :: "'a poly"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    unfolding less_eq_poly_def less_poly_def
    apply safe
    apply simp
    apply (drule (1) pos_poly_add)
    apply simp
    done
  show "x \<le> x"
    unfolding less_eq_poly_def by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding less_eq_poly_def
    apply safe
    apply (drule (1) pos_poly_add)
    apply (simp add: algebra_simps)
    done
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding less_eq_poly_def
    apply safe
    apply (drule (1) pos_poly_add)
    apply simp
    done
  show "x \<le> y \<Longrightarrow> z + x \<le> z + y"
    unfolding less_eq_poly_def
    apply safe
    apply (simp add: algebra_simps)
    done
  show "x \<le> y \<or> y \<le> x"
    unfolding less_eq_poly_def
    using pos_poly_total [of "x - y"]
    by auto
  show "x < y \<Longrightarrow> 0 < z \<Longrightarrow> z * x < z * y"
    unfolding less_poly_def
    by (simp add: right_diff_distrib [symmetric] pos_poly_mult)
  show "\<bar>x\<bar> = (if x < 0 then - x else x)"
    by (rule abs_poly_def)
  show "sgn x = (if x = 0 then 0 else if 0 < x then 1 else - 1)"
    by (rule sgn_poly_def)
qed

end

text \<open>TODO: Simplification rules for comparisons\<close>


subsection \<open>Synthetic division and polynomial roots\<close>

text \<open>
  Synthetic division is simply division by the linear polynomial @{term "x - c"}.
\<close>

definition synthetic_divmod :: "'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a poly \<times> 'a"
where
  "synthetic_divmod p c = fold_coeffs (\<lambda>a (q, r). (pCons r q, a + c * r)) p (0, 0)"

definition synthetic_div :: "'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a poly"
where
  "synthetic_div p c = fst (synthetic_divmod p c)"

lemma synthetic_divmod_0 [simp]:
  "synthetic_divmod 0 c = (0, 0)"
  by (simp add: synthetic_divmod_def)

lemma synthetic_divmod_pCons [simp]:
  "synthetic_divmod (pCons a p) c = (\<lambda>(q, r). (pCons r q, a + c * r)) (synthetic_divmod p c)"
  by (cases "p = 0 \<and> a = 0") (auto simp add: synthetic_divmod_def)

lemma synthetic_div_0 [simp]:
  "synthetic_div 0 c = 0"
  unfolding synthetic_div_def by simp

lemma synthetic_div_unique_lemma: "smult c p = pCons a p \<Longrightarrow> p = 0"
by (induct p arbitrary: a) simp_all

lemma snd_synthetic_divmod:
  "snd (synthetic_divmod p c) = poly p c"
  by (induct p, simp, simp add: split_def)

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
    with \<open>p \<noteq> 0\<close> have "k \<noteq> 0" by auto
    with k have "degree p = Suc (degree k)"
      by (simp add: degree_mult_eq del: mult_pCons_left)
    with \<open>Suc n = degree p\<close> have "n = degree k" by simp
    then have "finite {x. poly k x = 0}" using \<open>k \<noteq> 0\<close> by (rule Suc.hyps)
    then have "finite (insert a {x. poly k x = 0})" by simp
    then show "finite {x. poly p x = 0}"
      by (simp add: k Collect_disj_eq del: mult_pCons_left)
  qed
qed

lemma poly_eq_poly_eq_iff:
  fixes p q :: "'a::{idom,ring_char_0} poly"
  shows "poly p = poly q \<longleftrightarrow> p = q" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?Q then show ?P by simp
next
  { fix p :: "'a::{idom,ring_char_0} poly"
    have "poly p = poly 0 \<longleftrightarrow> p = 0"
      apply (cases "p = 0", simp_all)
      apply (drule poly_roots_finite)
      apply (auto simp add: infinite_UNIV_char_0)
      done
  } note this [of "p - q"]
  moreover assume ?P
  ultimately show ?Q by auto
qed

lemma poly_all_0_iff_0:
  fixes p :: "'a::{ring_char_0, idom} poly"
  shows "(\<forall>x. poly p x = 0) \<longleftrightarrow> p = 0"
  by (auto simp add: poly_eq_poly_eq_iff [symmetric])


subsection \<open>Long division of polynomials\<close>

definition pdivmod_rel :: "'a::field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> bool"
where
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
  with \<open>degree p \<le> n\<close> and \<open>coeff p n = 0\<close>
  have "coeff p (degree p) = 0" by simp
  then have "p = 0" by simp
  then show ?thesis ..
next
  case (Suc m)
  have "\<forall>i>n. coeff p i = 0"
    using \<open>degree p \<le> n\<close> by (simp add: coeff_eq_0)
  then have "\<forall>i\<ge>n. coeff p i = 0"
    using \<open>coeff p n = 0\<close> by (simp add: le_less)
  then have "\<forall>i>m. coeff p i = 0"
    using \<open>n = Suc m\<close> by (simp add: less_eq_Suc_le)
  then have "degree p \<le> m"
    by (rule degree_le)
  then have "degree p < n"
    using \<open>n = Suc m\<close> by (simp add: less_Suc_eq_le)
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
      using \<open>y \<noteq> 0\<close> unfolding b by simp
  qed

  from 1 2 show ?thesis
    unfolding pdivmod_rel_def
    using \<open>y \<noteq> 0\<close> by simp
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
      using \<open>q1 \<noteq> q2\<close> by (simp add: degree_mult_eq)
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

lemmas pdivmod_rel_unique_div = pdivmod_rel_unique [THEN conjunct1]

lemmas pdivmod_rel_unique_mod = pdivmod_rel_unique [THEN conjunct2]



subsection\<open>Pseudo-Division and Division of Polynomials\<close>

text\<open>This part is by René Thiemann and Akihisa Yamada.\<close>

fun pseudo_divmod_main :: "'a :: comm_ring_1  \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly 
  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a poly \<times> 'a poly" where
  "pseudo_divmod_main lc q r d dr (Suc n) = (let
     rr = smult lc r;
     qq = coeff r dr;
     rrr = rr - monom qq n * d;
     qqq = smult lc q + monom qq n
     in pseudo_divmod_main lc qqq rrr d (dr - 1) n)"
| "pseudo_divmod_main lc q r d dr 0 = (q,r)"

definition pseudo_divmod :: "'a :: comm_ring_1 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<times> 'a poly" where
  "pseudo_divmod p q \<equiv> if q = 0 then (0,p) else
     pseudo_divmod_main (coeff q (degree q)) 0 p q (degree p) (1 + length (coeffs p) - length (coeffs q))"

lemma coeff_0_degree_minus_1: "coeff rrr dr = 0 \<Longrightarrow> degree rrr \<le> dr \<Longrightarrow> degree rrr \<le> dr - 1"
  using eq_zero_or_degree_less by fastforce
  
lemma pseudo_divmod_main: assumes d: "d \<noteq> 0" "lc = coeff d (degree d)"
  and *: "degree r \<le> dr" "pseudo_divmod_main lc q r d dr n = (q',r')" 
    "n = 1 + dr - degree d \<or> dr = 0 \<and> n = 0 \<and> r = 0" 
  shows "(r' = 0 \<or> degree r' < degree d) \<and> smult (lc^n) (d * q + r) = d * q' + r'"
  using *
proof (induct n arbitrary: q r dr)
  case (Suc n q r dr)
  let ?rr = "smult lc r"
  let ?qq = "coeff r dr"
  def [simp]: b \<equiv> "monom ?qq n"
  let ?rrr = "?rr - b * d"
  let ?qqq = "smult lc q + b"
  note res = Suc(3)
  from res[unfolded pseudo_divmod_main.simps[of lc q] Let_def] 
  have res: "pseudo_divmod_main lc ?qqq ?rrr d (dr - 1) n = (q',r')" 
    by (simp del: pseudo_divmod_main.simps)
  have dr: "dr = n + degree d" using Suc(4) by auto
  have "coeff (b * d) dr = coeff b n * coeff d (degree d)"
  proof (cases "?qq = 0")
    case False
    hence n: "n = degree b" by (simp add: degree_monom_eq)
    show ?thesis unfolding n dr by (simp add: coeff_mult_degree_sum)
  qed auto
  also have "\<dots> = lc * coeff b n" unfolding d by simp
  finally have "coeff (b * d) dr = lc * coeff b n" .
  moreover have "coeff ?rr dr = lc * coeff r dr" by simp
  ultimately have c0: "coeff ?rrr dr = 0" by auto
  have dr: "dr = n + degree d" using Suc(4) by auto
  have deg_rr: "degree ?rr \<le> dr" using Suc(2) 
    using degree_smult_le dual_order.trans by blast 
  have deg_bd: "degree (b * d) \<le> dr"
    unfolding dr
    by(rule order.trans[OF degree_mult_le], auto simp: degree_monom_le)
  have "degree ?rrr \<le> dr"
    using degree_diff_le[OF deg_rr deg_bd] by auto
  with c0 have deg_rrr: "degree ?rrr \<le> (dr - 1)" by (rule coeff_0_degree_minus_1)
  have "n = 1 + (dr - 1) - degree d \<or> dr - 1 = 0 \<and> n = 0 \<and> ?rrr = 0"
  proof (cases dr)
    case 0
    with Suc(4) have 0: "dr = 0" "n = 0" "degree d = 0" by auto
    with deg_rrr have "degree ?rrr = 0" by simp
    hence "\<exists> a. ?rrr = [: a :]" by (metis degree_pCons_eq_if old.nat.distinct(2) pCons_cases)
    from this obtain a where rrr: "?rrr = [:a:]" by auto
    show ?thesis unfolding 0 using c0 unfolding rrr 0 by simp
  qed (insert Suc(4), auto)
  note IH = Suc(1)[OF deg_rrr res this]
  show ?case
  proof (intro conjI)
    show "r' = 0 \<or> degree r' < degree d" using IH by blast
    show "smult (lc ^ Suc n) (d * q + r) = d * q' + r'"
      unfolding IH[THEN conjunct2,symmetric]
      by (simp add: field_simps smult_add_right)
  qed
qed auto

lemma pseudo_divmod:
  assumes g: "g \<noteq> 0" and *: "pseudo_divmod f g = (q,r)" 
  shows "smult (coeff g (degree g) ^ (Suc (degree f) - degree g)) f = g * q + r" (is ?A)
    and "r = 0 \<or> degree r < degree g" (is ?B)
proof -
  from *[unfolded pseudo_divmod_def Let_def]
  have "pseudo_divmod_main (coeff g (degree g)) 0 f g (degree f) (1 + length (coeffs f) - length (coeffs g)) = (q, r)" by (auto simp: g)
  note main = pseudo_divmod_main[OF _ _ _ this, OF g refl le_refl]
  have "1 + length (coeffs f) - length (coeffs g) = 1 + degree f - degree g \<or>
    degree f = 0 \<and> 1 + length (coeffs f) - length (coeffs g) = 0 \<and> f = 0" using g 
    by (cases "f = 0"; cases "coeffs g", auto simp: degree_eq_length_coeffs)
  note main = main[OF this]
  from main show "r = 0 \<or> degree r < degree g" by auto
  show "smult (coeff g (degree g) ^ (Suc (degree f) - degree g)) f = g * q + r" 
    by (subst main[THEN conjunct2, symmetric], simp add: degree_eq_length_coeffs,
    insert g, cases "f = 0"; cases "coeffs g", auto)
qed
  
definition "pseudo_mod_main lc r d dr n = snd (pseudo_divmod_main lc 0 r d dr n)"

lemma snd_pseudo_divmod_main:
  "snd (pseudo_divmod_main lc q r d dr n) = snd (pseudo_divmod_main lc q' r d dr n)"
by (induct n arbitrary: q q' lc r d dr; simp add: Let_def)

definition pseudo_mod :: "'a :: idom_divide poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "pseudo_mod f g = snd (pseudo_divmod f g)"
  
lemma pseudo_mod:
  fixes f g
  defines "r \<equiv> pseudo_mod f g"
  assumes g: "g \<noteq> 0"
  shows "\<exists> a q. a \<noteq> 0 \<and> smult a f = g * q + r" "r = 0 \<or> degree r < degree g"
proof - 
  let ?cg = "coeff g (degree g)"
  let ?cge = "?cg ^ (Suc (degree f) - degree g)"
  def a \<equiv> ?cge
  obtain q where pdm: "pseudo_divmod f g = (q,r)" using r_def[unfolded pseudo_mod_def]
    by (cases "pseudo_divmod f g", auto)
  from pseudo_divmod[OF g pdm] have id: "smult a f = g * q + r" and "r = 0 \<or> degree r < degree g" 
    unfolding a_def by auto
  show "r = 0 \<or> degree r < degree g" by fact
  from g have "a \<noteq> 0" unfolding a_def by auto
  thus "\<exists> a q. a \<noteq> 0 \<and> smult a f = g * q + r" using id by auto
qed

instantiation poly :: (idom_divide) idom_divide
begin

fun divide_poly_main :: "'a \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly 
  \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "divide_poly_main lc q r d dr (Suc n) = (let cr = coeff r dr; a = cr div lc; mon = monom a n in 
     if False \<or> a * lc = cr then (* False \<or> is only because of problem in function-package *)
     divide_poly_main 
       lc 
       (q + mon) 
       (r - mon * d) 
       d (dr - 1) n else 0)"
| "divide_poly_main lc q r d dr 0 = q"

definition divide_poly :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "divide_poly f g = (if g = 0 then 0 else
     divide_poly_main (coeff g (degree g)) 0 f g (degree f) (1 + length (coeffs f) - length (coeffs g)))" 

lemma divide_poly_main:
  assumes d: "d \<noteq> 0" "lc = coeff d (degree d)"
    and *: "degree (d * r) \<le> dr" "divide_poly_main lc q (d * r) d dr n = q'" 
    "n = 1 + dr - degree d \<or> dr = 0 \<and> n = 0 \<and> d * r = 0" 
  shows "q' = q + r"
  using *
proof (induct n arbitrary: q r dr)
  case (Suc n q r dr)
  let ?rr = "d * r"
  let ?a = "coeff ?rr dr"
  let ?qq = "?a div lc"
  def [simp]: b \<equiv> "monom ?qq n"
  let ?rrr =  "d * (r - b)"
  let ?qqq = "q + b"
  note res = Suc(3)
  have dr: "dr = n + degree d" using Suc(4) by auto
  have lc: "lc \<noteq> 0" using d by auto
  have "coeff (b * d) dr = coeff b n * coeff d (degree d)"
  proof (cases "?qq = 0")
    case False
    hence n: "n = degree b" by (simp add: degree_monom_eq)
    show ?thesis unfolding n dr by (simp add: coeff_mult_degree_sum)
  qed simp
  also have "\<dots> = lc * coeff b n" unfolding d by simp
  finally have c2: "coeff (b * d) dr = lc * coeff b n" .
  have rrr: "?rrr = ?rr - b * d" by (simp add: field_simps)
  have c1: "coeff (d * r) dr = lc * coeff r n"
  proof (cases "degree r = n")
    case True
    thus ?thesis using Suc(2) unfolding dr using coeff_mult_degree_sum[of d r] d by (auto simp: ac_simps)
  next
    case False
    have "degree r \<le> n" using dr Suc(2) by auto
      (metis add.commute add_le_cancel_left d(1) degree_0 degree_mult_eq diff_is_0_eq diff_zero le_cases)
    with False have r_n: "degree r < n" by auto
    hence right: "lc * coeff r n = 0" by (simp add: coeff_eq_0)
    have "coeff (d * r) dr = coeff (d * r) (degree d + n)" unfolding dr by (simp add: ac_simps)
    also have "\<dots> = 0" using r_n
      by (metis False Suc.prems(1) add.commute add_left_imp_eq coeff_degree_mult coeff_eq_0 
        coeff_mult_degree_sum degree_mult_le dr le_eq_less_or_eq)
    finally show ?thesis unfolding right .
  qed
  have c0: "coeff ?rrr dr = 0" 
    and id: "lc * (coeff (d * r) dr div lc) = coeff (d * r) dr" unfolding rrr coeff_diff c2
    unfolding b_def coeff_monom coeff_smult c1 using lc by auto
  from res[unfolded divide_poly_main.simps[of lc q] Let_def] id
  have res: "divide_poly_main lc ?qqq ?rrr d (dr - 1) n = q'" 
    by (simp del: divide_poly_main.simps add: field_simps)
  note IH = Suc(1)[OF _ res] 
  have dr: "dr = n + degree d" using Suc(4) by auto
  have deg_rr: "degree ?rr \<le> dr" using Suc(2) by auto
  have deg_bd: "degree (b * d) \<le> dr"
    unfolding dr b_def by (rule order.trans[OF degree_mult_le], auto simp: degree_monom_le)
  have "degree ?rrr \<le> dr" unfolding rrr by (rule degree_diff_le[OF deg_rr deg_bd])
  with c0 have deg_rrr: "degree ?rrr \<le> (dr - 1)" by (rule coeff_0_degree_minus_1)
  have "n = 1 + (dr - 1) - degree d \<or> dr - 1 = 0 \<and> n = 0 \<and> ?rrr = 0"  
  proof (cases dr)
    case 0
    with Suc(4) have 0: "dr = 0" "n = 0" "degree d = 0" by auto
    with deg_rrr have "degree ?rrr = 0" by simp
    from degree_eq_zeroE[OF this] obtain a where rrr: "?rrr = [:a:]" by metis
    show ?thesis unfolding 0 using c0 unfolding rrr 0 by simp
  qed (insert Suc(4), auto)
  note IH = IH[OF deg_rrr this]
  show ?case using IH by simp
next
  case (0 q r dr)
  show ?case 
  proof (cases "r = 0")
    case True
    thus ?thesis using 0 by auto
  next
    case False
    have "degree (d * r) = degree d + degree r" using d False 
      by (subst degree_mult_eq, auto)
    thus ?thesis using 0 d by auto
  qed
qed 

lemma fst_pseudo_divmod_main_as_divide_poly_main:
  assumes d: "d \<noteq> 0"
  defines lc: "lc \<equiv> coeff d (degree d)"
  shows "fst (pseudo_divmod_main lc q r d dr n) = divide_poly_main lc (smult (lc^n) q) (smult (lc^n) r) d dr n"
proof(induct n arbitrary: q r dr)
  case 0 then show ?case by simp
next
  case (Suc n)
    note lc0 = leading_coeff_neq_0[OF d, folded lc]
    then have "pseudo_divmod_main lc q r d dr (Suc n) =
    pseudo_divmod_main lc (smult lc q + monom (coeff r dr) n)
      (smult lc r - monom (coeff r dr) n * d) d (dr - 1) n"
    by (simp add: Let_def ac_simps)
    also have "fst ... = divide_poly_main lc
     (smult (lc^n) (smult lc q + monom (coeff r dr) n))
     (smult (lc^n) (smult lc r - monom (coeff r dr) n * d))
     d (dr - 1) n"
      unfolding Suc[unfolded divide_poly_main.simps Let_def]..
    also have "... = divide_poly_main lc (smult (lc ^ Suc n) q)
        (smult (lc ^ Suc n) r) d dr (Suc n)"
      unfolding smult_monom smult_distribs mult_smult_left[symmetric]
      using lc0 by (simp add: Let_def ac_simps)
    finally show ?case.
qed


lemma divide_poly_main_0: "divide_poly_main 0 0 r d dr n = 0"
proof (induct n arbitrary: r d dr)
  case (Suc n r d dr)
  show ?case unfolding divide_poly_main.simps[of _ _ r] Let_def
    by (simp add: Suc del: divide_poly_main.simps)
qed simp

lemma divide_poly:
  assumes g: "g \<noteq> 0"
  shows "(f * g) div g = (f :: 'a poly)" 
proof - 
  have "divide_poly_main (coeff g (degree g)) 0 (g * f) g (degree (g * f)) (1 + length (coeffs (g * f)) - length (coeffs  g)) 
    = (f * g) div g" unfolding divide_poly_def Let_def by (simp add: ac_simps)
  note main = divide_poly_main[OF g refl le_refl this]
  {
    fix f :: "'a poly"
    assume "f \<noteq> 0"
    hence "length (coeffs f) = Suc (degree f)" unfolding degree_eq_length_coeffs by auto
  } note len = this
  have "(f * g) div g = 0 + f"
  proof (rule main, goal_cases)
    case 1
    show ?case
    proof (cases "f = 0")
      case True
      with g show ?thesis by (auto simp: degree_eq_length_coeffs)
    next
      case False
      with g have fg: "g * f \<noteq> 0" by auto
      show ?thesis unfolding len[OF fg] len[OF g] by auto
    qed
  qed
  thus ?thesis by simp
qed

lemma divide_poly_0: "f div 0 = (0 :: 'a poly)"
  by (simp add: divide_poly_def Let_def divide_poly_main_0)

instance by (standard, auto simp: divide_poly divide_poly_0)
end


subsubsection\<open>Division in Field Polynomials\<close>

text\<open>
 This part connects the above result to the division of field polynomials.
 Mainly imported from Isabelle 2016.
\<close>

lemma pseudo_divmod_field:
  assumes g: "(g::'a::field poly) \<noteq> 0" and *: "pseudo_divmod f g = (q,r)"
  defines "c \<equiv> coeff g (degree g) ^ (Suc (degree f) - degree g)"
  shows "f = g * smult (1/c) q + smult (1/c) r"
proof -
  from leading_coeff_neq_0[OF g] have c0: "c \<noteq> 0" unfolding c_def by auto
  from pseudo_divmod(1)[OF g *, folded c_def]
  have "smult c f = g * q + r" by auto
  also have "smult (1/c) ... = g * smult (1/c) q + smult (1/c) r" by (simp add: smult_add_right)
  finally show ?thesis using c0 by auto
qed

lemma divide_poly_main_field:
  assumes d: "(d::'a::field poly) \<noteq> 0"
  defines lc: "lc \<equiv> coeff d (degree d)"
  shows "divide_poly_main lc q r d dr n = fst (pseudo_divmod_main lc (smult ((1/lc)^n) q) (smult ((1/lc)^n) r) d dr n)"
  unfolding lc
  by(subst fst_pseudo_divmod_main_as_divide_poly_main, auto simp: d power_one_over)

lemma divide_poly_field:
  fixes f g :: "'a :: field poly"
  defines "f' \<equiv> smult ((1 / coeff g (degree g)) ^ (Suc (degree f) - degree g)) f"
  shows "(f::'a::field poly) div g = fst (pseudo_divmod f' g)"
proof (cases "g = 0")
  case True show ?thesis 
    unfolding divide_poly_def pseudo_divmod_def Let_def f'_def True by (simp add: divide_poly_main_0)
next
  case False
    from leading_coeff_neq_0[OF False] have "degree f' = degree f" unfolding f'_def by auto
    then show ?thesis
      using length_coeffs_degree[of f'] length_coeffs_degree[of f]
      unfolding divide_poly_def pseudo_divmod_def Let_def
                divide_poly_main_field[OF False]
                length_coeffs_degree[OF False] 
                f'_def
      by force
qed

instantiation poly :: (field) ring_div
begin

definition mod_poly where
  "f mod g \<equiv>
    if g = 0 then f
    else pseudo_mod (smult ((1/coeff g (degree g)) ^ (Suc (degree f) - degree g)) f) g"

lemma pdivmod_rel: "pdivmod_rel (x::'a::field poly) y (x div y) (x mod y)"
  unfolding pdivmod_rel_def
proof (intro conjI)
  show "x = x div y * y + x mod y"
  proof(cases "y = 0")
    case True show ?thesis by(simp add: True divide_poly_def divide_poly_0 mod_poly_def)
  next
    case False
    then have "pseudo_divmod (smult ((1 / coeff y (degree y)) ^ (Suc (degree x) - degree y)) x) y =
          (x div y, x mod y)"
      unfolding divide_poly_field mod_poly_def pseudo_mod_def by simp
    from pseudo_divmod[OF False this]
    show ?thesis using False
      by (simp add: power_mult_distrib[symmetric] mult.commute)
  qed
  show "if y = 0 then x div y = 0 else x mod y = 0 \<or> degree (x mod y) < degree y"
  proof (cases "y = 0")
    case True then show ?thesis by auto
  next
    case False
      with pseudo_mod[OF this] show ?thesis unfolding mod_poly_def by simp
  qed
qed

lemma div_poly_eq:
  "pdivmod_rel (x::'a::field poly) y q r \<Longrightarrow> x div y = q"
  by(rule pdivmod_rel_unique_div[OF pdivmod_rel])

lemma mod_poly_eq:
  "pdivmod_rel (x::'a::field poly) y q r \<Longrightarrow> x mod y = r"
  by (rule pdivmod_rel_unique_mod[OF pdivmod_rel])

instance
proof
  fix x y :: "'a poly"
  from pdivmod_rel[of x y,unfolded pdivmod_rel_def]
  show "x div y * y + x mod y = x" by auto
next
  fix x :: "'a poly"
  show "x div 0 = 0" by simp
next
  fix y :: "'a poly"
  show "0 div y = 0" by simp
next
  fix x y z :: "'a poly"
  assume "y \<noteq> 0"
  hence "pdivmod_rel (x + z * y) y (z + x div y) (x mod y)"
    using pdivmod_rel [of x y]
    by (simp add: pdivmod_rel_def distrib_right)
  thus "(x + z * y) div y = z + x div y"
    by (rule div_poly_eq)
next
  fix x y z :: "'a poly"
  assume "x \<noteq> 0"
  show "(x * y) div (x * z) = y div z"
  proof (cases "y \<noteq> 0 \<and> z \<noteq> 0")
    have "\<And>x::'a poly. pdivmod_rel x 0 0 x"
      by (rule pdivmod_rel_by_0)
    then have [simp]: "\<And>x::'a poly. x div 0 = 0"
      by (rule div_poly_eq)
    have "\<And>x::'a poly. pdivmod_rel 0 x 0 0"
      by (rule pdivmod_rel_0)
    then have [simp]: "\<And>x::'a poly. 0 div x = 0"
      by (rule div_poly_eq)
    case False then show ?thesis by auto
  next
    case True then have "y \<noteq> 0" and "z \<noteq> 0" by auto
    with \<open>x \<noteq> 0\<close>
    have "\<And>q r. pdivmod_rel y z q r \<Longrightarrow> pdivmod_rel (x * y) (x * z) q (x * r)"
      by (auto simp add: pdivmod_rel_def algebra_simps)
        (rule classical, simp add: degree_mult_eq)
    moreover from pdivmod_rel have "pdivmod_rel y z (y div z) (y mod z)" .
    ultimately have "pdivmod_rel (x * y) (x * z) (y div z) (x * (y mod z))" .
    then show ?thesis by (simp add: div_poly_eq)
  qed
qed

end

lemma is_unit_monom_0:
  fixes a :: "'a::field"
  assumes "a \<noteq> 0"
  shows "is_unit (monom a 0)"
proof
  from assms show "1 = monom a 0 * monom (inverse a) 0"
    by (simp add: mult_monom)
qed

lemma is_unit_triv:
  fixes a :: "'a::field"
  assumes "a \<noteq> 0"
  shows "is_unit [:a:]"
  using assms by (simp add: is_unit_monom_0 monom_0 [symmetric])

lemma is_unit_iff_degree:
  assumes "p \<noteq> 0"
  shows "is_unit p \<longleftrightarrow> degree p = 0" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?Q
  then obtain a where "p = [:a:]" by (rule degree_eq_zeroE)
  with assms show ?P by (simp add: is_unit_triv)
next
  assume ?P
  then obtain q where "q \<noteq> 0" "p * q = 1" ..
  then have "degree (p * q) = degree 1"
    by simp
  with \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> have "degree p + degree q = 0"
    by (simp add: degree_mult_eq)
  then show ?Q by simp
qed

lemma is_unit_pCons_iff:
  "is_unit (pCons a p) \<longleftrightarrow> p = 0 \<and> a \<noteq> 0" (is "?P \<longleftrightarrow> ?Q")
  by (cases "p = 0") (auto simp add: is_unit_triv is_unit_iff_degree)

lemma is_unit_monom_trival:
  fixes p :: "'a::field poly"
  assumes "is_unit p"
  shows "monom (coeff p (degree p)) 0 = p"
  using assms by (cases p) (simp_all add: monom_0 is_unit_pCons_iff)

lemma is_unit_polyE:
  assumes "is_unit p"
  obtains a where "p = monom a 0" and "a \<noteq> 0"
proof -
  obtain a q where "p = pCons a q" by (cases p)
  with assms have "p = [:a:]" and "a \<noteq> 0"
    by (simp_all add: is_unit_pCons_iff)
  with that show thesis by (simp add: monom_0)
qed

instantiation poly :: (field) normalization_semidom
begin

definition normalize_poly :: "'a poly \<Rightarrow> 'a poly"
  where "normalize_poly p = smult (inverse (coeff p (degree p))) p"

definition unit_factor_poly :: "'a poly \<Rightarrow> 'a poly"
  where "unit_factor_poly p = monom (coeff p (degree p)) 0"

instance
proof
  fix p :: "'a poly"
  show "unit_factor p * normalize p = p"
    by (cases "p = 0")
      (simp_all add: normalize_poly_def unit_factor_poly_def,
      simp only: mult_smult_left [symmetric] smult_monom, simp)
next
  show "normalize 0 = (0::'a poly)"
    by (simp add: normalize_poly_def)
next
  show "unit_factor 0 = (0::'a poly)"
    by (simp add: unit_factor_poly_def)
next
  fix p :: "'a poly"
  assume "is_unit p"
  then obtain a where "p = monom a 0" and "a \<noteq> 0"
    by (rule is_unit_polyE)
  then show "normalize p = 1"
    by (auto simp add: normalize_poly_def smult_monom degree_monom_eq)
next
  fix p q :: "'a poly"
  assume "q \<noteq> 0"
  from \<open>q \<noteq> 0\<close> have "is_unit (monom (coeff q (degree q)) 0)"
    by (auto intro: is_unit_monom_0)
  then show "is_unit (unit_factor q)"
    by (simp add: unit_factor_poly_def)
next
  fix p q :: "'a poly"
  have "monom (coeff (p * q) (degree (p * q))) 0 =
    monom (coeff p (degree p)) 0 * monom (coeff q (degree q)) 0"
    by (simp add: monom_0 coeff_degree_mult)
  then show "unit_factor (p * q) =
    unit_factor p * unit_factor q"
    by (simp add: unit_factor_poly_def)
qed

end

lemma unit_factor_monom [simp]:
  "unit_factor (monom a n) =
     (if a = 0 then 0 else monom a 0)"
  by (simp add: unit_factor_poly_def degree_monom_eq)

lemma unit_factor_pCons [simp]:
  "unit_factor (pCons a p) =
     (if p = 0 then monom a 0 else unit_factor p)"
  by (simp add: unit_factor_poly_def)

lemma normalize_monom [simp]:
  "normalize (monom a n) =
     (if a = 0 then 0 else monom 1 n)"
  by (simp add: normalize_poly_def degree_monom_eq smult_monom)

lemma degree_mod_less:
  "y \<noteq> 0 \<Longrightarrow> x mod y = 0 \<or> degree (x mod y) < degree y"
  using pdivmod_rel [of x y]
  unfolding pdivmod_rel_def by simp

lemma div_poly_less: "degree (x::'a::field poly) < degree y \<Longrightarrow> x div y = 0"
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

lemma div_smult_left: "(smult (a::'a::field) x) div y = smult a (x div y)"
  by (rule div_poly_eq, rule pdivmod_rel_smult_left, rule pdivmod_rel)

lemma mod_smult_left: "(smult a x) mod y = smult a (x mod y)"
  by (rule mod_poly_eq, rule pdivmod_rel_smult_left, rule pdivmod_rel)

lemma poly_div_minus_left [simp]:
  fixes x y :: "'a::field poly"
  shows "(- x) div y = - (x div y)"
  using div_smult_left [of "- 1::'a"] by simp

lemma poly_mod_minus_left [simp]:
  fixes x y :: "'a::field poly"
  shows "(- x) mod y = - (x mod y)"
  using mod_smult_left [of "- 1::'a"] by simp

lemma pdivmod_rel_add_left:
  assumes "pdivmod_rel x y q r"
  assumes "pdivmod_rel x' y q' r'"
  shows "pdivmod_rel (x + x') y (q + q') (r + r')"
  using assms unfolding pdivmod_rel_def
  by (auto simp add: algebra_simps degree_add_less)

lemma poly_div_add_left:
  fixes x y z :: "'a::field poly"
  shows "(x + y) div z = x div z + y div z"
  using pdivmod_rel_add_left [OF pdivmod_rel pdivmod_rel]
  by (rule div_poly_eq)

lemma poly_mod_add_left:
  fixes x y z :: "'a::field poly"
  shows "(x + y) mod z = x mod z + y mod z"
  using pdivmod_rel_add_left [OF pdivmod_rel pdivmod_rel]
  by (rule mod_poly_eq)

lemma poly_div_diff_left:
  fixes x y z :: "'a::field poly"
  shows "(x - y) div z = x div z - y div z"
  by (simp only: diff_conv_add_uminus poly_div_add_left poly_div_minus_left)

lemma poly_mod_diff_left:
  fixes x y z :: "'a::field poly"
  shows "(x - y) mod z = x mod z - y mod z"
  by (simp only: diff_conv_add_uminus poly_mod_add_left poly_mod_minus_left)

lemma pdivmod_rel_smult_right:
  "\<lbrakk>a \<noteq> 0; pdivmod_rel x y q r\<rbrakk>
    \<Longrightarrow> pdivmod_rel x (smult a y) (smult (inverse a) q) r"
  unfolding pdivmod_rel_def by simp

lemma div_smult_right:
  "(a::'a::field) \<noteq> 0 \<Longrightarrow> x div (smult a y) = smult (inverse a) (x div y)"
  by (rule div_poly_eq, erule pdivmod_rel_smult_right, rule pdivmod_rel)

lemma mod_smult_right: "a \<noteq> 0 \<Longrightarrow> x mod (smult a y) = x mod y"
  by (rule mod_poly_eq, erule pdivmod_rel_smult_right, rule pdivmod_rel)

lemma poly_div_minus_right [simp]:
  fixes x y :: "'a::field poly"
  shows "x div (- y) = - (x div y)"
  using div_smult_right [of "- 1::'a"] by (simp add: nonzero_inverse_minus_eq)

lemma poly_mod_minus_right [simp]:
  fixes x y :: "'a::field poly"
  shows "x mod (- y) = x mod y"
  using mod_smult_right [of "- 1::'a"] by simp

lemma pdivmod_rel_mult:
  "\<lbrakk>pdivmod_rel x y q r; pdivmod_rel q z q' r'\<rbrakk>
    \<Longrightarrow> pdivmod_rel x (y * z) q' (y * r' + r)"
apply (cases "z = 0", simp add: pdivmod_rel_def)
apply (cases "y = 0", simp add: pdivmod_rel_by_0_iff pdivmod_rel_0_iff)
apply (cases "r = 0")
apply (cases "r' = 0")
apply (simp add: pdivmod_rel_def)
apply (simp add: pdivmod_rel_def field_simps degree_mult_eq)
apply (cases "r' = 0")
apply (simp add: pdivmod_rel_def degree_mult_eq)
apply (simp add: pdivmod_rel_def field_simps)
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

definition pdivmod :: "'a::field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<times> 'a poly"
where
  "pdivmod p q = (p div q, p mod q)"

lemma pdivmod_0:
  "pdivmod 0 q = (0, 0)"
  by (simp add: pdivmod_def)

lemma pdivmod_pCons:
  "pdivmod (pCons a p) q =
    (if q = 0 then (0, pCons a p) else
      (let (s, r) = pdivmod p q;
           b = coeff (pCons a r) (degree q) / coeff q (degree q)
        in (pCons b s, pCons a r - smult b q)))"
  apply (simp add: pdivmod_def Let_def, safe)
  apply (rule div_poly_eq)
  apply (erule pdivmod_rel_pCons [OF pdivmod_rel _ refl])
  apply (rule mod_poly_eq)
  apply (erule pdivmod_rel_pCons [OF pdivmod_rel _ refl])
  done

lemma pdivmod_fold_coeffs:
  "pdivmod p q = (if q = 0 then (0, p)
    else fold_coeffs (\<lambda>a (s, r).
      let b = coeff (pCons a r) (degree q) / coeff q (degree q)
      in (pCons b s, pCons a r - smult b q)
   ) p (0, 0))"
  apply (cases "q = 0")
  apply (simp add: pdivmod_def)
  apply (rule sym)
  apply (induct p)
  apply (simp_all add: pdivmod_0 pdivmod_pCons)
  apply (case_tac "a = 0 \<and> p = 0")
  apply (auto simp add: pdivmod_def)
  done

subsection \<open>List-based versions for fast implementation\<close>
(* Subsection by:
      Sebastiaan Joosten
      René Thiemann
      Akihisa Yamada
    *)
fun minus_poly_rev_list :: "'a :: group_add list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "minus_poly_rev_list (x # xs) (y # ys) = (x - y) # (minus_poly_rev_list xs ys)"
| "minus_poly_rev_list xs [] = xs"
| "minus_poly_rev_list [] (y # ys) = []"
fun pseudo_divmod_main_list :: "'a::comm_ring_1 \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list 
  \<Rightarrow> nat \<Rightarrow> 'a list \<times> 'a list" where
  "pseudo_divmod_main_list lc q r d (Suc n) = (let
     rr = map (op * lc) r;
     a = hd r;
     qqq = cCons a (map (op * lc) q);
     rrr = tl (if a = 0 then rr else minus_poly_rev_list rr (map (op * a) d))
     in pseudo_divmod_main_list lc qqq rrr d n)"
| "pseudo_divmod_main_list lc q r d 0 = (q,r)"

fun divmod_poly_one_main_list :: "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> 'a list 
  \<Rightarrow> nat \<Rightarrow> 'a list \<times> 'a list" where
  "divmod_poly_one_main_list q r d (Suc n) = (let
     a = hd r;
     qqq = cCons a q;
     rr = tl (if a = 0 then r else minus_poly_rev_list r (map (op * a) d))
     in divmod_poly_one_main_list qqq rr d n)"
| "divmod_poly_one_main_list q r d 0 = (q,r)"

fun mod_poly_one_main_list :: "'a::comm_ring_1 list \<Rightarrow> 'a list 
  \<Rightarrow> nat \<Rightarrow> 'a list" where
  "mod_poly_one_main_list r d (Suc n) = (let
     a = hd r;
     rr = tl (if a = 0 then r else minus_poly_rev_list r (map (op * a) d))
     in mod_poly_one_main_list rr d n)"
| "mod_poly_one_main_list r d 0 = r"

definition pseudo_divmod_list :: "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list" where
  "pseudo_divmod_list p q =
  (if q = [] then ([],p) else
 (let rq = rev q;
     (qu,re) = pseudo_divmod_main_list (hd rq) [] (rev p) rq (1 + length p - length q) in 
   (qu,rev re)))"

lemma minus_zero_does_nothing:
"(minus_poly_rev_list x (map (op * 0) y)) = (x :: 'a :: ring list)"
  by(induct x y rule: minus_poly_rev_list.induct, auto)

lemma length_minus_poly_rev_list[simp]:
 "length (minus_poly_rev_list xs ys) = length xs"
  by(induct xs ys rule: minus_poly_rev_list.induct, auto)

lemma if_0_minus_poly_rev_list:
  "(if a = 0 then x else minus_poly_rev_list x (map (op * a) y))
      = minus_poly_rev_list x (map (op * (a :: 'a :: ring)) y)"
  by(cases "a=0",simp_all add:minus_zero_does_nothing)

lemma Poly_append:
  "Poly ((a::'a::comm_semiring_1 list) @ b) = Poly a + monom 1 (length a) * Poly b"
  by (induct a,auto simp: monom_0 monom_Suc)

lemma minus_poly_rev_list: "length p \<ge> length (q :: 'a :: comm_ring_1 list) \<Longrightarrow>
  Poly (rev (minus_poly_rev_list (rev p) (rev q)))
  = Poly p - monom 1 (length p - length q) * Poly q"
proof (induct "rev p" "rev q" arbitrary: p q rule: minus_poly_rev_list.induct)
  case (1 x xs y ys) 
  have "length (rev q) \<le> length (rev p)" using 1 by simp
  from this[folded 1(2,3)] have ys_xs:"length ys \<le> length xs" by simp
  hence a:"Poly (rev (minus_poly_rev_list xs ys)) =
           Poly (rev xs) - monom 1 (length xs - length ys) * Poly (rev ys)"
    by(subst "1.hyps"(1)[of "rev xs" "rev ys", unfolded rev_rev_ident length_rev],auto)
  have "Poly p - monom 1 (length p - length q) * Poly q
      = Poly (rev (rev p)) - monom 1 (length (rev (rev p)) - length (rev (rev q))) * Poly (rev (rev q))"
    by simp
  also have "\<dots> = Poly (rev (x # xs)) - monom 1 (length (x # xs) - length (y # ys)) * Poly (rev (y # ys))"
    unfolding 1(2,3) by simp
  also have "\<dots> = Poly (rev xs) + monom x (length xs) -
  (monom 1 (length xs - length ys) * Poly (rev ys) + monom y (length xs))" using ys_xs
    by (simp add:Poly_append distrib_left mult_monom smult_monom)
  also have "\<dots> = Poly (rev (minus_poly_rev_list xs ys)) + monom (x - y) (length xs)"
    unfolding a diff_monom[symmetric] by(simp)
  finally show ?case
    unfolding 1(2,3)[symmetric] by (simp add: smult_monom Poly_append)
qed auto

lemma smult_monom_mult: "smult a (monom b n * f) = monom (a * b) n * f"
  using smult_monom [of a _ n] by (metis mult_smult_left)

lemma head_minus_poly_rev_list:
  "length d \<le> length r \<Longrightarrow> d\<noteq>[] \<Longrightarrow>
  hd (minus_poly_rev_list (map (op * (last d :: 'a :: comm_ring)) r) (map (op * (hd r)) (rev d))) = 0"
proof(induct r)
  case (Cons a rs)
  thus ?case by(cases "rev d", simp_all add:ac_simps)
qed simp

lemma Poly_map: "Poly (map (op * a) p) = smult a (Poly p)"
proof (induct p)
  case(Cons x xs) thus ?case by (cases "Poly xs = 0",auto)
qed simp

lemma last_coeff_is_hd: "xs \<noteq> [] \<Longrightarrow> coeff (Poly xs) (length xs - 1) = hd (rev xs)"
  by (simp_all add: hd_conv_nth rev_nth nth_default_nth nth_append)

lemma pseudo_divmod_main_list_invar :
  assumes leading_nonzero:"last d \<noteq> 0"
  and lc:"last d = lc"
  and dNonempty:"d \<noteq> []"
  and "pseudo_divmod_main_list lc q (rev r) (rev d) n = (q',rev r')"
  and "n = (1 + length r - length d)"
  shows 
  "pseudo_divmod_main lc (monom 1 n * Poly q) (Poly r) (Poly d) (length r - 1) n = 
  (Poly q', Poly r')"
using assms(4-)
proof(induct "n" arbitrary: r q)
case (Suc n r q)
  have ifCond: "\<not> Suc (length r) \<le> length d" using Suc.prems by simp
  have rNonempty:"r \<noteq> []"
    using ifCond dNonempty using Suc_leI length_greater_0_conv list.size(3) by fastforce
  let ?a = "(hd (rev r))"
  let ?rr = "map (op * lc) (rev r)"
  let ?rrr = "rev (tl (minus_poly_rev_list ?rr (map (op * ?a) (rev d))))"
  let ?qq = "cCons ?a (map (op * lc) q)"
  have n: "n = (1 + length r - length d - 1)"
    using ifCond Suc(3) by simp
  have rr_val:"(length ?rrr) = (length r - 1)" using ifCond by auto
  hence rr_smaller: "(1 + length r - length d - 1) = (1 + length ?rrr - length d)"
    using rNonempty ifCond unfolding One_nat_def by auto
  from ifCond have id: "Suc (length r) - length d = Suc (length r - length d)" by auto
  have "pseudo_divmod_main_list lc ?qq (rev ?rrr) (rev d) (1 + length r - length d - 1) = (q', rev r')"
    using Suc.prems ifCond by (simp add:Let_def if_0_minus_poly_rev_list id)
  hence v:"pseudo_divmod_main_list lc ?qq (rev ?rrr) (rev d) n = (q', rev r')"
    using n by auto
  have sucrr:"Suc (length r) - length d = Suc (length r - length d)"
    using Suc_diff_le ifCond not_less_eq_eq by blast
  have n_ok : "n = 1 + (length ?rrr) - length d" using Suc(3) rNonempty by simp
  have cong: "\<And> x1 x2 x3 x4 y1 y2 y3 y4. x1 = y1 \<Longrightarrow> x2 = y2 \<Longrightarrow> x3 = y3 \<Longrightarrow> x4 = y4 \<Longrightarrow>
    pseudo_divmod_main lc x1 x2 x3 x4 n = pseudo_divmod_main lc y1 y2 y3 y4 n" by simp
  have hd_rev:"coeff (Poly r) (length r - Suc 0) = hd (rev r)"
    using last_coeff_is_hd[OF rNonempty] by simp
  show ?case unfolding Suc.hyps(1)[OF v n_ok, symmetric] pseudo_divmod_main.simps Let_def
  proof (rule cong[OF _ _ refl], goal_cases)
    case 1 
    show ?case unfolding monom_Suc hd_rev[symmetric]
      by (simp add: smult_monom Poly_map)
  next
    case 2 
    show ?case 
    proof (subst Poly_on_rev_starting_with_0, goal_cases)
      show "hd (minus_poly_rev_list (map (op * lc) (rev r)) (map (op * (hd (rev r))) (rev d))) = 0"
        by (fold lc, subst head_minus_poly_rev_list, insert ifCond dNonempty,auto)
      from ifCond have "length d \<le> length r" by simp
      then show "smult lc (Poly r) - monom (coeff (Poly r) (length r - 1)) n * Poly d =
        Poly (rev (minus_poly_rev_list (map (op * lc) (rev r)) (map (op * (hd (rev r))) (rev d))))"
        by (fold rev_map) (auto simp add: n smult_monom_mult Poly_map hd_rev [symmetric]
          minus_poly_rev_list)
    qed
  qed simp
qed simp

lemma pseudo_divmod_impl[code]: "pseudo_divmod (f::'a::comm_ring_1 poly) g =
  map_prod poly_of_list poly_of_list (pseudo_divmod_list (coeffs f) (coeffs g))"
proof (cases "g=0")
case False
  hence coeffs_g_nonempty:"(coeffs g) \<noteq> []" by simp
  hence lastcoeffs:"last (coeffs g) = coeff g (degree g)"
    by (simp add: hd_rev last_coeffs_eq_coeff_degree not_0_coeffs_not_Nil)
  obtain q r where qr: "pseudo_divmod_main_list
            (last (coeffs g)) (rev [])
            (rev (coeffs f)) (rev (coeffs g))
            (1 + length (coeffs f) -
             length (coeffs g)) = (q,rev (rev r))"  by force
  then have qr': "pseudo_divmod_main_list
            (hd (rev (coeffs g))) []
            (rev (coeffs f)) (rev (coeffs g))
            (1 + length (coeffs f) -
             length (coeffs g)) = (q,r)" using hd_rev[OF coeffs_g_nonempty] by(auto)
  from False have cg: "(coeffs g = []) = False" by auto
  have last_non0:"last (coeffs g) \<noteq> 0" using False by (simp add:last_coeffs_not_0)
  show ?thesis
    unfolding pseudo_divmod_def pseudo_divmod_list_def Let_def qr' map_prod_def split cg if_False
    pseudo_divmod_main_list_invar[OF last_non0 _ _ qr,unfolded lastcoeffs,simplified,symmetric,OF False]
    poly_of_list_def
    using False by (auto simp: degree_eq_length_coeffs)
next
  case True
  show ?thesis unfolding True unfolding pseudo_divmod_def pseudo_divmod_list_def
  by auto
qed

(* *************** *)
subsubsection \<open>Improved Code-Equations for Polynomial (Pseudo) Division\<close>

lemma pdivmod_pdivmodrel: "pdivmod_rel p q r s = (pdivmod p q = (r, s))"
  by (metis pdivmod_def pdivmod_rel pdivmod_rel_unique prod.sel)

lemma pdivmod_via_pseudo_divmod: "pdivmod f g = (if g = 0 then (0,f) 
     else let 
       ilc = inverse (coeff g (degree g));       
       h = smult ilc g;
       (q,r) = pseudo_divmod f h
     in (smult ilc q, r))" (is "?l = ?r")
proof (cases "g = 0")
  case False
  def lc \<equiv> "inverse (coeff g (degree g))"
  def h \<equiv> "smult lc g"
  from False have h1: "coeff h (degree h) = 1" and lc: "lc \<noteq> 0" unfolding h_def lc_def by auto
  hence h0: "h \<noteq> 0" by auto
  obtain q r where p: "pseudo_divmod f h = (q,r)" by force
  from False have id: "?r = (smult lc q, r)" 
    unfolding Let_def h_def[symmetric] lc_def[symmetric] p by auto
  from pseudo_divmod[OF h0 p, unfolded h1] 
  have f: "f = h * q + r" and r: "r = 0 \<or> degree r < degree h" by auto
  have "pdivmod_rel f h q r" unfolding pdivmod_rel_def using f r h0 by auto
  hence "pdivmod f h = (q,r)" by (simp add: pdivmod_pdivmodrel)
  hence "pdivmod f g = (smult lc q, r)" 
    unfolding pdivmod_def h_def div_smult_right[OF lc] mod_smult_right[OF lc]
    using lc by auto
  with id show ?thesis by auto
qed (auto simp: pdivmod_def)

lemma pdivmod_via_pseudo_divmod_list: "pdivmod f g = (let 
  cg = coeffs g
  in if cg = [] then (0,f)
     else let 
       cf = coeffs f;
       ilc = inverse (last cg);       
       ch = map (op * ilc) cg;
       (q,r) = pseudo_divmod_main_list 1 [] (rev cf) (rev ch) (1 + length cf - length cg)
     in (Poly (map (op * ilc) q), Poly (rev r)))"
proof -
  note d = pdivmod_via_pseudo_divmod
      pseudo_divmod_impl pseudo_divmod_list_def
  show ?thesis
  proof (cases "g = 0")
    case True thus ?thesis unfolding d by auto
  next
    case False
    def ilc \<equiv> "inverse (coeff g (degree g))"
    from False have ilc: "ilc \<noteq> 0" unfolding ilc_def by auto
    with False have id: "(g = 0) = False" "(coeffs g = []) = False" 
      "last (coeffs g) = coeff g (degree g)" 
      "(coeffs (smult ilc g) = []) = False"
      by (auto simp: last_coeffs_eq_coeff_degree) 
    have id2: "hd (rev (coeffs (smult ilc g))) = 1"      
      by (subst hd_rev, insert id ilc, auto simp: coeffs_smult, subst last_map, auto simp: id ilc_def)
    have id3: "length (coeffs (smult ilc g)) = length (coeffs g)" 
      "rev (coeffs (smult ilc g)) = rev (map (op * ilc) (coeffs g))" unfolding coeffs_smult using ilc by auto
    obtain q r where pair: "pseudo_divmod_main_list 1 [] (rev (coeffs f)) (rev (map (op * ilc) (coeffs g)))
           (1 + length (coeffs f) - length (coeffs g)) = (q,r)" by force
    show ?thesis unfolding d Let_def id if_False ilc_def[symmetric] map_prod_def[symmetric] id2 
      unfolding id3 pair map_prod_def split by (auto simp: Poly_map)
  qed
qed

lemma pseudo_divmod_main_list_1: "pseudo_divmod_main_list 1 = divmod_poly_one_main_list"
proof (intro ext, goal_cases)
  case (1 q r d n)
  {
    fix xs :: "'a list"
    have "map (op * 1) xs = xs" by (induct xs, auto)
  } note [simp] = this
  show ?case by (induct n arbitrary: q r d, auto simp: Let_def)
qed

fun divide_poly_main_list :: "'a::idom_divide \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list 
  \<Rightarrow> nat \<Rightarrow> 'a list" where
  "divide_poly_main_list lc q r d (Suc n) = (let
     cr = hd r
     in if cr = 0 then divide_poly_main_list lc (cCons cr q) (tl r) d n else let 
     a = cr div lc;
     qq = cCons a q;
     rr = minus_poly_rev_list r (map (op * a) d)
     in if hd rr = 0 then divide_poly_main_list lc qq (tl rr) d n else [])"
| "divide_poly_main_list lc q r d 0 = q"


lemma divide_poly_main_list_simp[simp]: "divide_poly_main_list lc q r d (Suc n) = (let
     cr = hd r;
     a = cr div lc;
     qq = cCons a q;
     rr = minus_poly_rev_list r (map (op * a) d)
     in if hd rr = 0 then divide_poly_main_list lc qq (tl rr) d n else [])"
  by (simp add: Let_def minus_zero_does_nothing)

declare divide_poly_main_list.simps(1)[simp del]

definition divide_poly_list :: "'a::idom_divide poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "divide_poly_list f g =
    (let cg = coeffs g
     in if cg = [] then g
        else let cf = coeffs f; cgr = rev cg
          in poly_of_list (divide_poly_main_list (hd cgr) [] (rev cf) cgr (1 + length cf - length cg)))"

lemmas pdivmod_via_divmod_list[code] = pdivmod_via_pseudo_divmod_list[unfolded pseudo_divmod_main_list_1]

lemma mod_poly_one_main_list: "snd (divmod_poly_one_main_list q r d n) = mod_poly_one_main_list r d n"
  by  (induct n arbitrary: q r d, auto simp: Let_def)

lemma mod_poly_code[code]: "f mod g =
    (let cg = coeffs g
     in if cg = [] then f
        else let cf = coeffs f; ilc = inverse (last cg); ch = map (op * ilc) cg;
                 r = mod_poly_one_main_list (rev cf) (rev ch) (1 + length cf - length cg)
             in poly_of_list (rev r))" (is "?l = ?r")
proof -
  have "?l = snd (pdivmod f g)" unfolding pdivmod_def by simp
  also have "\<dots> = ?r" unfolding pdivmod_via_divmod_list Let_def
     mod_poly_one_main_list[symmetric, of _ _ _ Nil] by (auto split: prod.splits)
  finally show ?thesis .
qed

definition div_field_poly_impl :: "'a :: field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where 
  "div_field_poly_impl f g = (
    let cg = coeffs g
      in if cg = [] then 0
        else let cf = coeffs f; ilc = inverse (last cg); ch = map (op * ilc) cg;
                 q = fst (divmod_poly_one_main_list [] (rev cf) (rev ch) (1 + length cf - length cg))
             in poly_of_list ((map (op * ilc) q)))"

text \<open>We do not declare the following lemma as code equation, since then polynomial division 
  on non-fields will no longer be executable. However, a code-unfold is possible, since 
  div_field_poly_impl is a bit more efficient than the generic polynomial division.\<close>
lemma div_field_poly_impl[code_unfold]: "op div = div_field_poly_impl"
proof (intro ext)
  fix f g :: "'a poly"
  have "f div g = fst (pdivmod f g)" unfolding pdivmod_def by simp
  also have "\<dots> = div_field_poly_impl f g" unfolding 
    div_field_poly_impl_def pdivmod_via_divmod_list Let_def by (auto split: prod.splits)
  finally show "f div g =  div_field_poly_impl f g" .
qed


lemma divide_poly_main_list:
  assumes lc0: "lc \<noteq> 0"
  and lc:"last d = lc"
  and d:"d \<noteq> []"
  and "n = (1 + length r - length d)"
  shows 
  "Poly (divide_poly_main_list lc q (rev r) (rev d) n) =
  divide_poly_main lc (monom 1 n * Poly q) (Poly r) (Poly d) (length r - 1) n"
using assms(4-)
proof(induct "n" arbitrary: r q)
case (Suc n r q)
  have ifCond: "\<not> Suc (length r) \<le> length d" using Suc.prems by simp
  have r: "r \<noteq> []"
    using ifCond d using Suc_leI length_greater_0_conv list.size(3) by fastforce
  then obtain rr lcr where r: "r = rr @ [lcr]" by (cases r rule: rev_cases, auto)
  from d lc obtain dd where d: "d = dd @ [lc]" 
    by (cases d rule: rev_cases, auto)
  from Suc(2) ifCond have n: "n = 1 + length rr - length d" by (auto simp: r)
  from ifCond have len: "length dd \<le> length rr" by (simp add: r d)
  show ?case
  proof (cases "lcr div lc * lc = lcr")
    case False
    thus ?thesis unfolding Suc(2)[symmetric] using r d
      by (auto simp add: Let_def nth_default_append)
  next
    case True
    hence id:
    "?thesis = (Poly (divide_poly_main_list lc (cCons (lcr div lc) q)
         (rev (rev (minus_poly_rev_list (rev rr) (rev (map (op * (lcr div lc)) dd))))) (rev d) n) = 
      divide_poly_main lc
           (monom 1 (Suc n) * Poly q + monom (lcr div lc) n)
           (Poly r - monom (lcr div lc) n * Poly d)
           (Poly d) (length rr - 1) n)"
           using r d 
      by (cases r rule: rev_cases; cases "d" rule: rev_cases; 
        auto simp add: Let_def rev_map nth_default_append)      
    have cong: "\<And> x1 x2 x3 x4 y1 y2 y3 y4. x1 = y1 \<Longrightarrow> x2 = y2 \<Longrightarrow> x3 = y3 \<Longrightarrow> x4 = y4 \<Longrightarrow>
      divide_poly_main lc x1 x2 x3 x4 n = divide_poly_main lc y1 y2 y3 y4 n" by simp
    show ?thesis unfolding id 
    proof (subst Suc(1), simp add: n,
      subst minus_poly_rev_list, force simp: len, rule cong[OF _ _ refl], goal_cases)
      case 2 
      have "monom lcr (length rr) = monom (lcr div lc) (length rr - length dd) * monom lc (length dd)"
        by (simp add: mult_monom len True)
      thus ?case unfolding r d Poly_append n ring_distribs
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
    show ?thesis unfolding d True by auto
  next
    case False
    then obtain cg lcg where cg: "coeffs g = cg @ [lcg]" by (cases "coeffs g" rule: rev_cases, auto)    
    with False have id: "(g = 0) = False" "(cg @ [lcg] = []) = False" by auto
    from cg False have lcg: "coeff g (degree g) = lcg" 
      using last_coeffs_eq_coeff_degree last_snoc by force
    with False have lcg0: "lcg \<noteq> 0" by auto
    from cg have ltp: "Poly (cg @ [lcg]) = g"
     using Poly_coeffs [of g] by auto
    show ?thesis unfolding d cg Let_def id if_False poly_of_list_def
      by (subst divide_poly_main_list, insert False cg lcg0, auto simp: lcg ltp,
      simp add: degree_eq_length_coeffs)
  qed
qed

subsection \<open>Order of polynomial roots\<close>

definition order :: "'a::idom \<Rightarrow> 'a poly \<Rightarrow> nat"
where
  "order a p = (LEAST n. \<not> [:-a, 1:] ^ Suc n dvd p)"

lemma coeff_linear_power:
  fixes a :: "'a::comm_semiring_1"
  shows "coeff ([:a, 1:] ^ n) n = 1"
apply (induct n, simp_all)
apply (subst coeff_eq_0)
apply (auto intro: le_less_trans degree_power_le)
done

lemma degree_linear_power:
  fixes a :: "'a::comm_semiring_1"
  shows "degree ([:a, 1:] ^ n) = n"
apply (rule order_antisym)
apply (rule ord_le_eq_trans [OF degree_power_le], simp)
apply (rule le_degree, simp add: coeff_linear_power)
done

lemma order_1: "[:-a, 1:] ^ order a p dvd p"
apply (cases "p = 0", simp)
apply (cases "order a p", simp)
apply (subgoal_tac "nat < (LEAST n. \<not> [:-a, 1:] ^ Suc n dvd p)")
apply (drule not_less_Least, simp)
apply (fold order_def, simp)
done

lemma order_2: "p \<noteq> 0 \<Longrightarrow> \<not> [:-a, 1:] ^ Suc (order a p) dvd p"
unfolding order_def
apply (rule LeastI_ex)
apply (rule_tac x="degree p" in exI)
apply (rule notI)
apply (drule (1) dvd_imp_degree_le)
apply (simp only: degree_linear_power)
done

lemma order:
  "p \<noteq> 0 \<Longrightarrow> [:-a, 1:] ^ order a p dvd p \<and> \<not> [:-a, 1:] ^ Suc (order a p) dvd p"
by (rule conjI [OF order_1 order_2])

lemma order_degree:
  assumes p: "p \<noteq> 0"
  shows "order a p \<le> degree p"
proof -
  have "order a p = degree ([:-a, 1:] ^ order a p)"
    by (simp only: degree_linear_power)
  also have "\<dots> \<le> degree p"
    using order_1 p by (rule dvd_imp_degree_le)
  finally show ?thesis .
qed

lemma order_root: "poly p a = 0 \<longleftrightarrow> p = 0 \<or> order a p \<noteq> 0"
apply (cases "p = 0", simp_all)
apply (rule iffI)
apply (metis order_2 not_gr0 poly_eq_0_iff_dvd power_0 power_Suc_0 power_one_right)
unfolding poly_eq_0_iff_dvd
apply (metis dvd_power dvd_trans order_1)
done

lemma order_0I: "poly p a \<noteq> 0 \<Longrightarrow> order a p = 0"
  by (subst (asm) order_root) auto


subsection \<open>Additional induction rules on polynomials\<close>

text \<open>
  An induction rule for induction over the roots of a polynomial with a certain property. 
  (e.g. all positive roots)
\<close>
lemma poly_root_induct [case_names 0 no_roots root]:
  fixes p :: "'a :: idom poly"
  assumes "Q 0"
  assumes "\<And>p. (\<And>a. P a \<Longrightarrow> poly p a \<noteq> 0) \<Longrightarrow> Q p"
  assumes "\<And>a p. P a \<Longrightarrow> Q p \<Longrightarrow> Q ([:a, -1:] * p)"
  shows   "Q p"
proof (induction "degree p" arbitrary: p rule: less_induct)
  case (less p)
  show ?case
  proof (cases "p = 0")
    assume nz: "p \<noteq> 0"
    show ?case
    proof (cases "\<exists>a. P a \<and> poly p a = 0")
      case False
      thus ?thesis by (intro assms(2)) blast
    next
      case True
      then obtain a where a: "P a" "poly p a = 0" 
        by blast
      hence "-[:-a, 1:] dvd p" 
        by (subst minus_dvd_iff) (simp add: poly_eq_0_iff_dvd)
      then obtain q where q: "p = [:a, -1:] * q" by (elim dvdE) simp
      with nz have q_nz: "q \<noteq> 0" by auto
      have "degree p = Suc (degree q)"
        by (subst q, subst degree_mult_eq) (simp_all add: q_nz)
      hence "Q q" by (intro less) simp
      from a(1) and this have "Q ([:a, -1:] * q)" 
        by (rule assms(3))
      with q show ?thesis by simp
    qed
  qed (simp add: assms(1))
qed

lemma dropWhile_replicate_append: 
  "dropWhile (op= a) (replicate n a @ ys) = dropWhile (op= a) ys"
  by (induction n) simp_all

lemma Poly_append_replicate_0: "Poly (xs @ replicate n 0) = Poly xs"
  by (subst coeffs_eq_iff) (simp_all add: strip_while_def dropWhile_replicate_append)

text \<open>
  An induction rule for simultaneous induction over two polynomials, 
  prepending one coefficient in each step.
\<close>
lemma poly_induct2 [case_names 0 pCons]:
  assumes "P 0 0" "\<And>a p b q. P p q \<Longrightarrow> P (pCons a p) (pCons b q)"
  shows   "P p q"
proof -
  def n \<equiv> "max (length (coeffs p)) (length (coeffs q))"
  def xs \<equiv> "coeffs p @ (replicate (n - length (coeffs p)) 0)"
  def ys \<equiv> "coeffs q @ (replicate (n - length (coeffs q)) 0)"
  have "length xs = length ys" 
    by (simp add: xs_def ys_def n_def)
  hence "P (Poly xs) (Poly ys)" 
    by (induction rule: list_induct2) (simp_all add: assms)
  also have "Poly xs = p" 
    by (simp add: xs_def Poly_append_replicate_0)
  also have "Poly ys = q" 
    by (simp add: ys_def Poly_append_replicate_0)
  finally show ?thesis .
qed


subsection \<open>Composition of polynomials\<close>

(* Several lemmas contributed by René Thiemann and Akihisa Yamada *)

definition pcompose :: "'a::comm_semiring_0 poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
where
  "pcompose p q = fold_coeffs (\<lambda>a c. [:a:] + q * c) p 0"

notation pcompose (infixl "\<circ>\<^sub>p" 71)

lemma pcompose_0 [simp]:
  "pcompose 0 q = 0"
  by (simp add: pcompose_def)
  
lemma pcompose_pCons:
  "pcompose (pCons a p) q = [:a:] + q * pcompose p q"
  by (cases "p = 0 \<and> a = 0") (auto simp add: pcompose_def)

lemma pcompose_1:
  fixes p :: "'a :: comm_semiring_1 poly"
  shows "pcompose 1 p = 1"
  unfolding one_poly_def by (auto simp: pcompose_pCons)

lemma poly_pcompose:
  "poly (pcompose p q) x = poly p (poly q x)"
  by (induct p) (simp_all add: pcompose_pCons)

lemma degree_pcompose_le:
  "degree (pcompose p q) \<le> degree p * degree q"
apply (induct p, simp)
apply (simp add: pcompose_pCons, clarify)
apply (rule degree_add_le, simp)
apply (rule order_trans [OF degree_mult_le], simp)
done

lemma pcompose_add:
  fixes p q r :: "'a :: {comm_semiring_0, ab_semigroup_add} poly"
  shows "pcompose (p + q) r = pcompose p r + pcompose q r"
proof (induction p q rule: poly_induct2)
  case (pCons a p b q)
  have "pcompose (pCons a p + pCons b q) r = 
          [:a + b:] + r * pcompose p r + r * pcompose q r"
    by (simp_all add: pcompose_pCons pCons.IH algebra_simps)
  also have "[:a + b:] = [:a:] + [:b:]" by simp
  also have "\<dots> + r * pcompose p r + r * pcompose q r = 
                 pcompose (pCons a p) r + pcompose (pCons b q) r"
    by (simp only: pcompose_pCons add_ac)
  finally show ?case .
qed simp

lemma pcompose_uminus:
  fixes p r :: "'a :: comm_ring poly"
  shows "pcompose (-p) r = -pcompose p r"
  by (induction p) (simp_all add: pcompose_pCons)

lemma pcompose_diff:
  fixes p q r :: "'a :: comm_ring poly"
  shows "pcompose (p - q) r = pcompose p r - pcompose q r"
  using pcompose_add[of p "-q"] by (simp add: pcompose_uminus)

lemma pcompose_smult:
  fixes p r :: "'a :: comm_semiring_0 poly"
  shows "pcompose (smult a p) r = smult a (pcompose p r)"
  by (induction p) 
     (simp_all add: pcompose_pCons pcompose_add smult_add_right)

lemma pcompose_mult:
  fixes p q r :: "'a :: comm_semiring_0 poly"
  shows "pcompose (p * q) r = pcompose p r * pcompose q r"
  by (induction p arbitrary: q)
     (simp_all add: pcompose_add pcompose_smult pcompose_pCons algebra_simps)

lemma pcompose_assoc: 
  "pcompose p (pcompose q r :: 'a :: comm_semiring_0 poly ) =
     pcompose (pcompose p q) r"
  by (induction p arbitrary: q) 
     (simp_all add: pcompose_pCons pcompose_add pcompose_mult)

lemma pcompose_idR[simp]:
  fixes p :: "'a :: comm_semiring_1 poly"
  shows "pcompose p [: 0, 1 :] = p"
  by (induct p; simp add: pcompose_pCons)


(* The remainder of this section and the next were contributed by Wenda Li *)

lemma degree_mult_eq_0:
  fixes p q:: "'a :: semidom poly"
  shows "degree (p*q) = 0 \<longleftrightarrow> p=0 \<or> q=0 \<or> (p\<noteq>0 \<and> q\<noteq>0 \<and> degree p =0 \<and> degree q =0)"
by (auto simp add:degree_mult_eq)

lemma pcompose_const[simp]:"pcompose [:a:] q = [:a:]" by (subst pcompose_pCons,simp) 

lemma pcompose_0': "pcompose p 0 = [:coeff p 0:]"
  by (induct p) (auto simp add:pcompose_pCons)

lemma degree_pcompose:
  fixes p q:: "'a::semidom poly"
  shows "degree (pcompose p q) = degree p * degree q"
proof (induct p)
  case 0
  thus ?case by auto
next
  case (pCons a p)
  have "degree (q * pcompose p q) = 0 \<Longrightarrow> ?case" 
    proof (cases "p=0")
      case True
      thus ?thesis by auto
    next
      case False assume "degree (q * pcompose p q) = 0"
      hence "degree q=0 \<or> pcompose p q=0" by (auto simp add: degree_mult_eq_0)
      moreover have "\<lbrakk>pcompose p q=0;degree q\<noteq>0\<rbrakk> \<Longrightarrow> False" using pCons.hyps(2) \<open>p\<noteq>0\<close> 
        proof -
          assume "pcompose p q=0" "degree q\<noteq>0"
          hence "degree p=0" using pCons.hyps(2) by auto
          then obtain a1 where "p=[:a1:]"
            by (metis degree_pCons_eq_if old.nat.distinct(2) pCons_cases)
          thus False using \<open>pcompose p q=0\<close> \<open>p\<noteq>0\<close> by auto
        qed
      ultimately have "degree (pCons a p) * degree q=0" by auto
      moreover have "degree (pcompose (pCons a p) q) = 0" 
        proof -
          have" 0 = max (degree [:a:]) (degree (q*pcompose p q))"
            using \<open>degree (q * pcompose p q) = 0\<close> by simp
          also have "... \<ge> degree ([:a:] + q * pcompose p q)"
            by (rule degree_add_le_max)
          finally show ?thesis by (auto simp add:pcompose_pCons)
        qed
      ultimately show ?thesis by simp
    qed
  moreover have "degree (q * pcompose p q)>0 \<Longrightarrow> ?case" 
    proof -
      assume asm:"0 < degree (q * pcompose p q)"
      hence "p\<noteq>0" "q\<noteq>0" "pcompose p q\<noteq>0" by auto
      have "degree (pcompose (pCons a p) q) = degree ( q * pcompose p q)"
        unfolding pcompose_pCons
        using degree_add_eq_right[of "[:a:]" ] asm by auto       
      thus ?thesis 
        using pCons.hyps(2) degree_mult_eq[OF \<open>q\<noteq>0\<close> \<open>pcompose p q\<noteq>0\<close>] by auto
    qed
  ultimately show ?case by blast
qed

lemma pcompose_eq_0:
  fixes p q:: "'a :: semidom poly"
  assumes "pcompose p q = 0" "degree q > 0" 
  shows "p = 0"
proof -
  have "degree p=0" using assms degree_pcompose[of p q] by auto
  then obtain a where "p=[:a:]" 
    by (metis degree_pCons_eq_if gr0_conv_Suc neq0_conv pCons_cases)
  hence "a=0" using assms(1) by auto
  thus ?thesis using \<open>p=[:a:]\<close> by simp
qed


subsection \<open>Leading coefficient\<close>

definition lead_coeff:: "'a::zero poly \<Rightarrow> 'a" where
  "lead_coeff p= coeff p (degree p)"

lemma lead_coeff_pCons[simp]:
    "p\<noteq>0 \<Longrightarrow>lead_coeff (pCons a p) = lead_coeff p"
    "p=0 \<Longrightarrow> lead_coeff (pCons a p) = a"
unfolding lead_coeff_def by auto

lemma lead_coeff_0[simp]:"lead_coeff 0 =0" 
  unfolding lead_coeff_def by auto

lemma lead_coeff_mult:
   fixes p q::"'a ::idom poly"
   shows "lead_coeff (p * q) = lead_coeff p * lead_coeff q"
by (unfold lead_coeff_def,cases "p=0 \<or> q=0",auto simp add:coeff_mult_degree_sum degree_mult_eq)

lemma lead_coeff_add_le:
  assumes "degree p < degree q"
  shows "lead_coeff (p+q) = lead_coeff q" 
using assms unfolding lead_coeff_def
by (metis coeff_add coeff_eq_0 monoid_add_class.add.left_neutral degree_add_eq_right)

lemma lead_coeff_minus:
  "lead_coeff (-p) = - lead_coeff p"
by (metis coeff_minus degree_minus lead_coeff_def)


lemma lead_coeff_comp:
  fixes p q:: "'a::idom poly"
  assumes "degree q > 0" 
  shows "lead_coeff (pcompose p q) = lead_coeff p * lead_coeff q ^ (degree p)"
proof (induct p)
  case 0
  thus ?case unfolding lead_coeff_def by auto
next
  case (pCons a p)
  have "degree ( q * pcompose p q) = 0 \<Longrightarrow> ?case"
    proof -
      assume "degree ( q * pcompose p q) = 0"
      hence "pcompose p q = 0" by (metis assms degree_0 degree_mult_eq_0 neq0_conv)
      hence "p=0" using pcompose_eq_0[OF _ \<open>degree q > 0\<close>] by simp
      thus ?thesis by auto
    qed
  moreover have "degree ( q * pcompose p q) > 0 \<Longrightarrow> ?case" 
    proof -
      assume "degree ( q * pcompose p q) > 0"
      hence "lead_coeff (pcompose (pCons a p) q) =lead_coeff ( q * pcompose p q)"
        by (auto simp add:pcompose_pCons lead_coeff_add_le)
      also have "... = lead_coeff q * (lead_coeff p * lead_coeff q ^ degree p)"
        using pCons.hyps(2) lead_coeff_mult[of q "pcompose p q"] by simp
      also have "... = lead_coeff p * lead_coeff q ^ (degree p + 1)"
        by auto
      finally show ?thesis by auto
    qed
  ultimately show ?case by blast
qed

lemma lead_coeff_smult: 
  "lead_coeff (smult c p :: 'a :: idom poly) = c * lead_coeff p"
proof -
  have "smult c p = [:c:] * p" by simp
  also have "lead_coeff \<dots> = c * lead_coeff p" 
    by (subst lead_coeff_mult) simp_all
  finally show ?thesis .
qed

lemma lead_coeff_1 [simp]: "lead_coeff 1 = 1"
  by (simp add: lead_coeff_def)

lemma lead_coeff_of_nat [simp]:
  "lead_coeff (of_nat n) = (of_nat n :: 'a :: {comm_semiring_1,semiring_char_0})"
  by (induction n) (simp_all add: lead_coeff_def of_nat_poly)

lemma lead_coeff_numeral [simp]: 
  "lead_coeff (numeral n) = numeral n"
  unfolding lead_coeff_def
  by (subst of_nat_numeral [symmetric], subst of_nat_poly) simp

lemma lead_coeff_power: 
  "lead_coeff (p ^ n :: 'a :: idom poly) = lead_coeff p ^ n"
  by (induction n) (simp_all add: lead_coeff_mult)

lemma lead_coeff_nonzero: "p \<noteq> 0 \<Longrightarrow> lead_coeff p \<noteq> 0"
  by (simp add: lead_coeff_def)


subsection \<open>Derivatives of univariate polynomials\<close>

function pderiv :: "('a :: semidom) poly \<Rightarrow> 'a poly"
where
  "pderiv (pCons a p) = (if p = 0 then 0 else p + pCons 0 (pderiv p))"
  by (auto intro: pCons_cases)

termination pderiv
  by (relation "measure degree") simp_all

declare pderiv.simps[simp del]

lemma pderiv_0 [simp]:
  "pderiv 0 = 0"
  using pderiv.simps [of 0 0] by simp

lemma pderiv_pCons:
  "pderiv (pCons a p) = p + pCons 0 (pderiv p)"
  by (simp add: pderiv.simps)

lemma pderiv_1 [simp]: "pderiv 1 = 0" 
  unfolding one_poly_def by (simp add: pderiv_pCons)

lemma pderiv_of_nat  [simp]: "pderiv (of_nat n) = 0"
  and pderiv_numeral [simp]: "pderiv (numeral m) = 0"
  by (simp_all add: of_nat_poly numeral_poly pderiv_pCons)

lemma coeff_pderiv: "coeff (pderiv p) n = of_nat (Suc n) * coeff p (Suc n)"
  by (induct p arbitrary: n) 
     (auto simp add: pderiv_pCons coeff_pCons algebra_simps split: nat.split)

fun pderiv_coeffs_code :: "('a :: semidom) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "pderiv_coeffs_code f (x # xs) = cCons (f * x) (pderiv_coeffs_code (f+1) xs)"
| "pderiv_coeffs_code f [] = []"

definition pderiv_coeffs :: "('a :: semidom) list \<Rightarrow> 'a list" where
  "pderiv_coeffs xs = pderiv_coeffs_code 1 (tl xs)"

(* Efficient code for pderiv contributed by René Thiemann and Akihisa Yamada *)
lemma pderiv_coeffs_code: 
  "nth_default 0 (pderiv_coeffs_code f xs) n = (f + of_nat n) * (nth_default 0 xs n)"
proof (induct xs arbitrary: f n)
  case (Cons x xs f n)
  show ?case 
  proof (cases n)
    case 0
    thus ?thesis by (cases "pderiv_coeffs_code (f + 1) xs = [] \<and> f * x = 0", auto simp: cCons_def)
  next
    case (Suc m) note n = this
    show ?thesis 
    proof (cases "pderiv_coeffs_code (f + 1) xs = [] \<and> f * x = 0")
      case False
      hence "nth_default 0 (pderiv_coeffs_code f (x # xs)) n = 
               nth_default 0 (pderiv_coeffs_code (f + 1) xs) m" 
        by (auto simp: cCons_def n)
      also have "\<dots> = (f + of_nat n) * (nth_default 0 xs m)" 
        unfolding Cons by (simp add: n add_ac)
      finally show ?thesis by (simp add: n)
    next
      case True
      {
        fix g 
        have "pderiv_coeffs_code g xs = [] \<Longrightarrow> g + of_nat m = 0 \<or> nth_default 0 xs m = 0"
        proof (induct xs arbitrary: g m)
          case (Cons x xs g)
          from Cons(2) have empty: "pderiv_coeffs_code (g + 1) xs = []"
                            and g: "(g = 0 \<or> x = 0)"
            by (auto simp: cCons_def split: if_splits)
          note IH = Cons(1)[OF empty]
          from IH[of m] IH[of "m - 1"] g
          show ?case by (cases m, auto simp: field_simps)
        qed simp
      } note empty = this
      from True have "nth_default 0 (pderiv_coeffs_code f (x # xs)) n = 0"
        by (auto simp: cCons_def n)
      moreover have "(f + of_nat n) * nth_default 0 (x # xs) n = 0" using True
        by (simp add: n, insert empty[of "f+1"], auto simp: field_simps)
      ultimately show ?thesis by simp
    qed
  qed
qed simp

lemma map_upt_Suc: "map f [0 ..< Suc n] = f 0 # map (\<lambda> i. f (Suc i)) [0 ..< n]"
  by (induct n arbitrary: f, auto)

lemma coeffs_pderiv_code [code abstract]:
  "coeffs (pderiv p) = pderiv_coeffs (coeffs p)" unfolding pderiv_coeffs_def
proof (rule coeffs_eqI, unfold pderiv_coeffs_code coeff_pderiv, goal_cases)
  case (1 n)
  have id: "coeff p (Suc n) = nth_default 0 (map (\<lambda>i. coeff p (Suc i)) [0..<degree p]) n"
    by (cases "n < degree p", auto simp: nth_default_def coeff_eq_0)
  show ?case unfolding coeffs_def map_upt_Suc by (auto simp: id)
next
  case 2
  obtain n xs where id: "tl (coeffs p) = xs" "(1 :: 'a) = n" by auto
  from 2 show ?case
    unfolding id by (induct xs arbitrary: n, auto simp: cCons_def)
qed

context
  assumes "SORT_CONSTRAINT('a::{semidom, semiring_char_0})"
begin

lemma pderiv_eq_0_iff: 
  "pderiv (p :: 'a poly) = 0 \<longleftrightarrow> degree p = 0"
  apply (rule iffI)
  apply (cases p, simp)
  apply (simp add: poly_eq_iff coeff_pderiv del: of_nat_Suc)
  apply (simp add: poly_eq_iff coeff_pderiv coeff_eq_0)
  done

lemma degree_pderiv: "degree (pderiv (p :: 'a poly)) = degree p - 1"
  apply (rule order_antisym [OF degree_le])
  apply (simp add: coeff_pderiv coeff_eq_0)
  apply (cases "degree p", simp)
  apply (rule le_degree)
  apply (simp add: coeff_pderiv del: of_nat_Suc)
  apply (metis degree_0 leading_coeff_0_iff nat.distinct(1))
  done

lemma not_dvd_pderiv: 
  assumes "degree (p :: 'a poly) \<noteq> 0"
  shows "\<not> p dvd pderiv p"
proof
  assume dvd: "p dvd pderiv p"
  then obtain q where p: "pderiv p = p * q" unfolding dvd_def by auto
  from dvd have le: "degree p \<le> degree (pderiv p)"
    by (simp add: assms dvd_imp_degree_le pderiv_eq_0_iff)
  from this[unfolded degree_pderiv] assms show False by auto
qed

lemma dvd_pderiv_iff [simp]: "(p :: 'a poly) dvd pderiv p \<longleftrightarrow> degree p = 0"
  using not_dvd_pderiv[of p] by (auto simp: pderiv_eq_0_iff [symmetric])

end

lemma pderiv_singleton [simp]: "pderiv [:a:] = 0"
by (simp add: pderiv_pCons)

lemma pderiv_add: "pderiv (p + q) = pderiv p + pderiv q"
by (rule poly_eqI, simp add: coeff_pderiv algebra_simps)

lemma pderiv_minus: "pderiv (- p :: 'a :: idom poly) = - pderiv p"
by (rule poly_eqI, simp add: coeff_pderiv algebra_simps)

lemma pderiv_diff: "pderiv (p - q) = pderiv p - pderiv q"
by (rule poly_eqI, simp add: coeff_pderiv algebra_simps)

lemma pderiv_smult: "pderiv (smult a p) = smult a (pderiv p)"
by (rule poly_eqI, simp add: coeff_pderiv algebra_simps)

lemma pderiv_mult: "pderiv (p * q) = p * pderiv q + q * pderiv p"
by (induct p) (auto simp: pderiv_add pderiv_smult pderiv_pCons algebra_simps)

lemma pderiv_power_Suc:
  "pderiv (p ^ Suc n) = smult (of_nat (Suc n)) (p ^ n) * pderiv p"
apply (induct n)
apply simp
apply (subst power_Suc)
apply (subst pderiv_mult)
apply (erule ssubst)
apply (simp only: of_nat_Suc smult_add_left smult_1_left)
apply (simp add: algebra_simps)
done

lemma pderiv_setprod: "pderiv (setprod f (as)) = 
  (\<Sum>a \<in> as. setprod f (as - {a}) * pderiv (f a))"
proof (induct as rule: infinite_finite_induct)
  case (insert a as)
  hence id: "setprod f (insert a as) = f a * setprod f as" 
    "\<And> g. setsum g (insert a as) = g a + setsum g as"
    "insert a as - {a} = as"
    by auto
  {
    fix b
    assume "b \<in> as"
    hence id2: "insert a as - {b} = insert a (as - {b})" using \<open>a \<notin> as\<close> by auto
    have "setprod f (insert a as - {b}) = f a * setprod f (as - {b})"
      unfolding id2
      by (subst setprod.insert, insert insert, auto)
  } note id2 = this
  show ?case
    unfolding id pderiv_mult insert(3) setsum_right_distrib
    by (auto simp add: ac_simps id2 intro!: setsum.cong)
qed auto

lemma DERIV_pow2: "DERIV (%x. x ^ Suc n) x :> real (Suc n) * (x ^ n)"
by (rule DERIV_cong, rule DERIV_pow, simp)
declare DERIV_pow2 [simp] DERIV_pow [simp]

lemma DERIV_add_const: "DERIV f x :> D ==>  DERIV (%x. a + f x :: 'a::real_normed_field) x :> D"
by (rule DERIV_cong, rule DERIV_add, auto)

lemma poly_DERIV [simp]: "DERIV (%x. poly p x) x :> poly (pderiv p) x"
  by (induct p, auto intro!: derivative_eq_intros simp add: pderiv_pCons)

lemma continuous_on_poly [continuous_intros]: 
  fixes p :: "'a :: {real_normed_field} poly"
  assumes "continuous_on A f"
  shows   "continuous_on A (\<lambda>x. poly p (f x))"
proof -
  have "continuous_on A (\<lambda>x. (\<Sum>i\<le>degree p. (f x) ^ i * coeff p i))" 
    by (intro continuous_intros assms)
  also have "\<dots> = (\<lambda>x. poly p (f x))" by (intro ext) (simp add: poly_altdef mult_ac)
  finally show ?thesis .
qed

text\<open>Consequences of the derivative theorem above\<close>

lemma poly_differentiable[simp]: "(%x. poly p x) differentiable (at x::real filter)"
apply (simp add: real_differentiable_def)
apply (blast intro: poly_DERIV)
done

lemma poly_isCont[simp]: "isCont (%x. poly p x) (x::real)"
by (rule poly_DERIV [THEN DERIV_isCont])

lemma poly_IVT_pos: "[| a < b; poly p (a::real) < 0; 0 < poly p b |]
      ==> \<exists>x. a < x & x < b & (poly p x = 0)"
using IVT_objl [of "poly p" a 0 b]
by (auto simp add: order_le_less)

lemma poly_IVT_neg: "[| (a::real) < b; 0 < poly p a; poly p b < 0 |]
      ==> \<exists>x. a < x & x < b & (poly p x = 0)"
by (insert poly_IVT_pos [where p = "- p" ]) simp

lemma poly_IVT:
  fixes p::"real poly"
  assumes "a<b" and "poly p a * poly p b < 0"
  shows "\<exists>x>a. x < b \<and> poly p x = 0"
by (metis assms(1) assms(2) less_not_sym mult_less_0_iff poly_IVT_neg poly_IVT_pos)

lemma poly_MVT: "(a::real) < b ==>
     \<exists>x. a < x & x < b & (poly p b - poly p a = (b - a) * poly (pderiv p) x)"
using MVT [of a b "poly p"]
apply auto
apply (rule_tac x = z in exI)
apply (auto simp add: mult_left_cancel poly_DERIV [THEN DERIV_unique])
done

lemma poly_MVT':
  assumes "{min a b..max a b} \<subseteq> A"
  shows   "\<exists>x\<in>A. poly p b - poly p a = (b - a) * poly (pderiv p) (x::real)"
proof (cases a b rule: linorder_cases)
  case less
  from poly_MVT[OF less, of p] guess x by (elim exE conjE)
  thus ?thesis by (intro bexI[of _ x]) (auto intro!: subsetD[OF assms])

next
  case greater
  from poly_MVT[OF greater, of p] guess x by (elim exE conjE)
  thus ?thesis by (intro bexI[of _ x]) (auto simp: algebra_simps intro!: subsetD[OF assms])
qed (insert assms, auto)

lemma poly_pinfty_gt_lc:
  fixes p:: "real poly"
  assumes  "lead_coeff p > 0" 
  shows "\<exists> n. \<forall> x \<ge> n. poly p x \<ge> lead_coeff p" using assms
proof (induct p)
  case 0
  thus ?case by auto
next
  case (pCons a p)
  have "\<lbrakk>a\<noteq>0;p=0\<rbrakk> \<Longrightarrow> ?case" by auto
  moreover have "p\<noteq>0 \<Longrightarrow> ?case"
    proof -
      assume "p\<noteq>0"
      then obtain n1 where gte_lcoeff:"\<forall>x\<ge>n1. lead_coeff p \<le> poly p x" using that pCons by auto
      have gt_0:"lead_coeff p >0" using pCons(3) \<open>p\<noteq>0\<close> by auto
      def n\<equiv>"max n1 (1+ \<bar>a\<bar>/(lead_coeff p))"
      show ?thesis 
        proof (rule_tac x=n in exI,rule,rule) 
          fix x assume "n \<le> x"
          hence "lead_coeff p \<le> poly p x" 
            using gte_lcoeff unfolding n_def by auto
          hence " \<bar>a\<bar>/(lead_coeff p) \<ge> \<bar>a\<bar>/(poly p x)" and "poly p x>0" using gt_0
            by (intro frac_le,auto)
          hence "x\<ge>1+ \<bar>a\<bar>/(poly p x)" using \<open>n\<le>x\<close>[unfolded n_def] by auto
          thus "lead_coeff (pCons a p) \<le> poly (pCons a p) x"
            using \<open>lead_coeff p \<le> poly p x\<close> \<open>poly p x>0\<close> \<open>p\<noteq>0\<close>
            by (auto simp add:field_simps)
        qed
    qed
  ultimately show ?case by fastforce
qed


subsection \<open>Algebraic numbers\<close>

text \<open>
  Algebraic numbers can be defined in two equivalent ways: all real numbers that are 
  roots of rational polynomials or of integer polynomials. The Algebraic-Numbers AFP entry 
  uses the rational definition, but we need the integer definition.

  The equivalence is obvious since any rational polynomial can be multiplied with the 
  LCM of its coefficients, yielding an integer polynomial with the same roots.
\<close>
subsection \<open>Algebraic numbers\<close>

definition algebraic :: "'a :: field_char_0 \<Rightarrow> bool" where
  "algebraic x \<longleftrightarrow> (\<exists>p. (\<forall>i. coeff p i \<in> \<int>) \<and> p \<noteq> 0 \<and> poly p x = 0)"

lemma algebraicI:
  assumes "\<And>i. coeff p i \<in> \<int>" "p \<noteq> 0" "poly p x = 0"
  shows   "algebraic x"
  using assms unfolding algebraic_def by blast
  
lemma algebraicE:
  assumes "algebraic x"
  obtains p where "\<And>i. coeff p i \<in> \<int>" "p \<noteq> 0" "poly p x = 0"
  using assms unfolding algebraic_def by blast

lemma quotient_of_denom_pos': "snd (quotient_of x) > 0"
  using quotient_of_denom_pos[OF surjective_pairing] .
  
lemma of_int_div_in_Ints: 
  "b dvd a \<Longrightarrow> of_int a div of_int b \<in> (\<int> :: 'a :: ring_div set)"
proof (cases "of_int b = (0 :: 'a)")
  assume "b dvd a" "of_int b \<noteq> (0::'a)"
  then obtain c where "a = b * c" by (elim dvdE)
  with \<open>of_int b \<noteq> (0::'a)\<close> show ?thesis by simp
qed auto

lemma of_int_divide_in_Ints: 
  "b dvd a \<Longrightarrow> of_int a / of_int b \<in> (\<int> :: 'a :: field set)"
proof (cases "of_int b = (0 :: 'a)")
  assume "b dvd a" "of_int b \<noteq> (0::'a)"
  then obtain c where "a = b * c" by (elim dvdE)
  with \<open>of_int b \<noteq> (0::'a)\<close> show ?thesis by simp
qed auto

lemma algebraic_altdef:
  fixes p :: "'a :: field_char_0 poly"
  shows "algebraic x \<longleftrightarrow> (\<exists>p. (\<forall>i. coeff p i \<in> \<rat>) \<and> p \<noteq> 0 \<and> poly p x = 0)"
proof safe
  fix p assume rat: "\<forall>i. coeff p i \<in> \<rat>" and root: "poly p x = 0" and nz: "p \<noteq> 0"
  def cs \<equiv> "coeffs p"
  from rat have "\<forall>c\<in>range (coeff p). \<exists>c'. c = of_rat c'" unfolding Rats_def by blast
  then obtain f where f: "\<And>i. coeff p i = of_rat (f (coeff p i))" 
    by (subst (asm) bchoice_iff) blast
  def cs' \<equiv> "map (quotient_of \<circ> f) (coeffs p)"
  def d \<equiv> "Lcm (set (map snd cs'))"
  def p' \<equiv> "smult (of_int d) p"
  
  have "\<forall>n. coeff p' n \<in> \<int>"
  proof
    fix n :: nat
    show "coeff p' n \<in> \<int>"
    proof (cases "n \<le> degree p")
      case True
      def c \<equiv> "coeff p n"
      def a \<equiv> "fst (quotient_of (f (coeff p n)))" and b \<equiv> "snd (quotient_of (f (coeff p n)))"
      have b_pos: "b > 0" unfolding b_def using quotient_of_denom_pos' by simp
      have "coeff p' n = of_int d * coeff p n" by (simp add: p'_def)
      also have "coeff p n = of_rat (of_int a / of_int b)" unfolding a_def b_def
        by (subst quotient_of_div [of "f (coeff p n)", symmetric])
           (simp_all add: f [symmetric])
      also have "of_int d * \<dots> = of_rat (of_int (a*d) / of_int b)"
        by (simp add: of_rat_mult of_rat_divide)
      also from nz True have "b \<in> snd ` set cs'" unfolding cs'_def
        by (force simp: o_def b_def coeffs_def simp del: upt_Suc)
      hence "b dvd (a * d)" unfolding d_def by simp
      hence "of_int (a * d) / of_int b \<in> (\<int> :: rat set)"
        by (rule of_int_divide_in_Ints)
      hence "of_rat (of_int (a * d) / of_int b) \<in> \<int>" by (elim Ints_cases) auto
      finally show ?thesis .
    qed (auto simp: p'_def not_le coeff_eq_0)
  qed
  
  moreover have "set (map snd cs') \<subseteq> {0<..}"
    unfolding cs'_def using quotient_of_denom_pos' by (auto simp: coeffs_def simp del: upt_Suc) 
  hence "d \<noteq> 0" unfolding d_def by (induction cs') simp_all
  with nz have "p' \<noteq> 0" by (simp add: p'_def)
  moreover from root have "poly p' x = 0" by (simp add: p'_def)
  ultimately show "algebraic x" unfolding algebraic_def by blast
next

  assume "algebraic x"
  then obtain p where p: "\<And>i. coeff p i \<in> \<int>" "poly p x = 0" "p \<noteq> 0" 
    by (force simp: algebraic_def)
  moreover have "coeff p i \<in> \<int> \<Longrightarrow> coeff p i \<in> \<rat>" for i by (elim Ints_cases) simp
  ultimately show  "(\<exists>p. (\<forall>i. coeff p i \<in> \<rat>) \<and> p \<noteq> 0 \<and> poly p x = 0)" by auto
qed


text\<open>Lemmas for Derivatives\<close>

lemma order_unique_lemma:
  fixes p :: "'a::idom poly"
  assumes "[:-a, 1:] ^ n dvd p" "\<not> [:-a, 1:] ^ Suc n dvd p"
  shows "n = order a p"
unfolding Polynomial.order_def
apply (rule Least_equality [symmetric])
apply (fact assms)
apply (rule classical)
apply (erule notE)
unfolding not_less_eq_eq
using assms(1) apply (rule power_le_dvd)
apply assumption
done

lemma lemma_order_pderiv1:
  "pderiv ([:- a, 1:] ^ Suc n * q) = [:- a, 1:] ^ Suc n * pderiv q +
    smult (of_nat (Suc n)) (q * [:- a, 1:] ^ n)"
apply (simp only: pderiv_mult pderiv_power_Suc)
apply (simp del: power_Suc of_nat_Suc add: pderiv_pCons)
done

lemma lemma_order_pderiv:
  fixes p :: "'a :: field_char_0 poly"
  assumes n: "0 < n" 
      and pd: "pderiv p \<noteq> 0" 
      and pe: "p = [:- a, 1:] ^ n * q" 
      and nd: "~ [:- a, 1:] dvd q"
    shows "n = Suc (order a (pderiv p))"
using n 
proof -
  have "pderiv ([:- a, 1:] ^ n * q) \<noteq> 0"
    using assms by auto
  obtain n' where "n = Suc n'" "0 < Suc n'" "pderiv ([:- a, 1:] ^ Suc n' * q) \<noteq> 0"
    using assms by (cases n) auto
  have *: "!!k l. k dvd k * pderiv q + smult (of_nat (Suc n')) l \<Longrightarrow> k dvd l"
    by (auto simp del: of_nat_Suc simp: dvd_add_right_iff dvd_smult_iff)
  have "n' = order a (pderiv ([:- a, 1:] ^ Suc n' * q))" 
  proof (rule order_unique_lemma)
    show "[:- a, 1:] ^ n' dvd pderiv ([:- a, 1:] ^ Suc n' * q)"
      apply (subst lemma_order_pderiv1)
      apply (rule dvd_add)
      apply (metis dvdI dvd_mult2 power_Suc2)
      apply (metis dvd_smult dvd_triv_right)
      done
  next
    show "\<not> [:- a, 1:] ^ Suc n' dvd pderiv ([:- a, 1:] ^ Suc n' * q)"
     apply (subst lemma_order_pderiv1)
     by (metis * nd dvd_mult_cancel_right power_not_zero pCons_eq_0_iff power_Suc zero_neq_one)
  qed
  then show ?thesis
    by (metis \<open>n = Suc n'\<close> pe)
qed

lemma order_decomp:
  assumes "p \<noteq> 0"
  shows "\<exists>q. p = [:- a, 1:] ^ order a p * q \<and> \<not> [:- a, 1:] dvd q"
proof -
  from assms have A: "[:- a, 1:] ^ order a p dvd p"
    and B: "\<not> [:- a, 1:] ^ Suc (order a p) dvd p" by (auto dest: order)
  from A obtain q where C: "p = [:- a, 1:] ^ order a p * q" ..
  with B have "\<not> [:- a, 1:] ^ Suc (order a p) dvd [:- a, 1:] ^ order a p * q"
    by simp
  then have "\<not> [:- a, 1:] ^ order a p * [:- a, 1:] dvd [:- a, 1:] ^ order a p * q"
    by simp
  then have D: "\<not> [:- a, 1:] dvd q"
    using idom_class.dvd_mult_cancel_left [of "[:- a, 1:] ^ order a p" "[:- a, 1:]" q]
    by auto
  from C D show ?thesis by blast
qed

lemma order_pderiv:
  "\<lbrakk>pderiv p \<noteq> 0; order a (p :: 'a :: field_char_0 poly) \<noteq> 0\<rbrakk> \<Longrightarrow>
     (order a p = Suc (order a (pderiv p)))"
apply (case_tac "p = 0", simp)
apply (drule_tac a = a and p = p in order_decomp)
using neq0_conv
apply (blast intro: lemma_order_pderiv)
done

lemma order_mult: "p * q \<noteq> 0 \<Longrightarrow> order a (p * q) = order a p + order a q"
proof -
  def i \<equiv> "order a p"
  def j \<equiv> "order a q"
  def t \<equiv> "[:-a, 1:]"
  have t_dvd_iff: "\<And>u. t dvd u \<longleftrightarrow> poly u a = 0"
    unfolding t_def by (simp add: dvd_iff_poly_eq_0)
  assume "p * q \<noteq> 0"
  then show "order a (p * q) = i + j"
    apply clarsimp
    apply (drule order [where a=a and p=p, folded i_def t_def])
    apply (drule order [where a=a and p=q, folded j_def t_def])
    apply clarify
    apply (erule dvdE)+
    apply (rule order_unique_lemma [symmetric], fold t_def)
    apply (simp_all add: power_add t_dvd_iff)
    done
qed

lemma order_smult:
  assumes "c \<noteq> 0" 
  shows "order x (smult c p) = order x p"
proof (cases "p = 0")
  case False
  have "smult c p = [:c:] * p" by simp
  also from assms False have "order x \<dots> = order x [:c:] + order x p" 
    by (subst order_mult) simp_all
  also from assms have "order x [:c:] = 0" by (intro order_0I) auto
  finally show ?thesis by simp
qed simp

(* Next two lemmas contributed by Wenda Li *)
lemma order_1_eq_0 [simp]:"order x 1 = 0" 
  by (metis order_root poly_1 zero_neq_one)

lemma order_power_n_n: "order a ([:-a,1:]^n)=n" 
proof (induct n) (*might be proved more concisely using nat_less_induct*)
  case 0
  thus ?case by (metis order_root poly_1 power_0 zero_neq_one)
next 
  case (Suc n)
  have "order a ([:- a, 1:] ^ Suc n)=order a ([:- a, 1:] ^ n) + order a [:-a,1:]" 
    by (metis (no_types, hide_lams) One_nat_def add_Suc_right monoid_add_class.add.right_neutral 
      one_neq_zero order_mult pCons_eq_0_iff power_add power_eq_0_iff power_one_right)
  moreover have "order a [:-a,1:]=1" unfolding order_def
    proof (rule Least_equality,rule ccontr)
      assume  "\<not> \<not> [:- a, 1:] ^ Suc 1 dvd [:- a, 1:]"
      hence "[:- a, 1:] ^ Suc 1 dvd [:- a, 1:]" by simp
      hence "degree ([:- a, 1:] ^ Suc 1) \<le> degree ([:- a, 1:] )" 
        by (rule dvd_imp_degree_le,auto) 
      thus False by auto
    next
      fix y assume asm:"\<not> [:- a, 1:] ^ Suc y dvd [:- a, 1:]"
      show "1 \<le> y" 
        proof (rule ccontr)
          assume "\<not> 1 \<le> y"
          hence "y=0" by auto
          hence "[:- a, 1:] ^ Suc y dvd [:- a, 1:]" by auto
          thus False using asm by auto
        qed
    qed
  ultimately show ?case using Suc by auto
qed

text\<open>Now justify the standard squarefree decomposition, i.e. f / gcd(f,f').\<close>

lemma order_divides: "[:-a, 1:] ^ n dvd p \<longleftrightarrow> p = 0 \<or> n \<le> order a p"
apply (cases "p = 0", auto)
apply (drule order_2 [where a=a and p=p])
apply (metis not_less_eq_eq power_le_dvd)
apply (erule power_le_dvd [OF order_1])
done

lemma poly_squarefree_decomp_order:
  assumes "pderiv (p :: 'a :: field_char_0 poly) \<noteq> 0"
  and p: "p = q * d"
  and p': "pderiv p = e * d"
  and d: "d = r * p + s * pderiv p"
  shows "order a q = (if order a p = 0 then 0 else 1)"
proof (rule classical)
  assume 1: "order a q \<noteq> (if order a p = 0 then 0 else 1)"
  from \<open>pderiv p \<noteq> 0\<close> have "p \<noteq> 0" by auto
  with p have "order a p = order a q + order a d"
    by (simp add: order_mult)
  with 1 have "order a p \<noteq> 0" by (auto split: if_splits)
  have "order a (pderiv p) = order a e + order a d"
    using \<open>pderiv p \<noteq> 0\<close> \<open>pderiv p = e * d\<close> by (simp add: order_mult)
  have "order a p = Suc (order a (pderiv p))"
    using \<open>pderiv p \<noteq> 0\<close> \<open>order a p \<noteq> 0\<close> by (rule order_pderiv)
  have "d \<noteq> 0" using \<open>p \<noteq> 0\<close> \<open>p = q * d\<close> by simp
  have "([:-a, 1:] ^ (order a (pderiv p))) dvd d"
    apply (simp add: d)
    apply (rule dvd_add)
    apply (rule dvd_mult)
    apply (simp add: order_divides \<open>p \<noteq> 0\<close>
           \<open>order a p = Suc (order a (pderiv p))\<close>)
    apply (rule dvd_mult)
    apply (simp add: order_divides)
    done
  then have "order a (pderiv p) \<le> order a d"
    using \<open>d \<noteq> 0\<close> by (simp add: order_divides)
  show ?thesis
    using \<open>order a p = order a q + order a d\<close>
    using \<open>order a (pderiv p) = order a e + order a d\<close>
    using \<open>order a p = Suc (order a (pderiv p))\<close>
    using \<open>order a (pderiv p) \<le> order a d\<close>
    by auto
qed

lemma poly_squarefree_decomp_order2: 
     "\<lbrakk>pderiv p \<noteq> (0 :: 'a :: field_char_0 poly);
       p = q * d;
       pderiv p = e * d;
       d = r * p + s * pderiv p
      \<rbrakk> \<Longrightarrow> \<forall>a. order a q = (if order a p = 0 then 0 else 1)"
by (blast intro: poly_squarefree_decomp_order)

lemma order_pderiv2: 
  "\<lbrakk>pderiv p \<noteq> 0; order a (p :: 'a :: field_char_0 poly) \<noteq> 0\<rbrakk>
      \<Longrightarrow> (order a (pderiv p) = n) = (order a p = Suc n)"
by (auto dest: order_pderiv)

definition
  rsquarefree :: "'a::idom poly => bool" where
  "rsquarefree p = (p \<noteq> 0 & (\<forall>a. (order a p = 0) | (order a p = 1)))"

lemma pderiv_iszero: "pderiv p = 0 \<Longrightarrow> \<exists>h. p = [:h :: 'a :: {semidom,semiring_char_0}:]"
apply (simp add: pderiv_eq_0_iff)
apply (case_tac p, auto split: if_splits)
done

lemma rsquarefree_roots:
  fixes p :: "'a :: field_char_0 poly"
  shows "rsquarefree p = (\<forall>a. \<not>(poly p a = 0 \<and> poly (pderiv p) a = 0))"
apply (simp add: rsquarefree_def)
apply (case_tac "p = 0", simp, simp)
apply (case_tac "pderiv p = 0")
apply simp
apply (drule pderiv_iszero, clarsimp)
apply (metis coeff_0 coeff_pCons_0 degree_pCons_0 le0 le_antisym order_degree)
apply (force simp add: order_root order_pderiv2)
done

lemma poly_squarefree_decomp:
  assumes "pderiv (p :: 'a :: field_char_0 poly) \<noteq> 0"
    and "p = q * d"
    and "pderiv p = e * d"
    and "d = r * p + s * pderiv p"
  shows "rsquarefree q & (\<forall>a. (poly q a = 0) = (poly p a = 0))"
proof -
  from \<open>pderiv p \<noteq> 0\<close> have "p \<noteq> 0" by auto
  with \<open>p = q * d\<close> have "q \<noteq> 0" by simp
  have "\<forall>a. order a q = (if order a p = 0 then 0 else 1)"
    using assms by (rule poly_squarefree_decomp_order2)
  with \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> show ?thesis
    by (simp add: rsquarefree_def order_root)
qed


no_notation cCons (infixr "##" 65)

end
