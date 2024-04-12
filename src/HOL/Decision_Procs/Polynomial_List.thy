(*  Title:      HOL/Decision_Procs/Polynomial_List.thy
    Author:     Amine Chaieb
*)

section \<open>Univariate Polynomials as lists\<close>

theory Polynomial_List
  imports Complex_Main 

begin

text \<open>Application of polynomial as a function.\<close>

primrec (in semiring_0) poly :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a"
where
  poly_Nil: "poly [] x = 0"
| poly_Cons: "poly (h # t) x = h + x * poly t x"


subsection \<open>Arithmetic Operations on Polynomials\<close>

text \<open>Addition\<close>
primrec (in semiring_0) padd :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixl \<open>+++\<close> 65)
where
  padd_Nil: "[] +++ l2 = l2"
| padd_Cons: "(h # t) +++ l2 = (if l2 = [] then h # t else (h + hd l2) # (t +++ tl l2))"

text \<open>Multiplication by a constant\<close>
primrec (in semiring_0) cmult :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixl \<open>%*\<close> 70) where
  cmult_Nil: "c %* [] = []"
| cmult_Cons: "c %* (h#t) = (c * h)#(c %* t)"

text \<open>Multiplication by a polynomial\<close>
primrec (in semiring_0) pmult :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixl \<open>***\<close> 70)
where
  pmult_Nil: "[] *** l2 = []"
| pmult_Cons: "(h # t) *** l2 = (if t = [] then h %* l2 else (h %* l2) +++ (0 # (t *** l2)))"

text \<open>Repeated multiplication by a polynomial\<close>
primrec (in semiring_0) mulexp :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a  list \<Rightarrow> 'a list"
where
  mulexp_zero: "mulexp 0 p q = q"
| mulexp_Suc: "mulexp (Suc n) p q = p *** mulexp n p q"

text \<open>Exponential\<close>
primrec (in semiring_1) pexp :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list"  (infixl \<open>%^\<close> 80)
where
  pexp_0: "p %^ 0 = [1]"
| pexp_Suc: "p %^ (Suc n) = p *** (p %^ n)"

text \<open>Quotient related value of dividing a polynomial by x + a.
  Useful for divisor properties in inductive proofs.\<close>
primrec (in field) "pquot" :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
where
  pquot_Nil: "pquot [] a = []"
| pquot_Cons: "pquot (h # t) a =
    (if t = [] then [h] else (inverse a * (h - hd( pquot t a))) # pquot t a)"

text \<open>Normalization of polynomials (remove extra 0 coeff).\<close>
primrec (in semiring_0) pnormalize :: "'a list \<Rightarrow> 'a list"
where
  pnormalize_Nil: "pnormalize [] = []"
| pnormalize_Cons: "pnormalize (h # p) =
    (if pnormalize p = [] then (if h = 0 then [] else [h]) else h # pnormalize p)"

definition (in semiring_0) "pnormal p \<longleftrightarrow> pnormalize p = p \<and> p \<noteq> []"
definition (in semiring_0) "nonconstant p \<longleftrightarrow> pnormal p \<and> (\<forall>x. p \<noteq> [x])"

text \<open>Other definitions.\<close>

definition (in ring_1) poly_minus :: "'a list \<Rightarrow> 'a list" (\<open>-- _\<close> [80] 80)
  where "-- p = (- 1) %* p"

definition (in semiring_0) divides :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"  (infixl \<open>divides\<close> 70)
  where "p1 divides p2 \<longleftrightarrow> (\<exists>q. poly p2 = poly(p1 *** q))"

lemma (in semiring_0) dividesI: "poly p2 = poly (p1 *** q) \<Longrightarrow> p1 divides p2"
  by (auto simp add: divides_def)

lemma (in semiring_0) dividesE:
  assumes "p1 divides p2"
  obtains q where "poly p2 = poly (p1 *** q)"
  using assms by (auto simp add: divides_def)

\<comment> \<open>order of a polynomial\<close>
definition (in ring_1) order :: "'a \<Rightarrow> 'a list \<Rightarrow> nat"
  where "order a p = (SOME n. ([-a, 1] %^ n) divides p \<and> \<not> (([-a, 1] %^ (Suc n)) divides p))"

\<comment> \<open>degree of a polynomial\<close>
definition (in semiring_0) degree :: "'a list \<Rightarrow> nat"
  where "degree p = length (pnormalize p) - 1"

\<comment> \<open>squarefree polynomials --- NB with respect to real roots only\<close>
definition (in ring_1) rsquarefree :: "'a list \<Rightarrow> bool"
  where "rsquarefree p \<longleftrightarrow> poly p \<noteq> poly [] \<and> (\<forall>a. order a p = 0 \<or> order a p = 1)"

context semiring_0
begin

lemma padd_Nil2[simp]: "p +++ [] = p"
  by (induct p) auto

lemma padd_Cons_Cons: "(h1 # p1) +++ (h2 # p2) = (h1 + h2) # (p1 +++ p2)"
  by auto

lemma pminus_Nil: "-- [] = []"
  by (simp add: poly_minus_def)

lemma pmult_singleton: "[h1] *** p1 = h1 %* p1" by simp

end

lemma (in semiring_1) poly_ident_mult[simp]: "1 %* t = t"
  by (induct t) auto

lemma (in semiring_0) poly_simple_add_Cons[simp]: "[a] +++ (0 # t) = a # t"
  by simp


text \<open>Handy general properties.\<close>

lemma (in comm_semiring_0) padd_commut: "b +++ a = a +++ b"
proof (induct b arbitrary: a)
  case Nil
  then show ?case
    by auto
next
  case (Cons b bs a)
  then show ?case
    by (cases a) (simp_all add: add.commute)
qed

lemma (in comm_semiring_0) padd_assoc: "(a +++ b) +++ c = a +++ (b +++ c)"
proof (induct a arbitrary: b c)
  case Nil
  then show ?case
    by simp
next
  case Cons
  then show ?case
    by (cases b) (simp_all add: ac_simps)
qed

lemma (in semiring_0) poly_cmult_distr: "a %* (p +++ q) = a %* p +++ a %* q"
proof (induct p arbitrary: q)
  case Nil
  then show ?case
    by simp
next
  case Cons
  then show ?case
    by (cases q) (simp_all add: distrib_left)
qed

lemma (in ring_1) pmult_by_x[simp]: "[0, 1] *** t = 0 # t"
proof (induct t)
  case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  then show ?case
    by (cases t) (auto simp add: padd_commut)
qed

text \<open>Properties of evaluation of polynomials.\<close>

lemma (in semiring_0) poly_add: "poly (p1 +++ p2) x = poly p1 x + poly p2 x"
proof (induct p1 arbitrary: p2)
  case Nil
  then show ?case
    by simp
next
  case (Cons a as p2)
  then show ?case
    by (cases p2) (simp_all add: ac_simps distrib_left)
qed

lemma (in comm_semiring_0) poly_cmult: "poly (c %* p) x = c * poly p x"
proof (induct p)
  case Nil
  then show ?case
    by simp
next
  case Cons
  then show ?case
    by (cases "x = zero") (auto simp add: distrib_left ac_simps)
qed

lemma (in comm_semiring_0) poly_cmult_map: "poly (map ((*) c) p) x = c * poly p x"
  by (induct p) (auto simp add: distrib_left ac_simps)

lemma (in comm_ring_1) poly_minus: "poly (-- p) x = - (poly p x)"
  by (simp add: poly_minus_def) (auto simp add: poly_cmult)

lemma (in comm_semiring_0) poly_mult: "poly (p1 *** p2) x = poly p1 x * poly p2 x"
proof (induct p1 arbitrary: p2)
  case Nil
  then show ?case
    by simp
next
  case (Cons a as)
  then show ?case
    by (cases as) (simp_all add: poly_cmult poly_add distrib_right distrib_left ac_simps)
qed

class idom_char_0 = idom + ring_char_0

subclass (in field_char_0) idom_char_0 ..

lemma (in comm_ring_1) poly_exp: "poly (p %^ n) x = (poly p x) ^ n"
  by (induct n) (auto simp add: poly_cmult poly_mult)


text \<open>More Polynomial Evaluation lemmas.\<close>

lemma (in semiring_0) poly_add_rzero[simp]: "poly (a +++ []) x = poly a x"
  by simp

lemma (in comm_semiring_0) poly_mult_assoc: "poly ((a *** b) *** c) x = poly (a *** (b *** c)) x"
  by (simp add: poly_mult mult.assoc)

lemma (in semiring_0) poly_mult_Nil2[simp]: "poly (p *** []) x = 0"
  by (induct p) auto

lemma (in comm_semiring_1) poly_exp_add: "poly (p %^ (n + d)) x = poly (p %^ n *** p %^ d) x"
  by (induct n) (auto simp add: poly_mult mult.assoc)


subsection \<open>Key Property: if \<^term>\<open>f a = 0\<close> then \<^term>\<open>(x - a)\<close> divides \<^term>\<open>p(x)\<close>.\<close>

lemma (in comm_ring_1) lemma_poly_linear_rem: "\<exists>q r. h#t = [r] +++ [-a, 1] *** q"
proof (induct t arbitrary: h)
  case Nil
  have "[h] = [h] +++ [- a, 1] *** []" by simp
  then show ?case by blast
next
  case (Cons  x xs)
  have "\<exists>q r. h # x # xs = [r] +++ [-a, 1] *** q"
  proof -
    from Cons obtain q r where qr: "x # xs = [r] +++ [- a, 1] *** q"
      by blast
    have "h # x # xs = [a * r + h] +++ [-a, 1] *** (r # q)"
      using qr by (cases q) (simp_all add: algebra_simps)
    then show ?thesis by blast
  qed
  then show ?case by blast
qed

lemma (in comm_ring_1) poly_linear_rem: "\<exists>q r. h#t = [r] +++ [-a, 1] *** q"
  using lemma_poly_linear_rem [where t = t and a = a] by auto

lemma (in comm_ring_1) poly_linear_divides: "poly p a = 0 \<longleftrightarrow> p = [] \<or> (\<exists>q. p = [-a, 1] *** q)"
proof (cases p)
  case Nil
  then show ?thesis by simp
next
  case (Cons x xs)
  have "poly p a = 0" if "p = [-a, 1] *** q" for q
    using that by (simp add: poly_add poly_cmult)
  moreover
  have "\<exists>q. p = [- a, 1] *** q" if p0: "poly p a = 0"
  proof -
    from poly_linear_rem[of x xs a] obtain q r where qr: "x#xs = [r] +++ [- a, 1] *** q"
      by blast
    have "r = 0"
      using p0 by (simp only: Cons qr poly_mult poly_add) simp
    with Cons qr have "p = [- a, 1] *** q"
      by (simp add: local.padd_commut)
    then show ?thesis ..
  qed
  ultimately show ?thesis using Cons by blast
qed

lemma (in semiring_0) lemma_poly_length_mult[simp]:
  "length (k %* p +++  (h # (a %* p))) = Suc (length p)"
  by (induct p arbitrary: h k a) auto

lemma (in semiring_0) lemma_poly_length_mult2[simp]:
  "length (k %* p +++  (h # p)) = Suc (length p)"
  by (induct p arbitrary: h k) auto

lemma (in ring_1) poly_length_mult[simp]: "length([-a,1] *** q) = Suc (length q)"
  by auto


subsection \<open>Polynomial length\<close>

lemma (in semiring_0) poly_cmult_length[simp]: "length (a %* p) = length p"
  by (induct p) auto

lemma (in semiring_0) poly_add_length: "length (p1 +++ p2) = max (length p1) (length p2)"
  by (induct p1 arbitrary: p2) auto

lemma (in semiring_0) poly_root_mult_length[simp]: "length ([a, b] *** p) = Suc (length p)"
  by (simp add: poly_add_length)

lemma (in idom) poly_mult_not_eq_poly_Nil[simp]:
  "poly (p *** q) x \<noteq> poly [] x \<longleftrightarrow> poly p x \<noteq> poly [] x \<and> poly q x \<noteq> poly [] x"
  by (auto simp add: poly_mult)

lemma (in idom) poly_mult_eq_zero_disj: "poly (p *** q) x = 0 \<longleftrightarrow> poly p x = 0 \<or> poly q x = 0"
  by (auto simp add: poly_mult)


text \<open>Normalisation Properties.\<close>

lemma (in semiring_0) poly_normalized_nil: "pnormalize p = [] \<longrightarrow> poly p x = 0"
  by (induct p) auto

text \<open>A nontrivial polynomial of degree n has no more than n roots.\<close>
lemma (in idom) poly_roots_index_lemma:
  assumes "poly p x \<noteq> poly [] x"
    and "length p = n"
  shows "\<exists>i. \<forall>x. poly p x = 0 \<longrightarrow> (\<exists>m\<le>n. x = i m)"
  using assms
proof (induct n arbitrary: p x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have False if C: "\<And>i. \<exists>x. poly p x = 0 \<and> (\<forall>m\<le>Suc n. x \<noteq> i m)"
  proof -
    from Suc.prems have p0: "poly p x \<noteq> 0" "p \<noteq> []"
      by auto
    from p0(1)[unfolded poly_linear_divides[of p x]]
    have "\<forall>q. p \<noteq> [- x, 1] *** q"
      by blast
    from C obtain a where a: "poly p a = 0"
      by blast
    from a[unfolded poly_linear_divides[of p a]] p0(2) obtain q where q: "p = [-a, 1] *** q"
      by blast
    have lg: "length q = n"
      using q Suc.prems(2) by simp
    from q p0 have qx: "poly q x \<noteq> poly [] x"
      by (auto simp add: poly_mult poly_add poly_cmult)
    from Suc.hyps[OF qx lg] obtain i where i: "\<And>x. poly q x = 0 \<longrightarrow> (\<exists>m\<le>n. x = i m)"
      by blast
    let ?i = "\<lambda>m. if m = Suc n then a else i m"
    from C[of ?i] obtain y where y: "poly p y = 0" "\<forall>m\<le> Suc n. y \<noteq> ?i m"
      by blast
    from y have "y = a \<or> poly q y = 0"
      by (simp only: q poly_mult_eq_zero_disj poly_add) (simp add: algebra_simps)
    with i[of y] y show ?thesis
      using le_Suc_eq by auto
  qed
  then show ?case by blast
qed


lemma (in idom) poly_roots_index_length:
  "poly p x \<noteq> poly [] x \<Longrightarrow> \<exists>i. \<forall>x. poly p x = 0 \<longrightarrow> (\<exists>n. n \<le> length p \<and> x = i n)"
  by (blast intro: poly_roots_index_lemma)

lemma (in idom) poly_roots_finite_lemma1:
  "poly p x \<noteq> poly [] x \<Longrightarrow> \<exists>N i. \<forall>x. poly p x = 0 \<longrightarrow> (\<exists>n::nat. n < N \<and> x = i n)"
  by (metis le_imp_less_Suc poly_roots_index_length)

lemma (in idom) idom_finite_lemma:
  assumes "\<forall>x. P x \<longrightarrow> (\<exists>n. n < length j \<and> x = j!n)"
  shows "finite {x. P x}"
proof -
  from assms have "{x. P x} \<subseteq> set j"
    by auto
  then show ?thesis
    using finite_subset by auto
qed

lemma (in idom) poly_roots_finite_lemma2:
  "poly p x \<noteq> poly [] x \<Longrightarrow> \<exists>i. \<forall>x. poly p x = 0 \<longrightarrow> x \<in> set i"
  using poly_roots_index_length atMost_iff atMost_upto imageI set_map
  by metis

lemma (in ring_char_0) UNIV_ring_char_0_infinte: "\<not> finite (UNIV :: 'a set)"
proof
  assume F: "finite (UNIV :: 'a set)"
  have "finite (UNIV :: nat set)"
  proof (rule finite_imageD)
    have "of_nat ` UNIV \<subseteq> UNIV"
      by simp
    then show "finite (of_nat ` UNIV :: 'a set)"
      using F by (rule finite_subset)
    show "inj (of_nat :: nat \<Rightarrow> 'a)"
      by (simp add: inj_on_def)
  qed
  with infinite_UNIV_nat show False ..
qed

lemma (in idom_char_0) poly_roots_finite: "poly p \<noteq> poly [] \<longleftrightarrow> finite {x. poly p x = 0}"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if ?lhs
  proof -
    have False if  F: "\<not> finite {x. poly p x = 0}"
      and P: "\<forall>x. poly p x = 0 \<longrightarrow> x \<in> set i" for  i
      by (smt (verit, del_insts) in_set_conv_nth local.idom_finite_lemma that)
    with that show ?thesis
      using local.poly_roots_finite_lemma2 by blast
  qed
  show ?lhs if ?rhs
    using UNIV_ring_char_0_infinte that by auto
qed


text \<open>Entirety and Cancellation for polynomials\<close>

lemma (in idom_char_0) poly_entire_lemma2:
  assumes p0: "poly p \<noteq> poly []"
    and q0: "poly q \<noteq> poly []"
  shows "poly (p***q) \<noteq> poly []"
proof -
  let ?S = "\<lambda>p. {x. poly p x = 0}"
  have "?S (p *** q) = ?S p \<union> ?S q"
    by (auto simp add: poly_mult)
  with p0 q0 show ?thesis
    unfolding poly_roots_finite by auto
qed

lemma (in idom_char_0) poly_entire:
  "poly (p *** q) = poly [] \<longleftrightarrow> poly p = poly [] \<or> poly q = poly []"
  using poly_entire_lemma2[of p q]
  by (auto simp add: fun_eq_iff poly_mult)

lemma (in idom_char_0) poly_entire_neg:
  "poly (p *** q) \<noteq> poly [] \<longleftrightarrow> poly p \<noteq> poly [] \<and> poly q \<noteq> poly []"
  by (simp add: poly_entire)

lemma (in comm_ring_1) poly_add_minus_zero_iff:
  "poly (p +++ -- q) = poly [] \<longleftrightarrow> poly p = poly q"
  by (auto simp add: algebra_simps poly_add poly_minus_def fun_eq_iff poly_cmult)

lemma (in comm_ring_1) poly_add_minus_mult_eq:
  "poly (p *** q +++ --(p *** r)) = poly (p *** (q +++ -- r))"
  by (auto simp add: poly_add poly_minus_def fun_eq_iff poly_mult poly_cmult algebra_simps)

subclass (in idom_char_0) comm_ring_1 ..

lemma (in idom_char_0) poly_mult_left_cancel:
  "poly (p *** q) = poly (p *** r) \<longleftrightarrow> poly p = poly [] \<or> poly q = poly r"
proof -
  have "poly (p *** q) = poly (p *** r) \<longleftrightarrow> poly (p *** q +++ -- (p *** r)) = poly []"
    by (simp only: poly_add_minus_zero_iff)
  also have "\<dots> \<longleftrightarrow> poly p = poly [] \<or> poly q = poly r"
    by (auto intro: simp add: poly_add_minus_mult_eq poly_entire poly_add_minus_zero_iff)
  finally show ?thesis .
qed

lemma (in idom) poly_exp_eq_zero[simp]: "poly (p %^ n) = poly [] \<longleftrightarrow> poly p = poly [] \<and> n \<noteq> 0"
  by (simp add: local.poly_exp fun_eq_iff)

lemma (in comm_ring_1) poly_prime_eq_zero[simp]: "poly [a, 1] \<noteq> poly []"
proof -
  have "\<exists>x. a + x \<noteq> 0"
    by (metis add_cancel_left_right zero_neq_one)
  then show ?thesis
    by (simp add: fun_eq_iff)
qed

lemma (in idom) poly_exp_prime_eq_zero: "poly ([a, 1] %^ n) \<noteq> poly []"
  by auto


text \<open>A more constructive notion of polynomials being trivial.\<close>

lemma (in idom_char_0) poly_zero_lemma': 
  assumes "poly (h # t) = poly []" shows "h = 0 \<and> poly t = poly []"
proof -
  have "poly t x = 0" if H: "\<forall>x. x = 0 \<or> poly t x = 0" and pnz: "poly t \<noteq> poly []" for x
  proof -
    from H have "{x. poly t x = 0} \<supseteq> UNIV - {0}"
      by auto
    then show ?thesis
      using finite_subset local.poly_roots_finite pnz by fastforce
  qed
  with assms show ?thesis
    by (simp add: fun_eq_iff) (metis add_cancel_right_left mult_eq_0_iff)
qed

lemma (in idom_char_0) poly_zero: "poly p = poly [] \<longleftrightarrow> (\<forall>c \<in> set p. c = 0)"
proof (induct p)
  case Nil
  then show ?case by simp
next
  case Cons
  then show ?case
    by (smt (verit) list.set_intros pmult_by_x poly_entire poly_zero_lemma' set_ConsD)
qed

lemma (in idom_char_0) poly_0: "\<forall>c \<in> set p. c = 0 \<Longrightarrow> poly p x = 0"
  unfolding poly_zero[symmetric] by simp


text \<open>Basics of divisibility.\<close>

lemma (in idom) poly_primes: "[a, 1] divides (p *** q) \<longleftrightarrow> [a, 1] divides p \<or> [a, 1] divides q"
proof -
  have "\<exists>q. \<forall>x. poly p x = (a + x) * poly q x"
    if "poly p (uminus a) * poly q (uminus a) = (a + (uminus a)) * poly qa (uminus a)"
      and "\<forall>qa. \<exists>x. poly q x \<noteq> (a + x) * poly qa x"
    for qa 
    using that   
    apply (simp add: poly_linear_divides poly_add)
    by (metis add_cancel_left_right combine_common_factor mult_eq_0_iff poly.poly_Cons poly.poly_Nil poly_add poly_cmult)
  moreover have "\<exists>qb. \<forall>x. (a + x) * poly qa x * poly q x = (a + x) * poly qb x" for qa
    by (metis local.poly_mult mult_assoc)
  moreover have "\<exists>q. \<forall>x. poly p x * ((a + x) * poly qa x) = (a + x) * poly q x" for qa 
    by (metis mult.left_commute local.poly_mult)
  ultimately show ?thesis
    by (auto simp: divides_def divisors_zero fun_eq_iff poly_mult poly_add poly_cmult simp flip: distrib_right)
qed

lemma (in comm_semiring_1) poly_divides_refl[simp]: "p divides p"
proof -
  have "poly p = poly (p *** [1])"
    by (auto simp add: poly_mult fun_eq_iff)
  then show ?thesis
    using local.dividesI by blast
qed

lemma (in comm_semiring_1) poly_divides_trans: "p divides q \<Longrightarrow> q divides r \<Longrightarrow> p divides r"
  unfolding divides_def
  by (metis ext local.poly_mult local.poly_mult_assoc)

lemma (in comm_semiring_1) poly_divides_exp: "m \<le> n \<Longrightarrow> (p %^ m) divides (p %^ n)"
  by (auto simp: le_iff_add divides_def poly_exp_add fun_eq_iff)

lemma (in comm_semiring_1) poly_exp_divides: "(p %^ n) divides q \<Longrightarrow> m \<le> n \<Longrightarrow> (p %^ m) divides q"
  by (blast intro: poly_divides_exp poly_divides_trans)

lemma (in comm_semiring_0) poly_divides_add:
  assumes "p divides q" and "p divides r" shows "p divides (q +++ r)"
proof -
  have "\<And>qa qb. \<lbrakk>poly q = poly (p *** qa); poly r = poly (p *** qb)\<rbrakk>
       \<Longrightarrow> poly (q +++ r) = poly (p *** (qa +++ qb))"
    by (auto simp add: poly_add fun_eq_iff poly_mult distrib_left)
  with assms show ?thesis
    by (auto simp add: divides_def)
qed

lemma (in comm_ring_1) poly_divides_diff:
  assumes "p divides q" and "p divides (q +++ r)"
  shows "p divides r"
proof -
  have "\<And>qa qb. \<lbrakk>poly q = poly (p *** qa); poly (q +++ r) = poly (p *** qb)\<rbrakk>
         \<Longrightarrow> poly r = poly (p *** (qb +++ -- qa))"
  by (auto simp add: poly_add fun_eq_iff poly_mult poly_minus algebra_simps)
  with assms show ?thesis
    by (auto simp add: divides_def)
qed

lemma (in comm_ring_1) poly_divides_diff2: "p divides r \<Longrightarrow> p divides (q +++ r) \<Longrightarrow> p divides q"
  by (metis local.padd_commut local.poly_divides_diff)

lemma (in semiring_0) poly_divides_zero: "poly p = poly [] \<Longrightarrow> q divides p"
  by (metis ext dividesI poly.poly_Nil poly_mult_Nil2)

lemma (in semiring_0) poly_divides_zero2 [simp]: "q divides []"
  using local.poly_divides_zero by force


text \<open>At last, we can consider the order of a root.\<close>

lemma (in idom_char_0) poly_order_exists_lemma:
  assumes "length p = d"
    and "poly p \<noteq> poly []"
  shows "\<exists>n q. p = mulexp n [-a, 1] q \<and> poly q a \<noteq> 0"
  using assms
proof (induct d arbitrary: p)
  case 0
  then show ?case by simp
next
  case (Suc n p)
  show ?case
  proof (cases "poly p a = 0")
    case True
    from Suc.prems have h: "length p = Suc n" "poly p \<noteq> poly []"
      by auto
    then have pN: "p \<noteq> []"
      by auto
    from True[unfolded poly_linear_divides] pN obtain q where q: "p = [-a, 1] *** q"
      by blast
    from q h True have qh: "length q = n" "poly q \<noteq> poly []"
      using h(2) local.poly_entire q by fastforce+
    from Suc.hyps[OF qh] obtain m r where mr: "q = mulexp m [-a,1] r" "poly r a \<noteq> 0"
      by blast
    from mr q have "p = mulexp (Suc m) [-a,1] r \<and> poly r a \<noteq> 0"
      by simp
    then show ?thesis by blast
  next
    case False
    with Suc.prems show ?thesis
      by (smt (verit, best) local.mulexp.mulexp_zero)
  qed
qed


lemma (in comm_semiring_1) poly_mulexp: "poly (mulexp n p q) x = (poly p x) ^ n * poly q x"
  by (induct n) (auto simp add: poly_mult ac_simps)

lemma (in comm_semiring_1) divides_left_mult:
  assumes "(p *** q) divides r"
  shows "p divides r \<and> q divides r"
proof-
  from assms obtain t where "poly r = poly (p *** q *** t)"
    unfolding divides_def by blast
  then have "poly r = poly (p *** (q *** t))" and "poly r = poly (q *** (p *** t))"
    by (auto simp add: fun_eq_iff poly_mult ac_simps)
  then show ?thesis
    unfolding divides_def by blast
qed


(* FIXME: Tidy up *)

lemma (in semiring_1) zero_power_iff: "0 ^ n = (if n = 0 then 1 else 0)"
  by (induct n) simp_all

lemma (in idom_char_0) poly_order_exists:
  assumes "length p = d"
    and "poly p \<noteq> poly []"
  shows "\<exists>n. [- a, 1] %^ n divides p \<and> \<not> [- a, 1] %^ Suc n divides p"
proof -
  from assms have "\<exists>n q. p = mulexp n [- a, 1] q \<and> poly q a \<noteq> 0"
    by (rule poly_order_exists_lemma)
  then obtain n q where p: "p = mulexp n [- a, 1] q" and "poly q a \<noteq> 0"
    by blast
  have "[- a, 1] %^ n divides mulexp n [- a, 1] q"
  proof (rule dividesI)
    show "poly (mulexp n [- a, 1] q) = poly ([- a, 1] %^ n *** q)"
      by (induct n) (simp_all add: poly_add poly_cmult poly_mult algebra_simps)
  qed
  moreover have "\<not> [- a, 1] %^ Suc n divides mulexp n [- a, 1] q"
  proof
    assume "[- a, 1] %^ Suc n divides mulexp n [- a, 1] q"
    then obtain m where "poly (mulexp n [- a, 1] q) = poly ([- a, 1] %^ Suc n *** m)"
      by (rule dividesE)
    moreover have "poly (mulexp n [- a, 1] q) \<noteq> poly ([- a, 1] %^ Suc n *** m)"
    proof (induct n)
      case 0
      show ?case
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "poly q a = 0"
          by (simp add: poly_add poly_cmult)
        with \<open>poly q a \<noteq> 0\<close> show False
          by simp
      qed
    next
      case (Suc n)
      show ?case
        by (rule pexp_Suc [THEN ssubst])
          (simp add: poly_mult_left_cancel poly_mult_assoc Suc del: pmult_Cons pexp_Suc)
    qed
    ultimately show False by simp
  qed
  ultimately show ?thesis
    by (auto simp add: p)
qed

lemma (in semiring_1) poly_one_divides[simp]: "[1] divides p"
  by (auto simp add: divides_def)

lemma (in idom_char_0) poly_order:
  "poly p \<noteq> poly [] \<Longrightarrow> \<exists>!n. ([-a, 1] %^ n) divides p \<and> \<not> (([-a, 1] %^ Suc n) divides p)"
  by (meson Suc_le_eq linorder_neqE_nat local.poly_exp_divides poly_order_exists)


text \<open>Order\<close>

lemma some1_equalityD: "n = (SOME n. P n) \<Longrightarrow> \<exists>!n. P n \<Longrightarrow> P n"
  by (blast intro: someI2)

lemma (in idom_char_0) order:
  "([-a, 1] %^ n) divides p \<and> \<not> (([-a, 1] %^ Suc n) divides p) \<longleftrightarrow>
    n = order a p \<and> poly p \<noteq> poly []"
  unfolding order_def
  by (metis (no_types, lifting) local.poly_divides_zero local.poly_order someI)

lemma (in idom_char_0) order2:
  "poly p \<noteq> poly [] \<Longrightarrow>
    ([-a, 1] %^ (order a p)) divides p \<and> \<not> ([-a, 1] %^ Suc (order a p)) divides p"
  by (simp add: order del: pexp_Suc)

lemma (in idom_char_0) order_unique:
  "poly p \<noteq> poly [] \<Longrightarrow> ([-a, 1] %^ n) divides p \<Longrightarrow> \<not> ([-a, 1] %^ (Suc n)) divides p \<Longrightarrow>
    n = order a p"
  using order [of a n p] by auto

lemma (in idom_char_0) order_unique_lemma:
  "poly p \<noteq> poly [] \<and> ([-a, 1] %^ n) divides p \<and> \<not> ([-a, 1] %^ (Suc n)) divides p \<Longrightarrow>
    n = order a p"
  by (blast intro: order_unique)

lemma (in ring_1) order_poly: "poly p = poly q \<Longrightarrow> order a p = order a q"
  by (auto simp add: fun_eq_iff divides_def poly_mult order_def)

lemma (in semiring_1) pexp_one[simp]: "p %^ (Suc 0) = p"
  by (induct p) auto

lemma (in comm_ring_1) lemma_order_root:
  "0 < n \<and> [- a, 1] %^ n divides p \<and> \<not> [- a, 1] %^ (Suc n) divides p \<Longrightarrow> poly p a = 0"
  by (induct n arbitrary: a p) (auto simp add: divides_def poly_mult simp del: pmult_Cons)

lemma (in idom_char_0) order_root: "poly p a = 0 \<longleftrightarrow> poly p = poly [] \<or> order a p \<noteq> 0"
proof (cases "poly p = poly []")
  case False
  then show ?thesis 
    by (metis (mono_tags, lifting) dividesI lemma_order_root order2 pexp_one poly_linear_divides neq0_conv)
qed auto

lemma (in idom_char_0) order_divides:
  "([-a, 1] %^ n) divides p \<longleftrightarrow> poly p = poly [] \<or> n \<le> order a p"
proof (cases "poly p = poly []")
  case True
  then show ?thesis 
    using local.poly_divides_zero by force
next
  case False
  then show ?thesis 
    by (meson local.order2 local.poly_exp_divides not_less_eq_eq)
qed

lemma (in idom_char_0) order_decomp:
  assumes "poly p \<noteq> poly []"
  shows "\<exists>q. poly p = poly (([-a, 1] %^ order a p) *** q) \<and> \<not> [-a, 1] divides q"
proof -
  obtain q where q: "poly p = poly ([- a, 1] %^ order a p *** q)"
    using assms local.order2 divides_def by blast
  have False if "poly q = poly ([- a, 1] *** qa)" for qa
  proof -
    have "poly p \<noteq> poly ([- a, 1] %^ Suc (order a p) *** qa)"
      using assms local.divides_def local.order2 by blast
    with q that show False
      by (auto simp add: poly_mult ac_simps simp del: pmult_Cons)
  qed 
  with q show ?thesis
    unfolding divides_def by blast
qed

text \<open>Important composition properties of orders.\<close>
lemma order_mult:
  fixes a :: "'a::idom_char_0"
  assumes "poly (p *** q) \<noteq> poly []"
  shows "order a (p *** q) = order a p + order a q"
proof -
  have p: "poly p \<noteq> poly []" and q: "poly q \<noteq> poly []"
    using assms poly_entire by auto
  obtain p' where p': 
          "\<And>x. poly p x = poly ([- a, 1] %^ order a p) x * poly p' x"
          "\<not> [- a, 1] divides p'"
    by (metis order_decomp p poly_mult)
  obtain q' where q': 
          "\<And>x. poly q x = poly ([- a, 1] %^ order a q) x * poly q' x"
          "\<not> [- a, 1] divides q'"
    by (metis order_decomp q poly_mult)
  have "[- a, 1] %^ (order a p + order a q) divides (p *** q)"
  proof -
    have *: "poly p x * poly q x =
          poly ([- a, 1] %^ order a p) x * poly ([- a, 1] %^ order a q) x * poly (p' *** q') x" for x
      using p' q' by (simp add: poly_mult)
    then show ?thesis
      unfolding divides_def  poly_exp_add poly_mult using * by blast
  qed
  moreover have False
    if pq: "order a (p *** q) \<noteq> order a p + order a q"
      and dv: "[- a, 1] *** [- a, 1] %^ (order a p + order a q) divides (p *** q)"
  proof -
    obtain pq' :: "'a list"
      where pq': "poly (p *** q) = poly ([- a, 1] *** [- a, 1] %^ (order a p + order a q) *** pq')"
      using dv unfolding divides_def by auto
    have "poly ([-a, 1] %^ (order a q) *** ([-a, 1] %^ (order a p) *** (p' *** q'))) =
          poly ([-a, 1] %^ (order a q) *** ([-a, 1] %^ (order a p) *** ([-a, 1] *** pq')))"
      using p' q' pq pq'
      by (simp add: fun_eq_iff poly_exp_add poly_mult ac_simps del: pmult_Cons)
    then have "poly ([-a, 1] %^ (order a p) *** (p' *** q')) = poly ([-a, 1] %^ (order a p) *** ([-a, 1] *** pq'))"
      by (simp add: poly_mult_left_cancel)
    then have "[-a, 1] divides (p' *** q')"
      unfolding divides_def by (meson poly_exp_prime_eq_zero poly_mult_left_cancel)
    with p' q' show ?thesis
      by (simp add: poly_primes)
  qed
  ultimately show ?thesis
    by (metis order pexp_Suc)
qed

lemma (in idom_char_0) order_root2: "poly p \<noteq> poly [] \<Longrightarrow> poly p a = 0 \<longleftrightarrow> order a p \<noteq> 0"
  using order_root by presburger

lemma (in semiring_1) pmult_one[simp]: "[1] *** p = p"
  by auto

lemma (in semiring_0) poly_Nil_zero: "poly [] = poly [0]"
  by (simp add: fun_eq_iff)

lemma (in idom_char_0) rsquarefree_decomp:
  assumes "rsquarefree p" and "poly p a = 0"
  shows "\<exists>q. poly p = poly ([-a, 1] *** q) \<and> poly q a \<noteq> 0"
proof -
  have "order a p = Suc 0"
    using assms local.order_root2 rsquarefree_def by force
  moreover
  obtain q where "poly p = poly ([- a, 1] %^ order a p *** q)" 
                 "\<not> [- a, 1] divides q"
    using assms(1) order_decomp rsquarefree_def by blast
  ultimately show ?thesis
    using dividesI poly_linear_divides by auto
qed

text \<open>Normalization of a polynomial.\<close>

lemma (in semiring_0) poly_normalize[simp]: "poly (pnormalize p) = poly p"
  by (induct p) (auto simp add: fun_eq_iff)

text \<open>The degree of a polynomial.\<close>

lemma (in semiring_0) lemma_degree_zero: "(\<forall>c \<in> set p. c = 0) \<longleftrightarrow> pnormalize p = []"
  by (induct p) auto

lemma (in idom_char_0) degree_zero:
  assumes "poly p = poly []"
  shows "degree p = 0"
  using assms
  by (cases "pnormalize p = []") (auto simp add: degree_def poly_zero lemma_degree_zero)

lemma (in semiring_0) pnormalize_sing: "pnormalize [x] = [x] \<longleftrightarrow> x \<noteq> 0"
  by simp

lemma (in semiring_0) pnormalize_pair: "y \<noteq> 0 \<longleftrightarrow> pnormalize [x, y] = [x, y]"
  by simp

lemma (in semiring_0) pnormal_cons: "pnormal p \<Longrightarrow> pnormal (c # p)"
  unfolding pnormal_def by simp

lemma (in semiring_0) pnormal_tail: "p \<noteq> [] \<Longrightarrow> pnormal (c # p) \<Longrightarrow> pnormal p"
  unfolding pnormal_def by (auto split: if_split_asm)

lemma (in semiring_0) pnormal_last_nonzero: "pnormal p \<Longrightarrow> last p \<noteq> 0"
  by (induct p) (simp_all add: pnormal_def split: if_split_asm)

lemma (in semiring_0) pnormal_length: "pnormal p \<Longrightarrow> 0 < length p"
  unfolding pnormal_def length_greater_0_conv by blast

lemma (in semiring_0) pnormal_last_length: "0 < length p \<Longrightarrow> last p \<noteq> 0 \<Longrightarrow> pnormal p"
  by (induct p) (auto simp: pnormal_def  split: if_split_asm)

lemma (in semiring_0) pnormal_id: "pnormal p \<longleftrightarrow> 0 < length p \<and> last p \<noteq> 0"
  using pnormal_last_length pnormal_length pnormal_last_nonzero by blast

lemma (in idom_char_0) poly_Cons_eq: "poly (c # cs) = poly (d # ds) \<longleftrightarrow> c = d \<and> poly cs = poly ds"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if ?lhs
  proof -
    from that have "poly ((c # cs) +++ -- (d # ds)) x = 0" for x
      by (simp only: poly_minus poly_add algebra_simps) (simp add: algebra_simps)
    then have "poly ((c # cs) +++ -- (d # ds)) = poly []"
      by (simp add: fun_eq_iff)
    then have "c = d" and "\<forall>x \<in> set (cs +++ -- ds). x = 0"
      unfolding poly_zero by (simp_all add: poly_minus_def algebra_simps)
    from this(2) have "poly (cs +++ -- ds) x = 0" for x
      unfolding poly_zero[symmetric] by simp
    with \<open>c = d\<close> show ?thesis
      by (simp add: poly_minus poly_add algebra_simps fun_eq_iff)
  qed
  show ?lhs if ?rhs
    using that by (simp add:fun_eq_iff)
qed

lemma (in idom_char_0) pnormalize_unique: "poly p = poly q \<Longrightarrow> pnormalize p = pnormalize q"
proof (induct q arbitrary: p)
  case Nil
  then show ?case
    by (simp only: poly_zero lemma_degree_zero) simp
next
  case (Cons c cs p)
  then show ?case
  proof (induct p)
    case Nil
    then show ?case
      by (metis local.poly_zero_lemma')
  next
    case (Cons d ds)
    then show ?case
      by (metis pnormalize.pnormalize_Cons local.poly_Cons_eq)
  qed
qed

lemma (in idom_char_0) degree_unique:
  assumes pq: "poly p = poly q"
  shows "degree p = degree q"
  using pnormalize_unique[OF pq] unfolding degree_def by simp

lemma (in semiring_0) pnormalize_length: "length (pnormalize p) \<le> length p"
  by (induct p) auto

lemma (in semiring_0) last_linear_mul_lemma:
  "last ((a %* p) +++ (x # (b %* p))) = (if p = [] then x else b * last p)"
proof (induct p arbitrary: a x b)
  case Nil
  then show ?case by auto
next
  case (Cons a p c x b)
  then have "padd (cmult c p) (times b a # cmult b p) \<noteq> []"
    by (metis local.padd.padd_Nil local.padd_Cons_Cons neq_Nil_conv)
  then show ?case
    by (simp add: local.Cons)
qed

lemma (in semiring_1) last_linear_mul:
  assumes p: "p \<noteq> []"
  shows "last ([a, 1] *** p) = last p"
proof -
  from p obtain c cs where cs: "p = c # cs"
    by (cases p) auto
  from cs have eq: "[a, 1] *** p = (a %* (c # cs)) +++ (0 # (1 %* (c # cs)))"
    by (simp add: poly_cmult_distr)
  show ?thesis
    using cs unfolding eq last_linear_mul_lemma by simp
qed

lemma (in semiring_0) pnormalize_eq: "last p \<noteq> 0 \<Longrightarrow> pnormalize p = p"
  by (induct p) (auto split: if_split_asm)

lemma (in semiring_0) last_pnormalize: "pnormalize p \<noteq> [] \<Longrightarrow> last (pnormalize p) \<noteq> 0"
  by (induct p) auto

lemma (in semiring_0) pnormal_degree: "last p \<noteq> 0 \<Longrightarrow> degree p = length p - 1"
  using pnormalize_eq[of p] unfolding degree_def by simp

lemma (in semiring_0) poly_Nil_ext: "poly [] = (\<lambda>x. 0)"
  by auto

lemma (in idom_char_0) linear_mul_degree:
  assumes p: "poly p \<noteq> poly []"
  shows "degree ([a, 1] *** p) = degree p + 1"
proof -
  from p have pnz: "pnormalize p \<noteq> []"
    unfolding poly_zero lemma_degree_zero .

  from last_linear_mul[OF pnz, of a] last_pnormalize[OF pnz]
  have l0: "last ([a, 1] *** pnormalize p) \<noteq> 0" by simp

  from last_pnormalize[OF pnz] last_linear_mul[OF pnz, of a]
    pnormal_degree[OF l0] pnormal_degree[OF last_pnormalize[OF pnz]] pnz
  have th: "degree ([a,1] *** pnormalize p) = degree (pnormalize p) + 1"
    by simp

  have eqs: "poly ([a,1] *** pnormalize p) = poly ([a,1] *** p)"
    by (rule ext) (simp add: poly_mult poly_add poly_cmult)
  from degree_unique[OF eqs] th show ?thesis
    by (simp add: degree_unique[OF poly_normalize])
qed

lemma (in idom_char_0) linear_pow_mul_degree:
  "degree([a,1] %^n *** p) = (if poly p = poly [] then 0 else degree p + n)"
proof (induct n arbitrary: a p)
  case (0 a p)
  show ?case
  proof (cases "poly p = poly []")
    case True
    then show ?thesis
      using degree_unique[OF True] by (simp add: degree_def)
  qed (auto simp add: poly_Nil_ext)
next
  case (Suc n a p)
  have eq: "poly ([a, 1] %^(Suc n) *** p) = poly ([a, 1] %^ n *** ([a, 1] *** p))"
    by (force simp add: poly_mult poly_add poly_cmult ac_simps distrib_left)
  note deq = degree_unique[OF eq]
  show ?case
  proof (cases "poly p = poly []")
    case True
    with eq have eq': "poly ([a, 1] %^(Suc n) *** p) = poly []"
      by (auto simp add: poly_mult poly_cmult poly_add)
    from degree_unique[OF eq'] True show ?thesis
      by (simp add: degree_def)
  next
    case False
    then have ap: "poly ([a,1] *** p) \<noteq> poly []"
      using poly_mult_not_eq_poly_Nil unfolding poly_entire by auto
    have eq: "poly ([a, 1] %^(Suc n) *** p) = poly ([a, 1]%^n *** ([a, 1] *** p))"
      by (auto simp add: poly_mult poly_add poly_exp poly_cmult algebra_simps)
    from ap have ap': "poly ([a, 1] *** p) = poly [] \<longleftrightarrow> False"
      by blast
    have th0: "degree ([a, 1]%^n *** ([a, 1] *** p)) = degree ([a, 1] *** p) + n"
      unfolding Suc.hyps[of a "pmult [a,one] p"] ap' by simp
    from degree_unique[OF eq] ap False th0 linear_mul_degree[OF False, of a]
    show ?thesis
      by (auto simp del: poly.simps)
  qed
qed

lemma (in idom_char_0) order_degree:
  assumes p0: "poly p \<noteq> poly []"
  shows "order a p \<le> degree p"
proof -
  from order2[OF p0, unfolded divides_def]
  obtain q where q: "poly p = poly ([- a, 1]%^ (order a p) *** q)"
    by blast
  with q p0 have "poly q \<noteq> poly []"
    by (simp add: poly_mult poly_entire)
  with degree_unique[OF q, unfolded linear_pow_mul_degree] show ?thesis
    by auto
qed


text \<open>Tidier versions of finiteness of roots.\<close>
lemma (in idom_char_0) poly_roots_finite_set:
  "poly p \<noteq> poly [] \<Longrightarrow> finite {x. poly p x = 0}"
  unfolding poly_roots_finite .


text \<open>Bound for polynomial.\<close>
lemma poly_mono:
  fixes x :: "'a::linordered_idom"
  shows "\<bar>x\<bar> \<le> k \<Longrightarrow> \<bar>poly p x\<bar> \<le> poly (map abs p) k"
proof (induct p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  have "\<bar>a + x * poly p x\<bar> \<le> \<bar>a\<bar> + \<bar>x * poly p x\<bar>"
    using abs_triangle_ineq by blast
  also have "\<dots> \<le> \<bar>a\<bar> + k * poly (map abs p) k"
    by (simp add: Cons.hyps Cons.prems abs_mult mult_mono')
  finally show ?case
    using Cons by auto
qed

lemma (in semiring_0) poly_Sing: "poly [c] x = c"
  by simp

end
