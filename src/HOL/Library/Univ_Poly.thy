(*  Title:      HOL/Library/Univ_Poly.thy
    Author:     Amine Chaieb
*)

header {* Univariate Polynomials *}

theory Univ_Poly
imports Main
begin

text{* Application of polynomial as a function. *}

primrec (in semiring_0) poly :: "'a list => 'a  => 'a" where
  poly_Nil:  "poly [] x = 0"
| poly_Cons: "poly (h#t) x = h + x * poly t x"


subsection{*Arithmetic Operations on Polynomials*}

text{*addition*}

primrec (in semiring_0) padd :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixl "+++" 65)
where
  padd_Nil:  "[] +++ l2 = l2"
| padd_Cons: "(h#t) +++ l2 = (if l2 = [] then h#t
                            else (h + hd l2)#(t +++ tl l2))"

text{*Multiplication by a constant*}
primrec (in semiring_0) cmult :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixl "%*" 70) where
   cmult_Nil:  "c %* [] = []"
|  cmult_Cons: "c %* (h#t) = (c * h)#(c %* t)"

text{*Multiplication by a polynomial*}
primrec (in semiring_0) pmult :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixl "***" 70)
where
   pmult_Nil:  "[] *** l2 = []"
|  pmult_Cons: "(h#t) *** l2 = (if t = [] then h %* l2
                              else (h %* l2) +++ ((0) # (t *** l2)))"

text{*Repeated multiplication by a polynomial*}
primrec (in semiring_0) mulexp :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a  list \<Rightarrow> 'a list" where
   mulexp_zero:  "mulexp 0 p q = q"
|  mulexp_Suc:   "mulexp (Suc n) p q = p *** mulexp n p q"

text{*Exponential*}
primrec (in semiring_1) pexp :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list"  (infixl "%^" 80) where
   pexp_0:   "p %^ 0 = [1]"
|  pexp_Suc: "p %^ (Suc n) = p *** (p %^ n)"

text{*Quotient related value of dividing a polynomial by x + a*}
(* Useful for divisor properties in inductive proofs *)
primrec (in field) "pquot" :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
   pquot_Nil:  "pquot [] a= []"
|  pquot_Cons: "pquot (h#t) a = (if t = [] then [h]
                   else (inverse(a) * (h - hd( pquot t a)))#(pquot t a))"

text{*normalization of polynomials (remove extra 0 coeff)*}
primrec (in semiring_0) pnormalize :: "'a list \<Rightarrow> 'a list" where
  pnormalize_Nil:  "pnormalize [] = []"
| pnormalize_Cons: "pnormalize (h#p) = (if ( (pnormalize p) = [])
                                     then (if (h = 0) then [] else [h])
                                     else (h#(pnormalize p)))"

definition (in semiring_0) "pnormal p = ((pnormalize p = p) \<and> p \<noteq> [])"
definition (in semiring_0) "nonconstant p = (pnormal p \<and> (\<forall>x. p \<noteq> [x]))"
text{*Other definitions*}

definition (in ring_1)
  poly_minus :: "'a list => 'a list" ("-- _" [80] 80) where
  "-- p = (- 1) %* p"

definition (in semiring_0)
  divides :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"  (infixl "divides" 70) where
  "p1 divides p2 = (\<exists>q. poly p2 = poly(p1 *** q))"

    --{*order of a polynomial*}
definition (in ring_1) order :: "'a => 'a list => nat" where
  "order a p = (SOME n. ([-a, 1] %^ n) divides p &
                      ~ (([-a, 1] %^ (Suc n)) divides p))"

     --{*degree of a polynomial*}
definition (in semiring_0) degree :: "'a list => nat" where
  "degree p = length (pnormalize p) - 1"

     --{*squarefree polynomials --- NB with respect to real roots only.*}
definition (in ring_1)
  rsquarefree :: "'a list => bool" where
  "rsquarefree p = (poly p \<noteq> poly [] &
                     (\<forall>a. (order a p = 0) | (order a p = 1)))"

context semiring_0
begin

lemma padd_Nil2[simp]: "p +++ [] = p"
by (induct p) auto

lemma padd_Cons_Cons: "(h1 # p1) +++ (h2 # p2) = (h1 + h2) # (p1 +++ p2)"
by auto

lemma pminus_Nil[simp]: "-- [] = []"
by (simp add: poly_minus_def)

lemma pmult_singleton: "[h1] *** p1 = h1 %* p1" by simp
end

lemma (in semiring_1) poly_ident_mult[simp]: "1 %* t = t" by (induct "t", auto)

lemma (in semiring_0) poly_simple_add_Cons[simp]: "[a] +++ ((0)#t) = (a#t)"
by simp

text{*Handy general properties*}

lemma (in comm_semiring_0) padd_commut: "b +++ a = a +++ b"
proof(induct b arbitrary: a)
  case Nil thus ?case by auto
next
  case (Cons b bs a) thus ?case by (cases a, simp_all add: add_commute)
qed

lemma (in comm_semiring_0) padd_assoc: "\<forall>b c. (a +++ b) +++ c = a +++ (b +++ c)"
apply (induct a)
apply (simp, clarify)
apply (case_tac b, simp_all add: add_ac)
done

lemma (in semiring_0) poly_cmult_distr: "a %* ( p +++ q) = (a %* p +++ a %* q)"
apply (induct p arbitrary: q, simp)
apply (case_tac q, simp_all add: right_distrib)
done

lemma (in ring_1) pmult_by_x[simp]: "[0, 1] *** t = ((0)#t)"
apply (induct "t", simp)
apply (auto simp add: mult_zero_left poly_ident_mult padd_commut)
apply (case_tac t, auto)
done

text{*properties of evaluation of polynomials.*}

lemma (in semiring_0) poly_add: "poly (p1 +++ p2) x = poly p1 x + poly p2 x"
proof(induct p1 arbitrary: p2)
  case Nil thus ?case by simp
next
  case (Cons a as p2) thus ?case
    by (cases p2, simp_all  add: add_ac right_distrib)
qed

lemma (in comm_semiring_0) poly_cmult: "poly (c %* p) x = c * poly p x"
apply (induct "p")
apply (case_tac [2] "x=zero")
apply (auto simp add: right_distrib mult_ac)
done

lemma (in comm_semiring_0) poly_cmult_map: "poly (map (op * c) p) x = c*poly p x"
  by (induct p, auto simp add: right_distrib mult_ac)

lemma (in comm_ring_1) poly_minus: "poly (-- p) x = - (poly p x)"
apply (simp add: poly_minus_def)
apply (auto simp add: poly_cmult minus_mult_left[symmetric])
done

lemma (in comm_semiring_0) poly_mult: "poly (p1 *** p2) x = poly p1 x * poly p2 x"
proof(induct p1 arbitrary: p2)
  case Nil thus ?case by simp
next
  case (Cons a as p2)
  thus ?case by (cases as,
    simp_all add: poly_cmult poly_add left_distrib right_distrib mult_ac)
qed

class idom_char_0 = idom + ring_char_0

lemma (in comm_ring_1) poly_exp: "poly (p %^ n) x = (poly p x) ^ n"
apply (induct "n")
apply (auto simp add: poly_cmult poly_mult power_Suc)
done

text{*More Polynomial Evaluation Lemmas*}

lemma  (in semiring_0) poly_add_rzero[simp]: "poly (a +++ []) x = poly a x"
by simp

lemma (in comm_semiring_0) poly_mult_assoc: "poly ((a *** b) *** c) x = poly (a *** (b *** c)) x"
  by (simp add: poly_mult mult_assoc)

lemma (in semiring_0) poly_mult_Nil2[simp]: "poly (p *** []) x = 0"
by (induct "p", auto)

lemma (in comm_semiring_1) poly_exp_add: "poly (p %^ (n + d)) x = poly( p %^ n *** p %^ d) x"
apply (induct "n")
apply (auto simp add: poly_mult mult_assoc)
done

subsection{*Key Property: if @{term "f(a) = 0"} then @{term "(x - a)"} divides
 @{term "p(x)"} *}

lemma (in comm_ring_1) lemma_poly_linear_rem: "\<forall>h. \<exists>q r. h#t = [r] +++ [-a, 1] *** q"
proof(induct t)
  case Nil
  {fix h have "[h] = [h] +++ [- a, 1] *** []" by simp}
  thus ?case by blast
next
  case (Cons  x xs)
  {fix h
    from Cons.hyps[rule_format, of x]
    obtain q r where qr: "x#xs = [r] +++ [- a, 1] *** q" by blast
    have "h#x#xs = [a*r + h] +++ [-a, 1] *** (r#q)"
      using qr by(cases q, simp_all add: algebra_simps diff_minus[symmetric]
        minus_mult_left[symmetric] right_minus)
    hence "\<exists>q r. h#x#xs = [r] +++ [-a, 1] *** q" by blast}
  thus ?case by blast
qed

lemma (in comm_ring_1) poly_linear_rem: "\<exists>q r. h#t = [r] +++ [-a, 1] *** q"
by (cut_tac t = t and a = a in lemma_poly_linear_rem, auto)


lemma (in comm_ring_1) poly_linear_divides: "(poly p a = 0) = ((p = []) | (\<exists>q. p = [-a, 1] *** q))"
proof-
  {assume p: "p = []" hence ?thesis by simp}
  moreover
  {fix x xs assume p: "p = x#xs"
    {fix q assume "p = [-a, 1] *** q" hence "poly p a = 0"
        by (simp add: poly_add poly_cmult minus_mult_left[symmetric])}
    moreover
    {assume p0: "poly p a = 0"
      from poly_linear_rem[of x xs a] obtain q r
      where qr: "x#xs = [r] +++ [- a, 1] *** q" by blast
      have "r = 0" using p0 by (simp only: p qr poly_mult poly_add) simp
      hence "\<exists>q. p = [- a, 1] *** q" using p qr  apply - apply (rule exI[where x=q])apply auto apply (cases q) apply auto done}
    ultimately have ?thesis using p by blast}
  ultimately show ?thesis by (cases p, auto)
qed

lemma (in semiring_0) lemma_poly_length_mult[simp]: "\<forall>h k a. length (k %* p +++  (h # (a %* p))) = Suc (length p)"
by (induct "p", auto)

lemma (in semiring_0) lemma_poly_length_mult2[simp]: "\<forall>h k. length (k %* p +++  (h # p)) = Suc (length p)"
by (induct "p", auto)

lemma (in ring_1) poly_length_mult[simp]: "length([-a,1] *** q) = Suc (length q)"
by auto

subsection{*Polynomial length*}

lemma (in semiring_0) poly_cmult_length[simp]: "length (a %* p) = length p"
by (induct "p", auto)

lemma (in semiring_0) poly_add_length: "length (p1 +++ p2) = max (length p1) (length p2)"
apply (induct p1 arbitrary: p2, simp_all)
apply arith
done

lemma (in semiring_0) poly_root_mult_length[simp]: "length([a,b] *** p) = Suc (length p)"
by (simp add: poly_add_length)

lemma (in idom) poly_mult_not_eq_poly_Nil[simp]:
 "poly (p *** q) x \<noteq> poly [] x \<longleftrightarrow> poly p x \<noteq> poly [] x \<and> poly q x \<noteq> poly [] x"
by (auto simp add: poly_mult)

lemma (in idom) poly_mult_eq_zero_disj: "poly (p *** q) x = 0 \<longleftrightarrow> poly p x = 0 \<or> poly q x = 0"
by (auto simp add: poly_mult)

text{*Normalisation Properties*}

lemma (in semiring_0) poly_normalized_nil: "(pnormalize p = []) --> (poly p x = 0)"
by (induct "p", auto)

text{*A nontrivial polynomial of degree n has no more than n roots*}
lemma (in idom) poly_roots_index_lemma:
   assumes p: "poly p x \<noteq> poly [] x" and n: "length p = n"
  shows "\<exists>i. \<forall>x. poly p x = 0 \<longrightarrow> (\<exists>m\<le>n. x = i m)"
  using p n
proof(induct n arbitrary: p x)
  case 0 thus ?case by simp
next
  case (Suc n p x)
  {assume C: "\<And>i. \<exists>x. poly p x = 0 \<and> (\<forall>m\<le>Suc n. x \<noteq> i m)"
    from Suc.prems have p0: "poly p x \<noteq> 0" "p\<noteq> []" by auto
    from p0(1)[unfolded poly_linear_divides[of p x]]
    have "\<forall>q. p \<noteq> [- x, 1] *** q" by blast
    from C obtain a where a: "poly p a = 0" by blast
    from a[unfolded poly_linear_divides[of p a]] p0(2)
    obtain q where q: "p = [-a, 1] *** q" by blast
    have lg: "length q = n" using q Suc.prems(2) by simp
    from q p0 have qx: "poly q x \<noteq> poly [] x"
      by (auto simp add: poly_mult poly_add poly_cmult)
    from Suc.hyps[OF qx lg] obtain i where
      i: "\<forall>x. poly q x = 0 \<longrightarrow> (\<exists>m\<le>n. x = i m)" by blast
    let ?i = "\<lambda>m. if m = Suc n then a else i m"
    from C[of ?i] obtain y where y: "poly p y = 0" "\<forall>m\<le> Suc n. y \<noteq> ?i m"
      by blast
    from y have "y = a \<or> poly q y = 0"
      by (simp only: q poly_mult_eq_zero_disj poly_add) (simp add: algebra_simps)
    with i[rule_format, of y] y(1) y(2) have False apply auto
      apply (erule_tac x="m" in allE)
      apply auto
      done}
  thus ?case by blast
qed


lemma (in idom) poly_roots_index_length: "poly p x \<noteq> poly [] x ==>
      \<exists>i. \<forall>x. (poly p x = 0) --> (\<exists>n. n \<le> length p & x = i n)"
by (blast intro: poly_roots_index_lemma)

lemma (in idom) poly_roots_finite_lemma1: "poly p x \<noteq> poly [] x ==>
      \<exists>N i. \<forall>x. (poly p x = 0) --> (\<exists>n. (n::nat) < N & x = i n)"
apply (drule poly_roots_index_length, safe)
apply (rule_tac x = "Suc (length p)" in exI)
apply (rule_tac x = i in exI)
apply (simp add: less_Suc_eq_le)
done


lemma (in idom) idom_finite_lemma:
  assumes P: "\<forall>x. P x --> (\<exists>n. n < length j & x = j!n)"
  shows "finite {x. P x}"
proof-
  let ?M = "{x. P x}"
  let ?N = "set j"
  have "?M \<subseteq> ?N" using P by auto
  thus ?thesis using finite_subset by auto
qed


lemma (in idom) poly_roots_finite_lemma2: "poly p x \<noteq> poly [] x ==>
      \<exists>i. \<forall>x. (poly p x = 0) --> x \<in> set i"
apply (drule poly_roots_index_length, safe)
apply (rule_tac x="map (\<lambda>n. i n) [0 ..< Suc (length p)]" in exI)
apply (auto simp add: image_iff)
apply (erule_tac x="x" in allE, clarsimp)
by (case_tac "n=length p", auto simp add: order_le_less)

lemma (in ring_char_0) UNIV_ring_char_0_infinte:
  "\<not> (finite (UNIV:: 'a set))"
proof
  assume F: "finite (UNIV :: 'a set)"
  have "finite (UNIV :: nat set)"
  proof (rule finite_imageD)
    have "of_nat ` UNIV \<subseteq> UNIV" by simp
    then show "finite (of_nat ` UNIV :: 'a set)" using F by (rule finite_subset)
    show "inj (of_nat :: nat \<Rightarrow> 'a)" by (simp add: inj_on_def)
  qed
  with infinite_UNIV_nat show False ..
qed

lemma (in idom_char_0) poly_roots_finite: "(poly p \<noteq> poly []) =
  finite {x. poly p x = 0}"
proof
  assume H: "poly p \<noteq> poly []"
  show "finite {x. poly p x = (0::'a)}"
    using H
    apply -
    apply (erule contrapos_np, rule ext)
    apply (rule ccontr)
    apply (clarify dest!: poly_roots_finite_lemma2)
    using finite_subset
  proof-
    fix x i
    assume F: "\<not> finite {x. poly p x = (0\<Colon>'a)}"
      and P: "\<forall>x. poly p x = (0\<Colon>'a) \<longrightarrow> x \<in> set i"
    let ?M= "{x. poly p x = (0\<Colon>'a)}"
    from P have "?M \<subseteq> set i" by auto
    with finite_subset F show False by auto
  qed
next
  assume F: "finite {x. poly p x = (0\<Colon>'a)}"
  show "poly p \<noteq> poly []" using F UNIV_ring_char_0_infinte by auto
qed

text{*Entirety and Cancellation for polynomials*}

lemma (in idom_char_0) poly_entire_lemma2:
  assumes p0: "poly p \<noteq> poly []" and q0: "poly q \<noteq> poly []"
  shows "poly (p***q) \<noteq> poly []"
proof-
  let ?S = "\<lambda>p. {x. poly p x = 0}"
  have "?S (p *** q) = ?S p \<union> ?S q" by (auto simp add: poly_mult)
  with p0 q0 show ?thesis  unfolding poly_roots_finite by auto
qed

lemma (in idom_char_0) poly_entire:
  "poly (p *** q) = poly [] \<longleftrightarrow> poly p = poly [] \<or> poly q = poly []"
using poly_entire_lemma2[of p q]
by (auto simp add: fun_eq_iff poly_mult)

lemma (in idom_char_0) poly_entire_neg: "(poly (p *** q) \<noteq> poly []) = ((poly p \<noteq> poly []) & (poly q \<noteq> poly []))"
by (simp add: poly_entire)

lemma fun_eq: " (f = g) = (\<forall>x. f x = g x)"
by (auto intro!: ext)

lemma (in comm_ring_1) poly_add_minus_zero_iff: "(poly (p +++ -- q) = poly []) = (poly p = poly q)"
by (auto simp add: algebra_simps poly_add poly_minus_def fun_eq poly_cmult minus_mult_left[symmetric])

lemma (in comm_ring_1) poly_add_minus_mult_eq: "poly (p *** q +++ --(p *** r)) = poly (p *** (q +++ -- r))"
by (auto simp add: poly_add poly_minus_def fun_eq poly_mult poly_cmult right_distrib minus_mult_left[symmetric] minus_mult_right[symmetric])

subclass (in idom_char_0) comm_ring_1 ..
lemma (in idom_char_0) poly_mult_left_cancel: "(poly (p *** q) = poly (p *** r)) = (poly p = poly [] | poly q = poly r)"
proof-
  have "poly (p *** q) = poly (p *** r) \<longleftrightarrow> poly (p *** q +++ -- (p *** r)) = poly []" by (simp only: poly_add_minus_zero_iff)
  also have "\<dots> \<longleftrightarrow> poly p = poly [] | poly q = poly r"
    by (auto intro: ext simp add: poly_add_minus_mult_eq poly_entire poly_add_minus_zero_iff)
  finally show ?thesis .
qed

lemma (in idom) poly_exp_eq_zero[simp]:
     "(poly (p %^ n) = poly []) = (poly p = poly [] & n \<noteq> 0)"
apply (simp only: fun_eq add: HOL.all_simps [symmetric])
apply (rule arg_cong [where f = All])
apply (rule ext)
apply (induct n)
apply (auto simp add: poly_exp poly_mult)
done

lemma (in semiring_1) one_neq_zero[simp]: "1 \<noteq> 0" using zero_neq_one by blast
lemma (in comm_ring_1) poly_prime_eq_zero[simp]: "poly [a,1] \<noteq> poly []"
apply (simp add: fun_eq)
apply (rule_tac x = "minus one a" in exI)
apply (unfold diff_minus)
apply (subst add_commute)
apply (subst add_assoc)
apply simp
done

lemma (in idom) poly_exp_prime_eq_zero: "(poly ([a, 1] %^ n) \<noteq> poly [])"
by auto

text{*A more constructive notion of polynomials being trivial*}

lemma (in idom_char_0) poly_zero_lemma': "poly (h # t) = poly [] ==> h = 0 & poly t = poly []"
apply(simp add: fun_eq)
apply (case_tac "h = zero")
apply (drule_tac [2] x = zero in spec, auto)
apply (cases "poly t = poly []", simp)
proof-
  fix x
  assume H: "\<forall>x. x = (0\<Colon>'a) \<or> poly t x = (0\<Colon>'a)"  and pnz: "poly t \<noteq> poly []"
  let ?S = "{x. poly t x = 0}"
  from H have "\<forall>x. x \<noteq>0 \<longrightarrow> poly t x = 0" by blast
  hence th: "?S \<supseteq> UNIV - {0}" by auto
  from poly_roots_finite pnz have th': "finite ?S" by blast
  from finite_subset[OF th th'] UNIV_ring_char_0_infinte
  show "poly t x = (0\<Colon>'a)" by simp
  qed

lemma (in idom_char_0) poly_zero: "(poly p = poly []) = list_all (%c. c = 0) p"
apply (induct "p", simp)
apply (rule iffI)
apply (drule poly_zero_lemma', auto)
done

lemma (in idom_char_0) poly_0: "list_all (\<lambda>c. c = 0) p \<Longrightarrow> poly p x = 0"
  unfolding poly_zero[symmetric] by simp



text{*Basics of divisibility.*}

lemma (in idom) poly_primes: "([a, 1] divides (p *** q)) = ([a, 1] divides p | [a, 1] divides q)"
apply (auto simp add: divides_def fun_eq poly_mult poly_add poly_cmult left_distrib [symmetric])
apply (drule_tac x = "uminus a" in spec)
apply (simp add: poly_linear_divides poly_add poly_cmult left_distrib [symmetric])
apply (cases "p = []")
apply (rule exI[where x="[]"])
apply simp
apply (cases "q = []")
apply (erule allE[where x="[]"], simp)

apply clarsimp
apply (cases "\<exists>q\<Colon>'a list. p = a %* q +++ ((0\<Colon>'a) # q)")
apply (clarsimp simp add: poly_add poly_cmult)
apply (rule_tac x="qa" in exI)
apply (simp add: left_distrib [symmetric])
apply clarsimp

apply (auto simp add: right_minus poly_linear_divides poly_add poly_cmult left_distrib [symmetric])
apply (rule_tac x = "pmult qa q" in exI)
apply (rule_tac [2] x = "pmult p qa" in exI)
apply (auto simp add: poly_add poly_mult poly_cmult mult_ac)
done

lemma (in comm_semiring_1) poly_divides_refl[simp]: "p divides p"
apply (simp add: divides_def)
apply (rule_tac x = "[one]" in exI)
apply (auto simp add: poly_mult fun_eq)
done

lemma (in comm_semiring_1) poly_divides_trans: "[| p divides q; q divides r |] ==> p divides r"
apply (simp add: divides_def, safe)
apply (rule_tac x = "pmult qa qaa" in exI)
apply (auto simp add: poly_mult fun_eq mult_assoc)
done


lemma (in comm_semiring_1) poly_divides_exp: "m \<le> n ==> (p %^ m) divides (p %^ n)"
apply (auto simp add: le_iff_add)
apply (induct_tac k)
apply (rule_tac [2] poly_divides_trans)
apply (auto simp add: divides_def)
apply (rule_tac x = p in exI)
apply (auto simp add: poly_mult fun_eq mult_ac)
done

lemma (in comm_semiring_1) poly_exp_divides: "[| (p %^ n) divides q;  m\<le>n |] ==> (p %^ m) divides q"
by (blast intro: poly_divides_exp poly_divides_trans)

lemma (in comm_semiring_0) poly_divides_add:
   "[| p divides q; p divides r |] ==> p divides (q +++ r)"
apply (simp add: divides_def, auto)
apply (rule_tac x = "padd qa qaa" in exI)
apply (auto simp add: poly_add fun_eq poly_mult right_distrib)
done

lemma (in comm_ring_1) poly_divides_diff:
   "[| p divides q; p divides (q +++ r) |] ==> p divides r"
apply (simp add: divides_def, auto)
apply (rule_tac x = "padd qaa (poly_minus qa)" in exI)
apply (auto simp add: poly_add fun_eq poly_mult poly_minus algebra_simps)
done

lemma (in comm_ring_1) poly_divides_diff2: "[| p divides r; p divides (q +++ r) |] ==> p divides q"
apply (erule poly_divides_diff)
apply (auto simp add: poly_add fun_eq poly_mult divides_def add_ac)
done

lemma (in semiring_0) poly_divides_zero: "poly p = poly [] ==> q divides p"
apply (simp add: divides_def)
apply (rule exI[where x="[]"])
apply (auto simp add: fun_eq poly_mult)
done

lemma (in semiring_0) poly_divides_zero2[simp]: "q divides []"
apply (simp add: divides_def)
apply (rule_tac x = "[]" in exI)
apply (auto simp add: fun_eq)
done

text{*At last, we can consider the order of a root.*}

lemma (in idom_char_0)  poly_order_exists_lemma:
  assumes lp: "length p = d" and p: "poly p \<noteq> poly []"
  shows "\<exists>n q. p = mulexp n [-a, 1] q \<and> poly q a \<noteq> 0"
using lp p
proof(induct d arbitrary: p)
  case 0 thus ?case by simp
next
  case (Suc n p)
  {assume p0: "poly p a = 0"
    from Suc.prems have h: "length p = Suc n" "poly p \<noteq> poly []" by auto
    hence pN: "p \<noteq> []" by auto
    from p0[unfolded poly_linear_divides] pN  obtain q where
      q: "p = [-a, 1] *** q" by blast
    from q h p0 have qh: "length q = n" "poly q \<noteq> poly []"
      apply -
      apply simp
      apply (simp only: fun_eq)
      apply (rule ccontr)
      apply (simp add: fun_eq poly_add poly_cmult minus_mult_left[symmetric])
      done
    from Suc.hyps[OF qh] obtain m r where
      mr: "q = mulexp m [-a,1] r" "poly r a \<noteq> 0" by blast
    from mr q have "p = mulexp (Suc m) [-a,1] r \<and> poly r a \<noteq> 0" by simp
    hence ?case by blast}
  moreover
  {assume p0: "poly p a \<noteq> 0"
    hence ?case using Suc.prems apply simp by (rule exI[where x="0::nat"], simp)}
  ultimately show ?case by blast
qed


lemma (in comm_semiring_1) poly_mulexp: "poly (mulexp n p q) x = (poly p x) ^ n * poly q x"
by(induct n, auto simp add: poly_mult power_Suc mult_ac)

lemma (in comm_semiring_1) divides_left_mult:
  assumes d:"(p***q) divides r" shows "p divides r \<and> q divides r"
proof-
  from d obtain t where r:"poly r = poly (p***q *** t)"
    unfolding divides_def by blast
  hence "poly r = poly (p *** (q *** t))"
    "poly r = poly (q *** (p***t))" by(auto simp add: fun_eq poly_mult mult_ac)
  thus ?thesis unfolding divides_def by blast
qed



(* FIXME: Tidy up *)

lemma (in semiring_1)
  zero_power_iff: "0 ^ n = (if n = 0 then 1 else 0)"
  by (induct n, simp_all add: power_Suc)

lemma (in idom_char_0) poly_order_exists:
  assumes lp: "length p = d" and p0: "poly p \<noteq> poly []"
  shows "\<exists>n. ([-a, 1] %^ n) divides p & ~(([-a, 1] %^ (Suc n)) divides p)"
proof-
let ?poly = poly
let ?mulexp = mulexp
let ?pexp = pexp
from lp p0
show ?thesis
apply -
apply (drule poly_order_exists_lemma [where a=a], assumption, clarify)
apply (rule_tac x = n in exI, safe)
apply (unfold divides_def)
apply (rule_tac x = q in exI)
apply (induct_tac "n", simp)
apply (simp (no_asm_simp) add: poly_add poly_cmult poly_mult right_distrib mult_ac)
apply safe
apply (subgoal_tac "?poly (?mulexp n [uminus a, one] q) \<noteq> ?poly (pmult (?pexp [uminus a, one] (Suc n)) qa)")
apply simp
apply (induct_tac "n")
apply (simp del: pmult_Cons pexp_Suc)
apply (erule_tac Q = "?poly q a = zero" in contrapos_np)
apply (simp add: poly_add poly_cmult minus_mult_left[symmetric])
apply (rule pexp_Suc [THEN ssubst])
apply (rule ccontr)
apply (simp add: poly_mult_left_cancel poly_mult_assoc del: pmult_Cons pexp_Suc)
done
qed


lemma (in semiring_1) poly_one_divides[simp]: "[1] divides p"
by (simp add: divides_def, auto)

lemma (in idom_char_0) poly_order: "poly p \<noteq> poly []
      ==> EX! n. ([-a, 1] %^ n) divides p &
                 ~(([-a, 1] %^ (Suc n)) divides p)"
apply (auto intro: poly_order_exists simp add: less_linear simp del: pmult_Cons pexp_Suc)
apply (cut_tac x = y and y = n in less_linear)
apply (drule_tac m = n in poly_exp_divides)
apply (auto dest: Suc_le_eq [THEN iffD2, THEN [2] poly_exp_divides]
            simp del: pmult_Cons pexp_Suc)
done

text{*Order*}

lemma some1_equalityD: "[| n = (@n. P n); EX! n. P n |] ==> P n"
by (blast intro: someI2)

lemma (in idom_char_0) order:
      "(([-a, 1] %^ n) divides p &
        ~(([-a, 1] %^ (Suc n)) divides p)) =
        ((n = order a p) & ~(poly p = poly []))"
apply (unfold order_def)
apply (rule iffI)
apply (blast dest: poly_divides_zero intro!: some1_equality [symmetric] poly_order)
apply (blast intro!: poly_order [THEN [2] some1_equalityD])
done

lemma (in idom_char_0) order2: "[| poly p \<noteq> poly [] |]
      ==> ([-a, 1] %^ (order a p)) divides p &
              ~(([-a, 1] %^ (Suc(order a p))) divides p)"
by (simp add: order del: pexp_Suc)

lemma (in idom_char_0) order_unique: "[| poly p \<noteq> poly []; ([-a, 1] %^ n) divides p;
         ~(([-a, 1] %^ (Suc n)) divides p)
      |] ==> (n = order a p)"
by (insert order [of a n p], auto)

lemma (in idom_char_0) order_unique_lemma: "(poly p \<noteq> poly [] & ([-a, 1] %^ n) divides p &
         ~(([-a, 1] %^ (Suc n)) divides p))
      ==> (n = order a p)"
by (blast intro: order_unique)

lemma (in ring_1) order_poly: "poly p = poly q ==> order a p = order a q"
by (auto simp add: fun_eq divides_def poly_mult order_def)

lemma (in semiring_1) pexp_one[simp]: "p %^ (Suc 0) = p"
apply (induct "p")
apply (auto simp add: numeral_1_eq_1)
done

lemma (in comm_ring_1) lemma_order_root:
     " 0 < n & [- a, 1] %^ n divides p & ~ [- a, 1] %^ (Suc n) divides p
             \<Longrightarrow> poly p a = 0"
apply (induct n arbitrary: a p, blast)
apply (auto simp add: divides_def poly_mult simp del: pmult_Cons)
done

lemma (in idom_char_0) order_root: "(poly p a = 0) = ((poly p = poly []) | order a p \<noteq> 0)"
proof-
  let ?poly = poly
  show ?thesis
apply (case_tac "?poly p = ?poly []", auto)
apply (simp add: poly_linear_divides del: pmult_Cons, safe)
apply (drule_tac [!] a = a in order2)
apply (rule ccontr)
apply (simp add: divides_def poly_mult fun_eq del: pmult_Cons, blast)
using neq0_conv
apply (blast intro: lemma_order_root)
done
qed

lemma (in idom_char_0) order_divides: "(([-a, 1] %^ n) divides p) = ((poly p = poly []) | n \<le> order a p)"
proof-
  let ?poly = poly
  show ?thesis
apply (case_tac "?poly p = ?poly []", auto)
apply (simp add: divides_def fun_eq poly_mult)
apply (rule_tac x = "[]" in exI)
apply (auto dest!: order2 [where a=a]
            intro: poly_exp_divides simp del: pexp_Suc)
done
qed

lemma (in idom_char_0) order_decomp:
     "poly p \<noteq> poly []
      ==> \<exists>q. (poly p = poly (([-a, 1] %^ (order a p)) *** q)) &
                ~([-a, 1] divides q)"
apply (unfold divides_def)
apply (drule order2 [where a = a])
apply (simp add: divides_def del: pexp_Suc pmult_Cons, safe)
apply (rule_tac x = q in exI, safe)
apply (drule_tac x = qa in spec)
apply (auto simp add: poly_mult fun_eq poly_exp mult_ac simp del: pmult_Cons)
done

text{*Important composition properties of orders.*}
lemma order_mult: "poly (p *** q) \<noteq> poly []
      ==> order a (p *** q) = order a p + order (a::'a::{idom_char_0}) q"
apply (cut_tac a = a and p = "p *** q" and n = "order a p + order a q" in order)
apply (auto simp add: poly_entire simp del: pmult_Cons)
apply (drule_tac a = a in order2)+
apply safe
apply (simp add: divides_def fun_eq poly_exp_add poly_mult del: pmult_Cons, safe)
apply (rule_tac x = "qa *** qaa" in exI)
apply (simp add: poly_mult mult_ac del: pmult_Cons)
apply (drule_tac a = a in order_decomp)+
apply safe
apply (subgoal_tac "[-a,1] divides (qa *** qaa) ")
apply (simp add: poly_primes del: pmult_Cons)
apply (auto simp add: divides_def simp del: pmult_Cons)
apply (rule_tac x = qb in exI)
apply (subgoal_tac "poly ([-a, 1] %^ (order a p) *** (qa *** qaa)) = poly ([-a, 1] %^ (order a p) *** ([-a, 1] *** qb))")
apply (drule poly_mult_left_cancel [THEN iffD1], force)
apply (subgoal_tac "poly ([-a, 1] %^ (order a q) *** ([-a, 1] %^ (order a p) *** (qa *** qaa))) = poly ([-a, 1] %^ (order a q) *** ([-a, 1] %^ (order a p) *** ([-a, 1] *** qb))) ")
apply (drule poly_mult_left_cancel [THEN iffD1], force)
apply (simp add: fun_eq poly_exp_add poly_mult mult_ac del: pmult_Cons)
done

lemma (in idom_char_0) order_mult:
  assumes pq0: "poly (p *** q) \<noteq> poly []"
  shows "order a (p *** q) = order a p + order a q"
proof-
  let ?order = order
  let ?divides = "op divides"
  let ?poly = poly
from pq0
show ?thesis
apply (cut_tac a = a and p = "pmult p q" and n = "?order a p + ?order a q" in order)
apply (auto simp add: poly_entire simp del: pmult_Cons)
apply (drule_tac a = a in order2)+
apply safe
apply (simp add: divides_def fun_eq poly_exp_add poly_mult del: pmult_Cons, safe)
apply (rule_tac x = "pmult qa qaa" in exI)
apply (simp add: poly_mult mult_ac del: pmult_Cons)
apply (drule_tac a = a in order_decomp)+
apply safe
apply (subgoal_tac "?divides [uminus a,one ] (pmult qa qaa) ")
apply (simp add: poly_primes del: pmult_Cons)
apply (auto simp add: divides_def simp del: pmult_Cons)
apply (rule_tac x = qb in exI)
apply (subgoal_tac "?poly (pmult (pexp [uminus a, one] (?order a p)) (pmult qa qaa)) = ?poly (pmult (pexp [uminus a, one] (?order a p)) (pmult [uminus a, one] qb))")
apply (drule poly_mult_left_cancel [THEN iffD1], force)
apply (subgoal_tac "?poly (pmult (pexp [uminus a, one ] (order a q)) (pmult (pexp [uminus a, one] (order a p)) (pmult qa qaa))) = ?poly (pmult (pexp [uminus a, one] (order a q)) (pmult (pexp [uminus a, one] (order a p)) (pmult [uminus a, one] qb))) ")
apply (drule poly_mult_left_cancel [THEN iffD1], force)
apply (simp add: fun_eq poly_exp_add poly_mult mult_ac del: pmult_Cons)
done
qed

lemma (in idom_char_0) order_root2: "poly p \<noteq> poly [] ==> (poly p a = 0) = (order a p \<noteq> 0)"
by (rule order_root [THEN ssubst], auto)

lemma (in semiring_1) pmult_one[simp]: "[1] *** p = p" by auto

lemma (in semiring_0) poly_Nil_zero: "poly [] = poly [0]"
by (simp add: fun_eq)

lemma (in idom_char_0) rsquarefree_decomp:
     "[| rsquarefree p; poly p a = 0 |]
      ==> \<exists>q. (poly p = poly ([-a, 1] *** q)) & poly q a \<noteq> 0"
apply (simp add: rsquarefree_def, safe)
apply (frule_tac a = a in order_decomp)
apply (drule_tac x = a in spec)
apply (drule_tac a = a in order_root2 [symmetric])
apply (auto simp del: pmult_Cons)
apply (rule_tac x = q in exI, safe)
apply (simp add: poly_mult fun_eq)
apply (drule_tac p1 = q in poly_linear_divides [THEN iffD1])
apply (simp add: divides_def del: pmult_Cons, safe)
apply (drule_tac x = "[]" in spec)
apply (auto simp add: fun_eq)
done


text{*Normalization of a polynomial.*}

lemma (in semiring_0) poly_normalize[simp]: "poly (pnormalize p) = poly p"
apply (induct "p")
apply (auto simp add: fun_eq)
done

text{*The degree of a polynomial.*}

lemma (in semiring_0) lemma_degree_zero:
     "list_all (%c. c = 0) p \<longleftrightarrow>  pnormalize p = []"
by (induct "p", auto)

lemma (in idom_char_0) degree_zero:
  assumes pN: "poly p = poly []" shows"degree p = 0"
proof-
  let ?pn = pnormalize
  from pN
  show ?thesis
    apply (simp add: degree_def)
    apply (case_tac "?pn p = []")
    apply (auto simp add: poly_zero lemma_degree_zero )
    done
qed

lemma (in semiring_0) pnormalize_sing: "(pnormalize [x] = [x]) \<longleftrightarrow> x \<noteq> 0"
by simp
lemma (in semiring_0) pnormalize_pair: "y \<noteq> 0 \<longleftrightarrow> (pnormalize [x, y] = [x, y])" by simp
lemma (in semiring_0) pnormal_cons: "pnormal p \<Longrightarrow> pnormal (c#p)"
  unfolding pnormal_def by simp
lemma (in semiring_0) pnormal_tail: "p\<noteq>[] \<Longrightarrow> pnormal (c#p) \<Longrightarrow> pnormal p"
  unfolding pnormal_def by(auto split: split_if_asm)


lemma (in semiring_0) pnormal_last_nonzero: "pnormal p ==> last p \<noteq> 0"
by(induct p) (simp_all add: pnormal_def split: split_if_asm)

lemma (in semiring_0) pnormal_length: "pnormal p \<Longrightarrow> 0 < length p"
  unfolding pnormal_def length_greater_0_conv by blast

lemma (in semiring_0) pnormal_last_length: "\<lbrakk>0 < length p ; last p \<noteq> 0\<rbrakk> \<Longrightarrow> pnormal p"
by (induct p) (auto simp: pnormal_def  split: split_if_asm)


lemma (in semiring_0) pnormal_id: "pnormal p \<longleftrightarrow> (0 < length p \<and> last p \<noteq> 0)"
  using pnormal_last_length pnormal_length pnormal_last_nonzero by blast

lemma (in idom_char_0) poly_Cons_eq: "poly (c#cs) = poly (d#ds) \<longleftrightarrow> c=d \<and> poly cs = poly ds" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume eq: ?lhs
  hence "\<And>x. poly ((c#cs) +++ -- (d#ds)) x = 0"
    by (simp only: poly_minus poly_add algebra_simps) simp
  hence "poly ((c#cs) +++ -- (d#ds)) = poly []" by(simp add: fun_eq_iff)
  hence "c = d \<and> list_all (\<lambda>x. x=0) ((cs +++ -- ds))"
    unfolding poly_zero by (simp add: poly_minus_def algebra_simps)
  hence "c = d \<and> (\<forall>x. poly (cs +++ -- ds) x = 0)"
    unfolding poly_zero[symmetric] by simp
  thus ?rhs  by (simp add: poly_minus poly_add algebra_simps fun_eq_iff)
next
  assume ?rhs then show ?lhs by(simp add:fun_eq_iff)
qed

lemma (in idom_char_0) pnormalize_unique: "poly p = poly q \<Longrightarrow> pnormalize p = pnormalize q"
proof(induct q arbitrary: p)
  case Nil thus ?case by (simp only: poly_zero lemma_degree_zero) simp
next
  case (Cons c cs p)
  thus ?case
  proof(induct p)
    case Nil
    hence "poly [] = poly (c#cs)" by blast
    then have "poly (c#cs) = poly [] " by simp
    thus ?case by (simp only: poly_zero lemma_degree_zero) simp
  next
    case (Cons d ds)
    hence eq: "poly (d # ds) = poly (c # cs)" by blast
    hence eq': "\<And>x. poly (d # ds) x = poly (c # cs) x" by simp
    hence "poly (d # ds) 0 = poly (c # cs) 0" by blast
    hence dc: "d = c" by auto
    with eq have "poly ds = poly cs"
      unfolding  poly_Cons_eq by simp
    with Cons.prems have "pnormalize ds = pnormalize cs" by blast
    with dc show ?case by simp
  qed
qed

lemma (in idom_char_0) degree_unique: assumes pq: "poly p = poly q"
  shows "degree p = degree q"
using pnormalize_unique[OF pq] unfolding degree_def by simp

lemma (in semiring_0) pnormalize_length: "length (pnormalize p) \<le> length p" by (induct p, auto)

lemma (in semiring_0) last_linear_mul_lemma:
  "last ((a %* p) +++ (x#(b %* p))) = (if p=[] then x else b*last p)"

apply (induct p arbitrary: a x b, auto)
apply (subgoal_tac "padd (cmult aa p) (times b a # cmult b p) \<noteq> []", simp)
apply (induct_tac p, auto)
done

lemma (in semiring_1) last_linear_mul: assumes p:"p\<noteq>[]" shows "last ([a,1] *** p) = last p"
proof-
  from p obtain c cs where cs: "p = c#cs" by (cases p, auto)
  from cs have eq:"[a,1] *** p = (a %* (c#cs)) +++ (0#(1 %* (c#cs)))"
    by (simp add: poly_cmult_distr)
  show ?thesis using cs
    unfolding eq last_linear_mul_lemma by simp
qed

lemma (in semiring_0) pnormalize_eq: "last p \<noteq> 0 \<Longrightarrow> pnormalize p = p"
by (induct p) (auto split: split_if_asm)

lemma (in semiring_0) last_pnormalize: "pnormalize p \<noteq> [] \<Longrightarrow> last (pnormalize p) \<noteq> 0"
  by (induct p, auto)

lemma (in semiring_0) pnormal_degree: "last p \<noteq> 0 \<Longrightarrow> degree p = length p - 1"
  using pnormalize_eq[of p] unfolding degree_def by simp

lemma (in semiring_0) poly_Nil_ext: "poly [] = (\<lambda>x. 0)" by (rule ext) simp

lemma (in idom_char_0) linear_mul_degree: assumes p: "poly p \<noteq> poly []"
  shows "degree ([a,1] *** p) = degree p + 1"
proof-
  from p have pnz: "pnormalize p \<noteq> []"
    unfolding poly_zero lemma_degree_zero .

  from last_linear_mul[OF pnz, of a] last_pnormalize[OF pnz]
  have l0: "last ([a, 1] *** pnormalize p) \<noteq> 0" by simp
  from last_pnormalize[OF pnz] last_linear_mul[OF pnz, of a]
    pnormal_degree[OF l0] pnormal_degree[OF last_pnormalize[OF pnz]] pnz


  have th: "degree ([a,1] *** pnormalize p) = degree (pnormalize p) + 1"
    by (auto simp add: poly_length_mult)

  have eqs: "poly ([a,1] *** pnormalize p) = poly ([a,1] *** p)"
    by (rule ext) (simp add: poly_mult poly_add poly_cmult)
  from degree_unique[OF eqs] th
  show ?thesis by (simp add: degree_unique[OF poly_normalize])
qed

lemma (in idom_char_0) linear_pow_mul_degree:
  "degree([a,1] %^n *** p) = (if poly p = poly [] then 0 else degree p + n)"
proof(induct n arbitrary: a p)
  case (0 a p)
  {assume p: "poly p = poly []"
    hence ?case using degree_unique[OF p] by (simp add: degree_def)}
  moreover
  {assume p: "poly p \<noteq> poly []" hence ?case by (auto simp add: poly_Nil_ext) }
  ultimately show ?case by blast
next
  case (Suc n a p)
  have eq: "poly ([a,1] %^(Suc n) *** p) = poly ([a,1] %^ n *** ([a,1] *** p))"
    apply (rule ext, simp add: poly_mult poly_add poly_cmult)
    by (simp add: mult_ac add_ac right_distrib)
  note deq = degree_unique[OF eq]
  {assume p: "poly p = poly []"
    with eq have eq': "poly ([a,1] %^(Suc n) *** p) = poly []"
      by - (rule ext,simp add: poly_mult poly_cmult poly_add)
    from degree_unique[OF eq'] p have ?case by (simp add: degree_def)}
  moreover
  {assume p: "poly p \<noteq> poly []"
    from p have ap: "poly ([a,1] *** p) \<noteq> poly []"
      using poly_mult_not_eq_poly_Nil unfolding poly_entire by auto
    have eq: "poly ([a,1] %^(Suc n) *** p) = poly ([a,1]%^n *** ([a,1] *** p))"
     by (rule ext, simp add: poly_mult poly_add poly_exp poly_cmult algebra_simps)
   from ap have ap': "(poly ([a,1] *** p) = poly []) = False" by blast
   have  th0: "degree ([a,1]%^n *** ([a,1] *** p)) = degree ([a,1] *** p) + n"
     apply (simp only: Suc.hyps[of a "pmult [a,one] p"] ap')
     by simp

   from degree_unique[OF eq] ap p th0 linear_mul_degree[OF p, of a]
   have ?case by (auto simp del: poly.simps)}
  ultimately show ?case by blast
qed

lemma (in idom_char_0) order_degree:
  assumes p0: "poly p \<noteq> poly []"
  shows "order a p \<le> degree p"
proof-
  from order2[OF p0, unfolded divides_def]
  obtain q where q: "poly p = poly ([- a, 1]%^ (order a p) *** q)" by blast
  {assume "poly q = poly []"
    with q p0 have False by (simp add: poly_mult poly_entire)}
  with degree_unique[OF q, unfolded linear_pow_mul_degree]
  show ?thesis by auto
qed

text{*Tidier versions of finiteness of roots.*}

lemma (in idom_char_0) poly_roots_finite_set: "poly p \<noteq> poly [] ==> finite {x. poly p x = 0}"
unfolding poly_roots_finite .

text{*bound for polynomial.*}

lemma poly_mono: "abs(x) \<le> k ==> abs(poly p (x::'a::{linordered_idom})) \<le> poly (map abs p) k"
apply (induct "p", auto)
apply (rule_tac y = "abs a + abs (x * poly p x)" in order_trans)
apply (rule abs_triangle_ineq)
apply (auto intro!: mult_mono simp add: abs_mult)
done

lemma (in semiring_0) poly_Sing: "poly [c] x = c" by simp

end
