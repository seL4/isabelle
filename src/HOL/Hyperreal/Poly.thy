(*  Title:       Poly.thy
    ID:         $Id$
    Author:      Jacques D. Fleuriot
    Copyright:   2000 University of Edinburgh

    Conversion to Isar and new proofs by Lawrence C Paulson, 2003/4
*)

header{*Univariate Real Polynomials*}

theory Poly = Transcendental:


text{*Application of polynomial as a real function.*}

consts poly :: "real list => real => real"
primrec
  poly_Nil:  "poly [] x = 0"
  poly_Cons: "poly (h#t) x = h + x * poly t x"


subsection{*Arithmetic Operations on Polynomials*}

text{*addition*}
consts "+++" :: "[real list, real list] => real list"  (infixl 65)
primrec
  padd_Nil:  "[] +++ l2 = l2"
  padd_Cons: "(h#t) +++ l2 = (if l2 = [] then h#t
                            else (h + hd l2)#(t +++ tl l2))"

text{*Multiplication by a constant*}
consts "%*" :: "[real, real list] => real list"  (infixl 70)
primrec
   cmult_Nil:  "c %* [] = []"
   cmult_Cons: "c %* (h#t) = (c * h)#(c %* t)"

text{*Multiplication by a polynomial*}
consts "***" :: "[real list, real list] => real list"  (infixl 70)
primrec
   pmult_Nil:  "[] *** l2 = []"
   pmult_Cons: "(h#t) *** l2 = (if t = [] then h %* l2
                              else (h %* l2) +++ ((0) # (t *** l2)))"

text{*Repeated multiplication by a polynomial*}
consts mulexp :: "[nat, real list, real list] => real list"
primrec
   mulexp_zero:  "mulexp 0 p q = q"
   mulexp_Suc:   "mulexp (Suc n) p q = p *** mulexp n p q"


text{*Exponential*}
consts "%^" :: "[real list, nat] => real list"  (infixl 80)
primrec
   pexp_0:   "p %^ 0 = [1]"
   pexp_Suc: "p %^ (Suc n) = p *** (p %^ n)"

text{*Quotient related value of dividing a polynomial by x + a*}
(* Useful for divisor properties in inductive proofs *)
consts "pquot" :: "[real list, real] => real list"
primrec
   pquot_Nil:  "pquot [] a= []"
   pquot_Cons: "pquot (h#t) a = (if t = [] then [h]
                   else (inverse(a) * (h - hd( pquot t a)))#(pquot t a))"

text{*Differentiation of polynomials (needs an auxiliary function).*}
consts pderiv_aux :: "nat => real list => real list"
primrec
   pderiv_aux_Nil:  "pderiv_aux n [] = []"
   pderiv_aux_Cons: "pderiv_aux n (h#t) =
                     (real n * h)#(pderiv_aux (Suc n) t)"

text{*normalization of polynomials (remove extra 0 coeff)*}
consts pnormalize :: "real list => real list"
primrec
   pnormalize_Nil:  "pnormalize [] = []"
   pnormalize_Cons: "pnormalize (h#p) = (if ( (pnormalize p) = [])
                                     then (if (h = 0) then [] else [h])
                                     else (h#(pnormalize p)))"


text{*Other definitions*}

constdefs
   poly_minus :: "real list => real list"      ("-- _" [80] 80)
   "-- p == (- 1) %* p"

   pderiv :: "real list => real list"
   "pderiv p == if p = [] then [] else pderiv_aux 1 (tl p)"

   divides :: "[real list,real list] => bool"  (infixl "divides" 70)
   "p1 divides p2 == \<exists>q. poly p2 = poly(p1 *** q)"

   order :: "real => real list => nat"
     --{*order of a polynomial*}
   "order a p == (@n. ([-a, 1] %^ n) divides p &
                      ~ (([-a, 1] %^ (Suc n)) divides p))"

   degree :: "real list => nat"
     --{*degree of a polynomial*}
   "degree p == length (pnormalize p)"

   rsquarefree :: "real list => bool"
     --{*squarefree polynomials --- NB with respect to real roots only.*}
   "rsquarefree p == poly p \<noteq> poly [] &
                     (\<forall>a. (order a p = 0) | (order a p = 1))"



lemma padd_Nil2: "p +++ [] = p"
by (induct_tac "p", auto)
declare padd_Nil2 [simp]

lemma padd_Cons_Cons: "(h1 # p1) +++ (h2 # p2) = (h1 + h2) # (p1 +++ p2)"
by auto

lemma pminus_Nil: "-- [] = []"
by (simp add: poly_minus_def)
declare pminus_Nil [simp]

lemma pmult_singleton: "[h1] *** p1 = h1 %* p1"
by simp

lemma poly_ident_mult: "1 %* t = t"
by (induct_tac "t", auto)
declare poly_ident_mult [simp]

lemma poly_simple_add_Cons: "[a] +++ ((0)#t) = (a#t)"
by simp
declare poly_simple_add_Cons [simp]

text{*Handy general properties*}

lemma padd_commut: "b +++ a = a +++ b"
apply (subgoal_tac "\<forall>a. b +++ a = a +++ b")
apply (induct_tac [2] "b", auto)
apply (rule padd_Cons [THEN ssubst])
apply (case_tac "aa", auto)
done

lemma padd_assoc [rule_format]: "\<forall>b c. (a +++ b) +++ c = a +++ (b +++ c)"
apply (induct_tac "a", simp, clarify)
apply (case_tac b, simp_all)
done

lemma poly_cmult_distr [rule_format]:
     "\<forall>q. a %* ( p +++ q) = (a %* p +++ a %* q)"
apply (induct_tac "p", simp, clarify)
apply (case_tac "q")
apply (simp_all add: right_distrib)
done

lemma pmult_by_x: "[0, 1] *** t = ((0)#t)"
apply (induct_tac "t", simp)
apply (simp add: poly_ident_mult padd_commut)
apply (case_tac "list")
apply (simp (no_asm_simp))
apply (simp add: poly_ident_mult padd_commut)
done
declare pmult_by_x [simp]


text{*properties of evaluation of polynomials.*}

lemma poly_add: "poly (p1 +++ p2) x = poly p1 x + poly p2 x"
apply (subgoal_tac "\<forall>p2. poly (p1 +++ p2) x = poly (p1) x + poly (p2) x")
apply (induct_tac [2] "p1", auto)
apply (case_tac "p2")
apply (auto simp add: right_distrib)
done

lemma poly_cmult: "poly (c %* p) x = c * poly p x"
apply (induct_tac "p")
apply (case_tac [2] "x=0")
apply (auto simp add: right_distrib mult_ac)
done

lemma poly_minus: "poly (-- p) x = - (poly p x)"
apply (simp add: poly_minus_def)
apply (auto simp add: poly_cmult)
done

lemma poly_mult: "poly (p1 *** p2) x = poly p1 x * poly p2 x"
apply (subgoal_tac "\<forall>p2. poly (p1 *** p2) x = poly p1 x * poly p2 x")
apply (simp (no_asm_simp))
apply (induct_tac "p1")
apply (auto simp add: poly_cmult)
apply (case_tac "list")
apply (auto simp add: poly_cmult poly_add left_distrib right_distrib mult_ac)
done

lemma poly_exp: "poly (p %^ n) x = (poly p x) ^ n"
apply (induct_tac "n")
apply (auto simp add: poly_cmult poly_mult)
done

text{*More Polynomial Evaluation Lemmas*}

lemma poly_add_rzero: "poly (a +++ []) x = poly a x"
by simp
declare poly_add_rzero [simp]

lemma poly_mult_assoc: "poly ((a *** b) *** c) x = poly (a *** (b *** c)) x"
by (simp add: poly_mult real_mult_assoc)

lemma poly_mult_Nil2: "poly (p *** []) x = 0"
by (induct_tac "p", auto)
declare poly_mult_Nil2 [simp]

lemma poly_exp_add: "poly (p %^ (n + d)) x = poly( p %^ n *** p %^ d) x"
apply (induct_tac "n")
apply (auto simp add: poly_mult real_mult_assoc)
done

text{*The derivative*}

lemma pderiv_Nil: "pderiv [] = []"

apply (simp add: pderiv_def)
done
declare pderiv_Nil [simp]

lemma pderiv_singleton: "pderiv [c] = []"
by (simp add: pderiv_def)
declare pderiv_singleton [simp]

lemma pderiv_Cons: "pderiv (h#t) = pderiv_aux 1 t"
by (simp add: pderiv_def)

lemma DERIV_cmult2: "DERIV f x :> D ==> DERIV (%x. (f x) * c) x :> D * c"
by (simp add: DERIV_cmult mult_commute [of _ c])

lemma DERIV_pow2: "DERIV (%x. x ^ Suc n) x :> real (Suc n) * (x ^ n)"
by (rule lemma_DERIV_subst, rule DERIV_pow, simp)
declare DERIV_pow2 [simp] DERIV_pow [simp]

lemma lemma_DERIV_poly1: "\<forall>n. DERIV (%x. (x ^ (Suc n) * poly p x)) x :>
        x ^ n * poly (pderiv_aux (Suc n) p) x "
apply (induct_tac "p")
apply (auto intro!: DERIV_add DERIV_cmult2 
            simp add: pderiv_def right_distrib real_mult_assoc [symmetric] 
            simp del: realpow_Suc)
apply (subst mult_commute) 
apply (simp del: realpow_Suc) 
apply (simp add: mult_commute realpow_Suc [symmetric] del: realpow_Suc)
done

lemma lemma_DERIV_poly: "DERIV (%x. (x ^ (Suc n) * poly p x)) x :>
        x ^ n * poly (pderiv_aux (Suc n) p) x "
by (simp add: lemma_DERIV_poly1 del: realpow_Suc)

lemma DERIV_add_const: "DERIV f x :> D ==>  DERIV (%x. a + f x) x :> D"
by (rule lemma_DERIV_subst, rule DERIV_add, auto)

lemma poly_DERIV: "DERIV (%x. poly p x) x :> poly (pderiv p) x"
apply (induct_tac "p")
apply (auto simp add: pderiv_Cons)
apply (rule DERIV_add_const)
apply (rule lemma_DERIV_subst)
apply (rule lemma_DERIV_poly [where n=0, simplified], simp) 
done
declare poly_DERIV [simp]


text{* Consequences of the derivative theorem above*}

lemma poly_differentiable: "(%x. poly p x) differentiable x"

apply (simp add: differentiable_def)
apply (blast intro: poly_DERIV)
done
declare poly_differentiable [simp]

lemma poly_isCont: "isCont (%x. poly p x) x"
by (rule poly_DERIV [THEN DERIV_isCont])
declare poly_isCont [simp]

lemma poly_IVT_pos: "[| a < b; poly p a < 0; 0 < poly p b |]
      ==> \<exists>x. a < x & x < b & (poly p x = 0)"
apply (cut_tac f = "%x. poly p x" and a = a and b = b and y = 0 in IVT_objl)
apply (auto simp add: order_le_less)
done

lemma poly_IVT_neg: "[| a < b; 0 < poly p a; poly p b < 0 |]
      ==> \<exists>x. a < x & x < b & (poly p x = 0)"
apply (insert poly_IVT_pos [where p = "-- p" ]) 
apply (simp add: poly_minus neg_less_0_iff_less) 
done

lemma poly_MVT: "a < b ==>
     \<exists>x. a < x & x < b & (poly p b - poly p a = (b - a) * poly (pderiv p) x)"
apply (drule_tac f = "poly p" in MVT, auto)
apply (rule_tac x = z in exI)
apply (auto simp add: real_mult_left_cancel poly_DERIV [THEN DERIV_unique])
done


text{*Lemmas for Derivatives*}

lemma lemma_poly_pderiv_aux_add: "\<forall>p2 n. poly (pderiv_aux n (p1 +++ p2)) x =
                poly (pderiv_aux n p1 +++ pderiv_aux n p2) x"
apply (induct_tac "p1", simp, clarify) 
apply (case_tac "p2")
apply (auto simp add: right_distrib)
done

lemma poly_pderiv_aux_add: "poly (pderiv_aux n (p1 +++ p2)) x =
      poly (pderiv_aux n p1 +++ pderiv_aux n p2) x"
apply (simp add: lemma_poly_pderiv_aux_add)
done

lemma lemma_poly_pderiv_aux_cmult: "\<forall>n. poly (pderiv_aux n (c %* p)) x = poly (c %* pderiv_aux n p) x"
apply (induct_tac "p")
apply (auto simp add: poly_cmult mult_ac)
done

lemma poly_pderiv_aux_cmult: "poly (pderiv_aux n (c %* p)) x = poly (c %* pderiv_aux n p) x"
by (simp add: lemma_poly_pderiv_aux_cmult)

lemma poly_pderiv_aux_minus:
   "poly (pderiv_aux n (-- p)) x = poly (-- pderiv_aux n p) x"
apply (simp add: poly_minus_def poly_pderiv_aux_cmult)
done

lemma lemma_poly_pderiv_aux_mult1: "\<forall>n. poly (pderiv_aux (Suc n) p) x = poly ((pderiv_aux n p) +++ p) x"
apply (induct_tac "p")
apply (auto simp add: real_of_nat_Suc left_distrib)
done

lemma lemma_poly_pderiv_aux_mult: "poly (pderiv_aux (Suc n) p) x = poly ((pderiv_aux n p) +++ p) x"
by (simp add: lemma_poly_pderiv_aux_mult1)

lemma lemma_poly_pderiv_add: "\<forall>q. poly (pderiv (p +++ q)) x = poly (pderiv p +++ pderiv q) x"
apply (induct_tac "p", simp, clarify) 
apply (case_tac "q")
apply (auto simp add: poly_pderiv_aux_add poly_add pderiv_def)
done

lemma poly_pderiv_add: "poly (pderiv (p +++ q)) x = poly (pderiv p +++ pderiv q) x"
by (simp add: lemma_poly_pderiv_add)

lemma poly_pderiv_cmult: "poly (pderiv (c %* p)) x = poly (c %* (pderiv p)) x"
apply (induct_tac "p")
apply (auto simp add: poly_pderiv_aux_cmult poly_cmult pderiv_def)
done

lemma poly_pderiv_minus: "poly (pderiv (--p)) x = poly (--(pderiv p)) x"
by (simp add: poly_minus_def poly_pderiv_cmult)

lemma lemma_poly_mult_pderiv:
   "poly (pderiv (h#t)) x = poly ((0 # (pderiv t)) +++ t) x"
apply (simp add: pderiv_def)
apply (induct_tac "t")
apply (auto simp add: poly_add lemma_poly_pderiv_aux_mult)
done

lemma poly_pderiv_mult: "\<forall>q. poly (pderiv (p *** q)) x =
      poly (p *** (pderiv q) +++ q *** (pderiv p)) x"
apply (induct_tac "p")
apply (auto simp add: poly_add poly_cmult poly_pderiv_cmult poly_pderiv_add poly_mult)
apply (rule lemma_poly_mult_pderiv [THEN ssubst])
apply (rule lemma_poly_mult_pderiv [THEN ssubst])
apply (rule poly_add [THEN ssubst])
apply (rule poly_add [THEN ssubst])
apply (simp (no_asm_simp) add: poly_mult right_distrib add_ac mult_ac)
done

lemma poly_pderiv_exp: "poly (pderiv (p %^ (Suc n))) x =
         poly ((real (Suc n)) %* (p %^ n) *** pderiv p) x"
apply (induct_tac "n")
apply (auto simp add: poly_add poly_pderiv_cmult poly_cmult poly_pderiv_mult
                      real_of_nat_zero poly_mult real_of_nat_Suc 
                      right_distrib left_distrib mult_ac)
done

lemma poly_pderiv_exp_prime: "poly (pderiv ([-a, 1] %^ (Suc n))) x =
      poly (real (Suc n) %* ([-a, 1] %^ n)) x"
apply (simp add: poly_pderiv_exp poly_mult del: pexp_Suc)
apply (simp add: poly_cmult pderiv_def)
done

subsection{*Key Property: if @{term "f(a) = 0"} then @{term "(x - a)"} divides
 @{term "p(x)"} *}

lemma lemma_poly_linear_rem: "\<forall>h. \<exists>q r. h#t = [r] +++ [-a, 1] *** q"
apply (induct_tac "t", safe)
apply (rule_tac x = "[]" in exI)
apply (rule_tac x = h in exI, simp)
apply (drule_tac x = aa in spec, safe)
apply (rule_tac x = "r#q" in exI)
apply (rule_tac x = "a*r + h" in exI)
apply (case_tac "q", auto)
done

lemma poly_linear_rem: "\<exists>q r. h#t = [r] +++ [-a, 1] *** q"
by (cut_tac t = t and a = a in lemma_poly_linear_rem, auto)


lemma poly_linear_divides: "(poly p a = 0) = ((p = []) | (\<exists>q. p = [-a, 1] *** q))"
apply (auto simp add: poly_add poly_cmult right_distrib)
apply (case_tac "p", simp) 
apply (cut_tac h = aa and t = list and a = a in poly_linear_rem, safe)
apply (case_tac "q", auto)
apply (drule_tac x = "[]" in spec, simp)
apply (auto simp add: poly_add poly_cmult real_add_assoc)
apply (drule_tac x = "aa#lista" in spec, auto)
done

lemma lemma_poly_length_mult: "\<forall>h k a. length (k %* p +++  (h # (a %* p))) = Suc (length p)"
by (induct_tac "p", auto)
declare lemma_poly_length_mult [simp]

lemma lemma_poly_length_mult2: "\<forall>h k. length (k %* p +++  (h # p)) = Suc (length p)"
by (induct_tac "p", auto)
declare lemma_poly_length_mult2 [simp]

lemma poly_length_mult: "length([-a,1] *** q) = Suc (length q)"
by auto
declare poly_length_mult [simp]


subsection{*Polynomial length*}

lemma poly_cmult_length: "length (a %* p) = length p"
by (induct_tac "p", auto)
declare poly_cmult_length [simp]

lemma poly_add_length [rule_format]:
     "\<forall>p2. length (p1 +++ p2) =
             (if (length p1 < length p2) then length p2 else length p1)"
apply (induct_tac "p1", simp_all, arith)
done

lemma poly_root_mult_length: "length([a,b] *** p) = Suc (length p)"
by (simp add: poly_cmult_length poly_add_length)
declare poly_root_mult_length [simp]

lemma poly_mult_not_eq_poly_Nil: "(poly (p *** q) x \<noteq> poly [] x) =
      (poly p x \<noteq> poly [] x & poly q x \<noteq> poly [] x)"
apply (auto simp add: poly_mult)
done
declare poly_mult_not_eq_poly_Nil [simp]

lemma poly_mult_eq_zero_disj: "(poly (p *** q) x = 0) = (poly p x = 0 | poly q x = 0)"
by (auto simp add: poly_mult)

text{*Normalisation Properties*}

lemma poly_normalized_nil: "(pnormalize p = []) --> (poly p x = 0)"
by (induct_tac "p", auto)

text{*A nontrivial polynomial of degree n has no more than n roots*}

lemma poly_roots_index_lemma [rule_format]:
   "\<forall>p x. poly p x \<noteq> poly [] x & length p = n
    --> (\<exists>i. \<forall>x. (poly p x = (0::real)) --> (\<exists>m. (m \<le> n & x = i m)))"
apply (induct_tac "n", safe)
apply (rule ccontr)
apply (subgoal_tac "\<exists>a. poly p a = 0", safe)
apply (drule poly_linear_divides [THEN iffD1], safe)
apply (drule_tac x = q in spec)
apply (drule_tac x = x in spec)
apply (simp del: poly_Nil pmult_Cons)
apply (erule exE)
apply (drule_tac x = "%m. if m = Suc n then a else i m" in spec, safe)
apply (drule poly_mult_eq_zero_disj [THEN iffD1], safe)
apply (drule_tac x = "Suc (length q) " in spec)
apply simp
apply (drule_tac x = xa in spec, safe)
apply (drule_tac x = m in spec, simp, blast)
done
lemmas poly_roots_index_lemma2 = conjI [THEN poly_roots_index_lemma, standard]

lemma poly_roots_index_length: "poly p x \<noteq> poly [] x ==>
      \<exists>i. \<forall>x. (poly p x = 0) --> (\<exists>n. n \<le> length p & x = i n)"
by (blast intro: poly_roots_index_lemma2)

lemma poly_roots_finite_lemma: "poly p x \<noteq> poly [] x ==>
      \<exists>N i. \<forall>x. (poly p x = 0) --> (\<exists>n. (n::nat) < N & x = i n)"
apply (drule poly_roots_index_length, safe)
apply (rule_tac x = "Suc (length p) " in exI)
apply (rule_tac x = i in exI) 
apply (simp add: less_Suc_eq_le)
done

(* annoying proof *)
lemma real_finite_lemma [rule_format (no_asm)]:
     "\<forall>P. (\<forall>x. P x --> (\<exists>n. (n::nat) < N & x = (j::nat=>real) n))
      --> (\<exists>a. \<forall>x. P x --> x < a)"
apply (induct_tac "N", simp, safe)
apply (drule_tac x = "%z. P z & (z \<noteq> (j::nat=>real) n) " in spec)
apply auto
apply (drule_tac x = x in spec, safe)
apply (rule_tac x = na in exI)
apply (auto simp add: less_Suc_eq) 
apply (rule_tac x = "abs a + abs (j n) + 1" in exI)
apply safe
apply (drule_tac x = x in spec, safe)
apply (drule_tac x = "j na" in spec, arith+)
done

lemma poly_roots_finite: "(poly p \<noteq> poly []) =
      (\<exists>N j. \<forall>x. poly p x = 0 --> (\<exists>n. (n::nat) < N & x = j n))"
apply safe
apply (erule swap, rule ext)
apply (rule ccontr)
apply (clarify dest!: poly_roots_finite_lemma)
apply (clarify dest!: real_finite_lemma)
apply (drule_tac x = a in fun_cong, auto)
done

text{*Entirety and Cancellation for polynomials*}

lemma poly_entire_lemma: "[| poly p \<noteq> poly [] ; poly q \<noteq> poly [] |]
      ==>  poly (p *** q) \<noteq> poly []"
apply (auto simp add: poly_roots_finite)
apply (rule_tac x = "N + Na" in exI)
apply (rule_tac x = "%n. if n < N then j n else ja (n - N) " in exI)
apply (auto simp add: poly_mult_eq_zero_disj, force) 
done

lemma poly_entire: "(poly (p *** q) = poly []) = ((poly p = poly []) | (poly q = poly []))"
apply (auto intro: ext dest: fun_cong simp add: poly_entire_lemma poly_mult)
apply (blast intro: ccontr dest: poly_entire_lemma poly_mult [THEN subst])
done

lemma poly_entire_neg: "(poly (p *** q) \<noteq> poly []) = ((poly p \<noteq> poly []) & (poly q \<noteq> poly []))"
by (simp add: poly_entire)

lemma fun_eq: " (f = g) = (\<forall>x. f x = g x)"
by (auto intro!: ext)

lemma poly_add_minus_zero_iff: "(poly (p +++ -- q) = poly []) = (poly p = poly q)"
by (auto simp add: poly_add poly_minus_def fun_eq poly_cmult)

lemma poly_add_minus_mult_eq: "poly (p *** q +++ --(p *** r)) = poly (p *** (q +++ -- r))"
by (auto simp add: poly_add poly_minus_def fun_eq poly_mult poly_cmult right_distrib)

lemma poly_mult_left_cancel: "(poly (p *** q) = poly (p *** r)) = (poly p = poly [] | poly q = poly r)"
apply (rule_tac p1 = "p *** q" in poly_add_minus_zero_iff [THEN subst])
apply (auto intro: ext simp add: poly_add_minus_mult_eq poly_entire poly_add_minus_zero_iff)
done

lemma real_mult_zero_disj_iff: "(x * y = 0) = (x = (0::real) | y = 0)"
by simp

lemma poly_exp_eq_zero:
     "(poly (p %^ n) = poly []) = (poly p = poly [] & n \<noteq> 0)"
apply (simp only: fun_eq add: all_simps [symmetric]) 
apply (rule arg_cong [where f = All]) 
apply (rule ext)
apply (induct_tac "n")
apply (auto simp add: poly_mult real_mult_zero_disj_iff)
done
declare poly_exp_eq_zero [simp]

lemma poly_prime_eq_zero: "poly [a,1] \<noteq> poly []"
apply (simp add: fun_eq)
apply (rule_tac x = "1 - a" in exI, simp)
done
declare poly_prime_eq_zero [simp]

lemma poly_exp_prime_eq_zero: "(poly ([a, 1] %^ n) \<noteq> poly [])"
by auto
declare poly_exp_prime_eq_zero [simp]

text{*A more constructive notion of polynomials being trivial*}

lemma poly_zero_lemma: "poly (h # t) = poly [] ==> h = 0 & poly t = poly []"
apply (simp add: fun_eq)
apply (case_tac "h = 0")
apply (drule_tac [2] x = 0 in spec, auto) 
apply (case_tac "poly t = poly []", simp) 
apply (auto simp add: poly_roots_finite real_mult_zero_disj_iff)
apply (drule real_finite_lemma, safe)
apply (drule_tac x = "abs a + 1" in spec)+
apply arith
done


lemma poly_zero: "(poly p = poly []) = list_all (%c. c = 0) p"
apply (induct_tac "p", simp)
apply (rule iffI)
apply (drule poly_zero_lemma, auto)
done

declare real_mult_zero_disj_iff [simp]

lemma pderiv_aux_iszero [rule_format, simp]:
    "\<forall>n. list_all (%c. c = 0) (pderiv_aux (Suc n) p) = list_all (%c. c = 0) p"
by (induct_tac "p", auto)

lemma pderiv_aux_iszero_num: "(number_of n :: nat) \<noteq> 0
      ==> (list_all (%c. c = 0) (pderiv_aux (number_of n) p) =
      list_all (%c. c = 0) p)"
apply (rule_tac n1 = "number_of n" and m1 = 0 in less_imp_Suc_add [THEN exE], force)
apply (rule_tac n1 = "0 + x" in pderiv_aux_iszero [THEN subst])
apply (simp (no_asm_simp) del: pderiv_aux_iszero)
done

lemma pderiv_iszero [rule_format]:
     "poly (pderiv p) = poly [] --> (\<exists>h. poly p = poly [h])"
apply (simp add: poly_zero)
apply (induct_tac "p", force)
apply (simp add: pderiv_Cons pderiv_aux_iszero_num del: poly_Cons)
apply (auto simp add: poly_zero [symmetric])
done

lemma pderiv_zero_obj: "poly p = poly [] --> (poly (pderiv p) = poly [])"
apply (simp add: poly_zero)
apply (induct_tac "p", force)
apply (simp add: pderiv_Cons pderiv_aux_iszero_num del: poly_Cons)
done

lemma pderiv_zero: "poly p = poly [] ==> (poly (pderiv p) = poly [])"
by (blast elim: pderiv_zero_obj [THEN impE])
declare pderiv_zero [simp]

lemma poly_pderiv_welldef: "poly p = poly q ==> (poly (pderiv p) = poly (pderiv q))"
apply (cut_tac p = "p +++ --q" in pderiv_zero_obj)
apply (simp add: fun_eq poly_add poly_minus poly_pderiv_add poly_pderiv_minus del: pderiv_zero)
done

text{*Basics of divisibility.*}

lemma poly_primes: "([a, 1] divides (p *** q)) = ([a, 1] divides p | [a, 1] divides q)"
apply (auto simp add: divides_def fun_eq poly_mult poly_add poly_cmult left_distrib [symmetric])
apply (drule_tac x = "-a" in spec)
apply (auto simp add: poly_linear_divides poly_add poly_cmult left_distrib [symmetric])
apply (rule_tac x = "qa *** q" in exI)
apply (rule_tac [2] x = "p *** qa" in exI)
apply (auto simp add: poly_add poly_mult poly_cmult mult_ac)
done

lemma poly_divides_refl: "p divides p"
apply (simp add: divides_def)
apply (rule_tac x = "[1]" in exI)
apply (auto simp add: poly_mult fun_eq)
done
declare poly_divides_refl [simp]

lemma poly_divides_trans: "[| p divides q; q divides r |] ==> p divides r"
apply (simp add: divides_def, safe)
apply (rule_tac x = "qa *** qaa" in exI)
apply (auto simp add: poly_mult fun_eq real_mult_assoc)
done

lemma le_iff_add: "(m::nat) \<le> n = (\<exists>d. n = m + d)"
by (auto simp add: le_eq_less_or_eq less_iff_Suc_add)

lemma poly_divides_exp: "m \<le> n ==> (p %^ m) divides (p %^ n)"
apply (auto simp add: le_iff_add)
apply (induct_tac "d")
apply (rule_tac [2] poly_divides_trans)
apply (auto simp add: divides_def)
apply (rule_tac x = p in exI)
apply (auto simp add: poly_mult fun_eq mult_ac)
done

lemma poly_exp_divides: "[| (p %^ n) divides q;  m \<le> n |] ==> (p %^ m) divides q"
by (blast intro: poly_divides_exp poly_divides_trans)

lemma poly_divides_add:
   "[| p divides q; p divides r |] ==> p divides (q +++ r)"
apply (simp add: divides_def, auto)
apply (rule_tac x = "qa +++ qaa" in exI)
apply (auto simp add: poly_add fun_eq poly_mult right_distrib)
done

lemma poly_divides_diff:
   "[| p divides q; p divides (q +++ r) |] ==> p divides r"
apply (simp add: divides_def, auto)
apply (rule_tac x = "qaa +++ -- qa" in exI)
apply (auto simp add: poly_add fun_eq poly_mult poly_minus right_diff_distrib compare_rls add_ac)
done

lemma poly_divides_diff2: "[| p divides r; p divides (q +++ r) |] ==> p divides q"
apply (erule poly_divides_diff)
apply (auto simp add: poly_add fun_eq poly_mult divides_def add_ac)
done

lemma poly_divides_zero: "poly p = poly [] ==> q divides p"
apply (simp add: divides_def)
apply (auto simp add: fun_eq poly_mult)
done

lemma poly_divides_zero2: "q divides []"
apply (simp add: divides_def)
apply (rule_tac x = "[]" in exI)
apply (auto simp add: fun_eq)
done
declare poly_divides_zero2 [simp]

text{*At last, we can consider the order of a root.*}


lemma poly_order_exists_lemma [rule_format]:
     "\<forall>p. length p = d --> poly p \<noteq> poly [] 
             --> (\<exists>n q. p = mulexp n [-a, 1] q & poly q a \<noteq> 0)"
apply (induct_tac "d")
apply (simp add: fun_eq, safe)
apply (case_tac "poly p a = 0")
apply (drule_tac poly_linear_divides [THEN iffD1], safe)
apply (drule_tac x = q in spec)
apply (drule_tac poly_entire_neg [THEN iffD1], safe, force, blast) 
apply (rule_tac x = "Suc na" in exI)
apply (rule_tac x = qa in exI)
apply (simp del: pmult_Cons)
apply (rule_tac x = 0 in exI, force) 
done

(* FIXME: Tidy up *)
lemma poly_order_exists:
     "[| length p = d; poly p \<noteq> poly [] |]
      ==> \<exists>n. ([-a, 1] %^ n) divides p &
                ~(([-a, 1] %^ (Suc n)) divides p)"
apply (drule poly_order_exists_lemma [where a=a], assumption, clarify)  
apply (rule_tac x = n in exI, safe)
apply (unfold divides_def)
apply (rule_tac x = q in exI)
apply (induct_tac "n", simp)
apply (simp (no_asm_simp) add: poly_add poly_cmult poly_mult right_distrib mult_ac)
apply safe
apply (subgoal_tac "poly (mulexp n [- a, 1] q) \<noteq> poly ([- a, 1] %^ Suc n *** qa)") 
apply simp 
apply (induct_tac "n")
apply (simp del: pmult_Cons pexp_Suc)
apply (erule_tac Pa = "poly q a = 0" in swap)
apply (simp add: poly_add poly_cmult)
apply (rule pexp_Suc [THEN ssubst])
apply (rule ccontr)
apply (simp add: poly_mult_left_cancel poly_mult_assoc del: pmult_Cons pexp_Suc)
done

lemma poly_one_divides: "[1] divides p"
by (simp add: divides_def, auto)
declare poly_one_divides [simp]

lemma poly_order: "poly p \<noteq> poly []
      ==> EX! n. ([-a, 1] %^ n) divides p &
                 ~(([-a, 1] %^ (Suc n)) divides p)"
apply (auto intro: poly_order_exists simp add: less_linear simp del: pmult_Cons pexp_Suc)
apply (cut_tac m = y and n = n in less_linear)
apply (drule_tac m = n in poly_exp_divides)
apply (auto dest: Suc_le_eq [THEN iffD2, THEN [2] poly_exp_divides]
            simp del: pmult_Cons pexp_Suc)
done

text{*Order*}

lemma some1_equalityD: "[| n = (@n. P n); EX! n. P n |] ==> P n"
by (blast intro: someI2)

lemma order:
      "(([-a, 1] %^ n) divides p &
        ~(([-a, 1] %^ (Suc n)) divides p)) =
        ((n = order a p) & ~(poly p = poly []))"
apply (unfold order_def)
apply (rule iffI)
apply (blast dest: poly_divides_zero intro!: some1_equality [symmetric] poly_order)
apply (blast intro!: poly_order [THEN [2] some1_equalityD])
done

lemma order2: "[| poly p \<noteq> poly [] |]
      ==> ([-a, 1] %^ (order a p)) divides p &
              ~(([-a, 1] %^ (Suc(order a p))) divides p)"
by (simp add: order del: pexp_Suc)

lemma order_unique: "[| poly p \<noteq> poly []; ([-a, 1] %^ n) divides p;
         ~(([-a, 1] %^ (Suc n)) divides p)
      |] ==> (n = order a p)"
by (insert order [of a n p], auto) 

lemma order_unique_lemma: "(poly p \<noteq> poly [] & ([-a, 1] %^ n) divides p &
         ~(([-a, 1] %^ (Suc n)) divides p))
      ==> (n = order a p)"
by (blast intro: order_unique)

lemma order_poly: "poly p = poly q ==> order a p = order a q"
by (auto simp add: fun_eq divides_def poly_mult order_def)

lemma pexp_one: "p %^ (Suc 0) = p"
apply (induct_tac "p")
apply (auto simp add: numeral_1_eq_1)
done
declare pexp_one [simp]

lemma lemma_order_root [rule_format]:
     "\<forall>p a. 0 < n & [- a, 1] %^ n divides p & ~ [- a, 1] %^ (Suc n) divides p
             --> poly p a = 0"
apply (induct_tac "n", blast)
apply (auto simp add: divides_def poly_mult simp del: pmult_Cons)
done

lemma order_root: "(poly p a = 0) = ((poly p = poly []) | order a p \<noteq> 0)"
apply (case_tac "poly p = poly []", auto)
apply (simp add: poly_linear_divides del: pmult_Cons, safe)
apply (drule_tac [!] a = a in order2)
apply (rule ccontr)
apply (simp add: divides_def poly_mult fun_eq del: pmult_Cons, blast)
apply (blast intro: lemma_order_root)
done

lemma order_divides: "(([-a, 1] %^ n) divides p) = ((poly p = poly []) | n \<le> order a p)"
apply (case_tac "poly p = poly []", auto)
apply (simp add: divides_def fun_eq poly_mult)
apply (rule_tac x = "[]" in exI)
apply (auto dest!: order2 [where a=a]
	    intro: poly_exp_divides simp del: pexp_Suc)
done

lemma order_decomp:
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
      ==> order a (p *** q) = order a p + order a q"
apply (cut_tac a = a and p = "p***q" and n = "order a p + order a q" in order)
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

(* FIXME: too too long! *)
lemma lemma_order_pderiv [rule_format]:
     "\<forall>p q a. 0 < n &
       poly (pderiv p) \<noteq> poly [] &
       poly p = poly ([- a, 1] %^ n *** q) & ~ [- a, 1] divides q
       --> n = Suc (order a (pderiv p))"
apply (induct_tac "n", safe)
apply (rule order_unique_lemma, rule conjI, assumption)
apply (subgoal_tac "\<forall>r. r divides (pderiv p) = r divides (pderiv ([-a, 1] %^ Suc n *** q))")
apply (drule_tac [2] poly_pderiv_welldef)
 prefer 2 apply (simp add: divides_def del: pmult_Cons pexp_Suc) 
apply (simp del: pmult_Cons pexp_Suc) 
apply (rule conjI)
apply (simp add: divides_def fun_eq del: pmult_Cons pexp_Suc)
apply (rule_tac x = "[-a, 1] *** (pderiv q) +++ real (Suc n) %* q" in exI)
apply (simp add: poly_pderiv_mult poly_pderiv_exp_prime poly_add poly_mult poly_cmult right_distrib mult_ac del: pmult_Cons pexp_Suc)
apply (simp add: poly_mult right_distrib left_distrib mult_ac del: pmult_Cons)
apply (erule_tac V = "\<forall>r. r divides pderiv p = r divides pderiv ([- a, 1] %^ Suc n *** q) " in thin_rl)
apply (unfold divides_def)
apply (simp (no_asm) add: poly_pderiv_mult poly_pderiv_exp_prime fun_eq poly_add poly_mult del: pmult_Cons pexp_Suc)
apply (rule swap, assumption)
apply (rotate_tac 3, erule swap)
apply (simp del: pmult_Cons pexp_Suc, safe)
apply (rule_tac x = "inverse (real (Suc n)) %* (qa +++ -- (pderiv q))" in exI)
apply (subgoal_tac "poly ([-a, 1] %^ n *** q) = poly ([-a, 1] %^ n *** ([-a, 1] *** (inverse (real (Suc n)) %* (qa +++ -- (pderiv q))))) ")
apply (drule poly_mult_left_cancel [THEN iffD1], simp)
apply (simp add: fun_eq poly_mult poly_add poly_cmult poly_minus del: pmult_Cons mult_cancel_left field_mult_cancel_left, safe)
apply (rule_tac c1 = "real (Suc n) " in real_mult_left_cancel [THEN iffD1])
apply (simp (no_asm))
apply (subgoal_tac "real (Suc n) * (poly ([- a, 1] %^ n) xa * poly q xa) =
          (poly qa xa + - poly (pderiv q) xa) *
          (poly ([- a, 1] %^ n) xa *
           ((- a + xa) * (inverse (real (Suc n)) * real (Suc n))))")
apply (simp only: mult_ac)  
apply (rotate_tac 2)
apply (drule_tac x = xa in spec)
apply (simp add: left_distrib mult_ac del: pmult_Cons)
done

lemma order_pderiv: "[| poly (pderiv p) \<noteq> poly []; order a p \<noteq> 0 |]
      ==> (order a p = Suc (order a (pderiv p)))"
apply (case_tac "poly p = poly []")
apply (auto dest: pderiv_zero)
apply (drule_tac a = a and p = p in order_decomp)
apply (blast intro: lemma_order_pderiv)
done

text{*Now justify the standard squarefree decomposition, i.e. f / gcd(f,f').    *)
(* `a la Harrison*}

lemma poly_squarefree_decomp_order: "[| poly (pderiv p) \<noteq> poly [];
         poly p = poly (q *** d);
         poly (pderiv p) = poly (e *** d);
         poly d = poly (r *** p +++ s *** pderiv p)
      |] ==> order a q = (if order a p = 0 then 0 else 1)"
apply (subgoal_tac "order a p = order a q + order a d")
apply (rule_tac [2] s = "order a (q *** d) " in trans)
prefer 2 apply (blast intro: order_poly)
apply (rule_tac [2] order_mult)
 prefer 2 apply force
apply (case_tac "order a p = 0", simp)
apply (subgoal_tac "order a (pderiv p) = order a e + order a d")
apply (rule_tac [2] s = "order a (e *** d) " in trans)
prefer 2 apply (blast intro: order_poly)
apply (rule_tac [2] order_mult)
 prefer 2 apply force
apply (case_tac "poly p = poly []")
apply (drule_tac p = p in pderiv_zero, simp)
apply (drule order_pderiv, assumption)
apply (subgoal_tac "order a (pderiv p) \<le> order a d")
apply (subgoal_tac [2] " ([-a, 1] %^ (order a (pderiv p))) divides d")
 prefer 2 apply (simp add: poly_entire order_divides)
apply (subgoal_tac [2] " ([-a, 1] %^ (order a (pderiv p))) divides p & ([-a, 1] %^ (order a (pderiv p))) divides (pderiv p) ")
 prefer 3 apply (simp add: order_divides)
 prefer 2 apply (simp add: divides_def del: pexp_Suc pmult_Cons, safe)
apply (rule_tac x = "r *** qa +++ s *** qaa" in exI)
apply (simp add: fun_eq poly_add poly_mult left_distrib right_distrib mult_ac del: pexp_Suc pmult_Cons, auto)
done


lemma poly_squarefree_decomp_order2: "[| poly (pderiv p) \<noteq> poly [];
         poly p = poly (q *** d);
         poly (pderiv p) = poly (e *** d);
         poly d = poly (r *** p +++ s *** pderiv p)
      |] ==> \<forall>a. order a q = (if order a p = 0 then 0 else 1)"
apply (blast intro: poly_squarefree_decomp_order)
done

lemma order_root2: "poly p \<noteq> poly [] ==> (poly p a = 0) = (order a p \<noteq> 0)"
by (rule order_root [THEN ssubst], auto)

lemma order_pderiv2: "[| poly (pderiv p) \<noteq> poly []; order a p \<noteq> 0 |]
      ==> (order a (pderiv p) = n) = (order a p = Suc n)"
apply (auto dest: order_pderiv)
done

lemma rsquarefree_roots:
  "rsquarefree p = (\<forall>a. ~(poly p a = 0 & poly (pderiv p) a = 0))"
apply (simp add: rsquarefree_def)
apply (case_tac "poly p = poly []", simp, simp)
apply (case_tac "poly (pderiv p) = poly []")
apply simp
apply (drule pderiv_iszero, clarify)
apply (subgoal_tac "\<forall>a. order a p = order a [h]")
apply (simp add: fun_eq)
apply (rule allI)
apply (cut_tac p = "[h]" and a = a in order_root)
apply (simp add: fun_eq)
apply (blast intro: order_poly)
apply (auto simp add: order_root order_pderiv2)
apply (drule spec, auto)
done

lemma pmult_one: "[1] *** p = p"
by auto
declare pmult_one [simp]

lemma poly_Nil_zero: "poly [] = poly [0]"
by (simp add: fun_eq)

lemma rsquarefree_decomp:
     "[| rsquarefree p; poly p a = 0 |]
      ==> \<exists>q. (poly p = poly ([-a, 1] *** q)) & poly q a \<noteq> 0"
apply (simp add: rsquarefree_def, safe)
apply (frule_tac a = a in order_decomp)
apply (drule_tac x = a in spec)
apply (drule_tac a1 = a in order_root2 [symmetric])
apply (auto simp del: pmult_Cons)
apply (rule_tac x = q in exI, safe)
apply (simp add: poly_mult fun_eq)
apply (drule_tac p1 = q in poly_linear_divides [THEN iffD1])
apply (simp add: divides_def del: pmult_Cons, safe)
apply (drule_tac x = "[]" in spec)
apply (auto simp add: fun_eq)
done

lemma poly_squarefree_decomp: "[| poly (pderiv p) \<noteq> poly [];
         poly p = poly (q *** d);
         poly (pderiv p) = poly (e *** d);
         poly d = poly (r *** p +++ s *** pderiv p)
      |] ==> rsquarefree q & (\<forall>a. (poly q a = 0) = (poly p a = 0))"
apply (frule poly_squarefree_decomp_order2, assumption+) 
apply (case_tac "poly p = poly []")
apply (blast dest: pderiv_zero)
apply (simp (no_asm) add: rsquarefree_def order_root del: pmult_Cons)
apply (simp add: poly_entire del: pmult_Cons)
done


text{*Normalization of a polynomial.*}

lemma poly_normalize: "poly (pnormalize p) = poly p"
apply (induct_tac "p")
apply (auto simp add: fun_eq)
done
declare poly_normalize [simp]


text{*The degree of a polynomial.*}

lemma lemma_degree_zero [rule_format]:
     "list_all (%c. c = 0) p -->  pnormalize p = []"
by (induct_tac "p", auto)

lemma degree_zero: "poly p = poly [] ==> degree p = 0"
apply (simp add: degree_def)
apply (case_tac "pnormalize p = []")
apply (auto dest: lemma_degree_zero simp add: poly_zero)
done

text{*Tidier versions of finiteness of roots.*}

lemma poly_roots_finite_set: "poly p \<noteq> poly [] ==> finite {x. poly p x = 0}"
apply (auto simp add: poly_roots_finite)
apply (rule_tac B = "{x::real. \<exists>n. (n::nat) < N & (x = j n) }" in finite_subset)
apply (induct_tac [2] "N", auto)
apply (subgoal_tac "{x::real. \<exists>na. na < Suc n & (x = j na) } = { (j n) } Un {x. \<exists>na. na < n & (x = j na) }") 
apply (auto simp add: less_Suc_eq)
done

text{*bound for polynomial.*}

lemma poly_mono: "abs(x) \<le> k ==> abs(poly p x) \<le> poly (map abs p) k"
apply (induct_tac "p", auto)
apply (rule_tac j = "abs a + abs (x * poly list x) " in real_le_trans)
apply (rule abs_triangle_ineq)
apply (auto intro!: mult_mono simp add: abs_mult, arith)
done

ML
{*
val padd_Nil2 = thm "padd_Nil2";
val padd_Cons_Cons = thm "padd_Cons_Cons";
val pminus_Nil = thm "pminus_Nil";
val pmult_singleton = thm "pmult_singleton";
val poly_ident_mult = thm "poly_ident_mult";
val poly_simple_add_Cons = thm "poly_simple_add_Cons";
val padd_commut = thm "padd_commut";
val padd_assoc = thm "padd_assoc";
val poly_cmult_distr = thm "poly_cmult_distr";
val pmult_by_x = thm "pmult_by_x";
val poly_add = thm "poly_add";
val poly_cmult = thm "poly_cmult";
val poly_minus = thm "poly_minus";
val poly_mult = thm "poly_mult";
val poly_exp = thm "poly_exp";
val poly_add_rzero = thm "poly_add_rzero";
val poly_mult_assoc = thm "poly_mult_assoc";
val poly_mult_Nil2 = thm "poly_mult_Nil2";
val poly_exp_add = thm "poly_exp_add";
val pderiv_Nil = thm "pderiv_Nil";
val pderiv_singleton = thm "pderiv_singleton";
val pderiv_Cons = thm "pderiv_Cons";
val DERIV_cmult2 = thm "DERIV_cmult2";
val DERIV_pow2 = thm "DERIV_pow2";
val lemma_DERIV_poly1 = thm "lemma_DERIV_poly1";
val lemma_DERIV_poly = thm "lemma_DERIV_poly";
val DERIV_add_const = thm "DERIV_add_const";
val poly_DERIV = thm "poly_DERIV";
val poly_differentiable = thm "poly_differentiable";
val poly_isCont = thm "poly_isCont";
val poly_IVT_pos = thm "poly_IVT_pos";
val poly_IVT_neg = thm "poly_IVT_neg";
val poly_MVT = thm "poly_MVT";
val lemma_poly_pderiv_aux_add = thm "lemma_poly_pderiv_aux_add";
val poly_pderiv_aux_add = thm "poly_pderiv_aux_add";
val lemma_poly_pderiv_aux_cmult = thm "lemma_poly_pderiv_aux_cmult";
val poly_pderiv_aux_cmult = thm "poly_pderiv_aux_cmult";
val poly_pderiv_aux_minus = thm "poly_pderiv_aux_minus";
val lemma_poly_pderiv_aux_mult1 = thm "lemma_poly_pderiv_aux_mult1";
val lemma_poly_pderiv_aux_mult = thm "lemma_poly_pderiv_aux_mult";
val lemma_poly_pderiv_add = thm "lemma_poly_pderiv_add";
val poly_pderiv_add = thm "poly_pderiv_add";
val poly_pderiv_cmult = thm "poly_pderiv_cmult";
val poly_pderiv_minus = thm "poly_pderiv_minus";
val lemma_poly_mult_pderiv = thm "lemma_poly_mult_pderiv";
val poly_pderiv_mult = thm "poly_pderiv_mult";
val poly_pderiv_exp = thm "poly_pderiv_exp";
val poly_pderiv_exp_prime = thm "poly_pderiv_exp_prime";
val lemma_poly_linear_rem = thm "lemma_poly_linear_rem";
val poly_linear_rem = thm "poly_linear_rem";
val poly_linear_divides = thm "poly_linear_divides";
val lemma_poly_length_mult = thm "lemma_poly_length_mult";
val lemma_poly_length_mult2 = thm "lemma_poly_length_mult2";
val poly_length_mult = thm "poly_length_mult";
val poly_cmult_length = thm "poly_cmult_length";
val poly_add_length = thm "poly_add_length";
val poly_root_mult_length = thm "poly_root_mult_length";
val poly_mult_not_eq_poly_Nil = thm "poly_mult_not_eq_poly_Nil";
val poly_mult_eq_zero_disj = thm "poly_mult_eq_zero_disj";
val poly_normalized_nil = thm "poly_normalized_nil";
val poly_roots_index_lemma = thm "poly_roots_index_lemma";
val poly_roots_index_lemma2 = thms "poly_roots_index_lemma2";
val poly_roots_index_length = thm "poly_roots_index_length";
val poly_roots_finite_lemma = thm "poly_roots_finite_lemma";
val real_finite_lemma = thm "real_finite_lemma";
val poly_roots_finite = thm "poly_roots_finite";
val poly_entire_lemma = thm "poly_entire_lemma";
val poly_entire = thm "poly_entire";
val poly_entire_neg = thm "poly_entire_neg";
val fun_eq = thm "fun_eq";
val poly_add_minus_zero_iff = thm "poly_add_minus_zero_iff";
val poly_add_minus_mult_eq = thm "poly_add_minus_mult_eq";
val poly_mult_left_cancel = thm "poly_mult_left_cancel";
val real_mult_zero_disj_iff = thm "real_mult_zero_disj_iff";
val poly_exp_eq_zero = thm "poly_exp_eq_zero";
val poly_prime_eq_zero = thm "poly_prime_eq_zero";
val poly_exp_prime_eq_zero = thm "poly_exp_prime_eq_zero";
val poly_zero_lemma = thm "poly_zero_lemma";
val poly_zero = thm "poly_zero";
val pderiv_aux_iszero = thm "pderiv_aux_iszero";
val pderiv_aux_iszero_num = thm "pderiv_aux_iszero_num";
val pderiv_iszero = thm "pderiv_iszero";
val pderiv_zero_obj = thm "pderiv_zero_obj";
val pderiv_zero = thm "pderiv_zero";
val poly_pderiv_welldef = thm "poly_pderiv_welldef";
val poly_primes = thm "poly_primes";
val poly_divides_refl = thm "poly_divides_refl";
val poly_divides_trans = thm "poly_divides_trans";
val le_iff_add = thm "le_iff_add";
val poly_divides_exp = thm "poly_divides_exp";
val poly_exp_divides = thm "poly_exp_divides";
val poly_divides_add = thm "poly_divides_add";
val poly_divides_diff = thm "poly_divides_diff";
val poly_divides_diff2 = thm "poly_divides_diff2";
val poly_divides_zero = thm "poly_divides_zero";
val poly_divides_zero2 = thm "poly_divides_zero2";
val poly_order_exists_lemma = thm "poly_order_exists_lemma";
val poly_order_exists = thm "poly_order_exists";
val poly_one_divides = thm "poly_one_divides";
val poly_order = thm "poly_order";
val some1_equalityD = thm "some1_equalityD";
val order = thm "order";
val order2 = thm "order2";
val order_unique = thm "order_unique";
val order_unique_lemma = thm "order_unique_lemma";
val order_poly = thm "order_poly";
val pexp_one = thm "pexp_one";
val lemma_order_root = thm "lemma_order_root";
val order_root = thm "order_root";
val order_divides = thm "order_divides";
val order_decomp = thm "order_decomp";
val order_mult = thm "order_mult";
val lemma_order_pderiv = thm "lemma_order_pderiv";
val order_pderiv = thm "order_pderiv";
val poly_squarefree_decomp_order = thm "poly_squarefree_decomp_order";
val poly_squarefree_decomp_order2 = thm "poly_squarefree_decomp_order2";
val order_root2 = thm "order_root2";
val order_pderiv2 = thm "order_pderiv2";
val rsquarefree_roots = thm "rsquarefree_roots";
val pmult_one = thm "pmult_one";
val poly_Nil_zero = thm "poly_Nil_zero";
val rsquarefree_decomp = thm "rsquarefree_decomp";
val poly_squarefree_decomp = thm "poly_squarefree_decomp";
val poly_normalize = thm "poly_normalize";
val lemma_degree_zero = thm "lemma_degree_zero";
val degree_zero = thm "degree_zero";
val poly_roots_finite_set = thm "poly_roots_finite_set";
val poly_mono = thm "poly_mono";
*}

end
