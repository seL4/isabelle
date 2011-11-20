(*  Title:      HOL/Decision_Procs/Polynomial_List.thy
    Author:     Amine Chaieb
*)

header {* Univariate Polynomials as Lists *}

theory Polynomial_List
imports Main
begin

text{* Application of polynomial as a real function. *}

primrec poly :: "'a list => 'a  => ('a::{comm_ring})" where
  poly_Nil:  "poly [] x = 0"
| poly_Cons: "poly (h#t) x = h + x * poly t x"


subsection{*Arithmetic Operations on Polynomials*}

text{*addition*}
primrec padd :: "['a list, 'a list] => ('a::comm_ring_1) list"  (infixl "+++" 65) where
  padd_Nil:  "[] +++ l2 = l2"
| padd_Cons: "(h#t) +++ l2 = (if l2 = [] then h#t
                            else (h + hd l2)#(t +++ tl l2))"

text{*Multiplication by a constant*}
primrec cmult :: "['a :: comm_ring_1, 'a list] => 'a list"  (infixl "%*" 70) where
  cmult_Nil:  "c %* [] = []"
| cmult_Cons: "c %* (h#t) = (c * h)#(c %* t)"

text{*Multiplication by a polynomial*}
primrec pmult :: "['a list, 'a list] => ('a::comm_ring_1) list"  (infixl "***" 70) where
  pmult_Nil:  "[] *** l2 = []"
| pmult_Cons: "(h#t) *** l2 = (if t = [] then h %* l2
                              else (h %* l2) +++ ((0) # (t *** l2)))"

text{*Repeated multiplication by a polynomial*}
primrec mulexp :: "[nat, 'a list, 'a  list] => ('a ::comm_ring_1) list" where
  mulexp_zero:  "mulexp 0 p q = q"
| mulexp_Suc:   "mulexp (Suc n) p q = p *** mulexp n p q"

text{*Exponential*}
primrec pexp :: "['a list, nat] => ('a::comm_ring_1) list"  (infixl "%^" 80) where
  pexp_0:   "p %^ 0 = [1]"
| pexp_Suc: "p %^ (Suc n) = p *** (p %^ n)"

text{*Quotient related value of dividing a polynomial by x + a*}
(* Useful for divisor properties in inductive proofs *)
primrec pquot :: "['a list, 'a::field] => 'a list" where
  pquot_Nil:  "pquot [] a= []"
| pquot_Cons: "pquot (h#t) a = (if t = [] then [h]
                   else (inverse(a) * (h - hd( pquot t a)))#(pquot t a))"


text{*normalization of polynomials (remove extra 0 coeff)*}
primrec pnormalize :: "('a::comm_ring_1) list => 'a list" where
  pnormalize_Nil:  "pnormalize [] = []"
| pnormalize_Cons: "pnormalize (h#p) = (if ( (pnormalize p) = [])
                                     then (if (h = 0) then [] else [h])
                                     else (h#(pnormalize p)))"

definition "pnormal p = ((pnormalize p = p) \<and> p \<noteq> [])"
definition "nonconstant p = (pnormal p \<and> (\<forall>x. p \<noteq> [x]))"
text{*Other definitions*}

definition
  poly_minus :: "'a list => ('a :: comm_ring_1) list"      ("-- _" [80] 80) where
  "-- p = (- 1) %* p"

definition
  divides :: "[('a::comm_ring_1) list, 'a list] => bool"  (infixl "divides" 70) where
  "p1 divides p2 = (\<exists>q. poly p2 = poly(p1 *** q))"

definition
  order :: "('a::comm_ring_1) => 'a list => nat" where
    --{*order of a polynomial*}
  "order a p = (SOME n. ([-a, 1] %^ n) divides p &
                      ~ (([-a, 1] %^ (Suc n)) divides p))"

definition
  degree :: "('a::comm_ring_1) list => nat" where
     --{*degree of a polynomial*}
  "degree p = length (pnormalize p) - 1"

definition
  rsquarefree :: "('a::comm_ring_1) list => bool" where
     --{*squarefree polynomials --- NB with respect to real roots only.*}
  "rsquarefree p = (poly p \<noteq> poly [] &
                     (\<forall>a. (order a p = 0) | (order a p = 1)))"

lemma padd_Nil2: "p +++ [] = p"
by (induct p) auto
declare padd_Nil2 [simp]

lemma padd_Cons_Cons: "(h1 # p1) +++ (h2 # p2) = (h1 + h2) # (p1 +++ p2)"
by auto

lemma pminus_Nil: "-- [] = []"
by (simp add: poly_minus_def)
declare pminus_Nil [simp]

lemma pmult_singleton: "[h1] *** p1 = h1 %* p1"
by simp

lemma poly_ident_mult: "1 %* t = t"
by (induct "t", auto)
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
apply (induct "a", simp, clarify)
apply (case_tac b, simp_all)
done

lemma poly_cmult_distr [rule_format]:
     "\<forall>q. a %* ( p +++ q) = (a %* p +++ a %* q)"
apply (induct "p", simp, clarify) 
apply (case_tac "q")
apply (simp_all add: right_distrib)
done

lemma pmult_by_x[simp]: "[0, 1] *** t = ((0)#t)"
apply (induct "t", simp)
by (auto simp add: mult_zero_left poly_ident_mult padd_commut)


text{*properties of evaluation of polynomials.*}

lemma poly_add: "poly (p1 +++ p2) x = poly p1 x + poly p2 x"
apply (subgoal_tac "\<forall>p2. poly (p1 +++ p2) x = poly (p1) x + poly (p2) x")
apply (induct_tac [2] "p1", auto)
apply (case_tac "p2")
apply (auto simp add: right_distrib)
done

lemma poly_cmult: "poly (c %* p) x = c * poly p x"
apply (induct "p") 
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
apply (induct "p1")
apply (auto simp add: poly_cmult)
apply (case_tac p1)
apply (auto simp add: poly_cmult poly_add left_distrib right_distrib mult_ac)
done

lemma poly_exp: "poly (p %^ n) (x::'a::comm_ring_1) = (poly p x) ^ n"
apply (induct "n")
apply (auto simp add: poly_cmult poly_mult power_Suc)
done

text{*More Polynomial Evaluation Lemmas*}

lemma poly_add_rzero: "poly (a +++ []) x = poly a x"
by simp
declare poly_add_rzero [simp]

lemma poly_mult_assoc: "poly ((a *** b) *** c) x = poly (a *** (b *** c)) x"
  by (simp add: poly_mult mult_assoc)

lemma poly_mult_Nil2: "poly (p *** []) x = 0"
by (induct "p", auto)
declare poly_mult_Nil2 [simp]

lemma poly_exp_add: "poly (p %^ (n + d)) x = poly( p %^ n *** p %^ d) x"
apply (induct "n")
apply (auto simp add: poly_mult mult_assoc)
done

subsection{*Key Property: if @{term "f(a) = 0"} then @{term "(x - a)"} divides
 @{term "p(x)"} *}

lemma lemma_poly_linear_rem: "\<forall>h. \<exists>q r. h#t = [r] +++ [-a, 1] *** q"
apply (induct "t", safe)
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
apply (auto simp add: poly_add poly_cmult add_assoc)
apply (drule_tac x = "aa#lista" in spec, auto)
done

lemma lemma_poly_length_mult: "\<forall>h k a. length (k %* p +++  (h # (a %* p))) = Suc (length p)"
by (induct "p", auto)
declare lemma_poly_length_mult [simp]

lemma lemma_poly_length_mult2: "\<forall>h k. length (k %* p +++  (h # p)) = Suc (length p)"
by (induct "p", auto)
declare lemma_poly_length_mult2 [simp]

lemma poly_length_mult: "length([-a,1] *** q) = Suc (length q)"
by auto
declare poly_length_mult [simp]


subsection{*Polynomial length*}

lemma poly_cmult_length: "length (a %* p) = length p"
by (induct "p", auto)
declare poly_cmult_length [simp]

lemma poly_add_length [rule_format]:
     "\<forall>p2. length (p1 +++ p2) =
             (if (length p1 < length p2) then length p2 else length p1)"
apply (induct "p1", simp_all)
apply arith
done

lemma poly_root_mult_length: "length([a,b] *** p) = Suc (length p)"
by (simp add: poly_cmult_length poly_add_length)
declare poly_root_mult_length [simp]

lemma poly_mult_not_eq_poly_Nil: "(poly (p *** q) x \<noteq> poly [] x) =
      (poly p x \<noteq> poly [] x & poly q x \<noteq> poly [] (x::'a::idom))"
apply (auto simp add: poly_mult)
done
declare poly_mult_not_eq_poly_Nil [simp]

lemma poly_mult_eq_zero_disj: "(poly (p *** q) (x::'a::idom) = 0) = (poly p x = 0 | poly q x = 0)"
by (auto simp add: poly_mult)

text{*Normalisation Properties*}

lemma poly_normalized_nil: "(pnormalize p = []) --> (poly p x = 0)"
by (induct "p", auto)

text{*A nontrivial polynomial of degree n has no more than n roots*}

lemma poly_roots_index_lemma0 [rule_format]:
   "\<forall>p x. poly p x \<noteq> poly [] x & length p = n
    --> (\<exists>i. \<forall>x. (poly p x = (0::'a::idom)) --> (\<exists>m. (m \<le> n & x = i m)))"
apply (induct "n", safe)
apply (rule ccontr)
apply (subgoal_tac "\<exists>a. poly p a = 0", safe)
apply (drule poly_linear_divides [THEN iffD1], safe)
apply (drule_tac x = q in spec)
apply (drule_tac x = x in spec)
apply (simp del: poly_Nil pmult_Cons)
apply (erule exE)
apply (drule_tac x = "%m. if m = Suc n then a else i m" in spec, safe)
apply (drule poly_mult_eq_zero_disj [THEN iffD1], safe)
apply (drule_tac x = "Suc (length q)" in spec)
apply (auto simp add: field_simps)
apply (drule_tac x = xa in spec)
apply (clarsimp simp add: field_simps)
apply (drule_tac x = m in spec)
apply (auto simp add:field_simps)
done
lemmas poly_roots_index_lemma1 = conjI [THEN poly_roots_index_lemma0]

lemma poly_roots_index_length0: "poly p (x::'a::idom) \<noteq> poly [] x ==>
      \<exists>i. \<forall>x. (poly p x = 0) --> (\<exists>n. n \<le> length p & x = i n)"
by (blast intro: poly_roots_index_lemma1)

lemma poly_roots_finite_lemma: "poly p (x::'a::idom) \<noteq> poly [] x ==>
      \<exists>N i. \<forall>x. (poly p x = 0) --> (\<exists>n. (n::nat) < N & x = i n)"
apply (drule poly_roots_index_length0, safe)
apply (rule_tac x = "Suc (length p)" in exI)
apply (rule_tac x = i in exI) 
apply (simp add: less_Suc_eq_le)
done


lemma real_finite_lemma:
  assumes P: "\<forall>x. P x --> (\<exists>n. n < length j & x = j!n)"
  shows "finite {(x::'a::idom). P x}"
proof-
  let ?M = "{x. P x}"
  let ?N = "set j"
  have "?M \<subseteq> ?N" using P by auto
  thus ?thesis using finite_subset by auto
qed

lemma poly_roots_index_lemma [rule_format]:
   "\<forall>p x. poly p x \<noteq> poly [] x & length p = n
    --> (\<exists>i. \<forall>x. (poly p x = (0::'a::{idom})) --> x \<in> set i)"
apply (induct "n", safe)
apply (rule ccontr)
apply (subgoal_tac "\<exists>a. poly p a = 0", safe)
apply (drule poly_linear_divides [THEN iffD1], safe)
apply (drule_tac x = q in spec)
apply (drule_tac x = x in spec)
apply (auto simp del: poly_Nil pmult_Cons)
apply (drule_tac x = "a#i" in spec)
apply (auto simp only: poly_mult List.list.size)
apply (drule_tac x = xa in spec)
apply (clarsimp simp add: field_simps)
done

lemmas poly_roots_index_lemma2 = conjI [THEN poly_roots_index_lemma]

lemma poly_roots_index_length: "poly p (x::'a::idom) \<noteq> poly [] x ==>
      \<exists>i. \<forall>x. (poly p x = 0) --> x \<in> set i"
by (blast intro: poly_roots_index_lemma2)

lemma poly_roots_finite_lemma': "poly p (x::'a::idom) \<noteq> poly [] x ==>
      \<exists>i. \<forall>x. (poly p x = 0) --> x \<in> set i"
by (drule poly_roots_index_length, safe)

lemma UNIV_nat_infinite: "\<not> finite (UNIV :: nat set)"
  unfolding finite_conv_nat_seg_image
proof(auto simp add: set_eq_iff image_iff)
  fix n::nat and f:: "nat \<Rightarrow> nat"
  let ?N = "{i. i < n}"
  let ?fN = "f ` ?N"
  let ?y = "Max ?fN + 1"
  from nat_seg_image_imp_finite[of "?fN" "f" n] 
  have thfN: "finite ?fN" by simp
  {assume "n =0" hence "\<exists>x. \<forall>xa<n. x \<noteq> f xa" by auto}
  moreover
  {assume nz: "n \<noteq> 0"
    hence thne: "?fN \<noteq> {}" by (auto simp add: neq0_conv)
    have "\<forall>x\<in> ?fN. Max ?fN \<ge> x" using nz Max_ge_iff[OF thfN thne] by auto
    hence "\<forall>x\<in> ?fN. ?y > x" by (auto simp add: less_Suc_eq_le)
    hence "?y \<notin> ?fN" by auto
    hence "\<exists>x. \<forall>xa<n. x \<noteq> f xa" by auto }
  ultimately show "\<exists>x. \<forall>xa<n. x \<noteq> f xa" by blast
qed

lemma UNIV_ring_char_0_infinte: "\<not> finite (UNIV:: ('a::ring_char_0) set)"
proof
  assume F: "finite (UNIV :: 'a set)"
  have th0: "of_nat ` UNIV \<subseteq> (UNIV:: 'a set)" by simp
  from finite_subset[OF th0 F] have th: "finite (of_nat ` UNIV :: 'a set)" .
  have th': "inj_on (of_nat::nat \<Rightarrow> 'a) (UNIV)"
    unfolding inj_on_def by auto
  from finite_imageD[OF th th'] UNIV_nat_infinite 
  show False by blast
qed

lemma poly_roots_finite: "(poly p \<noteq> poly []) = 
  finite {x. poly p x = (0::'a::{idom, ring_char_0})}"
proof
  assume H: "poly p \<noteq> poly []"
  show "finite {x. poly p x = (0::'a)}"
    using H
    apply -
    apply (erule contrapos_np, rule ext)
    apply (rule ccontr)
    apply (clarify dest!: poly_roots_finite_lemma')
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

lemma poly_entire_lemma: "[| poly (p:: ('a::{idom,ring_char_0}) list) \<noteq> poly [] ; poly q \<noteq> poly [] |]
      ==>  poly (p *** q) \<noteq> poly []"
by (auto simp add: poly_roots_finite poly_mult Collect_disj_eq)

lemma poly_entire: "(poly (p *** q) = poly ([]::('a::{idom,ring_char_0}) list)) = ((poly p = poly []) | (poly q = poly []))"
apply (auto intro: ext dest: fun_cong simp add: poly_entire_lemma poly_mult)
apply (blast intro: ccontr dest: poly_entire_lemma poly_mult [THEN subst])
done

lemma poly_entire_neg: "(poly (p *** q) \<noteq> poly ([]::('a::{idom,ring_char_0}) list)) = ((poly p \<noteq> poly []) & (poly q \<noteq> poly []))"
by (simp add: poly_entire)

lemma fun_eq: " (f = g) = (\<forall>x. f x = g x)"
by (auto intro!: ext)

lemma poly_add_minus_zero_iff: "(poly (p +++ -- q) = poly []) = (poly p = poly q)"
by (auto simp add: field_simps poly_add poly_minus_def fun_eq poly_cmult)

lemma poly_add_minus_mult_eq: "poly (p *** q +++ --(p *** r)) = poly (p *** (q +++ -- r))"
by (auto simp add: poly_add poly_minus_def fun_eq poly_mult poly_cmult right_distrib)

lemma poly_mult_left_cancel: "(poly (p *** q) = poly (p *** r)) = (poly p = poly ([]::('a::{idom, ring_char_0}) list) | poly q = poly r)"
apply (rule_tac p1 = "p *** q" in poly_add_minus_zero_iff [THEN subst])
apply (auto intro: ext simp add: poly_add_minus_mult_eq poly_entire poly_add_minus_zero_iff)
done

lemma poly_exp_eq_zero:
     "(poly (p %^ n) = poly ([]::('a::idom) list)) = (poly p = poly [] & n \<noteq> 0)"
apply (simp only: fun_eq add: HOL.all_simps [symmetric]) 
apply (rule arg_cong [where f = All]) 
apply (rule ext)
apply (induct_tac "n")
apply (auto simp add: poly_mult)
done
declare poly_exp_eq_zero [simp]

lemma poly_prime_eq_zero: "poly [a,(1::'a::comm_ring_1)] \<noteq> poly []"
apply (simp add: fun_eq)
apply (rule_tac x = "1 - a" in exI, simp)
done
declare poly_prime_eq_zero [simp]

lemma poly_exp_prime_eq_zero: "(poly ([a, (1::'a::idom)] %^ n) \<noteq> poly [])"
by auto
declare poly_exp_prime_eq_zero [simp]

text{*A more constructive notion of polynomials being trivial*}

lemma poly_zero_lemma': "poly (h # t) = poly [] ==> h = (0::'a::{idom,ring_char_0}) & poly t = poly []"
apply(simp add: fun_eq)
apply (case_tac "h = 0")
apply (drule_tac [2] x = 0 in spec, auto) 
apply (case_tac "poly t = poly []", simp) 
proof-
  fix x
  assume H: "\<forall>x. x = (0\<Colon>'a) \<or> poly t x = (0\<Colon>'a)"  and pnz: "poly t \<noteq> poly []"
  let ?S = "{x. poly t x = 0}"
  from H have "\<forall>x. x \<noteq>0 \<longrightarrow> poly t x = 0" by blast
  hence th: "?S \<supseteq> UNIV - {0}" by auto
  from poly_roots_finite pnz have th': "finite ?S" by blast
  from finite_subset[OF th th'] UNIV_ring_char_0_infinte[where ?'a = 'a]
  show "poly t x = (0\<Colon>'a)" by simp
  qed

lemma poly_zero: "(poly p = poly []) = list_all (%c. c = (0::'a::{idom,ring_char_0})) p"
apply (induct "p", simp)
apply (rule iffI)
apply (drule poly_zero_lemma', auto)
done



text{*Basics of divisibility.*}

lemma poly_primes: "([a, (1::'a::idom)] divides (p *** q)) = ([a, 1] divides p | [a, 1] divides q)"
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
apply (auto simp add: poly_mult fun_eq mult_assoc)
done

lemma poly_divides_exp: "m \<le> n ==> (p %^ m) divides (p %^ n)"
apply (auto simp add: le_iff_add)
apply (induct_tac k)
apply (rule_tac [2] poly_divides_trans)
apply (auto simp add: divides_def)
apply (rule_tac x = p in exI)
apply (auto simp add: poly_mult fun_eq mult_ac)
done

lemma poly_exp_divides: "[| (p %^ n) divides q;  m\<le>n |] ==> (p %^ m) divides q"
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
apply (auto simp add: poly_add fun_eq poly_mult poly_minus right_diff_distrib algebra_simps)
done

lemma poly_divides_diff2: "[| p divides r; p divides (q +++ r) |] ==> p divides q"
apply (erule poly_divides_diff)
apply (auto simp add: poly_add fun_eq poly_mult divides_def add_ac)
done

lemma poly_divides_zero: "poly p = poly [] ==> q divides p"
apply (simp add: divides_def)
apply (rule exI[where x="[]"])
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
             --> (\<exists>n q. p = mulexp n [-a, (1::'a::{idom,ring_char_0})] q & poly q a \<noteq> 0)"
apply (induct "d")
apply (simp add: fun_eq, safe)
apply (case_tac "poly p a = 0")
apply (drule_tac poly_linear_divides [THEN iffD1], safe)
apply (drule_tac x = q in spec)
apply (drule_tac poly_entire_neg [THEN iffD1], safe, force) 
apply (rule_tac x = "Suc n" in exI)
apply (rule_tac x = qa in exI)
apply (simp del: pmult_Cons)
apply (rule_tac x = 0 in exI, force) 
done

(* FIXME: Tidy up *)
lemma poly_order_exists:
     "[| length p = d; poly p \<noteq> poly [] |]
      ==> \<exists>n. ([-a, 1] %^ n) divides p &
                ~(([-a, (1::'a::{idom,ring_char_0})] %^ (Suc n)) divides p)"
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
apply (erule_tac Q = "poly q a = 0" in contrapos_np)
apply (simp add: poly_add poly_cmult)
apply (rule pexp_Suc [THEN ssubst])
apply (rule ccontr)
apply (simp add: poly_mult_left_cancel poly_mult_assoc del: pmult_Cons pexp_Suc)
done

lemma poly_one_divides: "[1] divides p"
by (simp add: divides_def, auto)
declare poly_one_divides [simp]

lemma poly_order: "poly p \<noteq> poly []
      ==> EX! n. ([-a, (1::'a::{idom,ring_char_0})] %^ n) divides p &
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

lemma order:
      "(([-a, (1::'a::{idom,ring_char_0})] %^ n) divides p &
        ~(([-a, 1] %^ (Suc n)) divides p)) =
        ((n = order a p) & ~(poly p = poly []))"
apply (unfold order_def)
apply (rule iffI)
apply (blast dest: poly_divides_zero intro!: some1_equality [symmetric] poly_order)
apply (blast intro!: poly_order [THEN [2] some1_equalityD])
done

lemma order2: "[| poly p \<noteq> poly [] |]
      ==> ([-a, (1::'a::{idom,ring_char_0})] %^ (order a p)) divides p &
              ~(([-a, 1] %^ (Suc(order a p))) divides p)"
by (simp add: order del: pexp_Suc)

lemma order_unique: "[| poly p \<noteq> poly []; ([-a, 1] %^ n) divides p;
         ~(([-a, (1::'a::{idom,ring_char_0})] %^ (Suc n)) divides p)
      |] ==> (n = order a p)"
by (insert order [of a n p], auto) 

lemma order_unique_lemma: "(poly p \<noteq> poly [] & ([-a, 1] %^ n) divides p &
         ~(([-a, (1::'a::{idom,ring_char_0})] %^ (Suc n)) divides p))
      ==> (n = order a p)"
by (blast intro: order_unique)

lemma order_poly: "poly p = poly q ==> order a p = order a q"
by (auto simp add: fun_eq divides_def poly_mult order_def)

lemma pexp_one: "p %^ (Suc 0) = p"
apply (induct "p")
apply (auto simp add: numeral_1_eq_1)
done
declare pexp_one [simp]

lemma lemma_order_root [rule_format]:
     "\<forall>p a. 0 < n & [- a, 1] %^ n divides p & ~ [- a, 1] %^ (Suc n) divides p
             --> poly p a = 0"
apply (induct "n", blast)
apply (auto simp add: divides_def poly_mult simp del: pmult_Cons)
done

lemma order_root: "(poly p a = (0::'a::{idom,ring_char_0})) = ((poly p = poly []) | order a p \<noteq> 0)"
apply (case_tac "poly p = poly []", auto)
apply (simp add: poly_linear_divides del: pmult_Cons, safe)
apply (drule_tac [!] a = a in order2)
apply (rule ccontr)
apply (simp add: divides_def poly_mult fun_eq del: pmult_Cons, blast)
using neq0_conv
apply (blast intro: lemma_order_root)
done

lemma order_divides: "(([-a, 1::'a::{idom,ring_char_0}] %^ n) divides p) = ((poly p = poly []) | n \<le> order a p)"
apply (case_tac "poly p = poly []", auto)
apply (simp add: divides_def fun_eq poly_mult)
apply (rule_tac x = "[]" in exI)
apply (auto dest!: order2 [where a=a]
            intro: poly_exp_divides simp del: pexp_Suc)
done

lemma order_decomp:
     "poly p \<noteq> poly []
      ==> \<exists>q. (poly p = poly (([-a, 1] %^ (order a p)) *** q)) &
                ~([-a, 1::'a::{idom,ring_char_0}] divides q)"
apply (unfold divides_def)
apply (drule order2 [where a = a])
apply (simp add: divides_def del: pexp_Suc pmult_Cons, safe)
apply (rule_tac x = q in exI, safe)
apply (drule_tac x = qa in spec)
apply (auto simp add: poly_mult fun_eq poly_exp mult_ac simp del: pmult_Cons)
done

text{*Important composition properties of orders.*}

lemma order_mult: "poly (p *** q) \<noteq> poly []
      ==> order a (p *** q) = order a p + order (a::'a::{idom,ring_char_0}) q"
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



lemma order_root2: "poly p \<noteq> poly [] ==> (poly p a = 0) = (order (a::'a::{idom,ring_char_0}) p \<noteq> 0)"
by (rule order_root [THEN ssubst], auto)


lemma pmult_one: "[1] *** p = p"
by auto
declare pmult_one [simp]

lemma poly_Nil_zero: "poly [] = poly [0]"
by (simp add: fun_eq)

lemma rsquarefree_decomp:
     "[| rsquarefree p; poly p a = (0::'a::{idom,ring_char_0}) |]
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

lemma poly_normalize: "poly (pnormalize p) = poly p"
apply (induct "p")
apply (auto simp add: fun_eq)
done
declare poly_normalize [simp]


text{*The degree of a polynomial.*}

lemma lemma_degree_zero:
     "list_all (%c. c = 0) p \<longleftrightarrow>  pnormalize p = []"
by (induct "p", auto)

lemma degree_zero: "(poly p = poly ([]:: (('a::{idom,ring_char_0}) list))) \<Longrightarrow> (degree p = 0)"
apply (simp add: degree_def)
apply (case_tac "pnormalize p = []")
apply (auto simp add: poly_zero lemma_degree_zero )
done

lemma pnormalize_sing: "(pnormalize [x] = [x]) \<longleftrightarrow> x \<noteq> 0" by simp
lemma pnormalize_pair: "y \<noteq> 0 \<longleftrightarrow> (pnormalize [x, y] = [x, y])" by simp
lemma pnormal_cons: "pnormal p \<Longrightarrow> pnormal (c#p)" 
  unfolding pnormal_def by simp
lemma pnormal_tail: "p\<noteq>[] \<Longrightarrow> pnormal (c#p) \<Longrightarrow> pnormal p"
  unfolding pnormal_def 
  apply (cases "pnormalize p = []", auto)
  by (cases "c = 0", auto)
lemma pnormal_last_nonzero: "pnormal p ==> last p \<noteq> 0"
  apply (induct p, auto simp add: pnormal_def)
  apply (case_tac "pnormalize p = []", auto)
  by (case_tac "a=0", auto)
lemma  pnormal_length: "pnormal p \<Longrightarrow> 0 < length p"
  unfolding pnormal_def length_greater_0_conv by blast
lemma pnormal_last_length: "\<lbrakk>0 < length p ; last p \<noteq> 0\<rbrakk> \<Longrightarrow> pnormal p"
  apply (induct p, auto)
  apply (case_tac "p = []", auto)
  apply (simp add: pnormal_def)
  by (rule pnormal_cons, auto)
lemma pnormal_id: "pnormal p \<longleftrightarrow> (0 < length p \<and> last p \<noteq> 0)"
  using pnormal_last_length pnormal_length pnormal_last_nonzero by blast

text{*Tidier versions of finiteness of roots.*}

lemma poly_roots_finite_set: "poly p \<noteq> poly [] ==> finite {x::'a::{idom,ring_char_0}. poly p x = 0}"
unfolding poly_roots_finite .

text{*bound for polynomial.*}

lemma poly_mono: "abs(x) \<le> k ==> abs(poly p (x::'a::{linordered_idom})) \<le> poly (map abs p) k"
apply (induct "p", auto)
apply (rule_tac y = "abs a + abs (x * poly p x)" in order_trans)
apply (rule abs_triangle_ineq)
apply (auto intro!: mult_mono simp add: abs_mult)
done

lemma poly_Sing: "poly [c] x = c" by simp

end
