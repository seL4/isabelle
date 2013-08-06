(*  Title:      HOL/Decision_Procs/Polynomial_List.thy
    Author:     Amine Chaieb
*)

header {* Univariate Polynomials as Lists *}

theory Polynomial_List
imports Main
begin

text{* Application of polynomial as a real function. *}

primrec poly :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a::comm_ring"
where
  poly_Nil:  "poly [] x = 0"
| poly_Cons: "poly (h # t) x = h + x * poly t x"


subsection{*Arithmetic Operations on Polynomials*}

text{*addition*}
primrec padd :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a::comm_ring_1 list"  (infixl "+++" 65)
where
  padd_Nil:  "[] +++ l2 = l2"
| padd_Cons: "(h # t) +++ l2 = (if l2 = [] then h # t else (h + hd l2) # (t +++ tl l2))"

text{*Multiplication by a constant*}
primrec cmult :: "'a::comm_ring_1 \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixl "%*" 70)
where
  cmult_Nil:  "c %* [] = []"
| cmult_Cons: "c %* (h # t) = (c * h) # (c %* t)"

text{*Multiplication by a polynomial*}
primrec pmult :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a::comm_ring_1 list"  (infixl "***" 70)
where
  pmult_Nil:  "[] *** l2 = []"
| pmult_Cons: "(h # t) *** l2 =
    (if t = [] then h %* l2 else (h %* l2) +++ (0 # (t *** l2)))"

text{*Repeated multiplication by a polynomial*}
primrec mulexp :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a::comm_ring_1 list"
where
  mulexp_zero:  "mulexp 0 p q = q"
| mulexp_Suc:   "mulexp (Suc n) p q = p *** mulexp n p q"

text{*Exponential*}
primrec pexp :: "'a list \<Rightarrow> nat \<Rightarrow> 'a::comm_ring_1 list"  (infixl "%^" 80)
where
  pexp_0:   "p %^ 0 = [1]"
| pexp_Suc: "p %^ (Suc n) = p *** (p %^ n)"

text{*Quotient related value of dividing a polynomial by x + a*}
(* Useful for divisor properties in inductive proofs *)
primrec pquot :: "'a list \<Rightarrow> 'a::field \<Rightarrow> 'a list"
where
  pquot_Nil: "pquot [] a = []"
| pquot_Cons: "pquot (h # t) a =
    (if t = [] then [h] else (inverse a * (h - hd (pquot t a))) # pquot t a)"


text{*normalization of polynomials (remove extra 0 coeff)*}
primrec pnormalize :: "'a::comm_ring_1 list \<Rightarrow> 'a list"
where
  pnormalize_Nil:  "pnormalize [] = []"
| pnormalize_Cons: "pnormalize (h # p) =
    (if (pnormalize p = []) then (if h = 0 then [] else [h])
     else (h # pnormalize p))"

definition "pnormal p = ((pnormalize p = p) \<and> p \<noteq> [])"
definition "nonconstant p = (pnormal p \<and> (\<forall>x. p \<noteq> [x]))"
text{*Other definitions*}

definition poly_minus :: "'a list => ('a :: comm_ring_1) list"  ("-- _" [80] 80)
  where "-- p = (- 1) %* p"

definition divides :: "'a::comm_ring_1 list \<Rightarrow> 'a list \<Rightarrow> bool"  (infixl "divides" 70)
  where "p1 divides p2 = (\<exists>q. poly p2 = poly (p1 *** q))"

definition order :: "'a::comm_ring_1 \<Rightarrow> 'a list \<Rightarrow> nat" --{*order of a polynomial*}
  where "order a p = (SOME n. ([-a, 1] %^ n) divides p & ~ (([-a, 1] %^ Suc n) divides p))"

definition degree :: "'a::comm_ring_1 list \<Rightarrow> nat" --{*degree of a polynomial*}
  where "degree p = length (pnormalize p) - 1"

definition rsquarefree :: "'a::comm_ring_1 list \<Rightarrow> bool"
  where --{*squarefree polynomials --- NB with respect to real roots only.*}
  "rsquarefree p = (poly p \<noteq> poly [] \<and> (\<forall>a. order a p = 0 \<or> order a p = 1))"

lemma padd_Nil2 [simp]: "p +++ [] = p"
  by (induct p) auto

lemma padd_Cons_Cons: "(h1 # p1) +++ (h2 # p2) = (h1 + h2) # (p1 +++ p2)"
  by auto

lemma pminus_Nil [simp]: "-- [] = []"
  by (simp add: poly_minus_def)

lemma pmult_singleton: "[h1] *** p1 = h1 %* p1"
  by simp

lemma poly_ident_mult [simp]: "1 %* t = t"
  by (induct t) auto

lemma poly_simple_add_Cons [simp]: "[a] +++ ((0)#t) = (a#t)"
  by simp

text{*Handy general properties*}

lemma padd_commut: "b +++ a = a +++ b"
  apply (induct b arbitrary: a)
  apply auto
  apply (rule padd_Cons [THEN ssubst])
  apply (case_tac aa)
  apply auto
  done

lemma padd_assoc: "(a +++ b) +++ c = a +++ (b +++ c)"
  apply (induct a arbitrary: b c)
  apply simp
  apply (case_tac b)
  apply simp_all
  done

lemma poly_cmult_distr: "a %* ( p +++ q) = (a %* p +++ a %* q)"
  apply (induct p arbitrary: q)
  apply simp
  apply (case_tac q)
  apply (simp_all add: distrib_left)
  done

lemma pmult_by_x [simp]: "[0, 1] *** t = ((0)#t)"
  by (induct t) (auto simp add: padd_commut)


text{*properties of evaluation of polynomials.*}

lemma poly_add: "poly (p1 +++ p2) x = poly p1 x + poly p2 x"
  apply (induct p1 arbitrary: p2)
  apply auto
  apply (case_tac "p2")
  apply (auto simp add: distrib_left)
  done

lemma poly_cmult: "poly (c %* p) x = c * poly p x"
  apply (induct p)
  apply simp
  apply (cases "x = 0")
  apply (auto simp add: distrib_left mult_ac)
  done

lemma poly_minus: "poly (-- p) x = - (poly p x)"
  by (simp add: poly_minus_def poly_cmult)

lemma poly_mult: "poly (p1 *** p2) x = poly p1 x * poly p2 x"
  apply (induct p1 arbitrary: p2)
  apply (case_tac p1)
  apply (auto simp add: poly_cmult poly_add distrib_right distrib_left mult_ac)
  done

lemma poly_exp: "poly (p %^ n) (x::'a::comm_ring_1) = (poly p x) ^ n"
  by (induct n) (auto simp add: poly_cmult poly_mult)

text{*More Polynomial Evaluation Lemmas*}

lemma poly_add_rzero [simp]: "poly (a +++ []) x = poly a x"
  by simp

lemma poly_mult_assoc: "poly ((a *** b) *** c) x = poly (a *** (b *** c)) x"
  by (simp add: poly_mult mult_assoc)

lemma poly_mult_Nil2 [simp]: "poly (p *** []) x = 0"
  by (induct p) auto

lemma poly_exp_add: "poly (p %^ (n + d)) x = poly( p %^ n *** p %^ d) x"
  by (induct n) (auto simp add: poly_mult mult_assoc)

subsection{*Key Property: if @{term "f(a) = 0"} then @{term "(x - a)"} divides
 @{term "p(x)"} *}

lemma poly_linear_rem: "\<exists>q r. h # t = [r] +++ [-a, 1] *** q"
  apply (induct t arbitrary: h)
  apply (rule_tac x = "[]" in exI)
  apply (rule_tac x = h in exI)
  apply simp
  apply (drule_tac x = aa in meta_spec)
  apply safe
  apply (rule_tac x = "r#q" in exI)
  apply (rule_tac x = "a*r + h" in exI)
  apply (case_tac q)
  apply auto
  done

lemma poly_linear_divides: "poly p a = 0 \<longleftrightarrow> p = [] \<or> (\<exists>q. p = [-a, 1] *** q)"
  apply (auto simp add: poly_add poly_cmult distrib_left)
  apply (case_tac p)
  apply simp
  apply (cut_tac h = aa and t = list and a = a in poly_linear_rem)
  apply safe
  apply (case_tac q)
  apply auto
  apply (drule_tac x = "[]" in spec)
  apply simp
  apply (auto simp add: poly_add poly_cmult add_assoc)
  apply (drule_tac x = "aa#lista" in spec)
  apply auto
  done

lemma lemma_poly_length_mult [simp]: "length (k %* p +++  (h # (a %* p))) = Suc (length p)"
  by (induct p arbitrary: h k a) auto

lemma lemma_poly_length_mult2 [simp]: "length (k %* p +++  (h # p)) = Suc (length p)"
  by (induct p arbitrary: h k) auto

lemma poly_length_mult [simp]: "length([-a, 1] *** q) = Suc (length q)"
  by auto


subsection{*Polynomial length*}

lemma poly_cmult_length [simp]: "length (a %* p) = length p"
  by (induct p) auto

lemma poly_add_length:
  "length (p1 +++ p2) = (if (length p1 < length p2) then length p2 else length p1)"
  by (induct p1 arbitrary: p2) auto

lemma poly_root_mult_length [simp]: "length ([a, b] *** p) = Suc (length p)"
  by simp

lemma poly_mult_not_eq_poly_Nil [simp]:
  "poly (p *** q) x \<noteq> poly [] x \<longleftrightarrow> poly p x \<noteq> poly [] x \<and> poly q x \<noteq> poly [] (x::'a::idom)"
  by (auto simp add: poly_mult)

lemma poly_mult_eq_zero_disj: "poly (p *** q) (x::'a::idom) = 0 \<longleftrightarrow> poly p x = 0 \<or> poly q x = 0"
  by (auto simp add: poly_mult)

text{*Normalisation Properties*}

lemma poly_normalized_nil: "pnormalize p = [] \<longrightarrow> poly p x = 0"
  by (induct p) auto

text{*A nontrivial polynomial of degree n has no more than n roots*}

lemma poly_roots_index_lemma0 [rule_format]:
   "\<forall>p x. poly p x \<noteq> poly [] x & length p = n
    --> (\<exists>i. \<forall>x. (poly p x = (0::'a::idom)) --> (\<exists>m. (m \<le> n & x = i m)))"
  apply (induct n)
  apply safe
  apply (rule ccontr)
  apply (subgoal_tac "\<exists>a. poly p a = 0")
  apply safe
  apply (drule poly_linear_divides [THEN iffD1])
  apply safe
  apply (drule_tac x = q in spec)
  apply (drule_tac x = x in spec)
  apply (simp del: poly_Nil pmult_Cons)
  apply (erule exE)
  apply (drule_tac x = "%m. if m = Suc n then a else i m" in spec)
  apply safe
  apply (drule poly_mult_eq_zero_disj [THEN iffD1])
  apply safe
  apply (drule_tac x = "Suc (length q)" in spec)
  apply (auto simp add: field_simps)
  apply (drule_tac x = xa in spec)
  apply (clarsimp simp add: field_simps)
  apply (drule_tac x = m in spec)
  apply (auto simp add:field_simps)
  done
lemmas poly_roots_index_lemma1 = conjI [THEN poly_roots_index_lemma0]

lemma poly_roots_index_length0:
  "poly p (x::'a::idom) \<noteq> poly [] x \<Longrightarrow>
    \<exists>i. \<forall>x. (poly p x = 0) \<longrightarrow> (\<exists>n. n \<le> length p & x = i n)"
  by (blast intro: poly_roots_index_lemma1)

lemma poly_roots_finite_lemma:
  "poly p (x::'a::idom) \<noteq> poly [] x \<Longrightarrow>
    \<exists>N i. \<forall>x. (poly p x = 0) \<longrightarrow> (\<exists>n. (n::nat) < N & x = i n)"
  apply (drule poly_roots_index_length0)
  apply safe
  apply (rule_tac x = "Suc (length p)" in exI)
  apply (rule_tac x = i in exI)
  apply (simp add: less_Suc_eq_le)
  done


lemma real_finite_lemma:
  assumes "\<forall>x. P x \<longrightarrow> (\<exists>n. n < length j & x = j!n)"
  shows "finite {(x::'a::idom). P x}"
proof -
  let ?M = "{x. P x}"
  let ?N = "set j"
  have "?M \<subseteq> ?N" using assms by auto
  then show ?thesis using finite_subset by auto
qed

lemma poly_roots_index_lemma [rule_format]:
  "\<forall>p x. poly p x \<noteq> poly [] x & length p = n
    \<longrightarrow> (\<exists>i. \<forall>x. (poly p x = (0::'a::{idom})) \<longrightarrow> x \<in> set i)"
  apply (induct n)
  apply safe
  apply (rule ccontr)
  apply (subgoal_tac "\<exists>a. poly p a = 0")
  apply safe
  apply (drule poly_linear_divides [THEN iffD1])
  apply safe
  apply (drule_tac x = q in spec)
  apply (drule_tac x = x in spec)
  apply (auto simp del: poly_Nil pmult_Cons)
  apply (drule_tac x = "a#i" in spec)
  apply (auto simp only: poly_mult List.list.size)
  apply (drule_tac x = xa in spec)
  apply (clarsimp simp add: field_simps)
  done

lemmas poly_roots_index_lemma2 = conjI [THEN poly_roots_index_lemma]

lemma poly_roots_index_length:
  "poly p (x::'a::idom) \<noteq> poly [] x \<Longrightarrow>
    \<exists>i. \<forall>x. (poly p x = 0) --> x \<in> set i"
  by (blast intro: poly_roots_index_lemma2)

lemma poly_roots_finite_lemma':
  "poly p (x::'a::idom) \<noteq> poly [] x \<Longrightarrow>
    \<exists>i. \<forall>x. (poly p x = 0) --> x \<in> set i"
  apply (drule poly_roots_index_length)
  apply auto
  done

lemma UNIV_nat_infinite: "\<not> finite (UNIV :: nat set)"
  unfolding finite_conv_nat_seg_image
proof (auto simp add: set_eq_iff image_iff)
  fix n::nat and f:: "nat \<Rightarrow> nat"
  let ?N = "{i. i < n}"
  let ?fN = "f ` ?N"
  let ?y = "Max ?fN + 1"
  from nat_seg_image_imp_finite[of "?fN" "f" n]
  have thfN: "finite ?fN" by simp
  { assume "n =0" hence "\<exists>x. \<forall>xa<n. x \<noteq> f xa" by auto }
  moreover
  { assume nz: "n \<noteq> 0"
    hence thne: "?fN \<noteq> {}" by auto
    have "\<forall>x\<in> ?fN. Max ?fN \<ge> x" using nz Max_ge_iff[OF thfN thne] by auto
    hence "\<forall>x\<in> ?fN. ?y > x" by (auto simp add: less_Suc_eq_le)
    hence "?y \<notin> ?fN" by auto
    hence "\<exists>x. \<forall>xa<n. x \<noteq> f xa" by auto }
  ultimately show "\<exists>x. \<forall>xa<n. x \<noteq> f xa" by blast
qed

lemma UNIV_ring_char_0_infinte: "\<not> finite (UNIV:: ('a::ring_char_0) set)"
proof
  assume F: "finite (UNIV :: 'a set)"
  have th0: "of_nat ` UNIV \<subseteq> (UNIV :: 'a set)" by simp
  from finite_subset[OF th0 F] have th: "finite (of_nat ` UNIV :: 'a set)" .
  have th': "inj_on (of_nat::nat \<Rightarrow> 'a) UNIV"
    unfolding inj_on_def by auto
  from finite_imageD[OF th th'] UNIV_nat_infinite
  show False by blast
qed

lemma poly_roots_finite: "poly p \<noteq> poly [] \<longleftrightarrow> finite {x. poly p x = (0::'a::{idom,ring_char_0})}"
proof
  assume "poly p \<noteq> poly []"
  then show "finite {x. poly p x = (0::'a)}"
    apply -
    apply (erule contrapos_np)
    apply (rule ext)
    apply (rule ccontr)
    apply (clarify dest!: poly_roots_finite_lemma')
    using finite_subset
  proof -
    fix x i
    assume F: "\<not> finite {x. poly p x = (0\<Colon>'a)}"
      and P: "\<forall>x. poly p x = (0\<Colon>'a) \<longrightarrow> x \<in> set i"
    let ?M= "{x. poly p x = (0\<Colon>'a)}"
    from P have "?M \<subseteq> set i" by auto
    with finite_subset F show False by auto
  qed
next
  assume "finite {x. poly p x = (0\<Colon>'a)}"
  then show "poly p \<noteq> poly []"
    using UNIV_ring_char_0_infinte by auto
qed

text{*Entirety and Cancellation for polynomials*}

lemma poly_entire_lemma:
  "poly (p:: ('a::{idom,ring_char_0}) list) \<noteq> poly [] \<Longrightarrow> poly q \<noteq> poly [] \<Longrightarrow>
    poly (p *** q) \<noteq> poly []"
  by (auto simp add: poly_roots_finite poly_mult Collect_disj_eq)

lemma poly_entire:
  "poly (p *** q) = poly ([]::('a::{idom,ring_char_0}) list) \<longleftrightarrow>
    (poly p = poly [] \<or> poly q = poly [])"
  apply (auto dest: fun_cong simp add: poly_entire_lemma poly_mult)
  apply (blast intro: ccontr dest: poly_entire_lemma poly_mult [THEN subst])
  done

lemma poly_entire_neg:
  "poly (p *** q) \<noteq> poly ([]::('a::{idom,ring_char_0}) list) \<longleftrightarrow>
    poly p \<noteq> poly [] \<and> poly q \<noteq> poly []"
  by (simp add: poly_entire)

lemma fun_eq: "f = g \<longleftrightarrow> (\<forall>x. f x = g x)"
  by auto

lemma poly_add_minus_zero_iff: "poly (p +++ -- q) = poly [] \<longleftrightarrow> poly p = poly q"
  by (auto simp add: field_simps poly_add poly_minus_def fun_eq poly_cmult)

lemma poly_add_minus_mult_eq: "poly (p *** q +++ --(p *** r)) = poly (p *** (q +++ -- r))"
  by (auto simp add: poly_add poly_minus_def fun_eq poly_mult poly_cmult distrib_left)

lemma poly_mult_left_cancel:
  "(poly (p *** q) = poly (p *** r)) =
    (poly p = poly ([]::('a::{idom,ring_char_0}) list) | poly q = poly r)"
  apply (rule_tac p1 = "p *** q" in poly_add_minus_zero_iff [THEN subst])
  apply (auto simp add: poly_add_minus_mult_eq poly_entire poly_add_minus_zero_iff)
  done

lemma poly_exp_eq_zero [simp]:
  "poly (p %^ n) = poly ([]::('a::idom) list) \<longleftrightarrow> poly p = poly [] \<and> n \<noteq> 0"
  apply (simp only: fun_eq add: HOL.all_simps [symmetric])
  apply (rule arg_cong [where f = All])
  apply (rule ext)
  apply (induct_tac n)
  apply (auto simp add: poly_mult)
  done

lemma poly_prime_eq_zero [simp]: "poly [a, 1::'a::comm_ring_1] \<noteq> poly []"
  apply (simp add: fun_eq)
  apply (rule_tac x = "1 - a" in exI)
  apply simp
  done

lemma poly_exp_prime_eq_zero [simp]: "poly ([a, (1::'a::idom)] %^ n) \<noteq> poly []"
  by auto

text{*A more constructive notion of polynomials being trivial*}

lemma poly_zero_lemma':
  "poly (h # t) = poly [] \<Longrightarrow> h = (0::'a::{idom,ring_char_0}) & poly t = poly []"
  apply (simp add: fun_eq)
  apply (case_tac "h = 0")
  apply (drule_tac [2] x = 0 in spec)
  apply auto
  apply (case_tac "poly t = poly []")
  apply simp
proof -
  fix x
  assume H: "\<forall>x. x = (0\<Colon>'a) \<or> poly t x = (0\<Colon>'a)"  and pnz: "poly t \<noteq> poly []"
  let ?S = "{x. poly t x = 0}"
  from H have "\<forall>x. x \<noteq>0 \<longrightarrow> poly t x = 0" by blast
  hence th: "?S \<supseteq> UNIV - {0}" by auto
  from poly_roots_finite pnz have th': "finite ?S" by blast
  from finite_subset[OF th th'] UNIV_ring_char_0_infinte[where ?'a = 'a]
  show "poly t x = (0\<Colon>'a)" by simp
qed

lemma poly_zero: "poly p = poly [] \<longleftrightarrow> list_all (\<lambda>c. c = (0::'a::{idom,ring_char_0})) p"
  apply (induct p)
  apply simp
  apply (rule iffI)
  apply (drule poly_zero_lemma')
  apply auto
  done


text{*Basics of divisibility.*}

lemma poly_primes: "[a, (1::'a::idom)] divides (p *** q) \<longleftrightarrow> [a, 1] divides p \<or> [a, 1] divides q"
  apply (auto simp add: divides_def fun_eq poly_mult poly_add poly_cmult distrib_right [symmetric])
  apply (drule_tac x = "-a" in spec)
  apply (auto simp add: poly_linear_divides poly_add poly_cmult distrib_right [symmetric])
  apply (rule_tac x = "qa *** q" in exI)
  apply (rule_tac [2] x = "p *** qa" in exI)
  apply (auto simp add: poly_add poly_mult poly_cmult mult_ac)
  done

lemma poly_divides_refl [simp]: "p divides p"
  apply (simp add: divides_def)
  apply (rule_tac x = "[1]" in exI)
  apply (auto simp add: poly_mult fun_eq)
  done

lemma poly_divides_trans: "p divides q \<Longrightarrow> q divides r \<Longrightarrow> p divides r"
  apply (simp add: divides_def)
  apply safe
  apply (rule_tac x = "qa *** qaa" in exI)
  apply (auto simp add: poly_mult fun_eq mult_assoc)
  done

lemma poly_divides_exp: "m \<le> n \<Longrightarrow> (p %^ m) divides (p %^ n)"
  apply (auto simp add: le_iff_add)
  apply (induct_tac k)
  apply (rule_tac [2] poly_divides_trans)
  apply (auto simp add: divides_def)
  apply (rule_tac x = p in exI)
  apply (auto simp add: poly_mult fun_eq mult_ac)
  done

lemma poly_exp_divides: "(p %^ n) divides q \<Longrightarrow> m \<le> n \<Longrightarrow> (p %^ m) divides q"
  by (blast intro: poly_divides_exp poly_divides_trans)

lemma poly_divides_add: "p divides q \<Longrightarrow> p divides r \<Longrightarrow> p divides (q +++ r)"
  apply (simp add: divides_def)
  apply auto
  apply (rule_tac x = "qa +++ qaa" in exI)
  apply (auto simp add: poly_add fun_eq poly_mult distrib_left)
  done

lemma poly_divides_diff: "p divides q \<Longrightarrow> p divides (q +++ r) \<Longrightarrow> p divides r"
  apply (auto simp add: divides_def)
  apply (rule_tac x = "qaa +++ -- qa" in exI)
  apply (auto simp add: poly_add fun_eq poly_mult poly_minus algebra_simps)
  done

lemma poly_divides_diff2: "p divides r \<Longrightarrow> p divides (q +++ r) \<Longrightarrow> p divides q"
  apply (erule poly_divides_diff)
  apply (auto simp add: poly_add fun_eq poly_mult divides_def add_ac)
  done

lemma poly_divides_zero: "poly p = poly [] \<Longrightarrow> q divides p"
  apply (simp add: divides_def)
  apply (rule exI [where x = "[]"])
  apply (auto simp add: fun_eq poly_mult)
  done

lemma poly_divides_zero2 [simp]: "q divides []"
  apply (simp add: divides_def)
  apply (rule_tac x = "[]" in exI)
  apply (auto simp add: fun_eq)
  done

text{*At last, we can consider the order of a root.*}

lemma poly_order_exists_lemma [rule_format]:
  "\<forall>p. length p = d \<longrightarrow> poly p \<noteq> poly [] \<longrightarrow>
    (\<exists>n q. p = mulexp n [-a, (1::'a::{idom,ring_char_0})] q & poly q a \<noteq> 0)"
  apply (induct "d")
  apply (simp add: fun_eq)
  apply safe
  apply (case_tac "poly p a = 0")
  apply (drule_tac poly_linear_divides [THEN iffD1])
  apply safe
  apply (drule_tac x = q in spec)
  apply (drule_tac poly_entire_neg [THEN iffD1])
  apply safe
  apply force
  apply (rule_tac x = "Suc n" in exI)
  apply (rule_tac x = qa in exI)
  apply (simp del: pmult_Cons)
  apply (rule_tac x = 0 in exI)
  apply force
  done

(* FIXME: Tidy up *)
lemma poly_order_exists:
  "length p = d \<Longrightarrow> poly p \<noteq> poly [] \<Longrightarrow>
    \<exists>n. ([-a, 1] %^ n) divides p \<and> \<not> (([-a, (1::'a::{idom,ring_char_0})] %^ (Suc n)) divides p)"
  apply (drule poly_order_exists_lemma [where a=a])
  apply assumption
  apply clarify
  apply (rule_tac x = n in exI)
  apply safe
  apply (unfold divides_def)
  apply (rule_tac x = q in exI)
  apply (induct_tac n)
  apply simp
  apply (simp add: poly_add poly_cmult poly_mult distrib_left mult_ac)
  apply safe
  apply (subgoal_tac "poly (mulexp n [- a, 1] q) \<noteq> poly ([- a, 1] %^ Suc n *** qa)")
  apply simp
  apply (induct_tac n)
  apply (simp del: pmult_Cons pexp_Suc)
  apply (erule_tac Q = "poly q a = 0" in contrapos_np)
  apply (simp add: poly_add poly_cmult)
  apply (rule pexp_Suc [THEN ssubst])
  apply (rule ccontr)
  apply (simp add: poly_mult_left_cancel poly_mult_assoc del: pmult_Cons pexp_Suc)
  done

lemma poly_one_divides [simp]: "[1] divides p"
  by (auto simp: divides_def)

lemma poly_order: "poly p \<noteq> poly [] \<Longrightarrow>
    \<exists>! n. ([-a, (1::'a::{idom,ring_char_0})] %^ n) divides p \<and> \<not> (([-a, 1] %^ Suc n) divides p)"
  apply (auto intro: poly_order_exists simp add: less_linear simp del: pmult_Cons pexp_Suc)
  apply (cut_tac x = y and y = n in less_linear)
  apply (drule_tac m = n in poly_exp_divides)
  apply (auto dest: Suc_le_eq [THEN iffD2, THEN [2] poly_exp_divides]
    simp del: pmult_Cons pexp_Suc)
  done

text{*Order*}

lemma some1_equalityD: "n = (SOME n. P n) \<Longrightarrow> EX! n. P n \<Longrightarrow> P n"
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

lemma order2: "poly p \<noteq> poly [] \<Longrightarrow>
  ([-a, (1::'a::{idom,ring_char_0})] %^ (order a p)) divides p &
    ~(([-a, 1] %^ (Suc(order a p))) divides p)"
  by (simp add: order del: pexp_Suc)

lemma order_unique: "poly p \<noteq> poly [] \<Longrightarrow> ([-a, 1] %^ n) divides p \<Longrightarrow>
  \<not> (([-a, (1::'a::{idom,ring_char_0})] %^ (Suc n)) divides p) \<Longrightarrow> n = order a p"
  using order [of a n p] by auto

lemma order_unique_lemma:
  "(poly p \<noteq> poly [] \<and> ([-a, 1] %^ n) divides p \<and>
    \<not> (([-a, (1::'a::{idom,ring_char_0})] %^ (Suc n)) divides p)) \<Longrightarrow>
    n = order a p"
  by (blast intro: order_unique)

lemma order_poly: "poly p = poly q ==> order a p = order a q"
  by (auto simp add: fun_eq divides_def poly_mult order_def)

lemma pexp_one [simp]: "p %^ (Suc 0) = p"
  by (induct p) simp_all

lemma lemma_order_root:
  "0 < n & [- a, 1] %^ n divides p & ~ [- a, 1] %^ (Suc n) divides p \<Longrightarrow> poly p a = 0"
  apply (induct n arbitrary: p a)
  apply blast
  apply (auto simp add: divides_def poly_mult simp del: pmult_Cons)
  done

lemma order_root: "poly p a = (0::'a::{idom,ring_char_0}) \<longleftrightarrow> poly p = poly [] \<or> order a p \<noteq> 0"
  apply (cases "poly p = poly []")
  apply auto
  apply (simp add: poly_linear_divides del: pmult_Cons)
  apply safe
  apply (drule_tac [!] a = a in order2)
  apply (rule ccontr)
  apply (simp add: divides_def poly_mult fun_eq del: pmult_Cons)
  apply blast
  using neq0_conv apply (blast intro: lemma_order_root)
  done

lemma order_divides: "([-a, 1::'a::{idom,ring_char_0}] %^ n) divides p \<longleftrightarrow>
    poly p = poly [] \<or> n \<le> order a p"
  apply (cases "poly p = poly []")
  apply auto
  apply (simp add: divides_def fun_eq poly_mult)
  apply (rule_tac x = "[]" in exI)
  apply (auto dest!: order2 [where a = a] intro: poly_exp_divides simp del: pexp_Suc)
  done

lemma order_decomp:
  "poly p \<noteq> poly [] \<Longrightarrow>
    \<exists>q. poly p = poly (([-a, 1] %^ (order a p)) *** q) \<and>
      \<not> ([-a, 1::'a::{idom,ring_char_0}] divides q)"
  apply (unfold divides_def)
  apply (drule order2 [where a = a])
  apply (simp add: divides_def del: pexp_Suc pmult_Cons)
  apply safe
  apply (rule_tac x = q in exI)
  apply safe
  apply (drule_tac x = qa in spec)
  apply (auto simp add: poly_mult fun_eq poly_exp mult_ac simp del: pmult_Cons)
  done

text{*Important composition properties of orders.*}

lemma order_mult: "poly (p *** q) \<noteq> poly [] \<Longrightarrow>
  order a (p *** q) = order a p + order (a::'a::{idom,ring_char_0}) q"
  apply (cut_tac a = a and p = "p***q" and n = "order a p + order a q" in order)
  apply (auto simp add: poly_entire simp del: pmult_Cons)
  apply (drule_tac a = a in order2)+
  apply safe
  apply (simp add: divides_def fun_eq poly_exp_add poly_mult del: pmult_Cons)
  apply safe
  apply (rule_tac x = "qa *** qaa" in exI)
  apply (simp add: poly_mult mult_ac del: pmult_Cons)
  apply (drule_tac a = a in order_decomp)+
  apply safe
  apply (subgoal_tac "[-a, 1] divides (qa *** qaa) ")
  apply (simp add: poly_primes del: pmult_Cons)
  apply (auto simp add: divides_def simp del: pmult_Cons)
  apply (rule_tac x = qb in exI)
  apply (subgoal_tac "poly ([-a, 1] %^ (order a p) *** (qa *** qaa)) =
    poly ([-a, 1] %^ (order a p) *** ([-a, 1] *** qb))")
  apply (drule poly_mult_left_cancel [THEN iffD1])
  apply force
  apply (subgoal_tac "poly ([-a, 1] %^ (order a q) *** ([-a, 1] %^ (order a p) *** (qa *** qaa))) =
    poly ([-a, 1] %^ (order a q) *** ([-a, 1] %^ (order a p) *** ([-a, 1] *** qb))) ")
  apply (drule poly_mult_left_cancel [THEN iffD1])
  apply force
  apply (simp add: fun_eq poly_exp_add poly_mult mult_ac del: pmult_Cons)
  done

lemma order_root2: "poly p \<noteq> poly [] \<Longrightarrow> poly p a = 0 \<longleftrightarrow> order (a::'a::{idom,ring_char_0}) p \<noteq> 0"
  by (rule order_root [THEN ssubst]) auto

lemma pmult_one [simp]: "[1] *** p = p"
  by auto

lemma poly_Nil_zero: "poly [] = poly [0]"
  by (simp add: fun_eq)

lemma rsquarefree_decomp:
  "rsquarefree p \<Longrightarrow> poly p a = (0::'a::{idom,ring_char_0}) \<Longrightarrow>
    \<exists>q. poly p = poly ([-a, 1] *** q) \<and> poly q a \<noteq> 0"
  apply (simp add: rsquarefree_def)
  apply safe
  apply (frule_tac a = a in order_decomp)
  apply (drule_tac x = a in spec)
  apply (drule_tac a = a in order_root2 [symmetric])
  apply (auto simp del: pmult_Cons)
  apply (rule_tac x = q in exI)
  apply safe
  apply (simp add: poly_mult fun_eq)
  apply (drule_tac p1 = q in poly_linear_divides [THEN iffD1])
  apply (simp add: divides_def del: pmult_Cons)
  apply safe
  apply (drule_tac x = "[]" in spec)
  apply (auto simp add: fun_eq)
  done


text{*Normalization of a polynomial.*}

lemma poly_normalize [simp]: "poly (pnormalize p) = poly p"
  by (induct p) (auto simp add: fun_eq)


text{*The degree of a polynomial.*}

lemma lemma_degree_zero: "list_all (\<lambda>c. c = 0) p \<longleftrightarrow> pnormalize p = []"
  by (induct p) auto

lemma degree_zero: "poly p = poly ([] :: 'a::{idom,ring_char_0} list) \<Longrightarrow> degree p = 0"
  apply (cases "pnormalize p = []")
  apply (simp add: degree_def)
  apply (auto simp add: poly_zero lemma_degree_zero)
  done

lemma pnormalize_sing: "pnormalize [x] = [x] \<longleftrightarrow> x \<noteq> 0"
  by simp

lemma pnormalize_pair: "y \<noteq> 0 \<longleftrightarrow> (pnormalize [x, y] = [x, y])"
  by simp

lemma pnormal_cons: "pnormal p \<Longrightarrow> pnormal (c # p)"
  unfolding pnormal_def by simp

lemma pnormal_tail: "p \<noteq> [] \<Longrightarrow> pnormal (c # p) \<Longrightarrow> pnormal p"
  unfolding pnormal_def
  apply (cases "pnormalize p = []")
  apply auto
  apply (cases "c = 0")
  apply auto
  done

lemma pnormal_last_nonzero: "pnormal p \<Longrightarrow> last p \<noteq> 0"
  apply (induct p)
  apply (auto simp add: pnormal_def)
  apply (case_tac "pnormalize p = []")
  apply auto
  apply (case_tac "a = 0")
  apply auto
  done

lemma  pnormal_length: "pnormal p \<Longrightarrow> 0 < length p"
  unfolding pnormal_def length_greater_0_conv by blast

lemma pnormal_last_length: "0 < length p \<Longrightarrow> last p \<noteq> 0 \<Longrightarrow> pnormal p"
  apply (induct p)
  apply auto
  apply (case_tac "p = []")
  apply auto
  apply (simp add: pnormal_def)
  apply (rule pnormal_cons)
  apply auto
  done

lemma pnormal_id: "pnormal p \<longleftrightarrow> 0 < length p \<and> last p \<noteq> 0"
  using pnormal_last_length pnormal_length pnormal_last_nonzero by blast

text{*Tidier versions of finiteness of roots.*}

lemma poly_roots_finite_set:
  "poly p \<noteq> poly [] \<Longrightarrow> finite {x::'a::{idom,ring_char_0}. poly p x = 0}"
  unfolding poly_roots_finite .

text{*bound for polynomial.*}

lemma poly_mono: "abs x \<le> k \<Longrightarrow> abs (poly p (x::'a::{linordered_idom})) \<le> poly (map abs p) k"
  apply (induct p)
  apply auto
  apply (rule_tac y = "abs a + abs (x * poly p x)" in order_trans)
  apply (rule abs_triangle_ineq)
  apply (auto intro!: mult_mono simp add: abs_mult)
  done

lemma poly_Sing: "poly [c] x = c"
  by simp

end
