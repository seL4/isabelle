(*  Title:      HOL/Library/Poly_Deriv.thy
    Author:     Amine Chaieb
    Author:     Brian Huffman
*)

section\<open>Polynomials and Differentiation\<close>

theory Poly_Deriv
imports Deriv Polynomial
begin

subsection \<open>Derivatives of univariate polynomials\<close>

function pderiv :: "('a :: semidom) poly \<Rightarrow> 'a poly"
where
  [simp del]: "pderiv (pCons a p) = (if p = 0 then 0 else p + pCons 0 (pderiv p))"
  by (auto intro: pCons_cases)

termination pderiv
  by (relation "measure degree") simp_all

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

end
