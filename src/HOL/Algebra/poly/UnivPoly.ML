(*
    Univariate Polynomials
    $Id$
    Author: Clemens Ballarin, started 9 December 1996
TODO: monom is *mono*morphism (probably induction needed)
*)

(* Closure of UP under +, *s, monom, const and * *)

Goalw [UP_def]
  "[| f : UP; g : UP |] ==> (%n. (f n + g n::'a::ring)) : UP";
by Auto_tac;
(* instantiate bound for the sum and do case split *)
by (res_inst_tac [("x", "if n<=na then na else n")] exI 1);
by Auto_tac;
(* first case, bound of g higher *)
by (dtac le_bound 1 THEN assume_tac 1);
by (Force_tac 1);
(* second case is identical,
  apart from we have to massage the inequality *)
by (dtac (not_leE RS less_imp_le) 1);
by (dtac le_bound 1 THEN assume_tac 1);
by (Force_tac 1);
qed "UP_closed_add";

Goalw [UP_def]
  "f : UP ==> (%n. (a * f n::'a::ring)) : UP";
by (Force_tac 1);
qed "UP_closed_smult";

Goalw [UP_def]
  "(%n. if m = n then <1> else <0>) : UP";
by Auto_tac;
qed "UP_closed_monom";

Goalw [UP_def] "(%n. if n = 0 then a else <0>) : UP";
by Auto_tac;
qed "UP_closed_const";

Goal
  "!! f::nat=>'a::ring. \
\    [| bound n f; bound m g; n + m < k |] ==> f i * g (k - i) = <0>";
(* Case split: either f i or g (k - i) is zero *)
by (case_tac "n<i" 1);
(* First case, f i is zero *)
by (Force_tac 1);
(* Second case, we have to derive m < k-i *)
by (subgoal_tac "m < k-i" 1);
by (arith_tac 2);
by (Force_tac 1);
qed "bound_mult_zero";

Goalw [UP_def]
  "[| f : UP; g : UP |] ==> \
\      (%n. (SUM n (%i. f i * g (n-i))::'a::ring)) : UP";
by (Step_tac 1);
(* Instantiate bound for the product, and remove bound in goal *)
by (res_inst_tac [("x", "n + na")] exI 1);
by (Step_tac 1);
(* Show that the sum is 0 *)
by (asm_simp_tac (simpset() addsimps [bound_mult_zero]) 1);
qed "UP_closed_mult";

(* %x. <0> represents a polynomial *)

Goalw [UP_def] "(%x. <0>) : UP";
by (Fast_tac 1);
qed "UP_zero";

(* Effect of +, *s, monom, * and the other operations on the coefficients *)

Goalw [coeff_def, up_add_def]
  "coeff n (p+q) = (coeff n p + coeff n q::'a::ring)";
by (asm_simp_tac (simpset() addsimps [Abs_UP_inverse, UP_closed_add, Rep_UP]) 1);
qed "coeff_add";

Goalw [coeff_def, up_smult_def]
  "!!a::'a::ring. coeff n (a *s p) = a * coeff n p";
by (asm_simp_tac (simpset() addsimps [Abs_UP_inverse, UP_closed_smult, Rep_UP]) 1);
qed "coeff_smult";

Goalw [coeff_def, monom_def]
  "coeff n (monom m) = (if m=n then <1> else <0>)";
by (asm_simp_tac (simpset() addsimps [Abs_UP_inverse, UP_closed_monom, Rep_UP]) 1);
qed "coeff_monom";

Goalw [coeff_def, const_def]
  "coeff n (const a) = (if n=0 then a else <0>)";
by (asm_simp_tac (simpset() addsimps [Abs_UP_inverse, UP_closed_const, Rep_UP]) 1);
qed "coeff_const";

Goalw [coeff_def, up_mult_def]
  "coeff n (p * q) = (SUM n (%i. coeff i p * coeff (n-i) q)::'a::ring)";
by (asm_simp_tac (simpset() addsimps [Abs_UP_inverse, UP_closed_mult, Rep_UP]) 1);
qed "coeff_mult";

Goalw [coeff_def, up_zero_def] "coeff n <0> = <0>";
by (asm_simp_tac (simpset() addsimps [Abs_UP_inverse, UP_zero, Rep_UP]) 1);
qed "coeff_zero";

Addsimps [coeff_add, coeff_smult, coeff_monom, coeff_const, 
	  coeff_mult, coeff_zero];

Goalw [up_one_def]
  "coeff n <1> = (if n=0 then <1> else <0>)";
by (Simp_tac 1);
qed "coeff_one";

Goalw [up_uminus_def] "coeff n (-p) = (-coeff n p::'a::ring)";
by (simp_tac (simpset() addsimps m_minus) 1);
qed "coeff_uminus";

Addsimps [coeff_one, coeff_uminus];

(* Polynomials form a ring *)

val prems = Goalw [coeff_def]
  "(!! n. coeff n p = coeff n q) ==> p = q";
by (res_inst_tac [("t", "p")] (Rep_UP_inverse RS subst) 1);
by (res_inst_tac [("t", "q")] (Rep_UP_inverse RS subst) 1);
by (asm_simp_tac (simpset() addsimps prems) 1);
qed "up_eqI";

Goalw [coeff_def]
  "coeff n p ~= coeff n q ==> p ~= q";
by Auto_tac;
qed "up_neqI";

Goal "!! a::('a::ring) up. (a + b) + c = a + (b + c)";
by (rtac up_eqI 1);
by (Simp_tac 1);
by (rtac a_assoc 1);
qed "up_a_assoc";

Goal "!! a::('a::ring) up. <0> + a = a";
by (rtac up_eqI 1);
by (Simp_tac 1);
qed "up_l_zero";

Goal "!! a::('a::ring) up. (-a) + a = <0>";
by (rtac up_eqI 1);
by (Simp_tac 1);
qed "up_l_neg";

Goal "!! a::('a::ring) up. a + b = b + a";
by (rtac up_eqI 1);
by (Simp_tac 1);
by (rtac a_comm 1);
qed "up_a_comm";

Goal "!! a::('a::ring) up. (a * b) * c = a * (b * c)";
by (rtac up_eqI 1);
by (Simp_tac 1);
by (rtac poly_assoc_lemma 1);
qed "up_m_assoc";

Goal "!! a::('a::ring) up. <1> * a = a";
by (rtac up_eqI 1);
by (Simp_tac 1);
by (case_tac "n" 1); 
(* 0 case *)
by (Asm_simp_tac 1);
(* Suc case *)
by (asm_simp_tac (simpset() delsimps [SUM_Suc] addsimps [SUM_Suc2]) 1);
qed "up_l_one";

Goal "!! a::('a::ring) up. (a + b) * c = a * c + b * c";
by (rtac up_eqI 1);
by (simp_tac (simpset() addsimps [l_distr, SUM_add]) 1);
qed "up_l_distr";

Goal "!! a::('a::ring) up. a * b = b * a";
by (rtac up_eqI 1);
by (cut_inst_tac [("a", "%i. coeff i a"), ("b", "%i. coeff i b")]
  poly_comm_lemma 1);
by (asm_full_simp_tac (simpset() addsimps [m_comm]) 1);
qed "up_m_comm";

Goal "<1> ~= (<0>::('a::ring) up)";
by (res_inst_tac [("n", "0")] up_neqI 1);
by (Simp_tac 1);
qed "up_one_not_zero";

(* Further algebraic rules *)

Goal "!! a::'a::ring. const a * p = a *s p";
by (rtac up_eqI 1);
by (case_tac "n" 1); 
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() delsimps [SUM_Suc] addsimps [SUM_Suc2]) 1);
qed "const_mult_is_smult";

Goal "!! a::'a::ring. const (a + b) = const a + const b";
by (rtac up_eqI 1);
by (Simp_tac 1);
qed "const_add";

Goal "!! a::'a::ring. const (a * b) = const a * const b";
by (simp_tac (simpset() addsimps [const_mult_is_smult]) 1);
by (rtac up_eqI 1);
by (Simp_tac 1);
qed "const_mult";

Goal "const (<1>::'a::ring) = <1>";
by (rtac up_eqI 1);
by (Simp_tac 1);
qed "const_one";

Goal "const (<0>::'a::ring) = <0>";
by (rtac up_eqI 1);
by (Simp_tac 1);
qed "const_zero";

Addsimps [const_add, const_mult, const_one, const_zero];

Goalw [inj_on_def, UNIV_def, const_def] "inj const";
by (Simp_tac 1);
by (strip_tac 1);
by (dres_inst_tac [("f", "Rep_UP")] arg_cong 1);
by (full_simp_tac (simpset() addsimps [Abs_UP_inverse, UP_closed_const,
				       expand_fun_eq]) 1);
by (dres_inst_tac [("x", "0")] spec 1);
by (Full_simp_tac 1);
qed "const_inj";

(*Lemma used in PolyHomo*)
Goal
  "!! f::nat=>'a::ring. [| bound n f; bound m g|] ==> \
\    SUM (n + m) (%k. SUM k (%i. f i * g (k-i))) = SUM n f * SUM m g";
by (simp_tac (simpset() addsimps [SUM_ldistr, DiagSum]) 1);
(* SUM_rdistr must be applied after SUM_ldistr ! *)
by (simp_tac (simpset() addsimps [SUM_rdistr]) 1);
by (res_inst_tac [("m", "n"), ("n", "n+m")] SUM_extend 1);
by (rtac le_add1 1);
by (Force_tac 1);
by (rtac SUM_cong 1);
by (rtac refl 1);
by (res_inst_tac [("m", "m"), ("n", "n+m-i")] SUM_shrink 1);
by (asm_simp_tac (simpset() addsimps [le_add_diff]) 1);
by Auto_tac;
qed "CauchySum";
