(*  Title:       Poly.ML
    Author:      Jacques D. Fleuriot
    Copyright:   2000 University of Edinburgh
    Description: Properties of real polynomials following 
                 John Harrison's HOL-Light implementation.
                 Some early theorems by Lucas Dixon
*)

Goal "p +++ [] = p";
by (induct_tac "p" 1);
by Auto_tac;
qed "padd_Nil2";
Addsimps [padd_Nil2];

Goal "(h1 # p1) +++ (h2 # p2) = (h1 + h2) # (p1 +++ p2)";
by Auto_tac;
qed "padd_Cons_Cons";

Goal "-- [] = []";
by (rewtac poly_minus_def);
by (Auto_tac);
qed "pminus_Nil";
Addsimps [pminus_Nil];

Goal "[h1] *** p1 = h1 %* p1";
by (Simp_tac 1);
qed "pmult_singleton";

Goal "1 %* t = t";
by (induct_tac "t" 1);
by Auto_tac;
qed "poly_ident_mult";
Addsimps [poly_ident_mult];

Goal "[a] +++ ((0)#t) = (a#t)"; 
by (Simp_tac 1);
qed "poly_simple_add_Cons";
Addsimps [poly_simple_add_Cons];

(*-------------------------------------------------------------------------*)
(*  Handy general properties                                               *)
(*-------------------------------------------------------------------------*)

Goal "b +++ a = a +++ b"; 
by (subgoal_tac "ALL a. b +++ a = a +++ b" 1);
by (induct_tac "b" 2);
by Auto_tac;
by (rtac (padd_Cons RS ssubst) 1);
by (case_tac "aa" 1);
by Auto_tac;
qed "padd_commut";

Goal "(a +++ b) +++ c = a +++ (b +++ c)"; 
by (subgoal_tac "ALL b c. (a +++ b) +++ c = a +++ (b +++ c)" 1);
by (Asm_simp_tac 1);
by (induct_tac "a" 1);
by (Step_tac 2);
by (case_tac "b" 2);
by (Asm_simp_tac 2);
by (Asm_simp_tac 2);
by (Asm_simp_tac 1);
qed "padd_assoc";

Goal "a %* ( p +++ q ) = (a %* p +++ a %* q)";
by (subgoal_tac "ALL q. a %* ( p +++ q ) = (a %* p +++ a %* q) " 1);
by (induct_tac "p" 2);
by (Simp_tac 2);
by (rtac allI 2 );
by (case_tac "q" 2);
by (Asm_simp_tac 2);
by (asm_simp_tac (simpset() addsimps [real_add_mult_distrib2] ) 2);
by (Asm_simp_tac 1);
qed "poly_cmult_distr";

Goal "[0, 1] *** t = ((0)#t)";
by (induct_tac "t" 1);
by (Simp_tac 1);
by (simp_tac (simpset() addsimps [poly_ident_mult, padd_commut]) 1);
by (case_tac "list" 1);
by (Asm_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [poly_ident_mult, padd_commut]) 1);
qed "pmult_by_x";
Addsimps [pmult_by_x];


(*-------------------------------------------------------------------------*)
(*  properties of evaluation of polynomials.                               *)
(*-------------------------------------------------------------------------*)

Goal "poly (p1 +++ p2) x = poly p1 x + poly p2 x";
by (subgoal_tac "ALL p2. poly (p1 +++ p2) x = poly( p1 ) x + poly( p2 ) x" 1);
by (induct_tac "p1" 2);
by Auto_tac;
by (case_tac "p2" 1);
by (auto_tac (claset(),simpset() addsimps [real_add_mult_distrib2]));
qed "poly_add";

Goal "poly (c %* p) x = c * poly p x";
by (induct_tac "p" 1); 
by (case_tac "x=0" 2);
by (auto_tac (claset(),simpset() addsimps [real_add_mult_distrib2] 
    @ real_mult_ac));
qed "poly_cmult";

Goalw [poly_minus_def] "poly (-- p) x = - (poly p x)";
by (auto_tac (claset(),simpset() addsimps [poly_cmult]));
qed "poly_minus";

Goal "poly (p1 *** p2) x = poly p1 x * poly p2 x";
by (subgoal_tac "ALL p2. poly (p1 *** p2) x = poly p1 x * poly p2 x" 1);
by (Asm_simp_tac 1);
by (induct_tac "p1" 1);
by (auto_tac (claset(),simpset() addsimps [poly_cmult]));
by (case_tac "list" 1);
by (auto_tac (claset(),simpset() addsimps [poly_cmult,poly_add,
    real_add_mult_distrib,real_add_mult_distrib2] @ real_mult_ac));
qed "poly_mult";

Goal "poly (p %^ n) x = (poly p x) ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [poly_cmult, poly_mult]));
qed "poly_exp";

(*-------------------------------------------------------------------------*)
(*  More Polynomial Evaluation Lemmas                                      *)
(*-------------------------------------------------------------------------*)

Goal "poly (a +++ []) x = poly a x";
by (Simp_tac 1);
qed "poly_add_rzero";
Addsimps [poly_add_rzero];

Goal "poly ((a *** b) *** c) x = poly (a *** (b *** c)) x";
by (simp_tac (simpset() addsimps [poly_mult,real_mult_assoc])  1);
qed "poly_mult_assoc";

Goal "poly (p *** []) x = 0";
by (induct_tac "p" 1);
by Auto_tac;
qed "poly_mult_Nil2";
Addsimps [poly_mult_Nil2];

Goal "poly (p %^ (n + d)) x = poly( p %^ n *** p %^ d ) x";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [poly_mult,real_mult_assoc]));
qed "poly_exp_add";

(*-------------------------------------------------------------------------*)
(*  The derivative                                                         *)
(*-------------------------------------------------------------------------*)

Goalw [pderiv_def] "pderiv [] = []";
by (Simp_tac 1);
qed "pderiv_Nil";
Addsimps [pderiv_Nil];

Goalw [pderiv_def] "pderiv [c] = []";
by (Simp_tac 1);
qed "pderiv_singleton";
Addsimps [pderiv_singleton];

Goalw [pderiv_def] "pderiv (h#t) = pderiv_aux 1 t";
by (Simp_tac 1);
qed "pderiv_Cons";

Goal "DERIV f x :> D ==> DERIV (%x. (f x) * c) x :> D * c";
by (auto_tac (claset() addIs [DERIV_cmult,real_mult_commute RS subst],
    simpset() addsimps [real_mult_commute]));
qed "DERIV_cmult2";

Goal "DERIV (%x. x ^ Suc n) x :> real (Suc n) * (x ^ n)";
by (rtac lemma_DERIV_subst 1 THEN rtac DERIV_pow 1);
by (Simp_tac 1);
qed "DERIV_pow2";
Addsimps [DERIV_pow2,DERIV_pow];

Goal "ALL n. DERIV (%x. (x ^ (Suc n) * poly p x)) x :> \
    \   x ^ n * poly (pderiv_aux (Suc n) p) x ";
by (induct_tac "p" 1);
by (auto_tac (claset() addSIs [DERIV_add,DERIV_cmult2],simpset() addsimps 
    [pderiv_def,real_add_mult_distrib2,real_mult_assoc RS sym] delsimps 
    [realpow_Suc]));
by (rtac (real_mult_commute RS subst) 1);
by (simp_tac (simpset() delsimps [realpow_Suc]) 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult_commute,realpow_Suc RS sym] 
    delsimps [realpow_Suc]) 1);
qed "lemma_DERIV_poly1";

Goal "DERIV (%x. (x ^ (Suc n) * poly p x)) x :> \
    \   x ^ n * poly (pderiv_aux (Suc n) p) x ";
by (simp_tac (simpset() addsimps [lemma_DERIV_poly1] delsimps [realpow_Suc]) 1);
qed "lemma_DERIV_poly";

Goal "DERIV f x :> D ==>  DERIV (%x. a + f x) x :> D";
by (rtac lemma_DERIV_subst 1 THEN rtac DERIV_add 1);
by Auto_tac;
qed "DERIV_add_const";

Goal "DERIV (%x. poly p x) x :> poly (pderiv p) x";
by (induct_tac "p" 1);
by (auto_tac (claset(),simpset() addsimps [pderiv_Cons]));
by (rtac DERIV_add_const 1);
by (rtac lemma_DERIV_subst 1);
by (rtac (full_simplify (simpset()) 
    (read_instantiate [("n","0")] lemma_DERIV_poly)) 1);
by (simp_tac (simpset() addsimps [CLAIM "1 = 1"]) 1);
qed "poly_DERIV";
Addsimps [poly_DERIV];


(*-------------------------------------------------------------------------*)
(* Consequences of the derivative theorem above                            *)
(*-------------------------------------------------------------------------*)

Goalw [differentiable_def] "(%x. poly p x) differentiable x";
by (blast_tac (claset() addIs [poly_DERIV]) 1);
qed "poly_differentiable";
Addsimps [poly_differentiable];

Goal "isCont (%x. poly p x) x";
by (rtac (poly_DERIV RS DERIV_isCont) 1);
qed "poly_isCont";
Addsimps [poly_isCont];

Goal "[| a < b; poly p a < 0; 0 < poly p b |] \
\     ==> EX x. a < x & x < b & (poly p x = 0)";
by (cut_inst_tac [("f","%x. poly p x"),("a","a"),("b","b"),("y","0")] 
    IVT_objl 1);
by (auto_tac (claset(),simpset() addsimps [real_le_less]));
qed "poly_IVT_pos";

Goal "[| a < b; 0 < poly p a; poly p b < 0 |] \
\     ==> EX x. a < x & x < b & (poly p x = 0)";
by (blast_tac (claset() addIs [full_simplify (simpset() 
    addsimps [poly_minus, rename_numerals real_minus_zero_less_iff2])
   (read_instantiate [("p","-- p")] poly_IVT_pos)]) 1);
qed "poly_IVT_neg";

Goal "a < b ==> \
\    EX x. a < x & x < b & (poly p b - poly p a = (b - a) * poly (pderiv p) x)";
by (dres_inst_tac [("f","poly p")] MVT 1);
by Auto_tac;
by (res_inst_tac [("x","z")] exI 1);
by (auto_tac (claset() addDs [ARITH_PROVE 
    "[| a < z; z < b |] ==> (b - (a::real)) ~= 0"],simpset()
     addsimps [real_mult_left_cancel,poly_DERIV RS DERIV_unique]));
qed "poly_MVT";


(*-------------------------------------------------------------------------*)
(*  Lemmas for Derivatives                                                 *)
(*-------------------------------------------------------------------------*)

Goal "ALL p2 n. poly (pderiv_aux n (p1 +++ p2)) x = \
    \           poly (pderiv_aux n p1 +++ pderiv_aux n p2) x";
by (induct_tac "p1" 1);
by (Step_tac 2);
by (case_tac "p2" 2);
by (auto_tac (claset(),simpset() addsimps [real_add_mult_distrib2]));
qed "lemma_poly_pderiv_aux_add";

Goal "poly (pderiv_aux n (p1 +++ p2)) x = \
    \ poly (pderiv_aux n p1 +++ pderiv_aux n p2) x";
by (simp_tac (simpset() addsimps [lemma_poly_pderiv_aux_add]) 1);
qed "poly_pderiv_aux_add";

Goal "ALL n. poly (pderiv_aux n (c %* p) ) x = poly (c %* pderiv_aux n p) x";
by (induct_tac "p" 1);
by (auto_tac (claset(),simpset() addsimps [poly_cmult] @ real_mult_ac));
qed "lemma_poly_pderiv_aux_cmult";

Goal "poly (pderiv_aux n (c %* p) ) x = poly (c %* pderiv_aux n p) x";
by (simp_tac (simpset() addsimps [lemma_poly_pderiv_aux_cmult]) 1);
qed "poly_pderiv_aux_cmult";

Goalw [poly_minus_def]
   "poly (pderiv_aux n (-- p)) x = poly (-- pderiv_aux n p) x";
by (simp_tac (simpset() addsimps [poly_pderiv_aux_cmult]) 1);
qed "poly_pderiv_aux_minus";

Goal "ALL n. poly (pderiv_aux (Suc n) p) x = poly ((pderiv_aux n p) +++ p) x";
by (induct_tac "p" 1);
by (auto_tac (claset(),simpset() addsimps [real_of_nat_Suc,
    real_add_mult_distrib]));
qed "lemma_poly_pderiv_aux_mult1";

Goal "poly (pderiv_aux (Suc n) p) x = poly ((pderiv_aux n p) +++ p) x";
by (simp_tac (simpset() addsimps [lemma_poly_pderiv_aux_mult1]) 1);
qed "lemma_poly_pderiv_aux_mult";

Goal "ALL q. poly (pderiv (p +++ q)) x = poly (pderiv p +++ pderiv q) x";
by (induct_tac "p" 1);
by (Step_tac 2);
by (case_tac "q" 2);
by (auto_tac (claset(),simpset() addsimps [poly_pderiv_aux_add,poly_add,
    pderiv_def]));
qed "lemma_poly_pderiv_add";

Goal "poly (pderiv (p +++ q)) x = poly (pderiv p +++ pderiv q) x";
by (simp_tac (simpset() addsimps [lemma_poly_pderiv_add]) 1);
qed "poly_pderiv_add";

Goal "poly (pderiv (c %* p)) x = poly (c %* (pderiv p)) x";
by (induct_tac "p" 1);
by (auto_tac (claset(),simpset() addsimps [poly_pderiv_aux_cmult,poly_cmult,
    pderiv_def]));
qed "poly_pderiv_cmult";

Goalw [poly_minus_def] "poly (pderiv (--p)) x = poly (--(pderiv p)) x";
by (simp_tac (simpset() addsimps [poly_pderiv_cmult]) 1);
qed "poly_pderiv_minus";

Goalw [pderiv_def] 
   "poly (pderiv (h#t)) x = poly ((0 # (pderiv t)) +++ t) x";
by (induct_tac "t" 1);
by (auto_tac (claset(),simpset() addsimps [poly_add,
    lemma_poly_pderiv_aux_mult]));
qed "lemma_poly_mult_pderiv";

Goal "ALL q. poly (pderiv (p *** q)) x = \
\     poly (p *** (pderiv q) +++ q *** (pderiv p)) x";
by (induct_tac "p" 1);
by (auto_tac (claset(),simpset() addsimps [poly_add,poly_cmult,
    poly_pderiv_cmult,poly_pderiv_add,poly_mult]));
by (rtac (lemma_poly_mult_pderiv RS ssubst) 1);
by (rtac (lemma_poly_mult_pderiv RS ssubst) 1);
by (rtac (poly_add RS ssubst) 1);
by (rtac (poly_add RS ssubst) 1);
by (asm_simp_tac (simpset() addsimps [poly_mult,real_add_mult_distrib2] 
    @ real_add_ac @ real_mult_ac) 1);
qed "poly_pderiv_mult";

Goal "poly (pderiv (p %^ (Suc n))) x = \
    \    poly ((real (Suc n)) %* (p %^ n) *** pderiv p ) x";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [poly_add,poly_pderiv_cmult,
    poly_cmult,poly_pderiv_mult,real_of_nat_zero,poly_mult,
    real_of_nat_Suc,real_add_mult_distrib2,real_add_mult_distrib]
    @ real_mult_ac));
qed "poly_pderiv_exp";

Goal "poly (pderiv ([-a, 1] %^ (Suc n))) x = \
\     poly (real (Suc n) %* ([-a, 1] %^ n)) x";
by (simp_tac (simpset() addsimps [poly_pderiv_exp,poly_mult] 
    delsimps [pexp_Suc]) 1);
by (simp_tac (simpset() addsimps [poly_cmult,pderiv_def]) 1);
qed "poly_pderiv_exp_prime";

(* ----------------------------------------------------------------------- *)
(* Key property that f(a) = 0 ==> (x - a) divides p(x).                    *)
(* ----------------------------------------------------------------------- *)

Goal "ALL h. EX q r. h#t = [r] +++ [-a, 1] *** q";
by (induct_tac "t" 1);
by (Step_tac 1);
by (res_inst_tac [("x","[]")] exI 1);
by (res_inst_tac [("x","h")] exI 1);
by (Simp_tac 1);
by (dres_inst_tac [("x","aa")] spec 1);
by (Step_tac 1);
by (res_inst_tac [("x","r#q")] exI 1);
by (res_inst_tac [("x","a*r + h")] exI 1);
by (case_tac "q" 1);
by (Auto_tac);
qed "lemma_poly_linear_rem";

Goal "EX q r. h#t = [r] +++ [-a, 1] *** q";
by (cut_inst_tac [("t","t"),("a","a")] lemma_poly_linear_rem 1);
by Auto_tac;
qed "poly_linear_rem";


Goal "(poly p a = 0) = ((p = []) | (EX q. p = [-a, 1] *** q))";
by (auto_tac (claset(),simpset() addsimps [poly_add,poly_cmult,
    real_add_mult_distrib2]));
by (case_tac "p" 1);
by (cut_inst_tac [("h","aa"),("t","list"),("a","a")] poly_linear_rem 2);
by (Step_tac 2);
by (case_tac "q" 1);
by Auto_tac;
by (dres_inst_tac [("x","[]")] spec 1);
by (Asm_full_simp_tac 1);
by (auto_tac (claset(),simpset() addsimps [poly_add,poly_cmult,
    real_add_assoc]));
by (dres_inst_tac [("x","aa#lista")] spec 1);
by Auto_tac;
qed "poly_linear_divides";

Goal "ALL h k a. length (k %* p +++  (h # (a %* p))) = Suc (length p)";
by (induct_tac "p" 1);
by Auto_tac;
qed "lemma_poly_length_mult";
Addsimps [lemma_poly_length_mult];

Goal "ALL h k. length (k %* p +++  (h # p)) = Suc (length p)";
by (induct_tac "p" 1);
by Auto_tac;
qed "lemma_poly_length_mult2";
Addsimps [lemma_poly_length_mult2];

Goal "length([-a ,1] *** q) = Suc (length q)";
by Auto_tac;
qed "poly_length_mult";
Addsimps [poly_length_mult];


(*-------------------------------------------------------------------------*)
(* Polynomial length                                                       *)
(*-------------------------------------------------------------------------*)

Goal "length (a %* p) = length p";
by (induct_tac "p" 1);
by Auto_tac;
qed "poly_cmult_length";
Addsimps [poly_cmult_length];

Goal "length (p1 +++ p2) = (if (length( p1 ) < length( p2 )) \
\   then (length( p2 )) else (length( p1) ))";
by (subgoal_tac "ALL p2. length (p1 +++ p2) = (if (length( p1 ) < \
\   length( p2 )) then (length( p2 )) else (length( p1) ))" 1);
by (induct_tac "p1" 2);
by (Simp_tac 2);
by (Simp_tac 2);
by (Step_tac 2);  
by (Asm_full_simp_tac 2);
by (arith_tac 2);
by (Asm_full_simp_tac 2);
by (arith_tac 2);
by (induct_tac "p2" 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
qed "poly_add_length";

Goal "length([a,b] *** p) = Suc (length p)";
by (asm_full_simp_tac (simpset() addsimps [poly_cmult_length, 
    poly_add_length]) 1);
qed "poly_root_mult_length";
Addsimps [poly_root_mult_length];

Goal "(poly (p *** q) x ~= poly [] x) = \
\     (poly p x ~= poly [] x & poly q x ~= poly [] x)";
by (auto_tac (claset(),simpset() addsimps [poly_mult,rename_numerals
    real_mult_not_zero]));
qed "poly_mult_not_eq_poly_Nil";
Addsimps [poly_mult_not_eq_poly_Nil];

Goal "(poly (p *** q) x = 0) = (poly p x = 0 | poly q x = 0)";
by (auto_tac (claset() addDs [CLAIM "x * y = 0 ==> x = 0 | y = (0::real)"],
    simpset() addsimps [poly_mult]));
qed "poly_mult_eq_zero_disj";

(*-------------------------------------------------------------------------*)
(*  Normalisation Properties                                               *)
(*-------------------------------------------------------------------------*)

Goal "(pnormalize p = []) --> (poly p x = 0)";
by (induct_tac "p" 1);
by Auto_tac;
qed "poly_normalized_nil";

(*-------------------------------------------------------------------------*)
(*  A nontrivial polynomial of degree n has no more than n roots           *)
(*-------------------------------------------------------------------------*)

Goal 
   "ALL p x. (poly p x ~= poly [] x & length p = n  \
\   --> (EX i. ALL x. (poly p x = (0::real)) --> (EX m. (m <= n & x = i m))))";
by (induct_tac "n" 1);
by (Step_tac 1);
by (rtac ccontr 1);
by (subgoal_tac "EX a. poly p a = 0" 1 THEN Step_tac 1);
by (dtac (poly_linear_divides RS iffD1) 1);
by (Step_tac 1);
by (dres_inst_tac [("x","q")] spec 1);
by (dres_inst_tac [("x","x")] spec 1);
by (asm_full_simp_tac (simpset() delsimps [poly_Nil,pmult_Cons]) 1);
by (etac exE 1);
by (dres_inst_tac [("x","%m. if m = Suc n then a else i m")] spec 1);
by (Step_tac 1);
by (dtac (poly_mult_eq_zero_disj RS iffD1) 1);
by (Step_tac 1);
by (dres_inst_tac [("x","Suc(length q)")] spec 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("x","xa")] spec 1 THEN Step_tac 1);
by (dres_inst_tac [("x","m")] spec 1);
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed_spec_mp "poly_roots_index_lemma";
bind_thm ("poly_roots_index_lemma2",conjI RS poly_roots_index_lemma);

Goal "poly p x ~= poly [] x ==> \
\     EX i. ALL x. (poly p x = 0) --> (EX n. n <= length p & x = i n)";
by (blast_tac (claset() addIs [poly_roots_index_lemma2]) 1);
qed "poly_roots_index_length";

Goal "poly p x ~= poly [] x ==> \
\     EX N i. ALL x. (poly p x = 0) --> (EX n. (n::nat) < N & x = i n)";
by (dtac poly_roots_index_length 1 THEN Step_tac 1);
by (res_inst_tac [("x","Suc (length p)")] exI 1);
by (res_inst_tac [("x","i")] exI 1);
by (auto_tac (claset(),simpset() addsimps 
    [ARITH_PROVE "(m < Suc n) = (m <= n)"]));
qed "poly_roots_finite_lemma";

(* annoying proof *)
Goal "ALL P. (ALL x. P x --> (EX n. (n::nat) < N & x = (j::nat=>real) n)) \
\     --> (EX a. ALL x. P x --> x < a)";
by (induct_tac "N" 1);
by (Asm_full_simp_tac 1);
by (Step_tac 1);
by (dres_inst_tac [("x","%z. P z & (z ~= (j::nat=>real) n)")] spec 1);
by Auto_tac;
by (dres_inst_tac [("x","x")] spec 1);
by (Step_tac 1);
by (res_inst_tac [("x","na")] exI 1);
by (auto_tac (claset() addDs [ARITH_PROVE "na < Suc n ==> na = n | na < n"],
    simpset()));
by (res_inst_tac [("x","abs a + abs(j n) + 1")] exI 1);
by (Step_tac 1);
by (dres_inst_tac [("x","x")] spec 1);
by (Step_tac 1);
by (dres_inst_tac [("x","j na")] spec 1);
by (Step_tac 1);
by (ALLGOALS(arith_tac));
qed_spec_mp "real_finite_lemma";

Goal "(poly p ~= poly []) = \
\     (EX N j. ALL x. poly p x = 0 --> (EX n. (n::nat) < N & x = j n))";
by (Step_tac 1);
by (etac swap 1 THEN rtac ext 1);
by (rtac ccontr 1);
by (clarify_tac (claset() addSDs [poly_roots_finite_lemma]) 1);
by (clarify_tac (claset() addSDs [real_finite_lemma]) 1);
by (dres_inst_tac [("x","a")] fun_cong 1);
by Auto_tac;
qed "poly_roots_finite";

(*-------------------------------------------------------------------------*)
(*  Entirety and Cancellation for polynomials                              *)
(*-------------------------------------------------------------------------*)

Goal "[| poly p ~= poly [] ; poly q ~= poly [] |] \
\     ==>  poly (p *** q) ~= poly []";
by (auto_tac (claset(),simpset() addsimps [poly_roots_finite]));
by (res_inst_tac [("x","N + Na")] exI 1);
by (res_inst_tac [("x","%n. if n < N then j n else ja (n - N)")] exI 1);
by (auto_tac (claset(),simpset() addsimps [poly_mult_eq_zero_disj]));
by (flexflex_tac THEN rotate_tac 1 1);
by (dtac spec 1 THEN Auto_tac);
qed "poly_entire_lemma";

Goal "(poly (p *** q) = poly []) = ((poly p = poly []) | (poly q = poly []))";
by (auto_tac (claset() addIs [ext] addDs [fun_cong],simpset() 
    addsimps [poly_entire_lemma,poly_mult]));
by (blast_tac (claset() addIs [ccontr] addDs [poly_entire_lemma,
    poly_mult RS subst]) 1);
qed "poly_entire";

Goal "(poly (p *** q) ~= poly []) = ((poly p ~= poly []) & (poly q ~= poly []))";
by (asm_full_simp_tac (simpset() addsimps [poly_entire]) 1);
qed "poly_entire_neg";

Goal " (f = g) = (ALL x. f x = g x)";
by (auto_tac (claset() addSIs [ext],simpset()));
qed "fun_eq";

Goal "(poly (p +++ -- q) = poly []) = (poly p = poly q)";
by (auto_tac (claset(),simpset() addsimps [poly_add,poly_minus_def,
    fun_eq,poly_cmult,ARITH_PROVE "(p + -q = 0) = (p = (q::real))"]));
qed "poly_add_minus_zero_iff";

Goal "poly (p *** q +++ --(p *** r)) = poly (p *** (q +++ -- r))";
by (auto_tac (claset(),simpset() addsimps [poly_add,poly_minus_def,
    fun_eq,poly_mult,poly_cmult,real_add_mult_distrib2]));
qed "poly_add_minus_mult_eq";

Goal "(poly (p *** q) = poly (p *** r)) = (poly p = poly [] | poly q = poly r)";
by (res_inst_tac [("p1","p *** q")] (poly_add_minus_zero_iff RS subst) 1);
by (auto_tac (claset() addIs [ext], simpset() addsimps [poly_add_minus_mult_eq,
    poly_entire,poly_add_minus_zero_iff]));
qed "poly_mult_left_cancel";

Goal "(x * y = 0) = (x = (0::real) | y = 0)";
by (auto_tac (claset() addDs [CLAIM "x * y = 0 ==> x = 0 | y = (0::real)"],
    simpset()));
qed "real_mult_zero_disj_iff";

Goal "(poly (p %^ n) = poly []) = (poly p = poly [] & n ~= 0)";
by (simp_tac (simpset() addsimps [fun_eq]) 1);
by (rtac (CLAIM "((ALL x. P x) & Q) = (ALL x. P x & Q)" RS ssubst) 1);
by (rtac (CLAIM "f = g ==> (ALL x. f x) = (ALL x. g x)") 1);
by (rtac ext 1);
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [poly_mult,
    real_mult_zero_disj_iff]));
qed "poly_exp_eq_zero";
Addsimps [poly_exp_eq_zero];

Goal "poly [a,1] ~= poly []";
by (simp_tac (simpset() addsimps [fun_eq]) 1);
by (res_inst_tac [("x","1 - a")] exI 1);
by (Simp_tac 1);
qed "poly_prime_eq_zero";
Addsimps [poly_prime_eq_zero];

Goal "(poly ([a, 1] %^ n) ~= poly [])";
by Auto_tac;
qed "poly_exp_prime_eq_zero";
Addsimps [poly_exp_prime_eq_zero];

(*-------------------------------------------------------------------------*)
(*  A more constructive notion of polynomials being trivial                *)
(*-------------------------------------------------------------------------*)

Goal "poly (h # t) = poly [] ==> h = 0 & poly t = poly []";
by (asm_full_simp_tac (simpset() addsimps [fun_eq]) 1);
by (case_tac "h = 0" 1);
by (dres_inst_tac [("x","0")] spec 2);
by (rtac conjI 1);
by (rtac ((simplify (simpset()) (read_instantiate [("g","poly []")] fun_eq))
    RS iffD1) 2 THEN rtac ccontr 2);
by (auto_tac (claset(),simpset() addsimps [poly_roots_finite,
    real_mult_zero_disj_iff]));
by (dtac real_finite_lemma 1 THEN Step_tac 1);
by (REPEAT(dres_inst_tac [("x","abs a + 1")] spec 1));
by (arith_tac 1);
qed "poly_zero_lemma";

Goal "(poly p = poly []) = list_all (%c. c = 0) p";
by (induct_tac "p" 1);
by (Asm_full_simp_tac 1);
by (rtac iffI 1);
by (dtac poly_zero_lemma 1);
by Auto_tac;
qed "poly_zero";

Addsimps [real_mult_zero_disj_iff];
Goal "ALL n. (list_all (%c. c = 0) (pderiv_aux (Suc n) p) = \
\     list_all (%c. c = 0) p)";
by (induct_tac "p" 1);
by Auto_tac;
qed_spec_mp "pderiv_aux_iszero";
Addsimps [pderiv_aux_iszero];

Goal "(number_of n :: nat) ~= 0 \
\     ==> (list_all (%c. c = 0) (pderiv_aux (number_of n) p) = \
\     list_all (%c. c = 0) p)";
by (res_inst_tac [("n1","number_of n"),("m1","0")] (less_imp_Suc_add RS exE) 1);
by (Force_tac 1);
by (res_inst_tac [("n1","0 + x")] (pderiv_aux_iszero RS subst) 1);
by (asm_simp_tac (simpset() delsimps [pderiv_aux_iszero]) 1);
qed "pderiv_aux_iszero_num";

Goal "poly (pderiv p) = poly [] --> (EX h. poly p = poly [h])";
by (asm_full_simp_tac (simpset() addsimps [poly_zero]) 1);
by (induct_tac "p" 1);
by (Force_tac 1);
by (asm_full_simp_tac (simpset() addsimps [pderiv_Cons,
    pderiv_aux_iszero_num] delsimps [poly_Cons]) 1);
by (auto_tac (claset(),simpset() addsimps [poly_zero RS sym]));
qed_spec_mp "pderiv_iszero";

Goal "poly p = poly [] --> (poly (pderiv p) = poly [])";
by (asm_full_simp_tac (simpset() addsimps [poly_zero]) 1);
by (induct_tac "p" 1);
by (Force_tac 1);
by (asm_full_simp_tac (simpset() addsimps [pderiv_Cons,
    pderiv_aux_iszero_num] delsimps [poly_Cons]) 1);
qed "pderiv_zero_obj";

Goal "poly p = poly [] ==> (poly (pderiv p) = poly [])";
by (blast_tac (claset() addEs [pderiv_zero_obj RS impE]) 1);
qed "pderiv_zero";
Addsimps [pderiv_zero];

Goal "poly p = poly q ==> (poly (pderiv p) = poly (pderiv q))";
by (cut_inst_tac [("p","p +++ --q")] pderiv_zero_obj 1);
by (auto_tac (claset() addIs [ ARITH_PROVE "x + - y = 0 ==> x = (y::real)"],
    simpset() addsimps [fun_eq,poly_add,poly_minus,poly_pderiv_add,
    poly_pderiv_minus] delsimps [pderiv_zero]));
qed "poly_pderiv_welldef";

(* ------------------------------------------------------------------------- *)
(* Basics of divisibility.                                                   *)
(* ------------------------------------------------------------------------- *)

Goal "([a, 1] divides (p *** q)) = ([a, 1] divides p | [a, 1] divides q)";
by (auto_tac (claset(),simpset() addsimps [divides_def,fun_eq,poly_mult,
    poly_add,poly_cmult,real_add_mult_distrib RS sym]));
by (dres_inst_tac [("x","-a")] spec 1);
by (auto_tac (claset(),simpset() addsimps [poly_linear_divides,poly_add,
    poly_cmult,real_add_mult_distrib RS sym]));
by (res_inst_tac [("x","qa *** q")] exI 1);
by (res_inst_tac [("x","p *** qa")] exI 2);
by (auto_tac (claset(),simpset() addsimps [poly_add,poly_mult,
    poly_cmult] @ real_mult_ac));
qed "poly_primes";

Goalw [divides_def] "p divides p";
by (res_inst_tac [("x","[1]")] exI 1);
by (auto_tac (claset(),simpset() addsimps [poly_mult,fun_eq]));
qed "poly_divides_refl";
Addsimps [poly_divides_refl];

Goalw [divides_def] "[| p divides q; q divides r |] ==> p divides r";
by (Step_tac 1);
by (res_inst_tac [("x","qa *** qaa")] exI 1);
by (auto_tac (claset(),simpset() addsimps [poly_mult,fun_eq,
    real_mult_assoc]));
qed "poly_divides_trans";

Goal "(m::nat) <= n = (EX d. n = m + d)";
by (auto_tac (claset(),simpset() addsimps [le_eq_less_or_eq,
    less_iff_Suc_add]));
qed "le_iff_add";

Goal "m <= n ==> (p %^ m) divides (p %^ n)";
by (auto_tac (claset(),simpset() addsimps [le_iff_add]));
by (induct_tac "d" 1);
by (rtac poly_divides_trans 2);
by (auto_tac (claset(),simpset() addsimps [divides_def]));
by (res_inst_tac [("x","p")] exI 1);
by (auto_tac (claset(),simpset() addsimps [poly_mult,fun_eq]
    @ real_mult_ac));
qed "poly_divides_exp";

Goal "[| (p %^ n) divides q;  m <= n |] ==> (p %^ m) divides q";
by (blast_tac (claset() addIs [poly_divides_exp,poly_divides_trans]) 1);
qed "poly_exp_divides";

Goalw [divides_def] 
   "[| p divides q; p divides r |] ==> p divides (q +++ r)";
by Auto_tac;
by (res_inst_tac [("x","qa +++ qaa")] exI 1);
by (auto_tac (claset(),simpset() addsimps [poly_add,fun_eq,poly_mult,
    real_add_mult_distrib2]));
qed "poly_divides_add";

Goalw [divides_def] 
   "[| p divides q; p divides (q +++ r) |] ==> p divides r";
by Auto_tac;
by (res_inst_tac [("x","qaa +++ -- qa")] exI 1);
by (auto_tac (claset(),simpset() addsimps [poly_add,fun_eq,poly_mult,
    poly_minus,real_add_mult_distrib2,
    ARITH_PROVE "(x = y + -z) = (z + x = (y::real))"]));
qed "poly_divides_diff";

Goal "[| p divides r; p divides (q +++ r) |] ==> p divides q";
by (etac poly_divides_diff 1);
by (auto_tac (claset(),simpset() addsimps [poly_add,fun_eq,poly_mult,
    divides_def] @ real_add_ac));
qed "poly_divides_diff2";

Goalw [divides_def] "poly p = poly [] ==> q divides p";
by (auto_tac (claset(),simpset() addsimps [fun_eq,poly_mult]));
qed "poly_divides_zero";

Goalw [divides_def] "q divides []";
by (res_inst_tac [("x","[]")] exI 1); 
by (auto_tac (claset(),simpset() addsimps [fun_eq]));
qed "poly_divides_zero2";
Addsimps [poly_divides_zero2];

(* ------------------------------------------------------------------------- *)
(* At last, we can consider the order of a root.                             *)
(* ------------------------------------------------------------------------- *)

(* FIXME: Tidy up *)
Goal "[| length p = d; poly p ~= poly [] |] \
\     ==> EX n. ([-a, 1] %^ n) divides p & \
\               ~(([-a, 1] %^ (Suc n)) divides p)";
by (subgoal_tac "ALL p. length p = d & poly p ~= poly [] \
\     --> (EX n q. p = mulexp n [-a, 1] q & poly q a ~= 0)" 1);
by (induct_tac "d" 2);
by (asm_full_simp_tac (simpset() addsimps [fun_eq]) 2);
by (Step_tac 2);
by (case_tac "poly pa a = 0" 2);
by (dtac (poly_linear_divides RS iffD1) 2);
by (Step_tac 2);
by (dres_inst_tac [("x","q")] spec 2);
by (dtac (poly_entire_neg RS iffD1) 2);
by (Step_tac 2);
by (Force_tac 2 THEN Blast_tac 2);
by (res_inst_tac [("x","Suc na")] exI 2);
by (res_inst_tac [("x","qa")] exI 2);
by (asm_full_simp_tac (simpset() delsimps [pmult_Cons]) 2);
by (res_inst_tac [("x","0")] exI 2);
by (Force_tac 2);
by (dres_inst_tac [("x","p")] spec 1 THEN Step_tac 1);
by (res_inst_tac [("x","n")] exI 1 THEN Step_tac 1);
by (rewtac divides_def);
by (res_inst_tac [("x","q")] exI 1);
by (induct_tac "n" 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [poly_add,poly_cmult,poly_mult,
    real_add_mult_distrib2] @ real_mult_ac) 1);
by (Step_tac 1);
by (rotate_tac 2 1);
by (rtac swap 1 THEN assume_tac 2);
by (induct_tac "n" 1);
by (asm_full_simp_tac (simpset() delsimps [pmult_Cons,pexp_Suc]) 1);
by (eres_inst_tac [("Pa","poly q a = 0")] swap 1);
by (asm_full_simp_tac (simpset() addsimps [poly_add,poly_cmult]) 1);
by (rtac (pexp_Suc RS ssubst) 1);
by (rtac ccontr 1);
by (asm_full_simp_tac (simpset() addsimps [poly_mult_left_cancel,
    poly_mult_assoc] delsimps [pmult_Cons,pexp_Suc]) 1);
qed "poly_order_exists";

Goalw [divides_def] "[1] divides p";
by Auto_tac;
qed "poly_one_divides";
Addsimps [poly_one_divides];

Goal "poly p ~= poly [] \
\     ==> EX! n. ([-a, 1] %^ n) divides p & \
\                ~(([-a, 1] %^ (Suc n)) divides p)";
by (auto_tac (claset() addIs [poly_order_exists],
    simpset() addsimps [less_linear] delsimps [pmult_Cons,pexp_Suc]));
by (cut_inst_tac [("m","y"),("n","n")] less_linear 1);
by (dres_inst_tac [("m","n")] poly_exp_divides 1);
by (auto_tac (claset() addDs [ARITH_PROVE "n < m ==> Suc n <= m" RSN  
    (2,poly_exp_divides)],simpset() delsimps [pmult_Cons,pexp_Suc]));
qed "poly_order";

(* ------------------------------------------------------------------------- *)
(* Order                                                                     *)
(* ------------------------------------------------------------------------- *)

Goal "[| n = (@n. P n); EX! n. P n |] ==> P n";
by (blast_tac (claset() addIs [someI2]) 1);
qed "some1_equalityD";

Goalw [order_def]
      "(([-a, 1] %^ n) divides p & \
\       ~(([-a, 1] %^ (Suc n)) divides p)) = \
\       ((n = order a p) & ~(poly p = poly []))";
by (rtac iffI 1);
by (blast_tac (claset() addDs [poly_divides_zero] 
    addSIs [some1_equality RS sym, poly_order]) 1);
by (blast_tac (claset() addSIs [poly_order RSN (2,some1_equalityD)]) 1);
qed "order";

Goal "[| poly p ~= poly [] |] \
\     ==> ([-a, 1] %^ (order a p)) divides p & \
\             ~(([-a, 1] %^ (Suc(order a p))) divides p)";
by (asm_full_simp_tac (simpset() addsimps [order] delsimps [pexp_Suc]) 1);
qed "order2";

Goal "[| poly p ~= poly []; ([-a, 1] %^ n) divides p; \
\        ~(([-a, 1] %^ (Suc n)) divides p) \
\     |] ==> (n = order a p)";
by (cut_inst_tac [("p","p"),("a","a"),("n","n")] order 1);
by Auto_tac;
qed "order_unique";

Goal "(poly p ~= poly [] & ([-a, 1] %^ n) divides p & \
\        ~(([-a, 1] %^ (Suc n)) divides p)) \
\     ==> (n = order a p)";
by (blast_tac (claset() addIs [order_unique]) 1);
qed "order_unique_lemma";

Goal "poly p = poly q ==> order a p = order a q";
by (auto_tac (claset(),simpset() addsimps [fun_eq,divides_def,poly_mult,
    order_def]));
qed "order_poly";

Goal "p %^ (Suc 0) = p";
by (induct_tac "p" 1);
by (auto_tac (claset(),simpset() addsimps [numeral_1_eq_1]));
qed "pexp_one";
Addsimps [pexp_one];

Goal "ALL p a. 0 < n & [- a, 1] %^ n divides p & \
\            ~ [- a, 1] %^ (Suc n) divides p \
\            --> poly p a = 0";
by (induct_tac "n" 1);
by (Blast_tac 1);
by (auto_tac (claset(),simpset() addsimps [divides_def,poly_mult] 
    delsimps [pmult_Cons]));
qed_spec_mp "lemma_order_root";

Goal "(poly p a = 0) = ((poly p = poly []) | order a p ~= 0)";
by (case_tac "poly p = poly []" 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [poly_linear_divides]
    delsimps [pmult_Cons]) 1);
by (Step_tac 1);
by (ALLGOALS(dres_inst_tac [("a","a")] order2));
by (rtac ccontr 1);
by (asm_full_simp_tac (simpset() addsimps [divides_def,poly_mult,fun_eq]
    delsimps [pmult_Cons]) 1);
by (Blast_tac 1);
by (blast_tac (claset() addIs [lemma_order_root]) 1);
qed "order_root";

Goal "(([-a, 1] %^ n) divides p) = ((poly p = poly []) | n <= order a p)";
by (case_tac "poly p = poly []" 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [divides_def,fun_eq,poly_mult]) 1);
by (res_inst_tac [("x","[]")] exI 1);
by (TRYALL(dres_inst_tac [("a","a")] order2));
by (auto_tac (claset() addIs [poly_exp_divides],simpset()
    delsimps [pexp_Suc]));
qed "order_divides";

Goalw [divides_def] 
     "poly p ~= poly [] \
\     ==> EX q. (poly p = poly (([-a, 1] %^ (order a p)) *** q)) & \
\               ~([-a, 1] divides q)";
by (dres_inst_tac [("a","a")] order2 1);
by (asm_full_simp_tac (simpset() addsimps [divides_def]
     delsimps [pexp_Suc,pmult_Cons]) 1);
by (Step_tac 1);
by (res_inst_tac [("x","q")] exI 1);
by (Step_tac 1);
by (dres_inst_tac [("x","qa")] spec 1);
by (auto_tac (claset(),simpset() addsimps [poly_mult,fun_eq,poly_exp] 
    @ real_mult_ac delsimps [pmult_Cons]));
qed "order_decomp";

(* ------------------------------------------------------------------------- *)
(* Important composition properties of orders.                               *)
(* ------------------------------------------------------------------------- *)

Goal "poly (p *** q) ~= poly [] \
\     ==> order a (p *** q) = order a p + order a q";
by (cut_inst_tac [("a","a"),("p","p***q"),("n","order a p + order a q")] 
    order 1);
by (auto_tac (claset(),simpset() addsimps [poly_entire] delsimps [pmult_Cons]));
by (REPEAT(dres_inst_tac [("a","a")] order2 1));
by (Step_tac 1);
by (asm_full_simp_tac (simpset() addsimps [divides_def,fun_eq,poly_exp_add,
    poly_mult] delsimps [pmult_Cons]) 1);
by (Step_tac 1);
by (res_inst_tac [("x","qa *** qaa")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [poly_mult] @ real_mult_ac
    delsimps [pmult_Cons]) 1);
by (REPEAT(dres_inst_tac [("a","a")] order_decomp 1));
by (Step_tac 1);
by (subgoal_tac "[-a,1] divides (qa *** qaa)" 1);
by (asm_full_simp_tac (simpset() addsimps [poly_primes] 
    delsimps [pmult_Cons]) 1);
by (auto_tac (claset(),simpset() addsimps [divides_def] 
    delsimps [pmult_Cons]));
by (res_inst_tac [("x","qb")] exI 1);
by (subgoal_tac "poly ([-a, 1] %^ (order a p) *** (qa *** qaa)) = \
\                poly ([-a, 1] %^ (order a p) *** ([-a, 1] *** qb))" 1);
by (dtac (poly_mult_left_cancel RS iffD1) 1);
by (Force_tac 1);
by (subgoal_tac "poly ([-a, 1] %^ (order a q) *** \
\                      ([-a, 1] %^ (order a p) *** (qa *** qaa))) = \
\                poly ([-a, 1] %^ (order a q) *** \
\                      ([-a, 1] %^ (order a p) *** ([-a, 1] *** qb)))" 1);
by (dtac (poly_mult_left_cancel RS iffD1) 1);
by (Force_tac 1);
by (asm_full_simp_tac (simpset() addsimps [fun_eq,poly_exp_add,poly_mult] 
    @ real_mult_ac delsimps [pmult_Cons]) 1);
qed "order_mult";

(* FIXME: too too long! *)
Goal "ALL p q a. 0 < n &  \
\      poly (pderiv p) ~= poly [] & \
\      poly p = poly ([- a, 1] %^ n *** q) & ~ [- a, 1] divides q \
\      --> n = Suc (order a (pderiv p))";
by (induct_tac "n" 1);
by (Step_tac 1);
by (rtac order_unique_lemma 1 THEN rtac conjI 1);
by (assume_tac 1);
by (subgoal_tac "ALL r. r divides (pderiv p) = \
\                       r divides (pderiv ([-a, 1] %^ Suc n *** q))" 1);
by (dtac poly_pderiv_welldef 2);
by (asm_full_simp_tac (simpset() addsimps [divides_def] delsimps [pmult_Cons,
    pexp_Suc]) 2);
by (asm_full_simp_tac (simpset() delsimps [pmult_Cons,pexp_Suc]) 1);
by (rtac conjI 1);
by (asm_full_simp_tac (simpset() addsimps [divides_def,fun_eq] 
    delsimps [pmult_Cons,pexp_Suc]) 1);
by (res_inst_tac 
    [("x","[-a, 1] *** (pderiv q) +++ real (Suc n) %* q")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [poly_pderiv_mult,
    poly_pderiv_exp_prime,poly_add,poly_mult,poly_cmult,
    real_add_mult_distrib2] @ real_mult_ac
    delsimps [pmult_Cons,pexp_Suc]) 1);
by (asm_full_simp_tac (simpset() addsimps [poly_mult,real_add_mult_distrib2,
    real_add_mult_distrib] @ real_mult_ac delsimps [pmult_Cons]) 1);
by (thin_tac "ALL r. \
\             r divides pderiv p = \
\             r divides pderiv ([- a, 1] %^ Suc n *** q)" 1);
by (rewtac divides_def);
by (simp_tac (simpset() addsimps [poly_pderiv_mult,
    poly_pderiv_exp_prime,fun_eq,poly_add,poly_mult] 
    delsimps [pmult_Cons,pexp_Suc]) 1);
by (rtac swap 1 THEN assume_tac 1);
by (rotate_tac  3 1 THEN etac swap 1);
by (asm_full_simp_tac (simpset() delsimps [pmult_Cons,pexp_Suc]) 1);
by (Step_tac 1);
by (res_inst_tac [("x","inverse(real (Suc n)) %* (qa +++ --(pderiv q))")]
    exI 1);
by (subgoal_tac "poly ([-a, 1] %^ n *** q) = \
\         poly ([-a, 1] %^ n *** ([-a, 1] *** (inverse (real (Suc n)) %* \
\         (qa +++ -- (pderiv q)))))" 1);
by (dtac (poly_mult_left_cancel RS iffD1) 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [fun_eq,poly_mult,poly_add,poly_cmult,
    poly_minus] delsimps [pmult_Cons]) 1);
by (Step_tac 1);
by (res_inst_tac [("c1","real (Suc n)")] (real_mult_left_cancel 
    RS iffD1) 1);
by (Simp_tac 1);
by (rtac ((CLAIM_SIMP 
    "a * (b * (c * (d * e))) = e * (b * (c * (d * (a::real))))" 
     real_mult_ac) RS ssubst) 1);
by (rotate_tac 2 1);
by (dres_inst_tac [("x","xa")] spec 1);
by (asm_full_simp_tac (simpset()
    addsimps [real_add_mult_distrib] @ real_mult_ac
    delsimps [pmult_Cons]) 1);
qed_spec_mp "lemma_order_pderiv";

Goal "[| poly (pderiv p) ~= poly []; order a p ~= 0 |] \
\     ==> (order a p = Suc (order a (pderiv p)))";
by (case_tac "poly p = poly []" 1);
by (auto_tac (claset() addDs [pderiv_zero],simpset()));
by (dres_inst_tac [("a","a"),("p","p")] order_decomp 1);
by (blast_tac (claset() addIs [lemma_order_pderiv]) 1);
qed "order_pderiv";

(* ------------------------------------------------------------------------- *)
(* Now justify the standard squarefree decomposition, i.e. f / gcd(f,f').    *)
(* `a la Harrison                                                            *)
(* ------------------------------------------------------------------------- *)

Goal "[| poly (pderiv p) ~= poly []; \
\        poly p = poly (q *** d); \
\        poly (pderiv p) = poly (e *** d); \
\        poly d = poly (r *** p +++ s *** pderiv p) \
\     |] ==> order a q = (if order a p = 0 then 0 else 1)";
by (subgoal_tac "order a p = order a q + order a d" 1);
by (res_inst_tac [("s","order a (q *** d)")] trans 2);
by (blast_tac (claset() addIs [order_poly]) 2);
by (rtac order_mult 2);
by (rtac notI 2 THEN Asm_full_simp_tac 2);
by (dres_inst_tac [("p","p")] pderiv_zero 2);
by (Asm_full_simp_tac 2);
by (case_tac "order a p = 0" 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "order a (pderiv p) = order a e + order a d" 1);
by (res_inst_tac [("s","order a (e *** d)")] trans 2);
by (blast_tac (claset() addIs [order_poly]) 2);
by (rtac order_mult 2);
by (rtac notI 2 THEN Asm_full_simp_tac 2);
by (case_tac "poly p = poly []" 1);
by (dres_inst_tac [("p","p")] pderiv_zero 1);
by (Asm_full_simp_tac 1);
by (dtac order_pderiv 1 THEN assume_tac 1);
by (subgoal_tac "order a (pderiv p) <= order a d" 1);
by (subgoal_tac "([-a, 1] %^ (order a (pderiv p))) divides d" 2);
by (asm_full_simp_tac (simpset() addsimps [poly_entire,order_divides]) 2);
by (subgoal_tac "([-a, 1] %^ (order a (pderiv p))) divides p & \
\       ([-a, 1] %^ (order a (pderiv p))) divides (pderiv p)" 2);
by (asm_simp_tac (simpset() addsimps [order_divides]) 3);
by (asm_full_simp_tac (simpset() addsimps [divides_def]
    delsimps [pexp_Suc,pmult_Cons]) 2);
by (Step_tac 2);
by (res_inst_tac [("x","r *** qa +++ s *** qaa")] exI 2);
by (asm_full_simp_tac (simpset() addsimps [fun_eq,poly_add,poly_mult,
    real_add_mult_distrib, real_add_mult_distrib2] @ real_mult_ac
    delsimps [pexp_Suc,pmult_Cons]) 2);
by Auto_tac;
qed "poly_squarefree_decomp_order";


Goal "[| poly (pderiv p) ~= poly []; \
\        poly p = poly (q *** d); \
\        poly (pderiv p) = poly (e *** d); \
\        poly d = poly (r *** p +++ s *** pderiv p) \
\     |] ==> ALL a. order a q = (if order a p = 0 then 0 else 1)";
by (blast_tac (claset() addIs [poly_squarefree_decomp_order]) 1);
qed "poly_squarefree_decomp_order2";

Goal "poly p ~= poly [] ==> (poly p a = 0) = (order a p ~= 0)";
by (rtac (order_root RS ssubst) 1);
by Auto_tac;
qed "order_root2";

Goal "[| poly (pderiv p) ~= poly []; order a p ~= 0 |] \
\     ==> (order a (pderiv p) = n) = (order a p = Suc n)";
by (auto_tac (claset() addDs [order_pderiv],simpset()));
qed "order_pderiv2";

Goalw [rsquarefree_def]
  "rsquarefree p = (ALL a. ~(poly p a = 0 & poly (pderiv p) a = 0))";
by (case_tac "poly p = poly []" 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (case_tac "poly (pderiv p) = poly []" 1);
by (Asm_full_simp_tac 1);
by (dtac pderiv_iszero 1 THEN Clarify_tac 1);
by (subgoal_tac "ALL a. order a p = order a [h]" 1);
by (asm_full_simp_tac (simpset() addsimps [fun_eq]) 1);
by (rtac allI 1);
by (cut_inst_tac [("p","[h]"),("a","a")] order_root 1);
by (asm_full_simp_tac (simpset() addsimps [fun_eq]) 1);
by (blast_tac (claset() addIs [order_poly]) 1);
by (auto_tac (claset(),simpset() addsimps [order_root,order_pderiv2]));
by (dtac spec 1 THEN Auto_tac);
qed "rsquarefree_roots";

Goal "[1] *** p = p";
by Auto_tac;
qed "pmult_one";
Addsimps [pmult_one];

Goal "poly [] = poly [0]";
by (simp_tac (simpset() addsimps [fun_eq]) 1);
qed "poly_Nil_zero";

Goalw [rsquarefree_def]
     "[| rsquarefree p; poly p a = 0 |] \
\     ==> EX q. (poly p = poly ([-a, 1] *** q)) & poly q a ~= 0";
by (Step_tac 1);
by (forw_inst_tac [("a","a")] order_decomp 1);
by (dres_inst_tac [("x","a")] spec 1);
by (dres_inst_tac [("a1","a")] (order_root2 RS sym) 1);
by (auto_tac (claset(),simpset() delsimps [pmult_Cons]));
by (res_inst_tac [("x","q")] exI 1 THEN Step_tac 1);
by (asm_full_simp_tac (simpset() addsimps [poly_mult,fun_eq]) 1);
by (dres_inst_tac [("p1","q")] (poly_linear_divides RS iffD1) 1);
by (asm_full_simp_tac (simpset() addsimps [divides_def]
    delsimps [pmult_Cons]) 1);
by (Step_tac 1);
by (dres_inst_tac [("x","[]")] spec 1); 
by (auto_tac (claset(),simpset() addsimps [fun_eq]));
qed "rsquarefree_decomp";

Goal "[| poly (pderiv p) ~= poly []; \
\        poly p = poly (q *** d); \
\        poly (pderiv p) = poly (e *** d); \
\        poly d = poly (r *** p +++ s *** pderiv p) \
\     |] ==> rsquarefree q & (ALL a. (poly q a = 0) = (poly p a = 0))";
by (ftac poly_squarefree_decomp_order2 1);
by (TRYALL(assume_tac));
by (case_tac "poly p = poly []" 1);
by (blast_tac (claset() addDs [pderiv_zero]) 1);
by (simp_tac (simpset() addsimps [rsquarefree_def,
    order_root] delsimps [pmult_Cons]) 1);
by (asm_full_simp_tac (simpset() addsimps [poly_entire] 
    delsimps [pmult_Cons]) 1);
qed "poly_squarefree_decomp";


(* ------------------------------------------------------------------------- *)
(* Normalization of a polynomial.                                            *)
(* ------------------------------------------------------------------------- *)

Goal "poly (pnormalize p) = poly p";
by (induct_tac "p" 1);
by (auto_tac (claset(),simpset() addsimps [fun_eq]));
qed "poly_normalize";
Addsimps [poly_normalize];


(* ------------------------------------------------------------------------- *)
(* The degree of a polynomial.                                               *)
(* ------------------------------------------------------------------------- *)

Goal "list_all (%c. c = 0) p -->  pnormalize p = []";
by (induct_tac "p" 1);
by Auto_tac;
qed_spec_mp "lemma_degree_zero";

Goalw [degree_def] "poly p = poly [] ==> degree p = 0";
by (case_tac "pnormalize p = []" 1);
by (auto_tac (claset() addDs [lemma_degree_zero],simpset() 
    addsimps [poly_zero]));
qed "degree_zero";

(* ------------------------------------------------------------------------- *)
(* Tidier versions of finiteness of roots.                                   *)
(* ------------------------------------------------------------------------- *)

Goal "poly p ~= poly [] ==> finite {x. poly p x = 0}";
by (auto_tac (claset(),simpset() addsimps [poly_roots_finite]));
by (res_inst_tac [("B","{x::real. EX n. (n::nat) < N & (x = j n)}")] 
    finite_subset 1);
by (induct_tac "N" 2);
by Auto_tac;
by (subgoal_tac "{x::real. EX na. na < Suc n & (x = j na)} = \
\                 {(j n)} Un {x. EX na. na < n & (x = j na)}" 1);
by (auto_tac (claset(),simpset() addsimps [ARITH_PROVE 
    "(na < Suc n) = (na = n | na < n)"]));
qed "poly_roots_finite_set";

(* ------------------------------------------------------------------------- *)
(* bound for polynomial.                                                     *)
(* ------------------------------------------------------------------------- *)

Goal "abs(x) <= k --> abs(poly p x) <= poly (map abs p) k";
by (induct_tac "p" 1);
by Auto_tac;
by (res_inst_tac [("j","abs a + abs(x * poly list x)")] real_le_trans 1);
by (rtac abs_triangle_ineq 1);
by (auto_tac (claset() addSIs [real_mult_le_mono],simpset() 
    addsimps [abs_mult]));
by (arith_tac 1);
qed_spec_mp "poly_mono"; 
