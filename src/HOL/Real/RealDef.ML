(*  Title       : Real/RealDef.ML
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The reals
*)

(*Ensures that Blast_tac can cope with real*)
Blast.overloaded ("RealDef.real", domain_type); 

(*** Proving that realrel is an equivalence relation ***)

Goal "[| (x1::preal) + y2 = x2 + y1; x2 + y3 = x3 + y2 |] \
\     ==> x1 + y3 = x3 + y1";        
by (res_inst_tac [("C","y2")] preal_add_right_cancel 1);
by (rotate_tac 1 1 THEN dtac sym 1);
by (asm_full_simp_tac (simpset() addsimps preal_add_ac) 1);
by (rtac (preal_add_left_commute RS subst) 1);
by (res_inst_tac [("x1","x1")] (preal_add_assoc RS subst) 1);
by (asm_full_simp_tac (simpset() addsimps preal_add_ac) 1);
qed "preal_trans_lemma";

(** Natural deduction for realrel **)

Goalw [realrel_def]
    "(((x1,y1),(x2,y2)): realrel) = (x1 + y2 = x2 + y1)";
by (Blast_tac 1);
qed "realrel_iff";

Goalw [realrel_def]
    "[| x1 + y2 = x2 + y1 |] ==> ((x1,y1),(x2,y2)): realrel";
by (Blast_tac  1);
qed "realrelI";

Goalw [realrel_def]
  "p: realrel --> (EX x1 y1 x2 y2. \
\                  p = ((x1,y1),(x2,y2)) & x1 + y2 = x2 + y1)";
by (Blast_tac 1);
qed "realrelE_lemma";

val [major,minor] = Goal
  "[| p: realrel;  \
\     !!x1 y1 x2 y2. [| p = ((x1,y1),(x2,y2));  x1+y2 = x2+y1 \
\                    |] ==> Q |] ==> Q";
by (cut_facts_tac [major RS (realrelE_lemma RS mp)] 1);
by (REPEAT (eresolve_tac [asm_rl,exE,conjE,minor] 1));
qed "realrelE";

Goal "(x,x): realrel";
by (case_tac "x" 1);
by (asm_simp_tac (simpset() addsimps [realrel_def]) 1);
qed "realrel_refl";

Goalw [equiv_def, refl_def, sym_def, trans_def] "equiv UNIV realrel";
by (fast_tac (claset() addSIs [realrelI, realrel_refl] 
                       addSEs [sym, realrelE, preal_trans_lemma]) 1);
qed "equiv_realrel";

(* (realrel `` {x} = realrel `` {y}) = ((x,y) : realrel) *)
bind_thm ("equiv_realrel_iff",
    	  [equiv_realrel, UNIV_I, UNIV_I] MRS eq_equiv_class_iff);

Goalw [REAL_def,realrel_def,quotient_def] "realrel``{(x,y)}: REAL";
by (Blast_tac 1);
qed "realrel_in_real";

Goal "inj_on Abs_REAL REAL";
by (rtac inj_on_inverseI 1);
by (etac Abs_REAL_inverse 1);
qed "inj_on_Abs_REAL";

Addsimps [equiv_realrel_iff,inj_on_Abs_REAL RS inj_on_iff,
          realrel_iff, realrel_in_real, Abs_REAL_inverse];

Addsimps [equiv_realrel RS eq_equiv_class_iff];
bind_thm ("eq_realrelD", equiv_realrel RSN (2,eq_equiv_class));

Goal "inj Rep_REAL";
by (rtac inj_inverseI 1);
by (rtac Rep_REAL_inverse 1);
qed "inj_Rep_REAL";

(** real_of_preal: the injection from preal to real **)
Goal "inj(real_of_preal)";
by (rtac injI 1);
by (rewtac real_of_preal_def);
by (dtac (inj_on_Abs_REAL RS inj_onD) 1);
by (REPEAT (rtac realrel_in_real 1));
by (dtac eq_equiv_class 1);
by (rtac equiv_realrel 1);
by (Blast_tac 1);
by (asm_full_simp_tac (simpset() addsimps [realrel_def]) 1); 
qed "inj_real_of_preal";

val [prem] = Goal
    "(!!x y. z = Abs_REAL(realrel``{(x,y)}) ==> P) ==> P";
by (res_inst_tac [("x1","z")] 
    (rewrite_rule [REAL_def] Rep_REAL RS quotientE) 1);
by (dres_inst_tac [("f","Abs_REAL")] arg_cong 1);
by (case_tac "x" 1);
by (rtac prem 1);
by (asm_full_simp_tac (simpset() addsimps [Rep_REAL_inverse]) 1);
qed "eq_Abs_REAL";

(**** real_minus: additive inverse on real ****)

Goalw [congruent_def]
  "congruent realrel (%p. (%(x,y). realrel``{(y,x)}) p)";
by (Clarify_tac 1); 
by (asm_full_simp_tac (simpset() addsimps [preal_add_commute]) 1);
qed "real_minus_congruent";

Goalw [real_minus_def]
      "- (Abs_REAL(realrel``{(x,y)})) = Abs_REAL(realrel `` {(y,x)})";
by (res_inst_tac [("f","Abs_REAL")] arg_cong 1);
by (simp_tac (simpset() addsimps [realrel_in_real RS Abs_REAL_inverse,
                [equiv_realrel, real_minus_congruent] MRS UN_equiv_class]) 1);
qed "real_minus";

Goal "- (- z) = (z::real)";
by (res_inst_tac [("z","z")] eq_Abs_REAL 1);
by (asm_simp_tac (simpset() addsimps [real_minus]) 1);
qed "real_minus_minus";

Addsimps [real_minus_minus];

Goal "inj(%r::real. -r)";
by (rtac injI 1);
by (dres_inst_tac [("f","uminus")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [real_minus_minus]) 1);
qed "inj_real_minus";

Goalw [real_zero_def] "- 0 = (0::real)";
by (simp_tac (simpset() addsimps [real_minus]) 1);
qed "real_minus_zero";

Addsimps [real_minus_zero];

Goal "(-x = 0) = (x = (0::real))"; 
by (res_inst_tac [("z","x")] eq_Abs_REAL 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_zero_def, real_minus] @ preal_add_ac));
qed "real_minus_zero_iff";

Addsimps [real_minus_zero_iff];

(*** Congruence property for addition ***)
Goalw [congruent2_def]
    "congruent2 realrel (%p1 p2.                  \
\         (%(x1,y1). (%(x2,y2). realrel``{(x1+x2, y1+y2)}) p2) p1)";
by (clarify_tac (claset() addSEs [realrelE]) 1); 
by (asm_simp_tac (simpset() addsimps [preal_add_assoc]) 1);
by (res_inst_tac [("z1.1","x1a")] (preal_add_left_commute RS ssubst) 1);
by (asm_simp_tac (simpset() addsimps [preal_add_assoc RS sym]) 1);
by (asm_simp_tac (simpset() addsimps preal_add_ac) 1);
qed "real_add_congruent2";

Goalw [real_add_def]
  "Abs_REAL(realrel``{(x1,y1)}) + Abs_REAL(realrel``{(x2,y2)}) = \
\  Abs_REAL(realrel``{(x1+x2, y1+y2)})";
by (simp_tac (simpset() addsimps 
              [[equiv_realrel, real_add_congruent2] MRS UN_equiv_class2]) 1);
qed "real_add";

Goal "(z::real) + w = w + z";
by (res_inst_tac [("z","z")] eq_Abs_REAL 1);
by (res_inst_tac [("z","w")] eq_Abs_REAL 1);
by (asm_simp_tac (simpset() addsimps preal_add_ac @ [real_add]) 1);
qed "real_add_commute";

Goal "((z1::real) + z2) + z3 = z1 + (z2 + z3)";
by (res_inst_tac [("z","z1")] eq_Abs_REAL 1);
by (res_inst_tac [("z","z2")] eq_Abs_REAL 1);
by (res_inst_tac [("z","z3")] eq_Abs_REAL 1);
by (asm_simp_tac (simpset() addsimps [real_add, preal_add_assoc]) 1);
qed "real_add_assoc";

(*For AC rewriting*)
Goal "(x::real)+(y+z)=y+(x+z)";
by (rtac (real_add_commute RS trans) 1);
by (rtac (real_add_assoc RS trans) 1);
by (rtac (real_add_commute RS arg_cong) 1);
qed "real_add_left_commute";

(* real addition is an AC operator *)
bind_thms ("real_add_ac", [real_add_assoc,real_add_commute,real_add_left_commute]);

Goalw [real_of_preal_def,real_zero_def] "(0::real) + z = z";
by (res_inst_tac [("z","z")] eq_Abs_REAL 1);
by (asm_full_simp_tac (simpset() addsimps [real_add] @ preal_add_ac) 1);
qed "real_add_zero_left";
Addsimps [real_add_zero_left];

Goal "z + (0::real) = z";
by (simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "real_add_zero_right";
Addsimps [real_add_zero_right];

Goalw [real_zero_def] "z + (-z) = (0::real)";
by (res_inst_tac [("z","z")] eq_Abs_REAL 1);
by (asm_full_simp_tac (simpset() addsimps [real_minus,
        real_add, preal_add_commute]) 1);
qed "real_add_minus";
Addsimps [real_add_minus];

Goal "(-z) + z = (0::real)";
by (simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "real_add_minus_left";
Addsimps [real_add_minus_left];


Goal "z + ((- z) + w) = (w::real)";
by (simp_tac (simpset() addsimps [real_add_assoc RS sym]) 1);
qed "real_add_minus_cancel";

Goal "(-z) + (z + w) = (w::real)";
by (simp_tac (simpset() addsimps [real_add_assoc RS sym]) 1);
qed "real_minus_add_cancel";

Addsimps [real_add_minus_cancel, real_minus_add_cancel];

Goal "EX y. (x::real) + y = 0";
by (blast_tac (claset() addIs [real_add_minus]) 1);
qed "real_minus_ex";

Goal "EX! y. (x::real) + y = 0";
by (auto_tac (claset() addIs [real_add_minus],simpset()));
by (dres_inst_tac [("f","%x. ya+x")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_assoc RS sym]) 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "real_minus_ex1";

Goal "EX! y. y + (x::real) = 0";
by (auto_tac (claset() addIs [real_add_minus_left],simpset()));
by (dres_inst_tac [("f","%x. x+ya")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_assoc]) 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "real_minus_left_ex1";

Goal "x + y = (0::real) ==> x = -y";
by (cut_inst_tac [("z","y")] real_add_minus_left 1);
by (res_inst_tac [("x1","y")] (real_minus_left_ex1 RS ex1E) 1);
by (Blast_tac 1);
qed "real_add_minus_eq_minus";

Goal "EX (y::real). x = -y";
by (cut_inst_tac [("x","x")] real_minus_ex 1);
by (etac exE 1 THEN dtac real_add_minus_eq_minus 1);
by (Fast_tac 1);
qed "real_as_add_inverse_ex";

Goal "-(x + y) = (-x) + (- y :: real)";
by (res_inst_tac [("z","x")] eq_Abs_REAL 1);
by (res_inst_tac [("z","y")] eq_Abs_REAL 1);
by (auto_tac (claset(),simpset() addsimps [real_minus,real_add]));
qed "real_minus_add_distrib";

Addsimps [real_minus_add_distrib];

Goal "((x::real) + y = x + z) = (y = z)";
by (Step_tac 1);
by (dres_inst_tac [("f","%t. (-x) + t")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_assoc RS sym]) 1);
qed "real_add_left_cancel";

Goal "(y + (x::real)= z + x) = (y = z)";
by (simp_tac (simpset() addsimps [real_add_commute,real_add_left_cancel]) 1);
qed "real_add_right_cancel";

Goal "(0::real) - x = -x";
by (simp_tac (simpset() addsimps [real_diff_def]) 1);
qed "real_diff_0";

Goal "x - (0::real) = x";
by (simp_tac (simpset() addsimps [real_diff_def]) 1);
qed "real_diff_0_right";

Goal "x - x = (0::real)";
by (simp_tac (simpset() addsimps [real_diff_def]) 1);
qed "real_diff_self";

Addsimps [real_diff_0, real_diff_0_right, real_diff_self];


(*** Congruence property for multiplication ***)

Goal "!!(x1::preal). [| x1 + y2 = x2 + y1 |] ==> \
\         x * x1 + y * y1 + (x * y2 + x2 * y) = \
\         x * x2 + y * y2 + (x * y1 + x1 * y)";
by (asm_full_simp_tac (simpset() addsimps [preal_add_left_commute,
    preal_add_assoc RS sym,preal_add_mult_distrib2 RS sym]) 1);
by (rtac (preal_mult_commute RS subst) 1);
by (res_inst_tac [("y1","x2")] (preal_mult_commute RS subst) 1);
by (asm_full_simp_tac (simpset() addsimps [preal_add_assoc,
    preal_add_mult_distrib2 RS sym]) 1);
by (asm_full_simp_tac (simpset() addsimps [preal_add_commute]) 1);
qed "real_mult_congruent2_lemma";

Goal 
    "congruent2 realrel (%p1 p2.                  \
\         (%(x1,y1). (%(x2,y2). realrel``{(x1*x2 + y1*y2, x1*y2+x2*y1)}) p2) p1)";
by (rtac (equiv_realrel RS congruent2_commuteI) 1);
by (Clarify_tac 1); 
by (rewtac split_def);
by (asm_simp_tac (simpset() addsimps [preal_mult_commute,preal_add_commute]) 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_congruent2_lemma]));
qed "real_mult_congruent2";

Goalw [real_mult_def]
   "Abs_REAL((realrel``{(x1,y1)})) * Abs_REAL((realrel``{(x2,y2)})) =   \
\   Abs_REAL(realrel `` {(x1*x2+y1*y2,x1*y2+x2*y1)})";
by (simp_tac (simpset() addsimps
               [[equiv_realrel, real_mult_congruent2] MRS UN_equiv_class2]) 1);
qed "real_mult";

Goal "(z::real) * w = w * z";
by (res_inst_tac [("z","z")] eq_Abs_REAL 1);
by (res_inst_tac [("z","w")] eq_Abs_REAL 1);
by (asm_simp_tac
    (simpset() addsimps [real_mult] @ preal_add_ac @ preal_mult_ac) 1);
qed "real_mult_commute";

Goal "((z1::real) * z2) * z3 = z1 * (z2 * z3)";
by (res_inst_tac [("z","z1")] eq_Abs_REAL 1);
by (res_inst_tac [("z","z2")] eq_Abs_REAL 1);
by (res_inst_tac [("z","z3")] eq_Abs_REAL 1);
by (asm_simp_tac (simpset() addsimps [preal_add_mult_distrib2,real_mult] @ 
                                     preal_add_ac @ preal_mult_ac) 1);
qed "real_mult_assoc";

Goal "(z1::real) * (z2 * z3) = z2 * (z1 * z3)";
by (rtac (real_mult_commute RS trans) 1);
by (rtac (real_mult_assoc RS trans) 1);
by (rtac (real_mult_commute RS arg_cong) 1);
qed "real_mult_left_commute";

(* real multiplication is an AC operator *)
bind_thms ("real_mult_ac", 
	   [real_mult_assoc, real_mult_commute, real_mult_left_commute]);

Goalw [real_one_def,pnat_one_def] "(1::real) * z = z";
by (res_inst_tac [("z","z")] eq_Abs_REAL 1);
by (asm_full_simp_tac
    (simpset() addsimps [real_mult,
			 preal_add_mult_distrib2,preal_mult_1_right] 
                        @ preal_mult_ac @ preal_add_ac) 1);
qed "real_mult_1";

Addsimps [real_mult_1];

Goal "z * (1::real) = z";
by (simp_tac (simpset() addsimps [real_mult_commute]) 1);
qed "real_mult_1_right";

Addsimps [real_mult_1_right];

Goalw [real_zero_def,pnat_one_def] "0 * z = (0::real)";
by (res_inst_tac [("z","z")] eq_Abs_REAL 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult,
    preal_add_mult_distrib2,preal_mult_1_right] 
    @ preal_mult_ac @ preal_add_ac) 1);
qed "real_mult_0";

Goal "z * 0 = (0::real)";
by (simp_tac (simpset() addsimps [real_mult_commute, real_mult_0]) 1);
qed "real_mult_0_right";

Addsimps [real_mult_0_right, real_mult_0];

Goal "-(x * y) = (-x) * (y::real)";
by (res_inst_tac [("z","x")] eq_Abs_REAL 1);
by (res_inst_tac [("z","y")] eq_Abs_REAL 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_minus,real_mult] 
                                 @ preal_mult_ac @ preal_add_ac));
qed "real_minus_mult_eq1";

Goal "-(x * y) = x * (- y :: real)";
by (simp_tac (simpset() addsimps [inst "z" "x" real_mult_commute,
				  real_minus_mult_eq1]) 1);
qed "real_minus_mult_eq2";

(*Pull negations out*)
Addsimps [real_minus_mult_eq1 RS sym, real_minus_mult_eq2 RS sym];

Goal "(- (1::real)) * z = -z";
by (Simp_tac 1);
qed "real_mult_minus_1";
Addsimps [real_mult_minus_1];

Goal "z * (- (1::real)) = -z";
by (stac real_mult_commute 1);
by (Simp_tac 1);
qed "real_mult_minus_1_right";
Addsimps [real_mult_minus_1_right];

Goal "(-x) * (-y) = x * (y::real)";
by (full_simp_tac (simpset() addsimps [real_minus_mult_eq2 RS sym,
				       real_minus_mult_eq1 RS sym]) 1);
qed "real_minus_mult_cancel";

Addsimps [real_minus_mult_cancel];

Goal "(-x) * y = x * (- y :: real)";
by (full_simp_tac (simpset() addsimps [real_minus_mult_eq2 RS sym,
				       real_minus_mult_eq1 RS sym]) 1);
qed "real_minus_mult_commute";

(** Lemmas **)

Goal "(z::real) + v = z' + v' ==> z + (v + w) = z' + (v' + w)";
by (asm_simp_tac (simpset() addsimps [real_add_assoc RS sym]) 1);
qed "real_add_assoc_cong";

Goal "(z::real) + (v + w) = v + (z + w)";
by (REPEAT (ares_tac [real_add_commute RS real_add_assoc_cong] 1));
qed "real_add_assoc_swap";

Goal "((z1::real) + z2) * w = (z1 * w) + (z2 * w)";
by (res_inst_tac [("z","z1")] eq_Abs_REAL 1);
by (res_inst_tac [("z","z2")] eq_Abs_REAL 1);
by (res_inst_tac [("z","w")] eq_Abs_REAL 1);
by (asm_simp_tac 
    (simpset() addsimps [preal_add_mult_distrib2, real_add, real_mult] @ 
                        preal_add_ac @ preal_mult_ac) 1);
qed "real_add_mult_distrib";

val real_mult_commute'= inst "z" "w" real_mult_commute;

Goal "(w::real) * (z1 + z2) = (w * z1) + (w * z2)";
by (simp_tac (simpset() addsimps [real_mult_commute',
				  real_add_mult_distrib]) 1);
qed "real_add_mult_distrib2";

Goalw [real_diff_def] "((z1::real) - z2) * w = (z1 * w) - (z2 * w)";
by (simp_tac (simpset() addsimps [real_add_mult_distrib]) 1);
qed "real_diff_mult_distrib";

Goal "(w::real) * (z1 - z2) = (w * z1) - (w * z2)";
by (simp_tac (simpset() addsimps [real_mult_commute', 
				  real_diff_mult_distrib]) 1);
qed "real_diff_mult_distrib2";

(*** one and zero are distinct ***)
Goalw [real_zero_def,real_one_def] "0 ~= (1::real)";
by (auto_tac (claset(),
         simpset() addsimps [preal_self_less_add_left RS preal_not_refl2]));
qed "real_zero_not_eq_one";

(*** existence of inverse ***)
(** lemma -- alternative definition of 0 **)
Goalw [real_zero_def] "0 = Abs_REAL (realrel `` {(x, x)})";
by (auto_tac (claset(),simpset() addsimps [preal_add_commute]));
qed "real_zero_iff";

Goalw [real_zero_def,real_one_def] 
          "!!(x::real). x ~= 0 ==> EX y. x*y = (1::real)";
by (res_inst_tac [("z","x")] eq_Abs_REAL 1);
by (cut_inst_tac [("r1.0","xa"),("r2.0","y")] preal_linear 1);
by (auto_tac (claset() addSDs [preal_less_add_left_Ex],
           simpset() addsimps [real_zero_iff RS sym]));
by (res_inst_tac [("x",
    "Abs_REAL (realrel `` \
\     {(preal_of_prat(prat_of_pnat 1),  \
\       pinv(D) + preal_of_prat(prat_of_pnat 1))})")] exI 1);
by (res_inst_tac [("x",
     "Abs_REAL (realrel `` \
\      {(pinv(D) + preal_of_prat(prat_of_pnat 1),\
\        preal_of_prat(prat_of_pnat 1))})")] exI 2);
by (auto_tac (claset(),
	      simpset() addsimps [real_mult,
    pnat_one_def,preal_mult_1_right,preal_add_mult_distrib2,
    preal_add_mult_distrib,preal_mult_1,preal_mult_inv_right] 
    @ preal_add_ac @ preal_mult_ac));
qed "real_mult_inv_right_ex";

Goal "x ~= 0 ==> EX y. y*x = (1::real)";
by (dtac real_mult_inv_right_ex 1); 
by (auto_tac (claset(), simpset() addsimps [real_mult_commute]));  
qed "real_mult_inv_left_ex";

Goalw [real_inverse_def] "x ~= 0 ==> inverse(x)*x = (1::real)";
by (ftac real_mult_inv_left_ex 1);
by (Step_tac 1);
by (rtac someI2 1);
by Auto_tac;
qed "real_mult_inv_left";
Addsimps [real_mult_inv_left];

Goal "x ~= 0 ==> x*inverse(x) = (1::real)";
by (stac real_mult_commute 1);
by (auto_tac (claset(), simpset() addsimps [real_mult_inv_left]));
qed "real_mult_inv_right";
Addsimps [real_mult_inv_right];

(** Inverse of zero!  Useful to simplify certain equations **)

Goalw [real_inverse_def] "inverse 0 = (0::real)";
by (rtac someI2 1);
by (auto_tac (claset(), simpset() addsimps [real_zero_not_eq_one]));  
qed "INVERSE_ZERO";

Goal "a / (0::real) = 0";
by (simp_tac (simpset() addsimps [real_divide_def, INVERSE_ZERO]) 1);
qed "DIVISION_BY_ZERO";  (*NOT for adding to default simpset*)

fun real_div_undefined_case_tac s i =
  case_tac s i THEN 
  asm_simp_tac (simpset() addsimps [DIVISION_BY_ZERO, INVERSE_ZERO]) i;


Goal "(c::real) ~= 0 ==> (c*a=c*b) = (a=b)";
by Auto_tac;
by (dres_inst_tac [("f","%x. x*inverse c")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps real_mult_ac)  1);
qed "real_mult_left_cancel";
    
Goal "(c::real) ~= 0 ==> (a*c=b*c) = (a=b)";
by (Step_tac 1);
by (dres_inst_tac [("f","%x. x*inverse c")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps real_mult_ac)  1);
qed "real_mult_right_cancel";

Goal "c*a ~= c*b ==> a ~= b";
by Auto_tac;
qed "real_mult_left_cancel_ccontr";

Goal "a*c ~= b*c ==> a ~= b";
by Auto_tac;
qed "real_mult_right_cancel_ccontr";

Goalw [real_inverse_def] "x ~= 0 ==> inverse(x::real) ~= 0";
by (ftac real_mult_inv_left_ex 1);
by (etac exE 1);
by (rtac someI2 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_mult_0, real_zero_not_eq_one]));
qed "real_inverse_not_zero";

Goal "[| x ~= 0; y ~= 0 |] ==> x * y ~= (0::real)";
by (Step_tac 1);
by (dres_inst_tac [("f","%z. inverse x*z")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult_assoc RS sym]) 1);
qed "real_mult_not_zero";

Goal "inverse(inverse (x::real)) = x";
by (real_div_undefined_case_tac "x=0" 1);
by (res_inst_tac [("c1","inverse x")] (real_mult_right_cancel RS iffD1) 1);
by (etac real_inverse_not_zero 1);
by (auto_tac (claset() addDs [real_inverse_not_zero],simpset()));
qed "real_inverse_inverse";
Addsimps [real_inverse_inverse];

Goalw [real_inverse_def] "inverse((1::real)) = (1::real)";
by (cut_facts_tac [real_zero_not_eq_one RS 
                   not_sym RS real_mult_inv_left_ex] 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_zero_not_eq_one RS not_sym]));
qed "real_inverse_1";
Addsimps [real_inverse_1];

Goal "inverse(-x) = -inverse(x::real)";
by (real_div_undefined_case_tac "x=0" 1);
by (res_inst_tac [("c1","-x")] (real_mult_right_cancel RS iffD1) 1);
by (stac real_mult_inv_left 2);
by Auto_tac;
qed "real_minus_inverse";

Goal "inverse(x*y) = inverse(x)*inverse(y::real)";
by (real_div_undefined_case_tac "x=0" 1);
by (real_div_undefined_case_tac "y=0" 1);
by (forw_inst_tac [("y","y")] real_mult_not_zero 1 THEN assume_tac 1);
by (res_inst_tac [("c1","x")] (real_mult_left_cancel RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc RS sym]));
by (res_inst_tac [("c1","y")] (real_mult_left_cancel RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_left_commute]));
by (asm_simp_tac (simpset() addsimps [real_mult_assoc RS sym]) 1);
qed "real_inverse_distrib";

Goal "(x::real) * (y/z) = (x*y)/z";
by (simp_tac (simpset() addsimps [real_divide_def, real_mult_assoc]) 1); 
qed "real_times_divide1_eq";

Goal "(y/z) * (x::real) = (y*x)/z";
by (simp_tac (simpset() addsimps [real_divide_def]@real_mult_ac) 1); 
qed "real_times_divide2_eq";

Addsimps [real_times_divide1_eq, real_times_divide2_eq];

Goal "(x::real) / (y/z) = (x*z)/y";
by (simp_tac (simpset() addsimps [real_divide_def, real_inverse_distrib]@
                                 real_mult_ac) 1); 
qed "real_divide_divide1_eq";

Goal "((x::real) / y) / z = x/(y*z)";
by (simp_tac (simpset() addsimps [real_divide_def, real_inverse_distrib, 
                                  real_mult_assoc]) 1); 
qed "real_divide_divide2_eq";

Addsimps [real_divide_divide1_eq, real_divide_divide2_eq];

(** As with multiplication, pull minus signs OUT of the / operator **)

Goal "(-x) / (y::real) = - (x/y)";
by (simp_tac (simpset() addsimps [real_divide_def]) 1); 
qed "real_minus_divide_eq";
Addsimps [real_minus_divide_eq];

Goal "(x / -(y::real)) = - (x/y)";
by (simp_tac (simpset() addsimps [real_divide_def, real_minus_inverse]) 1); 
qed "real_divide_minus_eq";
Addsimps [real_divide_minus_eq];

Goal "(x+y)/(z::real) = x/z + y/z";
by (simp_tac (simpset() addsimps [real_divide_def, real_add_mult_distrib]) 1); 
qed "real_add_divide_distrib";

(*The following would e.g. convert (x+y)/2 to x/2 + y/2.  Sometimes that
  leads to cancellations in x or y, but is also prevents "multiplying out"
  the 2 in e.g. (x+y)/2 = 5.
  
Addsimps [inst "z" "number_of ?w" real_add_divide_distrib];
**)


(*---------------------------------------------------------
     Theorems for ordering
 --------------------------------------------------------*)
(* prove introduction and elimination rules for real_less *)

(* real_less is a strong order i.e. nonreflexive and transitive *)

(*** lemmas ***)
Goal "!!(x::preal). [| x = y; x1 = y1 |] ==> x + y1 = x1 + y";
by (asm_simp_tac (simpset() addsimps [preal_add_commute]) 1);
qed "preal_lemma_eq_rev_sum";

Goal "!!(b::preal). x + (b + y) = x1 + (b + y1) ==> x + y = x1 + y1";
by (asm_full_simp_tac (simpset() addsimps preal_add_ac) 1);
qed "preal_add_left_commute_cancel";

Goal "!!(x::preal). [| x + y2a = x2a + y; \
\                      x + y2b = x2b + y |] \
\                   ==> x2a + y2b = x2b + y2a";
by (dtac preal_lemma_eq_rev_sum 1);
by (assume_tac 1);
by (thin_tac "x + y2b = x2b + y" 1);
by (asm_full_simp_tac (simpset() addsimps preal_add_ac) 1);
by (dtac preal_add_left_commute_cancel 1);
by (asm_full_simp_tac (simpset() addsimps preal_add_ac) 1);
qed "preal_lemma_for_not_refl";

Goal "~ (R::real) < R";
by (res_inst_tac [("z","R")] eq_Abs_REAL 1);
by (auto_tac (claset(),simpset() addsimps [real_less_def]));
by (dtac preal_lemma_for_not_refl 1);
by (assume_tac 1);
by Auto_tac;
qed "real_less_not_refl";

(*** y < y ==> P ***)
bind_thm("real_less_irrefl", real_less_not_refl RS notE);
AddSEs [real_less_irrefl];

Goal "!!(x::real). x < y ==> x ~= y";
by (auto_tac (claset(),simpset() addsimps [real_less_not_refl]));
qed "real_not_refl2";

(* lemma re-arranging and eliminating terms *)
Goal "!! (a::preal). [| a + b = c + d; \
\            x2b + d + (c + y2e) < a + y2b + (x2e + b) |] \
\         ==> x2b + y2e < x2e + y2b";
by (asm_full_simp_tac (simpset() addsimps preal_add_ac) 1);
by (res_inst_tac [("C","c+d")] preal_add_left_less_cancel 1);
by (asm_full_simp_tac (simpset() addsimps [preal_add_assoc RS sym]) 1);
qed "preal_lemma_trans";

(** heavy re-writing involved*)
Goal "!!(R1::real). [| R1 < R2; R2 < R3 |] ==> R1 < R3";
by (res_inst_tac [("z","R1")] eq_Abs_REAL 1);
by (res_inst_tac [("z","R2")] eq_Abs_REAL 1);
by (res_inst_tac [("z","R3")] eq_Abs_REAL 1);
by (auto_tac (claset(),simpset() addsimps [real_less_def]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (dtac preal_lemma_for_not_refl 1 THEN assume_tac 1);
by (blast_tac (claset() addDs [preal_add_less_mono] 
    addIs [preal_lemma_trans]) 1);
qed "real_less_trans";

Goal "!! (R1::real). R1 < R2 ==> ~ (R2 < R1)";
by (rtac notI 1);
by (dtac real_less_trans 1 THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [real_less_not_refl]) 1);
qed "real_less_not_sym";

(* [| x < y;  ~P ==> y < x |] ==> P *)
bind_thm ("real_less_asym", real_less_not_sym RS contrapos_np);

Goalw [real_of_preal_def] 
     "real_of_preal ((z1::preal) + z2) = \
\     real_of_preal z1 + real_of_preal z2";
by (asm_simp_tac (simpset() addsimps [real_add,
       preal_add_mult_distrib,preal_mult_1] addsimps preal_add_ac) 1);
qed "real_of_preal_add";

Goalw [real_of_preal_def] 
     "real_of_preal ((z1::preal) * z2) = \
\     real_of_preal z1* real_of_preal z2";
by (full_simp_tac (simpset() addsimps [real_mult,
        preal_add_mult_distrib2,preal_mult_1,
        preal_mult_1_right,pnat_one_def] 
        @ preal_add_ac @ preal_mult_ac) 1);
qed "real_of_preal_mult";

Goalw [real_of_preal_def]
      "!!(x::preal). y < x ==> \
\      EX m. Abs_REAL (realrel `` {(x,y)}) = real_of_preal m";
by (auto_tac (claset() addSDs [preal_less_add_left_Ex],
    simpset() addsimps preal_add_ac));
qed "real_of_preal_ExI";

Goalw [real_of_preal_def]
      "!!(x::preal). EX m. Abs_REAL (realrel `` {(x,y)}) = \
\                    real_of_preal m ==> y < x";
by (auto_tac (claset(),
	      simpset() addsimps 
    [preal_add_commute,preal_add_assoc]));
by (asm_full_simp_tac (simpset() addsimps 
    [preal_add_assoc RS sym,preal_self_less_add_left]) 1);
qed "real_of_preal_ExD";

Goal "(EX m. Abs_REAL (realrel `` {(x,y)}) = real_of_preal m) = (y < x)";
by (blast_tac (claset() addSIs [real_of_preal_ExI,real_of_preal_ExD]) 1);
qed "real_of_preal_iff";

(*** Gleason prop 9-4.4 p 127 ***)
Goalw [real_of_preal_def,real_zero_def] 
      "EX m. (x::real) = real_of_preal m | x = 0 | x = -(real_of_preal m)";
by (res_inst_tac [("z","x")] eq_Abs_REAL 1);
by (auto_tac (claset(),simpset() addsimps [real_minus] @ preal_add_ac));
by (cut_inst_tac [("r1.0","x"),("r2.0","y")] preal_linear 1);
by (auto_tac (claset() addSDs [preal_less_add_left_Ex],
    simpset() addsimps [preal_add_assoc RS sym]));
by (auto_tac (claset(),simpset() addsimps [preal_add_commute]));
qed "real_of_preal_trichotomy";

Goal "!!P. [| !!m. x = real_of_preal m ==> P; \
\             x = 0 ==> P; \
\             !!m. x = -(real_of_preal m) ==> P |] ==> P";
by (cut_inst_tac [("x","x")] real_of_preal_trichotomy 1);
by Auto_tac;
qed "real_of_preal_trichotomyE";

Goalw [real_of_preal_def] 
      "real_of_preal m1 < real_of_preal m2 ==> m1 < m2";
by (auto_tac (claset(),simpset() addsimps [real_less_def] @ preal_add_ac));
by (auto_tac (claset(),simpset() addsimps [preal_add_assoc RS sym]));
by (auto_tac (claset(),simpset() addsimps preal_add_ac));
qed "real_of_preal_lessD";

Goal "m1 < m2 ==> real_of_preal m1 < real_of_preal m2";
by (dtac preal_less_add_left_Ex 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_of_preal_add,
    real_of_preal_def,real_less_def]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (simp_tac (simpset() addsimps [preal_self_less_add_left] 
    delsimps [preal_add_less_iff2]) 1);
qed "real_of_preal_lessI";

Goal "(real_of_preal m1 < real_of_preal m2) = (m1 < m2)";
by (blast_tac (claset() addIs [real_of_preal_lessI,real_of_preal_lessD]) 1);
qed "real_of_preal_less_iff1";

Addsimps [real_of_preal_less_iff1];

Goal "- real_of_preal m < real_of_preal m";
by (auto_tac (claset(),
	      simpset() addsimps 
    [real_of_preal_def,real_less_def,real_minus]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (full_simp_tac (simpset() addsimps preal_add_ac) 1);
by (full_simp_tac (simpset() addsimps [preal_self_less_add_right,
    preal_add_assoc RS sym]) 1);
qed "real_of_preal_minus_less_self";

Goalw [real_zero_def] "- real_of_preal m < 0";
by (auto_tac (claset(),
	      simpset() addsimps [real_of_preal_def,
				  real_less_def,real_minus]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (full_simp_tac (simpset() addsimps 
  [preal_self_less_add_right] @ preal_add_ac) 1);
qed "real_of_preal_minus_less_zero";

Goal "~ 0 < - real_of_preal m";
by (cut_facts_tac [real_of_preal_minus_less_zero] 1);
by (fast_tac (claset() addDs [real_less_trans] 
                        addEs [real_less_irrefl]) 1);
qed "real_of_preal_not_minus_gt_zero";

Goalw [real_zero_def] "0 < real_of_preal m";
by (auto_tac (claset(),simpset() addsimps 
   [real_of_preal_def,real_less_def,real_minus]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (full_simp_tac (simpset() addsimps 
		   [preal_self_less_add_right] @ preal_add_ac) 1);
qed "real_of_preal_zero_less";

Goal "~ real_of_preal m < 0";
by (cut_facts_tac [real_of_preal_zero_less] 1);
by (blast_tac (claset() addDs [real_less_trans] 
                        addEs [real_less_irrefl]) 1);
qed "real_of_preal_not_less_zero";

Goal "0 < - (- real_of_preal m)";
by (simp_tac (simpset() addsimps 
    [real_of_preal_zero_less]) 1);
qed "real_minus_minus_zero_less";

(* another lemma *)
Goalw [real_zero_def]
      "0 < real_of_preal m + real_of_preal m1";
by (auto_tac (claset(),
	      simpset() addsimps [real_of_preal_def,
				  real_less_def,real_add]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (full_simp_tac (simpset() addsimps preal_add_ac) 1);
by (full_simp_tac (simpset() addsimps [preal_self_less_add_right,
    preal_add_assoc RS sym]) 1);
qed "real_of_preal_sum_zero_less";

Goal "- real_of_preal m < real_of_preal m1";
by (auto_tac (claset(),
	      simpset() addsimps [real_of_preal_def,
              real_less_def,real_minus]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (full_simp_tac (simpset() addsimps preal_add_ac) 1);
by (full_simp_tac (simpset() addsimps [preal_self_less_add_right,
    preal_add_assoc RS sym]) 1);
qed "real_of_preal_minus_less_all";

Goal "~ real_of_preal m < - real_of_preal m1";
by (cut_facts_tac [real_of_preal_minus_less_all] 1);
by (blast_tac (claset() addDs [real_less_trans] 
               addEs [real_less_irrefl]) 1);
qed "real_of_preal_not_minus_gt_all";

Goal "- real_of_preal m1 < - real_of_preal m2 \
\     ==> real_of_preal m2 < real_of_preal m1";
by (auto_tac (claset(),
	      simpset() addsimps [real_of_preal_def,
              real_less_def,real_minus]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (auto_tac (claset(),simpset() addsimps preal_add_ac));
by (asm_full_simp_tac (simpset() addsimps [preal_add_assoc RS sym]) 1);
by (auto_tac (claset(),simpset() addsimps preal_add_ac));
qed "real_of_preal_minus_less_rev1";

Goal "real_of_preal m1 < real_of_preal m2 \
\     ==> - real_of_preal m2 < - real_of_preal m1";
by (auto_tac (claset(),
	      simpset() addsimps [real_of_preal_def,
              real_less_def,real_minus]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (auto_tac (claset(),simpset() addsimps preal_add_ac));
by (asm_full_simp_tac (simpset() addsimps [preal_add_assoc RS sym]) 1);
by (auto_tac (claset(),simpset() addsimps preal_add_ac));
qed "real_of_preal_minus_less_rev2";

Goal "(- real_of_preal m1 < - real_of_preal m2) = \
\     (real_of_preal m2 < real_of_preal m1)";
by (blast_tac (claset() addSIs [real_of_preal_minus_less_rev1,
               real_of_preal_minus_less_rev2]) 1);
qed "real_of_preal_minus_less_rev_iff";

Addsimps [real_of_preal_minus_less_rev_iff];

(*** linearity ***)
Goal "(R1::real) < R2 | R1 = R2 | R2 < R1";
by (res_inst_tac [("x","R1")]  real_of_preal_trichotomyE 1);
by (ALLGOALS(res_inst_tac [("x","R2")]  real_of_preal_trichotomyE));
by (auto_tac (claset() addSDs [preal_le_anti_sym],
              simpset() addsimps [preal_less_le_iff,real_of_preal_minus_less_zero,
               real_of_preal_zero_less,real_of_preal_minus_less_all]));
qed "real_linear";

Goal "!!w::real. (w ~= z) = (w<z | z<w)";
by (cut_facts_tac [real_linear] 1);
by (Blast_tac 1);
qed "real_neq_iff";

Goal "!!(R1::real). [| R1 < R2 ==> P;  R1 = R2 ==> P; \
\                      R2 < R1 ==> P |] ==> P";
by (cut_inst_tac [("R1.0","R1"),("R2.0","R2")] real_linear 1);
by Auto_tac;
qed "real_linear_less2";

(*** Properties of <= ***)

Goalw [real_le_def] "~(w < z) ==> z <= (w::real)";
by (assume_tac 1);
qed "real_leI";

Goalw [real_le_def] "z<=w ==> ~(w<(z::real))";
by (assume_tac 1);
qed "real_leD";

bind_thm ("real_leE", make_elim real_leD);

Goal "(~(w < z)) = (z <= (w::real))";
by (blast_tac (claset() addSIs [real_leI,real_leD]) 1);
qed "real_less_le_iff";

Goalw [real_le_def] "~ z <= w ==> w<(z::real)";
by (Blast_tac 1);
qed "not_real_leE";

Goalw [real_le_def] "!!(x::real). x <= y ==> x < y | x = y";
by (cut_facts_tac [real_linear] 1);
by (blast_tac (claset() addEs [real_less_irrefl,real_less_asym]) 1);
qed "real_le_imp_less_or_eq";

Goalw [real_le_def] "z<w | z=w ==> z <=(w::real)";
by (cut_facts_tac [real_linear] 1);
by (fast_tac (claset() addEs [real_less_irrefl,real_less_asym]) 1);
qed "real_less_or_eq_imp_le";

Goal "(x <= (y::real)) = (x < y | x=y)";
by (REPEAT(ares_tac [iffI, real_less_or_eq_imp_le, real_le_imp_less_or_eq] 1));
qed "real_le_less";

Goal "w <= (w::real)";
by (simp_tac (simpset() addsimps [real_le_less]) 1);
qed "real_le_refl";

(* Axiom 'linorder_linear' of class 'linorder': *)
Goal "(z::real) <= w | w <= z";
by (simp_tac (simpset() addsimps [real_le_less]) 1);
by (cut_facts_tac [real_linear] 1);
by (Blast_tac 1);
qed "real_le_linear";

Goal "[| i <= j; j <= k |] ==> i <= (k::real)";
by (EVERY1 [dtac real_le_imp_less_or_eq, dtac real_le_imp_less_or_eq,
            rtac real_less_or_eq_imp_le, 
            blast_tac (claset() addIs [real_less_trans])]);
qed "real_le_trans";

Goal "[| z <= w; w <= z |] ==> z = (w::real)";
by (EVERY1 [dtac real_le_imp_less_or_eq, dtac real_le_imp_less_or_eq,
            fast_tac (claset() addEs [real_less_irrefl,real_less_asym])]);
qed "real_le_anti_sym";

Goal "[| ~ y < x; y ~= x |] ==> x < (y::real)";
by (rtac not_real_leE 1);
by (blast_tac (claset() addDs [real_le_imp_less_or_eq]) 1);
qed "not_less_not_eq_real_less";

(* Axiom 'order_less_le' of class 'order': *)
Goal "((w::real) < z) = (w <= z & w ~= z)";
by (simp_tac (simpset() addsimps [real_le_def, real_neq_iff]) 1);
by (blast_tac (claset() addSEs [real_less_asym]) 1);
qed "real_less_le";

Goal "(0 < -R) = (R < (0::real))";
by (res_inst_tac [("x","R")]  real_of_preal_trichotomyE 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_of_preal_not_minus_gt_zero,
                        real_of_preal_not_less_zero,real_of_preal_zero_less,
                        real_of_preal_minus_less_zero]));
qed "real_minus_zero_less_iff";
Addsimps [real_minus_zero_less_iff];

Goal "(-R < 0) = ((0::real) < R)";
by (res_inst_tac [("x","R")]  real_of_preal_trichotomyE 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_of_preal_not_minus_gt_zero,
                        real_of_preal_not_less_zero,real_of_preal_zero_less,
                        real_of_preal_minus_less_zero]));
qed "real_minus_zero_less_iff2";
Addsimps [real_minus_zero_less_iff2];

(*Alternative definition for real_less*)
Goal "R < S ==> EX T::real. 0 < T & R + T = S";
by (res_inst_tac [("x","R")]  real_of_preal_trichotomyE 1);
by (ALLGOALS(res_inst_tac [("x","S")]  real_of_preal_trichotomyE));
by (auto_tac (claset() addSDs [preal_less_add_left_Ex],
	      simpset() addsimps [real_of_preal_not_minus_gt_all,
				  real_of_preal_add, real_of_preal_not_less_zero,
				  real_less_not_refl,
				  real_of_preal_not_minus_gt_zero]));
by (res_inst_tac [("x","real_of_preal D")] exI 1);
by (res_inst_tac [("x","real_of_preal m+real_of_preal ma")] exI 2);
by (res_inst_tac [("x","real_of_preal D")] exI 3);
by (auto_tac (claset(),
	      simpset() addsimps [real_of_preal_zero_less,
				  real_of_preal_sum_zero_less,real_add_assoc]));
qed "real_less_add_positive_left_Ex";

(** change naff name(s)! **)
Goal "(W < S) ==> (0 < S + (-W::real))";
by (dtac real_less_add_positive_left_Ex 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_add_minus,
    real_add_zero_right] @ real_add_ac));
qed "real_less_sum_gt_zero";

Goal "!!S::real. T = S + W ==> S = T + (-W)";
by (asm_simp_tac (simpset() addsimps real_add_ac) 1);
qed "real_lemma_change_eq_subj";

(* FIXME: long! *)
Goal "(0 < S + (-W::real)) ==> (W < S)";
by (rtac ccontr 1);
by (dtac (real_leI RS real_le_imp_less_or_eq) 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_less_not_refl]));
by (EVERY1[dtac real_less_add_positive_left_Ex, etac exE, etac conjE]);
by (Asm_full_simp_tac 1);
by (dtac real_lemma_change_eq_subj 1);
by Auto_tac;
by (dtac real_less_sum_gt_zero 1);
by (asm_full_simp_tac (simpset() addsimps real_add_ac) 1);
by (EVERY1[rotate_tac 1, dtac (real_add_left_commute RS ssubst)]);
by (auto_tac (claset() addEs [real_less_asym], simpset()));
qed "real_sum_gt_zero_less";

Goal "(0 < S + (-W::real)) = (W < S)";
by (blast_tac (claset() addIs [real_less_sum_gt_zero,
			       real_sum_gt_zero_less]) 1);
qed "real_less_sum_gt_0_iff";


Goalw [real_diff_def] "(x<y) = (x-y < (0::real))";
by (stac (real_minus_zero_less_iff RS sym) 1);
by (simp_tac (simpset() addsimps [real_add_commute,
				  real_less_sum_gt_0_iff]) 1);
qed "real_less_eq_diff";


(*** Subtraction laws ***)

Goal "x + (y - z) = (x + y) - (z::real)";
by (simp_tac (simpset() addsimps real_diff_def::real_add_ac) 1);
qed "real_add_diff_eq";

Goal "(x - y) + z = (x + z) - (y::real)";
by (simp_tac (simpset() addsimps real_diff_def::real_add_ac) 1);
qed "real_diff_add_eq";

Goal "(x - y) - z = x - (y + (z::real))";
by (simp_tac (simpset() addsimps real_diff_def::real_add_ac) 1);
qed "real_diff_diff_eq";

Goal "x - (y - z) = (x + z) - (y::real)";
by (simp_tac (simpset() addsimps real_diff_def::real_add_ac) 1);
qed "real_diff_diff_eq2";

Goal "(x-y < z) = (x < z + (y::real))";
by (stac real_less_eq_diff 1);
by (res_inst_tac [("y1", "z")] (real_less_eq_diff RS ssubst) 1);
by (simp_tac (simpset() addsimps real_diff_def::real_add_ac) 1);
qed "real_diff_less_eq";

Goal "(x < z-y) = (x + (y::real) < z)";
by (stac real_less_eq_diff 1);
by (res_inst_tac [("y1", "z-y")] (real_less_eq_diff RS ssubst) 1);
by (simp_tac (simpset() addsimps real_diff_def::real_add_ac) 1);
qed "real_less_diff_eq";

Goalw [real_le_def] "(x-y <= z) = (x <= z + (y::real))";
by (simp_tac (simpset() addsimps [real_less_diff_eq]) 1);
qed "real_diff_le_eq";

Goalw [real_le_def] "(x <= z-y) = (x + (y::real) <= z)";
by (simp_tac (simpset() addsimps [real_diff_less_eq]) 1);
qed "real_le_diff_eq";

Goalw [real_diff_def] "(x-y = z) = (x = z + (y::real))";
by (auto_tac (claset(), simpset() addsimps [real_add_assoc]));
qed "real_diff_eq_eq";

Goalw [real_diff_def] "(x = z-y) = (x + (y::real) = z)";
by (auto_tac (claset(), simpset() addsimps [real_add_assoc]));
qed "real_eq_diff_eq";

(*This list of rewrites simplifies (in)equalities by bringing subtractions
  to the top and then moving negative terms to the other side.  
  Use with real_add_ac*)
bind_thms ("real_compare_rls",
  [symmetric real_diff_def,
   real_add_diff_eq, real_diff_add_eq, real_diff_diff_eq, real_diff_diff_eq2, 
   real_diff_less_eq, real_less_diff_eq, real_diff_le_eq, real_le_diff_eq, 
   real_diff_eq_eq, real_eq_diff_eq]);


(** For the cancellation simproc.
    The idea is to cancel like terms on opposite sides by subtraction **)

Goal "(x::real) - y = x' - y' ==> (x<y) = (x'<y')";
by (stac real_less_eq_diff 1);
by (res_inst_tac [("y1", "y")] (real_less_eq_diff RS ssubst) 1);
by (Asm_simp_tac 1);
qed "real_less_eqI";

Goal "(x::real) - y = x' - y' ==> (y<=x) = (y'<=x')";
by (dtac real_less_eqI 1);
by (asm_simp_tac (simpset() addsimps [real_le_def]) 1);
qed "real_le_eqI";

Goal "(x::real) - y = x' - y' ==> (x=y) = (x'=y')";
by Safe_tac;
by (ALLGOALS
    (asm_full_simp_tac
     (simpset() addsimps [real_eq_diff_eq, real_diff_eq_eq])));
qed "real_eq_eqI";
