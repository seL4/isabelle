(*  Title       : Real/RealDef.ML
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The reals
*)

(*** Proving that realrel is an equivalence relation ***)

Goal "[| (x1::preal) + y2 = x2 + y1; x2 + y3 = x3 + y2 |] \
\            ==> x1 + y3 = x3 + y1";        
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

val [major,minor] = goal thy
  "[| p: realrel;  \
\     !!x1 y1 x2 y2. [| p = ((x1,y1),(x2,y2));  x1+y2 = x2+y1 \
\                    |] ==> Q |] ==> Q";
by (cut_facts_tac [major RS (realrelE_lemma RS mp)] 1);
by (REPEAT (eresolve_tac [asm_rl,exE,conjE,minor] 1));
qed "realrelE";

AddSIs [realrelI];
AddSEs [realrelE];

Goal "(x,x): realrel";
by (stac surjective_pairing 1 THEN rtac (refl RS realrelI) 1);
qed "realrel_refl";

Goalw [equiv_def, refl_def, sym_def, trans_def]
    "equiv {x::(preal*preal).True} realrel";
by (fast_tac (claset() addSIs [realrel_refl] 
                      addSEs [sym,preal_trans_lemma]) 1);
qed "equiv_realrel";

val equiv_realrel_iff =
    [TrueI, TrueI] MRS 
    ([CollectI, CollectI] MRS 
    (equiv_realrel RS eq_equiv_class_iff));

Goalw  [real_def,realrel_def,quotient_def] "realrel^^{(x,y)}:real";
by (Blast_tac 1);
qed "realrel_in_real";

Goal "inj_on Abs_real real";
by (rtac inj_on_inverseI 1);
by (etac Abs_real_inverse 1);
qed "inj_on_Abs_real";

Addsimps [equiv_realrel_iff,inj_on_Abs_real RS inj_on_iff,
          realrel_iff, realrel_in_real, Abs_real_inverse];

Addsimps [equiv_realrel RS eq_equiv_class_iff];
val eq_realrelD = equiv_realrel RSN (2,eq_equiv_class);

Goal "inj(Rep_real)";
by (rtac inj_inverseI 1);
by (rtac Rep_real_inverse 1);
qed "inj_Rep_real";

(** real_of_preal: the injection from preal to real **)
Goal "inj(real_of_preal)";
by (rtac injI 1);
by (rewtac real_of_preal_def);
by (dtac (inj_on_Abs_real RS inj_onD) 1);
by (REPEAT (rtac realrel_in_real 1));
by (dtac eq_equiv_class 1);
by (rtac equiv_realrel 1);
by (Blast_tac 1);
by Safe_tac;
by (Asm_full_simp_tac 1);
qed "inj_real_of_preal";

val [prem] = goal thy
    "(!!x y. z = Abs_real(realrel^^{(x,y)}) ==> P) ==> P";
by (res_inst_tac [("x1","z")] 
    (rewrite_rule [real_def] Rep_real RS quotientE) 1);
by (dres_inst_tac [("f","Abs_real")] arg_cong 1);
by (res_inst_tac [("p","x")] PairE 1);
by (rtac prem 1);
by (asm_full_simp_tac (simpset() addsimps [Rep_real_inverse]) 1);
qed "eq_Abs_real";

(**** real_minus: additive inverse on real ****)

Goalw [congruent_def]
  "congruent realrel (%p. split (%x y. realrel^^{(y,x)}) p)";
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [preal_add_commute]) 1);
qed "real_minus_congruent";

(*Resolve th against the corresponding facts for real_minus*)
val real_minus_ize = RSLIST [equiv_realrel, real_minus_congruent];

Goalw [real_minus_def]
      "- (Abs_real(realrel^^{(x,y)})) = Abs_real(realrel ^^ {(y,x)})";
by (res_inst_tac [("f","Abs_real")] arg_cong 1);
by (simp_tac (simpset() addsimps 
   [realrel_in_real RS Abs_real_inverse,real_minus_ize UN_equiv_class]) 1);
qed "real_minus";

Goal "- (- z) = (z::real)";
by (res_inst_tac [("z","z")] eq_Abs_real 1);
by (asm_simp_tac (simpset() addsimps [real_minus]) 1);
qed "real_minus_minus";

Addsimps [real_minus_minus];

Goal "inj(%r::real. -r)";
by (rtac injI 1);
by (dres_inst_tac [("f","uminus")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [real_minus_minus]) 1);
qed "inj_real_minus";

Goalw [real_zero_def] "-0r = 0r";
by (simp_tac (simpset() addsimps [real_minus]) 1);
qed "real_minus_zero";

Addsimps [real_minus_zero];

Goal "(-x = 0r) = (x = 0r)"; 
by (res_inst_tac [("z","x")] eq_Abs_real 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_zero_def, real_minus] @ preal_add_ac));
qed "real_minus_zero_iff";

Addsimps [real_minus_zero_iff];

Goal "(-x ~= 0r) = (x ~= 0r)"; 
by Auto_tac;
qed "real_minus_not_zero_iff";

(*** Congruence property for addition ***)
Goalw [congruent2_def]
    "congruent2 realrel (%p1 p2.                  \
\         split (%x1 y1. split (%x2 y2. realrel^^{(x1+x2, y1+y2)}) p2) p1)";
by Safe_tac;
by (asm_simp_tac (simpset() addsimps [preal_add_assoc]) 1);
by (res_inst_tac [("z1.1","x1a")] (preal_add_left_commute RS ssubst) 1);
by (asm_simp_tac (simpset() addsimps [preal_add_assoc RS sym]) 1);
by (asm_simp_tac (simpset() addsimps preal_add_ac) 1);
qed "real_add_congruent2";

(*Resolve th against the corresponding facts for real_add*)
val real_add_ize = RSLIST [equiv_realrel, real_add_congruent2];

Goalw [real_add_def]
  "Abs_real(realrel^^{(x1,y1)}) + Abs_real(realrel^^{(x2,y2)}) = \
\  Abs_real(realrel^^{(x1+x2, y1+y2)})";
by (asm_simp_tac (simpset() addsimps [real_add_ize UN_equiv_class2]) 1);
qed "real_add";

Goal "(z::real) + w = w + z";
by (res_inst_tac [("z","z")] eq_Abs_real 1);
by (res_inst_tac [("z","w")] eq_Abs_real 1);
by (asm_simp_tac (simpset() addsimps preal_add_ac @ [real_add]) 1);
qed "real_add_commute";

Goal "((z1::real) + z2) + z3 = z1 + (z2 + z3)";
by (res_inst_tac [("z","z1")] eq_Abs_real 1);
by (res_inst_tac [("z","z2")] eq_Abs_real 1);
by (res_inst_tac [("z","z3")] eq_Abs_real 1);
by (asm_simp_tac (simpset() addsimps [real_add, preal_add_assoc]) 1);
qed "real_add_assoc";

(*For AC rewriting*)
Goal "(x::real)+(y+z)=y+(x+z)";
by (rtac (real_add_commute RS trans) 1);
by (rtac (real_add_assoc RS trans) 1);
by (rtac (real_add_commute RS arg_cong) 1);
qed "real_add_left_commute";

(* real addition is an AC operator *)
val real_add_ac = [real_add_assoc,real_add_commute,real_add_left_commute];

Goalw [real_of_preal_def,real_zero_def] "0r + z = z";
by (res_inst_tac [("z","z")] eq_Abs_real 1);
by (asm_full_simp_tac (simpset() addsimps [real_add] @ preal_add_ac) 1);
qed "real_add_zero_left";
Addsimps [real_add_zero_left];

Goal "z + 0r = z";
by (simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "real_add_zero_right";
Addsimps [real_add_zero_right];

Goalw [real_zero_def] "z + (-z) = 0r";
by (res_inst_tac [("z","z")] eq_Abs_real 1);
by (asm_full_simp_tac (simpset() addsimps [real_minus,
        real_add, preal_add_commute]) 1);
qed "real_add_minus";
Addsimps [real_add_minus];

Goal "(-z) + z = 0r";
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

Goal "? y. (x::real) + y = 0r";
by (blast_tac (claset() addIs [real_add_minus]) 1);
qed "real_minus_ex";

Goal "?! y. (x::real) + y = 0r";
by (auto_tac (claset() addIs [real_add_minus],simpset()));
by (dres_inst_tac [("f","%x. ya+x")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_assoc RS sym]) 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "real_minus_ex1";

Goal "?! y. y + (x::real) = 0r";
by (auto_tac (claset() addIs [real_add_minus_left],simpset()));
by (dres_inst_tac [("f","%x. x+ya")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_assoc]) 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "real_minus_left_ex1";

Goal "x + y = 0r ==> x = -y";
by (cut_inst_tac [("z","y")] real_add_minus_left 1);
by (res_inst_tac [("x1","y")] (real_minus_left_ex1 RS ex1E) 1);
by (Blast_tac 1);
qed "real_add_minus_eq_minus";

Goal "? (y::real). x = -y";
by (cut_inst_tac [("x","x")] real_minus_ex 1);
by (etac exE 1 THEN dtac real_add_minus_eq_minus 1);
by (Fast_tac 1);
qed "real_as_add_inverse_ex";

Goal "-(x + y) = (-x) + (- y :: real)";
by (res_inst_tac [("z","x")] eq_Abs_real 1);
by (res_inst_tac [("z","y")] eq_Abs_real 1);
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

Goal "((x::real) = y) = (0r = x + (- y))";
by (Step_tac 1);
by (res_inst_tac [("x1","-y")] 
      (real_add_right_cancel RS iffD1) 2);
by Auto_tac;
qed "real_eq_minus_iff"; 

Goal "((x::real) = y) = (x + (- y) = 0r)";
by (Step_tac 1);
by (res_inst_tac [("x1","-y")] 
      (real_add_right_cancel RS iffD1) 2);
by Auto_tac;
qed "real_eq_minus_iff2"; 

Goal "0r - x = -x";
by (simp_tac (simpset() addsimps [real_diff_def]) 1);
qed "real_diff_0";

Goal "x - 0r = x";
by (simp_tac (simpset() addsimps [real_diff_def]) 1);
qed "real_diff_0_right";

Goal "x - x = 0r";
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
\         split (%x1 y1. split (%x2 y2. realrel^^{(x1*x2 + y1*y2, x1*y2+x2*y1)}) p2) p1)";
by (rtac (equiv_realrel RS congruent2_commuteI) 1);
by Safe_tac;
by (rewtac split_def);
by (asm_simp_tac (simpset() addsimps [preal_mult_commute,preal_add_commute]) 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_congruent2_lemma]));
qed "real_mult_congruent2";

(*Resolve th against the corresponding facts for real_mult*)
val real_mult_ize = RSLIST [equiv_realrel, real_mult_congruent2];

Goalw [real_mult_def]
   "Abs_real((realrel^^{(x1,y1)})) * Abs_real((realrel^^{(x2,y2)})) =   \
\   Abs_real(realrel ^^ {(x1*x2+y1*y2,x1*y2+x2*y1)})";
by (simp_tac (simpset() addsimps [real_mult_ize UN_equiv_class2]) 1);
qed "real_mult";

Goal "(z::real) * w = w * z";
by (res_inst_tac [("z","z")] eq_Abs_real 1);
by (res_inst_tac [("z","w")] eq_Abs_real 1);
by (asm_simp_tac
    (simpset() addsimps [real_mult] @ preal_add_ac @ preal_mult_ac) 1);
qed "real_mult_commute";

Goal "((z1::real) * z2) * z3 = z1 * (z2 * z3)";
by (res_inst_tac [("z","z1")] eq_Abs_real 1);
by (res_inst_tac [("z","z2")] eq_Abs_real 1);
by (res_inst_tac [("z","z3")] eq_Abs_real 1);
by (asm_simp_tac (simpset() addsimps [preal_add_mult_distrib2,real_mult] @ 
                                     preal_add_ac @ preal_mult_ac) 1);
qed "real_mult_assoc";

qed_goal "real_mult_left_commute" thy
    "(z1::real) * (z2 * z3) = z2 * (z1 * z3)"
 (fn _ => [rtac (real_mult_commute RS trans) 1, rtac (real_mult_assoc RS trans) 1,
           rtac (real_mult_commute RS arg_cong) 1]);

(* real multiplication is an AC operator *)
val real_mult_ac = [real_mult_assoc, real_mult_commute, real_mult_left_commute];

Goalw [real_one_def,pnat_one_def] "1r * z = z";
by (res_inst_tac [("z","z")] eq_Abs_real 1);
by (asm_full_simp_tac
    (simpset() addsimps [real_mult,
			 preal_add_mult_distrib2,preal_mult_1_right] 
                        @ preal_mult_ac @ preal_add_ac) 1);
qed "real_mult_1";

Addsimps [real_mult_1];

Goal "z * 1r = z";
by (simp_tac (simpset() addsimps [real_mult_commute]) 1);
qed "real_mult_1_right";

Addsimps [real_mult_1_right];

Goalw [real_zero_def,pnat_one_def] "0r * z = 0r";
by (res_inst_tac [("z","z")] eq_Abs_real 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult,
    preal_add_mult_distrib2,preal_mult_1_right] 
    @ preal_mult_ac @ preal_add_ac) 1);
qed "real_mult_0";

Goal "z * 0r = 0r";
by (simp_tac (simpset() addsimps [real_mult_commute, real_mult_0]) 1);
qed "real_mult_0_right";

Addsimps [real_mult_0_right, real_mult_0];

Goal "-(x * y) = (-x) * (y::real)";
by (res_inst_tac [("z","x")] eq_Abs_real 1);
by (res_inst_tac [("z","y")] eq_Abs_real 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_minus,real_mult] 
    @ preal_mult_ac @ preal_add_ac));
qed "real_minus_mult_eq1";

Goal "-(x * y) = x * (- y :: real)";
by (res_inst_tac [("z","x")] eq_Abs_real 1);
by (res_inst_tac [("z","y")] eq_Abs_real 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_minus,real_mult] 
    @ preal_mult_ac @ preal_add_ac));
qed "real_minus_mult_eq2";

Goal "(- 1r) * z = -z";
by (simp_tac (simpset() addsimps [real_minus_mult_eq1 RS sym]) 1);
qed "real_mult_minus_1";

Addsimps [real_mult_minus_1];

Goal "z * (- 1r) = -z";
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

(*-----------------------------------------------------------------------------

 ----------------------------------------------------------------------------*)

(** Lemmas **)

qed_goal "real_add_assoc_cong" thy
    "!!z. (z::real) + v = z' + v' ==> z + (v + w) = z' + (v' + w)"
 (fn _ => [(asm_simp_tac (simpset() addsimps [real_add_assoc RS sym]) 1)]);

qed_goal "real_add_assoc_swap" thy "(z::real) + (v + w) = v + (z + w)"
 (fn _ => [(REPEAT (ares_tac [real_add_commute RS real_add_assoc_cong] 1))]);

Goal "((z1::real) + z2) * w = (z1 * w) + (z2 * w)";
by (res_inst_tac [("z","z1")] eq_Abs_real 1);
by (res_inst_tac [("z","z2")] eq_Abs_real 1);
by (res_inst_tac [("z","w")] eq_Abs_real 1);
by (asm_simp_tac 
    (simpset() addsimps [preal_add_mult_distrib2, real_add, real_mult] @ 
                        preal_add_ac @ preal_mult_ac) 1);
qed "real_add_mult_distrib";

val real_mult_commute'= read_instantiate [("z","w")] real_mult_commute;

Goal "(w::real) * (z1 + z2) = (w * z1) + (w * z2)";
by (simp_tac (simpset() addsimps [real_mult_commute',real_add_mult_distrib]) 1);
qed "real_add_mult_distrib2";

(*** one and zero are distinct ***)
Goalw [real_zero_def,real_one_def] "0r ~= 1r";
by (auto_tac (claset(),
         simpset() addsimps [preal_self_less_add_left RS preal_not_refl2]));
qed "real_zero_not_eq_one";

(*** existence of inverse ***)
(** lemma -- alternative definition for 0r **)
Goalw [real_zero_def] "0r = Abs_real (realrel ^^ {(x, x)})";
by (auto_tac (claset(),simpset() addsimps [preal_add_commute]));
qed "real_zero_iff";

Goalw [real_zero_def,real_one_def] 
          "!!(x::real). x ~= 0r ==> ? y. x*y = 1r";
by (res_inst_tac [("z","x")] eq_Abs_real 1);
by (cut_inst_tac [("r1.0","xa"),("r2.0","y")] preal_linear 1);
by (auto_tac (claset() addSDs [preal_less_add_left_Ex],
           simpset() addsimps [real_zero_iff RS sym]));
by (res_inst_tac [("x","Abs_real (realrel ^^ \
\   {(preal_of_prat(prat_of_pnat 1p),pinv(D)+\
\    preal_of_prat(prat_of_pnat 1p))})")] exI 1);
by (res_inst_tac [("x","Abs_real (realrel ^^ \
\   {(pinv(D)+preal_of_prat(prat_of_pnat 1p),\
\    preal_of_prat(prat_of_pnat 1p))})")] exI 2);
by (auto_tac (claset(),
	      simpset() addsimps [real_mult,
    pnat_one_def,preal_mult_1_right,preal_add_mult_distrib2,
    preal_add_mult_distrib,preal_mult_1,preal_mult_inv_right] 
    @ preal_add_ac @ preal_mult_ac));
qed "real_mult_inv_right_ex";

Goal "!!(x::real). x ~= 0r ==> ? y. y*x = 1r";
by (asm_simp_tac (simpset() addsimps [real_mult_commute,
				      real_mult_inv_right_ex]) 1);
qed "real_mult_inv_left_ex";

Goalw [rinv_def] "x ~= 0r ==> rinv(x)*x = 1r";
by (forward_tac [real_mult_inv_left_ex] 1);
by (Step_tac 1);
by (rtac selectI2 1);
by Auto_tac;
qed "real_mult_inv_left";

Goal "x ~= 0r ==> x*rinv(x) = 1r";
by (auto_tac (claset() addIs [real_mult_commute RS subst],
              simpset() addsimps [real_mult_inv_left]));
qed "real_mult_inv_right";

Goal "(c::real) ~= 0r ==> (c*a=c*b) = (a=b)";
by Auto_tac;
by (dres_inst_tac [("f","%x. x*rinv c")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult_inv_right] @ real_mult_ac)  1);
qed "real_mult_left_cancel";
    
Goal "(c::real) ~= 0r ==> (a*c=b*c) = (a=b)";
by (Step_tac 1);
by (dres_inst_tac [("f","%x. x*rinv c")] arg_cong 1);
by (asm_full_simp_tac
    (simpset() addsimps [real_mult_inv_right] @ real_mult_ac)  1);
qed "real_mult_right_cancel";

Goal "c*a ~= c*b ==> a ~= b";
by Auto_tac;
qed "real_mult_left_cancel_ccontr";

Goal "a*c ~= b*c ==> a ~= b";
by Auto_tac;
qed "real_mult_right_cancel_ccontr";

Goalw [rinv_def] "x ~= 0r ==> rinv(x) ~= 0r";
by (forward_tac [real_mult_inv_left_ex] 1);
by (etac exE 1);
by (rtac selectI2 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_mult_0,
    real_zero_not_eq_one]));
qed "rinv_not_zero";

Addsimps [real_mult_inv_left,real_mult_inv_right];

Goal "[| x ~= 0r; y ~= 0r |] ==> x * y ~= 0r";
by (Step_tac 1);
by (dres_inst_tac [("f","%z. rinv x*z")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult_assoc RS sym]) 1);
qed "real_mult_not_zero";

bind_thm ("real_mult_not_zeroE",real_mult_not_zero RS notE);

Goal "x ~= 0r ==> rinv(rinv x) = x";
by (res_inst_tac [("c1","rinv x")] (real_mult_right_cancel RS iffD1) 1);
by (etac rinv_not_zero 1);
by (auto_tac (claset() addDs [rinv_not_zero],simpset()));
qed "real_rinv_rinv";

Goalw [rinv_def] "rinv(1r) = 1r";
by (cut_facts_tac [real_zero_not_eq_one RS 
       not_sym RS real_mult_inv_left_ex] 1);
by (etac exE 1);
by (rtac selectI2 1);
by (auto_tac (claset(),
	      simpset() addsimps 
    [real_zero_not_eq_one RS not_sym]));
qed "real_rinv_1";
Addsimps [real_rinv_1];

Goal "x ~= 0r ==> rinv(-x) = -rinv(x)";
by (res_inst_tac [("c1","-x")] (real_mult_right_cancel RS iffD1) 1);
by Auto_tac;
qed "real_minus_rinv";

Goal "[| x ~= 0r; y ~= 0r |] ==> rinv(x*y) = rinv(x)*rinv(y)";
by (forw_inst_tac [("y","y")] real_mult_not_zero 1 THEN assume_tac 1);
by (res_inst_tac [("c1","x")] (real_mult_left_cancel RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc RS sym]));
by (res_inst_tac [("c1","y")] (real_mult_left_cancel RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_left_commute]));
by (asm_simp_tac (simpset() addsimps [real_mult_assoc RS sym]) 1);
qed "real_rinv_distrib";

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
by (res_inst_tac [("z","R")] eq_Abs_real 1);
by (auto_tac (claset(),simpset() addsimps [real_less_def]));
by (dtac preal_lemma_for_not_refl 1);
by (assume_tac 1 THEN rotate_tac 2 1);
by (auto_tac (claset(),simpset() addsimps [preal_less_not_refl]));
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
by (res_inst_tac [("z","R1")] eq_Abs_real 1);
by (res_inst_tac [("z","R2")] eq_Abs_real 1);
by (res_inst_tac [("z","R3")] eq_Abs_real 1);
by (auto_tac (claset(),simpset() addsimps [real_less_def]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (dtac preal_lemma_for_not_refl 1 THEN assume_tac 1);
by (blast_tac (claset() addDs [preal_add_less_mono] 
    addIs [preal_lemma_trans]) 1);
qed "real_less_trans";

Goal "!! (R1::real). [| R1 < R2; R2 < R1 |] ==> P";
by (dtac real_less_trans 1 THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [real_less_not_refl]) 1);
qed "real_less_asym";

(****)(****)(****)(****)(****)(****)(****)(****)(****)(****)
    (****** Map and more real_less ******)
(*** mapping from preal into real ***)
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
\      ? m. Abs_real (realrel ^^ {(x,y)}) = real_of_preal m";
by (auto_tac (claset() addSDs [preal_less_add_left_Ex],
    simpset() addsimps preal_add_ac));
qed "real_of_preal_ExI";

Goalw [real_of_preal_def]
      "!!(x::preal). ? m. Abs_real (realrel ^^ {(x,y)}) = \
\                    real_of_preal m ==> y < x";
by (auto_tac (claset(),
	      simpset() addsimps 
    [preal_add_commute,preal_add_assoc]));
by (asm_full_simp_tac (simpset() addsimps 
    [preal_add_assoc RS sym,preal_self_less_add_left]) 1);
qed "real_of_preal_ExD";

Goal "(? m. Abs_real (realrel ^^ {(x,y)}) = real_of_preal m) = (y < x)";
by (blast_tac (claset() addSIs [real_of_preal_ExI,real_of_preal_ExD]) 1);
qed "real_of_preal_iff";

(*** Gleason prop 9-4.4 p 127 ***)
Goalw [real_of_preal_def,real_zero_def] 
      "? m. (x::real) = real_of_preal m | x = 0r | x = -(real_of_preal m)";
by (res_inst_tac [("z","x")] eq_Abs_real 1);
by (auto_tac (claset(),simpset() addsimps [real_minus] @ preal_add_ac));
by (cut_inst_tac [("r1.0","x"),("r2.0","y")] preal_linear 1);
by (auto_tac (claset() addSDs [preal_less_add_left_Ex],
    simpset() addsimps [preal_add_assoc RS sym]));
by (auto_tac (claset(),simpset() addsimps [preal_add_commute]));
qed "real_of_preal_trichotomy";

Goal "!!P. [| !!m. x = real_of_preal m ==> P; \
\             x = 0r ==> P; \
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

Goalw [real_zero_def] "- real_of_preal m < 0r";
by (auto_tac (claset(),
	      simpset() addsimps [real_of_preal_def,
				  real_less_def,real_minus]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (full_simp_tac (simpset() addsimps 
  [preal_self_less_add_right] @ preal_add_ac) 1);
qed "real_of_preal_minus_less_zero";

Goal "~ 0r < - real_of_preal m";
by (cut_facts_tac [real_of_preal_minus_less_zero] 1);
by (fast_tac (claset() addDs [real_less_trans] 
                        addEs [real_less_irrefl]) 1);
qed "real_of_preal_not_minus_gt_zero";

Goalw [real_zero_def] "0r < real_of_preal m";
by (auto_tac (claset(),simpset() addsimps 
   [real_of_preal_def,real_less_def,real_minus]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (full_simp_tac (simpset() addsimps 
		   [preal_self_less_add_right] @ preal_add_ac) 1);
qed "real_of_preal_zero_less";

Goal "~ real_of_preal m < 0r";
by (cut_facts_tac [real_of_preal_zero_less] 1);
by (blast_tac (claset() addDs [real_less_trans] 
                        addEs [real_less_irrefl]) 1);
qed "real_of_preal_not_less_zero";

Goal "0r < - (- real_of_preal m)";
by (simp_tac (simpset() addsimps 
    [real_of_preal_zero_less]) 1);
qed "real_minus_minus_zero_less";

(* another lemma *)
Goalw [real_zero_def]
      "0r < real_of_preal m + real_of_preal m1";
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

val real_leE = make_elim real_leD;

Goal "(~(w < z)) = (z <= (w::real))";
by (blast_tac (claset() addSIs [real_leI,real_leD]) 1);
qed "real_less_le_iff";

Goalw [real_le_def] "~ z <= w ==> w<(z::real)";
by (Blast_tac 1);
qed "not_real_leE";

Goalw [real_le_def] "z < w ==> z <= (w::real)";
by (blast_tac (claset() addEs [real_less_asym]) 1);
qed "real_less_imp_le";

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

AddIffs [real_le_refl];

(* Axiom 'linorder_linear' of class 'linorder': *)
Goal "(z::real) <= w | w <= z";
by (simp_tac (simpset() addsimps [real_le_less]) 1);
by (cut_facts_tac [real_linear] 1);
by (Blast_tac 1);
qed "real_le_linear";

Goal "[| i <= j; j < k |] ==> i < (k::real)";
by (dtac real_le_imp_less_or_eq 1);
by (blast_tac (claset() addIs [real_less_trans]) 1);
qed "real_le_less_trans";

Goal "!! (i::real). [| i < j; j <= k |] ==> i < k";
by (dtac real_le_imp_less_or_eq 1);
by (blast_tac (claset() addIs [real_less_trans]) 1);
qed "real_less_le_trans";

Goal "[| i <= j; j <= k |] ==> i <= (k::real)";
by (EVERY1 [dtac real_le_imp_less_or_eq, dtac real_le_imp_less_or_eq,
            rtac real_less_or_eq_imp_le, blast_tac (claset() addIs [real_less_trans])]);
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
Goal "(w::real) < z = (w <= z & w ~= z)";
by (simp_tac (simpset() addsimps [real_le_def, real_neq_iff]) 1);
by (blast_tac (claset() addSEs [real_less_asym]) 1);
qed "real_less_le";

Goal "(0r < -R) = (R < 0r)";
by (res_inst_tac [("x","R")]  real_of_preal_trichotomyE 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_of_preal_not_minus_gt_zero,
                        real_of_preal_not_less_zero,real_of_preal_zero_less,
                        real_of_preal_minus_less_zero]));
qed "real_minus_zero_less_iff";

Addsimps [real_minus_zero_less_iff];

Goal "(-R < 0r) = (0r < R)";
by (res_inst_tac [("x","R")]  real_of_preal_trichotomyE 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_of_preal_not_minus_gt_zero,
                        real_of_preal_not_less_zero,real_of_preal_zero_less,
                        real_of_preal_minus_less_zero]));
qed "real_minus_zero_less_iff2";

(*Alternative definition for real_less*)
Goal "R < S ==> ? T. 0r < T & R + T = S";
by (res_inst_tac [("x","R")]  real_of_preal_trichotomyE 1);
by (ALLGOALS(res_inst_tac [("x","S")]  real_of_preal_trichotomyE));
by (auto_tac (claset() addSDs [preal_less_add_left_Ex],
	      simpset() addsimps [real_of_preal_not_minus_gt_all,
				  real_of_preal_add, real_of_preal_not_less_zero,
				  real_less_not_refl,
				  real_of_preal_not_minus_gt_zero]));
by (res_inst_tac [("x","real_of_preal D")] exI 1);
by (res_inst_tac [("x","real_of_preal m+real_of_preal ma")] exI 2);
by (res_inst_tac [("x","real_of_preal m")] exI 3);
by (res_inst_tac [("x","real_of_preal D")] exI 4);
by (auto_tac (claset(),
	      simpset() addsimps [real_of_preal_zero_less,
				  real_of_preal_sum_zero_less,real_add_assoc]));
qed "real_less_add_positive_left_Ex";

(** change naff name(s)! **)
Goal "(W < S) ==> (0r < S + (-W))";
by (dtac real_less_add_positive_left_Ex 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_add_minus,
    real_add_zero_right] @ real_add_ac));
qed "real_less_sum_gt_zero";

Goal "!!S::real. T = S + W ==> S = T + (-W)";
by (asm_simp_tac (simpset() addsimps real_add_ac) 1);
qed "real_lemma_change_eq_subj";

(* FIXME: long! *)
Goal "(0r < S + (-W)) ==> (W < S)";
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

Goal "(0r < S + (-W)) = (W < S)";
by (blast_tac (claset() addIs [real_less_sum_gt_zero,
			       real_sum_gt_zero_less]) 1);
qed "real_less_sum_gt_0_iff";


Goalw [real_diff_def] "(x<y) = (x-y < 0r)";
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
val real_compare_rls = 
  [symmetric real_diff_def,
   real_add_diff_eq, real_diff_add_eq, real_diff_diff_eq, real_diff_diff_eq2, 
   real_diff_less_eq, real_less_diff_eq, real_diff_le_eq, real_le_diff_eq, 
   real_diff_eq_eq, real_eq_diff_eq];


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
