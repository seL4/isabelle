(*  Title       : Real.ML
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

(** real_preal: the injection from preal to real **)
Goal "inj(real_preal)";
by (rtac injI 1);
by (rewtac real_preal_def);
by (dtac (inj_on_Abs_real RS inj_onD) 1);
by (REPEAT (rtac realrel_in_real 1));
by (dtac eq_equiv_class 1);
by (rtac equiv_realrel 1);
by (Blast_tac 1);
by Safe_tac;
by (Asm_full_simp_tac 1);
qed "inj_real_preal";

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
      "%~ (Abs_real(realrel^^{(x,y)})) = Abs_real(realrel ^^ {(y,x)})";
by (res_inst_tac [("f","Abs_real")] arg_cong 1);
by (simp_tac (simpset() addsimps 
   [realrel_in_real RS Abs_real_inverse,real_minus_ize UN_equiv_class]) 1);
qed "real_minus";

Goal "%~ (%~ z) = z";
by (res_inst_tac [("z","z")] eq_Abs_real 1);
by (asm_simp_tac (simpset() addsimps [real_minus]) 1);
qed "real_minus_minus";

Addsimps [real_minus_minus];

Goal "inj(real_minus)";
by (rtac injI 1);
by (dres_inst_tac [("f","real_minus")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [real_minus_minus]) 1);
qed "inj_real_minus";

Goalw [real_zero_def] "%~0r = 0r";
by (simp_tac (simpset() addsimps [real_minus]) 1);
qed "real_minus_zero";

Addsimps [real_minus_zero];

Goal "(%~x = 0r) = (x = 0r)"; 
by (res_inst_tac [("z","x")] eq_Abs_real 1);
by (auto_tac (claset(),simpset() addsimps [real_zero_def,
    real_minus] @ preal_add_ac));
qed "real_minus_zero_iff";

Addsimps [real_minus_zero_iff];

Goal "(%~x ~= 0r) = (x ~= 0r)"; 
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
by (asm_simp_tac
    (simpset() addsimps [real_add_ize UN_equiv_class2]) 1);
qed "real_add";

Goal "(z::real) + w = w + z";
by (res_inst_tac [("z","z")] eq_Abs_real 1);
by (res_inst_tac [("z","w")] eq_Abs_real 1);
by (asm_simp_tac (simpset() addsimps (preal_add_ac @ [real_add])) 1);
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

Goalw [real_preal_def,real_zero_def] "0r + z = z";
by (res_inst_tac [("z","z")] eq_Abs_real 1);
by (asm_full_simp_tac (simpset() addsimps [real_add] @ preal_add_ac) 1);
qed "real_add_zero_left";

Goal "z + 0r = z";
by (simp_tac (simpset() addsimps [real_add_zero_left,real_add_commute]) 1);
qed "real_add_zero_right";

Goalw [real_zero_def] "z + %~z = 0r";
by (res_inst_tac [("z","z")] eq_Abs_real 1);
by (asm_full_simp_tac (simpset() addsimps [real_minus,
        real_add, preal_add_commute]) 1);
qed "real_add_minus";

Goal "%~z + z = 0r";
by (simp_tac (simpset() addsimps 
    [real_add_commute,real_add_minus]) 1);
qed "real_add_minus_left";

Goal "? y. (x::real) + y = 0r";
by (blast_tac (claset() addIs [real_add_minus]) 1);
qed "real_minus_ex";

Goal "?! y. (x::real) + y = 0r";
by (auto_tac (claset() addIs [real_add_minus],simpset()));
by (dres_inst_tac [("f","%x. ya+x")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_assoc RS sym]) 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_commute,
    real_add_zero_right,real_add_zero_left]) 1);
qed "real_minus_ex1";

Goal "?! y. y + (x::real) = 0r";
by (auto_tac (claset() addIs [real_add_minus_left],simpset()));
by (dres_inst_tac [("f","%x. x+ya")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_assoc]) 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_commute,
    real_add_zero_right,real_add_zero_left]) 1);
qed "real_minus_left_ex1";

Goal "x + y = 0r ==> x = %~y";
by (cut_inst_tac [("z","y")] real_add_minus_left 1);
by (res_inst_tac [("x1","y")] (real_minus_left_ex1 RS ex1E) 1);
by (Blast_tac 1);
qed "real_add_minus_eq_minus";

Goal "? y. x = %~y";
by (cut_inst_tac [("x","x")] real_minus_ex 1);
by (etac exE 1 THEN dtac real_add_minus_eq_minus 1);
by (Blast_tac 1);
qed "real_as_add_inverse_ex";

(* real_minus_add_distrib *)
Goal "%~(x + y) = %~x + %~y";
by (res_inst_tac [("z","x")] eq_Abs_real 1);
by (res_inst_tac [("z","y")] eq_Abs_real 1);
by (auto_tac (claset(),simpset() addsimps [real_minus,real_add]));
qed "real_minus_add_eq";

val real_minus_add_distrib = real_minus_add_eq;

Goal "((x::real) + y = x + z) = (y = z)";
by (Step_tac 1);
by (dres_inst_tac [("f","%t.%~x + t")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_minus_left,
                 real_add_assoc RS sym,real_add_zero_left]) 1);
qed "real_add_left_cancel";

Goal "(y + (x::real)= z + x) = (y = z)";
by (simp_tac (simpset() addsimps [real_add_commute,real_add_left_cancel]) 1);
qed "real_add_right_cancel";

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
by (asm_simp_tac (simpset() addsimps ([real_mult] @ preal_add_ac @ preal_mult_ac)) 1);
qed "real_mult_commute";

Goal "((z1::real) * z2) * z3 = z1 * (z2 * z3)";
by (res_inst_tac [("z","z1")] eq_Abs_real 1);
by (res_inst_tac [("z","z2")] eq_Abs_real 1);
by (res_inst_tac [("z","z3")] eq_Abs_real 1);
by (asm_simp_tac (simpset() addsimps ([preal_add_mult_distrib2,real_mult] @ 
                                     preal_add_ac @ preal_mult_ac)) 1);
qed "real_mult_assoc";

qed_goal "real_mult_left_commute" thy
    "(z1::real) * (z2 * z3) = z2 * (z1 * z3)"
 (fn _ => [rtac (real_mult_commute RS trans) 1, rtac (real_mult_assoc RS trans) 1,
           rtac (real_mult_commute RS arg_cong) 1]);

(* real multiplication is an AC operator *)
val real_mult_ac = [real_mult_assoc, real_mult_commute, real_mult_left_commute];

Goalw [real_one_def,pnat_one_def] "1r * z = z";
by (res_inst_tac [("z","z")] eq_Abs_real 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult,
    preal_add_mult_distrib2,preal_mult_1_right] 
    @ preal_mult_ac @ preal_add_ac) 1);
qed "real_mult_1";

Goal "z * 1r = z";
by (simp_tac (simpset() addsimps [real_mult_commute,
    real_mult_1]) 1);
qed "real_mult_1_right";

Goalw [real_zero_def,pnat_one_def] "0r * z = 0r";
by (res_inst_tac [("z","z")] eq_Abs_real 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult,
    preal_add_mult_distrib2,preal_mult_1_right] 
    @ preal_mult_ac @ preal_add_ac) 1);
qed "real_mult_0";

Goal "z * 0r = 0r";
by (simp_tac (simpset() addsimps [real_mult_commute,
    real_mult_0]) 1);
qed "real_mult_0_right";

Addsimps [real_mult_0_right,real_mult_0];

Goal "%~(x * y) = %~x * y";
by (res_inst_tac [("z","x")] eq_Abs_real 1);
by (res_inst_tac [("z","y")] eq_Abs_real 1);
by (auto_tac (claset(),simpset() addsimps [real_minus,real_mult] 
    @ preal_mult_ac @ preal_add_ac));
qed "real_minus_mult_eq1";

Goal "%~(x * y) = x * %~y";
by (res_inst_tac [("z","x")] eq_Abs_real 1);
by (res_inst_tac [("z","y")] eq_Abs_real 1);
by (auto_tac (claset(),simpset() addsimps [real_minus,real_mult] 
    @ preal_mult_ac @ preal_add_ac));
qed "real_minus_mult_eq2";

Goal "%~x*%~y = x*y";
by (full_simp_tac (simpset() addsimps [real_minus_mult_eq2 RS sym,
    real_minus_mult_eq1 RS sym]) 1);
qed "real_minus_mult_cancel";

Addsimps [real_minus_mult_cancel];

Goal "%~x*y = x*%~y";
by (full_simp_tac (simpset() addsimps [real_minus_mult_eq2 RS sym,
    real_minus_mult_eq1 RS sym]) 1);
qed "real_minus_mult_commute";

(*-----------------------------------------------------------------------------

 -----------------------------------------------------------------------------*)

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
    (simpset() addsimps ([preal_add_mult_distrib2, real_add, real_mult] @ 
                        preal_add_ac @ preal_mult_ac)) 1);
qed "real_add_mult_distrib";

val real_mult_commute'= read_instantiate [("z","w")] real_mult_commute;

Goal "(w::real) * (z1 + z2) = (w * z1) + (w * z2)";
by (simp_tac (simpset() addsimps [real_mult_commute',real_add_mult_distrib]) 1);
qed "real_add_mult_distrib2";

val real_mult_simps = [real_mult_1, real_mult_1_right];
Addsimps real_mult_simps;

(*** one and zero are distinct ***)
Goalw [real_zero_def,real_one_def] "0r ~= 1r";
by (auto_tac (claset(),simpset() addsimps 
   [preal_self_less_add_left RS preal_not_refl2]));
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
by (res_inst_tac [("x","Abs_real (realrel ^^ {(@#$#1p,pinv(D)+@#$#1p)})")] exI 1);
by (res_inst_tac [("x","Abs_real (realrel ^^ {(pinv(D)+@#$#1p,@#$#1p)})")] exI 2);
by (auto_tac (claset(),simpset() addsimps [real_mult,
    pnat_one_def,preal_mult_1_right,preal_add_mult_distrib2,
    preal_add_mult_distrib,preal_mult_1,preal_mult_inv_right] 
    @ preal_add_ac @ preal_mult_ac));
qed "real_mult_inv_right_ex";

Goal "!!(x::real). x ~= 0r ==> ? y. y*x = 1r";
by (asm_simp_tac (simpset() addsimps [real_mult_commute,
    real_mult_inv_right_ex]) 1);
qed "real_mult_inv_left_ex";

Goalw [rinv_def] "!!(x::real). x ~= 0r ==> rinv(x)*x = 1r";
by (forward_tac [real_mult_inv_left_ex] 1);
by (Step_tac 1);
by (rtac selectI2 1);
by Auto_tac;
qed "real_mult_inv_left";

Goal "!!(x::real). x ~= 0r ==> x*rinv(x) = 1r";
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
by (asm_full_simp_tac (simpset() addsimps [real_mult_inv_right] @ real_mult_ac)  1);
qed "real_mult_right_cancel";

Goalw [rinv_def] "x ~= 0r ==> rinv(x) ~= 0r";
by (forward_tac [real_mult_inv_left_ex] 1);
by (etac exE 1);
by (rtac selectI2 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_0,
    real_zero_not_eq_one]));
qed "rinv_not_zero";

Addsimps [real_mult_inv_left,real_mult_inv_right];

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
by (auto_tac (claset(),simpset() addsimps 
    [real_zero_not_eq_one RS not_sym]));
qed "real_rinv_1";

Goal "x ~= 0r ==> rinv(%~x) = %~rinv(x)";
by (res_inst_tac [("c1","%~x")] (real_mult_right_cancel RS iffD1) 1);
by Auto_tac;
qed "real_minus_rinv";

      (*** theorems for ordering ***)
(* prove introduction and elimination rules for real_less *)

Goalw [real_less_def]
 "P < (Q::real) = (EX x1 y1 x2 y2. x1 + y2 < x2 + y1 & \
\                                  (x1,y1::preal):Rep_real(P) & \
\                                  (x2,y2):Rep_real(Q))";
by (Blast_tac 1);
qed "real_less_iff";

Goalw [real_less_def]
 "[| x1 + y2 < x2 + y1; (x1,y1::preal):Rep_real(P); \
\         (x2,y2):Rep_real(Q) |] ==> P < (Q::real)";
by (Blast_tac 1);
qed "real_lessI";

Goalw [real_less_def]
 "!!P. [| R1 < (R2::real); \
\         !!x1 x2 y1 y2. x1 + y2 < x2 + y1 ==> P; \
\         !!x1 y1. (x1,y1::preal):Rep_real(R1) ==> P; \ 
\         !!x2 y2. (x2,y2::preal):Rep_real(R2) ==> P |] \
\     ==> P";
by Auto_tac;
qed "real_lessE";

Goalw [real_less_def]
 "R1 < (R2::real) ==> (EX x1 y1 x2 y2. x1 + y2 < x2 + y1 & \
\                                  (x1,y1::preal):Rep_real(R1) & \
\                                  (x2,y2):Rep_real(R2))";
by (Blast_tac 1);
qed "real_lessD";

(* real_less is a strong order i.e nonreflexive and transitive *)
(*** lemmas ***)
Goal "!!(x::preal). [| x = y; x1 = y1 |] ==> x + y1 = x1 + y";
by (asm_simp_tac (simpset() addsimps [preal_add_commute]) 1);
qed "preal_lemma_eq_rev_sum";

Goal "!!(b::preal). x + (b + y) = x1 + (b + y1) ==> x + y = x1 + y1";
by (asm_full_simp_tac (simpset() addsimps preal_add_ac) 1);
qed "preal_add_left_commute_cancel";

Goal 
     "!!(x::preal). [| x + y2a = x2a + y; \
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
bind_thm("real_less_irrefl",real_less_not_refl RS notE);

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
Goalw [real_preal_def] 
            "%#((z1::preal) + z2) = %#z1 + %#z2";
by (asm_simp_tac (simpset() addsimps [real_add,
       preal_add_mult_distrib,preal_mult_1] addsimps preal_add_ac) 1);
qed "real_preal_add";

Goalw [real_preal_def] 
            "%#((z1::preal) * z2) = %#z1* %#z2";
by (full_simp_tac (simpset() addsimps [real_mult,
        preal_add_mult_distrib2,preal_mult_1,
        preal_mult_1_right,pnat_one_def] 
        @ preal_add_ac @ preal_mult_ac) 1);
qed "real_preal_mult";

Goalw [real_preal_def]
      "!!(x::preal). y < x ==> ? m. Abs_real (realrel ^^ {(x,y)}) = %#m";
by (auto_tac (claset() addSDs [preal_less_add_left_Ex],
    simpset() addsimps preal_add_ac));
qed "real_preal_ExI";

Goalw [real_preal_def]
      "!!(x::preal). ? m. Abs_real (realrel ^^ {(x,y)}) = %#m ==> y < x";
by (auto_tac (claset(),simpset() addsimps 
    [preal_add_commute,preal_add_assoc]));
by (asm_full_simp_tac (simpset() addsimps 
    [preal_add_assoc RS sym,preal_self_less_add_left]) 1);
qed "real_preal_ExD";

Goal "(? m. Abs_real (realrel ^^ {(x,y)}) = %#m) = (y < x)";
by (blast_tac (claset() addSIs [real_preal_ExI,real_preal_ExD]) 1);
qed "real_preal_iff";

(*** Gleason prop 9-4.4 p 127 ***)
Goalw [real_preal_def,real_zero_def] 
      "? m. (x::real) = %#m | x = 0r | x = %~(%#m)";
by (res_inst_tac [("z","x")] eq_Abs_real 1);
by (auto_tac (claset(),simpset() addsimps [real_minus] @ preal_add_ac));
by (cut_inst_tac [("r1.0","x"),("r2.0","y")] preal_linear 1);
by (auto_tac (claset() addSDs [preal_less_add_left_Ex],
    simpset() addsimps [preal_add_assoc RS sym]));
by (auto_tac (claset(),simpset() addsimps [preal_add_commute]));
qed "real_preal_trichotomy";

Goal "!!P. [| !!m. x = %#m ==> P; \
\             x = 0r ==> P; \
\             !!m. x = %~(%#m) ==> P |] ==> P";
by (cut_inst_tac [("x","x")] real_preal_trichotomy 1);
by Auto_tac;
qed "real_preal_trichotomyE";

Goalw [real_preal_def] "%#m1 < %#m2 ==> m1 < m2";
by (auto_tac (claset(),simpset() addsimps [real_less_def] @ preal_add_ac));
by (auto_tac (claset(),simpset() addsimps [preal_add_assoc RS sym]));
by (auto_tac (claset(),simpset() addsimps preal_add_ac));
qed "real_preal_lessD";

Goal "m1 < m2 ==> %#m1 < %#m2";
by (dtac preal_less_add_left_Ex 1);
by (auto_tac (claset(),simpset() addsimps [real_preal_add,
    real_preal_def,real_less_def]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (simp_tac (simpset() addsimps [preal_self_less_add_left] 
    delsimps [preal_add_less_iff2]) 1);
qed "real_preal_lessI";

Goal "(%#m1 < %#m2) = (m1 < m2)";
by (blast_tac (claset() addIs [real_preal_lessI,real_preal_lessD]) 1);
qed "real_preal_less_iff1";

Addsimps [real_preal_less_iff1];

Goal "%~ %#m < %#m";
by (auto_tac (claset(),simpset() addsimps 
    [real_preal_def,real_less_def,real_minus]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (full_simp_tac (simpset() addsimps preal_add_ac) 1);
by (full_simp_tac (simpset() addsimps [preal_self_less_add_right,
    preal_add_assoc RS sym]) 1);
qed "real_preal_minus_less_self";

Goalw [real_zero_def] "%~ %#m < 0r";
by (auto_tac (claset(),simpset() addsimps 
    [real_preal_def,real_less_def,real_minus]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (full_simp_tac (simpset() addsimps 
  [preal_self_less_add_right] @ preal_add_ac) 1);
qed "real_preal_minus_less_zero";

Goal "~ 0r < %~ %#m";
by (cut_facts_tac [real_preal_minus_less_zero] 1);
by (fast_tac (claset() addDs [real_less_trans] 
                        addEs [real_less_irrefl]) 1);
qed "real_preal_not_minus_gt_zero";

Goalw [real_zero_def] " 0r < %#m";
by (auto_tac (claset(),simpset() addsimps 
    [real_preal_def,real_less_def,real_minus]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (full_simp_tac (simpset() addsimps 
  [preal_self_less_add_right] @ preal_add_ac) 1);
qed "real_preal_zero_less";

Goal "~ %#m < 0r";
by (cut_facts_tac [real_preal_zero_less] 1);
by (blast_tac (claset() addDs [real_less_trans] 
               addEs [real_less_irrefl]) 1);
qed "real_preal_not_less_zero";

Goal "0r < %~ %~ %#m";
by (simp_tac (simpset() addsimps 
    [real_preal_zero_less]) 1);
qed "real_minus_minus_zero_less";

(* another lemma *)
Goalw [real_zero_def] " 0r < %#m + %#m1";
by (auto_tac (claset(),simpset() addsimps 
    [real_preal_def,real_less_def,real_add]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (full_simp_tac (simpset() addsimps preal_add_ac) 1);
by (full_simp_tac (simpset() addsimps [preal_self_less_add_right,
    preal_add_assoc RS sym]) 1);
qed "real_preal_sum_zero_less";

Goal "%~ %#m < %#m1";
by (auto_tac (claset(),simpset() addsimps 
    [real_preal_def,real_less_def,real_minus]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (full_simp_tac (simpset() addsimps preal_add_ac) 1);
by (full_simp_tac (simpset() addsimps [preal_self_less_add_right,
    preal_add_assoc RS sym]) 1);
qed "real_preal_minus_less_all";

Goal "~ %#m < %~ %#m1";
by (cut_facts_tac [real_preal_minus_less_all] 1);
by (blast_tac (claset() addDs [real_less_trans] 
               addEs [real_less_irrefl]) 1);
qed "real_preal_not_minus_gt_all";

Goal "%~ %#m1 < %~ %#m2 ==> %#m2 < %#m1";
by (auto_tac (claset(),simpset() addsimps 
    [real_preal_def,real_less_def,real_minus]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (auto_tac (claset(),simpset() addsimps preal_add_ac));
by (asm_full_simp_tac (simpset() addsimps [preal_add_assoc RS sym]) 1);
by (auto_tac (claset(),simpset() addsimps preal_add_ac));
qed "real_preal_minus_less_rev1";

Goal "%#m1 < %#m2 ==> %~ %#m2 < %~ %#m1";
by (auto_tac (claset(),simpset() addsimps 
    [real_preal_def,real_less_def,real_minus]));
by (REPEAT(rtac exI 1));
by (EVERY[rtac conjI 1, rtac conjI 2]);
by (REPEAT(Blast_tac 2));
by (auto_tac (claset(),simpset() addsimps preal_add_ac));
by (asm_full_simp_tac (simpset() addsimps [preal_add_assoc RS sym]) 1);
by (auto_tac (claset(),simpset() addsimps preal_add_ac));
qed "real_preal_minus_less_rev2";

Goal "(%~ %#m1 < %~ %#m2) = (%#m2 < %#m1)";
by (blast_tac (claset() addSIs [real_preal_minus_less_rev1,
               real_preal_minus_less_rev2]) 1);
qed "real_preal_minus_less_rev_iff";

Addsimps [real_preal_minus_less_rev_iff];

(*** linearity ***)
Goal "(R1::real) < R2 | R1 = R2 | R2 < R1";
by (res_inst_tac [("x","R1")]  real_preal_trichotomyE 1);
by (ALLGOALS(res_inst_tac [("x","R2")]  real_preal_trichotomyE));
by (auto_tac (claset() addSDs [preal_le_anti_sym],
              simpset() addsimps [preal_less_le_iff,real_preal_minus_less_zero,
               real_preal_zero_less,real_preal_minus_less_all]));
qed "real_linear";

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
qed "real_le_eq_less_or_eq";

Goal "w <= (w::real)";
by (simp_tac (simpset() addsimps [real_le_eq_less_or_eq]) 1);
qed "real_le_refl";

val prems = goal Real.thy "!!i. [| i <= j; j < k |] ==> i < (k::real)";
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

Goal "(0r < %~R) = (R < 0r)";
by (res_inst_tac [("x","R")]  real_preal_trichotomyE 1);
by (auto_tac (claset(),simpset() addsimps [real_preal_not_minus_gt_zero,
                        real_preal_not_less_zero,real_preal_zero_less,
                        real_preal_minus_less_zero]));
qed "real_minus_zero_less_iff";

Addsimps [real_minus_zero_less_iff];

Goal "(%~R < 0r) = (0r < R)";
by (res_inst_tac [("x","R")]  real_preal_trichotomyE 1);
by (auto_tac (claset(),simpset() addsimps [real_preal_not_minus_gt_zero,
                        real_preal_not_less_zero,real_preal_zero_less,
                        real_preal_minus_less_zero]));
qed "real_minus_zero_less_iff2";

(** lemma **)
Goal "(0r < x) = (? y. x = %#y)";
by (auto_tac (claset(),simpset() addsimps [real_preal_zero_less]));
by (cut_inst_tac [("x","x")] real_preal_trichotomy 1);
by (blast_tac (claset() addSEs [real_less_irrefl,
     real_preal_not_minus_gt_zero RS notE]) 1);
qed "real_gt_zero_preal_Ex";

Goal "%#z < x ==> ? y. x = %#y";
by (blast_tac (claset() addSDs [real_preal_zero_less RS real_less_trans]
               addIs [real_gt_zero_preal_Ex RS iffD1]) 1);
qed "real_gt_preal_preal_Ex";

Goal "%#z <= x ==> ? y. x = %#y";
by (blast_tac (claset() addDs [real_le_imp_less_or_eq,
              real_gt_preal_preal_Ex]) 1);
qed "real_ge_preal_preal_Ex";

Goal "y <= 0r ==> !x. y < %#x";
by (auto_tac (claset() addEs [real_le_imp_less_or_eq RS disjE]
              addIs [real_preal_zero_less RSN(2,real_less_trans)],
              simpset() addsimps [real_preal_zero_less]));
qed "real_less_all_preal";

Goal "~ 0r < y ==> !x. y < %#x";
by (blast_tac (claset() addSIs [real_less_all_preal,real_leI]) 1);
qed "real_less_all_real2";

(**** Derive alternative definition for real_less ****)
(** lemma **)
Goal "!!(R::real). ? A. S + A = R";
by (res_inst_tac [("x","%~S + R")] exI 1);
by (simp_tac (simpset() addsimps [real_add_minus,
    real_add_zero_right] @ real_add_ac) 1);
qed "real_lemma_add_left_ex";

Goal "!!(R::real). R < S ==> ? T. R + T = S";
by (res_inst_tac [("x","R")]  real_preal_trichotomyE 1);
by (ALLGOALS(res_inst_tac [("x","S")]  real_preal_trichotomyE));
by (auto_tac (claset() addSDs [preal_le_anti_sym] addSDs [preal_less_add_left_Ex],
              simpset() addsimps [preal_less_le_iff,real_preal_add,real_minus_add_eq,
               real_preal_minus_less_zero,real_less_not_refl,real_minus_ex,real_add_assoc,
               real_preal_zero_less,real_preal_minus_less_all,real_add_minus_left,
               real_preal_not_less_zero,real_add_zero_left,real_lemma_add_left_ex]));
qed "real_less_add_left_Ex";

Goal "!!(R::real). R < S ==> ? T. 0r < T & R + T = S";
by (res_inst_tac [("x","R")]  real_preal_trichotomyE 1);
by (ALLGOALS(res_inst_tac [("x","S")]  real_preal_trichotomyE));
by (auto_tac (claset() addSDs [preal_less_add_left_Ex],
                         simpset() addsimps [real_preal_not_minus_gt_all,
            real_preal_add, real_preal_not_less_zero,real_less_not_refl,
    real_preal_not_minus_gt_zero,real_add_zero_left,real_minus_add_eq]));
by (res_inst_tac [("x","%#D")] exI 1);
by (res_inst_tac [("x","%#m+%#ma")] exI 2);
by (res_inst_tac [("x","%#m")] exI 3);
by (res_inst_tac [("x","%#D")] exI 4);
by (auto_tac (claset(),simpset() addsimps [real_preal_zero_less,
    real_preal_sum_zero_less,real_add_minus_left,real_add_assoc,
                          real_add_minus,real_add_zero_right]));
by (simp_tac (simpset() addsimps [real_add_assoc RS sym, 
            real_add_minus_left,real_add_zero_left]) 1);
qed "real_less_add_positive_left_Ex";

(* lemmas *)
(** change naff name(s)! **)
Goal "(W < S) ==> (0r < S + %~W)";
by (dtac real_less_add_positive_left_Ex 1);
by (auto_tac (claset(),simpset() addsimps [real_add_minus,
    real_add_zero_right] @ real_add_ac));
qed "real_less_sum_gt_zero";

Goal "!!S. T = S + W ==> S = T + %~W";
by (asm_simp_tac (simpset() addsimps [real_add_minus, real_add_zero_right] 
		                     @ real_add_ac) 1);
qed "real_lemma_change_eq_subj";

(* FIXME: long! *)
Goal "(0r < S + %~W) ==> (W < S)";
by (rtac ccontr 1);
by (dtac (real_leI RS real_le_imp_less_or_eq) 1);
by (auto_tac (claset(),
    simpset() addsimps [real_less_not_refl,real_add_minus]));
by (EVERY1[dtac real_less_add_positive_left_Ex, etac exE, etac conjE]);
by (asm_full_simp_tac (simpset() addsimps [real_add_zero_left]) 1);
by (dtac real_lemma_change_eq_subj 1);
by (auto_tac (claset(),simpset() addsimps [real_minus_minus]));
by (dtac real_less_sum_gt_zero 1);
by (asm_full_simp_tac (simpset() addsimps [real_minus_add_eq] @ real_add_ac) 1);
by (EVERY1[rotate_tac 1, dtac (real_add_left_commute RS ssubst)]);
by (auto_tac (claset() addEs [real_less_asym],
              simpset() addsimps [real_add_minus,real_add_zero_right]));
qed "real_sum_gt_zero_less";

Goal "(0r < S + %~W) = (W < S)";
by (blast_tac (claset() addIs [real_less_sum_gt_zero,
    real_sum_gt_zero_less]) 1);
qed "real_less_sum_gt_0_iff";

Goal "((x::real) < y) = (%~y < %~x)";
by (rtac (real_less_sum_gt_0_iff RS subst) 1);
by (res_inst_tac [("W1","x")] (real_less_sum_gt_0_iff RS subst) 1);
by (simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "real_less_swap_iff";

Goal "[| R + L = S; 0r < L |] ==> R < S";
by (rtac (real_less_sum_gt_0_iff RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [
    real_add_minus,real_add_zero_right] @ real_add_ac));
qed "real_lemma_add_positive_imp_less";

Goal "!!(R::real). ? T. 0r < T & R + T = S ==> R < S";
by (blast_tac (claset() addIs [real_lemma_add_positive_imp_less]) 1);
qed "real_ex_add_positive_left_less";

(*** alternative definition for real_less ***)
Goal "!!(R::real). (? T. 0r < T & R + T = S) = (R < S)";
by (blast_tac (claset() addSIs [real_less_add_positive_left_Ex,
    real_ex_add_positive_left_less]) 1);
qed "real_less_iffdef";

Goal "(0r < x) = (%~x < x)";
by Safe_tac;
by (rtac ccontr 2 THEN forward_tac 
    [real_leI RS real_le_imp_less_or_eq] 2);
by (Step_tac 2);
by (dtac (real_minus_zero_less_iff RS iffD2) 2);
by (blast_tac (claset() addIs [real_less_trans]) 2);
by (auto_tac (claset(),simpset() addsimps 
    [real_gt_zero_preal_Ex,real_preal_minus_less_self]));
qed "real_gt_zero_iff";

Goal "(x < 0r) = (x < %~x)";
by (rtac (real_minus_zero_less_iff RS subst) 1);
by (stac real_gt_zero_iff 1);
by (Full_simp_tac 1);
qed "real_lt_zero_iff";

Goalw [real_le_def] "(0r <= x) = (%~x <= x)";
by (auto_tac (claset(),simpset() addsimps [real_lt_zero_iff RS sym]));
qed "real_ge_zero_iff";

Goalw [real_le_def] "(x <= 0r) = (x <= %~x)";
by (auto_tac (claset(),simpset() addsimps [real_gt_zero_iff RS sym]));
qed "real_le_zero_iff";

Goal "(%#m1 <= %#m2) = (m1 <= m2)";
by (auto_tac (claset() addSIs [preal_leI],
    simpset() addsimps [real_less_le_iff RS sym]));
by (dtac preal_le_less_trans 1 THEN assume_tac 1);
by (etac preal_less_irrefl 1);
qed "real_preal_le_iff";

Goal "!!(x::real). [| 0r < x; 0r < y |] ==> 0r < x * y";
by (auto_tac (claset(),simpset() addsimps [real_gt_zero_preal_Ex]));  
by (res_inst_tac [("x","y*ya")] exI 1);
by (full_simp_tac (simpset() addsimps [real_preal_mult]) 1);
qed "real_mult_order";

Goal "!!(x::real). [| x < 0r; y < 0r |] ==> 0r < x * y";
by (REPEAT(dtac (real_minus_zero_less_iff RS iffD2) 1));
by (dtac real_mult_order 1 THEN assume_tac 1);
by (Asm_full_simp_tac 1);
qed "real_mult_less_zero1";

Goal "!!(x::real). [| 0r <= x; 0r <= y |] ==> 0r <= x * y";
by (REPEAT(dtac real_le_imp_less_or_eq 1));
by (auto_tac (claset() addIs [real_mult_order,
    real_less_imp_le],simpset() addsimps [real_le_refl]));
qed "real_le_mult_order";

Goal "!!(x::real). [| x <= 0r; y <= 0r |] ==> 0r <= x * y";
by (rtac real_less_or_eq_imp_le 1);
by (dtac real_le_imp_less_or_eq 1 THEN etac disjE 1);
by Auto_tac;
by (dtac real_le_imp_less_or_eq 1);
by (auto_tac (claset() addDs [real_mult_less_zero1],simpset()));
qed "real_mult_le_zero1";

Goal "!!(x::real). [| 0r <= x; y < 0r |] ==> x * y <= 0r";
by (rtac real_less_or_eq_imp_le 1);
by (dtac real_le_imp_less_or_eq 1 THEN etac disjE 1);
by Auto_tac;
by (dtac (real_minus_zero_less_iff RS iffD2) 1);
by (rtac (real_minus_zero_less_iff RS subst) 1);
by (blast_tac (claset() addDs [real_mult_order] 
    addIs [real_minus_mult_eq2 RS ssubst]) 1);
qed "real_mult_le_zero";

Goal "!!(x::real). [| 0r < x; y < 0r |] ==> x*y < 0r";
by (dtac (real_minus_zero_less_iff RS iffD2) 1);
by (dtac real_mult_order 1 THEN assume_tac 1);
by (rtac (real_minus_zero_less_iff RS iffD1) 1);
by (asm_full_simp_tac (simpset() addsimps [real_minus_mult_eq2]) 1);
qed "real_mult_less_zero";

Goalw [real_one_def] "0r < 1r";
by (auto_tac (claset() addIs [real_gt_zero_preal_Ex RS iffD2],
    simpset() addsimps [real_preal_def]));
qed "real_zero_less_one";

(*** Completeness of reals ***)
(** use supremum property of preal and theorems about real_preal **)
              (*** a few lemmas ***)
Goal "! x:P. 0r < x ==> ((? x:P. y < x) = (? X. %#X : P & y < %#X))";
by (blast_tac (claset() addSDs [bspec,real_gt_zero_preal_Ex RS iffD1]) 1);
qed "real_sup_lemma1";

Goal "[| ! x:P. 0r < x; ? x. x: P; ? y. !x: P. x < y |] \
\         ==> (? X. X: {w. %#w : P}) & (? Y. !X: {w. %#w : P}. X < Y)";
by (rtac conjI 1);
by (blast_tac (claset() addDs [bspec,real_gt_zero_preal_Ex RS iffD1]) 1);
by Auto_tac;
by (dtac bspec 1 THEN assume_tac 1);
by (forward_tac [bspec] 1  THEN assume_tac 1);
by (dtac real_less_trans 1 THEN assume_tac 1);
by (dtac (real_gt_zero_preal_Ex RS iffD1) 1 THEN etac exE 1);
by (res_inst_tac [("x","ya")] exI 1);
by Auto_tac;
by (dres_inst_tac [("x","%#X")] bspec 1 THEN assume_tac 1);
by (etac real_preal_lessD 1);
qed "real_sup_lemma2";

(*-------------------------------------------------------------
            Completeness of Positive Reals
 -------------------------------------------------------------*)

(* Supremum property for the set of positive reals *)
(* FIXME: long proof - can be improved - need only have one case split *)
(* will do for now *)
Goal "[| ! x:P. 0r < x; ? x. x: P; ? y. !x: P. x < y |] \
\         ==> (? S. !y. (? x: P. y < x) = (y < S))";
by (res_inst_tac [("x","%#psup({w. %#w : P})")] exI 1);
by Auto_tac;
by (forward_tac [real_sup_lemma2] 1 THEN Auto_tac);
by (case_tac "0r < ya" 1);
by (dtac (real_gt_zero_preal_Ex RS iffD1) 1);
by (dtac real_less_all_real2 2);
by Auto_tac;
by (rtac (preal_complete RS spec RS iffD1) 1);
by Auto_tac;
by (forward_tac [real_gt_preal_preal_Ex] 1);
by Auto_tac;
(* second part *)
by (rtac (real_sup_lemma1 RS iffD2) 1 THEN assume_tac 1);
by (case_tac "0r < ya" 1);
by (auto_tac (claset() addSDs [real_less_all_real2,
        real_gt_zero_preal_Ex RS iffD1],simpset()));
by (forward_tac [real_sup_lemma2] 2 THEN Auto_tac);
by (forward_tac [real_sup_lemma2] 1 THEN Auto_tac);
by (rtac (preal_complete RS spec RS iffD2 RS bexE) 1);
by (Blast_tac 3);
by (Blast_tac 1);
by (Blast_tac 1);
by (Blast_tac 1);
qed "posreal_complete";

(*------------------------------------------------------------------

 ------------------------------------------------------------------*)

Goal "!!(A::real). A < B ==> A + C < B + C";
by (dtac (real_less_iffdef RS iffD2) 1);
by (rtac (real_less_iffdef RS iffD1) 1);
by (REPEAT(Step_tac 1));
by (full_simp_tac (simpset() addsimps real_add_ac) 1);
qed "real_add_less_mono1";

Goal "!!(A::real). A < B ==> C + A < C + B";
by (auto_tac (claset() addIs [real_add_less_mono1],
    simpset() addsimps [real_add_commute]));
qed "real_add_less_mono2";

Goal "!!(A::real). A + C < B + C ==> A < B";
by (dres_inst_tac [("C","%~C")] real_add_less_mono1 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_assoc,
    real_add_minus,real_add_zero_right]) 1);
qed "real_less_add_right_cancel";

Goal "!!(A::real). C + A < C + B ==> A < B";
by (dres_inst_tac [("C","%~C")] real_add_less_mono2 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_assoc RS sym,
    real_add_minus_left,real_add_zero_left]) 1);
qed "real_less_add_left_cancel";

Goal "[| 0r < x; 0r < y |] ==> 0r < x + y";
by (REPEAT(dtac (real_gt_zero_preal_Ex RS iffD1) 1));
by (rtac (real_gt_zero_preal_Ex RS iffD2) 1);
by (Step_tac 1);
by (res_inst_tac [("x","y + ya")] exI 1);
by (full_simp_tac (simpset() addsimps [real_preal_add]) 1);
qed "real_add_order";

Goal "!!(x::real). [| 0r <= x; 0r <= y |] ==> 0r <= x + y";
by (REPEAT(dtac real_le_imp_less_or_eq 1));
by (auto_tac (claset() addIs [real_add_order,
    real_less_imp_le],simpset() addsimps [real_add_zero_left,
    real_add_zero_right,real_le_refl]));
qed "real_le_add_order";

Goal 
      "[| R1 < S1; R2 < S2 |] ==> R1 + R2 < S1 + (S2::real)";
by (dtac (real_less_iffdef RS iffD2) 1);
by (dtac (real_less_iffdef RS iffD2) 1);
by (rtac (real_less_iffdef RS iffD1) 1);
by Auto_tac;
by (res_inst_tac [("x","T + Ta")] exI 1);
by (auto_tac (claset(),simpset() addsimps [real_add_order] @ real_add_ac));
qed "real_add_less_mono";

Goal "!!(x::real). [| 0r <= x; 0r <= y |] ==> 0r <= x + y";
by (REPEAT(dtac real_le_imp_less_or_eq 1));
by (auto_tac (claset() addIs [real_add_order,
    real_less_imp_le],simpset() addsimps [real_add_zero_left,
    real_add_zero_right,real_le_refl]));
qed "real_le_add_order";

Goal "!!(q1::real). q1 <= q2  ==> x + q1 <= x + q2";
by (dtac real_le_imp_less_or_eq 1);
by (Step_tac 1);
by (auto_tac (claset() addSIs [real_le_refl,
    real_less_imp_le,real_add_less_mono1],
    simpset() addsimps [real_add_commute]));
qed "real_add_left_le_mono1";

Goal "!!(q1::real). q1 <= q2  ==> q1 + x <= q2 + x";
by (auto_tac (claset() addDs [real_add_left_le_mono1],
    simpset() addsimps [real_add_commute]));
qed "real_add_le_mono1";

Goal "!!k l::real. [|i<=j;  k<=l |] ==> i + k <= j + l";
by (etac (real_add_le_mono1 RS real_le_trans) 1);
by (simp_tac (simpset() addsimps [real_add_commute]) 1);
(*j moves to the end because it is free while k, l are bound*)
by (etac real_add_le_mono1 1);
qed "real_add_le_mono";

Goal "EX (x::real). x < y";
by (rtac (real_add_zero_right RS subst) 1);
by (res_inst_tac [("x","y + %~1r")] exI 1);
by (auto_tac (claset() addSIs [real_add_less_mono2],
    simpset() addsimps [real_minus_zero_less_iff2,
    real_zero_less_one]));
qed "real_less_Ex";
(*---------------------------------------------------------------------------------
             An embedding of the naturals in the reals
 ---------------------------------------------------------------------------------*)

Goalw [real_nat_def] "%%#0 = 1r";
by (full_simp_tac (simpset() addsimps [pnat_one_iff RS sym,real_preal_def]) 1);
by (fold_tac [real_one_def]);
by (rtac refl 1);
qed "real_nat_one";

Goalw [real_nat_def] "%%#1 = 1r + 1r";
by (full_simp_tac (simpset() addsimps [real_preal_def,real_one_def,
    pnat_two_eq,real_add,prat_pnat_add RS sym,preal_prat_add RS sym
    ] @ pnat_add_ac) 1);
qed "real_nat_two";

Goalw [real_nat_def]
          "%%#n1 + %%#n2 = %%#(n1 + n2) + 1r";
by (full_simp_tac (simpset() addsimps [real_nat_one RS sym,
    real_nat_def,real_preal_add RS sym,preal_prat_add RS sym,
    prat_pnat_add RS sym,pnat_nat_add]) 1);
qed "real_nat_add";

Goal "%%#(n + 1) = %%#n + 1r";
by (res_inst_tac [("x1","1r")] (real_add_right_cancel RS iffD1) 1);
by (rtac (real_nat_add RS subst) 1);
by (full_simp_tac (simpset() addsimps [real_nat_two,real_add_assoc]) 1);
qed "real_nat_add_one";

Goal "Suc n = n + 1";
by Auto_tac;
qed "lemma";

Goal "%%#Suc n = %%#n + 1r";
by (stac lemma 1);
by (rtac real_nat_add_one 1);
qed "real_nat_Suc";

Goal "inj(real_nat)";
by (rtac injI 1);
by (rewtac real_nat_def);
by (dtac (inj_real_preal RS injD) 1);
by (dtac (inj_preal_prat RS injD) 1);
by (dtac (inj_prat_pnat RS injD) 1);
by (etac (inj_pnat_nat RS injD) 1);
qed "inj_real_nat";

Goalw [real_nat_def] "0r < %%#n";
by (rtac (real_gt_zero_preal_Ex RS iffD2) 1);
by (Blast_tac 1);
qed "real_nat_less_zero";

Goal "1r <= %%#n";
by (simp_tac (simpset() addsimps [real_nat_one RS sym]) 1);
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset () 
    addsimps [real_nat_Suc,real_le_refl,real_nat_one]));
by (res_inst_tac [("t","1r")] (real_add_zero_left RS subst) 1);
by (rtac real_add_le_mono 1);
by (auto_tac (claset(),simpset () 
    addsimps [real_le_refl,real_nat_less_zero,
    real_less_imp_le,real_add_zero_left]));
qed "real_nat_less_one";

Goal "rinv(%%#n) ~= 0r";
by (rtac ((real_nat_less_zero RS 
    real_not_refl2 RS not_sym) RS rinv_not_zero) 1);
qed "real_nat_rinv_not_zero";

Goal "rinv(%%#x) = rinv(%%#y) ==> x = y";
by (rtac (inj_real_nat RS injD) 1);
by (res_inst_tac [("n2","x")] 
    (real_nat_rinv_not_zero RS real_mult_left_cancel RS iffD1) 1);
by (full_simp_tac (simpset() addsimps [(real_nat_less_zero RS 
    real_not_refl2 RS not_sym) RS real_mult_inv_left]) 1);
by (asm_full_simp_tac (simpset() addsimps [(real_nat_less_zero RS 
    real_not_refl2 RS not_sym)]) 1);
qed "real_nat_rinv_inj";

Goal "0r < x ==> 0r < rinv x";
by (EVERY1[rtac ccontr, dtac real_leI]);
by (forward_tac [real_minus_zero_less_iff2 RS iffD2] 1);
by (forward_tac [real_not_refl2 RS not_sym] 1);
by (dtac (real_not_refl2 RS not_sym RS rinv_not_zero) 1);
by (EVERY1[dtac real_le_imp_less_or_eq, Step_tac]); 
by (dtac real_mult_less_zero1 1 THEN assume_tac 1);
by (auto_tac (claset() addIs [real_zero_less_one RS real_less_asym],
    simpset() addsimps [real_minus_mult_eq1 RS sym]));
qed "real_rinv_gt_zero";

Goal "x < 0r ==> rinv x < 0r";
by (forward_tac [real_not_refl2] 1);
by (dtac (real_minus_zero_less_iff RS iffD2) 1);
by (rtac (real_minus_zero_less_iff RS iffD1) 1);
by (dtac (real_minus_rinv RS sym) 1);
by (auto_tac (claset() addIs [real_rinv_gt_zero],
    simpset()));
qed "real_rinv_less_zero";

Goal "x+x=x*(1r+1r)";
by (simp_tac (simpset() addsimps [real_add_mult_distrib2]) 1);
qed "real_add_self";

Goal "x < x + 1r";
by (rtac (real_less_sum_gt_0_iff RS iffD1) 1);
by (full_simp_tac (simpset() addsimps [real_zero_less_one,
    real_add_assoc,real_add_minus,real_add_zero_right,
    real_add_left_commute]) 1);
qed "real_self_less_add_one";

Goal "1r < 1r + 1r";
by (rtac real_self_less_add_one 1);
qed "real_one_less_two";

Goal "0r < 1r + 1r";
by (rtac ([real_zero_less_one,
          real_one_less_two] MRS real_less_trans) 1);
qed "real_zero_less_two";

Goal "1r + 1r ~= 0r";
by (rtac (real_zero_less_two RS real_not_refl2 RS not_sym) 1);
qed "real_two_not_zero";

Addsimps [real_two_not_zero];

Goal "x*rinv(1r + 1r) + x*rinv(1r + 1r) = x";
by (stac real_add_self 1);
by (full_simp_tac (simpset() addsimps [real_mult_assoc]) 1);
qed "real_sum_of_halves";

Goal "!!(x::real). [| 0r<z; x<y |] ==> x*z<y*z";       
by (rotate_tac 1 1);
by (dtac real_less_sum_gt_zero 1);
by (rtac real_sum_gt_zero_less 1);
by (dtac real_mult_order 1 THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_mult_distrib2,
    real_minus_mult_eq2 RS sym, real_mult_commute ]) 1);
qed "real_mult_less_mono1";

Goal "!!(y::real). [| 0r<z; x<y |] ==> z*x<z*y";       
by (asm_simp_tac (simpset() addsimps [real_mult_commute,real_mult_less_mono1]) 1);
qed "real_mult_less_mono2";

Goal "!!(x::real). [| 0r<z; x*z<y*z |] ==> x<y";
by (forw_inst_tac [("x","x*z")] (real_rinv_gt_zero 
                       RS real_mult_less_mono1) 1);
by (auto_tac (claset(),simpset() addsimps 
     [real_mult_assoc,real_not_refl2 RS not_sym]));
qed "real_mult_less_cancel1";

Goal "!!(x::real). [| 0r<z; z*x<z*y |] ==> x<y";
by (etac real_mult_less_cancel1 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult_commute]) 1);
qed "real_mult_less_cancel2";

Goal "0r < z ==> (x*z < y*z) = (x < y)";
by (blast_tac (claset() addIs [real_mult_less_mono1,
    real_mult_less_cancel1]) 1);
qed "real_mult_less_iff1";

Goal "0r < z ==> (z*x < z*y) = (x < y)";
by (blast_tac (claset() addIs [real_mult_less_mono2,
    real_mult_less_cancel2]) 1);
qed "real_mult_less_iff2";

Addsimps [real_mult_less_iff1,real_mult_less_iff2];

Goal "!!(x::real). [| 0r<=z; x<y |] ==> x*z<=y*z";
by (EVERY1 [rtac real_less_or_eq_imp_le, dtac real_le_imp_less_or_eq]);
by (auto_tac (claset() addIs [real_mult_less_mono1],simpset()));
qed "real_mult_le_less_mono1";

Goal "!!(x::real). [| 0r<=z; x<y |] ==> z*x<=z*y";
by (asm_simp_tac (simpset() addsimps [real_mult_commute,real_mult_le_less_mono1]) 1);
qed "real_mult_le_less_mono2";

Goal "!!x y (z::real). [| 0r<=z; x<=y |] ==> z*x<=z*y";
by (dres_inst_tac [("x","x")] real_le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [real_mult_le_less_mono2,real_le_refl],simpset()));
qed "real_mult_le_le_mono1";

Goal "!!(x::real). x < y ==> x < (x + y)*rinv(1r + 1r)";
by (dres_inst_tac [("C","x")] real_add_less_mono2 1);
by (dtac (real_add_self RS subst) 1);
by (dtac (real_zero_less_two RS real_rinv_gt_zero RS 
          real_mult_less_mono1) 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult_assoc]) 1);
qed "real_less_half_sum";

Goal "!!(x::real). x < y ==> (x + y)*rinv(1r + 1r) < y";
by (dres_inst_tac [("C","y")] real_add_less_mono1 1);
by (dtac (real_add_self RS subst) 1);
by (dtac (real_zero_less_two RS real_rinv_gt_zero RS 
          real_mult_less_mono1) 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult_assoc]) 1);
qed "real_gt_half_sum";

Goal "!!(x::real). x < y ==> EX r. x < r & r < y";
by (blast_tac (claset() addSIs [real_less_half_sum,real_gt_half_sum]) 1);
qed "real_dense";

Goal "(EX n. rinv(%%#n) < r) = (EX n. 1r < r * %%#n)";
by (Step_tac 1);
by (dres_inst_tac [("n1","n")] (real_nat_less_zero 
                       RS real_mult_less_mono1) 1);
by (dres_inst_tac [("n2","n")] (real_nat_less_zero RS 
        real_rinv_gt_zero RS real_mult_less_mono1) 2);
by (auto_tac (claset(),simpset() addsimps [(real_nat_less_zero RS 
    real_not_refl2 RS not_sym),real_mult_assoc]));
qed "real_nat_rinv_Ex_iff";

Goalw [real_nat_def] "(%%#n < %%#m) = (n < m)";
by Auto_tac;
qed "real_nat_less_iff";

Addsimps [real_nat_less_iff];

Goal "0r < u  ==> (u < rinv (%%#n)) = (%%#n < rinv(u))";
by (Step_tac 1);
by (res_inst_tac [("n2","n")] (real_nat_less_zero RS 
    real_rinv_gt_zero RS real_mult_less_cancel1) 1);
by (res_inst_tac [("x1","u")] ( real_rinv_gt_zero
   RS real_mult_less_cancel1) 2);
by (auto_tac (claset(),simpset() addsimps [real_nat_less_zero, 
    real_not_refl2 RS not_sym]));
by (res_inst_tac [("z","u")] real_mult_less_cancel2 1);
by (res_inst_tac [("n1","n")] (real_nat_less_zero RS 
    real_mult_less_cancel2) 3);
by (auto_tac (claset(),simpset() addsimps [real_nat_less_zero, 
    real_not_refl2 RS not_sym,real_mult_assoc RS sym]));
qed "real_nat_less_rinv_iff";

Goal "0r < u ==> (u = rinv(%%#n)) = (%%#n = rinv u)";
by (auto_tac (claset(),simpset() addsimps [real_rinv_rinv,
    real_nat_less_zero,real_not_refl2 RS not_sym]));
qed "real_nat_rinv_eq_iff";

(*
(*------------------------------------------------------------------
     lemmas about upper bounds and least upper bound
 ------------------------------------------------------------------*)
Goalw [real_ub_def] "[| real_ub u S; x : S |] ==> x <= u";
by Auto_tac;
qed "real_ubD";

*)
