(*  Title:       NSComplex.ML
    Author:      Jacques D. Fleuriot
    Copyhright:  2001  University of Edinburgh
    Description: Nonstandard Complex numbers
*)

Goalw [hcomplexrel_def]
   "((X,Y): hcomplexrel) = ({n. X n = Y n}: FreeUltrafilterNat)";
by (Fast_tac 1);
qed "hcomplexrel_iff";

Goalw [hcomplexrel_def] 
     "!!X. {n. X n = Y n}: FreeUltrafilterNat \
\      ==> (X,Y): hcomplexrel";
by (Fast_tac 1);
qed "hcomplexrelI";

Goalw [hcomplexrel_def]
  "p: hcomplexrel --> (EX X Y. \
\                 p = (X,Y) & {n. X n = Y n} : FreeUltrafilterNat)";
by (Fast_tac 1);
qed "hcomplexrelE_lemma";

val [major,minor] = goal thy
  "[| p: hcomplexrel;  \
\     !!X Y. [| p = (X,Y); {n. X n = Y n}: FreeUltrafilterNat\
\                    |] ==> Q |] ==> Q";
by (cut_facts_tac [major RS (hcomplexrelE_lemma RS mp)] 1);
by (REPEAT (eresolve_tac [asm_rl,exE,conjE,minor] 1));
qed "hcomplexrelE";

AddSIs [hcomplexrelI];
AddSEs [hcomplexrelE];

Goalw [hcomplexrel_def] "(x,x): hcomplexrel";
by (Auto_tac);
qed "hcomplexrel_refl";

Goalw [hcomplexrel_def] "(x,y): hcomplexrel ==> (y,x):hcomplexrel";
by (auto_tac (claset(), simpset() addsimps [eq_commute]));
qed "hcomplexrel_sym";

Goalw [hcomplexrel_def]
      "(x,y): hcomplexrel --> (y,z):hcomplexrel --> (x,z):hcomplexrel";
by (Auto_tac);
by (Ultra_tac 1);
qed_spec_mp "hcomplexrel_trans";

Goalw [equiv_def, refl_def, sym_def, trans_def]
    "equiv {x::nat=>complex. True} hcomplexrel";
by (auto_tac (claset() addSIs [hcomplexrel_refl] addSEs 
    [hcomplexrel_sym,hcomplexrel_trans] delrules [hcomplexrelI,hcomplexrelE],
    simpset()));
qed "equiv_hcomplexrel";

val equiv_hcomplexrel_iff =
    [TrueI, TrueI] MRS 
    ([CollectI, CollectI] MRS 
    (equiv_hcomplexrel RS eq_equiv_class_iff));

Goalw  [hcomplex_def,hcomplexrel_def,quotient_def] "hcomplexrel``{x}:hcomplex";
by (Blast_tac 1);
qed "hcomplexrel_in_hcomplex";

Goal "inj_on Abs_hcomplex hcomplex";
by (rtac inj_on_inverseI 1);
by (etac Abs_hcomplex_inverse 1);
qed "inj_on_Abs_hcomplex";

Addsimps [equiv_hcomplexrel_iff,inj_on_Abs_hcomplex RS inj_on_iff,
          hcomplexrel_iff, hcomplexrel_in_hcomplex, Abs_hcomplex_inverse];

Addsimps [equiv_hcomplexrel RS eq_equiv_class_iff];
val eq_hcomplexrelD = equiv_hcomplexrel RSN (2,eq_equiv_class);

Goal "inj(Rep_hcomplex)";
by (rtac inj_inverseI 1);
by (rtac Rep_hcomplex_inverse 1);
qed "inj_Rep_hcomplex";

Goalw [hcomplexrel_def] "x: hcomplexrel `` {x}";
by (Step_tac 1);
by (Auto_tac);
qed "lemma_hcomplexrel_refl";
Addsimps [lemma_hcomplexrel_refl];

Goalw [hcomplex_def] "{} ~: hcomplex";
by (auto_tac (claset() addSEs [quotientE],simpset()));
qed "hcomplex_empty_not_mem";
Addsimps [hcomplex_empty_not_mem];

Goal "Rep_hcomplex x ~= {}";
by (cut_inst_tac [("x","x")] Rep_hcomplex 1);
by (Auto_tac);
qed "Rep_hcomplex_nonempty";
Addsimps [Rep_hcomplex_nonempty];

val [prem] = goal thy
    "(!!x. z = Abs_hcomplex(hcomplexrel `` {x}) ==> P) ==> P";
by (res_inst_tac [("x1","z")] 
    (rewrite_rule [hcomplex_def] Rep_hcomplex RS quotientE) 1);
by (dres_inst_tac [("f","Abs_hcomplex")] arg_cong 1);
by (res_inst_tac [("x","x")] prem 1);
by (asm_full_simp_tac (simpset() addsimps [Rep_hcomplex_inverse]) 1);
qed "eq_Abs_hcomplex";

(*-----------------------------------------------------------------------*)
(* Properties of nonstandard real and imaginary parts                    *)
(*-----------------------------------------------------------------------*)

Goalw [hRe_def] 
     "hRe(Abs_hcomplex (hcomplexrel `` {X})) = \
\     Abs_hypreal(hyprel `` {%n. Re(X n)})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by (Auto_tac THEN Ultra_tac 1);
qed "hRe";

Goalw [hIm_def] 
     "hIm(Abs_hcomplex (hcomplexrel `` {X})) = \
\     Abs_hypreal(hyprel `` {%n. Im(X n)})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by (Auto_tac THEN Ultra_tac 1);
qed "hIm";

Goal "(w=z) = (hRe(w) = hRe(z) & hIm(w) = hIm(z))";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","w")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hRe,hIm,
    complex_Re_Im_cancel_iff]));
by (ALLGOALS(Ultra_tac));
qed "hcomplex_hRe_hIm_cancel_iff";

Goalw [hcomplex_zero_def] "hRe 0 = 0";
by (simp_tac (simpset() addsimps [hRe,hypreal_zero_num]) 1);
qed "hcomplex_hRe_zero";
Addsimps [hcomplex_hRe_zero];

Goalw [hcomplex_zero_def] "hIm 0 = 0";
by (simp_tac (simpset() addsimps [hIm,hypreal_zero_num]) 1);
qed "hcomplex_hIm_zero";
Addsimps [hcomplex_hIm_zero];

Goalw [hcomplex_one_def] "hRe 1 = 1";
by (simp_tac (simpset() addsimps [hRe,hypreal_one_num]) 1);
qed "hcomplex_hRe_one";
Addsimps [hcomplex_hRe_one];

Goalw [hcomplex_one_def] "hIm 1 = 0";
by (simp_tac (simpset() addsimps [hIm,hypreal_one_def,hypreal_zero_num]) 1);
qed "hcomplex_hIm_one";
Addsimps [hcomplex_hIm_one];

(*-----------------------------------------------------------------------*)
(*   hcomplex_of_complex: the injection from complex to hcomplex         *)
(* ----------------------------------------------------------------------*)

Goal "inj(hcomplex_of_complex)";
by (rtac injI 1 THEN rtac ccontr 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_complex_def]));
qed "inj_hcomplex_of_complex";

Goalw [iii_def,hcomplex_of_complex_def] "iii = hcomplex_of_complex ii";
by (Simp_tac 1);
qed "hcomplex_of_complex_i";

(*-----------------------------------------------------------------------*)
(*   Addition for nonstandard complex numbers: hcomplex_add              *)
(* ----------------------------------------------------------------------*)

Goalw [congruent2_def]
    "congruent2 hcomplexrel (%X Y. hcomplexrel `` {%n. X n + Y n})";
by (safe_tac (claset()));
by (ALLGOALS(Ultra_tac));
qed "hcomplex_add_congruent2";

Goalw [hcomplex_add_def]
  "Abs_hcomplex(hcomplexrel``{%n. X n}) + Abs_hcomplex(hcomplexrel``{%n. Y n}) = \
\  Abs_hcomplex(hcomplexrel``{%n. X n + Y n})";
by (res_inst_tac [("f","Abs_hcomplex")] arg_cong 1);
by Auto_tac;
by (Ultra_tac 1);
qed "hcomplex_add";

Goal "(z::hcomplex) + w = w + z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","w")] eq_Abs_hcomplex 1);
by (asm_simp_tac (simpset() addsimps (complex_add_ac @ [hcomplex_add])) 1);
qed "hcomplex_add_commute";

Goal "((z1::hcomplex) + z2) + z3 = z1 + (z2 + z3)";
by (res_inst_tac [("z","z1")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","z2")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","z3")] eq_Abs_hcomplex 1);
by (asm_simp_tac (simpset() addsimps [hcomplex_add,complex_add_assoc]) 1);
qed "hcomplex_add_assoc";

(*For AC rewriting*)
Goal "(x::hcomplex)+(y+z)=y+(x+z)";
by (rtac (hcomplex_add_commute RS trans) 1);
by (rtac (hcomplex_add_assoc RS trans) 1);
by (rtac (hcomplex_add_commute RS arg_cong) 1);
qed "hcomplex_add_left_commute";

(* hcomplex addition is an AC operator *)
val hcomplex_add_ac = [hcomplex_add_assoc,hcomplex_add_commute,
                      hcomplex_add_left_commute];

Goalw [hcomplex_zero_def] "(0::hcomplex) + z = z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (asm_full_simp_tac (simpset() addsimps 
    [hcomplex_add]) 1);
qed "hcomplex_add_zero_left";

Goal "z + (0::hcomplex) = z";
by (simp_tac (simpset() addsimps 
    [hcomplex_add_zero_left,hcomplex_add_commute]) 1);
qed "hcomplex_add_zero_right";
Addsimps [hcomplex_add_zero_left,hcomplex_add_zero_right];

Goal "hRe(x + y) = hRe(x) + hRe(y)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hRe,hcomplex_add,
    hypreal_add,complex_Re_add]));
qed "hRe_add";

Goal "hIm(x + y) = hIm(x) + hIm(y)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hIm,hcomplex_add,
    hypreal_add,complex_Im_add]));
qed "hIm_add";

(*-----------------------------------------------------------------------*)
(* hypreal_minus: additive inverse on nonstandard complex                *)
(* ----------------------------------------------------------------------*)

Goalw [congruent_def]
  "congruent hcomplexrel (%X. hcomplexrel `` {%n. - (X n)})";
by (safe_tac (claset()));
by (ALLGOALS(Ultra_tac));
qed "hcomplex_minus_congruent";

Goalw [hcomplex_minus_def]
  "- (Abs_hcomplex(hcomplexrel `` {%n. X n})) = \
\     Abs_hcomplex(hcomplexrel `` {%n. -(X n)})";
by (res_inst_tac [("f","Abs_hcomplex")] arg_cong 1);
by (Auto_tac THEN Ultra_tac 1);
qed "hcomplex_minus";

Goal "- (- z) = (z::hcomplex)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (asm_simp_tac (simpset() addsimps [hcomplex_minus]) 1);
qed "hcomplex_minus_minus";
Addsimps [hcomplex_minus_minus];

Goal "inj(%z::hcomplex. -z)";
by (rtac injI 1);
by (dres_inst_tac [("f","uminus")] arg_cong 1);
by (Asm_full_simp_tac 1);
qed "inj_hcomplex_minus";

Goalw [hcomplex_zero_def] "- 0 = (0::hcomplex)";
by (simp_tac (simpset() addsimps [hcomplex_minus]) 1);
qed "hcomplex_minus_zero";
Addsimps [hcomplex_minus_zero];

Goal "(-x = 0) = (x = (0::hcomplex))"; 
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_zero_def,
    hcomplex_minus] @ complex_add_ac));
qed "hcomplex_minus_zero_iff";
Addsimps [hcomplex_minus_zero_iff];

Goal "(0 = -x) = (x = (0::hcomplex))"; 
by (auto_tac (claset() addDs [sym],simpset()));
qed "hcomplex_minus_zero_iff2";
Addsimps [hcomplex_minus_zero_iff2];

Goal "(-x ~= 0) = (x ~= (0::hcomplex))"; 
by Auto_tac;
qed "hcomplex_minus_not_zero_iff";

Goal "z + - z = (0::hcomplex)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_add,hcomplex_minus,
    hcomplex_zero_def]));
qed "hcomplex_add_minus_right";
Addsimps [hcomplex_add_minus_right];

Goal "-z + z = (0::hcomplex)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_add,hcomplex_minus,
    hcomplex_zero_def]));
qed "hcomplex_add_minus_left";
Addsimps [hcomplex_add_minus_left];

Goal "z + (- z + w) = (w::hcomplex)";
by (simp_tac (simpset() addsimps [hcomplex_add_assoc RS sym]) 1);
qed "hcomplex_add_minus_cancel";

Goal "(-z) + (z + w) = (w::hcomplex)";
by (simp_tac (simpset() addsimps [hcomplex_add_assoc RS sym]) 1);
qed "hcomplex_minus_add_cancel";

Goal "hRe(-z) = - hRe(z)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hRe,hcomplex_minus,
    hypreal_minus,complex_Re_minus]));
qed "hRe_minus";

Goal "hIm(-z) = - hIm(z)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hIm,hcomplex_minus,
    hypreal_minus,complex_Im_minus]));
qed "hIm_minus";

Goalw [hcomplex_zero_def] 
      "x + y = (0::hcomplex) ==> x = -y";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_add,hcomplex_minus]));
by (ultra_tac (claset() addIs [complex_add_minus_eq_minus],simpset()) 1);
qed "hcomplex_add_minus_eq_minus";

Goal "-(x + y) = -x + -(y::hcomplex)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_add,hcomplex_minus]));
qed "hcomplex_minus_add_distrib";
Addsimps [hcomplex_minus_add_distrib];

Goal "((x::hcomplex) + y = x + z) = (y = z)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_add]));
qed "hcomplex_add_left_cancel";
AddIffs [hcomplex_add_left_cancel];

Goal "(y + (x::hcomplex)= z + x) = (y = z)";
by (simp_tac (simpset() addsimps [hcomplex_add_commute]) 1);
qed "hcomplex_add_right_cancel";
AddIffs [hcomplex_add_right_cancel];

Goal "((x::hcomplex) = y) = ((0::hcomplex) = x + - y)";
by (Step_tac 1);
by (res_inst_tac [("x1","-y")] 
      (hcomplex_add_right_cancel RS iffD1) 2);
by (Auto_tac);
qed "hcomplex_eq_minus_iff"; 

Goal "((x::hcomplex) = y) = (x + - y = (0::hcomplex))";
by (Step_tac 1);
by (res_inst_tac [("x1","-y")] 
      (hcomplex_add_right_cancel RS iffD1) 2);
by (Auto_tac);
qed "hcomplex_eq_minus_iff2"; 

(*-----------------------------------------------------------------------*)
(* Subraction for nonstandard complex numbers: hcomplex_diff             *)
(* ----------------------------------------------------------------------*)

Goalw [hcomplex_diff_def] 
  "Abs_hcomplex(hcomplexrel``{%n. X n}) - Abs_hcomplex(hcomplexrel``{%n. Y n}) = \
\  Abs_hcomplex(hcomplexrel``{%n. X n - Y n})";
by (auto_tac (claset(),simpset() addsimps [hcomplex_minus,hcomplex_add,
    complex_diff_def]));
qed "hcomplex_diff";

Goalw [hcomplex_diff_def] "(z::hcomplex) - z = (0::hcomplex)";
by (Simp_tac 1);
qed "hcomplex_diff_zero";
Addsimps [hcomplex_diff_zero];

Goal "(0::hcomplex) - x = -x";
by (simp_tac (simpset() addsimps [hcomplex_diff_def]) 1);
qed "hcomplex_diff_0";

Goal "x - (0::hcomplex) = x";
by (simp_tac (simpset() addsimps [hcomplex_diff_def]) 1);
qed "hcomplex_diff_0_right";

Goal "x - x = (0::hcomplex)";
by (simp_tac (simpset() addsimps [hcomplex_diff_def]) 1);
qed "hcomplex_diff_self";

Addsimps [hcomplex_diff_0, hcomplex_diff_0_right, hcomplex_diff_self];

Goal "((x::hcomplex) - y = z) = (x = z + y)";
by (auto_tac (claset(),simpset() addsimps [hcomplex_diff_def,hcomplex_add_assoc]));
qed "hcomplex_diff_eq_eq";

(*-----------------------------------------------------------------------*)
(* Multiplication for nonstandard complex numbers: hcomplex_mult         *)
(* ----------------------------------------------------------------------*)

Goalw [hcomplex_mult_def] 
  "Abs_hcomplex(hcomplexrel``{%n. X n}) * Abs_hcomplex(hcomplexrel``{%n. Y n}) = \
\  Abs_hcomplex(hcomplexrel``{%n. X n * Y n})";
by (res_inst_tac [("f","Abs_hcomplex")] arg_cong 1);
by (Auto_tac THEN Ultra_tac 1);
qed "hcomplex_mult";

Goal "(w::hcomplex) * z = z * w";
by (res_inst_tac [("z","w")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult,
    complex_mult_commute]));
qed "hcomplex_mult_commute";

Goal "((u::hcomplex) * v) * w = u * (v * w)";
by (res_inst_tac [("z","u")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","v")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","w")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult,
    complex_mult_assoc]));
qed "hcomplex_mult_assoc";

Goal "(x::hcomplex) * (y * z) = y * (x * z)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult,
    complex_mult_left_commute]));
qed "hcomplex_mult_left_commute";

val hcomplex_mult_ac = [hcomplex_mult_assoc,hcomplex_mult_commute,
                        hcomplex_mult_left_commute];

Goalw [hcomplex_one_def] "(1::hcomplex) * z = z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult]));
qed "hcomplex_mult_one_left";
Addsimps [hcomplex_mult_one_left];

Goal "z * (1::hcomplex) = z";
by (simp_tac (simpset() addsimps [hcomplex_mult_commute]) 1);
qed "hcomplex_mult_one_right";
Addsimps [hcomplex_mult_one_right];

Goalw [hcomplex_zero_def] "(0::hcomplex) * z = 0";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult]));
qed "hcomplex_mult_zero_left";
Addsimps [hcomplex_mult_zero_left];

Goal "z * (0::hcomplex) = 0";
by (simp_tac (simpset() addsimps [hcomplex_mult_commute]) 1);
qed "hcomplex_mult_zero_right";
Addsimps [hcomplex_mult_zero_right];

Goal "-(x * y) = -x * (y::hcomplex)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult,
    hcomplex_minus]));
qed "hcomplex_minus_mult_eq1";

Goal "-(x * y) = x * -(y::hcomplex)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult,
    hcomplex_minus]));
qed "hcomplex_minus_mult_eq2";

Addsimps [hcomplex_minus_mult_eq1 RS sym,hcomplex_minus_mult_eq2 RS sym];

Goal "- 1 * (z::hcomplex) = -z";
by (Simp_tac 1);
qed "hcomplex_mult_minus_one";
Addsimps [hcomplex_mult_minus_one];

Goal "(z::hcomplex) * - 1 = -z";
by (stac hcomplex_mult_commute 1);
by (Simp_tac 1);
qed "hcomplex_mult_minus_one_right";
Addsimps [hcomplex_mult_minus_one_right];

Goal "-x * -y = x * (y::hcomplex)";
by Auto_tac;
qed "hcomplex_minus_mult_cancel";
Addsimps [hcomplex_minus_mult_cancel];

Goal "-x * y = x * -(y::hcomplex)";
by Auto_tac;
qed "hcomplex_minus_mult_commute";

qed_goal "hcomplex_add_assoc_cong" thy
    "!!z. (z::hcomplex) + v = z' + v' ==> z + (v + w) = z' + (v' + w)"
 (fn _ => [(asm_simp_tac (simpset() addsimps [hcomplex_add_assoc RS sym]) 1)]);

qed_goal "hcomplex_add_assoc_swap" thy "(z::hcomplex) + (v + w) = v + (z + w)"
 (fn _ => [(REPEAT (ares_tac [hcomplex_add_commute RS hcomplex_add_assoc_cong] 1))]);

Goal "((z1::hcomplex) + z2) * w = (z1 * w) + (z2 * w)";
by (res_inst_tac [("z","z1")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","z2")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","w")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult,hcomplex_add,
    complex_add_mult_distrib]));
qed "hcomplex_add_mult_distrib";

Goal "(w::hcomplex) * (z1 + z2) = (w * z1) + (w * z2)";
by (res_inst_tac [("z1","z1 + z2")] (hcomplex_mult_commute RS ssubst) 1);
by (simp_tac (simpset() addsimps [hcomplex_add_mult_distrib]) 1);
by (simp_tac (simpset() addsimps [hcomplex_mult_commute]) 1);
qed "hcomplex_add_mult_distrib2";

Goalw [hcomplex_zero_def,hcomplex_one_def] "(0::hcomplex) ~= (1::hcomplex)";
by Auto_tac;
qed "hcomplex_zero_not_eq_one";
Addsimps [hcomplex_zero_not_eq_one];
Addsimps [hcomplex_zero_not_eq_one RS not_sym];

(*-----------------------------------------------------------------------*)
(* Inverse of nonstandard complex number                                 *)
(*-----------------------------------------------------------------------*)

Goalw [hcinv_def]
  "inverse (Abs_hcomplex(hcomplexrel `` {%n. X n})) = \
\     Abs_hcomplex(hcomplexrel `` {%n. inverse (X n)})";
by (res_inst_tac [("f","Abs_hcomplex")] arg_cong 1);
by (Auto_tac THEN Ultra_tac 1);
qed "hcomplex_inverse";

Goalw [hcomplex_zero_def] "inverse (0::hcomplex) = 0";
by (auto_tac (claset(),simpset() addsimps [hcomplex_inverse]));
qed "HCOMPLEX_INVERSE_ZERO";

Goal "a / (0::hcomplex) = 0";
by (simp_tac (simpset() addsimps [hcomplex_divide_def, HCOMPLEX_INVERSE_ZERO]) 1);
qed "HCOMPLEX_DIVISION_BY_ZERO";  (*NOT for adding to default simpset*)

fun hcomplex_div_undefined_case_tac s i =
  case_tac s i THEN 
  asm_simp_tac (simpset() addsimps [HCOMPLEX_DIVISION_BY_ZERO, HCOMPLEX_INVERSE_ZERO]) i;

Goalw [hcomplex_zero_def,hcomplex_one_def] 
      "z ~= (0::hcomplex) ==> inverse(z) * z = (1::hcomplex)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_inverse,hcomplex_mult]));
by (Ultra_tac 1);
by (rtac ccontr 1 THEN dtac (complex_mult_inv_left) 1);
by Auto_tac;
qed "hcomplex_mult_inv_left";
Addsimps [hcomplex_mult_inv_left];

Goal "z ~= (0::hcomplex) ==> z * inverse(z) = (1::hcomplex)";
by (auto_tac (claset() addIs [hcomplex_mult_commute RS subst],simpset()));
qed "hcomplex_mult_inv_right";
Addsimps [hcomplex_mult_inv_right];

Goal "(c::hcomplex) ~= (0::hcomplex) ==> (c*a=c*b) = (a=b)";
by Auto_tac;
by (dres_inst_tac [("f","%x. x*inverse c")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps hcomplex_mult_ac)  1);
qed "hcomplex_mult_left_cancel";
        
Goal "(c::hcomplex) ~= (0::hcomplex) ==> (a*c=b*c) = (a=b)";
by (Step_tac 1);
by (dres_inst_tac [("f","%x. x*inverse c")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps hcomplex_mult_ac)  1);
qed "hcomplex_mult_right_cancel";

Goal "z ~= (0::hcomplex) ==> inverse(z) ~= 0";
by (Step_tac 1);
by (ftac (hcomplex_mult_right_cancel RS iffD2) 1);
by (thin_tac "inverse z = 0" 2);
by (assume_tac 1 THEN Auto_tac);
qed "hcomplex_inverse_not_zero";
Addsimps [hcomplex_inverse_not_zero];

Goal "[| x ~= (0::hcomplex); y ~= 0 |] ==> x * y ~= 0";
by (Step_tac 1);
by (dres_inst_tac [("f","%z. inverse x*z")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [hcomplex_mult_assoc RS sym]) 1);
qed "hcomplex_mult_not_zero";

bind_thm ("hcomplex_mult_not_zeroE",hcomplex_mult_not_zero RS notE);

Goal "inverse(inverse x) = (x::hcomplex)";
by (hcomplex_div_undefined_case_tac "x = 0" 1);
by (res_inst_tac [("c1","inverse x")] (hcomplex_mult_right_cancel RS iffD1) 1);
by (etac hcomplex_inverse_not_zero 1);
by (auto_tac (claset() addDs [hcomplex_inverse_not_zero],simpset()));
qed "hcomplex_inverse_inverse";
Addsimps [hcomplex_inverse_inverse];

Goalw [hcomplex_one_def] "inverse((1::hcomplex)) = 1";
by (simp_tac (simpset() addsimps [hcomplex_inverse]) 1);
qed "hcomplex_inverse_one";
Addsimps [hcomplex_inverse_one];

Goal "inverse(-x) = -inverse(x::hcomplex)";
by (hcomplex_div_undefined_case_tac "x = 0" 1);
by (res_inst_tac [("c1","-x")] (hcomplex_mult_right_cancel RS iffD1) 1);
by (stac hcomplex_mult_inv_left 2);
by Auto_tac;
qed "hcomplex_minus_inverse";

Goal "inverse(x*y) = inverse x * inverse (y::hcomplex)";
by (hcomplex_div_undefined_case_tac "x = 0" 1);
by (hcomplex_div_undefined_case_tac "y = 0" 1);
by (res_inst_tac [("c1","x*y")] (hcomplex_mult_left_cancel RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult_not_zero]
    @ hcomplex_mult_ac));
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult_not_zero,
    hcomplex_mult_assoc RS sym]));
qed "hcomplex_inverse_distrib";

(*** division ***)

(* adding some of these theorems to simpset as for reals: not 100% convinced for some*)

Goal "(x::hcomplex) * (y/z) = (x*y)/z";
by (simp_tac (simpset() addsimps [hcomplex_divide_def, hcomplex_mult_assoc]) 1); 
qed "hcomplex_times_divide1_eq";

Goal "(y/z) * (x::hcomplex) = (y*x)/z";
by (simp_tac (simpset() addsimps [hcomplex_divide_def] @ hcomplex_mult_ac) 1); 
qed "hcomplex_times_divide2_eq";

Addsimps [hcomplex_times_divide1_eq, hcomplex_times_divide2_eq];

Goal "(x::hcomplex) / (y/z) = (x*z)/y";
by (simp_tac (simpset() addsimps [hcomplex_divide_def, hcomplex_inverse_distrib]@
                                  hcomplex_mult_ac) 1); 
qed "hcomplex_divide_divide1_eq";

Goal "((x::hcomplex) / y) / z = x/(y*z)";
by (simp_tac (simpset() addsimps [hcomplex_divide_def, hcomplex_inverse_distrib, 
                                  hcomplex_mult_assoc]) 1); 
qed "hcomplex_divide_divide2_eq";

Addsimps [hcomplex_divide_divide1_eq, hcomplex_divide_divide2_eq];

(** As with multiplication, pull minus signs OUT of the / operator **)

Goal "(-x) / (y::hcomplex) = - (x/y)";
by (simp_tac (simpset() addsimps [hcomplex_divide_def]) 1); 
qed "hcomplex_minus_divide_eq";
Addsimps [hcomplex_minus_divide_eq];

Goal "(x / -(y::hcomplex)) = - (x/y)";
by (simp_tac (simpset() addsimps [hcomplex_divide_def, hcomplex_minus_inverse]) 1); 
qed "hcomplex_divide_minus_eq";
Addsimps [hcomplex_divide_minus_eq];

Goal "(x+y)/(z::hcomplex) = x/z + y/z";
by (simp_tac (simpset() addsimps [hcomplex_divide_def, hcomplex_add_mult_distrib]) 1); 
qed "hcomplex_add_divide_distrib";

(*---------------------------------------------------------------------------*)
(* Embedding properties for hcomplex_of_hypreal map                          *)
(*---------------------------------------------------------------------------*)

Goalw [hcomplex_of_hypreal_def]
  "hcomplex_of_hypreal (Abs_hypreal(hyprel `` {%n. X n})) = \
\     Abs_hcomplex(hcomplexrel `` {%n. complex_of_real (X n)})";
by (res_inst_tac [("f","Abs_hcomplex")] arg_cong 1);
by Auto_tac;
by (Ultra_tac 1);
qed "hcomplex_of_hypreal";

Goal "inj hcomplex_of_hypreal";
by (rtac injI 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal]));
qed "inj_hcomplex_of_hypreal";

Goal "(hcomplex_of_hypreal x = hcomplex_of_hypreal y) = (x = y)";
by (auto_tac (claset() addDs [inj_hcomplex_of_hypreal RS injD],simpset()));
qed "hcomplex_of_hypreal_cancel_iff";
AddIffs [hcomplex_of_hypreal_cancel_iff];

Goal "hcomplex_of_hypreal(-x) = - hcomplex_of_hypreal x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    hcomplex_minus,hypreal_minus,complex_of_real_minus]));
qed "hcomplex_of_hypreal_minus";

Goal "hcomplex_of_hypreal(inverse x) = inverse(hcomplex_of_hypreal x)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    hypreal_inverse,hcomplex_inverse,complex_of_real_inverse]));
qed "hcomplex_of_hypreal_inverse";

Goal "hcomplex_of_hypreal x + hcomplex_of_hypreal y = \
\     hcomplex_of_hypreal (x + y)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    hypreal_add,hcomplex_add,complex_of_real_add]));
qed "hcomplex_of_hypreal_add";

Goalw [hcomplex_diff_def] 
     "hcomplex_of_hypreal x - hcomplex_of_hypreal y = \
\     hcomplex_of_hypreal (x - y)";
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal_minus 
    RS sym,hcomplex_of_hypreal_add,hypreal_diff_def]));
qed "hcomplex_of_hypreal_diff";

Goal "hcomplex_of_hypreal x * hcomplex_of_hypreal y = \
\     hcomplex_of_hypreal (x * y)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    hypreal_mult,hcomplex_mult,complex_of_real_mult]));
qed "hcomplex_of_hypreal_mult";

Goalw [hcomplex_divide_def]
  "hcomplex_of_hypreal x / hcomplex_of_hypreal y = hcomplex_of_hypreal(x/y)";
by (case_tac "y=0" 1);
by (asm_simp_tac (simpset() addsimps [HYPREAL_DIVISION_BY_ZERO,HYPREAL_INVERSE_ZERO,
    HCOMPLEX_INVERSE_ZERO]) 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal_mult,
    hcomplex_of_hypreal_inverse RS sym]));
by (simp_tac (simpset() addsimps [hypreal_divide_def]) 1);
qed "hcomplex_of_hypreal_divide";

Goalw [hcomplex_one_def]
      "hcomplex_of_hypreal 1 = 1";
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,hypreal_one_num]));
qed "hcomplex_of_hypreal_one";

Goalw [hcomplex_zero_def,hypreal_zero_def]
      "hcomplex_of_hypreal 0 = 0";
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal]));
qed "hcomplex_of_hypreal_zero";

Addsimps [hcomplex_of_hypreal_one,hcomplex_of_hypreal_zero,
          rename_numerals hcomplex_of_hypreal_zero];

Goal "hcomplex_of_hypreal (x ^ n) = (hcomplex_of_hypreal x) ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal_mult RS sym]));
qed "hcomplex_of_hypreal_pow";

Goal "hRe(hcomplex_of_hypreal z) = z";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,hRe]));
qed "hRe_hcomplex_of_hypreal";
Addsimps [hRe_hcomplex_of_hypreal];

Goal "hIm(hcomplex_of_hypreal z) = 0";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,hIm,
    hypreal_zero_num]));
qed "hIm_hcomplex_of_hypreal";
Addsimps [hIm_hcomplex_of_hypreal];

Goal "hcomplex_of_hypreal epsilon ~= 0";
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    epsilon_def,hcomplex_zero_def]));
qed "hcomplex_of_hypreal_epsilon_not_zero";
Addsimps [hcomplex_of_hypreal_epsilon_not_zero];

(*---------------------------------------------------------------------------*)
(*  Modulus (absolute value) of nonstandard complex number                   *) 
(*---------------------------------------------------------------------------*)

Goalw [hcmod_def]
  "hcmod (Abs_hcomplex(hcomplexrel `` {%n. X n})) = \
\     Abs_hypreal(hyprel `` {%n. cmod (X n)})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by (Auto_tac THEN Ultra_tac 1);
qed "hcmod";

Goalw [hcomplex_zero_def,hypreal_zero_def] 
      "hcmod(0) = 0";
by (auto_tac (claset(),simpset() addsimps [hcmod]));
qed "hcmod_zero";
Addsimps [hcmod_zero,rename_numerals hcmod_zero];

Goalw [hcomplex_one_def] 
      "hcmod(1) = 1";
by (auto_tac (claset(),simpset() addsimps [hcmod,hypreal_one_num]));
qed "hcmod_one";
Addsimps [hcmod_one];

Goal "hcmod(hcomplex_of_hypreal x) = abs x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,hcomplex_of_hypreal,
    hypreal_hrabs]));
qed "hcmod_hcomplex_of_hypreal";
Addsimps [hcmod_hcomplex_of_hypreal];

Goal "hcomplex_of_hypreal (abs x) = \
\     hcomplex_of_hypreal(hcmod(hcomplex_of_hypreal x))";
by (Simp_tac 1);
qed "hcomplex_of_hypreal_abs";

(*---------------------------------------------------------------------------*)
(*                   conjugation                                             *)
(*---------------------------------------------------------------------------*)

Goalw [hcnj_def]
  "hcnj (Abs_hcomplex(hcomplexrel `` {%n. X n})) = \
\     Abs_hcomplex(hcomplexrel `` {%n. cnj(X n)})";
by (res_inst_tac [("f","Abs_hcomplex")] arg_cong 1);
by (Auto_tac THEN Ultra_tac 1);
qed "hcnj";

Goal "inj hcnj";
by (rtac injI 1);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcnj]));
qed "inj_hcnj";

Goal "(hcnj x = hcnj y) = (x = y)";
by (auto_tac (claset() addDs [inj_hcnj RS injD],simpset()));
qed "hcomplex_hcnj_cancel_iff";
Addsimps [hcomplex_hcnj_cancel_iff];

Goal "hcnj (hcnj z) = z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcnj]));
qed "hcomplex_hcnj_hcnj";
Addsimps [hcomplex_hcnj_hcnj];

Goal "hcnj (hcomplex_of_hypreal x) = hcomplex_of_hypreal x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcnj,hcomplex_of_hypreal]));
qed "hcomplex_hcnj_hcomplex_of_hypreal";
Addsimps [hcomplex_hcnj_hcomplex_of_hypreal];

Goal "hcmod (hcnj z) = hcmod z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcnj,hcmod]));
qed "hcomplex_hmod_hcnj";
Addsimps [hcomplex_hmod_hcnj];

Goal "hcnj (-z) = - hcnj z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcnj,hcomplex_minus,
    complex_cnj_minus]));
qed "hcomplex_hcnj_minus";

Goal "hcnj(inverse z) = inverse(hcnj z)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcnj,hcomplex_inverse,
    complex_cnj_inverse]));
qed "hcomplex_hcnj_inverse";

Goal "hcnj(w + z) = hcnj(w) + hcnj(z)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","w")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcnj,hcomplex_add,
    complex_cnj_add]));
qed "hcomplex_hcnj_add";

Goal "hcnj(w - z) = hcnj(w) - hcnj(z)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","w")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcnj,hcomplex_diff,
    complex_cnj_diff]));
qed "hcomplex_hcnj_diff";

Goal "hcnj(w * z) = hcnj(w) * hcnj(z)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","w")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcnj,hcomplex_mult,
    complex_cnj_mult]));
qed "hcomplex_hcnj_mult";

Goalw [hcomplex_divide_def] "hcnj(w / z) = (hcnj w)/(hcnj z)";
by (simp_tac (simpset() addsimps [hcomplex_hcnj_mult,hcomplex_hcnj_inverse]) 1);
qed "hcomplex_hcnj_divide";

Goalw [hcomplex_one_def] "hcnj 1 = 1";
by (simp_tac (simpset() addsimps [hcnj]) 1);
qed "hcnj_one";
Addsimps [hcnj_one];

Goal "hcnj(z ^ n) = hcnj(z) ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_hcnj_mult]));
qed "hcomplex_hcnj_pow";

(* MOVE to NSComplexBin
Goal "z + hcnj z = \
\     hcomplex_of_hypreal (2 * hRe(z))";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),HOL_ss addsimps [hRe,hcnj,hcomplex_add,
    hypreal_mult,hcomplex_of_hypreal,complex_add_cnj]));
qed "hcomplex_add_hcnj";

Goal "z - hcnj z = \
\     hcomplex_of_hypreal (hypreal_of_real 2 * hIm(z)) * iii";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hIm,hcnj,hcomplex_diff,
    hypreal_of_real_def,hypreal_mult,hcomplex_of_hypreal,
    complex_diff_cnj,iii_def,hcomplex_mult]));
qed "hcomplex_diff_hcnj";
*)

Goalw [hcomplex_zero_def] 
      "hcnj 0 = 0";
by (auto_tac (claset(),simpset() addsimps [hcnj]));
qed "hcomplex_hcnj_zero";
Addsimps [hcomplex_hcnj_zero];

Goal "(hcnj z = 0) = (z = 0)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_zero_def,
    hcnj]));
qed "hcomplex_hcnj_zero_iff";
AddIffs [hcomplex_hcnj_zero_iff];

Goal "z * hcnj z = hcomplex_of_hypreal (hRe(z) ^ 2 + hIm(z) ^ 2)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcnj,hcomplex_mult,
    hcomplex_of_hypreal,hRe,hIm,hypreal_add,hypreal_mult,
    complex_mult_cnj,two_eq_Suc_Suc]));
qed "hcomplex_mult_hcnj";


(*---------------------------------------------------------------------------*)
(*  some algebra etc.                                                        *)
(*---------------------------------------------------------------------------*)

Goal "(x*y = (0::hcomplex)) = (x = 0 | y = 0)";
by Auto_tac;
by (auto_tac (claset() addIs [ccontr] addDs 
    [hcomplex_mult_not_zero],simpset()));
qed "hcomplex_mult_zero_iff";
Addsimps [hcomplex_mult_zero_iff];

Goal "(x + y = x) = (y = (0::hcomplex))";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_add,
    hcomplex_zero_def]));
qed "hcomplex_add_left_cancel_zero";
Addsimps [hcomplex_add_left_cancel_zero];

Goalw [hcomplex_diff_def] 
      "((z1::hcomplex) - z2) * w = (z1 * w) - (z2 * w)";
by (simp_tac (simpset() addsimps [hcomplex_add_mult_distrib]) 1);
qed "hcomplex_diff_mult_distrib";

Goalw [hcomplex_diff_def]
      "(w::hcomplex) * (z1 - z2) = (w * z1) - (w * z2)";
by (simp_tac (simpset() addsimps [hcomplex_add_mult_distrib2]) 1);
qed "hcomplex_diff_mult_distrib2";

(*---------------------------------------------------------------------------*)
(*  More theorems about hcmod                                                *)
(*---------------------------------------------------------------------------*)

Goal "(hcmod x = 0) = (x = 0)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,hcomplex_zero_def,
    hypreal_zero_num]));
qed "hcomplex_hcmod_eq_zero_cancel";
Addsimps [hcomplex_hcmod_eq_zero_cancel];

(* not proved already? strange! *)
Goalw [hypreal_le_def] 
      "(hypreal_of_nat n <= hypreal_of_nat m) = (n <= m)";
by Auto_tac;
qed "hypreal_of_nat_le_iff";
Addsimps [hypreal_of_nat_le_iff];

Goal "0 <= hypreal_of_nat n";
by (simp_tac (simpset() addsimps [hypreal_of_nat_zero RS sym]
    delsimps [hypreal_of_nat_zero]) 1);
qed "hypreal_of_nat_ge_zero";
Addsimps [hypreal_of_nat_ge_zero];

Addsimps [hypreal_of_nat_ge_zero RS hrabs_eqI1];

Goal "0 <= hypreal_of_hypnat n";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (asm_simp_tac (simpset() addsimps [hypreal_of_hypnat,
    hypreal_zero_num,hypreal_le]) 1);
qed "hypreal_of_hypnat_ge_zero";
Addsimps [hypreal_of_hypnat_ge_zero];

Addsimps [hypreal_of_hypnat_ge_zero RS hrabs_eqI1];

Goal "hcmod (hcomplex_of_hypreal(hypreal_of_nat n)) = hypreal_of_nat n";
by Auto_tac;
qed "hcmod_hcomplex_of_hypreal_of_nat";
Addsimps [hcmod_hcomplex_of_hypreal_of_nat];

Goal "hcmod (hcomplex_of_hypreal(hypreal_of_hypnat n)) = hypreal_of_hypnat n";
by Auto_tac;
qed "hcmod_hcomplex_of_hypreal_of_hypnat";
Addsimps [hcmod_hcomplex_of_hypreal_of_hypnat];

Goal "hcmod (-x) = hcmod(x)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,hcomplex_minus]));
qed "hcmod_minus";
Addsimps [hcmod_minus];

Goal "hcmod(z * hcnj(z)) = hcmod(z) ^ 2";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,hcomplex_mult,
    hcnj,hypreal_mult,complex_mod_mult_cnj,two_eq_Suc_Suc]));
qed "hcmod_mult_hcnj";

Goal "(0::hypreal) <= hcmod x";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,
    hypreal_zero_num,hypreal_le]));
qed "hcmod_ge_zero";
Addsimps [hcmod_ge_zero];

Goal "abs(hcmod x) = hcmod x";
by (auto_tac (claset() addIs [hrabs_eqI1],simpset()));
qed "hrabs_hcmod_cancel";
Addsimps [hrabs_hcmod_cancel];

Goal "hcmod(x*y) = hcmod(x) * hcmod(y)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,hcomplex_mult,
    hypreal_mult,complex_mod_mult]));
qed "hcmod_mult";

Goal "hcmod(x + y) ^ 2 = hcmod(x) ^ 2 + hcmod(y) ^ 2 + 2 * hRe(x * hcnj y)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,hcomplex_add,
    hypreal_mult,hRe,hcnj,hcomplex_mult,two_eq_Suc_Suc,
    realpow_two RS sym] delsimps [realpow_Suc]));
by (auto_tac (claset(),simpset() addsimps [two_eq_Suc_Suc RS sym,
    complex_mod_add_squared_eq,hypreal_add RS sym,hypreal_mult RS sym,
    symmetric hypreal_of_real_def]));
qed "hcmod_add_squared_eq";

Goal "hRe(x * hcnj y) <= hcmod(x * hcnj y)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,hcnj,
    hcomplex_mult,hRe,hypreal_le]));
qed "hcomplex_hRe_mult_hcnj_le_hcmod";
Addsimps [hcomplex_hRe_mult_hcnj_le_hcmod];

Goal "hRe(x * hcnj y) <= hcmod(x * y)";
by (cut_inst_tac [("x","x"),("y","y")] hcomplex_hRe_mult_hcnj_le_hcmod 1);
by (asm_full_simp_tac (simpset() addsimps [hcmod_mult]) 1);
qed "hcomplex_hRe_mult_hcnj_le_hcmod2";
Addsimps [hcomplex_hRe_mult_hcnj_le_hcmod2];

Goal "hcmod (x + y) ^ 2 <= (hcmod(x) + hcmod(y)) ^ 2";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,hcnj,
    hcomplex_add,hypreal_mult,hypreal_add,hypreal_le,
    realpow_two RS sym,two_eq_Suc_Suc] delsimps [realpow_Suc]));
by (simp_tac (simpset() addsimps [two_eq_Suc_Suc RS sym]) 1);
qed "hcmod_triangle_squared";
Addsimps [hcmod_triangle_squared];

Goal "hcmod (x + y) <= hcmod(x) + hcmod(y)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,
    hcomplex_add,hypreal_add,hypreal_le]));
qed "hcmod_triangle_ineq";
Addsimps [hcmod_triangle_ineq];

Goal "hcmod(b + a) - hcmod b <= hcmod a";
by (cut_inst_tac [("x1","b"),("y1","a"),("c","-hcmod b")]
   (hcmod_triangle_ineq RS add_right_mono) 1);
by (asm_full_simp_tac (simpset() addsimps hypreal_add_ac) 1);
qed "hcmod_triangle_ineq2";
Addsimps [hcmod_triangle_ineq2];

Goal "hcmod (x - y) = hcmod (y - x)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,
    hcomplex_diff,complex_mod_diff_commute]));
qed "hcmod_diff_commute";

Goal "[| hcmod x < r; hcmod y < s |] ==> hcmod (x + y) < r + s";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","s")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,hcomplex_add,
    hypreal_add,hypreal_less]));
by (ultra_tac (claset() addIs [complex_mod_add_less],simpset()) 1);
qed "hcmod_add_less";

Goal "[| hcmod x < r; hcmod y < s |] ==> hcmod (x * y) < r * s";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","y")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","s")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,hypreal_mult,
    hypreal_less,hcomplex_mult]));
by (ultra_tac (claset() addIs [complex_mod_mult_less],simpset()) 1);
qed "hcmod_mult_less";

goal NSComplex.thy "hcmod(a) - hcmod(b) <= hcmod(a + b)";
by (res_inst_tac [("z","a")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","b")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,hcomplex_add,
    hypreal_diff,hypreal_le]));
qed "hcmod_diff_ineq";
Addsimps [hcmod_diff_ineq];


(*---------------------------------------------------------------------------*)
(*                       a few nonlinear theorems                            *)
(*---------------------------------------------------------------------------*)

Goalw [hcpow_def] 
  "Abs_hcomplex(hcomplexrel``{%n. X n}) hcpow \
\  Abs_hypnat(hypnatrel``{%n. Y n}) = \
\  Abs_hcomplex(hcomplexrel``{%n. X n ^ Y n})";
by (res_inst_tac [("f","Abs_hcomplex")] arg_cong 1);
by (Auto_tac THEN Ultra_tac 1);
qed "hcpow";

Goal "hcomplex_of_hypreal (x pow n) = (hcomplex_of_hypreal x) hcpow n";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    hyperpow,hcpow,complex_of_real_pow]));
qed "hcomplex_of_hypreal_hyperpow";

Goal "hcmod(x ^ n) = hcmod(x) ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [hcmod_mult]));
qed "hcmod_hcomplexpow";

Goal "hcmod(x hcpow n) = hcmod(x) pow n";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hcpow,hyperpow,
    hcmod,complex_mod_complexpow]));
qed "hcmod_hcpow";

Goal "(-x::hcomplex) ^ n = (if even n then (x ^ n) else -(x ^ n))";
by (induct_tac "n" 1);
by Auto_tac;
qed "hcomplexpow_minus";

Goal "(-x::hcomplex) hcpow n = \
\     (if ( *pNat* even) n then (x hcpow n) else -(x hcpow n))";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hcpow,hyperpow,starPNat,
    hcomplex_minus]));
by (ALLGOALS(ultra_tac (claset(),simpset() addsimps [complexpow_minus])));
qed "hcpow_minus";

Goal "inverse(-x) = - inverse (x::hcomplex)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_inverse,hcomplex_minus,
    complex_inverse_minus]));
qed "hccomplex_inverse_minus";

Goalw [hcomplex_divide_def] "x / (1::hcomplex) = x";
by (Simp_tac 1);
qed "hcomplex_div_one";
Addsimps [hcomplex_div_one];

Goal "hcmod(inverse x) = inverse(hcmod x)"; 
by (hcomplex_div_undefined_case_tac "x = 0" 1);
by (res_inst_tac [("c1","hcmod x")] (hypreal_mult_left_cancel RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [hcmod_mult RS sym]));
qed "hcmod_hcomplex_inverse";

Goalw [hcomplex_divide_def,hypreal_divide_def] 
      "hcmod(x/y) = hcmod(x)/(hcmod y)";
by (auto_tac (claset(),simpset() addsimps [hcmod_mult,
    hcmod_hcomplex_inverse]));
qed "hcmod_divide";

Goalw [hcomplex_divide_def]  
      "inverse(x/y) = y/(x::hcomplex)";
by (auto_tac (claset(),simpset() addsimps [hcomplex_inverse_distrib,
    hcomplex_mult_commute]));
qed "hcomplex_inverse_divide";
Addsimps [hcomplex_inverse_divide];

Goal "((r::hcomplex) * s) ^ n = (r ^ n) * (s ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps hcomplex_mult_ac));
qed "hcomplexpow_mult";

Goal "((r::hcomplex) * s) hcpow n = (r hcpow n) * (s hcpow n)";
by (res_inst_tac [("z","r")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","s")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hcpow,hypreal_mult,
    hcomplex_mult,complexpow_mult]));
qed "hcpow_mult";

Goal "(0::hcomplex) ^ (Suc n) = 0";
by (Auto_tac);
qed "hcomplexpow_zero";
Addsimps [hcomplexpow_zero];

Goalw [hcomplex_zero_def,hypnat_one_def]
   "0 hcpow (n + 1) = 0";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hcpow,hypnat_add]));
qed "hcpow_zero";
Addsimps [hcpow_zero];

Goalw [hSuc_def]
   "0 hcpow (hSuc n) = 0";
by (Simp_tac 1);
qed "hcpow_zero2";
Addsimps [hcpow_zero2];

Goal "r ~= (0::hcomplex) --> r ^ n ~= 0";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps 
    [hcomplex_mult_not_zero]));
qed_spec_mp "hcomplexpow_not_zero";
Addsimps [hcomplexpow_not_zero];
AddIs [hcomplexpow_not_zero];

Goal "r ~= 0 ==> r hcpow n ~= (0::hcomplex)";
by (res_inst_tac [("z","r")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hcpow,
    hcomplex_zero_def]));
by (ultra_tac (claset() addDs [complexpow_zero_zero],simpset()) 1);
qed "hcpow_not_zero";
Addsimps [hcpow_not_zero];
AddIs [hcpow_not_zero];

Goal "r ^ n = (0::hcomplex) ==> r = 0";
by (blast_tac (claset() addIs [ccontr] 
    addDs [hcomplexpow_not_zero]) 1);
qed "hcomplexpow_zero_zero";

Goal "r hcpow n = (0::hcomplex) ==> r = 0";
by (blast_tac (claset() addIs [ccontr] 
    addDs [hcpow_not_zero]) 1);
qed "hcpow_zero_zero";

Goalw [iii_def] "iii * iii = - 1";
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult,
    hcomplex_one_def,hcomplex_minus]));
qed "hcomplex_i_mult_eq";
Addsimps [hcomplex_i_mult_eq];

Goal "iii ^ 2 = - 1";
by (simp_tac (simpset() addsimps [two_eq_Suc_Suc]) 1);
qed "hcomplexpow_i_squared";
Addsimps [hcomplexpow_i_squared];

Goalw [iii_def,hcomplex_zero_def] "iii ~= 0";
by Auto_tac;
qed "hcomplex_i_not_zero";
Addsimps [hcomplex_i_not_zero];

Goal "x * y ~= (0::hcomplex) ==> x ~= 0";
by Auto_tac;
qed "hcomplex_mult_eq_zero_cancel1";

Goal "x * y ~= (0::hcomplex) ==> y ~= 0";
by Auto_tac;
qed "hcomplex_mult_eq_zero_cancel2";

Goal "(x * y ~= (0::hcomplex)) = (x ~= 0 & y ~= 0)";
by Auto_tac;
qed "hcomplex_mult_not_eq_zero_iff";
AddIffs [hcomplex_mult_not_eq_zero_iff];

Goalw [hcomplex_divide_def,complex_divide_def] 
  "Abs_hcomplex(hcomplexrel``{%n. X n}) / Abs_hcomplex(hcomplexrel``{%n. Y n}) = \
\  Abs_hcomplex(hcomplexrel``{%n. X n / Y n})";
by (auto_tac (claset(),simpset() addsimps [hcomplex_inverse,hcomplex_mult]));
qed "hcomplex_divide";

(*---------------------------------------------------------------------------*)
(*                             hsgn                                          *)
(*---------------------------------------------------------------------------*)

Goalw [hsgn_def]
  "hsgn (Abs_hcomplex(hcomplexrel `` {%n. X n})) = \
\     Abs_hcomplex(hcomplexrel `` {%n. sgn (X n)})";
by (res_inst_tac [("f","Abs_hcomplex")] arg_cong 1);
by (Auto_tac THEN Ultra_tac 1);
qed "hsgn";

Addsimps [rename_numerals sgn_zero];
Goalw [hcomplex_zero_def] "hsgn 0 = 0";
by (simp_tac (simpset() addsimps [hsgn]) 1);
qed "hsgn_zero";
Addsimps[hsgn_zero];

Addsimps [rename_numerals sgn_one];

Goalw [hcomplex_one_def] "hsgn 1 = 1";
by (simp_tac (simpset() addsimps [hsgn]) 1);
qed "hsgn_one";
Addsimps[hsgn_one];

Goal "hsgn (-z) = - hsgn(z)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hsgn,hcomplex_minus,
    sgn_minus]));
qed "hsgn_minus";

Goal "hsgn z = z / hcomplex_of_hypreal (hcmod z)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hsgn,hcomplex_divide,
    hcomplex_of_hypreal,hcmod,sgn_eq]));
qed "hsgn_eq";

Goal "(EX (x::hypreal) y. P x y) = \
\     (EX f g. P (Abs_hypreal(hyprel `` {f})) (Abs_hypreal(hyprel `` {g})))";
by Auto_tac;
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by Auto_tac;
qed "lemma_hypreal_P_EX2";

Goal "ALL (n::nat). EX x y. (z n) = complex_of_real(x) + ii * complex_of_real(y)";
by (blast_tac (claset() addIs [complex_split]) 1);
qed "complex_split2";

(* Interesting proof! *)
Goal "EX x y. z = hcomplex_of_hypreal(x) + iii * hcomplex_of_hypreal(y)";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [lemma_hypreal_P_EX2,
    hcomplex_of_hypreal,iii_def,hcomplex_add,hcomplex_mult]));
by (cut_inst_tac [("z","x")] complex_split2 1);
by (REPEAT(dtac choice 1 THEN Step_tac 1));
by (res_inst_tac [("x","f")] exI 1);
by (res_inst_tac [("x","fa")] exI 1);
by Auto_tac;
qed "hcomplex_split";

Goal "hRe(hcomplex_of_hypreal(x) + iii * hcomplex_of_hypreal(y)) = x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hRe,iii_def,hcomplex_add,
    hcomplex_mult,hcomplex_of_hypreal]));
qed "hRe_hcomplex_i";
Addsimps [hRe_hcomplex_i];

Goal "hIm(hcomplex_of_hypreal(x) + iii * hcomplex_of_hypreal(y)) = y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hIm,iii_def,hcomplex_add,
    hcomplex_mult,hcomplex_of_hypreal]));
qed "hIm_hcomplex_i";
Addsimps [hIm_hcomplex_i];

Goal "hcmod (hcomplex_of_hypreal(x) + iii * hcomplex_of_hypreal(y)) = \
\     ( *f* sqrt) (x ^ 2 + y ^ 2)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    iii_def,hcomplex_add,hcomplex_mult,starfun,hypreal_mult,
    hypreal_add,hcmod,cmod_i,two_eq_Suc_Suc]));
qed "hcmod_i";

Goalw [iii_def] 
     "hcomplex_of_hypreal xa + iii * hcomplex_of_hypreal ya = \
\     hcomplex_of_hypreal xb + iii * hcomplex_of_hypreal yb \
\      ==> xa = xb";
by (res_inst_tac [("z","xa")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","ya")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","xb")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","yb")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult,hcomplex_add,
    hcomplex_of_hypreal]));
by (Ultra_tac 1);
qed "hcomplex_eq_hRe_eq";

Goalw [iii_def] 
     "hcomplex_of_hypreal xa + iii * hcomplex_of_hypreal ya = \
\     hcomplex_of_hypreal xb + iii * hcomplex_of_hypreal yb \
\      ==> ya = yb";
by (res_inst_tac [("z","xa")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","ya")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","xb")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","yb")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult,hcomplex_add,
    hcomplex_of_hypreal]));
by (Ultra_tac 1);
qed "hcomplex_eq_hIm_eq";

Goal "(hcomplex_of_hypreal xa + iii * hcomplex_of_hypreal ya = \
\      hcomplex_of_hypreal xb + iii * hcomplex_of_hypreal yb) = \
\     ((xa = xb) & (ya = yb))";
by (auto_tac (claset() addIs [hcomplex_eq_hIm_eq,hcomplex_eq_hRe_eq],simpset()));
qed "hcomplex_eq_cancel_iff";
Addsimps [hcomplex_eq_cancel_iff];

Goal "(hcomplex_of_hypreal xa + hcomplex_of_hypreal ya * iii = \
\      hcomplex_of_hypreal xb + hcomplex_of_hypreal yb * iii ) = ((xa = xb) & (ya = yb))";
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult_commute]));
qed "hcomplex_eq_cancel_iffA";
AddIffs [hcomplex_eq_cancel_iffA];

Goal "(hcomplex_of_hypreal xa + hcomplex_of_hypreal ya * iii = \
\      hcomplex_of_hypreal xb + iii * hcomplex_of_hypreal yb) = ((xa = xb) & (ya = yb))";
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult_commute]));
qed "hcomplex_eq_cancel_iffB";
AddIffs [hcomplex_eq_cancel_iffB];

Goal "(hcomplex_of_hypreal xa + iii * hcomplex_of_hypreal ya  = \
\      hcomplex_of_hypreal xb + hcomplex_of_hypreal yb * iii) = ((xa = xb) & (ya = yb))";
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult_commute]));
qed "hcomplex_eq_cancel_iffC";
AddIffs [hcomplex_eq_cancel_iffC];

Goal"(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y = \
\     hcomplex_of_hypreal xa) = (x = xa & y = 0)";
by (cut_inst_tac [("xa","x"),("ya","y"),("xb","xa"),("yb","0")]  
    hcomplex_eq_cancel_iff 1);
by (asm_full_simp_tac (simpset() delsimps [hcomplex_eq_cancel_iff]) 1);
qed "hcomplex_eq_cancel_iff2";
Addsimps [hcomplex_eq_cancel_iff2];

Goal"(hcomplex_of_hypreal x + hcomplex_of_hypreal y * iii = \
\     hcomplex_of_hypreal xa) = (x = xa & y = 0)";
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult_commute]));
qed "hcomplex_eq_cancel_iff2a";
Addsimps [hcomplex_eq_cancel_iff2a];

Goal "(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y = \
\     iii * hcomplex_of_hypreal ya) = (x = 0 & y = ya)";
by (cut_inst_tac [("xa","x"),("ya","y"),("xb","0"),("yb","ya")]  
    hcomplex_eq_cancel_iff 1);
by (asm_full_simp_tac (simpset() delsimps [hcomplex_eq_cancel_iff]) 1);
qed "hcomplex_eq_cancel_iff3";
Addsimps [hcomplex_eq_cancel_iff3];

Goal "(hcomplex_of_hypreal x + hcomplex_of_hypreal y * iii = \
\     iii * hcomplex_of_hypreal ya) = (x = 0 & y = ya)";
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult_commute]));
qed "hcomplex_eq_cancel_iff3a";
Addsimps [hcomplex_eq_cancel_iff3a];

Goalw [iii_def] 
     "hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y = 0 \
\     ==> x = 0";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    hcomplex_add,hcomplex_mult,hcomplex_zero_def,hypreal_zero_num]));
by (ultra_tac (claset(),simpset() addsimps [complex_split_Re_zero]) 1);
qed "hcomplex_split_hRe_zero";

Goalw [iii_def] 
     "hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y = 0 \
\     ==> y = 0";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    hcomplex_add,hcomplex_mult,hcomplex_zero_def,hypreal_zero_num]));
by (ultra_tac (claset(),simpset() addsimps [complex_split_Im_zero]) 1);
qed "hcomplex_split_hIm_zero";

Goal "hRe(hsgn z) = hRe(z)/hcmod z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hsgn,hcmod,hRe,hypreal_divide]));
qed "hRe_hsgn";
Addsimps [hRe_hsgn];

Goal "hIm(hsgn z) = hIm(z)/hcmod z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hsgn,hcmod,hIm,hypreal_divide]));
qed "hIm_hsgn";
Addsimps [hIm_hsgn];

Goal "(x*x + y*y = 0) = ((x::real) = 0 & y = 0)";
by (auto_tac (claset() addIs [real_sum_squares_cancel],simpset()));
qed "real_two_squares_add_zero_iff";
Addsimps [real_two_squares_add_zero_iff];

Goal "inverse(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y) = \
\     hcomplex_of_hypreal(x/(x ^ 2 + y ^ 2)) - \
\     iii * hcomplex_of_hypreal(y/(x ^ 2 + y ^ 2))";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    hcomplex_mult,hcomplex_add,iii_def,starfun,hypreal_mult,
    hypreal_add,hcomplex_inverse,hypreal_divide,hcomplex_diff,
    complex_inverse_complex_split,two_eq_Suc_Suc]));
qed "hcomplex_inverse_complex_split";

Goalw [iii_def]
    "hRe (iii * hcomplex_of_hypreal y) = 0";
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    hcomplex_mult,hRe,hypreal_zero_num]));
qed "hRe_mult_i_eq";
Addsimps [hRe_mult_i_eq];

Goalw [iii_def]
    "hIm (iii * hcomplex_of_hypreal y) = y";
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    hcomplex_mult,hIm,hypreal_zero_num]));
qed "hIm_mult_i_eq";
Addsimps [hIm_mult_i_eq];

Goal "hcmod (iii * hcomplex_of_hypreal y) = abs y";
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    hcmod,hypreal_hrabs,iii_def,hcomplex_mult]));
qed "hcmod_mult_i";
Addsimps [hcmod_mult_i];

Goal "hcmod (hcomplex_of_hypreal y * iii) = abs y";
by (auto_tac (claset(),simpset() addsimps [hcomplex_mult_commute]));
qed "hcmod_mult_i2";
Addsimps [hcmod_mult_i2];

(*---------------------------------------------------------------------------*)
(*  harg                                                                     *)
(*---------------------------------------------------------------------------*)

Goalw [harg_def]
  "harg (Abs_hcomplex(hcomplexrel `` {%n. X n})) = \
\     Abs_hypreal(hyprel `` {%n. arg (X n)})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by (Auto_tac THEN Ultra_tac 1);
qed "harg";

Goal "0 < y ==> ( *f* cos) (harg(iii * hcomplex_of_hypreal y)) = 0";
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    iii_def,hcomplex_mult,hypreal_zero_num,hypreal_less,starfun,
    harg]));
by (Ultra_tac 1);
qed "cos_harg_i_mult_zero";
Addsimps [cos_harg_i_mult_zero];

Goal "y < 0 ==> ( *f* cos) (harg(iii * hcomplex_of_hypreal y)) = 0";
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    iii_def,hcomplex_mult,hypreal_zero_num,hypreal_less,starfun,
    harg]));
by (Ultra_tac 1);
qed "cos_harg_i_mult_zero2";
Addsimps [cos_harg_i_mult_zero2];

Goal "(hcomplex_of_hypreal y ~= 0) = (y ~= 0)";
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    hypreal_zero_num,hcomplex_zero_def]));
qed "hcomplex_of_hypreal_not_zero_iff";
Addsimps [hcomplex_of_hypreal_not_zero_iff];

Goal "(hcomplex_of_hypreal y = 0) = (y = 0)";
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    hypreal_zero_num,hcomplex_zero_def]));
qed "hcomplex_of_hypreal_zero_iff";
Addsimps [hcomplex_of_hypreal_zero_iff];

Goal "y ~= 0 ==> ( *f* cos) (harg(iii * hcomplex_of_hypreal y)) = 0";
by (cut_inst_tac [("x","y"),("y","0")] hypreal_linear 1);
by Auto_tac;
qed "cos_harg_i_mult_zero3";
Addsimps [cos_harg_i_mult_zero3];

(*---------------------------------------------------------------------------*)
(* Polar form for nonstandard complex numbers                                 *) 
(*---------------------------------------------------------------------------*)

Goal "ALL n. EX r a. (z n) = complex_of_real r * \
\     (complex_of_real(cos a) + ii * complex_of_real(sin a))";
by (blast_tac (claset() addIs [complex_split_polar]) 1);
qed "complex_split_polar2";

Goal 
  "EX r a. z = hcomplex_of_hypreal r * \
\  (hcomplex_of_hypreal(( *f* cos) a) + iii * hcomplex_of_hypreal(( *f* sin) a))";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [lemma_hypreal_P_EX2,
    hcomplex_of_hypreal,iii_def,starfun,hcomplex_add,hcomplex_mult]));
by (cut_inst_tac [("z","x")] complex_split_polar2 1);
by (REPEAT(dtac choice 1 THEN Step_tac 1));
by (res_inst_tac [("x","f")] exI 1);
by (res_inst_tac [("x","fa")] exI 1);
by Auto_tac;
qed "hcomplex_split_polar";

Goalw [hcis_def]
  "hcis (Abs_hypreal(hyprel `` {%n. X n})) = \
\     Abs_hcomplex(hcomplexrel `` {%n. cis (X n)})";
by (res_inst_tac [("f","Abs_hcomplex")] arg_cong 1);
by Auto_tac;
by (Ultra_tac 1);
qed "hcis";

Goal 
   "hcis a = \
\   (hcomplex_of_hypreal(( *f* cos) a) + \
\   iii * hcomplex_of_hypreal(( *f* sin) a))";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun, hcis,
    hcomplex_of_hypreal,iii_def,hcomplex_mult,hcomplex_add,
    cis_def]));
qed "hcis_eq";

Goalw [hrcis_def]
  "hrcis (Abs_hypreal(hyprel `` {%n. X n})) (Abs_hypreal(hyprel `` {%n. Y n})) = \
\     Abs_hcomplex(hcomplexrel `` {%n. rcis (X n) (Y n)})";
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,hcomplex_mult,
    hcis,rcis_def]));
qed "hrcis";

Goal "EX r a. z = hrcis r a";
by (simp_tac (simpset() addsimps [hrcis_def,hcis_eq]) 1);
by (rtac hcomplex_split_polar 1);
qed "hrcis_Ex";

Goal "hRe(hcomplex_of_hypreal r * \
\     (hcomplex_of_hypreal(( *f* cos) a) + \
\      iii * hcomplex_of_hypreal(( *f* sin) a))) = r * ( *f* cos) a";
by (auto_tac (claset(),simpset() addsimps [hcomplex_add_mult_distrib2,
    hcomplex_of_hypreal_mult] @ hcomplex_mult_ac));
qed "hRe_hcomplex_polar";
Addsimps [hRe_hcomplex_polar];

Goalw [hrcis_def] "hRe(hrcis r a) = r * ( *f* cos) a";
by (auto_tac (claset(),simpset() addsimps [hcis_eq]));
qed "hRe_hrcis";
Addsimps [hRe_hrcis];

Goal "hIm(hcomplex_of_hypreal r * \
\     (hcomplex_of_hypreal(( *f* cos) a) + \
\      iii * hcomplex_of_hypreal(( *f* sin) a))) = r * ( *f* sin) a";
by (auto_tac (claset(),simpset() addsimps [hcomplex_add_mult_distrib2,
    hcomplex_of_hypreal_mult] @ hcomplex_mult_ac));
qed "hIm_hcomplex_polar";
Addsimps [hIm_hcomplex_polar];

Goalw [hrcis_def] "hIm(hrcis r a) = r * ( *f* sin) a";
by (auto_tac (claset(),simpset() addsimps [hcis_eq]));
qed "hIm_hrcis";
Addsimps [hIm_hrcis];

Goal "hcmod (hcomplex_of_hypreal r * \
\     (hcomplex_of_hypreal(( *f* cos) a) + \
\      iii * hcomplex_of_hypreal(( *f* sin) a))) = abs r";
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [iii_def,starfun,
    hcomplex_of_hypreal,hcomplex_mult,hcmod,hcomplex_add,
    hypreal_hrabs]));
qed "hcmod_complex_polar";
Addsimps [hcmod_complex_polar];

Goalw [hrcis_def] "hcmod(hrcis r a) = abs r";
by (auto_tac (claset(),simpset() addsimps [hcis_eq]));
qed "hcmod_hrcis";
Addsimps [hcmod_hrcis];

(*---------------------------------------------------------------------------*)
(*  (r1 * hrcis a) * (r2 * hrcis b) = r1 * r2 * hrcis (a + b)                *) 
(*---------------------------------------------------------------------------*)

Goalw [hrcis_def] "hcis a = hrcis 1 a";
by (Simp_tac 1);
qed "hcis_hrcis_eq";
Addsimps [hcis_hrcis_eq RS sym];

Goalw [hrcis_def] 
  "hrcis r1 a * hrcis r2 b = hrcis (r1*r2) (a + b)";
by (res_inst_tac [("z","r1")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","r2")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","b")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hrcis,hcis,
    hypreal_add,hypreal_mult,hcomplex_of_hypreal,
    hcomplex_mult,cis_mult RS sym,complex_of_real_mult
    RS sym] addsimps complex_mult_ac));
qed "hrcis_mult";

Goal "hcis a * hcis b = hcis (a + b)";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","b")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcis,hcomplex_mult,
    hypreal_add,cis_mult]));
qed "hcis_mult";

Goalw [hcomplex_one_def] 
  "hcis 0 = 1";
by (auto_tac (claset(),simpset() addsimps [hcis,hypreal_zero_num]));
qed "hcis_zero";
Addsimps [hcis_zero];

Goalw [hcomplex_zero_def] 
  "hrcis 0 a = 0";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hrcis,hypreal_zero_num]));
qed "hrcis_zero_mod";
Addsimps [hrcis_zero_mod];

Goal "hrcis r 0 = hcomplex_of_hypreal r";
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hrcis,
    hypreal_zero_num,hcomplex_of_hypreal]));
qed "hrcis_zero_arg";
Addsimps [hrcis_zero_arg];

Goal "iii * (iii * x) = - x";
by (simp_tac (simpset() addsimps [hcomplex_mult_assoc RS sym]) 1);
qed "hcomplex_i_mult_minus";
Addsimps [hcomplex_i_mult_minus];

Goal "iii * iii * x = - x";
by (Simp_tac 1);
qed "hcomplex_i_mult_minus2";
Addsimps [hcomplex_i_mult_minus2];

(* Move to one of the hyperreal theories *)
Goal "hypreal_of_nat m = Abs_hypreal(hyprel `` {%n. real m})";
by (induct_tac "m" 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_zero_def,
    hypreal_of_nat_Suc,hypreal_zero_num,
    hypreal_one_num,hypreal_add,real_of_nat_Suc]));
qed "hypreal_of_nat";

Goal
   "hcis (hypreal_of_nat (Suc n) * a) = hcis a * hcis (hypreal_of_nat n * a)";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_of_nat,hcis,
    hypreal_mult,hcomplex_mult,cis_real_of_nat_Suc_mult]));
qed "hcis_hypreal_of_nat_Suc_mult";

Goal "(hcis a) ^ n = hcis (hypreal_of_nat n * a)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [hcis_hypreal_of_nat_Suc_mult]));
qed "NSDeMoivre";

Goal "hcis (hypreal_of_hypnat (n + 1) * a) = \
\     hcis a * hcis (hypreal_of_hypnat n * a)";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hcis,hypreal_of_hypnat,
    hypnat_add,hypnat_one_def,hypreal_mult,hcomplex_mult,
    cis_real_of_nat_Suc_mult]));
qed "hcis_hypreal_of_hypnat_Suc_mult";

Goal "(hcis a) hcpow n = hcis (hypreal_of_hypnat n * a)";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hcis,hypreal_of_hypnat,
    hypreal_mult,hcpow,DeMoivre]));
qed "NSDeMoivre_ext";

Goalw [hrcis_def] 
  "(hrcis r a) ^ n = hrcis (r ^ n) (hypreal_of_nat n * a)";
by (auto_tac (claset(),simpset() addsimps [hcomplexpow_mult,
    NSDeMoivre,hcomplex_of_hypreal_pow]));
qed "DeMoivre2";

Goalw [hrcis_def] 
  "(hrcis r a) hcpow n = hrcis (r pow n) (hypreal_of_hypnat n * a)";
by (auto_tac (claset(),simpset() addsimps [hcpow_mult,
    NSDeMoivre_ext,hcomplex_of_hypreal_hyperpow]));
qed "DeMoivre2_ext";

Goal "inverse(hcis a) = hcis (-a)";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_inverse,hcis,hypreal_minus]));
qed "hcis_inverse";
Addsimps [hcis_inverse];

Goal "inverse(hrcis r a) = hrcis (inverse r) (-a)";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_inverse,hrcis,hypreal_minus,
    hypreal_inverse,rcis_inverse]));
by (Ultra_tac 1);
by (rewtac real_divide_def);
by (auto_tac (claset(),simpset() addsimps [INVERSE_ZERO]));
qed "hrcis_inverse";

Goal "hRe(hcis a) = ( *f* cos) a";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcis,starfun,hRe]));
qed "hRe_hcis";
Addsimps [hRe_hcis];

Goal "hIm(hcis a) = ( *f* sin) a";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcis,starfun,hIm]));
qed "hIm_hcis";
Addsimps [hIm_hcis];

Goal "( *f* cos) (hypreal_of_nat n * a) = hRe(hcis a ^ n)";
by (auto_tac (claset(),simpset() addsimps [NSDeMoivre]));
qed "cos_n_hRe_hcis_pow_n";

Goal "( *f* sin) (hypreal_of_nat n * a) = hIm(hcis a ^ n)";
by (auto_tac (claset(),simpset() addsimps [NSDeMoivre]));
qed "sin_n_hIm_hcis_pow_n";

Goal "( *f* cos) (hypreal_of_hypnat n * a) = hRe(hcis a hcpow n)";
by (auto_tac (claset(),simpset() addsimps [NSDeMoivre_ext]));
qed "cos_n_hRe_hcis_hcpow_n";

Goal "( *f* sin) (hypreal_of_hypnat n * a) = hIm(hcis a hcpow n)";
by (auto_tac (claset(),simpset() addsimps [NSDeMoivre_ext]));
qed "sin_n_hIm_hcis_hcpow_n";

Goalw [hexpi_def] "hexpi(a + b) = hexpi(a) * hexpi(b)";
by (res_inst_tac [("z","a")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","b")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcis,hRe,hIm,
    hcomplex_add,hcomplex_mult,hypreal_mult,starfun,
    hcomplex_of_hypreal,cis_mult RS sym,complex_Im_add,
    complex_Re_add,exp_add,complex_of_real_mult]));
qed "hexpi_add";

(*----------------------------------------------------------------------------------*)
(* hcomplex_of_complex  preserves field and order properties                        *)
(*----------------------------------------------------------------------------------*)

Goalw [hcomplex_of_complex_def] 
     "hcomplex_of_complex (z1 + z2) = hcomplex_of_complex z1 + hcomplex_of_complex z2";
by (simp_tac (simpset() addsimps [hcomplex_add]) 1);
qed "hcomplex_of_complex_add";
Addsimps [hcomplex_of_complex_add];

Goalw [hcomplex_of_complex_def] 
     "hcomplex_of_complex (z1 * z2) = hcomplex_of_complex z1 * hcomplex_of_complex z2";
by (simp_tac (simpset() addsimps [hcomplex_mult]) 1);
qed "hcomplex_of_complex_mult";
Addsimps [hcomplex_of_complex_mult];

Goalw [hcomplex_of_complex_def]
 "(hcomplex_of_complex z1 = hcomplex_of_complex z2) = (z1 = z2)";
by Auto_tac;
qed "hcomplex_of_complex_eq_iff";
Addsimps [hcomplex_of_complex_eq_iff];

Goalw [hcomplex_of_complex_def] "hcomplex_of_complex (-r) = - hcomplex_of_complex  r";
by (auto_tac (claset(),simpset() addsimps [hcomplex_minus]));
qed "hcomplex_of_complex_minus";
Addsimps [hcomplex_of_complex_minus];

Goalw [hcomplex_of_complex_def,hcomplex_one_def] 
      "hcomplex_of_complex 1 = 1";
by Auto_tac;
qed "hcomplex_of_complex_one";

Goalw [hcomplex_of_complex_def,hcomplex_zero_def] 
      "hcomplex_of_complex 0 = 0";
by (Simp_tac 1);
qed "hcomplex_of_complex_zero";

Goal "(hcomplex_of_complex r = 0) = (r = 0)";
by (auto_tac (claset() addIs [FreeUltrafilterNat_P],
    simpset() addsimps [hcomplex_of_complex_def,
                        hcomplex_zero_def]));
qed "hcomplex_of_complex_zero_iff";

Goal "hcomplex_of_complex (inverse r) = inverse (hcomplex_of_complex r)";
by (case_tac "r=0" 1);
by (asm_simp_tac (simpset() addsimps [COMPLEX_INVERSE_ZERO, 
                              HCOMPLEX_INVERSE_ZERO, hcomplex_of_complex_zero,
                              COMPLEX_DIVIDE_ZERO]) 1);
by (res_inst_tac [("c1","hcomplex_of_complex r")] 
    (hcomplex_mult_left_cancel RS iffD1) 1);
by (stac (hcomplex_of_complex_mult RS sym) 2); 
by (auto_tac (claset(), 
         simpset() addsimps [hcomplex_of_complex_one, hcomplex_of_complex_zero_iff]));
qed "hcomplex_of_complex_inverse";
Addsimps [hcomplex_of_complex_inverse];

Goal "hcomplex_of_complex (z1 / z2) = hcomplex_of_complex z1 / hcomplex_of_complex z2";
by (simp_tac (simpset() addsimps [hcomplex_divide_def, complex_divide_def]) 1);
qed "hcomplex_of_complex_divide"; 
Addsimps [hcomplex_of_complex_divide];

Goalw [hcomplex_of_complex_def,hypreal_of_real_def] 
   "hRe (hcomplex_of_complex z) = hypreal_of_real (Re z)";
by (auto_tac (claset(),simpset() addsimps [hRe]));
qed "hRe_hcomplex_of_complex";

Goalw [hcomplex_of_complex_def,hypreal_of_real_def] 
   "hIm (hcomplex_of_complex z) = hypreal_of_real (Im z)";
by (auto_tac (claset(),simpset() addsimps [hIm]));
qed "hIm_hcomplex_of_complex";

Goalw [hypreal_of_real_def,hcomplex_of_complex_def] 
     "hcmod (hcomplex_of_complex x) = hypreal_of_real (cmod x)";
by (auto_tac (claset(),simpset() addsimps [hcmod]));
qed "hcmod_hcomplex_of_complex";
