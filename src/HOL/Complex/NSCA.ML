(*  Title       : NSCA.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 2001,2002 University of Edinburgh
    Description : Infinite, infinitesimal complex number etc! 
*)

(*--------------------------------------------------------------------------------------*)
(* Closure laws for members of (embedded) set standard complex SComplex                 *)
(* -------------------------------------------------------------------------------------*)

Goalw [SComplex_def] "[| (x::hcomplex): SComplex; y: SComplex |] ==> x + y: SComplex";
by (Step_tac 1);
by (res_inst_tac [("x","r + ra")] exI 1);
by (Simp_tac 1);
qed "SComplex_add";

Goalw [SComplex_def] "[| (x::hcomplex): SComplex; y: SComplex |] ==> x * y: SComplex";
by (Step_tac 1);
by (res_inst_tac [("x","r * ra")] exI 1);
by (Simp_tac 1);
qed "SComplex_mult";

Goalw [SComplex_def] "x: SComplex ==> inverse x : SComplex";
by (blast_tac (claset() addIs [hcomplex_of_complex_inverse RS sym]) 1); 
qed "SComplex_inverse";

Goal "[| x: SComplex;  y: SComplex |] ==> x/y: SComplex";
by (asm_simp_tac (simpset() addsimps [SComplex_mult,SComplex_inverse,
                                      hcomplex_divide_def]) 1); 
qed "SComplex_divide";

Goalw [SComplex_def] "x: SComplex ==> -x : SComplex";
by (blast_tac (claset() addIs [hcomplex_of_complex_minus RS sym]) 1); 
qed "SComplex_minus";

Goal "(-x : SComplex) = (x: SComplex)";
by Auto_tac;  
by (etac SComplex_minus 2); 
by (dtac SComplex_minus 1); 
by Auto_tac;  
qed "SComplex_minus_iff";
Addsimps [SComplex_minus_iff]; 

Goal "[| x + y : SComplex; y: SComplex |] ==> x: SComplex";
by (dres_inst_tac [("x","y")] SComplex_minus 1);
by (dtac SComplex_add 1);
by (assume_tac 1); 
by Auto_tac;  
qed "SComplex_add_cancel";

Goalw [hcomplex_of_complex_def]
     "hcmod (hcomplex_of_complex r) : Reals";
by (simp_tac (simpset() addsimps [hcmod,SReal_def,
    hypreal_of_real_def]) 1);
qed "SReal_hcmod_hcomplex_of_complex";
Addsimps [SReal_hcmod_hcomplex_of_complex];

Goalw [hcomplex_number_of_def]
    "hcmod (number_of w ::hcomplex) : Reals";
by (rtac SReal_hcmod_hcomplex_of_complex 1);
qed "SReal_hcmod_number_of";
Addsimps [SReal_hcmod_number_of];

Goalw [SComplex_def] "x: SComplex ==> hcmod x : Reals";
by Auto_tac;
qed "SReal_hcmod_SComplex";

Goalw [SComplex_def] "hcomplex_of_complex x: SComplex";
by (Blast_tac 1);
qed "SComplex_hcomplex_of_complex";
Addsimps [SComplex_hcomplex_of_complex];

Goalw [hcomplex_number_of_def] "(number_of w ::hcomplex) : SComplex";
by (rtac SComplex_hcomplex_of_complex 1);
qed "SComplex_number_of";
Addsimps [SComplex_number_of];

Goalw [hcomplex_divide_def] "r : SComplex ==> r/(number_of w::hcomplex) : SComplex";
by (blast_tac (claset() addSIs [SComplex_number_of, SComplex_mult, 
                                SComplex_inverse]) 1);
qed "SComplex_divide_number_of";

Goalw [SComplex_def] "{x. hcomplex_of_complex x : SComplex} = (UNIV::complex set)";
by Auto_tac;
qed "SComplex_UNIV_complex";

Goalw [SComplex_def] "(x: SComplex) = (EX y. x = hcomplex_of_complex y)";
by Auto_tac;
qed "SComplex_iff";

Goalw [SComplex_def] "hcomplex_of_complex `(UNIV::complex set) = SComplex";
by Auto_tac;
qed "hcomplex_of_complex_image";

Goalw [SComplex_def] "inv hcomplex_of_complex `SComplex = (UNIV::complex set)";
by Auto_tac;
by (rtac (inj_hcomplex_of_complex RS inv_f_f RS subst) 1);
by (Blast_tac 1);
qed "inv_hcomplex_of_complex_image";

Goalw [SComplex_def] 
      "[| EX x. x: P; P <= SComplex |] ==> EX Q. P = hcomplex_of_complex ` Q";
by (Best_tac 1); 
qed "SComplex_hcomplex_of_complex_image";

Goal "[| (x::hcomplex): SComplex; y: SComplex; hcmod x < hcmod y \
\     |] ==> EX r: Reals. hcmod x< r & r < hcmod y";
by (auto_tac (claset() addIs [SReal_dense], simpset() 
    addsimps [SReal_hcmod_SComplex]));
qed "SComplex_SReal_dense";

Goalw [SComplex_def,SReal_def] 
      "z : SComplex ==> hcmod z : Reals";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,hypreal_of_real_def,
    hcomplex_of_complex_def,cmod_def]));
by (res_inst_tac [("x","cmod r")] exI 1);
by (ultra_tac (claset(),simpset() addsimps [cmod_def]) 1);
qed "SComplex_hcmod_SReal";

Goal "0 : SComplex";
by (auto_tac (claset(),simpset() addsimps [SComplex_def]));
qed "SComplex_zero";
Addsimps [SComplex_zero];

Goal "1 : SComplex";
by (auto_tac (claset(),simpset() addsimps [SComplex_def,hcomplex_of_complex_def,
    hcomplex_one_def]));
qed "SComplex_one";
Addsimps [SComplex_one];

(*
Goalw [SComplex_def,SReal_def] "hcmod z : Reals ==> z : SComplex";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcmod,hypreal_of_real_def,
    hcomplex_of_complex_def,cmod_def]));
*)

(*--------------------------------------------------------------------------------------------*)
(*        Set of finite elements is a subring of the extended complex numbers                 *)
(* -------------------------------------------------------------------------------------------*)

Goalw [CFinite_def] "[|x : CFinite; y : CFinite|] ==> (x+y) : CFinite";
by (blast_tac (claset() addSIs [SReal_add,hcmod_add_less]) 1);
qed "CFinite_add";

Goalw [CFinite_def] "[|x : CFinite; y : CFinite|] ==> x*y : CFinite";
by (blast_tac (claset() addSIs [SReal_mult,hcmod_mult_less]) 1);
qed "CFinite_mult";

Goalw [CFinite_def] "(-x : CFinite) = (x : CFinite)";
by (Simp_tac 1);
qed "CFinite_minus_iff";
Addsimps [CFinite_minus_iff];

Goalw [SComplex_def,CFinite_def] "SComplex <= CFinite";
by Auto_tac;
by (res_inst_tac [("x","1 + hcmod(hcomplex_of_complex r)")] bexI 1);
by (auto_tac (claset() addIs [SReal_add],simpset()));
qed "SComplex_subset_CFinite";
Addsimps [ SComplex_subset_CFinite];

Goal "hcmod (hcomplex_of_complex r) : HFinite";
by (auto_tac (claset() addSIs [ SReal_subset_HFinite RS subsetD],simpset()));
qed "HFinite_hcmod_hcomplex_of_complex";
Addsimps [HFinite_hcmod_hcomplex_of_complex];

Goal "hcomplex_of_complex x: CFinite";
by (auto_tac (claset() addSIs [ SComplex_subset_CFinite RS subsetD],simpset()));
qed "CFinite_hcomplex_of_complex";
Addsimps [CFinite_hcomplex_of_complex];

Goalw [CFinite_def] "x : CFinite ==> EX t: Reals. hcmod x < t";
by Auto_tac;
qed "CFiniteD";

Goalw [CFinite_def] "(x : CFinite) = (hcmod x : HFinite)";
by (auto_tac (claset(), simpset() addsimps [HFinite_def]));
qed "CFinite_hcmod_iff";

Goal "number_of w : CFinite";
by (rtac (SComplex_number_of RS (SComplex_subset_CFinite RS subsetD)) 1);
qed "CFinite_number_of";
Addsimps [CFinite_number_of];

Goal "[|x : CFinite; y <= hcmod x; 0 <= y |] ==> y: HFinite";
by (auto_tac (claset() addIs [HFinite_bounded],simpset() addsimps 
    [CFinite_hcmod_iff]));
qed "CFinite_bounded";

(*--------------------------------------------------------------------------------------*)
(* Set of complex infinitesimals is a subring of the nonstandard complex numbers        *) 
(*--------------------------------------------------------------------------------------*)
	 
Goalw [CInfinitesimal_def]
      "x : CInfinitesimal ==> ALL r: Reals. 0 < r --> hcmod x < r";
by Auto_tac;
qed "CInfinitesimalD";

Goalw [CInfinitesimal_def] "0 : CInfinitesimal";
by Auto_tac;
qed "CInfinitesimal_zero";
AddIffs [CInfinitesimal_zero];

Goal "x/(2::hcomplex) + x/(2::hcomplex) = x";
by Auto_tac;  
qed "hcomplex_sum_of_halves";

Goalw [CInfinitesimal_def,Infinitesimal_def] 
   "(z : CInfinitesimal) = (hcmod z : Infinitesimal)";
by Auto_tac;
qed "CInfinitesimal_hcmod_iff";

Goal "1 ~: CInfinitesimal";
by (simp_tac (simpset() addsimps [CInfinitesimal_hcmod_iff]) 1);
qed "one_not_CInfinitesimal";
Addsimps [one_not_CInfinitesimal];

Goal "[| x : CInfinitesimal; y : CInfinitesimal |] ==> (x+y) : CInfinitesimal";
by (auto_tac (claset(),simpset() addsimps [CInfinitesimal_hcmod_iff]));
by (rtac hrabs_le_Infinitesimal 1);
by (res_inst_tac [("y","hcmod y")] Infinitesimal_add 1);
by Auto_tac;
qed "CInfinitesimal_add";

Goalw [CInfinitesimal_def] "(-x:CInfinitesimal) = (x:CInfinitesimal)";
by (Full_simp_tac 1);
qed "CInfinitesimal_minus_iff";
Addsimps [CInfinitesimal_minus_iff];

Goal "[| x : CInfinitesimal;  y : CInfinitesimal |] ==> x-y : CInfinitesimal";
by (asm_simp_tac
    (simpset() addsimps [hcomplex_diff_def, CInfinitesimal_add]) 1);
qed "CInfinitesimal_diff";

Goal "[| x : CInfinitesimal; y : CInfinitesimal |] ==> (x * y) : CInfinitesimal";
by (auto_tac (claset() addIs [Infinitesimal_mult],simpset() addsimps 
    [CInfinitesimal_hcmod_iff,hcmod_mult]));
qed "CInfinitesimal_mult";

Goal "[| x : CInfinitesimal; y : CFinite |] ==> (x * y) : CInfinitesimal";
by (auto_tac (claset() addIs [Infinitesimal_HFinite_mult],simpset() 
    addsimps [CInfinitesimal_hcmod_iff,CFinite_hcmod_iff,hcmod_mult]));
qed "CInfinitesimal_CFinite_mult";

Goal "[| x : CInfinitesimal; y : CFinite |] ==> (y * x) : CInfinitesimal";
by (auto_tac (claset() addDs [CInfinitesimal_CFinite_mult],
              simpset() addsimps [hcomplex_mult_commute]));
qed "CInfinitesimal_CFinite_mult2";

Goalw [CInfinite_def,HInfinite_def] 
   "(z : CInfinite) = (hcmod z : HInfinite)";
by Auto_tac;
qed "CInfinite_hcmod_iff";

Goal "x: CInfinite ==> inverse x: CInfinitesimal";
by (auto_tac (claset() addIs [HInfinite_inverse_Infinitesimal],
    simpset() addsimps [CInfinitesimal_hcmod_iff,
    CInfinite_hcmod_iff,hcmod_hcomplex_inverse]));
qed "CInfinite_inverse_CInfinitesimal";

Goal "[|x: CInfinite; y: CInfinite|] ==> (x*y): CInfinite";
by (auto_tac (claset() addIs [HInfinite_mult],simpset() addsimps 
    [CInfinite_hcmod_iff,hcmod_mult]));
qed "CInfinite_mult";

Goalw [CInfinite_def] "(-x : CInfinite) = (x : CInfinite)";
by (Simp_tac 1);
qed "CInfinite_minus_iff";
Addsimps [CInfinite_minus_iff];

Goal "[|a: CFinite; b: CFinite; c: CFinite|] \ 
\     ==> a*a + b*b + c*c : CFinite";
by (auto_tac (claset() addIs [CFinite_mult,CFinite_add], simpset()));
qed "CFinite_sum_squares";

Goal "x ~: CInfinitesimal ==> x ~= 0";
by Auto_tac;
qed "not_CInfinitesimal_not_zero";

Goal "x: CFinite - CInfinitesimal ==> x ~= 0";
by Auto_tac;
qed "not_CInfinitesimal_not_zero2";

Goal "x : CFinite - CInfinitesimal ==> hcmod x : HFinite - Infinitesimal";
by (auto_tac (claset(),simpset() addsimps [CFinite_hcmod_iff,CInfinitesimal_hcmod_iff]));
qed "CFinite_diff_CInfinitesimal_hcmod";

Goal "[| e : CInfinitesimal; hcmod x < hcmod e |] ==> x : CInfinitesimal";
by (auto_tac (claset() addIs [hrabs_less_Infinitesimal],simpset() 
    addsimps [CInfinitesimal_hcmod_iff]));
qed "hcmod_less_CInfinitesimal";

Goal "[| e : CInfinitesimal; hcmod x <= hcmod e |] ==> x : CInfinitesimal";
by (auto_tac (claset() addIs [hrabs_le_Infinitesimal],simpset() 
    addsimps [CInfinitesimal_hcmod_iff]));
qed "hcmod_le_CInfinitesimal";

Goal  "[| e : CInfinitesimal; \
\         e' : CInfinitesimal; \
\         hcmod e' < hcmod x ; hcmod x < hcmod e \
\      |] ==> x : CInfinitesimal";
by (auto_tac (claset() addIs [Infinitesimal_interval],simpset() 
    addsimps [CInfinitesimal_hcmod_iff]));
qed "CInfinitesimal_interval";

Goal "[| e : CInfinitesimal; \
\        e' : CInfinitesimal; \
\        hcmod e' <= hcmod x ; hcmod x <= hcmod e \
\     |] ==> x : CInfinitesimal";
by (auto_tac (claset() addIs [Infinitesimal_interval2],simpset() 
    addsimps [CInfinitesimal_hcmod_iff]));
qed "CInfinitesimal_interval2";

Goal "[| x ~: CInfinitesimal;  y ~: CInfinitesimal|] ==> (x*y) ~: CInfinitesimal";
by (auto_tac (claset(),simpset() addsimps [CInfinitesimal_hcmod_iff,hcmod_mult]));
by (dtac not_Infinitesimal_mult 1);
by Auto_tac;
qed "not_CInfinitesimal_mult";

Goal "x*y : CInfinitesimal ==> x : CInfinitesimal | y : CInfinitesimal";
by (auto_tac (claset() addDs [Infinitesimal_mult_disj],simpset() addsimps 
    [CInfinitesimal_hcmod_iff,hcmod_mult]));
qed "CInfinitesimal_mult_disj";

Goal "[| x : CFinite - CInfinitesimal; \
\                  y : CFinite - CInfinitesimal \
\               |] ==> (x*y) : CFinite - CInfinitesimal";
by (Clarify_tac 1);
by (blast_tac (claset() addDs [CFinite_mult,not_CInfinitesimal_mult]) 1);
qed "CFinite_CInfinitesimal_diff_mult";

Goal "CInfinitesimal <= CFinite";
by (auto_tac (claset() addIs [Infinitesimal_subset_HFinite RS subsetD],
    simpset() addsimps [CInfinitesimal_hcmod_iff,CFinite_hcmod_iff]));
qed "CInfinitesimal_subset_CFinite";

Goal "x: CInfinitesimal ==> x * hcomplex_of_complex r : CInfinitesimal";
by (auto_tac (claset() addSIs [Infinitesimal_HFinite_mult],
    simpset() addsimps [CInfinitesimal_hcmod_iff,hcmod_mult]));
qed "CInfinitesimal_hcomplex_of_complex_mult";

Goal "x: CInfinitesimal ==> hcomplex_of_complex r * x: CInfinitesimal";
by (auto_tac (claset() addSIs [Infinitesimal_HFinite_mult2],
    simpset() addsimps [CInfinitesimal_hcmod_iff,hcmod_mult]));
qed "CInfinitesimal_hcomplex_of_complex_mult2";


(*--------------------------------------------------------------------------------------*)
(* Infinitely close relation @c=                                                        *)
(* -------------------------------------------------------------------------------------*)

(*
Goalw [capprox_def,approx_def] "(z @c= w) = (hcmod z @= hcmod w)";
by (auto_tac (claset(),simpset() addsimps [CInfinitesimal_hcmod_iff]));
*)

Goal "x:CInfinitesimal = (x @c= 0)";
by (simp_tac (simpset() addsimps [CInfinitesimal_hcmod_iff,
    capprox_def]) 1);
qed "mem_cinfmal_iff";

Goalw [capprox_def,hcomplex_diff_def]
      " (x @c= y) = (x + -y @c= 0)";
by (Simp_tac 1);
qed "capprox_minus_iff";

Goalw [capprox_def,hcomplex_diff_def]
      " (x @c= y) = (-y + x @c= 0)";
by (simp_tac (simpset() addsimps [hcomplex_add_commute]) 1);
qed "capprox_minus_iff2";

Goalw [capprox_def] "x @c= x";
by (Simp_tac 1);
qed "capprox_refl";
Addsimps [capprox_refl];

Goalw [capprox_def,CInfinitesimal_def]  
     "x @c= y ==> y @c= x";
by (auto_tac (claset() addSDs [bspec],simpset() addsimps 
    [hcmod_diff_commute]));
qed "capprox_sym";

Goalw [capprox_def]  "[| x @c= y; y @c= z |] ==> x @c= z";
by (dtac CInfinitesimal_add 1); 
by (assume_tac 1); 
by (auto_tac (claset(),simpset() addsimps [hcomplex_diff_def]));
qed "capprox_trans";

Goal "[| r @c= x; s @c= x |] ==> r @c= s";
by (blast_tac (claset() addIs [capprox_sym, capprox_trans]) 1); 
qed "capprox_trans2";

Goal "[| x @c= r; x @c= s|] ==> r @c= s";
by (blast_tac (claset() addIs [capprox_sym, capprox_trans]) 1); 
qed "capprox_trans3";

Goal "(number_of w @c= x) = (x @c= number_of w)";
by (blast_tac (claset() addIs [capprox_sym]) 1); 
qed "number_of_capprox_reorient";
Addsimps [number_of_capprox_reorient];

Goal "(x-y : CInfinitesimal) = (x @c= y)";
by (auto_tac (claset(),
              simpset() addsimps [hcomplex_diff_def, capprox_minus_iff RS sym,
                                  mem_cinfmal_iff]));
qed "CInfinitesimal_capprox_minus";

Goalw [cmonad_def] "(x @c= y) = (cmonad(x)=cmonad(y))";
by (auto_tac (claset() addDs [capprox_sym] 
                       addSEs [capprox_trans,equalityCE],
              simpset()));
qed "capprox_monad_iff";

Goal "[| x: CInfinitesimal; y: CInfinitesimal |] ==> x @c= y";
by (asm_full_simp_tac (simpset() addsimps [mem_cinfmal_iff]) 1);
by (blast_tac (claset() addIs [capprox_trans, capprox_sym]) 1); 
qed "Infinitesimal_capprox";

val prem1::prem2::rest = 
goalw thy [capprox_def,hcomplex_diff_def] 
     "[| a @c= b; c @c= d |] ==> a+c @c= b+d";
by (rtac (hcomplex_minus_add_distrib RS ssubst) 1);
by (rtac (hcomplex_add_assoc RS ssubst) 1);
by (res_inst_tac [("y1","c")] (hcomplex_add_left_commute RS subst) 1);
by (rtac (hcomplex_add_assoc RS subst) 1);
by (rtac ([prem1,prem2] MRS CInfinitesimal_add) 1);
qed "capprox_add";

Goal "a @c= b ==> -a @c= -b";
by (rtac ((capprox_minus_iff RS iffD2) RS capprox_sym) 1);
by (dtac (capprox_minus_iff RS iffD1) 1);
by (simp_tac (simpset() addsimps [hcomplex_add_commute]) 1);
qed "capprox_minus";

Goal "-a @c= -b ==> a @c= b";
by (auto_tac (claset() addDs [capprox_minus], simpset()));
qed "capprox_minus2";

Goal "(-a @c= -b) = (a @c= b)";
by (blast_tac (claset() addIs [capprox_minus,capprox_minus2]) 1);
qed "capprox_minus_cancel";
Addsimps [capprox_minus_cancel];

Goal "[| a @c= b; c @c= d |] ==> a + -c @c= b + -d";
by (blast_tac (claset() addSIs [capprox_add,capprox_minus]) 1);
qed "capprox_add_minus";

Goalw [capprox_def,hcomplex_diff_def] 
      "[| a @c= b; c: CFinite|] ==> a*c @c= b*c"; 
by (asm_full_simp_tac (simpset() addsimps [CInfinitesimal_CFinite_mult,
    hcomplex_minus_mult_eq1,hcomplex_add_mult_distrib RS sym] 
    delsimps [hcomplex_minus_mult_eq1 RS sym]) 1);
qed "capprox_mult1";

Goal "[|a @c= b; c: CFinite|] ==> c*a @c= c*b"; 
by (asm_simp_tac (simpset() addsimps [capprox_mult1,hcomplex_mult_commute]) 1);
qed "capprox_mult2";

Goal "[|u @c= v*x; x @c= y; v: CFinite|] ==> u @c= v*y";
by (fast_tac (claset() addIs [capprox_mult2,capprox_trans]) 1);
qed "capprox_mult_subst";

Goal "[| u @c= x*v; x @c= y; v: CFinite |] ==> u @c= y*v";
by (fast_tac (claset() addIs [capprox_mult1,capprox_trans]) 1);
qed "capprox_mult_subst2";

Goal "[| u @c= x*hcomplex_of_complex v; x @c= y |] ==> u @c= y*hcomplex_of_complex v";
by (auto_tac (claset() addIs [capprox_mult_subst2], simpset()));
qed "capprox_mult_subst_SComplex";

Goalw [capprox_def]  "a = b ==> a @c= b";
by (Asm_simp_tac 1);
qed "capprox_eq_imp";

Goal "x: CInfinitesimal ==> -x @c= x"; 
by (fast_tac (HOL_cs addIs [CInfinitesimal_minus_iff RS iffD2,
    mem_cinfmal_iff RS iffD1,capprox_trans2]) 1);
qed "CInfinitesimal_minus_capprox";

Goalw [capprox_def]  
     "(EX y: CInfinitesimal. x - z = y) = (x @c= z)";
by (Blast_tac 1);
qed "bex_CInfinitesimal_iff";

Goal "(EX y: CInfinitesimal. x = z + y) = (x @c= z)";
by (asm_full_simp_tac (simpset() addsimps [bex_CInfinitesimal_iff RS sym]) 1);
by (Force_tac 1);
qed "bex_CInfinitesimal_iff2";

Goal "[| y: CInfinitesimal; x + y = z |] ==> x @c= z";
by (rtac (bex_CInfinitesimal_iff RS iffD1) 1);
by (dtac (CInfinitesimal_minus_iff RS iffD2) 1);
by (auto_tac (claset(), simpset() addsimps [hcomplex_add_assoc RS sym]));
qed "CInfinitesimal_add_capprox";

Goal "y: CInfinitesimal ==> x @c= x + y";
by (rtac (bex_CInfinitesimal_iff RS iffD1) 1);
by (dtac (CInfinitesimal_minus_iff RS iffD2) 1);
by (auto_tac (claset(), simpset() addsimps [hcomplex_add_assoc RS sym]));
qed "CInfinitesimal_add_capprox_self";

Goal "y: CInfinitesimal ==> x @c= y + x";
by (auto_tac (claset() addDs [CInfinitesimal_add_capprox_self],
    simpset() addsimps [hcomplex_add_commute]));
qed "CInfinitesimal_add_capprox_self2";

Goal "y: CInfinitesimal ==> x @c= x + -y";
by (blast_tac (claset() addSIs [CInfinitesimal_add_capprox_self,
                                CInfinitesimal_minus_iff RS iffD2]) 1);
qed "CInfinitesimal_add_minus_capprox_self";

Goal "[| y: CInfinitesimal; x+y @c= z|] ==> x @c= z";
by (dres_inst_tac [("x","x")] (CInfinitesimal_add_capprox_self RS capprox_sym) 1);
by (etac (capprox_trans3 RS capprox_sym) 1);
by (assume_tac 1);
qed "CInfinitesimal_add_cancel";

Goal "[| y: CInfinitesimal; x @c= z + y|] ==> x @c= z";
by (dres_inst_tac [("x","z")] (CInfinitesimal_add_capprox_self2  RS capprox_sym) 1);
by (etac (capprox_trans3 RS capprox_sym) 1);
by (asm_full_simp_tac (simpset() addsimps [hcomplex_add_commute]) 1);
by (etac capprox_sym 1);
qed "CInfinitesimal_add_right_cancel";

Goal "d + b  @c= d + c ==> b @c= c";
by (dtac (capprox_minus_iff RS iffD1) 1);
by (asm_full_simp_tac (simpset() addsimps 
    [hcomplex_minus_add_distrib,capprox_minus_iff RS sym] 
    @ hcomplex_add_ac) 1);
qed "capprox_add_left_cancel";

Goal "b + d @c= c + d ==> b @c= c";
by (rtac capprox_add_left_cancel 1);
by (asm_full_simp_tac (simpset() addsimps 
    [hcomplex_add_commute]) 1);
qed "capprox_add_right_cancel";

Goal "b @c= c ==> d + b @c= d + c";
by (rtac (capprox_minus_iff RS iffD2) 1);
by (asm_full_simp_tac (simpset() addsimps 
    [capprox_minus_iff RS sym] @ hcomplex_add_ac) 1);
qed "capprox_add_mono1";

Goal "b @c= c ==> b + a @c= c + a";
by (asm_simp_tac (simpset() addsimps 
    [hcomplex_add_commute,capprox_add_mono1]) 1);
qed "capprox_add_mono2";

Goal "(a + b @c= a + c) = (b @c= c)";
by (fast_tac (claset() addEs [capprox_add_left_cancel,
    capprox_add_mono1]) 1);
qed "capprox_add_left_iff";

AddIffs [capprox_add_left_iff];


Goal "(b + a @c= c + a) = (b @c= c)";
by (simp_tac (simpset() addsimps [hcomplex_add_commute]) 1);
qed "capprox_add_right_iff";

AddIffs [capprox_add_right_iff];

Goal "[| x: CFinite; x @c= y |] ==> y: CFinite";
by (dtac (bex_CInfinitesimal_iff2 RS iffD2) 1);
by (Step_tac 1);
by (dtac (CInfinitesimal_subset_CFinite RS subsetD 
          RS (CFinite_minus_iff RS iffD2)) 1);
by (dtac CFinite_add 1);
by (assume_tac 1 THEN Auto_tac);
qed "capprox_CFinite";

Goal "x @c= hcomplex_of_complex D ==> x: CFinite";
by (rtac (capprox_sym RSN (2,capprox_CFinite)) 1);
by Auto_tac;
qed "capprox_hcomplex_of_complex_CFinite";

Goal "[|a @c= b; c @c= d; b: CFinite; d: CFinite|] ==> a*c @c= b*d";
by (rtac capprox_trans 1); 
by (rtac capprox_mult2 2); 
by (rtac capprox_mult1 1);
by (blast_tac (claset() addIs [capprox_CFinite, capprox_sym]) 2);  
by Auto_tac;  
qed "capprox_mult_CFinite";

Goal "[|a @c= hcomplex_of_complex b; c @c= hcomplex_of_complex d |] \
\     ==> a*c @c= hcomplex_of_complex b * hcomplex_of_complex d";
by (blast_tac (claset() addSIs [capprox_mult_CFinite,
            capprox_hcomplex_of_complex_CFinite,CFinite_hcomplex_of_complex]) 1);
qed "capprox_mult_hcomplex_of_complex";

Goal "[| a: SComplex; a ~= 0; a*x @c= 0 |] ==> x @c= 0";
by (dtac (SComplex_inverse RS (SComplex_subset_CFinite RS subsetD)) 1);
by (auto_tac (claset() addDs [capprox_mult2],
    simpset() addsimps [hcomplex_mult_assoc RS sym]));
qed "capprox_SComplex_mult_cancel_zero";

Goal "[| a: SComplex; x @c= 0 |] ==> x*a @c= 0";
by (auto_tac (claset() addDs [(SComplex_subset_CFinite RS subsetD),
              capprox_mult1], simpset()));
qed "capprox_mult_SComplex1";

Goal "[| a: SComplex; x @c= 0 |] ==> a*x @c= 0";
by (auto_tac (claset() addDs [(SComplex_subset_CFinite RS subsetD),
              capprox_mult2], simpset()));
qed "capprox_mult_SComplex2";

Goal "[|a : SComplex; a ~= 0 |] ==> (a*x @c= 0) = (x @c= 0)";
by (blast_tac (claset() addIs [capprox_SComplex_mult_cancel_zero,
    capprox_mult_SComplex2]) 1);
qed "capprox_mult_SComplex_zero_cancel_iff";
Addsimps [capprox_mult_SComplex_zero_cancel_iff];

Goal "[| a: SComplex; a ~= 0; a* w @c= a*z |] ==> w @c= z";
by (dtac (SComplex_inverse RS (SComplex_subset_CFinite RS subsetD)) 1);
by (auto_tac (claset() addDs [capprox_mult2],
    simpset() addsimps [hcomplex_mult_assoc RS sym]));
qed "capprox_SComplex_mult_cancel";

Goal "[| a: SComplex; a ~= 0|] ==> (a* w @c= a*z) = (w @c= z)";
by (auto_tac (claset() addSIs [capprox_mult2,SComplex_subset_CFinite RS subsetD] 
    addIs [capprox_SComplex_mult_cancel], simpset()));
qed "capprox_SComplex_mult_cancel_iff1";
Addsimps [capprox_SComplex_mult_cancel_iff1];

Goal "(x @c= y) = (hcmod (y - x) @= 0)";
by (rtac (capprox_minus_iff RS ssubst) 1);
by (auto_tac (claset(),simpset() addsimps [capprox_def,
    CInfinitesimal_hcmod_iff,mem_infmal_iff,symmetric hcomplex_diff_def,
    hcmod_diff_commute]));
qed "capprox_hcmod_approx_zero";

Goal "(x @c= 0) = (hcmod x @= 0)";
by (auto_tac (claset(),simpset() addsimps 
    [capprox_hcmod_approx_zero]));
qed "capprox_approx_zero_iff";

Goal "(-x @c= 0) = (x @c= 0)";
by (auto_tac (claset(),simpset() addsimps 
    [capprox_hcmod_approx_zero]));
qed "capprox_minus_zero_cancel_iff";
Addsimps [capprox_minus_zero_cancel_iff];

Goal "u @c= 0 ==> hcmod(x + u) - hcmod x : Infinitesimal";
by (res_inst_tac [("e","hcmod u"),("e'","- hcmod u")] Infinitesimal_interval2 1);
by (auto_tac (claset() addDs [capprox_approx_zero_iff RS iffD1], 
    simpset() addsimps [mem_infmal_iff RS sym,hypreal_diff_def]));
by (res_inst_tac [("C","hcmod x")] hypreal_le_add_left_cancel 1);
by (auto_tac (claset(),simpset() addsimps [symmetric hypreal_diff_def]));
qed "Infinitesimal_hcmod_add_diff";

Goal "u @c= 0 ==> hcmod(x + u) @= hcmod x";
by (rtac (approx_minus_iff RS iffD2) 1);
by (auto_tac (claset() addIs [Infinitesimal_hcmod_add_diff],
    simpset() addsimps [mem_infmal_iff RS sym,symmetric hypreal_diff_def]));
qed "approx_hcmod_add_hcmod";

Goal "x @c= y ==> hcmod x @= hcmod y";
by (auto_tac (claset() addIs [approx_hcmod_add_hcmod] 
    addSDs [bex_CInfinitesimal_iff2 RS iffD2],simpset() addsimps [mem_cinfmal_iff]));
qed "capprox_hcmod_approx";

(*--------------------------------------------------------------------------------------*)
(* zero is the only complex number that is also infinitesimal                           *)
(*--------------------------------------------------------------------------------------*)

Goal "[| x: SComplex; y: CInfinitesimal; 0 < hcmod x |] ==> hcmod y < hcmod x";
by (auto_tac (claset() addSIs [Infinitesimal_less_SReal,SComplex_hcmod_SReal],
    simpset() addsimps [CInfinitesimal_hcmod_iff]));
qed "CInfinitesimal_less_SComplex";

Goal "y: CInfinitesimal ==> ALL r: SComplex. 0 < hcmod r --> hcmod y < hcmod r";
by (blast_tac (claset() addIs [CInfinitesimal_less_SComplex]) 1);
qed "CInfinitesimal_less_SComplex2";

Goal "SComplex Int CInfinitesimal = {0}";
by (auto_tac (claset(),simpset() addsimps [SComplex_def,CInfinitesimal_hcmod_iff]));
by (cut_inst_tac [("r","r")] SReal_hcmod_hcomplex_of_complex 1);
by (dres_inst_tac [("A","Reals")] IntI 1 THEN assume_tac 1);
by (subgoal_tac "hcmod (hcomplex_of_complex r) = 0" 1);
by (Asm_full_simp_tac 1);
by (cut_facts_tac [SReal_Int_Infinitesimal_zero] 1);
by (rotate_tac 2 1);
by (Asm_full_simp_tac 1);
qed "SComplex_Int_CInfinitesimal_zero";

Goal "[| x: SComplex; x: CInfinitesimal|] ==> x = 0";
by (cut_facts_tac [SComplex_Int_CInfinitesimal_zero] 1);
by (Blast_tac 1);
qed "SComplex_CInfinitesimal_zero";

Goal "[| x : SComplex; x ~= 0 |] ==> x : CFinite - CInfinitesimal";
by (auto_tac (claset() addDs [SComplex_CInfinitesimal_zero,
                              SComplex_subset_CFinite RS subsetD], 
              simpset()));
qed "SComplex_CFinite_diff_CInfinitesimal";

Goal "hcomplex_of_complex x ~= 0 ==> hcomplex_of_complex x : CFinite - CInfinitesimal";
by (rtac SComplex_CFinite_diff_CInfinitesimal 1);
by Auto_tac;
qed "hcomplex_of_complex_CFinite_diff_CInfinitesimal";

Goal "(hcomplex_of_complex x : CInfinitesimal) = (x=0)";
by (auto_tac (claset(), simpset() addsimps [hcomplex_of_complex_zero]));  
by (rtac ccontr 1); 
by (rtac (hcomplex_of_complex_CFinite_diff_CInfinitesimal RS DiffD2) 1); 
by Auto_tac;  
qed "hcomplex_of_complex_CInfinitesimal_iff_0";
AddIffs [hcomplex_of_complex_CInfinitesimal_iff_0];

Goal "number_of w ~= (0::hcomplex) ==> number_of w ~: CInfinitesimal";
by (fast_tac (claset() addDs [SComplex_number_of RS SComplex_CInfinitesimal_zero]) 1);
qed "number_of_not_CInfinitesimal";
Addsimps [number_of_not_CInfinitesimal];

Goal "[| y: SComplex; x @c= y; y~= 0 |] ==> x ~= 0";
by (auto_tac (claset() addDs [SComplex_CInfinitesimal_zero,
    capprox_sym RS (mem_cinfmal_iff RS iffD2)],simpset()));
qed "capprox_SComplex_not_zero";

Goal "[| x @c= y; y : CFinite - CInfinitesimal |] \
\     ==> x : CFinite - CInfinitesimal";
by (auto_tac (claset() addIs [capprox_sym RSN (2,capprox_CFinite)],
              simpset() addsimps [mem_cinfmal_iff]));
by (dtac capprox_trans3 1 THEN assume_tac 1);
by (blast_tac (claset() addDs [capprox_sym]) 1);
qed "CFinite_diff_CInfinitesimal_capprox";

Goal "[| y ~= 0;  y: CInfinitesimal;  x/y : CFinite |] ==> x : CInfinitesimal";
by (dtac CInfinitesimal_CFinite_mult2 1);
by (assume_tac 1);
by (asm_full_simp_tac 
    (simpset() addsimps [hcomplex_divide_def, hcomplex_mult_assoc]) 1);
qed "CInfinitesimal_ratio";

Goal "[|x: SComplex; y: SComplex|] ==> (x @c= y) = (x = y)"; 
by Auto_tac;
by (rewrite_goals_tac [capprox_def]);
by (dres_inst_tac [("x","y")] SComplex_minus 1);
by (dtac SComplex_add 1 THEN assume_tac 1);
by (rtac (CLAIM "x - y = 0 ==> x = (y::hcomplex)") 1);
by (rtac SComplex_CInfinitesimal_zero 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_diff_def]));
qed "SComplex_capprox_iff";

Goal "(number_of v @c= number_of w) = (number_of v = (number_of w :: hcomplex))";
by (rtac SComplex_capprox_iff 1); 
by Auto_tac;  
qed "number_of_capprox_iff";
Addsimps [number_of_capprox_iff];

Goal "(number_of w : CInfinitesimal) = (number_of w = (0::hcomplex))";
by (rtac iffI 1);
by (fast_tac (claset() addDs [SComplex_number_of RS SComplex_CInfinitesimal_zero]) 1);
by (Asm_simp_tac 1);
qed "number_of_CInfinitesimal_iff";
Addsimps [number_of_CInfinitesimal_iff];

Goal "(hcomplex_of_complex k @c= hcomplex_of_complex m) = (k = m)";
by Auto_tac;  
by (rtac (inj_hcomplex_of_complex RS injD) 1); 
by (rtac (SComplex_capprox_iff RS iffD1) 1); 
by Auto_tac;  
qed "hcomplex_of_complex_approx_iff";
Addsimps [hcomplex_of_complex_approx_iff];

Goal "(hcomplex_of_complex k @c= number_of w) = (k = number_of w)";
by (stac (hcomplex_of_complex_approx_iff RS sym) 1); 
by Auto_tac;  
qed "hcomplex_of_complex_capprox_number_of_iff";
Addsimps [hcomplex_of_complex_capprox_number_of_iff];

Goal "[| r: SComplex; s: SComplex; r @c= x; s @c= x|] ==> r = s";
by (blast_tac (claset() addIs [(SComplex_capprox_iff RS iffD1),
               capprox_trans2]) 1);
qed "capprox_unique_complex";

Goal "Abs_hcomplex(hcomplexrel ``{%n. X n}) @c= Abs_hcomplex(hcomplexrel``{%n. Y n}) \
\     ==> Abs_hypreal(hyprel `` {%n. Re(X n)}) @= \
\         Abs_hypreal(hyprel `` {%n. Re(Y n)})";
by (auto_tac (claset(),simpset() addsimps [approx_FreeUltrafilterNat_iff]));
by (dtac (capprox_minus_iff RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_minus,hcomplex_add,
    mem_cinfmal_iff RS sym,CInfinitesimal_hcmod_iff,hcmod,
    Infinitesimal_FreeUltrafilterNat_iff2]));
by (dres_inst_tac [("x","m")] spec 1);
by (Ultra_tac 1);
by (rename_tac "Z x" 1);
by (res_inst_tac [("z","X x")] eq_Abs_complex 1);
by (res_inst_tac [("z","Y x")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_minus,complex_add,
    complex_mod] delsimps [realpow_Suc]));
by (rtac order_le_less_trans 1 THEN assume_tac 2);
by (dres_inst_tac [("t","Z x")] sym 1);
by (auto_tac (claset(),simpset() addsimps [abs_eqI1] delsimps [realpow_Suc]));
qed "hcomplex_capproxD1";

(* same proof *)
Goal "Abs_hcomplex(hcomplexrel ``{%n. X n}) @c= Abs_hcomplex(hcomplexrel``{%n. Y n}) \
\     ==> Abs_hypreal(hyprel `` {%n. Im(X n)}) @= \
\         Abs_hypreal(hyprel `` {%n. Im(Y n)})";
by (auto_tac (claset(),simpset() addsimps [approx_FreeUltrafilterNat_iff]));
by (dtac (capprox_minus_iff RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_minus,hcomplex_add,
    mem_cinfmal_iff RS sym,CInfinitesimal_hcmod_iff,hcmod,
    Infinitesimal_FreeUltrafilterNat_iff2]));
by (dres_inst_tac [("x","m")] spec 1);
by (Ultra_tac 1);
by (rename_tac "Z x" 1);
by (res_inst_tac [("z","X x")] eq_Abs_complex 1);
by (res_inst_tac [("z","Y x")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_minus,complex_add,
    complex_mod] delsimps [realpow_Suc]));
by (rtac order_le_less_trans 1 THEN assume_tac 2);
by (dres_inst_tac [("t","Z x")] sym 1);
by (auto_tac (claset(),simpset() addsimps [abs_eqI1] delsimps [realpow_Suc]));
qed "hcomplex_capproxD2";

Goal "[| Abs_hypreal(hyprel `` {%n. Re(X n)}) @= \
\        Abs_hypreal(hyprel `` {%n. Re(Y n)}); \
\        Abs_hypreal(hyprel `` {%n. Im(X n)}) @= \
\        Abs_hypreal(hyprel `` {%n. Im(Y n)}) \
\     |] ==> Abs_hcomplex(hcomplexrel ``{%n. X n}) @c= Abs_hcomplex(hcomplexrel``{%n. Y n})";
by (dtac (approx_minus_iff RS iffD1) 1);
by (dtac (approx_minus_iff RS iffD1) 1);
by (rtac (capprox_minus_iff RS iffD2) 1);
by (auto_tac (claset(),simpset() addsimps [mem_cinfmal_iff RS sym,
    mem_infmal_iff RS sym,hypreal_minus,hypreal_add,hcomplex_minus,
    hcomplex_add,CInfinitesimal_hcmod_iff,hcmod,Infinitesimal_FreeUltrafilterNat_iff]));
by (rtac bexI 1 THEN rtac lemma_hyprel_refl 2);
by Auto_tac;
by (dres_inst_tac [("x","u/2")] spec 1);
by (dres_inst_tac [("x","u/2")] spec 1);
by (Step_tac 1);
by (TRYALL(Force_tac));
by (ultra_tac (claset(),HOL_ss) 1);
by (dtac sym 1 THEN dtac sym 1);
by (res_inst_tac [("z","X x")] eq_Abs_complex 1);
by (res_inst_tac [("z","Y x")] eq_Abs_complex 1);
by (auto_tac (claset(),HOL_ss addsimps [complex_minus,complex_add,
    complex_mod,pair_mem_complex RS Abs_complex_inverse,snd_conv,
    fst_conv,two_eq_Suc_Suc]));
by (rtac (realpow_two_abs RS subst) 1);
by (res_inst_tac [("x1","xa + - xb")] (realpow_two_abs RS subst) 1);
by (simp_tac (simpset() addsimps [two_eq_Suc_Suc RS sym]) 1);
by (rtac lemma_sqrt_hcomplex_capprox 1);
by Auto_tac;
qed "hcomplex_capproxI";

Goal "(Abs_hcomplex(hcomplexrel ``{%n. X n}) @c= Abs_hcomplex(hcomplexrel``{%n. Y n})) =\
\      (Abs_hypreal(hyprel `` {%n. Re(X n)}) @= Abs_hypreal(hyprel `` {%n. Re(Y n)}) & \
\       Abs_hypreal(hyprel `` {%n. Im(X n)}) @= Abs_hypreal(hyprel `` {%n. Im(Y n)}))";
by (blast_tac (claset() addIs [hcomplex_capproxI,hcomplex_capproxD1,hcomplex_capproxD2]) 1);
qed "capprox_approx_iff";

Goal "(hcomplex_of_hypreal x @c= hcomplex_of_hypreal z) = (x @= z)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    capprox_approx_iff]));
qed "hcomplex_of_hypreal_capprox_iff";
Addsimps [hcomplex_of_hypreal_capprox_iff];

Goal "Abs_hcomplex(hcomplexrel ``{%n. X n}) : CFinite \
\     ==> Abs_hypreal(hyprel `` {%n. Re(X n)}) : HFinite";
by (auto_tac (claset(),simpset() addsimps [CFinite_hcmod_iff,
    hcmod,HFinite_FreeUltrafilterNat_iff]));
by (rtac bexI 1 THEN rtac lemma_hyprel_refl 2);
by (res_inst_tac [("x","u")] exI 1 THEN Auto_tac);
by (Ultra_tac 1);
by (dtac sym 1 THEN res_inst_tac [("z","X x")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mod,two_eq_Suc_Suc] delsimps [realpow_Suc]));
by (rtac ccontr 1 THEN dtac real_leI 1);
by (dtac order_less_le_trans 1 THEN assume_tac 1);
by (dtac (real_sqrt_ge_abs1 RSN (2,order_less_le_trans)) 1);
by (auto_tac (claset(),simpset() addsimps [two_eq_Suc_Suc RS sym]));
qed "CFinite_HFinite_Re";

Goal "Abs_hcomplex(hcomplexrel ``{%n. X n}) : CFinite \
\     ==> Abs_hypreal(hyprel `` {%n. Im(X n)}) : HFinite";
by (auto_tac (claset(),simpset() addsimps [CFinite_hcmod_iff,
    hcmod,HFinite_FreeUltrafilterNat_iff]));
by (rtac bexI 1 THEN rtac lemma_hyprel_refl 2);
by (res_inst_tac [("x","u")] exI 1 THEN Auto_tac);
by (Ultra_tac 1);
by (dtac sym 1 THEN res_inst_tac [("z","X x")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mod] delsimps [realpow_Suc]));
by (rtac ccontr 1 THEN dtac real_leI 1);
by (dtac order_less_le_trans 1 THEN assume_tac 1);
by (dtac (real_sqrt_ge_abs2 RSN (2,order_less_le_trans)) 1);
by Auto_tac;
qed "CFinite_HFinite_Im";

Goal "[| Abs_hypreal(hyprel `` {%n. Re(X n)}) : HFinite; \
\        Abs_hypreal(hyprel `` {%n. Im(X n)}) : HFinite \
\     |] ==> Abs_hcomplex(hcomplexrel ``{%n. X n}) : CFinite";
by (auto_tac (claset(),simpset() addsimps [CFinite_hcmod_iff,
    hcmod,HFinite_FreeUltrafilterNat_iff]));
by (rename_tac "Y Z u v" 1);
by (rtac bexI 1 THEN rtac lemma_hyprel_refl 2);
by (res_inst_tac [("x","2*(u + v)")] exI 1);
by (Ultra_tac 1);
by (dtac sym 1 THEN res_inst_tac [("z","X x")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mod,two_eq_Suc_Suc] delsimps [realpow_Suc]));
by (subgoal_tac "0 < u" 1 THEN arith_tac 2);
by (subgoal_tac "0 < v" 1 THEN arith_tac 2);
by (rtac (realpow_two_abs RS subst) 1);
by (res_inst_tac [("x1","Y x")] (realpow_two_abs RS subst) 1);
by (simp_tac (simpset() addsimps [two_eq_Suc_Suc RS sym]) 1);
by (rtac lemma_sqrt_hcomplex_capprox 1);
by Auto_tac;
qed "HFinite_Re_Im_CFinite";

Goal "(Abs_hcomplex(hcomplexrel ``{%n. X n}) : CFinite) = \
\     (Abs_hypreal(hyprel `` {%n. Re(X n)}) : HFinite & \
\      Abs_hypreal(hyprel `` {%n. Im(X n)}) : HFinite)";
by (blast_tac (claset() addIs [HFinite_Re_Im_CFinite,CFinite_HFinite_Im,
    CFinite_HFinite_Re]) 1);
qed "CFinite_HFinite_iff";

Goal "Abs_hcomplex(hcomplexrel ``{%n. X n}) : SComplex \
\     ==> Abs_hypreal(hyprel `` {%n. Re(X n)}) : Reals";
by (auto_tac (claset(),simpset() addsimps [SComplex_def,
    hcomplex_of_complex_def,SReal_def,hypreal_of_real_def]));
by (res_inst_tac [("x","Re r")] exI 1);
by (Ultra_tac 1);
qed "SComplex_Re_SReal";

Goal "Abs_hcomplex(hcomplexrel ``{%n. X n}) : SComplex \
\     ==> Abs_hypreal(hyprel `` {%n. Im(X n)}) : Reals";
by (auto_tac (claset(),simpset() addsimps [SComplex_def,
    hcomplex_of_complex_def,SReal_def,hypreal_of_real_def]));
by (res_inst_tac [("x","Im r")] exI 1);
by (Ultra_tac 1);
qed "SComplex_Im_SReal";

Goal "[| Abs_hypreal(hyprel `` {%n. Re(X n)}) : Reals; \
\        Abs_hypreal(hyprel `` {%n. Im(X n)}) : Reals \
\     |] ==> Abs_hcomplex(hcomplexrel ``{%n. X n}) : SComplex";
by (auto_tac (claset(),simpset() addsimps [SComplex_def,
    hcomplex_of_complex_def,SReal_def,hypreal_of_real_def]));
by (res_inst_tac [("x","complex_of_real r + ii  * complex_of_real ra")] exI 1);
by (Ultra_tac 1);
by (res_inst_tac [("z","X x")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_of_real_def,i_def,
    complex_add,complex_mult]));
qed "Reals_Re_Im_SComplex";

Goal "(Abs_hcomplex(hcomplexrel ``{%n. X n}) : SComplex) = \
\     (Abs_hypreal(hyprel `` {%n. Re(X n)}) : Reals & \
\      Abs_hypreal(hyprel `` {%n. Im(X n)}) : Reals)";
by (blast_tac (claset() addIs [SComplex_Re_SReal,SComplex_Im_SReal,
    Reals_Re_Im_SComplex]) 1);
qed "SComplex_SReal_iff";

Goal "(Abs_hcomplex(hcomplexrel ``{%n. X n}) : CInfinitesimal) = \
\     (Abs_hypreal(hyprel `` {%n. Re(X n)}) : Infinitesimal & \
\      Abs_hypreal(hyprel `` {%n. Im(X n)}) : Infinitesimal)";
by (auto_tac (claset(),simpset() addsimps [mem_cinfmal_iff,
    mem_infmal_iff,hcomplex_zero_num,hypreal_zero_num,capprox_approx_iff]));
qed "CInfinitesimal_Infinitesimal_iff";

(*** more lemmas ****)
Goal "(EX t. P t) = (EX X. P (Abs_hcomplex(hcomplexrel `` {X})))";
by Auto_tac;
by (res_inst_tac [("z","t")] eq_Abs_hcomplex 1);
by Auto_tac;
qed "eq_Abs_hcomplex_EX";

Goal "(EX t : A. P t) = (EX X. (Abs_hcomplex(hcomplexrel `` {X})) : A & \
\                        P (Abs_hcomplex(hcomplexrel `` {X})))";
by Auto_tac;
by (res_inst_tac [("z","t")] eq_Abs_hcomplex 1);
by Auto_tac;
qed "eq_Abs_hcomplex_Bex";

(* Here we go - easy proof now!! *)
Goal "x:CFinite ==> EX t: SComplex. x @c= t";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [CFinite_HFinite_iff,
    eq_Abs_hcomplex_Bex,SComplex_SReal_iff,capprox_approx_iff]));
by (REPEAT(dtac st_part_Ex 1 THEN Step_tac 1));
by (res_inst_tac [("z","t")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","ta")] eq_Abs_hypreal 1);
by Auto_tac;
by (res_inst_tac [("x","%n. complex_of_real (xa n) + ii * complex_of_real (xb n)")]
    exI 1);
by Auto_tac;
qed "stc_part_Ex";

Goal "x:CFinite ==> EX! t. t : SComplex &  x @c= t";
by (dtac stc_part_Ex 1 THEN Step_tac 1);
by (dtac capprox_sym 2 THEN dtac capprox_sym 2 
    THEN dtac capprox_sym 2);
by (auto_tac (claset() addSIs [capprox_unique_complex], simpset()));
qed "stc_part_Ex1";

Goalw [CFinite_def,CInfinite_def] "CFinite Int CInfinite = {}";
by Auto_tac;
qed "CFinite_Int_CInfinite_empty";
Addsimps [CFinite_Int_CInfinite_empty];

Goal "x: CFinite ==> x ~: CInfinite";
by (EVERY1[Step_tac, dtac IntI, assume_tac]);
by Auto_tac;
qed "CFinite_not_CInfinite";

Goal "x~: CFinite ==> x: CInfinite";
by (auto_tac (claset() addIs [not_HFinite_HInfinite],
    simpset() addsimps [CFinite_hcmod_iff,CInfinite_hcmod_iff]));
qed "not_CFinite_CInfinite";

Goal "x : CInfinite | x : CFinite";
by (blast_tac (claset() addIs [not_CFinite_CInfinite]) 1);
qed "CInfinite_CFinite_disj";

Goal "(x : CInfinite) = (x ~: CFinite)";
by (blast_tac (claset() addDs [CFinite_not_CInfinite,
               not_CFinite_CInfinite]) 1);
qed "CInfinite_CFinite_iff";

Goal "(x : CFinite) = (x ~: CInfinite)";
by (simp_tac (simpset() addsimps [CInfinite_CFinite_iff]) 1);
qed "CFinite_CInfinite_iff";

Goal "x ~: CInfinitesimal ==> x : CInfinite | x : CFinite - CInfinitesimal";
by (fast_tac (claset() addIs [not_CFinite_CInfinite]) 1);
qed "CInfinite_diff_CFinite_CInfinitesimal_disj";

Goal "[| x : CFinite; x ~: CInfinitesimal |] ==> inverse x : CFinite";
by (cut_inst_tac [("x","inverse x")] CInfinite_CFinite_disj 1);
by (auto_tac (claset() addSDs [CInfinite_inverse_CInfinitesimal], simpset()));
qed "CFinite_inverse";

Goal "x : CFinite - CInfinitesimal ==> inverse x : CFinite";
by (blast_tac (claset() addIs [CFinite_inverse]) 1);
qed "CFinite_inverse2";

Goal "x ~: CInfinitesimal ==> inverse(x) : CFinite";
by (dtac CInfinite_diff_CFinite_CInfinitesimal_disj 1);
by (blast_tac (claset() addIs [CFinite_inverse,
                 CInfinite_inverse_CInfinitesimal,
                 CInfinitesimal_subset_CFinite RS subsetD]) 1);
qed "CInfinitesimal_inverse_CFinite";


Goal "x : CFinite - CInfinitesimal ==> inverse x : CFinite - CInfinitesimal";
by (auto_tac (claset() addIs [CInfinitesimal_inverse_CFinite], simpset()));
by (dtac CInfinitesimal_CFinite_mult2 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [not_CInfinitesimal_not_zero]) 1); 
qed "CFinite_not_CInfinitesimal_inverse";

Goal "[| x @c= y; y :  CFinite - CInfinitesimal |] \
\     ==> inverse x @c= inverse y";
by (forward_tac [CFinite_diff_CInfinitesimal_capprox] 1);
by (assume_tac 1);
by (forward_tac [not_CInfinitesimal_not_zero2] 1);
by (forw_inst_tac [("x","x")] not_CInfinitesimal_not_zero2 1);
by (REPEAT(dtac CFinite_inverse2 1));
by (dtac capprox_mult2 1 THEN assume_tac 1);
by Auto_tac;
by (dres_inst_tac [("c","inverse x")] capprox_mult1 1 
    THEN assume_tac 1);
by (auto_tac (claset() addIs [capprox_sym],
    simpset() addsimps [hcomplex_mult_assoc]));
qed "capprox_inverse";

bind_thm ("hcomplex_of_complex_capprox_inverse",
       hcomplex_of_complex_CFinite_diff_CInfinitesimal RSN (2, capprox_inverse));

Goal "[| x: CFinite - CInfinitesimal; \
\        h : CInfinitesimal |] ==> inverse(x + h) @c= inverse x";
by (auto_tac (claset() addIs [capprox_inverse, capprox_sym, 
                              CInfinitesimal_add_capprox_self], 
              simpset()));
qed "inverse_add_CInfinitesimal_capprox";

Goal "[| x: CFinite - CInfinitesimal; \
\        h : CInfinitesimal |] ==> inverse(h + x) @c= inverse x";
by (rtac (hcomplex_add_commute RS subst) 1);
by (blast_tac (claset() addIs [inverse_add_CInfinitesimal_capprox]) 1);
qed "inverse_add_CInfinitesimal_capprox2";

Goal "[| x : CFinite - CInfinitesimal; \
\        h : CInfinitesimal |] ==> inverse(x + h) - inverse x @c= h"; 
by (rtac capprox_trans2 1);
by (auto_tac (claset() addIs [inverse_add_CInfinitesimal_capprox],
              simpset() addsimps [mem_cinfmal_iff,hcomplex_diff_def,
                                  capprox_minus_iff RS sym]));
qed "inverse_add_CInfinitesimal_approx_CInfinitesimal";

Goal "(x*x : CInfinitesimal) = (x : CInfinitesimal)";
by (auto_tac (claset(), simpset() addsimps [CInfinitesimal_hcmod_iff,
    hcmod_mult]));
qed "CInfinitesimal_square_iff";
AddIffs [CInfinitesimal_square_iff];

Goal "[| a: CFinite-CInfinitesimal; a*w @c= a*z |] ==> w @c= z";
by (Step_tac 1);
by (ftac CFinite_inverse 1 THEN assume_tac 1);
by (dtac not_CInfinitesimal_not_zero 1);
by (auto_tac (claset() addDs [capprox_mult2],
    simpset() addsimps [hcomplex_mult_assoc RS sym]));
qed "capprox_CFinite_mult_cancel";

Goal "a: CFinite-CInfinitesimal ==> (a * w @c= a * z) = (w @c= z)";
by (auto_tac (claset() addIs [capprox_mult2,
    capprox_CFinite_mult_cancel], simpset()));
qed "capprox_CFinite_mult_cancel_iff1";


(*---------------------------------------------------------------------------*)
(* Theorems about monads                                                     *)
(*---------------------------------------------------------------------------*)

Goalw [cmonad_def] "(x @c= y) = (cmonad(x)=cmonad(y))";
by (auto_tac (claset() addDs [capprox_sym] 
                       addSEs [capprox_trans,equalityCE],
              simpset()));
qed "capprox_cmonad_iff";

Goal "e : CInfinitesimal ==> cmonad (x+e) = cmonad x";
by (fast_tac (claset() addSIs [CInfinitesimal_add_capprox_self RS capprox_sym,
    capprox_cmonad_iff RS iffD1]) 1);
qed "CInfinitesimal_cmonad_eq";

Goalw [cmonad_def] "(u:cmonad x) = (-u:cmonad (-x))";
by Auto_tac;
qed "mem_cmonad_iff";

Goalw [cmonad_def] "(x:CInfinitesimal) = (x:cmonad 0)";
by (auto_tac (claset() addIs [capprox_sym],
    simpset() addsimps [mem_cinfmal_iff]));
qed "CInfinitesimal_cmonad_zero_iff";

Goal "(x:cmonad 0) = (-x:cmonad 0)";
by (simp_tac (simpset() addsimps [CInfinitesimal_cmonad_zero_iff RS sym]) 1);
qed "cmonad_zero_minus_iff";

Goal "(x:cmonad 0) = (hcmod x:monad 0)";
by (auto_tac (claset(), simpset() addsimps 
    [CInfinitesimal_cmonad_zero_iff RS sym,
     CInfinitesimal_hcmod_iff,Infinitesimal_monad_zero_iff RS sym]));
qed "cmonad_zero_hcmod_iff";

Goalw [cmonad_def] "x:cmonad x";
by (Simp_tac 1);
qed "mem_cmonad_self";
Addsimps [mem_cmonad_self];

(*---------------------------------------------------------------------------*)
(* Theorems about standard part                                              *)
(*---------------------------------------------------------------------------*)
Goalw [stc_def] "x: CFinite ==> stc x @c= x";
by (forward_tac [stc_part_Ex] 1 THEN Step_tac 1);
by (rtac someI2 1);
by (auto_tac (claset() addIs [capprox_sym], simpset()));
qed "stc_capprox_self";

Goalw [stc_def] "x: CFinite ==> stc x: SComplex";
by (forward_tac [stc_part_Ex] 1 THEN Step_tac 1);
by (rtac someI2 1);
by (auto_tac (claset() addIs [capprox_sym], simpset()));
qed "stc_SComplex";

Goal "x: CFinite ==> stc x: CFinite";
by (etac (stc_SComplex RS (SComplex_subset_CFinite RS subsetD)) 1);
qed "stc_CFinite";

Goalw [stc_def] "x: SComplex ==> stc x = x";
by (rtac some_equality 1);
by (auto_tac (claset() addIs [(SComplex_subset_CFinite RS subsetD)],simpset()));
by (blast_tac (claset() addDs [SComplex_capprox_iff RS iffD1]) 1);
qed "stc_SComplex_eq";
Addsimps [stc_SComplex_eq];

Goal "stc (hcomplex_of_complex x) = hcomplex_of_complex x";
by Auto_tac;
qed "stc_hcomplex_of_complex";

Goal "[| x: CFinite; y: CFinite; stc x = stc y |] ==> x @c= y";
by (auto_tac (claset() addSDs [stc_capprox_self] 
              addSEs [capprox_trans3], simpset()));
qed "stc_eq_capprox";

Goal "[| x: CFinite; y: CFinite; x @c= y |] ==> stc x = stc y";
by (EVERY1 [forward_tac [stc_capprox_self],
    forw_inst_tac [("x","y")] stc_capprox_self,
    dtac stc_SComplex,dtac stc_SComplex]);
by (fast_tac (claset() addEs [capprox_trans,
    capprox_trans2,SComplex_capprox_iff RS iffD1]) 1);
qed "capprox_stc_eq";

Goal "[| x: CFinite; y: CFinite|] ==> (x @c= y) = (stc x = stc y)";
by (blast_tac (claset() addIs [capprox_stc_eq,stc_eq_capprox]) 1);
qed "stc_eq_capprox_iff";

Goal "[| x: SComplex; e: CInfinitesimal |] ==> stc(x + e) = x";
by (forward_tac [stc_SComplex_eq RS subst] 1);
by (assume_tac 2);
by (forward_tac [SComplex_subset_CFinite RS subsetD] 1);
by (forward_tac [CInfinitesimal_subset_CFinite RS subsetD] 1);
by (dtac stc_SComplex_eq 1);
by (rtac capprox_stc_eq 1);
by (auto_tac (claset() addIs  [CFinite_add],
    simpset() addsimps [CInfinitesimal_add_capprox_self 
    RS capprox_sym]));
qed "stc_CInfinitesimal_add_SComplex";

Goal "[| x: SComplex; e: CInfinitesimal |] ==> stc(e + x) = x";
by (rtac (hcomplex_add_commute RS subst) 1);
by (blast_tac (claset() addSIs [stc_CInfinitesimal_add_SComplex]) 1);
qed "stc_CInfinitesimal_add_SComplex2";

Goal "x: CFinite ==> EX e: CInfinitesimal. x = stc(x) + e";
by (blast_tac (claset() addSDs [(stc_capprox_self RS 
    capprox_sym),bex_CInfinitesimal_iff2 RS iffD2]) 1);
qed "CFinite_stc_CInfinitesimal_add";

Goal "[| x: CFinite; y: CFinite |] ==> stc (x + y) = stc(x) + stc(y)";
by (forward_tac [CFinite_stc_CInfinitesimal_add] 1);
by (forw_inst_tac [("x","y")] CFinite_stc_CInfinitesimal_add 1);
by (Step_tac 1);
by (subgoal_tac "stc (x + y) = stc ((stc x + e) + (stc y + ea))" 1);
by (dtac sym 2 THEN dtac sym 2);
by (Asm_full_simp_tac 2);
by (asm_simp_tac (simpset() addsimps hcomplex_add_ac) 1);
by (REPEAT(dtac stc_SComplex 1));
by (dtac SComplex_add 1 THEN assume_tac 1);
by (dtac CInfinitesimal_add 1 THEN assume_tac 1);
by (rtac (hcomplex_add_assoc RS subst) 1);
by (blast_tac (claset() addSIs [stc_CInfinitesimal_add_SComplex2]) 1);
qed "stc_add";

Goal "stc (number_of w) = number_of w";
by (rtac (SComplex_number_of RS stc_SComplex_eq) 1);
qed "stc_number_of";
Addsimps [stc_number_of];

Goal "stc 0 = 0";
by (Simp_tac 1);
qed "stc_zero";
Addsimps [stc_zero];

Goal "stc 1 = 1";
by (Simp_tac 1);
qed "stc_one";
Addsimps [stc_one];

Goal "y: CFinite ==> stc(-y) = -stc(y)";
by (forward_tac [CFinite_minus_iff RS iffD2] 1);
by (rtac hcomplex_add_minus_eq_minus 1);
by (dtac (stc_add RS sym) 1 THEN assume_tac 1);
by (asm_simp_tac (simpset() addsimps [add_commute]) 1); 
qed "stc_minus";

Goalw [hcomplex_diff_def]
     "[| x: CFinite; y: CFinite |] ==> stc (x-y) = stc(x) - stc(y)";
by (forw_inst_tac [("y1","y")] (stc_minus RS sym) 1);
by (dres_inst_tac [("x1","y")] (CFinite_minus_iff RS iffD2) 1);
by (auto_tac (claset() addIs [stc_add],simpset()));
qed "stc_diff";

Goal "[| x: CFinite; y: CFinite; \
\        e: CInfinitesimal;       \
\        ea: CInfinitesimal |]   \
\      ==> e*y + x*ea + e*ea: CInfinitesimal";
by (forw_inst_tac [("x","e"),("y","y")] CInfinitesimal_CFinite_mult 1);
by (forw_inst_tac [("x","ea"),("y","x")] CInfinitesimal_CFinite_mult 2);
by (dtac CInfinitesimal_mult 3);
by (auto_tac (claset() addIs [CInfinitesimal_add],
              simpset() addsimps hcomplex_add_ac @ hcomplex_mult_ac));
qed "lemma_stc_mult";

Goal "[| x: CFinite; y: CFinite |] \
\              ==> stc (x * y) = stc(x) * stc(y)";
by (forward_tac [CFinite_stc_CInfinitesimal_add] 1);
by (forw_inst_tac [("x","y")] CFinite_stc_CInfinitesimal_add 1);
by (Step_tac 1);
by (subgoal_tac "stc (x * y) = stc ((stc x + e) * (stc y + ea))" 1);
by (dtac sym 2 THEN dtac sym 2);
by (Asm_full_simp_tac 2);
by (thin_tac "x = stc x + e" 1);
by (thin_tac "y = stc y + ea" 1);
by (asm_full_simp_tac (simpset() addsimps 
    [hcomplex_add_mult_distrib,hcomplex_add_mult_distrib2]) 1);
by (REPEAT(dtac stc_SComplex 1));
by (full_simp_tac (simpset() addsimps [hcomplex_add_assoc]) 1);
by (rtac stc_CInfinitesimal_add_SComplex 1);
by (blast_tac (claset() addSIs [SComplex_mult]) 1);
by (REPEAT(dtac (SComplex_subset_CFinite RS subsetD) 1));
by (rtac (hcomplex_add_assoc RS subst) 1);
by (blast_tac (claset() addSIs [lemma_stc_mult]) 1);
qed "stc_mult";

Goal "x: CInfinitesimal ==> stc x = 0";
by (rtac (stc_zero RS subst) 1);
by (rtac capprox_stc_eq 1);
by (auto_tac (claset() addIs [CInfinitesimal_subset_CFinite RS subsetD],
              simpset() addsimps [mem_cinfmal_iff RS sym]));
qed "stc_CInfinitesimal";

Goal "stc(x) ~= 0 ==> x ~: CInfinitesimal";
by (fast_tac (claset() addIs [stc_CInfinitesimal]) 1);
qed "stc_not_CInfinitesimal";

Goal "[| x: CFinite; stc x ~= 0 |] \
\     ==> stc(inverse x) = inverse (stc x)";
by (res_inst_tac [("c1","stc x")] (hcomplex_mult_left_cancel RS iffD1) 1);
by (auto_tac (claset(),
       simpset() addsimps [stc_mult RS sym, stc_not_CInfinitesimal,
                           CFinite_inverse]));
by (stac right_inverse 1); 
by Auto_tac;  
qed "stc_inverse";

Goal "[| x: CFinite; y: CFinite; stc y ~= 0 |] \
\     ==> stc(x/y) = (stc x) / (stc y)";
by (auto_tac (claset(),
      simpset() addsimps [hcomplex_divide_def, stc_mult, stc_not_CInfinitesimal, 
                          CFinite_inverse, stc_inverse]));
qed "stc_divide";
Addsimps [stc_divide];

Goal "x: CFinite ==> stc(stc(x)) = stc(x)";
by (blast_tac (claset() addIs [stc_CFinite, stc_capprox_self,
                               capprox_stc_eq]) 1);
qed "stc_idempotent";
Addsimps [stc_idempotent];

Goal "z : HFinite ==> hcomplex_of_hypreal z : CFinite";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    CFinite_HFinite_iff,symmetric hypreal_zero_def]));
qed "CFinite_HFinite_hcomplex_of_hypreal";

Goal "x : Reals ==>  hcomplex_of_hypreal x : SComplex";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_hypreal,
    SComplex_SReal_iff,symmetric hypreal_zero_def]));
qed "SComplex_SReal_hcomplex_of_hypreal";

Goalw [st_def,stc_def] 
 "z : HFinite ==> stc(hcomplex_of_hypreal z) = hcomplex_of_hypreal (st z)";
by (ftac st_part_Ex 1 THEN Step_tac 1);
by (rtac someI2 1);
by (auto_tac (claset() addIs [approx_sym],simpset()));
by (dtac CFinite_HFinite_hcomplex_of_hypreal 1);
by (ftac stc_part_Ex 1 THEN Step_tac 1);
by (rtac someI2 1);
by (auto_tac (claset() addIs [capprox_sym] addSIs [capprox_unique_complex] 
    addDs [SComplex_SReal_hcomplex_of_hypreal],simpset()));
qed "stc_hcomplex_of_hypreal";

(*
Goal "x: CFinite ==> hcmod(stc x) = st(hcmod x)";
by (dtac stc_capprox_self 1);
by (auto_tac (claset(),simpset() addsimps [bex_CInfinitesimal_iff2 RS sym]));


approx_hcmod_add_hcmod
*)

(*---------------------------------------------------------------------------*)
(* More nonstandard complex specific theorems                                *)        
(*---------------------------------------------------------------------------*)
Goal "(hcnj z : CInfinitesimal) = (z : CInfinitesimal)";
by (auto_tac (claset(),simpset() addsimps [CInfinitesimal_hcmod_iff]));
qed "CInfinitesimal_hcnj_iff";
Addsimps [CInfinitesimal_hcnj_iff];

Goal "(Abs_hcomplex(hcomplexrel ``{%n. X n}) : CInfinite) = \
\     (Abs_hypreal(hyprel `` {%n. Re(X n)}) : HInfinite | \
\      Abs_hypreal(hyprel `` {%n. Im(X n)}) : HInfinite)";
by (auto_tac (claset(),simpset() addsimps [CInfinite_CFinite_iff,
    HInfinite_HFinite_iff,CFinite_HFinite_iff]));
qed "CInfinite_HInfinite_iff";

Goal "(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y : CInfinitesimal) = \
\     (x : Infinitesimal & y : Infinitesimal)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [iii_def,hcomplex_add,hcomplex_mult,
    hcomplex_of_hypreal,CInfinitesimal_Infinitesimal_iff]));
qed "hcomplex_split_CInfinitesimal_iff";

Goal "(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y : CFinite) = \
\     (x : HFinite & y : HFinite)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [iii_def,hcomplex_add,hcomplex_mult,
    hcomplex_of_hypreal,CFinite_HFinite_iff]));
qed "hcomplex_split_CFinite_iff";

Goal "(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y : SComplex) = \
\     (x : Reals & y : Reals)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [iii_def,hcomplex_add,hcomplex_mult,
    hcomplex_of_hypreal,SComplex_SReal_iff]));
qed "hcomplex_split_SComplex_iff";

Goal "(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y : CInfinite) = \
\     (x : HInfinite | y : HInfinite)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [iii_def,hcomplex_add,hcomplex_mult,
    hcomplex_of_hypreal,CInfinite_HInfinite_iff]));
qed "hcomplex_split_CInfinite_iff";

Goal "(hcomplex_of_hypreal x + iii * hcomplex_of_hypreal y @c= \
\      hcomplex_of_hypreal x' + iii * hcomplex_of_hypreal y') = \
\     (x @= x' & y @= y')";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","x'")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y'")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [iii_def,hcomplex_add,hcomplex_mult,
    hcomplex_of_hypreal,capprox_approx_iff]));
qed "hcomplex_split_capprox_iff";

(*** More theorems ***)

Goal "ALL n. cmod (X n - x) < inverse (real (Suc n)) ==> \
\     Abs_hcomplex(hcomplexrel``{X}) - hcomplex_of_complex x : CInfinitesimal";
by (auto_tac (claset(),simpset() addsimps [hcomplex_diff,
    CInfinitesimal_hcmod_iff,hcomplex_of_complex_def,
    Infinitesimal_FreeUltrafilterNat_iff,hcmod]));
by (rtac bexI 1 THEN Auto_tac);
by (auto_tac (claset() addDs [FreeUltrafilterNat_inverse_real_of_posnat,
                  FreeUltrafilterNat_all,FreeUltrafilterNat_Int] 
           addIs [order_less_trans, FreeUltrafilterNat_subset],
      simpset()));
qed "complex_seq_to_hcomplex_CInfinitesimal";

Goal "hcomplex_of_hypreal epsilon : CInfinitesimal";
by (auto_tac (claset(),simpset() addsimps [CInfinitesimal_hcmod_iff]));
qed "CInfinitesimal_hcomplex_of_hypreal_epsilon";
Addsimps [CInfinitesimal_hcomplex_of_hypreal_epsilon];

Goal "(hcomplex_of_complex z @c= 0) = (z = 0)";
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_complex_zero RS sym]
    delsimps [hcomplex_of_complex_zero]));
qed "hcomplex_of_complex_approx_zero_iff";

Goal "(0 @c= hcomplex_of_complex z) = (z = 0)";
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_complex_zero RS sym]
    delsimps [hcomplex_of_complex_zero]));
qed "hcomplex_of_complex_approx_zero_iff2";

Addsimps [hcomplex_of_complex_approx_zero_iff,hcomplex_of_complex_approx_zero_iff2];


