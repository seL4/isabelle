(*  Title       : CLim.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh
    Description : A first theory of limits, continuity and 
                  differentiation for complex functions
*)

(*-----------------------------------------------------------------------*)
(* Limit of complex to complex function                                               *)
(*-----------------------------------------------------------------------*)

Goalw [NSCLIM_def,NSCRLIM_def] 
   "f -- a --NSC> L ==> (%x. Re(f x)) -- a --NSCR> Re(L)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunC_approx_Re_Im_iff,
    hRe_hcomplex_of_complex]));
qed "NSCLIM_NSCRLIM_Re";

Goalw [NSCLIM_def,NSCRLIM_def] 
   "f -- a --NSC> L ==> (%x. Im(f x)) -- a --NSCR> Im(L)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunC_approx_Re_Im_iff,
    hIm_hcomplex_of_complex]));
qed "NSCLIM_NSCRLIM_Im";

Goalw [CLIM_def,NSCLIM_def,capprox_def] 
      "f -- x --C> L ==> f -- x --NSC> L";
by Auto_tac;
by (res_inst_tac [("z","xa")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_complex_def,
    starfunC,hcomplex_diff,CInfinitesimal_hcmod_iff,hcmod,
    Infinitesimal_FreeUltrafilterNat_iff]));
by (rtac bexI 1 THEN rtac lemma_hyprel_refl 2);
by (Step_tac 1);
by (dres_inst_tac [("x","u")] spec 1 THEN Auto_tac);
by (dres_inst_tac [("x","s")] spec 1 THEN Auto_tac);
by (Ultra_tac 1);
by (dtac sym 1 THEN Auto_tac);
qed "CLIM_NSCLIM";

Goal "(ALL t. P t) = (ALL X. P (Abs_hcomplex(hcomplexrel `` {X})))";
by Auto_tac;
by (res_inst_tac [("z","t")] eq_Abs_hcomplex 1);
by Auto_tac;
qed "eq_Abs_hcomplex_ALL";

Goal "ALL s. 0 < s --> (EX xa.  xa ~= x & \
\        cmod (xa - x) < s  & r <= cmod (f xa - L)) \
\     ==> ALL (n::nat). EX xa.  xa ~= x & \
\             cmod(xa - x) < inverse(real(Suc n)) & r <= cmod(f xa - L)";
by (Clarify_tac 1); 
by (cut_inst_tac [("n1","n")]
    (real_of_nat_Suc_gt_zero RS positive_imp_inverse_positive) 1);
by Auto_tac;
val lemma_CLIM = result();

(* not needed? *)
Goal "ALL x z. EX y. Q x z y ==> EX f. ALL x z. Q x z (f x z)";
by (rtac choice 1 THEN Step_tac 1);
by (blast_tac (claset() addIs [choice]) 1);
qed "choice2";

Goal "ALL s. 0 < s --> (EX xa.  xa ~= x & \
\        cmod (xa - x) < s  & r <= cmod (f xa - L)) \
\     ==> EX X. ALL (n::nat). X n ~= x & \
\               cmod(X n - x) < inverse(real(Suc n)) & r <= cmod(f (X n) - L)";
by (dtac lemma_CLIM 1);
by (dtac choice 1);
by (Blast_tac 1);
val lemma_skolemize_CLIM2 = result();

Goal "ALL n. X n ~= x & \
\         cmod (X n - x) < inverse (real(Suc n)) & \
\         r <= cmod (f (X n) - L) ==> \
\         ALL n. cmod (X n - x) < inverse (real(Suc n))";
by (Auto_tac );
val lemma_csimp = result();

Goalw [CLIM_def,NSCLIM_def] 
     "f -- x --NSC> L ==> f -- x --C> L";
by (auto_tac (claset(),simpset() addsimps [eq_Abs_hcomplex_ALL,
    starfunC,CInfinitesimal_capprox_minus RS sym,hcomplex_diff,
    CInfinitesimal_hcmod_iff,hcomplex_of_complex_def,
    Infinitesimal_FreeUltrafilterNat_iff,hcmod]));
by (EVERY1[rtac ccontr, Asm_full_simp_tac]);
by (fold_tac [real_le_def]);
by (dtac lemma_skolemize_CLIM2 1);
by (Step_tac 1);
by (dres_inst_tac [("x","X")] spec 1);
by Auto_tac;
by (dtac (lemma_csimp RS complex_seq_to_hcomplex_CInfinitesimal) 1);
by (asm_full_simp_tac (simpset() addsimps [CInfinitesimal_hcmod_iff,
    hcomplex_of_complex_def,Infinitesimal_FreeUltrafilterNat_iff,
    hcomplex_diff,hcmod]) 1);
by (Blast_tac 1); 
by (dres_inst_tac [("x","r")] spec 1);
by (Clarify_tac 1);
by (dtac FreeUltrafilterNat_all 1);
by (Ultra_tac 1);
by (arith_tac 1);
qed "NSCLIM_CLIM";

(**** First key result ****)

Goal "(f -- x --C> L) = (f -- x --NSC> L)";
by (blast_tac (claset() addIs [CLIM_NSCLIM,NSCLIM_CLIM]) 1);
qed "CLIM_NSCLIM_iff";

(*-----------------------------------------------------------------------*)
(* Limit of complex to real function                                                  *)
(*-----------------------------------------------------------------------*)

Goalw [CRLIM_def,NSCRLIM_def,capprox_def] 
      "f -- x --CR> L ==> f -- x --NSCR> L";
by Auto_tac;
by (res_inst_tac [("z","xa")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_of_complex_def,
    starfunCR,hcomplex_diff,CInfinitesimal_hcmod_iff,hcmod,hypreal_diff,
    Infinitesimal_FreeUltrafilterNat_iff,Infinitesimal_approx_minus RS sym,
    hypreal_of_real_def]));
by (rtac bexI 1 THEN rtac lemma_hyprel_refl 2);
by (Step_tac 1);
by (dres_inst_tac [("x","u")] spec 1 THEN Auto_tac);
by (dres_inst_tac [("x","s")] spec 1 THEN Auto_tac);
by (Ultra_tac 1);
by (dtac sym 1 THEN Auto_tac);
qed "CRLIM_NSCRLIM";

Goal "ALL s. 0 < s --> (EX xa.  xa ~= x & \
\        cmod (xa - x) < s  & r <= abs (f xa - L)) \
\     ==> ALL (n::nat). EX xa.  xa ~= x & \
\             cmod(xa - x) < inverse(real(Suc n)) & r <= abs (f xa - L)";
by (Clarify_tac 1); 
by (cut_inst_tac [("n1","n")]
    (real_of_nat_Suc_gt_zero RS positive_imp_inverse_positive) 1);
by Auto_tac;
val lemma_CRLIM = result();

Goal "ALL s. 0 < s --> (EX xa.  xa ~= x & \
\        cmod (xa - x) < s  & r <= abs (f xa - L)) \
\     ==> EX X. ALL (n::nat). X n ~= x & \
\               cmod(X n - x) < inverse(real(Suc n)) & r <= abs (f (X n) - L)";
by (dtac lemma_CRLIM 1);
by (dtac choice 1);
by (Blast_tac 1);
val lemma_skolemize_CRLIM2 = result();

Goal "ALL n. X n ~= x & \
\         cmod (X n - x) < inverse (real(Suc n)) & \
\         r <= abs (f (X n) - L) ==> \
\         ALL n. cmod (X n - x) < inverse (real(Suc n))";
by (Auto_tac );
val lemma_crsimp = result();

Goalw [CRLIM_def,NSCRLIM_def,capprox_def] 
      "f -- x --NSCR> L ==> f -- x --CR> L";
by (auto_tac (claset(),simpset() addsimps [eq_Abs_hcomplex_ALL,
    starfunCR,hcomplex_diff,hcomplex_of_complex_def,hypreal_diff,
    CInfinitesimal_hcmod_iff,hcmod,Infinitesimal_approx_minus RS sym,
    Infinitesimal_FreeUltrafilterNat_iff]));
by (EVERY1[rtac ccontr, Asm_full_simp_tac]);
by (fold_tac [real_le_def]);
by (dtac lemma_skolemize_CRLIM2 1);
by (Step_tac 1);
by (dres_inst_tac [("x","X")] spec 1);
by Auto_tac;
by (dtac (lemma_crsimp RS complex_seq_to_hcomplex_CInfinitesimal) 1);
by (asm_full_simp_tac (simpset() addsimps [CInfinitesimal_hcmod_iff,
    hcomplex_of_complex_def,Infinitesimal_FreeUltrafilterNat_iff,
    hcomplex_diff,hcmod]) 1);
by (Blast_tac 1); 
by (auto_tac (claset(),simpset() addsimps [hypreal_of_real_def,
    hypreal_diff]));
by (dres_inst_tac [("x","r")] spec 1);
by (Clarify_tac 1);
by (dtac FreeUltrafilterNat_all 1);
by (Ultra_tac 1);
qed "NSCRLIM_CRLIM";

(** second key result **)
Goal "(f -- x --CR> L) = (f -- x --NSCR> L)";
by (blast_tac (claset() addIs [CRLIM_NSCRLIM,NSCRLIM_CRLIM]) 1);
qed "CRLIM_NSCRLIM_iff";

(** get this result easily now **)
Goal "f -- a --C> L ==> (%x. Re(f x)) -- a --CR> Re(L)";
by (auto_tac (claset() addDs [NSCLIM_NSCRLIM_Re],simpset() 
    addsimps [CLIM_NSCLIM_iff,CRLIM_NSCRLIM_iff RS sym]));
qed "CLIM_CRLIM_Re";

Goal "f -- a --C> L ==> (%x. Im(f x)) -- a --CR> Im(L)";
by (auto_tac (claset() addDs [NSCLIM_NSCRLIM_Im],simpset() 
    addsimps [CLIM_NSCLIM_iff,CRLIM_NSCRLIM_iff RS sym]));
qed "CLIM_CRLIM_Im";

Goal "f -- a --C> L ==> (%x. cnj (f x)) -- a --C> cnj L";
by (auto_tac (claset(),simpset() addsimps [CLIM_def,
    complex_cnj_diff RS sym]));
qed "CLIM_cnj";

Goal "((%x. cnj (f x)) -- a --C> cnj L) = (f -- a --C> L)";
by (auto_tac (claset(),simpset() addsimps [CLIM_def,
    complex_cnj_diff RS sym]));
qed "CLIM_cnj_iff";

(*** NSLIM_add hence CLIM_add *)

Goalw [NSCLIM_def]
     "[| f -- x --NSC> l; g -- x --NSC> m |] \
\     ==> (%x. f(x) + g(x)) -- x --NSC> (l + m)";
by (auto_tac (claset() addSIs [capprox_add], simpset()));
qed "NSCLIM_add";

Goal "[| f -- x --C> l; g -- x --C> m |] \
\     ==> (%x. f(x) + g(x)) -- x --C> (l + m)";
by (asm_full_simp_tac (simpset() addsimps [CLIM_NSCLIM_iff, NSCLIM_add]) 1);
qed "CLIM_add";

(*** NSLIM_mult hence CLIM_mult *)

Goalw [NSCLIM_def]
     "[| f -- x --NSC> l; g -- x --NSC> m |] \
\     ==> (%x. f(x) * g(x)) -- x --NSC> (l * m)";
by (auto_tac (claset() addSIs [capprox_mult_CFinite],  simpset()));
qed "NSCLIM_mult";

Goal "[| f -- x --C> l; g -- x --C> m |] \
\     ==> (%x. f(x) * g(x)) -- x --C> (l * m)";
by (asm_full_simp_tac (simpset() addsimps [CLIM_NSCLIM_iff, NSCLIM_mult]) 1);
qed "CLIM_mult";

(*** NSCLIM_const and CLIM_const ***)

Goalw [NSCLIM_def] "(%x. k) -- x --NSC> k";
by Auto_tac;
qed "NSCLIM_const";
Addsimps [NSCLIM_const];

Goalw [CLIM_def] "(%x. k) -- x --C> k";
by Auto_tac;
qed "CLIM_const";
Addsimps [CLIM_const];

(*** NSCLIM_minus and CLIM_minus ***)

Goalw [NSCLIM_def] 
      "f -- a --NSC> L ==> (%x. -f(x)) -- a --NSC> -L";
by Auto_tac;  
qed "NSCLIM_minus";

Goal "f -- a --C> L ==> (%x. -f(x)) -- a --C> -L";
by (asm_full_simp_tac (simpset() addsimps [CLIM_NSCLIM_iff, NSCLIM_minus]) 1);
qed "CLIM_minus";

(*** NSCLIM_diff hence CLIM_diff ***)

Goalw [complex_diff_def]
     "[| f -- x --NSC> l; g -- x --NSC> m |] \
\     ==> (%x. f(x) - g(x)) -- x --NSC> (l - m)";
by (auto_tac (claset(), simpset() addsimps [NSCLIM_add,NSCLIM_minus]));
qed "NSCLIM_diff";

Goal "[| f -- x --C> l; g -- x --C> m |] \
\     ==> (%x. f(x) - g(x)) -- x --C> (l - m)";
by (asm_full_simp_tac (simpset() addsimps [CLIM_NSCLIM_iff, NSCLIM_diff]) 1);
qed "CLIM_diff";

(*** NSCLIM_inverse and hence CLIM_inverse *)

Goalw [NSCLIM_def] 
     "[| f -- a --NSC> L;  L ~= 0 |] \
\     ==> (%x. inverse(f(x))) -- a --NSC> (inverse L)";
by (Clarify_tac 1);
by (dtac spec 1);
by (auto_tac (claset(), 
              simpset() addsimps [hcomplex_of_complex_capprox_inverse]));  
qed "NSCLIM_inverse";

Goal "[| f -- a --C> L;  L ~= 0 |] \
\     ==> (%x. inverse(f(x))) -- a --C> (inverse L)";
by (asm_full_simp_tac (simpset() addsimps [CLIM_NSCLIM_iff, NSCLIM_inverse]) 1);
qed "CLIM_inverse";

(*** NSCLIM_zero, CLIM_zero, etc. ***)

Goal "f -- a --NSC> l ==> (%x. f(x) - l) -- a --NSC> 0";
by (res_inst_tac [("z1","l")] (complex_add_minus_right_zero RS subst) 1);
by (rewtac complex_diff_def);
by (rtac NSCLIM_add 1 THEN Auto_tac);
qed "NSCLIM_zero";

Goal "f -- a --C> l ==> (%x. f(x) - l) -- a --C> 0";
by (asm_full_simp_tac (simpset() addsimps [CLIM_NSCLIM_iff, NSCLIM_zero]) 1);
qed "CLIM_zero";

Goal "(%x. f(x) - l) -- x --NSC> 0 ==> f -- x --NSC> l";
by (dres_inst_tac [("g","%x. l"),("m","l")] NSCLIM_add 1);
by Auto_tac;
qed "NSCLIM_zero_cancel";

Goal "(%x. f(x) - l) -- x --C> 0 ==> f -- x --C> l";
by (dres_inst_tac [("g","%x. l"),("m","l")] CLIM_add 1);
by Auto_tac;
qed "CLIM_zero_cancel";

(*** NSCLIM_not zero and hence CLIM_not_zero ***)

(*not in simpset?*)
Addsimps [hypreal_epsilon_not_zero];

Goalw [NSCLIM_def] "k ~= 0 ==> ~ ((%x. k) -- x --NSC> 0)";
by (auto_tac (claset(),simpset() delsimps [hcomplex_of_complex_zero]));
by (res_inst_tac [("x","hcomplex_of_complex x + hcomplex_of_hypreal epsilon")] exI 1);
by (auto_tac (claset() addIs [CInfinitesimal_add_capprox_self RS capprox_sym],simpset()
    delsimps [hcomplex_of_complex_zero]));
qed "NSCLIM_not_zero";

(* [| k ~= 0; (%x. k) -- x --NSC> 0 |] ==> R *)
bind_thm("NSCLIM_not_zeroE", NSCLIM_not_zero RS notE);

Goal "k ~= 0 ==> ~ ((%x. k) -- x --C> 0)";
by (asm_full_simp_tac (simpset() addsimps [CLIM_NSCLIM_iff, NSCLIM_not_zero]) 1);
qed "CLIM_not_zero";

(*** NSCLIM_const hence CLIM_const ***)

Goal "(%x. k) -- x --NSC> L ==> k = L";
by (rtac ccontr 1);
by (dtac NSCLIM_zero 1);
by (rtac NSCLIM_not_zeroE 1 THEN assume_tac 2);
by Auto_tac;
qed "NSCLIM_const_eq";

Goal "(%x. k) -- x --C> L ==> k = L";
by (asm_full_simp_tac (simpset() addsimps [CLIM_NSCLIM_iff,NSCLIM_const_eq]) 1);
qed "CLIM_const_eq";

(*** NSCLIM and hence CLIM are unique ***)

Goal "[| f -- x --NSC> L; f -- x --NSC> M |] ==> L = M";
by (dtac NSCLIM_minus 1);
by (dtac NSCLIM_add 1 THEN assume_tac 1);
by (auto_tac (claset() addSDs [NSCLIM_const_eq RS sym], simpset()));
qed "NSCLIM_unique";

Goal "[| f -- x --C> L; f -- x --C> M |] ==> L = M";
by (asm_full_simp_tac (simpset() addsimps [CLIM_NSCLIM_iff, NSCLIM_unique]) 1);
qed "CLIM_unique";

(***  NSCLIM_mult_zero and CLIM_mult_zero ***)

Goal "[| f -- x --NSC> 0; g -- x --NSC> 0 |] \
\         ==> (%x. f(x)*g(x)) -- x --NSC> 0";
by (dtac NSCLIM_mult 1 THEN Auto_tac);
qed "NSCLIM_mult_zero";

Goal "[| f -- x --C> 0; g -- x --C> 0 |] \
\     ==> (%x. f(x)*g(x)) -- x --C> 0";
by (dtac CLIM_mult 1 THEN Auto_tac);
qed "CLIM_mult_zero";

(*** NSCLIM_self hence CLIM_self ***)

Goalw [NSCLIM_def] "(%x. x) -- a --NSC> a";
by (auto_tac (claset() addIs [starfunC_Idfun_capprox],simpset()));
qed "NSCLIM_self";

Goal "(%x. x) -- a --C> a";
by (simp_tac (simpset() addsimps [CLIM_NSCLIM_iff,NSCLIM_self]) 1);
qed "CLIM_self";

(** another equivalence result **)
Goalw [NSCLIM_def,NSCRLIM_def] 
   "(f -- x --NSC> L) = ((%y. cmod(f y - L)) -- x --NSCR> 0)";
by (auto_tac (claset(),simpset() addsimps [CInfinitesimal_capprox_minus 
    RS sym,CInfinitesimal_hcmod_iff]));
by (ALLGOALS(dtac spec) THEN Auto_tac);
by (ALLGOALS(res_inst_tac [("z","xa")] eq_Abs_hcomplex));
by (auto_tac (claset(),simpset() addsimps [hcomplex_diff,
    starfunC,starfunCR,hcomplex_of_complex_def,hcmod,mem_infmal_iff]));
qed "NSCLIM_NSCRLIM_iff";

(** much, much easier standard proof **)
Goalw [CLIM_def,CRLIM_def] 
   "(f -- x --C> L) = ((%y. cmod(f y - L)) -- x --CR> 0)";
by Auto_tac;
qed "CLIM_CRLIM_iff";

(* so this is nicer nonstandard proof *)
Goal "(f -- x --NSC> L) = ((%y. cmod(f y - L)) -- x --NSCR> 0)";
by (auto_tac (claset(),simpset() addsimps [CRLIM_NSCRLIM_iff RS sym,
    CLIM_CRLIM_iff,CLIM_NSCLIM_iff RS sym]));
qed "NSCLIM_NSCRLIM_iff2";

Goal "(f -- a --NSC> L) = ((%x. Re(f x)) -- a --NSCR> Re(L) & \
\                           (%x. Im(f x)) -- a --NSCR> Im(L))";
by (auto_tac (claset() addIs [NSCLIM_NSCRLIM_Re,NSCLIM_NSCRLIM_Im],simpset()));
by (auto_tac (claset(),simpset() addsimps [NSCLIM_def,NSCRLIM_def]));
by (REPEAT(dtac spec 1) THEN Auto_tac);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [capprox_approx_iff,starfunC,
    hcomplex_of_complex_def,starfunCR,hypreal_of_real_def]));
qed "NSCLIM_NSCRLIM_Re_Im_iff";

Goal "(f -- a --C> L) = ((%x. Re(f x)) -- a --CR> Re(L) & \
\                        (%x. Im(f x)) -- a --CR> Im(L))";
by (auto_tac (claset(),simpset() addsimps [CLIM_NSCLIM_iff,CRLIM_NSCRLIM_iff,
    NSCLIM_NSCRLIM_Re_Im_iff]));
qed "CLIM_CRLIM_Re_Im_iff";


(*-----------------------------------------------------------------------*)
(* Continuity                                                                         *)
(*-----------------------------------------------------------------------*)

Goalw [isNSContc_def] 
      "[| isNSContc f a; y @c= hcomplex_of_complex a |] \
\           ==> ( *fc* f) y @c= hcomplex_of_complex (f a)";
by (Blast_tac 1);
qed "isNSContcD";

Goalw [isNSContc_def,NSCLIM_def] 
      "isNSContc f a ==> f -- a --NSC> (f a) ";
by (Blast_tac 1);
qed "isNSContc_NSCLIM";

Goalw [isNSContc_def,NSCLIM_def] 
      "f -- a --NSC> (f a) ==> isNSContc f a";
by Auto_tac;
by (res_inst_tac [("Q","y = hcomplex_of_complex a")] 
    (excluded_middle RS disjE) 1);
by Auto_tac;
qed "NSCLIM_isNSContc";

(*--------------------------------------------------*)
(* NS continuity can be defined using NS Limit in   *)
(* similar fashion to standard def of continuity    *)
(* -------------------------------------------------*)

Goal "(isNSContc f a) = (f -- a --NSC> (f a))";
by (blast_tac (claset() addIs [isNSContc_NSCLIM,NSCLIM_isNSContc]) 1);
qed "isNSContc_NSCLIM_iff";

Goal "(isNSContc f a) = (f -- a --C> (f a))";
by (asm_full_simp_tac (simpset() addsimps 
    [CLIM_NSCLIM_iff,isNSContc_NSCLIM_iff]) 1);
qed "isNSContc_CLIM_iff";

(*** key result for continuity ***)
Goalw [isContc_def] "(isNSContc f a) = (isContc f a)";
by (rtac isNSContc_CLIM_iff 1);
qed "isNSContc_isContc_iff";

Goal "isContc f a ==> isNSContc f a";
by (etac (isNSContc_isContc_iff RS iffD2) 1);
qed "isContc_isNSContc";

Goal "isNSContc f a ==> isContc f a";
by (etac (isNSContc_isContc_iff RS iffD1) 1);
qed "isNSContc_isContc";

(*--------------------------------------------------*)
(* Alternative definition of continuity             *)
(* -------------------------------------------------*)

Goalw [NSCLIM_def] 
     "(f -- a --NSC> L) = ((%h. f(a + h)) -- 0 --NSC> L)";
by Auto_tac;
by (dres_inst_tac [("x","hcomplex_of_complex a + x")] spec 1);
by (dres_inst_tac [("x","- hcomplex_of_complex a + x")] spec 2);
by Safe_tac;
by (Asm_full_simp_tac 1);
by (rtac ((mem_cinfmal_iff RS iffD2) RS 
    (CInfinitesimal_add_capprox_self RS capprox_sym)) 1);
by (rtac (capprox_minus_iff2 RS iffD1) 4);
by (asm_full_simp_tac (simpset() addsimps compare_rls@[hcomplex_add_commute]) 3);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 2);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 4);
by (auto_tac (claset(),
       simpset() addsimps [starfunC, hcomplex_of_complex_def, 
              hcomplex_minus, hcomplex_add]));
qed "NSCLIM_h_iff";

Goal "(f -- a --NSC> f a) = ((%h. f(a + h)) -- 0 --NSC> f a)";
by (rtac NSCLIM_h_iff 1);
qed "NSCLIM_isContc_iff";

Goal "(f -- a --C> f a) = ((%h. f(a + h)) -- 0 --C> f(a))";
by (simp_tac (simpset() addsimps [CLIM_NSCLIM_iff, NSCLIM_isContc_iff]) 1);
qed "CLIM_isContc_iff";

Goalw [isContc_def] "(isContc f x) = ((%h. f(x + h)) -- 0 --C> f(x))";
by (simp_tac (simpset() addsimps [CLIM_isContc_iff]) 1);
qed "isContc_iff";

Goal "[| isContc f a; isContc g a |] ==> isContc (%x. f(x) + g(x)) a";
by (auto_tac (claset() addIs [capprox_add],
              simpset() addsimps [isNSContc_isContc_iff RS sym, isNSContc_def]));
qed "isContc_add";

Goal "[| isContc f a; isContc g a |] ==> isContc (%x. f(x) * g(x)) a";
by (auto_tac (claset() addSIs [starfunC_mult_CFinite_capprox],
              simpset() delsimps [starfunC_mult RS sym]
			addsimps [isNSContc_isContc_iff RS sym, isNSContc_def]));
qed "isContc_mult";

(*** more theorems: note simple proofs ***)

Goal "[| isContc f a; isContc g (f a) |] \
\     ==> isContc (g o f) a";
by (auto_tac (claset(),simpset() addsimps [isNSContc_isContc_iff RS sym,
              isNSContc_def,starfunC_o RS sym]));
qed "isContc_o";

Goal "[| isContc f a; isContc g (f a) |] \
\     ==> isContc (%x. g (f x)) a";
by (auto_tac (claset() addDs [isContc_o],simpset() addsimps [o_def]));
qed "isContc_o2";

Goalw [isNSContc_def] "isNSContc f a ==> isNSContc (%x. - f x) a";
by Auto_tac; 
qed "isNSContc_minus";

Goal "isContc f a ==> isContc (%x. - f x) a";
by (auto_tac (claset(),simpset() addsimps [isNSContc_isContc_iff RS sym,
              isNSContc_minus]));
qed "isContc_minus";

Goalw [isContc_def]  
      "[| isContc f x; f x ~= 0 |] ==> isContc (%x. inverse (f x)) x";
by (blast_tac (claset() addIs [CLIM_inverse]) 1);
qed "isContc_inverse";

Goal "[| isNSContc f x; f x ~= 0 |] ==> isNSContc (%x. inverse (f x)) x";
by (auto_tac (claset() addIs [isContc_inverse],simpset() addsimps 
    [isNSContc_isContc_iff]));
qed "isNSContc_inverse";

Goalw [complex_diff_def] 
      "[| isContc f a; isContc g a |] ==> isContc (%x. f(x) - g(x)) a";
by (auto_tac (claset() addIs [isContc_add,isContc_minus],simpset()));
qed "isContc_diff";

Goalw [isContc_def]  "isContc (%x. k) a";
by (Simp_tac 1);
qed "isContc_const";
Addsimps [isContc_const];

Goalw [isNSContc_def]  "isNSContc (%x. k) a";
by (Simp_tac 1);
qed "isNSContc_const";
Addsimps [isNSContc_const];


(*-----------------------------------------------------------------------*)
(* functions from complex to reals                                                    *)
(* ----------------------------------------------------------------------*)

Goalw [isNSContCR_def] 
      "[| isNSContCR f a; y @c= hcomplex_of_complex a |] \
\           ==> ( *fcR* f) y @= hypreal_of_real (f a)";
by (Blast_tac 1);
qed "isNSContCRD";

Goalw [isNSContCR_def,NSCRLIM_def] 
      "isNSContCR f a ==> f -- a --NSCR> (f a) ";
by (Blast_tac 1);
qed "isNSContCR_NSCRLIM";

Goalw [isNSContCR_def,NSCRLIM_def] 
      "f -- a --NSCR> (f a) ==> isNSContCR f a";
by Auto_tac;
by (res_inst_tac [("Q","y = hcomplex_of_complex a")] 
    (excluded_middle RS disjE) 1);
by Auto_tac;
qed "NSCRLIM_isNSContCR";

Goal "(isNSContCR f a) = (f -- a --NSCR> (f a))";
by (blast_tac (claset() addIs [isNSContCR_NSCRLIM,NSCRLIM_isNSContCR]) 1);
qed "isNSContCR_NSCRLIM_iff";

Goal "(isNSContCR f a) = (f -- a --CR> (f a))";
by (asm_full_simp_tac (simpset() addsimps 
    [CRLIM_NSCRLIM_iff,isNSContCR_NSCRLIM_iff]) 1);
qed "isNSContCR_CRLIM_iff";

(*** another key result for continuity ***)
Goalw [isContCR_def] "(isNSContCR f a) = (isContCR f a)";
by (rtac isNSContCR_CRLIM_iff 1);
qed "isNSContCR_isContCR_iff";

Goal "isContCR f a ==> isNSContCR f a";
by (etac (isNSContCR_isContCR_iff RS iffD2) 1);
qed "isContCR_isNSContCR";

Goal "isNSContCR f a ==> isContCR f a";
by (etac (isNSContCR_isContCR_iff RS iffD1) 1);
qed "isNSContCR_isContCR";

Goalw [isNSContCR_def]  "isNSContCR cmod (a)";
by (auto_tac (claset() addIs [capprox_hcmod_approx],
    simpset() addsimps [starfunCR_cmod,hcmod_hcomplex_of_complex
    RS sym]));
qed "isNSContCR_cmod";    
Addsimps [isNSContCR_cmod];

Goal "isContCR cmod (a)";
by (auto_tac (claset(),simpset() addsimps [isNSContCR_isContCR_iff RS sym]));
qed "isContCR_cmod";    
Addsimps [isContCR_cmod];

Goalw [isContc_def,isContCR_def] 
  "isContc f a ==> isContCR (%x. Re (f x)) a";
by (etac CLIM_CRLIM_Re 1);
qed "isContc_isContCR_Re"; 

Goalw [isContc_def,isContCR_def] 
  "isContc f a ==> isContCR (%x. Im (f x)) a";
by (etac CLIM_CRLIM_Im 1);
qed "isContc_isContCR_Im"; 

(*-----------------------------------------------------------------------*)
(* Derivatives                                                                        *)
(*-----------------------------------------------------------------------*)

Goalw [cderiv_def] 
      "(CDERIV f x :> D) = ((%h. (f(x + h) - f(x))/h) -- 0 --C> D)";
by (Blast_tac 1);        
qed "CDERIV_iff";

Goalw [cderiv_def] 
      "(CDERIV f x :> D) = ((%h. (f(x + h) - f(x))/h) -- 0 --NSC> D)";
by (simp_tac (simpset() addsimps [CLIM_NSCLIM_iff]) 1);
qed "CDERIV_NSC_iff";

Goalw [cderiv_def] 
      "CDERIV f x :> D \
\      ==> (%h. (f(x + h) - f(x))/h) -- 0 --C> D";
by (Blast_tac 1);        
qed "CDERIVD";

Goalw [cderiv_def] 
      "CDERIV f x :> D ==> (%h. (f(x + h) - f(x))/h) -- 0 --NSC> D";
by (asm_full_simp_tac (simpset() addsimps [CLIM_NSCLIM_iff]) 1);
qed "NSC_DERIVD";

(*** Uniqueness ***)

Goalw [cderiv_def] 
      "[| CDERIV f x :> D; CDERIV f x :> E |] ==> D = E";
by (blast_tac (claset() addIs [CLIM_unique]) 1);
qed "CDERIV_unique";

(*** uniqueness: a nonstandard proof ***)
Goalw [nscderiv_def] 
     "[| NSCDERIV f x :> D; NSCDERIV f x :> E |] ==> D = E";
by (auto_tac (claset() addSDs [inst "x" "hcomplex_of_hypreal epsilon" bspec] 
                       addSIs [inj_hcomplex_of_complex RS injD] 
                       addDs [capprox_trans3],
              simpset()));
qed "NSCDeriv_unique";


(*-----------------------------------------------------------------------*)
(* Differentiability                                                                  *)
(*-----------------------------------------------------------------------*)

Goalw [cdifferentiable_def] 
      "f cdifferentiable x ==> EX D. CDERIV f x :> D";
by (assume_tac 1);
qed "cdifferentiableD";

Goalw [cdifferentiable_def] 
      "CDERIV f x :> D ==> f cdifferentiable x";
by (Blast_tac 1);
qed "cdifferentiableI";

Goalw [NSCdifferentiable_def] 
      "f NSCdifferentiable x ==> EX D. NSCDERIV f x :> D";
by (assume_tac 1);
qed "NSCdifferentiableD";

Goalw [NSCdifferentiable_def] 
      "NSCDERIV f x :> D ==> f NSCdifferentiable x";
by (Blast_tac 1);
qed "NSCdifferentiableI";


(*-----------------------------------------------------------------------*)
(* Alternative definition for differentiability                                       *)
(*-----------------------------------------------------------------------*)

Goalw [CLIM_def] 
 "((%h. (f(a + h) - f(a))/h) -- 0 --C> D) = \
\ ((%x. (f(x) - f(a)) / (x - a)) -- a --C> D)";
by (Step_tac 1);
by (ALLGOALS(dtac spec));
by (Step_tac 1);
by (Blast_tac 1 THEN Blast_tac 2);
by (ALLGOALS(res_inst_tac [("x","s")] exI));
by (Step_tac 1);
by (dres_inst_tac [("x","x - a")] spec 1);
by (dres_inst_tac [("x","x + a")] spec 2);
by (auto_tac (claset(), simpset() addsimps complex_add_ac));
qed "CDERIV_CLIM_iff";

Goalw [cderiv_def] "(CDERIV f x :> D) = \
\         ((%z. (f(z) - f(x)) / (z - x)) -- x --C> D)";
by (simp_tac (simpset() addsimps [CDERIV_CLIM_iff]) 1);
qed "CDERIV_iff2";


(*-----------------------------------------------------------------------*)
(* Equivalence of NS and standard defs of differentiation                             *)
(*-----------------------------------------------------------------------*)

(*** first equivalence ***)
Goalw [nscderiv_def,NSCLIM_def] 
      "(NSCDERIV f x :> D) = ((%h. (f(x + h) - f(x))/h) -- 0 --NSC> D)";
by Auto_tac;
by (dres_inst_tac [("x","xa")] bspec 1);
by (rtac ccontr 3);
by (dres_inst_tac [("x","h")] spec 3);
by (auto_tac (claset(),
              simpset() addsimps [mem_cinfmal_iff, starfunC_lambda_cancel]));
qed "NSCDERIV_NSCLIM_iff";

(*** 2nd equivalence ***)
Goal "(NSCDERIV f x :> D) = \
\         ((%z. (f(z) - f(x)) / (z - x)) -- x --NSC> D)";
by (full_simp_tac (simpset() addsimps 
     [NSCDERIV_NSCLIM_iff, CDERIV_CLIM_iff, CLIM_NSCLIM_iff RS sym]) 1);
qed "NSCDERIV_NSCLIM_iff2";

Goal "(NSCDERIV f x :> D) = \
\     (ALL xa. xa ~= hcomplex_of_complex x & xa @c= hcomplex_of_complex x --> \
\       ( *fc* (%z. (f z - f x) / (z - x))) xa @c= hcomplex_of_complex D)";
by (auto_tac (claset(), simpset() addsimps [NSCDERIV_NSCLIM_iff2, NSCLIM_def]));
qed "NSCDERIV_iff2";

Goalw [cderiv_def] "(NSCDERIV f x :> D) = (CDERIV f x :> D)";
by (simp_tac (simpset() addsimps [NSCDERIV_NSCLIM_iff,CLIM_NSCLIM_iff]) 1);
qed "NSCDERIV_CDERIV_iff";

Goalw [nscderiv_def]
      "NSCDERIV f x :> D ==> isNSContc f x";
by (auto_tac (claset(),simpset() addsimps [isNSContc_NSCLIM_iff,
    NSCLIM_def,hcomplex_diff_def]));
by (dtac (capprox_minus_iff RS iffD1) 1);
by (subgoal_tac "xa + - (hcomplex_of_complex x) ~= 0" 1);
 by (asm_full_simp_tac (simpset() addsimps compare_rls) 2);
by (dres_inst_tac [("x","- hcomplex_of_complex x + xa")] bspec 1);
by (asm_full_simp_tac (simpset() addsimps [hcomplex_add_assoc RS sym]) 2);
by (auto_tac (claset(),simpset() addsimps 
    [mem_cinfmal_iff RS sym,hcomplex_add_commute]));
by (dres_inst_tac [("c","xa + - hcomplex_of_complex x")] capprox_mult1 1);
by (auto_tac (claset() addIs [CInfinitesimal_subset_CFinite
    RS subsetD],simpset() addsimps [hcomplex_mult_assoc]));
by (dres_inst_tac [("x3","D")] (CFinite_hcomplex_of_complex RSN
    (2,CInfinitesimal_CFinite_mult) RS (mem_cinfmal_iff RS iffD1)) 1);
by (blast_tac (claset() addIs [capprox_trans,hcomplex_mult_commute RS subst,
    (capprox_minus_iff RS iffD2)]) 1);
qed "NSCDERIV_isNSContc";

Goal "CDERIV f x :> D ==> isContc f x";
by (asm_full_simp_tac (simpset() addsimps [NSCDERIV_CDERIV_iff RS sym, 
    isNSContc_isContc_iff RS sym,NSCDERIV_isNSContc]) 1);
qed "CDERIV_isContc";

(*-----------------------------------------------------------------------*)
(* Differentiation rules for combinations of functions follow from clear,             *)
(* straightforard, algebraic manipulations                                            *)
(*-----------------------------------------------------------------------*)

(* use simple constant nslimit theorem *)
Goal "(NSCDERIV (%x. k) x :> 0)";
by (simp_tac (simpset() addsimps [NSCDERIV_NSCLIM_iff]) 1);
qed "NSCDERIV_const";
Addsimps [NSCDERIV_const];

Goal "(CDERIV (%x. k) x :> 0)";
by (simp_tac (simpset() addsimps [NSCDERIV_CDERIV_iff RS sym]) 1);
qed "CDERIV_const";
Addsimps [CDERIV_const];

Goal "[| NSCDERIV f x :> Da;  NSCDERIV g x :> Db |] \
\     ==> NSCDERIV (%x. f x + g x) x :> Da + Db";
by (asm_full_simp_tac (simpset() addsimps [NSCDERIV_NSCLIM_iff,
           NSCLIM_def]) 1 THEN REPEAT(Step_tac 1));
by (auto_tac (claset(),
       simpset() addsimps [hcomplex_add_divide_distrib,hcomplex_diff_def]));
by (dres_inst_tac [("b","hcomplex_of_complex Da"),
                   ("d","hcomplex_of_complex Db")] capprox_add 1);
by (auto_tac (claset(), simpset() addsimps add_ac));
qed "NSCDERIV_add";

Goal "[| CDERIV f x :> Da; CDERIV g x :> Db |] \
\     ==> CDERIV (%x. f x + g x) x :> Da + Db";
by (asm_full_simp_tac (simpset() addsimps [NSCDERIV_add,
                                     NSCDERIV_CDERIV_iff RS sym]) 1);
qed "CDERIV_add";

(*** lemmas for multiplication ***)

Goal "((a::hcomplex)*b) - (c*d) = (b*(a - c)) + (c*(b - d))";
by (simp_tac (simpset() addsimps [right_diff_distrib]) 1);
val lemma_nscderiv1 = result();

Goal "[| (x + y) / z = hcomplex_of_complex D + yb; z ~= 0; \
\        z : CInfinitesimal; yb : CInfinitesimal |] \
\     ==> x + y @c= 0";
by (forw_inst_tac [("c1","z")] (hcomplex_mult_right_cancel RS iffD2) 1 
    THEN assume_tac 1);
by (thin_tac "(x + y) / z = hcomplex_of_complex D + yb" 1);
by (auto_tac (claset() addSIs [CInfinitesimal_CFinite_mult2, CFinite_add],
              simpset() addsimps [mem_cinfmal_iff RS sym]));
by (etac (CInfinitesimal_subset_CFinite RS subsetD) 1);
val lemma_nscderiv2 = result();

Goal "[| NSCDERIV f x :> Da; NSCDERIV g x :> Db |] \
\     ==> NSCDERIV (%x. f x * g x) x :> (Da * g(x)) + (Db * f(x))";
by (asm_full_simp_tac (simpset() addsimps [NSCDERIV_NSCLIM_iff, NSCLIM_def]) 1 
    THEN REPEAT(Step_tac 1));
by (auto_tac (claset(),
       simpset() addsimps [starfunC_lambda_cancel, lemma_nscderiv1,
       hcomplex_of_complex_zero]));
by (simp_tac (simpset() addsimps [hcomplex_add_divide_distrib]) 1); 
by (REPEAT(dtac (bex_CInfinitesimal_iff2 RS iffD2) 1));
by (auto_tac (claset(),
        simpset() delsimps [times_divide_eq_right]
		  addsimps [times_divide_eq_right RS sym]));
by (rewtac hcomplex_diff_def);
by (dres_inst_tac [("D","Db")] lemma_nscderiv2 1);
by (dtac (capprox_minus_iff RS iffD2 RS (bex_CInfinitesimal_iff2 RS iffD2)) 4);
by (auto_tac (claset() addSIs [capprox_add_mono1],
      simpset() addsimps [hcomplex_add_mult_distrib, right_distrib, 
			  hcomplex_mult_commute, hcomplex_add_assoc]));
by (res_inst_tac [("w1","hcomplex_of_complex Db * hcomplex_of_complex (f x)")]
    (hcomplex_add_commute RS subst) 1);
by (auto_tac (claset() addSIs [CInfinitesimal_add_capprox_self2 RS capprox_sym,
			       CInfinitesimal_add, CInfinitesimal_mult,
			       CInfinitesimal_hcomplex_of_complex_mult,
			       CInfinitesimal_hcomplex_of_complex_mult2],
	      simpset() addsimps [hcomplex_add_assoc RS sym]));
qed "NSCDERIV_mult";

Goal "[| CDERIV f x :> Da; CDERIV g x :> Db |] \
\     ==> CDERIV (%x. f x * g x) x :> (Da * g(x)) + (Db * f(x))";
by (asm_full_simp_tac (simpset() addsimps [NSCDERIV_mult,
                                           NSCDERIV_CDERIV_iff RS sym]) 1);
qed "CDERIV_mult";

Goal "NSCDERIV f x :> D ==> NSCDERIV (%x. c * f x) x :> c*D";
by (asm_full_simp_tac 
    (simpset() addsimps [times_divide_eq_right RS sym, NSCDERIV_NSCLIM_iff,
                         minus_mult_right, complex_add_mult_distrib2 RS sym,
                         complex_diff_def] 
             delsimps [times_divide_eq_right, minus_mult_right RS sym]) 1);
by (etac (NSCLIM_const RS NSCLIM_mult) 1);
qed "NSCDERIV_cmult";

Goal "CDERIV f x :> D ==> CDERIV (%x. c * f x) x :> c*D";
by (auto_tac (claset(),simpset() addsimps [NSCDERIV_cmult,NSCDERIV_CDERIV_iff
    RS sym]));
qed "CDERIV_cmult";

Goal "NSCDERIV f x :> D ==> NSCDERIV (%x. -(f x)) x :> -D";
by (asm_full_simp_tac (simpset() addsimps [NSCDERIV_NSCLIM_iff,complex_diff_def]) 1);
by (res_inst_tac [("t","f x")] (complex_minus_minus RS subst) 1);
by (asm_simp_tac (simpset() addsimps [complex_minus_add_distrib RS sym] 
                   delsimps [complex_minus_add_distrib, complex_minus_minus]
                   delsimps [minus_add_distrib, minus_minus]

) 1);
by (etac NSCLIM_minus 1);
qed "NSCDERIV_minus";

Goal "CDERIV f x :> D ==> CDERIV (%x. -(f x)) x :> -D";
by (asm_full_simp_tac (simpset() addsimps [NSCDERIV_minus,NSCDERIV_CDERIV_iff RS sym]) 1);
qed "CDERIV_minus";

Goal "[| NSCDERIV f x :> Da; NSCDERIV g x :> Db |] \
\     ==> NSCDERIV (%x. f x + -g x) x :> Da + -Db";
by (blast_tac (claset() addDs [NSCDERIV_add,NSCDERIV_minus]) 1);
qed "NSCDERIV_add_minus";

Goal "[| CDERIV f x :> Da; CDERIV g x :> Db |] \
\     ==> CDERIV (%x. f x + -g x) x :> Da + -Db";
by (blast_tac (claset() addDs [CDERIV_add,CDERIV_minus]) 1);
qed "CDERIV_add_minus";

Goalw [complex_diff_def]
     "[| NSCDERIV f x :> Da; NSCDERIV g x :> Db |] \
\     ==> NSCDERIV (%x. f x - g x) x :> Da - Db";
by (blast_tac (claset() addIs [NSCDERIV_add_minus]) 1);
qed "NSCDERIV_diff";

Goalw [complex_diff_def]
     "[| CDERIV f x :> Da; CDERIV g x :> Db |] \
\      ==> CDERIV (%x. f x - g x) x :> Da - Db";
by (blast_tac (claset() addIs [CDERIV_add_minus]) 1);
qed "CDERIV_diff";


(*--------------------------------------------------*)
(* Chain rule                                       *)
(*--------------------------------------------------*)

(* lemmas *)
Goalw [nscderiv_def] 
      "[| NSCDERIV g x :> D; \
\         ( *fc* g) (hcomplex_of_complex(x) + xa) = hcomplex_of_complex(g x);\
\         xa : CInfinitesimal; xa ~= 0 \
\      |] ==> D = 0";
by (dtac bspec 1);
by Auto_tac;
qed "NSCDERIV_zero";

Goalw [nscderiv_def] 
     "[| NSCDERIV f x :> D;  h: CInfinitesimal;  h ~= 0 |]  \
\     ==> ( *fc* f) (hcomplex_of_complex(x) + h) - hcomplex_of_complex(f x) @c= 0";    
by (asm_full_simp_tac (simpset() addsimps [mem_cinfmal_iff RS sym]) 1);
by (rtac CInfinitesimal_ratio 1);
by (rtac capprox_hcomplex_of_complex_CFinite 3);
by Auto_tac;
qed "NSCDERIV_capprox";


(*--------------------------------------------------*)
(* from one version of differentiability            *)
(*                                                  *)                                   
(*   f(x) - f(a)                                    *)
(* --------------- @= Db                            *)
(*     x - a                                        *)
(* -------------------------------------------------*)

Goal "[| NSCDERIV f (g x) :> Da; \
\        ( *fc* g) (hcomplex_of_complex(x) + xa) ~= hcomplex_of_complex (g x); \
\        ( *fc* g) (hcomplex_of_complex(x) + xa) @c= hcomplex_of_complex (g x) \
\     |] ==> (( *fc* f) (( *fc* g) (hcomplex_of_complex(x) + xa)) \
\                     - hcomplex_of_complex (f (g x))) \
\             / (( *fc* g) (hcomplex_of_complex(x) + xa) - hcomplex_of_complex (g x)) \
\            @c= hcomplex_of_complex (Da)";
by (auto_tac (claset(),simpset() addsimps [NSCDERIV_NSCLIM_iff2, NSCLIM_def]));
qed "NSCDERIVD1";

(*--------------------------------------------------*)
(* from other version of differentiability          *)
(*                                                  *)
(*  f(x + h) - f(x)                                 *)
(* ----------------- @= Db                          *)
(*         h                                        *)
(*--------------------------------------------------*)

Goal "[| NSCDERIV g x :> Db; xa: CInfinitesimal; xa ~= 0 |] \
\     ==> (( *fc* g) (hcomplex_of_complex(x) + xa) - hcomplex_of_complex(g x)) / xa \
\         @c= hcomplex_of_complex (Db)";
by (auto_tac (claset(),
    simpset() addsimps [NSCDERIV_NSCLIM_iff, NSCLIM_def, 
		mem_cinfmal_iff, starfunC_lambda_cancel]));
qed "NSCDERIVD2";

Goal "(z::hcomplex) ~= 0 ==> x*y = (x*inverse(z))*(z*y)";
by Auto_tac;  
qed "lemma_complex_chain";

(*** chain rule ***)

Goal "[| NSCDERIV f (g x) :> Da; NSCDERIV g x :> Db |] \
\     ==> NSCDERIV (f o g) x :> Da * Db";
by (asm_simp_tac (simpset() addsimps [NSCDERIV_NSCLIM_iff,
    NSCLIM_def,mem_cinfmal_iff RS sym]) 1 THEN Step_tac 1);
by (forw_inst_tac [("f","g")] NSCDERIV_capprox 1);
by (auto_tac (claset(),
              simpset() addsimps [starfunC_lambda_cancel2, starfunC_o RS sym]));
by (case_tac "( *fc* g) (hcomplex_of_complex(x) + xa) = hcomplex_of_complex (g x)" 1);
by (dres_inst_tac [("g","g")] NSCDERIV_zero 1);
by (auto_tac (claset(),simpset() addsimps [hcomplex_divide_def]));
by (res_inst_tac [("z1","( *fc* g) (hcomplex_of_complex(x) + xa) - hcomplex_of_complex (g x)"),
    ("y1","inverse xa")] (lemma_complex_chain RS ssubst) 1);
by (Asm_simp_tac 1);
by (rtac capprox_mult_hcomplex_of_complex 1);
by (fold_tac [hcomplex_divide_def]);
by (blast_tac (claset() addIs [NSCDERIVD2]) 2);
by (auto_tac (claset() addSIs [NSCDERIVD1] addIs [capprox_minus_iff RS iffD2],
    simpset() addsimps [symmetric hcomplex_diff_def]));
qed "NSCDERIV_chain";

(* standard version *)
Goal "[| CDERIV f (g x) :> Da; CDERIV g x :> Db |] \
\     ==> CDERIV (f o g) x :> Da * Db";
by (asm_full_simp_tac (simpset() addsimps [NSCDERIV_CDERIV_iff RS sym,
    NSCDERIV_chain]) 1);
qed "CDERIV_chain";

Goal "[| CDERIV f (g x) :> Da; CDERIV g x :> Db |] \
\     ==> CDERIV (%x. f (g x)) x :> Da * Db";
by (auto_tac (claset() addDs [CDERIV_chain], simpset() addsimps [o_def]));
qed "CDERIV_chain2";

(*-----------------------------------------------------------------------*)
(* Differentiation of natural number powers                                           *)
(*-----------------------------------------------------------------------*)

Goal "NSCDERIV (%x. x) x :> 1";
by (auto_tac (claset(),
     simpset() addsimps [NSCDERIV_NSCLIM_iff,NSCLIM_def]));
qed "NSCDERIV_Id";
Addsimps [NSCDERIV_Id];

Goal "CDERIV (%x. x) x :> 1";
by (simp_tac (simpset() addsimps [NSCDERIV_CDERIV_iff RS sym]) 1);
qed "CDERIV_Id";
Addsimps [CDERIV_Id];

bind_thm ("isContc_Id", CDERIV_Id RS CDERIV_isContc);

(*derivative of linear multiplication*)
Goal "CDERIV (op * c) x :> c";
by (cut_inst_tac [("c","c"),("x","x")] (CDERIV_Id RS CDERIV_cmult) 1);
by (Asm_full_simp_tac 1);
qed "CDERIV_cmult_Id";
Addsimps [CDERIV_cmult_Id];

Goal "NSCDERIV (op * c) x :> c";
by (simp_tac (simpset() addsimps [NSCDERIV_CDERIV_iff]) 1);
qed "NSCDERIV_cmult_Id";
Addsimps [NSCDERIV_cmult_Id];

Goal "CDERIV (%x. x ^ n) x :> (complex_of_real (real n)) * (x ^ (n - 1))";
by (induct_tac "n" 1);
by (dtac (CDERIV_Id RS CDERIV_mult) 2);
by (auto_tac (claset(), 
              simpset() addsimps [complex_of_real_add RS sym,
                        complex_add_mult_distrib,real_of_nat_Suc] 
                 delsimps [complex_of_real_add]));
by (case_tac "n" 1);
by (auto_tac (claset(), 
              simpset() addsimps [complex_mult_assoc, complex_add_commute]));
by (auto_tac (claset(),simpset() addsimps [complex_mult_commute]));
qed "CDERIV_pow";
Addsimps [CDERIV_pow,simplify (simpset()) CDERIV_pow];

(* NS version *)
Goal "NSCDERIV (%x. x ^ n) x :> complex_of_real (real n) * (x ^ (n - 1))";
by (simp_tac (simpset() addsimps [NSCDERIV_CDERIV_iff]) 1);
qed "NSCDERIV_pow";

Goal "[|CDERIV f x :> D; D = E|] ==> CDERIV f x :> E";
by Auto_tac;
qed "lemma_CDERIV_subst";

(*used once, in NSCDERIV_inverse*)
Goal "[| h: CInfinitesimal; x ~= 0 |] ==> hcomplex_of_complex x + h ~= 0";
by (Clarify_tac 1);
by (dtac (thm"equals_zero_I") 1);
by Auto_tac;  
qed "CInfinitesimal_add_not_zero";

(*Can't get rid of x ~= 0 because it isn't continuous at zero*)

Goalw [nscderiv_def]
     "x ~= 0 ==> NSCDERIV (%x. inverse(x)) x :> (- (inverse x ^ 2))";
by (rtac ballI 1 THEN Asm_full_simp_tac 1 THEN Step_tac 1);
by (forward_tac [CInfinitesimal_add_not_zero] 1);
by (asm_full_simp_tac (simpset() addsimps [hcomplex_add_commute,numeral_2_eq_2]) 2); 
by (auto_tac (claset(),
     simpset() addsimps [starfunC_inverse_inverse,hcomplex_diff_def] 
               delsimps [minus_mult_left RS sym, minus_mult_right RS sym]));
by (asm_simp_tac
     (simpset() addsimps [inverse_add,
          inverse_mult_distrib RS sym, inverse_minus_eq RS sym] 
          @ add_ac @ mult_ac 
       delsimps [inverse_minus_eq,
		 inverse_mult_distrib, minus_mult_right RS sym, minus_mult_left RS sym] ) 1);
by (asm_simp_tac (HOL_ss addsimps [mult_assoc RS sym, right_distrib]) 1);
by (res_inst_tac [("y"," inverse(- hcomplex_of_complex x * hcomplex_of_complex x)")] 
                 capprox_trans 1);
by (rtac inverse_add_CInfinitesimal_capprox2 1);
by (auto_tac (claset() addSDs [hcomplex_of_complex_CFinite_diff_CInfinitesimal] addIs [CFinite_mult], 
         simpset() addsimps [inverse_minus_eq RS sym]));
by (rtac CInfinitesimal_CFinite_mult2 1); 
by Auto_tac;  
qed "NSCDERIV_inverse";

Goal "x ~= 0 ==> CDERIV (%x. inverse(x)) x :> (-(inverse x ^ 2))";
by (asm_simp_tac (simpset() addsimps [NSCDERIV_inverse,
         NSCDERIV_CDERIV_iff RS sym] delsimps [complexpow_Suc]) 1);
qed "CDERIV_inverse";


(*-----------------------------------------------------------------------*)
(* Derivative of inverse                                                              *)
(*-----------------------------------------------------------------------*)

Goal "[| CDERIV f x :> d; f(x) ~= 0 |] \
\     ==> CDERIV (%x. inverse(f x)) x :> (- (d * inverse(f(x) ^ 2)))";
by (rtac (complex_mult_commute RS subst) 1);
by (asm_simp_tac (simpset() addsimps [complex_minus_mult_eq1,
    power_inverse] delsimps [complexpow_Suc, minus_mult_left RS sym,
complex_minus_mult_eq1 RS sym]) 1);
by (fold_goals_tac [o_def]);
by (blast_tac (claset() addSIs [CDERIV_chain,CDERIV_inverse]) 1);
qed "CDERIV_inverse_fun";

Goal "[| NSCDERIV f x :> d; f(x) ~= 0 |] \
\     ==> NSCDERIV (%x. inverse(f x)) x :> (- (d * inverse(f(x) ^ 2)))";
by (asm_full_simp_tac (simpset() addsimps [NSCDERIV_CDERIV_iff,
            CDERIV_inverse_fun] delsimps [complexpow_Suc]) 1);
qed "NSCDERIV_inverse_fun";

(*-----------------------------------------------------------------------*)
(* Derivative of quotient                                                             *)
(*-----------------------------------------------------------------------*)


Goal "x ~= (0::complex) \\<Longrightarrow> (x * inverse(x) ^ 2) = inverse x";
by (auto_tac (claset(),simpset() addsimps [numeral_2_eq_2]));
qed "lemma_complex_mult_inverse_squared";
Addsimps [lemma_complex_mult_inverse_squared];

Goalw [complex_diff_def] 
     "[| CDERIV f x :> d; CDERIV g x :> e; g(x) ~= 0 |] \
\      ==> CDERIV (%y. f(y) / (g y)) x :> (d*g(x) - (e*f(x))) / (g(x) ^ 2)";
by (dres_inst_tac [("f","g")] CDERIV_inverse_fun 1);
by (dtac CDERIV_mult 2);
by (REPEAT(assume_tac 1));
by (asm_full_simp_tac
    (simpset() addsimps [complex_divide_def, complex_add_mult_distrib2,
                         power_inverse,complex_minus_mult_eq1] @ complex_mult_ac 
       delsimps [complexpow_Suc, minus_mult_right RS sym, minus_mult_left RS sym]) 1);
qed "CDERIV_quotient";

Goal "[| NSCDERIV f x :> d; NSCDERIV g x :> e; g(x) ~= 0 |] \
\      ==> NSCDERIV (%y. f(y) / (g y)) x :> (d*g(x) - (e*f(x))) / (g(x) ^ 2)";
by (asm_full_simp_tac (simpset() addsimps [NSCDERIV_CDERIV_iff,
            CDERIV_quotient] delsimps [complexpow_Suc]) 1);
qed "NSCDERIV_quotient";
 

(*-----------------------------------------------------------------------*)
(* Caratheodory formulation of derivative at a point: standard proof                  *)
(*-----------------------------------------------------------------------*)


Goalw [CLIM_def] 
      "[| ALL x. x ~= a --> (f x = g x) |] \
\           ==> (f -- a --C> l) = (g -- a --C> l)";
by (auto_tac (claset(), simpset() addsimps [complex_add_minus_iff]));
qed "CLIM_equal";

Goal "[| (%x. f(x) + -g(x)) -- a --C> 0; \
\        g -- a --C> l |] \
\      ==> f -- a --C> l";
by (dtac CLIM_add 1 THEN assume_tac 1);
by (auto_tac (claset(), simpset() addsimps [complex_add_assoc]));
qed "CLIM_trans";

Goal "(CDERIV f x :> l) = \
\     (EX g. (ALL z. f z - f x = g z * (z - x)) & isContc g x & g x = l)";
by (Step_tac 1);
by (res_inst_tac 
    [("x","%z. if  z = x then l else (f(z) - f(x)) / (z - x)")] exI 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult_assoc,
    CLAIM "z ~= x ==> z - x ~= (0::complex)"]));
by (auto_tac (claset(),simpset() addsimps [isContc_iff,CDERIV_iff]));
by (ALLGOALS(rtac (CLIM_equal RS iffD1)));
by Auto_tac;
qed "CARAT_CDERIV";

Goal "NSCDERIV f x :> l ==> \
\     EX g. (ALL z. f z - f x = g z * (z - x)) & isNSContc g x & g x = l";
by (auto_tac (claset(),simpset() addsimps [NSCDERIV_CDERIV_iff,
    isNSContc_isContc_iff,CARAT_CDERIV]));
qed "CARAT_NSCDERIV";

(* How about a NS proof? *)
Goal "(ALL z. f z - f x = g z * (z - x)) & isNSContc g x & g x = l \
\     ==> NSCDERIV f x :> l";
by (auto_tac (claset(), 
              simpset() delsimprocs complex_cancel_factor
                        addsimps [NSCDERIV_iff2]));
by (asm_full_simp_tac (simpset() addsimps [isNSContc_def]) 1);
qed "CARAT_CDERIVD";
 
