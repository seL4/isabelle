(*  Title       : NSA.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Infinite numbers, Infinitesimals,
                  infinitely close relation  etc.
*) 

fun CLAIM_SIMP str thms =
               prove_goal (the_context()) str
               (fn prems => [cut_facts_tac prems 1,
                   auto_tac (claset(),simpset() addsimps thms)]);
fun CLAIM str = CLAIM_SIMP str [];

(*--------------------------------------------------------------------
     Closure laws for members of (embedded) set standard real SReal
 --------------------------------------------------------------------*)

Goalw [SReal_def] "[| (x::hypreal): SReal; y: SReal |] ==> x + y: SReal";
by (Step_tac 1);
by (res_inst_tac [("x","r + ra")] exI 1);
by (Simp_tac 1);
qed "SReal_add";

Goalw [SReal_def] "[| (x::hypreal): SReal; y: SReal |] ==> x * y: SReal";
by (Step_tac 1);
by (res_inst_tac [("x","r * ra")] exI 1);
by (simp_tac (simpset() addsimps [hypreal_of_real_mult]) 1);
qed "SReal_mult";

Goalw [SReal_def] "(x::hypreal): SReal ==> inverse x : SReal";
by (blast_tac (claset() addIs [hypreal_of_real_inverse RS sym]) 1); 
qed "SReal_inverse";

Goal "[| (x::hypreal): SReal;  y: SReal |] ==> x/y: SReal";
by (asm_simp_tac (simpset() addsimps [SReal_mult,SReal_inverse,
                                      hypreal_divide_def]) 1); 
qed "SReal_divide";

Goalw [SReal_def] "(x::hypreal): SReal ==> -x : SReal";
by (blast_tac (claset() addIs [hypreal_of_real_minus RS sym]) 1); 
qed "SReal_minus";

Goal "(-x : SReal) = ((x::hypreal): SReal)";
by Auto_tac;  
by (etac SReal_minus 2); 
by (dtac SReal_minus 1); 
by Auto_tac;  
qed "SReal_minus_iff";
Addsimps [SReal_minus_iff]; 

Goal "[| (x::hypreal) + y : SReal; y: SReal |] ==> x: SReal";
by (dres_inst_tac [("x","y")] SReal_minus 1);
by (dtac SReal_add 1);
by (assume_tac 1); 
by Auto_tac;  
qed "SReal_add_cancel";

Goalw [SReal_def] "(x::hypreal): SReal ==> abs x : SReal";
by (auto_tac (claset(), simpset() addsimps [hypreal_of_real_hrabs]));
qed "SReal_hrabs";

Goalw [SReal_def] "hypreal_of_real x: SReal";
by (Blast_tac 1);
qed "SReal_hypreal_of_real";
Addsimps [SReal_hypreal_of_real];

Goalw [hypreal_number_of_def] "(number_of w ::hypreal) : SReal";
by (rtac SReal_hypreal_of_real 1);
qed "SReal_number_of";
Addsimps [SReal_number_of];

Goalw [hypreal_divide_def] "r : SReal ==> r/(number_of w::hypreal) : SReal";
by (blast_tac (claset() addSIs [SReal_number_of, SReal_mult, 
                                SReal_inverse]) 1);
qed "SReal_divide_number_of";

(* Infinitesimal ehr not in SReal *)

Goalw [SReal_def] "ehr ~: SReal";
by (auto_tac (claset(),
              simpset() addsimps [hypreal_of_real_not_eq_epsilon RS not_sym]));
qed "SReal_epsilon_not_mem";

Goalw [SReal_def] "whr ~: SReal";
by (auto_tac (claset(),
              simpset() addsimps [hypreal_of_real_not_eq_omega RS not_sym]));
qed "SReal_omega_not_mem";

Goalw [SReal_def] "{x. hypreal_of_real x : SReal} = (UNIV::real set)";
by Auto_tac;
qed "SReal_UNIV_real";

Goalw [SReal_def] "(x: SReal) = (EX y. x = hypreal_of_real y)";
by Auto_tac;
qed "SReal_iff";

Goalw [SReal_def] "hypreal_of_real ``(UNIV::real set) = SReal";
by Auto_tac;
qed "hypreal_of_real_image";

Goalw [SReal_def] "inv hypreal_of_real ``SReal = (UNIV::real set)";
by Auto_tac;
by (rtac (inj_hypreal_of_real RS inv_f_f RS subst) 1);
by (Blast_tac 1);
qed "inv_hypreal_of_real_image";

Goalw [SReal_def] 
      "[| EX x. x: P; P <= SReal |] ==> EX Q. P = hypreal_of_real `` Q";
by (Best_tac 1); 
qed "SReal_hypreal_of_real_image";

Goal "[| (x::hypreal): SReal; y: SReal;  x<y |] ==> EX r: SReal. x<r & r<y";
by (auto_tac (claset(), simpset() addsimps [SReal_iff]));
by (dtac real_dense 1 THEN Step_tac 1);
by (res_inst_tac [("x","hypreal_of_real r")] bexI 1);
by Auto_tac;
qed "SReal_dense";

(*------------------------------------------------------------------
                   Completeness of SReal
 ------------------------------------------------------------------*)
Goal "P <= SReal ==> ((EX x:P. y < x) = \ 
\     (EX X. hypreal_of_real X : P & y < hypreal_of_real X))";
by (blast_tac (claset() addSDs [SReal_iff RS iffD1]) 1);
by (flexflex_tac );
qed "SReal_sup_lemma";

Goal "[| P <= SReal; EX x. x: P; EX y : SReal. ALL x: P. x < y |] \
\     ==> (EX X. X: {w. hypreal_of_real w : P}) & \
\         (EX Y. ALL X: {w. hypreal_of_real w : P}. X < Y)";
by (rtac conjI 1);
by (fast_tac (claset() addSDs [SReal_iff RS iffD1]) 1);
by (Auto_tac THEN forward_tac [subsetD] 1 THEN assume_tac 1);
by (dtac (SReal_iff RS iffD1) 1);
by (Auto_tac THEN res_inst_tac [("x","ya")] exI 1);
by Auto_tac;
qed "SReal_sup_lemma2";

(*------------------------------------------------------
    lifting of ub and property of lub
 -------------------------------------------------------*)
Goalw [isUb_def,setle_def] 
      "(isUb (SReal) (hypreal_of_real `` Q) (hypreal_of_real Y)) = \
\      (isUb (UNIV :: real set) Q Y)";
by Auto_tac;
qed "hypreal_of_real_isUb_iff";

Goalw [isLub_def,leastP_def] 
     "isLub SReal (hypreal_of_real `` Q) (hypreal_of_real Y) \
\     ==> isLub (UNIV :: real set) Q Y";
by (auto_tac (claset() addIs [hypreal_of_real_isUb_iff RS iffD2],
              simpset() addsimps [hypreal_of_real_isUb_iff, setge_def]));
qed "hypreal_of_real_isLub1";

Goalw [isLub_def,leastP_def] 
      "isLub (UNIV :: real set) Q Y \
\      ==> isLub SReal (hypreal_of_real `` Q) (hypreal_of_real Y)";
by (auto_tac (claset(),
              simpset() addsimps [hypreal_of_real_isUb_iff, setge_def]));
by (forw_inst_tac [("x2","x")] (isUbD2a RS (SReal_iff RS iffD1) RS exE) 1);
by (assume_tac 2);
by (dres_inst_tac [("x","xa")] spec 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_of_real_isUb_iff]));
qed "hypreal_of_real_isLub2";

Goal "(isLub SReal (hypreal_of_real `` Q) (hypreal_of_real Y)) = \
\     (isLub (UNIV :: real set) Q Y)";
by (blast_tac (claset() addIs [hypreal_of_real_isLub1,
                               hypreal_of_real_isLub2]) 1);
qed "hypreal_of_real_isLub_iff";

(* lemmas *)
Goalw [isUb_def] 
     "isUb SReal P Y ==> EX Yo. isUb SReal P (hypreal_of_real Yo)";
by (auto_tac (claset(), simpset() addsimps [SReal_iff]));
qed "lemma_isUb_hypreal_of_real";

Goalw [isLub_def,leastP_def,isUb_def] 
     "isLub SReal P Y ==> EX Yo. isLub SReal P (hypreal_of_real Yo)";
by (auto_tac (claset(), simpset() addsimps [SReal_iff]));
qed "lemma_isLub_hypreal_of_real";

Goalw [isLub_def,leastP_def,isUb_def] 
     "EX Yo. isLub SReal P (hypreal_of_real Yo) ==> EX Y. isLub SReal P Y";
by Auto_tac;
qed "lemma_isLub_hypreal_of_real2";

Goal "[| P <= SReal;  EX x. x: P;  EX Y. isUb SReal P Y |] \
\     ==> EX t::hypreal. isLub SReal P t";
by (forward_tac [SReal_hypreal_of_real_image] 1);
by (Auto_tac THEN dtac lemma_isUb_hypreal_of_real 1);
by (auto_tac (claset() addSIs [reals_complete, lemma_isLub_hypreal_of_real2], 
     simpset() addsimps [hypreal_of_real_isLub_iff,hypreal_of_real_isUb_iff]));
qed "SReal_complete";

(*--------------------------------------------------------------------
        Set of finite elements is a subring of the extended reals
 --------------------------------------------------------------------*)
Goalw [HFinite_def] "[|x : HFinite; y : HFinite|] ==> (x+y) : HFinite";
by (blast_tac (claset() addSIs [SReal_add,hrabs_add_less]) 1);
qed "HFinite_add";

Goalw [HFinite_def] "[|x : HFinite; y : HFinite|] ==> x*y : HFinite";
by (Asm_full_simp_tac 1); 
by (blast_tac (claset() addSIs [SReal_mult,hrabs_mult_less]) 1);
qed "HFinite_mult";

Goalw [HFinite_def] "(-x : HFinite) = (x : HFinite)";
by (Simp_tac 1);
qed "HFinite_minus_iff";

Goalw [SReal_def,HFinite_def] "SReal <= HFinite";
by Auto_tac;
by (res_inst_tac [("x","#1 + abs(hypreal_of_real r)")] exI 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_of_real_hrabs]));
by (res_inst_tac [("x","#1 + abs r")] exI 1);
by (Simp_tac 1);
qed "SReal_subset_HFinite";

Goal "hypreal_of_real x : HFinite";
by (auto_tac (claset() addIs [(SReal_subset_HFinite RS subsetD)],
              simpset()));
qed "HFinite_hypreal_of_real";

Addsimps [HFinite_hypreal_of_real];

Goalw [HFinite_def] "x : HFinite ==> EX t: SReal. abs x < t";
by Auto_tac;
qed "HFiniteD";

Goalw [HFinite_def] "(abs x : HFinite) = (x : HFinite)";
by (auto_tac (claset(), simpset() addsimps [hrabs_idempotent]));
qed "HFinite_hrabs_iff";
AddIffs [HFinite_hrabs_iff];

Goal "number_of w : HFinite";
by (rtac (SReal_number_of RS (SReal_subset_HFinite RS subsetD)) 1);
qed "HFinite_number_of";
Addsimps [HFinite_number_of];

Goal "[|x : HFinite; y <= x; #0 <= y |] ==> y: HFinite";
by (case_tac "x <= #0" 1);
by (dres_inst_tac [("y","x")] order_trans 1);
by (dtac hypreal_le_anti_sym 2);
by (auto_tac (claset() addSDs [not_hypreal_leE], simpset()));
by (auto_tac (claset() addSIs [bexI] addIs [order_le_less_trans],
     simpset() addsimps [hrabs_eqI1,hrabs_eqI2,hrabs_minus_eqI1,HFinite_def]));
qed "HFinite_bounded"; 

(*------------------------------------------------------------------
       Set of infinitesimals is a subring of the hyperreals   
 ------------------------------------------------------------------*)
Goalw [Infinitesimal_def]
      "x : Infinitesimal ==> ALL r: SReal. #0 < r --> abs x < r";
by Auto_tac;
qed "InfinitesimalD";

Goalw [Infinitesimal_def] "#0 : Infinitesimal";
by (simp_tac (simpset() addsimps [hrabs_zero]) 1);
qed "Infinitesimal_zero";
AddIffs [Infinitesimal_zero];

Goal "x/(#2::hypreal) + x/(#2::hypreal) = x";
by Auto_tac;  
qed "hypreal_sum_of_halves";

Goal "#0 < r ==> #0 < r/(#2::hypreal)";
by Auto_tac;  
qed "hypreal_half_gt_zero";

Goalw [Infinitesimal_def] 
     "[| x : Infinitesimal; y : Infinitesimal |] ==> (x+y) : Infinitesimal";
by Auto_tac;
by (rtac (hypreal_sum_of_halves RS subst) 1);
by (dtac hypreal_half_gt_zero 1);
by (blast_tac (claset() addIs [hrabs_add_less, hrabs_add_less, 
                               SReal_divide_number_of]) 1); 
qed "Infinitesimal_add";

Goalw [Infinitesimal_def] "(-x:Infinitesimal) = (x:Infinitesimal)";
by (Full_simp_tac 1);
qed "Infinitesimal_minus_iff";
Addsimps [Infinitesimal_minus_iff];

Goal "[| x : Infinitesimal;  y : Infinitesimal |] ==> x-y : Infinitesimal";
by (asm_simp_tac
    (simpset() addsimps [hypreal_diff_def, Infinitesimal_add]) 1);
qed "Infinitesimal_diff";

Goalw [Infinitesimal_def] 
     "[| x : Infinitesimal; y : Infinitesimal |] ==> (x * y) : Infinitesimal";
by Auto_tac;
by (case_tac "y=#0" 1);
by (cut_inst_tac [("u","abs x"),("v","#1"),("x","abs y"),("y","r")] 
    hypreal_mult_less_mono 2);
by Auto_tac;  
qed "Infinitesimal_mult";

Goal "[| x : Infinitesimal; y : HFinite |] ==> (x * y) : Infinitesimal";
by (auto_tac (claset() addSDs [HFiniteD],
              simpset() addsimps [Infinitesimal_def]));
by (forward_tac [hrabs_less_gt_zero] 1);
by (dres_inst_tac [("x","r/t")] bspec 1); 
by (blast_tac (claset() addIs [SReal_divide]) 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_0_less_divide_iff]) 1); 
by (case_tac "x=0 | y=0" 1);
by (cut_inst_tac [("u","abs x"),("v","r/t"),("x","abs y")] 
    hypreal_mult_less_mono 2);
by (auto_tac (claset(), simpset() addsimps [hypreal_0_less_divide_iff]));  
qed "Infinitesimal_HFinite_mult";

Goal "[| x : Infinitesimal; y : HFinite |] ==> (y * x) : Infinitesimal";
by (auto_tac (claset() addDs [Infinitesimal_HFinite_mult],
              simpset() addsimps [hypreal_mult_commute]));
qed "Infinitesimal_HFinite_mult2";

(*** rather long proof ***)
Goalw [HInfinite_def,Infinitesimal_def] 
     "x: HInfinite ==> inverse x: Infinitesimal";
by Auto_tac;
by (eres_inst_tac [("x","inverse r")] ballE 1);
by (rtac (hrabs_inverse RS ssubst) 1);
by (forw_inst_tac [("x1","r"),("z","abs x")] 
    (hypreal_inverse_gt_0 RS order_less_trans) 1);
by (assume_tac 1);
by (dtac ((hypreal_inverse_inverse RS sym) RS subst) 1);
by (rtac (hypreal_inverse_less_iff RS iffD1) 1);
by (auto_tac (claset(), simpset() addsimps [SReal_inverse]));  
qed "HInfinite_inverse_Infinitesimal";



Goalw [HInfinite_def] "[|x: HInfinite;y: HInfinite|] ==> (x*y): HInfinite";
by Auto_tac;
by (eres_inst_tac [("x","#1")] ballE 1);
by (eres_inst_tac [("x","r")] ballE 1);
by (case_tac "y=0" 1); 
by (cut_inst_tac [("x","#1"),("y","abs x"),
                  ("u","r"),("v","abs y")] hypreal_mult_less_mono 2);
by (auto_tac (claset(), simpset() addsimps hypreal_mult_ac));  
qed "HInfinite_mult";

Goalw [HInfinite_def] 
      "[|x: HInfinite; #0 <= y; #0 <= x|] ==> (x + y): HInfinite";
by (auto_tac (claset() addSIs [hypreal_add_zero_less_le_mono],
              simpset() addsimps [hrabs_eqI1, hypreal_add_commute,
                                  hypreal_le_add_order]));
qed "HInfinite_add_ge_zero";

Goal "[|x: HInfinite; #0 <= y; #0 <= x|] ==> (y + x): HInfinite";
by (auto_tac (claset() addSIs [HInfinite_add_ge_zero],
              simpset() addsimps [hypreal_add_commute]));
qed "HInfinite_add_ge_zero2";

Goal "[|x: HInfinite; #0 < y; #0 < x|] ==> (x + y): HInfinite";
by (blast_tac (claset() addIs [HInfinite_add_ge_zero,
                    order_less_imp_le]) 1);
qed "HInfinite_add_gt_zero";

Goalw [HInfinite_def] "(-x: HInfinite) = (x: HInfinite)";
by Auto_tac;
qed "HInfinite_minus_iff";

Goal "[|x: HInfinite; y <= #0; x <= #0|] ==> (x + y): HInfinite";
by (dtac (HInfinite_minus_iff RS iffD2) 1);
by (rtac (HInfinite_minus_iff RS iffD1) 1);
by (auto_tac (claset() addIs [HInfinite_add_ge_zero],
              simpset() addsimps [hypreal_minus_zero_le_iff]));
qed "HInfinite_add_le_zero";

Goal "[|x: HInfinite; y < #0; x < #0|] ==> (x + y): HInfinite";
by (blast_tac (claset() addIs [HInfinite_add_le_zero,
                               order_less_imp_le]) 1);
qed "HInfinite_add_lt_zero";

Goal "[|a: HFinite; b: HFinite; c: HFinite|] \ 
\     ==> a*a + b*b + c*c : HFinite";
by (auto_tac (claset() addIs [HFinite_mult,HFinite_add], simpset()));
qed "HFinite_sum_squares";

Goal "x ~: Infinitesimal ==> x ~= #0";
by Auto_tac;
qed "not_Infinitesimal_not_zero";

Goal "x: HFinite - Infinitesimal ==> x ~= #0";
by Auto_tac;
qed "not_Infinitesimal_not_zero2";

Goal "(abs x : Infinitesimal) = (x : Infinitesimal)";
by (auto_tac (claset(), simpset() addsimps [hrabs_def]));
qed "Infinitesimal_hrabs_iff";
AddIffs [Infinitesimal_hrabs_iff];

Goal "x : HFinite - Infinitesimal ==> abs x : HFinite - Infinitesimal";
by (Blast_tac 1);
qed "HFinite_diff_Infinitesimal_hrabs";

Goalw [Infinitesimal_def] 
      "[| e : Infinitesimal; abs x < e |] ==> x : Infinitesimal";
by (auto_tac (claset() addSDs [bspec], simpset()));
by (dres_inst_tac [("x","e")] (hrabs_ge_self RS order_le_less_trans) 1);
by (fast_tac (claset() addIs [order_less_trans]) 1);
qed "hrabs_less_Infinitesimal";

Goal "[| e : Infinitesimal; abs x <= e |] ==> x : Infinitesimal";
by (blast_tac (claset() addDs [order_le_imp_less_or_eq] 
                        addIs [hrabs_less_Infinitesimal]) 1);
qed "hrabs_le_Infinitesimal";

Goalw [Infinitesimal_def] 
      "[| e : Infinitesimal; \
\         e' : Infinitesimal; \
\         e' < x ; x < e |] ==> x : Infinitesimal";
by (auto_tac (claset() addSDs [bspec], simpset()));
by (dres_inst_tac [("x","e")] (hrabs_ge_self RS order_le_less_trans) 1);
by (dtac (hrabs_interval_iff RS iffD1) 1);
by (fast_tac(claset() addIs [order_less_trans,hrabs_interval_iff RS iffD2]) 1);
qed "Infinitesimal_interval";

Goal "[| e : Infinitesimal; e' : Infinitesimal; \
\        e' <= x ; x <= e |] ==> x : Infinitesimal";
by (auto_tac (claset() addIs [Infinitesimal_interval],
    simpset() addsimps [hypreal_le_eq_less_or_eq]));
qed "Infinitesimal_interval2";

Goalw [Infinitesimal_def] 
     "[| x ~: Infinitesimal;  y ~: Infinitesimal|] ==> (x*y) ~:Infinitesimal";
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [linorder_not_less]) 1); 
by (eres_inst_tac [("x","r*ra")] ballE 1);
by (fast_tac (claset() addIs [SReal_mult]) 2);
by (auto_tac (claset(), simpset() addsimps [hypreal_0_less_mult_iff]));
by (cut_inst_tac [("x","ra"),("y","abs y"),
                  ("u","r"),("v","abs x")] hypreal_mult_le_mono 1);
by Auto_tac;  
qed "not_Infinitesimal_mult";

Goal "x*y : Infinitesimal ==> x : Infinitesimal | y : Infinitesimal";
by (rtac ccontr 1);
by (dtac (de_Morgan_disj RS iffD1) 1);
by (fast_tac (claset() addDs [not_Infinitesimal_mult]) 1);
qed "Infinitesimal_mult_disj";

Goal "x: HFinite-Infinitesimal ==> x ~= #0";
by (Blast_tac 1);
qed "HFinite_Infinitesimal_not_zero";

Goal "[| x : HFinite - Infinitesimal; \
\                  y : HFinite - Infinitesimal \
\               |] ==> (x*y) : HFinite - Infinitesimal";
by (Clarify_tac 1);
by (blast_tac (claset() addDs [HFinite_mult,not_Infinitesimal_mult]) 1);
qed "HFinite_Infinitesimal_diff_mult";

Goalw [Infinitesimal_def,HFinite_def]  
      "Infinitesimal <= HFinite";
by Auto_tac;  
by (res_inst_tac [("x","#1")] bexI 1); 
by Auto_tac;  
qed "Infinitesimal_subset_HFinite";

Goal "x: Infinitesimal ==> x * hypreal_of_real r : Infinitesimal";
by (etac (HFinite_hypreal_of_real RSN 
          (2,Infinitesimal_HFinite_mult)) 1);
qed "Infinitesimal_hypreal_of_real_mult";

Goal "x: Infinitesimal ==> hypreal_of_real r * x: Infinitesimal";
by (etac (HFinite_hypreal_of_real RSN 
          (2,Infinitesimal_HFinite_mult2)) 1);
qed "Infinitesimal_hypreal_of_real_mult2";

(*----------------------------------------------------------------------
                   Infinitely close relation @=
 ----------------------------------------------------------------------*)

Goalw [Infinitesimal_def,inf_close_def] 
        "x:Infinitesimal = (x @= #0)";
by (Simp_tac 1);
qed "mem_infmal_iff";

Goalw [inf_close_def]" (x @= y) = (x + -y @= #0)";
by (Simp_tac 1);
qed "inf_close_minus_iff";

Goalw [inf_close_def]" (x @= y) = (-y + x @= #0)";
by (simp_tac (simpset() addsimps [hypreal_add_commute]) 1);
qed "inf_close_minus_iff2";

Goalw [inf_close_def,Infinitesimal_def]  "x @= x";
by (Simp_tac 1);
qed "inf_close_refl";
AddIffs [inf_close_refl];

Goalw [inf_close_def]  "x @= y ==> y @= x";
by (rtac (hypreal_minus_distrib1 RS subst) 1);
by (etac (Infinitesimal_minus_iff RS iffD2) 1);
qed "inf_close_sym";

Goalw [inf_close_def]  "[| x @= y; y @= z |] ==> x @= z";
by (dtac Infinitesimal_add 1); 
by (assume_tac 1); 
by Auto_tac;  
qed "inf_close_trans";

Goal "[| r @= x; s @= x |] ==> r @= s";
by (blast_tac (claset() addIs [inf_close_sym, inf_close_trans]) 1); 
qed "inf_close_trans2";

Goal "[| x @= r; x @= s|] ==> r @= s";
by (blast_tac (claset() addIs [inf_close_sym, inf_close_trans]) 1); 
qed "inf_close_trans3";

Goal "(number_of w @= x) = (x @= number_of w)";
by (blast_tac (claset() addIs [inf_close_sym]) 1); 
qed "number_of_inf_close_reorient";
Addsimps [number_of_inf_close_reorient];

Goal "(x-y : Infinitesimal) = (x @= y)";
by (auto_tac (claset(),
              simpset() addsimps [hypreal_diff_def, inf_close_minus_iff RS sym,
                                  mem_infmal_iff]));
qed "Infinitesimal_inf_close_minus";

Goalw [monad_def] "(x @= y) = (monad(x)=monad(y))";
by (auto_tac (claset() addDs [inf_close_sym] 
                       addSEs [inf_close_trans,equalityCE],
              simpset()));
qed "inf_close_monad_iff";

Goal "[| x: Infinitesimal; y: Infinitesimal |] ==> x @= y";
by (asm_full_simp_tac (simpset() addsimps [mem_infmal_iff]) 1);
by (blast_tac (claset() addIs [inf_close_trans, inf_close_sym]) 1); 
qed "Infinitesimal_inf_close";

val prem1::prem2::rest = 
goalw thy [inf_close_def] "[| a @= b; c @= d |] ==> a+c @= b+d";
by (rtac (hypreal_minus_add_distrib RS ssubst) 1);
by (rtac (hypreal_add_assoc RS ssubst) 1);
by (res_inst_tac [("y1","c")] (hypreal_add_left_commute RS subst) 1);
by (rtac (hypreal_add_assoc RS subst) 1);
by (rtac ([prem1,prem2] MRS Infinitesimal_add) 1);
qed "inf_close_add";

Goal "a @= b ==> -a @= -b";
by (rtac ((inf_close_minus_iff RS iffD2) RS inf_close_sym) 1);
by (dtac (inf_close_minus_iff RS iffD1) 1);
by (simp_tac (simpset() addsimps [hypreal_add_commute]) 1);
qed "inf_close_minus";

Goal "-a @= -b ==> a @= b";
by (auto_tac (claset() addDs [inf_close_minus], simpset()));
qed "inf_close_minus2";

Goal "(-a @= -b) = (a @= b)";
by (blast_tac (claset() addIs [inf_close_minus,inf_close_minus2]) 1);
qed "inf_close_minus_cancel";

Addsimps [inf_close_minus_cancel];

Goal "[| a @= b; c @= d |] ==> a + -c @= b + -d";
by (blast_tac (claset() addSIs [inf_close_add,inf_close_minus]) 1);
qed "inf_close_add_minus";

Goalw [inf_close_def] "[| a @= b; c: HFinite|] ==> a*c @= b*c"; 
by (asm_full_simp_tac (simpset() addsimps [Infinitesimal_HFinite_mult,
    hypreal_minus_mult_eq1,hypreal_add_mult_distrib RS sym] 
    delsimps [hypreal_minus_mult_eq1 RS sym]) 1);
qed "inf_close_mult1";

Goal "[|a @= b; c: HFinite|] ==> c*a @= c*b"; 
by (asm_simp_tac (simpset() addsimps [inf_close_mult1,hypreal_mult_commute]) 1);
qed "inf_close_mult2";

Goal "[|u @= v*x; x @= y; v: HFinite|] ==> u @= v*y";
by (fast_tac (claset() addIs [inf_close_mult2,inf_close_trans]) 1);
qed "inf_close_mult_subst";

Goal "[| u @= x*v; x @= y; v: HFinite |] ==> u @= y*v";
by (fast_tac (claset() addIs [inf_close_mult1,inf_close_trans]) 1);
qed "inf_close_mult_subst2";

Goal "[| u @= x*hypreal_of_real v; x @= y |] ==> u @= y*hypreal_of_real v";
by (auto_tac (claset() addIs [inf_close_mult_subst2], simpset()));
qed "inf_close_mult_subst_SReal";

Goalw [inf_close_def]  "a = b ==> a @= b";
by (Asm_simp_tac 1);
qed "inf_close_eq_imp";

Goal "x: Infinitesimal ==> -x @= x"; 
by (fast_tac (HOL_cs addIs [Infinitesimal_minus_iff RS iffD2,
    mem_infmal_iff RS iffD1,inf_close_trans2]) 1);
qed "Infinitesimal_minus_inf_close";

Goalw [inf_close_def]  "(EX y: Infinitesimal. x + -z = y) = (x @= z)";
by (Blast_tac 1);
qed "bex_Infinitesimal_iff";

Goal "(EX y: Infinitesimal. x = z + y) = (x @= z)";
by (asm_full_simp_tac (simpset() addsimps [bex_Infinitesimal_iff RS sym]) 1);
by (Force_tac 1);
qed "bex_Infinitesimal_iff2";

Goal "[| y: Infinitesimal; x + y = z |] ==> x @= z";
by (rtac (bex_Infinitesimal_iff RS iffD1) 1);
by (dtac (Infinitesimal_minus_iff RS iffD2) 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_minus_add_distrib,
    hypreal_add_assoc RS sym]));
qed "Infinitesimal_add_inf_close";

Goal "y: Infinitesimal ==> x @= x + y";
by (rtac (bex_Infinitesimal_iff RS iffD1) 1);
by (dtac (Infinitesimal_minus_iff RS iffD2) 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_minus_add_distrib,
    hypreal_add_assoc RS sym]));
qed "Infinitesimal_add_inf_close_self";

Goal "y: Infinitesimal ==> x @= y + x";
by (auto_tac (claset() addDs [Infinitesimal_add_inf_close_self],
    simpset() addsimps [hypreal_add_commute]));
qed "Infinitesimal_add_inf_close_self2";

Goal "y: Infinitesimal ==> x @= x + -y";
by (blast_tac (claset() addSIs [Infinitesimal_add_inf_close_self,
                                Infinitesimal_minus_iff RS iffD2]) 1);
qed "Infinitesimal_add_minus_inf_close_self";

Goal "[| y: Infinitesimal; x+y @= z|] ==> x @= z";
by (dres_inst_tac [("x","x")] (Infinitesimal_add_inf_close_self RS inf_close_sym) 1);
by (etac (inf_close_trans3 RS inf_close_sym) 1);
by (assume_tac 1);
qed "Infinitesimal_add_cancel";

Goal "[| y: Infinitesimal; x @= z + y|] ==> x @= z";
by (dres_inst_tac [("x","z")] (Infinitesimal_add_inf_close_self2  RS inf_close_sym) 1);
by (etac (inf_close_trans3 RS inf_close_sym) 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_add_commute]) 1);
by (etac inf_close_sym 1);
qed "Infinitesimal_add_right_cancel";

Goal "d + b  @= d + c ==> b @= c";
by (dtac (inf_close_minus_iff RS iffD1) 1);
by (asm_full_simp_tac (simpset() addsimps 
    [hypreal_minus_add_distrib,inf_close_minus_iff RS sym] 
    @ hypreal_add_ac) 1);
qed "inf_close_add_left_cancel";

Goal "b + d @= c + d ==> b @= c";
by (rtac inf_close_add_left_cancel 1);
by (asm_full_simp_tac (simpset() addsimps 
    [hypreal_add_commute]) 1);
qed "inf_close_add_right_cancel";

Goal "b @= c ==> d + b @= d + c";
by (rtac (inf_close_minus_iff RS iffD2) 1);
by (asm_full_simp_tac (simpset() addsimps 
    [hypreal_minus_add_distrib,inf_close_minus_iff RS sym] 
    @ hypreal_add_ac) 1);
qed "inf_close_add_mono1";

Goal "b @= c ==> b + a @= c + a";
by (asm_simp_tac (simpset() addsimps 
    [hypreal_add_commute,inf_close_add_mono1]) 1);
qed "inf_close_add_mono2";

Goal "(a + b @= a + c) = (b @= c)";
by (fast_tac (claset() addEs [inf_close_add_left_cancel,
    inf_close_add_mono1]) 1);
qed "inf_close_add_left_iff";

Addsimps [inf_close_add_left_iff];

Goal "(b + a @= c + a) = (b @= c)";
by (simp_tac (simpset() addsimps [hypreal_add_commute]) 1);
qed "inf_close_add_right_iff";

Addsimps [inf_close_add_right_iff];

Goal "[| x: HFinite; x @= y |] ==> y: HFinite";
by (dtac (bex_Infinitesimal_iff2 RS iffD2) 1);
by (Step_tac 1);
by (dtac (Infinitesimal_subset_HFinite RS subsetD 
          RS (HFinite_minus_iff RS iffD2)) 1);
by (dtac HFinite_add 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_add_assoc]));
qed "inf_close_HFinite";

Goal "x @= hypreal_of_real D ==> x: HFinite";
by (rtac (inf_close_sym RSN (2,inf_close_HFinite)) 1);
by Auto_tac;
qed "inf_close_hypreal_of_real_HFinite";

Goal "[|a @= b; c @= d; b: HFinite; d: HFinite|] ==> a*c @= b*d";
by (rtac inf_close_trans 1); 
by (rtac inf_close_mult2 2); 
by (rtac inf_close_mult1 1);
by (blast_tac (claset() addIs [inf_close_HFinite, inf_close_sym]) 2);  
by Auto_tac;  
qed "inf_close_mult_HFinite";

Goal "[|a @= hypreal_of_real b; c @= hypreal_of_real d |] \
\     ==> a*c @= hypreal_of_real b*hypreal_of_real d";
by (blast_tac (claset() addSIs [inf_close_mult_HFinite,
            inf_close_hypreal_of_real_HFinite,HFinite_hypreal_of_real]) 1);
qed "inf_close_mult_hypreal_of_real";

Goal "[| a: SReal; a ~= #0; a*x @= #0 |] ==> x @= #0";
by (dtac (SReal_inverse RS (SReal_subset_HFinite RS subsetD)) 1);
by (auto_tac (claset() addDs [inf_close_mult2],
    simpset() addsimps [hypreal_mult_assoc RS sym]));
qed "inf_close_SReal_mult_cancel_zero";

(* REM comments: newly added *)
Goal "[| a: SReal; x @= #0 |] ==> x*a @= #0";
by (auto_tac (claset() addDs [(SReal_subset_HFinite RS subsetD),
              inf_close_mult1], simpset()));
qed "inf_close_mult_SReal1";

Goal "[| a: SReal; x @= #0 |] ==> a*x @= #0";
by (auto_tac (claset() addDs [(SReal_subset_HFinite RS subsetD),
              inf_close_mult2], simpset()));
qed "inf_close_mult_SReal2";

Goal "[|a : SReal; a ~= #0 |] ==> (a*x @= #0) = (x @= #0)";
by (blast_tac (claset() addIs [inf_close_SReal_mult_cancel_zero,
    inf_close_mult_SReal2]) 1);
qed "inf_close_mult_SReal_zero_cancel_iff";
Addsimps [inf_close_mult_SReal_zero_cancel_iff];

Goal "[| a: SReal; a ~= #0; a* w @= a*z |] ==> w @= z";
by (dtac (SReal_inverse RS (SReal_subset_HFinite RS subsetD)) 1);
by (auto_tac (claset() addDs [inf_close_mult2],
    simpset() addsimps [hypreal_mult_assoc RS sym]));
qed "inf_close_SReal_mult_cancel";

Goal "[| a: SReal; a ~= #0|] ==> (a* w @= a*z) = (w @= z)";
by (auto_tac (claset() addSIs [inf_close_mult2,SReal_subset_HFinite RS subsetD] 
    addIs [inf_close_SReal_mult_cancel], simpset()));
qed "inf_close_SReal_mult_cancel_iff1";
Addsimps [inf_close_SReal_mult_cancel_iff1];

Goal "[| z <= f; f @= g; g <= z |] ==> f @= z";
by (asm_full_simp_tac (simpset() addsimps [bex_Infinitesimal_iff2 RS sym]) 1); 
by Auto_tac;  
by (res_inst_tac [("x","g+y-z")] bexI 1);
by (Simp_tac 1); 
by (rtac Infinitesimal_interval2 1); 
by (rtac Infinitesimal_zero 2); 
by Auto_tac;  
qed "inf_close_le_bound";

(*-----------------------------------------------------------------
    Zero is the only infinitesimal that is also a real
 -----------------------------------------------------------------*)

Goalw [Infinitesimal_def] 
     "[| x: SReal; y: Infinitesimal; #0 < x |] ==> y < x";
by (rtac (hrabs_ge_self RS order_le_less_trans) 1);
by Auto_tac;  
qed "Infinitesimal_less_SReal";

Goal "y: Infinitesimal ==> ALL r: SReal. #0 < r --> y < r";
by (blast_tac (claset() addIs [Infinitesimal_less_SReal]) 1);
qed "Infinitesimal_less_SReal2";

Goalw [Infinitesimal_def] 
     "[| #0 < y;  y: SReal|] ==> y ~: Infinitesimal";
by (auto_tac (claset(), simpset() addsimps [hrabs_def]));
qed "SReal_not_Infinitesimal";

Goal "[| y < #0;  y : SReal |] ==> y ~: Infinitesimal";
by (stac (Infinitesimal_minus_iff RS sym) 1); 
by (rtac SReal_not_Infinitesimal 1); 
by Auto_tac;  
qed "SReal_minus_not_Infinitesimal";

Goal "SReal Int Infinitesimal = {#0}";
by Auto_tac;
by (cut_inst_tac [("x","x"),("y","#0")] hypreal_linear 1);
by (blast_tac (claset() addDs [SReal_not_Infinitesimal,
                               SReal_minus_not_Infinitesimal]) 1);
qed "SReal_Int_Infinitesimal_zero";

Goal "[| x: SReal; x: Infinitesimal|] ==> x = #0";
by (cut_facts_tac [SReal_Int_Infinitesimal_zero] 1);
by (Blast_tac 1);
qed "SReal_Infinitesimal_zero";

Goal "[| x : SReal; x ~= #0 |] ==> x : HFinite - Infinitesimal";
by (auto_tac (claset() addDs [SReal_Infinitesimal_zero,
                              SReal_subset_HFinite RS subsetD], 
              simpset()));
qed "SReal_HFinite_diff_Infinitesimal";

Goal "hypreal_of_real x ~= #0 ==> hypreal_of_real x : HFinite - Infinitesimal";
by (rtac SReal_HFinite_diff_Infinitesimal 1);
by Auto_tac;
qed "hypreal_of_real_HFinite_diff_Infinitesimal";

Goal "(hypreal_of_real x : Infinitesimal) = (x=#0)";
by (auto_tac (claset(), simpset() addsimps [hypreal_of_real_zero]));  
by (rtac ccontr 1); 
by (rtac (hypreal_of_real_HFinite_diff_Infinitesimal RS DiffD2) 1); 
by Auto_tac;  
qed "hypreal_of_real_Infinitesimal_iff_0";
AddIffs [hypreal_of_real_Infinitesimal_iff_0];

Goal "number_of w ~= (#0::hypreal) ==> number_of w ~: Infinitesimal";
by (fast_tac (claset() addDs [SReal_number_of RS SReal_Infinitesimal_zero]) 1);
qed "number_of_not_Infinitesimal";
Addsimps [number_of_not_Infinitesimal];

Goal "[| y: SReal; x @= y; y~= #0 |] ==> x ~= #0";
by (cut_inst_tac [("x","y")] hypreal_trichotomy 1);
by (Asm_full_simp_tac 1); 
by (blast_tac (claset() addDs 
		[inf_close_sym RS (mem_infmal_iff RS iffD2),
		 SReal_not_Infinitesimal, SReal_minus_not_Infinitesimal]) 1);
qed "inf_close_SReal_not_zero";

Goal "[| x @= y; y : HFinite - Infinitesimal |] \
\     ==> x : HFinite - Infinitesimal";
by (auto_tac (claset() addIs [inf_close_sym RSN (2,inf_close_HFinite)],
              simpset() addsimps [mem_infmal_iff]));
by (dtac inf_close_trans3 1 THEN assume_tac 1);
by (blast_tac (claset() addDs [inf_close_sym]) 1);
qed "HFinite_diff_Infinitesimal_inf_close";

(*The premise y~=0 is essential; otherwise x/y =0 and we lose the 
  HFinite premise.*)
Goal "[| y ~= #0;  y: Infinitesimal;  x/y : HFinite |] ==> x : Infinitesimal";
by (dtac Infinitesimal_HFinite_mult2 1);
by (assume_tac 1);
by (asm_full_simp_tac 
    (simpset() addsimps [hypreal_divide_def, hypreal_mult_assoc]) 1);
qed "Infinitesimal_ratio";

(*------------------------------------------------------------------
       Standard Part Theorem: Every finite x: R* is infinitely 
       close to a unique real number (i.e a member of SReal)
 ------------------------------------------------------------------*)
(*------------------------------------------------------------------
         Uniqueness: Two infinitely close reals are equal
 ------------------------------------------------------------------*)

Goal "[|x: SReal; y: SReal|] ==> (x @= y) = (x = y)"; 
by Auto_tac;
by (rewrite_goals_tac [inf_close_def]);
by (dres_inst_tac [("x","y")] SReal_minus 1);
by (dtac SReal_add 1 THEN assume_tac 1);
by (dtac SReal_Infinitesimal_zero 1 THEN assume_tac 1);
by (dtac sym 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_eq_minus_iff RS sym]) 1);
qed "SReal_inf_close_iff";

Goal "(number_of v @= number_of w) = (number_of v = (number_of w :: hypreal))";
by (rtac SReal_inf_close_iff 1); 
by Auto_tac;  
qed "number_of_inf_close_iff";
Addsimps [number_of_inf_close_iff];

Goal "(hypreal_of_real k @= hypreal_of_real m) = (k = m)";
by Auto_tac;  
by (rtac (inj_hypreal_of_real RS injD) 1); 
by (rtac (SReal_inf_close_iff RS iffD1) 1); 
by Auto_tac;  
qed "hypreal_of_real_inf_close_iff";
Addsimps [hypreal_of_real_inf_close_iff];

Goal "(hypreal_of_real k @= number_of w) = (k = number_of w)";
by (stac (hypreal_of_real_inf_close_iff RS sym) 1); 
by Auto_tac;  
qed "hypreal_of_real_inf_close_number_of_iff";
Addsimps [hypreal_of_real_inf_close_number_of_iff];

Goal "[| r: SReal; s: SReal; r @= x; s @= x|] ==> r = s";
by (blast_tac (claset() addIs [(SReal_inf_close_iff RS iffD1),
               inf_close_trans2]) 1);
qed "inf_close_unique_real";

(*------------------------------------------------------------------
       Existence of unique real infinitely close
 ------------------------------------------------------------------*)
(* lemma about lubs *)
Goal "!!(x::hypreal). [| isLub R S x; isLub R S y |] ==> x = y";
by (forward_tac [isLub_isUb] 1);
by (forw_inst_tac [("x","y")] isLub_isUb 1);
by (blast_tac (claset() addSIs [hypreal_le_anti_sym]
                addSDs [isLub_le_isUb]) 1);
qed "hypreal_isLub_unique";

Goal "x: HFinite ==> EX u. isUb SReal {s. s: SReal & s < x} u";
by (dtac HFiniteD 1 THEN Step_tac 1);
by (rtac exI 1 THEN rtac isUbI 1 THEN assume_tac 2);
by (auto_tac (claset() addIs [order_less_imp_le,setleI,isUbI,
    order_less_trans], simpset() addsimps [hrabs_interval_iff]));
qed "lemma_st_part_ub";

Goal "x: HFinite ==> EX y. y: {s. s: SReal & s < x}";
by (dtac HFiniteD 1 THEN Step_tac 1);
by (dtac SReal_minus 1);
by (res_inst_tac [("x","-t")] exI 1); 
by (auto_tac (claset(), simpset() addsimps [hrabs_interval_iff]));
qed "lemma_st_part_nonempty";

Goal "{s. s: SReal & s < x} <= SReal";
by Auto_tac;
qed "lemma_st_part_subset";

Goal "x: HFinite ==> EX t. isLub SReal {s. s: SReal & s < x} t";
by (blast_tac (claset() addSIs [SReal_complete,lemma_st_part_ub,
    lemma_st_part_nonempty, lemma_st_part_subset]) 1);
qed "lemma_st_part_lub";

Goal "((t::hypreal) + r <= t) = (r <= #0)";
by (Step_tac 1);
by (dres_inst_tac [("x","-t")] hypreal_add_left_le_mono1 1);
by (dres_inst_tac [("x","t")] hypreal_add_left_le_mono1 2);
by (auto_tac (claset(), simpset() addsimps [hypreal_add_assoc RS sym]));
qed "lemma_hypreal_le_left_cancel";

Goal "[| x: HFinite;  isLub SReal {s. s: SReal & s < x} t; \
\        r: SReal;  #0 < r |] ==> x <= t + r";
by (forward_tac [isLubD1a] 1);
by (rtac ccontr 1 THEN dtac (linorder_not_le RS iffD2) 1);
by (dres_inst_tac [("x","t")] SReal_add 1 THEN assume_tac 1);
by (dres_inst_tac [("y","t + r")] (isLubD1 RS setleD) 1);
by Auto_tac;  
qed "lemma_st_part_le1";

Goalw [setle_def] "!!x::hypreal. [| S *<= x; x < y |] ==> S *<= y";
by (auto_tac (claset() addSDs [bspec,order_le_less_trans]
                       addIs [order_less_imp_le],
              simpset()));
qed "hypreal_setle_less_trans";

Goalw [isUb_def] 
     "!!x::hypreal. [| isUb R S x; x < y; y: R |] ==> isUb R S y";
by (blast_tac (claset() addIs [hypreal_setle_less_trans]) 1);
qed "hypreal_gt_isUb";

Goal "[| x: HFinite; x < y; y: SReal |] \
\              ==> isUb SReal {s. s: SReal & s < x} y";
by (auto_tac (claset() addDs [order_less_trans]
    addIs [order_less_imp_le] addSIs [isUbI,setleI], simpset()));
qed "lemma_st_part_gt_ub";

Goal "t <= t + -r ==> r <= (#0::hypreal)";
by (dres_inst_tac [("x","-t")] hypreal_add_left_le_mono1 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_add_assoc RS sym]));
qed "lemma_minus_le_zero";

Goal "[| x: HFinite; \
\        isLub SReal {s. s: SReal & s < x} t; \
\        r: SReal; #0 < r |] \
\     ==> t + -r <= x";
by (forward_tac [isLubD1a] 1);
by (rtac ccontr 1 THEN dtac not_hypreal_leE 1);
by (dtac SReal_minus 1 THEN dres_inst_tac [("x","t")] 
    SReal_add 1 THEN assume_tac 1);
by (dtac lemma_st_part_gt_ub 1 THEN REPEAT(assume_tac 1));
by (dtac isLub_le_isUb 1 THEN assume_tac 1);
by (dtac lemma_minus_le_zero 1);
by (auto_tac (claset() addDs [order_less_le_trans],  simpset()));
qed "lemma_st_part_le2";

Goal "((x::hypreal) <= t + r) = (x + -t <= r)";
by Auto_tac;  
qed "lemma_hypreal_le_swap";

Goal "[| x: HFinite; \
\        isLub SReal {s. s: SReal & s < x} t; \
\        r: SReal; #0 < r |] \
\     ==> x + -t <= r";
by (blast_tac (claset() addSIs [lemma_hypreal_le_swap RS iffD1,
                                lemma_st_part_le1]) 1);
qed "lemma_st_part1a";

Goal "(t + -r <= x) = (-(x + -t) <= (r::hypreal))";
by Auto_tac;  
qed "lemma_hypreal_le_swap2";

Goal "[| x: HFinite; \
\        isLub SReal {s. s: SReal & s < x} t; \
\        r: SReal;  #0 < r |] \
\     ==> -(x + -t) <= r";
by (blast_tac (claset() addSIs [lemma_hypreal_le_swap2 RS iffD1,
                                lemma_st_part_le2]) 1);
qed "lemma_st_part2a";

Goal "(x::hypreal): SReal ==> isUb SReal {s. s: SReal & s < x} x";
by (auto_tac (claset() addIs [isUbI, setleI,order_less_imp_le], simpset()));
qed "lemma_SReal_ub";

Goal "(x::hypreal): SReal ==> isLub SReal {s. s: SReal & s < x} x";
by (auto_tac (claset() addSIs [isLubI2,lemma_SReal_ub,setgeI], simpset()));
by (forward_tac [isUbD2a] 1);
by (res_inst_tac [("x","x"),("y","y")] hypreal_linear_less2 1);
by (auto_tac (claset() addSIs [order_less_imp_le], simpset()));
by (EVERY1[dtac SReal_dense, assume_tac, assume_tac, Step_tac]);
by (dres_inst_tac [("y","r")] isUbD 1);
by (auto_tac (claset() addDs [order_less_le_trans], simpset()));
qed "lemma_SReal_lub";

Goal "[| x: HFinite; \
\        isLub SReal {s. s: SReal & s < x} t; \
\        r: SReal; #0 < r |] \
\     ==> x + -t ~= r";
by Auto_tac;
by (forward_tac [isLubD1a RS SReal_minus] 1);
by (dtac SReal_add_cancel 1 THEN assume_tac 1);
by (dres_inst_tac [("x","x")] lemma_SReal_lub 1);
by (dtac hypreal_isLub_unique 1 THEN assume_tac 1);
by Auto_tac;
qed "lemma_st_part_not_eq1";

Goal "[| x: HFinite; \
\        isLub SReal {s. s: SReal & s < x} t; \
\        r: SReal; #0 < r |] \
\     ==> -(x + -t) ~= r";
by (auto_tac (claset(), simpset() addsimps [hypreal_minus_add_distrib]));
by (forward_tac [isLubD1a] 1);
by (dtac SReal_add_cancel 1 THEN assume_tac 1);
by (dres_inst_tac [("x","-x")] SReal_minus 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("x","x")] lemma_SReal_lub 1);
by (dtac hypreal_isLub_unique 1 THEN assume_tac 1);
by Auto_tac;
qed "lemma_st_part_not_eq2";

Goal "[| x: HFinite; \
\        isLub SReal {s. s: SReal & s < x} t; \
\        r: SReal; #0 < r |] \
\     ==> abs (x + -t) < r";
by (forward_tac [lemma_st_part1a] 1);
by (forward_tac [lemma_st_part2a] 4);
by Auto_tac;
by (REPEAT(dtac order_le_imp_less_or_eq 1));
by (auto_tac (claset() addDs [lemma_st_part_not_eq1,
    lemma_st_part_not_eq2], simpset() addsimps [hrabs_interval_iff2]));
qed "lemma_st_part_major";

Goal "[| x: HFinite; \
\        isLub SReal {s. s: SReal & s < x} t |] \
\     ==> ALL r: SReal. #0 < r --> abs (x + -t) < r";
by (blast_tac (claset() addSDs [lemma_st_part_major]) 1);
qed "lemma_st_part_major2";

(*----------------------------------------------
  Existence of real and Standard Part Theorem
 ----------------------------------------------*)
Goal "x: HFinite ==> \
\     EX t: SReal. ALL r: SReal. #0 < r --> abs (x + -t) < r";
by (forward_tac [lemma_st_part_lub] 1 THEN Step_tac 1);
by (forward_tac [isLubD1a] 1);
by (blast_tac (claset() addDs [lemma_st_part_major2]) 1);
qed "lemma_st_part_Ex";

Goalw [inf_close_def,Infinitesimal_def] 
     "x:HFinite ==> EX t: SReal. x @= t";
by (dtac lemma_st_part_Ex 1);
by Auto_tac;  
qed "st_part_Ex";

(*--------------------------------
  Unique real infinitely close
 -------------------------------*)
Goal "x:HFinite ==> EX! t. t: SReal & x @= t";
by (dtac st_part_Ex 1 THEN Step_tac 1);
by (dtac inf_close_sym 2 THEN dtac inf_close_sym 2 
    THEN dtac inf_close_sym 2);
by (auto_tac (claset() addSIs [inf_close_unique_real], simpset()));
qed "st_part_Ex1";

(*------------------------------------------------------------------
       Finite and Infinite --- more theorems
 ------------------------------------------------------------------*)

Goalw [HFinite_def,HInfinite_def] "HFinite Int HInfinite = {}";
by (auto_tac (claset() addIs [hypreal_less_irrefl] addDs [order_less_trans],
              simpset()));
qed "HFinite_Int_HInfinite_empty";
Addsimps [HFinite_Int_HInfinite_empty];

Goal "x: HFinite ==> x ~: HInfinite";
by (EVERY1[Step_tac, dtac IntI, assume_tac]);
by Auto_tac;
qed "HFinite_not_HInfinite";

Goalw [HInfinite_def, HFinite_def] "x~: HFinite ==> x: HInfinite";
by Auto_tac;  
by (dres_inst_tac [("x","r + #1")] bspec 1);
by (auto_tac (claset(), simpset() addsimps [SReal_add]));   
qed "not_HFinite_HInfinite";

Goal "x : HInfinite | x : HFinite";
by (blast_tac (claset() addIs [not_HFinite_HInfinite]) 1);
qed "HInfinite_HFinite_disj";

Goal "(x : HInfinite) = (x ~: HFinite)";
by (blast_tac (claset() addDs [HFinite_not_HInfinite,
               not_HFinite_HInfinite]) 1);
qed "HInfinite_HFinite_iff";

Goal "(x : HFinite) = (x ~: HInfinite)";
by (simp_tac (simpset() addsimps [HInfinite_HFinite_iff]) 1);
qed "HFinite_HInfinite_iff";

(*------------------------------------------------------------------
       Finite, Infinite and Infinitesimal --- more theorems
 ------------------------------------------------------------------*)

Goal "x ~: Infinitesimal ==> x : HInfinite | x : HFinite - Infinitesimal";
by (fast_tac (claset() addIs [not_HFinite_HInfinite]) 1);
qed "HInfinite_diff_HFinite_Infinitesimal_disj";

Goal "[| x : HFinite; x ~: Infinitesimal |] ==> inverse x : HFinite";
by (cut_inst_tac [("x","inverse x")] HInfinite_HFinite_disj 1);
by (auto_tac (claset() addSDs [HInfinite_inverse_Infinitesimal], simpset()));
qed "HFinite_inverse";

Goal "x : HFinite - Infinitesimal ==> inverse x : HFinite";
by (blast_tac (claset() addIs [HFinite_inverse]) 1);
qed "HFinite_inverse2";

(* stronger statement possible in fact *)
Goal "x ~: Infinitesimal ==> inverse(x) : HFinite";
by (dtac HInfinite_diff_HFinite_Infinitesimal_disj 1);
by (blast_tac (claset() addIs [HFinite_inverse,
                 HInfinite_inverse_Infinitesimal,
                 Infinitesimal_subset_HFinite RS subsetD]) 1);
qed "Infinitesimal_inverse_HFinite";

Goal "x : HFinite - Infinitesimal ==> inverse x : HFinite - Infinitesimal";
by (auto_tac (claset() addIs [Infinitesimal_inverse_HFinite], simpset()));
by (dtac Infinitesimal_HFinite_mult2 1);
by (assume_tac 1);
by (asm_full_simp_tac
   (simpset() addsimps [not_Infinitesimal_not_zero, hypreal_mult_inverse]) 1); 
qed "HFinite_not_Infinitesimal_inverse";

Goal "[| x @= y; y :  HFinite - Infinitesimal |] \
\     ==> inverse x @= inverse y";
by (forward_tac [HFinite_diff_Infinitesimal_inf_close] 1);
by (assume_tac 1);
by (forward_tac [not_Infinitesimal_not_zero2] 1);
by (forw_inst_tac [("x","x")] not_Infinitesimal_not_zero2 1);
by (REPEAT(dtac HFinite_inverse2 1));
by (dtac inf_close_mult2 1 THEN assume_tac 1);
by Auto_tac;
by (dres_inst_tac [("c","inverse x")] inf_close_mult1 1 
    THEN assume_tac 1);
by (auto_tac (claset() addIs [inf_close_sym],
    simpset() addsimps [hypreal_mult_assoc]));
qed "inf_close_inverse";

(*Used for NSLIM_inverse, NSLIMSEQ_inverse*)
bind_thm ("hypreal_of_real_inf_close_inverse",
       hypreal_of_real_HFinite_diff_Infinitesimal RSN (2, inf_close_inverse));

Goal "[| x: HFinite - Infinitesimal; \
\        h : Infinitesimal |] ==> inverse(x + h) @= inverse x";
by (auto_tac (claset() addIs [inf_close_inverse, inf_close_sym, 
                              Infinitesimal_add_inf_close_self], 
              simpset()));
qed "inverse_add_Infinitesimal_inf_close";

Goal "[| x: HFinite - Infinitesimal; \
\        h : Infinitesimal |] ==> inverse(h + x) @= inverse x";
by (rtac (hypreal_add_commute RS subst) 1);
by (blast_tac (claset() addIs [inverse_add_Infinitesimal_inf_close]) 1);
qed "inverse_add_Infinitesimal_inf_close2";

Goal "[| x : HFinite - Infinitesimal; \
\        h : Infinitesimal |] ==> inverse(x + h) + -inverse x @= h"; 
by (rtac inf_close_trans2 1);
by (auto_tac (claset() addIs [inverse_add_Infinitesimal_inf_close],
              simpset() addsimps [mem_infmal_iff,
                                  inf_close_minus_iff RS sym]));
qed "inverse_add_Infinitesimal_inf_close_Infinitesimal";

Goal "(x : Infinitesimal) = (x*x : Infinitesimal)";
by (auto_tac (claset() addIs [Infinitesimal_mult], simpset()));
by (rtac ccontr 1 THEN forward_tac [Infinitesimal_inverse_HFinite] 1);
by (forward_tac [not_Infinitesimal_not_zero] 1);
by (auto_tac (claset() addDs [Infinitesimal_HFinite_mult],
    simpset() addsimps [hypreal_mult_assoc]));
qed "Infinitesimal_square_iff";
Addsimps [Infinitesimal_square_iff RS sym];

Goal "(x*x : HFinite) = (x : HFinite)";
by (auto_tac (claset() addIs [HFinite_mult], simpset()));
by (auto_tac (claset() addDs [HInfinite_mult],
    simpset() addsimps [HFinite_HInfinite_iff]));
qed "HFinite_square_iff";
Addsimps [HFinite_square_iff];

Goal "(x*x : HInfinite) = (x : HInfinite)";
by (auto_tac (claset(), simpset() addsimps 
    [HInfinite_HFinite_iff]));
qed "HInfinite_square_iff";
Addsimps [HInfinite_square_iff];

Goal "[| a: HFinite-Infinitesimal; a* w @= a*z |] ==> w @= z";
by (Step_tac 1);
by (ftac HFinite_inverse 1 THEN assume_tac 1);
by (dtac not_Infinitesimal_not_zero 1);
by (auto_tac (claset() addDs [inf_close_mult2],
    simpset() addsimps [hypreal_mult_assoc RS sym]));
qed "inf_close_HFinite_mult_cancel";

Goal "a: HFinite-Infinitesimal ==> (a * w @= a * z) = (w @= z)";
by (auto_tac (claset() addIs [inf_close_mult2,
    inf_close_HFinite_mult_cancel], simpset()));
qed "inf_close_HFinite_mult_cancel_iff1";

(*------------------------------------------------------------------
                  more about absolute value (hrabs)
 ------------------------------------------------------------------*)

Goal "abs x @= x | abs x @= -x";
by (cut_inst_tac [("x","x")] hrabs_disj 1);
by Auto_tac;
qed "inf_close_hrabs_disj";

(*------------------------------------------------------------------
                  Theorems about monads
 ------------------------------------------------------------------*)

Goal "monad (abs x) <= monad(x) Un monad(-x)";
by (res_inst_tac [("x1","x")] (hrabs_disj RS disjE) 1);
by Auto_tac;
qed "monad_hrabs_Un_subset";

Goal "e : Infinitesimal ==> monad (x+e) = monad x";
by (fast_tac (claset() addSIs [Infinitesimal_add_inf_close_self RS inf_close_sym,
    inf_close_monad_iff RS iffD1]) 1);
qed "Infinitesimal_monad_eq";

Goalw [monad_def] "(u:monad x) = (-u:monad (-x))";
by Auto_tac;
qed "mem_monad_iff";

Goalw [monad_def] "(x:Infinitesimal) = (x:monad #0)";
by (auto_tac (claset() addIs [inf_close_sym],
    simpset() addsimps [mem_infmal_iff]));
qed "Infinitesimal_monad_zero_iff";

Goal "(x:monad #0) = (-x:monad #0)";
by (simp_tac (simpset() addsimps [Infinitesimal_monad_zero_iff RS sym]) 1);
qed "monad_zero_minus_iff";

Goal "(x:monad #0) = (abs x:monad #0)";
by (res_inst_tac [("x1","x")] (hrabs_disj RS disjE) 1);
by (auto_tac (claset(), simpset() addsimps [monad_zero_minus_iff RS sym]));
qed "monad_zero_hrabs_iff";

Goalw [monad_def] "x:monad x";
by (Simp_tac 1);
qed "mem_monad_self";
Addsimps [mem_monad_self];

(*------------------------------------------------------------------
         Proof that x @= y ==> abs x @= abs y
 ------------------------------------------------------------------*)
Goal "x @= y ==> {x,y}<=monad x";
by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps 
    [inf_close_monad_iff]) 1);
qed "inf_close_subset_monad";

Goal "x @= y ==> {x,y}<=monad y";
by (dtac inf_close_sym 1);
by (fast_tac (claset() addDs [inf_close_subset_monad]) 1);
qed "inf_close_subset_monad2";

Goalw [monad_def] "u:monad x ==> x @= u";
by (Fast_tac 1);
qed "mem_monad_inf_close";

Goalw [monad_def] "x @= u ==> u:monad x";
by (Fast_tac 1);
qed "inf_close_mem_monad";

Goalw [monad_def] "x @= u ==> x:monad u";
by (blast_tac (claset() addSIs [inf_close_sym]) 1);
qed "inf_close_mem_monad2";

Goal "[| x @= y;x:monad #0 |] ==> y:monad #0";
by (dtac mem_monad_inf_close 1);
by (fast_tac (claset() addIs [inf_close_mem_monad,inf_close_trans]) 1);
qed "inf_close_mem_monad_zero";

Goal "[| x @= y; x: Infinitesimal |] ==> abs x @= abs y";
by (dtac (Infinitesimal_monad_zero_iff RS iffD1) 1); 
by (blast_tac (claset() addIs [inf_close_mem_monad_zero, 
     monad_zero_hrabs_iff RS iffD1, mem_monad_inf_close, inf_close_trans3]) 1);
qed "Infinitesimal_inf_close_hrabs";

Goal "[| #0 < x;  x ~:Infinitesimal;  e :Infinitesimal |] ==> e < x";
by (rtac ccontr 1);
by (auto_tac (claset()
               addIs [Infinitesimal_zero RSN (2, Infinitesimal_interval)] 
               addSDs [hypreal_leI, order_le_imp_less_or_eq],
              simpset()));
qed "less_Infinitesimal_less";

Goal "[| #0 < x;  x ~: Infinitesimal; u: monad x |] ==> #0 < u";
by (dtac (mem_monad_inf_close RS inf_close_sym) 1);
by (etac (bex_Infinitesimal_iff2 RS iffD2 RS bexE) 1);
by (dres_inst_tac [("e","-xa")] less_Infinitesimal_less 1);
by Auto_tac;  
qed "Ball_mem_monad_gt_zero";

Goal "[| x < #0; x ~: Infinitesimal; u: monad x |] ==> u < #0";
by (dtac (mem_monad_inf_close RS inf_close_sym) 1);
by (etac (bex_Infinitesimal_iff RS iffD2 RS bexE) 1);
by (cut_inst_tac [("x","-x"),("e","xa")] less_Infinitesimal_less 1);
by Auto_tac;  
qed "Ball_mem_monad_less_zero";

Goal "[|#0 < x; x ~: Infinitesimal; x @= y|] ==> #0 < y";
by (blast_tac (claset() addDs [Ball_mem_monad_gt_zero,
                               inf_close_subset_monad]) 1);
qed "lemma_inf_close_gt_zero";

Goal "[|x < #0; x ~: Infinitesimal; x @= y|] ==> y < #0";
by (blast_tac (claset() addDs [Ball_mem_monad_less_zero,
    inf_close_subset_monad]) 1);
qed "lemma_inf_close_less_zero";

Goal "[| x @= y; x < #0; x ~: Infinitesimal |] ==> abs x @= abs y";
by (forward_tac [lemma_inf_close_less_zero] 1);
by (REPEAT(assume_tac 1));
by (REPEAT(dtac hrabs_minus_eqI2 1));
by Auto_tac;
qed "inf_close_hrabs1";

Goal "[| x @= y; #0 < x; x ~: Infinitesimal |] ==> abs x @= abs y";
by (forward_tac [lemma_inf_close_gt_zero] 1);
by (REPEAT(assume_tac 1));
by (REPEAT(dtac hrabs_eqI2 1));
by Auto_tac;
qed "inf_close_hrabs2";

Goal "x @= y ==> abs x @= abs y";
by (res_inst_tac [("Q","x:Infinitesimal")] (excluded_middle RS disjE) 1);
by (res_inst_tac [("x1","x"),("y1","#0")] (hypreal_linear RS disjE) 1);
by (auto_tac (claset() addIs [inf_close_hrabs1,inf_close_hrabs2,
    Infinitesimal_inf_close_hrabs], simpset()));
qed "inf_close_hrabs";

Goal "abs(x) @= #0 ==> x @= #0";
by (cut_inst_tac [("x","x")] hrabs_disj 1);
by (auto_tac (claset() addDs [inf_close_minus], simpset()));
qed "inf_close_hrabs_zero_cancel";

Goal "e: Infinitesimal ==> abs x @= abs(x+e)";
by (fast_tac (claset() addIs [inf_close_hrabs,
       Infinitesimal_add_inf_close_self]) 1);
qed "inf_close_hrabs_add_Infinitesimal";

Goal "e: Infinitesimal ==> abs x @= abs(x + -e)";
by (fast_tac (claset() addIs [inf_close_hrabs,
    Infinitesimal_add_minus_inf_close_self]) 1);
qed "inf_close_hrabs_add_minus_Infinitesimal";

Goal "[| e: Infinitesimal; e': Infinitesimal; \
\        abs(x+e) = abs(y+e')|] ==> abs x @= abs y";
by (dres_inst_tac [("x","x")] inf_close_hrabs_add_Infinitesimal 1);
by (dres_inst_tac [("x","y")] inf_close_hrabs_add_Infinitesimal 1);
by (auto_tac (claset() addIs [inf_close_trans2], simpset()));
qed "hrabs_add_Infinitesimal_cancel";

Goal "[| e: Infinitesimal; e': Infinitesimal; \
\        abs(x + -e) = abs(y + -e')|] ==> abs x @= abs y";
by (dres_inst_tac [("x","x")] inf_close_hrabs_add_minus_Infinitesimal 1);
by (dres_inst_tac [("x","y")] inf_close_hrabs_add_minus_Infinitesimal 1);
by (auto_tac (claset() addIs [inf_close_trans2], simpset()));
qed "hrabs_add_minus_Infinitesimal_cancel";

(* interesting slightly counterintuitive theorem: necessary 
   for proving that an open interval is an NS open set 
*)
Goalw [Infinitesimal_def] 
     "[| x < y;  u: Infinitesimal |] \
\     ==> hypreal_of_real x + u < hypreal_of_real y";
by (dtac (hypreal_of_real_less_iff RS iffD2) 1); 
by (dtac (hypreal_less_minus_iff RS iffD1) 1 THEN Step_tac 1);
by (rtac (hypreal_less_minus_iff RS iffD2) 1);
by (dres_inst_tac [("x","hypreal_of_real y + -hypreal_of_real x")] bspec 1);
by (auto_tac (claset(),
              simpset() addsimps [hypreal_add_commute, 
                                  hrabs_interval_iff,
                                  SReal_add, SReal_minus]));
qed "Infinitesimal_add_hypreal_of_real_less";

Goal "[| x: Infinitesimal; abs(hypreal_of_real r) < hypreal_of_real y |] \
\     ==> abs (hypreal_of_real r + x) < hypreal_of_real y";
by (dres_inst_tac [("x","hypreal_of_real r")] 
    inf_close_hrabs_add_Infinitesimal 1);
by (dtac (inf_close_sym RS (bex_Infinitesimal_iff2 RS iffD2)) 1);
by (auto_tac (claset() addSIs [Infinitesimal_add_hypreal_of_real_less],
              simpset() addsimps [hypreal_of_real_hrabs]));
qed "Infinitesimal_add_hrabs_hypreal_of_real_less";

Goal "[| x: Infinitesimal;  abs(hypreal_of_real r) < hypreal_of_real y |] \
\     ==> abs (x + hypreal_of_real r) < hypreal_of_real y";
by (rtac (hypreal_add_commute RS subst) 1);
by (etac Infinitesimal_add_hrabs_hypreal_of_real_less 1);
by (assume_tac 1);
qed "Infinitesimal_add_hrabs_hypreal_of_real_less2";

Goalw [hypreal_le_def]
     "[| u: Infinitesimal; hypreal_of_real x + u <= hypreal_of_real y |] \
\     ==> hypreal_of_real x <= hypreal_of_real y";
by (EVERY1 [rtac notI, rtac contrapos_np, assume_tac]);
by (res_inst_tac [("C","-u")] hypreal_less_add_right_cancel 1);
by (Asm_full_simp_tac 1); 
by (dtac (Infinitesimal_minus_iff RS iffD2) 1); 
by (dtac Infinitesimal_add_hypreal_of_real_less 1); 
by (assume_tac 1); 
by Auto_tac;  
qed "Infinitesimal_add_cancel_hypreal_of_real_le";

Goal "[| u: Infinitesimal;  hypreal_of_real x + u <= hypreal_of_real y |] \
\     ==> x <= y";
by (blast_tac (claset() addSIs [hypreal_of_real_le_iff RS iffD1,
               Infinitesimal_add_cancel_hypreal_of_real_le]) 1);
qed "Infinitesimal_add_cancel_real_le";

Goal "[| u: Infinitesimal; v: Infinitesimal; \
\        hypreal_of_real x + u <= hypreal_of_real y + v |] \
\     ==> hypreal_of_real x <= hypreal_of_real y";
by (asm_full_simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1); 
by Auto_tac;  
by (dres_inst_tac [("u","v-u")] Infinitesimal_add_hypreal_of_real_less 1);
by (auto_tac (claset(), simpset() addsimps [Infinitesimal_diff]));   
qed "hypreal_of_real_le_add_Infininitesimal_cancel";

Goal "[| u: Infinitesimal; v: Infinitesimal; \
\        hypreal_of_real x + u <= hypreal_of_real y + v |] \
\     ==> x <= y";
by (blast_tac (claset() addSIs [hypreal_of_real_le_iff RS iffD1,
                          hypreal_of_real_le_add_Infininitesimal_cancel]) 1);
qed "hypreal_of_real_le_add_Infininitesimal_cancel2";

Goal "[| hypreal_of_real x < e; e: Infinitesimal |] ==> hypreal_of_real x <= #0";
by (rtac hypreal_leI 1 THEN Step_tac 1);
by (dtac Infinitesimal_interval 1);
by (dtac (SReal_hypreal_of_real RS SReal_Infinitesimal_zero) 4);
by (auto_tac (claset(), simpset() addsimps [hypreal_of_real_zero]));
qed "hypreal_of_real_less_Infinitesimal_le_zero";

(*used once, in NSDERIV_inverse*)
Goal "[| h: Infinitesimal; x ~= #0 |] ==> hypreal_of_real x + h ~= #0";
by Auto_tac;  
qed "Infinitesimal_add_not_zero";

Goal "x*x + y*y : Infinitesimal ==> x*x : Infinitesimal";
by (rtac Infinitesimal_interval2 1); 
by (rtac hypreal_le_square 3); 
by (rtac hypreal_self_le_add_pos 3); 
by Auto_tac;  
qed "Infinitesimal_square_cancel";
Addsimps [Infinitesimal_square_cancel];

Goal "x*x + y*y : HFinite ==> x*x : HFinite";
by (rtac HFinite_bounded 1); 
by (rtac hypreal_self_le_add_pos 2); 
by (rtac (rename_numerals hypreal_le_square) 2); 
by (assume_tac 1); 
qed "HFinite_square_cancel";
Addsimps [HFinite_square_cancel];

Goal "x*x + y*y : Infinitesimal ==> y*y : Infinitesimal";
by (rtac Infinitesimal_square_cancel 1);
by (rtac (hypreal_add_commute RS subst) 1);
by (Simp_tac 1);
qed "Infinitesimal_square_cancel2";
Addsimps [Infinitesimal_square_cancel2];

Goal "x*x + y*y : HFinite ==> y*y : HFinite";
by (rtac HFinite_square_cancel 1);
by (rtac (hypreal_add_commute RS subst) 1);
by (Simp_tac 1);
qed "HFinite_square_cancel2";
Addsimps [HFinite_square_cancel2];

Goal "x*x + y*y + z*z : Infinitesimal ==> x*x : Infinitesimal";
by (blast_tac (claset() addIs [hypreal_self_le_add_pos2,
    Infinitesimal_interval2, rename_numerals hypreal_le_square]) 1);
qed "Infinitesimal_sum_square_cancel";
Addsimps [Infinitesimal_sum_square_cancel];

Goal "x*x + y*y + z*z : HFinite ==> x*x : HFinite";
by (blast_tac (claset() addIs [hypreal_self_le_add_pos2, HFinite_bounded, 
                               rename_numerals hypreal_le_square,
		               HFinite_number_of]) 1);
qed "HFinite_sum_square_cancel";
Addsimps [HFinite_sum_square_cancel];

Goal "y*y + x*x + z*z : Infinitesimal ==> x*x : Infinitesimal";
by (rtac Infinitesimal_sum_square_cancel 1);
by (asm_full_simp_tac (simpset() addsimps hypreal_add_ac) 1);
qed "Infinitesimal_sum_square_cancel2";
Addsimps [Infinitesimal_sum_square_cancel2];

Goal "y*y + x*x + z*z : HFinite ==> x*x : HFinite";
by (rtac HFinite_sum_square_cancel 1);
by (asm_full_simp_tac (simpset() addsimps hypreal_add_ac) 1);
qed "HFinite_sum_square_cancel2";
Addsimps [HFinite_sum_square_cancel2];

Goal "z*z + y*y + x*x : Infinitesimal ==> x*x : Infinitesimal";
by (rtac Infinitesimal_sum_square_cancel 1);
by (asm_full_simp_tac (simpset() addsimps hypreal_add_ac) 1);
qed "Infinitesimal_sum_square_cancel3";
Addsimps [Infinitesimal_sum_square_cancel3];

Goal "z*z + y*y + x*x : HFinite ==> x*x : HFinite";
by (rtac HFinite_sum_square_cancel 1);
by (asm_full_simp_tac (simpset() addsimps hypreal_add_ac) 1);
qed "HFinite_sum_square_cancel3";
Addsimps [HFinite_sum_square_cancel3];

Goal "[| y: monad x; #0 < hypreal_of_real e |] \
\     ==> abs (y + -x) < hypreal_of_real e";
by (dtac (mem_monad_inf_close RS inf_close_sym) 1);
by (dtac (bex_Infinitesimal_iff RS iffD2) 1);
by (auto_tac (claset() addSDs [InfinitesimalD], simpset()));
qed "monad_hrabs_less";

Goal "x: monad (hypreal_of_real  a) ==> x: HFinite";
by (dtac (mem_monad_inf_close RS inf_close_sym) 1);
by (dtac (bex_Infinitesimal_iff2 RS iffD2) 1);
by (step_tac (claset() addSDs 
       [Infinitesimal_subset_HFinite RS subsetD]) 1);
by (etac (SReal_hypreal_of_real RS (SReal_subset_HFinite 
         RS subsetD) RS HFinite_add) 1);
qed "mem_monad_SReal_HFinite";

(*------------------------------------------------------------------
              Theorems about standard part
 ------------------------------------------------------------------*)

Goalw [st_def] "x: HFinite ==> st x @= x";
by (forward_tac [st_part_Ex] 1 THEN Step_tac 1);
by (rtac someI2 1);
by (auto_tac (claset() addIs [inf_close_sym], simpset()));
qed "st_inf_close_self";

Goalw [st_def] "x: HFinite ==> st x: SReal";
by (forward_tac [st_part_Ex] 1 THEN Step_tac 1);
by (rtac someI2 1);
by (auto_tac (claset() addIs [inf_close_sym], simpset()));
qed "st_SReal";

Goal "x: HFinite ==> st x: HFinite";
by (etac (st_SReal RS (SReal_subset_HFinite RS subsetD)) 1);
qed "st_HFinite";

Goalw [st_def] "x: SReal ==> st x = x";
by (rtac some_equality 1);
by (fast_tac (claset() addIs [(SReal_subset_HFinite RS subsetD)]) 1);
by (blast_tac (claset() addDs [SReal_inf_close_iff RS iffD1]) 1);
qed "st_SReal_eq";

(* should be added to simpset *)
Goal "st (hypreal_of_real x) = hypreal_of_real x";
by (rtac (SReal_hypreal_of_real RS st_SReal_eq) 1);
qed "st_hypreal_of_real";

Goal "[| x: HFinite; y: HFinite; st x = st y |] ==> x @= y";
by (auto_tac (claset() addSDs [st_inf_close_self] 
              addSEs [inf_close_trans3], simpset()));
qed "st_eq_inf_close";

Goal "[| x: HFinite; y: HFinite; x @= y |] ==> st x = st y";
by (EVERY1 [forward_tac [st_inf_close_self],
    forw_inst_tac [("x","y")] st_inf_close_self,
    dtac st_SReal,dtac st_SReal]);
by (fast_tac (claset() addEs [inf_close_trans,
    inf_close_trans2,SReal_inf_close_iff RS iffD1]) 1);
qed "inf_close_st_eq";

Goal "[| x: HFinite; y: HFinite|] \
\                  ==> (x @= y) = (st x = st y)";
by (blast_tac (claset() addIs [inf_close_st_eq,
               st_eq_inf_close]) 1);
qed "st_eq_inf_close_iff";

Goal "[| x: SReal; e: Infinitesimal |] ==> st(x + e) = x";
by (forward_tac [st_SReal_eq RS subst] 1);
by (assume_tac 2);
by (forward_tac [SReal_subset_HFinite RS subsetD] 1);
by (forward_tac [Infinitesimal_subset_HFinite RS subsetD] 1);
by (dtac st_SReal_eq 1);
by (rtac inf_close_st_eq 1);
by (auto_tac (claset() addIs  [HFinite_add],
    simpset() addsimps [Infinitesimal_add_inf_close_self 
    RS inf_close_sym]));
qed "st_Infinitesimal_add_SReal";

Goal "[| x: SReal; e: Infinitesimal |] \
\     ==> st(e + x) = x";
by (rtac (hypreal_add_commute RS subst) 1);
by (blast_tac (claset() addSIs [st_Infinitesimal_add_SReal]) 1);
qed "st_Infinitesimal_add_SReal2";

Goal "x: HFinite ==> \
\     EX e: Infinitesimal. x = st(x) + e";
by (blast_tac (claset() addSDs [(st_inf_close_self RS 
    inf_close_sym),bex_Infinitesimal_iff2 RS iffD2]) 1);
qed "HFinite_st_Infinitesimal_add";

Goal "[| x: HFinite; y: HFinite |] \
\     ==> st (x + y) = st(x) + st(y)";
by (forward_tac [HFinite_st_Infinitesimal_add] 1);
by (forw_inst_tac [("x","y")] HFinite_st_Infinitesimal_add 1);
by (Step_tac 1);
by (subgoal_tac "st (x + y) = st ((st x + e) + (st y + ea))" 1);
by (dtac sym 2 THEN dtac sym 2);
by (Asm_full_simp_tac 2);
by (asm_simp_tac (simpset() addsimps hypreal_add_ac) 1);
by (REPEAT(dtac st_SReal 1));
by (dtac SReal_add 1 THEN assume_tac 1);
by (dtac Infinitesimal_add 1 THEN assume_tac 1);
by (rtac (hypreal_add_assoc RS subst) 1);
by (blast_tac (claset() addSIs [st_Infinitesimal_add_SReal2]) 1);
qed "st_add";

Goal "st (number_of w) = number_of w";
by (rtac (SReal_number_of RS st_SReal_eq) 1);
qed "st_number_of";
Addsimps [st_number_of];

Goal "y: HFinite ==> st(-y) = -st(y)";
by (forward_tac [HFinite_minus_iff RS iffD2] 1);
by (rtac hypreal_add_minus_eq_minus 1);
by (dtac (st_add RS sym) 1 THEN assume_tac 1);
by Auto_tac;  
qed "st_minus";

Goalw [hypreal_diff_def]
     "[| x: HFinite; y: HFinite |] ==> st (x-y) = st(x) - st(y)";
by (forw_inst_tac [("y1","y")] (st_minus RS sym) 1);
by (dres_inst_tac [("x1","y")] (HFinite_minus_iff RS iffD2) 1);
by (asm_simp_tac (simpset() addsimps [st_add]) 1);
qed "st_diff";

(* lemma *)
Goal "[| x: HFinite; y: HFinite; \
\        e: Infinitesimal;       \
\        ea : Infinitesimal |]   \
\      ==> e*y + x*ea + e*ea: Infinitesimal";
by (forw_inst_tac [("x","e"),("y","y")] Infinitesimal_HFinite_mult 1);
by (forw_inst_tac [("x","ea"),("y","x")] Infinitesimal_HFinite_mult 2);
by (dtac Infinitesimal_mult 3);
by (auto_tac (claset() addIs [Infinitesimal_add],
              simpset() addsimps hypreal_add_ac @ hypreal_mult_ac));
qed "lemma_st_mult";

Goal "[| x: HFinite; y: HFinite |] \
\              ==> st (x * y) = st(x) * st(y)";
by (forward_tac [HFinite_st_Infinitesimal_add] 1);
by (forw_inst_tac [("x","y")] HFinite_st_Infinitesimal_add 1);
by (Step_tac 1);
by (subgoal_tac "st (x * y) = st ((st x + e) * (st y + ea))" 1);
by (dtac sym 2 THEN dtac sym 2);
by (Asm_full_simp_tac 2);
by (thin_tac "x = st x + e" 1);
by (thin_tac "y = st y + ea" 1);
by (asm_full_simp_tac (simpset() addsimps 
    [hypreal_add_mult_distrib,hypreal_add_mult_distrib2]) 1);
by (REPEAT(dtac st_SReal 1));
by (full_simp_tac (simpset() addsimps [hypreal_add_assoc]) 1);
by (rtac st_Infinitesimal_add_SReal 1);
by (blast_tac (claset() addSIs [SReal_mult]) 1);
by (REPEAT(dtac (SReal_subset_HFinite RS subsetD) 1));
by (rtac (hypreal_add_assoc RS subst) 1);
by (blast_tac (claset() addSIs [lemma_st_mult]) 1);
qed "st_mult";

Goal "x: Infinitesimal ==> st x = #0";
by (rtac (st_number_of RS subst) 1);
by (rtac inf_close_st_eq 1);
by (auto_tac (claset() addIs [Infinitesimal_subset_HFinite RS subsetD],
              simpset() addsimps [mem_infmal_iff RS sym]));
qed "st_Infinitesimal";

Goal "st(x) ~= #0 ==> x ~: Infinitesimal";
by (fast_tac (claset() addIs [st_Infinitesimal]) 1);
qed "st_not_Infinitesimal";

Goal "[| x: HFinite; st x ~= #0 |] \
\     ==> st(inverse x) = inverse (st x)";
by (res_inst_tac [("c1","st x")] (hypreal_mult_left_cancel RS iffD1) 1);
by (auto_tac (claset(),
       simpset() addsimps [st_mult RS sym, st_not_Infinitesimal,
                           HFinite_inverse]));
by (stac hypreal_mult_inverse 1); 
by Auto_tac;  
qed "st_inverse";

Goal "[| x: HFinite; y: HFinite; st y ~= #0 |] \
\     ==> st(x/y) = (st x) / (st y)";
by (auto_tac (claset(),
      simpset() addsimps [hypreal_divide_def, st_mult, st_not_Infinitesimal, 
                          HFinite_inverse, st_inverse]));
qed "st_divide";
Addsimps [st_divide];

Goal "x: HFinite ==> st(st(x)) = st(x)";
by (blast_tac (claset() addIs [st_HFinite, st_inf_close_self,
                               inf_close_st_eq]) 1);
qed "st_idempotent";
Addsimps [st_idempotent];

(*** lemmas ***)
Goal "[| x: HFinite; y: HFinite; \
\        u: Infinitesimal; st x < st y \
\     |] ==> st x + u < st y";
by (REPEAT(dtac st_SReal 1));
by (auto_tac (claset() addSIs [Infinitesimal_add_hypreal_of_real_less],
              simpset() addsimps [SReal_iff]));
qed "Infinitesimal_add_st_less";

Goalw [hypreal_le_def]
     "[| x: HFinite; y: HFinite; \
\        u: Infinitesimal; st x <= st y + u\
\     |] ==> st x <= st y";
by (auto_tac (claset() addDs [Infinitesimal_add_st_less],
              simpset()));
qed "Infinitesimal_add_st_le_cancel";

Goal "[| x: HFinite; y: HFinite; x <= y |] \
\     ==> st(x) <= st(y)";
by (forward_tac [HFinite_st_Infinitesimal_add] 1);
by (rotate_tac 1 1);
by (forward_tac [HFinite_st_Infinitesimal_add] 1);
by (Step_tac 1);
by (rtac Infinitesimal_add_st_le_cancel 1);
by (res_inst_tac [("x","ea"),("y","e")] 
             Infinitesimal_diff 3);
by (auto_tac (claset(),
         simpset() addsimps [hypreal_add_assoc RS sym]));
qed "st_le";

Goal "[| #0 <= x;  x: HFinite |] ==> #0 <= st x";
by (rtac (st_number_of RS subst) 1);
by (auto_tac (claset() addIs [st_le],
              simpset() delsimps [st_number_of]));
qed "st_zero_le";

Goal "[| x <= #0;  x: HFinite |] ==> st x <= #0";
by (rtac (st_number_of RS subst) 1);
by (auto_tac (claset() addIs [st_le],
              simpset() delsimps [st_number_of]));
qed "st_zero_ge";

Goal "x: HFinite ==> abs(st x) = st(abs x)";
by (case_tac "#0 <= x" 1);
by (auto_tac (claset() addSDs [not_hypreal_leE, order_less_imp_le],
              simpset() addsimps [st_zero_le,hrabs_eqI1, hrabs_minus_eqI1,
                                  st_zero_ge,st_minus]));
qed "st_hrabs";

(*--------------------------------------------------------------------
   Alternative definitions for HFinite using Free ultrafilter
 --------------------------------------------------------------------*)

Goal "[| X: Rep_hypreal x; Y: Rep_hypreal x |] \
\     ==> {n. X n = Y n} : FreeUltrafilterNat";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by Auto_tac;
by (Ultra_tac 1);
qed "FreeUltrafilterNat_Rep_hypreal";

Goal "{n. Yb n < Y n} Int {n. -y = Yb n} <= {n. -y < Y n}";
by Auto_tac;
qed "lemma_free1";

Goal "{n. Xa n < Yc n} Int {n. y = Yc n} <= {n. Xa n < y}";
by Auto_tac;
qed "lemma_free2";

Goalw [HFinite_def] 
    "x : HFinite ==> EX X: Rep_hypreal x. \
\    EX u. {n. abs (X n) < u}:  FreeUltrafilterNat";
by (auto_tac (claset(), simpset() addsimps 
    [hrabs_interval_iff]));
by (auto_tac (claset(), simpset() addsimps 
    [hypreal_less_def,SReal_iff,hypreal_minus,
     hypreal_of_real_def]));
by (dtac FreeUltrafilterNat_Rep_hypreal 1 THEN assume_tac 1);
by (res_inst_tac [("x","Y")] bexI 1 THEN assume_tac 2);
by (res_inst_tac [("x","y")] exI 1);
by (Ultra_tac 1 THEN arith_tac 1);
qed "HFinite_FreeUltrafilterNat";

Goalw [HFinite_def] 
     "EX X: Rep_hypreal x. \
\      EX u. {n. abs (X n) < u}: FreeUltrafilterNat\
\      ==>  x : HFinite";
by (auto_tac (claset(), simpset() addsimps 
    [hrabs_interval_iff]));
by (res_inst_tac [("x","hypreal_of_real u")] bexI 1);
by (auto_tac (claset() addSIs [exI], simpset() addsimps 
    [hypreal_less_def,SReal_iff,hypreal_minus,
     hypreal_of_real_def]));
by (ALLGOALS(Ultra_tac THEN' arith_tac));
qed "FreeUltrafilterNat_HFinite";

Goal "(x : HFinite) = (EX X: Rep_hypreal x. \
\          EX u. {n. abs (X n) < u}:  FreeUltrafilterNat)";
by (blast_tac (claset() addSIs [HFinite_FreeUltrafilterNat,
               FreeUltrafilterNat_HFinite]) 1);
qed "HFinite_FreeUltrafilterNat_iff";

(*--------------------------------------------------------------------
   Alternative definitions for HInfinite using Free ultrafilter
 --------------------------------------------------------------------*)
Goal "- {n. (u::real) < abs (xa n)} = {n. abs (xa n) <= u}";
by Auto_tac;
qed "lemma_Compl_eq";

Goal "- {n. abs (xa n) < (u::real)} = {n. u <= abs (xa n)}";
by Auto_tac;
qed "lemma_Compl_eq2";

Goal "{n. abs (xa n) <= (u::real)} Int {n. u <= abs (xa n)} \
\         = {n. abs(xa n) = u}";
by Auto_tac;
qed "lemma_Int_eq1";

Goal "{n. abs (xa n) = u} <= {n. abs (xa n) < u + (#1::real)}";
by Auto_tac;
qed "lemma_FreeUltrafilterNat_one";

(*-------------------------------------
  Exclude this type of sets from free 
  ultrafilter for Infinite numbers!
 -------------------------------------*)
Goal "[| xa: Rep_hypreal x; \
\                 {n. abs (xa n) = u} : FreeUltrafilterNat \
\              |] ==> x: HFinite";
by (rtac FreeUltrafilterNat_HFinite 1);
by (res_inst_tac [("x","xa")] bexI 1);
by (res_inst_tac [("x","u + #1")] exI 1);
by (Ultra_tac 1 THEN assume_tac 1);
qed "FreeUltrafilterNat_const_Finite";

val [prem] = goal thy "x : HInfinite ==> EX X: Rep_hypreal x. \
\          ALL u. {n. u < abs (X n)}:  FreeUltrafilterNat";
by (cut_facts_tac [(prem RS (HInfinite_HFinite_iff RS iffD1))] 1);
by (cut_inst_tac [("x","x")] Rep_hypreal_nonempty 1);
by (auto_tac (claset(), simpset() delsimps [Rep_hypreal_nonempty] 
    addsimps [HFinite_FreeUltrafilterNat_iff,Bex_def]));
by (REPEAT(dtac spec 1));
by Auto_tac;
by (dres_inst_tac [("x","u")] spec 1 THEN 
    REPEAT(dtac FreeUltrafilterNat_Compl_mem 1));
by (dtac FreeUltrafilterNat_Int 1 THEN assume_tac 1);


by (asm_full_simp_tac (simpset() addsimps [lemma_Compl_eq,
    lemma_Compl_eq2,lemma_Int_eq1]) 1);
by (auto_tac (claset() addDs [FreeUltrafilterNat_const_Finite],
    simpset() addsimps [(prem RS (HInfinite_HFinite_iff RS iffD1))]));
qed "HInfinite_FreeUltrafilterNat";

(* yet more lemmas! *)
Goal "{n. abs (Xa n) < u} Int {n. X n = Xa n} \
\         <= {n. abs (X n) < (u::real)}";
by Auto_tac;
qed "lemma_Int_HI";

Goal "{n. u < abs (X n)} Int {n. abs (X n) < (u::real)} = {}";
by (auto_tac (claset() addIs [real_less_asym], simpset()));
qed "lemma_Int_HIa";

Goal "EX X: Rep_hypreal x. ALL u. \
\              {n. u < abs (X n)}: FreeUltrafilterNat\
\              ==>  x : HInfinite";
by (rtac (HInfinite_HFinite_iff RS iffD2) 1);
by (Step_tac 1 THEN dtac HFinite_FreeUltrafilterNat 1);
by Auto_tac;
by (dres_inst_tac [("x","u")] spec 1);
by (dtac FreeUltrafilterNat_Rep_hypreal 1 THEN assume_tac 1);
by (dres_inst_tac [("Y","{n. X n = Xa n}")] FreeUltrafilterNat_Int 1);
by (dtac (lemma_Int_HI RSN (2,FreeUltrafilterNat_subset)) 2);
by (dres_inst_tac [("Y","{n. abs (X n) < u}")] FreeUltrafilterNat_Int 2);
by (auto_tac (claset(), simpset() addsimps [lemma_Int_HIa,
              FreeUltrafilterNat_empty]));
qed "FreeUltrafilterNat_HInfinite";

Goal "(x : HInfinite) = (EX X: Rep_hypreal x. \
\          ALL u. {n. u < abs (X n)}:  FreeUltrafilterNat)";
by (blast_tac (claset() addSIs [HInfinite_FreeUltrafilterNat,
               FreeUltrafilterNat_HInfinite]) 1);
qed "HInfinite_FreeUltrafilterNat_iff";

(*--------------------------------------------------------------------
   Alternative definitions for Infinitesimal using Free ultrafilter
 --------------------------------------------------------------------*)

Goal "{n. - u < Yd n} Int {n. xa n = Yd n} <= {n. -u < xa n}";
by Auto_tac;
qed "lemma_free4";

Goal "{n. Yb n < u} Int {n. xa n = Yb n} <= {n. xa n < u}";
by Auto_tac;
qed "lemma_free5";

Goalw [Infinitesimal_def] 
          "x : Infinitesimal ==> EX X: Rep_hypreal x. \
\          ALL u. #0 < u --> {n. abs (X n) < u}:  FreeUltrafilterNat";
by (auto_tac (claset(), simpset() addsimps [hrabs_interval_iff]));
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (EVERY[Auto_tac, rtac bexI 1, rtac lemma_hyprel_refl 2, Step_tac 1]);
by (dtac (hypreal_of_real_less_iff RS iffD2) 1);
by (dres_inst_tac [("x","hypreal_of_real u")] bspec 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_of_real_zero]));
by (auto_tac (claset(), 
              simpset() addsimps [hypreal_less_def, hypreal_minus,
                                  hypreal_of_real_def,hypreal_of_real_zero]));
by (Ultra_tac 1 THEN arith_tac 1);
qed "Infinitesimal_FreeUltrafilterNat";

Goalw [Infinitesimal_def] 
     "EX X: Rep_hypreal x. \
\           ALL u. #0 < u --> {n. abs (X n) < u} : FreeUltrafilterNat \
\     ==> x : Infinitesimal";
by (auto_tac (claset(),
              simpset() addsimps [hrabs_interval_iff,abs_interval_iff]));
by (auto_tac (claset(),
              simpset() addsimps [SReal_iff]));
by (auto_tac (claset() addSIs [exI] 
                               addIs [FreeUltrafilterNat_subset],
    simpset() addsimps [hypreal_less_def, hypreal_minus,hypreal_of_real_def]));
qed "FreeUltrafilterNat_Infinitesimal";

Goal "(x : Infinitesimal) = (EX X: Rep_hypreal x. \
\          ALL u. #0 < u --> {n. abs (X n) < u}:  FreeUltrafilterNat)";
by (blast_tac (claset() addSIs [Infinitesimal_FreeUltrafilterNat,
               FreeUltrafilterNat_Infinitesimal]) 1);
qed "Infinitesimal_FreeUltrafilterNat_iff";

(*------------------------------------------------------------------------
         Infinitesimals as smaller than 1/n for all n::nat (> 0)
 ------------------------------------------------------------------------*)

Goal "(ALL r. #0 < r --> x < r) = (ALL n. x < inverse(real_of_nat (Suc n)))";
by (auto_tac (claset(), simpset() addsimps [real_of_nat_Suc_gt_zero]));
by (blast_tac (claset() addSDs [reals_Archimedean] 
                        addIs [order_less_trans]) 1);
qed "lemma_Infinitesimal";

Goal "(ALL r: SReal. #0 < r --> x < r) = \
\     (ALL n. x < inverse(hypreal_of_nat (Suc n)))";
by (Step_tac 1);
by (dres_inst_tac [("x","inverse (hypreal_of_real(real_of_nat (Suc n)))")] 
    bspec 1);
by (full_simp_tac (simpset() addsimps [SReal_inverse]) 1); 
by (rtac (real_of_nat_Suc_gt_zero RS rename_numerals real_inverse_gt_zero RS 
          (hypreal_of_real_less_iff RS iffD2) RSN(2,impE)) 1);
by (assume_tac 2);
by (asm_full_simp_tac (simpset() addsimps 
       [real_of_nat_Suc_gt_zero, hypreal_of_real_zero, hypreal_of_nat_def]) 1);
by (auto_tac (claset() addSDs [reals_Archimedean],
              simpset() addsimps [SReal_iff,hypreal_of_real_zero RS sym]));
by (dtac (hypreal_of_real_less_iff RS iffD2) 1);
by (asm_full_simp_tac (simpset() addsimps 
         [real_of_nat_Suc_gt_zero, hypreal_of_nat_def])1);
by (blast_tac (claset() addIs [order_less_trans]) 1);
qed "lemma_Infinitesimal2";

Goalw [Infinitesimal_def] 
     "Infinitesimal = {x. ALL n. abs x < inverse (hypreal_of_nat (Suc n))}";
by (auto_tac (claset(), simpset() addsimps [lemma_Infinitesimal2]));
qed "Infinitesimal_hypreal_of_nat_iff";


(*---------------------------------------------------------------------------
       Proof that omega (whr) is an infinite number and 
       hence that epsilon (ehr) is an infinitesimal number.
 ---------------------------------------------------------------------------*)
Goal "{n. n < Suc m} = {n. n < m} Un {n. n = m}";
by (auto_tac (claset(), simpset() addsimps [less_Suc_eq]));
qed "Suc_Un_eq";

(*-------------------------------------------
  Prove that any segment is finite and 
  hence cannot belong to FreeUltrafilterNat
 -------------------------------------------*)
Goal "finite {n::nat. n < m}";
by (nat_ind_tac "m" 1);
by (auto_tac (claset(), simpset() addsimps [Suc_Un_eq]));
qed "finite_nat_segment";

Goal "finite {n::nat. real_of_nat n < real_of_nat m}";
by (auto_tac (claset() addIs [finite_nat_segment], simpset()));
qed "finite_real_of_nat_segment";

Goal "finite {n. real_of_nat n < u}";
by (cut_inst_tac [("x","u")] reals_Archimedean2 1);
by (Step_tac 1);
by (rtac (finite_real_of_nat_segment RSN (2,finite_subset)) 1);
by (auto_tac (claset() addDs [order_less_trans], simpset()));
qed "finite_real_of_nat_less_real";

Goal "{n. f n <= u} = {n. f n < u} Un {n. u = (f n :: real)}";
by (auto_tac (claset() addDs [order_le_imp_less_or_eq],
              simpset() addsimps [order_less_imp_le]));
qed "lemma_real_le_Un_eq";

Goal "finite {n. real_of_nat n <= u}";
by (auto_tac (claset(), 
              simpset() addsimps [lemma_real_le_Un_eq,lemma_finite_omega_set, 
                                  finite_real_of_nat_less_real]));
qed "finite_real_of_nat_le_real";

Goal "finite {n. abs(real_of_nat n) <= u}";
by (simp_tac (simpset() addsimps [real_of_nat_Suc_gt_zero,
                                  finite_real_of_nat_le_real]) 1);
qed "finite_rabs_real_of_nat_le_real";

Goal "{n. abs(real_of_nat n) <= u} ~: FreeUltrafilterNat";
by (blast_tac (claset() addSIs [FreeUltrafilterNat_finite,
                                finite_rabs_real_of_nat_le_real]) 1);
qed "rabs_real_of_nat_le_real_FreeUltrafilterNat";

Goal "{n. u < real_of_nat n} : FreeUltrafilterNat";
by (rtac ccontr 1 THEN dtac FreeUltrafilterNat_Compl_mem 1);
by (subgoal_tac "- {n. u < real_of_nat n} = {n. real_of_nat n <= u}" 1);
by (Force_tac 2); 
by (asm_full_simp_tac (simpset() addsimps
        [finite_real_of_nat_le_real RS FreeUltrafilterNat_finite]) 1); 
qed "FreeUltrafilterNat_nat_gt_real";

(*--------------------------------------------------------------
 The complement of {n. abs(real_of_nat n) <= u} = 
 {n. u < abs (real_of_nat n)} is in FreeUltrafilterNat 
 by property of (free) ultrafilters
 --------------------------------------------------------------*)
Goal "- {n. real_of_nat n <= u} = {n. u < real_of_nat n}";
by (auto_tac (claset() addSDs [order_le_less_trans],
              simpset() addsimps [not_real_leE]));
val lemma = result();

Goal "{n. u < abs (real_of_nat n)} : FreeUltrafilterNat";
by (cut_inst_tac [("u","u")] rabs_real_of_nat_le_real_FreeUltrafilterNat 1);
by (auto_tac (claset() addDs [FreeUltrafilterNat_Compl_mem],
              simpset() addsimps [lemma]));
qed "FreeUltrafilterNat_omega";

(*-----------------------------------------------
       Omega is a member of HInfinite
 -----------------------------------------------*)

Goal "hyprel```{%n::nat. real_of_nat (Suc n)} : hypreal";
by Auto_tac;
qed "hypreal_omega";


Goal "{n. u < real_of_nat n} : FreeUltrafilterNat";
by (cut_inst_tac [("u","u")] rabs_real_of_nat_le_real_FreeUltrafilterNat 1);
by (auto_tac (claset() addDs [FreeUltrafilterNat_Compl_mem],
              simpset() addsimps [lemma]));
qed "FreeUltrafilterNat_omega";

Goalw [omega_def] "whr: HInfinite";
by (auto_tac (claset() addSIs [FreeUltrafilterNat_HInfinite], 
              simpset()));
by (rtac bexI 1); 
by (rtac lemma_hyprel_refl 2); 
by Auto_tac;  
by (simp_tac (simpset() addsimps [real_of_nat_Suc, real_diff_less_eq RS sym, 
                                  FreeUltrafilterNat_omega]) 1); 
qed "HInfinite_omega";

(*-----------------------------------------------
       Epsilon is a member of Infinitesimal
 -----------------------------------------------*)

Goal "ehr : Infinitesimal";
by (auto_tac (claset() addSIs [HInfinite_inverse_Infinitesimal,HInfinite_omega],
    simpset() addsimps [hypreal_epsilon_inverse_omega]));
qed "Infinitesimal_epsilon";
Addsimps [Infinitesimal_epsilon];

Goal "ehr : HFinite";
by (auto_tac (claset() addIs [Infinitesimal_subset_HFinite RS subsetD],
    simpset()));
qed "HFinite_epsilon";
Addsimps [HFinite_epsilon];

Goal "ehr @= #0";
by (simp_tac (simpset() addsimps [mem_infmal_iff RS sym]) 1);
qed "epsilon_inf_close_zero";
Addsimps [epsilon_inf_close_zero];

(*------------------------------------------------------------------------
  Needed for proof that we define a hyperreal [<X(n)] @= hypreal_of_real a given 
  that ALL n. |X n - a| < 1/n. Used in proof of NSLIM => LIM.
 -----------------------------------------------------------------------*)

Goal "0 < u  ==> \
\     (u < inverse (real_of_nat(Suc n))) = (real_of_nat(Suc n) < inverse u)";
by (asm_full_simp_tac (simpset() addsimps [real_inverse_eq_divide]) 1);
by (stac pos_real_less_divide_eq 1); 
by (assume_tac 1); 
by (stac pos_real_less_divide_eq 1); 
by (simp_tac (simpset() addsimps [real_mult_commute]) 2); 
by (simp_tac (simpset() addsimps [real_of_nat_Suc_gt_zero]) 1); 
qed "real_of_nat_less_inverse_iff";

Goal "#0 < u ==> finite {n. u < inverse(real_of_nat(Suc n))}";
by (asm_simp_tac (simpset() addsimps [real_of_nat_less_inverse_iff]) 1);
by (asm_simp_tac (simpset() addsimps [real_of_nat_Suc, 
                         real_less_diff_eq RS sym]) 1); 
by (rtac finite_real_of_nat_less_real 1);
qed "finite_inverse_real_of_posnat_gt_real";

Goal "{n. u <= inverse(real_of_nat(Suc n))} = \
\    {n. u < inverse(real_of_nat(Suc n))} Un {n. u = inverse(real_of_nat(Suc n))}";
by (auto_tac (claset() addDs [order_le_imp_less_or_eq],
              simpset() addsimps [order_less_imp_le]));
qed "lemma_real_le_Un_eq2";

Goal "(inverse (real_of_nat(Suc n)) <= r) = (#1 <= r * real_of_nat(Suc n))";
by (simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1); 
by (simp_tac (simpset() addsimps [real_inverse_eq_divide]) 1);
by (stac pos_real_less_divide_eq 1); 
by (simp_tac (simpset() addsimps [real_of_nat_Suc_gt_zero]) 1); 
by (simp_tac (simpset() addsimps [real_mult_commute]) 1); 
qed "real_of_nat_inverse_le_iff";

Goal "(u = inverse (real_of_nat(Suc n))) = (real_of_nat(Suc n) = inverse u)";
by (auto_tac (claset(),
      simpset() addsimps [real_inverse_inverse, real_of_nat_Suc_gt_zero, 
			  real_not_refl2 RS not_sym]));
qed "real_of_nat_inverse_eq_iff";

Goal "finite {n::nat. u = inverse(real_of_nat(Suc n))}";
by (asm_simp_tac (simpset() addsimps [real_of_nat_inverse_eq_iff]) 1);
by (cut_inst_tac [("x","inverse u - #1")] lemma_finite_omega_set 1);
by (asm_full_simp_tac (simpset() addsimps [real_of_nat_Suc, 
                         real_diff_eq_eq RS sym, eq_commute]) 1); 
qed "lemma_finite_omega_set2";

Goal "#0 < u ==> finite {n. u <= inverse(real_of_nat(Suc n))}";
by (auto_tac (claset(), 
      simpset() addsimps [lemma_real_le_Un_eq2,lemma_finite_omega_set2,
                          finite_inverse_real_of_posnat_gt_real]));
qed "finite_inverse_real_of_posnat_ge_real";

Goal "#0 < u ==> \
\      {n. u <= inverse(real_of_nat(Suc n))} ~: FreeUltrafilterNat";
by (blast_tac (claset() addSIs [FreeUltrafilterNat_finite,
                                finite_inverse_real_of_posnat_ge_real]) 1);
qed "inverse_real_of_posnat_ge_real_FreeUltrafilterNat";

(*--------------------------------------------------------------
    The complement of  {n. u <= inverse(real_of_nat(Suc n))} =
    {n. inverse(real_of_nat(Suc n)) < u} is in FreeUltrafilterNat 
    by property of (free) ultrafilters
 --------------------------------------------------------------*)
Goal "- {n. u <= inverse(real_of_nat(Suc n))} = \
\     {n. inverse(real_of_nat(Suc n)) < u}";
by (auto_tac (claset() addSDs [order_le_less_trans],
              simpset() addsimps [not_real_leE]));
val lemma = result();

Goal "#0 < u ==> \
\     {n. inverse(real_of_nat(Suc n)) < u} : FreeUltrafilterNat";
by (cut_inst_tac [("u","u")]  inverse_real_of_posnat_ge_real_FreeUltrafilterNat 1);
by (auto_tac (claset() addDs [FreeUltrafilterNat_Compl_mem],
    simpset() addsimps [lemma]));
qed "FreeUltrafilterNat_inverse_real_of_posnat";

(*--------------------------------------------------------------
      Example where we get a hyperreal from a real sequence
      for which a particular property holds. The theorem is
      used in proofs about equivalence of nonstandard and
      standard neighbourhoods. Also used for equivalence of
      nonstandard ans standard definitions of pointwise 
      limit (the theorem was previously in REALTOPOS.thy).
 -------------------------------------------------------------*)
(*-----------------------------------------------------
    |X(n) - x| < 1/n ==> [<X n>] - hypreal_of_real x|: Infinitesimal 
 -----------------------------------------------------*)
Goal "ALL n. abs(X n + -x) < inverse(real_of_nat(Suc n)) \ 
\    ==> Abs_hypreal(hyprel```{X}) + -hypreal_of_real x : Infinitesimal";
by (auto_tac (claset() addSIs [bexI] 
           addDs [rename_numerals FreeUltrafilterNat_inverse_real_of_posnat,
                  FreeUltrafilterNat_all,FreeUltrafilterNat_Int] 
           addIs [order_less_trans, FreeUltrafilterNat_subset],
      simpset() addsimps [hypreal_minus, 
                          hypreal_of_real_def,hypreal_add,
                      Infinitesimal_FreeUltrafilterNat_iff,hypreal_inverse]));
qed "real_seq_to_hypreal_Infinitesimal";

Goal "ALL n. abs(X n + -x) < inverse(real_of_nat(Suc n)) \ 
\     ==> Abs_hypreal(hyprel```{X}) @= hypreal_of_real x";
by (rtac (inf_close_minus_iff RS ssubst) 1);
by (rtac (mem_infmal_iff RS subst) 1);
by (etac real_seq_to_hypreal_Infinitesimal 1);
qed "real_seq_to_hypreal_inf_close";

Goal "ALL n. abs(x + -X n) < inverse(real_of_nat(Suc n)) \ 
\              ==> Abs_hypreal(hyprel```{X}) @= hypreal_of_real x";
by (asm_full_simp_tac (simpset() addsimps [abs_minus_add_cancel,
        real_seq_to_hypreal_inf_close]) 1);
qed "real_seq_to_hypreal_inf_close2";

Goal "ALL n. abs(X n + -Y n) < inverse(real_of_nat(Suc n)) \ 
\     ==> Abs_hypreal(hyprel```{X}) + \
\         -Abs_hypreal(hyprel```{Y}) : Infinitesimal";
by (auto_tac (claset() addSIs [bexI] 
                  addDs [rename_numerals 
                         FreeUltrafilterNat_inverse_real_of_posnat,
                         FreeUltrafilterNat_all,FreeUltrafilterNat_Int] 
        addIs [order_less_trans, FreeUltrafilterNat_subset],
     simpset() addsimps 
            [Infinitesimal_FreeUltrafilterNat_iff,hypreal_minus,hypreal_add, 
             hypreal_inverse]));
qed "real_seq_to_hypreal_Infinitesimal2";
