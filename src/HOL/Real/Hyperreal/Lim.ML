(*  Title       : Lim.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Theory of limits, continuity and 
                  differentiation of real=>real functions
*)


(*DELETE?????*)
fun ARITH_PROVE str = prove_goal thy str 
                      (fn prems => [cut_facts_tac prems 1,arith_tac 1]);



(***?REALARITH.ML?? also below??*)
Goal "(x + - a = (#0::real)) = (x=a)";
by (arith_tac 1);
qed "real_add_minus_iff";
Addsimps [real_add_minus_iff];

Goal "(-b = -a) = (b = (a::real))";
by (arith_tac 1);
qed "real_minus_eq_cancel";
Addsimps [real_minus_eq_cancel];


(*---------------------------------------------------------------
   Theory of limits, continuity and differentiation of 
   real=>real functions 
 ----------------------------------------------------------------*)

Goalw [LIM_def] "(%x. k) -- x --> k";
by Auto_tac;
qed "LIM_const";
Addsimps [LIM_const];

(***-----------------------------------------------------------***)
(***  Some Purely Standard Proofs - Can be used for comparison ***)
(***-----------------------------------------------------------***)
 
(*--------------- 
    LIM_add    
 ---------------*)
Goalw [LIM_def] 
     "[| f -- x --> l; g -- x --> m |] \
\     ==> (%x. f(x) + g(x)) -- x --> (l + m)";
by (Step_tac 1);
by (REPEAT(dres_inst_tac [("x","r/#2")] spec 1));
by (dtac (rename_numerals (real_zero_less_two RS real_inverse_gt_zero 
          RSN (2,real_mult_less_mono2))) 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (res_inst_tac [("R1.0","s"),("R2.0","sa")] 
    real_linear_less2 1);
by (res_inst_tac [("x","s")] exI 1);
by (res_inst_tac [("x","sa")] exI 2);
by (res_inst_tac [("x","sa")] exI 3);
by (Step_tac 1);
by (REPEAT(dres_inst_tac [("x","xa")] spec 1) 
    THEN step_tac (claset() addSEs [real_less_trans]) 1);
by (REPEAT(dres_inst_tac [("x","xa")] spec 2) 
    THEN step_tac (claset() addSEs [real_less_trans]) 2);
by (REPEAT(dres_inst_tac [("x","xa")] spec 3) 
    THEN step_tac (claset() addSEs [real_less_trans]) 3);
by (ALLGOALS(rtac (abs_sum_triangle_ineq RS real_le_less_trans)));
by (ALLGOALS(rtac (real_sum_of_halves RS subst)));
by (auto_tac (claset() addIs [real_add_less_mono],simpset()));
qed "LIM_add";

Goalw [LIM_def] "f -- a --> L ==> (%x. -f(x)) -- a --> -L";
by (full_simp_tac (simpset() addsimps [real_minus_add_distrib RS sym,
                                       abs_minus_cancel] 
                    delsimps [real_minus_add_distrib,real_minus_minus]) 1);
qed "LIM_minus";

(*----------------------------------------------
     LIM_add_minus
 ----------------------------------------------*)
Goal "[| f -- x --> l; g -- x --> m |] \
\     ==> (%x. f(x) + -g(x)) -- x --> (l + -m)";
by (blast_tac (claset() addDs [LIM_add,LIM_minus]) 1);
qed "LIM_add_minus";

(*----------------------------------------------
     LIM_zero
 ----------------------------------------------*)
Goal "f -- a --> l ==> (%x. f(x) + -l) -- a --> #0";
by (res_inst_tac [("z1","l")] (rename_numerals (real_add_minus RS subst)) 1);
by (rtac LIM_add_minus 1 THEN Auto_tac);
qed "LIM_zero";

(*--------------------------
   Limit not zero
 --------------------------*)
Goalw [LIM_def] "k ~= #0 ==> ~ ((%x. k) -- x --> #0)";
by (res_inst_tac [("R1.0","k"),("R2.0","#0")] real_linear_less2 1);
by (auto_tac (claset(),simpset() addsimps [abs_minus_eqI2,abs_eqI2]));
by (dtac (rename_numerals (real_minus_zero_less_iff RS iffD2)) 1);
by (res_inst_tac [("x","-k")] exI 1);
by (res_inst_tac [("x","k")] exI 2);
by Auto_tac;
by (ALLGOALS(dres_inst_tac [("y","s")] real_dense));
by (Step_tac 1);
by (ALLGOALS(res_inst_tac [("x","r + x")] exI));
by (auto_tac (claset(),simpset() addsimps [real_add_assoc,abs_eqI2]));
qed "LIM_not_zero";

(* [| k ~= #0; (%x. k) -- x --> #0 |] ==> R *)
bind_thm("LIM_not_zeroE", (LIM_not_zero RS notE));

Goal "(%x. k) -- x --> L ==> k = L";
by (rtac ccontr 1);
by (dtac LIM_zero 1);
by (rtac LIM_not_zeroE 1 THEN assume_tac 2);
by (arith_tac 1);
qed "LIM_const_eq";

(*------------------------
     Limit is Unique
 ------------------------*)
Goal "[| f -- x --> L; f -- x --> M |] ==> L = M";
by (dtac LIM_minus 1);
by (dtac LIM_add 1 THEN assume_tac 1);
by (auto_tac (claset() addSDs [LIM_const_eq RS sym],
    simpset()));
qed "LIM_unique";

(*-------------
    LIM_mult_zero
 -------------*)
Goalw [LIM_def] "[| f -- x --> #0; g -- x --> #0 |] \
\         ==> (%x. f(x)*g(x)) -- x --> #0";
by (Step_tac 1);
by (dres_inst_tac [("x","#1")] spec 1);
by (dres_inst_tac [("x","r")] spec 1);
by (cut_facts_tac [real_zero_less_one] 1);
by (asm_full_simp_tac (simpset() addsimps 
    [abs_mult]) 1);
by (Clarify_tac 1);
by (res_inst_tac [("R1.0","s"),("R2.0","sa")] 
    real_linear_less2 1);
by (res_inst_tac [("x","s")] exI 1);
by (res_inst_tac [("x","sa")] exI 2);
by (res_inst_tac [("x","sa")] exI 3);
by (Step_tac 1);
by (REPEAT(dres_inst_tac [("x","xa")] spec 1) 
    THEN step_tac (claset() addSEs [real_less_trans]) 1);
by (REPEAT(dres_inst_tac [("x","xa")] spec 2) 
    THEN step_tac (claset() addSEs [real_less_trans]) 2);
by (REPEAT(dres_inst_tac [("x","xa")] spec 3) 
    THEN step_tac (claset() addSEs [real_less_trans]) 3);
by (ALLGOALS(res_inst_tac [("t","r")] (real_mult_1 RS subst)));
by (ALLGOALS(rtac abs_mult_less2));
by Auto_tac;
qed "LIM_mult_zero";

Goalw [LIM_def] "(%x. x) -- a --> a";
by (Auto_tac);
qed "LIM_self";

(*--------------------------------------------------------------
   Limits are equal for functions equal except at limit point
 --------------------------------------------------------------*)
Goalw [LIM_def] 
      "[| ALL x. x ~= a --> (f x = g x) |] \
\           ==> (f -- a --> l) = (g -- a --> l)";
by (auto_tac (claset(), simpset() addsimps [real_add_minus_iff]));
qed "LIM_equal";

Goal "[| (%x. f(x) + -g(x)) -- a --> #0; \
\        g -- a --> l |] \
\      ==> f -- a --> l";
by (dtac LIM_add 1 THEN assume_tac 1);
by (auto_tac (claset(), simpset() addsimps [real_add_assoc]));
qed "LIM_trans";

(***-------------------------------------------------------------***)
(***           End of Purely Standard Proofs                     ***)
(***-------------------------------------------------------------***)
(*--------------------------------------------------------------
       Standard and NS definitions of Limit
 --------------------------------------------------------------*)
Goalw [LIM_def,NSLIM_def,inf_close_def] 
      "f -- x --> L ==> f -- x --NS> L";
by (asm_full_simp_tac
    (simpset() addsimps [Infinitesimal_FreeUltrafilterNat_iff]) 1);
by (Step_tac 1);
by (res_inst_tac [("z","xa")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
      simpset() addsimps [real_add_minus_iff,
                          starfun, hypreal_minus,hypreal_of_real_minus RS sym,
                          hypreal_of_real_def, hypreal_add]));
by (rtac bexI 1 THEN rtac lemma_hyprel_refl 2 THEN Step_tac 1);
by (dres_inst_tac [("x","u")] spec 1 THEN Clarify_tac 1);
by (dres_inst_tac [("x","s")] spec 1 THEN Clarify_tac 1);
by (subgoal_tac "ALL n::nat. (xa n) ~= x & \
\                    abs ((xa n) + - x) < s --> abs (f (xa n) + - L) < u" 1);
by (Blast_tac 2);
by (dtac FreeUltrafilterNat_all 1);
by (Ultra_tac 1);
qed "LIM_NSLIM";
 
(*---------------------------------------------------------------------
    Limit: NS definition ==> standard definition
 ---------------------------------------------------------------------*)

Goal "ALL s. #0 < s --> (EX xa.  xa ~= x & \
\        abs (xa + - x) < s  & r <= abs (f xa + -L)) \
\     ==> ALL n::nat. EX xa.  xa ~= x & \
\             abs(xa + -x) < inverse(real_of_posnat n) & r <= abs(f xa + -L)";
by (Step_tac 1);
by (cut_inst_tac [("n1","n")] (real_of_posnat_gt_zero RS real_inverse_gt_zero) 1);
by Auto_tac;
val lemma_LIM = result();

Goal "ALL s. #0 < s --> (EX xa.  xa ~= x & \
\        abs (xa + - x) < s  & r <= abs (f xa + -L)) \
\     ==> EX X. ALL n::nat. X n ~= x & \
\               abs(X n + -x) < inverse(real_of_posnat n) & r <= abs(f (X n) + -L)";
by (dtac lemma_LIM 1);
by (dtac choice 1);
by (Blast_tac 1);
val lemma_skolemize_LIM2 = result();

Goal "ALL n. X n ~= x & \
\         abs (X n + - x) < inverse (real_of_posnat  n) & \
\         r <= abs (f (X n) + - L) ==> \
\         ALL n. abs (X n + - x) < inverse (real_of_posnat  n)";
by (Auto_tac );
val lemma_simp = result();
 
(*-------------------
    NSLIM => LIM
 -------------------*)

Goalw [LIM_def,NSLIM_def,inf_close_def] 
      "f -- x --NS> L ==> f -- x --> L";
by (asm_full_simp_tac
    (simpset() addsimps [Infinitesimal_FreeUltrafilterNat_iff]) 1);
by (EVERY1[Step_tac, rtac ccontr, Asm_full_simp_tac]);
by (fold_tac [real_le_def]);
by (dtac lemma_skolemize_LIM2 1);
by (Step_tac 1);
by (dres_inst_tac [("x","Abs_hypreal(hyprel^^{X})")] spec 1);
by (asm_full_simp_tac
    (simpset() addsimps [starfun,
                         hypreal_minus,hypreal_of_real_minus RS sym,
                         hypreal_of_real_def,hypreal_add]) 1);
by (Step_tac 1);
by (dtac (lemma_simp RS real_seq_to_hypreal_Infinitesimal) 1);
by (asm_full_simp_tac
    (simpset() addsimps 
       [Infinitesimal_FreeUltrafilterNat_iff,hypreal_of_real_def,
        hypreal_minus,hypreal_of_real_minus,hypreal_add]) 1);
by (Blast_tac 1); 
by (rotate_tac 2 1);
by (dres_inst_tac [("x","r")] spec 1);
by (Clarify_tac 1);
by (dtac FreeUltrafilterNat_all 1);
by (Ultra_tac 1);
qed "NSLIM_LIM";


(**** Key result ****)
Goal "(f -- x --> L) = (f -- x --NS> L)";
by (blast_tac (claset() addIs [LIM_NSLIM,NSLIM_LIM]) 1);
qed "LIM_NSLIM_iff";

(*-------------------------------------------------------------------*)
(*   Proving properties of limits using nonstandard definition and   *)
(*   hence, the properties hold for standard limits as well          *)
(*-------------------------------------------------------------------*)
(*------------------------------------------------
      NSLIM_mult and hence (trivially) LIM_mult
 ------------------------------------------------*)

Goalw [NSLIM_def]
     "[| f -- x --NS> l; g -- x --NS> m |] \
\     ==> (%x. f(x) * g(x)) -- x --NS> (l * m)";
by (auto_tac (claset() addSIs [starfun_mult_HFinite_inf_close],
              simpset() addsimps [hypreal_of_real_mult]));
qed "NSLIM_mult";

Goal "[| f -- x --> l; g -- x --> m |] \
\     ==> (%x. f(x) * g(x)) -- x --> (l * m)";
by (asm_full_simp_tac (simpset() addsimps [LIM_NSLIM_iff,
    NSLIM_mult]) 1);
qed "LIM_mult2";

(*----------------------------------------------
      NSLIM_add and hence (trivially) LIM_add
      Note the much shorter proof
 ----------------------------------------------*)
Goalw [NSLIM_def]
     "[| f -- x --NS> l; g -- x --NS> m |] \
\     ==> (%x. f(x) + g(x)) -- x --NS> (l + m)";
by (auto_tac (claset() addSIs [starfun_add_inf_close],
              simpset() addsimps [hypreal_of_real_add]));
qed "NSLIM_add";

Goal "[| f -- x --> l; g -- x --> m |] \
\     ==> (%x. f(x) + g(x)) -- x --> (l + m)";
by (asm_full_simp_tac (simpset() addsimps [LIM_NSLIM_iff,
    NSLIM_add]) 1);
qed "LIM_add2";

(*----------------------------------------------
     NSLIM_const
 ----------------------------------------------*)
Goalw [NSLIM_def] "(%x. k) -- x --NS> k";
by (Auto_tac);
qed "NSLIM_const";

Addsimps [NSLIM_const];

Goal "(%x. k) -- x --> k";
by (asm_full_simp_tac (simpset() addsimps [LIM_NSLIM_iff]) 1);
qed "LIM_const2";

(*----------------------------------------------
     NSLIM_minus
 ----------------------------------------------*)
Goalw [NSLIM_def] 
      "f -- a --NS> L ==> (%x. -f(x)) -- a --NS> -L";
by (auto_tac (claset() addIs [inf_close_minus],
    simpset() addsimps [starfun_minus RS sym,
    hypreal_of_real_minus]));
qed "NSLIM_minus";

Goal "f -- a --> L ==> (%x. -f(x)) -- a --> -L";
by (asm_full_simp_tac (simpset() addsimps [LIM_NSLIM_iff,
    NSLIM_minus]) 1);
qed "LIM_minus2";

(*----------------------------------------------
     NSLIM_add_minus
 ----------------------------------------------*)
Goal "[| f -- x --NS> l; g -- x --NS> m |] \
\     ==> (%x. f(x) + -g(x)) -- x --NS> (l + -m)";
by (blast_tac (claset() addDs [NSLIM_add,NSLIM_minus]) 1);
qed "NSLIM_add_minus";

Goal "[| f -- x --> l; g -- x --> m |] \
\     ==> (%x. f(x) + -g(x)) -- x --> (l + -m)";
by (asm_full_simp_tac (simpset() addsimps [LIM_NSLIM_iff,
    NSLIM_add_minus]) 1);
qed "LIM_add_minus2";

(*-----------------------------
    NSLIM_inverse
 -----------------------------*)
Goalw [NSLIM_def] 
     "[| f -- a --NS> L;  L ~= #0 |] \
\     ==> (%x. inverse(f(x))) -- a --NS> (inverse L)";
by (Clarify_tac 1);
by (dtac spec 1);
by (auto_tac (claset(),
              simpset() addsimps [hypreal_of_real_not_zero_iff RS sym,
                                  hypreal_of_real_inverse RS sym]));
by (forward_tac [inf_close_hypreal_of_real_not_zero] 1 THEN assume_tac 1);
by (dtac hypreal_of_real_HFinite_diff_Infinitesimal 1);
by (stac (starfun_inverse RS sym) 1);
by (auto_tac (claset() addSEs [inf_close_inverse],
              simpset() addsimps [hypreal_of_real_zero_iff]));
qed "NSLIM_inverse";

Goal "[| f -- a --> L; \
\        L ~= #0 |] ==> (%x. inverse(f(x))) -- a --> (inverse L)";
by (asm_full_simp_tac (simpset() addsimps [LIM_NSLIM_iff,
    NSLIM_inverse]) 1);
qed "LIM_inverse";

(*------------------------------
    NSLIM_zero
 ------------------------------*)
Goal "f -- a --NS> l ==> (%x. f(x) + -l) -- a --NS> #0";
by (res_inst_tac [("z1","l")] (rename_numerals 
    (real_add_minus RS subst)) 1);
by (rtac NSLIM_add_minus 1 THEN Auto_tac);
qed "NSLIM_zero";

Goal "f -- a --> l ==> (%x. f(x) + -l) -- a --> #0";
by (asm_full_simp_tac (simpset() addsimps [LIM_NSLIM_iff,
    NSLIM_zero]) 1);
qed "LIM_zero2";

Goal "(%x. f(x) - l) -- x --NS> #0 ==> f -- x --NS> l";
by (dres_inst_tac [("g","%x. l"),("m","l")] NSLIM_add 1);
by (auto_tac (claset(),simpset() addsimps [real_diff_def,
    real_add_assoc]));
qed "NSLIM_zero_cancel";

Goal "(%x. f(x) - l) -- x --> #0 ==> f -- x --> l";
by (dres_inst_tac [("g","%x. l"),("m","l")] LIM_add 1);
by (auto_tac (claset(),simpset() addsimps [real_diff_def,
    real_add_assoc]));
qed "LIM_zero_cancel";

(*--------------------------
   NSLIM_not_zero
 --------------------------*)
Goalw [NSLIM_def] "k ~= #0 ==> ~ ((%x. k) -- x --NS> #0)";
by (Auto_tac);
by (res_inst_tac [("x","hypreal_of_real x + ehr")] exI 1);
by (auto_tac (claset() addIs [Infinitesimal_add_inf_close_self 
    RS inf_close_sym],simpset()));
by (dres_inst_tac [("x1","-hypreal_of_real x")] (hypreal_add_left_cancel RS iffD2) 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_add_assoc RS sym,
    hypreal_epsilon_not_zero]) 1);
qed "NSLIM_not_zero";

(* [| k ~= #0; (%x. k) -- x --NS> #0 |] ==> R *)
bind_thm("NSLIM_not_zeroE", (NSLIM_not_zero RS notE));

Goal "k ~= #0 ==> ~ ((%x. k) -- x --> #0)";
by (asm_full_simp_tac (simpset() addsimps [LIM_NSLIM_iff,
    NSLIM_not_zero]) 1);
qed "LIM_not_zero2";

(*-------------------------------------
   NSLIM of constant function
 -------------------------------------*)
Goal "(%x. k) -- x --NS> L ==> k = L";
by (rtac ccontr 1);
by (dtac NSLIM_zero 1);
by (rtac NSLIM_not_zeroE 1 THEN assume_tac 2);
by (arith_tac 1);
qed "NSLIM_const_eq";

Goal "(%x. k) -- x --> L ==> k = L";
by (asm_full_simp_tac (simpset() addsimps [LIM_NSLIM_iff,
    NSLIM_const_eq]) 1);
qed "LIM_const_eq2";

(*------------------------
     NS Limit is Unique
 ------------------------*)
(* can actually be proved more easily by unfolding def! *)
Goal "[| f -- x --NS> L; f -- x --NS> M |] ==> L = M";
by (dtac NSLIM_minus 1);
by (dtac NSLIM_add 1 THEN assume_tac 1);
by (auto_tac (claset() addSDs [NSLIM_const_eq RS sym],
    simpset() addsimps [real_add_minus]));
qed "NSLIM_unique";

Goal "[| f -- x --> L; f -- x --> M |] ==> L = M";
by (asm_full_simp_tac (simpset() addsimps [LIM_NSLIM_iff,
    NSLIM_unique]) 1);
qed "LIM_unique2";

(*--------------------
    NSLIM_mult_zero
 --------------------*)
Goal "[| f -- x --NS> #0; g -- x --NS> #0 |] \
\         ==> (%x. f(x)*g(x)) -- x --NS> #0";
by (dtac NSLIM_mult 1 THEN Auto_tac);
qed "NSLIM_mult_zero";

(* we can use the corresponding thm LIM_mult2 *)
(* for standard definition of limit           *)

Goal "[| f -- x --> #0; g -- x --> #0 |] \
\     ==> (%x. f(x)*g(x)) -- x --> #0";
by (dtac LIM_mult2 1 THEN Auto_tac);
qed "LIM_mult_zero2";

(*----------------------------
    NSLIM_self
 ----------------------------*)
Goalw [NSLIM_def] "(%x. x) -- a --NS> a";
by (auto_tac (claset() addIs [starfun_Idfun_inf_close],simpset()));
qed "NSLIM_self";

Goal "(%x. x) -- a --> a";
by (simp_tac (simpset() addsimps [LIM_NSLIM_iff,NSLIM_self]) 1);
qed "LIM_self2";

(*-----------------------------------------------------------------------------
   Derivatives and Continuity - NS and Standard properties
 -----------------------------------------------------------------------------*)
(*---------------
    Continuity 
 ---------------*)

Goalw [isNSCont_def] 
      "[| isNSCont f a; y @= hypreal_of_real a |] \
\           ==> (*f* f) y @= hypreal_of_real (f a)";
by (Blast_tac 1);
qed "isNSContD";

Goalw [isNSCont_def,NSLIM_def] 
      "isNSCont f a ==> f -- a --NS> (f a) ";
by (Blast_tac 1);
qed "isNSCont_NSLIM";

Goalw [isNSCont_def,NSLIM_def] 
      "f -- a --NS> (f a) ==> isNSCont f a";
by (Auto_tac);
by (res_inst_tac [("Q","y = hypreal_of_real a")] 
    (excluded_middle RS disjE) 1);
by (Auto_tac);
qed "NSLIM_isNSCont";

(*-----------------------------------------------------
    NS continuity can be defined using NS Limit in
    similar fashion to standard def of continuity
 -----------------------------------------------------*)
Goal "(isNSCont f a) = (f -- a --NS> (f a))";
by (blast_tac (claset() addIs [isNSCont_NSLIM,NSLIM_isNSCont]) 1);
qed "isNSCont_NSLIM_iff";

(*----------------------------------------------
  Hence, NS continuity can be given
  in terms of standard limit
 ---------------------------------------------*)
Goal "(isNSCont f a) = (f -- a --> (f a))";
by (asm_full_simp_tac (simpset() addsimps 
    [LIM_NSLIM_iff,isNSCont_NSLIM_iff]) 1);
qed "isNSCont_LIM_iff";

(*-----------------------------------------------
  Moreover, it's trivial now that NS continuity 
  is equivalent to standard continuity
 -----------------------------------------------*)
Goalw [isCont_def] "(isNSCont f a) = (isCont f a)";
by (rtac isNSCont_LIM_iff 1);
qed "isNSCont_isCont_iff";

(*----------------------------------------
  Standard continuity ==> NS continuity 
 ----------------------------------------*)
Goal "isCont f a ==> isNSCont f a";
by (etac (isNSCont_isCont_iff RS iffD2) 1);
qed "isCont_isNSCont";

(*----------------------------------------
  NS continuity ==> Standard continuity 
 ----------------------------------------*)
Goal "isNSCont f a ==> isCont f a";
by (etac (isNSCont_isCont_iff RS iffD1) 1);
qed "isNSCont_isCont";

(*--------------------------------------------------------------------------
                 Alternative definition of continuity
 --------------------------------------------------------------------------*)
(* Prove equivalence between NS limits - *)
(* seems easier than using standard def  *)
Goalw [NSLIM_def] 
      "(f -- a --NS> L) = ((%h. f(a + h)) -- #0 --NS> L)";
by (auto_tac (claset(),simpset() addsimps [hypreal_of_real_zero]));
by (dres_inst_tac [("x","hypreal_of_real a + x")] spec 1);
by (dres_inst_tac [("x","-hypreal_of_real a + x")] spec 2);
by (Step_tac 1);
by (dtac (sym RS (hypreal_eq_minus_iff4 RS iffD1)) 1);
by (rtac ((mem_infmal_iff RS iffD2) RS 
    (Infinitesimal_add_inf_close_self RS inf_close_sym)) 2);
by (rtac (inf_close_minus_iff2 RS iffD1) 5);
by (asm_full_simp_tac (simpset() addsimps [hypreal_add_commute]) 4);
by (dtac (sym RS (hypreal_eq_minus_iff RS iffD2)) 4);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 3);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 6);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_of_real_def,hypreal_minus,hypreal_add,
    real_add_assoc,inf_close_refl,hypreal_zero_def]));
qed "NSLIM_h_iff";

Goal "(f -- a --NS> f a) = ((%h. f(a + h)) -- #0 --NS> f a)";
by (rtac NSLIM_h_iff 1);
qed "NSLIM_isCont_iff";

Goal "(f -- a --> f a) = ((%h. f(a + h)) -- #0 --> f(a))";
by (asm_full_simp_tac (simpset() addsimps [LIM_NSLIM_iff,
    NSLIM_isCont_iff]) 1);
qed "LIM_isCont_iff";

Goalw [isCont_def] 
      "(isCont f x) = ((%h. f(x + h)) -- #0 --> f(x))";
by (simp_tac (simpset() addsimps [LIM_isCont_iff]) 1);
qed "isCont_iff";

(*--------------------------------------------------------------------------
   Immediate application of nonstandard criterion for continuity can offer 
   very simple proofs of some standard property of continuous functions
 --------------------------------------------------------------------------*)
(*------------------------
     sum continuous
 ------------------------*)
Goal "[| isCont f a; isCont g a |] ==> isCont (%x. f(x) + g(x)) a";
by (auto_tac (claset() addIs [starfun_add_inf_close],simpset() addsimps 
              [isNSCont_isCont_iff RS sym,isNSCont_def,hypreal_of_real_add]));
qed "isCont_add";

(*------------------------
     mult continuous
 ------------------------*)
Goal "[| isCont f a; isCont g a |] ==> isCont (%x. f(x) * g(x)) a";
by (auto_tac (claset() addSIs [starfun_mult_HFinite_inf_close],simpset() addsimps 
              [isNSCont_isCont_iff RS sym,isNSCont_def,hypreal_of_real_mult]));
qed "isCont_mult";

(*-------------------------------------------
     composition of continuous functions
     Note very short straightforard proof!
 ------------------------------------------*)
Goal "[| isCont f a; isCont g (f a) |] \
\     ==> isCont (g o f) a";
by (auto_tac (claset(),simpset() addsimps [isNSCont_isCont_iff RS sym,
              isNSCont_def,starfun_o RS sym]));
qed "isCont_o";

Goal "[| isCont f a; isCont g (f a) |] \
\     ==> isCont (%x. g (f x)) a";
by (auto_tac (claset() addDs [isCont_o],simpset() addsimps [o_def]));
qed "isCont_o2";

Goalw [isNSCont_def] "isNSCont f a ==> isNSCont (%x. - f x) a";
by (auto_tac (claset(),simpset() addsimps [starfun_minus RS sym, 
    hypreal_of_real_minus])); 
qed "isNSCont_minus";

Goal "isCont f a ==> isCont (%x. - f x) a";
by (auto_tac (claset(),simpset() addsimps [isNSCont_isCont_iff RS sym,
              isNSCont_minus]));
qed "isCont_minus";

Goalw [isCont_def]  
      "[| isCont f x; f x ~= #0 |] ==> isCont (%x. inverse (f x)) x";
by (blast_tac (claset() addIs [LIM_inverse]) 1);
qed "isCont_inverse";

Goal "[| isNSCont f x; f x ~= #0 |] ==> isNSCont (%x. inverse (f x)) x";
by (auto_tac (claset() addIs [isCont_inverse],simpset() addsimps 
    [isNSCont_isCont_iff]));
qed "isNSCont_inverse";

Goalw [real_diff_def] 
      "[| isCont f a; isCont g a |] ==> isCont (%x. f(x) - g(x)) a";
by (auto_tac (claset() addIs [isCont_add,isCont_minus],simpset()));
qed "isCont_diff";

Goalw [isCont_def]  "isCont (%x. k) a";
by (Simp_tac 1);
qed "isCont_const";
Addsimps [isCont_const];

Goalw [isNSCont_def]  "isNSCont (%x. k) a";
by (Simp_tac 1);
qed "isNSCont_const";
Addsimps [isNSCont_const];

Goalw [isNSCont_def]  "isNSCont abs a";
by (auto_tac (claset() addIs [inf_close_hrabs],simpset() addsimps 
    [hypreal_of_real_hrabs RS sym,starfun_rabs_hrabs]));
qed "isNSCont_rabs";
Addsimps [isNSCont_rabs];

Goal "isCont abs a";
by (auto_tac (claset(),simpset() addsimps [isNSCont_isCont_iff RS sym]));
qed "isCont_rabs";
Addsimps [isCont_rabs];

(****************************************************************
(%* Leave as commented until I add topology theory or remove? *%)
(%*------------------------------------------------------------
  Elementary topology proof for a characterisation of 
  continuity now: a function f is continuous if and only 
  if the inverse image, {x. f(x) : A}, of any open set A 
  is always an open set
 ------------------------------------------------------------*%)
Goal "[| isNSopen A; ALL x. isNSCont f x |] \
\              ==> isNSopen {x. f x : A}";
by (auto_tac (claset(),simpset() addsimps [isNSopen_iff1]));
by (dtac (mem_monad_inf_close RS inf_close_sym) 1);
by (dres_inst_tac [("x","a")] spec 1);
by (dtac isNSContD 1 THEN assume_tac 1);
by (dtac bspec 1 THEN assume_tac 1);
by (dres_inst_tac [("x","( *f* f) x")] inf_close_mem_monad2 1);
by (blast_tac (claset() addIs [starfun_mem_starset]) 1);
qed "isNSCont_isNSopen";

Goalw [isNSCont_def]
          "ALL A. isNSopen A --> isNSopen {x. f x : A} \
\              ==> isNSCont f x";
by (auto_tac (claset() addSIs [(mem_infmal_iff RS iffD1) RS 
     (inf_close_minus_iff RS iffD2)],simpset() addsimps 
      [Infinitesimal_def,SReal_iff]));
by (dres_inst_tac [("x","{z. abs(z + -f(x)) < ya}")] spec 1);
by (etac (isNSopen_open_interval RSN (2,impE)) 1);
by (auto_tac (claset(),simpset() addsimps [isNSopen_def,isNSnbhd_def]));
by (dres_inst_tac [("x","x")] spec 1);
by (auto_tac (claset() addDs [inf_close_sym RS inf_close_mem_monad],
    simpset() addsimps [hypreal_of_real_zero RS sym,STAR_starfun_rabs_add_minus]));
qed "isNSopen_isNSCont";

Goal "(ALL x. isNSCont f x) = \
\     (ALL A. isNSopen A --> isNSopen {x. f(x) : A})";
by (blast_tac (claset() addIs [isNSCont_isNSopen,
    isNSopen_isNSCont]) 1);
qed "isNSCont_isNSopen_iff";

(%*------- Standard version of same theorem --------*%)
Goal "(ALL x. isCont f x) = \
\         (ALL A. isopen A --> isopen {x. f(x) : A})";
by (auto_tac (claset() addSIs [isNSCont_isNSopen_iff],
              simpset() addsimps [isNSopen_isopen_iff RS sym,
              isNSCont_isCont_iff RS sym]));
qed "isCont_isopen_iff";
*******************************************************************)

(*-----------------------------------------------------------------
                        Uniform continuity
 ------------------------------------------------------------------*)
Goalw [isNSUCont_def] 
      "[| isNSUCont f; x @= y|] ==> (*f* f) x @= (*f* f) y";
by (Blast_tac 1);
qed "isNSUContD";

Goalw [isUCont_def,isCont_def,LIM_def]
     "isUCont f ==> EX x. isCont f x";
by (Force_tac 1);
qed "isUCont_isCont";

Goalw [isNSUCont_def,isUCont_def,inf_close_def] 
     "isUCont f ==> isNSUCont f";
by (asm_full_simp_tac (simpset() addsimps 
    [Infinitesimal_FreeUltrafilterNat_iff]) 1);
by (Step_tac 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_minus, hypreal_add]));
by (rtac bexI 1 THEN rtac lemma_hyprel_refl 2 THEN Step_tac 1);
by (dres_inst_tac [("x","u")] spec 1 THEN Clarify_tac 1);
by (dres_inst_tac [("x","s")] spec 1 THEN Clarify_tac 1);
by (subgoal_tac "ALL n::nat. abs ((xa n) + - (xb n)) < s --> abs (f (xa n) + - f (xb n)) < u" 1);
by (Blast_tac 2);
by (thin_tac "ALL x y. abs (x + - y) < s --> abs (f x + - f y) < u" 1);
by (dtac FreeUltrafilterNat_all 1);
by (Ultra_tac 1);
qed "isUCont_isNSUCont";

Goal "ALL s. #0 < s --> \
\              (EX xa y. abs (xa + - y) < s  & \
\              r <= abs (f xa + -f y)) ==> \
\              ALL n::nat. EX xa y.  \
\              abs(xa + -y) < inverse(real_of_posnat n) & \
\              r <= abs(f xa + -f y)";
by (Step_tac 1);
by (cut_inst_tac [("n1","n")] (real_of_posnat_gt_zero RS real_inverse_gt_zero) 1);
by Auto_tac;
val lemma_LIMu = result();

Goal "ALL s. #0 < s --> \
\              (EX xa y. abs (xa + - y) < s  & \
\              r <= abs (f xa + -f y)) ==> \
\              EX X Y. ALL n::nat. \
\              abs(X n + -(Y n)) < inverse(real_of_posnat n) & \
\              r <= abs(f (X n) + -f (Y n))";
by (dtac lemma_LIMu 1);
by (dtac choice 1);
by (Step_tac 1);
by (dtac choice 1);
by (Blast_tac 1);
val lemma_skolemize_LIM2u = result();

Goal "ALL n. abs (X n + -Y n) < inverse (real_of_posnat  n) & \
\         r <= abs (f (X n) + - f(Y n)) ==> \
\         ALL n. abs (X n + - Y n) < inverse (real_of_posnat  n)";
by (Auto_tac );
val lemma_simpu = result();

Goal "{n. f (X n) + - f(Y n) = Ya n} Int \
\         {n. abs (X n + - Y n) < inverse (real_of_posnat  n) & \
\             r <= abs (f (X n) + - f(Y n))} <= \
\         {n. r <= abs (Ya n)}";
by (Auto_tac);
val lemma_Intu = result ();

Goalw [isNSUCont_def,isUCont_def,inf_close_def] 
     "isNSUCont f ==> isUCont f";
by (asm_full_simp_tac (simpset() addsimps 
    [Infinitesimal_FreeUltrafilterNat_iff]) 1);
by (EVERY1[Step_tac, rtac ccontr, Asm_full_simp_tac]);
by (fold_tac [real_le_def]);
by (dtac lemma_skolemize_LIM2u 1);
by (Step_tac 1);
by (dres_inst_tac [("x","Abs_hypreal(hyprel^^{X})")] spec 1);
by (dres_inst_tac [("x","Abs_hypreal(hyprel^^{Y})")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [starfun,
    hypreal_minus,hypreal_add]) 1);
by (Auto_tac);
by (dtac (lemma_simpu RS real_seq_to_hypreal_Infinitesimal2) 1);
by (asm_full_simp_tac (simpset() addsimps 
    [Infinitesimal_FreeUltrafilterNat_iff,
     hypreal_minus,hypreal_add]) 1);
by (Blast_tac 1);
by (rotate_tac 2 1);
by (dres_inst_tac [("x","r")] spec 1);
by (Clarify_tac 1);
by (dtac FreeUltrafilterNat_all 1);
by (Ultra_tac 1);
qed "isNSUCont_isUCont";

(*------------------------------------------------------------------
                         Derivatives
 ------------------------------------------------------------------*)
Goalw [deriv_def] 
      "(DERIV f x :> D) = ((%h. (f(x + h) + - f(x))/h) -- #0 --> D)";
by (Blast_tac 1);        
qed "DERIV_iff";

Goalw [deriv_def] 
      "(DERIV f x :> D) = ((%h. (f(x + h) + - f(x))/h) -- #0 --NS> D)";
by (simp_tac (simpset() addsimps [LIM_NSLIM_iff]) 1);
qed "DERIV_NS_iff";

Goalw [deriv_def] 
      "DERIV f x :> D \
\      ==> (%h. (f(x + h) + - f(x))/h) -- #0 --> D";
by (Blast_tac 1);        
qed "DERIVD";

Goalw [deriv_def] "DERIV f x :> D ==> \
\          (%h. (f(x + h) + - f(x))/h) -- #0 --NS> D";
by (asm_full_simp_tac (simpset() addsimps [LIM_NSLIM_iff]) 1);
qed "NS_DERIVD";

(* Uniqueness *)
Goalw [deriv_def] 
      "[| DERIV f x :> D; DERIV f x :> E |] ==> D = E";
by (blast_tac (claset() addIs [LIM_unique]) 1);
qed "DERIV_unique";

Goalw [nsderiv_def] 
     "[| NSDERIV f x :> D; NSDERIV f x :> E |] ==> D = E";
by (cut_facts_tac [Infinitesimal_epsilon,
             hypreal_epsilon_not_zero] 1);
by (auto_tac (claset() addSDs [bspec] addSIs 
   [inj_hypreal_of_real RS injD] addDs [inf_close_trans3],simpset()));
qed "NSDeriv_unique";

(*------------------------------------------------------------------------
                          Differentiable
 ------------------------------------------------------------------------*)

Goalw [differentiable_def] 
      "f differentiable x ==> EX D. DERIV f x :> D";
by (assume_tac 1);
qed "differentiableD";

Goalw [differentiable_def] 
      "DERIV f x :> D ==> f differentiable x";
by (Blast_tac 1);
qed "differentiableI";

Goalw [NSdifferentiable_def] 
      "f NSdifferentiable x ==> EX D. NSDERIV f x :> D";
by (assume_tac 1);
qed "NSdifferentiableD";

Goalw [NSdifferentiable_def] 
      "NSDERIV f x :> D ==> f NSdifferentiable x";
by (Blast_tac 1);
qed "NSdifferentiableI";

(*--------------------------------------------------------
      Alternative definition for differentiability
 -------------------------------------------------------*)

Goalw [LIM_def] 
 "((%h. (f(a + h) + - f(a))/h) -- #0 --> D) = \
\ ((%x. (f(x) + -f(a)) / (x + -a)) -- a --> D)";
by (Step_tac 1);
by (ALLGOALS(dtac spec));
by (Step_tac 1);
by (Blast_tac 1 THEN Blast_tac 2);
by (ALLGOALS(res_inst_tac [("x","s")] exI));
by (Step_tac 1);
by (dres_inst_tac [("x","x + -a")] spec 1);
by (dres_inst_tac [("x","x + a")] spec 2);
by (auto_tac (claset(), simpset() addsimps real_add_ac));
qed "DERIV_LIM_iff";

Goalw [deriv_def] "(DERIV f x :> D) = \
\         ((%z. (f(z) + -f(x)) / (z + -x)) -- x --> D)";
by (simp_tac (simpset() addsimps [DERIV_LIM_iff]) 1);
qed "DERIV_iff2";

(*--------------------------------------------------------
  Equivalence of NS and standard defs of differentiation
 -------------------------------------------------------*)
(*-------------------------------------------
   First NSDERIV in terms of NSLIM 
 -------------------------------------------*)

(*--- first equivalence ---*)
Goalw [nsderiv_def,NSLIM_def] 
      "(NSDERIV f x :> D) = ((%h. (f(x + h) + - f(x))/h) -- #0 --NS> D)";
by (auto_tac (claset(), simpset() addsimps [hypreal_of_real_zero]));
by (dres_inst_tac [("x","xa")] bspec 1);
by (rtac ccontr 3);
by (dres_inst_tac [("x","h")] spec 3);
by (auto_tac (claset(),
              simpset() addsimps [mem_infmal_iff,
            starfun_divide RS sym, starfun_add RS sym,
            hypreal_of_real_minus, starfun_lambda_cancel]));
qed "NSDERIV_NSLIM_iff";

(*--- second equivalence ---*)
Goal "(NSDERIV f x :> D) = \
\         ((%z. (f(z) + -f(x)) / (z + -x)) -- x --NS> D)";
by (full_simp_tac (simpset() addsimps 
     [NSDERIV_NSLIM_iff, DERIV_LIM_iff, LIM_NSLIM_iff RS sym]) 1);
qed "NSDERIV_NSLIM_iff2";

(* while we're at it! *)
Goalw [real_diff_def]
     "(NSDERIV f x :> D) = \
\     (ALL xa. \
\       xa ~= hypreal_of_real x & xa @= hypreal_of_real x --> \
\       (*f* (%z. (f z - f x) / (z - x))) xa @= hypreal_of_real D)";
by (auto_tac (claset(), simpset() addsimps [NSDERIV_NSLIM_iff2, NSLIM_def]));
qed "NSDERIV_iff2";

Addsimps [inf_close_refl];


(*FIXME: replace by simprocs for cancellation of common factors*)
Goal "h ~= (0::hypreal) ==> x*h/h = x";
by (asm_simp_tac 
    (simpset() addsimps [hypreal_divide_def, hypreal_mult_inverse_left, 
                         hypreal_mult_assoc]) 1);
qed "hypreal_divide_mult_self_eq"; 
Addsimps [hypreal_divide_mult_self_eq];

(*FIXME: replace by simprocs for cancellation of common factors*)
Goal "h ~= (0::hypreal) ==> (h*x)/h = x";
by (asm_simp_tac 
    (simpset() addsimps [inst "z" "h" hypreal_mult_commute]) 1);
qed "hypreal_times_divide_self_eq"; 
Addsimps [hypreal_times_divide_self_eq];

(*FIXME: replace by simprocs for cancellation of common factors*)
Goal "h ~= (0::hypreal) ==> h/h = 1hr";
by (asm_simp_tac 
    (simpset() addsimps [hypreal_divide_def, hypreal_mult_inverse_left]) 1);
qed "hypreal_divide_self_eq"; 
Addsimps [hypreal_divide_self_eq];


Goal "(NSDERIV f x :> D) ==> \
\    (ALL xa. \
\       xa @= hypreal_of_real x --> \
\       (*f* (%z. f z - f x)) xa @= hypreal_of_real D * (xa - hypreal_of_real x))";
by (auto_tac (claset(), simpset() addsimps [NSDERIV_iff2]));
by (case_tac "xa = hypreal_of_real x" 1);
by (auto_tac (claset(), 
              simpset() addsimps [hypreal_diff_def, hypreal_of_real_zero]));
by (dres_inst_tac [("x","xa")] spec 1);
by Auto_tac;
by (dres_inst_tac [("c","xa - hypreal_of_real x"),("b","hypreal_of_real D")]
     inf_close_mult1 1);
by (ALLGOALS(dtac (hypreal_not_eq_minus_iff RS iffD1)));
by (subgoal_tac "(*f* (%z. z - x)) xa ~= (0::hypreal)" 2);
by (rotate_tac ~1 2);
by (auto_tac (claset(),
    simpset() addsimps [starfun_divide RS sym, 
			starfun_add RS sym, real_diff_def, 
			hypreal_of_real_minus, hypreal_diff_def, 
		(inf_close_minus_iff RS iffD1) RS (mem_infmal_iff RS iffD2),  
			Infinitesimal_subset_HFinite RS subsetD]));
qed "NSDERIVD5";

Goal "(NSDERIV f x :> D) ==> \
\     (ALL h: Infinitesimal. \
\              ((*f* f)(hypreal_of_real x + h) - \
\                hypreal_of_real (f x))@= (hypreal_of_real D) * h)";
by (auto_tac (claset(),simpset() addsimps [nsderiv_def]));
by (case_tac "h = (0::hypreal)" 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_diff_def]));
by (dres_inst_tac [("x","h")] bspec 1);
by (dres_inst_tac [("c","h")] inf_close_mult1 2);
by (auto_tac (claset() addIs [Infinitesimal_subset_HFinite RS subsetD],
              simpset() addsimps [hypreal_diff_def]));
qed "NSDERIVD4";

Goal "(NSDERIV f x :> D) ==> \
\     (ALL h: Infinitesimal - {0}. \
\              ((*f* f)(hypreal_of_real x + h) - \
\                hypreal_of_real (f x))@= (hypreal_of_real D) * h)";
by (auto_tac (claset(),simpset() addsimps [nsderiv_def]));
by (rtac ccontr 1 THEN dres_inst_tac [("x","h")] bspec 1);
by (dres_inst_tac [("c","h")] inf_close_mult1 2);
by (auto_tac (claset() addIs [Infinitesimal_subset_HFinite RS subsetD],
              simpset() addsimps [hypreal_mult_assoc, hypreal_diff_def]));
qed "NSDERIVD3";

(*--------------------------------------------------------------
          Now equivalence between NSDERIV and DERIV
 -------------------------------------------------------------*)
Goalw [deriv_def] "(NSDERIV f x :> D) = (DERIV f x :> D)";
by (simp_tac (simpset() addsimps [NSDERIV_NSLIM_iff,LIM_NSLIM_iff]) 1);
qed "NSDERIV_DERIV_iff";

(*---------------------------------------------------
         Differentiability implies continuity 
         nice and simple "algebraic" proof
 --------------------------------------------------*)
Goalw [nsderiv_def]
      "NSDERIV f x :> D ==> isNSCont f x";
by (auto_tac (claset(),simpset() addsimps 
        [isNSCont_NSLIM_iff,NSLIM_def]));
by (dtac (inf_close_minus_iff RS iffD1) 1);
by (dtac (hypreal_not_eq_minus_iff RS iffD1) 1);
by (dres_inst_tac [("x","-hypreal_of_real x + xa")] bspec 1);
by (asm_full_simp_tac (simpset() addsimps 
    [hypreal_add_assoc RS sym]) 2);
by (auto_tac (claset(),simpset() addsimps 
    [mem_infmal_iff RS sym,hypreal_add_commute]));
by (dres_inst_tac [("c","xa + -hypreal_of_real x")] inf_close_mult1 1);
by (auto_tac (claset() addIs [Infinitesimal_subset_HFinite
    RS subsetD],simpset() addsimps [hypreal_mult_assoc]));
by (dres_inst_tac [("x3","D")] (HFinite_hypreal_of_real RSN
    (2,Infinitesimal_HFinite_mult) RS (mem_infmal_iff RS iffD1)) 1);
by (blast_tac (claset() addIs [inf_close_trans,
    hypreal_mult_commute RS subst,
    (inf_close_minus_iff RS iffD2)]) 1);
qed "NSDERIV_isNSCont";

(* Now Sandard proof *)
Goal "DERIV f x :> D ==> isCont f x";
by (asm_full_simp_tac (simpset() addsimps 
    [NSDERIV_DERIV_iff RS sym, isNSCont_isCont_iff RS sym,
     NSDERIV_isNSCont]) 1);
qed "DERIV_isCont";

(*----------------------------------------------------------------------------
      Differentiation rules for combinations of functions
      follow from clear, straightforard, algebraic 
      manipulations
 ----------------------------------------------------------------------------*)
(*-------------------------
    Constant function
 ------------------------*)

(* use simple constant nslimit theorem *)
Goal "(NSDERIV (%x. k) x :> #0)";
by (simp_tac (simpset() addsimps 
    [NSDERIV_NSLIM_iff,real_add_minus]) 1);
qed "NSDERIV_const";
Addsimps [NSDERIV_const];

Goal "(DERIV (%x. k) x :> #0)";
by (simp_tac (simpset() addsimps [NSDERIV_DERIV_iff RS sym]) 1);
qed "DERIV_const";
Addsimps [DERIV_const];

(*-----------------------------------------------------
    Sum of functions- proved easily
 ----------------------------------------------------*)


Goal "[| NSDERIV f x :> Da;  NSDERIV g x :> Db |] \
\     ==> NSDERIV (%x. f x + g x) x :> Da + Db";
by (asm_full_simp_tac (simpset() addsimps [NSDERIV_NSLIM_iff,
           NSLIM_def]) 1 THEN REPEAT(Step_tac 1));
by (auto_tac (claset(),
       simpset() addsimps [starfun_divide RS sym, starfun_add RS sym,
    hypreal_of_real_minus, hypreal_of_real_add, hypreal_of_real_divide,
    hypreal_add_divide_distrib]));
by (thin_tac "xa @= hypreal_of_real #0" 1 THEN dtac inf_close_add 1);
by (auto_tac (claset(),simpset() addsimps hypreal_add_ac));
qed "NSDERIV_add";

(* Standard theorem *)
Goal "[| DERIV f x :> Da; DERIV g x :> Db |] \
\     ==> DERIV (%x. f x + g x) x :> Da + Db";
by (asm_full_simp_tac (simpset() addsimps [NSDERIV_add,
    NSDERIV_DERIV_iff RS sym]) 1);
qed "DERIV_add";

(*-----------------------------------------------------
  Product of functions - Proof is trivial but tedious
  and long due to rearrangement of terms  
 ----------------------------------------------------*)
(* lemma - terms manipulation tedious as usual*)

Goal "((a::real)*b) + -(c*d) = (b*(a + -c)) + \
\                           (c*(b + -d))";
by (full_simp_tac (simpset() addsimps [real_add_mult_distrib2,
    real_minus_mult_eq2 RS sym,real_mult_commute]) 1);
val lemma_nsderiv1 = result();

Goal "[| (x + y) / z = hypreal_of_real D + yb; z ~= 0; \
\        z : Infinitesimal; yb : Infinitesimal |] \
\     ==> x + y @= 0";
by (forw_inst_tac [("c1","z")] (hypreal_mult_right_cancel RS iffD2) 1 
    THEN assume_tac 1);
by (thin_tac "(x + y) / z = hypreal_of_real  D + yb" 1);
by (auto_tac (claset() addSIs [Infinitesimal_HFinite_mult2, HFinite_add],
              simpset() addsimps [hypreal_mult_assoc, mem_infmal_iff RS sym]));
by (etac (Infinitesimal_subset_HFinite RS subsetD) 1);
val lemma_nsderiv2 = result();

Goal "[| NSDERIV f x :> Da; NSDERIV g x :> Db |] \
\     ==> NSDERIV (%x. f x * g x) x :> (Da * g(x)) + (Db * f(x))";
by (asm_full_simp_tac (simpset() addsimps [NSDERIV_NSLIM_iff, NSLIM_def]) 1 
    THEN REPEAT(Step_tac 1));
by (auto_tac (claset(),
       simpset() addsimps [starfun_divide RS sym, starfun_mult RS sym,
              starfun_add RS sym,starfun_lambda_cancel,hypreal_of_real_zero,
              lemma_nsderiv1]));
by (simp_tac (simpset() addsimps [hypreal_add_divide_distrib]) 1);
by (REPEAT(dtac (bex_Infinitesimal_iff2 RS iffD2) 1));
by (auto_tac (claset(),
        simpset() delsimps [hypreal_times_divide1_eq]
		  addsimps [hypreal_times_divide1_eq RS sym, 
                            hypreal_of_real_minus]));
by (dres_inst_tac [("D","Db")] lemma_nsderiv2 1);
by (dtac (inf_close_minus_iff RS iffD2 RS (bex_Infinitesimal_iff2 RS iffD2)) 4);
by (auto_tac (claset() addSIs [inf_close_add_mono1],
    simpset() addsimps [hypreal_of_real_add,hypreal_add_mult_distrib,
         hypreal_add_mult_distrib2,hypreal_of_real_mult,hypreal_mult_commute,
         hypreal_add_assoc]));
by (res_inst_tac [("w1","hypreal_of_real Db * hypreal_of_real (f x)")]
    (hypreal_add_commute RS subst) 1);
by (auto_tac (claset() addSIs [Infinitesimal_add_inf_close_self2 RS 
                 inf_close_sym,Infinitesimal_add,Infinitesimal_mult,
                 Infinitesimal_hypreal_of_real_mult,
                 Infinitesimal_hypreal_of_real_mult2 ],
      simpset() addsimps [hypreal_add_assoc RS sym]));
qed "NSDERIV_mult";

Goal "[| DERIV f x :> Da; DERIV g x :> Db |] \
\     ==> DERIV (%x. f x * g x) x :> (Da * g(x)) + (Db * f(x))";
by (asm_full_simp_tac (simpset() addsimps [NSDERIV_mult,
                                           NSDERIV_DERIV_iff RS sym]) 1);
qed "DERIV_mult";

(*----------------------------
   Multiplying by a constant
 ---------------------------*)
Goal "NSDERIV f x :> D \
\     ==> NSDERIV (%x. c * f x) x :> c*D";
by (asm_full_simp_tac 
    (simpset() addsimps [real_times_divide1_eq RS sym, NSDERIV_NSLIM_iff,
                         real_minus_mult_eq2, real_add_mult_distrib2 RS sym] 
             delsimps [real_times_divide1_eq, real_minus_mult_eq2 RS sym]) 1);
by (etac (NSLIM_const RS NSLIM_mult) 1);
qed "NSDERIV_cmult";

(* let's do the standard proof though theorem *)
(* LIM_mult2 follows from a NS proof          *)

Goalw [deriv_def] 
      "DERIV f x :> D \
\      ==> DERIV (%x. c * f x) x :> c*D";
by (asm_full_simp_tac 
    (simpset() addsimps [real_times_divide1_eq RS sym, NSDERIV_NSLIM_iff,
                         real_minus_mult_eq2, real_add_mult_distrib2 RS sym] 
             delsimps [real_times_divide1_eq, real_minus_mult_eq2 RS sym]) 1);
by (etac (LIM_const RS LIM_mult2) 1);
qed "DERIV_cmult";

(*--------------------------------
   Negation of function
 -------------------------------*)
Goal "NSDERIV f x :> D \
\      ==> NSDERIV (%x. -(f x)) x :> -D";
by (asm_full_simp_tac (simpset() addsimps [NSDERIV_NSLIM_iff]) 1);
by (res_inst_tac [("t","f x")] (real_minus_minus RS subst) 1);
by (asm_simp_tac (simpset() addsimps [real_minus_add_distrib RS sym,
    real_minus_mult_eq1 RS sym] delsimps [real_minus_add_distrib,
    real_minus_minus]) 1);
by (etac NSLIM_minus 1);
qed "NSDERIV_minus";

Goal "DERIV f x :> D \
\     ==> DERIV (%x. -(f x)) x :> -D";
by (asm_full_simp_tac (simpset() addsimps 
    [NSDERIV_minus,NSDERIV_DERIV_iff RS sym]) 1);
qed "DERIV_minus";

(*-------------------------------
   Subtraction
 ------------------------------*)
Goal "[| NSDERIV f x :> Da; NSDERIV g x :> Db |] \
\     ==> NSDERIV (%x. f x + -g x) x :> Da + -Db";
by (blast_tac (claset() addDs [NSDERIV_add,NSDERIV_minus]) 1);
qed "NSDERIV_add_minus";

Goal "[| DERIV f x :> Da; DERIV g x :> Db |] \
\     ==> DERIV (%x. f x + -g x) x :> Da + -Db";
by (blast_tac (claset() addDs [DERIV_add,DERIV_minus]) 1);
qed "DERIV_add_minus";

Goalw [real_diff_def]
     "[| NSDERIV f x :> Da; NSDERIV g x :> Db |] \
\     ==> NSDERIV (%x. f x - g x) x :> Da - Db";
by (blast_tac (claset() addIs [NSDERIV_add_minus]) 1);
qed "NSDERIV_diff";

Goalw [real_diff_def]
     "[| DERIV f x :> Da; DERIV g x :> Db |] \
\      ==> DERIV (%x. f x - g x) x :> Da - Db";
by (blast_tac (claset() addIs [DERIV_add_minus]) 1);
qed "DERIV_diff";

(*---------------------------------------------------------------
                     (NS) Increment
 ---------------------------------------------------------------*)
Goalw [increment_def] 
      "f NSdifferentiable x ==> \
\     increment f x h = (*f* f) (hypreal_of_real(x) + h) + \
\     -hypreal_of_real (f x)";
by (Blast_tac 1);
qed "incrementI";

Goal "NSDERIV f x :> D ==> \
\    increment f x h = (*f* f) (hypreal_of_real(x) + h) + \
\    -hypreal_of_real (f x)";
by (etac (NSdifferentiableI RS incrementI) 1);
qed "incrementI2";

(* The Increment theorem -- Keisler p. 65 *)
Goal "[| NSDERIV f x :> D; h: Infinitesimal; h ~= 0 |] \
\     ==> EX e: Infinitesimal. increment f x h = hypreal_of_real(D)*h + e*h";
by (forw_inst_tac [("h","h")] incrementI2 1 THEN rewtac nsderiv_def);
by (dtac bspec 1 THEN Auto_tac);
by (dtac (bex_Infinitesimal_iff2 RS iffD2) 1 THEN Step_tac 1);
by (forw_inst_tac [("b1","hypreal_of_real(D) + y")] 
    (hypreal_mult_right_cancel RS iffD2) 1);
by (thin_tac "((*f* f) (hypreal_of_real(x) + h) + \
\   - hypreal_of_real (f x)) / h = hypreal_of_real(D) + y" 2);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_times_divide1_eq RS sym]
             delsimps [hypreal_times_divide1_eq]) 1);
by (auto_tac (claset(),
              simpset() addsimps [hypreal_add_mult_distrib]));
qed "increment_thm";

Goal "[| NSDERIV f x :> D; h @= 0; h ~= 0 |] \
\      ==> EX e: Infinitesimal. increment f x h = \
\             hypreal_of_real(D)*h + e*h";
by (blast_tac (claset() addSDs [mem_infmal_iff RS iffD2] 
    addSIs [increment_thm]) 1);
qed "increment_thm2";

Goal "[| NSDERIV f x :> D; h @= 0; h ~= 0 |] \
\     ==> increment f x h @= 0";
by (dtac increment_thm2 1 THEN auto_tac (claset() addSIs 
    [Infinitesimal_HFinite_mult2,HFinite_add],simpset() addsimps 
    [hypreal_add_mult_distrib RS sym,mem_infmal_iff RS sym]));
by (etac (Infinitesimal_subset_HFinite RS subsetD) 1);
qed "increment_inf_close_zero";

(*---------------------------------------------------------------
   Similarly to the above, the chain rule admits an entirely
   straightforward derivation. Compare this with Harrison's
   HOL proof of the chain rule, which proved to be trickier and
   required an alternative characterisation of differentiability- 
   the so-called Carathedory derivative. Our main problem is
   manipulation of terms.
 --------------------------------------------------------------*)

(* lemmas *)
Goalw [nsderiv_def] 
      "[| NSDERIV g x :> D; \
\              (*f* g) (hypreal_of_real(x) + xa) = hypreal_of_real(g x);\
\              xa : Infinitesimal;\
\              xa ~= 0 \
\           |] ==> D = #0";
by (dtac bspec 1);
by (Auto_tac);
by (asm_full_simp_tac (simpset() addsimps [hypreal_of_real_zero RS sym]) 1);
qed "NSDERIV_zero";

(* can be proved differently using NSLIM_isCont_iff *)
Goalw [nsderiv_def] 
      "[| NSDERIV f x :> D; \
\              h: Infinitesimal; h ~= 0 \
\           |] ==> (*f* f) (hypreal_of_real(x) + h) + -hypreal_of_real(f x) @= 0";    
by (asm_full_simp_tac (simpset() addsimps 
    [mem_infmal_iff RS sym]) 1);
by (rtac Infinitesimal_ratio 1);
by (rtac inf_close_hypreal_of_real_HFinite 3);
by (Auto_tac);
qed "NSDERIV_inf_close";

(*--------------------------------------------------------------- 
   from one version of differentiability 
 
                f(x) - f(a)
              --------------- @= Db
                  x - a
 ---------------------------------------------------------------*)
Goal "[| NSDERIV f (g x) :> Da; \
\        (*f* g) (hypreal_of_real(x) + xa) ~= hypreal_of_real (g x); \
\        (*f* g) (hypreal_of_real(x) + xa) @= hypreal_of_real (g x) \
\     |] ==> ((*f* f) ((*f* g) (hypreal_of_real(x) + xa)) \
\                  + - hypreal_of_real (f (g x))) \
\             / ((*f* g) (hypreal_of_real(x) + xa) + - hypreal_of_real (g x)) \
\            @= hypreal_of_real(Da)";
by (auto_tac (claset(),
       simpset() addsimps [NSDERIV_NSLIM_iff2, NSLIM_def, starfun_divide RS sym,
                           hypreal_of_real_minus,
                           starfun_add RS sym]));
qed "NSDERIVD1";

(*-------------------------------------------------------------- 
   from other version of differentiability 

                f(x + h) - f(x)
               ----------------- @= Db
                       h
 --------------------------------------------------------------*)
Goal "[| NSDERIV g x :> Db; xa: Infinitesimal; xa ~= 0 |] \
\     ==> ((*f* g) (hypreal_of_real(x) + xa) + - hypreal_of_real(g x)) / xa \
\         @= hypreal_of_real(Db)";
by (auto_tac (claset(),
    simpset() addsimps [NSDERIV_NSLIM_iff, NSLIM_def, starfun_divide RS sym,
		starfun_add RS sym, hypreal_of_real_zero, mem_infmal_iff,
		starfun_lambda_cancel,hypreal_of_real_minus]));
qed "NSDERIVD2";

(*---------------------------------------------
  This proof uses both possible definitions
  for differentiability.
 --------------------------------------------*)
Goal "[| NSDERIV f (g x) :> Da; NSDERIV g x :> Db |] \
\     ==> NSDERIV (f o g) x :> Da * Db";
by (asm_simp_tac (simpset() addsimps [NSDERIV_NSLIM_iff,
    NSLIM_def,hypreal_of_real_zero,mem_infmal_iff RS sym]) 1 THEN Step_tac 1);
by (forw_inst_tac [("f","g")] NSDERIV_inf_close 1);
by (auto_tac (claset(),simpset() addsimps [starfun_add RS sym,
    hypreal_of_real_minus, hypreal_of_real_mult,
    starfun_lambda_cancel2,starfun_o RS sym, starfun_divide RS sym]));
by (case_tac "(*f* g) (hypreal_of_real(x) + xa) = hypreal_of_real (g x)" 1);
by (dres_inst_tac [("g","g")] NSDERIV_zero 1);
by (auto_tac (claset(),
    simpset() addsimps [hypreal_divide_def, hypreal_of_real_zero]));
by (res_inst_tac [("z1","(*f* g) (hypreal_of_real(x) + xa) + -hypreal_of_real (g x)"),
    ("y1","inverse xa")] (lemma_chain RS ssubst) 1);
by (etac (hypreal_not_eq_minus_iff RS iffD1) 1);
by (rtac inf_close_mult_hypreal_of_real 1);
by (fold_tac [hypreal_divide_def]);
by (blast_tac (claset() addIs [NSDERIVD1,
    inf_close_minus_iff RS iffD2]) 1);
by (blast_tac (claset() addIs [NSDERIVD2]) 1);
qed "NSDERIV_chain";

(* standard version *)
Goal "[| DERIV f (g x) :> Da; \
\                 DERIV g x :> Db \
\              |] ==> DERIV (f o g) x :> Da * Db";
by (asm_full_simp_tac (simpset() addsimps [NSDERIV_DERIV_iff RS sym,
    NSDERIV_chain]) 1);
qed "DERIV_chain";

Goal "[| DERIV f (g x) :> Da; DERIV g x :> Db |] \
\     ==> DERIV (%x. f (g x)) x :> Da * Db";
by (auto_tac (claset() addDs [DERIV_chain], simpset() addsimps [o_def]));
qed "DERIV_chain2";

(*------------------------------------------------------------------
           Differentiation of natural number powers
 ------------------------------------------------------------------*)
Goal "NSDERIV (%x. x) x :> #1";
by (auto_tac (claset(),
     simpset() addsimps [NSDERIV_NSLIM_iff,
          NSLIM_def, starfun_divide RS sym,starfun_Id, hypreal_of_real_zero,
           hypreal_of_real_one]));
qed "NSDERIV_Id";
Addsimps [NSDERIV_Id];

(*derivative of the identity function*)
Goal "DERIV (%x. x) x :> #1";
by (simp_tac (simpset() addsimps [NSDERIV_DERIV_iff RS sym]) 1);
qed "DERIV_Id";
Addsimps [DERIV_Id];

bind_thm ("isCont_Id", DERIV_Id RS DERIV_isCont);

(*derivative of linear multiplication*)
Goal "DERIV (op * c) x :> c";
by (cut_inst_tac [("c","c"),("x","x")] (DERIV_Id RS DERIV_cmult) 1);
by (Asm_full_simp_tac 1);
qed "DERIV_cmult_Id";
Addsimps [DERIV_cmult_Id];

Goal "NSDERIV (op * c) x :> c";
by (simp_tac (simpset() addsimps [NSDERIV_DERIV_iff]) 1);
qed "NSDERIV_cmult_Id";
Addsimps [NSDERIV_cmult_Id];

Goal "DERIV (%x. x ^ n) x :> real_of_nat n * (x ^ (n - 1))";
by (induct_tac "n" 1);
by (dtac (DERIV_Id RS DERIV_mult) 2);
by (auto_tac (claset(),simpset() addsimps 
    [real_add_mult_distrib]));
by (case_tac "0 < n" 1);
by (dres_inst_tac [("x","x")] realpow_minus_mult 1);
by (auto_tac (claset(),simpset() addsimps 
    [real_mult_assoc,real_add_commute]));
qed "DERIV_pow";

(* NS version *)
Goal "NSDERIV (%x. x ^ n) x :> real_of_nat n * (x ^ (n - 1))";
by (simp_tac (simpset() addsimps [NSDERIV_DERIV_iff,DERIV_pow]) 1);
qed "NSDERIV_pow";

(*---------------------------------------------------------------
                    Power of -1 
 ---------------------------------------------------------------*)


(*Can't get rid of x ~= #0 because it isn't continuous at zero*)
Goalw [nsderiv_def]
     "x ~= #0 ==> NSDERIV (%x. inverse(x)) x :> (- (inverse x ^ 2))";
by (rtac ballI 1 THEN Asm_full_simp_tac 1 THEN Step_tac 1);
by (forward_tac [Infinitesimal_add_not_zero] 1);
by (auto_tac (claset(),
     simpset() addsimps [starfun_inverse_inverse,
         hypreal_of_real_inverse RS sym,hypreal_of_real_minus,realpow_two,
         hypreal_of_real_mult,
         hypreal_of_real_divide] 
               delsimps [hypreal_minus_mult_eq1 RS sym,
                         hypreal_minus_mult_eq2 RS sym]));
by (dtac (hypreal_of_real_not_zero_iff RS iffD2) 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_inverse_add,
         inverse_mult_eq RS sym, hypreal_minus_inverse RS sym] 
         @ hypreal_add_ac @ hypreal_mult_ac delsimps [hypreal_minus_mult_eq1 RS
         sym,hypreal_minus_mult_eq2 RS sym] ) 1);
by (asm_simp_tac (simpset() addsimps [hypreal_mult_assoc RS sym,
         hypreal_add_mult_distrib2] delsimps [hypreal_minus_mult_eq1 RS
         sym,hypreal_minus_mult_eq2 RS sym]) 1);
by (dres_inst_tac [("x3","x") ] ((HFinite_hypreal_of_real RSN
         (2,Infinitesimal_HFinite_mult2)) RS  
          (Infinitesimal_minus_iff RS iffD1)) 1); 
by (forw_inst_tac [("x","hypreal_of_real x"),("y","hypreal_of_real x")] hypreal_mult_not_0 1);
by (res_inst_tac [("y"," inverse(- hypreal_of_real x * hypreal_of_real x)")] inf_close_trans 2);
by (rtac inverse_add_Infinitesimal_inf_close2 2);
by (auto_tac (claset() addIs [HFinite_minus_iff RS iffD1]
         addSDs [Infinitesimal_minus_iff RS iffD2,
         hypreal_of_real_HFinite_diff_Infinitesimal], simpset() addsimps 
         [hypreal_minus_inverse RS sym,hypreal_of_real_mult RS sym]));
qed "NSDERIV_inverse";

Goal "x ~= #0 ==> DERIV (%x. inverse(x)) x :> (-(inverse x ^ 2))";
by (asm_simp_tac (simpset() addsimps [NSDERIV_inverse,
         NSDERIV_DERIV_iff RS sym] delsimps [realpow_Suc]) 1);
qed "DERIV_inverse";

(*--------------------------------------------------------------
        Derivative of inverse 
 -------------------------------------------------------------*)
Goal "[| DERIV f x :> d; f(x) ~= #0 |] \
\     ==> DERIV (%x. inverse(f x)) x :> (- (d * inverse(f(x) ^ 2)))";
by (rtac (real_mult_commute RS subst) 1);
by (asm_simp_tac (simpset() addsimps [real_minus_mult_eq1,
    realpow_inverse] delsimps [realpow_Suc, 
    real_minus_mult_eq1 RS sym]) 1);
by (fold_goals_tac [o_def]);
by (blast_tac (claset() addSIs [DERIV_chain,DERIV_inverse]) 1);
qed "DERIV_inverse_fun";

Goal "[| NSDERIV f x :> d; f(x) ~= #0 |] \
\     ==> NSDERIV (%x. inverse(f x)) x :> (- (d * inverse(f(x) ^ 2)))";
by (asm_full_simp_tac (simpset() addsimps [NSDERIV_DERIV_iff,
            DERIV_inverse_fun] delsimps [realpow_Suc]) 1);
qed "NSDERIV_inverse_fun";

(*--------------------------------------------------------------
        Derivative of quotient 
 -------------------------------------------------------------*)
Goal "[| DERIV f x :> d; DERIV g x :> e; g(x) ~= #0 |] \
\      ==> DERIV (%y. f(y) / (g y)) x :> (d*g(x) + -(e*f(x))) / (g(x) ^ 2)";
by (dres_inst_tac [("f","g")] DERIV_inverse_fun 1);
by (dtac DERIV_mult 2);
by (REPEAT(assume_tac 1));
by (asm_full_simp_tac
    (simpset() addsimps [real_divide_def, real_add_mult_distrib2,
                         realpow_inverse,real_minus_mult_eq1] @ real_mult_ac 
       delsimps [realpow_Suc, real_minus_mult_eq1 RS sym,
                 real_minus_mult_eq2 RS sym]) 1);
qed "DERIV_quotient";

Goal "[| NSDERIV f x :> d; DERIV g x :> e; g(x) ~= #0 |] \
\      ==> NSDERIV (%y. f(y) / (g y)) x :> (d*g(x) \
\                           + -(e*f(x))) / (g(x) ^ 2)";
by (asm_full_simp_tac (simpset() addsimps [NSDERIV_DERIV_iff,
            DERIV_quotient] delsimps [realpow_Suc]) 1);
qed "NSDERIV_quotient";
 
(* ------------------------------------------------------------------------ *)
(* Caratheodory formulation of derivative at a point: standard proof        *)
(* ------------------------------------------------------------------------ *)

Goal "(DERIV f x :> l) = \
\     (EX g. (ALL z. f z - f x = g z * (z - x)) & isCont g x & g x = l)";
by (Step_tac 1);
by (res_inst_tac 
    [("x","%z. if  z = x then l else (f(z) - f(x)) / (z - x)")] exI 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc,
    ARITH_PROVE "z ~= x ==> z - x ~= (#0::real)"]));
by (auto_tac (claset(),simpset() addsimps [isCont_iff,DERIV_iff]));
by (ALLGOALS(rtac (LIM_equal RS iffD1)));
by (auto_tac (claset(),simpset() addsimps [real_diff_def,real_mult_assoc]));
qed "CARAT_DERIV";

Goal "NSDERIV f x :> l ==> \
\     EX g. (ALL z. f z - f x = g z * (z - x)) & isNSCont g x & g x = l";
by (auto_tac (claset(),simpset() addsimps [NSDERIV_DERIV_iff,
    isNSCont_isCont_iff,CARAT_DERIV]));
qed "CARAT_NSDERIV";

(* How about a NS proof? *)
Goal "(ALL z. f z - f x = g z * (z - x)) & isNSCont g x & g x = l \
\     ==> NSDERIV f x :> l";
by (auto_tac (claset(), 
              simpset() delsimprocs real_cancel_factor
                        addsimps [NSDERIV_iff2, starfun_mult RS sym, 
                                  starfun_divide RS sym]));
by (auto_tac (claset(),
              simpset() addsimps [hypreal_mult_assoc,
                                  starfun_diff RS sym]));
by (asm_full_simp_tac (simpset() addsimps [hypreal_eq_minus_iff3 RS sym,
                                           hypreal_diff_def]) 1);
by (asm_full_simp_tac (simpset() addsimps [isNSCont_def]) 1);
qed "CARAT_DERIVD";
 


(*----------------------------------------------------------------------------*)
(* Useful lemmas about nested intervals and proof by bisection (cf.Harrison)  *)
(*----------------------------------------------------------------------------*)

Goal "(ALL n. (f::nat=>real) n <= f (Suc n)) --> f m <= f(m + no)";
by (induct_tac "no" 1);
by (auto_tac (claset() addIs [real_le_trans],simpset()));
qed_spec_mp "lemma_f_mono_add";


Goal "[| ALL n. f(n) <= f(Suc n); \
\        ALL n. g(Suc n) <= g(n); \
\        ALL n. f(n) <= g(n) |] \
\     ==> Bseq f";
by (res_inst_tac [("k","f 0"),("K","g 0")] BseqI2 1 THEN rtac allI 1);
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [real_le_trans], simpset()));
by (res_inst_tac [("j","g(Suc na)")] real_le_trans 1);
by (induct_tac "na" 2);
by (auto_tac (claset() addIs [real_le_trans], simpset()));
qed "f_inc_g_dec_Beq_f";

Goal "[| ALL n. f(n) <= f(Suc n); \
\        ALL n. g(Suc n) <= g(n); \
\        ALL n. f(n) <= g(n) |] \
\     ==> Bseq g";
by (stac (Bseq_minus_iff RS sym) 1);
by (res_inst_tac [("g","%x. -(f x)")] f_inc_g_dec_Beq_f 1); 
by Auto_tac;  
qed "f_inc_g_dec_Beq_g";

Goal "[| ALL n. f n <= f (Suc n);  convergent f |] ==> f n <= lim f";
by (rtac real_leI 1);
by (auto_tac (claset(), 
      simpset() addsimps [convergent_LIMSEQ_iff, LIMSEQ_iff, monoseq_Suc]));
by (dtac real_less_sum_gt_zero 1);
by (dres_inst_tac [("x","f n + - lim f")] spec 1);
by Safe_tac;
by (dres_inst_tac [("P","%na. no<=na --> ?Q na"),("x","no + n")] spec 2);
by Auto_tac;
by (subgoal_tac "lim f <= f(no + n)" 1);
by (induct_tac "no" 2);
by (auto_tac (claset() addIs [real_le_trans],
              simpset() addsimps [real_diff_def, abs_real_def]));
by (dres_inst_tac [("i","f(no + n)"),("no1","no")] 
    (lemma_f_mono_add RSN (2,real_less_le_trans)) 1);
by (auto_tac (claset(), simpset() addsimps [add_commute]));
qed "f_inc_imp_le_lim";

Goal "convergent g ==> lim (%x. - g x) = - (lim g)";
by (rtac (LIMSEQ_minus RS limI) 1); 
by (asm_full_simp_tac (simpset() addsimps [convergent_LIMSEQ_iff]) 1); 
qed "lim_uminus";

Goal "[| ALL n. g(Suc n) <= g(n);  convergent g |] ==> lim g <= g n";
by (subgoal_tac "- (g n) <= - (lim g)" 1);
by (cut_inst_tac [("f", "%x. - (g x)")] f_inc_imp_le_lim 2);
by (auto_tac (claset(), 
              simpset() addsimps [lim_uminus, convergent_minus_iff RS sym]));  
qed "g_dec_imp_lim_le";

Goal "[| ALL n. f(n) <= f(Suc n); \
\        ALL n. g(Suc n) <= g(n); \
\        ALL n. f(n) <= g(n) |] \
\     ==> EX l m. l <= m &  ((ALL n. f(n) <= l) & f ----> l) & \
\                           ((ALL n. m <= g(n)) & g ----> m)";
by (subgoal_tac "monoseq f & monoseq g" 1);
by (force_tac (claset(), simpset() addsimps [LIMSEQ_iff,monoseq_Suc]) 2);
by (subgoal_tac "Bseq f & Bseq g" 1);
by (blast_tac (claset() addIs [f_inc_g_dec_Beq_f, f_inc_g_dec_Beq_g]) 2); 
by (auto_tac (claset() addSDs [Bseq_monoseq_convergent],
              simpset() addsimps [convergent_LIMSEQ_iff]));
by (res_inst_tac [("x","lim f")] exI 1);
by (res_inst_tac [("x","lim g")] exI 1);
by (auto_tac (claset() addIs [LIMSEQ_le], simpset()));
by (auto_tac (claset(), 
              simpset() addsimps [f_inc_imp_le_lim, g_dec_imp_lim_le, 
                                  convergent_LIMSEQ_iff]));  
qed "lemma_nest";


Goal "[| ALL n. f(n) <= f(Suc n); \
\        ALL n. g(Suc n) <= g(n); \
\        ALL n. f(n) <= g(n); \
\        (%n. f(n) - g(n)) ----> 0 |] \
\     ==> EX l. ((ALL n. f(n) <= l) & f ----> l) & \
\               ((ALL n. l <= g(n)) & g ----> l)";
by (dtac lemma_nest 1 THEN Auto_tac);
by (subgoal_tac "l = m" 1);
by (dres_inst_tac [("X","f")] LIMSEQ_diff 2);
by (auto_tac (claset() addIs [LIMSEQ_unique], simpset()));
qed "lemma_nest_unique";

Goal "EX! fn. (fn 0 = e) & (ALL n. fn (Suc n) = f n (fn n))";
by (rtac ex1I 1);
by (rtac conjI 1 THEN rtac allI 2);
by (rtac def_nat_rec_0 1 THEN rtac def_nat_rec_Suc 2);
by (Auto_tac);
by (rtac ext 1 THEN induct_tac "n" 1);
by (Auto_tac);
qed "nat_Axiom";


Goal "((x::real) = y / (#2 * z)) = (#2 * x = y/z)";
by Auto_tac;  
by (dres_inst_tac [("f","%u. (#1/#2)*u")] arg_cong 1); 
by Auto_tac;  
qed "eq_divide_2_times_iff";


val [prem1,prem2] =
Goal "[| !!a b c. [| a <= b; b <= c; P(a,b); P(b,c)|] ==> P(a,c); \
\        ALL x. EX d::real. 0 < d & \
\               (ALL a b. a <= x & x <= b & (b - a) < d --> P(a,b)) \
\     |] ==> ALL a b. a <= b --> P(a,b)";
by (Step_tac 1);
by (cut_inst_tac [("e","(a,b)"),
    ("f","%n fn. if P(fst fn, (fst fn + snd fn)/#2) \
\              then ((fst fn + snd fn) /#2,snd fn) \
\              else (fst fn,(fst fn + snd fn)/#2)")] 
    nat_Axiom 1);
by (etac ex1E 1 THEN etac conjE 1 THEN rtac ccontr 1);
(* set up 1st premise of lemma_nest_unique *)
by (subgoal_tac "ALL n. fst((fn::nat =>(real*real)) n) <= snd (fn n)" 1);
by (rtac allI 2);
by (induct_tac "n" 2);
by (Asm_simp_tac 2);
by (dres_inst_tac [("x","na")] spec 2);
by (case_tac "P (fst (fn na), (fst (fn na) + snd (fn na)) / #2)" 2);
by (Asm_simp_tac 3);
by (Asm_simp_tac 2);
(* 2nd premise *) 
by (subgoal_tac "ALL n. fst(fn n) <= fst (fn (Suc n))" 1);
by (rtac allI 2);
by (induct_tac "n" 2);
by (dres_inst_tac [("x","0")] spec 2);
by (Asm_simp_tac 3);  (*super slow, but proved!*)
by (Asm_simp_tac 2);
(* 3rd premise? [lcp] *)
by (subgoal_tac "ALL n. ~P(fst(fn n),snd(fn n))" 1);
by (rtac allI 2);
by (induct_tac "n" 2);
by (Asm_simp_tac 2);
by (Asm_simp_tac 2 THEN rtac impI 2);
by (rtac ccontr 2);
by (res_inst_tac [("Pa","P (fst (fn na), snd (fn na))")] swap 2);
by (assume_tac 2);
by (res_inst_tac [("b","(fst(fn na) + snd(fn na))/#2")] prem1 2);
by (Asm_full_simp_tac 4); 
by (Asm_full_simp_tac 4); 
by (Asm_full_simp_tac 2); 
by (Asm_simp_tac 2); 
(* 3rd premise [looks like the 4th to lcp!] *)
by (subgoal_tac "ALL n. snd(fn (Suc n)) <= snd (fn n)" 1);
by (rtac allI 2);
by (induct_tac "n" 2);
by (Asm_simp_tac 2);
by (Asm_simp_tac 2);
(* FIXME: simplification takes a very long time! *)
by (ALLGOALS(thin_tac "ALL y. \
\            y 0 = (a, b) & \
\            (ALL n. \
\                y (Suc n) = \
\                (if P (fst (y n), (fst (y n) + snd (y n)) /#2) \
\                 then ((fst (y n) + snd (y n)) /#2, snd (y n)) \
\                 else (fst (y n),\
\                       (fst (y n) + snd (y n)) /#2))) --> \
\            y = fn"));
(*another premise? the 5th? lcp*)
by (subgoal_tac "ALL n. snd(fn n) - fst(fn n) = \
\                       (b - a) * inverse(#2 ^ n)" 1);
by (rtac allI 2);
by (induct_tac "n" 2);
by (Asm_simp_tac 2);
by (asm_full_simp_tac
    (simpset() addsimps [eq_divide_2_times_iff, real_inverse_eq_divide,
                         real_diff_mult_distrib2]) 2);
(*end of the premises [lcp]*)
by (dtac lemma_nest_unique 1);
by (REPEAT(assume_tac 1));
by (Step_tac 2);
by (rtac LIMSEQ_minus_cancel 1);
by (asm_simp_tac (simpset() addsimps [CLAIM "-((a::real) - b) = (b - a)",
    realpow_inverse]) 1);
by (subgoal_tac "#0 = (b-a) * #0" 1);
by (eres_inst_tac [("t","#0")] ssubst 1); 
by (rtac (LIMSEQ_const RS LIMSEQ_mult) 1);
by (rtac LIMSEQ_realpow_zero 1);
by (Asm_full_simp_tac 3); 
by (EVERY1[Simp_tac, Simp_tac]);
by (cut_facts_tac [prem2] 1);
by (dres_inst_tac [("x","l")] spec 1 THEN Step_tac 1);
by (rewtac LIMSEQ_def);
by (dres_inst_tac [("x","d/#2")] spec 1);
by (dres_inst_tac [("x","d/#2")] spec 1);
by (dtac real_less_half_sum 1);
by (thin_tac "ALL n. \
\             fn (Suc n) = \
\             (if P (fst (fn n), (fst (fn n) + snd (fn n))/#2) \
\              then ((fst (fn n) + snd (fn n))/#2, snd (fn n)) \
\              else (fst (fn n), \
\                    (fst (fn n) + snd (fn n))/#2))" 1);
by (Step_tac 1);
by (ALLGOALS(Asm_full_simp_tac));
by (dres_inst_tac [("x","fst(fn (no + noa))")] spec 1);
by (dres_inst_tac [("x","snd(fn (no + noa))")] spec 1);
by (Step_tac 1);
by (ALLGOALS(Asm_full_simp_tac));
by (res_inst_tac [("j","abs(fst(fn(no + noa)) - l) + \
\                       abs(snd(fn(no + noa)) - l)")] real_le_less_trans 1);
by (rtac (real_sum_of_halves RS subst) 2);
by (rewtac real_diff_def);
by (rtac real_add_less_mono 2);

by (Asm_full_simp_tac 2); 
by (Asm_full_simp_tac 2); 
by (res_inst_tac [("y1","fst(fn (no + noa)) ")] 
    (abs_minus_add_cancel RS subst) 1);
by (subgoal_tac "#0 <= (l + - fst (fn (no + noa)))" 1);
by (subgoal_tac "#0 <= (snd (fn (no + noa)) + - l)" 1);
by (asm_simp_tac (simpset() addsimps [abs_eqI1] @ real_add_ac) 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps real_add_divide_distrib::real_add_ac)));
qed "lemma_BOLZANO";

Goal "((ALL a b c. (a <= b & b <= c & P(a,b) & P(b,c)) --> P(a,c)) & \
\         (ALL x. EX d::real. 0 < d & \
\               (ALL a b. a <= x & x <= b & (b - a) < d --> P(a,b)))) \
\         --> (ALL a b. a <= b --> P(a,b))";
by (Step_tac 1);
by (rtac (lemma_BOLZANO RS allE) 1);
by (assume_tac 2);
by (ALLGOALS(Blast_tac));
qed "lemma_BOLZANO2";

(*----------------------------------------------------------------------------*)
(* Intermediate Value Theorem (prove contrapositive by bisection)             *)
(*----------------------------------------------------------------------------*)

Goal "[| f(a) <= y & y <= f(b); \
\        a <= b; \
\        (ALL x. a <= x & x <= b --> isCont f x) \
\     |] ==> EX x. a <= x & x <= b & f(x) = y";
by (rtac contrapos_pp 1);
by (assume_tac 1);
by (cut_inst_tac [("P","%(u,v). a <= u & u <= v & v <= b --> \
\   ~(f(u) <= y & y <= f(v))")] lemma_BOLZANO2 1);
by (Step_tac 1);
by (ALLGOALS(Asm_full_simp_tac));
by (Blast_tac 2);
by (asm_full_simp_tac (simpset() addsimps [isCont_iff,LIM_def]) 1);
by (rtac ccontr 1);
by (subgoal_tac "a <= x & x <= b" 1);
by (Asm_full_simp_tac 2);
by (rotate_tac 3 2);
by (dres_inst_tac [("x","1r")] spec 2);
by (Step_tac 2);
by (Asm_full_simp_tac 2);
by (Asm_full_simp_tac 2);
by (REPEAT(blast_tac (claset() addIs [real_le_trans]) 2));
by (REPEAT(dres_inst_tac [("x","x")] spec 1));
by (Asm_full_simp_tac 1);
(**)
by (rotate_tac 4 1);
by (dres_inst_tac [("x","abs(y - f x)")] spec 1);
by (Step_tac 1);
by (asm_full_simp_tac (simpset() addsimps [real_less_le,
                                           abs_ge_zero,real_diff_def]) 1);
by (dtac (sym RS (abs_zero_iff RS iffD2)) 1);
by (arith_tac 1);
by (dres_inst_tac [("x","s")] spec 1);
by (Step_tac 1);
by (cut_inst_tac [("R1.0","f x"),("R2.0","y")] real_linear 1);
by (Auto_tac);
by (dres_inst_tac [("x","ba - x")] spec 1);
by (auto_tac (claset(),
     simpset() 
	       addsimps [abs_iff, real_diff_le_eq,
       (real_diff_def RS meta_eq_to_obj_eq) RS sym,
       real_less_le_iff, real_le_diff_eq, 
       CLAIM "(~(x::real) <= y) = (y < x)",
       CLAIM "(-x < -y) = ((y::real) < x)",
       CLAIM "(-(y - x)) = (x - (y::real))",
       CLAIM "(x-y=#0) = (x = (y::real))"]));
by (dres_inst_tac [("x","aa - x")] spec 1);
by (case_tac "x <= aa" 1);
by (auto_tac (claset(),simpset() addsimps [real_minus_zero_le_iff2,
    real_le_diff_eq,real_diff_le_eq,(real_le_def RS meta_eq_to_obj_eq) 
    RS sym]));
by (dres_inst_tac [("z","x"),("w","aa")] real_le_anti_sym 1);
by (assume_tac 1 THEN Asm_full_simp_tac 1);
qed "IVT";

Goal "[| f(b) <= y & y <= f(a); \
\        a <= b; \
\        (ALL x. a <= x & x <= b --> isCont f x) \
\     |] ==> EX x. a <= x & x <= b & f(x) = y";
by (subgoal_tac "- f a <= -y & -y <= - f b" 1);
by (thin_tac "f b <= y & y <= f a" 1);
by (dres_inst_tac [("f","%x. - f x")] IVT 1);
by (auto_tac (claset() addIs [isCont_minus],simpset()));
qed "IVT2";

Goal "(f(a) <= y & y <= f(b) & a <= b & \
\     (ALL x. a <= x & x <= b --> isCont f x)) \
\     --> (EX x. a <= x & x <= b & f(x) = y)";
by (blast_tac (claset() addIs [IVT]) 1);
qed "IVT_objl";

Goal "(f(b) <= y & y <= f(a) & a <= b & \
\     (ALL x. a <= x & x <= b --> isCont f x)) \
\     --> (EX x. a <= x & x <= b & f(x) = y)";
by (blast_tac (claset() addIs [IVT2]) 1);
qed "IVT2_objl";

(*----------------------------------------------------------------------------*)
(* By bisection, function continuous on closed interval is bounded above      *)
(*----------------------------------------------------------------------------*)

Goal "abs (real_of_nat x) = real_of_nat x";
by (auto_tac (claset() addIs [abs_eqI1],simpset()));
qed "abs_real_of_nat_cancel";
Addsimps [abs_real_of_nat_cancel];

Goal "~ abs(x) + 1r < x";
by (rtac real_leD 1);
by (auto_tac (claset() addIs [abs_ge_self RS real_le_trans],simpset()));
qed "abs_add_one_not_less_self";
Addsimps [abs_add_one_not_less_self];


Goal "[| a <= b; ALL x. a <= x & x <= b --> isCont f x |]\
\     ==> EX M. ALL x. a <= x & x <= b --> f(x) <= M";
by (cut_inst_tac [("P","%(u,v). a <= u & u <= v & v <= b --> \
\                         (EX M. ALL x. u <= x & x <= v --> f x <= M)")] 
    lemma_BOLZANO2 1);
by (Step_tac 1);
by (ALLGOALS(Asm_full_simp_tac));
by (cut_inst_tac [("x","M"),("y","Ma")] 
    (CLAIM "x <= y | y <= (x::real)") 1);
by (Step_tac 1);
by (res_inst_tac [("x","Ma")] exI 1);
by (Step_tac 1);
by (cut_inst_tac [("x","xb"),("y","xa")] 
    (CLAIM "x <= y | y <= (x::real)") 1);
by (Step_tac 1);
by (rtac real_le_trans 1 THEN assume_tac 2);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (res_inst_tac [("x","M")] exI 1);
by (Step_tac 1);
by (cut_inst_tac [("x","xb"),("y","xa")] 
    (CLAIM "x <= y | y <= (x::real)") 1);
by (Step_tac 1);
by (Asm_full_simp_tac 1);
by (rtac real_le_trans 1 THEN assume_tac 2);
by (Asm_full_simp_tac 1);
by (case_tac "a <= x & x <= b" 1);
by (res_inst_tac [("x","#1")] exI 2);
by (auto_tac (claset(),
              simpset() addsimps [LIM_def,isCont_iff]));
by (dres_inst_tac [("x","x")] spec 1 THEN Auto_tac);
by (thin_tac "ALL M. EX x. a <= x & x <= b & ~ f x <= M" 1);
by (dres_inst_tac [("x","#1")] spec 1);
by Auto_tac;  
by (res_inst_tac [("x","s")] exI 1 THEN Auto_tac);
by (res_inst_tac [("x","abs(f x) + #1")] exI 1 THEN Step_tac 1);
by (dres_inst_tac [("x","xa - x")] spec 1 THEN Auto_tac);
by (res_inst_tac [("j","abs(f xa)")] real_le_trans 3);
by (res_inst_tac [("j","abs(f x) + abs(f(xa) - f(x))")] real_le_trans 4);
by (auto_tac (claset() addIs [abs_triangle_ineq RSN (2, real_le_trans)],
              simpset() addsimps [real_diff_def,abs_ge_self]));
(*arith_tac problem: this step should not be needed*)
by (asm_full_simp_tac (simpset() addsimps [rename_numerals (real_eq_minus_iff2 RS sym)]) 1);
by (auto_tac (claset(),
              simpset() addsimps [abs_real_def] addsplits [split_if_asm]));
qed "isCont_bounded";

(*----------------------------------------------------------------------------*)
(* Refine the above to existence of least upper bound                         *)
(*----------------------------------------------------------------------------*)

Goal "((EX x. x : S) & (EX y. isUb UNIV S (y::real))) --> \
\     (EX t. isLub UNIV S t)";
by (blast_tac (claset() addIs [reals_complete]) 1);
qed "lemma_reals_complete";

Goal "[| a <= b; ALL x. a <= x & x <= b --> isCont f x |] \
\        ==> EX M. (ALL x. a <= x & x <= b --> f(x) <= M) & \
\                  (ALL N. N < M --> (EX x. a <= x & x <= b & N < f(x)))";
by (cut_inst_tac [("S","Collect (%y. EX x. a <= x & x <= b & y = f x)")]
    lemma_reals_complete 1);
by (Auto_tac);
by (dtac isCont_bounded 1 THEN assume_tac 1);
by (auto_tac (claset(),simpset() addsimps [isUb_def,leastP_def,
    isLub_def,setge_def,setle_def]));
by (rtac exI 1 THEN Auto_tac);
by (REPEAT(dtac spec 1) THEN Auto_tac);
by (dres_inst_tac [("x","x")] spec 1);
by (auto_tac (claset() addSIs [real_leI],simpset()));
qed "isCont_has_Ub";

(*----------------------------------------------------------------------------*)
(* Now show that it attains its upper bound                                   *)
(*----------------------------------------------------------------------------*)

Goal "[| a <= b; ALL x. a <= x & x <= b --> isCont f x |] \
\        ==> EX M. (ALL x. a <= x & x <= b --> f(x) <= M) & \
\                  (EX x. a <= x & x <= b & f(x) = M)";
by (ftac isCont_has_Ub 1 THEN assume_tac 1);
by (Clarify_tac 1);
by (res_inst_tac [("x","M")] exI 1);
by (Asm_full_simp_tac 1); 
by (rtac ccontr 1);
by (subgoal_tac "ALL x. a <= x & x <= b --> f x < M" 1 THEN Step_tac 1);
by (rtac ccontr 2 THEN dtac real_leI 2);
by (dres_inst_tac [("z","M")] real_le_anti_sym 2);
by (REPEAT(Blast_tac 2));
by (subgoal_tac "ALL x. a <= x & x <= b --> isCont (%x. inverse(M - f x)) x" 1);
by (Step_tac 1);
by (EVERY[rtac isCont_inverse 2, rtac isCont_diff 2, rtac notI 4]);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [real_diff_eq_eq])));
by (Blast_tac 2);
by (subgoal_tac 
    "EX k. ALL x. a <= x & x <= b --> (%x. inverse(M - (f x))) x <= k" 1);
by (rtac isCont_bounded 2);
by (Step_tac 1);
by (subgoal_tac "ALL x. a <= x & x <= b --> #0 < inverse(M - f(x))" 1);
by (Asm_full_simp_tac 1); 
by (Step_tac 1);
by (asm_full_simp_tac (simpset() addsimps [real_less_diff_eq]) 2);
by (subgoal_tac 
    "ALL x. a <= x & x <= b --> (%x. inverse(M - (f x))) x < (k + #1)" 1);
by (Step_tac 1);
by (res_inst_tac [("j","k")] real_le_less_trans 2);
by (asm_full_simp_tac (simpset() addsimps [real_zero_less_one]) 3);
by (Asm_full_simp_tac 2); 
by (subgoal_tac "ALL x. a <= x & x <= b --> \
\                inverse(k + #1) < inverse((%x. inverse(M - (f x))) x)" 1);
by (Step_tac 1);
by (rtac real_inverse_less_swap 2);
by (ALLGOALS Asm_full_simp_tac);
by (dres_inst_tac [("P", "%N. N<M --> ?Q N"),
                   ("x","M - inverse(k + #1)")] spec 1);
by (Step_tac 1 THEN dtac real_leI 1);
by (dtac (real_le_diff_eq RS iffD1) 1);
by (REPEAT(dres_inst_tac [("x","a")] spec 1));
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac 
    (simpset() addsimps [real_inverse_eq_divide, pos_real_divide_le_eq]) 1); 
by (cut_inst_tac [("x","k"),("y","M-f a")] real_0_less_mult_iff 1);
by (Asm_full_simp_tac 1); 
(*last one*)
by (REPEAT(dres_inst_tac [("x","x")] spec 1));
by (Asm_full_simp_tac 1); 
qed "isCont_eq_Ub";


(*----------------------------------------------------------------------------*)
(* Same theorem for lower bound                                               *)
(*----------------------------------------------------------------------------*)

Goal "[| a <= b; ALL x. a <= x & x <= b --> isCont f x |] \
\        ==> EX M. (ALL x. a <= x & x <= b --> M <= f(x)) & \
\                  (EX x. a <= x & x <= b & f(x) = M)";
by (subgoal_tac "ALL x. a <= x & x <= b --> isCont (%x. -(f x)) x" 1);
by (blast_tac (claset() addIs [isCont_minus]) 2);
by (dres_inst_tac [("f","(%x. -(f x))")] isCont_eq_Ub 1);
by (Step_tac 1);
by (Auto_tac);
qed "isCont_eq_Lb";


(* ------------------------------------------------------------------------- *)
(* Another version.                                                          *)
(* ------------------------------------------------------------------------- *)

Goal "[|a <= b; ALL x. a <= x & x <= b --> isCont f x |] \
\     ==> EX L M. (ALL x. a <= x & x <= b --> L <= f(x) & f(x) <= M) & \
\         (ALL y. L <= y & y <= M --> (EX x. a <= x & x <= b & (f(x) = y)))";
by (ftac isCont_eq_Lb 1);
by (ftac isCont_eq_Ub 2);
by (REPEAT(assume_tac 1));
by (Step_tac 1);
by (res_inst_tac [("x","f x")] exI 1);
by (res_inst_tac [("x","f xa")] exI 1);
by (Asm_full_simp_tac 1);
by (Step_tac 1);
by (cut_inst_tac [("x","x"),("y","xa")] (CLAIM "x <= y | y <= (x::real)") 1);
by (Step_tac 1);
by (cut_inst_tac [("f","f"),("a","x"),("b","xa"),("y","y")] IVT_objl 1);
by (cut_inst_tac [("f","f"),("a","xa"),("b","x"),("y","y")] IVT2_objl 2);
by (Step_tac 1);
by (res_inst_tac [("x","xb")] exI 2);
by (res_inst_tac [("x","xb")] exI 4);
by (ALLGOALS(Asm_full_simp_tac));
qed "isCont_Lb_Ub";

(*----------------------------------------------------------------------------*)
(* If f'(x) > 0 then x is locally strictly increasing at the right            *)
(*----------------------------------------------------------------------------*)

Goalw [deriv_def,LIM_def] 
    "[| DERIV f x :> l;  #0 < l |] ==> \
\      EX d. #0 < d & (ALL h. #0 < h & h < d --> f(x) < f(x + h))";
by (dtac spec 1 THEN Auto_tac);
by (res_inst_tac [("x","s")] exI 1 THEN Auto_tac);
by (subgoal_tac "#0 < l*h" 1);
by (asm_full_simp_tac (simpset() addsimps [real_0_less_mult_iff]) 2); 
by (dres_inst_tac [("x","h")] spec 1);
by (asm_full_simp_tac
    (simpset() addsimps [abs_real_def, real_inverse_eq_divide, 
                 pos_real_le_divide_eq, pos_real_less_divide_eq]
              addsplits [split_if_asm]) 1); 
qed "DERIV_left_inc";

Goalw [deriv_def,LIM_def] 
    "[| DERIV f x :> l;  l < #0 |] ==> \
\      EX d. #0 < d & (ALL h. #0 < h & h < d --> f(x) < f(x - h))";
by (dres_inst_tac [("x","-l")] spec 1 THEN Auto_tac);
by (res_inst_tac [("x","s")] exI 1 THEN Auto_tac);
by (subgoal_tac "l*h < #0" 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult_less_0_iff]) 2); 
by (dres_inst_tac [("x","-h")] spec 1);
by (asm_full_simp_tac
    (simpset() addsimps [abs_real_def, real_inverse_eq_divide, 
                         pos_real_less_divide_eq,
                         symmetric real_diff_def]
               addsplits [split_if_asm]) 1);
by (subgoal_tac "#0 < (f (x - h) - f x)/h" 1);
by (arith_tac 2);
by (asm_full_simp_tac
    (simpset() addsimps [pos_real_less_divide_eq]) 1); 
qed "DERIV_left_dec";


Goal "[| DERIV f x :> l; \
\        EX d. #0 < d & (ALL y. abs(x - y) < d --> f(y) <= f(x)) |] \
\     ==> l = #0";
by (res_inst_tac [("R1.0","l"),("R2.0","#0")] real_linear_less2 1);
by (Step_tac 1);
by (dtac DERIV_left_dec 1);
by (dtac DERIV_left_inc 3);
by (Step_tac 1);
by (dres_inst_tac [("d1.0","d"),("d2.0","da")] real_lbound_gt_zero 1);
by (dres_inst_tac [("d1.0","d"),("d2.0","da")] real_lbound_gt_zero 3);
by (Step_tac 1);
by (dres_inst_tac [("x","x - e")] spec 1);
by (dres_inst_tac [("x","x + e")] spec 2);
by (auto_tac (claset(),simpset() addsimps [abs_eqI2,abs_minus_cancel]));
qed "DERIV_local_max";

(*----------------------------------------------------------------------------*)
(* Similar theorem for a local minimum                                        *)
(*----------------------------------------------------------------------------*)

Goal "[| DERIV f x :> l; \
\        EX d::real. #0 < d & (ALL y. abs(x - y) < d --> f(x) <= f(y)) |] \
\     ==> l = #0";
by (dtac (DERIV_minus RS DERIV_local_max) 1); 
by Auto_tac;  
qed "DERIV_local_min";

(*----------------------------------------------------------------------------*)
(* In particular if a function is locally flat                                *)
(*----------------------------------------------------------------------------*)

Goal "[| DERIV f x :> l; \
\        EX d. #0 < d & (ALL y. abs(x - y) < d --> f(x) = f(y)) |] \
\     ==> l = #0";
by (auto_tac (claset() addSDs [DERIV_local_max],simpset()));
qed "DERIV_local_const";

(*----------------------------------------------------------------------------*)
(* Lemma about introducing open ball in open interval                         *)
(*----------------------------------------------------------------------------*)

Goal "[| a < x;  x < b |] ==> \
\       EX d::real. #0 < d &  (ALL y. abs(x - y) < d --> a < y & y < b)";
by (simp_tac (simpset() addsimps [abs_interval_iff]) 1);
by (cut_inst_tac [("x","x - a"),("y","b - x")] 
    (CLAIM "x <= y | y <= (x::real)") 1);
by (Step_tac 1);
by (res_inst_tac [("x","x - a")] exI 1);
by (res_inst_tac [("x","b - x")] exI 2);
by (Auto_tac);
by (auto_tac (claset(),simpset() addsimps [real_less_diff_eq]));
qed "lemma_interval_lt";

Goal "[| a < x;  x < b |] ==> \
\       EX d::real. #0 < d &  (ALL y. abs(x - y) < d --> a <= y & y <= b)";
by (dtac lemma_interval_lt 1);
by (Auto_tac);
by (auto_tac (claset() addSIs [exI] ,simpset()));
qed "lemma_interval";

(*-----------------------------------------------------------------------
            Rolle's Theorem
   If f is defined and continuous on the finite closed interval [a,b]
   and differentiable a least on the open interval (a,b), and f(a) = f(b),
   then x0 : (a,b) such that f'(x0) = #0
 ----------------------------------------------------------------------*)

Goal "[| a < b; f(a) = f(b); \
\        ALL x. a <= x & x <= b --> isCont f x; \
\        ALL x. a < x & x < b --> f differentiable x \
\     |] ==> EX z. a < z & z < b & DERIV f z :> #0";
by (ftac (real_less_imp_le RS isCont_eq_Ub) 1);
by (EVERY1[assume_tac,Step_tac]);
by (ftac (real_less_imp_le RS isCont_eq_Lb) 1);
by (EVERY1[assume_tac,Step_tac]);
by (case_tac "a < x & x < b" 1 THEN etac conjE 1);
by (Asm_full_simp_tac 2);
by (forw_inst_tac [("a","a"),("x","x")] lemma_interval 1);
by (EVERY1[assume_tac,etac exE]);
by (res_inst_tac [("x","x")] exI 1 THEN Asm_full_simp_tac 1);
by (subgoal_tac "(EX l. DERIV f x :> l) & \
\        (EX d. #0 < d & (ALL y. abs(x - y) < d --> f(y) <= f(x)))" 1);
by (Clarify_tac 1 THEN rtac conjI 2);
by (blast_tac (claset() addIs [differentiableD]) 2);
by (Blast_tac 2);
by (ftac DERIV_local_max 1);
by (EVERY1[Blast_tac,Blast_tac]);
by (case_tac "a < xa & xa < b" 1 THEN etac conjE 1);
by (Asm_full_simp_tac 2);
by (forw_inst_tac [("a","a"),("x","xa")] lemma_interval 1);
by (EVERY1[assume_tac,etac exE]);
by (res_inst_tac [("x","xa")] exI 1 THEN Asm_full_simp_tac 1);
by (subgoal_tac "(EX l. DERIV f xa :> l) & \
\        (EX d. #0 < d & (ALL y. abs(xa - y) < d --> f(xa) <= f(y)))" 1);
by (Clarify_tac 1 THEN rtac conjI 2);
by (blast_tac (claset() addIs [differentiableD]) 2);
by (Blast_tac 2);
by (ftac DERIV_local_min 1);
by (EVERY1[Blast_tac,Blast_tac]);
by (subgoal_tac "ALL x. a <= x & x <= b --> f(x) = f(b)" 1);
by (Clarify_tac 2);
by (rtac real_le_anti_sym 2);
by (subgoal_tac "f b = f x" 2);
by (Asm_full_simp_tac 2);
by (res_inst_tac [("x1","a"),("y1","x")] (real_le_imp_less_or_eq RS disjE) 2);
by (assume_tac 2);
by (dres_inst_tac [("z","x"),("w","b")] real_le_anti_sym 2);
by (subgoal_tac "f b = f xa" 5);
by (Asm_full_simp_tac 5);
by (res_inst_tac [("x1","a"),("y1","xa")] (real_le_imp_less_or_eq RS disjE) 5);
by (assume_tac 5);
by (dres_inst_tac [("z","xa"),("w","b")] real_le_anti_sym 5);
by (REPEAT(Asm_full_simp_tac 2));
by (dtac real_dense 1 THEN etac exE 1);
by (res_inst_tac [("x","r")] exI 1 THEN Asm_full_simp_tac 1);
by (etac conjE 1);
by (forw_inst_tac [("a","a"),("x","r")] lemma_interval 1);
by (EVERY1[assume_tac, etac exE]);
by (subgoal_tac "(EX l. DERIV f r :> l) & \
\        (EX d. #0 < d & (ALL y. abs(r - y) < d --> f(r) = f(y)))" 1);
by (Clarify_tac 1 THEN rtac conjI 2);
by (blast_tac (claset() addIs [differentiableD]) 2);
by (EVERY1[ftac DERIV_local_const, Blast_tac, Blast_tac]);
by (res_inst_tac [("x","d")] exI 1);
by (EVERY1[rtac conjI, Blast_tac, rtac allI, rtac impI]);
by (res_inst_tac [("s","f b")] trans 1);
by (blast_tac (claset() addSDs [real_less_imp_le]) 1);
by (rtac sym 1 THEN Blast_tac 1);
qed "Rolle";

(*----------------------------------------------------------------------------*)
(* Mean value theorem                                                         *)
(*----------------------------------------------------------------------------*)

Goal "f a - (f b - f a)/(b - a) * a = \
\     f b - (f b - f a)/(b - a) * (b::real)";
by (case_tac "a = b" 1);
by (asm_full_simp_tac (simpset() addsimps [REAL_DIVIDE_ZERO]) 1); 
by (res_inst_tac [("c1","b - a")] (real_mult_left_cancel RS iffD1) 1);
by (arith_tac 1);
by (auto_tac (claset(),
              simpset() addsimps [real_diff_mult_distrib2]));
by (auto_tac (claset(),
           simpset() addsimps [real_diff_mult_distrib]));
qed "lemma_MVT";

Goal "[| a < b; \
\        ALL x. a <= x & x <= b --> isCont f x; \
\        ALL x. a < x & x < b --> f differentiable x |] \
\     ==>  EX l z. a < z & z < b & DERIV f z :> l & \
\                  (f(b) - f(a) = (b - a) * l)";
by (dres_inst_tac [("f","%x. f(x) - (((f(b) - f(a)) / (b - a)) * x)")]
    Rolle 1);
by (rtac lemma_MVT 1);
by (Step_tac 1);
by (rtac isCont_diff 1 THEN Blast_tac 1);
by (rtac (isCont_const RS isCont_mult) 1);
by (rtac isCont_Id 1); 
by (dres_inst_tac [("P", "%x. ?Pre x --> f differentiable x"), 
                   ("x","x")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [differentiable_def]) 1);
by (Step_tac 1);
by (res_inst_tac [("x","xa - ((f(b) - f(a)) / (b - a))")] exI 1);
by (rtac DERIV_diff 1 THEN assume_tac 1);
(*derivative of a linear function is the constant...*)
by (subgoal_tac "(%x. (f b - f a) * x / (b - a)) = \
\                op * ((f b - f a) / (b - a))" 1);
by (rtac ext 2 THEN Simp_tac 2);
by (Asm_full_simp_tac 1); 
(*final case*)
by (res_inst_tac [("x","((f(b) - f(a)) / (b - a))")] exI 1);
by (res_inst_tac [("x","z")] exI 1);
by (Step_tac 1);
by (Asm_full_simp_tac 2); 
by (subgoal_tac "DERIV (%x. ((f(b) - f(a)) / (b - a)) * x) z :> \
\                           ((f(b) - f(a)) / (b - a))" 1);
by (rtac DERIV_cmult_Id 2); 
by (dtac DERIV_add 1 THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_assoc, real_diff_def]) 1);
qed "MVT";

(*----------------------------------------------------------------------------*)
(* Theorem that function is constant if its derivative is 0 over an interval. *)
(*----------------------------------------------------------------------------*)

Goal "[| a < b; \
\        ALL x. a <= x & x <= b --> isCont f x; \
\        ALL x. a < x & x < b --> DERIV f x :> #0 |] \
\       ==> (f b = f a)";
by (dtac MVT 1 THEN assume_tac 1);
by (blast_tac (claset() addIs [differentiableI]) 1);
by (auto_tac (claset() addSDs [DERIV_unique],simpset() 
    addsimps [real_diff_eq_eq]));
qed "DERIV_isconst_end";

Goal "[| a < b; \
\        ALL x. a <= x & x <= b --> isCont f x; \
\        ALL x. a < x & x < b --> DERIV f x :> #0 |] \
\       ==> ALL x. a <= x & x <= b --> f x = f a";
by (Step_tac 1);
by (dres_inst_tac [("x","a")] real_le_imp_less_or_eq 1);
by (Step_tac 1);
by (dres_inst_tac [("b","x")] DERIV_isconst_end 1);
by (Auto_tac);
qed "DERIV_isconst1";

Goal "[| a < b; \
\        ALL x. a <= x & x <= b --> isCont f x; \
\        ALL x. a < x & x < b --> DERIV f x :> #0; \
\        a <= x; x <= b |] \
\       ==> f x = f a";
by (blast_tac (claset() addDs [DERIV_isconst1]) 1);
qed "DERIV_isconst2";

Goal "ALL x. DERIV f x :> #0 ==> f(x) = f(y)";
by (res_inst_tac [("R1.0","x"),("R2.0","y")] real_linear_less2 1);
by (rtac sym 1);
by (auto_tac (claset() addIs [DERIV_isCont,DERIV_isconst_end],simpset()));
qed "DERIV_isconst_all";

Goal "[|a ~= b; ALL x. DERIV f x :> k |] ==> (f(b) - f(a)) = (b - a) * k";
by (res_inst_tac [("R1.0","a"),("R2.0","b")] real_linear_less2 1);
by (Auto_tac);
by (ALLGOALS(dres_inst_tac [("f","f")] MVT));
by (auto_tac (claset() addDs [DERIV_isCont,DERIV_unique],simpset() addsimps 
    [differentiable_def]));
by (auto_tac (claset() addDs [DERIV_unique],
       simpset() addsimps [real_add_mult_distrib, real_diff_def,
                           real_minus_mult_eq1 RS sym]));
qed "DERIV_const_ratio_const";

Goal "[|a ~= b; ALL x. DERIV f x :> k |] ==> (f(b) - f(a))/(b - a) = k";
by (res_inst_tac [("c1","b - a")] (real_mult_right_cancel RS iffD1) 1);
by (auto_tac (claset() addSDs [DERIV_const_ratio_const], 
              simpset() addsimps [real_mult_assoc]));
qed "DERIV_const_ratio_const2";

Goal "((a + b) /#2 - a) = (b - a)/(#2::real)";
by Auto_tac;  
qed "real_average_minus_first";
Addsimps [real_average_minus_first];

Goal "((b + a)/#2 - a) = (b - a)/(#2::real)";
by Auto_tac;  
qed "real_average_minus_second";
Addsimps [real_average_minus_second];


(* Gallileo's "trick": average velocity = av. of end velocities *)
Goal "[|a ~= (b::real); ALL x. DERIV v x :> k|] \
\     ==> v((a + b)/#2) = (v a + v b)/#2";
by (res_inst_tac [("R1.0","a"),("R2.0","b")] real_linear_less2 1);
by (Auto_tac);
by (ftac DERIV_const_ratio_const2 1 THEN assume_tac 1);
by (ftac DERIV_const_ratio_const2 2 THEN assume_tac 2);
by (dtac real_less_half_sum 1);
by (dtac real_gt_half_sum 2); 
by (ftac (real_not_refl2 RS DERIV_const_ratio_const2) 1 THEN assume_tac 1);
by (dtac ((real_not_refl2 RS not_sym) RS DERIV_const_ratio_const2) 2
    THEN assume_tac 2);
by (ALLGOALS (dres_inst_tac [("f","%u. (b-a)*u")] arg_cong)); 
by (auto_tac (claset(), simpset() addsimps [real_inverse_eq_divide])); 
by (asm_full_simp_tac (simpset() addsimps [real_add_commute, eq_commute]) 1);  
qed "DERIV_const_average";


(* ------------------------------------------------------------------------ *)
(* Dull lemma that an continuous injection on an interval must have a strict*)
(* maximum at an end point, not in the middle.                              *)
(* ------------------------------------------------------------------------ *)

Goal "[|#0 < d; ALL z. abs(z - x) <= d --> g(f z) = z; \
\       ALL z. abs(z - x) <= d --> isCont f z |]  \
\     ==> ~(ALL z. abs(z - x) <= d --> f(z) <= f(x))";
by (rtac notI 1);
by (rotate_tac 3 1);
by (forw_inst_tac [("x","x - d")] spec 1);
by (forw_inst_tac [("x","x + d")] spec 1);
by (Step_tac 1);
by (cut_inst_tac [("x","f(x - d)"),("y","f(x + d)")] 
    (ARITH_PROVE "x <= y | y <= (x::real)") 4);
by (etac disjE 4);
by (REPEAT(arith_tac 1));
by (cut_inst_tac [("f","f"),("a","x - d"),("b","x"),("y","f(x + d)")]
    IVT_objl 1);
by (Step_tac 1);
by (arith_tac 1);
by (asm_full_simp_tac (simpset() addsimps [abs_le_interval_iff]) 1);
by (dres_inst_tac [("f","g")] arg_cong 1);
by (rotate_tac 2 1);
by (forw_inst_tac [("x","xa")] spec 1);
by (dres_inst_tac [("x","x + d")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [abs_le_interval_iff]) 1);
(* 2nd case: similar *)
by (cut_inst_tac [("f","f"),("a","x"),("b","x + d"),("y","f(x - d)")]
    IVT2_objl 1);
by (Step_tac 1);
by (arith_tac 1);
by (asm_full_simp_tac (simpset() addsimps [abs_le_interval_iff]) 1);
by (dres_inst_tac [("f","g")] arg_cong 1);
by (rotate_tac 2 1);
by (forw_inst_tac [("x","xa")] spec 1);
by (dres_inst_tac [("x","x - d")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [abs_le_interval_iff]) 1);
qed "lemma_isCont_inj";

(* ------------------------------------------------------------------------ *)
(* Similar version for lower bound                                          *)
(* ------------------------------------------------------------------------ *)

Goal "[|#0 < d; ALL z. abs(z - x) <= d --> g(f z) = z; \
\       ALL z. abs(z - x) <= d --> isCont f z |]  \
\     ==> ~(ALL z. abs(z - x) <= d --> f(x) <= f(z))";
by (auto_tac (claset() addSDs [(asm_full_simplify (simpset()) 
    (read_instantiate [("f","%x. - f x"),("g","%y. g(-y)"),("x","x"),("d","d")]
     lemma_isCont_inj))],simpset() addsimps [isCont_minus]));
qed "lemma_isCont_inj2";

(* ------------------------------------------------------------------------ *)
(* Show there's an interval surrounding f(x) in f[[x - d, x + d]]           *)
(* Also from John's theory                                                  *)
(* ------------------------------------------------------------------------ *)

Addsimps [zero_eq_numeral_0,one_eq_numeral_1];

val lemma_le = ARITH_PROVE "#0 <= (d::real) ==> -d <= d";

(* FIXME: awful proof - needs improvement *)
Goal "[| #0 < d; ALL z. abs(z - x) <= d --> g(f z) = z; \
\        ALL z. abs(z - x) <= d --> isCont f z |] \
\      ==> EX e. #0 < e & \
\                 (ALL y. \
\                     abs(y - f(x)) <= e --> \
\                     (EX z. abs(z - x) <= d & (f z = y)))";
by (ftac real_less_imp_le 1);
by (dtac (lemma_le RS (asm_full_simplify (simpset()) (read_instantiate 
    [("f","f"),("a","x - d"),("b","x + d")] isCont_Lb_Ub))) 1);
by (Step_tac 1);
by (asm_full_simp_tac (simpset() addsimps [abs_le_interval_iff]) 1);
by (subgoal_tac "L <= f x & f x <= M" 1);
by (dres_inst_tac [("P", "%v. ?P v --> ?Q v & ?R v"), ("x","x")] spec 2);
by (Asm_full_simp_tac 2);
by (subgoal_tac "L < f x & f x < M" 1);
by (Step_tac 1);
by (dres_inst_tac [("x","L")] (ARITH_PROVE "x < y ==> #0 < y - (x::real)") 1);
by (dres_inst_tac [("x","f x")] (ARITH_PROVE "x < y ==> #0 < y - (x::real)") 1);
by (dres_inst_tac [("d1.0","f x - L"),("d2.0","M - f x")] 
    (rename_numerals real_lbound_gt_zero) 1);
by (Step_tac 1);
by (res_inst_tac [("x","e")] exI 1);
by (Step_tac 1);
by (asm_full_simp_tac (simpset() addsimps [abs_le_interval_iff]) 1);
by (dres_inst_tac [("P","%v. ?PP v --> (EX xa. ?Q v xa)"),("x","y")] spec 1);
by (Step_tac 1 THEN REPEAT(arith_tac 1));
by (res_inst_tac [("x","xa")] exI 1);
by (arith_tac 1);
by (ALLGOALS(etac (ARITH_PROVE "[|x <= y; x ~= y |] ==> x < (y::real)")));
by (ALLGOALS(rotate_tac 3));
by (dtac lemma_isCont_inj2 1);
by (assume_tac 2);
by (dtac lemma_isCont_inj 3);
by (assume_tac 4);
by (TRYALL(assume_tac));
by (Step_tac 1);
by (ALLGOALS(dres_inst_tac [("x","z")] spec));
by (ALLGOALS(arith_tac));
qed "isCont_inj_range";


(* ------------------------------------------------------------------------ *)
(* Continuity of inverse function                                           *)
(* ------------------------------------------------------------------------ *)

Goal "[| #0 < d; ALL z. abs(z - x) <= d --> g(f(z)) = z; \
\        ALL z. abs(z - x) <= d --> isCont f z |] \
\     ==> isCont g (f x)";
by (simp_tac (simpset() addsimps [isCont_iff,LIM_def]) 1);
by (Step_tac 1);
by (dres_inst_tac [("d1.0","r")] (rename_numerals real_lbound_gt_zero) 1);
by (assume_tac 1 THEN Step_tac 1);
by (subgoal_tac "ALL z. abs(z - x) <= e --> (g(f z) = z)" 1);
by (Force_tac 2);
by (subgoal_tac "ALL z. abs(z - x) <= e --> isCont f z" 1);
by (Force_tac 2);
by (dres_inst_tac [("d","e")] isCont_inj_range 1);
by (assume_tac 2 THEN assume_tac 1);
by (Step_tac 1);
by (res_inst_tac [("x","ea")] exI 1);
by Auto_tac;
by (rotate_tac 4 1);
by (dres_inst_tac [("x","f(x) + xa")] spec 1); 
by Auto_tac;
by (dtac sym 1 THEN Auto_tac);
by (arith_tac 1);
qed "isCont_inverse";

