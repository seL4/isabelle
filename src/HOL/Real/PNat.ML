(*  Title       : HOL/Real/PNat.ML
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

The positive naturals -- proofs mainly as in theory Nat.
*)

Goal "mono(%X. {1} Un (Suc``X))";
by (REPEAT (ares_tac [monoI, subset_refl, image_mono, Un_mono] 1));
qed "pnat_fun_mono";

bind_thm ("pnat_unfold", pnat_fun_mono RS (pnat_def RS def_lfp_unfold));

Goal "1 : pnat";
by (stac pnat_unfold 1);
by (rtac (singletonI RS UnI1) 1);
qed "one_RepI";

Addsimps [one_RepI];

Goal "i: pnat ==> Suc(i) : pnat";
by (stac pnat_unfold 1);
by (etac (imageI RS UnI2) 1);
qed "pnat_Suc_RepI";

Goal "2 : pnat";
by (rtac (one_RepI RS pnat_Suc_RepI) 1);
qed "two_RepI";

(*** Induction ***)

val major::prems = Goal
    "[| i: pnat;  P(1);   \
\       !!j. [| j: pnat; P(j) |] ==> P(Suc(j)) |]  ==> P(i)";
by (rtac ([pnat_def, pnat_fun_mono, major] MRS def_lfp_induct) 1);
by (blast_tac (claset() addIs prems) 1);
qed "PNat_induct";

val prems = Goalw [pnat_one_def,pnat_Suc_def]
    "[| P(1p);   \
\       !!n. P(n) ==> P(pSuc n) |]  ==> P(n)";
by (rtac (Rep_pnat_inverse RS subst) 1);   
by (rtac (Rep_pnat RS PNat_induct) 1);
by (REPEAT (ares_tac prems 1
     ORELSE eresolve_tac [Abs_pnat_inverse RS subst] 1));
qed "pnat_induct";

(*Perform induction on n. *)
fun pnat_ind_tac a i = 
  induct_thm_tac pnat_induct a i  THEN  rename_last_tac a [""] (i+1);

val prems = Goal
    "[| !!x. P x 1p;  \
\       !!y. P 1p (pSuc y);  \
\       !!x y. [| P x y |] ==> P (pSuc x) (pSuc y)  \
\    |] ==> P m n";
by (res_inst_tac [("x","m")] spec 1);
by (pnat_ind_tac "n" 1);
by (rtac allI 2);
by (pnat_ind_tac "x" 2);
by (REPEAT (ares_tac (prems@[allI]) 1 ORELSE etac spec 1));
qed "pnat_diff_induct";

(*Case analysis on the natural numbers*)
val prems = Goal
    "[| n=1p ==> P;  !!x. n = pSuc(x) ==> P |] ==> P";
by (subgoal_tac "n=1p | (EX x. n = pSuc(x))" 1);
by (fast_tac (claset() addSEs prems) 1);
by (pnat_ind_tac "n" 1);
by (rtac (refl RS disjI1) 1);
by (Blast_tac 1);
qed "pnatE";

(*** Isomorphisms: Abs_Nat and Rep_Nat ***)

Goal "inj_on Abs_pnat pnat";
by (rtac inj_on_inverseI 1);
by (etac Abs_pnat_inverse 1);
qed "inj_on_Abs_pnat";

Addsimps [inj_on_Abs_pnat RS inj_on_iff];

Goal "inj(Rep_pnat)";
by (rtac inj_inverseI 1);
by (rtac Rep_pnat_inverse 1);
qed "inj_Rep_pnat";

Goal "0 ~: pnat";
by (stac pnat_unfold 1);
by Auto_tac;
qed "zero_not_mem_pnat";

(* 0 : pnat ==> P *)
bind_thm ("zero_not_mem_pnatE", zero_not_mem_pnat RS notE);

Addsimps [zero_not_mem_pnat];

Goal "x : pnat ==> 0 < x";
by (dtac (pnat_unfold RS subst) 1);
by Auto_tac;
qed "mem_pnat_gt_zero";

Goal "0 < x ==> x: pnat";
by (stac pnat_unfold 1);
by (dtac (gr_implies_not0 RS not0_implies_Suc) 1); 
by (etac exE 1 THEN Asm_simp_tac 1);
by (induct_tac "m" 1);
by (auto_tac (claset(),simpset() 
    addsimps [one_RepI]) THEN dtac pnat_Suc_RepI 1);
by (Blast_tac 1);
qed "gt_0_mem_pnat";

Goal "(x: pnat) = (0 < x)";
by (blast_tac (claset() addDs [mem_pnat_gt_zero,gt_0_mem_pnat]) 1);
qed "mem_pnat_gt_0_iff";

Goal "0 < Rep_pnat x";
by (rtac (Rep_pnat RS mem_pnat_gt_zero) 1);
qed "Rep_pnat_gt_zero";

Goalw [pnat_add_def] "(x::pnat) + y = y + x";
by (simp_tac (simpset() addsimps [add_commute]) 1);
qed "pnat_add_commute";

(** alternative definition for pnat **)
(** order isomorphism **)
Goal "pnat = {x::nat. 0 < x}";
by (rtac set_ext 1);
by (simp_tac (simpset() addsimps 
    [mem_pnat_gt_0_iff]) 1);
qed "Collect_pnat_gt_0";

(*** Distinctness of constructors ***)

Goalw [pnat_one_def,pnat_Suc_def] "pSuc(m) ~= 1p";
by (rtac (inj_on_Abs_pnat RS inj_on_contraD) 1);
by (rtac (Rep_pnat_gt_zero RS Suc_mono RS less_not_refl2) 1);
by (REPEAT (resolve_tac [Rep_pnat RS  pnat_Suc_RepI, one_RepI] 1));
qed "pSuc_not_one";

bind_thm ("one_not_pSuc", pSuc_not_one RS not_sym);

AddIffs [pSuc_not_one,one_not_pSuc];

bind_thm ("pSuc_neq_one", (pSuc_not_one RS notE));
bind_thm ("one_neq_pSuc", pSuc_neq_one RS pSuc_neq_one);

(** Injectiveness of pSuc **)

Goalw [pnat_Suc_def] "inj(pSuc)";
by (rtac injI 1);
by (dtac (inj_on_Abs_pnat RS inj_onD) 1);
by (REPEAT (resolve_tac [Rep_pnat, pnat_Suc_RepI] 1));
by (dtac (inj_Suc RS injD) 1);
by (etac (inj_Rep_pnat RS injD) 1);
qed "inj_pSuc"; 

bind_thm ("pSuc_inject", inj_pSuc RS injD);

Goal "(pSuc(m)=pSuc(n)) = (m=n)";
by (EVERY1 [rtac iffI, etac pSuc_inject, etac arg_cong]); 
qed "pSuc_pSuc_eq";

AddIffs [pSuc_pSuc_eq];

Goal "n ~= pSuc(n)";
by (pnat_ind_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "n_not_pSuc_n";

bind_thm ("pSuc_n_not_n", n_not_pSuc_n RS not_sym);

Goal "n ~= 1p ==> EX m. n = pSuc m";
by (rtac pnatE 1);
by (REPEAT (Blast_tac 1));
qed "not1p_implies_pSuc";

Goal "pSuc m = m + 1p";
by (auto_tac (claset(),simpset() addsimps [pnat_Suc_def,
    pnat_one_def,Abs_pnat_inverse,pnat_add_def]));
qed "pSuc_is_plus_one";

Goal
      "(Rep_pnat x + Rep_pnat y): pnat";
by (cut_facts_tac [[Rep_pnat_gt_zero,
    Rep_pnat_gt_zero] MRS add_less_mono,Collect_pnat_gt_0] 1);
by (etac ssubst 1);
by Auto_tac;
qed "sum_Rep_pnat";

Goalw [pnat_add_def] 
      "Rep_pnat x + Rep_pnat y = Rep_pnat (x + y)";
by (simp_tac (simpset() addsimps [sum_Rep_pnat RS 
                          Abs_pnat_inverse]) 1);
qed "sum_Rep_pnat_sum";

Goalw [pnat_add_def] 
      "(x + y) + z = x + (y + (z::pnat))";
by (res_inst_tac [("f","Abs_pnat")] arg_cong 1);
by (simp_tac (simpset() addsimps [sum_Rep_pnat RS 
                Abs_pnat_inverse,add_assoc]) 1);
qed "pnat_add_assoc";

Goalw [pnat_add_def] "x + (y + z) = y + (x + (z::pnat))";
by (res_inst_tac [("f","Abs_pnat")] arg_cong 1);
by (simp_tac (simpset() addsimps [sum_Rep_pnat RS 
          Abs_pnat_inverse,add_left_commute]) 1);
qed "pnat_add_left_commute";

(*Addition is an AC-operator*)
bind_thms ("pnat_add_ac", [pnat_add_assoc, pnat_add_commute, pnat_add_left_commute]);

Goalw [pnat_add_def] "((x::pnat) + y = x + z) = (y = z)";
by (auto_tac (claset() addDs [inj_on_Abs_pnat RS inj_onD,
     inj_Rep_pnat RS injD],simpset() addsimps [sum_Rep_pnat]));
qed "pnat_add_left_cancel";

Goalw [pnat_add_def] "(y + (x::pnat) = z + x) = (y = z)";
by (auto_tac (claset() addDs [inj_on_Abs_pnat RS inj_onD,
     inj_Rep_pnat RS injD],simpset() addsimps [sum_Rep_pnat]));
qed "pnat_add_right_cancel";

Goalw [pnat_add_def] "!(y::pnat). x + y ~= x";
by (rtac (Rep_pnat_inverse RS subst) 1);
by (auto_tac (claset() addDs [inj_on_Abs_pnat RS inj_onD] 
  	               addSDs [add_eq_self_zero],
	      simpset() addsimps [sum_Rep_pnat, Rep_pnat,Abs_pnat_inverse,
				  Rep_pnat_gt_zero RS less_not_refl2]));
qed "pnat_no_add_ident";


(***) (***) (***) (***) (***) (***) (***) (***) (***)

  (*** pnat_less ***)

Goalw [pnat_less_def] 
      "[| x < (y::pnat); y < z |] ==> x < z";
by ((etac less_trans 1) THEN assume_tac 1);
qed "pnat_less_trans";

Goalw [pnat_less_def] "x < (y::pnat) ==> ~ y < x";
by (etac less_not_sym 1);
qed "pnat_less_not_sym";

(* [| x < y;  ~P ==> y < x |] ==> P *)
bind_thm ("pnat_less_asym", pnat_less_not_sym RS contrapos_np);

Goalw [pnat_less_def] "~ y < (y::pnat)";
by Auto_tac;
qed "pnat_less_not_refl";

bind_thm ("pnat_less_irrefl",pnat_less_not_refl RS notE);

Goalw [pnat_less_def] 
     "x < (y::pnat) ==> x ~= y";
by Auto_tac;
qed "pnat_less_not_refl2";

Goal "~ Rep_pnat y < 0";
by Auto_tac;
qed "Rep_pnat_not_less0";

(*** Rep_pnat < 0 ==> P ***)
bind_thm ("Rep_pnat_less_zeroE",Rep_pnat_not_less0 RS notE);

Goal "~ Rep_pnat y < 1";
by (auto_tac (claset(),simpset() addsimps [less_Suc_eq,
                  Rep_pnat_gt_zero,less_not_refl2]));
qed "Rep_pnat_not_less_one";

(*** Rep_pnat < 1 ==> P ***)
bind_thm ("Rep_pnat_less_oneE",Rep_pnat_not_less_one RS notE);

Goalw [pnat_less_def] 
     "x < (y::pnat) ==> Rep_pnat y ~= 1";
by (auto_tac (claset(),simpset() 
    addsimps [Rep_pnat_not_less_one] delsimps [less_one]));
qed "Rep_pnat_gt_implies_not0";

Goalw [pnat_less_def] 
      "(x::pnat) < y | x = y | y < x";
by (cut_facts_tac [less_linear] 1);
by (fast_tac (claset() addIs [inj_Rep_pnat RS injD]) 1);
qed "pnat_less_linear";

Goalw [le_def] "1 <= Rep_pnat x";
by (rtac Rep_pnat_not_less_one 1);
qed "Rep_pnat_le_one";

Goalw [pnat_less_def]
     "!! (z1::nat). z1 < z2  ==> EX z3. z1 + Rep_pnat z3 = z2";
by (dtac less_imp_add_positive 1);
by (force_tac (claset() addSIs [Abs_pnat_inverse],
	       simpset() addsimps [Collect_pnat_gt_0]) 1);
qed "lemma_less_ex_sum_Rep_pnat";


   (*** pnat_le ***)

Goalw [pnat_le_def] "~ (x::pnat) < y ==> y <= x";
by (assume_tac 1);
qed "pnat_leI";

Goalw [pnat_le_def] "(x::pnat) <= y ==> ~ y < x";
by (assume_tac 1);
qed "pnat_leD";

bind_thm ("pnat_leE", make_elim pnat_leD);

Goal "(~ (x::pnat) < y) = (y <= x)";
by (blast_tac (claset() addIs [pnat_leI] addEs [pnat_leE]) 1);
qed "pnat_not_less_iff_le";

Goalw [pnat_le_def] "~(x::pnat) <= y ==> y < x";
by (Blast_tac 1);
qed "pnat_not_leE";

Goalw [pnat_le_def] "(x::pnat) < y ==> x <= y";
by (blast_tac (claset() addEs [pnat_less_asym]) 1);
qed "pnat_less_imp_le";

(** Equivalence of m<=n and  m<n | m=n **)

Goalw [pnat_le_def] "m <= n ==> m < n | m=(n::pnat)";
by (cut_facts_tac [pnat_less_linear] 1);
by (blast_tac (claset() addEs [pnat_less_irrefl,pnat_less_asym]) 1);
qed "pnat_le_imp_less_or_eq";

Goalw [pnat_le_def] "m<n | m=n ==> m <=(n::pnat)";
by (cut_facts_tac [pnat_less_linear] 1);
by (blast_tac (claset() addSEs [pnat_less_irrefl] addEs [pnat_less_asym]) 1);
qed "pnat_less_or_eq_imp_le";

Goal "(m <= (n::pnat)) = (m < n | m=n)";
by (REPEAT(ares_tac [iffI,pnat_less_or_eq_imp_le,pnat_le_imp_less_or_eq] 1));
qed "pnat_le_eq_less_or_eq";

Goal "n <= (n::pnat)";
by (simp_tac (simpset() addsimps [pnat_le_eq_less_or_eq]) 1);
qed "pnat_le_refl";

Goal "[| i < j; j <= k |] ==> i < (k::pnat)";
by (dtac pnat_le_imp_less_or_eq 1);
by (blast_tac (claset() addIs [pnat_less_trans]) 1);
qed "pnat_less_le_trans";

Goal "[| i <= j; j <= k |] ==> i <= (k::pnat)";
by (EVERY1[dtac pnat_le_imp_less_or_eq, 
           dtac pnat_le_imp_less_or_eq,
           rtac pnat_less_or_eq_imp_le, 
           blast_tac (claset() addIs [pnat_less_trans])]);
qed "pnat_le_trans";

Goal "[| m <= n; n <= m |] ==> m = (n::pnat)";
by (EVERY1[dtac pnat_le_imp_less_or_eq, 
           dtac pnat_le_imp_less_or_eq,
           blast_tac (claset() addIs [pnat_less_asym])]);
qed "pnat_le_anti_sym";

Goal "(m::pnat) < n = (m <= n & m ~= n)";
by (rtac iffI 1);
by (rtac conjI 1);
by (etac pnat_less_imp_le 1);
by (etac pnat_less_not_refl2 1);
by (blast_tac (claset() addSDs [pnat_le_imp_less_or_eq]) 1);
qed "pnat_less_le";


(***) (***) (***) (***) (***) (***) (***) (***)

(*** alternative definition for pnat_le ***)
Goalw [pnat_le_def,pnat_less_def] 
      "((m::pnat) <= n) = (Rep_pnat m <= Rep_pnat n)";
by (auto_tac (claset() addSIs [leI] addSEs [leD],simpset()));
qed "pnat_le_iff_Rep_pnat_le";

Goal "!!k::pnat. (k + m <= k + n) = (m<=n)";
by (simp_tac (simpset() addsimps [pnat_le_iff_Rep_pnat_le,
                           sum_Rep_pnat_sum RS sym]) 1);
qed "pnat_add_left_cancel_le";

Goalw [pnat_less_def] "!!k::pnat. (k + m < k + n) = (m<n)";
by (simp_tac (simpset() addsimps [sum_Rep_pnat_sum RS sym]) 1);
qed "pnat_add_left_cancel_less";

Addsimps [pnat_add_left_cancel, pnat_add_right_cancel,
  pnat_add_left_cancel_le, pnat_add_left_cancel_less];

Goalw [pnat_less_def] "i+j < (k::pnat) ==> i<k";
by (auto_tac (claset() addEs [add_lessD1],
    simpset() addsimps [sum_Rep_pnat_sum RS sym]));
qed "pnat_add_lessD1";

Goal "!!i::pnat. ~ (i+j < i)";
by (rtac  notI 1);
by (etac (pnat_add_lessD1 RS pnat_less_irrefl) 1);
qed "pnat_not_add_less1";

Goal "!!i::pnat. ~ (j+i < i)";
by (simp_tac (simpset() addsimps [pnat_add_commute, pnat_not_add_less1]) 1);
qed "pnat_not_add_less2";

AddIffs [pnat_not_add_less1, pnat_not_add_less2];

Goal "m + k <= n --> m <= (n::pnat)";
by (simp_tac (simpset() addsimps [pnat_le_iff_Rep_pnat_le,
    sum_Rep_pnat_sum RS sym]) 1);
qed_spec_mp "pnat_add_leD1";

Goal "!!n::pnat. m + k <= n ==> k <= n";
by (full_simp_tac (simpset() addsimps [pnat_add_commute]) 1);
by (etac pnat_add_leD1 1);
qed_spec_mp "pnat_add_leD2";

Goal "!!n::pnat. m + k <= n ==> m <= n & k <= n";
by (blast_tac (claset() addDs [pnat_add_leD1, pnat_add_leD2]) 1);
bind_thm ("pnat_add_leE", result() RS conjE);

Goalw [pnat_less_def] 
      "!!k l::pnat. [| k < l; m + l = k + n |] ==> m < n";
by (rtac less_add_eq_less 1 THEN assume_tac 1);
by (auto_tac (claset(),simpset() addsimps [sum_Rep_pnat_sum]));
qed "pnat_less_add_eq_less";

(* ordering on positive naturals in terms of existence of sum *)
(* could provide alternative definition -- Gleason *)
Goalw [pnat_less_def,pnat_add_def] 
      "(z1::pnat) < z2 = (EX z3. z1 + z3 = z2)";
by (rtac iffI 1);
by (res_inst_tac [("t","z2")] (Rep_pnat_inverse RS subst) 1);
by (dtac lemma_less_ex_sum_Rep_pnat 1);
by (etac exE 1 THEN res_inst_tac [("x","z3")] exI 1);
by (auto_tac (claset(),simpset() addsimps [sum_Rep_pnat_sum,Rep_pnat_inverse]));
by (res_inst_tac [("t","Rep_pnat z1")] (add_0_right RS subst) 1);
by (auto_tac (claset(),simpset() addsimps [sum_Rep_pnat_sum RS sym,
               Rep_pnat_gt_zero] delsimps [add_0_right]));
qed "pnat_less_iff";

Goal "(EX (x::pnat). z1 + x = z2) | z1 = z2 \
\          |(EX x. z2 + x = z1)";
by (cut_facts_tac [pnat_less_linear] 1);
by (asm_full_simp_tac (simpset() addsimps [pnat_less_iff]) 1);
qed "pnat_linear_Ex_eq";

Goal "!!(x::pnat). x + y = z ==> x < z";
by (rtac (pnat_less_iff RS iffD2) 1);
by (Blast_tac 1);
qed "pnat_eq_lessI";

(*** Monotonicity of Addition ***)

(*strict, in 1st argument*)
Goalw [pnat_less_def] "!!i j k::pnat. i < j ==> i + k < j + k";
by (auto_tac (claset() addIs [add_less_mono1],
       simpset() addsimps [sum_Rep_pnat_sum RS sym]));
qed "pnat_add_less_mono1";

Goalw [pnat_less_def] "!!i j k::pnat. [|i < j; k < l|] ==> i + k < j + l";
by (auto_tac (claset() addIs [add_less_mono],
       simpset() addsimps [sum_Rep_pnat_sum RS sym]));
qed "pnat_add_less_mono";

Goalw [pnat_less_def]
"!!f. [| !!i j::pnat. i<j ==> f(i) < f(j);       \
\        i <= j                                 \
\     |] ==> f(i) <= (f(j)::pnat)";
by (auto_tac (claset() addSDs [inj_Rep_pnat RS injD],
             simpset() addsimps [pnat_le_iff_Rep_pnat_le,
				 order_le_less]));
qed "pnat_less_mono_imp_le_mono";

Goal "!!i j k::pnat. i<=j ==> i + k <= j + k";
by (res_inst_tac [("f", "%j. j+k")] pnat_less_mono_imp_le_mono 1);
by (etac pnat_add_less_mono1 1);
by (assume_tac 1);
qed "pnat_add_le_mono1";

Goal "!!k l::pnat. [|i<=j;  k<=l |] ==> i + k <= j + l";
by (etac (pnat_add_le_mono1 RS pnat_le_trans) 1);
by (simp_tac (simpset() addsimps [pnat_add_commute]) 1);
(*j moves to the end because it is free while k, l are bound*)
by (etac pnat_add_le_mono1 1);
qed "pnad_add_le_mono";

Goal "1 * Rep_pnat n = Rep_pnat n";
by (Asm_simp_tac 1);
qed "Rep_pnat_mult_1";

Goal "Rep_pnat n * 1 = Rep_pnat n";
by (Asm_simp_tac 1);
qed "Rep_pnat_mult_1_right";

Goal
      "(Rep_pnat x * Rep_pnat y): pnat";
by (cut_facts_tac [[Rep_pnat_gt_zero,
    Rep_pnat_gt_zero] MRS mult_less_mono1,Collect_pnat_gt_0] 1);
by (etac ssubst 1);
by Auto_tac;
qed "mult_Rep_pnat";

Goalw [pnat_mult_def] 
      "Rep_pnat x * Rep_pnat y = Rep_pnat (x * y)";
by (simp_tac (simpset() addsimps [mult_Rep_pnat RS 
                          Abs_pnat_inverse]) 1);
qed "mult_Rep_pnat_mult";

Goalw [pnat_mult_def] "m * n = n * (m::pnat)";
by (full_simp_tac (simpset() addsimps [mult_commute]) 1);
qed "pnat_mult_commute";

Goalw [pnat_mult_def,pnat_add_def] "(m + n)*k = (m*k) + ((n*k)::pnat)";
by (res_inst_tac [("f","Abs_pnat")] arg_cong 1);
by (simp_tac (simpset() addsimps [mult_Rep_pnat RS 
                Abs_pnat_inverse,sum_Rep_pnat RS 
             Abs_pnat_inverse, add_mult_distrib]) 1);
qed "pnat_add_mult_distrib";

Goalw [pnat_mult_def,pnat_add_def] "k*(m + n) = (k*m) + ((k*n)::pnat)";
by (res_inst_tac [("f","Abs_pnat")] arg_cong 1);
by (simp_tac (simpset() addsimps [mult_Rep_pnat RS 
                Abs_pnat_inverse,sum_Rep_pnat RS 
             Abs_pnat_inverse, add_mult_distrib2]) 1);
qed "pnat_add_mult_distrib2";

Goalw [pnat_mult_def] 
      "(x * y) * z = x * (y * (z::pnat))";
by (res_inst_tac [("f","Abs_pnat")] arg_cong 1);
by (simp_tac (simpset() addsimps [mult_Rep_pnat RS 
                Abs_pnat_inverse,mult_assoc]) 1);
qed "pnat_mult_assoc";

Goalw [pnat_mult_def] "x * (y * z) = y * (x * (z::pnat))";
by (res_inst_tac [("f","Abs_pnat")] arg_cong 1);
by (simp_tac (simpset() addsimps [mult_Rep_pnat RS 
          Abs_pnat_inverse,mult_left_commute]) 1);
qed "pnat_mult_left_commute";

Goalw [pnat_mult_def] "x * (Abs_pnat 1) = x";
by (full_simp_tac (simpset() addsimps [one_RepI RS Abs_pnat_inverse,
                   Rep_pnat_inverse]) 1);
qed "pnat_mult_1";

Goal "Abs_pnat 1 * x = x";
by (full_simp_tac (simpset() addsimps [pnat_mult_1,
                   pnat_mult_commute]) 1);
qed "pnat_mult_1_left";

(*Multiplication is an AC-operator*)
bind_thms ("pnat_mult_ac", 
	   [pnat_mult_assoc, pnat_mult_commute, pnat_mult_left_commute]);


Goal "!!i::pnat. i<j ==> k*i < k*j";
by (asm_full_simp_tac (simpset() addsimps [pnat_less_def,
    mult_Rep_pnat_mult RS sym,Rep_pnat_gt_zero,mult_less_mono2]) 1);
qed "pnat_mult_less_mono2";

Goal "!!i::pnat. i<j ==> i*k < j*k";
by (dtac pnat_mult_less_mono2 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [pnat_mult_commute])));
qed "pnat_mult_less_mono1";

Goalw [pnat_less_def] "(m*(k::pnat) < n*k) = (m<n)";
by (asm_full_simp_tac (simpset() addsimps [mult_Rep_pnat_mult 
              RS sym,Rep_pnat_gt_zero]) 1);
qed "pnat_mult_less_cancel2";

Goalw [pnat_less_def] "((k::pnat)*m < k*n) = (m<n)";
by (asm_full_simp_tac (simpset() addsimps [mult_Rep_pnat_mult 
              RS sym,Rep_pnat_gt_zero]) 1);
qed "pnat_mult_less_cancel1";

Addsimps [pnat_mult_less_cancel1, pnat_mult_less_cancel2];

Goalw [pnat_mult_def]  "(m*(k::pnat) = n*k) = (m=n)";
by (cut_inst_tac [("x","k")] Rep_pnat_gt_zero 1);
by (auto_tac (claset() addSDs [inj_on_Abs_pnat RS inj_onD,
                               inj_Rep_pnat RS injD] 
                       addIs [mult_Rep_pnat], 
    simpset() addsimps [mult_cancel2]));
qed "pnat_mult_cancel2";

Goal "((k::pnat)*m = k*n) = (m=n)";
by (rtac (pnat_mult_cancel2 RS subst) 1);
by (auto_tac (claset () addIs [pnat_mult_commute RS subst],simpset()));
qed "pnat_mult_cancel1";

Addsimps [pnat_mult_cancel1, pnat_mult_cancel2];

Goal "!!(z1::pnat). z2*z3 = z4*z5  ==> z2*(z1*z3) = z4*(z1*z5)";
by (auto_tac (claset() addIs [pnat_mult_cancel1 RS iffD2],
              simpset() addsimps [pnat_mult_left_commute]));
qed "pnat_same_multI2";

val [prem] = Goal
    "(!!u. z = Abs_pnat(u) ==> P) ==> P";
by (cut_inst_tac [("x1","z")] 
    (rewrite_rule [pnat_def] (Rep_pnat RS Abs_pnat_inverse)) 1);
by (res_inst_tac [("u","Rep_pnat z")] prem 1);
by (dtac (inj_Rep_pnat RS injD) 1);
by (Asm_simp_tac 1);
qed "eq_Abs_pnat";

(** embedding of naturals in positive naturals **)

(* pnat_one_eq! *)
Goalw [pnat_of_nat_def,pnat_one_def]"1p = pnat_of_nat 0";
by (Full_simp_tac 1);
qed "pnat_one_iff";

Goalw [pnat_of_nat_def,pnat_one_def,
       pnat_add_def] "1p + 1p = pnat_of_nat 1";
by (res_inst_tac [("f","Abs_pnat")] arg_cong 1);
by (auto_tac (claset() addIs [(gt_0_mem_pnat RS Abs_pnat_inverse RS ssubst)],
    simpset()));
qed "pnat_two_eq";

Goal "inj(pnat_of_nat)";
by (rtac injI 1);
by (rewtac pnat_of_nat_def);
by (dtac (inj_on_Abs_pnat RS inj_onD) 1);
by (auto_tac (claset() addSIs [gt_0_mem_pnat],simpset()));
qed "inj_pnat_of_nat";

Goal "0 < n + 1";
by Auto_tac;
qed "nat_add_one_less";

Goal "0 < n1 + n2 + 1";
by Auto_tac;
qed "nat_add_one_less1";

(* this worked with one call to auto_tac before! *)
Goalw [pnat_add_def,pnat_of_nat_def,pnat_one_def] 
      "pnat_of_nat n1 + pnat_of_nat n2 = \
\      pnat_of_nat (n1 + n2) + 1p";
by (res_inst_tac [("f","Abs_pnat")] arg_cong 1);
by (rtac (gt_0_mem_pnat RS Abs_pnat_inverse RS ssubst) 1);
by (rtac (gt_0_mem_pnat RS Abs_pnat_inverse RS ssubst) 2);
by (rtac (gt_0_mem_pnat RS Abs_pnat_inverse RS ssubst) 3);
by (rtac (gt_0_mem_pnat RS Abs_pnat_inverse RS ssubst) 4);
by (auto_tac (claset(),
	      simpset() addsimps [sum_Rep_pnat_sum,
				  nat_add_one_less,nat_add_one_less1]));
qed "pnat_of_nat_add";

Goalw [pnat_of_nat_def,pnat_less_def] 
       "(n < m) = (pnat_of_nat n < pnat_of_nat m)";
by (auto_tac (claset(),simpset() 
    addsimps [Abs_pnat_inverse,Collect_pnat_gt_0]));
qed "pnat_of_nat_less_iff";
Addsimps [pnat_of_nat_less_iff RS sym];

Goalw [pnat_mult_def,pnat_of_nat_def] 
      "pnat_of_nat n1 * pnat_of_nat n2 = \
\      pnat_of_nat (n1 * n2 + n1 + n2)";
by (auto_tac (claset(),simpset() addsimps [mult_Rep_pnat_mult,
    pnat_add_def,Abs_pnat_inverse,gt_0_mem_pnat]));
qed "pnat_of_nat_mult";
