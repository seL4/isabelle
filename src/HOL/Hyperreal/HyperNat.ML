(*  Title       : HyperNat.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Explicit construction of hypernaturals using 
                  ultrafilters
*) 
       
(*------------------------------------------------------------------------
                       Properties of hypnatrel
 ------------------------------------------------------------------------*)

(** Proving that hyprel is an equivalence relation       **)
(** Natural deduction for hypnatrel - similar to hyprel! **)

Goalw [hypnatrel_def]
     "((X,Y): hypnatrel) = ({n. X n = Y n}: FreeUltrafilterNat)";
by (Fast_tac 1);
qed "hypnatrel_iff";

Goalw [hypnatrel_def] 
     "{n. X n = Y n}: FreeUltrafilterNat ==> (X,Y): hypnatrel";
by (Fast_tac 1);
qed "hypnatrelI";

Goalw [hypnatrel_def]
  "p: hypnatrel --> (EX X Y. \
\                 p = (X,Y) & {n. X n = Y n} : FreeUltrafilterNat)";
by (Fast_tac 1);
qed "hypnatrelE_lemma";

val [major,minor] = Goal
  "[| p: hypnatrel;  \
\     !!X Y. [| p = (X,Y); {n. X n = Y n}: FreeUltrafilterNat |] \
\            ==> Q |] \
\  ==> Q";
by (cut_facts_tac [major RS (hypnatrelE_lemma RS mp)] 1);
by (REPEAT (eresolve_tac [asm_rl,exE,conjE,minor] 1));
qed "hypnatrelE";

AddSIs [hypnatrelI];
AddSEs [hypnatrelE];

Goalw [hypnatrel_def] "(x,x): hypnatrel";
by Auto_tac;
qed "hypnatrel_refl";

Goalw [hypnatrel_def] "(x,y): hypnatrel --> (y,x):hypnatrel";
by (auto_tac (claset() addIs [lemma_perm RS subst], simpset()));
qed_spec_mp "hypnatrel_sym";

Goalw [hypnatrel_def]
     "(x,y): hypnatrel --> (y,z):hypnatrel --> (x,z):hypnatrel";
by Auto_tac;
by (Fuf_tac 1);
qed_spec_mp "hypnatrel_trans";

Goalw [equiv_def, refl_def, sym_def, trans_def]
     "equiv UNIV hypnatrel";
by (auto_tac (claset() addSIs [hypnatrel_refl] 
                       addSEs [hypnatrel_sym,hypnatrel_trans] 
                       delrules [hypnatrelI,hypnatrelE],
              simpset()));
qed "equiv_hypnatrel";

val equiv_hypnatrel_iff =
    [UNIV_I, UNIV_I] MRS (equiv_hypnatrel RS eq_equiv_class_iff);

Goalw  [hypnat_def,hypnatrel_def,quotient_def] "hypnatrel``{x}:hypnat";
by (Blast_tac 1);
qed "hypnatrel_in_hypnat";

Goal "inj_on Abs_hypnat hypnat";
by (rtac inj_on_inverseI 1);
by (etac Abs_hypnat_inverse 1);
qed "inj_on_Abs_hypnat";

Addsimps [equiv_hypnatrel_iff,inj_on_Abs_hypnat RS inj_on_iff,
          hypnatrel_iff, hypnatrel_in_hypnat, Abs_hypnat_inverse];

Addsimps [equiv_hypnatrel RS eq_equiv_class_iff];
val eq_hypnatrelD = equiv_hypnatrel RSN (2,eq_equiv_class);

Goal "inj(Rep_hypnat)";
by (rtac inj_inverseI 1);
by (rtac Rep_hypnat_inverse 1);
qed "inj_Rep_hypnat";

Goalw [hypnatrel_def] "x: hypnatrel `` {x}";
by (Step_tac 1);
by Auto_tac;
qed "lemma_hypnatrel_refl";

Addsimps [lemma_hypnatrel_refl];

Goalw [hypnat_def] "{} ~: hypnat";
by (auto_tac (claset() addSEs [quotientE],simpset()));
qed "hypnat_empty_not_mem";

Addsimps [hypnat_empty_not_mem];

Goal "Rep_hypnat x ~= {}";
by (cut_inst_tac [("x","x")] Rep_hypnat 1);
by Auto_tac;
qed "Rep_hypnat_nonempty";

Addsimps [Rep_hypnat_nonempty];

(*------------------------------------------------------------------------
   hypnat_of_nat: the injection from nat to hypnat
 ------------------------------------------------------------------------*)
Goal "inj(hypnat_of_nat)";
by (rtac injI 1);
by (rewtac hypnat_of_nat_def);
by (dtac (inj_on_Abs_hypnat RS inj_onD) 1);
by (REPEAT (rtac hypnatrel_in_hypnat 1));
by (dtac eq_equiv_class 1);
by (rtac equiv_hypnatrel 1);
by (Fast_tac 1);
by (rtac ccontr 1 THEN rotate_tac 1 1);
by Auto_tac;
qed "inj_hypnat_of_nat";

val [prem] = Goal
    "(!!x. z = Abs_hypnat(hypnatrel``{x}) ==> P) ==> P";
by (res_inst_tac [("x1","z")] 
    (rewrite_rule [hypnat_def] Rep_hypnat RS quotientE) 1);
by (dres_inst_tac [("f","Abs_hypnat")] arg_cong 1);
by (res_inst_tac [("x","x")] prem 1);
by (asm_full_simp_tac (simpset() addsimps [Rep_hypnat_inverse]) 1);
qed "eq_Abs_hypnat";

(*-----------------------------------------------------------
   Addition for hyper naturals: hypnat_add 
 -----------------------------------------------------------*)
Goalw [congruent2_def]
     "congruent2 hypnatrel (%X Y. hypnatrel``{%n. X n + Y n})";
by Safe_tac;
by (ALLGOALS(Fuf_tac));
qed "hypnat_add_congruent2";

Goalw [hypnat_add_def]
  "Abs_hypnat(hypnatrel``{%n. X n}) + Abs_hypnat(hypnatrel``{%n. Y n}) = \
\  Abs_hypnat(hypnatrel``{%n. X n + Y n})";
by (asm_simp_tac
    (simpset() addsimps [[equiv_hypnatrel, hypnat_add_congruent2] 
     MRS UN_equiv_class2]) 1);
qed "hypnat_add";

Goal "(z::hypnat) + w = w + z";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","w")] eq_Abs_hypnat 1);
by (asm_simp_tac (simpset() addsimps (add_ac @ [hypnat_add])) 1);
qed "hypnat_add_commute";

Goal "((z1::hypnat) + z2) + z3 = z1 + (z2 + z3)";
by (res_inst_tac [("z","z1")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","z2")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","z3")] eq_Abs_hypnat 1);
by (asm_simp_tac (simpset() addsimps [hypnat_add,add_assoc]) 1);
qed "hypnat_add_assoc";

(*For AC rewriting*)
Goal "(x::hypnat)+(y+z)=y+(x+z)";
by (rtac (hypnat_add_commute RS trans) 1);
by (rtac (hypnat_add_assoc RS trans) 1);
by (rtac (hypnat_add_commute RS arg_cong) 1);
qed "hypnat_add_left_commute";

(* hypnat addition is an AC operator *)
val hypnat_add_ac = [hypnat_add_assoc,hypnat_add_commute,
                      hypnat_add_left_commute];

Goalw [hypnat_zero_def] "(0::hypnat) + z = z";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (asm_full_simp_tac (simpset() addsimps [hypnat_add]) 1);
qed "hypnat_add_zero_left";

Goal "z + (0::hypnat) = z";
by (simp_tac (simpset() addsimps 
    [hypnat_add_zero_left,hypnat_add_commute]) 1);
qed "hypnat_add_zero_right";

Addsimps [hypnat_add_zero_left,hypnat_add_zero_right];

(*-----------------------------------------------------------
   Subtraction for hyper naturals: hypnat_minus
 -----------------------------------------------------------*)
Goalw [congruent2_def]
    "congruent2 hypnatrel (%X Y. hypnatrel``{%n. X n - Y n})";
by Safe_tac;
by (ALLGOALS(Fuf_tac));
qed "hypnat_minus_congruent2";
 
Goalw [hypnat_minus_def]
  "Abs_hypnat(hypnatrel``{%n. X n}) - Abs_hypnat(hypnatrel``{%n. Y n}) = \
\  Abs_hypnat(hypnatrel``{%n. X n - Y n})";
by (asm_simp_tac
    (simpset() addsimps [[equiv_hypnatrel, hypnat_minus_congruent2] 
     MRS UN_equiv_class2]) 1);
qed "hypnat_minus";

Goalw [hypnat_zero_def] "z - z = (0::hypnat)";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (asm_full_simp_tac (simpset() addsimps [hypnat_minus]) 1);
qed "hypnat_minus_zero";

Goalw [hypnat_zero_def] "(0::hypnat) - n = 0";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (asm_full_simp_tac (simpset() addsimps [hypnat_minus]) 1);
qed "hypnat_diff_0_eq_0";

Addsimps [hypnat_minus_zero,hypnat_diff_0_eq_0];

Goalw [hypnat_zero_def] "(m+n = (0::hypnat)) = (m=0 & n=0)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (auto_tac (claset() addIs [FreeUltrafilterNat_subset]
                       addDs [FreeUltrafilterNat_Int],
              simpset() addsimps [hypnat_add] ));
qed "hypnat_add_is_0";

AddIffs [hypnat_add_is_0];

Goal "!!i::hypnat. i-j-k = i - (j+k)";
by (res_inst_tac [("z","i")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","j")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","k")] eq_Abs_hypnat 1);
by (asm_full_simp_tac (simpset() addsimps 
    [hypnat_minus,hypnat_add,diff_diff_left]) 1);
qed "hypnat_diff_diff_left";

Goal "!!i::hypnat. i-j-k = i-k-j";
by (simp_tac (simpset() addsimps 
    [hypnat_diff_diff_left, hypnat_add_commute]) 1);
qed "hypnat_diff_commute";

Goal "!!n::hypnat. (n+m) - n = m";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (asm_full_simp_tac (simpset() addsimps [hypnat_minus,hypnat_add]) 1);
qed "hypnat_diff_add_inverse";
Addsimps [hypnat_diff_add_inverse];

Goal "!!n::hypnat.(m+n) - n = m";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (asm_full_simp_tac (simpset() addsimps [hypnat_minus,hypnat_add]) 1);
qed "hypnat_diff_add_inverse2";
Addsimps [hypnat_diff_add_inverse2];

Goal "!!k::hypnat. (k+m) - (k+n) = m - n";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","k")] eq_Abs_hypnat 1);
by (asm_full_simp_tac (simpset() addsimps [hypnat_minus,hypnat_add]) 1);
qed "hypnat_diff_cancel";
Addsimps [hypnat_diff_cancel];

Goal "!!m::hypnat. (m+k) - (n+k) = m - n";
val hypnat_add_commute_k = read_instantiate [("w","k")] hypnat_add_commute;
by (asm_simp_tac (simpset() addsimps ([hypnat_add_commute_k])) 1);
qed "hypnat_diff_cancel2";
Addsimps [hypnat_diff_cancel2];

Goalw [hypnat_zero_def] "!!n::hypnat. n - (n+m) = (0::hypnat)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (asm_full_simp_tac (simpset() addsimps [hypnat_minus,hypnat_add]) 1);
qed "hypnat_diff_add_0";
Addsimps [hypnat_diff_add_0];

(*-----------------------------------------------------------
   Multiplication for hyper naturals: hypnat_mult
 -----------------------------------------------------------*)
Goalw [congruent2_def]
    "congruent2 hypnatrel (%X Y. hypnatrel``{%n. X n * Y n})";
by Safe_tac;
by (ALLGOALS(Fuf_tac));
qed "hypnat_mult_congruent2";

Goalw [hypnat_mult_def]
  "Abs_hypnat(hypnatrel``{%n. X n}) * Abs_hypnat(hypnatrel``{%n. Y n}) = \
\  Abs_hypnat(hypnatrel``{%n. X n * Y n})";
by (asm_simp_tac
    (simpset() addsimps [[equiv_hypnatrel,hypnat_mult_congruent2] MRS
     UN_equiv_class2]) 1);
qed "hypnat_mult";

Goal "(z::hypnat) * w = w * z";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","w")] eq_Abs_hypnat 1);
by (asm_simp_tac (simpset() addsimps ([hypnat_mult] @ mult_ac)) 1);
qed "hypnat_mult_commute";

Goal "((z1::hypnat) * z2) * z3 = z1 * (z2 * z3)";
by (res_inst_tac [("z","z1")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","z2")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","z3")] eq_Abs_hypnat 1);
by (asm_simp_tac (simpset() addsimps [hypnat_mult,mult_assoc]) 1);
qed "hypnat_mult_assoc";


Goal "(z1::hypnat) * (z2 * z3) = z2 * (z1 * z3)";
by (rtac (hypnat_mult_commute RS trans) 1);
by (rtac (hypnat_mult_assoc RS trans) 1);
by (rtac (hypnat_mult_commute RS arg_cong) 1);
qed "hypnat_mult_left_commute";

(* hypnat multiplication is an AC operator *)
val hypnat_mult_ac = [hypnat_mult_assoc, hypnat_mult_commute, 
                      hypnat_mult_left_commute];

Goalw [hypnat_one_def] "1hn * z = z";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (asm_full_simp_tac (simpset() addsimps [hypnat_mult]) 1);
qed "hypnat_mult_1";
Addsimps [hypnat_mult_1];

Goal "z * 1hn = z";
by (simp_tac (simpset() addsimps [hypnat_mult_commute]) 1);
qed "hypnat_mult_1_right";
Addsimps [hypnat_mult_1_right];

Goalw [hypnat_zero_def] "(0::hypnat) * z = 0";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (asm_full_simp_tac (simpset() addsimps [hypnat_mult]) 1);
qed "hypnat_mult_0";
Addsimps [hypnat_mult_0];

Goal "z * (0::hypnat) = 0";
by (simp_tac (simpset() addsimps [hypnat_mult_commute]) 1);
qed "hypnat_mult_0_right";
Addsimps [hypnat_mult_0_right];

Goal "!!m::hypnat. (m - n) * k = (m * k) - (n * k)";
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","k")] eq_Abs_hypnat 1);
by (asm_simp_tac (simpset() addsimps [hypnat_mult,
    hypnat_minus,diff_mult_distrib]) 1);
qed "hypnat_diff_mult_distrib" ;

Goal "!!m::hypnat. k * (m - n) = (k * m) - (k * n)";
val hypnat_mult_commute_k = read_instantiate [("z","k")] hypnat_mult_commute;
by (simp_tac (simpset() addsimps [hypnat_diff_mult_distrib, 
                                  hypnat_mult_commute_k]) 1);
qed "hypnat_diff_mult_distrib2" ;

(*--------------------------
    A Few more theorems
 -------------------------*)

Goal "(z::hypnat) + v = z' + v' ==> z + (v + w) = z' + (v' + w)";
by (asm_simp_tac (simpset() addsimps [hypnat_add_assoc RS sym]) 1);
qed "hypnat_add_assoc_cong";

Goal "(z::hypnat) + (v + w) = v + (z + w)";
by (REPEAT (ares_tac [hypnat_add_commute RS hypnat_add_assoc_cong] 1));
qed "hypnat_add_assoc_swap";

Goal "((z1::hypnat) + z2) * w = (z1 * w) + (z2 * w)";
by (res_inst_tac [("z","z1")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","z2")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","w")] eq_Abs_hypnat 1);
by (asm_simp_tac (simpset() addsimps [hypnat_mult,hypnat_add,
                                      add_mult_distrib]) 1);
qed "hypnat_add_mult_distrib";
Addsimps [hypnat_add_mult_distrib];

val hypnat_mult_commute'= read_instantiate [("z","w")] hypnat_mult_commute;

Goal "(w::hypnat) * (z1 + z2) = (w * z1) + (w * z2)";
by (simp_tac (simpset() addsimps [hypnat_mult_commute']) 1);
qed "hypnat_add_mult_distrib2";
Addsimps [hypnat_add_mult_distrib2];

(*** (hypnat) one and zero are distinct ***)
Goalw [hypnat_zero_def,hypnat_one_def] "(0::hypnat) ~= 1hn";
by Auto_tac;
qed "hypnat_zero_not_eq_one";
Addsimps [hypnat_zero_not_eq_one];
Addsimps [hypnat_zero_not_eq_one RS not_sym];

Goalw [hypnat_zero_def] "(m*n = (0::hypnat)) = (m=0 | n=0)";
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset() addSDs [FreeUltrafilterNat_Compl_mem],
    simpset() addsimps [hypnat_mult]));
by (ALLGOALS(Fuf_tac));
qed "hypnat_mult_is_0";
Addsimps [hypnat_mult_is_0];

(*------------------------------------------------------------------
                   Theorems for ordering 
 ------------------------------------------------------------------*)

(* prove introduction and elimination rules for hypnat_less *)

Goalw [hypnat_less_def]
 "P < (Q::hypnat) = (EX X Y. X : Rep_hypnat(P) & \
\                             Y : Rep_hypnat(Q) & \
\                             {n. X n < Y n} : FreeUltrafilterNat)";
by (Fast_tac 1);
qed "hypnat_less_iff";

Goalw [hypnat_less_def]
 "[| {n. X n < Y n} : FreeUltrafilterNat; \
\         X : Rep_hypnat(P); \
\         Y : Rep_hypnat(Q) |] ==> P < (Q::hypnat)";
by (Fast_tac 1);
qed "hypnat_lessI";

Goalw [hypnat_less_def]
     "!! R1. [| R1 < (R2::hypnat); \
\         !!X Y. {n. X n < Y n} : FreeUltrafilterNat ==> P; \
\         !!X. X : Rep_hypnat(R1) ==> P; \ 
\         !!Y. Y : Rep_hypnat(R2) ==> P |] \
\     ==> P";
by Auto_tac;
qed "hypnat_lessE";

Goalw [hypnat_less_def]
 "R1 < (R2::hypnat) ==> (EX X Y. {n. X n < Y n} : FreeUltrafilterNat & \
\                                  X : Rep_hypnat(R1) & \
\                                  Y : Rep_hypnat(R2))";
by (Fast_tac 1);
qed "hypnat_lessD";

Goal "~ (R::hypnat) < R";
by (res_inst_tac [("z","R")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hypnat_less_def]));
by (Fuf_empty_tac 1);
qed "hypnat_less_not_refl";
Addsimps [hypnat_less_not_refl];

bind_thm("hypnat_less_irrefl",hypnat_less_not_refl RS notE);

Goalw [hypnat_less_def,hypnat_zero_def] "~ n<(0::hypnat)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by Auto_tac;
by (Fuf_empty_tac 1);
qed "hypnat_not_less0";
AddIffs [hypnat_not_less0];

(* n<(0::hypnat) ==> R *)
bind_thm ("hypnat_less_zeroE", hypnat_not_less0 RS notE);

Goalw [hypnat_less_def,hypnat_zero_def,hypnat_one_def]
      "(n<1hn) = (n=0)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset() addSIs [exI] addEs 
    [FreeUltrafilterNat_subset],simpset()));
by (Fuf_tac 1);
qed "hypnat_less_one";
AddIffs [hypnat_less_one];

Goal "!!(R1::hypnat). [| R1 < R2; R2 < R3 |] ==> R1 < R3";
by (res_inst_tac [("z","R1")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","R2")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","R3")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hypnat_less_def]));
by (res_inst_tac [("x","X")] exI 1);
by Auto_tac;
by (res_inst_tac [("x","Ya")] exI 1);
by Auto_tac;
by (Fuf_tac 1);
qed "hypnat_less_trans";

Goal "!! (R1::hypnat). [| R1 < R2; R2 < R1 |] ==> P";
by (dtac hypnat_less_trans 1 THEN assume_tac 1);
by (Asm_full_simp_tac 1);
qed "hypnat_less_asym";

(*----- hypnat less iff less a.e -----*)
(* See comments in HYPER for corresponding thm *)

Goalw [hypnat_less_def]
      "(Abs_hypnat(hypnatrel``{%n. X n}) < \
\           Abs_hypnat(hypnatrel``{%n. Y n})) = \
\      ({n. X n < Y n} : FreeUltrafilterNat)";
by (auto_tac (claset() addSIs [lemma_hypnatrel_refl],simpset()));
by (Fuf_tac 1);
qed "hypnat_less";

Goal "~ m<n --> n+(m-n) = (m::hypnat)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps 
    [hypnat_minus,hypnat_add,hypnat_less]));
by (dtac FreeUltrafilterNat_Compl_mem 1);
by (Fuf_tac 1);
qed_spec_mp "hypnat_add_diff_inverse";

Goal "n<=m ==> n+(m-n) = (m::hypnat)";
by (asm_full_simp_tac (simpset() addsimps 
    [hypnat_add_diff_inverse, hypnat_le_def]) 1);
qed "hypnat_le_add_diff_inverse";

Goal "n<=m ==> (m-n)+n = (m::hypnat)";
by (asm_simp_tac (simpset() addsimps [hypnat_le_add_diff_inverse, 
    hypnat_add_commute]) 1);
qed "hypnat_le_add_diff_inverse2";

(*---------------------------------------------------------------------------------
                    Hyper naturals as a linearly ordered field
 ---------------------------------------------------------------------------------*)
Goalw [hypnat_zero_def] 
     "[| (0::hypnat) < x; 0 < y |] ==> 0 < x + y";
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","y")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps
   [hypnat_less_def,hypnat_add]));
by (REPEAT(Step_tac 1));
by (Fuf_tac 1);
qed "hypnat_add_order";

Goalw [hypnat_zero_def] 
      "!!(x::hypnat). [| (0::hypnat) < x; 0 < y |] ==> 0 < x * y";
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","y")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps 
    [hypnat_less_def,hypnat_mult]));
by (REPEAT(Step_tac 1));
by (Fuf_tac 1);
qed "hypnat_mult_order";

(*---------------------------------------------------------------------------------
                   Trichotomy of the hyper naturals
  --------------------------------------------------------------------------------*)
Goalw [hypnatrel_def] "EX x. x: hypnatrel `` {%n. 0}";
by (res_inst_tac [("x","%n. 0")] exI 1);
by (Step_tac 1);
by Auto_tac;
qed "lemma_hypnatrel_0_mem";

(* linearity is actually proved further down! *)
Goalw [hypnat_zero_def, hypnat_less_def]
     "(0::hypnat) <  x | x = 0 | x < 0";
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (Auto_tac );
by (REPEAT(Step_tac 1));
by (REPEAT(dtac FreeUltrafilterNat_Compl_mem 1));
by (Fuf_tac 1);
qed "hypnat_trichotomy";

Goal "!!P. [| (0::hypnat) < x ==> P; \
\             x = 0 ==> P; \
\             x < 0 ==> P |] ==> P";
by (cut_inst_tac [("x","x")] hypnat_trichotomy 1);
by Auto_tac;
qed "hypnat_trichotomyE";

(*----------------------------------------------------------------------------
            More properties of <
 ----------------------------------------------------------------------------*)
Goal "!!(A::hypnat). A < B ==> A + C < B + C";
by (res_inst_tac [("z","A")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","B")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","C")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [hypnat_less_def,hypnat_add]));
by (REPEAT(Step_tac 1));
by (Fuf_tac 1);
qed "hypnat_add_less_mono1";

Goal "!!(A::hypnat). A < B ==> C + A < C + B";
by (auto_tac (claset() addIs [hypnat_add_less_mono1],
              simpset() addsimps [hypnat_add_commute]));
qed "hypnat_add_less_mono2";

Goal "!!k l::hypnat. [|i<j;  k<l |] ==> i + k < j + l";
by (etac (hypnat_add_less_mono1 RS hypnat_less_trans) 1);
by (simp_tac (simpset() addsimps [hypnat_add_commute]) 1);
(*j moves to the end because it is free while k, l are bound*)
by (etac hypnat_add_less_mono1 1);
qed "hypnat_add_less_mono";

(*---------------------------------------
        hypnat_minus_less
 ---------------------------------------*)
Goalw [hypnat_less_def,hypnat_zero_def] 
      "((x::hypnat) < y) = ((0::hypnat) < y - x)";
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","y")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps 
    [hypnat_minus]));
by (REPEAT(Step_tac 1));
by (REPEAT(Step_tac 2));
by (ALLGOALS(fuf_tac (claset() addDs [sym],simpset())));

(*** linearity ***)
Goalw [hypnat_less_def] "(x::hypnat) < y | x = y | y < x";
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","y")] eq_Abs_hypnat 1);
by (Auto_tac );
by (REPEAT(Step_tac 1));
by (REPEAT(dtac FreeUltrafilterNat_Compl_mem 1));
by (Fuf_tac 1);
qed "hypnat_linear";

Goal "!!(x::hypnat). [| x < y ==> P;  x = y ==> P; \
\                       y < x ==> P |] ==> P";
by (cut_inst_tac [("x","x"),("y","y")] hypnat_linear 1);
by Auto_tac;
qed "hypnat_linear_less2";

Goal "((w::hypnat) ~= z) = (w<z | z<w)";
by (cut_facts_tac [hypnat_linear] 1);
by Auto_tac;
qed "hypnat_neq_iff";

(* Axiom 'order_less_le' of class 'order': *)
Goal "(w::hypnat) < z = (w <= z & w ~= z)";
by (simp_tac (simpset() addsimps [hypnat_le_def, hypnat_neq_iff]) 1);
by (blast_tac (claset() addIs [hypnat_less_asym]) 1);
qed "hypnat_less_le";

(*----------------------------------------------------------------------------
                            Properties of <=
 ----------------------------------------------------------------------------*)

(*------ hypnat le iff nat le a.e ------*)
Goalw [hypnat_le_def,le_def]
      "(Abs_hypnat(hypnatrel``{%n. X n}) <= \
\           Abs_hypnat(hypnatrel``{%n. Y n})) = \
\      ({n. X n <= Y n} : FreeUltrafilterNat)";
by (auto_tac (claset() addSDs [FreeUltrafilterNat_Compl_mem],
    simpset() addsimps [hypnat_less]));
by (Fuf_tac 1 THEN Fuf_empty_tac 1);
qed "hypnat_le";

(*---------------------------------------------------------*)
(*---------------------------------------------------------*)

Goalw [hypnat_le_def] "z < w ==> z <= (w::hypnat)";
by (fast_tac (claset() addEs [hypnat_less_asym]) 1);
qed "hypnat_less_imp_le";

Goalw [hypnat_le_def] "!!(x::hypnat). x <= y ==> x < y | x = y";
by (cut_facts_tac [hypnat_linear] 1);
by (fast_tac (claset() addEs [hypnat_less_irrefl,hypnat_less_asym]) 1);
qed "hypnat_le_imp_less_or_eq";

Goalw [hypnat_le_def] "z<w | z=w ==> z <=(w::hypnat)";
by (cut_facts_tac [hypnat_linear] 1);
by (blast_tac (claset() addDs [hypnat_less_irrefl,hypnat_less_asym]) 1);
qed "hypnat_less_or_eq_imp_le";

Goal "(x <= (y::hypnat)) = (x < y | x=y)";
by (REPEAT(ares_tac [iffI, hypnat_less_or_eq_imp_le, 
                     hypnat_le_imp_less_or_eq] 1));
qed "hypnat_le_less";

(* Axiom 'linorder_linear' of class 'linorder': *)
Goal "(z::hypnat) <= w | w <= z";
by (simp_tac (simpset() addsimps [hypnat_le_less]) 1);
by (cut_facts_tac [hypnat_linear] 1);
by (Blast_tac 1);
qed "hypnat_le_linear";

Goal "w <= (w::hypnat)";
by (simp_tac (simpset() addsimps [hypnat_le_less]) 1);
qed "hypnat_le_refl";
Addsimps [hypnat_le_refl];

Goal "[| i <= j; j <= k |] ==> i <= (k::hypnat)";
by (EVERY1 [dtac hypnat_le_imp_less_or_eq, dtac hypnat_le_imp_less_or_eq,
            rtac hypnat_less_or_eq_imp_le, 
            fast_tac (claset() addIs [hypnat_less_trans])]);
qed "hypnat_le_trans";

Goal "[| z <= w; w <= z |] ==> z = (w::hypnat)";
by (EVERY1 [dtac hypnat_le_imp_less_or_eq, dtac hypnat_le_imp_less_or_eq,
            fast_tac (claset() addEs [hypnat_less_irrefl,hypnat_less_asym])]);
qed "hypnat_le_anti_sym";

Goal "[| (0::hypnat) <= x; 0 <= y |] ==> 0 <= x * y";
by (REPEAT(dtac hypnat_le_imp_less_or_eq 1));
by (auto_tac (claset() addIs [hypnat_mult_order, hypnat_less_imp_le],
              simpset() addsimps [hypnat_le_refl]));
qed "hypnat_le_mult_order";

Goalw [hypnat_one_def,hypnat_zero_def,hypnat_less_def] 
      "(0::hypnat) < 1hn";
by (res_inst_tac [("x","%n. 0")] exI 1);
by (res_inst_tac [("x","%n. 1")] exI 1);
by Auto_tac;
qed "hypnat_zero_less_one";

Goal "[| (0::hypnat) <= x; 0 <= y |] ==> 0 <= x + y";
by (REPEAT(dtac hypnat_le_imp_less_or_eq 1));
by (auto_tac (claset() addIs [hypnat_add_order,
    hypnat_less_imp_le],simpset() addsimps [hypnat_le_refl]));
qed "hypnat_le_add_order";

Goal "!!(q1::hypnat). q1 <= q2  ==> x + q1 <= x + q2";
by (dtac hypnat_le_imp_less_or_eq 1);
by (Step_tac 1);
by (auto_tac (claset() addSIs [hypnat_le_refl,
    hypnat_less_imp_le,hypnat_add_less_mono1],
    simpset() addsimps [hypnat_add_commute]));
qed "hypnat_add_le_mono2";

Goal "!!(q1::hypnat). q1 <= q2  ==> q1 + x <= q2 + x";
by (auto_tac (claset() addDs [hypnat_add_le_mono2],
    simpset() addsimps [hypnat_add_commute]));
qed "hypnat_add_le_mono1";

Goal "!!k l::hypnat. [|i<=j;  k<=l |] ==> i + k <= j + l";
by (etac (hypnat_add_le_mono1 RS hypnat_le_trans) 1);
by (simp_tac (simpset() addsimps [hypnat_add_commute]) 1);
(*j moves to the end because it is free while k, l are bound*)
by (etac hypnat_add_le_mono1 1);
qed "hypnat_add_le_mono";

Goalw [hypnat_zero_def]
     "!!x::hypnat. [| (0::hypnat) < z; x < y |] ==> x * z < y * z";
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","y")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps 
    [hypnat_less,hypnat_mult]));
by (Fuf_tac 1);
qed "hypnat_mult_less_mono1";

Goal "!!x::hypnat. [| 0 < z; x < y |] ==> z * x < z * y";
by (auto_tac (claset() addIs [hypnat_mult_less_mono1],
              simpset() addsimps [hypnat_mult_commute]));
qed "hypnat_mult_less_mono2";

Addsimps [hypnat_mult_less_mono2,hypnat_mult_less_mono1];

Goal "(x::hypnat) <= n + x";
by (res_inst_tac [("x","n")] hypnat_trichotomyE 1);
by (auto_tac (claset() addDs [(hypnat_less_imp_le RS
    hypnat_add_le_mono1)],simpset() addsimps [hypnat_le_refl]));
qed "hypnat_add_self_le";
Addsimps [hypnat_add_self_le];

Goal "(x::hypnat) < x + 1hn";
by (cut_facts_tac [hypnat_zero_less_one 
         RS hypnat_add_less_mono2] 1);
by Auto_tac;
qed "hypnat_add_one_self_less";
Addsimps [hypnat_add_one_self_less];

Goalw [hypnat_le_def] "~ x + 1hn <= x";
by (Simp_tac 1);
qed "not_hypnat_add_one_le_self";
Addsimps [not_hypnat_add_one_le_self];

Goal "((0::hypnat) < n) = (1hn <= n)";
by (res_inst_tac [("x","n")] hypnat_trichotomyE 1);
by (auto_tac (claset(),simpset() addsimps [hypnat_le_def]));
qed "hypnat_gt_zero_iff";

Addsimps  [hypnat_le_add_diff_inverse, hypnat_le_add_diff_inverse2,
           hypnat_less_imp_le RS hypnat_le_add_diff_inverse2];

Goal "(0 < n) = (EX m. n = m + 1hn)";
by (Step_tac 1);
by (res_inst_tac [("x","m")] hypnat_trichotomyE 2);
by (rtac hypnat_less_trans 2);
by (res_inst_tac [("x","n - 1hn")] exI 1);
by (auto_tac (claset(),simpset() addsimps 
    [hypnat_gt_zero_iff,hypnat_add_commute]));
qed "hypnat_gt_zero_iff2";

Goalw [hypnat_zero_def] "(0::hypnat) <= n";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (asm_simp_tac (simpset() addsimps [hypnat_le]) 1);
qed "hypnat_le_zero";
Addsimps [hypnat_le_zero];

(*------------------------------------------------------------------
     hypnat_of_nat: properties embedding of naturals in hypernaturals
 -----------------------------------------------------------------*)
    (** hypnat_of_nat preserves field and order properties **)

Goalw [hypnat_of_nat_def] 
      "hypnat_of_nat ((z1::nat) + z2) = \
\      hypnat_of_nat z1 + hypnat_of_nat z2";
by (asm_simp_tac (simpset() addsimps [hypnat_add]) 1);
qed "hypnat_of_nat_add";

Goalw [hypnat_of_nat_def] 
      "hypnat_of_nat ((z1::nat) - z2) = \
\      hypnat_of_nat z1 - hypnat_of_nat z2";
by (asm_simp_tac (simpset() addsimps [hypnat_minus]) 1);
qed "hypnat_of_nat_minus";

Goalw [hypnat_of_nat_def] 
      "hypnat_of_nat (z1 * z2) = hypnat_of_nat z1 * hypnat_of_nat z2";
by (full_simp_tac (simpset() addsimps [hypnat_mult]) 1);
qed "hypnat_of_nat_mult";

Goalw [hypnat_less_def,hypnat_of_nat_def] 
      "(z1 < z2) = (hypnat_of_nat z1 < hypnat_of_nat z2)";
by (auto_tac (claset() addSIs [exI] addIs 
   [FreeUltrafilterNat_all],simpset()));
by (rtac FreeUltrafilterNat_P 1 THEN Fuf_tac 1);
qed "hypnat_of_nat_less_iff";
Addsimps [hypnat_of_nat_less_iff RS sym];

Goalw [hypnat_le_def,le_def] 
      "(z1 <= z2) = (hypnat_of_nat z1 <= hypnat_of_nat z2)";
by Auto_tac;
qed "hypnat_of_nat_le_iff";

Goalw [hypnat_of_nat_def,hypnat_one_def] "hypnat_of_nat  1 = 1hn";
by (Simp_tac 1);
qed "hypnat_of_nat_one";

Goalw [hypnat_of_nat_def,hypnat_zero_def] "hypnat_of_nat  0 = 0";
by (Simp_tac 1);
qed "hypnat_of_nat_zero";

Goal "(hypnat_of_nat  n = 0) = (n = 0)";
by (auto_tac (claset() addIs [FreeUltrafilterNat_P],
    simpset() addsimps [hypnat_of_nat_def,
    hypnat_zero_def]));
qed "hypnat_of_nat_zero_iff";

Goal "(hypnat_of_nat  n ~= 0) = (n ~= 0)";
by (full_simp_tac (simpset() addsimps [hypnat_of_nat_zero_iff]) 1);
qed "hypnat_of_nat_not_zero_iff";

Goalw [hypnat_of_nat_def,hypnat_one_def]
     "hypnat_of_nat (Suc n) = hypnat_of_nat n + 1hn";
by (auto_tac (claset(),simpset() addsimps [hypnat_add]));
qed "hypnat_of_nat_Suc";

(*---------------------------------------------------------------------------------
              Existence of infinite hypernatural number
 ---------------------------------------------------------------------------------*)

Goal "hypnatrel``{%n::nat. n} : hypnat";
by Auto_tac;
qed "hypnat_omega";

Goalw [hypnat_omega_def] "Rep_hypnat(whn) : hypnat";
by (rtac Rep_hypnat 1);
qed "Rep_hypnat_omega";

(* See Hyper.thy for similar argument*)
(* existence of infinite number not corresponding to any natural number *)
(* use assumption that member FreeUltrafilterNat is not finite       *)
(* a few lemmas first *)

Goalw [hypnat_omega_def,hypnat_of_nat_def]
      "~ (EX x. hypnat_of_nat x = whn)";
by (auto_tac (claset() addDs [FreeUltrafilterNat_not_finite], 
              simpset()));
qed "not_ex_hypnat_of_nat_eq_omega";

Goal "hypnat_of_nat x ~= whn";
by (cut_facts_tac [not_ex_hypnat_of_nat_eq_omega] 1);
by Auto_tac;
qed "hypnat_of_nat_not_eq_omega";
Addsimps [hypnat_of_nat_not_eq_omega RS not_sym];

(*-----------------------------------------------------------
    Properties of the set SNat of embedded natural numbers
              (cf. set SReal in NSA.thy/NSA.ML)
 ----------------------------------------------------------*)

(* Infinite hypernatural not in embedded SNat *)
Goalw [SHNat_def] "whn ~: SNat";
by Auto_tac;
qed "SHNAT_omega_not_mem";
Addsimps [SHNAT_omega_not_mem];

(*-----------------------------------------------------------------------
     Closure laws for members of (embedded) set standard naturals SNat
 -----------------------------------------------------------------------*)
Goalw [SHNat_def] 
     "!!x::hypnat. [| x: SNat; y: SNat |] ==> x + y: SNat";
by (Step_tac 1);
by (res_inst_tac [("x","N + Na")] exI 1);
by (simp_tac (simpset() addsimps [hypnat_of_nat_add]) 1);
qed "SHNat_add";

Goalw [SHNat_def] 
     "!!x::hypnat. [| x: SNat; y: SNat |] ==> x - y: SNat";
by (Step_tac 1);
by (res_inst_tac [("x","N - Na")] exI 1);
by (simp_tac (simpset() addsimps [hypnat_of_nat_minus]) 1);
qed "SHNat_minus";

Goalw [SHNat_def] 
     "!!x::hypnat. [| x: SNat; y: SNat |] ==> x * y: SNat";
by (Step_tac 1);
by (res_inst_tac [("x","N * Na")] exI 1);
by (simp_tac (simpset() addsimps [hypnat_of_nat_mult]) 1);
qed "SHNat_mult";

Goal"!!x::hypnat. [| x + y : SNat; y: SNat |] ==> x: SNat";
by (dres_inst_tac [("x","x+y")] SHNat_minus 1);
by Auto_tac;
qed "SHNat_add_cancel";

Goalw [SHNat_def] "hypnat_of_nat x : SNat";
by (Blast_tac 1);
qed "SHNat_hypnat_of_nat";
Addsimps [SHNat_hypnat_of_nat];

Goal "hypnat_of_nat 1 : SNat";
by (Simp_tac 1);
qed "SHNat_hypnat_of_nat_one";

Goal "hypnat_of_nat 0 : SNat";
by (Simp_tac 1);
qed "SHNat_hypnat_of_nat_zero";

Goal "1hn : SNat";
by (simp_tac (simpset() addsimps [SHNat_hypnat_of_nat_one,
    hypnat_of_nat_one RS sym]) 1);
qed "SHNat_one";

Goal "(0::hypnat) : SNat";
by (simp_tac (simpset() addsimps [SHNat_hypnat_of_nat_zero,
                                  hypnat_of_nat_zero RS sym]) 1);
qed "SHNat_zero";

Addsimps [SHNat_hypnat_of_nat_one,SHNat_hypnat_of_nat_zero,
          SHNat_one,SHNat_zero];

Goal "1hn + 1hn : SNat";
by (rtac ([SHNat_one,SHNat_one] MRS SHNat_add) 1);
qed "SHNat_two";

Goalw [SHNat_def] "{x. hypnat_of_nat x : SNat} = (UNIV::nat set)";
by Auto_tac;
qed "SHNat_UNIV_nat";

Goalw [SHNat_def] "(x: SNat) = (EX y. x = hypnat_of_nat  y)";
by Auto_tac;
qed "SHNat_iff";

Goalw [SHNat_def] "hypnat_of_nat `(UNIV::nat set) = SNat";
by Auto_tac;
qed "hypnat_of_nat_image";

Goalw [SHNat_def] "inv hypnat_of_nat `SNat = (UNIV::nat set)";
by Auto_tac;
by (rtac (inj_hypnat_of_nat RS inv_f_f RS subst) 1);
by (Blast_tac 1);
qed "inv_hypnat_of_nat_image";

Goalw [SHNat_def] 
     "[| EX x. x: P; P <= SNat |] ==> EX Q. P = hypnat_of_nat ` Q";
by (Best_tac 1); 
qed "SHNat_hypnat_of_nat_image";

Goalw [SHNat_def] 
      "SNat = hypnat_of_nat ` (UNIV::nat set)";
by Auto_tac;
qed "SHNat_hypnat_of_nat_iff";

Goalw [SHNat_def] "SNat <= (UNIV::hypnat set)";
by Auto_tac;
qed "SHNat_subset_UNIV";

Goal "{n. n <= Suc m} = {n. n <= m} Un {n. n = Suc m}";
by (auto_tac (claset(),simpset() addsimps [le_Suc_eq]));
qed "leSuc_Un_eq";

Goal "finite {n::nat. n <= m}";
by (nat_ind_tac "m" 1);
by (auto_tac (claset(),simpset() addsimps [leSuc_Un_eq]));
qed "finite_nat_le_segment";

Goal "{n::nat. m < n} : FreeUltrafilterNat";
by (cut_inst_tac [("m2","m")] (finite_nat_le_segment RS 
    FreeUltrafilterNat_finite RS FreeUltrafilterNat_Compl_mem) 1);
by (Fuf_tac 1);
qed "lemma_unbounded_set";
Addsimps [lemma_unbounded_set];

Goalw [SHNat_def,hypnat_of_nat_def, hypnat_less_def,hypnat_omega_def] 
     "ALL n: SNat. n < whn";
by (Clarify_tac 1);
by (auto_tac (claset() addSIs [exI],simpset()));
qed "hypnat_omega_gt_SHNat";

Goal "hypnat_of_nat n < whn";
by (cut_facts_tac [hypnat_omega_gt_SHNat] 1);
by (dres_inst_tac [("x","hypnat_of_nat n")] bspec 1);
by Auto_tac;
qed "hypnat_of_nat_less_whn";
Addsimps [hypnat_of_nat_less_whn];

Goal "hypnat_of_nat n <= whn";
by (rtac (hypnat_of_nat_less_whn RS hypnat_less_imp_le) 1);
qed "hypnat_of_nat_le_whn";
Addsimps [hypnat_of_nat_le_whn];

Goal "0 < whn";
by (rtac (hypnat_omega_gt_SHNat RS ballE) 1);
by Auto_tac;
qed "hypnat_zero_less_hypnat_omega";
Addsimps [hypnat_zero_less_hypnat_omega];

Goal "1hn < whn";
by (rtac (hypnat_omega_gt_SHNat RS ballE) 1);
by Auto_tac;
qed "hypnat_one_less_hypnat_omega";
Addsimps [hypnat_one_less_hypnat_omega];

(*--------------------------------------------------------------------------
     Theorems about infinite hypernatural numbers -- HNatInfinite
 -------------------------------------------------------------------------*)
Goalw [HNatInfinite_def,SHNat_def] "whn : HNatInfinite";
by Auto_tac;
qed "HNatInfinite_whn";
Addsimps [HNatInfinite_whn];

Goalw [HNatInfinite_def] "x: SNat ==> x ~: HNatInfinite";
by (Simp_tac 1);
qed "SHNat_not_HNatInfinite";

Goalw [HNatInfinite_def] "x ~: HNatInfinite ==> x: SNat";
by (Asm_full_simp_tac 1);
qed "not_HNatInfinite_SHNat";

Goalw [HNatInfinite_def] "x ~: SNat ==> x: HNatInfinite";
by (Simp_tac 1);
qed "not_SHNat_HNatInfinite";

Goalw [HNatInfinite_def] "x: HNatInfinite ==> x ~: SNat";
by (Asm_full_simp_tac 1);
qed "HNatInfinite_not_SHNat";

Goal "(x: SNat) = (x ~: HNatInfinite)";
by (blast_tac (claset() addSIs [SHNat_not_HNatInfinite,
    not_HNatInfinite_SHNat]) 1);
qed "SHNat_not_HNatInfinite_iff";

Goal "(x ~: SNat) = (x: HNatInfinite)";
by (blast_tac (claset() addSIs [not_SHNat_HNatInfinite,
    HNatInfinite_not_SHNat]) 1);
qed "not_SHNat_HNatInfinite_iff";

Goal "x : SNat | x : HNatInfinite";
by (simp_tac (simpset() addsimps [SHNat_not_HNatInfinite_iff]) 1);
qed "SHNat_HNatInfinite_disj";

(*-------------------------------------------------------------------
   Proof of alternative definition for set of Infinite hypernatural 
   numbers --- HNatInfinite = {N. ALL n: SNat. n < N}
 -------------------------------------------------------------------*)
Goal "!!N (xa::nat=>nat). \
\         (ALL N. {n. xa n ~= N} : FreeUltrafilterNat) ==> \
\         ({n. N < xa n} : FreeUltrafilterNat)";
by (nat_ind_tac "N" 1);
by (dres_inst_tac [("x","0")] spec 1);
by (rtac ccontr 1 THEN dtac FreeUltrafilterNat_Compl_mem 1
    THEN dtac FreeUltrafilterNat_Int 1 THEN assume_tac 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("x","Suc N")] spec 1);
by (fuf_tac (claset() addSDs [Suc_leI],simpset() addsimps 
    [le_eq_less_or_eq]) 1);
qed "HNatInfinite_FreeUltrafilterNat_lemma";

(*** alternative definition ***)
Goalw [HNatInfinite_def,SHNat_def,hypnat_of_nat_def] 
     "HNatInfinite = {N. ALL n:SNat. n < N}";
by (Step_tac 1);
by (dres_inst_tac [("x","Abs_hypnat \
\        (hypnatrel `` {%n. N})")] bspec 2);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hypnat_less_iff]));
by (auto_tac (claset() addSIs [exI] addEs 
    [HNatInfinite_FreeUltrafilterNat_lemma],
    simpset() addsimps [FreeUltrafilterNat_Compl_iff1, 
     CLAIM "- {n. xa n = N} = {n. xa n ~= N}"]));
qed "HNatInfinite_iff";

(*--------------------------------------------------------------------
   Alternative definition for HNatInfinite using Free ultrafilter
 --------------------------------------------------------------------*)
Goal "x : HNatInfinite ==> EX X: Rep_hypnat x. \
\                           ALL u. {n. u < X n}:  FreeUltrafilterNat";
by (auto_tac (claset(),simpset() addsimps [hypnat_less_def,
    HNatInfinite_iff,SHNat_iff,hypnat_of_nat_def]));
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (EVERY[Auto_tac, rtac bexI 1, 
    rtac lemma_hypnatrel_refl 2, Step_tac 1]);
by (dres_inst_tac [("x","hypnat_of_nat u")] bspec 1);
by (Simp_tac 1);
by (auto_tac (claset(),
    simpset() addsimps [hypnat_of_nat_def]));
by (Fuf_tac 1);
qed "HNatInfinite_FreeUltrafilterNat";

Goal "EX X: Rep_hypnat x. ALL u. {n. u < X n}:  FreeUltrafilterNat \
\     ==> x: HNatInfinite";
by (auto_tac (claset(),simpset() addsimps [hypnat_less_def,
    HNatInfinite_iff,SHNat_iff,hypnat_of_nat_def]));
by (rtac exI 1 THEN Auto_tac);
qed "FreeUltrafilterNat_HNatInfinite";

Goal "(x : HNatInfinite) = (EX X: Rep_hypnat x. \
\          ALL u. {n. u < X n}:  FreeUltrafilterNat)";
by (blast_tac (claset() addIs [HNatInfinite_FreeUltrafilterNat,
    FreeUltrafilterNat_HNatInfinite]) 1);
qed "HNatInfinite_FreeUltrafilterNat_iff";

Goal "x : HNatInfinite ==> 1hn < x";
by (auto_tac (claset(),simpset() addsimps [HNatInfinite_iff]));
qed "HNatInfinite_gt_one";
Addsimps [HNatInfinite_gt_one];

Goal "0 ~: HNatInfinite";
by (auto_tac (claset(),simpset() 
    addsimps [HNatInfinite_iff]));
by (dres_inst_tac [("a","1hn")] equals0D 1);
by (Asm_full_simp_tac 1);
qed "zero_not_mem_HNatInfinite";
Addsimps [zero_not_mem_HNatInfinite];

Goal "x : HNatInfinite ==> x ~= 0";
by Auto_tac;
qed "HNatInfinite_not_eq_zero";

Goal "x : HNatInfinite ==> 1hn <= x";
by (blast_tac (claset() addIs [hypnat_less_imp_le,
         HNatInfinite_gt_one]) 1);
qed "HNatInfinite_ge_one";
Addsimps [HNatInfinite_ge_one];

(*--------------------------------------------------
                   Closure Rules
 --------------------------------------------------*)
Goal "[| x: HNatInfinite; y: HNatInfinite |] \
\           ==> x + y: HNatInfinite";
by (auto_tac (claset(),simpset() addsimps [HNatInfinite_iff]));
by (dtac bspec 1 THEN assume_tac 1);
by (dtac (SHNat_zero RSN (2,bspec)) 1);
by (dtac hypnat_add_less_mono 1 THEN assume_tac 1);
by (Asm_full_simp_tac 1);
qed "HNatInfinite_add";

Goal "[| x: HNatInfinite; y: SNat |] ==> x + y: HNatInfinite";
by (rtac ccontr 1 THEN dtac not_HNatInfinite_SHNat 1);
by (dres_inst_tac [("x","x + y")] SHNat_minus 1);
by (auto_tac (claset(),simpset() addsimps 
    [SHNat_not_HNatInfinite_iff]));
qed "HNatInfinite_SHNat_add";

Goal "[| x: HNatInfinite; y: SNat |] ==> x - y: HNatInfinite";
by (rtac ccontr 1 THEN dtac not_HNatInfinite_SHNat 1);
by (dres_inst_tac [("x","x - y")] SHNat_add 1);
by (subgoal_tac "y <= x" 2);
by (auto_tac (claset() addSDs [hypnat_le_add_diff_inverse2],
    simpset() addsimps [not_SHNat_HNatInfinite_iff RS sym]));
by (auto_tac (claset() addSIs [hypnat_less_imp_le],
    simpset() addsimps [not_SHNat_HNatInfinite_iff,HNatInfinite_iff]));
qed "HNatInfinite_SHNat_diff";

Goal "x: HNatInfinite ==> x + 1hn: HNatInfinite";
by (auto_tac (claset() addIs [HNatInfinite_SHNat_add],
              simpset()));
qed "HNatInfinite_add_one";

Goal "x: HNatInfinite ==> x - 1hn: HNatInfinite";
by (rtac ccontr 1 THEN dtac not_HNatInfinite_SHNat 1);
by (dres_inst_tac [("x","x - 1hn"),("y","1hn")] SHNat_add 1);
by (auto_tac (claset(),simpset() addsimps 
    [not_SHNat_HNatInfinite_iff RS sym]));
qed "HNatInfinite_minus_one";

Goal "x : HNatInfinite ==> EX y. x = y + 1hn";
by (res_inst_tac [("x","x - 1hn")] exI 1);
by Auto_tac;
qed "HNatInfinite_is_Suc";

(*---------------------------------------------------------------
       HNat : the hypernaturals embedded in the hyperreals
       Obtained using the NS extension of the naturals
 --------------------------------------------------------------*)
 
Goalw [HNat_def,starset_def, hypreal_of_nat_def,hypreal_of_real_def] 
     "hypreal_of_nat N : HNat";
by Auto_tac;
by (Ultra_tac 1);
by (res_inst_tac [("x","N")] exI 1);
by Auto_tac;  
qed "HNat_hypreal_of_nat";
Addsimps [HNat_hypreal_of_nat];

Goalw [HNat_def,starset_def]
     "[| x: HNat; y: HNat |] ==> x + y: HNat";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSDs [bspec] addIs [lemma_hyprel_refl],
              simpset() addsimps [hypreal_add]));
by (Ultra_tac 1);
by (res_inst_tac [("x","no+noa")] exI 1);
by Auto_tac;
qed "HNat_add";

Goalw [HNat_def,starset_def]
     "[| x: HNat; y: HNat |] ==> x * y: HNat";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSDs [bspec] addIs [lemma_hyprel_refl],
              simpset() addsimps [hypreal_mult]));
by (Ultra_tac 1);
by (res_inst_tac [("x","no*noa")] exI 1);
by Auto_tac;
qed "HNat_mult";

(*---------------------------------------------------------------
    Embedding of the hypernaturals into the hyperreal
 --------------------------------------------------------------*)

Goal "(Ya : hyprel ``{%n. f(n)}) = \
\     ({n. f n = Ya n} : FreeUltrafilterNat)";
by Auto_tac;
qed "lemma_hyprel_FUFN";

Goalw [hypreal_of_hypnat_def]
      "hypreal_of_hypnat (Abs_hypnat(hypnatrel``{%n. X n})) = \
\         Abs_hypreal(hyprel `` {%n. real_of_nat (X n)})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by (auto_tac (claset()
                  addEs [FreeUltrafilterNat_Int RS FreeUltrafilterNat_subset],
              simpset() addsimps [lemma_hyprel_FUFN]));
qed "hypreal_of_hypnat";

Goal "inj(hypreal_of_hypnat)";
by (rtac injI 1);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","y")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_of_hypnat]));
qed "inj_hypreal_of_hypnat";

Goal "(hypreal_of_hypnat n = hypreal_of_hypnat m) = (n = m)";
by (auto_tac (claset(),simpset() addsimps [inj_hypreal_of_hypnat RS injD]));
qed "hypreal_of_hypnat_eq_cancel";
Addsimps [hypreal_of_hypnat_eq_cancel];

Goal "(hypnat_of_nat n = hypnat_of_nat m) = (n = m)";
by (auto_tac (claset() addDs [inj_hypnat_of_nat RS injD],
              simpset()));
qed "hypnat_of_nat_eq_cancel";
Addsimps [hypnat_of_nat_eq_cancel];

Goalw [hypnat_zero_def] 
     "hypreal_of_hypnat 0 = #0";
by (simp_tac (HOL_ss addsimps
             [zero_eq_numeral_0 RS sym, hypreal_zero_def]) 1); 
by (simp_tac (simpset() addsimps [hypreal_of_hypnat, real_of_nat_zero]) 1);
qed "hypreal_of_hypnat_zero";

Goalw [hypnat_one_def] 
     "hypreal_of_hypnat 1hn = #1";
by (simp_tac (HOL_ss addsimps
             [one_eq_numeral_1 RS sym, hypreal_one_def]) 1); 
by (simp_tac (simpset() addsimps [hypreal_of_hypnat, real_of_nat_one]) 1);
qed "hypreal_of_hypnat_one";

Goal "hypreal_of_hypnat (m + n) = hypreal_of_hypnat m + hypreal_of_hypnat n";
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (asm_simp_tac (simpset() addsimps
           [hypreal_of_hypnat, hypreal_add,hypnat_add,real_of_nat_add]) 1);
qed "hypreal_of_hypnat_add";
Addsimps [hypreal_of_hypnat_add];

Goal "hypreal_of_hypnat (m * n) = hypreal_of_hypnat m * hypreal_of_hypnat n";
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (asm_simp_tac (simpset() addsimps
           [hypreal_of_hypnat, hypreal_mult,hypnat_mult,real_of_nat_mult]) 1);
qed "hypreal_of_hypnat_mult";
Addsimps [hypreal_of_hypnat_mult];

Goal "(hypreal_of_hypnat n < hypreal_of_hypnat m) = (n < m)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (asm_simp_tac (simpset() addsimps 
    [hypreal_of_hypnat,hypreal_less,hypnat_less]) 1);
qed "hypreal_of_hypnat_less_iff";
Addsimps [hypreal_of_hypnat_less_iff];

Goal "(hypreal_of_hypnat N = #0) = (N = 0)";
by (simp_tac (simpset() addsimps [hypreal_of_hypnat_zero RS sym]) 1);
qed "hypreal_of_hypnat_eq_zero_iff";
Addsimps [hypreal_of_hypnat_eq_zero_iff];

Goal "ALL n. N <= n ==> N = (0::hypnat)";
by (dres_inst_tac [("x","0")] spec 1);
by (res_inst_tac [("z","N")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hypnat_le,hypnat_zero_def]));
qed "hypnat_eq_zero";
Addsimps [hypnat_eq_zero];

Goal "~ (ALL n. n = (0::hypnat))";
by Auto_tac;
by (res_inst_tac [("x","1hn")] exI 1);
by (Simp_tac 1);
qed "hypnat_not_all_eq_zero";
Addsimps [hypnat_not_all_eq_zero];

Goal "n ~= 0 ==> (n <= 1hn) = (n = 1hn)";
by (auto_tac (claset(), simpset() addsimps [hypnat_le_less]));
qed "hypnat_le_one_eq_one";
Addsimps [hypnat_le_one_eq_one];




