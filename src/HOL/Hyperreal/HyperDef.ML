(*  Title       : HOL/Real/Hyperreal/Hyper.ML
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Ultrapower construction of hyperreals
*) 

(*------------------------------------------------------------------------
             Proof that the set of naturals is not finite
 ------------------------------------------------------------------------*)

(*** based on James' proof that the set of naturals is not finite ***)
Goal "finite (A::nat set) --> (EX n. ALL m. Suc (n + m) ~: A)";
by (rtac impI 1);
by (eres_inst_tac [("F","A")] finite_induct 1);
by (Blast_tac 1 THEN etac exE 1);
by (res_inst_tac [("x","n + x")] exI 1);
by (rtac allI 1 THEN eres_inst_tac [("x","x + m")] allE 1);
by (auto_tac (claset(), simpset() addsimps add_ac));
by (auto_tac (claset(),
	      simpset() addsimps [add_assoc RS sym,
				  less_add_Suc2 RS less_not_refl2]));
qed_spec_mp "finite_exhausts";

Goal "finite (A :: nat set) --> (EX n. n ~:A)";
by (rtac impI 1 THEN dtac finite_exhausts 1);
by (Blast_tac 1);
qed_spec_mp "finite_not_covers";

Goal "~ finite(UNIV:: nat set)";
by (fast_tac (claset() addSDs [finite_exhausts]) 1);
qed "not_finite_nat";

(*------------------------------------------------------------------------
   Existence of free ultrafilter over the naturals and proof of various 
   properties of the FreeUltrafilterNat- an arbitrary free ultrafilter
 ------------------------------------------------------------------------*)

Goal "EX U. U: FreeUltrafilter (UNIV::nat set)";
by (rtac (not_finite_nat RS FreeUltrafilter_Ex) 1);
qed "FreeUltrafilterNat_Ex";

Goalw [FreeUltrafilterNat_def] 
     "FreeUltrafilterNat: FreeUltrafilter(UNIV:: nat set)";
by (rtac (FreeUltrafilterNat_Ex RS exE) 1);
by (rtac someI2 1 THEN ALLGOALS(assume_tac));
qed "FreeUltrafilterNat_mem";
Addsimps [FreeUltrafilterNat_mem];

Goalw [FreeUltrafilterNat_def] "finite x ==> x ~: FreeUltrafilterNat";
by (rtac (FreeUltrafilterNat_Ex RS exE) 1);
by (rtac someI2 1 THEN assume_tac 1);
by (blast_tac (claset() addDs [mem_FreeUltrafiltersetD1]) 1);
qed "FreeUltrafilterNat_finite";

Goal "x: FreeUltrafilterNat ==> ~ finite x";
by (blast_tac (claset() addDs [FreeUltrafilterNat_finite]) 1);
qed "FreeUltrafilterNat_not_finite";

Goalw [FreeUltrafilterNat_def] "{} ~: FreeUltrafilterNat";
by (rtac (FreeUltrafilterNat_Ex RS exE) 1);
by (rtac someI2 1 THEN assume_tac 1);
by (blast_tac (claset() addDs [FreeUltrafilter_Ultrafilter,
			       Ultrafilter_Filter,Filter_empty_not_mem]) 1);
qed "FreeUltrafilterNat_empty";
Addsimps [FreeUltrafilterNat_empty];

Goal "[| X: FreeUltrafilterNat;  Y: FreeUltrafilterNat |]  \
\     ==> X Int Y : FreeUltrafilterNat";
by (cut_facts_tac [FreeUltrafilterNat_mem] 1);
by (blast_tac (claset() addDs [FreeUltrafilter_Ultrafilter,
			       Ultrafilter_Filter,mem_FiltersetD1]) 1);
qed "FreeUltrafilterNat_Int";

Goal "[| X: FreeUltrafilterNat;  X <= Y |] \
\     ==> Y : FreeUltrafilterNat";
by (cut_facts_tac [FreeUltrafilterNat_mem] 1);
by (blast_tac (claset() addDs [FreeUltrafilter_Ultrafilter,
			       Ultrafilter_Filter,mem_FiltersetD2]) 1);
qed "FreeUltrafilterNat_subset";

Goal "X: FreeUltrafilterNat ==> -X ~: FreeUltrafilterNat";
by (Step_tac 1);
by (dtac FreeUltrafilterNat_Int 1 THEN assume_tac 1);
by Auto_tac;
qed "FreeUltrafilterNat_Compl";

Goal "X~: FreeUltrafilterNat ==> -X : FreeUltrafilterNat";
by (cut_facts_tac [FreeUltrafilterNat_mem RS (FreeUltrafilter_iff RS iffD1)] 1);
by (Step_tac 1 THEN dres_inst_tac [("x","X")] bspec 1);
by (auto_tac (claset(), simpset() addsimps [UNIV_diff_Compl]));
qed "FreeUltrafilterNat_Compl_mem";

Goal "(X ~: FreeUltrafilterNat) = (-X: FreeUltrafilterNat)";
by (blast_tac (claset() addDs [FreeUltrafilterNat_Compl,
			       FreeUltrafilterNat_Compl_mem]) 1);
qed "FreeUltrafilterNat_Compl_iff1";

Goal "(X: FreeUltrafilterNat) = (-X ~: FreeUltrafilterNat)";
by (auto_tac (claset(),
	      simpset() addsimps [FreeUltrafilterNat_Compl_iff1 RS sym]));
qed "FreeUltrafilterNat_Compl_iff2";

Goal "(UNIV::nat set) : FreeUltrafilterNat";
by (rtac (FreeUltrafilterNat_mem RS FreeUltrafilter_Ultrafilter RS 
          Ultrafilter_Filter RS mem_FiltersetD4) 1);
qed "FreeUltrafilterNat_UNIV";
Addsimps [FreeUltrafilterNat_UNIV];

Goal "UNIV : FreeUltrafilterNat";
by Auto_tac;
qed "FreeUltrafilterNat_Nat_set";
Addsimps [FreeUltrafilterNat_Nat_set];

Goal "{n. P(n) = P(n)} : FreeUltrafilterNat";
by (Simp_tac 1);
qed "FreeUltrafilterNat_Nat_set_refl";
AddIs [FreeUltrafilterNat_Nat_set_refl];

Goal "{n::nat. P} : FreeUltrafilterNat ==> P";
by (rtac ccontr 1);
by (rotate_tac 1 1);
by (Asm_full_simp_tac 1);
qed "FreeUltrafilterNat_P";

Goal "{n. P(n)} : FreeUltrafilterNat ==> EX n. P(n)";
by (rtac ccontr 1 THEN rotate_tac 1 1);
by (Asm_full_simp_tac 1);
qed "FreeUltrafilterNat_Ex_P";

Goal "ALL n. P(n) ==> {n. P(n)} : FreeUltrafilterNat";
by (auto_tac (claset() addIs [FreeUltrafilterNat_Nat_set], simpset()));
qed "FreeUltrafilterNat_all";

(*-------------------------------------------------------
     Define and use Ultrafilter tactics
 -------------------------------------------------------*)
use "fuf.ML";

(*-------------------------------------------------------
  Now prove one further property of our free ultrafilter
 -------------------------------------------------------*)
Goal "X Un Y: FreeUltrafilterNat \
\     ==> X: FreeUltrafilterNat | Y: FreeUltrafilterNat";
by Auto_tac;
by (Ultra_tac 1);
qed "FreeUltrafilterNat_Un";

(*-------------------------------------------------------
   Properties of hyprel
 -------------------------------------------------------*)

(** Proving that hyprel is an equivalence relation **)
(** Natural deduction for hyprel **)

Goalw [hyprel_def]
   "((X,Y): hyprel) = ({n. X n = Y n}: FreeUltrafilterNat)";
by (Fast_tac 1);
qed "hyprel_iff";

Goalw [hyprel_def] 
     "{n. X n = Y n}: FreeUltrafilterNat  ==> (X,Y): hyprel";
by (Fast_tac 1);
qed "hyprelI";

Goalw [hyprel_def]
  "p: hyprel --> (EX X Y. \
\                 p = (X,Y) & {n. X n = Y n} : FreeUltrafilterNat)";
by (Fast_tac 1);
qed "hyprelE_lemma";

val [major,minor] = goal (the_context ())
  "[| p: hyprel;  \
\     !!X Y. [| p = (X,Y); {n. X n = Y n}: FreeUltrafilterNat\
\                    |] ==> Q |] ==> Q";
by (cut_facts_tac [major RS (hyprelE_lemma RS mp)] 1);
by (REPEAT (eresolve_tac [asm_rl,exE,conjE,minor] 1));
qed "hyprelE";

AddSIs [hyprelI];
AddSEs [hyprelE];

Goalw [hyprel_def] "(x,x): hyprel";
by (auto_tac (claset(),
              simpset() addsimps [FreeUltrafilterNat_Nat_set]));
qed "hyprel_refl";

Goal "{n. X n = Y n} = {n. Y n = X n}";
by Auto_tac;
qed "lemma_perm";

Goalw [hyprel_def] "(x,y): hyprel --> (y,x):hyprel";
by (auto_tac (claset() addIs [lemma_perm RS subst], simpset()));
qed_spec_mp "hyprel_sym";

Goalw [hyprel_def]
      "(x,y): hyprel --> (y,z):hyprel --> (x,z):hyprel";
by Auto_tac;
by (Ultra_tac 1);
qed_spec_mp "hyprel_trans";

Goalw [equiv_def, refl_def, sym_def, trans_def] "equiv UNIV hyprel";
by (auto_tac (claset() addSIs [hyprel_refl] 
                       addSEs [hyprel_sym,hyprel_trans] 
                       delrules [hyprelI,hyprelE],
	      simpset() addsimps [FreeUltrafilterNat_Nat_set]));
qed "equiv_hyprel";

(* (hyprel `` {x} = hyprel `` {y}) = ((x,y) : hyprel) *)
bind_thm ("equiv_hyprel_iff",
    	  [equiv_hyprel, UNIV_I, UNIV_I] MRS eq_equiv_class_iff);

Goalw  [hypreal_def,hyprel_def,quotient_def] "hyprel``{x}:hypreal";
by (Blast_tac 1);
qed "hyprel_in_hypreal";

Goal "inj_on Abs_hypreal hypreal";
by (rtac inj_on_inverseI 1);
by (etac Abs_hypreal_inverse 1);
qed "inj_on_Abs_hypreal";

Addsimps [equiv_hyprel_iff,inj_on_Abs_hypreal RS inj_on_iff,
          hyprel_iff, hyprel_in_hypreal, Abs_hypreal_inverse];

Addsimps [equiv_hyprel RS eq_equiv_class_iff];
bind_thm ("eq_hyprelD", equiv_hyprel RSN (2,eq_equiv_class));

Goal "inj(Rep_hypreal)";
by (rtac inj_inverseI 1);
by (rtac Rep_hypreal_inverse 1);
qed "inj_Rep_hypreal";

Goalw [hyprel_def] "x: hyprel `` {x}";
by (Step_tac 1);
by (auto_tac (claset() addSIs [FreeUltrafilterNat_Nat_set], simpset()));
qed "lemma_hyprel_refl";

Addsimps [lemma_hyprel_refl];

Goalw [hypreal_def] "{} ~: hypreal";
by (auto_tac (claset() addSEs [quotientE], simpset()));
qed "hypreal_empty_not_mem";

Addsimps [hypreal_empty_not_mem];

Goal "Rep_hypreal x ~= {}";
by (cut_inst_tac [("x","x")] Rep_hypreal 1);
by Auto_tac;
qed "Rep_hypreal_nonempty";

Addsimps [Rep_hypreal_nonempty];

(*------------------------------------------------------------------------
   hypreal_of_real: the injection from real to hypreal
 ------------------------------------------------------------------------*)

Goal "inj(hypreal_of_real)";
by (rtac injI 1);
by (rewtac hypreal_of_real_def);
by (dtac (inj_on_Abs_hypreal RS inj_onD) 1);
by (REPEAT (rtac hyprel_in_hypreal 1));
by (dtac eq_equiv_class 1);
by (rtac equiv_hyprel 1);
by (Fast_tac 1);
by (rtac ccontr 1 THEN rotate_tac 1 1);
by Auto_tac;
qed "inj_hypreal_of_real";

val [prem] = goal (the_context ())
    "(!!x y. z = Abs_hypreal(hyprel``{x}) ==> P) ==> P";
by (res_inst_tac [("x1","z")] 
    (rewrite_rule [hypreal_def] Rep_hypreal RS quotientE) 1);
by (dres_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by (res_inst_tac [("x","x")] prem 1);
by (asm_full_simp_tac (simpset() addsimps [Rep_hypreal_inverse]) 1);
qed "eq_Abs_hypreal";

(**** hypreal_minus: additive inverse on hypreal ****)

Goalw [congruent_def]
  "congruent hyprel (%X. hyprel``{%n. - (X n)})";
by Safe_tac;
by (ALLGOALS Ultra_tac);
qed "hypreal_minus_congruent";

Goalw [hypreal_minus_def]
   "- (Abs_hypreal(hyprel``{%n. X n})) = Abs_hypreal(hyprel `` {%n. -(X n)})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by (simp_tac (simpset() addsimps 
      [hyprel_in_hypreal RS Abs_hypreal_inverse,
       [equiv_hyprel, hypreal_minus_congruent] MRS UN_equiv_class]) 1);
qed "hypreal_minus";

Goal "- (- z) = (z::hypreal)";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (asm_simp_tac (simpset() addsimps [hypreal_minus]) 1);
qed "hypreal_minus_minus";

Addsimps [hypreal_minus_minus];

Goal "inj(%r::hypreal. -r)";
by (rtac injI 1);
by (dres_inst_tac [("f","uminus")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_minus_minus]) 1);
qed "inj_hypreal_minus";

Goalw [hypreal_zero_def] "- 0 = (0::hypreal)";
by (simp_tac (simpset() addsimps [hypreal_minus]) 1);
qed "hypreal_minus_zero";
Addsimps [hypreal_minus_zero];

Goal "(-x = 0) = (x = (0::hypreal))"; 
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
       simpset() addsimps [hypreal_zero_def, hypreal_minus, eq_commute] @ 
                          real_add_ac));
qed "hypreal_minus_zero_iff";

Addsimps [hypreal_minus_zero_iff];


(**** hyperreal addition: hypreal_add  ****)

Goalw [congruent2_def]
    "congruent2 hyprel (%X Y. hyprel``{%n. X n + Y n})";
by Safe_tac;
by (ALLGOALS(Ultra_tac));
qed "hypreal_add_congruent2";

Goalw [hypreal_add_def]
  "Abs_hypreal(hyprel``{%n. X n}) + Abs_hypreal(hyprel``{%n. Y n}) = \
\  Abs_hypreal(hyprel``{%n. X n + Y n})";
by (simp_tac (simpset() addsimps 
         [[equiv_hyprel, hypreal_add_congruent2] MRS UN_equiv_class2]) 1);
qed "hypreal_add";

Goal "Abs_hypreal(hyprel``{%n. X n}) - Abs_hypreal(hyprel``{%n. Y n}) = \
\     Abs_hypreal(hyprel``{%n. X n - Y n})";
by (simp_tac (simpset() addsimps 
         [hypreal_diff_def, hypreal_minus,hypreal_add]) 1);
qed "hypreal_diff";

Goal "(z::hypreal) + w = w + z";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","w")] eq_Abs_hypreal 1);
by (asm_simp_tac (simpset() addsimps (real_add_ac @ [hypreal_add])) 1);
qed "hypreal_add_commute";

Goal "((z1::hypreal) + z2) + z3 = z1 + (z2 + z3)";
by (res_inst_tac [("z","z1")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","z2")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","z3")] eq_Abs_hypreal 1);
by (asm_simp_tac (simpset() addsimps [hypreal_add, real_add_assoc]) 1);
qed "hypreal_add_assoc";

(*For AC rewriting*)
Goal "(x::hypreal)+(y+z)=y+(x+z)";
by (rtac (hypreal_add_commute RS trans) 1);
by (rtac (hypreal_add_assoc RS trans) 1);
by (rtac (hypreal_add_commute RS arg_cong) 1);
qed "hypreal_add_left_commute";

(* hypreal addition is an AC operator *)
bind_thms ("hypreal_add_ac", [hypreal_add_assoc,hypreal_add_commute,
                      hypreal_add_left_commute]);

Goalw [hypreal_zero_def] "(0::hypreal) + z = z";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (asm_full_simp_tac (simpset() addsimps 
    [hypreal_add]) 1);
qed "hypreal_add_zero_left";

Goal "z + (0::hypreal) = z";
by (simp_tac (simpset() addsimps 
    [hypreal_add_zero_left,hypreal_add_commute]) 1);
qed "hypreal_add_zero_right";

Goalw [hypreal_zero_def] "z + -z = (0::hypreal)";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_minus, hypreal_add]) 1);
qed "hypreal_add_minus";

Goal "-z + z = (0::hypreal)";
by (simp_tac (simpset() addsimps [hypreal_add_commute, hypreal_add_minus]) 1);
qed "hypreal_add_minus_left";

Addsimps [hypreal_add_minus,hypreal_add_minus_left,
          hypreal_add_zero_left,hypreal_add_zero_right];

Goal "EX y. (x::hypreal) + y = 0";
by (fast_tac (claset() addIs [hypreal_add_minus]) 1);
qed "hypreal_minus_ex";

Goal "EX! y. (x::hypreal) + y = 0";
by (auto_tac (claset() addIs [hypreal_add_minus], simpset()));
by (dres_inst_tac [("f","%x. ya+x")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_add_assoc RS sym]) 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_add_commute]) 1);
qed "hypreal_minus_ex1";

Goal "EX! y. y + (x::hypreal) = 0";
by (auto_tac (claset() addIs [hypreal_add_minus_left], simpset()));
by (dres_inst_tac [("f","%x. x+ya")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_add_assoc]) 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_add_commute]) 1);
qed "hypreal_minus_left_ex1";

Goal "x + y = (0::hypreal) ==> x = -y";
by (cut_inst_tac [("z","y")] hypreal_add_minus_left 1);
by (res_inst_tac [("x1","y")] (hypreal_minus_left_ex1 RS ex1E) 1);
by (Blast_tac 1);
qed "hypreal_add_minus_eq_minus";

Goal "EX y::hypreal. x = -y";
by (cut_inst_tac [("x","x")] hypreal_minus_ex 1);
by (etac exE 1 THEN dtac hypreal_add_minus_eq_minus 1);
by (Fast_tac 1);
qed "hypreal_as_add_inverse_ex";

Goal "-(x + (y::hypreal)) = -x + -y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
              simpset() addsimps [hypreal_minus, hypreal_add,
                                  real_minus_add_distrib]));
qed "hypreal_minus_add_distrib";
Addsimps [hypreal_minus_add_distrib];

Goal "-(y + -(x::hypreal)) = x + -y";
by (simp_tac (simpset() addsimps [hypreal_add_commute]) 1);
qed "hypreal_minus_distrib1";

Goal "(x + - (y::hypreal)) + (y + - z) = x + -z";
by (res_inst_tac [("w1","y")] (hypreal_add_commute RS subst) 1);
by (simp_tac (simpset() addsimps [hypreal_add_left_commute,
                                  hypreal_add_assoc]) 1);
by (simp_tac (simpset() addsimps [hypreal_add_commute]) 1);
qed "hypreal_add_minus_cancel1";

Goal "((x::hypreal) + y = x + z) = (y = z)";
by (Step_tac 1);
by (dres_inst_tac [("f","%t.-x + t")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_add_assoc RS sym]) 1);
qed "hypreal_add_left_cancel";

Goal "z + (x + (y + -z)) = x + (y::hypreal)";
by (simp_tac (simpset() addsimps hypreal_add_ac) 1);
qed "hypreal_add_minus_cancel2";
Addsimps [hypreal_add_minus_cancel2];

Goal "y + -(x + y) = -(x::hypreal)";
by (Full_simp_tac 1);
by (rtac (hypreal_add_left_commute RS subst) 1);
by (Full_simp_tac 1);
qed "hypreal_add_minus_cancel";
Addsimps [hypreal_add_minus_cancel];

Goal "y + -(y + x) = -(x::hypreal)";
by (simp_tac (simpset() addsimps [hypreal_add_assoc RS sym]) 1);
qed "hypreal_add_minus_cancelc";
Addsimps [hypreal_add_minus_cancelc];

Goal "(z + -x) + (y + -z) = (y + -(x::hypreal))";
by (full_simp_tac
    (simpset() addsimps [hypreal_minus_add_distrib RS sym, 
                         hypreal_add_left_cancel] @ hypreal_add_ac 
               delsimps [hypreal_minus_add_distrib]) 1); 
qed "hypreal_add_minus_cancel3";
Addsimps [hypreal_add_minus_cancel3];

Goal "(y + (x::hypreal)= z + x) = (y = z)";
by (simp_tac (simpset() addsimps [hypreal_add_commute,
                                  hypreal_add_left_cancel]) 1);
qed "hypreal_add_right_cancel";

Goal "z + (y + -z) = (y::hypreal)";
by (simp_tac (simpset() addsimps hypreal_add_ac) 1);
qed "hypreal_add_minus_cancel4";
Addsimps [hypreal_add_minus_cancel4];

Goal "z + (w + (x + (-z + y))) = w + x + (y::hypreal)";
by (simp_tac (simpset() addsimps hypreal_add_ac) 1);
qed "hypreal_add_minus_cancel5";
Addsimps [hypreal_add_minus_cancel5];

Goal "z + ((- z) + w) = (w::hypreal)";
by (simp_tac (simpset() addsimps [hypreal_add_assoc RS sym]) 1);
qed "hypreal_add_minus_cancelA";

Goal "(-z) + (z + w) = (w::hypreal)";
by (simp_tac (simpset() addsimps [hypreal_add_assoc RS sym]) 1);
qed "hypreal_minus_add_cancelA";

Addsimps [hypreal_add_minus_cancelA, hypreal_minus_add_cancelA];

(**** hyperreal multiplication: hypreal_mult  ****)

Goalw [congruent2_def]
    "congruent2 hyprel (%X Y. hyprel``{%n. X n * Y n})";
by Safe_tac;
by (ALLGOALS(Ultra_tac));
qed "hypreal_mult_congruent2";

Goalw [hypreal_mult_def]
  "Abs_hypreal(hyprel``{%n. X n}) * Abs_hypreal(hyprel``{%n. Y n}) = \
\  Abs_hypreal(hyprel``{%n. X n * Y n})";
by (simp_tac (simpset() addsimps 
      [[equiv_hyprel, hypreal_mult_congruent2] MRS UN_equiv_class2]) 1);
qed "hypreal_mult";

Goal "(z::hypreal) * w = w * z";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","w")] eq_Abs_hypreal 1);
by (asm_simp_tac (simpset() addsimps ([hypreal_mult] @ real_mult_ac)) 1);
qed "hypreal_mult_commute";

Goal "((z1::hypreal) * z2) * z3 = z1 * (z2 * z3)";
by (res_inst_tac [("z","z1")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","z2")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","z3")] eq_Abs_hypreal 1);
by (asm_simp_tac (simpset() addsimps [hypreal_mult,real_mult_assoc]) 1);
qed "hypreal_mult_assoc";

qed_goal "hypreal_mult_left_commute" (the_context ())
    "(z1::hypreal) * (z2 * z3) = z2 * (z1 * z3)"
 (fn _ => [rtac (hypreal_mult_commute RS trans) 1, 
           rtac (hypreal_mult_assoc RS trans) 1,
           rtac (hypreal_mult_commute RS arg_cong) 1]);

(* hypreal multiplication is an AC operator *)
bind_thms ("hypreal_mult_ac", [hypreal_mult_assoc, hypreal_mult_commute, 
                       hypreal_mult_left_commute]);

Goalw [hypreal_one_def] "(1::hypreal) * z = z";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_mult]) 1);
qed "hypreal_mult_1";

Goal "z * (1::hypreal) = z";
by (simp_tac (simpset() addsimps [hypreal_mult_commute,
    hypreal_mult_1]) 1);
qed "hypreal_mult_1_right";

Goalw [hypreal_zero_def] "0 * z = (0::hypreal)";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_mult,real_mult_0]) 1);
qed "hypreal_mult_0";

Goal "z * 0 = (0::hypreal)";
by (simp_tac (simpset() addsimps [hypreal_mult_commute, hypreal_mult_0]) 1);
qed "hypreal_mult_0_right";

Addsimps [hypreal_mult_0,hypreal_mult_0_right];

Goal "-(x * y) = -x * (y::hypreal)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
	      simpset() addsimps [hypreal_minus, hypreal_mult] 
                                 @ real_mult_ac @ real_add_ac));
qed "hypreal_minus_mult_eq1";

Goal "-(x * y) = (x::hypreal) * -y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_minus, hypreal_mult] 
                                           @ real_mult_ac @ real_add_ac));
qed "hypreal_minus_mult_eq2";

(*Pull negations out*)
Addsimps [hypreal_minus_mult_eq2 RS sym, hypreal_minus_mult_eq1 RS sym];

Goal "-x*y = (x::hypreal)*-y";
by Auto_tac;
qed "hypreal_minus_mult_commute";

(*-----------------------------------------------------------------------------
    A few more theorems
 ----------------------------------------------------------------------------*)
Goal "(z::hypreal) + v = z' + v' ==> z + (v + w) = z' + (v' + w)";
by (asm_simp_tac (simpset() addsimps [hypreal_add_assoc RS sym]) 1);
qed "hypreal_add_assoc_cong";

Goal "(z::hypreal) + (v + w) = v + (z + w)";
by (REPEAT (ares_tac [hypreal_add_commute RS hypreal_add_assoc_cong] 1));
qed "hypreal_add_assoc_swap";

Goal "((z1::hypreal) + z2) * w = (z1 * w) + (z2 * w)";
by (res_inst_tac [("z","z1")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","z2")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","w")] eq_Abs_hypreal 1);
by (asm_simp_tac (simpset() addsimps [hypreal_mult,hypreal_add,
     real_add_mult_distrib]) 1);
qed "hypreal_add_mult_distrib";

val hypreal_mult_commute'= read_instantiate [("z","w")] hypreal_mult_commute;

Goal "(w::hypreal) * (z1 + z2) = (w * z1) + (w * z2)";
by (simp_tac (simpset() addsimps [hypreal_mult_commute',hypreal_add_mult_distrib]) 1);
qed "hypreal_add_mult_distrib2";

bind_thms ("hypreal_mult_simps", [hypreal_mult_1, hypreal_mult_1_right]);
Addsimps hypreal_mult_simps;

(* 07/00 *)

Goalw [hypreal_diff_def] "((z1::hypreal) - z2) * w = (z1 * w) - (z2 * w)";
by (simp_tac (simpset() addsimps [hypreal_add_mult_distrib]) 1);
qed "hypreal_diff_mult_distrib";

Goal "(w::hypreal) * (z1 - z2) = (w * z1) - (w * z2)";
by (simp_tac (simpset() addsimps [hypreal_mult_commute', 
				  hypreal_diff_mult_distrib]) 1);
qed "hypreal_diff_mult_distrib2";

(*** one and zero are distinct ***)
Goalw [hypreal_zero_def,hypreal_one_def] "0 ~= (1::hypreal)";
by (auto_tac (claset(), simpset() addsimps [real_zero_not_eq_one]));
qed "hypreal_zero_not_eq_one";


(**** multiplicative inverse on hypreal ****)

Goalw [congruent_def]
  "congruent hyprel (%X. hyprel``{%n. if X n = Numeral0 then Numeral0 else inverse(X n)})";
by (Auto_tac THEN Ultra_tac 1);
qed "hypreal_inverse_congruent";

Goalw [hypreal_inverse_def]
      "inverse (Abs_hypreal(hyprel``{%n. X n})) = \
\      Abs_hypreal(hyprel `` {%n. if X n = Numeral0 then Numeral0 else inverse(X n)})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by (simp_tac (simpset() addsimps 
   [hyprel_in_hypreal RS Abs_hypreal_inverse,
    [equiv_hyprel, hypreal_inverse_congruent] MRS UN_equiv_class]) 1);
qed "hypreal_inverse";

Goal "inverse 0 = (0::hypreal)";
by (simp_tac (simpset() addsimps [hypreal_inverse, hypreal_zero_def]) 1);
qed "HYPREAL_INVERSE_ZERO";

Goal "a / (0::hypreal) = 0";
by (simp_tac
    (simpset() addsimps [hypreal_divide_def, HYPREAL_INVERSE_ZERO]) 1);
qed "HYPREAL_DIVISION_BY_ZERO";  (*NOT for adding to default simpset*)

fun hypreal_div_undefined_case_tac s i =
  case_tac s i THEN 
  asm_simp_tac 
       (simpset() addsimps [HYPREAL_DIVISION_BY_ZERO, HYPREAL_INVERSE_ZERO]) i;

Goal "inverse (inverse (z::hypreal)) = z";
by (hypreal_div_undefined_case_tac "z=0" 1);
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (asm_full_simp_tac (simpset() addsimps 
                       [hypreal_inverse, hypreal_zero_def]) 1);
qed "hypreal_inverse_inverse";
Addsimps [hypreal_inverse_inverse];

Goalw [hypreal_one_def] "inverse((1::hypreal)) = (1::hypreal)";
by (full_simp_tac (simpset() addsimps [hypreal_inverse,
                                       real_zero_not_eq_one RS not_sym]) 1);
qed "hypreal_inverse_1";
Addsimps [hypreal_inverse_1];


(*** existence of inverse ***)

Goalw [hypreal_one_def,hypreal_zero_def] 
     "x ~= 0 ==> x*inverse(x) = (1::hypreal)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (rotate_tac 1 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_inverse, hypreal_mult]) 1);
by (dtac FreeUltrafilterNat_Compl_mem 1);
by (blast_tac (claset() addSIs [real_mult_inv_right,
    FreeUltrafilterNat_subset]) 1);
qed "hypreal_mult_inverse";

Goal "x ~= 0 ==> inverse(x)*x = (1::hypreal)";
by (asm_simp_tac (simpset() addsimps [hypreal_mult_inverse,
				      hypreal_mult_commute]) 1);
qed "hypreal_mult_inverse_left";

Goal "(c::hypreal) ~= 0 ==> (c*a=c*b) = (a=b)";
by Auto_tac;
by (dres_inst_tac [("f","%x. x*inverse c")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_mult_inverse] @ hypreal_mult_ac)  1);
qed "hypreal_mult_left_cancel";
    
Goal "(c::hypreal) ~= 0 ==> (a*c=b*c) = (a=b)";
by (Step_tac 1);
by (dres_inst_tac [("f","%x. x*inverse c")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_mult_inverse] @ hypreal_mult_ac)  1);
qed "hypreal_mult_right_cancel";

Goalw [hypreal_zero_def] "x ~= 0 ==> inverse (x::hypreal) ~= 0";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_inverse, hypreal_mult]) 1);
qed "hypreal_inverse_not_zero";

Addsimps [hypreal_mult_inverse,hypreal_mult_inverse_left];

Goal "[| x ~= 0; y ~= 0 |] ==> x * y ~= (0::hypreal)";
by (Step_tac 1);
by (dres_inst_tac [("f","%z. inverse x*z")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_mult_assoc RS sym]) 1);
qed "hypreal_mult_not_0";

Goal "x*y = (0::hypreal) ==> x = 0 | y = 0";
by (auto_tac (claset() addIs [ccontr] addDs [hypreal_mult_not_0],
              simpset()));
qed "hypreal_mult_zero_disj";

Goal "inverse(-x) = -inverse(x::hypreal)";
by (hypreal_div_undefined_case_tac "x=0" 1);
by (rtac (hypreal_mult_right_cancel RS iffD1) 1);
by (stac hypreal_mult_inverse_left 2);
by Auto_tac;
qed "hypreal_minus_inverse";

Goal "inverse(x*y) = inverse(x)*inverse(y::hypreal)";
by (hypreal_div_undefined_case_tac "x=0" 1);
by (hypreal_div_undefined_case_tac "y=0" 1);
by (forw_inst_tac [("y","y")] hypreal_mult_not_0 1 THEN assume_tac 1);
by (res_inst_tac [("c1","x")] (hypreal_mult_left_cancel RS iffD1) 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_mult_assoc RS sym]));
by (res_inst_tac [("c1","y")] (hypreal_mult_left_cancel RS iffD1) 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_mult_left_commute]));
by (asm_simp_tac (simpset() addsimps [hypreal_mult_assoc RS sym]) 1);
qed "hypreal_inverse_distrib";

(*------------------------------------------------------------------
                   Theorems for ordering 
 ------------------------------------------------------------------*)

(* prove introduction and elimination rules for hypreal_less *)

Goalw [hypreal_less_def]
 "(P < (Q::hypreal)) = (EX X Y. X : Rep_hypreal(P) & \
\                             Y : Rep_hypreal(Q) & \
\                             {n. X n < Y n} : FreeUltrafilterNat)";
by (Fast_tac 1);
qed "hypreal_less_iff";

Goalw [hypreal_less_def]
 "[| {n. X n < Y n} : FreeUltrafilterNat; \
\         X : Rep_hypreal(P); \
\         Y : Rep_hypreal(Q) |] ==> P < (Q::hypreal)";
by (Fast_tac 1);
qed "hypreal_lessI";


Goalw [hypreal_less_def]
     "!! R1. [| R1 < (R2::hypreal); \
\         !!X Y. {n. X n < Y n} : FreeUltrafilterNat ==> P; \
\         !!X. X : Rep_hypreal(R1) ==> P; \ 
\         !!Y. Y : Rep_hypreal(R2) ==> P |] \
\     ==> P";
by Auto_tac;
qed "hypreal_lessE";

Goalw [hypreal_less_def]
 "R1 < (R2::hypreal) ==> (EX X Y. {n. X n < Y n} : FreeUltrafilterNat & \
\                                  X : Rep_hypreal(R1) & \
\                                  Y : Rep_hypreal(R2))";
by (Fast_tac 1);
qed "hypreal_lessD";

Goal "~ (R::hypreal) < R";
by (res_inst_tac [("z","R")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_less_def]));
by (Ultra_tac 1);
qed "hypreal_less_not_refl";

(*** y < y ==> P ***)
bind_thm("hypreal_less_irrefl",hypreal_less_not_refl RS notE);
AddSEs [hypreal_less_irrefl];

Goal "!!(x::hypreal). x < y ==> x ~= y";
by (auto_tac (claset(), simpset() addsimps [hypreal_less_not_refl]));
qed "hypreal_not_refl2";

Goal "!!(R1::hypreal). [| R1 < R2; R2 < R3 |] ==> R1 < R3";
by (res_inst_tac [("z","R1")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","R2")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","R3")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSIs [exI], simpset() addsimps [hypreal_less_def]));
by (ultra_tac (claset() addIs [order_less_trans], simpset()) 1);
qed "hypreal_less_trans";

Goal "!! (R1::hypreal). [| R1 < R2; R2 < R1 |] ==> P";
by (dtac hypreal_less_trans 1 THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps 
    [hypreal_less_not_refl]) 1);
qed "hypreal_less_asym";

(*-------------------------------------------------------
  TODO: The following theorem should have been proved 
  first and then used througout the proofs as it probably 
  makes many of them more straightforward. 
 -------------------------------------------------------*)
Goalw [hypreal_less_def]
      "(Abs_hypreal(hyprel``{%n. X n}) < \
\           Abs_hypreal(hyprel``{%n. Y n})) = \
\      ({n. X n < Y n} : FreeUltrafilterNat)";
by (auto_tac (claset() addSIs [lemma_hyprel_refl], simpset()));
by (Ultra_tac 1);
qed "hypreal_less";

(*---------------------------------------------------------------------------------
             Hyperreals as a linearly ordered field
 ---------------------------------------------------------------------------------*)
(*** sum order 
Goalw [hypreal_zero_def] 
      "[| 0 < x; 0 < y |] ==> (0::hypreal) < x + y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps
    [hypreal_less_def,hypreal_add]));
by (auto_tac (claset() addSIs [exI],simpset() addsimps
    [hypreal_less_def,hypreal_add]));
by (ultra_tac (claset() addIs [real_add_order],simpset()) 1);
qed "hypreal_add_order";
***)

(*** mult order 
Goalw [hypreal_zero_def] 
          "[| 0 < x; 0 < y |] ==> (0::hypreal) < x * y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSIs [exI],simpset() addsimps
    [hypreal_less_def,hypreal_mult]));
by (ultra_tac (claset() addIs [rename_numerals real_mult_order],
	       simpset()) 1);
qed "hypreal_mult_order";
****)


(*---------------------------------------------------------------------------------
                         Trichotomy of the hyperreals
  --------------------------------------------------------------------------------*)

Goalw [hyprel_def] "EX x. x: hyprel `` {%n. Numeral0}";
by (res_inst_tac [("x","%n. Numeral0")] exI 1);
by (Step_tac 1);
by (auto_tac (claset() addSIs [FreeUltrafilterNat_Nat_set], simpset()));
qed "lemma_hyprel_0_mem";

Goalw [hypreal_zero_def]"0 <  x | x = 0 | x < (0::hypreal)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_less_def]));
by (cut_facts_tac [lemma_hyprel_0_mem] 1 THEN etac exE 1);
by (dres_inst_tac [("x","xa")] spec 1);
by (dres_inst_tac [("x","x")] spec 1);
by (cut_inst_tac [("x","x")] lemma_hyprel_refl 1);
by Auto_tac;
by (dres_inst_tac [("x","x")] spec 1);
by (dres_inst_tac [("x","xa")] spec 1);
by Auto_tac;
by (Ultra_tac 1);
by (auto_tac (claset() addIs [real_linear_less2],simpset()));
qed "hypreal_trichotomy";

val prems = Goal "[| (0::hypreal) < x ==> P; \
\                 x = 0 ==> P; \
\                 x < 0 ==> P |] ==> P";
by (cut_inst_tac [("x","x")] hypreal_trichotomy 1);
by (REPEAT (eresolve_tac (disjE::prems) 1));
qed "hypreal_trichotomyE";

(*----------------------------------------------------------------------------
            More properties of <
 ----------------------------------------------------------------------------*)

Goal "((x::hypreal) < y) = (0 < y + -x)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_add,
    hypreal_zero_def,hypreal_minus,hypreal_less]));
by (ALLGOALS(Ultra_tac));
qed "hypreal_less_minus_iff"; 

Goal "((x::hypreal) < y) = (x + -y < 0)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_add,
    hypreal_zero_def,hypreal_minus,hypreal_less]));
by (ALLGOALS(Ultra_tac));
qed "hypreal_less_minus_iff2";

Goal "((x::hypreal) = y) = (x + - y = 0)";
by Auto_tac;
by (res_inst_tac [("x1","-y")] (hypreal_add_right_cancel RS iffD1) 1);
by Auto_tac;
qed "hypreal_eq_minus_iff"; 

Goal "((x::hypreal) = y) = (0 = y + - x)";
by Auto_tac;
by (res_inst_tac [("x1","-x")] (hypreal_add_right_cancel RS iffD1) 1);
by Auto_tac;
qed "hypreal_eq_minus_iff2"; 

(* 07/00 *)
Goal "(0::hypreal) - x = -x";
by (simp_tac (simpset() addsimps [hypreal_diff_def]) 1);
qed "hypreal_diff_zero";

Goal "x - (0::hypreal) = x";
by (simp_tac (simpset() addsimps [hypreal_diff_def]) 1);
qed "hypreal_diff_zero_right";

Goal "x - x = (0::hypreal)";
by (simp_tac (simpset() addsimps [hypreal_diff_def]) 1);
qed "hypreal_diff_self";

Addsimps [hypreal_diff_zero, hypreal_diff_zero_right, hypreal_diff_self];

Goal "(x = y + z) = (x + -z = (y::hypreal))";
by (auto_tac (claset(),simpset() addsimps [hypreal_add_assoc]));
qed "hypreal_eq_minus_iff3";

Goal "(x ~= a) = (x + -a ~= (0::hypreal))";
by (auto_tac (claset() addDs [hypreal_eq_minus_iff RS iffD2],
              simpset())); 
qed "hypreal_not_eq_minus_iff";

Goal "(x+y = (0::hypreal)) = (x = -y)";
by (stac hypreal_eq_minus_iff 1);
by Auto_tac;
qed "hypreal_add_eq_0_iff";
AddIffs [hypreal_add_eq_0_iff];


(*** linearity ***)

Goal "(x::hypreal) < y | x = y | y < x";
by (stac hypreal_eq_minus_iff2 1);
by (res_inst_tac [("x1","x")] (hypreal_less_minus_iff RS ssubst) 1);
by (res_inst_tac [("x1","y")] (hypreal_less_minus_iff2 RS ssubst) 1);
by (rtac hypreal_trichotomyE 1);
by Auto_tac;
qed "hypreal_linear";

Goal "((w::hypreal) ~= z) = (w<z | z<w)";
by (cut_facts_tac [hypreal_linear] 1);
by (Blast_tac 1);
qed "hypreal_neq_iff";

Goal "!!(x::hypreal). [| x < y ==> P;  x = y ==> P; \
\          y < x ==> P |] ==> P";
by (cut_inst_tac [("x","x"),("y","y")] hypreal_linear 1);
by Auto_tac;
qed "hypreal_linear_less2";

(*------------------------------------------------------------------------------
                            Properties of <=
 ------------------------------------------------------------------------------*)
(*------ hypreal le iff reals le a.e ------*)

Goalw [hypreal_le_def,real_le_def]
      "(Abs_hypreal(hyprel``{%n. X n}) <= \
\           Abs_hypreal(hyprel``{%n. Y n})) = \
\      ({n. X n <= Y n} : FreeUltrafilterNat)";
by (auto_tac (claset(),simpset() addsimps [hypreal_less]));
by (ALLGOALS(Ultra_tac));
qed "hypreal_le";

(*---------------------------------------------------------*)
(*---------------------------------------------------------*)
Goalw [hypreal_le_def] 
     "~(w < z) ==> z <= (w::hypreal)";
by (assume_tac 1);
qed "hypreal_leI";

Goalw [hypreal_le_def] 
      "z<=w ==> ~(w<(z::hypreal))";
by (assume_tac 1);
qed "hypreal_leD";

bind_thm ("hypreal_leE", make_elim hypreal_leD);

Goal "(~(w < z)) = (z <= (w::hypreal))";
by (fast_tac (claset() addSIs [hypreal_leI,hypreal_leD]) 1);
qed "hypreal_less_le_iff";

Goalw [hypreal_le_def] "~ z <= w ==> w<(z::hypreal)";
by (Fast_tac 1);
qed "not_hypreal_leE";

Goalw [hypreal_le_def] "!!(x::hypreal). x <= y ==> x < y | x = y";
by (cut_facts_tac [hypreal_linear] 1);
by (fast_tac (claset() addEs [hypreal_less_irrefl,hypreal_less_asym]) 1);
qed "hypreal_le_imp_less_or_eq";

Goalw [hypreal_le_def] "z<w | z=w ==> z <=(w::hypreal)";
by (cut_facts_tac [hypreal_linear] 1);
by (fast_tac (claset() addEs [hypreal_less_irrefl,hypreal_less_asym]) 1);
qed "hypreal_less_or_eq_imp_le";

Goal "(x <= (y::hypreal)) = (x < y | x=y)";
by (REPEAT(ares_tac [iffI, hypreal_less_or_eq_imp_le, hypreal_le_imp_less_or_eq] 1));
qed "hypreal_le_eq_less_or_eq";
val hypreal_le_less = hypreal_le_eq_less_or_eq;

Goal "w <= (w::hypreal)";
by (simp_tac (simpset() addsimps [hypreal_le_eq_less_or_eq]) 1);
qed "hypreal_le_refl";

(* Axiom 'linorder_linear' of class 'linorder': *)
Goal "(z::hypreal) <= w | w <= z";
by (simp_tac (simpset() addsimps [hypreal_le_less]) 1);
by (cut_facts_tac [hypreal_linear] 1);
by (Blast_tac 1);
qed "hypreal_le_linear";

Goal "[| i <= j; j <= k |] ==> i <= (k::hypreal)";
by (EVERY1 [dtac hypreal_le_imp_less_or_eq, dtac hypreal_le_imp_less_or_eq,
            rtac hypreal_less_or_eq_imp_le, 
            fast_tac (claset() addIs [hypreal_less_trans])]);
qed "hypreal_le_trans";

Goal "[| z <= w; w <= z |] ==> z = (w::hypreal)";
by (EVERY1 [dtac hypreal_le_imp_less_or_eq, dtac hypreal_le_imp_less_or_eq,
            fast_tac (claset() addEs [hypreal_less_irrefl,hypreal_less_asym])]);
qed "hypreal_le_anti_sym";

Goal "[| ~ y < x; y ~= x |] ==> x < (y::hypreal)";
by (rtac not_hypreal_leE 1);
by (fast_tac (claset() addDs [hypreal_le_imp_less_or_eq]) 1);
qed "not_less_not_eq_hypreal_less";

(* Axiom 'order_less_le' of class 'order': *)
Goal "((w::hypreal) < z) = (w <= z & w ~= z)";
by (simp_tac (simpset() addsimps [hypreal_le_def, hypreal_neq_iff]) 1);
by (blast_tac (claset() addIs [hypreal_less_asym]) 1);
qed "hypreal_less_le";

Goal "(0 < -R) = (R < (0::hypreal))";
by (res_inst_tac [("z","R")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
       simpset() addsimps [hypreal_zero_def, hypreal_less,hypreal_minus]));
qed "hypreal_minus_zero_less_iff";
Addsimps [hypreal_minus_zero_less_iff];

Goal "(-R < 0) = ((0::hypreal) < R)";
by (res_inst_tac [("z","R")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
         simpset() addsimps [hypreal_zero_def, hypreal_less,hypreal_minus]));
by (ALLGOALS(Ultra_tac));
qed "hypreal_minus_zero_less_iff2";

Goalw [hypreal_le_def] "((0::hypreal) <= -r) = (r <= (0::hypreal))";
by (simp_tac (simpset() addsimps [hypreal_minus_zero_less_iff2]) 1);
qed "hypreal_minus_zero_le_iff";
Addsimps [hypreal_minus_zero_le_iff];

(*----------------------------------------------------------
  hypreal_of_real preserves field and order properties
 -----------------------------------------------------------*)
Goalw [hypreal_of_real_def] 
     "hypreal_of_real (z1 + z2) = hypreal_of_real z1 + hypreal_of_real z2";
by (simp_tac (simpset() addsimps [hypreal_add, hypreal_add_mult_distrib]) 1);
qed "hypreal_of_real_add";
Addsimps [hypreal_of_real_add];

Goalw [hypreal_of_real_def] 
     "hypreal_of_real (z1 * z2) = hypreal_of_real z1 * hypreal_of_real z2";
by (simp_tac (simpset() addsimps [hypreal_mult, hypreal_add_mult_distrib2]) 1);
qed "hypreal_of_real_mult";
Addsimps [hypreal_of_real_mult];

Goalw [hypreal_less_def,hypreal_of_real_def] 
     "(hypreal_of_real z1 <  hypreal_of_real z2) = (z1 < z2)";
by Auto_tac;
by (res_inst_tac [("x","%n. z1")] exI 2);
by (Step_tac 1); 
by (res_inst_tac [("x","%n. z2")] exI 3);
by Auto_tac;
by (rtac FreeUltrafilterNat_P 1);
by (Ultra_tac 1);
qed "hypreal_of_real_less_iff";
Addsimps [hypreal_of_real_less_iff];

Goalw [hypreal_le_def,real_le_def] 
     "(hypreal_of_real z1 <= hypreal_of_real z2) = (z1 <= z2)";
by Auto_tac;
qed "hypreal_of_real_le_iff";
Addsimps [hypreal_of_real_le_iff];

Goal "(hypreal_of_real z1 = hypreal_of_real z2) = (z1 = z2)";
by (force_tac (claset() addIs [order_antisym, hypreal_of_real_le_iff RS iffD1],
               simpset()) 1); 
qed "hypreal_of_real_eq_iff";
Addsimps [hypreal_of_real_eq_iff];

Goalw [hypreal_of_real_def] "hypreal_of_real (-r) = - hypreal_of_real  r";
by (auto_tac (claset(),simpset() addsimps [hypreal_minus]));
qed "hypreal_of_real_minus";
Addsimps [hypreal_of_real_minus];

(*DON'T insert this or the next one as default simprules.
  They are used in both orientations and anyway aren't the ones we finally
  need, which would use binary literals.*)
Goalw [hypreal_of_real_def,hypreal_one_def] "hypreal_of_real  Numeral1 = (1::hypreal)";
by (Step_tac 1);
qed "hypreal_of_real_one";

Goalw [hypreal_of_real_def,hypreal_zero_def] "hypreal_of_real Numeral0 = 0";
by (Step_tac 1);
qed "hypreal_of_real_zero";

Goal "(hypreal_of_real r = 0) = (r = Numeral0)";
by (auto_tac (claset() addIs [FreeUltrafilterNat_P],
    simpset() addsimps [hypreal_of_real_def,
                        hypreal_zero_def,FreeUltrafilterNat_Nat_set]));
qed "hypreal_of_real_zero_iff";

Goal "hypreal_of_real (inverse r) = inverse (hypreal_of_real r)";
by (case_tac "r=Numeral0" 1);
by (asm_simp_tac (simpset() addsimps [REAL_DIVIDE_ZERO, INVERSE_ZERO, 
                              HYPREAL_INVERSE_ZERO, hypreal_of_real_zero]) 1);
by (res_inst_tac [("c1","hypreal_of_real r")] 
    (hypreal_mult_left_cancel RS iffD1) 1);
by (stac (hypreal_of_real_mult RS sym) 2); 
by (auto_tac (claset(), 
         simpset() addsimps [hypreal_of_real_one, hypreal_of_real_zero_iff]));
qed "hypreal_of_real_inverse";
Addsimps [hypreal_of_real_inverse];

Goal "hypreal_of_real (z1 / z2) = hypreal_of_real z1 / hypreal_of_real z2";
by (simp_tac (simpset() addsimps [hypreal_divide_def, real_divide_def]) 1);
qed "hypreal_of_real_divide"; 
Addsimps [hypreal_of_real_divide];


(*** Division lemmas ***)

Goal "(0::hypreal)/x = 0";
by (simp_tac (simpset() addsimps [hypreal_divide_def]) 1); 
qed "hypreal_zero_divide";

Goal "x/(1::hypreal) = x";
by (simp_tac (simpset() addsimps [hypreal_divide_def]) 1); 
qed "hypreal_divide_one";
Addsimps [hypreal_zero_divide, hypreal_divide_one];

Goal "(x::hypreal) * (y/z) = (x*y)/z";
by (simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_mult_assoc]) 1); 
qed "hypreal_times_divide1_eq";

Goal "(y/z) * (x::hypreal) = (y*x)/z";
by (simp_tac (simpset() addsimps [hypreal_divide_def]@hypreal_mult_ac) 1); 
qed "hypreal_times_divide2_eq";

Addsimps [hypreal_times_divide1_eq, hypreal_times_divide2_eq];

Goal "(x::hypreal) / (y/z) = (x*z)/y";
by (simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_inverse_distrib]@
                                 hypreal_mult_ac) 1); 
qed "hypreal_divide_divide1_eq";

Goal "((x::hypreal) / y) / z = x/(y*z)";
by (simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_inverse_distrib, 
                                  hypreal_mult_assoc]) 1); 
qed "hypreal_divide_divide2_eq";

Addsimps [hypreal_divide_divide1_eq, hypreal_divide_divide2_eq];

(** As with multiplication, pull minus signs OUT of the / operator **)

Goal "(-x) / (y::hypreal) = - (x/y)";
by (simp_tac (simpset() addsimps [hypreal_divide_def]) 1); 
qed "hypreal_minus_divide_eq";
Addsimps [hypreal_minus_divide_eq];

Goal "(x / -(y::hypreal)) = - (x/y)";
by (simp_tac (simpset() addsimps [hypreal_divide_def, hypreal_minus_inverse]) 1); 
qed "hypreal_divide_minus_eq";
Addsimps [hypreal_divide_minus_eq];

Goal "(x+y)/(z::hypreal) = x/z + y/z";
by (simp_tac (simpset() addsimps [hypreal_divide_def, 
                                  hypreal_add_mult_distrib]) 1); 
qed "hypreal_add_divide_distrib";

Goal "[|(x::hypreal) ~= 0;  y ~= 0 |]  \
\     ==> inverse(x) + inverse(y) = (x + y)*inverse(x*y)";
by (asm_full_simp_tac (simpset() addsimps [hypreal_inverse_distrib,
                    hypreal_add_mult_distrib,hypreal_mult_assoc RS sym]) 1);
by (stac hypreal_mult_assoc 1);
by (rtac (hypreal_mult_left_commute RS subst) 1);
by (asm_full_simp_tac (simpset() addsimps [hypreal_add_commute]) 1);
qed "hypreal_inverse_add";

Goal "x = -x ==> x = (0::hypreal)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_minus, hypreal_zero_def]));
by (Ultra_tac 1);
qed "hypreal_self_eq_minus_self_zero";

Goal "(x + x = 0) = (x = (0::hypreal))";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_add, hypreal_zero_def]));
qed "hypreal_add_self_zero_cancel";
Addsimps [hypreal_add_self_zero_cancel];

Goal "(x + x + y = y) = (x = (0::hypreal))";
by Auto_tac;
by (dtac (hypreal_eq_minus_iff RS iffD1) 1);
by (auto_tac (claset(), 
     simpset() addsimps [hypreal_add_assoc, hypreal_self_eq_minus_self_zero]));
qed "hypreal_add_self_zero_cancel2";
Addsimps [hypreal_add_self_zero_cancel2];

Goal "(x + (x + y) = y) = (x = (0::hypreal))";
by (simp_tac (simpset() addsimps [hypreal_add_assoc RS sym]) 1);
qed "hypreal_add_self_zero_cancel2a";
Addsimps [hypreal_add_self_zero_cancel2a];

Goal "(b = -a) = (-b = (a::hypreal))";
by Auto_tac;
qed "hypreal_minus_eq_swap";

Goal "(-b = -a) = (b = (a::hypreal))";
by (asm_full_simp_tac (simpset() addsimps 
    [hypreal_minus_eq_swap]) 1);
qed "hypreal_minus_eq_cancel";
Addsimps [hypreal_minus_eq_cancel];

Goalw [hypreal_diff_def] "(x<y) = (x-y < (0::hypreal))";
by (rtac hypreal_less_minus_iff2 1);
qed "hypreal_less_eq_diff";

(*** Subtraction laws ***)

Goal "x + (y - z) = (x + y) - (z::hypreal)";
by (simp_tac (simpset() addsimps hypreal_diff_def::hypreal_add_ac) 1);
qed "hypreal_add_diff_eq";

Goal "(x - y) + z = (x + z) - (y::hypreal)";
by (simp_tac (simpset() addsimps hypreal_diff_def::hypreal_add_ac) 1);
qed "hypreal_diff_add_eq";

Goal "(x - y) - z = x - (y + (z::hypreal))";
by (simp_tac (simpset() addsimps hypreal_diff_def::hypreal_add_ac) 1);
qed "hypreal_diff_diff_eq";

Goal "x - (y - z) = (x + z) - (y::hypreal)";
by (simp_tac (simpset() addsimps hypreal_diff_def::hypreal_add_ac) 1);
qed "hypreal_diff_diff_eq2";

Goal "(x-y < z) = (x < z + (y::hypreal))";
by (stac hypreal_less_eq_diff 1);
by (res_inst_tac [("y1", "z")] (hypreal_less_eq_diff RS ssubst) 1);
by (simp_tac (simpset() addsimps hypreal_diff_def::hypreal_add_ac) 1);
qed "hypreal_diff_less_eq";

Goal "(x < z-y) = (x + (y::hypreal) < z)";
by (stac hypreal_less_eq_diff 1);
by (res_inst_tac [("y1", "z-y")] (hypreal_less_eq_diff RS ssubst) 1);
by (simp_tac (simpset() addsimps hypreal_diff_def::hypreal_add_ac) 1);
qed "hypreal_less_diff_eq";

Goalw [hypreal_le_def] "(x-y <= z) = (x <= z + (y::hypreal))";
by (simp_tac (simpset() addsimps [hypreal_less_diff_eq]) 1);
qed "hypreal_diff_le_eq";

Goalw [hypreal_le_def] "(x <= z-y) = (x + (y::hypreal) <= z)";
by (simp_tac (simpset() addsimps [hypreal_diff_less_eq]) 1);
qed "hypreal_le_diff_eq";

Goalw [hypreal_diff_def] "(x-y = z) = (x = z + (y::hypreal))";
by (auto_tac (claset(), simpset() addsimps [hypreal_add_assoc]));
qed "hypreal_diff_eq_eq";

Goalw [hypreal_diff_def] "(x = z-y) = (x + (y::hypreal) = z)";
by (auto_tac (claset(), simpset() addsimps [hypreal_add_assoc]));
qed "hypreal_eq_diff_eq";

(*This list of rewrites simplifies (in)equalities by bringing subtractions
  to the top and then moving negative terms to the other side.  
  Use with hypreal_add_ac*)
val hypreal_compare_rls = 
  [symmetric hypreal_diff_def,
   hypreal_add_diff_eq, hypreal_diff_add_eq, hypreal_diff_diff_eq, 
   hypreal_diff_diff_eq2, 
   hypreal_diff_less_eq, hypreal_less_diff_eq, hypreal_diff_le_eq, 
   hypreal_le_diff_eq, hypreal_diff_eq_eq, hypreal_eq_diff_eq];


(** For the cancellation simproc.
    The idea is to cancel like terms on opposite sides by subtraction **)

Goal "(x::hypreal) - y = x' - y' ==> (x<y) = (x'<y')";
by (stac hypreal_less_eq_diff 1);
by (res_inst_tac [("y1", "y")] (hypreal_less_eq_diff RS ssubst) 1);
by (Asm_simp_tac 1);
qed "hypreal_less_eqI";

Goal "(x::hypreal) - y = x' - y' ==> (y<=x) = (y'<=x')";
by (dtac hypreal_less_eqI 1);
by (asm_simp_tac (simpset() addsimps [hypreal_le_def]) 1);
qed "hypreal_le_eqI";

Goal "(x::hypreal) - y = x' - y' ==> (x=y) = (x'=y')";
by Safe_tac;
by (ALLGOALS
    (asm_full_simp_tac
     (simpset() addsimps [hypreal_eq_diff_eq, hypreal_diff_eq_eq])));
qed "hypreal_eq_eqI";

