(*  Title       : STAR.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : *-transforms
*) 

(*--------------------------------------------------------
   Preamble - Pulling "EX" over "ALL"
 ---------------------------------------------------------*)
 
(* This proof does not need AC and was suggested by the 
   referee for the JCM Paper: let f(x) be least y such 
   that  Q(x,y) 
*)
Goal "!!Q. ALL x. EX y. Q x y ==> EX (f :: nat => nat). ALL x. Q x (f x)";
by (res_inst_tac [("x","%x. LEAST y. Q x y")] exI 1);
by (blast_tac (claset() addIs [LeastI]) 1);
qed "no_choice";

(*------------------------------------------------------------
    Properties of the *-transform applied to sets of reals
 ------------------------------------------------------------*)

Goalw [starset_def] "*s*(UNIV::real set) = (UNIV::hypreal set)";
by (Auto_tac);
qed "STAR_real_set";
Addsimps [STAR_real_set];

Goalw [starset_def] "*s* {} = {}";
by (Step_tac 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (dres_inst_tac [("x","%n. xa n")] bspec 1);
by (Auto_tac);
qed "STAR_empty_set";
Addsimps [STAR_empty_set];

Goalw [starset_def] "*s* (A Un B) = *s* A Un *s* B";
by (Auto_tac);
by (REPEAT(blast_tac (claset() addIs [FreeUltrafilterNat_subset]) 2));
by (dtac FreeUltrafilterNat_Compl_mem 1);
by (dtac bspec 1 THEN assume_tac 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (Auto_tac);
by (Fuf_tac 1);
qed "STAR_Un";

Goalw [starset_def] "*s* (A Int B) = *s* A Int *s* B";
by (Auto_tac);
by (blast_tac (claset() addIs [FreeUltrafilterNat_Int,
               FreeUltrafilterNat_subset]) 3);
by (REPEAT(blast_tac (claset() addIs [FreeUltrafilterNat_subset]) 1));
qed "STAR_Int";

Goalw [starset_def] "*s* -A = -(*s* A)";
by (Auto_tac);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 2);
by (REPEAT(Step_tac 1) THEN Auto_tac);
by (Fuf_empty_tac 1);
by (dtac FreeUltrafilterNat_Compl_mem 1);
by (Fuf_tac 1);
qed "STAR_Compl";

goal Set.thy "(A - B) = (A Int (- B))";
by (Step_tac 1);
qed "set_diff_iff2";

Goal "!!x. x ~: *s* F ==> x : *s* (- F)";
by (auto_tac (claset(),simpset() addsimps [STAR_Compl]));
qed "STAR_mem_Compl";

Goal "*s* (A - B) = *s* A - *s* B";
by (auto_tac (claset(),simpset() addsimps 
         [set_diff_iff2,STAR_Int,STAR_Compl]));
qed "STAR_diff";

Goalw [starset_def] "!!A. A <= B ==> *s* A <= *s* B";
by (REPEAT(blast_tac (claset() addIs [FreeUltrafilterNat_subset]) 1));
qed "STAR_subset";

Goalw [starset_def,hypreal_of_real_def] 
          "!!A. a : A ==> hypreal_of_real a : *s* A";
by (auto_tac (claset() addIs [FreeUltrafilterNat_subset],simpset()));
qed "STAR_mem";

Goalw [starset_def] "hypreal_of_real `` A <= *s* A";
by (auto_tac (claset(),simpset() addsimps [hypreal_of_real_def]));
by (blast_tac (claset() addIs [FreeUltrafilterNat_subset]) 1);
qed "STAR_hypreal_of_real_image_subset";

Goalw [starset_def] "*s* X Int SReal = hypreal_of_real `` X";
by (auto_tac (claset(),simpset() addsimps [hypreal_of_real_def,SReal_def]));
by (fold_tac [hypreal_of_real_def]);
by (rtac imageI 1 THEN rtac ccontr 1);
by (dtac bspec 1);
by (rtac lemma_hyprel_refl 1);
by (blast_tac (claset() addIs [FreeUltrafilterNat_subset]) 2);
by (Auto_tac);
qed "STAR_hypreal_of_real_Int";

Goal "!!x. x ~: hypreal_of_real `` A ==> ALL y: A. x ~= hypreal_of_real y";
by (Auto_tac);
qed "lemma_not_hyprealA";

Goal "- {n. X n = xa} = {n. X n ~= xa}";
by (Auto_tac);
qed "lemma_Compl_eq";

Goalw [starset_def]
    "!!M. ALL n. (X n) ~: M \
\         ==> Abs_hypreal(hyprel^^{X}) ~: *s* M";
by (Auto_tac THEN rtac bexI 1 THEN rtac lemma_hyprel_refl 2);
by (Auto_tac);
qed "STAR_real_seq_to_hypreal";

Goalw [starset_def] "*s* {x} = {hypreal_of_real x}";
by (auto_tac (claset(),simpset() addsimps [hypreal_of_real_def]));
by (res_inst_tac [("z","xa")] eq_Abs_hypreal 1);
by (auto_tac (claset() addIs [FreeUltrafilterNat_subset],simpset()));
qed "STAR_singleton";
Addsimps [STAR_singleton];

Goal "!!x. x ~: F ==> hypreal_of_real x ~: *s* F";
by (auto_tac (claset(),simpset() addsimps
    [starset_def,hypreal_of_real_def]));
by (rtac bexI 1 THEN rtac lemma_hyprel_refl 2);
by (Auto_tac);
qed "STAR_not_mem";

Goal "!!x. [| x : *s* A; A <= B |] ==> x : *s* B";
by (blast_tac (claset() addDs [STAR_subset]) 1);
qed "STAR_subset_closed";

(*------------------------------------------------------------------ 
   Nonstandard extension of a set (defined using a constant 
   sequence) as a special case of an internal set
 -----------------------------------------------------------------*)

Goalw [starset_n_def,starset_def] 
     "!!A. ALL n. (As n = A) ==> *sn* As = *s* A";
by (Auto_tac);
qed "starset_n_starset";


(*----------------------------------------------------------------*)
(* Theorems about nonstandard extensions of functions             *)
(*----------------------------------------------------------------*)

(*----------------------------------------------------------------*) 
(* Nonstandard extension of a function (defined using a           *)
(* constant sequence) as a special case of an internal function   *)
(*----------------------------------------------------------------*)

Goalw [starfun_n_def,starfun_def] 
     "!!A. ALL n. (F n = f) ==> *fn* F = *f* f";
by (Auto_tac);
qed "starfun_n_starfun";


(* 
   Prove that hrabs is a nonstandard extension of rabs without
   use of congruence property (proved after this for general
   nonstandard extensions of real valued functions). This makes 
   proof much longer- see comments at end of HREALABS.thy where
   we proved a congruence theorem for hrabs. 

   NEW!!! No need to prove all the lemmas anymore. Use the ultrafilter
   tactic! 
*)
  
Goalw [is_starext_def] "is_starext abs abs";
by (Step_tac 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by Auto_tac;
by (rtac bexI 1 THEN rtac lemma_hyprel_refl 2);
by (rtac bexI 1 THEN rtac lemma_hyprel_refl 2);
by (auto_tac (claset() addSDs [spec],simpset() addsimps [hypreal_minus,hrabs_def,
    hypreal_zero_def,hypreal_le_def,hypreal_less_def]));
by (TRYALL(Ultra_tac));
by (TRYALL(arith_tac));
qed "hrabs_is_starext_rabs";

Goal "!!z. [| X: Rep_hypreal z; Y: Rep_hypreal z |] \
\              ==> {n. X n = Y n} : FreeUltrafilterNat";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (Auto_tac THEN Fuf_tac 1);
qed "Rep_hypreal_FreeUltrafilterNat";

(*-----------------------------------------------------------------------
    Nonstandard extension of functions- congruence 
 -----------------------------------------------------------------------*) 

Goalw [congruent_def] "congruent hyprel (%X. hyprel^^{%n. f (X n)})";
by (safe_tac (claset()));
by (ALLGOALS(Fuf_tac));
qed "starfun_congruent";

Goalw [starfun_def]
      "(*f* f) (Abs_hypreal(hyprel^^{%n. X n})) = \
\      Abs_hypreal(hyprel ^^ {%n. f (X n)})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by (simp_tac (simpset() addsimps 
   [hyprel_in_hypreal RS Abs_hypreal_inverse,[equiv_hyprel,
   starfun_congruent] MRS UN_equiv_class]) 1);
qed "starfun";

(*-------------------------------------------
  multiplication: ( *f ) x ( *g ) = *(f x g)  
 ------------------------------------------*)
Goal "(*f* f) xa * (*f* g) xa = (*f* (%x. f x * g x)) xa";
by (res_inst_tac [("z","xa")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,hypreal_mult]));
qed "starfun_mult";

(*---------------------------------------
  addition: ( *f ) + ( *g ) = *(f + g)  
 ---------------------------------------*)
Goal "(*f* f) xa + (*f* g) xa = (*f* (%x. f x + g x)) xa";
by (res_inst_tac [("z","xa")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,hypreal_add]));
qed "starfun_add";

(*--------------------------------------------
  subtraction: ( *f ) + -( *g ) = *(f + -g)  
 -------------------------------------------*)
Goal "(*f* f) xa + -(*f* g) xa = (*f* (%x. f x + -g x)) xa";
by (res_inst_tac [("z","xa")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_minus,hypreal_add]));
qed "starfun_add_minus";

Goalw [hypreal_diff_def,real_diff_def]
  "(*f* f) xa  - (*f* g) xa = (*f* (%x. f x - g x)) xa";
by (rtac starfun_add_minus 1);
qed "starfun_diff";

(*--------------------------------------
  composition: ( *f ) o ( *g ) = *(f o g)  
 ---------------------------------------*)

Goal "(%x. (*f* f) ((*f* g) x)) = *f* (%x. f (g x))";
by (rtac ext 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun]));
qed "starfun_o2";

Goalw [o_def] "(*f* f) o (*f* g) = (*f* (f o g))";
by (simp_tac (simpset() addsimps [starfun_o2]) 1);
qed "starfun_o";

(*--------------------------------------
  NS extension of constant function
 --------------------------------------*)
Goal "(*f* (%x. k)) xa = hypreal_of_real  k";
by (res_inst_tac [("z","xa")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_of_real_def]));
qed "starfun_const_fun";

Addsimps [starfun_const_fun];

Goal "- (*f* f) x = (*f* (%x. - f x)) x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
              hypreal_minus]));
qed "starfun_minus";

(*----------------------------------------------------
   the NS extension of the identity function
 ----------------------------------------------------*)

Goal "!!x. x @= hypreal_of_real a ==> (*f* (%x. x)) x @= hypreal_of_real  a";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun]));
qed "starfun_Idfun_inf_close";

Goal "(*f* (%x. x)) x = x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun]));
qed "starfun_Id";

(*----------------------------------------------------------------------
      the *-function is a (nonstandard) extension of the function
 ----------------------------------------------------------------------*)

Goalw [is_starext_def] "is_starext (*f* f) f";
by (Auto_tac);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSIs [bexI] ,simpset() addsimps [starfun]));
qed "is_starext_starfun";

(*----------------------------------------------------------------------
     Any nonstandard extension is in fact the *-function
 ----------------------------------------------------------------------*)

Goalw [is_starext_def] "!!f. is_starext F f ==> F = *f* f";
by (rtac ext 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (dres_inst_tac [("x","x")] spec 1);
by (dres_inst_tac [("x","(*f* f) x")] spec 1);
by (auto_tac (claset() addSDs [FreeUltrafilterNat_Compl_mem],
    simpset() addsimps [starfun]));
by (Fuf_empty_tac 1);
qed "is_starfun_starext";

Goal "(is_starext F f) = (F = *f* f)";
by (blast_tac (claset() addIs [is_starfun_starext,is_starext_starfun]) 1);
qed "is_starext_starfun_iff";

(*--------------------------------------------------------
   extented function has same solution as its standard
   version for real arguments. i.e they are the same
   for all real arguments
 -------------------------------------------------------*)
Goal "(*f* f) (hypreal_of_real a) = hypreal_of_real (f a)";
by (auto_tac (claset(),simpset() addsimps 
     [starfun,hypreal_of_real_def]));
qed "starfun_eq";

Addsimps [starfun_eq];

Goal "(*f* f) (hypreal_of_real a) @= hypreal_of_real (f a)";
by (Auto_tac);
qed "starfun_inf_close";

(* useful for NS definition of derivatives *)
Goal "(*f* (%h. f (x + h))) xa  = (*f* f) (hypreal_of_real  x + xa)";
by (res_inst_tac [("z","xa")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_of_real_def,hypreal_add]));
qed "starfun_lambda_cancel";

Goal "(*f* (%h. f(g(x + h)))) xa = (*f* (f o g)) (hypreal_of_real x + xa)";
by (res_inst_tac [("z","xa")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_of_real_def,hypreal_add]));
qed "starfun_lambda_cancel2";

Goal "!!f. [| (*f* f) xa @= l; (*f* g) xa @= m; \
\                 l: HFinite; m: HFinite  \
\              |] ==>  (*f* (%x. f x * g x)) xa @= l * m";
by (dtac inf_close_mult_HFinite 1);
by (REPEAT(assume_tac 1));
by (auto_tac (claset() addIs [inf_close_sym RSN (2,inf_close_HFinite)],
              simpset() addsimps [starfun_mult]));
qed "starfun_mult_HFinite_inf_close";

Goal "!!f. [| (*f* f) xa @= l; (*f* g) xa @= m \
\              |] ==>  (*f* (%x. f x + g x)) xa @= l + m";
by (auto_tac (claset() addIs [inf_close_add],
              simpset() addsimps [starfun_add RS sym]));
qed "starfun_add_inf_close";

(*----------------------------------------------------
    Examples: hrabs is nonstandard extension of rabs 
              inverse is nonstandard extension of inverse
 ---------------------------------------------------*)

(* can be proved easily using theorem "starfun" and *)
(* properties of ultrafilter as for inverse below we  *)
(* use the theorem we proved above instead          *)

Goal "*f* abs = abs";
by (rtac (hrabs_is_starext_rabs RS 
    (is_starext_starfun_iff RS iffD1) RS sym) 1);
qed "starfun_rabs_hrabs";

Goal "!!x. x ~= 0 ==> (*f* inverse) x = inverse(x)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_inverse,hypreal_zero_def]));
by (dtac FreeUltrafilterNat_Compl_mem 1);
by (auto_tac (claset() addEs [FreeUltrafilterNat_subset],simpset()));
qed "starfun_inverse_inverse";

(* more specifically *)
Goal "(*f* inverse) ehr = inverse (ehr)";
by (rtac (hypreal_epsilon_not_zero RS starfun_inverse_inverse) 1);
qed "starfun_inverse_epsilon";

Goal "ALL x. f x ~= 0 ==> \
\     inverse ((*f* f) x) = (*f* (%x. inverse (f x))) x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
              hypreal_inverse]));
qed "starfun_inverse";

Goal "(*f* f) x ~= 0 ==> \
\     inverse ((*f* f) x) = (*f* (%x. inverse (f x))) x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset() addIs [FreeUltrafilterNat_subset]
    addSDs [FreeUltrafilterNat_Compl_mem],
    simpset() addsimps [starfun,hypreal_inverse,
    hypreal_zero_def]));
qed "starfun_inverse2";

Goal "a ~= hypreal_of_real b ==> \
\     (*f* (%z. inverse (z + -b))) a = inverse(a + -hypreal_of_real b)";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset() addIs [FreeUltrafilterNat_subset]
    addSDs [FreeUltrafilterNat_Compl_mem],
    simpset() addsimps [starfun,hypreal_of_real_def,hypreal_add,
    hypreal_minus,hypreal_inverse,rename_numerals 
    (real_eq_minus_iff2 RS sym)]));
qed "starfun_inverse3";

Goal 
     "!!f. a + hypreal_of_real b ~= 0 ==> \
\          (*f* (%z. inverse (z + b))) a = inverse(a + hypreal_of_real b)";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset() addIs [FreeUltrafilterNat_subset]
    addSDs [FreeUltrafilterNat_Compl_mem],
    simpset() addsimps [starfun,hypreal_of_real_def,hypreal_add,
    hypreal_inverse,hypreal_zero_def]));
qed "starfun_inverse4";

(*-------------------------------------------------------------
    General lemma/theorem needed for proofs in elementary
    topology of the reals
 ------------------------------------------------------------*)
Goalw [starset_def] 
      "!!A. (*f* f) x : *s* A ==> x : *s* {x. f x : A}";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun]));
by (dres_inst_tac [("x","%n. f (Xa n)")] bspec 1);
by (Auto_tac THEN Fuf_tac 1);
qed "starfun_mem_starset";

(*------------------------------------------------------------
   Alternative definition for hrabs with rabs function
   applied entrywise to equivalence class representative.
   This is easily proved using starfun and ns extension thm
 ------------------------------------------------------------*)
Goal "abs (Abs_hypreal (hyprel ^^ {X})) = \
\                 Abs_hypreal(hyprel ^^ {%n. abs (X n)})";
by (simp_tac (simpset() addsimps [starfun_rabs_hrabs RS sym,starfun]) 1);
qed "hypreal_hrabs";

(*----------------------------------------------------------------
   nonstandard extension of set through nonstandard extension
   of rabs function i.e hrabs. A more general result should be 
   where we replace rabs by some arbitrary function f and hrabs
   by its NS extenson ( *f* f). See second NS set extension below.
 ----------------------------------------------------------------*)
Goalw [starset_def]
   "*s* {x. abs (x + - y) < r} = {x. abs(x + -hypreal_of_real y) < hypreal_of_real r}";
by (Step_tac 1);
by (ALLGOALS(res_inst_tac [("z","x")] eq_Abs_hypreal));
by (auto_tac (claset() addSIs [exI] addSDs [bspec],
    simpset() addsimps [hypreal_minus, hypreal_of_real_def,hypreal_add,
    hypreal_hrabs,hypreal_less_def]));
by (Fuf_tac 1);
qed "STAR_rabs_add_minus";

Goalw [starset_def]
  "*s* {x. abs (f x + - y) < r} = \
\      {x. abs((*f* f) x + -hypreal_of_real y) < hypreal_of_real r}";
by (Step_tac 1);
by (ALLGOALS(res_inst_tac [("z","x")] eq_Abs_hypreal));
by (auto_tac (claset() addSIs [exI] addSDs [bspec],
    simpset() addsimps [hypreal_minus, hypreal_of_real_def,hypreal_add,
    hypreal_hrabs,hypreal_less_def,starfun]));
by (Fuf_tac 1);
qed "STAR_starfun_rabs_add_minus";

(*-------------------------------------------------------------------
   Another charaterization of Infinitesimal and one of @= relation. 
   In this theory since hypreal_hrabs proved here. (To Check:) Maybe 
   move both if possible? 
 -------------------------------------------------------------------*)
Goal "(x:Infinitesimal) = (EX X:Rep_hypreal(x). \
\              ALL m. {n. abs(X n) < inverse(real_of_posnat m)}:FreeUltrafilterNat)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSIs [bexI,lemma_hyprel_refl],
    simpset() addsimps [Infinitesimal_hypreal_of_posnat_iff,
    hypreal_of_real_of_posnat,hypreal_of_real_def,hypreal_inverse,
    hypreal_hrabs,hypreal_less])); 
by (dres_inst_tac [("x","n")] spec 1);
by (Fuf_tac 1);
qed  "Infinitesimal_FreeUltrafilterNat_iff2";

Goal "(Abs_hypreal(hyprel^^{X}) @= Abs_hypreal(hyprel^^{Y})) = \
\     (ALL m. {n. abs (X n + - Y n) < \
\                 inverse(real_of_posnat m)} : FreeUltrafilterNat)";
by (rtac (inf_close_minus_iff RS ssubst) 1);
by (rtac (mem_infmal_iff RS subst) 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_minus,
              hypreal_add,Infinitesimal_FreeUltrafilterNat_iff2]));
by (dres_inst_tac [("x","m")] spec 1);
by (Fuf_tac 1);
qed "inf_close_FreeUltrafilterNat_iff";

Goal "inj starfun";
by (rtac injI 1);
by (rtac ext 1 THEN rtac ccontr 1);
by (dres_inst_tac [("x","Abs_hypreal(hyprel ^^{%n. xa})")] fun_cong 1);
by (auto_tac (claset(),simpset() addsimps [starfun]));
qed "inj_starfun";





