(*  Title       : CStar.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh
    Description : defining *-transforms in NSA which extends sets of complex numbers, 
                  and complex functions
*)



(*-----------------------------------------------------------------------------------*)
(*    Properties of the *-transform applied to sets of reals                         *)
(* ----------------------------------------------------------------------------------*)

Goalw [starsetC_def] "*sc*(UNIV::complex set) = (UNIV::hcomplex set)";
by (Auto_tac);
qed "STARC_complex_set";
Addsimps [STARC_complex_set];

Goalw [starsetC_def] "*sc* {} = {}";
by (Auto_tac);
qed "STARC_empty_set";
Addsimps [STARC_empty_set];

Goalw [starsetC_def] "*sc* (A Un B) = *sc* A Un *sc* B";
by (Auto_tac);
by (REPEAT(blast_tac (claset() addIs [FreeUltrafilterNat_subset]) 2));
by (dtac bspec 1 THEN assume_tac 1);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (Auto_tac);
by (Ultra_tac 1);
qed "STARC_Un";

Goalw [starsetC_n_def] 
      "*scn* (%n. (A n) Un (B n)) = *scn* A Un *scn* B";
by Auto_tac;
by (dres_inst_tac [("x","Xa")] bspec 1);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 2);
by (auto_tac (claset() addSDs [bspec], simpset()));
by (TRYALL(Ultra_tac));
qed "starsetC_n_Un";

Goalw [InternalCSets_def]
     "[| X : InternalCSets; Y : InternalCSets |] \
\     ==> (X Un Y) : InternalCSets";
by (auto_tac (claset(),
         simpset() addsimps [starsetC_n_Un RS sym]));
qed "InternalCSets_Un";

Goalw [starsetC_def] "*sc* (A Int B) = *sc* A Int *sc* B";
by (Auto_tac);
by (blast_tac (claset() addIs [FreeUltrafilterNat_Int,
               FreeUltrafilterNat_subset]) 3);
by (REPEAT(blast_tac (claset() addIs [FreeUltrafilterNat_subset]) 1));
qed "STARC_Int";

Goalw [starsetC_n_def] 
      "*scn* (%n. (A n) Int (B n)) = *scn* A Int *scn* B";
by (Auto_tac);
by (auto_tac (claset() addSDs [bspec],simpset()));
by (TRYALL(Ultra_tac));
qed "starsetC_n_Int";

Goalw [InternalCSets_def]
     "[| X : InternalCSets; Y : InternalCSets |] \
\     ==> (X Int Y) : InternalCSets";
by (auto_tac (claset(),
         simpset() addsimps [starsetC_n_Int RS sym]));
qed "InternalCSets_Int";

Goalw [starsetC_def] "*sc* -A = -( *sc* A)";
by (Auto_tac);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 2);
by (REPEAT(Step_tac 1) THEN Auto_tac);
by (ALLGOALS(Ultra_tac));
qed "STARC_Compl";

Goalw [starsetC_n_def] "*scn* ((%n. - A n)) = -( *scn* A)";
by (Auto_tac);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 2);
by (REPEAT(Step_tac 1) THEN Auto_tac);
by (TRYALL(Ultra_tac));
qed "starsetC_n_Compl";

Goalw [InternalCSets_def]
     "X :InternalCSets ==> -X : InternalCSets";
by (auto_tac (claset(),
         simpset() addsimps [starsetC_n_Compl RS sym]));
qed "InternalCSets_Compl";

Goal "x ~: *sc* F ==> x : *sc* (- F)";
by (auto_tac (claset(),simpset() addsimps [STARC_Compl]));
qed "STARC_mem_Compl";

Goal "*sc* (A - B) = *sc* A - *sc* B";
by (auto_tac (claset(),simpset() addsimps 
         [Diff_eq,STARC_Int,STARC_Compl]));
qed "STARC_diff";

Goalw [starsetC_n_def] 
      "*scn* (%n. (A n) - (B n)) = *scn* A - *scn* B";
by (Auto_tac);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 2);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 3);
by (auto_tac (claset() addSDs [bspec], simpset()));
by (TRYALL(Ultra_tac));
qed "starsetC_n_diff";

Goalw [InternalCSets_def]
     "[| X : InternalCSets; Y : InternalCSets |] \
\     ==> (X - Y) : InternalCSets";
by (auto_tac (claset(), simpset() addsimps [starsetC_n_diff RS sym]));
qed "InternalCSets_diff";

Goalw [starsetC_def] "A <= B ==> *sc* A <= *sc* B";
by (REPEAT(blast_tac (claset() addIs [FreeUltrafilterNat_subset]) 1));
qed "STARC_subset";

Goalw [starsetC_def,hcomplex_of_complex_def] 
          "a : A ==> hcomplex_of_complex a : *sc* A";
by (auto_tac (claset() addIs [FreeUltrafilterNat_subset],
         simpset()));
qed "STARC_mem";

Goalw [starsetC_def] "hcomplex_of_complex ` A <= *sc* A";
by (auto_tac (claset(), simpset() addsimps [hcomplex_of_complex_def]));
by (blast_tac (claset() addIs [FreeUltrafilterNat_subset]) 1);
qed "STARC_hcomplex_of_complex_image_subset";

Goal "SComplex <= *sc* (UNIV:: complex set)";
by Auto_tac;
qed "STARC_SComplex_subset";

Goalw [starsetC_def] 
     "*sc* X Int SComplex = hcomplex_of_complex ` X";
by (auto_tac (claset(),
         simpset() addsimps 
           [hcomplex_of_complex_def,SComplex_def]));
by (fold_tac [hcomplex_of_complex_def]);
by (rtac imageI 1 THEN rtac ccontr 1);
by (dtac bspec 1);
by (rtac lemma_hcomplexrel_refl 1);
by (blast_tac (claset() addIs [FreeUltrafilterNat_subset]) 2);
by (Auto_tac);
qed "STARC_hcomplex_of_complex_Int";

Goal "x ~: hcomplex_of_complex ` A ==> ALL y: A. x ~= hcomplex_of_complex y";
by (Auto_tac);
qed "lemma_not_hcomplexA";

Goalw [starsetC_n_def,starsetC_def] "*sc* X = *scn* (%n. X)";
by Auto_tac;
qed "starsetC_starsetC_n_eq";

Goalw [InternalCSets_def] "( *sc* X) : InternalCSets";
by (auto_tac (claset(),
         simpset() addsimps [starsetC_starsetC_n_eq]));
qed "InternalCSets_starsetC_n";
Addsimps [InternalCSets_starsetC_n];

Goal "X : InternalCSets ==> UNIV - X : InternalCSets";
by (auto_tac (claset() addIs [InternalCSets_Compl], simpset()));
qed "InternalCSets_UNIV_diff";

(*-----------------------------------------------------------------------------------*)
(* Nonstandard extension of a set (defined using a constant sequence) as a special   *)
(* case of an internal set                                                           *)
(*-----------------------------------------------------------------------------------*)

Goalw [starsetC_n_def,starsetC_def] 
     "ALL n. (As n = A) ==> *scn* As = *sc* A";
by (Auto_tac);
qed "starsetC_n_starsetC";

(*-----------------------------------------------------------------------------------*)
(* Theorems about nonstandard extensions of functions                                *)   
(*-----------------------------------------------------------------------------------*)

Goalw [starfunC_n_def,starfunC_def] 
     "ALL n. (F n = f) ==> *fcn* F = *fc* f";
by (Auto_tac);
qed "starfunC_n_starfunC";

Goalw [starfunRC_n_def,starfunRC_def] 
     "ALL n. (F n = f) ==> *fRcn* F = *fRc* f";
by (Auto_tac);
qed "starfunRC_n_starfunRC";

Goalw [starfunCR_n_def,starfunCR_def] 
     "ALL n. (F n = f) ==> *fcRn* F = *fcR* f";
by (Auto_tac);
qed "starfunCR_n_starfunCR";

Goalw [congruent_def] 
      "congruent hcomplexrel (%X. hcomplexrel``{%n. f (X n)})";
by (auto_tac (clasimpset() addIffs [hcomplexrel_iff]));
by (ALLGOALS(Ultra_tac));
qed "starfunC_congruent";

(* f::complex => complex *)
Goalw [starfunC_def]
      "( *fc* f) (Abs_hcomplex(hcomplexrel``{%n. X n})) = \
\      Abs_hcomplex(hcomplexrel `` {%n. f (X n)})";
by (res_inst_tac [("f","Abs_hcomplex")] arg_cong 1);
by (auto_tac (clasimpset() addIffs [hcomplexrel_iff]));
by (Ultra_tac 1);
qed "starfunC";

Goalw [starfunRC_def]
      "( *fRc* f) (Abs_hypreal(hyprel``{%n. X n})) = \
\      Abs_hcomplex(hcomplexrel `` {%n. f (X n)})";
by (res_inst_tac [("f","Abs_hcomplex")] arg_cong 1);
by Auto_tac;
by (Ultra_tac 1);
qed "starfunRC";

Goalw [starfunCR_def]
      "( *fcR* f) (Abs_hcomplex(hcomplexrel``{%n. X n})) = \
\      Abs_hypreal(hyprel `` {%n. f (X n)})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by (auto_tac (clasimpset() addIffs [hcomplexrel_iff]));
by (Ultra_tac 1);
qed "starfunCR";

(**  multiplication: ( *f ) x ( *g ) = *(f x g) **)

Goal "( *fc* f) z * ( *fc* g) z = ( *fc* (%x. f x * g x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(), simpset() addsimps [starfunC,hcomplex_mult]));
qed "starfunC_mult";
Addsimps [starfunC_mult RS sym];

Goal "( *fRc* f) z * ( *fRc* g) z = ( *fRc* (%x. f x * g x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [starfunRC,hcomplex_mult]));
qed "starfunRC_mult";
Addsimps [starfunRC_mult RS sym];

Goal "( *fcR* f) z * ( *fcR* g) z = ( *fcR* (%x. f x * g x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(), simpset() addsimps [starfunCR,hypreal_mult]));
qed "starfunCR_mult";
Addsimps [starfunCR_mult RS sym];

(**  addition: ( *f ) + ( *g ) = *(f + g)  **)

Goal "( *fc* f) z + ( *fc* g) z = ( *fc* (%x. f x + g x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(), simpset() addsimps [starfunC,hcomplex_add]));
qed "starfunC_add";
Addsimps [starfunC_add RS sym];

Goal "( *fRc* f) z + ( *fRc* g) z = ( *fRc* (%x. f x + g x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [starfunRC,hcomplex_add]));
qed "starfunRC_add";
Addsimps [starfunRC_add RS sym];

Goal "( *fcR* f) z + ( *fcR* g) z = ( *fcR* (%x. f x + g x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(), simpset() addsimps [starfunCR,hypreal_add]));
qed "starfunCR_add";
Addsimps [starfunCR_add RS sym];

(**  uminus **)
Goal "( *fc* (%x. - f x)) x = - ( *fc* f) x";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunC, hcomplex_minus]));
qed "starfunC_minus";
Addsimps [starfunC_minus];

Goal "( *fRc* (%x. - f x)) x = - ( *fRc* f) x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfunRC, hcomplex_minus]));
qed "starfunRC_minus";
Addsimps [starfunRC_minus];

Goal "( *fcR* (%x. - f x)) x = - ( *fcR* f) x";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunCR, hypreal_minus]));
qed "starfunCR_minus";
Addsimps [starfunCR_minus];

(**  addition: ( *f ) - ( *g ) = *(f - g)  **)

Goalw [hcomplex_diff_def,complex_diff_def]
  "( *fc* f) xa  - ( *fc* g) xa = ( *fc* (%x. f x - g x)) xa";
by (auto_tac (claset(),simpset() addsimps [starfunC_minus,starfunC_add RS sym]));
qed "starfunC_diff";
Addsimps [starfunC_diff RS sym];

Goalw [hcomplex_diff_def,complex_diff_def]
  "( *fRc* f) xa  - ( *fRc* g) xa = ( *fRc* (%x. f x - g x)) xa";
by (auto_tac (claset(),simpset() addsimps [starfunRC_minus,starfunRC_add RS sym]));
qed "starfunRC_diff";
Addsimps [starfunRC_diff RS sym];

Goalw [hypreal_diff_def,real_diff_def]
  "( *fcR* f) xa  - ( *fcR* g) xa = ( *fcR* (%x. f x - g x)) xa";
by (auto_tac (claset(),simpset() addsimps [starfunCR_minus,starfunCR_add RS sym]));
qed "starfunCR_diff";
Addsimps [starfunCR_diff RS sym];

(**  composition: ( *f ) o ( *g ) = *(f o g) **)

Goal "(%x. ( *fc* f) (( *fc* g) x)) = *fc* (%x. f (g x))"; 
by (rtac ext 1);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunC]));
qed "starfunC_o2";

Goalw [o_def] "( *fc* f) o ( *fc* g) = ( *fc* (f o g))";
by (simp_tac (simpset() addsimps [starfunC_o2]) 1);
qed "starfunC_o";

Goal "(%x. ( *fc* f) (( *fRc* g) x)) = *fRc* (%x. f (g x))"; 
by (rtac ext 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfunRC,starfunC]));
qed "starfunC_starfunRC_o2";

Goal "(%x. ( *f* f) (( *fcR* g) x)) = *fcR* (%x. f (g x))"; 
by (rtac ext 1);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunCR,starfun]));
qed "starfun_starfunCR_o2";

Goalw [o_def] "( *fc* f) o ( *fRc* g) = ( *fRc* (f o g))";
by (simp_tac (simpset() addsimps [starfunC_starfunRC_o2]) 1);
qed "starfunC_starfunRC_o";

Goalw [o_def] "( *f* f) o ( *fcR* g) = ( *fcR* (f o g))";
by (simp_tac (simpset() addsimps [starfun_starfunCR_o2]) 1);
qed "starfun_starfunCR_o";

Goal "( *fc* (%x. k)) z = hcomplex_of_complex k";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(), simpset() addsimps [starfunC, hcomplex_of_complex_def]));
qed "starfunC_const_fun";
Addsimps [starfunC_const_fun];

Goal "( *fRc* (%x. k)) z = hcomplex_of_complex k";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [starfunRC, hcomplex_of_complex_def]));
qed "starfunRC_const_fun";
Addsimps [starfunRC_const_fun];

Goal "( *fcR* (%x. k)) z = hypreal_of_real k";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(), simpset() addsimps [starfunCR, hypreal_of_real_def]));
qed "starfunCR_const_fun";
Addsimps [starfunCR_const_fun];

Goal "inverse (( *fc* f) x) = ( *fc* (%x. inverse (f x))) x";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(), simpset() addsimps [starfunC, hcomplex_inverse]));
qed "starfunC_inverse";
Addsimps [starfunC_inverse RS sym];

Goal "inverse (( *fRc* f) x) = ( *fRc* (%x. inverse (f x))) x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [starfunRC, hcomplex_inverse]));
qed "starfunRC_inverse";
Addsimps [starfunRC_inverse RS sym];

Goal "inverse (( *fcR* f) x) = ( *fcR* (%x. inverse (f x))) x";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(), simpset() addsimps [starfunCR, hypreal_inverse]));
qed "starfunCR_inverse";
Addsimps [starfunCR_inverse RS sym];

Goal "( *fc* f) (hcomplex_of_complex a) = hcomplex_of_complex (f a)";
by (auto_tac (claset(),
      simpset() addsimps [starfunC,hcomplex_of_complex_def]));
qed "starfunC_eq";
Addsimps [starfunC_eq];

Goal "( *fRc* f) (hypreal_of_real a) = hcomplex_of_complex (f a)";
by (auto_tac (claset(),
      simpset() addsimps [starfunRC,hcomplex_of_complex_def,hypreal_of_real_def]));
qed "starfunRC_eq";
Addsimps [starfunRC_eq];

Goal "( *fcR* f) (hcomplex_of_complex a) = hypreal_of_real (f a)";
by (auto_tac (claset(),
      simpset() addsimps [starfunCR,hcomplex_of_complex_def,hypreal_of_real_def]));
qed "starfunCR_eq";
Addsimps [starfunCR_eq];

Goal "( *fc* f) (hcomplex_of_complex a) @c= hcomplex_of_complex (f a)";
by (Auto_tac);
qed "starfunC_capprox";

Goal "( *fRc* f) (hypreal_of_real a) @c= hcomplex_of_complex (f a)";
by (Auto_tac);
qed "starfunRC_capprox";

Goal "( *fcR* f) (hcomplex_of_complex a) @= hypreal_of_real (f a)";
by (Auto_tac);
qed "starfunCR_approx";

(*
Goal "( *fcNat* (%n. z ^ n)) N = (hcomplex_of_complex z) hcpow N";
*)

Goalw [hypnat_of_nat_def] 
   "( *fc* (%z. z ^ n)) Z = Z hcpow hypnat_of_nat n";
by (res_inst_tac [("z","Z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(), simpset() addsimps [hcpow,starfunC]));
qed "starfunC_hcpow";

Goal "( *fc* (%h. f (x + h))) xa  = ( *fc* f) (hcomplex_of_complex  x + xa)";
by (res_inst_tac [("z","xa")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunC,
    hcomplex_of_complex_def,hcomplex_add]));
qed "starfunC_lambda_cancel";

Goal "( *fcR* (%h. f (x + h))) xa  = ( *fcR* f) (hcomplex_of_complex  x + xa)";
by (res_inst_tac [("z","xa")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunCR,
    hcomplex_of_complex_def,hcomplex_add]));
qed "starfunCR_lambda_cancel";

Goal "( *fRc* (%h. f (x + h))) xa  = ( *fRc* f) (hypreal_of_real x + xa)";
by (res_inst_tac [("z","xa")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfunRC,
    hypreal_of_real_def,hypreal_add]));
qed "starfunRC_lambda_cancel";

Goal "( *fc* (%h. f(g(x + h)))) xa = ( *fc* (f o g)) (hcomplex_of_complex x + xa)";
by (res_inst_tac [("z","xa")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunC,
    hcomplex_of_complex_def,hcomplex_add]));
qed "starfunC_lambda_cancel2";

Goal "( *fcR* (%h. f(g(x + h)))) xa = ( *fcR* (f o g)) (hcomplex_of_complex x + xa)";
by (res_inst_tac [("z","xa")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunCR,
    hcomplex_of_complex_def,hcomplex_add]));
qed "starfunCR_lambda_cancel2";

Goal "( *fRc* (%h. f(g(x + h)))) xa = ( *fRc* (f o g)) (hypreal_of_real x + xa)";
by (res_inst_tac [("z","xa")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfunRC,
    hypreal_of_real_def,hypreal_add]));
qed "starfunRC_lambda_cancel2";

Goal "[| ( *fc* f) xa @c= l; ( *fc* g) xa @c= m; \
\                 l: CFinite; m: CFinite  \
\              |] ==>  ( *fc* (%x. f x * g x)) xa @c= l * m";
by (dtac capprox_mult_CFinite 1);
by (REPEAT(assume_tac 1));
by (auto_tac (claset() addIs [capprox_sym RSN (2,capprox_CFinite)],
              simpset()));
qed "starfunC_mult_CFinite_capprox";

Goal "[| ( *fcR* f) xa @= l; ( *fcR* g) xa @= m; \
\                 l: HFinite; m: HFinite  \
\              |] ==>  ( *fcR* (%x. f x * g x)) xa @= l * m";
by (dtac approx_mult_HFinite 1);
by (REPEAT(assume_tac 1));
by (auto_tac (claset() addIs [approx_sym RSN (2,approx_HFinite)],
              simpset()));
qed "starfunCR_mult_HFinite_capprox";

Goal "[| ( *fRc* f) xa @c= l; ( *fRc* g) xa @c= m; \
\                 l: CFinite; m: CFinite  \
\              |] ==>  ( *fRc* (%x. f x * g x)) xa @c= l * m";
by (dtac capprox_mult_CFinite 1);
by (REPEAT(assume_tac 1));
by (auto_tac (claset() addIs [capprox_sym RSN (2,capprox_CFinite)],
              simpset()));
qed "starfunRC_mult_CFinite_capprox";

Goal "[| ( *fc* f) xa @c= l; ( *fc* g) xa @c= m \
\              |] ==>  ( *fc* (%x. f x + g x)) xa @c= l + m";
by (auto_tac (claset() addIs [capprox_add], simpset()));
qed "starfunC_add_capprox";

Goal "[| ( *fRc* f) xa @c= l; ( *fRc* g) xa @c= m \
\              |] ==>  ( *fRc* (%x. f x + g x)) xa @c= l + m";
by (auto_tac (claset() addIs [capprox_add], simpset()));
qed "starfunRC_add_capprox";

Goal "[| ( *fcR* f) xa @= l; ( *fcR* g) xa @= m \
\              |] ==>  ( *fcR* (%x. f x + g x)) xa @= l + m";
by (auto_tac (claset() addIs [approx_add], simpset()));
qed "starfunCR_add_approx";

Goal "*fcR* cmod = hcmod";
by (rtac ext 1);
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunCR,hcmod]));
qed "starfunCR_cmod";

Goal "( *fc* inverse) x = inverse(x)";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunC,hcomplex_inverse]));
qed "starfunC_inverse_inverse";

Goalw [hcomplex_divide_def,complex_divide_def]
  "( *fc* f) xa  / ( *fc* g) xa = ( *fc* (%x. f x / g x)) xa";
by Auto_tac;
qed "starfunC_divide";
Addsimps [starfunC_divide RS sym];

Goalw [hypreal_divide_def,real_divide_def]
  "( *fcR* f) xa  / ( *fcR* g) xa = ( *fcR* (%x. f x / g x)) xa";
by Auto_tac;
qed "starfunCR_divide";
Addsimps [starfunCR_divide RS sym];

Goalw [hcomplex_divide_def,complex_divide_def]
  "( *fRc* f) xa  / ( *fRc* g) xa = ( *fRc* (%x. f x / g x)) xa";
by Auto_tac;
qed "starfunRC_divide";
Addsimps [starfunRC_divide RS sym];

(*-----------------------------------------------------------------------------------*)
(* Internal functions - some redundancy with *fc* now                                *)
(*-----------------------------------------------------------------------------------*)

Goalw [congruent_def] 
      "congruent hcomplexrel (%X. hcomplexrel``{%n. f n (X n)})";
by (auto_tac (clasimpset() addIffs [hcomplexrel_iff]));
by (ALLGOALS(Fuf_tac));
qed "starfunC_n_congruent";

Goalw [starfunC_n_def]
     "( *fcn* f) (Abs_hcomplex(hcomplexrel``{%n. X n})) = \
\     Abs_hcomplex(hcomplexrel `` {%n. f n (X n)})";
by (res_inst_tac [("f","Abs_hcomplex")] arg_cong 1);
by (auto_tac (clasimpset() addIffs [hcomplexrel_iff]));
by (Ultra_tac 1);
qed "starfunC_n";

(**  multiplication: ( *fn ) x ( *gn ) = *(fn x gn) **)

Goal "( *fcn* f) z * ( *fcn* g) z = ( *fcn* (% i x. f i x * g i x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(), simpset() addsimps [starfunC_n,hcomplex_mult]));
qed "starfunC_n_mult";

(**  addition: ( *fn ) + ( *gn ) = *(fn + gn) **)

Goal "( *fcn* f) z + ( *fcn* g) z = ( *fcn* (%i x. f i x + g i x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(), simpset() addsimps [starfunC_n,hcomplex_add]));
qed "starfunC_n_add";

(** uminus **)

Goal "- ( *fcn* g) z = ( *fcn* (%i x. - g i x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(), simpset() addsimps [starfunC_n,hcomplex_minus]));
qed "starfunC_n_minus";

(** subtraction: ( *fn ) - ( *gn ) = *(fn - gn) **)

Goalw [hcomplex_diff_def,complex_diff_def] 
   "( *fcn* f) z - ( *fcn* g) z = ( *fcn* (%i x. f i x - g i x)) z";
by (auto_tac (claset(), 
          simpset() addsimps [starfunC_n_add,starfunC_n_minus]));
qed "starfunNat_n_diff";

(** composition: ( *fn ) o ( *gn ) = *(fn o gn) **)
 
Goal "( *fcn* (%i x. k)) z = hcomplex_of_complex  k";
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(), 
       simpset() addsimps [starfunC_n, hcomplex_of_complex_def]));
qed "starfunC_n_const_fun";
Addsimps [starfunC_n_const_fun];

Goal "( *fcn* f) (hcomplex_of_complex n) = Abs_hcomplex(hcomplexrel `` {%i. f i n})";
by (auto_tac (claset(), simpset() addsimps [starfunC_n,hcomplex_of_complex_def]));
qed "starfunC_n_eq";
Addsimps [starfunC_n_eq];

Goal "(( *fc* f) = ( *fc* g)) = (f = g)";
by Auto_tac;
by (rtac ext 1 THEN rtac ccontr 1);
by (dres_inst_tac [("x","hcomplex_of_complex(x)")] fun_cong 1);
by (auto_tac (claset(), simpset() addsimps [starfunC,hcomplex_of_complex_def]));
qed "starfunC_eq_iff";

Goal "(( *fRc* f) = ( *fRc* g)) = (f = g)";
by Auto_tac;
by (rtac ext 1 THEN rtac ccontr 1);
by (dres_inst_tac [("x","hypreal_of_real(x)")] fun_cong 1);
by Auto_tac;
qed "starfunRC_eq_iff";

Goal "(( *fcR* f) = ( *fcR* g)) = (f = g)";
by Auto_tac;
by (rtac ext 1 THEN rtac ccontr 1);
by (dres_inst_tac [("x","hcomplex_of_complex(x)")] fun_cong 1);
by Auto_tac;
qed "starfunCR_eq_iff";

(*** more theorems ***)

Goal "(( *fc* f) x = z) = ((( *fcR* (%x. Re(f x))) x = hRe (z)) & \
\                         (( *fcR* (%x. Im(f x))) x = hIm (z)))";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunCR,starfunC,
    hIm,hRe,complex_Re_Im_cancel_iff]));
by (ALLGOALS(Ultra_tac));
qed "starfunC_eq_Re_Im_iff";

Goal "(( *fc* f) x @c= z) = ((( *fcR* (%x. Re(f x))) x @= hRe (z)) & \
\                           (( *fcR* (%x. Im(f x))) x @= hIm (z)))";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (res_inst_tac [("z","z")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunCR,starfunC,
    hIm,hRe,capprox_approx_iff]));
qed "starfunC_approx_Re_Im_iff";

Goal "x @c= hcomplex_of_complex a ==> ( *fc* (%x. x)) x @c= hcomplex_of_complex  a";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunC]));
qed "starfunC_Idfun_capprox";

Goal "( *fc* (%x. x)) x = x";
by (res_inst_tac [("z","x")] eq_Abs_hcomplex 1);
by (auto_tac (claset(),simpset() addsimps [starfunC]));
qed "starfunC_Id";
Addsimps [starfunC_Id];  
