(*  Title       : NatStar.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : *-transforms in NSA which extends 
                  sets of reals, and nat=>real, 
                  nat=>nat functions
*) 

Goalw [starsetNat_def] 
      "*sNat*(UNIV::nat set) = (UNIV::hypnat set)";
by (auto_tac (claset(), simpset() addsimps [FreeUltrafilterNat_Nat_set]));
qed "NatStar_real_set";

Goalw [starsetNat_def] "*sNat* {} = {}";
by (Step_tac 1);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (dres_inst_tac [("x","%n. xa n")] bspec 1);
by (auto_tac (claset(), simpset() addsimps [FreeUltrafilterNat_empty]));
qed "NatStar_empty_set";

Addsimps [NatStar_empty_set];

Goalw [starsetNat_def] 
      "*sNat* (A Un B) = *sNat* A Un *sNat* B";
by (Auto_tac);
by (REPEAT(blast_tac (claset() addIs [FreeUltrafilterNat_subset]) 2));
by (dtac FreeUltrafilterNat_Compl_mem 1);
by (dtac bspec 1 THEN assume_tac 1);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (Auto_tac);
by (Fuf_tac 1);
qed "NatStar_Un";

Goalw [starsetNat_n_def] 
      "*sNatn* (%n. (A n) Un (B n)) = *sNatn* A Un *sNatn* B";
by Auto_tac;
by (dres_inst_tac [("x","Xa")] bspec 1);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 2);
by (auto_tac (claset() addSDs [bspec], simpset()));
by (TRYALL(Ultra_tac));
qed "starsetNat_n_Un";

Goalw [InternalNatSets_def]
     "[| X : InternalNatSets; Y : InternalNatSets |] \
\     ==> (X Un Y) : InternalNatSets";
by (auto_tac (claset(),
         simpset() addsimps [starsetNat_n_Un RS sym]));
qed "InternalNatSets_Un";

Goalw [starsetNat_def] "*sNat* (A Int B) = *sNat* A Int *sNat* B";
by (Auto_tac);
by (blast_tac (claset() addIs [FreeUltrafilterNat_Int,
    FreeUltrafilterNat_subset]) 3);
by (REPEAT(blast_tac (claset() addIs 
    [FreeUltrafilterNat_subset]) 1));
qed "NatStar_Int";

Goalw [starsetNat_n_def] 
      "*sNatn* (%n. (A n) Int (B n)) = *sNatn* A Int *sNatn* B";
by (Auto_tac);
by (auto_tac (claset() addSDs [bspec],
         simpset()));
by (TRYALL(Ultra_tac));
qed "starsetNat_n_Int";

Goalw [InternalNatSets_def]
     "[| X : InternalNatSets; Y : InternalNatSets |] \
\     ==> (X Int Y) : InternalNatSets";
by (auto_tac (claset(),
         simpset() addsimps [starsetNat_n_Int RS sym]));
qed "InternalNatSets_Int";

Goalw [starsetNat_def] "*sNat* (-A) = -(*sNat* A)";
by (Auto_tac);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 2);
by (REPEAT(Step_tac 1) THEN Auto_tac);
by (TRYALL(Ultra_tac));
qed "NatStar_Compl";

Goalw [starsetNat_n_def] "*sNatn* ((%n. - A n)) = -(*sNatn* A)";
by (Auto_tac);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 2);
by (REPEAT(Step_tac 1) THEN Auto_tac);
by (TRYALL(Ultra_tac));
qed "starsetNat_n_Compl";

Goalw [InternalNatSets_def]
     "X :InternalNatSets ==> -X : InternalNatSets";
by (auto_tac (claset(),
         simpset() addsimps [starsetNat_n_Compl RS sym]));
qed "InternalNatSets_Compl";

Goalw [starsetNat_n_def] 
      "*sNatn* (%n. (A n) - (B n)) = *sNatn* A - *sNatn* B";
by (Auto_tac);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 2);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 3);
by (auto_tac (claset() addSDs [bspec], simpset()));
by (TRYALL(Ultra_tac));
qed "starsetNat_n_diff";

Goalw [InternalNatSets_def]
     "[| X : InternalNatSets; Y : InternalNatSets |] \
\     ==> (X - Y) : InternalNatSets";
by (auto_tac (claset(), simpset() addsimps [starsetNat_n_diff RS sym]));
qed "InternalNatSets_diff";

Goalw [starsetNat_def] "A <= B ==> *sNat* A <= *sNat* B";
by (REPEAT(blast_tac (claset() addIs [FreeUltrafilterNat_subset]) 1));
qed "NatStar_subset";

Goalw [starsetNat_def,hypnat_of_nat_def] 
          "a : A ==> hypnat_of_nat a : *sNat* A";
by (auto_tac (claset() addIs [FreeUltrafilterNat_subset],
         simpset()));
qed "NatStar_mem";

Goalw [starsetNat_def] "hypnat_of_nat `` A <= *sNat* A";
by (auto_tac (claset(), simpset() addsimps [hypnat_of_nat_def]));
by (blast_tac (claset() addIs [FreeUltrafilterNat_subset]) 1);
qed "NatStar_hypreal_of_real_image_subset";

Goal "SHNat <= *sNat* (UNIV:: nat set)";
by (simp_tac (simpset() addsimps [SHNat_hypnat_of_nat_iff,
    NatStar_hypreal_of_real_image_subset]) 1);
qed "NatStar_SHNat_subset";

Goalw [starsetNat_def] 
      "*sNat* X Int SHNat = hypnat_of_nat `` X";
by (auto_tac (claset(),
         simpset() addsimps 
           [hypnat_of_nat_def,SHNat_def]));
by (fold_tac [hypnat_of_nat_def]);
by (rtac imageI 1 THEN rtac ccontr 1);
by (dtac bspec 1);
by (rtac lemma_hypnatrel_refl 1);
by (blast_tac (claset() addIs [FreeUltrafilterNat_subset]) 2);
by (Auto_tac);
qed "NatStar_hypreal_of_real_Int";

Goal "x ~: hypnat_of_nat `` A ==> ALL y: A. x ~= hypnat_of_nat y";
by (Auto_tac);
qed "lemma_not_hypnatA";

Goalw [starsetNat_n_def,starsetNat_def] "*sNat* X = *sNatn* (%n. X)";
by Auto_tac;
qed "starsetNat_starsetNat_n_eq";

Goalw [InternalNatSets_def] "(*sNat* X) : InternalNatSets";
by (auto_tac (claset(),
         simpset() addsimps [starsetNat_starsetNat_n_eq]));
qed "InternalNatSets_starsetNat_n";
Addsimps [InternalNatSets_starsetNat_n];

Goal "X : InternalNatSets ==> UNIV - X : InternalNatSets";
by (auto_tac (claset() addIs [InternalNatSets_Compl], simpset()));
qed "InternalNatSets_UNIV_diff";

(*------------------------------------------------------------------ 
   Nonstandard extension of a set (defined using a constant 
   sequence) as a special case of an internal set
 -----------------------------------------------------------------*)

Goalw [starsetNat_n_def,starsetNat_def] 
     "ALL n. (As n = A) ==> *sNatn* As = *sNat* A";
by (Auto_tac);
qed "starsetNat_n_starsetNat";

(*------------------------------------------------------
   Theorems about nonstandard extensions of functions
 ------------------------------------------------------*)

(*------------------------------------------------------------------ 
   Nonstandard extension of a function (defined using a constant 
   sequence) as a special case of an internal function
 -----------------------------------------------------------------*)

Goalw [starfunNat_n_def,starfunNat_def] 
     "ALL n. (F n = f) ==> *fNatn* F = *fNat* f";
by (Auto_tac);
qed "starfunNat_n_starfunNat";

Goalw [starfunNat2_n_def,starfunNat2_def] 
     "ALL n. (F n = f) ==> *fNat2n* F = *fNat2* f";
by (Auto_tac);
qed "starfunNat2_n_starfunNat2";

Goalw [congruent_def] 
      "congruent hypnatrel (%X. hypnatrel^^{%n. f (X n)})";
by (safe_tac (claset()));
by (ALLGOALS(Fuf_tac));
qed "starfunNat_congruent";

(* f::nat=>real *)
Goalw [starfunNat_def]
      "(*fNat* f) (Abs_hypnat(hypnatrel^^{%n. X n})) = \
\      Abs_hypreal(hyprel ^^ {%n. f (X n)})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by (simp_tac (simpset() addsimps 
   [hyprel_in_hypreal RS Abs_hypreal_inverse]) 1);
by (Auto_tac THEN Fuf_tac 1);
qed "starfunNat";

(* f::nat=>nat *)
Goalw [starfunNat2_def]
      "(*fNat2* f) (Abs_hypnat(hypnatrel^^{%n. X n})) = \
\      Abs_hypnat(hypnatrel ^^ {%n. f (X n)})";
by (res_inst_tac [("f","Abs_hypnat")] arg_cong 1);
by (simp_tac (simpset() addsimps 
   [hypnatrel_in_hypnat RS Abs_hypnat_inverse,
    [equiv_hypnatrel, starfunNat_congruent] MRS UN_equiv_class]) 1);
qed "starfunNat2";

(*---------------------------------------------
  multiplication: ( *f ) x ( *g ) = *(f x g)  
 ---------------------------------------------*)
Goal "(*fNat* f) z * (*fNat* g) z = (*fNat* (%x. f x * g x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat,hypreal_mult]));
qed "starfunNat_mult";

Goal "(*fNat2* f) z * (*fNat2* g) z = (*fNat2* (%x. f x * g x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat2,hypnat_mult]));
qed "starfunNat2_mult";

(*---------------------------------------
  addition: ( *f ) + ( *g ) = *(f + g)  
 ---------------------------------------*)
Goal "(*fNat* f) z + (*fNat* g) z = (*fNat* (%x. f x + g x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat,hypreal_add]));
qed "starfunNat_add";

Goal "(*fNat2* f) z + (*fNat2* g) z = (*fNat2* (%x. f x + g x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat2,hypnat_add]));
qed "starfunNat2_add";

Goal "(*fNat2* f) z - (*fNat2* g) z = (*fNat2* (%x. f x - g x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat2, hypnat_minus]));
qed "starfunNat2_minus";

(*--------------------------------------
  composition: ( *f ) o ( *g ) = *(f o g)  
 ---------------------------------------*)
(***** ( *f::nat=>real ) o ( *g::nat=>nat ) = *(f o g) *****)
 
Goal "(*fNat* f) o (*fNat2* g) = (*fNat* (f o g))";
by (rtac ext 1);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat2, starfunNat]));
qed "starfunNatNat2_o";

Goal "(%x. (*fNat* f) ((*fNat2* g) x)) = (*fNat* (%x. f(g x)))";
by (rtac ( simplify (simpset() addsimps [o_def]) starfunNatNat2_o) 1);
qed "starfunNatNat2_o2";

(***** ( *f::nat=>nat ) o ( *g::nat=>nat ) = *(f o g) *****)
Goal "(*fNat2* f) o (*fNat2* g) = (*fNat2* (f o g))";
by (rtac ext 1);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat2]));
qed "starfunNat2_o";

(***** ( *f::real=>real ) o ( *g::nat=>real ) = *(f o g) *****)

Goal "(*f* f) o (*fNat* g) = (*fNat* (f o g))"; 
by (rtac ext 1);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat,starfun]));
qed "starfun_stafunNat_o";

Goal "(%x. (*f* f) ((*fNat* g) x)) = (*fNat* (%x. f (g x)))"; 
by (rtac ( simplify (simpset() addsimps [o_def]) starfun_stafunNat_o) 1);
qed "starfun_stafunNat_o2";

(*--------------------------------------
  NS extension of constant function
 --------------------------------------*)
Goal "(*fNat* (%x. k)) z = hypreal_of_real k";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat, hypreal_of_real_def]));
qed "starfunNat_const_fun";
Addsimps [starfunNat_const_fun];

Goal "(*fNat2* (%x. k)) z = hypnat_of_nat  k";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat2, hypnat_of_nat_def]));
qed "starfunNat2_const_fun";

Addsimps [starfunNat2_const_fun];

Goal "- (*fNat* f) x = (*fNat* (%x. - f x)) x";
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat, hypreal_minus]));
qed "starfunNat_minus";

Goal "inverse ((*fNat* f) x) = (*fNat* (%x. inverse (f x))) x";
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat, hypreal_inverse]));
qed "starfunNat_inverse";

(*--------------------------------------------------------
   extented function has same solution as its standard
   version for natural arguments. i.e they are the same
   for all natural arguments (c.f. Hoskins pg. 107- SEQ)
 -------------------------------------------------------*)

Goal "(*fNat* f) (hypnat_of_nat a) = hypreal_of_real (f a)";
by (auto_tac (claset(),
      simpset() addsimps [starfunNat,hypnat_of_nat_def,hypreal_of_real_def]));
qed "starfunNat_eq";

Addsimps [starfunNat_eq];

Goal "(*fNat2* f) (hypnat_of_nat a) = hypnat_of_nat (f a)";
by (auto_tac (claset(), simpset() addsimps [starfunNat2,hypnat_of_nat_def]));
qed "starfunNat2_eq";

Addsimps [starfunNat2_eq];

Goal "(*fNat* f) (hypnat_of_nat a) @= hypreal_of_real (f a)";
by (Auto_tac);
qed "starfunNat_inf_close";


(*-----------------------------------------------------------------
    Example of transfer of a property from reals to hyperreals
    --- used for limit comparison of sequences
 ----------------------------------------------------------------*)
Goal "ALL n. N <= n --> f n <= g n \
\         ==> ALL n. hypnat_of_nat N <= n --> (*fNat* f) n <= (*fNat* g) n";
by (Step_tac 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
         simpset() addsimps [starfunNat, hypnat_of_nat_def,hypreal_le,
                             hypreal_less, hypnat_le,hypnat_less]));
by (Ultra_tac 1);
by Auto_tac;
qed "starfun_le_mono";

(*****----- and another -----*****) 
Goal "ALL n. N <= n --> f n < g n \
\         ==> ALL n. hypnat_of_nat N <= n --> (*fNat* f) n < (*fNat* g) n";
by (Step_tac 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
         simpset() addsimps [starfunNat, hypnat_of_nat_def,hypreal_le,
                             hypreal_less, hypnat_le,hypnat_less]));
by (Ultra_tac 1);
by Auto_tac;
qed "starfun_less_mono";

(*----------------------------------------------------------------
            NS extension when we displace argument by one
 ---------------------------------------------------------------*)
Goal "(*fNat* (%n. f (Suc n))) N = (*fNat* f) (N + 1hn)";
by (res_inst_tac [("z","N")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
         simpset() addsimps [starfunNat, hypnat_one_def,hypnat_add]));
qed "starfunNat_shift_one";

(*----------------------------------------------------------------
                 NS extension with rabs    
 ---------------------------------------------------------------*)
Goal "(*fNat* (%n. abs (f n))) N = abs((*fNat* f) N)";
by (res_inst_tac [("z","N")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat, hypreal_hrabs]));
qed "starfunNat_rabs";

(*----------------------------------------------------------------
       The hyperpow function as a NS extension of realpow
 ----------------------------------------------------------------*)
Goal "(*fNat* (%n. r ^ n)) N = (hypreal_of_real r) pow N";
by (res_inst_tac [("z","N")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
         simpset() addsimps [hyperpow, hypreal_of_real_def,starfunNat]));
qed "starfunNat_pow";

Goal "(*fNat* (%n. (X n) ^ m)) N = (*fNat* X) N pow hypnat_of_nat m";
by (res_inst_tac [("z","N")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
         simpset() addsimps [hyperpow, hypnat_of_nat_def,starfunNat]));
qed "starfunNat_pow2";

Goalw [hypnat_of_nat_def] "(*f* (%r. r ^ n)) R = (R) pow hypnat_of_nat n";
by (res_inst_tac [("z","R")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [hyperpow,starfun]));
qed "starfun_pow";

(*----------------------------------------------------- 
   hypreal_of_hypnat as NS extension of real_of_nat! 
-------------------------------------------------------*)
Goal "(*fNat* real_of_nat) = hypreal_of_hypnat";
by (rtac ext 1);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_of_hypnat,starfunNat]));
qed "starfunNat_real_of_nat";

Goal "N : HNatInfinite \
\  ==> (*fNat* (%x. inverse(real_of_nat x))) N = inverse(hypreal_of_hypnat N)";
by (res_inst_tac [("f1","inverse")]  (starfun_stafunNat_o2 RS subst) 1);
by (subgoal_tac "hypreal_of_hypnat N ~= #0" 1);
by (auto_tac (claset(), 
       simpset() addsimps [starfunNat_real_of_nat, starfun_inverse_inverse]));
qed "starfunNat_inverse_real_of_nat_eq";

(*----------------------------------------------------------
     Internal functions - some redundancy with *fNat* now
 ---------------------------------------------------------*)
Goalw [congruent_def] 
      "congruent hypnatrel (%X. hypnatrel^^{%n. f n (X n)})";
by (safe_tac (claset()));
by (ALLGOALS(Fuf_tac));
qed "starfunNat_n_congruent";

Goalw [starfunNat_n_def]
     "(*fNatn* f) (Abs_hypnat(hypnatrel^^{%n. X n})) = \
\     Abs_hypreal(hyprel ^^ {%n. f n (X n)})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by Auto_tac;
by (Ultra_tac 1);
qed "starfunNat_n";

(*-------------------------------------------------
  multiplication: ( *fn ) x ( *gn ) = *(fn x gn)  
 -------------------------------------------------*)
Goal "(*fNatn* f) z * (*fNatn* g) z = (*fNatn* (% i x. f i x * g i x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat_n,hypreal_mult]));
qed "starfunNat_n_mult";

(*-----------------------------------------------
  addition: ( *fn ) + ( *gn ) = *(fn + gn)  
 -----------------------------------------------*)
Goal "(*fNatn* f) z + (*fNatn* g) z = (*fNatn* (%i x. f i x + g i x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat_n,hypreal_add]));
qed "starfunNat_n_add";

(*-------------------------------------------------
  subtraction: ( *fn ) + -( *gn ) = *(fn + -gn)  
 -------------------------------------------------*)
Goal "(*fNatn* f) z + -(*fNatn* g) z = (*fNatn* (%i x. f i x + -g i x)) z";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (auto_tac (claset(), 
          simpset() addsimps [starfunNat_n, hypreal_minus,hypreal_add]));
qed "starfunNat_n_add_minus";

(*--------------------------------------------------
  composition: ( *fn ) o ( *gn ) = *(fn o gn)  
 -------------------------------------------------*)
 
Goal "(*fNatn* (%i x. k)) z = hypreal_of_real  k";
by (res_inst_tac [("z","z")] eq_Abs_hypnat 1);
by (auto_tac (claset(), 
       simpset() addsimps [starfunNat_n, hypreal_of_real_def]));
qed "starfunNat_n_const_fun";

Addsimps [starfunNat_n_const_fun];

Goal "- (*fNatn* f) x = (*fNatn* (%i x. - (f i) x)) x";
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat_n, hypreal_minus]));
qed "starfunNat_n_minus";

Goal "(*fNatn* f) (hypnat_of_nat n) = Abs_hypreal(hyprel ^^ {%i. f i n})";
by (auto_tac (claset(), simpset() addsimps [starfunNat_n,hypnat_of_nat_def]));
qed "starfunNat_n_eq";
Addsimps [starfunNat_n_eq];

Goal "((*fNat* f) = (*fNat* g)) = (f = g)";
by Auto_tac;
by (rtac ext 1 THEN rtac ccontr 1);
by (dres_inst_tac [("x","hypnat_of_nat(x)")] fun_cong 1);
by (auto_tac (claset(), simpset() addsimps [starfunNat,hypnat_of_nat_def]));
qed "starfun_eq_iff";
