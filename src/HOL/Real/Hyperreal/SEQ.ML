(*  Title       : SEQ.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Theory of sequence and series of real numbers
*) 

(*---------------------------------------------------------------------------
   Example of an hypersequence (i.e. an extended standard sequence) 
   whose term with an hypernatural suffix is an infinitesimal i.e. 
   the whn'nth term of the hypersequence is a member of Infinitesimal 
 -------------------------------------------------------------------------- *)

Goalw [hypnat_omega_def] 
      "(*fNat* (%n::nat. inverse(real_of_posnat n))) whn : Infinitesimal";
by (auto_tac (claset(),simpset() addsimps 
    [Infinitesimal_FreeUltrafilterNat_iff,starfunNat]));
by (rtac bexI 1 THEN rtac lemma_hyprel_refl 2);
by (auto_tac (claset(),simpset() addsimps (map rename_numerals) 
    [real_of_posnat_gt_zero,real_inverse_gt_zero,abs_eqI2,
     FreeUltrafilterNat_inverse_real_of_posnat]));
qed "SEQ_Infinitesimal";

(*--------------------------------------------------------------------------
                  Rules for LIMSEQ and NSLIMSEQ etc.
 --------------------------------------------------------------------------*)

(*** LIMSEQ ***)
Goalw [LIMSEQ_def] 
      "X ----> L ==> \
\      ALL r. #0 < r --> (EX no. ALL n. no <= n --> abs(X n + -L) < r)";
by (Asm_simp_tac 1);
qed "LIMSEQD1";

Goalw [LIMSEQ_def] 
      "[| X ----> L; #0 < r|] ==> \
\      EX no. ALL n. no <= n --> abs(X n + -L) < r";
by (Asm_simp_tac 1);
qed "LIMSEQD2";

Goalw [LIMSEQ_def] 
      "ALL r. #0 < r --> (EX no. ALL n. \
\      no <= n --> abs(X n + -L) < r) ==> X ----> L";
by (Asm_simp_tac 1);
qed "LIMSEQI";

Goalw [LIMSEQ_def] 
      "(X ----> L) = \
\      (ALL r. #0 <r --> (EX no. ALL n. no <= n --> abs(X n + -L) < r))";
by (Simp_tac 1);
qed "LIMSEQ_iff";

(*** NSLIMSEQ ***)
Goalw [NSLIMSEQ_def] 
      "X ----NS> L ==> ALL N: HNatInfinite. (*fNat* X) N @= hypreal_of_real L";
by (Asm_simp_tac 1);
qed "NSLIMSEQD1";

Goalw [NSLIMSEQ_def] 
      "[| X ----NS> L; N: HNatInfinite |] ==> (*fNat* X) N @= hypreal_of_real L";
by (Asm_simp_tac 1);
qed "NSLIMSEQD2";

Goalw [NSLIMSEQ_def] 
      "ALL N: HNatInfinite. (*fNat* X) N @= hypreal_of_real L ==> X ----NS> L";
by (Asm_simp_tac 1);
qed "NSLIMSEQI";

Goalw [NSLIMSEQ_def] 
      "(X ----NS> L) = (ALL N: HNatInfinite. (*fNat* X) N @= hypreal_of_real L)";
by (Simp_tac 1);
qed "NSLIMSEQ_iff";

(*----------------------------------------
          LIMSEQ ==> NSLIMSEQ
 ---------------------------------------*)
Goalw [LIMSEQ_def,NSLIMSEQ_def] 
      "X ----> L ==> X ----NS> L";
by (auto_tac (claset(),simpset() addsimps 
    [HNatInfinite_FreeUltrafilterNat_iff]));
by (res_inst_tac [("z","N")] eq_Abs_hypnat 1);
by (rtac (inf_close_minus_iff RS iffD2) 1);
by (auto_tac (claset(),simpset() addsimps [starfunNat,
    mem_infmal_iff RS sym,hypreal_of_real_def,
    hypreal_minus,hypreal_add,
    Infinitesimal_FreeUltrafilterNat_iff]));
by (EVERY[rtac bexI 1, rtac lemma_hyprel_refl 2, Step_tac 1]);
by (dres_inst_tac [("x","u")] spec 1 THEN Step_tac 1);
by (dres_inst_tac [("x","no")] spec 1);
by (Fuf_tac 1);
by (blast_tac (claset() addDs [less_imp_le]) 1);
qed "LIMSEQ_NSLIMSEQ";

(*-------------------------------------------------------------
          NSLIMSEQ ==> LIMSEQ
    proving NS def ==> Standard def is trickier as usual 
 -------------------------------------------------------------*)
(* the following sequence f(n) defines a hypernatural *)
(* lemmas etc. first *)
Goal "!!(f::nat=>nat). ALL n. n <= f n \
\          ==> {n. f n = 0} = {0} | {n. f n = 0} = {}";
by (Auto_tac);
by (dres_inst_tac [("x","xa")] spec 1);
by (dres_inst_tac [("x","x")] spec 2);
by (Auto_tac);
val lemma_NSLIMSEQ1 = result();

Goal "{n. f n <= Suc u} = {n. f n <= u} Un {n. f n = Suc u}";
by (auto_tac (claset(),simpset() addsimps [le_Suc_eq]));
val lemma_NSLIMSEQ2 = result();

Goal "!!(f::nat=>nat). ALL n. n <= f n \
\          ==> {n. f n = Suc u} <= {n. n <= Suc u}";
by (Auto_tac);
by (dres_inst_tac [("x","x")] spec 1);
by (Auto_tac);
val lemma_NSLIMSEQ3 = result();

Goal "!!(f::nat=>nat). ALL n. n <= f n \ 
\         ==> finite {n. f n <= u}";
by (induct_tac "u" 1);
by (auto_tac (claset(),simpset() addsimps [lemma_NSLIMSEQ2]));
by (auto_tac (claset() addIs [(lemma_NSLIMSEQ3 RS finite_subset),
    finite_nat_le_segment], simpset()));
by (dtac lemma_NSLIMSEQ1 1 THEN Step_tac 1);
by (ALLGOALS(Asm_simp_tac));
qed "NSLIMSEQ_finite_set";

Goal "- {n. u < (f::nat=>nat) n} = {n. f n <= u}";
by (auto_tac (claset() addDs [less_le_trans],
    simpset() addsimps [le_def]));
qed "Compl_less_set";

(* the index set is in the free ultrafilter *)
Goal "!!(f::nat=>nat). ALL n. n <= f n \ 
\         ==> {n. u < f n} : FreeUltrafilterNat";
by (rtac (FreeUltrafilterNat_Compl_iff2 RS iffD2) 1);
by (rtac FreeUltrafilterNat_finite 1);
by (auto_tac (claset() addDs [NSLIMSEQ_finite_set],
    simpset() addsimps [Compl_less_set]));
qed "FreeUltrafilterNat_NSLIMSEQ";

(* thus, the sequence defines an infinite hypernatural! *)
Goal "ALL n. n <= f n \
\         ==> Abs_hypnat (hypnatrel ^^ {f}) : HNatInfinite";
by (auto_tac (claset(),simpset() addsimps [HNatInfinite_FreeUltrafilterNat_iff]));
by (EVERY[rtac bexI 1, rtac lemma_hypnatrel_refl 2, Step_tac 1]);
by (etac FreeUltrafilterNat_NSLIMSEQ 1);
qed "HNatInfinite_NSLIMSEQ";

val lemmaLIM = CLAIM  "{n. X (f n) + - L = Y n} Int {n. abs (Y n) < r} <= \
\         {n. abs (X (f n) + - L) < r}";

Goal "{n. abs (X (f n) + - L) < r} Int \
\         {n. r <= abs (X (f n) + - (L::real))} = {}";
by (auto_tac (claset() addDs [real_less_le_trans] 
    addIs [real_less_irrefl], simpset()));
val lemmaLIM2 = result();

Goal "[| #0 < r; ALL n. r <= abs (X (f n) + - L); \
\          (*fNat* X) (Abs_hypnat (hypnatrel ^^ {f})) + \
\          - hypreal_of_real  L @= 0 |] ==> False";
by (auto_tac (claset(),simpset() addsimps [starfunNat,
    mem_infmal_iff RS sym,hypreal_of_real_def,
    hypreal_minus,hypreal_add,
    Infinitesimal_FreeUltrafilterNat_iff]));
by (dres_inst_tac [("x","r")] spec 1 THEN Step_tac 1);
by (dtac FreeUltrafilterNat_Int 1 THEN assume_tac 1);
by (dtac (lemmaLIM RSN (2,FreeUltrafilterNat_subset)) 1);
by (dtac FreeUltrafilterNat_all 1);
by (thin_tac "{n. abs (Y n) < r} : FreeUltrafilterNat" 1);
by (dtac FreeUltrafilterNat_Int 1 THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [lemmaLIM2,
    FreeUltrafilterNat_empty]) 1);
val lemmaLIM3 = result();

Goalw [LIMSEQ_def,NSLIMSEQ_def] 
      "X ----NS> L ==> X ----> L";
by (rtac ccontr 1 THEN Asm_full_simp_tac 1);
by (Step_tac 1);
(* skolemization step *)
by (dtac choice 1 THEN Step_tac 1);
by (dres_inst_tac [("x","Abs_hypnat(hypnatrel^^{f})")] bspec 1);
by (dtac (inf_close_minus_iff RS iffD1) 2);
by (fold_tac [real_le_def]);
by (blast_tac (claset() addIs [HNatInfinite_NSLIMSEQ]) 1);
by (blast_tac (claset() addIs [rename_numerals lemmaLIM3]) 1);
qed "NSLIMSEQ_LIMSEQ";

(* Now the all important result is trivially proved! *)
Goal "(f ----> L) = (f ----NS> L)";
by (blast_tac (claset() addIs [LIMSEQ_NSLIMSEQ,NSLIMSEQ_LIMSEQ]) 1);
qed "LIMSEQ_NSLIMSEQ_iff";

(*-------------------------------------------------------------------
                   Theorems about sequences
 ------------------------------------------------------------------*)
Goalw [NSLIMSEQ_def] "(%n. k) ----NS> k";
by (Auto_tac);
qed "NSLIMSEQ_const";

Goalw [LIMSEQ_def] "(%n. k) ----> k";
by (Auto_tac);
qed "LIMSEQ_const";

Goalw [NSLIMSEQ_def]
      "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n + Y n) ----NS> a + b";
by (auto_tac (claset() addIs [inf_close_add],
    simpset() addsimps [starfunNat_add RS sym,hypreal_of_real_add]));
qed "NSLIMSEQ_add";

Goal "[| X ----> a; Y ----> b |] ==> (%n. X n + Y n) ----> a + b";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff,
    NSLIMSEQ_add]) 1);
qed "LIMSEQ_add";

Goalw [NSLIMSEQ_def]
      "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n * Y n) ----NS> a * b";
by (auto_tac (claset() addSIs [inf_close_mult_HFinite],
    simpset() addsimps [hypreal_of_real_mult, starfunNat_mult RS sym]));
qed "NSLIMSEQ_mult";

Goal "[| X ----> a; Y ----> b |] ==> (%n. X n * Y n) ----> a * b";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff,
                                           NSLIMSEQ_mult]) 1);
qed "LIMSEQ_mult";

Goalw [NSLIMSEQ_def] 
     "X ----NS> a ==> (%n. -(X n)) ----NS> -a";
by (auto_tac (claset(), simpset() addsimps [starfunNat_minus RS sym]));
qed "NSLIMSEQ_minus";

Goal "X ----> a ==> (%n. -(X n)) ----> -a";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff,
                                           NSLIMSEQ_minus]) 1);
qed "LIMSEQ_minus";

Goal "(%n. -(X n)) ----> -a ==> X ----> a";
by (dtac LIMSEQ_minus 1);
by (Asm_full_simp_tac 1);
qed "LIMSEQ_minus_cancel";

Goal "(%n. -(X n)) ----NS> -a ==> X ----NS> a";
by (dtac NSLIMSEQ_minus 1);
by (Asm_full_simp_tac 1);
qed "NSLIMSEQ_minus_cancel";

Goal "[| X ----NS> a; Y ----NS> b |] \
\               ==> (%n. X n + -Y n) ----NS> a + -b";
by (dres_inst_tac [("X","Y")] NSLIMSEQ_minus 1);
by (auto_tac (claset(),simpset() addsimps [NSLIMSEQ_add]));
qed "NSLIMSEQ_add_minus";

Goal "[| X ----> a; Y ----> b |] \
\               ==> (%n. X n + -Y n) ----> a + -b";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff,
    NSLIMSEQ_add_minus]) 1);
qed "LIMSEQ_add_minus";

Goalw [real_diff_def] 
     "[| X ----> a; Y ----> b |] ==> (%n. X n - Y n) ----> a - b";
by (blast_tac (claset() addIs [LIMSEQ_add_minus]) 1);
qed "LIMSEQ_diff";

Goalw [real_diff_def] 
     "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n - Y n) ----NS> a - b";
by (blast_tac (claset() addIs [NSLIMSEQ_add_minus]) 1);
qed "NSLIMSEQ_diff";

(*---------------------------------------------------------------
    Proof is like that of NSLIM_inverse.
 --------------------------------------------------------------*)
Goalw [NSLIMSEQ_def] 
     "[| X ----NS> a;  a ~= #0 |] ==> (%n. inverse(X n)) ----NS> inverse(a)";
by (Clarify_tac 1);
by (dtac bspec 1);
by (auto_tac (claset(),
              simpset() addsimps [hypreal_of_real_not_zero_iff RS sym,
                                  hypreal_of_real_inverse RS sym]));
by (forward_tac [inf_close_hypreal_of_real_not_zero] 1 THEN assume_tac 1);
by (dtac hypreal_of_real_HFinite_diff_Infinitesimal 1);
by (stac (starfunNat_inverse RS sym) 1);
by (auto_tac (claset() addSEs [inf_close_inverse],
              simpset() addsimps [hypreal_of_real_zero_iff]));
qed "NSLIMSEQ_inverse";


(*------ Standard version of theorem -------*)
Goal "[| X ----> a; a ~= #0 |] ==> (%n. inverse(X n)) ----> inverse(a)";
by (asm_full_simp_tac (simpset() addsimps [NSLIMSEQ_inverse,
    LIMSEQ_NSLIMSEQ_iff]) 1);
qed "LIMSEQ_inverse";

Goal "[| X ----NS> a;  Y ----NS> b;  b ~= #0 |] \
\     ==> (%n. X n / Y n) ----NS> a/b";
by (asm_full_simp_tac (simpset() addsimps [NSLIMSEQ_mult, NSLIMSEQ_inverse, 
                                           real_divide_def]) 1);
qed "NSLIMSEQ_mult_inverse";

Goal "[| X ----> a;  Y ----> b;  b ~= #0 |] ==> (%n. X n / Y n) ----> a/b";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_mult, LIMSEQ_inverse, 
                                           real_divide_def]) 1);
qed "LIMSEQ_divide";

(*-----------------------------------------------
            Uniqueness of limit
 ----------------------------------------------*)
Goalw [NSLIMSEQ_def] 
     "[| X ----NS> a; X ----NS> b |] ==> a = b";
by (REPEAT(dtac (HNatInfinite_whn RSN (2,bspec)) 1));
by (auto_tac (claset() addDs [inf_close_trans3], simpset()));
qed "NSLIMSEQ_unique";

Goal "[| X ----> a; X ----> b |] ==> a = b";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff,
    NSLIMSEQ_unique]) 1);
qed "LIMSEQ_unique";

(*-----------------------------------------------------------------
    theorems about nslim and lim
 ----------------------------------------------------------------*)
Goalw [lim_def] "X ----> L ==> lim X = L";
by (blast_tac (claset() addIs [LIMSEQ_unique]) 1);
qed "limI";

Goalw [nslim_def] "X ----NS> L ==> nslim X = L";
by (blast_tac (claset() addIs [NSLIMSEQ_unique]) 1);
qed "nslimI";

Goalw [lim_def,nslim_def] "lim X = nslim X";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff]) 1);
qed "lim_nslim_iff";

(*------------------------------------------------------------------
                      Convergence
 -----------------------------------------------------------------*)
Goalw [convergent_def]
     "convergent X ==> EX L. (X ----> L)";
by (assume_tac 1);
qed "convergentD";

Goalw [convergent_def]
     "(X ----> L) ==> convergent X";
by (Blast_tac 1);
qed "convergentI";

Goalw [NSconvergent_def]
     "NSconvergent X ==> EX L. (X ----NS> L)";
by (assume_tac 1);
qed "NSconvergentD";

Goalw [NSconvergent_def]
     "(X ----NS> L) ==> NSconvergent X";
by (Blast_tac 1);
qed "NSconvergentI";

Goalw [convergent_def,NSconvergent_def] 
     "convergent X = NSconvergent X";
by (simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff]) 1);
qed "convergent_NSconvergent_iff";

Goalw [NSconvergent_def,nslim_def] 
     "NSconvergent X = (X ----NS> nslim X)";
by (auto_tac (claset() addIs [someI], simpset()));
qed "NSconvergent_NSLIMSEQ_iff";

Goalw [convergent_def,lim_def] 
     "convergent X = (X ----> lim X)";
by (auto_tac (claset() addIs [someI], simpset()));
qed "convergent_LIMSEQ_iff";

(*-------------------------------------------------------------------
         Subsequence (alternative definition) (e.g. Hoskins)
 ------------------------------------------------------------------*)
Goalw [subseq_def] "subseq f = (ALL n. (f n) < (f (Suc n)))";
by (auto_tac (claset() addSDs [less_imp_Suc_add], simpset()));
by (nat_ind_tac "k" 1);
by (auto_tac (claset() addIs [less_trans], simpset()));
qed "subseq_Suc_iff";

(*-------------------------------------------------------------------
                   Monotonicity
 ------------------------------------------------------------------*)

Goalw [monoseq_def]
   "monoseq X = ((ALL n. X n <= X (Suc n)) \
\                | (ALL n. X (Suc n) <= X n))";
by (auto_tac (claset () addSDs [le_imp_less_or_eq],
    simpset() addsimps [real_le_refl]));
by (auto_tac (claset() addSIs [lessI RS less_imp_le]
                       addSDs [less_imp_Suc_add], 
    simpset()));
by (induct_tac "ka" 1);
by (auto_tac (claset() addIs [real_le_trans], simpset()));
by (EVERY1[rtac ccontr, rtac swap, Simp_tac]);
by (induct_tac "k" 1);
by (auto_tac (claset() addIs [real_le_trans], simpset()));
qed "monoseq_Suc";

Goalw [monoseq_def] 
       "ALL m n. m <= n --> X m <= X n ==> monoseq X";
by (Blast_tac 1);
qed "monoI1";

Goalw [monoseq_def] 
       "ALL m n. m <= n --> X n <= X m ==> monoseq X";
by (Blast_tac 1);
qed "monoI2";

Goal "ALL n. X n <= X (Suc n) ==> monoseq X";
by (asm_simp_tac (simpset() addsimps [monoseq_Suc]) 1);
qed "mono_SucI1";

Goal "ALL n. X (Suc n) <= X n ==> monoseq X";
by (asm_simp_tac (simpset() addsimps [monoseq_Suc]) 1);
qed "mono_SucI2";

(*-------------------------------------------------------------------
                  Bounded Sequence
 ------------------------------------------------------------------*)
Goalw [Bseq_def] 
      "Bseq X ==> EX K. #0 < K & (ALL n. abs(X n) <= K)";
by (assume_tac 1);
qed "BseqD";

Goalw [Bseq_def]
      "[| #0 < K; ALL n. abs(X n) <= K |] \
\           ==> Bseq X";
by (Blast_tac 1);
qed "BseqI";

Goal "(EX K. #0 < K & (ALL n. abs(X n) <= K)) = \
\         (EX N. ALL n. abs(X n) <= real_of_posnat N)";
by (auto_tac (claset(),simpset() addsimps 
    (map rename_numerals) [real_gt_zero_preal_Ex,real_of_posnat_gt_zero]));
by (cut_inst_tac [("x","real_of_preal y")] reals_Archimedean2 1);
by (blast_tac (claset() addIs [real_le_less_trans,
    real_less_imp_le]) 1);
by (auto_tac (claset(),simpset() addsimps [real_of_posnat_def]));
qed "lemma_NBseq_def";

(* alternative definition for Bseq *)
Goalw [Bseq_def] 
      "Bseq X = (EX N. ALL n. abs(X n) <= real_of_posnat N)";
by (simp_tac (simpset() addsimps [lemma_NBseq_def]) 1);
qed "Bseq_iff";

Goal "(EX K. #0 < K & (ALL n. abs(X n) <= K)) = \
\         (EX N. ALL n. abs(X n) < real_of_posnat N)";
by (auto_tac (claset(),simpset() addsimps 
    (map rename_numerals) [real_gt_zero_preal_Ex,real_of_posnat_gt_zero]));
by (cut_inst_tac [("x","real_of_preal y")] reals_Archimedean2 1);
by (blast_tac (claset() addIs [real_less_trans,
    real_le_less_trans]) 1);
by (auto_tac (claset() addIs [real_less_imp_le],
    simpset() addsimps [real_of_posnat_def]));
qed "lemma_NBseq_def2";

(* yet another definition for Bseq *)
Goalw [Bseq_def] 
      "Bseq X = (EX N. ALL n. abs(X n) < real_of_posnat N)";
by (simp_tac (simpset() addsimps [lemma_NBseq_def2]) 1);
qed "Bseq_iff1a";

Goalw [NSBseq_def]
      "[| NSBseq X; N: HNatInfinite |] \
\           ==> (*fNat* X) N : HFinite";
by (Blast_tac 1);
qed "NSBseqD";

Goalw [NSBseq_def]
      "ALL N: HNatInfinite. (*fNat* X) N : HFinite \
\           ==> NSBseq X";
by (assume_tac 1);
qed "NSBseqI";

(*-----------------------------------------------------------
       Standard definition ==> NS definition
 ----------------------------------------------------------*)
(* a few lemmas *)
Goal "ALL n. abs(X n) <= K ==> \
\     ALL n. abs(X((f::nat=>nat) n)) <= K";
by (Auto_tac);
val lemma_Bseq = result();

Goalw [Bseq_def,NSBseq_def] "Bseq X ==> NSBseq X";
by (Step_tac 1);
by (res_inst_tac [("z","N")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [starfunNat,    
    HFinite_FreeUltrafilterNat_iff,
    HNatInfinite_FreeUltrafilterNat_iff]));
by (EVERY[rtac bexI 1, rtac lemma_hyprel_refl 2]);
by (dres_inst_tac [("f","Xa")] lemma_Bseq 1); 
by (res_inst_tac [("x","K+#1")] exI 1);
by (rotate_tac 2 1 THEN dtac FreeUltrafilterNat_all 1);
by (Ultra_tac 1);
qed "Bseq_NSBseq";

(*---------------------------------------------------------------
       NS  definition ==> Standard definition
 ---------------------------------------------------------------*)
(* similar to NSLIM proof in REALTOPOS *)
(*------------------------------------------------------------------- 
   We need to get rid of the real variable and do so by proving the
   following which relies on the Archimedean property of the reals
   When we skolemize we then get the required function f::nat=>nat 
   o/w we would be stuck with a skolem function f :: real=>nat which
   is not what we want (read useless!)
 -------------------------------------------------------------------*)
 
Goal "ALL K. #0 < K --> (EX n. K < abs (X n)) \
\          ==> ALL N. EX n. real_of_posnat  N < abs (X n)";
by (Step_tac 1);
by (cut_inst_tac [("n","N")] (rename_numerals real_of_posnat_gt_zero) 1);
by (Blast_tac 1);
val lemmaNSBseq = result();

Goal "ALL K. #0 < K --> (EX n. K < abs (X n)) \
\         ==> EX f. ALL N. real_of_posnat  N < abs (X (f N))";
by (dtac lemmaNSBseq 1);
by (dtac choice 1);
by (Blast_tac 1);
val lemmaNSBseq2 = result();

Goal "ALL N. real_of_posnat  N < abs (X (f N)) \
\         ==>  Abs_hypreal(hyprel^^{X o f}) : HInfinite";
by (auto_tac (claset(),simpset() addsimps 
    [HInfinite_FreeUltrafilterNat_iff,o_def]));
by (EVERY[rtac bexI 1, rtac lemma_hyprel_refl 2, 
    Step_tac 1]);
by (cut_inst_tac [("u","u")] FreeUltrafilterNat_nat_gt_real 1);
by (blast_tac (claset() addDs [FreeUltrafilterNat_all,
    FreeUltrafilterNat_Int] addIs [real_less_trans,
    FreeUltrafilterNat_subset]) 1);
qed "real_seq_to_hypreal_HInfinite";

(*--------------------------------------------------------------------------------
     Now prove that we can get out an infinite hypernatural as well 
     defined using the skolem function f::nat=>nat above
 --------------------------------------------------------------------------------*)

Goal "{n. f n <= Suc u & real_of_posnat  n < abs (X (f n))} <= \
\         {n. f n <= u & real_of_posnat  n < abs (X (f n))} \
\         Un {n. real_of_posnat n < abs (X (Suc u))}";
by (auto_tac (claset() addSDs [le_imp_less_or_eq] addIs [less_imp_le],
    simpset() addsimps [less_Suc_eq]));
val lemma_finite_NSBseq = result();

Goal "finite {n. f n <= (u::nat) &  real_of_posnat n < abs(X(f n))}";
by (induct_tac "u" 1);
by (rtac (CLAIM "{n. f n <= (0::nat) & real_of_posnat n < abs (X (f n))} <= \
\         {n. real_of_posnat n < abs (X 0)}"
          RS finite_subset) 1);
by (rtac finite_real_of_posnat_less_real 1);
by (rtac (lemma_finite_NSBseq RS finite_subset) 1);
by (auto_tac (claset() addIs [finite_real_of_posnat_less_real], simpset()));
val lemma_finite_NSBseq2 = result();

Goal "ALL N. real_of_posnat  N < abs (X (f N)) \
\     ==> Abs_hypnat(hypnatrel^^{f}) : HNatInfinite";
by (auto_tac (claset(),simpset() addsimps 
    [HNatInfinite_FreeUltrafilterNat_iff]));
by (EVERY[rtac bexI 1, rtac lemma_hypnatrel_refl 2, 
    Step_tac 1]);
by (rtac ccontr 1 THEN dtac FreeUltrafilterNat_Compl_mem 1);
by (asm_full_simp_tac (simpset() addsimps 
   [CLAIM_SIMP "- {n. u < (f::nat=>nat) n} \
\   = {n. f n <= u}" [le_def]]) 1);
by (dtac FreeUltrafilterNat_all 1);
by (dtac FreeUltrafilterNat_Int 1 THEN assume_tac 1);
by (auto_tac (claset(),simpset() addsimps 
    [CLAIM "({n. f n <= u} Int {n. real_of_posnat n < abs(X(f n))}) = \
\          {n. f n <= (u::nat) &  real_of_posnat n < abs(X(f n))}",
     lemma_finite_NSBseq2 RS FreeUltrafilterNat_finite]));
qed "HNatInfinite_skolem_f";

Goalw [Bseq_def,NSBseq_def] 
      "NSBseq X ==> Bseq X";
by (rtac ccontr 1);
by (auto_tac (claset(),simpset() addsimps [real_le_def]));
by (dtac lemmaNSBseq2 1 THEN Step_tac 1);
by (forw_inst_tac [("X","X"),("f","f")] real_seq_to_hypreal_HInfinite 1);
by (dtac (HNatInfinite_skolem_f RSN (2,bspec)) 1 THEN assume_tac 1);
by (auto_tac (claset(),simpset() addsimps [starfunNat,
    o_def,HFinite_HInfinite_iff]));
qed "NSBseq_Bseq";

(*----------------------------------------------------------------------
  Equivalence of nonstandard and standard definitions 
  for a bounded sequence
 -----------------------------------------------------------------------*)
Goal "(Bseq X) = (NSBseq X)";
by (blast_tac (claset() addSIs [NSBseq_Bseq,Bseq_NSBseq]) 1);
qed "Bseq_NSBseq_iff";

(*----------------------------------------------------------------------
   A convergent sequence is bounded
   (Boundedness as a necessary condition for convergence)
 -----------------------------------------------------------------------*)
(* easier --- nonstandard version - no existential as usual *)
Goalw [NSconvergent_def,NSBseq_def,NSLIMSEQ_def] 
          "NSconvergent X ==> NSBseq X";
by (blast_tac (claset() addDs [HFinite_hypreal_of_real RS 
               (inf_close_sym RSN (2,inf_close_HFinite))]) 1);
qed "NSconvergent_NSBseq";

(* standard version - easily now proved using *)
(* equivalence of NS and standard definitions *)
Goal "convergent X ==> Bseq X";
by (asm_full_simp_tac (simpset() addsimps [NSconvergent_NSBseq,
    convergent_NSconvergent_iff,Bseq_NSBseq_iff]) 1);
qed "convergent_Bseq";

(*----------------------------------------------------------------------
             Results about Ubs and Lubs of bounded sequences
 -----------------------------------------------------------------------*)
Goalw [Bseq_def]
  "!!(X::nat=>real). Bseq X ==> \
\  EX U. isUb (UNIV::real set) {x. EX n. X n = x} U";
by (auto_tac (claset() addIs [isUbI,setleI],
    simpset() addsimps [abs_le_interval_iff]));
qed "Bseq_isUb";

(*----------------------------------------------------------------------
   Use completeness of reals (supremum property) 
   to show that any bounded sequence has a lub 
-----------------------------------------------------------------------*)
Goal
  "!!(X::nat=>real). Bseq X ==> \
\  EX U. isLub (UNIV::real set) {x. EX n. X n = x} U";
by (blast_tac (claset() addIs [reals_complete,
    Bseq_isUb]) 1);
qed "Bseq_isLub";

(* nonstandard version of premise will be *)
(* handy when we work in NS universe      *)
Goal   "NSBseq X ==> \
\  EX U. isUb (UNIV::real set) {x. EX n. X n = x} U";
by (asm_full_simp_tac (simpset() addsimps 
    [Bseq_NSBseq_iff RS sym,Bseq_isUb]) 1);
qed "NSBseq_isUb";

Goal
  "NSBseq X ==> \
\  EX U. isLub (UNIV::real set) {x. EX n. X n = x} U";
by (asm_full_simp_tac (simpset() addsimps 
    [Bseq_NSBseq_iff RS sym,Bseq_isLub]) 1);
qed "NSBseq_isLub";

(*--------------------------------------------------------------------
             Bounded and monotonic sequence converges              
 --------------------------------------------------------------------*)
(* lemmas *)
Goal 
     "!!(X::nat=>real). [| ALL m n. m <= n -->  X m <= X n; \
\                 isLub (UNIV::real set) {x. EX n. X n = x} (X ma) \
\              |] ==> ALL n. ma <= n --> X n = X ma";
by (Step_tac 1);
by (dres_inst_tac [("y","X n")] isLubD2 1);
by (ALLGOALS(blast_tac (claset() addDs [real_le_anti_sym])));
val lemma_converg1 = result();

(*------------------------------------------------------------------- 
   The best of both world: Easier to prove this result as a standard
   theorem and then use equivalence to "transfer" it into the
   equivalent nonstandard form if needed!
 -------------------------------------------------------------------*)
Goalw [LIMSEQ_def] 
         "ALL n. m <= n --> X n = X m \
\         ==> EX L. (X ----> L)";  
by (res_inst_tac [("x","X m")] exI 1);
by (Step_tac 1);
by (res_inst_tac [("x","m")] exI 1);
by (Step_tac 1);
by (dtac spec 1 THEN etac impE 1);
by (Auto_tac);
qed "Bmonoseq_LIMSEQ";

(* Now same theorem in terms of NS limit *)
Goal "ALL n. m <= n --> X n = X m \
\         ==> EX L. (X ----NS> L)";  
by (auto_tac (claset() addSDs [Bmonoseq_LIMSEQ],
    simpset() addsimps [LIMSEQ_NSLIMSEQ_iff]));
qed "Bmonoseq_NSLIMSEQ";

(* a few more lemmas *)
Goal "!!(X::nat=>real). \
\              [| ALL m. X m ~= U; \
\                 isLub UNIV {x. EX n. X n = x} U \
\              |] ==> ALL m. X m < U";
by (Step_tac 1);
by (dres_inst_tac [("y","X m")] isLubD2 1);
by (auto_tac (claset() addSDs [real_le_imp_less_or_eq],
              simpset()));
val lemma_converg2 = result();

Goal "!!(X ::nat=>real). ALL m. X m <= U ==> \
\         isUb UNIV {x. EX n. X n = x} U";
by (rtac (setleI RS isUbI) 1);
by (Auto_tac);
val lemma_converg3 = result();

(* FIXME: U - T < U redundant *)
Goal "!!(X::nat=> real). \
\              [| ALL m. X m ~= U; \
\                 isLub UNIV {x. EX n. X n = x} U; \
\                 #0 < T; \
\                 U + - T < U \
\              |] ==> EX m. U + -T < X m & X m < U";
by (dtac lemma_converg2 1 THEN assume_tac 1);
by (rtac ccontr 1 THEN Asm_full_simp_tac 1);
by (fold_tac [real_le_def]);
by (dtac lemma_converg3 1);
by (dtac isLub_le_isUb 1 THEN assume_tac 1);
by (auto_tac (claset() addDs [real_less_le_trans],
    simpset() addsimps [real_minus_zero_le_iff]));
val lemma_converg4 = result();

(*-------------------------------------------------------------------
  A standard proof of the theorem for monotone increasing sequence
 ------------------------------------------------------------------*)

Goalw [convergent_def] 
     "[| Bseq X; ALL m n. m <= n --> X m <= X n |] \
\                ==> convergent X";
by (forward_tac [Bseq_isLub] 1);
by (Step_tac 1);
by (case_tac "EX m. X m = U" 1 THEN Auto_tac);
by (blast_tac (claset() addDs [lemma_converg1,
    Bmonoseq_LIMSEQ]) 1);
(* second case *)
by (res_inst_tac [("x","U")] exI 1);
by (rtac LIMSEQI 1 THEN Step_tac 1);
by (forward_tac [lemma_converg2] 1 THEN assume_tac 1);
by (dtac lemma_converg4 1 THEN Auto_tac);
by (res_inst_tac [("x","m")] exI 1 THEN Step_tac 1);
by (subgoal_tac "X m <= X n" 1 THEN Fast_tac 2);
by (rotate_tac 3 1 THEN dres_inst_tac [("x","n")] spec 1);
by (arith_tac 1);
qed "Bseq_mono_convergent";

(* NS version of theorem *)
Goalw [convergent_def] 
     "[| NSBseq X; ALL m n. m <= n --> X m <= X n |] \
\                ==> NSconvergent X";
by (auto_tac (claset() addIs [Bseq_mono_convergent], 
    simpset() addsimps [convergent_NSconvergent_iff RS sym,
    Bseq_NSBseq_iff RS sym]));
qed "NSBseq_mono_NSconvergent";

Goalw [convergent_def] 
      "(convergent X) = (convergent (%n. -(X n)))";
by (auto_tac (claset() addDs [LIMSEQ_minus], simpset()));
by (dtac LIMSEQ_minus 1 THEN Auto_tac);
qed "convergent_minus_iff";

Goalw [Bseq_def] "Bseq (%n. -(X n)) = Bseq X";
by (Asm_full_simp_tac 1);
qed "Bseq_minus_iff";

(*--------------------------------
   **** main mono theorem ****
 -------------------------------*)
Goalw [monoseq_def] "[| Bseq X; monoseq X |] ==> convergent X";
by (Step_tac 1);
by (rtac (convergent_minus_iff RS ssubst) 2);
by (dtac (Bseq_minus_iff RS ssubst) 2);
by (auto_tac (claset() addSIs [Bseq_mono_convergent], simpset()));
qed "Bseq_monoseq_convergent";

(*----------------------------------------------------------------
          A few more equivalence theorems for boundedness 
 ---------------------------------------------------------------*)
 
(***--- alternative formulation for boundedness---***)
Goalw [Bseq_def] 
   "Bseq X = (EX k x. #0 < k & (ALL n. abs(X(n) + -x) <= k))";
by (Step_tac 1);
by (res_inst_tac [("x","k + abs(x)")] exI 2);
by (res_inst_tac [("x","K")] exI 1);
by (res_inst_tac [("x","0")] exI 1);
by (Auto_tac);
by (ALLGOALS (dres_inst_tac [("x","n")] spec));
by (ALLGOALS arith_tac);
qed "Bseq_iff2";

(***--- alternative formulation for boundedness ---***)
Goal "Bseq X = (EX k N. #0 < k & (ALL n. abs(X(n) + -X(N)) <= k))";
by (Step_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Bseq_def]) 1);
by (Step_tac 1);
by (res_inst_tac [("x","K + abs(X N)")] exI 1);
by (Auto_tac);
by (arith_tac 1);
by (res_inst_tac [("x","N")] exI 1);
by (Step_tac 1);
by (dres_inst_tac [("x","n")] spec 1);
by (arith_tac 1);
by (auto_tac (claset(), simpset() addsimps [Bseq_iff2]));
qed "Bseq_iff3";

Goalw [Bseq_def] "(ALL n. k <= f n & f n <= K) ==> Bseq f";
by (res_inst_tac [("x","(abs(k) + abs(K)) + #1")] exI 1);
by (Auto_tac);
by (dres_inst_tac [("x","n")] spec 2);
by (ALLGOALS arith_tac);
qed "BseqI2";

(*-------------------------------------------------------------------
   Equivalence between NS and standard definitions of Cauchy seqs
 ------------------------------------------------------------------*)
(*-------------------------------
      Standard def => NS def
 -------------------------------*)
Goal "Abs_hypnat (hypnatrel ^^ {x}) : HNatInfinite \
\         ==> {n. M <= x n} : FreeUltrafilterNat";
by (auto_tac (claset(),
              simpset() addsimps [HNatInfinite_FreeUltrafilterNat_iff]));
by (dres_inst_tac [("x","M")] spec 1);
by (ultra_tac (claset(),simpset() addsimps [less_imp_le]) 1);
val lemmaCauchy1 = result();

Goal "{n. ALL m n. M <= m & M <= (n::nat) --> abs (X m + - X n) < u} Int \
\     {n. M <= xa n} Int {n. M <= x n} <= \
\     {n. abs (X (xa n) + - X (x n)) < u}";
by (Blast_tac 1);
val lemmaCauchy2 = result();

Goalw [Cauchy_def,NSCauchy_def] 
      "Cauchy X ==> NSCauchy X";
by (Step_tac 1);
by (res_inst_tac [("z","M")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","N")] eq_Abs_hypnat 1);
by (rtac (inf_close_minus_iff RS iffD2) 1);
by (rtac (mem_infmal_iff RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [starfunNat,
    hypreal_minus,hypreal_add,Infinitesimal_FreeUltrafilterNat_iff]));
by (EVERY[rtac bexI 1, Auto_tac]);
by (dtac spec 1 THEN Auto_tac);
by (dres_inst_tac [("M","M")] lemmaCauchy1 1);
by (dres_inst_tac [("M","M")] lemmaCauchy1 1);
by (res_inst_tac [("x1","xa")] 
    (lemmaCauchy2 RSN (2,FreeUltrafilterNat_subset)) 1);
by (rtac FreeUltrafilterNat_Int 1 THEN assume_tac 2);
by (auto_tac (claset() addIs [FreeUltrafilterNat_Int,
        FreeUltrafilterNat_Nat_set], simpset()));
qed "Cauchy_NSCauchy";

(*-----------------------------------------------
     NS def => Standard def -- rather long but 
     straightforward proof in this case
 ---------------------------------------------*)
Goalw [Cauchy_def,NSCauchy_def] 
      "NSCauchy X ==> Cauchy X";
by (EVERY1[Step_tac, rtac ccontr,Asm_full_simp_tac]);
by (dtac choice 1 THEN auto_tac (claset(),simpset() 
         addsimps [all_conj_distrib]));
by (dtac choice 1 THEN step_tac (claset() addSDs 
         [all_conj_distrib RS iffD1]) 1);
by (REPEAT(dtac HNatInfinite_NSLIMSEQ 1));
by (dtac bspec 1 THEN assume_tac 1);
by (dres_inst_tac [("x","Abs_hypnat (hypnatrel ^^ {fa})")] bspec 1 
    THEN auto_tac (claset(),simpset() addsimps [starfunNat]));
by (dtac (inf_close_minus_iff RS iffD1) 1);
by (dtac (mem_infmal_iff RS iffD2) 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_minus,
    hypreal_add,Infinitesimal_FreeUltrafilterNat_iff]));
by (dres_inst_tac [("x","e")] spec 1 THEN Auto_tac);
by (dtac FreeUltrafilterNat_Int 1 THEN assume_tac 1);
by (dtac (CLAIM "{n. X (f n) + - X (fa n) = Y n} Int \
\         {n. abs (Y n) < e} <= \
\         {n. abs (X (f n) + - X (fa n)) < e}" RSN 
          (2,FreeUltrafilterNat_subset)) 1);
by (thin_tac "{n. abs (Y n) < e} : FreeUltrafilterNat" 1);
by (dtac FreeUltrafilterNat_all 1);
by (dtac FreeUltrafilterNat_Int 1 THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps 
    [CLAIM "{n. abs (X (f n) + - X (fa n)) < e} Int \
\         {M. ~ abs (X (f M) + - X (fa M)) < e} = {}",
     FreeUltrafilterNat_empty]) 1);
qed "NSCauchy_Cauchy";

(*----- Equivalence -----*)
Goal "NSCauchy X = Cauchy X";
by (blast_tac (claset() addSIs[NSCauchy_Cauchy,
    Cauchy_NSCauchy]) 1);
qed "NSCauchy_Cauchy_iff";

(*-------------------------------------------------------
  Cauchy sequence is bounded -- this is the standard 
  proof mechanization rather than the nonstandard proof 
 -------------------------------------------------------*)

(***-------------  VARIOUS LEMMAS --------------***)
Goal "ALL n. M <= n --> abs (X M + - X n) < (#1::real) \
\         ==>  ALL n. M <= n --> abs(X n) < #1 + abs(X M)";
by (Step_tac 1);
by (dtac spec 1 THEN Auto_tac);
by (arith_tac 1);
val lemmaCauchy = result();

Goal "(n < Suc M) = (n <= M)";
by Auto_tac;
qed "less_Suc_cancel_iff";

(* FIXME: Long. Maximal element in subsequence *)
Goal "EX m. m <= M & (ALL n. n <= M --> \
\         abs ((X::nat=> real) n) <= abs (X m))";
by (induct_tac "M" 1);
by (res_inst_tac [("x","0")] exI 1);
by (Asm_full_simp_tac 1);
by (Step_tac 1);
by (cut_inst_tac [("R1.0","abs (X (Suc n))"),("R2.0","abs(X m)")]
        real_linear 1);
by (Step_tac 1);
by (res_inst_tac [("x","m")] exI 1);
by (res_inst_tac [("x","m")] exI 2);
by (res_inst_tac [("x","Suc n")] exI 3);
by (ALLGOALS(Asm_full_simp_tac));
by (Step_tac 1);
by (ALLGOALS(eres_inst_tac [("m1","na")] 
    (le_imp_less_or_eq RS disjE)));
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps 
    [real_le_refl,less_Suc_cancel_iff,
     real_less_imp_le])));
by (blast_tac (claset() addIs [real_le_less_trans RS
    real_less_imp_le]) 1);
qed "SUP_rabs_subseq";

(* lemmas to help proof - mostly trivial *)
Goal "[| ALL m::nat. m <= M --> P M m; \
\        ALL m. M <= m --> P M m |] \
\     ==> ALL m. P M m";
by (Step_tac 1);
by (REPEAT(dres_inst_tac [("x","m")] spec 1));
by (auto_tac (claset() addEs [less_asym],
    simpset() addsimps [le_def]));
val lemma_Nat_covered = result();

Goal "[| ALL n. n <= M --> abs ((X::nat=>real) n) <= a; \
\        a < b |] \
\     ==> ALL n. n <= M --> abs(X n) <= b";
by (blast_tac (claset() addIs [real_le_less_trans RS 
               real_less_imp_le]) 1);
val lemma_trans1 = result();

Goal "[| ALL n. M <= n --> abs ((X::nat=>real) n) < a; \
\        a < b |] \
\     ==> ALL n. M <= n --> abs(X n)<= b";
by (blast_tac (claset() addIs [real_less_trans RS 
               real_less_imp_le]) 1);
val lemma_trans2 = result();

Goal "[| ALL n. n <= M --> abs (X n) <= a; \
\        a = b |] \
\     ==> ALL n. n <= M --> abs(X n) <= b";
by (Auto_tac);
val lemma_trans3 = result();

Goal "ALL n. M <= n --> abs ((X::nat=>real) n) < a \
\             ==>  ALL n. M <= n --> abs (X n) <= a";
by (blast_tac (claset() addIs [real_less_imp_le]) 1);
val lemma_trans4 = result();

(*---------------------------------------------------------- 
   Trickier than expected --- proof is more involved than
   outlines sketched by various authors would suggest
 ---------------------------------------------------------*)
Goalw [Cauchy_def,Bseq_def] "Cauchy X ==> Bseq X";
by (dres_inst_tac [("x","#1")] spec 1);
by (etac (rename_numerals real_zero_less_one RSN (2,impE)) 1);
by (Step_tac 1);
by (dres_inst_tac [("x","M")] spec 1);
by (Asm_full_simp_tac 1);
by (dtac lemmaCauchy 1);
by (cut_inst_tac [("M","M"),("X","X")] SUP_rabs_subseq 1);
by (Step_tac 1);
by (cut_inst_tac [("R1.0","abs(X m)"),
     ("R2.0","#1 + abs(X M)")] real_linear 1);
by (Step_tac 1);
by (dtac lemma_trans1 1 THEN assume_tac 1);
by (dtac lemma_trans2 3 THEN assume_tac 3);
by (dtac lemma_trans3 2 THEN assume_tac 2);
by (dtac (abs_add_one_gt_zero RS real_less_trans) 3);
by (dtac lemma_trans4 1);
by (dtac lemma_trans4 2);
by (res_inst_tac [("x","#1 + abs(X M)")] exI 1);
by (res_inst_tac [("x","#1 + abs(X M)")] exI 2);
by (res_inst_tac [("x","abs(X m)")] exI 3);
by (auto_tac (claset() addSEs [lemma_Nat_covered],
              simpset()));
by (ALLGOALS arith_tac);
qed "Cauchy_Bseq";

(*------------------------------------------------
  Cauchy sequence is bounded -- NSformulation
 ------------------------------------------------*)
Goal "NSCauchy X ==> NSBseq X";
by (asm_full_simp_tac (simpset() addsimps [Cauchy_Bseq,
    Bseq_NSBseq_iff RS sym,NSCauchy_Cauchy_iff]) 1);
qed "NSCauchy_NSBseq";


(*-----------------------------------------------------------------
          Equivalence of Cauchy criterion and convergence
  
  We will prove this using our NS formulation which provides a
  much easier proof than using the standard definition. We do not 
  need to use properties of subsequences such as boundedness, 
  monotonicity etc... Compare with Harrison's corresponding proof
  in HOL which is much longer and more complicated. Of course, we do
  not have problems which he encountered with guessing the right 
  instantiations for his 'espsilon-delta' proof(s) in this case
  since the NS formulations do not involve existential quantifiers.
 -----------------------------------------------------------------*)
Goalw [NSconvergent_def,NSLIMSEQ_def]
      "NSCauchy X = NSconvergent X";
by (Step_tac 1);
by (forward_tac [NSCauchy_NSBseq] 1);
by (auto_tac (claset() addIs [inf_close_trans2], 
    simpset() addsimps 
    [NSBseq_def,NSCauchy_def]));
by (dtac (HNatInfinite_whn RSN (2,bspec)) 1);
by (dtac (HNatInfinite_whn RSN (2,bspec)) 1);
by (auto_tac (claset() addSDs [st_part_Ex], simpset() 
              addsimps [SReal_iff]));
by (blast_tac (claset() addIs [inf_close_trans3]) 1);
qed "NSCauchy_NSconvergent_iff";

(* Standard proof for free *)
Goal "Cauchy X = convergent X";
by (simp_tac (simpset() addsimps [NSCauchy_Cauchy_iff RS sym,
    convergent_NSconvergent_iff, NSCauchy_NSconvergent_iff]) 1);
qed "Cauchy_convergent_iff";

(*-----------------------------------------------------------------
     We can now try and derive a few properties of sequences
     starting with the limit comparison property for sequences
 -----------------------------------------------------------------*)
Goalw [NSLIMSEQ_def]
       "[| f ----NS> l; g ----NS> m; \
\                  EX N. ALL n. N <= n --> f(n) <= g(n) \
\               |] ==> l <= m";
by (Step_tac 1);
by (dtac starfun_le_mono 1);
by (REPEAT(dtac (HNatInfinite_whn RSN (2,bspec)) 1));
by (dres_inst_tac [("x","whn")] spec 1);
by (REPEAT(dtac (bex_Infinitesimal_iff2 RS iffD2) 1));
by (auto_tac (claset() addIs 
    [hypreal_of_real_le_add_Infininitesimal_cancel2], simpset()));
qed "NSLIMSEQ_le";

(* standard version *)
Goal "[| f ----> l; g ----> m; \
\        EX N. ALL n. N <= n --> f(n) <= g(n) |] \
\     ==> l <= m";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff,
    NSLIMSEQ_le]) 1);
qed "LIMSEQ_le";

(*---------------
    Also...
 --------------*)
Goal "[| X ----> r; ALL n. a <= X n |] ==> a <= r";
by (rtac LIMSEQ_le 1);
by (rtac LIMSEQ_const 1);
by (Auto_tac);
qed "LIMSEQ_le_const";

Goal "[| X ----NS> r; ALL n. a <= X n |] ==> a <= r";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff,
    LIMSEQ_le_const]) 1);
qed "NSLIMSEQ_le_const";

Goal "[| X ----> r; ALL n. X n <= a |] ==> r <= a";
by (rtac LIMSEQ_le 1);
by (rtac LIMSEQ_const 2);
by (Auto_tac);
qed "LIMSEQ_le_const2";

Goal "[| X ----NS> r; ALL n. X n <= a |] ==> r <= a";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff,
    LIMSEQ_le_const2]) 1);
qed "NSLIMSEQ_le_const2";

(*-----------------------------------------------------
            Shift a convergent series by 1
  We use the fact that Cauchyness and convergence
  are equivalent and also that the successor of an
  infinite hypernatural is also infinite.
 -----------------------------------------------------*)
Goal "f ----NS> l ==> (%n. f(Suc n)) ----NS> l";
by (forward_tac [NSconvergentI RS 
    (NSCauchy_NSconvergent_iff RS iffD2)] 1);
by (auto_tac (claset(),simpset() addsimps [NSCauchy_def,
    NSLIMSEQ_def,starfunNat_shift_one]));
by (dtac bspec 1 THEN assume_tac 1);
by (dtac bspec 1 THEN assume_tac 1);
by (dtac (SHNat_one RSN (2,HNatInfinite_SHNat_add)) 1);
by (blast_tac (claset() addIs [inf_close_trans3]) 1);
qed "NSLIMSEQ_Suc";

(* standard version *)
Goal "f ----> l ==> (%n. f(Suc n)) ----> l";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff,
    NSLIMSEQ_Suc]) 1);
qed "LIMSEQ_Suc";

Goal "(%n. f(Suc n)) ----NS> l ==> f ----NS> l";
by (forward_tac [NSconvergentI RS 
    (NSCauchy_NSconvergent_iff RS iffD2)] 1);
by (auto_tac (claset(),simpset() addsimps [NSCauchy_def,
    NSLIMSEQ_def,starfunNat_shift_one]));
by (dtac bspec 1 THEN assume_tac 1);
by (dtac bspec 1 THEN assume_tac 1);
by (ftac (SHNat_one RSN (2,HNatInfinite_SHNat_diff)) 1);
by (rotate_tac 2 1);
by (auto_tac (claset() addSDs [bspec] addIs [inf_close_trans3],
    simpset()));
qed "NSLIMSEQ_imp_Suc";

Goal "(%n. f(Suc n)) ----> l ==> f ----> l";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff]) 1);
by (etac NSLIMSEQ_imp_Suc 1);
qed "LIMSEQ_imp_Suc";

Goal "((%n. f(Suc n)) ----> l) = (f ----> l)";
by (blast_tac (claset() addIs [LIMSEQ_imp_Suc,LIMSEQ_Suc]) 1);
qed "LIMSEQ_Suc_iff";

Goal "((%n. f(Suc n)) ----NS> l) = (f ----NS> l)";
by (blast_tac (claset() addIs [NSLIMSEQ_imp_Suc,NSLIMSEQ_Suc]) 1);
qed "NSLIMSEQ_Suc_iff";

(*-----------------------------------------------------
       A sequence tends to zero iff its abs does
 ----------------------------------------------------*)
(* we can prove this directly since proof is trivial *)
Goalw [LIMSEQ_def] 
      "((%n. abs(f n)) ----> #0) = (f ----> #0)";
by (simp_tac (simpset() addsimps [abs_idempotent]) 1);
qed "LIMSEQ_rabs_zero";

(*-----------------------------------------------------*)
(* We prove the NS version from the standard one       *)
(* Actually pure NS proof seems more complicated       *)
(* than the direct standard one above!                 *)
(*-----------------------------------------------------*)

Goal "((%n. abs(f n)) ----NS> #0) = (f ----NS> #0)";
by (simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff RS sym,
             LIMSEQ_rabs_zero]) 1);
qed "NSLIMSEQ_rabs_zero";

(*----------------------------------------
    Also we have for a general limit 
        (NS proof much easier)
 ---------------------------------------*)
Goalw [NSLIMSEQ_def] 
       "f ----NS> l ==> (%n. abs(f n)) ----NS> abs(l)";
by (auto_tac (claset() addIs [inf_close_hrabs], simpset() 
    addsimps [starfunNat_rabs,hypreal_of_real_hrabs RS sym]));
qed "NSLIMSEQ_imp_rabs";

(* standard version *)
Goal "f ----> l ==> (%n. abs(f n)) ----> abs(l)";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff,
    NSLIMSEQ_imp_rabs]) 1);
qed "LIMSEQ_imp_rabs";

(*-----------------------------------------------------
       An unbounded sequence's inverse tends to 0
  ----------------------------------------------------*)
(* standard proof seems easier *)
Goalw [LIMSEQ_def] 
      "ALL y. EX N. ALL n. N <= n --> y < f(n) \
\      ==> (%n. inverse(f n)) ----> #0";
by (Step_tac 1 THEN Asm_full_simp_tac 1);
by (dres_inst_tac [("x","inverse r")] spec 1 THEN Step_tac 1);
by (res_inst_tac [("x","N")] exI 1 THEN Step_tac 1);
by (dtac spec 1 THEN Auto_tac);
by (forward_tac [rename_numerals real_inverse_gt_zero] 1);
by (forward_tac [real_less_trans] 1 THEN assume_tac 1);
by (forw_inst_tac [("x","f n")] (rename_numerals real_inverse_gt_zero) 1);
by (asm_simp_tac (simpset() addsimps [abs_eqI2]) 1);
by (res_inst_tac [("t","r")] (real_inverse_inverse RS subst) 1);
by (auto_tac (claset() addIs [real_inverse_less_iff RS iffD2], 
              simpset() delsimps [real_inverse_inverse]));
qed "LIMSEQ_inverse_zero";

Goal "ALL y. EX N. ALL n. N <= n --> y < f(n) \
\     ==> (%n. inverse(f n)) ----NS> #0";
by (asm_simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff RS sym,
                  LIMSEQ_inverse_zero]) 1);
qed "NSLIMSEQ_inverse_zero";

(*--------------------------------------------------------------
             Sequence  1/n --> 0 as n --> infinity 
 -------------------------------------------------------------*)
Goal "(%n. inverse(real_of_posnat n)) ----> #0";
by (rtac LIMSEQ_inverse_zero 1 THEN Step_tac 1);
by (cut_inst_tac [("x","y")] reals_Archimedean2 1);
by (Step_tac 1 THEN res_inst_tac [("x","n")] exI 1);
by (Step_tac 1 THEN etac (le_imp_less_or_eq RS disjE) 1);
by (dtac (real_of_posnat_less_iff RS iffD2) 1);
by (auto_tac (claset() addEs [real_less_trans], simpset()));
qed "LIMSEQ_inverse_real_of_posnat";

Goal "(%n. inverse(real_of_posnat n)) ----NS> #0";
by (simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff RS sym,
    LIMSEQ_inverse_real_of_posnat]) 1);
qed "NSLIMSEQ_inverse_real_of_posnat";

(*--------------------------------------------
    Sequence  r + 1/n --> r as n --> infinity 
    now easily proved
 --------------------------------------------*)
Goal "(%n. r + inverse(real_of_posnat n)) ----> r";
by (cut_facts_tac [[LIMSEQ_const,LIMSEQ_inverse_real_of_posnat]
    MRS LIMSEQ_add] 1);
by (Auto_tac);
qed "LIMSEQ_inverse_real_of_posnat_add";

Goal "(%n. r + inverse(real_of_posnat n)) ----NS> r";
by (simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff RS sym,
    LIMSEQ_inverse_real_of_posnat_add]) 1);
qed "NSLIMSEQ_inverse_real_of_posnat_add";

(*--------------
    Also...
 --------------*)

Goal "(%n. r + -inverse(real_of_posnat n)) ----> r";
by (cut_facts_tac [[LIMSEQ_const,LIMSEQ_inverse_real_of_posnat]
    MRS LIMSEQ_add_minus] 1);
by (Auto_tac);
qed "LIMSEQ_inverse_real_of_posnat_add_minus";

Goal "(%n. r + -inverse(real_of_posnat n)) ----NS> r";
by (simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff RS sym,
    LIMSEQ_inverse_real_of_posnat_add_minus]) 1);
qed "NSLIMSEQ_inverse_real_of_posnat_add_minus";

Goal "(%n. r*( #1 + -inverse(real_of_posnat n))) ----> r";
by (cut_inst_tac [("b","#1")] ([LIMSEQ_const,
    LIMSEQ_inverse_real_of_posnat_add_minus] MRS LIMSEQ_mult) 1);
by (Auto_tac);
qed "LIMSEQ_inverse_real_of_posnat_add_minus_mult";

Goal "(%n. r*( #1 + -inverse(real_of_posnat n))) ----NS> r";
by (simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff RS sym,
    LIMSEQ_inverse_real_of_posnat_add_minus_mult]) 1);
qed "NSLIMSEQ_inverse_real_of_posnat_add_minus_mult";

(*---------------------------------------------------------------
                          Real Powers
 --------------------------------------------------------------*)
Goal "(X ----NS> a) --> ((%n. (X n) ^ m) ----NS> a ^ m)";
by (induct_tac "m" 1);
by (auto_tac (claset() addIs [NSLIMSEQ_mult,NSLIMSEQ_const],
    simpset()));
qed_spec_mp "NSLIMSEQ_pow";

Goal "X ----> a ==> (%n. (X n) ^ m) ----> a ^ m";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_NSLIMSEQ_iff,
    NSLIMSEQ_pow]) 1);
qed "LIMSEQ_pow";

(*----------------------------------------------------------------
               0 <= x < #1 ==> (x ^ n ----> 0)
  Proof will use (NS) Cauchy equivalence for convergence and
  also fact that bounded and monotonic sequence converges.  
 ---------------------------------------------------------------*)
Goalw [Bseq_def] 
      "[| #0 <= x; x < #1 |] ==> Bseq (%n. x ^ n)";
by (res_inst_tac [("x","#1")] exI 1);
by (auto_tac (claset() addDs [conjI RS realpow_le2] 
    addIs [real_less_imp_le], simpset() addsimps 
    [real_zero_less_one,abs_eqI1,realpow_abs RS sym] ));
qed "Bseq_realpow";

Goal "[| #0 <= x; x < #1 |] ==> monoseq (%n. x ^ n)";
by (blast_tac (claset() addSIs [mono_SucI2,realpow_Suc_le3]) 1);
qed "monoseq_realpow";

Goal "[| #0 <= x; x < #1 |] ==> convergent (%n. x ^ n)";
by (blast_tac (claset() addSIs [Bseq_monoseq_convergent,
    Bseq_realpow,monoseq_realpow]) 1);
qed "convergent_realpow";

(* We now use NS criterion to bring proof of theorem through *)

Goalw [NSLIMSEQ_def]
     "[| #0 <= x; x < #1 |] ==> (%n. x ^ n) ----NS> #0";
by (auto_tac (claset() addSDs [convergent_realpow],
              simpset() addsimps [convergent_NSconvergent_iff]));
by (forward_tac [NSconvergentD] 1);
by (auto_tac (claset(),
        simpset() addsimps [NSLIMSEQ_def, NSCauchy_NSconvergent_iff RS sym,
                            NSCauchy_def, starfunNat_pow]));
by (forward_tac [HNatInfinite_add_one] 1);
by (dtac bspec 1 THEN assume_tac 1);
by (dtac bspec 1 THEN assume_tac 1);
by (dres_inst_tac [("x","N + 1hn")] bspec 1 THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [hyperpow_add]) 1);
by (dtac inf_close_mult_subst_SReal 1 THEN assume_tac 1);
by (dtac inf_close_trans3 1 THEN assume_tac 1);
by (auto_tac (claset(),
              simpset() addsimps [hypreal_of_real_mult RS sym]));
qed "NSLIMSEQ_realpow_zero";

(*---------------  standard version ---------------*)
Goal "[| #0 <= x; x < #1 |] ==> (%n. x ^ n) ----> #0";
by (asm_simp_tac (simpset() addsimps [NSLIMSEQ_realpow_zero,
                                      LIMSEQ_NSLIMSEQ_iff]) 1);
qed "LIMSEQ_realpow_zero";

Goal "#1 < x ==> (%n. a / (x ^ n)) ----> #0";
by (cut_inst_tac [("a","a"),("x1","inverse x")] 
    ([LIMSEQ_const, LIMSEQ_realpow_zero] MRS LIMSEQ_mult) 1);
by (auto_tac (claset(), 
              simpset() addsimps [real_divide_def, realpow_inverse])); 
by (asm_simp_tac (simpset() addsimps [real_inverse_eq_divide,
                                      pos_real_divide_less_eq]) 1); 
qed "LIMSEQ_divide_realpow_zero";

(*----------------------------------------------------------------
               Limit of c^n for |c| < 1  
 ---------------------------------------------------------------*)
Goal "abs(c) < #1 ==> (%n. abs(c) ^ n) ----> #0";
by (blast_tac (claset() addSIs [LIMSEQ_realpow_zero,abs_ge_zero]) 1);
qed "LIMSEQ_rabs_realpow_zero";

Goal "abs(c) < #1 ==> (%n. abs(c) ^ n) ----NS> #0";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_rabs_realpow_zero,
    LIMSEQ_NSLIMSEQ_iff RS sym]) 1);
qed "NSLIMSEQ_rabs_realpow_zero";

Goal "abs(c) < #1 ==> (%n. c ^ n) ----> #0";
by (rtac (LIMSEQ_rabs_zero RS iffD1) 1);
by (auto_tac (claset() addIs [LIMSEQ_rabs_realpow_zero],
              simpset() addsimps [realpow_abs RS sym]));
qed "LIMSEQ_rabs_realpow_zero2";

Goal "abs(c) < #1 ==> (%n. c ^ n) ----NS> #0";
by (asm_full_simp_tac (simpset() addsimps [LIMSEQ_rabs_realpow_zero2,
    LIMSEQ_NSLIMSEQ_iff RS sym]) 1);
qed "NSLIMSEQ_rabs_realpow_zero2";

(***---------------------------------------------------------------
                 Hyperreals and Sequences
 ---------------------------------------------------------------***)
(*** A bounded sequence is a finite hyperreal ***)
Goal "NSBseq X ==> Abs_hypreal(hyprel^^{X}) : HFinite";
by (auto_tac (claset() addSIs [bexI,lemma_hyprel_refl] addIs 
       [FreeUltrafilterNat_all RS FreeUltrafilterNat_subset],
       simpset() addsimps [HFinite_FreeUltrafilterNat_iff,
        Bseq_NSBseq_iff RS sym, Bseq_iff1a]));
qed "NSBseq_HFinite_hypreal";

(*** A sequence converging to zero defines an infinitesimal ***)
Goalw [NSLIMSEQ_def] 
      "X ----NS> #0 ==> Abs_hypreal(hyprel^^{X}) : Infinitesimal";
by (dres_inst_tac [("x","whn")] bspec 1);
by (simp_tac (simpset() addsimps [HNatInfinite_whn]) 1);
by (auto_tac (claset(),simpset() addsimps [hypnat_omega_def,
    mem_infmal_iff RS sym,starfunNat,hypreal_of_real_zero]));
qed "NSLIMSEQ_zero_Infinitesimal_hypreal";

(***---------------------------------------------------------------
    Theorems proved by Harrison in HOL that we do not need 
    in order to prove equivalence between Cauchy criterion 
    and convergence:
 -- Show that every sequence contains a monotonic subsequence   
Goal "EX f. subseq f & monoseq (%n. s (f n))";
 -- Show that a subsequence of a bounded sequence is bounded
Goal "Bseq X ==> Bseq (%n. X (f n))";
 -- Show we can take subsequential terms arbitrarily far 
    up a sequence       
Goal "subseq f ==> n <= f(n)";
Goal "subseq f ==> EX n. N1 <= n & N2 <= f(n)";
 ---------------------------------------------------------------***)
