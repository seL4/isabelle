(*  Title       : RComplete.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Completeness theorems for positive
                  reals and reals 
*) 

claset_ref() := claset() delWrapper "bspec";

(*---------------------------------------------------------
       Completeness of reals: use supremum property of 
       preal and theorems about real_preal. Theorems 
       previously in Real.ML. 
 ---------------------------------------------------------*)
 (*a few lemmas*)
Goal "! x:P. 0r < x ==> \ 
\       ((? x:P. y < x) = (? X. real_of_preal X : P & \
\                          y < real_of_preal X))";
by (blast_tac (claset() addSDs [bspec,
				real_gt_zero_preal_Ex RS iffD1]) 1);
qed "real_sup_lemma1";

Goal "[| ! x:P. 0r < x; ? x. x: P; ? y. !x: P. x < y |] \
\         ==> (? X. X: {w. real_of_preal w : P}) & \
\             (? Y. !X: {w. real_of_preal w : P}. X < Y)";
by (rtac conjI 1);
by (blast_tac (claset() addDs [bspec, real_gt_zero_preal_Ex RS iffD1]) 1);
by Auto_tac;
by (dtac bspec 1 THEN assume_tac 1);
by (forward_tac [bspec] 1  THEN assume_tac 1);
by (dtac real_less_trans 1 THEN assume_tac 1);
by (dtac (real_gt_zero_preal_Ex RS iffD1) 1 THEN etac exE 1);
by (res_inst_tac [("x","ya")] exI 1);
by Auto_tac;
by (dres_inst_tac [("x","real_of_preal X")] bspec 1 THEN assume_tac 1);
by (etac real_of_preal_lessD 1);
qed "real_sup_lemma2";

(*-------------------------------------------------------------
            Completeness of Positive Reals
 -------------------------------------------------------------*)

(* Supremum property for the set of positive reals *)
(* FIXME: long proof - can be improved - need only have 
   one case split *) (* will do for now *)
Goal "[| ! x:P. 0r < x; ? x. x: P; ? y. !x: P. x < y |] \
\         ==> (? S. !y. (? x: P. y < x) = (y < S))";
by (res_inst_tac 
   [("x","real_of_preal (psup({w. real_of_preal w : P}))")] exI 1);
by Auto_tac;
by (forward_tac [real_sup_lemma2] 1 THEN Auto_tac);
by (case_tac "0r < ya" 1);
by (dtac (real_gt_zero_preal_Ex RS iffD1) 1);
by (dtac real_less_all_real2 2);
by Auto_tac;
by (rtac (preal_complete RS spec RS iffD1) 1);
by Auto_tac;
by (forward_tac [real_gt_preal_preal_Ex] 1);
by Auto_tac;
(* second part *)
by (rtac (real_sup_lemma1 RS iffD2) 1 THEN assume_tac 1);
by (case_tac "0r < ya" 1);
by (auto_tac (claset() addSDs [real_less_all_real2,
			       real_gt_zero_preal_Ex RS iffD1],simpset()));
by (forward_tac [real_sup_lemma2] 2 THEN Auto_tac);
by (forward_tac [real_sup_lemma2] 1 THEN Auto_tac);
by (rtac (preal_complete RS spec RS iffD2 RS bexE) 1);
by (Blast_tac 3);
by (Blast_tac 1);
by (Blast_tac 1);
by (Blast_tac 1);
qed "posreal_complete";

(*--------------------------------------------------------
   Completeness properties using isUb, isLub etc.
 -------------------------------------------------------*)

Goal "[| isLub R S x; isLub R S y |] ==> x = (y::real)";
by (forward_tac [isLub_isUb] 1);
by (forw_inst_tac [("x","y")] isLub_isUb 1);
by (blast_tac (claset() addSIs [real_le_anti_sym]
                        addSDs [isLub_le_isUb]) 1);
qed "real_isLub_unique";

Goalw [setle_def,setge_def] "[| (x::real) <=* S'; S <= S' |] ==> x <=* S";
by (Blast_tac 1);
qed "real_order_restrict";

(*----------------------------------------------------------------
           Completeness theorem for the positive reals(again)
 ----------------------------------------------------------------*)

Goal "[| ALL x: S. 0r < x; \
\        EX x. x: S; \
\        EX u. isUb (UNIV::real set) S u \
\     |] ==> EX t. isLub (UNIV::real set) S t";
by (res_inst_tac [("x","real_of_preal(psup({w. real_of_preal w : S}))")] exI 1);
by (auto_tac (claset(), simpset() addsimps [isLub_def,leastP_def,isUb_def]));
by (auto_tac (claset() addSIs [setleI,setgeI] 
	               addSDs [real_gt_zero_preal_Ex RS iffD1],
	      simpset()));
by (forw_inst_tac [("x","y")] bspec 1 THEN assume_tac 1);
by (dtac (real_gt_zero_preal_Ex RS iffD1) 1);
by (auto_tac (claset(), simpset() addsimps [real_of_preal_le_iff]));
by (rtac preal_psup_leI2a 1);
by (forw_inst_tac [("y","real_of_preal ya")] setleD 1 THEN assume_tac 1);
by (forward_tac  [real_ge_preal_preal_Ex] 1);
by (Step_tac 1);
by (res_inst_tac [("x","y")] exI 1);
by (blast_tac (claset() addSDs [setleD] addIs [real_of_preal_le_iff RS iffD1]) 1);
by (forw_inst_tac [("x","x")] bspec 1 THEN assume_tac 1);
by (forward_tac [isUbD2] 1);
by (dtac (real_gt_zero_preal_Ex RS iffD1) 1);
by (auto_tac (claset() addSDs [isUbD, real_ge_preal_preal_Ex],
	      simpset() addsimps [real_of_preal_le_iff]));
by (blast_tac (claset() addSDs [setleD] addSIs [psup_le_ub1] 
	                addIs [real_of_preal_le_iff RS iffD1]) 1);
qed "posreals_complete";


(*-------------------------------
    Lemmas
 -------------------------------*)
Goal "! y : {z. ? x: P. z = x + (-xa) + 1r} Int {x. 0r < x}. 0r < y";
by Auto_tac;
qed "real_sup_lemma3";
 
Goal "(xa <= S + X + (-Z)) = (xa + (-X) + Z <= (S::real))";
by (simp_tac (simpset() addsimps [real_diff_def, real_diff_le_eq RS sym] @
	                         real_add_ac) 1);
qed "lemma_le_swap2";

Goal "[| 0r < x + (-X) + 1r; x < xa |] ==> 0r < xa + (-X) + 1r";
by (dtac real_add_less_mono 1);
by (assume_tac 1);
by (dres_inst_tac [("C","-x"),("A","0r + x")] real_add_less_mono2 1);
by (asm_full_simp_tac
    (simpset() addsimps [real_add_zero_right, real_add_assoc RS sym,
			 real_add_minus_left,real_add_zero_left]) 1);
by (asm_full_simp_tac (simpset() addsimps real_add_ac) 1);
qed "lemma_real_complete1";

Goal "[| x + (-X) + 1r <= S; xa < x |] ==> xa + (-X) + 1r <= S";
by (dtac real_less_imp_le 1);
by (dtac real_add_le_mono 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps real_add_ac) 1);
qed "lemma_real_complete2";

Goal "[| x + (-X) + 1r <= S; xa < x |] ==> xa <= S + X + (-1r)"; (**)
by (rtac (lemma_le_swap2 RS iffD2) 1);
by (etac lemma_real_complete2 1);
by (assume_tac 1);
qed "lemma_real_complete2a";

Goal "[| x + (-X) + 1r <= S; xa <= x |] ==> xa <= S + X + (-1r)";
by (rotate_tac 1 1);
by (etac (real_le_imp_less_or_eq RS disjE) 1);
by (blast_tac (claset() addIs [lemma_real_complete2a]) 1);
by (blast_tac (claset() addIs [(lemma_le_swap2 RS iffD2)]) 1);
qed "lemma_real_complete2b";

(*------------------------------------
      reals Completeness (again!)
 ------------------------------------*)
Goal "[| EX X. X: S;  EX Y. isUb (UNIV::real set) S Y |]  \
\     ==> EX t. isLub (UNIV :: real set) S t";
by (Step_tac 1);
by (subgoal_tac "? u. u: {z. ? x: S. z = x + (-X) + 1r} \
\                Int {x. 0r < x}" 1);
by (subgoal_tac "isUb (UNIV::real set) ({z. ? x: S. z = x + (-X) + 1r} \
\                Int {x. 0r < x})  (Y + (-X) + 1r)" 1); 
by (cut_inst_tac [("P","S"),("xa","X")] real_sup_lemma3 1);
by (EVERY1[forward_tac [exI RSN (3,posreals_complete)], Blast_tac, Blast_tac, 
	   Step_tac]);
by (res_inst_tac [("x","t + X + (-1r)")] exI 1);
by (rtac isLubI2 1);
by (rtac setgeI 2 THEN Step_tac 2);
by (subgoal_tac "isUb (UNIV:: real set) ({z. ? x: S. z = x + (-X) + 1r} \
\                Int {x. 0r < x})  (y + (-X) + 1r)" 2); 
by (dres_inst_tac [("y","(y + (- X) + 1r)")] isLub_le_isUb 2 
      THEN assume_tac 2);
by (full_simp_tac
    (simpset() addsimps [real_diff_def, real_diff_le_eq RS sym] @
                        real_add_ac) 2);
by (rtac (setleI RS isUbI) 1);
by (Step_tac 1);
by (res_inst_tac [("R1.0","x"),("R2.0","y")] real_linear_less2 1);
by (stac lemma_le_swap2 1);
by (forward_tac [isLubD2] 1 THEN assume_tac 2);
by (Step_tac 1);
by (Blast_tac 1);
by (dtac lemma_real_complete1 1 THEN REPEAT(assume_tac 1));
by (stac lemma_le_swap2 1);
by (forward_tac [isLubD2] 1 THEN assume_tac 2);
by (Blast_tac 1);
by (rtac lemma_real_complete2b 1);
by (etac real_less_imp_le 2);
by (blast_tac (claset() addSIs [isLubD2]) 1 THEN Step_tac 1);
by (full_simp_tac (simpset() addsimps [real_add_assoc]) 1);
by (blast_tac (claset() addDs [isUbD] addSIs [setleI RS isUbI]
                        addIs [real_add_le_mono1]) 1);
by (blast_tac (claset() addDs [isUbD] addSIs [setleI RS isUbI]
                        addIs [real_add_le_mono1]) 1);
by (auto_tac (claset(),
	      simpset() addsimps [real_add_assoc RS sym,
				  real_zero_less_one]));
qed "reals_complete";

(*----------------------------------------------------------------
        Related: Archimedean property of reals
 ----------------------------------------------------------------*)

Goal "0r < x ==> EX n. rinv(real_of_posnat n) < x";
by (stac real_of_posnat_rinv_Ex_iff 1);
by (EVERY1[rtac ccontr, Asm_full_simp_tac]);
by (fold_tac [real_le_def]);
by (subgoal_tac "isUb (UNIV::real set) \
\   {z. EX n. z = x*(real_of_posnat n)} 1r" 1);
by (subgoal_tac "EX X. X : {z. EX n. z = x*(real_of_posnat n)}" 1);
by (dtac reals_complete 1);
by (auto_tac (claset() addIs [isUbI,setleI],simpset()));
by (subgoal_tac "ALL m. x*(real_of_posnat(Suc m)) <= t" 1);
by (asm_full_simp_tac (simpset() addsimps 
   [real_of_posnat_Suc,real_add_mult_distrib2]) 1);
by (blast_tac (claset() addIs [isLubD2]) 2);
by (asm_full_simp_tac
    (simpset() addsimps [real_le_diff_eq RS sym, real_diff_def]) 1);
by (subgoal_tac "isUb (UNIV::real set) \
\   {z. EX n. z = x*(real_of_posnat n)} (t + (-x))" 1);
by (blast_tac (claset() addSIs [isUbI,setleI]) 2);
by (dres_inst_tac [("y","t+(-x)")] isLub_le_isUb 1);
by (dres_inst_tac [("x","-t")] real_add_left_le_mono1 2);
by (auto_tac (claset() addDs [real_le_less_trans,
			      (real_minus_zero_less_iff2 RS iffD2)], 
	      simpset() addsimps [real_less_not_refl,real_add_assoc RS sym]));
qed "reals_Archimedean";

Goal "EX n. (x::real) < real_of_posnat n";
by (res_inst_tac [("R1.0","x"),("R2.0","0r")] real_linear_less2 1);
by (res_inst_tac [("x","0")] exI 1);
by (res_inst_tac [("x","0")] exI 2);
by (auto_tac (claset() addEs [real_less_trans],
	      simpset() addsimps [real_of_posnat_one,real_zero_less_one]));
by (forward_tac [(real_rinv_gt_zero RS reals_Archimedean)] 1);
by (Step_tac 1 THEN res_inst_tac [("x","n")] exI 1);
by (forw_inst_tac [("y","rinv x")] real_mult_less_mono1 1);
by (auto_tac (claset(),simpset() addsimps [real_not_refl2 RS not_sym]));
by (dres_inst_tac [("n1","n"),("y","1r")] 
     (real_of_posnat_less_zero RS real_mult_less_mono2)  1);
by (auto_tac (claset(),
	      simpset() addsimps [real_of_posnat_less_zero,
				  real_not_refl2 RS not_sym,
				  real_mult_assoc RS sym]));
qed "reals_Archimedean2";





