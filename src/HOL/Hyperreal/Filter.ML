(*  Title       : Filter.ML
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Filters and Ultrafilter
*) 

(*------------------------------------------------------------------
      Properties of Filters and Freefilters - 
      rules for intro, destruction etc.
 ------------------------------------------------------------------*)

Goalw [is_Filter_def] "is_Filter X S ==> X <= Pow(S)";
by (Blast_tac 1);
qed "is_FilterD1";

Goalw [is_Filter_def] "is_Filter X S ==> X ~= {}";
by (Blast_tac 1);
qed "is_FilterD2";

Goalw [is_Filter_def] "is_Filter X S ==> {} ~: X";
by (Blast_tac 1);
qed "is_FilterD3";

Goalw [Filter_def] "is_Filter X S ==> X : Filter S";
by (Blast_tac 1);
qed "mem_FiltersetI";

Goalw [Filter_def] "X : Filter S ==> is_Filter X S";
by (Blast_tac 1);
qed "mem_FiltersetD";

Goal "X : Filter S ==> {} ~: X";
by (etac (mem_FiltersetD RS is_FilterD3) 1);
qed "Filter_empty_not_mem";

bind_thm ("Filter_empty_not_memE",(Filter_empty_not_mem RS notE));

Goalw [Filter_def,is_Filter_def] 
      "[| X: Filter S; A: X; B: X |] ==> A Int B : X";
by (Blast_tac 1);
qed "mem_FiltersetD1";

Goalw [Filter_def,is_Filter_def] 
      "[| X: Filter S; A: X; A <= B; B <= S|] ==> B : X";
by (Blast_tac 1);
qed "mem_FiltersetD2";

Goalw [Filter_def,is_Filter_def] 
      "[| X: Filter S; A: X |] ==> A : Pow S";
by (Blast_tac 1);
qed "mem_FiltersetD3";

Goalw [Filter_def,is_Filter_def] 
      "X: Filter S  ==> S : X";
by (Blast_tac 1);
qed "mem_FiltersetD4";

Goalw [is_Filter_def] 
      "[| X <= Pow(S);\
\              S : X; \
\              X ~= {}; \
\              {} ~: X; \
\              ALL u: X. ALL v: X. u Int v : X; \
\              ALL u v. u: X & u<=v & v<=S --> v: X \
\           |] ==> is_Filter X S";
by (Blast_tac 1); 
qed "is_FilterI";

Goal "[| X <= Pow(S);\
\              S : X; \
\              X ~= {}; \
\              {} ~: X; \
\              ALL u: X. ALL v: X. u Int v : X; \
\              ALL u v. u: X & u<=v & v<=S --> v: X \
\           |] ==> X: Filter S";
by (blast_tac (claset() addIs [mem_FiltersetI,is_FilterI]) 1);
qed "mem_FiltersetI2";

Goalw [is_Filter_def]
      "is_Filter X S ==> X <= Pow(S) & \
\                          S : X & \
\                          X ~= {} & \
\                          {} ~: X  & \
\                          (ALL u: X. ALL v: X. u Int v : X) & \
\                          (ALL u v. u: X & u <= v & v<=S --> v: X)";
by (Fast_tac 1);
qed "is_FilterE_lemma";

Goalw [is_Filter_def]
      "X : Filter S ==> X <= Pow(S) &\
\                          S : X & \
\                          X ~= {} & \
\                          {} ~: X  & \
\                          (ALL u: X. ALL v: X. u Int v : X) & \
\                          (ALL u v. u: X & u <= v & v<=S --> v: X)";
by (etac (mem_FiltersetD RS is_FilterE_lemma) 1);
qed "memFiltersetE_lemma";

Goalw [Filter_def,Freefilter_def] 
      "X: Freefilter S ==> X: Filter S";
by (Fast_tac 1);
qed "Freefilter_Filter";

Goalw [Freefilter_def] 
      "X: Freefilter S ==> ALL y: X. ~finite(y)";
by (Blast_tac 1);
qed "mem_Freefilter_not_finite";

Goal "[| X: Freefilter S; x: X |] ==> ~ finite x";
by (blast_tac (claset() addSDs [mem_Freefilter_not_finite]) 1);
qed "mem_FreefiltersetD1";

bind_thm ("mem_FreefiltersetE1", (mem_FreefiltersetD1 RS notE));

Goal "[| X: Freefilter S; finite x|] ==> x ~: X";
by (blast_tac (claset() addSDs [mem_Freefilter_not_finite]) 1);
qed "mem_FreefiltersetD2";

Goalw [Freefilter_def] 
      "[| X: Filter S; ALL x. ~(x: X & finite x) |] ==> X: Freefilter S";
by (Blast_tac 1);
qed "mem_FreefiltersetI1";

Goalw [Freefilter_def]
      "[| X: Filter S; ALL x. (x ~: X | ~ finite x) |] ==> X: Freefilter S";
by (Blast_tac 1);
qed "mem_FreefiltersetI2";

Goal "[| X: Filter S; A: X; B: X |] ==> A Int B ~= {}";
by (forw_inst_tac [("A","A"),("B","B")] mem_FiltersetD1 1);
by (auto_tac (claset() addSDs [Filter_empty_not_mem],simpset()));
qed "Filter_Int_not_empty";

bind_thm ("Filter_Int_not_emptyE",(Filter_Int_not_empty RS notE));

(*----------------------------------------------------------------------------------
              Ultrafilters and Free ultrafilters
 ----------------------------------------------------------------------------------*)

Goalw [Ultrafilter_def] "X : Ultrafilter S ==> X: Filter S";
by (Blast_tac 1);
qed "Ultrafilter_Filter";

Goalw [Ultrafilter_def] 
      "X : Ultrafilter S ==> !A: Pow(S). A : X | S - A: X";
by (Blast_tac 1);
qed "mem_UltrafiltersetD2";

Goalw [Ultrafilter_def] 
      "[|X : Ultrafilter S; A <= S; A ~: X |] ==> S - A: X";
by (Blast_tac 1);
qed "mem_UltrafiltersetD3";

Goalw [Ultrafilter_def] 
      "[|X : Ultrafilter S; A <= S; S - A ~: X |] ==> A: X";
by (Blast_tac 1);
qed "mem_UltrafiltersetD4";

Goalw [Ultrafilter_def]
     "[| X: Filter S; \
\             ALL A: Pow(S). A: X | S - A : X |] ==> X: Ultrafilter S";
by (Blast_tac 1);
qed "mem_UltrafiltersetI";

Goalw [Ultrafilter_def,FreeUltrafilter_def]
     "X: FreeUltrafilter S ==> X: Ultrafilter S";
by (Blast_tac 1);
qed "FreeUltrafilter_Ultrafilter";

Goalw [FreeUltrafilter_def]
     "X: FreeUltrafilter S ==> ALL y: X. ~finite(y)";
by (Blast_tac 1);
qed "mem_FreeUltrafilter_not_finite";

Goal "[| X: FreeUltrafilter S; x: X |] ==> ~ finite x";
by (blast_tac (claset() addSDs [mem_FreeUltrafilter_not_finite]) 1);
qed "mem_FreeUltrafiltersetD1";

bind_thm ("mem_FreeUltrafiltersetE1", (mem_FreeUltrafiltersetD1 RS notE));

Goal "[| X: FreeUltrafilter S; finite x|] ==> x ~: X";
by (blast_tac (claset() addSDs [mem_FreeUltrafilter_not_finite]) 1);
qed "mem_FreeUltrafiltersetD2";

Goalw [FreeUltrafilter_def] 
      "[| X: Ultrafilter S; \
\              ALL x. ~(x: X & finite x) |] ==> X: FreeUltrafilter S";
by (Blast_tac 1);
qed "mem_FreeUltrafiltersetI1";

Goalw [FreeUltrafilter_def]
      "[| X: Ultrafilter S; \
\              ALL x. (x ~: X | ~ finite x) |] ==> X: FreeUltrafilter S";
by (Blast_tac 1);
qed "mem_FreeUltrafiltersetI2";

Goalw [FreeUltrafilter_def,Freefilter_def,Ultrafilter_def]
     "(X: FreeUltrafilter S) = (X: Freefilter S & (ALL x:Pow(S). x: X | S - x: X))";
by (Blast_tac 1);
qed "FreeUltrafilter_iff";

(*-------------------------------------------------------------------
   A Filter F on S is an ultrafilter iff it is a maximal filter 
   i.e. whenever G is a filter on I and F <= F then F = G
 --------------------------------------------------------------------*)
(*---------------------------------------------------------------------
  lemmas that shows existence of an extension to what was assumed to
  be a maximal filter. Will be used to derive contradiction in proof of
  property of ultrafilter 
 ---------------------------------------------------------------------*)
Goal "[| F ~= {}; A <= S |] ==> \
\        EX x. x: {X. X <= S & (EX f:F. A Int f <= X)}";
by (Blast_tac 1);
qed "lemma_set_extend";

Goal "a: X ==> X ~= {}";
by (Step_tac 1);
qed "lemma_set_not_empty";

Goal "x Int F <= {} ==> F <= - x";
by (Blast_tac 1);
qed "lemma_empty_Int_subset_Compl";

Goalw [Filter_def,is_Filter_def]
      "[| F: Filter S; A ~: F; A <= S|] \
\          ==> ALL B. B ~: F | ~ B <= A";
by (Blast_tac 1);
qed "mem_Filterset_disjI";

Goal "F : Ultrafilter S ==> \
\         (F: Filter S & (ALL G: Filter S. F <= G --> F = G))";
by (auto_tac (claset(),simpset() addsimps [Ultrafilter_def]));
by (dres_inst_tac [("x","x")] bspec 1);
by (etac mem_FiltersetD3 1 THEN assume_tac 1);
by (Step_tac 1);
by (dtac subsetD 1 THEN assume_tac 1);
by (blast_tac (claset() addSDs [Filter_Int_not_empty]) 1);
qed "Ultrafilter_max_Filter";


(*--------------------------------------------------------------------------------
     This is a very long and tedious proof; need to break it into parts.
     Have proof that {X. X <= S & (EX f: F. A Int f <= X)} is a filter as 
     a lemma
--------------------------------------------------------------------------------*)
Goalw [Ultrafilter_def] 
      "[| F: Filter S; \
\              ALL G: Filter S. F <= G --> F = G |] ==> F : Ultrafilter S";
by (Step_tac 1);
by (rtac ccontr 1);
by (forward_tac [mem_FiltersetD RS is_FilterD2] 1);
by (forw_inst_tac [("x","{X. X <= S & (EX f: F. A Int f <= X)}")] bspec 1);
by (EVERY1[rtac mem_FiltersetI2, Blast_tac, Asm_full_simp_tac]);
by (blast_tac (claset() addDs [mem_FiltersetD3]) 1);
by (etac (lemma_set_extend RS exE) 1);
by (assume_tac 1 THEN etac lemma_set_not_empty 1);
by (REPEAT(rtac ballI 2) THEN Asm_full_simp_tac 2);
by (rtac conjI 2 THEN Blast_tac 2);
by (REPEAT(etac conjE 2) THEN REPEAT(etac bexE 2));
by (res_inst_tac [("x","f Int fa")] bexI 2);
by (etac mem_FiltersetD1 3);
by (assume_tac 3 THEN assume_tac 3);
by (Fast_tac 2);
by (EVERY[REPEAT(rtac allI 2), rtac impI 2,Asm_full_simp_tac 2]);
by (EVERY[REPEAT(etac conjE 2), etac bexE 2]);
by (res_inst_tac [("x","f")] bexI 2);
by (rtac subsetI 2);
by (Fast_tac 2 THEN assume_tac 2);
by (Step_tac 2);
by (Blast_tac 3);
by (eres_inst_tac [("c","A")] equalityCE 3);
by (REPEAT(Blast_tac 3));
by (dres_inst_tac [("A","xa")] mem_FiltersetD3 2 THEN assume_tac 2);
by (Blast_tac 2);
by (dtac lemma_empty_Int_subset_Compl 1);
by (EVERY1[ftac mem_Filterset_disjI , assume_tac, Fast_tac]);
by (dtac mem_FiltersetD3 1 THEN assume_tac 1);
by (dres_inst_tac [("x","f")] spec 1);
by (Blast_tac 1);
qed "max_Filter_Ultrafilter";

Goal "(F : Ultrafilter S) = (F: Filter S & (ALL G: Filter S. F <= G --> F = G))";
by (blast_tac (claset() addSIs [Ultrafilter_max_Filter,max_Filter_Ultrafilter]) 1);
qed "Ultrafilter_iff";

(*--------------------------------------------------------------------
             A few properties of freefilters
 -------------------------------------------------------------------*)

Goal "F1 Int F2 = ((F1 Int Y) Int F2) Un ((F2 Int (- Y)) Int F1)";
by (Auto_tac);
qed "lemma_Compl_cancel_eq";

Goal "finite X ==> finite (X Int Y)";
by (etac (Int_lower1 RS finite_subset) 1);
qed "finite_IntI1";

Goal "finite Y ==> finite (X Int Y)";
by (etac (Int_lower2 RS finite_subset) 1);
qed "finite_IntI2";

Goal "[| finite (F1 Int Y); \
\                 finite (F2 Int (- Y)) \
\              |] ==> finite (F1 Int F2)";
by (res_inst_tac [("Y1","Y")] (lemma_Compl_cancel_eq RS ssubst) 1);
by (rtac finite_UnI 1);
by (auto_tac (claset() addSIs [finite_IntI1,finite_IntI2],simpset()));
qed "finite_Int_Compl_cancel";

Goal "U: Freefilter S  ==> \
\         ~ (EX f1: U. EX f2: U. finite (f1 Int x) \
\                            & finite (f2 Int (- x)))";
by (Step_tac 1);
by (forw_inst_tac [("A","f1"),("B","f2")] 
    (Freefilter_Filter RS mem_FiltersetD1) 1);
by (dres_inst_tac [("x","f1 Int f2")] mem_FreefiltersetD1 3);
by (dtac finite_Int_Compl_cancel 4);
by (Auto_tac);
qed "Freefilter_lemma_not_finite";

(* the lemmas below follow *)
Goal "U: Freefilter S ==> \
\          ALL f: U. ~ finite (f Int x) | ~finite (f Int (- x))";
by (blast_tac (claset() addSDs [Freefilter_lemma_not_finite,bspec]) 1);
qed "Freefilter_Compl_not_finite_disjI";

Goal "U: Freefilter S ==> \
\          (ALL f: U. ~ finite (f Int x)) | (ALL f:U. ~finite (f Int (- x)))";
by (blast_tac (claset() addSDs [Freefilter_lemma_not_finite,bspec]) 1);
qed "Freefilter_Compl_not_finite_disjI2";

Goal "- UNIV = {}";
by (Auto_tac );
qed "Compl_UNIV_eq";

Addsimps [Compl_UNIV_eq];

Goal "- {} = UNIV";
by (Auto_tac );
qed "Compl_empty_eq";

Addsimps [Compl_empty_eq];

val [prem] = goal (the_context ()) "~ finite (UNIV:: 'a set) ==> \
\            {A:: 'a set. finite (- A)} : Filter UNIV";
by (cut_facts_tac [prem] 1);
by (rtac mem_FiltersetI2 1);
by (auto_tac (claset(), simpset() delsimps [Collect_empty_eq]));
by (eres_inst_tac [("c","UNIV")] equalityCE 1);
by (Auto_tac);
by (etac (Compl_anti_mono RS finite_subset) 1);
by (assume_tac 1);
qed "cofinite_Filter";

Goal "~finite(UNIV :: 'a set) ==> ~finite (X :: 'a set) | ~finite (- X)";
by (dres_inst_tac [("A1","X")] (Compl_partition RS ssubst) 1);
by (Asm_full_simp_tac 1); 
qed "not_finite_UNIV_disjI";

Goal "[| ~finite(UNIV :: 'a set); \
\                 finite (X :: 'a set) \
\              |] ==>  ~finite (- X)";
by (dres_inst_tac [("X","X")] not_finite_UNIV_disjI 1);
by (Blast_tac 1);
qed "not_finite_UNIV_Compl";

val [prem] = goal (the_context ()) "~ finite (UNIV:: 'a set) ==> \
\            !X: {A:: 'a set. finite (- A)}. ~ finite X";
by (cut_facts_tac [prem] 1);
by (auto_tac (claset() addDs [not_finite_UNIV_disjI],simpset()));
qed "mem_cofinite_Filter_not_finite";

val [prem] = goal (the_context ()) "~ finite (UNIV:: 'a set) ==> \
\            {A:: 'a set. finite (- A)} : Freefilter UNIV";
by (cut_facts_tac [prem] 1);
by (rtac mem_FreefiltersetI2 1);
by (rtac cofinite_Filter 1 THEN assume_tac 1);
by (blast_tac (claset() addSDs [mem_cofinite_Filter_not_finite]) 1);
qed "cofinite_Freefilter";

Goal "UNIV - x = - x";
by (Auto_tac);
qed "UNIV_diff_Compl";
Addsimps [UNIV_diff_Compl];

Goalw [Ultrafilter_def,FreeUltrafilter_def]
     "[| ~finite(UNIV :: 'a set); (U :: 'a set set): FreeUltrafilter UNIV\
\         |] ==> {X. finite(- X)} <= U";
by (ftac cofinite_Filter 1);
by (Step_tac 1);
by (forw_inst_tac [("X","- x :: 'a set")] not_finite_UNIV_Compl 1);
by (assume_tac 1);
by (Step_tac 1 THEN Fast_tac 1);
by (dres_inst_tac [("x","x")] bspec 1);
by (Blast_tac 1);
by (asm_full_simp_tac (simpset() addsimps [UNIV_diff_Compl]) 1);
qed "FreeUltrafilter_contains_cofinite_set";

(*--------------------------------------------------------------------
   We prove: 1. Existence of maximal filter i.e. ultrafilter
             2. Freeness property i.e ultrafilter is free
             Use a locale to prove various lemmas and then 
             export main result: The Ultrafilter Theorem
 -------------------------------------------------------------------*)
Open_locale "UFT"; 

Goalw [chain_def, thm "superfrechet_def", thm "frechet_def"]
   "!!(c :: 'a set set set). c : chain (superfrechet S) ==>  Union c <= Pow S";
by (Step_tac 1);
by (dtac subsetD 1 THEN assume_tac 1);
by (Step_tac 1);
by (dres_inst_tac [("X","X")] mem_FiltersetD3 1);
by (Auto_tac);
qed "chain_Un_subset_Pow";

Goalw [chain_def,Filter_def,is_Filter_def,
           thm "superfrechet_def", thm "frechet_def"] 
          "!!(c :: 'a set set set). c: chain (superfrechet S) \
\         ==> !x: c. {} < x";
by (blast_tac (claset() addSIs [psubsetI]) 1);
qed "mem_chain_psubset_empty";

Goal "!!(c :: 'a set set set). \
\            [| c: chain (superfrechet S);\
\               c ~= {} \
\            |]\
\            ==> Union(c) ~= {}";
by (dtac mem_chain_psubset_empty 1);
by (Step_tac 1);
by (dtac bspec 1 THEN assume_tac 1);
by (auto_tac (claset() addDs [Union_upper,bspec],
    simpset() addsimps [psubset_def]));
qed "chain_Un_not_empty";

Goalw [is_Filter_def,Filter_def,chain_def,thm "superfrechet_def"] 
           "!!(c :: 'a set set set). \
\           c : chain (superfrechet S)  \
\           ==> {} ~: Union(c)";
by (Blast_tac 1);
qed "Filter_empty_not_mem_Un";

Goal "c: chain (superfrechet S) \
\         ==> ALL u : Union(c). ALL v: Union(c). u Int v : Union(c)";
by (Step_tac 1);
by (forw_inst_tac [("x","X"),("y","Xa")] chainD 1);
by (REPEAT(assume_tac 1));
by (dtac chainD2 1);
by (etac disjE 1);
by (res_inst_tac [("X","Xa")] UnionI 1 THEN assume_tac 1);
by (dres_inst_tac [("A","X")] subsetD 1 THEN assume_tac 1);
by (dres_inst_tac [("c","Xa")] subsetD 1 THEN assume_tac 1);
by (res_inst_tac [("X","X")] UnionI 2 THEN assume_tac 2);
by (dres_inst_tac [("A","Xa")] subsetD 2 THEN assume_tac 2);
by (dres_inst_tac [("c","X")] subsetD 2 THEN assume_tac 2);
by (auto_tac (claset() addIs [mem_FiltersetD1], 
     simpset() addsimps [thm "superfrechet_def"]));
qed "Filter_Un_Int";

Goal "c: chain (superfrechet S) \
\         ==> ALL u v. u: Union(c) & \
\                 (u :: 'a set) <= v & v <= S --> v: Union(c)";
by (Step_tac 1);
by (dtac chainD2 1);
by (dtac subsetD 1 THEN assume_tac 1);
by (rtac UnionI 1 THEN assume_tac 1);
by (auto_tac (claset() addIs [mem_FiltersetD2], 
     simpset() addsimps [thm "superfrechet_def"]));
qed "Filter_Un_subset";

Goalw [chain_def,thm "superfrechet_def"]
      "!!(c :: 'a set set set). \
\            [| c: chain (superfrechet S);\
\               x: c \
\            |] ==> x : Filter S";
by (Blast_tac 1);
qed "lemma_mem_chain_Filter";

Goalw [chain_def,thm "superfrechet_def"]
     "!!(c :: 'a set set set). \
\            [| c: chain (superfrechet S);\
\               x: c \
\            |] ==> frechet S <= x";
by (Blast_tac 1);
qed "lemma_mem_chain_frechet_subset";

Goal "!!(c :: 'a set set set). \
\         [| c ~= {}; \
\            c : chain (superfrechet (UNIV :: 'a set))\
\         |] ==> Union c : superfrechet (UNIV)";
by (simp_tac (simpset() addsimps 
    [thm "superfrechet_def",thm "frechet_def"]) 1);
by (Step_tac 1);
by (rtac mem_FiltersetI2 1);
by (etac chain_Un_subset_Pow 1);
by (rtac UnionI 1 THEN assume_tac 1);
by (etac (lemma_mem_chain_Filter RS mem_FiltersetD4) 1 THEN assume_tac 1);
by (etac chain_Un_not_empty 1);
by (etac Filter_empty_not_mem_Un 2);
by (etac Filter_Un_Int 2);
by (etac Filter_Un_subset 2);
by (subgoal_tac "xa : frechet (UNIV)" 2);
by (rtac UnionI 2 THEN assume_tac 2);
by (rtac (lemma_mem_chain_frechet_subset RS subsetD) 2);
by (auto_tac (claset(),simpset() addsimps [thm "frechet_def"]));
qed "Un_chain_mem_cofinite_Filter_set";

Goal "EX U: superfrechet (UNIV). \
\               ALL G: superfrechet (UNIV). U <= G --> U = G";
by (rtac Zorn_Lemma2 1);
by (cut_facts_tac [thm "not_finite_UNIV" RS cofinite_Filter] 1);
by (Step_tac 1);
by (res_inst_tac [("Q","c={}")] (excluded_middle RS disjE) 1);
by (res_inst_tac [("x","Union c")] bexI 1 THEN Blast_tac 1);
by (rtac Un_chain_mem_cofinite_Filter_set 1 THEN REPEAT(assume_tac 1));
by (res_inst_tac [("x","frechet (UNIV)")] bexI 1 THEN Blast_tac 1);
by (auto_tac (claset(),
	      simpset() addsimps 
	      [thm "superfrechet_def", thm "frechet_def"]));
qed "max_cofinite_Filter_Ex";

Goal "EX U: superfrechet UNIV. (\
\               ALL G: superfrechet UNIV. U <= G --> U = G) \ 
\                             & (ALL x: U. ~finite x)";
by (cut_facts_tac [thm "not_finite_UNIV" RS 
         (export max_cofinite_Filter_Ex)] 1);
by (Step_tac 1);
by (res_inst_tac [("x","U")] bexI 1);
by (auto_tac (claset(),simpset() addsimps 
        [thm "superfrechet_def", thm "frechet_def"]));
by (dres_inst_tac [("c","- x")] subsetD 1);
by (Asm_simp_tac 1);
by (forw_inst_tac [("A","x"),("B","- x")] mem_FiltersetD1 1);
by (dtac Filter_empty_not_mem 3);
by (ALLGOALS(Asm_full_simp_tac ));
qed "max_cofinite_Freefilter_Ex";

(*--------------------------------------------------------------------------------
               There exists a free ultrafilter on any infinite set
 --------------------------------------------------------------------------------*)

Goalw [FreeUltrafilter_def] "EX U. U: FreeUltrafilter (UNIV :: 'a set)";
by (cut_facts_tac [thm "not_finite_UNIV" RS (export max_cofinite_Freefilter_Ex)] 1);
by (asm_full_simp_tac (simpset() addsimps 
    [thm "superfrechet_def", Ultrafilter_iff, thm "frechet_def"]) 1);
by (Step_tac 1);
by (res_inst_tac [("x","U")] exI 1);
by (Step_tac 1);
by (Blast_tac 1);
qed "FreeUltrafilter_ex";

bind_thm ("FreeUltrafilter_Ex", export FreeUltrafilter_ex);

Close_locale "UFT";
