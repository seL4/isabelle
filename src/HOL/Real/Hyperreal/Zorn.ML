(*  Title       : Zorn.ML
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Zorn's Lemma -- adapted proofs from lcp's ZF/Zorn.ML
*) 

(*---------------------------------------------------------------
      Section 1.  Mathematical Preamble 
 ---------------------------------------------------------------*)

Goal "(ALL x:C. x<=A | B<=x) ==> Union(C)<=A | B<=Union(C)";
by (Blast_tac 1);
qed "Union_lemma0";

(*-- similar to subset_cs in ZF/subset.thy --*)
val thissubset_SIs =
    [subset_refl,Union_least, UN_least, Un_least, 
     Inter_greatest, Int_greatest,
     Un_upper1, Un_upper2, Int_lower1, Int_lower2];


(*A claset for subset reasoning*)
val thissubset_cs = claset() 
    delrules [subsetI, subsetCE]
    addSIs thissubset_SIs
    addIs  [Union_upper, Inter_lower];

(* increasingD2 of ZF/Zorn.ML *) 
Goalw [succ_def] "x <= succ S x";
by (rtac (expand_if RS iffD2) 1);
by (auto_tac (claset(),simpset() addsimps [super_def,
               maxchain_def,psubset_def]));
by (rtac swap 1 THEN assume_tac 1);
by (rtac selectI2 1);
by (ALLGOALS(Blast_tac));
qed "Abrial_axiom1";

val [TFin_succI, Pow_TFin_UnionI] = TFin.intrs;
val TFin_UnionI = PowI RS Pow_TFin_UnionI;

val major::prems = Goal  
          "[| n : TFin S; \
\            !!x. [| x: TFin S; P(x) |] ==> P(succ S x); \
\            !!Y. [| Y <= TFin S; Ball Y P |] ==> P(Union Y) |] \
\         ==> P(n)";
by (rtac (major RS TFin.induct) 1);
by (ALLGOALS (fast_tac (claset() addIs prems)));
qed "TFin_induct";

(*Perform induction on n, then prove the major premise using prems. *)
fun TFin_ind_tac a prems i = 
    EVERY [res_inst_tac [("n",a)] TFin_induct i,
           rename_last_tac a ["1"] (i+1),
           rename_last_tac a ["2"] (i+2),
           ares_tac prems i];

Goal "x <= y ==> x <= succ S y";
by (etac (Abrial_axiom1 RSN (2,subset_trans)) 1);
qed "succ_trans";

(*Lemma 1 of section 3.1*)
Goal "[| n: TFin S;  m: TFin S;  \
\        ALL x: TFin S. x <= m --> x = m | succ S x <= m \
\     |] ==> n <= m | succ S m <= n";
by (etac TFin_induct 1);
by (etac Union_lemma0 2);               (*or just Blast_tac*)
by (blast_tac (thissubset_cs addIs [succ_trans]) 1);
qed "TFin_linear_lemma1";

(* Lemma 2 of section 3.2 *)
Goal "m: TFin S ==> ALL n: TFin S. n<=m --> n=m | succ S n<=m";
by (etac TFin_induct 1);
by (rtac (impI RS ballI) 1);
(*case split using TFin_linear_lemma1*)
by (res_inst_tac [("n1","n"), ("m1","x")] 
    (TFin_linear_lemma1 RS disjE) 1  THEN  REPEAT (assume_tac 1));
by (dres_inst_tac [("x","n")] bspec 1 THEN assume_tac 1);
by (blast_tac (thissubset_cs addIs [succ_trans]) 1);
by (REPEAT (ares_tac [disjI1,equalityI] 1));
(*second induction step*)
by (rtac (impI RS ballI) 1);
by (rtac (Union_lemma0 RS disjE) 1);
by (rtac disjI2 3);
by (REPEAT (ares_tac [disjI1,equalityI] 2));
by (rtac ballI 1);
by (ball_tac 1);
by (set_mp_tac 1);
by (res_inst_tac [("n1","n"), ("m1","x")] 
    (TFin_linear_lemma1 RS disjE) 1  THEN  REPEAT (assume_tac 1));
by (blast_tac thissubset_cs 1);
by (rtac (Abrial_axiom1 RS subset_trans RS disjI1) 1);
by (assume_tac 1);
qed "TFin_linear_lemma2";

(*a more convenient form for Lemma 2*)
Goal "[| n<=m;  m: TFin S;  n: TFin S |] ==> n=m | succ S n<=m";
by (rtac (TFin_linear_lemma2 RS bspec RS mp) 1);
by (REPEAT (assume_tac 1));
qed "TFin_subsetD";

(*Consequences from section 3.3 -- Property 3.2, the ordering is total*)
Goal "[| m: TFin S;  n: TFin S|] ==> n<=m | m<=n";
by (rtac (TFin_linear_lemma2 RSN (3,TFin_linear_lemma1) RS disjE) 1);
by (REPEAT (assume_tac 1) THEN etac disjI2 1);
by (blast_tac (thissubset_cs addIs [Abrial_axiom1 RS subset_trans]) 1);
qed "TFin_subset_linear";

(*Lemma 3 of section 3.3*)
Goal "[| n: TFin S;  m: TFin S;  m = succ S m |] ==> n<=m";
by (etac TFin_induct 1);
by (dtac TFin_subsetD 1);
by (REPEAT (assume_tac 1));
by (fast_tac (claset() addEs [ssubst]) 1);
by (blast_tac (thissubset_cs) 1);
qed "eq_succ_upper";

(*Property 3.3 of section 3.3*)
Goal "m: TFin S ==> (m = succ S m) = (m = Union(TFin S))";
by (rtac iffI 1);
by (rtac (Union_upper RS equalityI) 1);
by (rtac (eq_succ_upper RS Union_least) 2);
by (REPEAT (assume_tac 1));
by (etac ssubst 1);
by (rtac (Abrial_axiom1 RS equalityI) 1);
by (blast_tac (thissubset_cs addIs [TFin_UnionI, TFin_succI]) 1);
qed "equal_succ_Union";

(*-------------------------------------------------------------------------
    Section 4.  Hausdorff's Theorem: every set contains a maximal chain 
    NB: We assume the partial ordering is <=, the subset relation! 
 -------------------------------------------------------------------------*)

Goalw [chain_def] "({} :: 'a set set) : chain S";
by (Auto_tac);
qed "empty_set_mem_chain";

Goalw [super_def] "super S c <= chain S";
by (Fast_tac 1);
qed "super_subset_chain";

Goalw [maxchain_def] "maxchain S <= chain S";
by (Fast_tac 1);
qed "maxchain_subset_chain";

Goalw [succ_def] "c ~: chain S ==> succ S c = c";
by (fast_tac (claset() addSIs [if_P]) 1);
qed "succI1";

Goalw [succ_def] "c: maxchain S ==> succ S c = c";
by (fast_tac (claset() addSIs [if_P]) 1);
qed "succI2";

Goalw [succ_def] "c: chain S - maxchain S ==> \
\                         succ S c = (@c'. c': super S c)";
by (fast_tac (claset() addSIs [if_not_P]) 1);
qed "succI3";

Goal "c: chain S - maxchain S ==> ? d. d: super S c";
by (rewrite_goals_tac [super_def,maxchain_def]);
by (Auto_tac);
qed "mem_super_Ex";

Goal "c: chain S - maxchain S ==> \
\                         (@c'. c': super S c): super S c";
by (etac (mem_super_Ex RS exE) 1);
by (rtac selectI2 1);
by (Auto_tac);
qed "select_super";

Goal "c: chain S - maxchain S ==> \
\                         (@c'. c': super S c) ~= c";
by (rtac notI 1);
by (dtac select_super 1);
by (asm_full_simp_tac (simpset() addsimps [super_def,psubset_def]) 1);
qed "select_not_equals";

Goal "c: chain S - maxchain S ==> \
\                         succ S c ~= c";
by (ftac succI3 1);
by (Asm_simp_tac 1);
by (rtac select_not_equals 1);
by (assume_tac 1);
qed "succ_not_equals";

Goal "c: TFin S ==> (c :: 'a set set): chain S";
by (etac TFin_induct 1);
by (asm_simp_tac (simpset() addsimps [succ_def,
    select_super RS (super_subset_chain RS subsetD)]
                   setloop split_tac [expand_if]) 1);
by (rewtac chain_def);
by (rtac CollectI 1);
by Safe_tac;
by (dtac bspec 1 THEN assume_tac 1);
by (res_inst_tac  [("m1","Xa"), ("n1","X")] (TFin_subset_linear RS disjE) 2);
by (ALLGOALS(Blast_tac));
qed "TFin_chain_lemm4";
 
Goal "EX c. (c :: 'a set set): maxchain S";
by (res_inst_tac [("x", "Union(TFin S)")] exI 1);
by (rtac classical 1);
by (subgoal_tac "succ S (Union(TFin S)) = Union(TFin S)" 1);
by (resolve_tac [equal_succ_Union RS iffD2 RS sym] 2);
by (resolve_tac [subset_refl RS TFin_UnionI] 2);
by (rtac refl 2);
by (cut_facts_tac [subset_refl RS TFin_UnionI RS TFin_chain_lemm4] 1);
by (dtac (DiffI RS succ_not_equals) 1);
by (ALLGOALS(Blast_tac));
qed "Hausdorff";


(*---------------------------------------------------------------
  Section 5.  Zorn's Lemma: if all chains have upper bounds 
                               there is  a maximal element 
 ----------------------------------------------------------------*)
Goalw [chain_def]
    "[| c: chain S; z: S; \
\             ALL x:c. x<=(z:: 'a set) |] ==> {z} Un c : chain S";
by (Blast_tac 1);
qed "chain_extend";

Goalw [chain_def] "[| c: chain S; x: c |] ==> x <= Union(c)";
by (Auto_tac);
qed "chain_Union_upper";

Goalw [chain_def] "c: chain S ==> ! x: c. x <= Union(c)";
by (Auto_tac);
qed "chain_ball_Union_upper";

Goal "[| c: maxchain S; u: S; Union(c) <= u |] ==> Union(c) = u";
by (rtac ccontr 1);
by (asm_full_simp_tac (simpset() addsimps [maxchain_def]) 1);
by (etac conjE 1);
by (subgoal_tac "({u} Un c): super S c" 1);
by (Asm_full_simp_tac 1);
by (rewrite_tac [super_def,psubset_def]);
by Safe_tac;
by (fast_tac (claset() addEs [chain_extend]) 1);
by (subgoal_tac "u ~: c" 1);
by (blast_tac (claset() addEs [equalityE]) 1);
by (blast_tac (claset() addDs [chain_Union_upper]) 1);
qed "maxchain_Zorn";

Goal "ALL c: chain S. Union(c): S ==> \
\     EX y: S. ALL z: S. y <= z --> y = z";
by (cut_facts_tac [Hausdorff,maxchain_subset_chain] 1);
by (etac exE 1);
by (dtac subsetD 1 THEN assume_tac 1);
by (dtac bspec 1 THEN assume_tac 1);
by (res_inst_tac [("x","Union(c)")] bexI 1);
by (rtac ballI 1 THEN rtac impI 1);
by (blast_tac (claset() addSDs [maxchain_Zorn]) 1);
by (assume_tac 1);
qed "Zorn_Lemma";

(*-------------------------------------------------------------
             Alternative version of Zorn's Lemma
 --------------------------------------------------------------*)
Goal "ALL (c:: 'a set set): chain S. EX y : S. ALL x : c. x <= y ==> \
\     EX y : S. ALL x : S. (y :: 'a set) <= x --> y = x";
by (cut_facts_tac [Hausdorff,maxchain_subset_chain] 1);
by (EVERY1[etac exE, dtac subsetD, assume_tac]);
by (EVERY1[dtac bspec, assume_tac, etac bexE]);
by (res_inst_tac [("x","y")] bexI 1);
by (assume_tac 2);
by (EVERY1[rtac ballI, rtac impI, rtac ccontr]);
by (forw_inst_tac [("z","x")]  chain_extend 1);
by (assume_tac 1 THEN Blast_tac 1);
by (rewrite_tac [maxchain_def,super_def,psubset_def]);
by (Step_tac 1);
by (eres_inst_tac [("c","{x} Un c")] equalityCE 1);
by (Step_tac 1);
by (subgoal_tac "x ~: c" 1);
by (blast_tac (claset() addEs [equalityE]) 1);
by (Blast_tac 1);
qed "Zorn_Lemma2";

(** misc. lemmas **)

Goalw [chain_def] "[| c : chain S; x: c; y: c |] ==> x <= y | y <= x";
by (Blast_tac 1);
qed "chainD";

Goalw [chain_def] "!!(c :: 'a set set). c: chain S ==> c <= S";
by (Blast_tac 1);
qed "chainD2";

(* proved elsewhere? *) 
Goal "x : Union(c) ==> EX m:c. x:m";
by (Blast_tac 1);
qed "mem_UnionD";

