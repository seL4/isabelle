(* 
    File:	 TLA/ex/inc/Inc.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

Proofs for the "increment" example from SRC79.
*)

val PsiInv_defs = [PsiInv_def,PsiInv1_def,PsiInv2_def,PsiInv3_def];
val Psi_defs = [Psi_def,InitPsi_def,N1_def,N2_def,alpha1_def,alpha2_def,
                beta1_def,beta2_def,gamma1_def,gamma2_def];

val Inc_css = (claset(), simpset());

(*** Invariant proof for Psi: "manual" proof proves individual lemmas ***)

Goal "|- InitPsi --> PsiInv";
by (auto_tac (Inc_css addsimps2 InitPsi_def::PsiInv_defs));
qed "PsiInv_Init";

Goal "|- alpha1 & $PsiInv --> PsiInv$";
by (auto_tac (Inc_css addsimps2 alpha1_def::PsiInv_defs));
qed "PsiInv_alpha1";

Goal "|- alpha2 & $PsiInv --> PsiInv$";
by (auto_tac (Inc_css addsimps2 alpha2_def::PsiInv_defs));
qed "PsiInv_alpha2";

Goal "|- beta1 & $PsiInv --> PsiInv$";
by (auto_tac (Inc_css addsimps2 beta1_def::PsiInv_defs));
qed "PsiInv_beta1";

Goal "|- beta2 & $PsiInv --> PsiInv$";
by (auto_tac (Inc_css addsimps2 beta2_def::PsiInv_defs));
qed "PsiInv_beta2";

Goal "|- gamma1 & $PsiInv --> PsiInv$";
by (auto_tac (Inc_css addsimps2 gamma1_def::PsiInv_defs));
qed "PsiInv_gamma1";

Goal "|- gamma2 & $PsiInv --> PsiInv$";
by (auto_tac (Inc_css addsimps2 gamma2_def::PsiInv_defs));
qed "PsiInv_gamma2";

Goal "|- unchanged (x,y,sem,pc1,pc2) & $PsiInv --> PsiInv$";
by (auto_tac (Inc_css addsimps2 PsiInv_defs));
qed "PsiInv_stutter";

Goal "|- Psi --> []PsiInv";
by (inv_tac (Inc_css addsimps2 [Psi_def]) 1);
 by (force_tac (Inc_css addsimps2 [PsiInv_Init, Init_def]) 1);
by (auto_tac (Inc_css
              addIs2 [PsiInv_alpha1,PsiInv_alpha2,PsiInv_beta1,
                      PsiInv_beta2,PsiInv_gamma1,PsiInv_gamma2,PsiInv_stutter]
              addsimps2 [square_def,N1_def, N2_def]));
qed "PsiInv";

(* Automatic proof works too, but it make take a while on a slow machine.
   More realistic examples require user guidance anyway.

Goal "|- Psi --> []PsiInv";
by (auto_inv_tac (simpset() addsimps PsiInv_defs @ Psi_defs) 1);

*)

(**** Step simulation ****)

Goal "|- Psi --> Init InitPhi";
by (auto_tac (Inc_css addsimps2 [InitPhi_def,Psi_def,InitPsi_def,Init_def]));
qed "Init_sim";

Goal "|- Psi --> [][M1 | M2]_(x,y)";
by (auto_tac (Inc_css addsimps2 [square_def,M1_def,M2_def] @ Psi_defs
                      addSEs2 [STL4E]));
qed "Step_sim";

(**** Proof of fairness ****)

(*
   The goal is to prove Fair_M1 far below, which asserts 
         |- Psi --> WF(M1)_(x,y)
   (the other fairness condition is symmetrical).

   The strategy is to use WF2 (with beta1 as the helpful action). Proving its
   temporal premise needs two auxiliary lemmas:
   1. Stuck_at_b: control can only proceed at pc1 = b by executing beta1
   2. N1_live: the first component will eventually reach b

   Lemma 1 is easy, lemma 2 relies on the invariant, the strong fairness
   of the semaphore, and needs auxiliary lemmas that ensure that the second
   component will eventually release the semaphore. Most of the proofs of
   the auxiliary lemmas are very similar.
*)

Goal "|- [][(N1 | N2) & ~ beta1]_(x,y,sem,pc1,pc2) --> stable(pc1 = #b)";
by (auto_tac (Inc_css addSEs2 [Stable,squareE] addsimps2 Psi_defs));
qed "Stuck_at_b";

Goal "|- pc1 = #g --> Enabled (<N1>_(x,y,sem,pc1,pc2))";
by (Clarsimp_tac 1);
by (res_inst_tac [("F","gamma1")] enabled_mono 1);
by (enabled_tac Inc_base 1);
 by (force_tac (Inc_css addsimps2 [gamma1_def]) 1);
by (force_tac (Inc_css addsimps2 [angle_def,gamma1_def,N1_def]) 1);
qed "N1_enabled_at_g";

Goal "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N1)_(x,y,sem,pc1,pc2) & []#True \
\        --> (pc1 = #g ~> pc1 = #a)";
by (rtac SF1 1);
by (action_simp_tac (simpset() addsimps Psi_defs) [] [squareE] 1);
by (action_simp_tac (simpset() addsimps angle_def::Psi_defs) [] [] 1);
(* reduce |- []A --> <>Enabled B  to  |- A --> Enabled B *)
by (auto_tac (Inc_css addSIs2 [InitDmd_gen, N1_enabled_at_g]
	              addSDs2 [STL2_gen]
                      addsimps2 [Init_def]));
qed "g1_leadsto_a1";

(* symmetrical for N2, and similar for beta2 *)
Goal "|- pc2 = #g --> Enabled (<N2>_(x,y,sem,pc1,pc2))";
by (Clarsimp_tac 1);
by (res_inst_tac [("F","gamma2")] enabled_mono 1);
by (enabled_tac Inc_base 1);
 by (force_tac (Inc_css addsimps2 [gamma2_def]) 1);
by (force_tac (Inc_css addsimps2 [angle_def,gamma2_def,N2_def]) 1);
qed "N2_enabled_at_g";

Goal "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N2)_(x,y,sem,pc1,pc2) & []#True \
\        --> (pc2 = #g ~> pc2 = #a)";
by (rtac SF1 1);
by (action_simp_tac (simpset() addsimps Psi_defs) [] [squareE] 1);
by (action_simp_tac (simpset() addsimps angle_def::Psi_defs) [] [] 1);
by (auto_tac (Inc_css addSIs2 [InitDmd_gen, N2_enabled_at_g]
	              addSDs2 [STL2_gen]
                      addsimps2 [Init_def]));
qed "g2_leadsto_a2";

Goal "|- pc2 = #b --> Enabled (<N2>_(x,y,sem,pc1,pc2))";
by (Clarsimp_tac 1);
by (res_inst_tac [("F","beta2")] enabled_mono 1);
by (enabled_tac Inc_base 1);
 by (force_tac (Inc_css addsimps2 [beta2_def]) 1);
by (force_tac (Inc_css addsimps2 [angle_def,beta2_def,N2_def]) 1);
qed "N2_enabled_at_b";

Goal "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N2)_(x,y,sem,pc1,pc2) & []#True \
\        --> (pc2 = #b ~> pc2 = #g)";
by (rtac SF1 1);
by (action_simp_tac (simpset() addsimps Psi_defs) [] [squareE] 1);
by (action_simp_tac (simpset() addsimps angle_def::Psi_defs) [] [] 1);
by (auto_tac (Inc_css addSIs2 [InitDmd_gen, N2_enabled_at_b]
                      addSDs2 [STL2_gen]
                      addsimps2 [Init_def]));
qed "b2_leadsto_g2";

(* Combine above lemmas: the second component will eventually reach pc2 = a *)
Goal "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N2)_(x,y,sem,pc1,pc2) & []#True \
\        --> (pc2 = #a | pc2 = #b | pc2 = #g ~> pc2 = #a)";
by (auto_tac (Inc_css addSIs2 [LatticeDisjunctionIntro]));
by (rtac (temp_use LatticeReflexivity) 1);
by (rtac (temp_use LatticeTransitivity) 1);
by (auto_tac (Inc_css addSIs2 [b2_leadsto_g2,g2_leadsto_a2]));
qed "N2_leadsto_a";

(* Get rid of disjunction on the left-hand side of ~> above. *)
Goal "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N2)_(x,y,sem,pc1,pc2) \
\        --> <>(pc2 = #a)";
by (auto_tac (Inc_css addsimps2 Init_defs
                      addSIs2 [(temp_use N2_leadsto_a) 
                               RSN(2, (temp_use leadsto_init))]));
by (case_tac "pc2 (st1 sigma)" 1);
by Auto_tac;
qed "N2_live";

(* Now prove that the first component will eventually reach pc1 = b from pc1 = a *)

Goal "|- pc2 = #a & (PsiInv & pc1 = #a) --> Enabled (<N1>_(x,y,sem,pc1,pc2))";
by (Clarsimp_tac 1);
by (res_inst_tac [("F","alpha1")] enabled_mono 1);
by (enabled_tac Inc_base 1);
 by (force_tac (Inc_css addsimps2 (alpha1_def::PsiInv_defs)) 1);
by (force_tac (Inc_css addsimps2 [angle_def,alpha1_def,N1_def]) 1);
qed "N1_enabled_at_both_a";

Goal "|- []($PsiInv & [(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2))      \
\        & SF(N1)_(x,y,sem,pc1,pc2) & [] SF(N2)_(x,y,sem,pc1,pc2)  \
\        --> (pc1 = #a ~> pc1 = #b)";
by (rtac SF1 1);
by (action_simp_tac (simpset() addsimps Psi_defs) [] [squareE] 1);
by (action_simp_tac (simpset() addsimps angle_def::Psi_defs) [] [] 1);
by (clarsimp_tac (Inc_css addSIs2 [N1_enabled_at_both_a RS (temp_use DmdImpl)]) 1);
by (auto_tac (Inc_css addSIs2 [BoxDmd2_simple, N2_live]
	              addsimps2 split_box_conj::more_temp_simps));
qed "a1_leadsto_b1";

(* Combine the leadsto properties for N1: it will arrive at pc1 = b *)

Goal "|- []($PsiInv & [(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2))             \
\        & SF(N1)_(x,y,sem,pc1,pc2) & [] SF(N2)_(x,y,sem,pc1,pc2)  \
\        --> (pc1 = #b | pc1 = #g | pc1 = #a ~> pc1 = #b)";
by (auto_tac (Inc_css addSIs2 [LatticeDisjunctionIntro]));
by (rtac (temp_use LatticeReflexivity) 1);
by (rtac (temp_use LatticeTransitivity) 1);
by (auto_tac (Inc_css addSIs2 [a1_leadsto_b1,g1_leadsto_a1]
	              addsimps2 [split_box_conj]));
qed "N1_leadsto_b";

Goal "|- []($PsiInv & [(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2))             \
\        & SF(N1)_(x,y,sem,pc1,pc2) & [] SF(N2)_(x,y,sem,pc1,pc2)  \
\        --> <>(pc1 = #b)";
by (auto_tac (Inc_css addsimps2 Init_defs
                      addSIs2 [(temp_use N1_leadsto_b) 
                               RSN(2, temp_use leadsto_init)]));
by (case_tac "pc1 (st1 sigma)" 1);
by Auto_tac;
qed "N1_live";

Goal "|- pc1 = #b --> Enabled (<N1>_(x,y,sem,pc1,pc2))";
by (Clarsimp_tac 1);
by (res_inst_tac [("F","beta1")] enabled_mono 1);
by (enabled_tac Inc_base 1);
 by (force_tac (Inc_css addsimps2 [beta1_def]) 1);
by (force_tac (Inc_css addsimps2 [angle_def,beta1_def,N1_def]) 1);
qed "N1_enabled_at_b";

(* Now assemble the bits and pieces to prove that Psi is fair. *)

Goal "|- []($PsiInv & [(N1 | N2)]_(x,y,sem,pc1,pc2))   \
\        & SF(N1)_(x,y,sem,pc1,pc2) & []SF(N2)_(x,y,sem,pc1,pc2)  \
\        --> SF(M1)_(x,y)";
by (res_inst_tac [("B","beta1"),("P","PRED pc1 = #b")] SF2 1);
   (* action premises *)
by (force_tac (Inc_css addsimps2 [angle_def,M1_def,beta1_def]) 1);
by (force_tac (Inc_css addsimps2 angle_def::Psi_defs) 1);
by (force_tac (Inc_css addSEs2 [N1_enabled_at_b]) 1);
   (* temporal premise: use previous lemmas and simple TL *)
by (force_tac (Inc_css addSIs2 [DmdStable, N1_live,Stuck_at_b] 
                       addEs2 [STL4E] addsimps2 [square_def]) 1);
qed "Fair_M1_lemma";

Goal "|- Psi --> WF(M1)_(x,y)";
by (auto_tac (Inc_css addSIs2 [SFImplWF, Fair_M1_lemma, PsiInv]
		      addsimps2 [Psi_def,split_box_conj]@more_temp_simps));
qed "Fair_M1";
