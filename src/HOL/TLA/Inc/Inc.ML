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

qed_goal "PsiInv_Init" Inc.thy "|- InitPsi --> PsiInv"
 (fn _ => [ auto_tac (Inc_css addsimps2 InitPsi_def::PsiInv_defs) ]);

qed_goal "PsiInv_alpha1" Inc.thy "|- alpha1 & $PsiInv --> PsiInv`"
  (fn _ => [ auto_tac (Inc_css addsimps2 alpha1_def::PsiInv_defs) ]);

qed_goal "PsiInv_alpha2" Inc.thy "|- alpha2 & $PsiInv --> PsiInv`"
  (fn _ => [ auto_tac (Inc_css addsimps2 alpha2_def::PsiInv_defs) ]);

qed_goal "PsiInv_beta1" Inc.thy "|- beta1 & $PsiInv --> PsiInv`"
  (fn _ => [ auto_tac (Inc_css addsimps2 beta1_def::PsiInv_defs) ]);

qed_goal "PsiInv_beta2" Inc.thy "|- beta2 & $PsiInv --> PsiInv`"
  (fn _ => [ auto_tac (Inc_css addsimps2 beta2_def::PsiInv_defs) ]);

qed_goal "PsiInv_gamma1" Inc.thy "|- gamma1 & $PsiInv --> PsiInv`"
  (fn _ => [ auto_tac (Inc_css addsimps2 gamma1_def::PsiInv_defs) ]);

qed_goal "PsiInv_gamma2" Inc.thy "|- gamma2 & $PsiInv --> PsiInv`"
  (fn _ => [ auto_tac (Inc_css addsimps2 gamma2_def::PsiInv_defs) ]);

qed_goal "PsiInv_stutter" Inc.thy "|- unchanged (x,y,sem,pc1,pc2) & $PsiInv --> PsiInv`"
  (fn _ => [ auto_tac (Inc_css addsimps2 PsiInv_defs) ]);

qed_goal "PsiInv" Inc.thy "|- Psi --> []PsiInv" (K [
	    inv_tac (Inc_css addsimps2 [Psi_def]) 1,
	    force_tac (Inc_css addsimps2 [PsiInv_Init, Init_def]) 1,
	    auto_tac (Inc_css addIs2
		        [PsiInv_alpha1,PsiInv_alpha2,PsiInv_beta1,
			 PsiInv_beta2,PsiInv_gamma1,PsiInv_gamma2,PsiInv_stutter]
                        addsimps2 [square_def,N1_def, N2_def]) ]);

(* Automatic proof works too, but it make take a while on a slow machine.
   More realistic examples require user guidance anyway.

Goal "|- Psi --> []PsiInv";
by (auto_inv_tac (simpset() addsimps PsiInv_defs @ Psi_defs) 1);

*)

(**** Step simulation ****)

qed_goal "Init_sim" Inc.thy "|- Psi --> Init InitPhi"
  (fn _ => [ auto_tac (Inc_css addsimps2 [InitPhi_def,Psi_def,InitPsi_def,Init_def]) ]);

qed_goal "Step_sim" Inc.thy "|- Psi --> [][M1 | M2]_(x,y)"
  (fn _ => [auto_tac (Inc_css addsimps2 [square_def,M1_def,M2_def] @ Psi_defs
                              addSEs2 [STL4E])
           ]);

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

qed_goal "Stuck_at_b" Inc.thy
  "|- [][(N1 | N2) & ~ beta1]_(x,y,sem,pc1,pc2) --> stable(pc1 = #b)"
  (fn _ => [ auto_tac (Inc_css addSEs2 [Stable,squareE] addsimps2 Psi_defs) ]);

qed_goal "N1_enabled_at_g" Inc.thy
  "|- pc1 = #g --> Enabled (<N1>_(x,y,sem,pc1,pc2))"
  (fn _ => [Clarsimp_tac 1,
	    res_inst_tac [("F","gamma1")] enabled_mono 1,
	    enabled_tac Inc_base 1,
            force_tac (Inc_css addsimps2 [gamma1_def]) 1,
	    force_tac (Inc_css addsimps2 [angle_def,gamma1_def,N1_def]) 1
	   ]);

qed_goal "g1_leadsto_a1" Inc.thy
  "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N1)_(x,y,sem,pc1,pc2) & []#True \
\     --> (pc1 = #g ~> pc1 = #a)"
  (fn _ => [rtac SF1 1,
	    action_simp_tac (simpset() addsimps Psi_defs) [] [squareE] 1,
	    action_simp_tac (simpset() addsimps angle_def::Psi_defs) [] [] 1,
	    (* reduce |- []A --> <>Enabled B  to  |- A --> Enabled B *)
	    auto_tac (Inc_css addSIs2 [InitDmd_gen, N1_enabled_at_g]
		              addSDs2 [STL2_gen]
		              addsimps2 [Init_def])
	   ]);

(* symmetrical for N2, and similar for beta2 *)
qed_goal "N2_enabled_at_g" Inc.thy
  "|- pc2 = #g --> Enabled (<N2>_(x,y,sem,pc1,pc2))"
  (fn _ => [Clarsimp_tac 1,
	    res_inst_tac [("F","gamma2")] enabled_mono 1,
	    enabled_tac Inc_base 1,
            force_tac (Inc_css addsimps2 [gamma2_def]) 1,
	    force_tac (Inc_css addsimps2 [angle_def,gamma2_def,N2_def]) 1
	   ]);

qed_goal "g2_leadsto_a2" Inc.thy
  "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N2)_(x,y,sem,pc1,pc2) & []#True \
\     --> (pc2 = #g ~> pc2 = #a)"
  (fn _ => [rtac SF1 1,
	    action_simp_tac (simpset() addsimps Psi_defs) [] [squareE] 1,
	    action_simp_tac (simpset() addsimps angle_def::Psi_defs) [] [] 1,
	    auto_tac (Inc_css addSIs2 [InitDmd_gen, N2_enabled_at_g]
		              addSDs2 [STL2_gen]
		              addsimps2 [Init_def])
	   ]);

qed_goal "N2_enabled_at_b" Inc.thy
  "|- pc2 = #b --> Enabled (<N2>_(x,y,sem,pc1,pc2))"
  (fn _ => [Clarsimp_tac 1,
	    res_inst_tac [("F","beta2")] enabled_mono 1,
	    enabled_tac Inc_base 1,
            force_tac (Inc_css addsimps2 [beta2_def]) 1,
	    force_tac (Inc_css addsimps2 [angle_def,beta2_def,N2_def]) 1
	   ]);

qed_goal "b2_leadsto_g2" Inc.thy
  "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N2)_(x,y,sem,pc1,pc2) & []#True \
\     --> (pc2 = #b ~> pc2 = #g)"
  (fn _ => [rtac SF1 1,
	    action_simp_tac (simpset() addsimps Psi_defs) [] [squareE] 1,
	    action_simp_tac (simpset() addsimps angle_def::Psi_defs) [] [] 1,
	    auto_tac (Inc_css addSIs2 [InitDmd_gen, N2_enabled_at_b]
		              addSDs2 [STL2_gen]
		              addsimps2 [Init_def])
	   ]);

(* Combine above lemmas: the second component will eventually reach pc2 = a *)
qed_goal "N2_leadsto_a" Inc.thy
  "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N2)_(x,y,sem,pc1,pc2) & []#True \
\     --> (pc2 = #a | pc2 = #b | pc2 = #g ~> pc2 = #a)"
  (fn _ => [auto_tac (Inc_css addSIs2 [LatticeDisjunctionIntro]),
	    rtac (temp_use LatticeReflexivity) 1,
	    rtac (temp_use LatticeTransitivity) 1,
	    auto_tac (Inc_css addSIs2 [b2_leadsto_g2,g2_leadsto_a2])
	   ]);

(* Get rid of complete disjunction on the left-hand side of ~> above. *)
qed_goal "N2_live" Inc.thy
  "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N2)_(x,y,sem,pc1,pc2) \
\     --> <>(pc2 = #a)"
  (fn _ => [auto_tac (Inc_css addsimps2 Init_defs
                              addSIs2 [(temp_use N2_leadsto_a) 
                                       RSN(2, (temp_use leadsto_init))]),
	    exhaust_tac "pc2 (st1 sigma)" 1,
	    Auto_tac
	   ]);

(* Now prove that the first component will eventually reach pc1 = b from pc1 = a *)

qed_goal "N1_enabled_at_both_a" Inc.thy
  "|- pc2 = #a & (PsiInv & pc1 = #a) --> Enabled (<N1>_(x,y,sem,pc1,pc2))"
  (fn _ => [Clarsimp_tac 1,
	    res_inst_tac [("F","alpha1")] enabled_mono 1,
	    enabled_tac Inc_base 1,
            force_tac (Inc_css addsimps2 (alpha1_def::PsiInv_defs)) 1,
	    force_tac (Inc_css addsimps2 [angle_def,alpha1_def,N1_def]) 1
	   ]);

qed_goal "a1_leadsto_b1" Inc.thy
  "|- []($PsiInv & [(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2))            \
\           & SF(N1)_(x,y,sem,pc1,pc2) & [] SF(N2)_(x,y,sem,pc1,pc2)  \
\     --> (pc1 = #a ~> pc1 = #b)"
  (fn _ => [rtac SF1 1,
            action_simp_tac (simpset() addsimps Psi_defs) [] [squareE] 1,
            action_simp_tac (simpset() addsimps angle_def::Psi_defs) [] [] 1,
	    clarsimp_tac (Inc_css addSIs2 [N1_enabled_at_both_a RS (temp_use DmdImpl)]) 1,
	    auto_tac (Inc_css addSIs2 [BoxDmd2_simple, N2_live]
		              addsimps2 split_box_conj::more_temp_simps)
	   ]);

(* Combine the leadsto properties for N1: it will arrive at pc1 = b *)

qed_goal "N1_leadsto_b" Inc.thy
  "|- []($PsiInv & [(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2))             \
\            & SF(N1)_(x,y,sem,pc1,pc2) & [] SF(N2)_(x,y,sem,pc1,pc2)  \
\     --> (pc1 = #b | pc1 = #g | pc1 = #a ~> pc1 = #b)"
  (fn _ => [auto_tac (Inc_css addSIs2 [LatticeDisjunctionIntro]),
	    rtac (temp_use LatticeReflexivity) 1,
	    rtac (temp_use LatticeTransitivity) 1,
	    auto_tac (Inc_css addSIs2 [a1_leadsto_b1,g1_leadsto_a1]
		              addsimps2 [split_box_conj])
	   ]);

qed_goal "N1_live" Inc.thy
  "|- []($PsiInv & [(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2))             \
\            & SF(N1)_(x,y,sem,pc1,pc2) & [] SF(N2)_(x,y,sem,pc1,pc2)  \
\     --> <>(pc1 = #b)"
  (fn _ => [auto_tac (Inc_css addsimps2 Init_defs
                              addSIs2 [(temp_use N1_leadsto_b) 
                                       RSN(2, temp_use leadsto_init)]),
	    exhaust_tac "pc1 (st1 sigma)" 1,
	    Auto_tac
	   ]);

qed_goal "N1_enabled_at_b" Inc.thy
  "|- pc1 = #b --> Enabled (<N1>_(x,y,sem,pc1,pc2))"
  (fn _ => [Clarsimp_tac 1,
	    res_inst_tac [("F","beta1")] enabled_mono 1,
	    enabled_tac Inc_base 1,
            force_tac (Inc_css addsimps2 [beta1_def]) 1,
	    force_tac (Inc_css addsimps2 [angle_def,beta1_def,N1_def]) 1
	   ]);

(* Now assemble the bits and pieces to prove that Psi is fair. *)

qed_goal "Fair_M1_lemma" Inc.thy
  "|- []($PsiInv & [(N1 | N2)]_(x,y,sem,pc1,pc2))   \
\     & SF(N1)_(x,y,sem,pc1,pc2) & []SF(N2)_(x,y,sem,pc1,pc2)  \
\     --> SF(M1)_(x,y)"
  (fn _ => [ res_inst_tac [("B","beta1"),("P","PRED pc1 = #b")] SF2 1,
               (* action premises *)
             force_tac (Inc_css addsimps2 [angle_def,M1_def,beta1_def]) 1,
             force_tac (Inc_css addsimps2 angle_def::Psi_defs) 1,
             force_tac (Inc_css addSEs2 [N1_enabled_at_b]) 1,
               (* temporal premise: use previous lemmas and simple TL *)
             force_tac (Inc_css addSIs2 [DmdStable, N1_live,Stuck_at_b] 
                                addEs2 [STL4E] addsimps2 [square_def]) 1
            ]);

qed_goal "Fair_M1" Inc.thy "|- Psi --> WF(M1)_(x,y)"
  (fn _ => [auto_tac (Inc_css addSIs2 [SFImplWF, Fair_M1_lemma, PsiInv]
		              addsimps2 [Psi_def,split_box_conj]@more_temp_simps)
	   ]);
