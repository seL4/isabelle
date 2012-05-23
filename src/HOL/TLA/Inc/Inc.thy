(*  Title:      HOL/TLA/Inc/Inc.thy
    Author:     Stephan Merz, University of Munich
*)

header {* Lamport's "increment" example *}

theory Inc
imports TLA
begin

(* program counter as an enumeration type *)
datatype pcount = a | b | g

axiomatization
  (* program variables *)
  x :: "nat stfun" and
  y :: "nat stfun" and
  sem :: "nat stfun" and
  pc1 :: "pcount stfun" and
  pc2 :: "pcount stfun" and

  (* names of actions and predicates *)
  M1 :: action and
  M2 :: action and
  N1 :: action and
  N2 :: action and
  alpha1 :: action and
  alpha2 :: action and
  beta1 :: action and
  beta2 :: action and
  gamma1 :: action and
  gamma2 :: action and
  InitPhi :: stpred and
  InitPsi :: stpred and
  PsiInv :: stpred and
  PsiInv1 :: stpred and
  PsiInv2 :: stpred and
  PsiInv3 :: stpred and

  (* temporal formulas *)
  Phi :: temporal and
  Psi :: temporal
where
  (* the "base" variables, required to compute enabledness predicates *)
  Inc_base:      "basevars (x, y, sem, pc1, pc2)" and

  (* definitions for high-level program *)
  InitPhi_def:   "InitPhi == PRED x = # 0 & y = # 0" and
  M1_def:        "M1      == ACT  x$ = Suc<$x> & y$ = $y" and
  M2_def:        "M2      == ACT  y$ = Suc<$y> & x$ = $x" and
  Phi_def:       "Phi     == TEMP Init InitPhi & [][M1 | M2]_(x,y)
                                 & WF(M1)_(x,y) & WF(M2)_(x,y)" and

  (* definitions for low-level program *)
  InitPsi_def:   "InitPsi == PRED pc1 = #a & pc2 = #a
                                 & x = # 0 & y = # 0 & sem = # 1" and
  alpha1_def:    "alpha1  == ACT  $pc1 = #a & pc1$ = #b & $sem = Suc<sem$>
                                 & unchanged(x,y,pc2)" and
  alpha2_def:    "alpha2  == ACT  $pc2 = #a & pc2$ = #b & $sem = Suc<sem$>
                                 & unchanged(x,y,pc1)" and
  beta1_def:     "beta1   == ACT  $pc1 = #b & pc1$ = #g & x$ = Suc<$x>
                                 & unchanged(y,sem,pc2)" and
  beta2_def:     "beta2   == ACT  $pc2 = #b & pc2$ = #g & y$ = Suc<$y>
                                 & unchanged(x,sem,pc1)" and
  gamma1_def:    "gamma1  == ACT  $pc1 = #g & pc1$ = #a & sem$ = Suc<$sem>
                                 & unchanged(x,y,pc2)" and
  gamma2_def:    "gamma2  == ACT  $pc2 = #g & pc2$ = #a & sem$ = Suc<$sem>
                                 & unchanged(x,y,pc1)" and
  N1_def:        "N1      == ACT  (alpha1 | beta1 | gamma1)" and
  N2_def:        "N2      == ACT  (alpha2 | beta2 | gamma2)" and
  Psi_def:       "Psi     == TEMP Init InitPsi
                               & [][N1 | N2]_(x,y,sem,pc1,pc2)
                               & SF(N1)_(x,y,sem,pc1,pc2)
                               & SF(N2)_(x,y,sem,pc1,pc2)" and

  PsiInv1_def:  "PsiInv1  == PRED sem = # 1 & pc1 = #a & pc2 = #a" and
  PsiInv2_def:  "PsiInv2  == PRED sem = # 0 & pc1 = #a & (pc2 = #b | pc2 = #g)" and
  PsiInv3_def:  "PsiInv3  == PRED sem = # 0 & pc2 = #a & (pc1 = #b | pc1 = #g)" and
  PsiInv_def:   "PsiInv   == PRED (PsiInv1 | PsiInv2 | PsiInv3)"


lemmas PsiInv_defs = PsiInv_def PsiInv1_def PsiInv2_def PsiInv3_def
lemmas Psi_defs = Psi_def InitPsi_def N1_def N2_def alpha1_def alpha2_def
  beta1_def beta2_def gamma1_def gamma2_def


(*** Invariant proof for Psi: "manual" proof proves individual lemmas ***)

lemma PsiInv_Init: "|- InitPsi --> PsiInv"
  by (auto simp: InitPsi_def PsiInv_defs)

lemma PsiInv_alpha1: "|- alpha1 & $PsiInv --> PsiInv$"
  by (auto simp: alpha1_def PsiInv_defs)

lemma PsiInv_alpha2: "|- alpha2 & $PsiInv --> PsiInv$"
  by (auto simp: alpha2_def PsiInv_defs)

lemma PsiInv_beta1: "|- beta1 & $PsiInv --> PsiInv$"
  by (auto simp: beta1_def PsiInv_defs)

lemma PsiInv_beta2: "|- beta2 & $PsiInv --> PsiInv$"
  by (auto simp: beta2_def PsiInv_defs)

lemma PsiInv_gamma1: "|- gamma1 & $PsiInv --> PsiInv$"
  by (auto simp: gamma1_def PsiInv_defs)

lemma PsiInv_gamma2: "|- gamma2 & $PsiInv --> PsiInv$"
  by (auto simp: gamma2_def PsiInv_defs)

lemma PsiInv_stutter: "|- unchanged (x,y,sem,pc1,pc2) & $PsiInv --> PsiInv$"
  by (auto simp: PsiInv_defs)

lemma PsiInv: "|- Psi --> []PsiInv"
  apply (invariant simp: Psi_def)
   apply (force simp: PsiInv_Init [try_rewrite] Init_def)
  apply (auto intro: PsiInv_alpha1 [try_rewrite] PsiInv_alpha2 [try_rewrite]
    PsiInv_beta1 [try_rewrite] PsiInv_beta2 [try_rewrite] PsiInv_gamma1 [try_rewrite]
    PsiInv_gamma2 [try_rewrite] PsiInv_stutter [try_rewrite]
    simp add: square_def N1_def N2_def)
  done

(* Automatic proof works too, but it make take a while on a slow machine.
   More realistic examples require user guidance anyway.
*)

lemma "|- Psi --> []PsiInv"
  by (auto_invariant simp: PsiInv_defs Psi_defs)


(**** Step simulation ****)

lemma Init_sim: "|- Psi --> Init InitPhi"
  by (auto simp: InitPhi_def Psi_def InitPsi_def Init_def)

lemma Step_sim: "|- Psi --> [][M1 | M2]_(x,y)"
  by (auto simp: square_def M1_def M2_def Psi_defs elim!: STL4E [temp_use])


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

lemma Stuck_at_b: "|- [][(N1 | N2) & ~ beta1]_(x,y,sem,pc1,pc2) --> stable(pc1 = #b)"
  by (auto elim!: Stable squareE simp: Psi_defs)

lemma N1_enabled_at_g: "|- pc1 = #g --> Enabled (<N1>_(x,y,sem,pc1,pc2))"
  apply clarsimp
  apply (rule_tac F = gamma1 in enabled_mono)
   apply (enabled Inc_base)
  apply (force simp: gamma1_def)
  apply (force simp: angle_def gamma1_def N1_def)
  done

lemma g1_leadsto_a1:
  "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N1)_(x,y,sem,pc1,pc2) & []#True  
    --> (pc1 = #g ~> pc1 = #a)"
  apply (rule SF1)
    apply (tactic
      {* action_simp_tac (@{simpset} addsimps @{thms Psi_defs}) [] [@{thm squareE}] 1 *})
   apply (tactic
      {* action_simp_tac (@{simpset} addsimps @{thm angle_def} :: @{thms Psi_defs}) [] [] 1 *})
  (* reduce |- []A --> <>Enabled B  to  |- A --> Enabled B *)
  apply (auto intro!: InitDmd_gen [temp_use] N1_enabled_at_g [temp_use]
    dest!: STL2_gen [temp_use] simp: Init_def)
  done

(* symmetrical for N2, and similar for beta2 *)
lemma N2_enabled_at_g: "|- pc2 = #g --> Enabled (<N2>_(x,y,sem,pc1,pc2))"
  apply clarsimp
  apply (rule_tac F = gamma2 in enabled_mono)
  apply (enabled Inc_base)
   apply (force simp: gamma2_def)
  apply (force simp: angle_def gamma2_def N2_def)
  done

lemma g2_leadsto_a2:
  "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N2)_(x,y,sem,pc1,pc2) & []#True  
    --> (pc2 = #g ~> pc2 = #a)"
  apply (rule SF1)
  apply (tactic {* action_simp_tac (@{simpset} addsimps @{thms Psi_defs}) [] [@{thm squareE}] 1 *})
  apply (tactic {* action_simp_tac (@{simpset} addsimps @{thm angle_def} :: @{thms Psi_defs})
    [] [] 1 *})
  apply (auto intro!: InitDmd_gen [temp_use] N2_enabled_at_g [temp_use]
    dest!: STL2_gen [temp_use] simp add: Init_def)
  done

lemma N2_enabled_at_b: "|- pc2 = #b --> Enabled (<N2>_(x,y,sem,pc1,pc2))"
  apply clarsimp
  apply (rule_tac F = beta2 in enabled_mono)
   apply (enabled Inc_base)
   apply (force simp: beta2_def)
  apply (force simp: angle_def beta2_def N2_def)
  done

lemma b2_leadsto_g2:
  "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N2)_(x,y,sem,pc1,pc2) & []#True  
    --> (pc2 = #b ~> pc2 = #g)"
  apply (rule SF1)
    apply (tactic
      {* action_simp_tac (@{simpset} addsimps @{thms Psi_defs}) [] [@{thm squareE}] 1 *})
   apply (tactic
     {* action_simp_tac (@{simpset} addsimps @{thm angle_def} :: @{thms Psi_defs}) [] [] 1 *})
  apply (auto intro!: InitDmd_gen [temp_use] N2_enabled_at_b [temp_use]
    dest!: STL2_gen [temp_use] simp: Init_def)
  done

(* Combine above lemmas: the second component will eventually reach pc2 = a *)
lemma N2_leadsto_a:
  "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N2)_(x,y,sem,pc1,pc2) & []#True  
    --> (pc2 = #a | pc2 = #b | pc2 = #g ~> pc2 = #a)"
  apply (auto intro!: LatticeDisjunctionIntro [temp_use])
    apply (rule LatticeReflexivity [temp_use])
   apply (rule LatticeTransitivity [temp_use])
  apply (auto intro!: b2_leadsto_g2 [temp_use] g2_leadsto_a2 [temp_use])
  done

(* Get rid of disjunction on the left-hand side of ~> above. *)
lemma N2_live:
  "|- [][(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2) & SF(N2)_(x,y,sem,pc1,pc2)  
    --> <>(pc2 = #a)"
  apply (auto simp: Init_defs intro!: N2_leadsto_a [temp_use, THEN [2] leadsto_init [temp_use]])
  apply (case_tac "pc2 (st1 sigma)")
    apply auto
  done

(* Now prove that the first component will eventually reach pc1 = b from pc1 = a *)

lemma N1_enabled_at_both_a:
  "|- pc2 = #a & (PsiInv & pc1 = #a) --> Enabled (<N1>_(x,y,sem,pc1,pc2))"
  apply clarsimp
  apply (rule_tac F = alpha1 in enabled_mono)
  apply (enabled Inc_base)
   apply (force simp: alpha1_def PsiInv_defs)
  apply (force simp: angle_def alpha1_def N1_def)
  done

lemma a1_leadsto_b1:
  "|- []($PsiInv & [(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2))       
         & SF(N1)_(x,y,sem,pc1,pc2) & [] SF(N2)_(x,y,sem,pc1,pc2)   
         --> (pc1 = #a ~> pc1 = #b)"
  apply (rule SF1)
  apply (tactic {* action_simp_tac (@{simpset} addsimps @{thms Psi_defs}) [] [@{thm squareE}] 1 *})
  apply (tactic
    {* action_simp_tac (@{simpset} addsimps (@{thm angle_def} :: @{thms Psi_defs})) [] [] 1 *})
  apply (clarsimp intro!: N1_enabled_at_both_a [THEN DmdImpl [temp_use]])
  apply (auto intro!: BoxDmd2_simple [temp_use] N2_live [temp_use]
    simp: split_box_conj more_temp_simps)
  done

(* Combine the leadsto properties for N1: it will arrive at pc1 = b *)

lemma N1_leadsto_b: "|- []($PsiInv & [(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2))              
         & SF(N1)_(x,y,sem,pc1,pc2) & [] SF(N2)_(x,y,sem,pc1,pc2)   
         --> (pc1 = #b | pc1 = #g | pc1 = #a ~> pc1 = #b)"
  apply (auto intro!: LatticeDisjunctionIntro [temp_use])
    apply (rule LatticeReflexivity [temp_use])
   apply (rule LatticeTransitivity [temp_use])
    apply (auto intro!: a1_leadsto_b1 [temp_use] g1_leadsto_a1 [temp_use]
      simp: split_box_conj)
  done

lemma N1_live: "|- []($PsiInv & [(N1 | N2) & ~beta1]_(x,y,sem,pc1,pc2))              
         & SF(N1)_(x,y,sem,pc1,pc2) & [] SF(N2)_(x,y,sem,pc1,pc2)   
         --> <>(pc1 = #b)"
  apply (auto simp: Init_defs intro!: N1_leadsto_b [temp_use, THEN [2] leadsto_init [temp_use]])
  apply (case_tac "pc1 (st1 sigma)")
    apply auto
  done

lemma N1_enabled_at_b: "|- pc1 = #b --> Enabled (<N1>_(x,y,sem,pc1,pc2))"
  apply clarsimp
  apply (rule_tac F = beta1 in enabled_mono)
   apply (enabled Inc_base)
   apply (force simp: beta1_def)
  apply (force simp: angle_def beta1_def N1_def)
  done

(* Now assemble the bits and pieces to prove that Psi is fair. *)

lemma Fair_M1_lemma: "|- []($PsiInv & [(N1 | N2)]_(x,y,sem,pc1,pc2))    
         & SF(N1)_(x,y,sem,pc1,pc2) & []SF(N2)_(x,y,sem,pc1,pc2)   
         --> SF(M1)_(x,y)"
  apply (rule_tac B = beta1 and P = "PRED pc1 = #b" in SF2)
   (* action premises *)
     apply (force simp: angle_def M1_def beta1_def)
  apply (force simp: angle_def Psi_defs)
  apply (force elim!: N1_enabled_at_b [temp_use])
    (* temporal premise: use previous lemmas and simple TL *)
  apply (force intro!: DmdStable [temp_use] N1_live [temp_use] Stuck_at_b [temp_use]
    elim: STL4E [temp_use] simp: square_def)
  done

lemma Fair_M1: "|- Psi --> WF(M1)_(x,y)"
  by (auto intro!: SFImplWF [temp_use] Fair_M1_lemma [temp_use] PsiInv [temp_use]
    simp: Psi_def split_box_conj [temp_use] more_temp_simps)

end
