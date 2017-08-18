(*  Title:      HOL/TLA/Inc/Inc.thy
    Author:     Stephan Merz, University of Munich
*)

section \<open>Lamport's "increment" example\<close>

theory Inc
imports "HOL-TLA.TLA"
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
  InitPhi_def:   "InitPhi == PRED x = # 0 \<and> y = # 0" and
  M1_def:        "M1      == ACT  x$ = Suc<$x> \<and> y$ = $y" and
  M2_def:        "M2      == ACT  y$ = Suc<$y> \<and> x$ = $x" and
  Phi_def:       "Phi     == TEMP Init InitPhi \<and> \<box>[M1 \<or> M2]_(x,y)
                                 \<and> WF(M1)_(x,y) \<and> WF(M2)_(x,y)" and

  (* definitions for low-level program *)
  InitPsi_def:   "InitPsi == PRED pc1 = #a \<and> pc2 = #a
                                 \<and> x = # 0 \<and> y = # 0 \<and> sem = # 1" and
  alpha1_def:    "alpha1  == ACT  $pc1 = #a \<and> pc1$ = #b \<and> $sem = Suc<sem$>
                                 \<and> unchanged(x,y,pc2)" and
  alpha2_def:    "alpha2  == ACT  $pc2 = #a \<and> pc2$ = #b \<and> $sem = Suc<sem$>
                                 \<and> unchanged(x,y,pc1)" and
  beta1_def:     "beta1   == ACT  $pc1 = #b \<and> pc1$ = #g \<and> x$ = Suc<$x>
                                 \<and> unchanged(y,sem,pc2)" and
  beta2_def:     "beta2   == ACT  $pc2 = #b \<and> pc2$ = #g \<and> y$ = Suc<$y>
                                 \<and> unchanged(x,sem,pc1)" and
  gamma1_def:    "gamma1  == ACT  $pc1 = #g \<and> pc1$ = #a \<and> sem$ = Suc<$sem>
                                 \<and> unchanged(x,y,pc2)" and
  gamma2_def:    "gamma2  == ACT  $pc2 = #g \<and> pc2$ = #a \<and> sem$ = Suc<$sem>
                                 \<and> unchanged(x,y,pc1)" and
  N1_def:        "N1      == ACT  (alpha1 \<or> beta1 \<or> gamma1)" and
  N2_def:        "N2      == ACT  (alpha2 \<or> beta2 \<or> gamma2)" and
  Psi_def:       "Psi     == TEMP Init InitPsi
                               \<and> \<box>[N1 \<or> N2]_(x,y,sem,pc1,pc2)
                               \<and> SF(N1)_(x,y,sem,pc1,pc2)
                               \<and> SF(N2)_(x,y,sem,pc1,pc2)" and

  PsiInv1_def:  "PsiInv1  == PRED sem = # 1 \<and> pc1 = #a \<and> pc2 = #a" and
  PsiInv2_def:  "PsiInv2  == PRED sem = # 0 \<and> pc1 = #a \<and> (pc2 = #b \<or> pc2 = #g)" and
  PsiInv3_def:  "PsiInv3  == PRED sem = # 0 \<and> pc2 = #a \<and> (pc1 = #b \<or> pc1 = #g)" and
  PsiInv_def:   "PsiInv   == PRED (PsiInv1 \<or> PsiInv2 \<or> PsiInv3)"


lemmas PsiInv_defs = PsiInv_def PsiInv1_def PsiInv2_def PsiInv3_def
lemmas Psi_defs = Psi_def InitPsi_def N1_def N2_def alpha1_def alpha2_def
  beta1_def beta2_def gamma1_def gamma2_def


(*** Invariant proof for Psi: "manual" proof proves individual lemmas ***)

lemma PsiInv_Init: "\<turnstile> InitPsi \<longrightarrow> PsiInv"
  by (auto simp: InitPsi_def PsiInv_defs)

lemma PsiInv_alpha1: "\<turnstile> alpha1 \<and> $PsiInv \<longrightarrow> PsiInv$"
  by (auto simp: alpha1_def PsiInv_defs)

lemma PsiInv_alpha2: "\<turnstile> alpha2 \<and> $PsiInv \<longrightarrow> PsiInv$"
  by (auto simp: alpha2_def PsiInv_defs)

lemma PsiInv_beta1: "\<turnstile> beta1 \<and> $PsiInv \<longrightarrow> PsiInv$"
  by (auto simp: beta1_def PsiInv_defs)

lemma PsiInv_beta2: "\<turnstile> beta2 \<and> $PsiInv \<longrightarrow> PsiInv$"
  by (auto simp: beta2_def PsiInv_defs)

lemma PsiInv_gamma1: "\<turnstile> gamma1 \<and> $PsiInv \<longrightarrow> PsiInv$"
  by (auto simp: gamma1_def PsiInv_defs)

lemma PsiInv_gamma2: "\<turnstile> gamma2 \<and> $PsiInv \<longrightarrow> PsiInv$"
  by (auto simp: gamma2_def PsiInv_defs)

lemma PsiInv_stutter: "\<turnstile> unchanged (x,y,sem,pc1,pc2) \<and> $PsiInv \<longrightarrow> PsiInv$"
  by (auto simp: PsiInv_defs)

lemma PsiInv: "\<turnstile> Psi \<longrightarrow> \<box>PsiInv"
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

lemma "\<turnstile> Psi \<longrightarrow> \<box>PsiInv"
  by (auto_invariant simp: PsiInv_defs Psi_defs)


(**** Step simulation ****)

lemma Init_sim: "\<turnstile> Psi \<longrightarrow> Init InitPhi"
  by (auto simp: InitPhi_def Psi_def InitPsi_def Init_def)

lemma Step_sim: "\<turnstile> Psi \<longrightarrow> \<box>[M1 \<or> M2]_(x,y)"
  by (auto simp: square_def M1_def M2_def Psi_defs elim!: STL4E [temp_use])


(**** Proof of fairness ****)

(*
   The goal is to prove Fair_M1 far below, which asserts
         \<turnstile> Psi \<longrightarrow> WF(M1)_(x,y)
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

lemma Stuck_at_b: "\<turnstile> \<box>[(N1 \<or> N2) \<and> \<not> beta1]_(x,y,sem,pc1,pc2) \<longrightarrow> stable(pc1 = #b)"
  by (auto elim!: Stable squareE simp: Psi_defs)

lemma N1_enabled_at_g: "\<turnstile> pc1 = #g \<longrightarrow> Enabled (<N1>_(x,y,sem,pc1,pc2))"
  apply clarsimp
  apply (rule_tac F = gamma1 in enabled_mono)
   apply (enabled Inc_base)
  apply (force simp: gamma1_def)
  apply (force simp: angle_def gamma1_def N1_def)
  done

lemma g1_leadsto_a1:
  "\<turnstile> \<box>[(N1 \<or> N2) \<and> \<not>beta1]_(x,y,sem,pc1,pc2) \<and> SF(N1)_(x,y,sem,pc1,pc2) \<and> \<box>#True  
    \<longrightarrow> (pc1 = #g \<leadsto> pc1 = #a)"
  apply (rule SF1)
    apply (tactic
      \<open>action_simp_tac (@{context} addsimps @{thms Psi_defs}) [] [@{thm squareE}] 1\<close>)
   apply (tactic
      \<open>action_simp_tac (@{context} addsimps @{thm angle_def} :: @{thms Psi_defs}) [] [] 1\<close>)
  (* reduce \<turnstile> \<box>A \<longrightarrow> \<diamond>Enabled B  to  \<turnstile> A \<longrightarrow> Enabled B *)
  apply (auto intro!: InitDmd_gen [temp_use] N1_enabled_at_g [temp_use]
    dest!: STL2_gen [temp_use] simp: Init_def)
  done

(* symmetrical for N2, and similar for beta2 *)
lemma N2_enabled_at_g: "\<turnstile> pc2 = #g \<longrightarrow> Enabled (<N2>_(x,y,sem,pc1,pc2))"
  apply clarsimp
  apply (rule_tac F = gamma2 in enabled_mono)
  apply (enabled Inc_base)
   apply (force simp: gamma2_def)
  apply (force simp: angle_def gamma2_def N2_def)
  done

lemma g2_leadsto_a2:
  "\<turnstile> \<box>[(N1 \<or> N2) \<and> \<not>beta1]_(x,y,sem,pc1,pc2) \<and> SF(N2)_(x,y,sem,pc1,pc2) \<and> \<box>#True  
    \<longrightarrow> (pc2 = #g \<leadsto> pc2 = #a)"
  apply (rule SF1)
  apply (tactic \<open>action_simp_tac (@{context} addsimps @{thms Psi_defs}) [] [@{thm squareE}] 1\<close>)
  apply (tactic \<open>action_simp_tac (@{context} addsimps @{thm angle_def} :: @{thms Psi_defs})
    [] [] 1\<close>)
  apply (auto intro!: InitDmd_gen [temp_use] N2_enabled_at_g [temp_use]
    dest!: STL2_gen [temp_use] simp add: Init_def)
  done

lemma N2_enabled_at_b: "\<turnstile> pc2 = #b \<longrightarrow> Enabled (<N2>_(x,y,sem,pc1,pc2))"
  apply clarsimp
  apply (rule_tac F = beta2 in enabled_mono)
   apply (enabled Inc_base)
   apply (force simp: beta2_def)
  apply (force simp: angle_def beta2_def N2_def)
  done

lemma b2_leadsto_g2:
  "\<turnstile> \<box>[(N1 \<or> N2) \<and> \<not>beta1]_(x,y,sem,pc1,pc2) \<and> SF(N2)_(x,y,sem,pc1,pc2) \<and> \<box>#True  
    \<longrightarrow> (pc2 = #b \<leadsto> pc2 = #g)"
  apply (rule SF1)
    apply (tactic
      \<open>action_simp_tac (@{context} addsimps @{thms Psi_defs}) [] [@{thm squareE}] 1\<close>)
   apply (tactic
     \<open>action_simp_tac (@{context} addsimps @{thm angle_def} :: @{thms Psi_defs}) [] [] 1\<close>)
  apply (auto intro!: InitDmd_gen [temp_use] N2_enabled_at_b [temp_use]
    dest!: STL2_gen [temp_use] simp: Init_def)
  done

(* Combine above lemmas: the second component will eventually reach pc2 = a *)
lemma N2_leadsto_a:
  "\<turnstile> \<box>[(N1 \<or> N2) \<and> \<not>beta1]_(x,y,sem,pc1,pc2) \<and> SF(N2)_(x,y,sem,pc1,pc2) \<and> \<box>#True  
    \<longrightarrow> (pc2 = #a \<or> pc2 = #b \<or> pc2 = #g \<leadsto> pc2 = #a)"
  apply (auto intro!: LatticeDisjunctionIntro [temp_use])
    apply (rule LatticeReflexivity [temp_use])
   apply (rule LatticeTransitivity [temp_use])
  apply (auto intro!: b2_leadsto_g2 [temp_use] g2_leadsto_a2 [temp_use])
  done

(* Get rid of disjunction on the left-hand side of \<leadsto> above. *)
lemma N2_live:
  "\<turnstile> \<box>[(N1 \<or> N2) \<and> \<not>beta1]_(x,y,sem,pc1,pc2) \<and> SF(N2)_(x,y,sem,pc1,pc2)  
    \<longrightarrow> \<diamond>(pc2 = #a)"
  apply (auto simp: Init_defs intro!: N2_leadsto_a [temp_use, THEN [2] leadsto_init [temp_use]])
  apply (case_tac "pc2 (st1 sigma)")
    apply auto
  done

(* Now prove that the first component will eventually reach pc1 = b from pc1 = a *)

lemma N1_enabled_at_both_a:
  "\<turnstile> pc2 = #a \<and> (PsiInv \<and> pc1 = #a) \<longrightarrow> Enabled (<N1>_(x,y,sem,pc1,pc2))"
  apply clarsimp
  apply (rule_tac F = alpha1 in enabled_mono)
  apply (enabled Inc_base)
   apply (force simp: alpha1_def PsiInv_defs)
  apply (force simp: angle_def alpha1_def N1_def)
  done

lemma a1_leadsto_b1:
  "\<turnstile> \<box>($PsiInv \<and> [(N1 \<or> N2) \<and> \<not>beta1]_(x,y,sem,pc1,pc2))       
         \<and> SF(N1)_(x,y,sem,pc1,pc2) \<and> \<box> SF(N2)_(x,y,sem,pc1,pc2)   
         \<longrightarrow> (pc1 = #a \<leadsto> pc1 = #b)"
  apply (rule SF1)
  apply (tactic \<open>action_simp_tac (@{context} addsimps @{thms Psi_defs}) [] [@{thm squareE}] 1\<close>)
  apply (tactic
    \<open>action_simp_tac (@{context} addsimps (@{thm angle_def} :: @{thms Psi_defs})) [] [] 1\<close>)
  apply (clarsimp intro!: N1_enabled_at_both_a [THEN DmdImpl [temp_use]])
  apply (auto intro!: BoxDmd2_simple [temp_use] N2_live [temp_use]
    simp: split_box_conj more_temp_simps)
  done

(* Combine the leadsto properties for N1: it will arrive at pc1 = b *)

lemma N1_leadsto_b: "\<turnstile> \<box>($PsiInv \<and> [(N1 \<or> N2) \<and> \<not>beta1]_(x,y,sem,pc1,pc2))              
         \<and> SF(N1)_(x,y,sem,pc1,pc2) \<and> \<box> SF(N2)_(x,y,sem,pc1,pc2)   
         \<longrightarrow> (pc1 = #b \<or> pc1 = #g \<or> pc1 = #a \<leadsto> pc1 = #b)"
  apply (auto intro!: LatticeDisjunctionIntro [temp_use])
    apply (rule LatticeReflexivity [temp_use])
   apply (rule LatticeTransitivity [temp_use])
    apply (auto intro!: a1_leadsto_b1 [temp_use] g1_leadsto_a1 [temp_use]
      simp: split_box_conj)
  done

lemma N1_live: "\<turnstile> \<box>($PsiInv \<and> [(N1 \<or> N2) \<and> \<not>beta1]_(x,y,sem,pc1,pc2))              
         \<and> SF(N1)_(x,y,sem,pc1,pc2) \<and> \<box> SF(N2)_(x,y,sem,pc1,pc2)   
         \<longrightarrow> \<diamond>(pc1 = #b)"
  apply (auto simp: Init_defs intro!: N1_leadsto_b [temp_use, THEN [2] leadsto_init [temp_use]])
  apply (case_tac "pc1 (st1 sigma)")
    apply auto
  done

lemma N1_enabled_at_b: "\<turnstile> pc1 = #b \<longrightarrow> Enabled (<N1>_(x,y,sem,pc1,pc2))"
  apply clarsimp
  apply (rule_tac F = beta1 in enabled_mono)
   apply (enabled Inc_base)
   apply (force simp: beta1_def)
  apply (force simp: angle_def beta1_def N1_def)
  done

(* Now assemble the bits and pieces to prove that Psi is fair. *)

lemma Fair_M1_lemma: "\<turnstile> \<box>($PsiInv \<and> [(N1 \<or> N2)]_(x,y,sem,pc1,pc2))    
         \<and> SF(N1)_(x,y,sem,pc1,pc2) \<and> \<box>SF(N2)_(x,y,sem,pc1,pc2)   
         \<longrightarrow> SF(M1)_(x,y)"
  apply (rule_tac B = beta1 and P = "PRED pc1 = #b" in SF2)
   (* action premises *)
     apply (force simp: angle_def M1_def beta1_def)
  apply (force simp: angle_def Psi_defs)
  apply (force elim!: N1_enabled_at_b [temp_use])
    (* temporal premise: use previous lemmas and simple TL *)
  apply (force intro!: DmdStable [temp_use] N1_live [temp_use] Stuck_at_b [temp_use]
    elim: STL4E [temp_use] simp: square_def)
  done

lemma Fair_M1: "\<turnstile> Psi \<longrightarrow> WF(M1)_(x,y)"
  by (auto intro!: SFImplWF [temp_use] Fair_M1_lemma [temp_use] PsiInv [temp_use]
    simp: Psi_def split_box_conj [temp_use] more_temp_simps)

end
