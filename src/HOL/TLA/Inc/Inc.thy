(* 
    File:        TLA/ex/inc/Inc.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: Inc
    Logic Image: TLA

    Lamport's "increment" example.
*)

Inc  =  TLA + Nat +

(* program counter as an enumeration type *)
datatype pcount = a | b | g

consts
  (* program variables *)
  x,y,sem                 :: nat stfun
  pc1,pc2                 :: pcount stfun

  (* names of actions and predicates *)
  M1,M2,N1,N2                             :: action
  alpha1,alpha2,beta1,beta2,gamma1,gamma2 :: action
  InitPhi, InitPsi                        :: stpred
  PsiInv,PsiInv1,PsiInv2,PsiInv3          :: stpred

  (* temporal formulas *)
  Phi, Psi                                :: temporal
  
rules
  (* the "base" variables, required to compute enabledness predicates *)
  Inc_base      "basevars (x, y, sem, pc1, pc2)"

  (* definitions for high-level program *)
  InitPhi_def   "InitPhi == PRED x = # 0 & y = # 0"
  M1_def        "M1      == ACT  x` = Suc<$x> & y` = $y"
  M2_def        "M2      == ACT  y` = Suc<$y> & x` = $x"
  Phi_def       "Phi     == TEMP Init InitPhi & [][M1 | M2]_(x,y)
                                 & WF(M1)_(x,y) & WF(M2)_(x,y)"

  (* definitions for low-level program *)
  InitPsi_def   "InitPsi == PRED pc1 = #a & pc2 = #a
                                 & x = # 0 & y = # 0 & sem = # 1"
  alpha1_def    "alpha1  == ACT  $pc1 = #a & pc1$ = #b & $sem = Suc<sem`> 
                                 & unchanged(x,y,pc2)"
  alpha2_def    "alpha2  == ACT  $pc2 = #a & pc2$ = #b & $sem = Suc<sem`>
                                 & unchanged(x,y,pc1)"
  beta1_def     "beta1   == ACT  $pc1 = #b & pc1$ = #g & x$ = Suc<$x>
                                 & unchanged(y,sem,pc2)"
  beta2_def     "beta2   == ACT  $pc2 = #b & pc2$ = #g & y$ = Suc<$y>
                                 & unchanged(x,sem,pc1)"
  gamma1_def    "gamma1  == ACT  $pc1 = #g & pc1$ = #a & sem$ = Suc<$sem>
                                 & unchanged(x,y,pc2)"
  gamma2_def    "gamma2  == ACT  $pc2 = #g & pc2$ = #a & sem$ = Suc<$sem>
                                 & unchanged(x,y,pc1)"
  N1_def        "N1      == ACT  (alpha1 | beta1 | gamma1)"
  N2_def        "N2      == ACT  (alpha2 | beta2 | gamma2)"
  Psi_def       "Psi     == TEMP Init InitPsi
                               & [][N1 | N2]_(x,y,sem,pc1,pc2)
                               & SF(N1)_(x,y,sem,pc1,pc2)
                               & SF(N2)_(x,y,sem,pc1,pc2)"

  PsiInv1_def  "PsiInv1  == PRED sem = # 1 & pc1 = #a & pc2 = #a"
  PsiInv2_def  "PsiInv2  == PRED sem = # 0 & pc1 = #a & (pc2 = #b | pc2 = #g)"
  PsiInv3_def  "PsiInv3  == PRED sem = # 0 & pc2 = #a & (pc1 = #b | pc1 = #g)"
  PsiInv_def   "PsiInv   == PRED (PsiInv1 | PsiInv2 | PsiInv3)"
  
end

ML
