(*  Title:      HOLCF/IOA/meta_theory/Abstraction.thy
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Abstraction Theory -- tailored for I/O automata.
*)   

section "cex_abs";
	

(* ---------------------------------------------------------------- *)
(*                             cex_abs                              *)
(* ---------------------------------------------------------------- *)

Goal "cex_abs f (s,UU) = (f s, UU)";
by (simp_tac (simpset() addsimps [cex_abs_def]) 1);
qed"cex_abs_UU";

Goal "cex_abs f (s,nil) = (f s, nil)";
by (simp_tac (simpset() addsimps [cex_abs_def]) 1);
qed"cex_abs_nil";

Goal "cex_abs f (s,(a,t)>>ex) = (f s, (a,f t) >> (snd (cex_abs f (t,ex))))";
by (simp_tac (simpset() addsimps [cex_abs_def]) 1);
qed"cex_abs_cons";

Addsimps [cex_abs_UU, cex_abs_nil, cex_abs_cons];

 

section "lemmas";

(* ---------------------------------------------------------------- *)
(*                           Lemmas                                 *)
(* ---------------------------------------------------------------- *)

Goal "temp_weakening Q P h = (! ex. (ex |== P) --> (cex_abs h ex |== Q))";
by (simp_tac (simpset() addsimps [temp_weakening_def,temp_strengthening_def,
     NOT_def,temp_sat_def,satisfies_def]) 1);
by Auto_tac;
qed"temp_weakening_def2";

Goal "state_weakening Q P h = (! s t a. P (s,a,t) --> Q (h(s),a,h(t)))";
by (simp_tac (simpset() addsimps [state_weakening_def,state_strengthening_def,
     NOT_def]) 1);
by Auto_tac;
qed"state_weakening_def2";


section "Abstraction Rules for Properties";

(* ---------------------------------------------------------------- *)
(*                Abstraction Rules for Properties                  *)
(* ---------------------------------------------------------------- *)


Goalw [cex_abs_def]
 "[| is_abstraction h C A |] ==>\
\ !s. reachable C s & is_exec_frag C (s,xs) \
\ --> is_exec_frag A (cex_abs h (s,xs))"; 

by (Asm_full_simp_tac 1);
by (pair_induct_tac "xs" [is_exec_frag_def] 1);
(* main case *)
by (safe_tac set_cs);
by (asm_full_simp_tac (simpset() addsimps [is_abstraction_def])1);
by (forward_tac [reachable.reachable_n] 1);
by (assume_tac 1);
by (Asm_full_simp_tac 1);
qed_spec_mp"exec_frag_abstraction";


Goal "is_abstraction h C A ==> weakeningIOA A C h";
by (asm_full_simp_tac (simpset() addsimps [weakeningIOA_def])1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [executions_def]) 1);
(* start state *) 
by (rtac conjI 1);
by (asm_full_simp_tac (simpset() addsimps [is_abstraction_def,cex_abs_def]) 1);
(* is-execution-fragment *)
by (etac exec_frag_abstraction 1);
by (asm_full_simp_tac (simpset() addsimps [reachable.reachable_0]) 1);
qed"abs_is_weakening";


Goal "[|is_abstraction h C A; validIOA A Q; temp_strengthening Q P h |] \
\         ==> validIOA C P";
by (dtac abs_is_weakening 1);
by (asm_full_simp_tac (simpset() addsimps [weakeningIOA_def, 
    validIOA_def, temp_strengthening_def])1);
by (safe_tac set_cs);
by (pair_tac "ex" 1);
qed"AbsRuleT1";


(* FIX: Nach TLS.ML *)

Goal "(ex |== P .--> Q) = ((ex |== P) --> (ex |== Q))";
by (simp_tac (simpset() addsimps [IMPLIES_def,temp_sat_def, satisfies_def])1);
qed"IMPLIES_temp_sat";

Goal "(ex |== P .& Q) = ((ex |== P) & (ex |== Q))";
by (simp_tac (simpset() addsimps [AND_def,temp_sat_def, satisfies_def])1);
qed"AND_temp_sat";

Goal "(ex |== P .| Q) = ((ex |== P) | (ex |== Q))";
by (simp_tac (simpset() addsimps [OR_def,temp_sat_def, satisfies_def])1);
qed"OR_temp_sat";

Goal "(ex |== .~ P) = (~ (ex |== P))";
by (simp_tac (simpset() addsimps [NOT_def,temp_sat_def, satisfies_def])1);
qed"NOT_temp_sat";

Addsimps [IMPLIES_temp_sat,AND_temp_sat,OR_temp_sat,NOT_temp_sat];


Goalw [is_live_abstraction_def]
   "[|is_live_abstraction h (C,L) (A,M); \
\         validLIOA (A,M) Q;  temp_strengthening Q P h |] \
\         ==> validLIOA (C,L) P";
by Auto_tac;
by (dtac abs_is_weakening 1);
by (asm_full_simp_tac (simpset() addsimps [weakeningIOA_def, temp_weakening_def2,
    validLIOA_def, validIOA_def, temp_strengthening_def])1);
by (safe_tac set_cs);
by (pair_tac "ex" 1);
qed"AbsRuleT2";


Goalw [is_live_abstraction_def]
   "[|is_live_abstraction h (C,L) (A,M); \
\         validLIOA (A,M) (H1 .--> Q);  temp_strengthening Q P h; \
\         temp_weakening H1 H2 h; validLIOA (C,L) H2 |] \
\         ==> validLIOA (C,L) P";
by Auto_tac;
by (dtac abs_is_weakening 1);
by (asm_full_simp_tac (simpset() addsimps [weakeningIOA_def, temp_weakening_def2,
    validLIOA_def, validIOA_def, temp_strengthening_def])1);
by (safe_tac set_cs);
by (pair_tac "ex" 1);
qed"AbsRuleTImprove";


section "Correctness of safe abstraction";

(* ---------------------------------------------------------------- *)
(*              Correctness of safe abstraction                     *)
(* ---------------------------------------------------------------- *)


Goalw [is_abstraction_def,is_ref_map_def] 
"is_abstraction h C A ==> is_ref_map h C A";
by (safe_tac set_cs);
by (res_inst_tac[("x","(a,h t)>>nil")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [move_def])1);
qed"abstraction_is_ref_map";


Goal "[| inp(C)=inp(A); out(C)=out(A); \
\                  is_abstraction h C A |] \
\               ==> C =<| A";
by (asm_full_simp_tac (simpset() addsimps [ioa_implements_def]) 1);
by (rtac trace_inclusion 1);
by (simp_tac (simpset() addsimps [externals_def])1);
by (SELECT_GOAL (auto_tac (claset(),simpset()))1);
by (etac abstraction_is_ref_map 1);
qed"abs_safety";


section "Correctness of life abstraction";

(* ---------------------------------------------------------------- *)
(*              Correctness of life abstraction                     *)
(* ---------------------------------------------------------------- *)


(* Reduces to Filter (Map fst x) = Filter (Map fst (Map (%(a,t). (a,x)) x),
   that is to special Map Lemma *)
Goalw [cex_abs_def,mk_trace_def,filter_act_def]
  "ext C = ext A \
\        ==> mk_trace C$xs = mk_trace A$(snd (cex_abs f (s,xs)))";
by (Asm_full_simp_tac 1);
by (pair_induct_tac "xs" [] 1);
qed"traces_coincide_abs";


(* Does not work with abstraction_is_ref_map as proof of abs_safety, because
   is_live_abstraction includes temp_strengthening which is necessarily based
   on cex_abs and not on corresp_ex. Thus, the proof is redoone in a more specific
   way for cex_abs *)
Goal "[| inp(C)=inp(A); out(C)=out(A); \
\                  is_live_abstraction h (C,M) (A,L) |] \
\               ==> live_implements (C,M) (A,L)";

by (asm_full_simp_tac (simpset() addsimps [is_live_abstraction_def, live_implements_def,
livetraces_def,liveexecutions_def]) 1);
by (safe_tac set_cs);
by (res_inst_tac[("x","cex_abs h ex")] exI 1);
by (safe_tac set_cs);
  (* Traces coincide *)
  by (pair_tac "ex" 1);
  by (rtac traces_coincide_abs 1);
  by (simp_tac (simpset() addsimps [externals_def])1);
  by (SELECT_GOAL (auto_tac (claset(),simpset()))1);
 
  (* cex_abs is execution *)
  by (pair_tac "ex" 1);
  by (asm_full_simp_tac (simpset() addsimps [executions_def]) 1);
  (* start state *) 
  by (rtac conjI 1);
  by (asm_full_simp_tac (simpset() addsimps [is_abstraction_def,cex_abs_def]) 1);
  (* is-execution-fragment *)
  by (etac exec_frag_abstraction 1);
  by (asm_full_simp_tac (simpset() addsimps [reachable.reachable_0]) 1);

 (* Liveness *) 
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2]) 1);
 by (pair_tac "ex" 1);
qed"abs_liveness";

(* FIX: NAch Traces.ML bringen *)

Goalw [ioa_implements_def] 
"[| A =<| B; B =<| C|] ==> A =<| C"; 
by Auto_tac;
qed"implements_trans";


section "Abstraction Rules for Automata";

(* ---------------------------------------------------------------- *)
(*                Abstraction Rules for Automata                    *)
(* ---------------------------------------------------------------- *)

Goal "[| inp(C)=inp(A); out(C)=out(A); \
\                  inp(Q)=inp(P); out(Q)=out(P); \
\                  is_abstraction h1 C A; \
\                  A =<| Q ; \
\                  is_abstraction h2 Q P |] \
\               ==> C =<| P";   
by (dtac abs_safety 1);
by (REPEAT (atac 1));
by (dtac abs_safety 1);
by (REPEAT (atac 1));
by (etac implements_trans 1);
by (etac implements_trans 1);
by (assume_tac 1);
qed"AbsRuleA1";


Goal "[| inp(C)=inp(A); out(C)=out(A); \
\                  inp(Q)=inp(P); out(Q)=out(P); \
\                  is_live_abstraction h1 (C,LC) (A,LA); \
\                  live_implements (A,LA) (Q,LQ) ; \
\                  is_live_abstraction h2 (Q,LQ) (P,LP) |] \
\               ==> live_implements (C,LC) (P,LP)";   
by (dtac abs_liveness 1);
by (REPEAT (atac 1));
by (dtac abs_liveness 1);
by (REPEAT (atac 1));
by (etac live_implements_trans 1);
by (etac live_implements_trans 1);
by (assume_tac 1);
qed"AbsRuleA2";


Delsimps [split_paired_All];


section "Localizing Temporal Strengthenings and Weakenings";

(* ---------------------------------------------------------------- *)
(*                Localizing Temproal Strengthenings - 1               *)
(* ---------------------------------------------------------------- *)

Goalw [temp_strengthening_def]
"[| temp_strengthening P1 Q1 h; \
\         temp_strengthening P2 Q2 h |] \
\      ==> temp_strengthening (P1 .& P2) (Q1 .& Q2) h";
by Auto_tac;
qed"strength_AND";

Goalw [temp_strengthening_def]
"[| temp_strengthening P1 Q1 h; \
\         temp_strengthening P2 Q2 h |] \
\      ==> temp_strengthening (P1 .| P2) (Q1 .| Q2) h";
by Auto_tac;
qed"strength_OR";

Goalw [temp_strengthening_def]
"[| temp_weakening P Q h |] \
\      ==> temp_strengthening (.~ P) (.~ Q) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2])1);
by Auto_tac;
qed"strength_NOT";

Goalw [temp_strengthening_def]
"[| temp_weakening P1 Q1 h; \
\         temp_strengthening P2 Q2 h |] \
\      ==> temp_strengthening (P1 .--> P2) (Q1 .--> Q2) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2])1);
qed"strength_IMPLIES";



(* ---------------------------------------------------------------- *)
(*                Localizing Temproal Weakenings - Part 1           *)
(* ---------------------------------------------------------------- *)

Goal
"[| temp_weakening P1 Q1 h; \
\         temp_weakening P2 Q2 h |] \
\      ==> temp_weakening (P1 .& P2) (Q1 .& Q2) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2])1);
qed"weak_AND";

Goal 
"[| temp_weakening P1 Q1 h; \
\         temp_weakening P2 Q2 h |] \
\      ==> temp_weakening (P1 .| P2) (Q1 .| Q2) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2])1);
qed"weak_OR";

Goalw [temp_strengthening_def]
"[| temp_strengthening P Q h |] \
\      ==> temp_weakening (.~ P) (.~ Q) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2])1);
by Auto_tac;
qed"weak_NOT";

Goalw [temp_strengthening_def]
"[| temp_strengthening P1 Q1 h; \
\         temp_weakening P2 Q2 h |] \
\      ==> temp_weakening (P1 .--> P2) (Q1 .--> Q2) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2])1);
qed"weak_IMPLIES";


(* ---------------------------------------------------------------- *)
(*             Localizing Temproal Strengthenings - 2               *)
(* ---------------------------------------------------------------- *)


(* ------------------ Box ----------------------------*)

(* FIX: should be same as nil_is_Conc2 when all nils are turned to right side !! *)
Goal "(UU = x @@ y) = (((x::'a Seq)= UU) | (x=nil & y=UU))";
by (Seq_case_simp_tac "x" 1);
by Auto_tac;
qed"UU_is_Conc";

Goal 
"Finite s1 --> \
\ (! ex. (s~=nil & s~=UU & ex2seq ex = s1 @@ s) --> (? ex'. s = ex2seq ex'))";
by (rtac impI 1);
by (Seq_Finite_induct_tac 1);
by (Blast_tac 1);
(* main case *)
by (clarify_tac set_cs 1);
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
(* UU case *)
by (asm_full_simp_tac (simpset() addsimps [nil_is_Conc])1);
(* nil case *)
by (asm_full_simp_tac (simpset() addsimps [nil_is_Conc])1);
(* cons case *)
by (pair_tac "aa" 1);
by Auto_tac;
qed_spec_mp"ex2seqConc";

(* important property of ex2seq: can be shiftet, as defined "pointwise" *)

Goalw [tsuffix_def,suffix_def]
"tsuffix s (ex2seq ex) ==> ? ex'. s = (ex2seq ex')";
by Auto_tac;
by (dtac ex2seqConc 1);
by Auto_tac;
qed"ex2seq_tsuffix";


(* FIX: NAch Sequence.ML bringen *)

Goal "(Map f$s = nil) = (s=nil)";
by (Seq_case_simp_tac "s" 1);
qed"Mapnil";

Goal "(Map f$s = UU) = (s=UU)";
by (Seq_case_simp_tac "s" 1);
qed"MapUU";


(* important property of cex_absSeq: As it is a 1to1 correspondence, 
  properties carry over *)

Goalw [tsuffix_def,suffix_def,cex_absSeq_def]
"tsuffix s t ==> tsuffix (cex_absSeq h s) (cex_absSeq h t)";
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [Mapnil])1);
by (asm_full_simp_tac (simpset() addsimps [MapUU])1);
by (res_inst_tac [("x","Map (%(s,a,t). (h s,a, h t))$s1")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [Map2Finite,MapConc])1);
qed"cex_absSeq_tsuffix";


Goalw [temp_strengthening_def,state_strengthening_def, temp_sat_def,
satisfies_def,Box_def]
"[| temp_strengthening P Q h |]\
\      ==> temp_strengthening ([] P) ([] Q) h";
by (clarify_tac set_cs 1);
by (ftac ex2seq_tsuffix 1);
by (clarify_tac set_cs 1);
by (dres_inst_tac [("h","h")] cex_absSeq_tsuffix 1);
by (asm_full_simp_tac (simpset() addsimps [ex2seq_abs_cex])1);
qed"strength_Box";


(* ------------------ Init ----------------------------*)

Goalw [temp_strengthening_def,state_strengthening_def,
temp_sat_def,satisfies_def,Init_def,unlift_def]
"[| state_strengthening P Q h |]\
\      ==> temp_strengthening (Init P) (Init Q) h";
by (safe_tac set_cs);
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
qed"strength_Init";


(* ------------------ Next ----------------------------*)

Goal 
"(TL$(ex2seq (cex_abs h ex))=UU) = (TL$(ex2seq ex)=UU)";
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
by (Seq_case_simp_tac "s" 1);
by (pair_tac "a" 1);
qed"TL_ex2seq_UU";

Goal 
"(TL$(ex2seq (cex_abs h ex))=nil) = (TL$(ex2seq ex)=nil)";
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
by (Seq_case_simp_tac "s" 1);
by (pair_tac "a" 1);
qed"TL_ex2seq_nil";

(* FIX: put to Sequence Lemmas *)
Goal "Map f$(TL$s) = TL$(Map f$s)";
by (Seq_induct_tac "s" [] 1);
qed"MapTL";

(* important property of cex_absSeq: As it is a 1to1 correspondence, 
  properties carry over *)

Goalw [cex_absSeq_def]
"cex_absSeq h (TL$s) = (TL$(cex_absSeq h s))";
by (simp_tac (simpset() addsimps [MapTL]) 1);
qed"cex_absSeq_TL";

(* important property of ex2seq: can be shiftet, as defined "pointwise" *)

Goal "[| (snd ex)~=UU ; (snd ex)~=nil |] ==> (? ex'. TL$(ex2seq ex) = ex2seq ex')";
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
by Auto_tac;
qed"TLex2seq";

 
Goal "(TL$(ex2seq ex)~=nil) = ((snd ex)~=nil & (snd ex)~=UU)";
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
by (Seq_case_simp_tac "s" 1);
by (pair_tac "a" 1);
qed"ex2seqnilTL";


Goalw [temp_strengthening_def,state_strengthening_def,
temp_sat_def, satisfies_def,Next_def]
"[| temp_strengthening P Q h |]\
\      ==> temp_strengthening (Next P) (Next Q) h";
by (Asm_full_simp_tac 1);
by (safe_tac set_cs);
by (asm_full_simp_tac (simpset() addsimps [TL_ex2seq_nil,TL_ex2seq_UU]) 1);
by (asm_full_simp_tac (simpset() addsimps [TL_ex2seq_nil,TL_ex2seq_UU]) 1);
by (asm_full_simp_tac (simpset() addsimps [TL_ex2seq_nil,TL_ex2seq_UU]) 1);
by (asm_full_simp_tac (simpset() addsimps [TL_ex2seq_nil,TL_ex2seq_UU]) 1);
(* cons case *)
by (asm_full_simp_tac (simpset() addsimps [TL_ex2seq_nil,TL_ex2seq_UU,
        ex2seq_abs_cex,cex_absSeq_TL RS sym, ex2seqnilTL])1);
by (etac conjE 1);
by (dtac TLex2seq 1);
by (assume_tac 1);
by Auto_tac;
qed"strength_Next";



(* ---------------------------------------------------------------- *)
(*             Localizing Temporal Weakenings     - 2               *)
(* ---------------------------------------------------------------- *)


Goal 
"[| state_weakening P Q h |]\
\      ==> temp_weakening (Init P) (Init Q) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2,
      state_weakening_def2, temp_sat_def,satisfies_def,Init_def,unlift_def])1);
by (safe_tac set_cs);
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
qed"weak_Init";


(* ---------------------------------------------------------------- *)
(*             Localizing Temproal Strengthenings - 3               *)
(* ---------------------------------------------------------------- *)


Goalw [Diamond_def]
"[| temp_strengthening P Q h |]\
\      ==> temp_strengthening (<> P) (<> Q) h";
by (rtac strength_NOT 1);
by (rtac weak_Box 1);
by (etac weak_NOT 1);
qed"strength_Diamond";

Goalw [Leadsto_def]
"[| temp_weakening P1 P2 h;\
\         temp_strengthening Q1 Q2 h |]\
\      ==> temp_strengthening (P1 ~> Q1) (P2 ~> Q2) h";
by (rtac strength_Box 1);
by (etac strength_IMPLIES 1);
by (etac strength_Diamond 1);
qed"strength_Leadsto";


(* ---------------------------------------------------------------- *)
(*             Localizing Temporal Weakenings - 3                   *)
(* ---------------------------------------------------------------- *)


Goalw [Diamond_def]
"[| temp_weakening P Q h |]\
\      ==> temp_weakening (<> P) (<> Q) h";
by (rtac weak_NOT 1);
by (rtac strength_Box 1);
by (etac strength_NOT 1);
qed"weak_Diamond";

Goalw [Leadsto_def]
"[| temp_strengthening P1 P2 h;\
\         temp_weakening Q1 Q2 h |]\
\      ==> temp_weakening (P1 ~> Q1) (P2 ~> Q2) h";
by (rtac weak_Box 1);
by (etac weak_IMPLIES 1);
by (etac weak_Diamond 1);
qed"weak_Leadsto";

Goalw [WF_def]
  " !!A. [| !! s. Enabled A acts (h s) ==> Enabled C acts s|] \ 
\   ==> temp_weakening (WF A acts) (WF C acts) h";
by (rtac weak_IMPLIES 1);
by (rtac strength_Diamond 1);
by (rtac strength_Box 1);
by (rtac strength_Init 1);
by (rtac weak_Box 2);
by (rtac weak_Diamond 2);
by (rtac weak_Init 2);
by (auto_tac (claset(),
              simpset() addsimps [state_weakening_def,state_strengthening_def,
                             xt2_def,plift_def,option_lift_def,NOT_def]));
qed"weak_WF";

Goalw [SF_def]
  " !!A. [| !! s. Enabled A acts (h s) ==> Enabled C acts s|] \ 
\   ==> temp_weakening (SF A acts) (SF C acts) h";
by (rtac weak_IMPLIES 1);
by (rtac strength_Box 1);
by (rtac strength_Diamond 1);
by (rtac strength_Init 1);
by (rtac weak_Box 2);
by (rtac weak_Diamond 2);
by (rtac weak_Init 2);
by (auto_tac (claset(),
              simpset() addsimps [state_weakening_def,state_strengthening_def,
                             xt2_def,plift_def,option_lift_def,NOT_def]));
qed"weak_SF";


val weak_strength_lemmas = 
    [weak_OR,weak_AND,weak_NOT,weak_IMPLIES,weak_Box,weak_Next,weak_Init,
     weak_Diamond,weak_Leadsto,strength_OR,strength_AND,strength_NOT,
     strength_IMPLIES,strength_Box,strength_Next,strength_Init,
     strength_Diamond,strength_Leadsto,weak_WF,weak_SF];

fun abstraction_tac i = 
    SELECT_GOAL (auto_tac (claset() addSIs weak_strength_lemmas,
                           simpset() addsimps [state_strengthening_def,state_weakening_def])) i;
