(*  Title:      HOLCF/IOA/meta_theory/Abstraction.thy
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

Abstraction Theory -- tailored for I/O automata
*)   


section "cex_abs";
	

(* ---------------------------------------------------------------- *)
(*                             cex_abs                              *)
(* ---------------------------------------------------------------- *)

goal thy "cex_abs f (s,UU) = (f s, UU)";
by (simp_tac (simpset() addsimps [cex_abs_def]) 1);
qed"cex_abs_UU";

goal thy "cex_abs f (s,nil) = (f s, nil)";
by (simp_tac (simpset() addsimps [cex_abs_def]) 1);
qed"cex_abs_nil";

goal thy "cex_abs f (s,(a,t)>>ex) = (f s, (a,f t) >> (snd (cex_abs f (t,ex))))";
by (simp_tac (simpset() addsimps [cex_abs_def]) 1);
qed"cex_abs_cons";

Addsimps [cex_abs_UU, cex_abs_nil, cex_abs_cons];

 

section "lemmas";

(* ---------------------------------------------------------------- *)
(*                           Lemmas                                 *)
(* ---------------------------------------------------------------- *)

goal thy "temp_weakening Q P h = (! ex. (ex |== P) --> (cex_abs h ex |== Q))";
by (simp_tac (simpset() addsimps [temp_weakening_def,temp_strengthening_def,
     NOT_def,temp_sat_def,satisfies_def]) 1);
auto();
qed"temp_weakening_def2";

goal thy "state_weakening Q P h = (! s t a. P (s,a,t) --> Q (h(s),a,h(t)))";
by (simp_tac (simpset() addsimps [state_weakening_def,state_strengthening_def,
     NOT_def]) 1);
auto();
qed"state_weakening_def2";


section "Abstraction Rules for Properties";

(* ---------------------------------------------------------------- *)
(*                Abstraction Rules for Properties                  *)
(* ---------------------------------------------------------------- *)


goalw thy [cex_abs_def]
 "!!h.[| is_abstraction h C A |] ==>\
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
qed"exec_frag_abstraction";


goal thy "!!A. is_abstraction h C A ==> weakeningIOA A C h";
by (asm_full_simp_tac (simpset() addsimps [weakeningIOA_def])1);
auto();
by (asm_full_simp_tac (simpset() addsimps [executions_def]) 1);
(* start state *) 
by (rtac conjI 1);
by (asm_full_simp_tac (simpset() addsimps [is_abstraction_def,cex_abs_def]) 1);
(* is-execution-fragment *)
by (etac (exec_frag_abstraction RS spec RS mp) 1);
by (asm_full_simp_tac (simpset() addsimps [reachable.reachable_0]) 1);
qed"abs_is_weakening";


goal thy "!!A. [|is_abstraction h C A; validIOA A Q; temp_strengthening Q P h |] \
\         ==> validIOA C P";
bd abs_is_weakening 1;
by (asm_full_simp_tac (simpset() addsimps [weakeningIOA_def, 
    validIOA_def, temp_strengthening_def])1);
by (safe_tac set_cs);
by (pair_tac "ex" 1);
qed"AbsRuleT1";


(* FIX: Nach TLS.ML *)

goal thy "(ex |== P .--> Q) = ((ex |== P) --> (ex |== Q))";
by (simp_tac (simpset() addsimps [IMPLIES_def,temp_sat_def, satisfies_def])1);
qed"IMPLIES_temp_sat";

goal thy "(ex |== P .& Q) = ((ex |== P) & (ex |== Q))";
by (simp_tac (simpset() addsimps [AND_def,temp_sat_def, satisfies_def])1);
qed"AND_temp_sat";

goal thy "(ex |== P .| Q) = ((ex |== P) | (ex |== Q))";
by (simp_tac (simpset() addsimps [OR_def,temp_sat_def, satisfies_def])1);
qed"OR_temp_sat";

goal thy "(ex |== .~ P) = (~ (ex |== P))";
by (simp_tac (simpset() addsimps [NOT_def,temp_sat_def, satisfies_def])1);
qed"NOT_temp_sat";

Addsimps [IMPLIES_temp_sat,AND_temp_sat,OR_temp_sat,NOT_temp_sat];


goalw thy [is_live_abstraction_def]
   "!!A. [|is_live_abstraction h (C,L) (A,M); \
\         validLIOA (A,M) Q;  temp_strengthening Q P h |] \
\         ==> validLIOA (C,L) P";
auto();
bd abs_is_weakening 1;
by (asm_full_simp_tac (simpset() addsimps [weakeningIOA_def, temp_weakening_def2,
    validLIOA_def, validIOA_def, temp_strengthening_def])1);
by (safe_tac set_cs);
by (pair_tac "ex" 1);
qed"AbsRuleT2";


goalw thy [is_live_abstraction_def]
   "!!A. [|is_live_abstraction h (C,L) (A,M); \
\         validLIOA (A,M) (H1 .--> Q);  temp_strengthening Q P h; \
\         temp_weakening H1 H2 h; validLIOA (C,L) H2 |] \
\         ==> validLIOA (C,L) P";
auto();
bd abs_is_weakening 1;
by (asm_full_simp_tac (simpset() addsimps [weakeningIOA_def, temp_weakening_def2,
    validLIOA_def, validIOA_def, temp_strengthening_def])1);
by (safe_tac set_cs);
by (pair_tac "ex" 1);
qed"AbsRuleTImprove";


section "Correctness of safe abstraction";

(* ---------------------------------------------------------------- *)
(*              Correctness of safe abstraction                     *)
(* ---------------------------------------------------------------- *)


goalw thy [is_abstraction_def,is_ref_map_def] 
"!! h. is_abstraction h C A ==> is_ref_map h C A";
by (safe_tac set_cs);
by (res_inst_tac[("x","(a,h t)>>nil")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [move_def])1);
qed"abstraction_is_ref_map";


goal thy "!! h. [| inp(C)=inp(A); out(C)=out(A); \
\                  is_abstraction h C A |] \
\               ==> C =<| A";
by (asm_full_simp_tac (simpset() addsimps [ioa_implements_def]) 1);
br trace_inclusion 1;
by (simp_tac (simpset() addsimps [externals_def])1);
by (SELECT_GOAL (auto_tac (claset(),simpset()))1);
be abstraction_is_ref_map 1;
qed"abs_safety";


section "Correctness of life abstraction";

(* ---------------------------------------------------------------- *)
(*              Correctness of life abstraction                     *)
(* ---------------------------------------------------------------- *)


(* Reduces to Filter (Map fst x) = Filter (Map fst (Map (%(a,t). (a,x)) x),
   that is to special Map Lemma *)
goalw thy [cex_abs_def,mk_trace_def,filter_act_def]
  "!! f. ext C = ext A \
\        ==> mk_trace C`xs = mk_trace A`(snd (cex_abs f (s,xs)))";
by (Asm_full_simp_tac 1);
by (pair_induct_tac "xs" [] 1);
qed"traces_coincide_abs";


goalw thy [cex_abs_def]
 "!!f.[| is_abstraction h C A |] ==>\
\ !s. reachable C s & is_exec_frag C (s,xs) \
\ --> is_exec_frag A (cex_abs h (s,xs))"; 

by (Asm_full_simp_tac 1);
by (pair_induct_tac "xs" [is_exec_frag_def] 1);
(* main case *)
by (safe_tac set_cs);
(* Stepd correspond to each other *)
by (asm_full_simp_tac (simpset() addsimps [is_abstraction_def])1);
(* IH *)
(* reachable_n looping, therefore apply it manually *)
by (eres_inst_tac [("x","y")] allE 1);
by (Asm_full_simp_tac 1);
by (forward_tac [reachable.reachable_n] 1);
by (assume_tac 1);
by (Asm_full_simp_tac 1);
qed_spec_mp"correp_is_exec_abs";

(* Does not work with abstraction_is_ref_map as proof of abs_safety, because
   is_live_abstraction includes temp_strengthening which is necessarily based
   on cex_abs and not on corresp_ex. Thus, the proof is redoone in a more specific
   way for cex_abs *)
goal thy "!! h. [| inp(C)=inp(A); out(C)=out(A); \
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
  by (etac correp_is_exec_abs 1);
  by (asm_full_simp_tac (simpset() addsimps [reachable.reachable_0]) 1);

 (* Liveness *) 
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2]) 1);
 by (pair_tac "ex" 1);
qed"abs_liveness";

(* FIX: NAch Traces.ML bringen *)

goalw thy [ioa_implements_def] 
"!! A. [| A =<| B; B =<| C|] ==> A =<| C"; 
auto();
qed"implements_trans";


section "Abstraction Rules for Automata";

(* ---------------------------------------------------------------- *)
(*                Abstraction Rules for Automata                    *)
(* ---------------------------------------------------------------- *)

goal thy "!! C. [| inp(C)=inp(A); out(C)=out(A); \
\                  inp(Q)=inp(P); out(Q)=out(P); \
\                  is_abstraction h1 C A; \
\                  A =<| Q ; \
\                  is_abstraction h2 Q P |] \
\               ==> C =<| P";   
bd abs_safety 1;
by (REPEAT (atac 1));
bd abs_safety 1;
by (REPEAT (atac 1));
be implements_trans 1;
be implements_trans 1;
ba 1;
qed"AbsRuleA1";


goal thy "!! C. [| inp(C)=inp(A); out(C)=out(A); \
\                  inp(Q)=inp(P); out(Q)=out(P); \
\                  is_live_abstraction h1 (C,LC) (A,LA); \
\                  live_implements (A,LA) (Q,LQ) ; \
\                  is_live_abstraction h2 (Q,LQ) (P,LP) |] \
\               ==> live_implements (C,LC) (P,LP)";   
bd abs_liveness 1;
by (REPEAT (atac 1));
bd abs_liveness 1;
by (REPEAT (atac 1));
be live_implements_trans 1;
be live_implements_trans 1;
ba 1;
qed"AbsRuleA2";


Delsimps [split_paired_All];


section "Localizing Temporal Strengthenings and Weakenings";

(* ---------------------------------------------------------------- *)
(*                Localizing Temproal Strengthenings - 1               *)
(* ---------------------------------------------------------------- *)

goalw thy [temp_strengthening_def]
"!! h. [| temp_strengthening P1 Q1 h; \
\         temp_strengthening P2 Q2 h |] \
\      ==> temp_strengthening (P1 .& P2) (Q1 .& Q2) h";
auto();
qed"strength_AND";

goalw thy [temp_strengthening_def]
"!! h. [| temp_strengthening P1 Q1 h; \
\         temp_strengthening P2 Q2 h |] \
\      ==> temp_strengthening (P1 .| P2) (Q1 .| Q2) h";
auto();
qed"strength_OR";

goalw thy [temp_strengthening_def]
"!! h. [| temp_weakening P Q h |] \
\      ==> temp_strengthening (.~ P) (.~ Q) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2])1);
auto();
qed"strength_NOT";

goalw thy [temp_strengthening_def]
"!! h. [| temp_weakening P1 Q1 h; \
\         temp_strengthening P2 Q2 h |] \
\      ==> temp_strengthening (P1 .--> P2) (Q1 .--> Q2) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2])1);
qed"strength_IMPLIES";



(* ---------------------------------------------------------------- *)
(*                Localizing Temproal Weakenings - Part 1           *)
(* ---------------------------------------------------------------- *)

goal thy
"!! h. [| temp_weakening P1 Q1 h; \
\         temp_weakening P2 Q2 h |] \
\      ==> temp_weakening (P1 .& P2) (Q1 .& Q2) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2])1);
qed"weak_AND";

goal thy 
"!! h. [| temp_weakening P1 Q1 h; \
\         temp_weakening P2 Q2 h |] \
\      ==> temp_weakening (P1 .| P2) (Q1 .| Q2) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2])1);
qed"weak_OR";

goalw thy [temp_strengthening_def]
"!! h. [| temp_strengthening P Q h |] \
\      ==> temp_weakening (.~ P) (.~ Q) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2])1);
auto();
qed"weak_NOT";

goalw thy [temp_strengthening_def]
"!! h. [| temp_strengthening P1 Q1 h; \
\         temp_weakening P2 Q2 h |] \
\      ==> temp_weakening (P1 .--> P2) (Q1 .--> Q2) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2])1);
qed"weak_IMPLIES";


(* ---------------------------------------------------------------- *)
(*             Localizing Temproal Strengthenings - 2               *)
(* ---------------------------------------------------------------- *)


(* ------------------ Box ----------------------------*)

(* FIX: should be same as nil_is_Conc2 when all nils are turned to right side !! *)
goal thy "(UU = x @@ y) = (((x::'a Seq)= UU) | (x=nil & y=UU))";
by (Seq_case_simp_tac "x" 1);
by Auto_tac;
qed"UU_is_Conc";

goal thy 
"Finite s1 --> \
\ (! ex. (s~=nil & s~=UU & ex2seq ex = s1 @@ s) --> (? ex'. s = ex2seq ex'))";
by (rtac impI 1);
by (Seq_Finite_induct_tac 1);
(* main case *)
by (Blast_tac 1);
by (clarify_tac set_cs 1);
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
(* UU case *)
by (asm_full_simp_tac (simpset() addsimps [UU_is_Conc])1);
(* nil case *)
by (asm_full_simp_tac (simpset() addsimps [nil_is_Conc])1);
(* cons case *)
by (pair_tac "aa" 1);
auto();
qed_spec_mp"ex2seqConc";

(* important property of ex2seq: can be shiftet, as defined "pointwise" *)

goalw thy [tsuffix_def,suffix_def]
"!!s. tsuffix s (ex2seq ex) ==> ? ex'. s = (ex2seq ex')";
auto();
bd ex2seqConc 1;
auto();
qed"ex2seq_tsuffix";


goal thy "(Map f`s = nil) = (s=nil)";
by (Seq_case_simp_tac "s" 1);
qed"Mapnil";

goal thy "(Map f`s = UU) = (s=UU)";
by (Seq_case_simp_tac "s" 1);
qed"MapUU";


(* important property of cex_absSeq: As it is a 1to1 correspondence, 
  properties carry over *)

goalw thy [tsuffix_def,suffix_def,cex_absSeq_def]
"!! s. tsuffix s t ==> tsuffix (cex_absSeq h s) (cex_absSeq h t)";
auto();
by (asm_full_simp_tac (simpset() addsimps [Mapnil])1);
by (asm_full_simp_tac (simpset() addsimps [MapUU])1);
by (res_inst_tac [("x","Map (%(s,a,t). (h s,a, h t))`s1")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [Map2Finite,MapConc])1);
qed"cex_absSeq_tsuffix";


goalw thy [temp_strengthening_def,state_strengthening_def, temp_sat_def,
satisfies_def,Box_def]
"!! h. [| temp_strengthening P Q h |]\
\      ==> temp_strengthening ([] P) ([] Q) h";
by (clarify_tac set_cs 1);
by (forward_tac [ex2seq_tsuffix] 1);
by (clarify_tac set_cs 1);
by (dres_inst_tac [("h","h")] cex_absSeq_tsuffix 1);
by (asm_full_simp_tac (simpset() addsimps [ex2seq_abs_cex])1);
qed"strength_Box";


(* ------------------ Init ----------------------------*)

goalw thy [temp_strengthening_def,state_strengthening_def,
temp_sat_def,satisfies_def,Init_def,unlift_def]
"!! h. [| state_strengthening P Q h |]\
\      ==> temp_strengthening (Init P) (Init Q) h";
by (safe_tac set_cs);
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
qed"strength_Init";


(* ------------------ Next ----------------------------*)

goal thy 
"(TL`(ex2seq (cex_abs h ex))=UU) = (TL`(ex2seq ex)=UU)";
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
by (Seq_case_simp_tac "s" 1);
by (pair_tac "a" 1);
qed"TL_ex2seq_UU";

goal thy 
"(TL`(ex2seq (cex_abs h ex))=nil) = (TL`(ex2seq ex)=nil)";
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
by (Seq_case_simp_tac "s" 1);
by (pair_tac "a" 1);
qed"TL_ex2seq_nil";

(* FIX: put to Sequence Lemmas *)
goal thy "Map f`(TL`s) = TL`(Map f`s)";
by (Seq_induct_tac "s" [] 1);
qed"MapTL";

(* important property of cex_absSeq: As it is a 1to1 correspondence, 
  properties carry over *)

goalw thy [cex_absSeq_def]
"cex_absSeq h (TL`s) = (TL`(cex_absSeq h s))";
by (simp_tac (simpset() addsimps [MapTL]) 1);
qed"cex_absSeq_TL";

(* important property of ex2seq: can be shiftet, as defined "pointwise" *)

goal thy "!!ex. [| (snd ex)~=UU ; (snd ex)~=nil |] ==> (? ex'. TL`(ex2seq ex) = ex2seq ex')";
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
auto();
qed"TLex2seq";


goal thy "(TL`(ex2seq ex)~=UU) = ((snd ex)~=UU)";
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
by (Seq_case_simp_tac "s" 1);
by (pair_tac "a" 1);
qed"ex2seqUUTL";

goal thy "(TL`(ex2seq ex)~=nil) = ((snd ex)~=nil)";
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
by (Seq_case_simp_tac "s" 1);
by (pair_tac "a" 1);
qed"ex2seqnilTL";


goalw thy [temp_strengthening_def,state_strengthening_def,
temp_sat_def, satisfies_def,Next_def]
"!! h. [| temp_strengthening P Q h |]\
\      ==> temp_strengthening (Next P) (Next Q) h";
by (asm_full_simp_tac (simpset() setloop split_tac [expand_if]) 1);
by (safe_tac set_cs);
by (asm_full_simp_tac (simpset() addsimps [TL_ex2seq_nil,TL_ex2seq_UU]) 1);
by (asm_full_simp_tac (simpset() addsimps [TL_ex2seq_nil,TL_ex2seq_UU]) 1);
by (asm_full_simp_tac (simpset() addsimps [TL_ex2seq_nil,TL_ex2seq_UU]) 1);
by (asm_full_simp_tac (simpset() addsimps [TL_ex2seq_nil,TL_ex2seq_UU]) 1);
(* cons case *)
by (asm_full_simp_tac (simpset() addsimps [TL_ex2seq_nil,TL_ex2seq_UU,
        ex2seq_abs_cex,cex_absSeq_TL RS sym, ex2seqUUTL,ex2seqnilTL])1);
bd TLex2seq 1;
ba 1;
auto();
qed"strength_Next";



(* ---------------------------------------------------------------- *)
(*             Localizing Temporal Weakenings     - 2               *)
(* ---------------------------------------------------------------- *)


goal thy 
"!! h. [| state_weakening P Q h |]\
\      ==> temp_weakening (Init P) (Init Q) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2,
      state_weakening_def2, temp_sat_def,satisfies_def,Init_def,unlift_def])1);
by (safe_tac set_cs);
by (pair_tac "ex" 1);
by (Seq_case_simp_tac "y" 1);
by (pair_tac "a" 1);
qed"weak_Init";


(*

(* analog to strengthening thm above, with analog lemmas used  *)

goalw thy [state_weakening_def]
"!! h. [| temp_weakening P Q h |]\
\      ==> temp_weakening ([] P) ([] Q) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2,
         temp_sat_def,satisfies_def,Box_def])1);

(* analog to strengthening thm above, with analog lemmas used  *)

goalw thy [state_weakening_def]
"!! h. [| temp_weakening P Q h |]\
\      ==> temp_weakening (Next P) (Next Q) h";
by (asm_full_simp_tac (simpset() addsimps [temp_weakening_def2,
         temp_sat_def,satisfies_def,Next_def])1);

*)

(* ---------------------------------------------------------------- *)
(*             Localizing Temproal Strengthenings - 3               *)
(* ---------------------------------------------------------------- *)


goalw thy [Diamond_def]
"!! h. [| temp_strengthening P Q h |]\
\      ==> temp_strengthening (<> P) (<> Q) h";
br strength_NOT 1;
br weak_Box 1;
be weak_NOT 1;
qed"strength_Diamond";

goalw thy [Leadsto_def]
"!! h. [| temp_weakening P1 P2 h;\
\         temp_strengthening Q1 Q2 h |]\
\      ==> temp_strengthening (P1 ~> Q1) (P2 ~> Q2) h";
br strength_Box 1;
be strength_IMPLIES 1;
be strength_Diamond 1;
qed"strength_Leadsto";


(* ---------------------------------------------------------------- *)
(*             Localizing Temporal Weakenings - 3                   *)
(* ---------------------------------------------------------------- *)


goalw thy [Diamond_def]
"!! h. [| temp_weakening P Q h |]\
\      ==> temp_weakening (<> P) (<> Q) h";
br weak_NOT 1;
br strength_Box 1;
be strength_NOT 1;
qed"weak_Diamond";

goalw thy [Leadsto_def]
"!! h. [| temp_strengthening P1 P2 h;\
\         temp_weakening Q1 Q2 h |]\
\      ==> temp_weakening (P1 ~> Q1) (P2 ~> Q2) h";
br weak_Box 1;
be weak_IMPLIES 1;
be weak_Diamond 1;
qed"weak_Leadsto";

goalw thy [WF_def]
  " !!A. [| !! s. Enabled A acts (h s) ==> Enabled C acts s|] \ 
\   ==> temp_weakening (WF A acts) (WF C acts) h";
br weak_IMPLIES 1;
br strength_Diamond 1;
br strength_Box 1;
br strength_Init 1;
br weak_Box 2;
br weak_Diamond 2;
br weak_Init 2;
by (auto_tac (claset(),
              simpset() addsimps [state_weakening_def,state_strengthening_def,
                             xt2_def,plift_def,option_lift_def,NOT_def]));
qed"weak_WF";

goalw thy [SF_def]
  " !!A. [| !! s. Enabled A acts (h s) ==> Enabled C acts s|] \ 
\   ==> temp_weakening (SF A acts) (SF C acts) h";
br weak_IMPLIES 1;
br strength_Box 1;
br strength_Diamond 1;
br strength_Init 1;
br weak_Box 2;
br weak_Diamond 2;
br weak_Init 2;
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
