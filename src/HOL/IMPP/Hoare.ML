(*  Title:      HOL/IMPP/Hoare.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 TUM

Soundness and relative completeness of Hoare rules wrt operational semantics
*)

Goalw [state_not_singleton_def] 
	"state_not_singleton ==> !t. (!s::state. s = t) --> False";
by (Clarify_tac 1);
by (case_tac "ta = t" 1);
by  (ALLGOALS (blast_tac (HOL_cs addDs [not_sym])));
qed "single_stateE";

Addsimps[peek_and_def];


section "validity";

Goalw [triple_valid_def] 
  "|=n:{P}.c.{Q} = (!Z s. P Z s --> (!s'. <c,s> -n-> s' --> Q Z s'))";
by Auto_tac;
qed "triple_valid_def2";

Goal "|=0:{P}. BODY pn .{Q}";
by (simp_tac (simpset() addsimps [triple_valid_def2]) 1);
by (Clarsimp_tac 1);
qed "Body_triple_valid_0";

(* only ==> direction required *)
Goal "|=n:{P}. the (body pn) .{Q} = |=Suc n:{P}. BODY pn .{Q}";
by (simp_tac (simpset() addsimps [triple_valid_def2]) 1);
by (Force_tac 1);
qed "Body_triple_valid_Suc";

Goalw [triple_valid_def] "|=Suc n:t --> |=n:t";
by (induct_tac "t" 1);
by (Simp_tac 1);
by (fast_tac (claset() addIs [evaln_Suc]) 1);
qed_spec_mp "triple_valid_Suc";

Goal "||=Suc n:ts ==> ||=n:ts";
by (fast_tac (claset() addIs [triple_valid_Suc]) 1);
qed "triples_valid_Suc";


section "derived rules";

Goal "[| G|-{P'}.c.{Q'}; !Z s. P Z s --> \
\                        (!s'. (!Z'. P' Z' s --> Q' Z' s') --> Q Z s') |] \
\      ==> G|-{P}.c.{Q}";
by (rtac hoare_derivs.conseq 1);
by (Blast_tac 1);
qed "conseq12";

Goal "[| G|-{P'}.c.{Q}; !Z s. P Z s --> P' Z s |] ==> G|-{P}.c.{Q}";
by (etac conseq12 1);
by (Fast_tac 1);
qed "conseq1";

Goal "[| G|-{P}.c.{Q'}; !Z s. Q' Z s --> Q Z s |] ==> G|-{P}.c.{Q}";
by (etac conseq12 1);
by (Fast_tac 1);
qed "conseq2";

Goal "[| G Un (%p. {P p}.      BODY p  .{Q p})`Procs  \
\         ||- (%p. {P p}. the (body p) .{Q p})`Procs; \
\   pn:Procs |] ==> G|-{P pn}. BODY pn .{Q pn}";
by (dtac hoare_derivs.Body 1);
by (etac hoare_derivs.weaken 1);
by (Fast_tac 1);
qed "Body1";

Goal "(insert ({P}. BODY pn .{Q}) G) |-{P}. the (body pn) .{Q} ==> \
\ G|-{P}. BODY pn .{Q}";
by (rtac Body1 1);
by (rtac singletonI 2);
by (Clarsimp_tac 1);
qed "BodyN";

Goal "[| !Z s. P Z s --> G|-{%Z s'. s'=s}.c.{%Z'. Q Z} |] ==> G|-{P}.c.{Q}";
by (rtac hoare_derivs.conseq 1);
by (Fast_tac 1);
qed "escape";

Goal "[| C ==> G|-{P}.c.{Q} |] ==> G|-{%Z s. P Z s & C}.c.{Q}";
by (rtac hoare_derivs.conseq 1);
by (fast_tac (claset() addDs (premises())) 1);
qed "constant";

Goal "G|-{%Z s. P Z s & ~b s}.WHILE b DO c.{P}";
by (rtac (hoare_derivs.Loop RS conseq2) 1);
by  (ALLGOALS Simp_tac);
by (rtac hoare_derivs.conseq 1);
by (Fast_tac 1);
qed "LoopF";

(*
Goal "[| G'||-ts; G' <= G |] ==> G||-ts";
by (etac hoare_derivs.cut 1);
by (etac hoare_derivs.asm 1);
qed "thin";
*)
Goal "G'||-ts ==> !G. G' <= G --> G||-ts";
by (etac hoare_derivs.induct 1);
by                (ALLGOALS (EVERY'[Clarify_tac, REPEAT o smp_tac 1]));
by (rtac 		  hoare_derivs.empty 1);
by               (eatac hoare_derivs.insert 1 1);
by              (fast_tac (claset() addIs [hoare_derivs.asm]) 1);
by             (fast_tac (claset() addIs [hoare_derivs.cut]) 1);
by            (fast_tac (claset() addIs [hoare_derivs.weaken]) 1);
by           (EVERY'[rtac hoare_derivs.conseq, strip_tac, smp_tac 2,Clarify_tac,
	             smp_tac 1,rtac exI, rtac exI, eatac conjI 1] 1);
by          (EVERY'[rtac hoare_derivs.Body,dtac spec,etac mp,Fast_tac] 7); 
by         (ALLGOALS (resolve_tac ((funpow 5 tl) hoare_derivs.intrs)
	              THEN_ALL_NEW Fast_tac));
qed_spec_mp "thin";

Goal "G|-{P}. the (body pn) .{Q} ==> G|-{P}. BODY pn .{Q}";
by (rtac BodyN 1);
by (etac thin 1);
by Auto_tac;
qed "weak_Body";

Goal "G||-insert t ts ==> G|-t & G||-ts";
by (fast_tac (claset() addIs [hoare_derivs.weaken]) 1);
qed "derivs_insertD";

Goal "[| finite U; \
\ !p. G |-     {P' p}.c0 p.{Q' p}       --> G |-     {P p}.c0 p.{Q p} |] ==> \
\     G||-(%p. {P' p}.c0 p.{Q' p}) ` U --> G||-(%p. {P p}.c0 p.{Q p}) ` U";
by (etac finite_induct 1);
by (ALLGOALS Clarsimp_tac);
by (dtac derivs_insertD 1);
by (rtac hoare_derivs.insert 1);
by  Auto_tac;
qed_spec_mp "finite_pointwise";


section "soundness";

Goalw [hoare_valids_def]
 "G|={P &> b}. c .{P} ==> \
\ G|={P}. WHILE b DO c .{P &> (Not o b)}";
by (full_simp_tac (simpset() addsimps [triple_valid_def2]) 1);
by (rtac allI 1);
by (subgoal_tac "!d s s'. <d,s> -n-> s' --> \
\ d = WHILE b DO c --> ||=n:G --> (!Z. P Z s --> P Z s' & ~b s')" 1);
by  (EVERY'[etac thin_rl, Fast_tac] 1);
by (EVERY'[REPEAT o rtac allI, rtac impI] 1);
by ((etac evaln.induct THEN_ALL_NEW Simp_tac) 1);
by  (ALLGOALS Fast_tac);
qed "Loop_sound_lemma";

Goalw [hoare_valids_def]
   "[| G Un (%pn. {P pn}.      BODY pn  .{Q pn})`Procs \
\        ||=(%pn. {P pn}. the (body pn) .{Q pn})`Procs |] ==> \
\       G||=(%pn. {P pn}.      BODY pn  .{Q pn})`Procs";
by (rtac allI 1);
by (induct_tac "n" 1);
by  (fast_tac (claset() addIs [Body_triple_valid_0]) 1);
by (Clarsimp_tac 1);
by (dtac triples_valid_Suc 1);
by (mp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [ball_Un]) 1);
by (EVERY'[dtac spec, etac impE, etac conjI, atac] 1);
by (fast_tac (claset() addSIs [Body_triple_valid_Suc RS iffD1]) 1);
qed "Body_sound_lemma";

Goal "G||-ts ==> G||=ts";
by (etac hoare_derivs.induct 1);
by              (TRYALL (eresolve_tac [Loop_sound_lemma, Body_sound_lemma]
                         THEN_ALL_NEW atac));
by            (rewtac hoare_valids_def);
by            (Blast_tac 1);
by           (Blast_tac 1);
by          (Blast_tac 1); (* asm *)
by         (Blast_tac 1); (* cut *)
by        (Blast_tac 1); (* weaken *)
by       (ALLGOALS (EVERY'[REPEAT o thin_tac "?x : hoare_derivs", 
	                   Simp_tac, Clarify_tac, REPEAT o smp_tac 1]));
by       (ALLGOALS (full_simp_tac (simpset() addsimps [triple_valid_def2])));
by       (EVERY'[strip_tac, smp_tac 2, Blast_tac] 1); (* conseq *)
by      (ALLGOALS Clarsimp_tac); (* Skip, Ass, Local *)
by   (Force_tac 3); (* Call *)
by  (eresolve_tac evaln_elim_cases 2); (* If *)
by   (TRYALL Blast_tac);
qed "hoare_sound";


section "completeness";

(* Both versions *)

(*unused*)
Goalw [MGT_def] "G|-MGT c ==> \
\ G|-{%Z s0. !s1. <c,s0> -c-> s1 --> Z=s1}. c .{%Z s1. Z=s1}";
by (etac conseq12 1);
by Auto_tac;
qed "MGT_alternI";

(* requires com_det *)
Goalw [MGT_def] "state_not_singleton ==> \
\ G|-{%Z s0. !s1. <c,s0> -c-> s1 --> Z=s1}. c .{%Z s1. Z=s1} ==> G|-MGT c";
by (etac conseq12 1);
by Auto_tac;
by (case_tac "? t. <c,?s> -c-> t" 1);
by  (fast_tac (claset() addEs [com_det]) 1);
by (Clarsimp_tac 1);
by (dtac single_stateE 1);
by (Blast_tac 1);
qed "MGT_alternD";

Goalw [MGT_def] 
 "{}|-(MGT c::state triple) ==> {}|={P}.c.{Q} ==> {}|-{P}.c.{Q::state assn}";
by (etac conseq12 1);
by (clarsimp_tac (claset(), simpset() addsimps 
  [hoare_valids_def,eval_eq,triple_valid_def2]) 1);
qed "MGF_complete";

val WTs_elim_cases = map WTs.mk_cases
   ["WT SKIP", "WT (X:==a)", "WT (LOCAL Y:=a IN c)", 
    "WT (c1;;c2)","WT (IF b THEN c1 ELSE c2)", "WT (WHILE b DO c)",
    "WT (BODY P)", "WT (X:=CALL P(a))"];

AddSEs WTs_elim_cases;
(* requires com_det, escape (i.e. hoare_derivs.conseq) *)
Goal "state_not_singleton ==> \
\ !pn:dom body. G|-{=}.BODY pn.{->} ==> WT c --> G|-{=}.c.{->}";
by (induct_tac "c" 1);
by        (ALLGOALS Clarsimp_tac);
by        (fast_tac (claset() addIs [domI]) 7);
by (etac MGT_alternD 6);
by       (rewtac MGT_def);
by       (EVERY'[dtac bspec, etac domI] 7);
by       (EVERY'[rtac escape, Clarsimp_tac, res_inst_tac 
	     [("P1","%Z' s. s=(setlocs Z newlocs)[Loc Arg ::= fun Z]")]
	     (hoare_derivs.Call RS conseq1), etac conseq12] 7);
by        (ALLGOALS (etac thin_rl));
by (rtac (hoare_derivs.Skip RS conseq2) 1);
by (rtac (hoare_derivs.Ass RS conseq1) 2);
by        (EVERY'[rtac escape, Clarsimp_tac, res_inst_tac 
	          [("P1","%Z' s. s=(Z[Loc loc::=fun Z])")] 
		  (hoare_derivs.Local RS conseq1), etac conseq12] 3);
by         (EVERY'[etac hoare_derivs.Comp, etac conseq12] 5);
by         ((rtac hoare_derivs.If THEN_ALL_NEW etac conseq12) 6);
by          (EVERY'[rtac (hoare_derivs.Loop RS conseq2), etac conseq12] 8);
by           Auto_tac;
qed_spec_mp "MGF_lemma1";

(* Version: nested single recursion *)

Goal "[| !!G ts. ts <= G ==> P G ts;\
\ !!G pn. P (insert (mgt_call pn) G) {mgt(the(body pn))} ==> P G {mgt_call pn};\
\         !!G c. [| wt c; !pn:U. P G {mgt_call pn} |] ==> P G {mgt c}; \
\         !!pn. pn : U ==> wt (the (body pn)); \
\         finite U; uG = mgt_call`U |] ==> \
\ !G. G <= uG --> n <= card uG --> card G = card uG - n --> (!c. wt c --> P G {mgt c})";
by (cut_facts_tac (premises()) 1);
by (induct_tac "n" 1);
by  (ALLGOALS Clarsimp_tac);
by  (subgoal_tac "G = mgt_call ` U" 1);
by   (asm_simp_tac (simpset() addsimps [card_seteq, finite_imageI]) 2);
by  (Asm_full_simp_tac 1);
by  (eresolve_tac (tl(tl(premises()))(*MGF_lemma1*)) 1);
by (rtac ballI 1);
by  (resolve_tac (premises()(*hoare_derivs.asm*)) 1);
by  (Fast_tac 1);
by (eresolve_tac (tl(tl(premises()))(*MGF_lemma1*)) 1);
by (rtac ballI 1);
by (case_tac "mgt_call pn : G" 1);
by  (resolve_tac (premises()(*hoare_derivs.asm*)) 1);
by  (Fast_tac 1);
by (resolve_tac (tl(premises())(*MGT_BodyN*)) 1);
byev[dtac spec 1, etac impE 1, etac impE 2, dtac spec 3,etac mp 3];
by   (eresolve_tac (tl(tl(tl(premises())))) 3);
by   (Fast_tac 1);
by (dtac finite_subset 1);
by (etac finite_imageI 1);
by (Asm_simp_tac 1); 
by (arith_tac 1);
qed_spec_mp "nesting_lemma";

Goalw [MGT_def] "insert ({=}.BODY pn.{->}) G|-{=}. the (body pn) .{->} ==> \
\ G|-{=}.BODY pn.{->}";
by (rtac BodyN 1);
by (etac conseq2 1);
by (Force_tac 1);
qed "MGT_BodyN";

(* requires BodyN, com_det *)
Goal "[| state_not_singleton; WT_bodies; WT c |] ==> {}|-MGT c";
by (res_inst_tac [("P","%G ts. G||-ts"),("U","dom body")] nesting_lemma 1);
by (etac hoare_derivs.asm 1);
by (etac MGT_BodyN 1);
by (rtac finite_dom_body 3);
by (etac MGF_lemma1 1);
by (assume_tac 2);
by       (Blast_tac 1);
by      (Clarsimp_tac 1);
by     (eatac WT_bodiesD 1 1);
by (rtac le_refl 3);
by    Auto_tac;
qed "MGF";


(* Version: simultaneous recursion in call rule *)

(* finiteness not really necessary here *)
Goalw [MGT_def]     "[| G Un (%pn. {=}.      BODY pn  .{->})`Procs \
\                         ||-(%pn. {=}. the (body pn) .{->})`Procs; \
\ finite Procs |] ==>   G ||-(%pn. {=}.      BODY pn  .{->})`Procs";
by (rtac hoare_derivs.Body 1);
by (etac finite_pointwise 1);
by (assume_tac 2);
by (Clarify_tac 1);
by (etac conseq2 1);
by Auto_tac;
qed "MGT_Body";

(* requires empty, insert, com_det *)
Goal "[| state_not_singleton; WT_bodies; \
\ F<=(%pn. {=}.the (body pn).{->})`dom body |] ==> \
\    (%pn. {=}.     BODY pn .{->})`dom body||-F";
by (ftac finite_subset 1);
by (rtac (finite_dom_body RS finite_imageI) 1);
by (rotate_tac 2 1);
by (make_imp_tac 1);
by (etac finite_induct 1);
by  (ALLGOALS (clarsimp_tac (
	claset() addSIs [hoare_derivs.empty,hoare_derivs.insert],
	simpset() delsimps [range_composition])));
by (etac MGF_lemma1 1);
by  (fast_tac (claset() addDs [WT_bodiesD]) 2);
by (Clarsimp_tac 1);
by (rtac hoare_derivs.asm 1);
by (fast_tac (claset() addIs [domI]) 1);
qed_spec_mp "MGF_lemma2_simult";

(* requires Body, empty, insert, com_det *)
Goal "[| state_not_singleton; WT_bodies; WT c |] ==> {}|-MGT c";
by (rtac MGF_lemma1 1);
by (assume_tac 1);
by (assume_tac 2);
by (Clarsimp_tac 1);
by (subgoal_tac "{}||-(%pn. {=}. BODY pn .{->})`dom body" 1);
by (etac hoare_derivs.weaken 1);
by  (fast_tac (claset() addIs [domI]) 1);
by (rtac (finite_dom_body RSN (2,MGT_Body)) 1);
by (Simp_tac 1);
by (eatac MGF_lemma2_simult 1 1);
by (rtac subset_refl 1);
qed "MGF'";

(* requires Body+empty+insert / BodyN, com_det *)
bind_thm ("hoare_complete", MGF' RS MGF_complete); 

section "unused derived rules";

Goal "G|-{%Z s. False}.c.{Q}";
by (rtac hoare_derivs.conseq 1);
by (Fast_tac 1);
qed "falseE";

Goal "G|-{P}.c.{%Z s. True}";
by (rtac hoare_derivs.conseq 1);
by (fast_tac (claset() addSIs [falseE]) 1);
qed "trueI";

Goal "[| G|-{P}.c.{Q}; G|-{P'}.c.{Q'} |] \
\       ==> G|-{%Z s. P Z s | P' Z s}.c.{%Z s. Q Z s | Q' Z s}";
by (rtac hoare_derivs.conseq 1);
by (fast_tac (claset() addEs [conseq12]) 1);
qed "disj"; (* analogue conj non-derivable *)

Goal "(!Z s. P Z s --> Q Z s) ==> G|-{P}. SKIP .{Q}";
by (rtac conseq12 1);
by (rtac hoare_derivs.Skip 1);
by (Fast_tac 1);
qed "hoare_SkipI";


section "useful derived rules";

Goal "{t}|-t";
by (rtac hoare_derivs.asm 1);
by (rtac subset_refl 1);
qed "single_asm";

Goal "[| !!s'. G|-{%Z s. s'=s & P Z s}.c.{Q} |] ==> G|-{P}.c.{Q}";
by (rtac hoare_derivs.conseq 1);
by (Clarsimp_tac 1);
by (cut_facts_tac (premises()) 1);
by (Fast_tac 1);
qed "export_s";


Goal "[| G|-{P}. c .{Q}; !k Z s. Q Z s --> Q Z (s[Loc Y::=k]) |] ==> \
\   G|-{%Z s. P Z (s[Loc Y::=a s])}. LOCAL Y:=a IN c .{Q}";
by (rtac export_s 1);
by (rtac hoare_derivs.Local 1);
by (etac conseq2 1);
by (etac spec 1);
qed "weak_Local";

(*
Goal "!Q. G |-{%Z s. ~(? s'. <c,s> -c-> s')}. c .{Q}";
by (induct_tac "c" 1);
by Auto_tac;
by (rtac conseq1 1);
by (rtac hoare_derivs.Skip 1);
force 1;
by (rtac conseq1 1);
by (rtac hoare_derivs.Ass 1);
force 1;
by (defer_tac 1);
###
by (rtac hoare_derivs.Comp 1);
by (dtac spec 2);
by (dtac spec 2);
by (assume_tac 2);
by (etac conseq1 2);
by (Clarsimp_tac 2);
force 1;
*)
