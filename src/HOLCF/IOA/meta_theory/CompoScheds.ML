(*  Title:      HOLCF/IOA/meta_theory/CompoScheds.ML
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen

Compositionality on Schedule level.
*) 



Addsimps [surjective_pairing RS sym];



(* ------------------------------------------------------------------------------- *)

section "mkex rewrite rules";

(* ---------------------------------------------------------------- *)
(*                             mkex2                                *)
(* ---------------------------------------------------------------- *)


bind_thm ("mkex2_unfold", fix_prover2 thy mkex2_def 
"mkex2 A B = (LAM sch exA exB. (%s t. case sch of  \
\      nil => nil \
\   | x##xs => \
\     (case x of  \
\       Undef => UU   \
\     | Def y =>  \
\        (if y:act A then \
\            (if y:act B then \
\               (case HD$exA of \
\                  Undef => UU \
\                | Def a => (case HD$exB of \
\                             Undef => UU \
\                           | Def b => \
\                  (y,(snd a,snd b))>>  \
\                    (mkex2 A B$xs$(TL$exA)$(TL$exB)) (snd a) (snd b)))  \
\             else   \
\               (case HD$exA of   \
\                  Undef => UU  \
\                | Def a => \
\                  (y,(snd a,t))>>(mkex2 A B$xs$(TL$exA)$exB) (snd a) t)  \
\             )  \       
\         else   \
\            (if y:act B then \
\               (case HD$exB of  \
\                  Undef => UU  \
\                | Def b =>  \
\                  (y,(s,snd b))>>(mkex2 A B$xs$exA$(TL$exB)) s (snd b))  \
\            else  \
\              UU  \
\            )  \
\        )  \
\      )))");


Goal "(mkex2 A B$UU$exA$exB) s t = UU";
by (stac mkex2_unfold 1);
by (Simp_tac 1);
qed"mkex2_UU";

Goal "(mkex2 A B$nil$exA$exB) s t= nil";
by (stac mkex2_unfold 1);
by (Simp_tac 1);
qed"mkex2_nil";

Goal "[| x:act A; x~:act B; HD$exA=Def a|] \
\   ==> (mkex2 A B$(x>>sch)$exA$exB) s t =   \
\       (x,snd a,t) >> (mkex2 A B$sch$(TL$exA)$exB) (snd a) t";
by (rtac trans 1);
by (stac mkex2_unfold 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def,If_and_if]) 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def]) 1);
qed"mkex2_cons_1";

Goal "[| x~:act A; x:act B; HD$exB=Def b|] \
\   ==> (mkex2 A B$(x>>sch)$exA$exB) s t = \
\       (x,s,snd b) >> (mkex2 A B$sch$exA$(TL$exB)) s (snd b)";
by (rtac trans 1);
by (stac mkex2_unfold 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def,If_and_if]) 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def]) 1);
qed"mkex2_cons_2";

Goal "[| x:act A; x:act B; HD$exA=Def a;HD$exB=Def b|] \
\   ==> (mkex2 A B$(x>>sch)$exA$exB) s t =  \
\        (x,snd a,snd b) >> \
\           (mkex2 A B$sch$(TL$exA)$(TL$exB)) (snd a) (snd b)";
by (rtac trans 1);
by (stac mkex2_unfold 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def,If_and_if]) 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def]) 1);
qed"mkex2_cons_3";

Addsimps [mkex2_UU,mkex2_nil,mkex2_cons_1,mkex2_cons_2,mkex2_cons_3];


(* ---------------------------------------------------------------- *)
(*                             mkex                                 *)
(* ---------------------------------------------------------------- *)

Goal "mkex A B UU  (s,exA) (t,exB) = ((s,t),UU)";
by (simp_tac (simpset() addsimps [mkex_def]) 1);
qed"mkex_UU";

Goal "mkex A B nil (s,exA) (t,exB) = ((s,t),nil)";
by (simp_tac (simpset() addsimps [mkex_def]) 1);
qed"mkex_nil";

Goal "[| x:act A; x~:act B |] \
\   ==> mkex A B (x>>sch) (s,a>>exA) (t,exB)  =  \
\       ((s,t), (x,snd a,t) >> snd (mkex A B sch (snd a,exA) (t,exB)))";
by (simp_tac (simpset() addsimps [mkex_def]) 1);
by (cut_inst_tac [("exA","a>>exA")] mkex2_cons_1 1);
by Auto_tac;
qed"mkex_cons_1";

Goal "[| x~:act A; x:act B |] \
\   ==> mkex A B (x>>sch) (s,exA) (t,b>>exB) =  \ 
\       ((s,t), (x,s,snd b) >> snd (mkex A B sch (s,exA) (snd b,exB)))";
by (simp_tac (simpset() addsimps [mkex_def]) 1);
by (cut_inst_tac [("exB","b>>exB")] mkex2_cons_2 1);
by Auto_tac;
qed"mkex_cons_2";

Goal "[| x:act A; x:act B |]  \
\   ==>  mkex A B (x>>sch) (s,a>>exA) (t,b>>exB) = \
\        ((s,t), (x,snd a,snd b) >> snd (mkex A B sch (snd a,exA) (snd b,exB)))";
by (simp_tac (simpset() addsimps [mkex_def]) 1);
by (cut_inst_tac [("exB","b>>exB"),("exA","a>>exA")] mkex2_cons_3 1);
by Auto_tac;
qed"mkex_cons_3";

Delsimps [mkex2_UU,mkex2_nil,mkex2_cons_1,mkex2_cons_2,mkex2_cons_3];

val composch_simps = [mkex_UU,mkex_nil,
                      mkex_cons_1,mkex_cons_2,mkex_cons_3];

Addsimps composch_simps;



(* ------------------------------------------------------------------ *)
(*                      The following lemmata aim for                 *)
(*             COMPOSITIONALITY   on    SCHEDULE     Level            *)
(* ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------- *)
             section   "Lemmas for ==>";
(* ----------------------------------------------------------------------*)

(* --------------------------------------------------------------------- *)
(*    Lemma_2_1 :  tfilter(ex) and filter_act are commutative            *)
(* --------------------------------------------------------------------- *)

Goalw [filter_act_def,Filter_ex2_def]
   "filter_act$(Filter_ex2 (asig_of A)$xs)=\
\   Filter (%a. a:act A)$(filter_act$xs)";

by (simp_tac (simpset() addsimps [MapFilter,o_def]) 1);
qed"lemma_2_1a";


(* --------------------------------------------------------------------- *)
(*    Lemma_2_2 : State-projections do not affect filter_act             *)
(* --------------------------------------------------------------------- *)

Goal 
   "filter_act$(ProjA2$xs) =filter_act$xs &\
\   filter_act$(ProjB2$xs) =filter_act$xs";

by (pair_induct_tac "xs" [] 1);
qed"lemma_2_1b";


(* --------------------------------------------------------------------- *)
(*             Schedules of A||B have only  A- or B-actions              *)
(* --------------------------------------------------------------------- *)

(* very similar to lemma_1_1c, but it is not checking if every action element of 
   an ex is in A or B, but after projecting it onto the action schedule. Of course, this
   is the same proposition, but we cannot change this one, when then rather lemma_1_1c  *)

Goal "!s. is_exec_frag (A||B) (s,xs) \
\  --> Forall (%x. x:act (A||B)) (filter_act$xs)";

by (pair_induct_tac "xs" [is_exec_frag_def,Forall_def,sforall_def] 1);
(* main case *)
by (safe_tac set_cs);
by (REPEAT (asm_full_simp_tac (simpset() addsimps trans_of_defs2 @ 
                                [actions_asig_comp,asig_of_par]) 1));
qed"sch_actions_in_AorB";


(* --------------------------------------------------------------------------*)
                 section "Lemmas for <=="; 
(* ---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
    Filtering actions out of mkex(sch,exA,exB) yields the oracle sch
                             structural induction
  --------------------------------------------------------------------------- *)

Goal "! exA exB s t. \
\ Forall (%x. x:act (A||B)) sch  & \
\ Filter (%a. a:act A)$sch << filter_act$exA &\
\ Filter (%a. a:act B)$sch << filter_act$exB \
\ --> filter_act$(snd (mkex A B sch (s,exA) (t,exB))) = sch";

by (Seq_induct_tac "sch" [Filter_def,Forall_def,sforall_def,mkex_def] 1);

(* main case *) 
(* splitting into 4 cases according to a:A, a:B *)
by (Asm_full_simp_tac 1);
by (safe_tac set_cs);

(* Case y:A, y:B *)
by (Seq_case_simp_tac "exA" 1);
(* Case exA=UU, Case exA=nil*)
(* These UU and nil cases are the only places where the assumption filter A sch<<f_act exA 
   is used! --> to generate a contradiction using  ~a>>ss<< UU(nil), using theorems 
   Cons_not_less_UU and Cons_not_less_nil  *)
by (Seq_case_simp_tac "exB" 1);
(* Case exA=a>>x, exB=b>>y *)
(* here it is important that Seq_case_simp_tac uses no !full!_simp_tac for the cons case, 
   as otherwise mkex_cons_3 would  not be rewritten without use of rotate_tac: then tactic 
   would not be generally applicable *)
by (Asm_full_simp_tac 1);

(* Case y:A, y~:B *)
by (Seq_case_simp_tac "exA" 1);
by (Asm_full_simp_tac 1);

(* Case y~:A, y:B *)
by (Seq_case_simp_tac "exB" 1);
by (Asm_full_simp_tac 1);

(* Case y~:A, y~:B *)
by (asm_full_simp_tac (simpset() addsimps [asig_of_par,actions_asig_comp]) 1);
qed"Mapfst_mkex_is_sch";


(* generalizing the proof above to a tactic *)

fun mkex_induct_tac sch exA exB = 
    EVERY1[Seq_induct_tac sch [Filter_def,Forall_def,sforall_def,mkex_def,stutter_def], 
           Asm_full_simp_tac,
           SELECT_GOAL (safe_tac set_cs),
           Seq_case_simp_tac exA,
           Seq_case_simp_tac exB,
           Asm_full_simp_tac,
           Seq_case_simp_tac exA,
           Asm_full_simp_tac,
           Seq_case_simp_tac exB,
           Asm_full_simp_tac,
           asm_full_simp_tac (simpset() addsimps [asig_of_par,actions_asig_comp])
          ];



(*---------------------------------------------------------------------------
               Projection of mkex(sch,exA,exB) onto A stutters on A
                             structural induction
  --------------------------------------------------------------------------- *)


Goal "! exA exB s t. \
\ Forall (%x. x:act (A||B)) sch & \
\ Filter (%a. a:act A)$sch << filter_act$exA &\
\ Filter (%a. a:act B)$sch << filter_act$exB \
\ --> stutter (asig_of A) (s,ProjA2$(snd (mkex A B sch (s,exA) (t,exB))))";

by (mkex_induct_tac "sch" "exA" "exB");

qed"stutterA_mkex";


Goal "[|  \
\ Forall (%x. x:act (A||B)) sch ; \
\ Filter (%a. a:act A)$sch << filter_act$(snd exA) ;\
\ Filter (%a. a:act B)$sch << filter_act$(snd exB) |] \
\ ==> stutter (asig_of A) (ProjA (mkex A B sch exA exB))";

by (cut_facts_tac [stutterA_mkex] 1);
by (asm_full_simp_tac (simpset() addsimps [stutter_def,ProjA_def,mkex_def]) 1);
by (REPEAT (etac allE 1));
by (dtac mp 1);
by (assume_tac 2);
by (Asm_full_simp_tac 1);
qed"stutter_mkex_on_A";


(*---------------------------------------------------------------------------
               Projection of mkex(sch,exA,exB) onto B stutters on B
                             structural induction
  --------------------------------------------------------------------------- *)

Goal "! exA exB s t. \
\ Forall (%x. x:act (A||B)) sch & \
\ Filter (%a. a:act A)$sch << filter_act$exA &\
\ Filter (%a. a:act B)$sch << filter_act$exB \
\ --> stutter (asig_of B) (t,ProjB2$(snd (mkex A B sch (s,exA) (t,exB))))";

by (mkex_induct_tac "sch" "exA" "exB");

qed"stutterB_mkex";


Goal "[|  \
\ Forall (%x. x:act (A||B)) sch ; \
\ Filter (%a. a:act A)$sch << filter_act$(snd exA) ;\
\ Filter (%a. a:act B)$sch << filter_act$(snd exB) |] \
\ ==> stutter (asig_of B) (ProjB (mkex A B sch exA exB))";

by (cut_facts_tac [stutterB_mkex] 1);
by (asm_full_simp_tac (simpset() addsimps [stutter_def,ProjB_def,mkex_def]) 1);
by (REPEAT (etac allE 1));
by (dtac mp 1);
by (assume_tac 2);
by (Asm_full_simp_tac 1);
qed"stutter_mkex_on_B";


(*---------------------------------------------------------------------------
     Filter of mkex(sch,exA,exB) to A after projection onto A is exA 
        --  using zip$(proj1$exA)$(proj2$exA) instead of exA    --
        --           because of admissibility problems          --
                             structural induction
  --------------------------------------------------------------------------- *)

Goal "! exA exB s t. \
\ Forall (%x. x:act (A||B)) sch & \
\ Filter (%a. a:act A)$sch << filter_act$exA  &\
\ Filter (%a. a:act B)$sch << filter_act$exB \
\ --> Filter_ex2 (asig_of A)$(ProjA2$(snd (mkex A B sch (s,exA) (t,exB)))) =   \
\     Zip$(Filter (%a. a:act A)$sch)$(Map snd$exA)";

by (mkex_induct_tac "sch" "exB" "exA");

qed"filter_mkex_is_exA_tmp";

(*---------------------------------------------------------------------------
                      zip$(proj1$y)$(proj2$y) = y   (using the lift operations)
                    lemma for admissibility problems         
  --------------------------------------------------------------------------- *)

Goal  "Zip$(Map fst$y)$(Map snd$y) = y";
by (Seq_induct_tac "y" [] 1);
qed"Zip_Map_fst_snd";


(*---------------------------------------------------------------------------
      filter A$sch = proj1$ex   -->  zip$(filter A$sch)$(proj2$ex) = ex 
         lemma for eliminating non admissible equations in assumptions      
  --------------------------------------------------------------------------- *)

Goal "!! sch ex. \
\ Filter (%a. a:act AB)$sch = filter_act$ex  \
\ ==> ex = Zip$(Filter (%a. a:act AB)$sch)$(Map snd$ex)";
by (asm_full_simp_tac (simpset() addsimps [filter_act_def]) 1);
by (rtac (Zip_Map_fst_snd RS sym) 1);
qed"trick_against_eq_in_ass";

(*---------------------------------------------------------------------------
     Filter of mkex(sch,exA,exB) to A after projection onto A is exA 
                       using the above trick
  --------------------------------------------------------------------------- *)


Goal "!!sch exA exB.\
\ [| Forall (%a. a:act (A||B)) sch ; \
\ Filter (%a. a:act A)$sch = filter_act$(snd exA)  ;\
\ Filter (%a. a:act B)$sch = filter_act$(snd exB) |]\
\ ==> Filter_ex (asig_of A) (ProjA (mkex A B sch exA exB)) = exA";
by (asm_full_simp_tac (simpset() addsimps [ProjA_def,Filter_ex_def]) 1);
by (pair_tac "exA" 1);
by (pair_tac "exB" 1);
by (rtac conjI 1);
by (simp_tac (simpset() addsimps [mkex_def]) 1);
by (stac trick_against_eq_in_ass 1);
back();
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [filter_mkex_is_exA_tmp]) 1);
qed"filter_mkex_is_exA";
 

(*---------------------------------------------------------------------------
     Filter of mkex(sch,exA,exB) to B after projection onto B is exB 
        --  using zip$(proj1$exB)$(proj2$exB) instead of exB    --
        --           because of admissibility problems          --
                             structural induction
  --------------------------------------------------------------------------- *)


Goal "! exA exB s t. \
\ Forall (%x. x:act (A||B)) sch & \
\ Filter (%a. a:act A)$sch << filter_act$exA  &\
\ Filter (%a. a:act B)$sch << filter_act$exB \
\ --> Filter_ex2 (asig_of B)$(ProjB2$(snd (mkex A B sch (s,exA) (t,exB)))) =   \
\     Zip$(Filter (%a. a:act B)$sch)$(Map snd$exB)";

(* notice necessary change of arguments exA and exB *)
by (mkex_induct_tac "sch" "exA" "exB");

qed"filter_mkex_is_exB_tmp";


(*---------------------------------------------------------------------------
     Filter of mkex(sch,exA,exB) to A after projection onto B is exB 
                       using the above trick
  --------------------------------------------------------------------------- *)


Goal "!!sch exA exB.\
\ [| Forall (%a. a:act (A||B)) sch ; \
\ Filter (%a. a:act A)$sch = filter_act$(snd exA)  ;\
\ Filter (%a. a:act B)$sch = filter_act$(snd exB) |]\
\ ==> Filter_ex (asig_of B) (ProjB (mkex A B sch exA exB)) = exB";
by (asm_full_simp_tac (simpset() addsimps [ProjB_def,Filter_ex_def]) 1);
by (pair_tac "exA" 1);
by (pair_tac "exB" 1);
by (rtac conjI 1);
by (simp_tac (simpset() addsimps [mkex_def]) 1);
by (stac trick_against_eq_in_ass 1);
back();
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [filter_mkex_is_exB_tmp]) 1);
qed"filter_mkex_is_exB";

(* --------------------------------------------------------------------- *)
(*                    mkex has only  A- or B-actions                    *)
(* --------------------------------------------------------------------- *)


Goal "!s t exA exB. \
\ Forall (%x. x : act (A || B)) sch &\
\ Filter (%a. a:act A)$sch << filter_act$exA  &\
\ Filter (%a. a:act B)$sch << filter_act$exB \
\  --> Forall (%x. fst x : act (A ||B))   \
\        (snd (mkex A B sch (s,exA) (t,exB)))";

by (mkex_induct_tac "sch" "exA" "exB");

qed"mkex_actions_in_AorB";


(* ------------------------------------------------------------------ *)
(*           COMPOSITIONALITY   on    SCHEDULE      Level             *)
(*                          Main Theorem                              *)
(* ------------------------------------------------------------------ *)

Goal  
"sch : schedules (A||B) = \
\ (Filter (%a. a:act A)$sch : schedules A &\
\  Filter (%a. a:act B)$sch : schedules B &\
\  Forall (%x. x:act (A||B)) sch)";

by (simp_tac (simpset() addsimps [schedules_def, has_schedule_def]) 1);
by (safe_tac set_cs); 
(* ==> *) 
by (res_inst_tac [("x","Filter_ex (asig_of A) (ProjA ex)")] bexI 1);
by (asm_full_simp_tac (simpset() addsimps [compositionality_ex]) 2);
by (simp_tac (simpset() addsimps [Filter_ex_def,ProjA_def,
                                 lemma_2_1a,lemma_2_1b]) 1); 
by (res_inst_tac [("x","Filter_ex (asig_of B) (ProjB ex)")] bexI 1);
by (asm_full_simp_tac (simpset() addsimps [compositionality_ex]) 2);
by (simp_tac (simpset() addsimps [Filter_ex_def,ProjB_def,
                                 lemma_2_1a,lemma_2_1b]) 1);
by (asm_full_simp_tac (simpset() addsimps [executions_def]) 1);
by (pair_tac "ex" 1);
by (etac conjE 1);
by (asm_full_simp_tac (simpset() addsimps [sch_actions_in_AorB]) 1);

(* <== *)

(* mkex is exactly the construction of exA||B out of exA, exB, and the oracle sch,
   we need here *)
ren "exA exB" 1;
by (res_inst_tac [("x","mkex A B sch exA exB")] bexI 1);
(* mkex actions are just the oracle *)
by (pair_tac "exA" 1);
by (pair_tac "exB" 1);
by (asm_full_simp_tac (simpset() addsimps [Mapfst_mkex_is_sch]) 1);

(* mkex is an execution -- use compositionality on ex-level *)
by (asm_full_simp_tac (simpset() addsimps [compositionality_ex]) 1);
by (asm_full_simp_tac (simpset() addsimps 
                 [stutter_mkex_on_A, stutter_mkex_on_B,
                  filter_mkex_is_exB,filter_mkex_is_exA]) 1);
by (pair_tac "exA" 1);
by (pair_tac "exB" 1);
by (asm_full_simp_tac (simpset() addsimps [mkex_actions_in_AorB]) 1);
qed"compositionality_sch";


(* ------------------------------------------------------------------ *)
(*           COMPOSITIONALITY   on    SCHEDULE      Level             *)
(*                            For Modules                             *)
(* ------------------------------------------------------------------ *)

Goalw [Scheds_def,par_scheds_def]

"Scheds (A||B) = par_scheds (Scheds A) (Scheds B)";

by (asm_full_simp_tac (simpset() addsimps [asig_of_par]) 1);
by (rtac set_ext 1);
by (asm_full_simp_tac (simpset() addsimps [compositionality_sch,actions_of_par]) 1);
qed"compositionality_sch_modules";


Delsimps compoex_simps;
Delsimps composch_simps;
