(*  Title:      HOLCF/IOA/meta_theory/ShortExecutions.thy
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

Some properties about (Cut ex), defined as follows:

For every execution ex there is another shorter execution (Cut ex) 
that has the same trace as ex, but its schedule ends with an external action.

*) 




(* ---------------------------------------------------------------- *)
                   section "oraclebuild rewrite rules";
(* ---------------------------------------------------------------- *)


bind_thm ("oraclebuild_unfold", fix_prover2 thy oraclebuild_def 
"oraclebuild P = (LAM s t. case t of \
\       nil => nil\
\    | x##xs => \
\      (case x of\ 
\        Undef => UU\
\      | Def y => (Takewhile (%a.~ P a)`s)\
\                  @@ (y>>(oraclebuild P`(TL`(Dropwhile (%a.~ P a)`s))`xs))\
\      )\
\    )");

goal thy "oraclebuild P`sch`UU = UU";
by (stac oraclebuild_unfold 1);
by (Simp_tac 1);
qed"oraclebuild_UU";

goal thy "oraclebuild P`sch`nil = nil";
by (stac oraclebuild_unfold 1);
by (Simp_tac 1);
qed"oraclebuild_nil";

goal thy "oraclebuild P`s`(x>>t) = \
\         (Takewhile (%a.~ P a)`s)   \
\          @@ (x>>(oraclebuild P`(TL`(Dropwhile (%a.~ P a)`s))`t))";     
br trans 1;
by (stac oraclebuild_unfold 1);
by (asm_full_simp_tac (!simpset addsimps [Cons_def]) 1);
by (simp_tac (!simpset addsimps [Cons_def]) 1);
qed"oraclebuild_cons";



 
(* ---------------------------------------------------------------- *)
                   section "Cut rewrite rules";
(* ---------------------------------------------------------------- *)

goalw thy [Cut_def]
"!! s. [| Forall (%a.~ P a) s; Finite s|] \
\           ==> Cut P s =nil";
by (subgoal_tac "Filter P`s = nil" 1);
by (asm_simp_tac (!simpset addsimps [oraclebuild_nil]) 1);
br ForallQFilterPnil 1;
by (REPEAT (atac 1));
qed"Cut_nil";

goalw thy [Cut_def]
"!! s. [| Forall (%a.~ P a) s; ~Finite s|] \
\           ==> Cut P s =UU";
by (subgoal_tac "Filter P`s= UU" 1);
by (asm_simp_tac (!simpset addsimps [oraclebuild_UU]) 1);
br ForallQFilterPUU 1;
by (REPEAT (atac 1));
qed"Cut_UU";

goalw thy [Cut_def]
"!! s. [| P t;  Forall (%x.~ P x) ss; Finite ss|] \
\           ==> Cut P (ss @@ (t>> rs)) \
\                = ss @@ (t >> Cut P rs)";

by (asm_full_simp_tac (!simpset addsimps [ForallQFilterPnil,oraclebuild_cons,
          TakewhileConc,DropwhileConc]) 1);
qed"Cut_Cons";


(* ---------------------------------------------------------------- *)
                   section "Cut lemmas for main theorem";
(* ---------------------------------------------------------------- *)


goal thy "Filter P`s = Filter P`(Cut P s)";

by (res_inst_tac [("A1","%x.True")
                 ,("Q1","%x.~ P x"), ("x1","s")]
                 (take_lemma_induct RS mp) 1);
by (Fast_tac 3);
by (case_tac "Finite s" 1);
by (asm_full_simp_tac (!simpset addsimps [Cut_nil,
             ForallQFilterPnil]) 1);
by (asm_full_simp_tac (!simpset addsimps [Cut_UU,
             ForallQFilterPUU]) 1);
(* main case *)
by (asm_full_simp_tac (!simpset addsimps [Cut_Cons,ForallQFilterPnil]) 1);
auto();
qed"FilterCut";


goal thy "Cut P (Cut P s) = (Cut P s)";

by (res_inst_tac [("A1","%x.True")
                 ,("Q1","%x.~ P x"), ("x1","s")]
                 (take_lemma_less_induct RS mp) 1);
by (Fast_tac 3);
by (case_tac "Finite s" 1);
by (asm_full_simp_tac (!simpset addsimps [Cut_nil,
             ForallQFilterPnil]) 1);
by (asm_full_simp_tac (!simpset addsimps [Cut_UU,
             ForallQFilterPUU]) 1);
(* main case *)
by (asm_full_simp_tac (!simpset addsimps [Cut_Cons,ForallQFilterPnil]) 1);
br take_reduction 1;
auto();
qed"Cut_idemp";


goal thy "Map f`(Cut (P o f) s) = Cut P (Map f`s)";

by (res_inst_tac [("A1","%x.True")
                 ,("Q1","%x.~ P (f x)"), ("x1","s")]
                 (take_lemma_less_induct RS mp) 1);
by (Fast_tac 3);
by (case_tac "Finite s" 1);
by (asm_full_simp_tac (!simpset addsimps [Cut_nil]) 1); 
br (Cut_nil RS sym) 1;
by (asm_full_simp_tac (!simpset addsimps [ForallMap,o_def]) 1); 
by (asm_full_simp_tac (!simpset addsimps [Map2Finite]) 1);
(* csae ~ Finite s *)
by (asm_full_simp_tac (!simpset addsimps [Cut_UU]) 1);
br (Cut_UU RS sym) 1;
by (asm_full_simp_tac (!simpset addsimps [ForallMap,o_def]) 1); 
by (asm_full_simp_tac (!simpset addsimps [Map2Finite]) 1);
(* main case *)
by (asm_full_simp_tac (!simpset addsimps [Cut_Cons,MapConc,
          ForallMap,FiniteMap1,o_def]) 1);
br take_reduction 1;
auto();
qed"MapCut";




(* ---------------------------------------------------------------- *)
                   section "Main Cut Theorem";
(* ---------------------------------------------------------------- *)



goalw thy [schedules_def,has_schedule_def]
 "!! sch. [|sch : schedules A ; tr = Filter (%a.a:ext A)`sch|] \
\   ==> ? sch. sch : schedules A & \
\              tr = Filter (%a.a:ext A)`sch &\
\              LastActExtsch A sch";

by (safe_tac set_cs);
by (res_inst_tac [("x","filter_act`(Cut (%a.fst a:ext A) (snd ex))")] exI 1);
by (asm_full_simp_tac (!simpset addsimps [executions_def]) 1);
by (pair_tac "ex" 1);
by (safe_tac set_cs);
by (res_inst_tac [("x","(x,Cut (%a.fst a:ext A) y)")] exI 1);
by (Asm_simp_tac 1);

(* Subgoal 1: Lemma:  propagation of execution through Cut *)

by (asm_full_simp_tac (!simpset addsimps [execThruCut]) 1);

(* Subgoal 2:  Lemma:  Filter P s = Filter P (Cut P s) *)

by (simp_tac (!simpset addsimps [filter_act_def]) 1);
by (subgoal_tac "Map fst`(Cut (%a.fst a: ext A) y)= Cut (%a.a:ext A) (Map fst`y)" 1);
br (rewrite_rule [o_def] MapCut) 2;
by (asm_full_simp_tac (!simpset addsimps [FilterCut RS sym]) 1);

(* Subgoal 3: Lemma: Cut idempotent  *)

by (simp_tac (!simpset addsimps [LastActExtsch_def,filter_act_def]) 1);
by (subgoal_tac "Map fst`(Cut (%a.fst a: ext A) y)= Cut (%a.a:ext A) (Map fst`y)" 1);
br (rewrite_rule [o_def] MapCut) 2;
by (asm_full_simp_tac (!simpset addsimps [Cut_idemp]) 1);
qed"exists_LastActExtsch";


(* ---------------------------------------------------------------- *)
                   section "Further Cut lemmas";
(* ---------------------------------------------------------------- *)

goalw  thy [LastActExtsch_def]
  "!! A. [| LastActExtsch A sch; Filter (%x.x:ext A)`sch = nil |] \
\   ==> sch=nil";
bd FilternPnilForallP 1;
be conjE 1;
bd Cut_nil 1;
ba 1;
by (Asm_full_simp_tac 1);
qed"LastActExtimplnil";

goalw  thy [LastActExtsch_def]
  "!! A. [| LastActExtsch A sch; Filter (%x.x:ext A)`sch = UU |] \
\   ==> sch=UU";
bd FilternPUUForallP 1;
be conjE 1;
bd Cut_UU 1;
ba 1;
by (Asm_full_simp_tac 1);
qed"LastActExtimplUU";
