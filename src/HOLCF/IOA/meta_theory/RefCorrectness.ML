(*  Title:      HOLCF/IOA/meta_theory/RefCorrectness.ML
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1996  TU Muenchen

Correctness of Refinement Mappings in HOLCF/IOA
*)



(* -------------------------------------------------------------------------------- *)

section "corresp_ex";


(* ---------------------------------------------------------------- *)
(*                             corresp_exC                          *)
(* ---------------------------------------------------------------- *)


goal thy "corresp_exC A f  = (LAM ex. (%s. case ex of \
\      nil =>  nil   \
\    | x##xs => (flift1 (%pr. (@cex. move A cex (f s) (fst pr) (f (snd pr)))   \
\                              @@ ((corresp_exC A f `xs) (snd pr)))   \
\                        `x) ))";
by (rtac trans 1);
by (rtac fix_eq2 1);
by (rtac corresp_exC_def 1);
by (rtac beta_cfun 1);
by (simp_tac (simpset() addsimps [flift1_def]) 1);
qed"corresp_exC_unfold";

goal thy "(corresp_exC A f`UU) s=UU";
by (stac corresp_exC_unfold 1);
by (Simp_tac 1);
qed"corresp_exC_UU";

goal thy "(corresp_exC A f`nil) s = nil";
by (stac corresp_exC_unfold 1);
by (Simp_tac 1);
qed"corresp_exC_nil";

goal thy "(corresp_exC A f`(at>>xs)) s = \
\          (@cex. move A cex (f s) (fst at) (f (snd at)))  \
\          @@ ((corresp_exC A f`xs) (snd at))";
by (rtac trans 1);
by (stac corresp_exC_unfold 1);
by (asm_full_simp_tac (simpset() addsimps [Cons_def,flift1_def]) 1);
by (Simp_tac 1);
qed"corresp_exC_cons";


Addsimps [corresp_exC_UU,corresp_exC_nil,corresp_exC_cons];



(* ------------------------------------------------------------------ *)
(*               The following lemmata describe the definition        *)
(*                         of move in more detail                     *)
(* ------------------------------------------------------------------ *)

section"properties of move";

goalw thy [is_ref_map_def]
   "!!f. [|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==>\
\     move A (@x. move A x (f s) a (f t)) (f s) a (f t)";

by (subgoal_tac "? ex. move A ex (f s) a (f t)" 1);
by (Asm_full_simp_tac 2);
by (etac exE 1);
by (rtac selectI 1);
by (assume_tac 1);
qed"move_is_move";

goal thy
   "!!f. [|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==>\
\    is_exec_frag A (f s,@x. move A x (f s) a (f t))";
by (cut_inst_tac [] move_is_move 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (simpset() addsimps [move_def]) 1);
qed"move_subprop1";

goal thy
   "!!f. [|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==>\
\    Finite ((@x. move A x (f s) a (f t)))";
by (cut_inst_tac [] move_is_move 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (simpset() addsimps [move_def]) 1);
qed"move_subprop2";

goal thy
   "!!f. [|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==>\
\    laststate (f s,@x. move A x (f s) a (f t)) = (f t)";
by (cut_inst_tac [] move_is_move 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (simpset() addsimps [move_def]) 1);
qed"move_subprop3";

goal thy
   "!!f. [|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==>\
\     mk_trace A`((@x. move A x (f s) a (f t))) = \
\       (if a:ext A then a>>nil else nil)";

by (cut_inst_tac [] move_is_move 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (simpset() addsimps [move_def]) 1);
qed"move_subprop4";


(* ------------------------------------------------------------------ *)
(*                   The following lemmata contribute to              *)
(*                 TRACE INCLUSION Part 1: Traces coincide            *)
(* ------------------------------------------------------------------ *)

section "Lemmata for <==";

(* --------------------------------------------------- *)
(*   Lemma 1.1: Distribution of mk_trace and @@        *)
(* --------------------------------------------------- *)


goal thy "mk_trace C`(ex1 @@ ex2)= (mk_trace C`ex1) @@ (mk_trace C`ex2)";
by (simp_tac (simpset() addsimps [mk_trace_def,filter_act_def,
                                 FilterConc,MapConc]) 1);
qed"mk_traceConc";



(* ------------------------------------------------------
                 Lemma 1 :Traces coincide  
   ------------------------------------------------------- *)
Delsplits[split_if];
goalw thy [corresp_ex_def]
  "!!f.[|is_ref_map f C A; ext C = ext A|] ==>  \     
\        !s. reachable C s & is_exec_frag C (s,xs) --> \
\            mk_trace C`xs = mk_trace A`(snd (corresp_ex A f (s,xs)))";

by (pair_induct_tac "xs" [is_exec_frag_def] 1);
(* cons case *) 
by (safe_tac set_cs);
by (asm_full_simp_tac (simpset() addsimps [mk_traceConc]) 1);
by (forward_tac [reachable.reachable_n] 1);
by (assume_tac 1);
by (eres_inst_tac [("x","y")] allE 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [move_subprop4] 
                          addsplits [split_if]) 1);
qed"lemma_1";
Addsplits[split_if];

(* ------------------------------------------------------------------ *)
(*                   The following lemmata contribute to              *)
(*              TRACE INCLUSION Part 2: corresp_ex is execution       *)
(* ------------------------------------------------------------------ *)

section "Lemmata for ==>";

(* -------------------------------------------------- *)
(*                   Lemma 2.1                        *)
(* -------------------------------------------------- *)

goal thy 
"Finite xs --> \
\(!s .is_exec_frag A (s,xs) & is_exec_frag A (t,ys) & \ 
\     t = laststate (s,xs) \
\ --> is_exec_frag A (s,xs @@ ys))";

by (rtac impI 1);
by (Seq_Finite_induct_tac 1);
(* main case *)
by (safe_tac set_cs);
by (pair_tac "a" 1);
qed_spec_mp"lemma_2_1";


(* ----------------------------------------------------------- *)
(*               Lemma 2 : corresp_ex is execution             *)
(* ----------------------------------------------------------- *)



goalw thy [corresp_ex_def]
 "!!f.[| is_ref_map f C A |] ==>\
\ !s. reachable C s & is_exec_frag C (s,xs) \
\ --> is_exec_frag A (corresp_ex A f (s,xs))"; 

by (Asm_full_simp_tac 1);
by (pair_induct_tac "xs" [is_exec_frag_def] 1);
(* main case *)
by (safe_tac set_cs);
by (res_inst_tac [("t","f y")]  lemma_2_1 1);

(* Finite *)
by (etac move_subprop2 1);
by (REPEAT (atac 1));
by (rtac conjI 1);

(* is_exec_frag *)
by (etac move_subprop1 1);
by (REPEAT (atac 1));
by (rtac conjI 1);

(* Induction hypothesis  *)
(* reachable_n looping, therefore apply it manually *)
by (eres_inst_tac [("x","y")] allE 1);
by (Asm_full_simp_tac 1);
by (forward_tac [reachable.reachable_n] 1);
by (assume_tac 1);
by (Asm_full_simp_tac 1);
(* laststate *)
by (etac (move_subprop3 RS sym) 1);
by (REPEAT (atac 1));
qed"lemma_2";


(* -------------------------------------------------------------------------------- *)

section "Main Theorem: T R A C E - I N C L U S I O N";

(* -------------------------------------------------------------------------------- *)


goalw thy [traces_def]
  "!!f. [| ext C = ext A; is_ref_map f C A |] \
\          ==> traces C <= traces A"; 

  by (simp_tac(simpset() addsimps [has_trace_def2])1);
  by (safe_tac set_cs);

  (* give execution of abstract automata *)
  by (res_inst_tac[("x","corresp_ex A f ex")] bexI 1);
  
  (* Traces coincide, Lemma 1 *)
  by (pair_tac "ex" 1);
  by (etac (lemma_1 RS spec RS mp) 1);
  by (REPEAT (atac 1));
  by (asm_full_simp_tac (simpset() addsimps [executions_def,reachable.reachable_0]) 1);
 
  (* corresp_ex is execution, Lemma 2 *)
  by (pair_tac "ex" 1);
  by (asm_full_simp_tac (simpset() addsimps [executions_def]) 1);
  (* start state *) 
  by (rtac conjI 1);
  by (asm_full_simp_tac (simpset() addsimps [is_ref_map_def,corresp_ex_def]) 1);
  (* is-execution-fragment *)
  by (etac (lemma_2 RS spec RS mp) 1);
  by (asm_full_simp_tac (simpset() addsimps [reachable.reachable_0]) 1);
qed"trace_inclusion"; 


(* -------------------------------------------------------------------------------- *)

section "Corollary:  F A I R  T R A C E - I N C L U S I O N";

(* -------------------------------------------------------------------------------- *)


goalw thy [fin_often_def] "(~inf_often P s) = fin_often P s";
auto();
qed"fininf";


goal thy 
"is_wfair A W (s,ex) = \
\ (fin_often (%x. ~Enabled A W (snd x)) ex --> inf_often (%x. fst x :W) ex)";
by (asm_full_simp_tac (simpset() addsimps [is_wfair_def,fin_often_def])1);
auto();
qed"WF_alt";

goal thy  
"!! ex. [|is_wfair A W (s,ex); inf_often (%x. Enabled A W (snd x)) ex; \
\         en_persistent A W|] \
\   ==> inf_often (%x. fst x :W) ex";
bd persistent 1;
ba 1;
by (asm_full_simp_tac (simpset() addsimps [WF_alt])1);
auto();
qed"WF_persistent";


goal thy "!! C A. \
\         [| is_ref_map f C A; ext C = ext A; \
\         !! ex. [| ex:executions C; fair_ex C ex|] ==> fair_ex A (corresp_ex A f ex) |] \
\         ==> fairtraces C <= fairtraces A";
by (simp_tac (simpset() addsimps [fairtraces_def,
   fairexecutions_def]) 1);
by (safe_tac set_cs);
by (res_inst_tac[("x","corresp_ex A f ex")] exI 1);
by (safe_tac set_cs);

  (* Traces coincide, Lemma 1 *)
  by (pair_tac "ex" 1);
  by (etac (lemma_1 RS spec RS mp) 1);
  by (REPEAT (atac 1));
  by (asm_full_simp_tac (simpset() addsimps [executions_def,reachable.reachable_0]) 1);
 
  (* corresp_ex is execution, Lemma 2 *)
  by (pair_tac "ex" 1);
  by (asm_full_simp_tac (simpset() addsimps [executions_def]) 1);
  (* start state *) 
  by (rtac conjI 1);
  by (asm_full_simp_tac (simpset() addsimps [is_ref_map_def,corresp_ex_def]) 1);
  (* is-execution-fragment *)
  by (etac (lemma_2 RS spec RS mp) 1);
  by (asm_full_simp_tac (simpset() addsimps [reachable.reachable_0]) 1);

 (* Fairness *)
auto();
qed"fair_trace_inclusion";

goal thy "!! C A. \
\         [| inp(C) = inp(A); out(C)=out(A); \
\            is_fair_ref_map f C A |] \
\         ==> fair_implements C A";
by (asm_full_simp_tac (simpset() addsimps [is_fair_ref_map_def, fair_implements_def,
    fairtraces_def, fairexecutions_def]) 1);
by (safe_tac set_cs);
by (res_inst_tac[("x","corresp_ex A f ex")] exI 1);
by (safe_tac set_cs);
  (* Traces coincide, Lemma 1 *)
  by (pair_tac "ex" 1);
  by (etac (lemma_1 RS spec RS mp) 1);
  by (simp_tac (simpset() addsimps [externals_def])1);
  by (SELECT_GOAL (auto_tac (claset(),simpset()))1);
  by (asm_full_simp_tac (simpset() addsimps [executions_def,reachable.reachable_0]) 1);
 
  (* corresp_ex is execution, Lemma 2 *)
  by (pair_tac "ex" 1);
  by (asm_full_simp_tac (simpset() addsimps [executions_def]) 1);
  (* start state *) 
  by (rtac conjI 1);
  by (asm_full_simp_tac (simpset() addsimps [is_ref_map_def,corresp_ex_def]) 1);
  (* is-execution-fragment *)
  by (etac (lemma_2 RS spec RS mp) 1);
  by (asm_full_simp_tac (simpset() addsimps [reachable.reachable_0]) 1);

 (* Fairness *)
auto();
qed"fair_trace_inclusion2";





