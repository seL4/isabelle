(*  Title:      HOLCF/IOA/meta_theory/SimCorrectness.ML
    ID:         $Id$
    Author:     Olaf Müller

Correctness of Simulations in HOLCF/IOA.
*)



(* -------------------------------------------------------------------------------- *)

section "corresp_ex_sim";


(* ---------------------------------------------------------------- *)
(*                             corresp_ex_simC                          *)
(* ---------------------------------------------------------------- *)


Goal "corresp_ex_simC A R  = (LAM ex. (%s. case ex of \
\      nil =>  nil   \
\    | x##xs => (flift1 (%pr. let a = (fst pr); t = (snd pr); \
\                                 T' = @t'. ? ex1. (t,t'):R & move A ex1 s a t' \
\                             in \
\                                (@cex. move A cex s a T')  \
\                              @@ ((corresp_ex_simC A R $xs) T'))   \
\                        $x) ))";
by (rtac trans 1);
by (rtac fix_eq2 1);
by (rtac corresp_ex_simC_def 1);
by (rtac beta_cfun 1);
by (simp_tac (simpset() addsimps [flift1_def]) 1);
qed"corresp_ex_simC_unfold";

Goal "(corresp_ex_simC A R$UU) s=UU";
by (stac corresp_ex_simC_unfold 1);
by (Simp_tac 1);
qed"corresp_ex_simC_UU";

Goal "(corresp_ex_simC A R$nil) s = nil";
by (stac corresp_ex_simC_unfold 1);
by (Simp_tac 1);
qed"corresp_ex_simC_nil";

Goal "(corresp_ex_simC A R$((a,t)>>xs)) s = \
\          (let T' = @t'. ? ex1. (t,t'):R & move A ex1 s a t' \
\           in  \
\            (@cex. move A cex s a T')  \ 
\             @@ ((corresp_ex_simC A R$xs) T'))";
by (rtac trans 1);
by (stac corresp_ex_simC_unfold 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def,flift1_def]) 1);
by (Simp_tac 1);
qed"corresp_ex_simC_cons";


Addsimps [corresp_ex_simC_UU,corresp_ex_simC_nil,corresp_ex_simC_cons];



(* ------------------------------------------------------------------ *)
(*               The following lemmata describe the definition        *)
(*                         of move in more detail                     *)
(* ------------------------------------------------------------------ *)

section"properties of move";

Delsimps [Let_def];

Goalw [is_simulation_def]
   "[|is_simulation R C A; reachable C s; s -a--C-> t; (s,s'):R|] ==>\
\     let T' = @t'. ? ex1. (t,t'):R & move A ex1 s' a t' in \
\     (t,T'): R & move A (@ex2. move A ex2 s' a T') s' a T'";

(* Does not perform conditional rewriting on assumptions automatically as
   usual. Instantiate all variables per hand. Ask Tobias?? *)
by (subgoal_tac "? t' ex. (t,t'):R & move A ex s' a t'" 1);
by (Asm_full_simp_tac 2); 
by (etac conjE 2);
by (eres_inst_tac [("x","s")] allE 2);
by (eres_inst_tac [("x","s'")] allE 2);
by (eres_inst_tac [("x","t")] allE 2);
by (eres_inst_tac [("x","a")] allE 2);
by (Asm_full_simp_tac 2); 
(* Go on as usual *)
by (etac exE 1);
by (dres_inst_tac [("x","t'"),
         ("P","%t'. ? ex.(t,t'):R & move A ex s' a t'")] someI 1);
by (etac exE 1);
by (etac conjE 1);
by (asm_full_simp_tac (simpset() addsimps [Let_def]) 1);
by (res_inst_tac [("x","ex")] someI 1);
by (etac conjE 1);
by (assume_tac 1);
qed"move_is_move_sim";


Addsimps [Let_def];

Goal
   "[|is_simulation R C A; reachable C s; s-a--C-> t; (s,s'):R|] ==>\
\   let T' = @t'. ? ex1. (t,t'):R & move A ex1 s' a t' in \
\    is_exec_frag A (s',@x. move A x s' a T')";
by (cut_inst_tac [] move_is_move_sim 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (simpset() addsimps [move_def,Let_def]) 1);
qed"move_subprop1_sim";

Goal
   "[|is_simulation R C A; reachable C s; s-a--C-> t; (s,s'):R|] ==>\
\   let T' = @t'. ? ex1. (t,t'):R & move A ex1 s' a t' in \
\   Finite (@x. move A x s' a T')";
by (cut_inst_tac [] move_is_move_sim 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (simpset() addsimps [move_def,Let_def]) 1);
qed"move_subprop2_sim";

Goal
   "[|is_simulation R C A; reachable C s; s-a--C-> t; (s,s'):R|] ==>\
\   let T' = @t'. ? ex1. (t,t'):R & move A ex1 s' a t' in \
\    laststate (s',@x. move A x s' a T') = T'";
by (cut_inst_tac [] move_is_move_sim 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (simpset() addsimps [move_def,Let_def]) 1);
qed"move_subprop3_sim";

Goal
   "[|is_simulation R C A; reachable C s; s-a--C-> t; (s,s'):R|] ==>\
\   let T' = @t'. ? ex1. (t,t'):R & move A ex1 s' a t' in \
\     mk_trace A$((@x. move A x s' a T')) = \
\       (if a:ext A then a>>nil else nil)";
by (cut_inst_tac [] move_is_move_sim 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (simpset() addsimps [move_def,Let_def]) 1);
qed"move_subprop4_sim";

Goal
   "[|is_simulation R C A; reachable C s; s-a--C-> t; (s,s'):R|] ==>\
\   let T' = @t'. ? ex1. (t,t'):R & move A ex1 s' a t' in \
\     (t,T'):R";
by (cut_inst_tac [] move_is_move_sim 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (simpset() addsimps [move_def,Let_def]) 1);
qed"move_subprop5_sim";

(* ------------------------------------------------------------------ *)
(*                   The following lemmata contribute to              *)
(*                 TRACE INCLUSION Part 1: Traces coincide            *)
(* ------------------------------------------------------------------ *)

section "Lemmata for <==";


(* ------------------------------------------------------
                 Lemma 1 :Traces coincide  
   ------------------------------------------------------- *)

Delsplits[split_if];
Goal 
  "[|is_simulation R C A; ext C = ext A|] ==>  \     
\        !s s'. reachable C s & is_exec_frag C (s,ex) & (s,s'): R --> \
\            mk_trace C$ex = mk_trace A$((corresp_ex_simC A R$ex) s')";

by (pair_induct_tac "ex" [is_exec_frag_def] 1);
(* cons case *) 
by (safe_tac set_cs); 
ren "ex a t s s'" 1;
by (asm_full_simp_tac (simpset() addsimps [mk_traceConc]) 1);
by (forward_tac [reachable.reachable_n] 1);
by (assume_tac 1);
by (eres_inst_tac [("x","t")] allE 1);
by (eres_inst_tac [("x",
                    "@t'. ? ex1. (t,t'):R & move A ex1 s' a t'")] 
     allE 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps 
      [rewrite_rule [Let_def] move_subprop5_sim,
       rewrite_rule [Let_def] move_subprop4_sim] 
   addsplits [split_if]) 1);
qed_spec_mp"traces_coincide_sim";
Addsplits[split_if];


(* ----------------------------------------------------------- *)
(*               Lemma 2 : corresp_ex_sim is execution             *)
(* ----------------------------------------------------------- *)


Goal 
 "[| is_simulation R C A |] ==>\
\ !s s'. reachable C s & is_exec_frag C (s,ex) & (s,s'):R  \
\ --> is_exec_frag A (s',(corresp_ex_simC A R$ex) s')"; 

by (Asm_full_simp_tac 1);
by (pair_induct_tac "ex" [is_exec_frag_def] 1);
(* main case *)
by (safe_tac set_cs);
ren "ex a t s s'" 1;
by (res_inst_tac [("t",
                   "@t'. ? ex1. (t,t'):R & move A ex1 s' a t'")]  
    lemma_2_1 1);

(* Finite *)
by (etac (rewrite_rule [Let_def] move_subprop2_sim) 1);
by (REPEAT (atac 1));
by (rtac conjI 1);

(* is_exec_frag *)
by (etac (rewrite_rule [Let_def] move_subprop1_sim) 1);
by (REPEAT (atac 1));
by (rtac conjI 1);

(* Induction hypothesis  *)
(* reachable_n looping, therefore apply it manually *)
by (eres_inst_tac [("x","t")] allE 1);
by (eres_inst_tac [("x",
                    "@t'. ? ex1. (t,t'):R & move A ex1 s' a t'")] 
     allE 1);
by (Asm_full_simp_tac 1);
by (forward_tac [reachable.reachable_n] 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps 
            [rewrite_rule [Let_def] move_subprop5_sim]) 1);
(* laststate *)
by (etac ((rewrite_rule [Let_def] move_subprop3_sim) RS sym) 1);
by (REPEAT (atac 1));
qed_spec_mp"correspsim_is_execution";


(* -------------------------------------------------------------------------------- *)

section "Main Theorem: T R A C E - I N C L U S I O N";

(* -------------------------------------------------------------------------------- *)

  (* generate condition (s,S'):R & S':starts_of A, the first being intereting
     for the induction cases concerning the two lemmas correpsim_is_execution and 
     traces_coincide_sim, the second for the start state case. 
     S':= @s'. (s,s'):R & s':starts_of A, where s:starts_of C  *)

Goal 
"[| is_simulation R C A; s:starts_of C |] \
\ ==> let S' = @s'. (s,s'):R & s':starts_of A in \
\     (s,S'):R & S':starts_of A";
  by (asm_full_simp_tac (simpset() addsimps [is_simulation_def,
         corresp_ex_sim_def, Int_non_empty,Image_def]) 1);
  by (REPEAT (etac conjE 1));
  by (etac ballE 1);
  by (Blast_tac 2);
  by (etac exE 1);
  by (rtac someI2 1);
  by (assume_tac 1);
  by (Blast_tac 1);
qed"simulation_starts";

bind_thm("sim_starts1",(rewrite_rule [Let_def] simulation_starts) RS conjunct1);
bind_thm("sim_starts2",(rewrite_rule [Let_def] simulation_starts) RS conjunct2);


Goalw [traces_def]
  "[| ext C = ext A; is_simulation R C A |] \
\          ==> traces C <= traces A"; 

  by (simp_tac(simpset() addsimps [has_trace_def2])1);
  by (safe_tac set_cs);

  (* give execution of abstract automata *)
  by (res_inst_tac[("x","corresp_ex_sim A R ex")] bexI 1);
   
  (* Traces coincide, Lemma 1 *)
  by (pair_tac "ex" 1);
  ren "s ex" 1;
  by (simp_tac (simpset() addsimps [corresp_ex_sim_def]) 1);
  by (res_inst_tac [("s","s")] traces_coincide_sim 1);
  by (REPEAT (atac 1));
  by (asm_full_simp_tac (simpset() addsimps [executions_def,
          reachable.reachable_0,sim_starts1]) 1);
 
  (* corresp_ex_sim is execution, Lemma 2 *)
  by (pair_tac "ex" 1);
  by (asm_full_simp_tac (simpset() addsimps [executions_def]) 1);
  ren "s ex" 1;

  (* start state *) 
  by (rtac conjI 1);
  by (asm_full_simp_tac (simpset() addsimps [sim_starts2,
         corresp_ex_sim_def]) 1);

  (* is-execution-fragment *)
  by (asm_full_simp_tac (simpset() addsimps [corresp_ex_sim_def]) 1);
  by (res_inst_tac [("s","s")] correspsim_is_execution 1);
  by (assume_tac 1);
  by (asm_full_simp_tac (simpset() addsimps [reachable.reachable_0,sim_starts1]) 1);
qed"trace_inclusion_for_simulations"; 




