(*  Title:      HOLCF/IOA/meta_theory/RefCorrectness.ML
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1996  TU Muenchen

Correctness of Refinement Mappings in HOLCF/IOA
*)



(* -------------------------------------------------------------------------------- *)

section "corresp_ex";


(* ---------------------------------------------------------------- *)
(*                             corresp_ex2                          *)
(* ---------------------------------------------------------------- *)


goal thy "corresp_ex2 A f  = (LAM ex. (%s. case ex of \
\      nil =>  nil   \
\    | x##xs => (flift1 (%pr. (snd(@cex. move A cex s (fst pr) (f (snd pr))))   \
\                              @@ ((corresp_ex2 A f `xs) (f (snd pr))))   \
\                        `x) ))";
by (rtac trans 1);
br fix_eq2 1;
br corresp_ex2_def 1;
br beta_cfun 1;
by (simp_tac (!simpset addsimps [flift1_def]) 1);
qed"corresp_ex2_unfold";

goal thy "(corresp_ex2 A f`UU) s=UU";
by (stac corresp_ex2_unfold 1);
by (Simp_tac 1);
qed"corresp_ex2_UU";

goal thy "(corresp_ex2 A f`nil) s = nil";
by (stac corresp_ex2_unfold 1);
by (Simp_tac 1);
qed"corresp_ex2_nil";

goal thy "(corresp_ex2 A f`(at>>xs)) s = \
\          (snd(@cex. move A cex s (fst at) (f (snd at))))  \
\          @@ ((corresp_ex2 A f`xs) (f (snd at)))";
br trans 1;
by (stac corresp_ex2_unfold 1);
by (asm_full_simp_tac (!simpset addsimps [Cons_def,flift1_def]) 1);
by (Simp_tac 1);
qed"corresp_ex2_cons";


Addsimps [corresp_ex2_UU,corresp_ex2_nil,corresp_ex2_cons];



(* ------------------------------------------------------------------ *)
(*               The following lemmata describe the definition        *)
(*                         of move in more detail                     *)
(* ------------------------------------------------------------------ *)

section"properties of move";

goalw thy [is_ref_map_def]
   "!!f. [|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==>\
\     move A (@x. move A x (f s) a (f t)) (f s) a (f t)";

by (subgoal_tac "? ex.move A ex (f s) a (f t)" 1);
by (Asm_full_simp_tac 2);
by (etac exE 1);
by (rtac selectI 1);
by (assume_tac 1);
qed"move_is_move";

goal thy
   "!!f. [|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==>\
\    is_execution_fragment A (@x. move A x (f s) a (f t))";
by (cut_inst_tac [] move_is_move 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (!simpset addsimps [move_def]) 1);
qed"move_subprop1";

goal thy
   "!!f. [|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==>\
\    Finite (snd (@x. move A x (f s) a (f t)))";
by (cut_inst_tac [] move_is_move 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (!simpset addsimps [move_def]) 1);
qed"move_subprop2";

goal thy
   "!!f. [|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==>\
\    fst (@x. move A x (f s) a (f t)) = (f s)";
by (cut_inst_tac [] move_is_move 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (!simpset addsimps [move_def]) 1);
qed"move_subprop3";

goal thy
   "!!f. [|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==>\
\    laststate (@x. move A x (f s) a (f t)) = (f t)";
by (cut_inst_tac [] move_is_move 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (!simpset addsimps [move_def]) 1);
qed"move_subprop4";

goal thy
   "!!f. [|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==>\
\     mk_trace A`(snd(@x. move A x (f s) a (f t))) = \
\       (if a:ext A then a>>nil else nil)";

by (cut_inst_tac [] move_is_move 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (!simpset addsimps [move_def]) 1);
qed"move_subprop5";

goal thy
   "!!f. [|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==>\
\    (is_execution_fragment A (f s,(snd (@x. move A x (f s) a (f t)))))";
by (cut_inst_tac [] move_subprop3 1);
by (REPEAT (assume_tac 1));
by (cut_inst_tac [] move_subprop1 1);
by (REPEAT (assume_tac 1));
by (res_inst_tac [("s","fst (@x. move A x (f s) a (f t))")] subst 1);
back();
back();
back();
ba 1;
by (simp_tac (HOL_basic_ss addsimps [surjective_pairing RS sym]) 1);
qed"move_subprop_1and3";

goal thy
   "!!f. [|is_ref_map f C A; reachable C s; (s,a,t):trans_of C|] ==>\
\    (case Last`(snd (@x. move A x (f s) a (f t))) of \
\       Undef => (f s) \
\     | Def p => snd p) = (f t)";
by (cut_inst_tac [] move_subprop3 1);
by (REPEAT (assume_tac 1));
by (cut_inst_tac [] move_subprop4 1);
by (REPEAT (assume_tac 1));
by (asm_full_simp_tac (!simpset addsimps [laststate_def]) 1);
qed"move_subprop_4and3";



(* ------------------------------------------------------------------ *)
(*                   The following lemmata contribute to              *)
(*                 TRACE INCLUSION Part 1: Traces coincide            *)
(* ------------------------------------------------------------------ *)

section "Lemmata for <==";

(* --------------------------------------------------- *)
(*   Lemma 1.1: Distribution of mk_trace and @@        *)
(* --------------------------------------------------- *)


goal thy "mk_trace C`(ex1 @@ ex2)= (mk_trace C`ex1) @@ (mk_trace C`ex2)";
by (simp_tac (!simpset addsimps [mk_trace_def,filter_act_def,
                                 FilterConc,MapConc]) 1);
qed"mk_traceConc";



(* ------------------------------------------------------
                 Lemma 1 :Traces coincide  
   ------------------------------------------------------- *)

goalw thy [corresp_ex_def]
  "!!f.[|is_ref_map f C A; ext C = ext A|] ==>  \     
\        !s. reachable C s & is_execution_fragment C (s,xs) --> \
\            mk_trace C`xs = mk_trace A`(snd (corresp_ex A f (s,xs)))";

by (pair_induct_tac "xs" [is_execution_fragment_def] 1);
(* cons case *) 
by (safe_tac set_cs);
by (asm_full_simp_tac (!simpset addsimps [mk_traceConc]) 1);
by (forward_tac [reachable.reachable_n] 1);
ba 1;
by (eres_inst_tac [("x","y")] allE 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (!simpset addsimps [move_subprop5] 
                          setloop split_tac [expand_if] ) 1);
qed"lemma_1";


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
\(!s .is_execution_fragment A (s,xs) & is_execution_fragment A (t,ys) & \ 
\     t = laststate (s,xs) \
\ --> is_execution_fragment A (s,xs @@ ys))";

br impI 1;
by (Seq_Finite_induct_tac 1);
(* base_case *)
by (fast_tac HOL_cs 1);
(* main case *)
by (safe_tac set_cs);
by (pair_tac "a" 1);
qed"lemma_2_1";


(* ----------------------------------------------------------- *)
(*               Lemma 2 : corresp_ex is execution             *)
(* ----------------------------------------------------------- *)



goalw thy [corresp_ex_def]
 "!!f.[| is_ref_map f C A |] ==>\
\ !s. reachable C s & is_execution_fragment C (s,xs) \
\ --> is_execution_fragment A (corresp_ex A f (s,xs))"; 

by (Asm_full_simp_tac 1);
by (pair_induct_tac "xs" [is_execution_fragment_def] 1);
(* main case *)
by (safe_tac set_cs);
by (res_inst_tac [("t3","f y")]  (lemma_2_1 RS mp RS spec RS mp) 1);

(* Finite *)
be move_subprop2 1;
by (REPEAT (atac 1));
by (rtac conjI 1);

(* is_execution_fragment *)
be  move_subprop_1and3 1;
by (REPEAT (atac 1));
by (rtac conjI 1);

(* Induction hypothesis  *)
(* reachable_n looping, therefore apply it manually *)
by (eres_inst_tac [("x","y")] allE 1);
by (Asm_full_simp_tac 1);
by (forward_tac [reachable.reachable_n] 1);
ba 1;
by (Asm_full_simp_tac 1);
(* laststate *)
by (simp_tac (!simpset addsimps [laststate_def]) 1); 
be (move_subprop_4and3 RS sym) 1;
by (REPEAT (atac 1));
qed"lemma_2";


(* -------------------------------------------------------------------------------- *)

section "Main Theorem: T R A C E - I N C L U S I O N";

(* -------------------------------------------------------------------------------- *)


goalw thy [traces_def]
  "!!f. [| IOA C; IOA A; ext C = ext A; is_ref_map f C A |] \
\          ==> traces C <= traces A"; 

  by (simp_tac(!simpset addsimps [has_trace_def2])1);
  by (safe_tac set_cs);

  (* give execution of abstract automata *)
  by (res_inst_tac[("x","corresp_ex A f ex")] bexI 1);
  
  (* Traces coincide, Lemma 1 *)
  by (pair_tac "ex" 1);
  by (etac (lemma_1 RS spec RS mp) 1);
  by (REPEAT (atac 1));
  by (asm_full_simp_tac (!simpset addsimps [executions_def,reachable.reachable_0]) 1);
 
  (* corresp_ex is execution, Lemma 2 *)
  by (pair_tac "ex" 1);
  by (asm_full_simp_tac (!simpset addsimps [executions_def]) 1);
  (* start state *) 
  by (rtac conjI 1);
  by (asm_full_simp_tac (!simpset addsimps [is_ref_map_def,corresp_ex_def]) 1);
  (* is-execution-fragment *)
  by (etac (lemma_2 RS spec RS mp) 1);
  by (asm_full_simp_tac (!simpset addsimps [reachable.reachable_0]) 1);
qed"trace_inclusion"; 





