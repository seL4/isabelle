(*  Title:      HOL/IOA/meta_theory/Solve.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

Weak possibilities mapping (abstraction)
*)

open Solve; 

val SS = SS addsimps [mk_trace_thm,trans_in_actions];

goalw Solve.thy [is_weak_pmap_def,traces_def]
  "!!f. [| IOA(C); IOA(A); externals(asig_of(C)) = externals(asig_of(A)); \
\          is_weak_pmap f C A |] ==> traces(C) <= traces(A)";

  by (simp_tac(SS addsimps [has_trace_def])1);
  by (safe_tac set_cs);

  (* choose same trace, therefore same NF *)
  by (res_inst_tac[("x","mk_trace  C (fst ex)")] exI 1);
  by (asm_full_simp_tac set_ss 1);

  (* give execution of abstract automata *)
  by (res_inst_tac[("x","(mk_trace A (fst ex),%i.f(snd ex i))")] bexI 1);

  (* Traces coincide *)
  by (asm_simp_tac (SS addsimps [mk_trace_def,filter_oseq_idemp])1);

  (* Use lemma *)
  by (forward_tac [states_of_exec_reachable] 1);

  (* Now show that it's an execution *)
  by (asm_full_simp_tac(SS addsimps [executions_def]) 1);
  by (safe_tac set_cs);

  (* Start states map to start states *)
  by (dtac bspec 1);
  by (atac 1);

  (* Show that it's an execution fragment *)
  by (asm_full_simp_tac (SS addsimps [is_execution_fragment_def])1);
  by (safe_tac HOL_cs);

  by (eres_inst_tac [("x","snd ex n")] allE 1);
  by (eres_inst_tac [("x","snd ex (Suc n)")] allE 1);
  by (eres_inst_tac [("x","a")] allE 1);
  by (asm_full_simp_tac SS 1);
qed "trace_inclusion";

(* Lemmata *)

val prems = goal HOL.thy "(P ==> Q-->R) ==> P&Q --> R";
  by(fast_tac (HOL_cs addDs prems) 1);
val imp_conj_lemma = result();


(* fist_order_tautology of externals_of_par *)
goal IOA.thy "a:externals(asig_of(A1||A2)) =    \
\  (a:externals(asig_of(A1)) & a:externals(asig_of(A2)) |  \
\  a:externals(asig_of(A1)) & a~:externals(asig_of(A2)) |  \
\  a~:externals(asig_of(A1)) & a:externals(asig_of(A2)))";
by (asm_full_simp_tac (SS addsimps [externals_def,asig_of_par,asig_comp_def,asig_inputs_def,asig_outputs_def]) 1);
 by (fast_tac set_cs 1);
val externals_of_par_extra = result(); 

goal Solve.thy "!!s.[| reachable (C1||C2) s |] ==> reachable C1 (fst s)";
by (asm_full_simp_tac (SS addsimps [reachable_def]) 1); 
by (etac bexE 1);
by (res_inst_tac [("x",
   "(filter_oseq (%a.a:actions(asig_of(C1))) \
\                (fst ex),                                                \
\    %i.fst (snd ex i))")]  bexI 1);
(* fst(s) is in projected execution *)
 by (simp_tac SS 1);
 by (fast_tac HOL_cs 1);
(* projected execution is indeed an execution *)
by (asm_full_simp_tac (SS addsimps [executions_def,is_execution_fragment_def,
    par_def, starts_of_def,trans_of_def]) 1);
by (simp_tac (SS addsimps [filter_oseq_def]) 1);
 by (REPEAT(rtac allI 1));
 by (cut_inst_tac [("x","fst ex n")] opt_cases 1);
 by (etac disjE 1);
(* case 1: action sequence of || had already a None *)
by (asm_full_simp_tac SS 1);
 by (REPEAT(etac exE 1));
 by (case_tac "y:actions(asig_of(C1))" 1);
(* case 2: action sequence of || had Some(a) and 
           filtered sequence also       *)
by (asm_full_simp_tac SS 1);
 by (rtac impI 1);
 by (REPEAT(hyp_subst_tac 1)); 
 by (asm_full_simp_tac SS 1);
(* case 3: action sequence pf || had Some(a) but
           filtered sequence has None      *)
 by (asm_full_simp_tac SS 1);
qed"comp1_reachable";


(* Exact copy of proof of comp1_reachable for the second 
   component of a parallel composition.     *)
goal Solve.thy "!!s.[| reachable (C1||C2) s|] ==> reachable C2 (snd s)";
by (asm_full_simp_tac (SS addsimps [reachable_def]) 1); 
by (etac bexE 1);
by (res_inst_tac [("x",
   "(filter_oseq (%a.a:actions(asig_of(C2)))\
\                (fst ex),                                                \
\    %i.snd (snd ex i))")]  bexI 1);
(* fst(s) is in projected execution *)
 by (simp_tac list_ss 1);
 by (fast_tac HOL_cs 1);
(* projected execution is indeed an execution *)
 by (asm_full_simp_tac (SS addsimps [executions_def,is_execution_fragment_def,
    par_def, starts_of_def,trans_of_def]) 1);
 by (simp_tac (SS addsimps [filter_oseq_def]) 1);
 by (REPEAT(rtac allI 1));
 by (cut_inst_tac [("x","fst ex n")] opt_cases 1);
 by (etac disjE 1);
 by (asm_full_simp_tac SS 1);
 by (REPEAT(etac exE 1));
 by (case_tac "y:actions(asig_of(C2))" 1);
 by (asm_full_simp_tac SS 1);
 by (rtac impI 1);
 by (REPEAT(hyp_subst_tac 1)); 
 by (asm_full_simp_tac SS 1);
 by (asm_full_simp_tac SS 1);
qed"comp2_reachable";


(* Composition of possibility-mappings *)

goalw Solve.thy [is_weak_pmap_def] "!!f g.[| is_weak_pmap f C1 A1 & \
\               externals(asig_of(A1))=externals(asig_of(C1)) &\
\               is_weak_pmap g C2 A2 &  \
\               externals(asig_of(A2))=externals(asig_of(C2)) & \
\               compat_ioas C1 C2 & compat_ioas A1 A2  |]     \
\  ==> is_weak_pmap (%p.(f(fst(p)),g(snd(p)))) (C1||C2) (A1||A2)";
 by (rtac conjI 1);
(* start_states *)
 by (asm_full_simp_tac (SS addsimps [par_def, starts_of_def]) 1);
 by (fast_tac set_cs 1);
(* transitions *)
by (REPEAT (rtac allI 1));
by (rtac imp_conj_lemma 1);
by (REPEAT(etac conjE 1));
by (simp_tac (SS addsimps [externals_of_par_extra]) 1);
by (simp_tac (SS addsimps [par_def]) 1);
by (asm_full_simp_tac (SS addsimps [trans_of_def]) 1);
by (rtac (expand_if RS ssubst) 1);
by (rtac conjI 1);
by (rtac impI 1); 
by (etac disjE 1);
(* case 1      a:e(A1) | a:e(A2) *)
by (asm_full_simp_tac (SS addsimps [comp1_reachable,comp2_reachable,
                                    ext_is_act]) 1);
by (etac disjE 1);
(* case 2      a:e(A1) | a~:e(A2) *)
by (asm_full_simp_tac (SS addsimps [comp1_reachable,comp2_reachable,
             ext_is_act,ext1_ext2_is_not_act2]) 1);
(* case 3      a:~e(A1) | a:e(A2) *)
by (asm_full_simp_tac (SS addsimps [comp1_reachable,comp2_reachable,
             ext_is_act,ext1_ext2_is_not_act1]) 1);
(* case 4      a:~e(A1) | a~:e(A2) *)
by (rtac impI 1);
by (subgoal_tac "a~:externals(asig_of(A1)) & a~:externals(asig_of(A2))" 1);
(* delete auxiliary subgoal *)
by (asm_full_simp_tac SS 2);
by (fast_tac HOL_cs 2);
by (simp_tac (SS addsimps [conj_disj_distribR] addcongs [conj_cong]
                 setloop (split_tac [expand_if])) 1);
by(REPEAT((resolve_tac [conjI,impI] 1 ORELSE etac conjE 1) THEN
        asm_full_simp_tac(SS addsimps[comp1_reachable,
                                      comp2_reachable])1));
qed"fxg_is_weak_pmap_of_product_IOA";


goal Solve.thy "!!s.[| reachable (rename C g) s |] ==> reachable C s";
by (asm_full_simp_tac (SS addsimps [reachable_def]) 1); 
by (etac bexE 1);
by (res_inst_tac [("x",
   "((%i. case (fst ex i) \
\         of None => None\
\          | Some(x) => g x) ,snd ex)")]  bexI 1);
by (simp_tac SS 1);
(* execution is indeed an execution of C *)
by (asm_full_simp_tac (SS addsimps [executions_def,is_execution_fragment_def,
    par_def, starts_of_def,trans_of_def,rename_def]) 1);
by (REPEAT(rtac allI 1));
by (cut_inst_tac [("x","fst ex n")] opt_cases 1);
 by (etac disjE 1);
(* case 1: action sequence of rename C had already a None *)
by (asm_full_simp_tac SS 1);
(* case 2 *)
by (REPEAT(etac exE 1));
by (etac conjE 1);
by (eres_inst_tac [("x","n")] allE 1);
by (eres_inst_tac [("x","y")] allE 1);
by (asm_full_simp_tac SS 1);
by (etac exE 1);
by (etac conjE 1);
by (dtac sym 1);
by (dtac sym 1);
by (dtac sym 1);
by (asm_full_simp_tac SS 1);
by (safe_tac HOL_cs);
qed"reachable_rename_ioa";


(* HOL Lemmata - must already exist ! *)
goal HOL.thy  "(~(A|B)) =(~A&~B)";
 by (fast_tac HOL_cs 1);
val disj_demorgan = result();
goal HOL.thy  "(~(A&B)) =(~A|~B)";
 by (fast_tac HOL_cs 1);
val conj_demorgan = result();
goal HOL.thy  "(~(? x.P x)) =(! x. (~ (P x)))";
 by (fast_tac HOL_cs 1);
val neg_ex = result();


goal Solve.thy "!!f.[| is_weak_pmap f C A |]\
\                      ==> (is_weak_pmap f (rename C g) (rename A g))";
by (asm_full_simp_tac (SS addsimps [is_weak_pmap_def]) 1);
by (rtac conjI 1);
by (asm_full_simp_tac (SS addsimps [rename_def,starts_of_def]) 1);
by (fast_tac set_cs 1);
by (REPEAT (rtac allI 1));
by (rtac imp_conj_lemma 1);
by (simp_tac (SS addsimps [rename_def]) 1);
by (asm_full_simp_tac (SS addsimps [externals_def,asig_inputs_def,asig_outputs_def,asig_of_def,trans_of_def]) 1);
by (safe_tac set_cs);
by (rtac (expand_if RS ssubst) 1);
 by (rtac conjI 1);
 by (rtac impI 1);
 by (etac disjE 1);
 by (etac exE 1);
by (etac conjE 1);
(* x is input *)
 by (dtac sym 1);
 by (dtac sym 1);
by (asm_full_simp_tac SS 1);
by (REPEAT (hyp_subst_tac 1));
by (cut_inst_tac [("C","C"),("g","g"),("s","s")] reachable_rename_ioa 1);
by (assume_tac 1);
by (asm_full_simp_tac SS 1);
(* x is output *)
 by (etac exE 1);
by (etac conjE 1);
 by (dtac sym 1);
 by (dtac sym 1);
by (asm_full_simp_tac SS 1);
by (REPEAT (hyp_subst_tac 1));
by (cut_inst_tac [("C","C"),("g","g"),("s","s")] reachable_rename_ioa 1);
by (assume_tac 1);
by (asm_full_simp_tac SS 1);
(* x is internal *)
by (simp_tac (SS addsimps [disj_demorgan,neg_ex,conj_demorgan] addcongs [conj_cong]) 1);
by (rtac impI 1);
by (etac conjE 1);
by (cut_inst_tac [("C","C"),("g","g"),("s","s")] reachable_rename_ioa 1);
by (assume_tac 1);
by (eres_inst_tac [("x","s")] allE 1);
by (eres_inst_tac [("x","t")] allE 1);
by (eres_inst_tac [("x","x")] allE 1);
by (eres_inst_tac [("x","x")] allE 1);
by (asm_full_simp_tac SS 1);
qed"rename_through_pmap";



