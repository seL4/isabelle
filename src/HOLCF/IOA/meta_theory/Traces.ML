(*  Title:      HOLCF/IOA/meta_theory/Traces.ML
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen

Theorems about Executions and Traces of I/O automata in HOLCF.
*)   

(* global changes to simpset() and claset(), see also TLS.ML *)
Delsimps (ex_simps @ all_simps);
Delsimps [split_paired_Ex];
Addsimps [Let_def];
claset_ref() := claset() delSWrapper "split_all_tac";

val exec_rws = [executions_def,is_exec_frag_def];



(* ----------------------------------------------------------------------------------- *)

section "recursive equations of operators";


(* ---------------------------------------------------------------- *)
(*                               filter_act                         *)
(* ---------------------------------------------------------------- *)


Goal  "filter_act$UU = UU";
by (simp_tac (simpset() addsimps [filter_act_def]) 1);
qed"filter_act_UU";

Goal  "filter_act$nil = nil";
by (simp_tac (simpset() addsimps [filter_act_def]) 1);
qed"filter_act_nil";

Goal "filter_act$(x>>xs) = (fst x) >> filter_act$xs";
by (simp_tac (simpset() addsimps [filter_act_def]) 1);
qed"filter_act_cons";

Addsimps [filter_act_UU,filter_act_nil,filter_act_cons];


(* ---------------------------------------------------------------- *)
(*                             mk_trace                             *)
(* ---------------------------------------------------------------- *)

Goal "mk_trace A$UU=UU";
by (simp_tac (simpset() addsimps [mk_trace_def]) 1);
qed"mk_trace_UU";

Goal "mk_trace A$nil=nil";
by (simp_tac (simpset() addsimps [mk_trace_def]) 1);
qed"mk_trace_nil";

Goal "mk_trace A$(at >> xs) =    \
\            (if ((fst at):ext A)    \       
\                 then (fst at) >> (mk_trace A$xs) \   
\                 else mk_trace A$xs)";

by (asm_full_simp_tac (simpset() addsimps [mk_trace_def]) 1);
qed"mk_trace_cons";

Addsimps [mk_trace_UU,mk_trace_nil,mk_trace_cons];

(* ---------------------------------------------------------------- *)
(*                             is_exec_fragC                             *)
(* ---------------------------------------------------------------- *)


Goal "is_exec_fragC A = (LAM ex. (%s. case ex of \
\      nil => TT \
\    | x##xs => (flift1 \ 
\            (%p. Def ((s,p):trans_of A) andalso (is_exec_fragC A$xs) (snd p)) \
\             $x) \
\   ))";
by (rtac trans 1);
by (rtac fix_eq2 1);
by (rtac is_exec_fragC_def 1);
by (rtac beta_cfun 1);
by (simp_tac (simpset() addsimps [flift1_def]) 1);
qed"is_exec_fragC_unfold";

Goal "(is_exec_fragC A$UU) s=UU";
by (stac is_exec_fragC_unfold 1);
by (Simp_tac 1);
qed"is_exec_fragC_UU";

Goal "(is_exec_fragC A$nil) s = TT";
by (stac is_exec_fragC_unfold 1);
by (Simp_tac 1);
qed"is_exec_fragC_nil";

Goal "(is_exec_fragC A$(pr>>xs)) s = \
\                        (Def ((s,pr):trans_of A) \
\                andalso (is_exec_fragC A$xs)(snd pr))";
by (rtac trans 1);
by (stac is_exec_fragC_unfold 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def,flift1_def]) 1);
by (Simp_tac 1);
qed"is_exec_fragC_cons";


Addsimps [is_exec_fragC_UU,is_exec_fragC_nil,is_exec_fragC_cons];


(* ---------------------------------------------------------------- *)
(*                        is_exec_frag                              *)
(* ---------------------------------------------------------------- *)

Goal "is_exec_frag A (s, UU)";
by (simp_tac (simpset() addsimps [is_exec_frag_def]) 1);
qed"is_exec_frag_UU";

Goal "is_exec_frag A (s, nil)";
by (simp_tac (simpset() addsimps [is_exec_frag_def]) 1);
qed"is_exec_frag_nil";

Goal "is_exec_frag A (s, (a,t)>>ex) = \
\                               (((s,a,t):trans_of A) & \
\                               is_exec_frag A (t, ex))";
by (simp_tac (simpset() addsimps [is_exec_frag_def]) 1);
qed"is_exec_frag_cons";


(* Delsimps [is_exec_fragC_UU,is_exec_fragC_nil,is_exec_fragC_cons]; *)
Addsimps [is_exec_frag_UU,is_exec_frag_nil, is_exec_frag_cons];  

(* ---------------------------------------------------------------------------- *)
                           section "laststate";
(* ---------------------------------------------------------------------------- *)

Goal "laststate (s,UU) = s";
by (simp_tac (simpset() addsimps [laststate_def]) 1); 
qed"laststate_UU";

Goal "laststate (s,nil) = s";
by (simp_tac (simpset() addsimps [laststate_def]) 1);
qed"laststate_nil";

Goal "!! ex. Finite ex ==> laststate (s,at>>ex) = laststate (snd at,ex)";
by (simp_tac (simpset() addsimps [laststate_def]) 1);
by (case_tac "ex=nil" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (dtac (Finite_Last1 RS mp) 1);
by (assume_tac 1);
by (def_tac 1);
qed"laststate_cons";

Addsimps [laststate_UU,laststate_nil,laststate_cons];

Goal "!!ex. Finite ex ==> (! s. ? u. laststate (s,ex)=u)";
by (Seq_Finite_induct_tac 1);
qed"exists_laststate";


(* -------------------------------------------------------------------------------- *)

section "has_trace, mk_trace";

(* alternative definition of has_trace tailored for the refinement proof, as it does not 
   take the detour of schedules *)

Goalw  [executions_def,mk_trace_def,has_trace_def,schedules_def,has_schedule_def] 
"has_trace A b = (? ex:executions A. b = mk_trace A$(snd ex))";

by (safe_tac set_cs);
(* 1 *)
by (res_inst_tac[("x","ex")] bexI 1);
by (stac beta_cfun 1);
by (cont_tacR 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
(* 2 *)
by (res_inst_tac[("x","filter_act$(snd ex)")] bexI 1);
by (stac beta_cfun 1);
by (cont_tacR 1);
by (Simp_tac 1);
by (safe_tac set_cs);
by (res_inst_tac[("x","ex")] bexI 1);
by (REPEAT (Asm_simp_tac 1));
qed"has_trace_def2";


(* -------------------------------------------------------------------------------- *)

section "signatures and executions, schedules";


(* All executions of A have only actions of A. This is only true because of the 
   predicate state_trans (part of the predicate IOA): We have no dependent types.
   For executions of parallel automata this assumption is not needed, as in par_def
   this condition is included once more. (see Lemmas 1.1.1c in CompoExecs for example) *)

Goal 
  "!! A. is_trans_of A ==> \
\ ! s. is_exec_frag A (s,xs) --> Forall (%a. a:act A) (filter_act$xs)";

by (pair_induct_tac "xs" [is_exec_frag_def,Forall_def,sforall_def] 1);
(* main case *)
ren "ss a t" 1;
by (safe_tac set_cs);
by (REPEAT (asm_full_simp_tac (simpset() addsimps [is_trans_of_def]) 1));
qed"execfrag_in_sig";

Goal 
  "!! A.[|  is_trans_of A; x:executions A |] ==> \
\ Forall (%a. a:act A) (filter_act$(snd x))";

by (asm_full_simp_tac (simpset() addsimps [executions_def]) 1);
by (pair_tac "x" 1);
by (rtac (execfrag_in_sig RS spec RS mp) 1);
by Auto_tac;
qed"exec_in_sig";

Goalw [schedules_def,has_schedule_def]
  "!! A.[|  is_trans_of A; x:schedules A |] ==> \
\   Forall (%a. a:act A) x";

by (fast_tac (claset() addSIs [exec_in_sig]) 1);
qed"scheds_in_sig";

(*

is ok but needs ForallQFilterP which has to been proven first (is trivial also)

Goalw [traces_def,has_trace_def]
  "!! A.[| x:traces A |] ==> \
\   Forall (%a. a:act A) x";
 by (safe_tac set_cs );
by (rtac ForallQFilterP 1);
by (fast_tac (!claset addSIs [ext_is_act]) 1);
qed"traces_in_sig";
*)


(* -------------------------------------------------------------------------------- *)

section "executions are prefix closed";

(* only admissible in y, not if done in x !! *)
Goal "!x s. is_exec_frag A (s,x) & y<<x  --> is_exec_frag A (s,y)";
by (pair_induct_tac "y" [is_exec_frag_def] 1);
by (strip_tac 1);
by (Seq_case_simp_tac "xa" 1);
by (pair_tac "a" 1);
by Auto_tac;
qed"execfrag_prefixclosed";

bind_thm ("exec_prefixclosed",conjI RS (execfrag_prefixclosed RS spec RS spec RS mp));


(* second prefix notion for Finite x *)

Goal "! y s. is_exec_frag A (s,x@@y) --> is_exec_frag A (s,x)";
by (pair_induct_tac "x" [is_exec_frag_def] 1);
by (strip_tac 1);
by (Seq_case_simp_tac "s" 1);
by (pair_tac "a" 1);
by Auto_tac;
qed_spec_mp"exec_prefix2closed";

