(*  Title:      HOLCF/IOA/meta_theory/Traces.ML
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen

Theorems about Executions and Traces of I/O automata in HOLCF.
*)   

Delsimps (ex_simps @ all_simps);

val exec_rws = [executions_def,is_exec_frag_def];



(* ----------------------------------------------------------------------------------- *)

section "recursive equations of operators";


(* ---------------------------------------------------------------- *)
(*                               filter_act                         *)
(* ---------------------------------------------------------------- *)


goal thy  "filter_act`UU = UU";
by (simp_tac (!simpset addsimps [filter_act_def]) 1);
qed"filter_act_UU";

goal thy  "filter_act`nil = nil";
by (simp_tac (!simpset addsimps [filter_act_def]) 1);
qed"filter_act_nil";

goal thy "filter_act`(x>>xs) = (fst x) >> filter_act`xs";
by (simp_tac (!simpset addsimps [filter_act_def]) 1);
qed"filter_act_cons";

Addsimps [filter_act_UU,filter_act_nil,filter_act_cons];


(* ---------------------------------------------------------------- *)
(*                             mk_trace                             *)
(* ---------------------------------------------------------------- *)

goal thy "mk_trace A`UU=UU";
by (simp_tac (!simpset addsimps [mk_trace_def]) 1);
qed"mk_trace_UU";

goal thy "mk_trace A`nil=nil";
by (simp_tac (!simpset addsimps [mk_trace_def]) 1);
qed"mk_trace_nil";

goal thy "mk_trace A`(at >> xs) =    \
\            (if ((fst at):ext A)    \       
\                 then (fst at) >> (mk_trace A`xs) \   
\                 else mk_trace A`xs)";

by (asm_full_simp_tac (!simpset addsimps [mk_trace_def]) 1);
qed"mk_trace_cons";

Addsimps [mk_trace_UU,mk_trace_nil,mk_trace_cons];

(* ---------------------------------------------------------------- *)
(*                             is_exec_fragC                             *)
(* ---------------------------------------------------------------- *)


goal thy "is_exec_fragC A = (LAM ex. (%s. case ex of \
\      nil => TT \
\    | x##xs => (flift1 \ 
\            (%p.Def ((s,p):trans_of A) andalso (is_exec_fragC A`xs) (snd p)) \
\             `x) \
\   ))";
by (rtac trans 1);
br fix_eq2 1;
br is_exec_fragC_def 1;
br beta_cfun 1;
by (simp_tac (!simpset addsimps [flift1_def]) 1);
qed"is_exec_fragC_unfold";

goal thy "(is_exec_fragC A`UU) s=UU";
by (stac is_exec_fragC_unfold 1);
by (Simp_tac 1);
qed"is_exec_fragC_UU";

goal thy "(is_exec_fragC A`nil) s = TT";
by (stac is_exec_fragC_unfold 1);
by (Simp_tac 1);
qed"is_exec_fragC_nil";

goal thy "(is_exec_fragC A`(pr>>xs)) s = \
\                        (Def ((s,pr):trans_of A) \
\                andalso (is_exec_fragC A`xs)(snd pr))";
br trans 1;
by (stac is_exec_fragC_unfold 1);
by (asm_full_simp_tac (!simpset addsimps [Cons_def,flift1_def]) 1);
by (Simp_tac 1);
qed"is_exec_fragC_cons";


Addsimps [is_exec_fragC_UU,is_exec_fragC_nil,is_exec_fragC_cons];


(* ---------------------------------------------------------------- *)
(*                        is_exec_frag                              *)
(* ---------------------------------------------------------------- *)

goal thy "is_exec_frag A (s, UU)";
by (simp_tac (!simpset addsimps [is_exec_frag_def]) 1);
qed"is_exec_frag_UU";

goal thy "is_exec_frag A (s, nil)";
by (simp_tac (!simpset addsimps [is_exec_frag_def]) 1);
qed"is_exec_frag_nil";

goal thy "is_exec_frag A (s, (a,t)>>ex) = \
\                               (((s,a,t):trans_of A) & \
\                               is_exec_frag A (t, ex))";
by (simp_tac (!simpset addsimps [is_exec_frag_def]) 1);
qed"is_exec_frag_cons";


(* Delsimps [is_exec_fragC_UU,is_exec_fragC_nil,is_exec_fragC_cons]; *)
Addsimps [is_exec_frag_UU,is_exec_frag_nil, is_exec_frag_cons];  


(* -------------------------------------------------------------------------------- *)

section "has_trace, mk_trace";

(* alternative definition of has_trace tailored for the refinement proof, as it does not 
   take the detour of schedules *)

goalw thy  [executions_def,mk_trace_def,has_trace_def,schedules_def,has_schedule_def] 
"has_trace A b = (? ex:executions A. b = mk_trace A`(snd ex))";

by (safe_tac set_cs);
(* 1 *)
by (res_inst_tac[("x","ex")] bexI 1);
by (stac beta_cfun 1);
by (cont_tacR 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
(* 2 *)
by (res_inst_tac[("x","filter_act`(snd ex)")] bexI 1);
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

goal thy 
  "!! A. IOA A ==> \
\ ! s. is_exec_frag A (s,xs) --> Forall (%a.a:act A) (filter_act`xs)";

by (pair_induct_tac "xs" [is_exec_frag_def,Forall_def,sforall_def] 1);
(* main case *)
ren "ss a t" 1;
by (safe_tac set_cs);
by (REPEAT (asm_full_simp_tac (!simpset addsimps [ioa_def,state_trans_def]) 1));
qed"execfrag_in_sig";

goal thy 
  "!! A.[|  IOA A; x:executions A |] ==> \
\ Forall (%a.a:act A) (filter_act`(snd x))";

by (asm_full_simp_tac (!simpset addsimps [executions_def]) 1);
by (pair_tac "x" 1);
br (execfrag_in_sig RS spec RS mp) 1;
auto();
qed"exec_in_sig";

goalw thy [schedules_def,has_schedule_def]
  "!! A.[|  IOA A; x:schedules A |] ==> \
\   Forall (%a.a:act A) x";

by (fast_tac (!claset addSIs [exec_in_sig]) 1);
qed"scheds_in_sig";


(* -------------------------------------------------------------------------------- *)

section "executions are prefix closed";

(* only admissible in y, not if done in x !! *)
goal thy "!x s. is_exec_frag A (s,x) & y<<x  --> is_exec_frag A (s,y)";
by (pair_induct_tac "y" [is_exec_frag_def] 1);
by (strip_tac 1);
by (Seq_case_simp_tac "xa" 1);
by (pair_tac "a" 1);
auto();
qed"execfrag_prefixclosed";

bind_thm ("exec_prefixclosed",conjI RS (execfrag_prefixclosed RS spec RS spec RS mp));


(* second prefix notion for Finite x *)

goal thy "! y s.is_exec_frag A (s,x@@y) --> is_exec_frag A (s,x)";
by (pair_induct_tac "x" [is_exec_frag_def] 1);
by (strip_tac 1);
by (Seq_case_simp_tac "s" 1);
by (pair_tac "a" 1);
auto();
qed_spec_mp"exec_prefix2closed";

