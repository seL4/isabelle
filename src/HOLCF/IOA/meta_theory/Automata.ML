(*  Title:      HOLCF/IOA/meta_theory/Automata.ML
    ID:         $$
    Author:     Olaf Mueller, Tobias Nipkow, Konrad Slind
    Copyright   1994, 1996  TU Muenchen

The I/O automata of Lynch and Tuttle.
*)

(* Has been removed from HOL-simpset, who knows why? *)
Addsimps [Let_def];

open reachable;

val ioa_projections = [asig_of_def, starts_of_def, trans_of_def];

(* ----------------------------------------------------------------------------------- *)

section "asig_of, starts_of, trans_of";


goal thy
"asig_of((x,y,z)) = x & starts_of((x,y,z)) = y & trans_of((x,y,z)) = z";
  by (simp_tac (!simpset addsimps ioa_projections) 1);
qed "ioa_triple_proj";

goalw thy [ioa_def,state_trans_def,actions_def, is_asig_def]
  "!!A. [| IOA(A); (s1,a,s2):trans_of(A) |] ==> a:act A";
  by (REPEAT(etac conjE 1));
  by (EVERY1[etac allE, etac impE, atac]);
  by (Asm_full_simp_tac 1);
qed "trans_in_actions";

goal thy
"starts_of(A || B) = {p. fst(p):starts_of(A) & snd(p):starts_of(B)}";
  by(simp_tac (!simpset addsimps (par_def::ioa_projections)) 1);
qed "starts_of_par";


(* ----------------------------------------------------------------------------------- *)

section "actions and par";


goal thy 
"actions(asig_comp a b) = actions(a) Un actions(b)";
  by(simp_tac (!simpset addsimps
               ([actions_def,asig_comp_def]@asig_projections)) 1);
  by (fast_tac (set_cs addSIs [equalityI]) 1);
qed "actions_asig_comp";


goal thy "asig_of(A || B) = asig_comp (asig_of A) (asig_of B)";
  by(simp_tac (!simpset addsimps (par_def::ioa_projections)) 1);
qed "asig_of_par";


goal thy "ext (A1||A2) =    \
\  (ext A1) Un (ext A2)";
by (asm_full_simp_tac (!simpset addsimps [externals_def,asig_of_par,asig_comp_def,
      asig_inputs_def,asig_outputs_def,Un_def,set_diff_def]) 1);
by (rtac set_ext 1); 
by (fast_tac set_cs 1);
qed"externals_of_par"; 

goal thy "act (A1||A2) =    \
\  (act A1) Un (act A2)";
by (asm_full_simp_tac (!simpset addsimps [actions_def,asig_of_par,asig_comp_def,
      asig_inputs_def,asig_outputs_def,asig_internals_def,Un_def,set_diff_def]) 1);
by (rtac set_ext 1); 
by (fast_tac set_cs 1);
qed"actions_of_par"; 


goal thy "inp (A1||A2) =\
\         ((inp A1) Un (inp A2)) - ((out A1) Un (out A2))";
by (asm_full_simp_tac (!simpset addsimps [actions_def,asig_of_par,asig_comp_def,
      asig_inputs_def,asig_outputs_def,Un_def,set_diff_def]) 1);
qed"inputs_of_par";
  
goal thy "out (A1||A2) =\
\         (out A1) Un (out A2)";
by (asm_full_simp_tac (!simpset addsimps [actions_def,asig_of_par,asig_comp_def,
      asig_outputs_def,Un_def,set_diff_def]) 1);
qed"outputs_of_par";


(* ---------------------------------------------------------------------------------- *)

section "actions and compatibility"; 

goal thy"compat_ioas A B = compat_ioas B A";
by (asm_full_simp_tac (!simpset addsimps [compat_ioas_def,compat_asigs_def,Int_commute]) 1);
auto();
qed"compat_commute";

goalw thy [externals_def,actions_def,compat_ioas_def,compat_asigs_def]
 "!! a. [| compat_ioas A1 A2; a:ext A1|] ==> a~:int A2";
by (Asm_full_simp_tac 1);
by (best_tac (set_cs addEs [equalityCE]) 1);
qed"ext1_is_not_int2";

(* just commuting the previous one: better commute compat_ioas *)
goalw thy [externals_def,actions_def,compat_ioas_def,compat_asigs_def]
 "!! a. [| compat_ioas A2 A1 ; a:ext A1|] ==> a~:int A2";
by (Asm_full_simp_tac 1);
by (best_tac (set_cs addEs [equalityCE]) 1);
qed"ext2_is_not_int1";

bind_thm("ext1_ext2_is_not_act2",ext1_is_not_int2 RS int_and_ext_is_act);
bind_thm("ext1_ext2_is_not_act1",ext2_is_not_int1 RS int_and_ext_is_act);

goalw thy  [externals_def,actions_def,compat_ioas_def,compat_asigs_def]
 "!! x. [| compat_ioas A B; x:int A |] ==> x~:ext B";
by (Asm_full_simp_tac 1);
by (best_tac (set_cs addEs [equalityCE]) 1);
qed"intA_is_not_extB";

goalw thy [externals_def,actions_def,compat_ioas_def,compat_asigs_def,is_asig_def,asig_of_def]
"!! a. [| compat_ioas A B; a:int A |] ==> a ~: act B";
by (Asm_full_simp_tac 1);
by (best_tac (set_cs addEs [equalityCE]) 1);
qed"intA_is_not_actB";


(* ---------------------------------------------------------------------------------- *)

section "invariants";

val [p1,p2] = goalw thy [invariant_def]
  "[| !!s. s:starts_of(A) ==> P(s);     \
\     !!s t a. [|reachable A s; P(s)|] ==> (s,a,t): trans_of(A) --> P(t) |] \
\  ==> invariant A P";
by (rtac allI 1);
by (rtac impI 1);
by (res_inst_tac [("za","s")] reachable.induct 1);
by (atac 1);
by (etac p1 1);
by (eres_inst_tac [("s1","sa")] (p2 RS mp) 1);
by (REPEAT (atac 1));
qed"invariantI";


val [p1,p2] = goal thy
 "[| !!s. s : starts_of(A) ==> P(s); \
\   !!s t a. reachable A s ==> P(s) --> (s,a,t):trans_of(A) --> P(t) \
\ |] ==> invariant A P";
  by (fast_tac (HOL_cs addSIs [invariantI] addSDs [p1,p2]) 1);
qed "invariantI1";

val [p1,p2] = goalw thy [invariant_def]
"[| invariant A P; reachable A s |] ==> P(s)";
   br(p2 RS (p1 RS spec RS mp))1;
qed "invariantE";

(* ---------------------------------------------------------------------------------- *)

section "restrict";


goal thy "starts_of(restrict ioa acts) = starts_of(ioa) &     \
\             trans_of(restrict ioa acts) = trans_of(ioa)";
by(simp_tac (!simpset addsimps ([restrict_def]@ioa_projections)) 1);
qed "cancel_restrict_a";

goal thy "reachable (restrict ioa acts) s = reachable ioa s";
by (rtac iffI 1);
be reachable.induct 1;
by(asm_full_simp_tac (!simpset addsimps [cancel_restrict_a,reachable_0]) 1);
by (etac reachable_n 1);
by(asm_full_simp_tac (!simpset addsimps [cancel_restrict_a]) 1);
(* <--  *)
be reachable.induct 1;
by (rtac reachable_0 1);
by(asm_full_simp_tac (!simpset addsimps [cancel_restrict_a]) 1);
by (etac reachable_n 1);
by(asm_full_simp_tac (!simpset addsimps [cancel_restrict_a]) 1);
qed "cancel_restrict_b";

goal thy "starts_of(restrict ioa acts) = starts_of(ioa) &     \
\             trans_of(restrict ioa acts) = trans_of(ioa) & \
\             reachable (restrict ioa acts) s = reachable ioa s";
by (simp_tac (!simpset addsimps [cancel_restrict_a,cancel_restrict_b]) 1);
qed"cancel_restrict";

(* ---------------------------------------------------------------------------------- *)

section "rename";



goal thy "!!f. s -a--(rename C f)-> t ==> (? x. Some(x) = f(a) & s -x--C-> t)";
by (asm_full_simp_tac (!simpset addsimps [Let_def,rename_def,trans_of_def]) 1);
qed"trans_rename";


goal thy "!!s.[| reachable (rename C g) s |] ==> reachable C s";
be reachable.induct 1;
br reachable_0 1;
by(asm_full_simp_tac (!simpset addsimps [rename_def]@ioa_projections) 1);
bd trans_rename 1;
be exE 1;
be conjE 1;
be reachable_n 1;
ba 1;
qed"reachable_rename";



(* ---------------------------------------------------------------------------------- *)

section "trans_of(A||B)";


goal thy "!!A.[|(s,a,t):trans_of (A||B); a:act A|] \
\             ==> (fst s,a,fst t):trans_of A";
by (asm_full_simp_tac (!simpset addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_A_proj";

goal thy "!!A.[|(s,a,t):trans_of (A||B); a:act B|] \
\             ==> (snd s,a,snd t):trans_of B";
by (asm_full_simp_tac (!simpset addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_B_proj";

goal thy "!!A.[|(s,a,t):trans_of (A||B); a~:act A|]\
\             ==> fst s = fst t";
by (asm_full_simp_tac (!simpset addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_A_proj2";

goal thy "!!A.[|(s,a,t):trans_of (A||B); a~:act B|]\
\             ==> snd s = snd t";
by (asm_full_simp_tac (!simpset addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_B_proj2";

goal thy "!!A.(s,a,t):trans_of (A||B) \
\              ==> a :act A | a :act B";
by (asm_full_simp_tac (!simpset addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_AB_proj";

goal thy "!!A. [|a:act A;a:act B;\
\      (fst s,a,fst t):trans_of A;(snd s,a,snd t):trans_of B|]\
\  ==> (s,a,t):trans_of (A||B)";
by (asm_full_simp_tac (!simpset addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_AB";

goal thy "!!A. [|a:act A;a~:act B;\
\      (fst s,a,fst t):trans_of A;snd s=snd t|]\
\  ==> (s,a,t):trans_of (A||B)";
by (asm_full_simp_tac (!simpset addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_A_notB";

goal thy "!!A. [|a~:act A;a:act B;\
\      (snd s,a,snd t):trans_of B;fst s=fst t|]\
\  ==> (s,a,t):trans_of (A||B)";
by (asm_full_simp_tac (!simpset addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_notA_B";

val trans_of_defs1 = [trans_AB,trans_A_notB,trans_notA_B];
val trans_of_defs2 = [trans_A_proj,trans_B_proj,trans_A_proj2,
                      trans_B_proj2,trans_AB_proj];


goal thy 
"(s,a,t) : trans_of(A || B || C || D) =                                      \
\ ((a:actions(asig_of(A)) | a:actions(asig_of(B)) | a:actions(asig_of(C)) |  \
\   a:actions(asig_of(D))) &                                                 \
\  (if a:actions(asig_of(A)) then (fst(s),a,fst(t)):trans_of(A)              \
\   else fst t=fst s) &                                                      \
\  (if a:actions(asig_of(B)) then (fst(snd(s)),a,fst(snd(t))):trans_of(B)    \
\   else fst(snd(t))=fst(snd(s))) &                                          \
\  (if a:actions(asig_of(C)) then                                            \
\     (fst(snd(snd(s))),a,fst(snd(snd(t)))):trans_of(C)                      \
\   else fst(snd(snd(t)))=fst(snd(snd(s)))) &                                \
\  (if a:actions(asig_of(D)) then                                            \
\     (snd(snd(snd(s))),a,snd(snd(snd(t)))):trans_of(D)                      \
\   else snd(snd(snd(t)))=snd(snd(snd(s)))))";

  by(simp_tac (!simpset addsimps ([par_def,actions_asig_comp,Pair_fst_snd_eq,Let_def]@
                            ioa_projections)
                  setloop (split_tac [expand_if])) 1);
qed "trans_of_par4";



