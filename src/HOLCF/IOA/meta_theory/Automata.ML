(*  Title:      HOLCF/IOA/meta_theory/Automata.ML
    ID:         $Id$
    Author:     Olaf Mueller, Tobias Nipkow, Konrad Slind
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The I/O automata of Lynch and Tuttle.
*)

(* this modification of the simpset is local to this file *)
Delsimps [split_paired_Ex];

val ioa_projections = [asig_of_def, starts_of_def, trans_of_def,wfair_of_def,sfair_of_def];

(* ------------------------------------------------------------------------- *)

section "asig_of, starts_of, trans_of";


Goal
 "((asig_of (x,y,z,w,s)) = x)   & \
\ ((starts_of (x,y,z,w,s)) = y) & \
\ ((trans_of (x,y,z,w,s)) = z)  & \
\ ((wfair_of (x,y,z,w,s)) = w) & \
\ ((sfair_of (x,y,z,w,s)) = s)";
  by (simp_tac (simpset() addsimps ioa_projections) 1);
qed "ioa_triple_proj";

Goalw [is_trans_of_def,actions_def, is_asig_def]
  "[| is_trans_of A; (s1,a,s2):trans_of(A) |] ==> a:act A";
  by (REPEAT(etac conjE 1));
  by (EVERY1[etac allE, etac impE, atac]);
  by (Asm_full_simp_tac 1);
qed "trans_in_actions";

Goal
"starts_of(A || B) = {p. fst(p):starts_of(A) & snd(p):starts_of(B)}";
  by (simp_tac (simpset() addsimps (par_def::ioa_projections)) 1);
qed "starts_of_par";

Goal
"trans_of(A || B) = {tr. let s = fst(tr); a = fst(snd(tr)); t = snd(snd(tr)) \       
\            in (a:act A | a:act B) & \
\               (if a:act A then       \                
\                  (fst(s),a,fst(t)):trans_of(A) \                    
\                else fst(t) = fst(s))            \                      
\               &                                  \                     
\               (if a:act B then                    \   
\                  (snd(s),a,snd(t)):trans_of(B)     \                
\                else snd(t) = snd(s))}";

by (simp_tac (simpset() addsimps (par_def::ioa_projections)) 1);
qed "trans_of_par";


(* ------------------------------------------------------------------------- *)

section "actions and par";


Goal 
"actions(asig_comp a b) = actions(a) Un actions(b)";
  by (simp_tac (simpset() addsimps
               ([actions_def,asig_comp_def]@asig_projections)) 1);
  by (fast_tac (set_cs addSIs [equalityI]) 1);
qed "actions_asig_comp";


Goal "asig_of(A || B) = asig_comp (asig_of A) (asig_of B)";
  by (simp_tac (simpset() addsimps (par_def::ioa_projections)) 1);
qed "asig_of_par";


Goal "ext (A1||A2) =    \
\  (ext A1) Un (ext A2)";
by (asm_full_simp_tac (simpset() addsimps [externals_def,asig_of_par,asig_comp_def,
      asig_inputs_def,asig_outputs_def,Un_def,set_diff_def]) 1);
by (rtac set_ext 1); 
by (fast_tac set_cs 1);
qed"externals_of_par"; 

Goal "act (A1||A2) =    \
\  (act A1) Un (act A2)";
by (asm_full_simp_tac (simpset() addsimps [actions_def,asig_of_par,asig_comp_def,
      asig_inputs_def,asig_outputs_def,asig_internals_def,Un_def,set_diff_def]) 1);
by (rtac set_ext 1); 
by (fast_tac set_cs 1);
qed"actions_of_par"; 

Goal "inp (A1||A2) =\
\         ((inp A1) Un (inp A2)) - ((out A1) Un (out A2))";
by (asm_full_simp_tac (simpset() addsimps [actions_def,asig_of_par,asig_comp_def,
      asig_inputs_def,asig_outputs_def,Un_def,set_diff_def]) 1);
qed"inputs_of_par";
  
Goal "out (A1||A2) =\
\         (out A1) Un (out A2)";
by (asm_full_simp_tac (simpset() addsimps [actions_def,asig_of_par,asig_comp_def,
      asig_outputs_def,Un_def,set_diff_def]) 1);
qed"outputs_of_par";

Goal "int (A1||A2) =\
\         (int A1) Un (int A2)";
by (asm_full_simp_tac (simpset() addsimps [actions_def,asig_of_par,asig_comp_def,
      asig_inputs_def,asig_outputs_def,asig_internals_def,Un_def,set_diff_def]) 1);
qed"internals_of_par";

(* ------------------------------------------------------------------------ *)

section "actions and compatibility"; 

Goal"compatible A B = compatible B A";
by (asm_full_simp_tac (simpset() addsimps [compatible_def,Int_commute]) 1);
by Auto_tac;
qed"compat_commute";

Goalw [externals_def,actions_def,compatible_def]
 "[| compatible A1 A2; a:ext A1|] ==> a~:int A2";
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed"ext1_is_not_int2";

(* just commuting the previous one: better commute compatible *)
Goalw [externals_def,actions_def,compatible_def]
 "[| compatible A2 A1 ; a:ext A1|] ==> a~:int A2";
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed"ext2_is_not_int1";

bind_thm("ext1_ext2_is_not_act2",ext1_is_not_int2 RS int_and_ext_is_act);
bind_thm("ext1_ext2_is_not_act1",ext2_is_not_int1 RS int_and_ext_is_act);

Goalw  [externals_def,actions_def,compatible_def]
 "[| compatible A B; x:int A |] ==> x~:ext B";
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed"intA_is_not_extB";

Goalw [externals_def,actions_def,compatible_def,is_asig_def,asig_of_def]
"[| compatible A B; a:int A |] ==> a ~: act B";
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed"intA_is_not_actB";

(* the only one that needs disjointness of outputs and of internals and _all_ acts *)
Goalw [asig_outputs_def,asig_internals_def,actions_def,asig_inputs_def,
    compatible_def,is_asig_def,asig_of_def]
"[| compatible A B; a:out A ;a:act B|] ==> a : inp B";
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed"outAactB_is_inpB";

(* needed for propagation of input_enabledness from A,B to A||B *)
Goalw [asig_outputs_def,asig_internals_def,actions_def,asig_inputs_def,
    compatible_def,is_asig_def,asig_of_def]
"[| compatible A B; a:inp A ;a:act B|] ==> a : inp B | a: out B";
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed"inpAAactB_is_inpBoroutB";

(* ------------------------------------------------------------------------- *)

section "input_enabledness and par";  


(* ugly case distinctions. Heart of proof: 
     1. inpAAactB_is_inpBoroutB ie. internals are really hidden.
     2. inputs_of_par: outputs are no longer inputs of par. This is important here *)
Goalw [input_enabled_def] 
"[| compatible A B; input_enabled A; input_enabled B|] \
\     ==> input_enabled (A||B)";
by (asm_full_simp_tac (simpset()addsimps[Let_def,inputs_of_par,trans_of_par])1);
by (safe_tac set_cs);
by (asm_full_simp_tac (simpset() addsimps [inp_is_act]) 1);
by (asm_full_simp_tac (simpset() addsimps [inp_is_act]) 2);
(* a: inp A *)
by (case_tac "a:act B" 1);
(* a:act B *)
by (eres_inst_tac [("x","a")] allE 1);
by (Asm_full_simp_tac 1);
by (dtac inpAAactB_is_inpBoroutB 1);
by (assume_tac 1);
by (assume_tac 1);
by (eres_inst_tac [("x","a")] allE 1);
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("x","aa")] allE 1);
by (eres_inst_tac [("x","b")] allE 1);
by (etac exE 1);
by (etac exE 1);
by (res_inst_tac [("x","(s2,s2a)")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [inp_is_act]) 1);
(* a~: act B*)
by (asm_full_simp_tac (simpset() addsimps [inp_is_act]) 1);
by (eres_inst_tac [("x","a")] allE 1);
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("x","aa")] allE 1);
by (etac exE 1);
by (res_inst_tac [("x","(s2,b)")] exI 1);
by (Asm_full_simp_tac 1);

(* a:inp B *)
by (case_tac "a:act A" 1);
(* a:act A *)
by (eres_inst_tac [("x","a")] allE 1);
by (eres_inst_tac [("x","a")] allE 1);
by (asm_full_simp_tac (simpset() addsimps [inp_is_act]) 1);
by (forw_inst_tac [("A1","A")] (compat_commute RS iffD1) 1);
by (dtac inpAAactB_is_inpBoroutB 1);
back();
by (assume_tac 1);
by (assume_tac 1);
by (Asm_full_simp_tac 1);
by (rotate_tac ~1 1);
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("x","aa")] allE 1);
by (eres_inst_tac [("x","b")] allE 1);
by (etac exE 1);
by (etac exE 1);
by (res_inst_tac [("x","(s2,s2a)")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [inp_is_act]) 1);
(* a~: act B*)
by (asm_full_simp_tac (simpset() addsimps [inp_is_act]) 1);
by (eres_inst_tac [("x","a")] allE 1);
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("x","a")] allE 1);
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("x","b")] allE 1);
by (etac exE 1);
by (res_inst_tac [("x","(aa,s2)")] exI 1);
by (Asm_full_simp_tac 1);
qed"input_enabled_par";

(* ------------------------------------------------------------------------- *)

section "invariants";

val [p1,p2] = goalw thy [invariant_def]
  "[| !!s. s:starts_of(A) ==> P(s);     \
\     !!s t a. [|reachable A s; P(s)|] ==> (s,a,t): trans_of(A) --> P(t) |] \
\  ==> invariant A P";
by (rtac allI 1);
by (rtac impI 1);
by (res_inst_tac [("xa","s")] reachable.induct 1);
by (atac 1);
by (etac p1 1);
by (eres_inst_tac [("s1","sa")] (p2 RS mp) 1);
by (REPEAT (atac 1));
qed"invariantI";


val [p1,p2] = goal thy
 "[| !!s. s : starts_of(A) ==> P(s); \
\    !!s t a. reachable A s ==> P(s) --> (s,a,t):trans_of(A) --> P(t) \
\ |] ==> invariant A P";
  by (fast_tac (HOL_cs addSIs [invariantI] addSDs [p1,p2]) 1);
qed "invariantI1";

Goalw [invariant_def] "[| invariant A P; reachable A s |] ==> P(s)";
by (Blast_tac 1);   
qed "invariantE";

(* ------------------------------------------------------------------------- *)

section "restrict";


val reachable_0 = reachable.reachable_0
and reachable_n = reachable.reachable_n;

Goal "starts_of(restrict ioa acts) = starts_of(ioa) &     \
\         trans_of(restrict ioa acts) = trans_of(ioa)";
by (simp_tac (simpset() addsimps ([restrict_def]@ioa_projections)) 1);
qed "cancel_restrict_a";

Goal "reachable (restrict ioa acts) s = reachable ioa s";
by (rtac iffI 1);
by (etac reachable.induct 1);
by (asm_full_simp_tac (simpset() addsimps [cancel_restrict_a,reachable_0]) 1);
by (etac reachable_n 1);
by (asm_full_simp_tac (simpset() addsimps [cancel_restrict_a]) 1);
(* <--  *)
by (etac reachable.induct 1);
by (rtac reachable_0 1);
by (asm_full_simp_tac (simpset() addsimps [cancel_restrict_a]) 1);
by (etac reachable_n 1);
by (asm_full_simp_tac (simpset() addsimps [cancel_restrict_a]) 1);
qed "cancel_restrict_b";

Goal "act (restrict A acts) = act A";
by (simp_tac (simpset() addsimps [actions_def,asig_internals_def,
        asig_outputs_def,asig_inputs_def,externals_def,asig_of_def,restrict_def,
        restrict_asig_def]) 1);
by Auto_tac;
qed"acts_restrict";

Goal "starts_of(restrict ioa acts) = starts_of(ioa) &     \
\         trans_of(restrict ioa acts) = trans_of(ioa) & \
\         reachable (restrict ioa acts) s = reachable ioa s & \
\         act (restrict A acts) = act A";
  by (simp_tac (simpset() addsimps [cancel_restrict_a,cancel_restrict_b,acts_restrict]) 1);
qed"cancel_restrict";

(* ------------------------------------------------------------------------- *)

section "rename";



Goal "s -a--(rename C f)-> t ==> (? x. Some(x) = f(a) & s -x--C-> t)";
by (asm_full_simp_tac (simpset() addsimps [Let_def,rename_def,trans_of_def]) 1);
qed"trans_rename";


Goal "[| reachable (rename C g) s |] ==> reachable C s";
by (etac reachable.induct 1);
by (rtac reachable_0 1);
by (asm_full_simp_tac (simpset() addsimps [rename_def]@ioa_projections) 1);
by (dtac trans_rename 1);
by (etac exE 1);
by (etac conjE 1);
by (etac reachable_n 1);
by (assume_tac 1);
qed"reachable_rename";



(* ------------------------------------------------------------------------- *)

section "trans_of(A||B)";


Goal "[|(s,a,t):trans_of (A||B); a:act A|] \
\             ==> (fst s,a,fst t):trans_of A";
by (asm_full_simp_tac (simpset() addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_A_proj";

Goal "[|(s,a,t):trans_of (A||B); a:act B|] \
\             ==> (snd s,a,snd t):trans_of B";
by (asm_full_simp_tac (simpset() addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_B_proj";

Goal "[|(s,a,t):trans_of (A||B); a~:act A|]\
\             ==> fst s = fst t";
by (asm_full_simp_tac (simpset() addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_A_proj2";

Goal "[|(s,a,t):trans_of (A||B); a~:act B|]\
\             ==> snd s = snd t";
by (asm_full_simp_tac (simpset() addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_B_proj2";

Goal "(s,a,t):trans_of (A||B) \
\              ==> a :act A | a :act B";
by (asm_full_simp_tac (simpset() addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_AB_proj";

Goal "[|a:act A;a:act B;\
\      (fst s,a,fst t):trans_of A;(snd s,a,snd t):trans_of B|]\
\  ==> (s,a,t):trans_of (A||B)";
by (asm_full_simp_tac (simpset() addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_AB";

Goal "[|a:act A;a~:act B;\
\      (fst s,a,fst t):trans_of A;snd s=snd t|]\
\  ==> (s,a,t):trans_of (A||B)";
by (asm_full_simp_tac (simpset() addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_A_notB";

Goal "[|a~:act A;a:act B;\
\      (snd s,a,snd t):trans_of B;fst s=fst t|]\
\  ==> (s,a,t):trans_of (A||B)";
by (asm_full_simp_tac (simpset() addsimps [Let_def,par_def,trans_of_def]) 1);
qed"trans_notA_B";

val trans_of_defs1 = [trans_AB,trans_A_notB,trans_notA_B];
val trans_of_defs2 = [trans_A_proj,trans_B_proj,trans_A_proj2,
                      trans_B_proj2,trans_AB_proj];


Goal 
"((s,a,t) : trans_of(A || B || C || D)) =                                    \
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

  by (simp_tac (simpset() addsimps ([par_def,actions_asig_comp,Pair_fst_snd_eq,Let_def]@
                            ioa_projections)) 1);
qed "trans_of_par4";


(* ------------------------------------------------------------------------- *)

section "proof obligation generator for IOA requirements";  

(* without assumptions on A and B because is_trans_of is also incorporated in ||def *)
Goalw [is_trans_of_def] "is_trans_of (A||B)";
by (simp_tac (simpset() addsimps [Let_def,actions_of_par,trans_of_par]) 1);
qed"is_trans_of_par";

Goalw [is_trans_of_def] 
"is_trans_of A ==> is_trans_of (restrict A acts)";
by (asm_simp_tac (simpset() addsimps [cancel_restrict,acts_restrict])1);
qed"is_trans_of_restrict";

Goalw [is_trans_of_def,restrict_def,restrict_asig_def] 
"is_trans_of A ==> is_trans_of (rename A f)";
by (asm_full_simp_tac
    (simpset() addsimps [Let_def,actions_def,trans_of_def, asig_internals_def,
			 asig_outputs_def,asig_inputs_def,externals_def,
			 asig_of_def,rename_def,rename_set_def]) 1);
by (Blast_tac 1);
qed"is_trans_of_rename";

Goal "[| is_asig_of A; is_asig_of B; compatible A B|]  \
\         ==> is_asig_of (A||B)";
by (asm_full_simp_tac (simpset() addsimps [is_asig_of_def,asig_of_par,
       asig_comp_def,compatible_def,asig_internals_def,asig_outputs_def,
     asig_inputs_def,actions_def,is_asig_def]) 1);
by (asm_full_simp_tac (simpset() addsimps [asig_of_def]) 1);
by Auto_tac;
qed"is_asig_of_par";

Goalw [is_asig_of_def,is_asig_def,asig_of_def,restrict_def,restrict_asig_def,
           asig_internals_def,asig_outputs_def,asig_inputs_def,externals_def,o_def] 
"is_asig_of A ==> is_asig_of (restrict A f)";
by (Asm_full_simp_tac 1);
by Auto_tac;
qed"is_asig_of_restrict";

Goal "is_asig_of A ==> is_asig_of (rename A f)";
by (asm_full_simp_tac (simpset() addsimps [is_asig_of_def,
     rename_def,rename_set_def,asig_internals_def,asig_outputs_def,
     asig_inputs_def,actions_def,is_asig_def,asig_of_def]) 1);
by Auto_tac; 
by   (ALLGOALS(dres_inst_tac [("s","Some ?x")] sym THEN' Asm_full_simp_tac));
by   (ALLGOALS(Blast_tac));
qed"is_asig_of_rename";


Addsimps [is_asig_of_par,is_asig_of_restrict,is_asig_of_rename,
          is_trans_of_par,is_trans_of_restrict,is_trans_of_rename];


Goalw [compatible_def]
"[|compatible A B; compatible A C |]==> compatible A (B||C)";
by (asm_full_simp_tac (simpset() addsimps [internals_of_par, 
   outputs_of_par,actions_of_par]) 1);
by Auto_tac;
qed"compatible_par";

(*  better derive by previous one and compat_commute *)
Goalw [compatible_def]
"[|compatible A C; compatible B C |]==> compatible (A||B) C";
by (asm_full_simp_tac (simpset() addsimps [internals_of_par, 
   outputs_of_par,actions_of_par]) 1);
by Auto_tac;
qed"compatible_par2";

Goalw [compatible_def]
"[| compatible A B; (ext B - S) Int ext A = {}|] \
\     ==> compatible A (restrict B S)";
by (asm_full_simp_tac (simpset() addsimps [ioa_triple_proj,asig_triple_proj,
          externals_def,restrict_def,restrict_asig_def,actions_def]) 1);
by Auto_tac;
qed"compatible_restrict";


Addsimps [split_paired_Ex];
