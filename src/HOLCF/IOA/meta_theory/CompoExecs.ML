(*  Title:      HOLCF/IOA/meta_theory/CompoExecs.ML
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen

Compositionality on Execution level.
*)  

Delsimps (ex_simps @ all_simps); 
Delsimps [split_paired_All];

(* ----------------------------------------------------------------------------------- *)


section "recursive equations of operators";


(* ---------------------------------------------------------------- *)
(*                               ProjA2                             *)
(* ---------------------------------------------------------------- *)


goal thy  "ProjA2`UU = UU";
by (simp_tac (simpset() addsimps [ProjA2_def]) 1);
qed"ProjA2_UU";

goal thy  "ProjA2`nil = nil";
by (simp_tac (simpset() addsimps [ProjA2_def]) 1);
qed"ProjA2_nil";

goal thy "ProjA2`((a,t)>>xs) = (a,fst t) >> ProjA2`xs";
by (simp_tac (simpset() addsimps [ProjA2_def]) 1);
qed"ProjA2_cons";


(* ---------------------------------------------------------------- *)
(*                               ProjB2                             *)
(* ---------------------------------------------------------------- *)


goal thy  "ProjB2`UU = UU";
by (simp_tac (simpset() addsimps [ProjB2_def]) 1);
qed"ProjB2_UU";

goal thy  "ProjB2`nil = nil";
by (simp_tac (simpset() addsimps [ProjB2_def]) 1);
qed"ProjB2_nil";

goal thy "ProjB2`((a,t)>>xs) = (a,snd t) >> ProjB2`xs";
by (simp_tac (simpset() addsimps [ProjB2_def]) 1);
qed"ProjB2_cons";



(* ---------------------------------------------------------------- *)
(*                             Filter_ex2                           *)
(* ---------------------------------------------------------------- *)


goal thy "Filter_ex2 sig`UU=UU";
by (simp_tac (simpset() addsimps [Filter_ex2_def]) 1);
qed"Filter_ex2_UU";

goal thy "Filter_ex2 sig`nil=nil";
by (simp_tac (simpset() addsimps [Filter_ex2_def]) 1);
qed"Filter_ex2_nil";

goal thy "Filter_ex2 sig`(at >> xs) =    \
\            (if (fst at:actions sig)    \       
\                 then at >> (Filter_ex2 sig`xs) \   
\                 else        Filter_ex2 sig`xs)";

by (asm_full_simp_tac (simpset() addsimps [Filter_ex2_def]) 1);
qed"Filter_ex2_cons";


(* ---------------------------------------------------------------- *)
(*                             stutter2                             *)
(* ---------------------------------------------------------------- *)


goal thy "stutter2 sig = (LAM ex. (%s. case ex of \
\      nil => TT \
\    | x##xs => (flift1 \ 
\            (%p.(If Def ((fst p)~:actions sig) \
\                 then Def (s=(snd p)) \
\                 else TT fi) \
\                andalso (stutter2 sig`xs) (snd p))  \
\             `x) \
\           ))";
by (rtac trans 1);
by (rtac fix_eq2 1);
by (rtac stutter2_def 1);
by (rtac beta_cfun 1);
by (simp_tac (simpset() addsimps [flift1_def]) 1);
qed"stutter2_unfold";

goal thy "(stutter2 sig`UU) s=UU";
by (stac stutter2_unfold 1);
by (Simp_tac 1);
qed"stutter2_UU";

goal thy "(stutter2 sig`nil) s = TT";
by (stac stutter2_unfold 1);
by (Simp_tac 1);
qed"stutter2_nil";

goal thy "(stutter2 sig`(at>>xs)) s = \
\              ((if (fst at)~:actions sig then Def (s=snd at) else TT) \
\                andalso (stutter2 sig`xs) (snd at))"; 
by (rtac trans 1);
by (stac stutter2_unfold 1);
by (asm_full_simp_tac (simpset() addsimps [Cons_def,flift1_def,If_and_if]) 1);
by (Simp_tac 1);
qed"stutter2_cons";


Addsimps [stutter2_UU,stutter2_nil,stutter2_cons];


(* ---------------------------------------------------------------- *)
(*                             stutter                              *)
(* ---------------------------------------------------------------- *)

goal thy "stutter sig (s, UU)";
by (simp_tac (simpset() addsimps [stutter_def]) 1);
qed"stutter_UU";

goal thy "stutter sig (s, nil)";
by (simp_tac (simpset() addsimps [stutter_def]) 1);
qed"stutter_nil";

goal thy "stutter sig (s, (a,t)>>ex) = \
\     ((a~:actions sig --> (s=t)) & stutter sig (t,ex))";
by (simp_tac (simpset() addsimps [stutter_def] 
                       setloop (split_tac [expand_if]) ) 1);
qed"stutter_cons";

(* ----------------------------------------------------------------------------------- *)

Delsimps [stutter2_UU,stutter2_nil,stutter2_cons];

val compoex_simps = [ProjA2_UU,ProjA2_nil,ProjA2_cons,
                     ProjB2_UU,ProjB2_nil,ProjB2_cons,
                     Filter_ex2_UU,Filter_ex2_nil,Filter_ex2_cons,
                     stutter_UU,stutter_nil,stutter_cons];

Addsimps compoex_simps;



(* ------------------------------------------------------------------ *)
(*                      The following lemmata aim for                 *)
(*             COMPOSITIONALITY   on    EXECUTION     Level           *)
(* ------------------------------------------------------------------ *)


(* --------------------------------------------------------------------- *)
(*  Lemma_1_1a : is_ex_fr propagates from A||B to Projections A and B    *)
(* --------------------------------------------------------------------- *)

goal thy "!s. is_exec_frag (A||B) (s,xs) \
\      -->  is_exec_frag A (fst s, Filter_ex2 (asig_of A)`(ProjA2`xs)) &\
\           is_exec_frag B (snd s, Filter_ex2 (asig_of B)`(ProjB2`xs))";

by (pair_induct_tac "xs" [is_exec_frag_def] 1);
(* main case *)
ren "ss a t" 1;
by (safe_tac set_cs);
by (REPEAT (asm_full_simp_tac (simpset() addsimps trans_of_defs2
                       setloop (split_tac [expand_if])) 1));
qed"lemma_1_1a";


(* --------------------------------------------------------------------- *)
(*  Lemma_1_1b : is_ex_fr (A||B) implies stuttering on Projections       *)
(* --------------------------------------------------------------------- *)

goal thy "!s. is_exec_frag (A||B) (s,xs) \
\      --> stutter (asig_of A) (fst s,ProjA2`xs)  &\
\          stutter (asig_of B) (snd s,ProjB2`xs)"; 

by (pair_induct_tac "xs" [stutter_def,is_exec_frag_def] 1);
(* main case *)
by (safe_tac set_cs);
by (REPEAT (asm_full_simp_tac (simpset() addsimps trans_of_defs2
                 setloop (split_tac [expand_if])) 1));
qed"lemma_1_1b";


(* --------------------------------------------------------------------- *)
(*  Lemma_1_1c : Executions of A||B have only  A- or B-actions           *)
(* --------------------------------------------------------------------- *)

goal thy "!s. (is_exec_frag (A||B) (s,xs) \
\  --> Forall (%x. fst x:act (A||B)) xs)";

by (pair_induct_tac "xs" [Forall_def,sforall_def,is_exec_frag_def] 1);
(* main case *)
by (safe_tac set_cs);
by (REPEAT (asm_full_simp_tac (simpset() addsimps trans_of_defs2 @ 
                                [actions_asig_comp,asig_of_par]) 1));
qed"lemma_1_1c";


(* ----------------------------------------------------------------------- *)
(*  Lemma_1_2 : ex A, exB, stuttering and forall a:A|B implies ex (A||B)   *)
(* ----------------------------------------------------------------------- *)

goal thy 
"!s. is_exec_frag A (fst s,Filter_ex2 (asig_of A)`(ProjA2`xs)) &\
\    is_exec_frag B (snd s,Filter_ex2 (asig_of B)`(ProjB2`xs)) &\
\    stutter (asig_of A) (fst s,(ProjA2`xs)) & \
\    stutter (asig_of B) (snd s,(ProjB2`xs)) & \
\    Forall (%x. fst x:act (A||B)) xs \
\    --> is_exec_frag (A||B) (s,xs)";

by (pair_induct_tac "xs" [Forall_def,sforall_def,
         is_exec_frag_def, stutter_def] 1);
(* main case *)
by (rtac allI 1); 
ren "ss a t s" 1;
by (asm_full_simp_tac (simpset() addsimps trans_of_defs1 @ [actions_asig_comp,asig_of_par]
               setloop (split_tac [expand_if])) 1);
by (safe_tac set_cs);
(* problem with asm_full_simp_tac: (fst s) = (fst t) is too high in assumption order ! *)
by (rotate_tac ~4 1);
by (asm_full_simp_tac (simpset() setloop (split_tac [expand_if])) 1);
by (rotate_tac ~4 1);
by (asm_full_simp_tac (simpset() setloop (split_tac [expand_if])) 1);
qed"lemma_1_2";


(* ------------------------------------------------------------------ *)
(*           COMPOSITIONALITY   on    EXECUTION     Level             *)
(*                          Main Theorem                              *)
(* ------------------------------------------------------------------ *)


goal thy 
"ex:executions(A||B) =\
\(Filter_ex (asig_of A) (ProjA ex) : executions A &\
\ Filter_ex (asig_of B) (ProjB ex) : executions B &\
\ stutter (asig_of A) (ProjA ex) & stutter (asig_of B) (ProjB ex) &\
\ Forall (%x. fst x:act (A||B)) (snd ex))";

by (simp_tac (simpset() addsimps [executions_def,ProjB_def,
                                 Filter_ex_def,ProjA_def,starts_of_par]) 1);
by (pair_tac "ex" 1);
by (rtac iffI 1);
(* ==>  *)
by (REPEAT (etac conjE 1));
by (asm_full_simp_tac (simpset() addsimps [lemma_1_1a RS spec RS mp,
               lemma_1_1b RS spec RS mp,lemma_1_1c RS spec RS mp]) 1);
(* <==  *)
by (REPEAT (etac conjE 1));
by (asm_full_simp_tac (simpset() addsimps [lemma_1_2 RS spec RS mp]) 1);
qed"compositionality_ex";


(* ------------------------------------------------------------------ *)
(*           COMPOSITIONALITY   on    EXECUTION     Level             *)
(*                            For Modules                             *)
(* ------------------------------------------------------------------ *)

goalw thy [Execs_def,par_execs_def]

"Execs (A||B) = par_execs (Execs A) (Execs B)";

by (asm_full_simp_tac (simpset() addsimps [asig_of_par]) 1);
by (rtac set_ext 1);
by (asm_full_simp_tac (simpset() addsimps [compositionality_ex,actions_of_par]) 1);
qed"compositionality_ex_modules";







