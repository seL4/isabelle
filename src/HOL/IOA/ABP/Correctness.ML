 (*  Title:      HOL/IOA/example/Correctness.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

*)

open Correctness; open Abschannel; open Abschannel_finite;
open Impl; open Impl_finite;

goal Abschannel.thy "(? x.x=P & Q(x)) = Q(P)";
by (fast_tac HOL_cs 1);
qed"exis_elim";

val abschannel_ss = action_ss addsimps 
 ([srch_asig_def, rsch_asig_def, rsch_ioa_def, srch_ioa_def, ch_ioa_def, 
   ch_asig_def, srch_actions_def, rsch_actions_def, rename_def, asig_of_def, 
   actions_def, exis_elim, srch_trans_def, rsch_trans_def, ch_trans_def, 
   trans_of_def] 
   @ Option.option.simps @ act.simps @ asig_projections @ set_lemmas);

val abschannel_fin = [srch_fin_asig_def, rsch_fin_asig_def, 
                      rsch_fin_ioa_def, srch_fin_ioa_def, 
                      ch_fin_ioa_def,ch_fin_trans_def,ch_fin_asig_def];
val abschannel_fin_ss = abschannel_ss addsimps abschannel_fin;

val impl_ioas =  [Sender.sender_ioa_def,Receiver.receiver_ioa_def];
val impl_trans = [Sender.sender_trans_def,Receiver.receiver_trans_def];
val impl_asigs = [Sender.sender_asig_def,Receiver.receiver_asig_def];
val impl_ss = merge_ss(action_ss,list_ss) 
              addcongs [let_weak_cong] 
              addsimps [Let_def, ioa_triple_proj, starts_of_par];

val env_ioas = [Env.env_ioa_def,Env.env_asig_def,Env.env_trans_def];
val hom_ioas = env_ioas @ impl_ioas @ impl_trans @ impl_asigs @ 
               asig_projections @ set_lemmas;
val hom_ss = (impl_ss addsimps hom_ioas);

val red_ss = impl_ss addsimps [reduce_Nil,reduce_Cons];
val red_ss_ch = merge_ss(abschannel_fin_ss,red_ss);




(* auxiliary function *)
fun rotate n i = EVERY(replicate n (etac revcut_rl i));

(* lemmas about reduce *)

goal Correctness.thy "(reduce(l)=[]) = (l=[])";  
 by (rtac iffI 1);
 by (subgoal_tac "(l~=[]) --> (reduce(l)~=[])" 1);
 by (fast_tac HOL_cs 1); 
 by (List.list.induct_tac "l" 1);
 by (simp_tac red_ss 1);
 by (simp_tac red_ss 1);
 by (rtac (expand_list_case RS iffD2) 1);
 by (asm_full_simp_tac list_ss 1);
 by (REPEAT (rtac allI 1)); 
 by (rtac impI 1); 
 by (hyp_subst_tac 1);
 by (rtac (expand_if RS ssubst) 1);
 by (asm_full_simp_tac list_ss 1);
 by (asm_full_simp_tac red_ss 1);
val l_iff_red_nil = result();

goal Correctness.thy "s~=[] --> hd(s)=hd(reduce(s))";
by (List.list.induct_tac "s" 1);
by (simp_tac red_ss 1);
by (case_tac "list =[]" 1);
by (asm_full_simp_tac red_ss 1);
(* main case *)
by (rotate 1 1);
by (asm_full_simp_tac list_ss 1);
by (simp_tac red_ss 1);
by (rtac (expand_list_case RS iffD2) 1);
by (asm_full_simp_tac list_ss 1);
by (REPEAT (rtac allI 1)); 
 by (rtac impI 1); 
by (rtac (expand_if RS ssubst) 1);
by (REPEAT(hyp_subst_tac 1));
by (etac subst 1);
by (simp_tac list_ss 1);
qed"hd_is_reduce_hd";

(* to be used in the following Lemma *)
goal Correctness.thy "l~=[] --> reverse(reduce(l))~=[]";
by (List.list.induct_tac "l" 1);
by (simp_tac red_ss 1);
by (case_tac "list =[]" 1);
by (asm_full_simp_tac (red_ss addsimps [reverse_Cons]) 1);
(* main case *)
by (rotate 1 1);
by (asm_full_simp_tac red_ss 1);
by (cut_inst_tac [("l","list")] cons_not_nil 1); 
by (asm_full_simp_tac list_ss 1);
by (REPEAT (etac exE 1));
by (asm_simp_tac list_ss 1);
by (rtac (expand_if RS ssubst) 1);
by (hyp_subst_tac 1);
by (asm_full_simp_tac (list_ss addsimps [reverse_Cons]) 1); 
qed"rev_red_not_nil";

(* shows applicability of the induction hypothesis of the following Lemma 1 *)
goal Correctness.thy "!!l.[| l~=[] |] ==>   \
\   hd(reverse(reduce(a#l))) = hd(reverse(reduce(l)))";
 by (simp_tac red_ss 1);
 by (rtac (expand_list_case RS iffD2) 1);
 by (asm_full_simp_tac list_ss 1);
 by (REPEAT (rtac allI 1)); 
 by (rtac impI 1); 
 by (rtac (expand_if RS ssubst) 1);
 by (asm_full_simp_tac (list_ss addsimps [reverse_Cons,hd_append,
                          (rev_red_not_nil RS mp)])  1);
qed"last_ind_on_first";


(* Main Lemma 1 for S_pkt in showing that reduce is refinement  *) 
goal Correctness.thy 
   "if x=hd(reverse(reduce(l))) & reduce(l)~=[] then   \
\      reduce(l@[x])=reduce(l) else                  \
\      reduce(l@[x])=reduce(l)@[x]"; 
by (rtac (expand_if RS ssubst) 1);
by (rtac conjI 1);
(* --> *)
by (List.list.induct_tac "l" 1);
by (simp_tac red_ss 1);
by (case_tac "list=[]" 1);
 by (asm_full_simp_tac (red_ss  addsimps [reverse_Nil,reverse_Cons]) 1);
 by (rtac impI 1);
by (simp_tac red_ss 1);
by (cut_inst_tac [("l","list")] cons_not_nil 1);
 by (asm_full_simp_tac impl_ss 1);
 by (REPEAT (etac exE 1));
 by (hyp_subst_tac 1);
by (asm_full_simp_tac (impl_ss addsimps [last_ind_on_first,l_iff_red_nil]) 1);
(* <-- *)
by (simp_tac (red_ss addsimps [and_de_morgan_and_absorbe,l_iff_red_nil]) 1);
by (List.list.induct_tac "l" 1);
by (simp_tac red_ss 1);
by (case_tac "list=[]" 1);
 by (asm_full_simp_tac (red_ss  addsimps [reverse_Nil,reverse_Cons]) 1);
by (rtac (expand_if RS ssubst) 1);
 by (fast_tac HOL_cs 1);
 by (rtac impI 1);
by (simp_tac red_ss 1);
by (cut_inst_tac [("l","list")] cons_not_nil 1);
 by (asm_full_simp_tac impl_ss 1);
 by (REPEAT (etac exE 1));
 by (hyp_subst_tac 1);
by (asm_full_simp_tac (impl_ss addsimps [last_ind_on_first,l_iff_red_nil]) 1);
by (rtac (expand_if RS ssubst) 1);
by (rtac (expand_if RS ssubst) 1);
by (asm_full_simp_tac impl_ss 1);
qed"reduce_hd";


(* Main Lemma 2 for R_pkt in showing that reduce is refinement *)
goal Correctness.thy 
  "!! s. [| s~=[] |] ==>  \
\    if hd(s)=hd(tl(s)) & tl(s)~=[] then    \
\      reduce(tl(s))=reduce(s) else      \
\      reduce(tl(s))=tl(reduce(s))"; 
by (cut_inst_tac [("l","s")] cons_not_nil 1);
by (asm_full_simp_tac red_ss 1);
by (REPEAT (etac exE 1));
by (asm_full_simp_tac red_ss 1);
by (rtac (expand_if RS ssubst) 1);
by (rtac conjI 1);
by (simp_tac (red_ss addsimps [and_de_morgan_and_absorbe]) 2);
by (ALLGOALS (EVERY'[rtac impI,etac conjE,cut_inst_tac [("l","xs")] cons_not_nil,asm_full_simp_tac red_ss]));
by (REPEAT (etac exE 1));
by (REPEAT (etac exE 2));
by (REPEAT(hyp_subst_tac 2));
by (ALLGOALS (asm_full_simp_tac red_ss));
val reduce_tl =result();


(*******************************************************************
          C h a n n e l   A b s t r a c t i o n
 *******************************************************************)

goal Correctness.thy 
      "is_weak_pmap reduce ch_ioa ch_fin_ioa";
by (simp_tac (red_ss addsimps [Solve.is_weak_pmap_def]) 1);
by (rtac conjI 1);
(* --------------  start states ----------------- *)
by (simp_tac red_ss_ch 1);
br ballI 1;
by (asm_full_simp_tac red_ss_ch 1);
(* ---------------- main-part ------------------- *)
by (REPEAT (rtac allI 1));
by (rtac imp_conj_lemma 1);
by (act.induct_tac "a" 1);
(* ----------------- 2 cases ---------------------*)
by (ALLGOALS (simp_tac (red_ss_ch addsimps [externals_def])));
(* fst case --------------------------------------*)
 by (rtac impI 1);
 by (rtac disjI2 1);
by (rtac reduce_hd 1);
(* snd case --------------------------------------*)
 by (rtac impI 1);
 by (REPEAT (etac conjE 1));
 by (etac disjE 1);
by (asm_full_simp_tac (red_ss addsimps [l_iff_red_nil]) 1);
by (etac (hd_is_reduce_hd RS mp) 1); 
by (asm_full_simp_tac (red_ss addsimps [l_iff_red_nil]) 1);
by (rtac conjI 1);
by (etac (hd_is_reduce_hd RS mp) 1); 
by (rtac (bool_if_impl_or RS mp) 1);
by (etac reduce_tl 1);
qed"channel_abstraction";

goal Correctness.thy 
      "is_weak_pmap reduce srch_ioa srch_fin_ioa";
by (simp_tac (list_ss addsimps [srch_fin_ioa_def,rsch_fin_ioa_def,
 srch_ioa_def,rsch_ioa_def,rename_through_pmap,channel_abstraction]) 1);
qed"sender_abstraction";

goal Correctness.thy 
      "is_weak_pmap reduce rsch_ioa rsch_fin_ioa";
by (simp_tac (list_ss addsimps [srch_fin_ioa_def,rsch_fin_ioa_def,
 srch_ioa_def,rsch_ioa_def,rename_through_pmap,channel_abstraction]) 1);
qed"receiver_abstraction";


(* 3 thms that do not hold generally! The lucky restriction here is 
   the absence of internal actions. *)
goal Correctness.thy 
      "is_weak_pmap (%id.id) sender_ioa sender_ioa";
by (simp_tac (red_ss addsimps [Solve.is_weak_pmap_def]) 1);
by (rtac conjI 1);
(* start states *)
br ballI 1;
by (simp_tac red_ss_ch 1);
(* main-part *)
by (REPEAT (rtac allI 1));
by (rtac imp_conj_lemma 1);
by (Action.action.induct_tac "a" 1);
(* 7 cases *)
by (ALLGOALS (simp_tac ((hom_ss addsimps [externals_def]) setloop (split_tac [expand_if]))));
qed"sender_unchanged";

(* 2 copies of before *)
goal Correctness.thy 
      "is_weak_pmap (%id.id) receiver_ioa receiver_ioa";
by (simp_tac (red_ss addsimps [Solve.is_weak_pmap_def]) 1);
by (rtac conjI 1);
 (* start states *)
br ballI 1;
by (simp_tac red_ss_ch 1);
(* main-part *)
by (REPEAT (rtac allI 1));
by (rtac imp_conj_lemma 1);
by (Action.action.induct_tac "a" 1);
(* 7 cases *)
by (ALLGOALS (simp_tac ((hom_ss addsimps [externals_def]) setloop (split_tac [expand_if]))));
qed"receiver_unchanged";

goal Correctness.thy 
      "is_weak_pmap (%id.id) env_ioa env_ioa";
by (simp_tac (red_ss addsimps [Solve.is_weak_pmap_def]) 1);
by (rtac conjI 1);
(* start states *)
br ballI 1;
by (simp_tac red_ss_ch 1);
(* main-part *)
by (REPEAT (rtac allI 1));
by (rtac imp_conj_lemma 1);
by (Action.action.induct_tac "a" 1);
(* 7 cases *)
by (ALLGOALS (simp_tac ((hom_ss addsimps [externals_def]) setloop (split_tac [expand_if]))));
qed"env_unchanged";


goal Correctness.thy "compat_ioas srch_ioa rsch_ioa"; 
by (simp_tac (red_ss_ch addsimps [compat_ioas_def,compat_asigs_def,Int_def,empty_def]) 1);
by (rtac set_ext 1);
by (Action.action.induct_tac "x" 1);
by (ALLGOALS(simp_tac red_ss_ch));
val compat_single_ch = result();

(* totally the same as before *)
goal Correctness.thy "compat_ioas srch_fin_ioa rsch_fin_ioa"; 
by (simp_tac (red_ss_ch addsimps [compat_ioas_def,compat_asigs_def,Int_def,empty_def]) 1);
by (rtac set_ext 1);
by (Action.action.induct_tac "x" 1);
by (ALLGOALS(simp_tac red_ss_ch));
val compat_single_fin_ch = result();

goal Correctness.thy "compat_ioas receiver_ioa (srch_ioa || rsch_ioa)";
by (simp_tac (hom_ss addsimps [empty_def,compat_ioas_def,compat_asigs_def,asig_of_par,asig_comp_def,actions_def,Int_def]) 1);
by (simp_tac red_ss_ch 1);
by (rtac set_ext 1);
by (Action.action.induct_tac "x" 1);
by (ALLGOALS(simp_tac red_ss_ch));
by (ALLGOALS(simp_tac (red_ss addsimps [insert_def,Un_def]))); 
by (ALLGOALS(simp_tac (red_ss_ch addsimps [de_morgan,singleton_set])));
val compat_rec =result();

(* 5 proofs totally the same as before *)
goal Correctness.thy "compat_ioas receiver_ioa (srch_fin_ioa || rsch_fin_ioa)";
by (simp_tac (hom_ss addsimps [empty_def,compat_ioas_def,compat_asigs_def,asig_of_par,asig_comp_def,actions_def,Int_def]) 1);
by (simp_tac red_ss_ch 1);
by (rtac set_ext 1);
by (Action.action.induct_tac "x" 1);
by (ALLGOALS(simp_tac red_ss_ch));
by (ALLGOALS(simp_tac (red_ss addsimps [insert_def,Un_def]))); 
by (ALLGOALS(simp_tac (red_ss_ch addsimps [de_morgan,singleton_set])));
val compat_rec_fin =result();

goal Correctness.thy "compat_ioas sender_ioa \
\      (receiver_ioa || srch_ioa || rsch_ioa)";
by (simp_tac (hom_ss addsimps [empty_def,compat_ioas_def,compat_asigs_def,asig_of_par,asig_comp_def,actions_def,Int_def]) 1);
by (simp_tac red_ss_ch 1);
by (rtac set_ext 1);
by (Action.action.induct_tac "x" 1);
by (ALLGOALS(simp_tac red_ss_ch));
by (ALLGOALS(simp_tac (red_ss addsimps [insert_def,Un_def]))); 
by (ALLGOALS(simp_tac (red_ss_ch addsimps [de_morgan,singleton_set])));
val compat_sen=result();

goal Correctness.thy "compat_ioas sender_ioa\
\      (receiver_ioa || srch_fin_ioa || rsch_fin_ioa)";
by (simp_tac (hom_ss addsimps [empty_def,  compat_ioas_def,compat_asigs_def,asig_of_par,asig_comp_def,actions_def,Int_def]) 1);
by (simp_tac red_ss_ch 1);
by (rtac set_ext 1);
by (Action.action.induct_tac "x" 1);
by (ALLGOALS(simp_tac red_ss_ch));
by (ALLGOALS(simp_tac (red_ss addsimps [insert_def,Un_def]))); 
by (ALLGOALS(simp_tac (red_ss_ch addsimps [de_morgan,singleton_set])));
val compat_sen_fin =result();

goal Correctness.thy "compat_ioas env_ioa\
\      (sender_ioa || receiver_ioa || srch_ioa || rsch_ioa)";
by (simp_tac (hom_ss addsimps [empty_def,compat_ioas_def,compat_asigs_def,asig_of_par,asig_comp_def,actions_def,Int_def]) 1);
by (simp_tac red_ss_ch 1);
by (rtac set_ext 1);
by (Action.action.induct_tac "x" 1);
by (ALLGOALS(simp_tac red_ss_ch));
by (ALLGOALS(simp_tac (red_ss addsimps [insert_def,Un_def]))); 
by (ALLGOALS(simp_tac (red_ss_ch addsimps [de_morgan,singleton_set])));
val compat_env=result();

goal Correctness.thy "compat_ioas env_ioa\
\      (sender_ioa || receiver_ioa || srch_fin_ioa || rsch_fin_ioa)";
by (simp_tac (hom_ss addsimps [empty_def,compat_ioas_def,compat_asigs_def,asig_of_par,asig_comp_def,actions_def,Int_def]) 1);
by (simp_tac red_ss_ch 1);
by (rtac set_ext 1);
by (Action.action.induct_tac "x" 1);
by (ALLGOALS(simp_tac red_ss_ch));
by (ALLGOALS(simp_tac (red_ss addsimps [insert_def,Un_def]))); 
by (ALLGOALS(simp_tac (red_ss_ch addsimps [de_morgan,singleton_set])));
val compat_env_fin=result();


(* lemmata about externals of channels *)
goal Correctness.thy 
 "externals(asig_of(srch_fin_ioa)) = externals(asig_of(srch_ioa)) &  \
\ externals(asig_of(rsch_fin_ioa)) = externals(asig_of(rsch_ioa))";
by (simp_tac (red_ss_ch addsimps [externals_def]) 1);
val ext_single_ch = result();





val ext_ss = [externals_of_par,ext_single_ch];
val compat_ss = [compat_single_ch,compat_single_fin_ch,compat_rec,
         compat_rec_fin,compat_sen,compat_sen_fin,compat_env,compat_env_fin];
val abstractions = [env_unchanged,sender_unchanged,
          receiver_unchanged,sender_abstraction,receiver_abstraction];
val impl_ss = impl_ss addsimps [impl_def,impl_fin_def,sys_IOA, sys_fin_IOA];
val sys_ss = impl_ss addsimps [system_def, system_fin_def, abs_def];



(************************************************************************
            S o u n d n e s s   o f   A b s t r a c t i o n        
*************************************************************************)


goal Correctness.thy 
     "is_weak_pmap  abs  system_ioa  system_fin_ioa";

by (simp_tac sys_ss 1);

by (REPEAT (EVERY[rtac fxg_is_weak_pmap_of_product_IOA 1, 
                  simp_tac (red_ss addsimps abstractions) 1,
                  rtac conjI 1]));

by (ALLGOALS (simp_tac (red_ss addsimps ext_ss @ compat_ss))); 

qed "system_refinement";


