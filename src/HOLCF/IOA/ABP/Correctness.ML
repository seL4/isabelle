(*  Title:      HOLCF/IOA/ABP/Correctness.ML
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)


goal Abschannel.thy "(? x. x=P & Q(x)) = Q(P)";
by (Fast_tac 1);
qed"exis_elim";

Delsimps [split_paired_All,Collect_empty_eq];
Addsimps 
 ([srch_asig_def, rsch_asig_def, rsch_ioa_def, srch_ioa_def, ch_ioa_def, 
   ch_asig_def, srch_actions_def, rsch_actions_def, rename_def, rename_set_def, asig_of_def, 
   actions_def, exis_elim, srch_trans_def, rsch_trans_def, ch_trans_def, 
   trans_of_def] @ asig_projections @ set_lemmas);

val abschannel_fin = [srch_fin_asig_def, rsch_fin_asig_def, 
                      rsch_fin_ioa_def, srch_fin_ioa_def, 
                      ch_fin_ioa_def,ch_fin_trans_def,ch_fin_asig_def];
Addsimps abschannel_fin;

val impl_ioas =  [Sender.sender_ioa_def,Receiver.receiver_ioa_def];
val impl_trans = [Sender.sender_trans_def,Receiver.receiver_trans_def];
val impl_asigs = [Sender.sender_asig_def,Receiver.receiver_asig_def];
Addcongs [let_weak_cong];
Addsimps [Let_def, ioa_triple_proj, starts_of_par];

val env_ioas = [Env.env_ioa_def,Env.env_asig_def,Env.env_trans_def];
val hom_ioas = env_ioas @ impl_ioas @ impl_trans @ impl_asigs @ 
               asig_projections @ set_lemmas;
Addsimps hom_ioas;



(* auxiliary function *)
fun rotate n i = EVERY(replicate n (etac revcut_rl i));

(* lemmas about reduce *)

Goal "(reduce(l)=[]) = (l=[])";  
by (induct_tac "l" 1);
by (auto_tac (claset(), simpset() addsplits [list.split]));
val l_iff_red_nil = result();

Goal "s~=[] --> hd(s)=hd(reduce(s))";
by (induct_tac "s" 1);
by (auto_tac (claset(), simpset() addsplits [list.split]));
qed"hd_is_reduce_hd";

(* to be used in the following Lemma *)
Goal "l~=[] --> reverse(reduce(l))~=[]";
by (induct_tac "l" 1);
by (auto_tac (claset(), simpset() addsplits [list.split]));
qed_spec_mp "rev_red_not_nil";

(* shows applicability of the induction hypothesis of the following Lemma 1 *)
Goal "l~=[] ==> hd(reverse(reduce(a#l))) = hd(reverse(reduce(l)))";
 by (Simp_tac 1);
 by (asm_full_simp_tac (list_ss addsplits [list.split]
                                addsimps [reverse_Cons,hd_append,
					  rev_red_not_nil])  1);
qed"last_ind_on_first";

val impl_ss = simpset() delsimps [reduce_Cons];

(* Main Lemma 1 for S_pkt in showing that reduce is refinement  *) 
Goal 
   "if x=hd(reverse(reduce(l))) & reduce(l)~=[] then   \
\      reduce(l@[x])=reduce(l) else                  \
\      reduce(l@[x])=reduce(l)@[x]"; 
by (stac split_if 1);
by (rtac conjI 1);
(* --> *)
by (induct_tac "l" 1);
by (Simp_tac 1);
by (case_tac "list=[]" 1);
 by (asm_full_simp_tac (simpset() addsimps [reverse_Nil,reverse_Cons]) 1);
 by (rtac impI 1);
by (Simp_tac 1);
by (cut_inst_tac [("l","list")] cons_not_nil 1);
 by (asm_full_simp_tac impl_ss 1);
 by (REPEAT (etac exE 1));
 by (hyp_subst_tac 1);
by (asm_full_simp_tac (impl_ss addsimps [last_ind_on_first,l_iff_red_nil]) 1);
(* <-- *)
by (simp_tac (simpset() addsimps [and_de_morgan_and_absorbe,l_iff_red_nil]) 1);
by (induct_tac "l" 1);
by (Simp_tac 1);
by (case_tac "list=[]" 1);
by (cut_inst_tac [("l","list")] cons_not_nil 2);
by (Asm_full_simp_tac 1);
by (auto_tac (claset(), 
	      impl_ss addsimps [last_ind_on_first,l_iff_red_nil] 
                      setloop split_tac [split_if]));
by (Asm_full_simp_tac 1);
qed"reduce_hd";


(* Main Lemma 2 for R_pkt in showing that reduce is refinement *)
Goal "s~=[] ==>  \
\    if hd(s)=hd(tl(s)) & tl(s)~=[] then    \
\      reduce(tl(s))=reduce(s) else      \
\      reduce(tl(s))=tl(reduce(s))"; 
by (cut_inst_tac [("l","s")] cons_not_nil 1);
by (Asm_full_simp_tac 1);
by (REPEAT (etac exE 1));
by (auto_tac (claset(), simpset() addsplits [list.split]));
val reduce_tl =result();


(*******************************************************************
          C h a n n e l   A b s t r a c t i o n
 *******************************************************************)

Delsplits [split_if]; 

Goal "is_weak_ref_map reduce ch_ioa ch_fin_ioa";
by (simp_tac (simpset() addsimps [is_weak_ref_map_def]) 1);
(* ---------------- main-part ------------------- *)
by (REPEAT (rtac allI 1));
by (rtac imp_conj_lemma 1);
by (induct_tac "a" 1);
(* ----------------- 2 cases ---------------------*)
by (ALLGOALS (simp_tac (simpset() delcongs [if_weak_cong]
				  addsimps [externals_def])));
(* fst case --------------------------------------*)
 by (rtac impI 1);
 by (rtac disjI2 1);
by (rtac reduce_hd 1);
(* snd case --------------------------------------*)
 by (rtac impI 1);
 by (REPEAT (etac conjE 1));
 by (etac disjE 1);
by (asm_full_simp_tac (simpset() addsimps [l_iff_red_nil]) 1);
by (etac (hd_is_reduce_hd RS mp) 1); 
by (asm_full_simp_tac (simpset() addsimps [l_iff_red_nil]) 1);
by (rtac conjI 1);
by (etac (hd_is_reduce_hd RS mp) 1); 
by (rtac (bool_if_impl_or RS mp) 1);
by (etac reduce_tl 1);
qed"channel_abstraction";

Addsplits [split_if]; 

Goal "is_weak_ref_map reduce srch_ioa srch_fin_ioa";
by (simp_tac (list_ss addsimps [srch_fin_ioa_def,rsch_fin_ioa_def,
 srch_ioa_def,rsch_ioa_def,rename_through_pmap,channel_abstraction]) 1);
qed"sender_abstraction";

Goal "is_weak_ref_map reduce rsch_ioa rsch_fin_ioa";
by (simp_tac (list_ss addsimps [srch_fin_ioa_def,rsch_fin_ioa_def,
 srch_ioa_def,rsch_ioa_def,rename_through_pmap,channel_abstraction]) 1);
qed"receiver_abstraction";


(* 3 thms that do not hold generally! The lucky restriction here is 
   the absence of internal actions. *)
Goal "is_weak_ref_map (%id. id) sender_ioa sender_ioa";
by (simp_tac (simpset() addsimps [is_weak_ref_map_def]) 1);
(* main-part *)
by (REPEAT (rtac allI 1));
by (induct_tac "a" 1);
(* 7 cases *)
by (ALLGOALS (simp_tac (simpset() addsimps [externals_def])));
qed"sender_unchanged";

(* 2 copies of before *)
Goal "is_weak_ref_map (%id. id) receiver_ioa receiver_ioa";
by (simp_tac (simpset() addsimps [is_weak_ref_map_def]) 1);
(* main-part *)
by (REPEAT (rtac allI 1));
by (induct_tac "a" 1);
(* 7 cases *)
by (ALLGOALS(simp_tac (simpset() addsimps [externals_def])));
qed"receiver_unchanged";

Goal "is_weak_ref_map (%id. id) env_ioa env_ioa";
by (simp_tac (simpset() addsimps [is_weak_ref_map_def]) 1);
(* main-part *)
by (REPEAT (rtac allI 1));
by (induct_tac "a" 1);
(* 7 cases *)
by (ALLGOALS(simp_tac (simpset() addsimps [externals_def])));
qed"env_unchanged";


Goal "compatible srch_ioa rsch_ioa"; 
by (simp_tac (simpset() addsimps [compatible_def,Int_def,empty_def]) 1);
by (rtac set_ext 1);
by (induct_tac "x" 1);
by (ALLGOALS(Simp_tac));
val compat_single_ch = result();

(* totally the same as before *)
Goal "compatible srch_fin_ioa rsch_fin_ioa"; 
by (simp_tac (simpset() addsimps [compatible_def,Int_def,empty_def]) 1);
by (rtac set_ext 1);
by (induct_tac "x" 1);
by (ALLGOALS(Simp_tac));
val compat_single_fin_ch = result();

val ss =
  simpset() delsimps ([trans_of_def, srch_asig_def,rsch_asig_def,
                      asig_of_def, actions_def, srch_trans_def, rsch_trans_def,
                      srch_ioa_def, srch_fin_ioa_def, rsch_fin_ioa_def, 
                      rsch_ioa_def, Sender.sender_trans_def,
                      Receiver.receiver_trans_def] @ set_lemmas);

Goal "compatible receiver_ioa (srch_ioa || rsch_ioa)";
by (simp_tac (ss addsimps [empty_def,compatible_def,asig_of_par,asig_comp_def,
			   actions_def,Int_def]) 1);
by (Simp_tac 1);
by (rtac set_ext 1);
by (induct_tac "x" 1);
by (ALLGOALS Simp_tac);
val compat_rec = result();

(* 5 proofs totally the same as before *)
Goal "compatible receiver_ioa (srch_fin_ioa || rsch_fin_ioa)";
by (simp_tac (ss addsimps [empty_def,compatible_def,asig_of_par,asig_comp_def,
			actions_def,Int_def]) 1);
by (Simp_tac 1);
by (rtac set_ext 1);
by (induct_tac "x" 1);
by (ALLGOALS Simp_tac);
val compat_rec_fin =result();

Goal "compatible sender_ioa \
\      (receiver_ioa || srch_ioa || rsch_ioa)";
by (simp_tac (ss addsimps [empty_def,compatible_def,asig_of_par,asig_comp_def,
			actions_def,Int_def]) 1);
by (Simp_tac 1);
by (rtac set_ext 1);
by (induct_tac "x" 1);
by (ALLGOALS(Simp_tac));
val compat_sen=result();

Goal "compatible sender_ioa\
\      (receiver_ioa || srch_fin_ioa || rsch_fin_ioa)";
by (simp_tac (ss addsimps [empty_def,  compatible_def,asig_of_par,asig_comp_def,
				actions_def,Int_def]) 1);
by (Simp_tac 1);
by (rtac set_ext 1);
by (induct_tac "x" 1);
by (ALLGOALS(Simp_tac));
val compat_sen_fin =result();

Goal "compatible env_ioa\
\      (sender_ioa || receiver_ioa || srch_ioa || rsch_ioa)";
by (simp_tac (ss addsimps [empty_def,compatible_def,asig_of_par,asig_comp_def,
				actions_def,Int_def]) 1);
by (Simp_tac 1);
by (rtac set_ext 1);
by (induct_tac "x" 1);
by (ALLGOALS(Simp_tac));
val compat_env=result();

Goal "compatible env_ioa\
\      (sender_ioa || receiver_ioa || srch_fin_ioa || rsch_fin_ioa)";
by (simp_tac (ss addsimps [empty_def,compatible_def,asig_of_par,asig_comp_def,
			actions_def,Int_def]) 1);
by (Simp_tac 1);
by (rtac set_ext 1);
by (induct_tac "x" 1);
by (ALLGOALS Simp_tac);
val compat_env_fin=result();


(* lemmata about externals of channels *)
Goal "externals(asig_of(srch_fin_ioa)) = externals(asig_of(srch_ioa)) &  \
\ externals(asig_of(rsch_fin_ioa)) = externals(asig_of(rsch_ioa))";
   by (simp_tac (simpset() addsimps [externals_def]) 1);
val ext_single_ch = result();





val ext_ss = [externals_of_par,ext_single_ch];
val compat_ss = [compat_single_ch,compat_single_fin_ch,compat_rec,
         compat_rec_fin,compat_sen,compat_sen_fin,compat_env,compat_env_fin];
val abstractions = [env_unchanged,sender_unchanged,
          receiver_unchanged,sender_abstraction,receiver_abstraction];


(************************************************************************
            S o u n d n e s s   o f   A b s t r a c t i o n        
*************************************************************************)

val ss = simpset() delsimps ([asig_of_def, srch_ioa_def, rsch_ioa_def,
                             srch_fin_ioa_def, rsch_fin_ioa_def] @
                            impl_ioas @ env_ioas);

(* FIX: this proof should be done with compositionality on trace level, not on 
        weak_ref_map level, as done here with fxg_is_weak_ref_map_of_product_IOA 

Goal "is_weak_ref_map  abs  system_ioa  system_fin_ioa";

by (simp_tac (impl_ss delsimps ([srch_ioa_def, rsch_ioa_def, srch_fin_ioa_def,
                                 rsch_fin_ioa_def] @ env_ioas @ impl_ioas)
                      addsimps [system_def, system_fin_def, abs_def,
                                impl_ioa_def, impl_fin_ioa_def, sys_IOA,
                                sys_fin_IOA]) 1);

by (REPEAT (EVERY[rtac fxg_is_weak_ref_map_of_product_IOA 1, 
                  simp_tac (ss addsimps abstractions) 1,
                  rtac conjI 1]));

by (ALLGOALS (simp_tac (ss addsimps ext_ss @ compat_ss))); 

qed "system_refinement";


*)
