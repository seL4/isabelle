(*  Title:      HOL/IOA/NTP/Impl.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

The implementation --- Invariants
*)


Addsimps [Let_def, le_SucI];


open Abschannel Impl;

val impl_ioas =
  [Impl.impl_def,
   Sender.sender_ioa_def, 
   Receiver.receiver_ioa_def, 
   srch_ioa_thm RS eq_reflection,
   rsch_ioa_thm RS eq_reflection];

val transitions = [Sender.sender_trans_def, Receiver.receiver_trans_def,
                   srch_trans_def, rsch_trans_def];
 

Addsimps [ioa_triple_proj, starts_of_par, trans_of_par4,
          in_sender_asig, in_receiver_asig, in_srch_asig,
          in_rsch_asig];
Addcongs [let_weak_cong];

Goal
  "fst(x) = sen(x)            & \
\  fst(snd(x)) = rec(x)       & \
\  fst(snd(snd(x))) = srch(x) & \
\  snd(snd(snd(x))) = rsch(x)";
by (simp_tac (simpset() addsimps
             [sen_def,rec_def,srch_def,rsch_def]) 1);
Addsimps [result()];

Goal "a:actions(sender_asig)   \
\            | a:actions(receiver_asig) \
\            | a:actions(srch_asig)     \
\            | a:actions(rsch_asig)";
  by (induct_tac "a" 1);
  by (ALLGOALS (Simp_tac));
Addsimps [result()];

Delsimps [split_paired_All];


(* Three Simp_sets in different sizes 
----------------------------------------------

1) simpset() does not unfold the transition relations 
2) ss unfolds transition relations 
3) renname_ss unfolds transitions and the abstract channel *)


val ss = (simpset() addsimps transitions);     
val rename_ss = (ss addsimps unfold_renaming);

val tac     = asm_simp_tac (ss addcongs [conj_cong] addsplits [split_if]);
val tac_ren = asm_simp_tac (rename_ss addcongs [conj_cong] addsplits [split_if]);



(* INVARIANT 1 *)

Goalw impl_ioas "invariant impl_ioa inv1";
by (rtac invariantI 1);
by (asm_full_simp_tac (simpset()
   addsimps [inv1_def, hdr_sum_def, Sender.srcvd_def,
             Sender.ssent_def, Receiver.rsent_def,Receiver.rrcvd_def]) 1);

by (simp_tac (simpset() delsimps [trans_of_par4]
                addsimps [fork_lemma,inv1_def]) 1);

(* Split proof in two *)
by (rtac conjI 1); 

(* First half *)
by (asm_full_simp_tac (simpset() addsimps [Impl.inv1_def]
                                 delsplits [split_if]) 1);
by (rtac Action.action.induct 1);

by (EVERY1[tac, tac, tac, tac]);
by (tac 1);
by (tac_ren 1);

(* 5 + 1 *)

by (tac 1);
by (tac_ren 1);

(* 4 + 1 *)
by (EVERY1[tac, tac, tac, tac]);


(* Now the other half *)
by (asm_full_simp_tac (simpset() addsimps [Impl.inv1_def]
                                 delsplits [split_if]) 1);
by (rtac Action.action.induct 1);
by (EVERY1[tac, tac]);

(* detour 1 *)
by (tac 1);
by (tac_ren 1);
by (rtac impI 1);
by (REPEAT (etac conjE 1));
by (asm_simp_tac (simpset() addsimps [hdr_sum_def, Multiset.count_def,
                                      Multiset.countm_nonempty_def]
                            addsplits [split_if]) 1);
(* detour 2 *)
by (tac 1);
by (tac_ren 1);
by (rtac impI 1);
by (REPEAT (etac conjE 1));
by (asm_full_simp_tac (simpset() addsimps [Impl.hdr_sum_def, 
                                         Multiset.count_def,
                                         Multiset.countm_nonempty_def,
                                         Multiset.delm_nonempty_def]
                                 addsplits [split_if]) 1);
by (rtac allI 1);
by (rtac conjI 1);
by (rtac impI 1);
by (hyp_subst_tac 1);
by (rtac (pred_suc RS iffD1) 1);
by (dtac less_le_trans 1);
by (cut_facts_tac [rewrite_rule[Packet.hdr_def]
                   eq_packet_imp_eq_hdr RS countm_props] 1);;
by (assume_tac 1);
by (assume_tac 1);

by (rtac (countm_done_delm RS mp RS sym) 1);
by (rtac refl 1);
by (asm_simp_tac (simpset() addsimps [Multiset.count_def]) 1);

by (rtac impI 1);
by (asm_full_simp_tac (simpset() addsimps [neg_flip]) 1);
by (hyp_subst_tac 1);
by (rtac countm_spurious_delm 1);
by (Simp_tac 1);

by (EVERY1[tac, tac, tac, tac, tac, tac]);

qed "inv1";



(* INVARIANT 2 *)

Goal "invariant impl_ioa inv2";

  by (rtac invariantI1 1); 
  (* Base case *)
  by (asm_full_simp_tac (simpset() addsimps (inv2_def ::
                          (receiver_projections 
                           @ sender_projections @ impl_ioas)))
      1);

  by (asm_simp_tac (simpset() addsimps impl_ioas delsplits [split_if]) 1);
  by (induct_tac "a" 1);

  (* 10 cases. First 4 are simple, since state doesn't change *)

val tac2 = asm_full_simp_tac (ss addsimps [inv2_def]);

  (* 10 - 7 *)
  by (EVERY1[tac2,tac2,tac2,tac2]);
  (* 6 *)
  by (forward_tac [rewrite_rule [Impl.inv1_def]
                               (inv1 RS invariantE) RS conjunct1] 1);
  (* 6 - 5 *)
  by (EVERY1[tac2,tac2]);

  (* 4 *)
  by (forward_tac [rewrite_rule [Impl.inv1_def]
                                (inv1 RS invariantE) RS conjunct1] 1);
  by (tac2 1);
  by (arith_tac 1);

  (* 3 *)
  by (forward_tac [rewrite_rule [Impl.inv1_def] (inv1 RS invariantE)] 1);

  by (tac2 1);
  by (fold_tac [rewrite_rule [Packet.hdr_def]Impl.hdr_sum_def]);
  by (arith_tac 1);

  (* 2 *)
  by (tac2 1);
  by (forward_tac [rewrite_rule [Impl.inv1_def]
                               (inv1 RS invariantE) RS conjunct1] 1);
  by (strip_tac 1);
  by (REPEAT (etac conjE 1));
  by (Asm_full_simp_tac 1);

  (* 1 *)
  by (tac2 1);
  by (forward_tac [rewrite_rule [Impl.inv1_def]
                               (inv1 RS invariantE) RS conjunct2] 1);
  by (strip_tac 1);
  by (REPEAT (etac conjE 1));
  by (fold_tac  [rewrite_rule[Packet.hdr_def]Impl.hdr_sum_def]);
  by (Asm_full_simp_tac 1);
qed "inv2";


(* INVARIANT 3 *)

Goal "invariant impl_ioa inv3";

  by (rtac invariantI 1); 
  (* Base case *)
  by (asm_full_simp_tac (simpset() addsimps 
                    (Impl.inv3_def :: (receiver_projections 
                                       @ sender_projections @ impl_ioas))) 1);

  by (asm_simp_tac (simpset() addsimps impl_ioas delsplits [split_if]) 1);
  by (induct_tac "a" 1);

val tac3 = asm_full_simp_tac (ss addsimps [inv3_def]);

  (* 10 - 8 *)

  by (EVERY1[tac3,tac3,tac3]);
 
  by (tac_ren 1);
  by (strip_tac  1 THEN REPEAT (etac conjE 1));
  by (hyp_subst_tac 1);
  by (etac exE 1);
  by (Asm_full_simp_tac 1);

  (* 7 *)
  by (tac3 1);
  by (tac_ren 1);
  by (Blast_tac 1);

  (* 6 - 3 *)

  by (EVERY1[tac3,tac3,tac3,tac3]);

  (* 2 *)
  by (asm_full_simp_tac ss 1);
  by (simp_tac (simpset() addsimps [inv3_def]) 1);
  by (strip_tac  1 THEN REPEAT (etac conjE 1));
  by (rtac (imp_or_lem RS iffD2) 1);
  by (rtac impI 1);
  by (forward_tac [rewrite_rule [Impl.inv2_def] (inv2 RS invariantE)] 1);
  by (Asm_full_simp_tac 1);
  by (REPEAT (etac conjE 1));
  by (res_inst_tac [("j","count (ssent(sen s)) (~sbit(sen s))"),
                    ("k","count (rsent(rec s)) (sbit(sen s))")] le_trans 1);
  by (forward_tac [rewrite_rule [inv1_def]
                                (inv1 RS invariantE) RS conjunct2] 1);
  by (asm_full_simp_tac (simpset() addsimps
                         [hdr_sum_def, Multiset.count_def]) 1);
  by (rtac add_le_mono 1);
  by (rtac countm_props 1);
  by (Simp_tac 1);
  by (rtac countm_props 1);
  by (Simp_tac 1);
  by (assume_tac 1);

  (* 1 *)
  by (tac3 1);
  by (strip_tac  1 THEN REPEAT (etac conjE 1));
  by (rtac (imp_or_lem RS iffD2) 1);
  by (rtac impI 1);
  by (forward_tac [rewrite_rule [Impl.inv2_def] (inv2 RS invariantE)] 1);
  by (Asm_full_simp_tac 1);
qed "inv3";


(* INVARIANT 4 *)

Goal "invariant impl_ioa inv4";

  by (rtac invariantI 1); 
  (* Base case *)
  by (asm_full_simp_tac (simpset() addsimps 
                    (Impl.inv4_def :: (receiver_projections 
                                       @ sender_projections @ impl_ioas))) 1);

  by (asm_simp_tac (simpset() addsimps impl_ioas delsplits [split_if]) 1);
  by (induct_tac "a" 1);

val tac4 =  asm_full_simp_tac (ss addsimps [inv4_def]);

  (* 10 - 2 *)

  by (EVERY1[tac4,tac4,tac4,tac4,tac4,tac4,tac4,tac4,tac4]);

 (* 2 b *)

  by (strip_tac  1 THEN REPEAT (etac conjE 1));
  by (forward_tac [rewrite_rule [Impl.inv2_def]
                               (inv2 RS invariantE)] 1);
  by (Asm_full_simp_tac 1);

  (* 1 *)
  by (tac4 1);
  by (strip_tac  1 THEN REPEAT (etac conjE 1));
  by (rtac ccontr 1);
  by (forward_tac [rewrite_rule [Impl.inv2_def]
                               (inv2 RS invariantE)] 1);
  by (forward_tac [rewrite_rule [Impl.inv3_def]
                               (inv3 RS invariantE)] 1);
  by (Asm_full_simp_tac 1);
  by (eres_inst_tac [("x","m")] allE 1);
  by (Asm_full_simp_tac 1);
qed "inv4";


(* rebind them *)

val inv1 = rewrite_rule [Impl.inv1_def] (inv1 RS invariantE);
val inv2 = rewrite_rule [Impl.inv2_def] (inv2 RS invariantE);
val inv3 = rewrite_rule [Impl.inv3_def] (inv3 RS invariantE);
val inv4 = rewrite_rule [Impl.inv4_def] (inv4 RS invariantE);
