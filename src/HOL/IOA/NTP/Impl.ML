(*  Title:      HOL/IOA/NTP/Impl.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

The implementation --- Invariants
*)

open Abschannel;

val impl_ioas =
  [Impl.impl_def,
   Sender.sender_ioa_def, 
   Receiver.receiver_ioa_def, 
   srch_ioa_thm RS eq_reflection,
   rsch_ioa_thm RS eq_reflection];

val transitions = [Sender.sender_trans_def, Receiver.receiver_trans_def,
            Abschannel.srch_trans_def, Abschannel.rsch_trans_def];
 

Addsimps [ioa_triple_proj, starts_of_par, trans_of_par4,
          in_sender_asig, in_receiver_asig, in_srch_asig,
          in_rsch_asig, count_addm_simp, count_delm_simp,
          Multiset.countm_empty_def, Multiset.delm_empty_def,
          (* Multiset.count_def, *) count_empty,
          Packet.hdr_def, Packet.msg_def];

goal Impl.thy
  "fst(x) = sen(x)            & \
\  fst(snd(x)) = rec(x)       & \
\  fst(snd(snd(x))) = srch(x) & \
\  snd(snd(snd(x))) = rsch(x)";
by(simp_tac (!simpset addsimps
             [Impl.sen_def,Impl.rec_def,Impl.srch_def,Impl.rsch_def]) 1);
Addsimps [result()];

goal Impl.thy "a:actions(sender_asig)   \
\            | a:actions(receiver_asig) \
\            | a:actions(srch_asig)     \
\            | a:actions(rsch_asig)";
  by(Action.action.induct_tac "a" 1);
  by(ALLGOALS (simp_tac (!simpset
                         delsimps [actions_def,srch_asig_def,rsch_asig_def])));
Addsimps [result()];


(* INVARIANT 1 *)
val ss = !simpset addcongs [let_weak_cong] delsimps
  [trans_of_def, starts_of_def, srch_asig_def, rsch_asig_def,
   asig_of_def, actions_def, srch_trans_def, rsch_trans_def];

goalw Impl.thy impl_ioas "invariant impl_ioa inv1";
br invariantI 1;
by(asm_full_simp_tac (ss
   addsimps [Impl.inv1_def, Impl.hdr_sum_def, Sender.srcvd_def,
             Sender.ssent_def, Receiver.rsent_def,Receiver.rrcvd_def]) 1);

by(simp_tac (ss delsimps [trans_of_par4]
                      addsimps [fork_lemma,Impl.inv1_def]) 1);

(* Split proof in two *)
by (rtac conjI 1);

(* First half *)
by(asm_full_simp_tac (ss addsimps [Impl.inv1_def]) 1);
br Action.action.induct 1;

val tac = asm_simp_tac (ss delsimps [srch_ioa_def, rsch_ioa_def]
                                addcongs [if_weak_cong, conj_cong] 
                                addsimps (Suc_pred_lemma :: transitions)
                                setloop (split_tac [expand_if]));
val tac_abs = asm_simp_tac (!simpset
            delsimps [srch_asig_def, rsch_asig_def, actions_def,
                      srch_trans_def, rsch_trans_def]
            addcongs [if_weak_cong, conj_cong] 
            addsimps (Suc_pred_lemma :: transitions)
            setloop (split_tac [expand_if]));
by (EVERY1[tac, tac, tac, tac]);
by (tac 1);
by (tac_abs 1);

(* 5 + 1 *)

by (tac 1);
by (tac_abs 1);

(* 4 + 1 *)
by(EVERY1[tac, tac, tac, tac]);


(* Now the other half *)
by(asm_full_simp_tac (ss addsimps [Impl.inv1_def]) 1);
br Action.action.induct 1;
by(EVERY1[tac, tac]);

(* detour 1 *)
by (tac 1);
by (tac_abs 1);
by (rtac impI 1);
by (REPEAT (etac conjE 1));
by (asm_simp_tac (ss addsimps [Impl.hdr_sum_def, Multiset.count_def,
                                    Multiset.countm_nonempty_def]
                          setloop (split_tac [expand_if])) 1);
(* detour 2 *)
by (tac 1);
by (tac_abs 1);
by (rtac impI 1);
by (REPEAT (etac conjE 1));
by (asm_full_simp_tac (ss addsimps [Impl.hdr_sum_def, 
                                         Multiset.count_def,
                                         Multiset.countm_nonempty_def,
                                         Multiset.delm_nonempty_def,
                                         left_plus_cancel,
                                         left_plus_cancel_inside_succ,
                                         unzero_less]
                               setloop (split_tac [expand_if])) 1);
by (rtac allI 1);
by (rtac conjI 1);
by (rtac impI 1);
by (hyp_subst_tac 1);
by (rtac (pred_suc RS mp RS sym RS iffD2) 1);
by (dtac less_le_trans 1);
by (cut_facts_tac [rewrite_rule[Packet.hdr_def]
		   eq_packet_imp_eq_hdr RS countm_props] 1);;
by (assume_tac 1);
by (assume_tac 1);

by (rtac (countm_done_delm RS mp RS sym) 1);
by (rtac refl 1);
by (asm_simp_tac (ss addsimps [Multiset.count_def]) 1);

by (rtac impI 1);
by (asm_full_simp_tac (ss addsimps [neg_flip]) 1);
by (hyp_subst_tac 1);
by (rtac countm_spurious_delm 1);
by (Simp_tac 1);

by (EVERY1[tac, tac, tac, tac, tac, tac]);

qed "inv1";



(* INVARIANT 2 *)

  goal Impl.thy "invariant impl_ioa inv2";

  by (rtac invariantI1 1); 
  (* Base case *)
  by (asm_full_simp_tac (ss addsimps (Impl.inv2_def ::
                                           (receiver_projections 
                                            @ sender_projections @ impl_ioas)))
      1);

  by (asm_simp_tac (ss addsimps impl_ioas) 1);
  by (Action.action.induct_tac "a" 1);

  (* 10 cases. First 4 are simple, since state doesn't change wrt. invariant *)
  (* 10 *)
  by (asm_simp_tac (ss delsimps [srch_ioa_def, rsch_ioa_def]
                            addsimps (Impl.inv2_def::transitions)) 1);
  (* 9 *)
  by (asm_simp_tac (ss delsimps [srch_ioa_def, rsch_ioa_def]
                            addsimps (Impl.inv2_def::transitions)) 1);
  (* 8 *)
  by (asm_simp_tac (ss delsimps [srch_ioa_def, rsch_ioa_def]
                            addsimps (Impl.inv2_def::transitions)) 2);
  (* 7 *)
  by (asm_simp_tac (ss delsimps [srch_ioa_def, rsch_ioa_def]
                            addsimps (Impl.inv2_def::transitions)) 3);
  (* 6 *)
  by(forward_tac [rewrite_rule [Impl.inv1_def]
                               (inv1 RS invariantE) RS conjunct1] 1);
  by (asm_full_simp_tac (ss delsimps [srch_ioa_def, rsch_ioa_def]
                                 addsimps ([leq_imp_leq_suc,Impl.inv2_def]
                                           @ transitions)) 1);
  (* 5 *)
  by (asm_full_simp_tac (ss delsimps [srch_ioa_def, rsch_ioa_def]
                                 addsimps ([leq_imp_leq_suc,Impl.inv2_def]
                                           @ transitions)) 1);
  (* 4 *)
  by (forward_tac [rewrite_rule [Impl.inv1_def]
                                (inv1 RS invariantE) RS conjunct1] 1);
  by (asm_full_simp_tac (ss delsimps [srch_ioa_def, rsch_ioa_def]
                                 addsimps (Impl.inv2_def :: transitions)) 1);
  by (fast_tac (HOL_cs addDs [add_leD1,leD]) 1);

  (* 3 *)
  by (forward_tac [rewrite_rule [Impl.inv1_def] (inv1 RS invariantE)] 1);

  by (asm_full_simp_tac (ss delsimps [srch_ioa_def, rsch_ioa_def]
                                 addsimps (Impl.inv2_def :: transitions)) 1);
  by (fold_tac [rewrite_rule [Packet.hdr_def]Impl.hdr_sum_def]);
  by (fast_tac (HOL_cs addDs [add_leD1,leD]) 1);

  (* 2 *)
  by (asm_full_simp_tac (ss delsimps [srch_ioa_def, rsch_ioa_def]
                                 addsimps (Impl.inv2_def :: transitions)) 1);
  by(forward_tac [rewrite_rule [Impl.inv1_def]
                               (inv1 RS invariantE) RS conjunct1] 1);
  by (rtac impI 1);
  by (rtac impI 1);
  by (REPEAT (etac conjE 1));
  by (dres_inst_tac [("k","count (rsch s) (~sbit(sen s))")] 
                     (standard(leq_add_leq RS mp)) 1);
  by (asm_full_simp_tac ss 1);

  (* 1 *)
  by (asm_full_simp_tac (ss delsimps [srch_ioa_def, rsch_ioa_def]
                                 addsimps (Impl.inv2_def :: transitions)) 1);
  by(forward_tac [rewrite_rule [Impl.inv1_def]
                               (inv1 RS invariantE) RS conjunct2] 1);
  by (rtac impI 1);
  by (rtac impI 1);
  by (REPEAT (etac conjE 1));
  by (fold_tac  [rewrite_rule[Packet.hdr_def]Impl.hdr_sum_def]);
  by (dres_inst_tac [("k","hdr_sum (srch s) (sbit(sen s))")] 
                     (standard(leq_add_leq RS mp)) 1);
  by (asm_full_simp_tac ss 1);
qed "inv2";


(* INVARIANT 3 *)

val ss = ss delsimps [srch_ioa_def, rsch_ioa_def, Packet.hdr_def];

goal Impl.thy "invariant impl_ioa inv3";

  by (rtac invariantI 1); 
  (* Base case *)
  by (asm_full_simp_tac (ss addsimps 
                    (Impl.inv3_def :: (receiver_projections 
                                       @ sender_projections @ impl_ioas))) 1);

  by (asm_simp_tac (ss addsimps impl_ioas) 1);
  by (Action.action.induct_tac "a" 1);

  (* 10 *)
  by (asm_full_simp_tac (ss
              addsimps (append_cons::not_hd_append::Impl.inv3_def::transitions)
              setloop (split_tac [expand_if])) 1);

  (* 9 *)
  by (asm_full_simp_tac (ss
              addsimps (append_cons::not_hd_append::Impl.inv3_def::transitions)
              setloop (split_tac [expand_if])) 1);

  (* 8 *)
  by (asm_full_simp_tac (ss
              addsimps (append_cons::not_hd_append::Impl.inv3_def::transitions)
              setloop (split_tac [expand_if])) 1);
  by (tac_abs 1);
  by (strip_tac  1 THEN REPEAT (etac conjE 1));
  by (asm_full_simp_tac (ss addsimps [cons_imp_not_null]) 1);

  by (hyp_subst_tac 1);
  by (etac exE 1);
  by (Asm_full_simp_tac 1);

  (* 7 *)
  by (asm_full_simp_tac (ss addsimps 
      (Suc_pred_lemma::append_cons::not_hd_append::Impl.inv3_def::transitions)
                  setloop (split_tac [expand_if])) 1); 
  by (tac_abs 1);
  by (fast_tac HOL_cs 1);

  (* 6 *)
  by (asm_full_simp_tac (ss addsimps 
                  (append_cons::not_hd_append::Impl.inv3_def::transitions)
                  setloop (split_tac [expand_if])) 1);
  (* 5 *)
  by (asm_full_simp_tac (ss addsimps 
                  (append_cons::not_hd_append::Impl.inv3_def::transitions)
                  setloop (split_tac [expand_if])) 1);
  (* 4 *)
  by (asm_full_simp_tac (ss addsimps 
                  (append_cons::not_hd_append::Impl.inv3_def::transitions)
                  setloop (split_tac [expand_if])) 1);

  (* 3 *)
  by (asm_full_simp_tac (ss addsimps 
                  (append_cons::not_hd_append::Impl.inv3_def::transitions)
                  setloop (split_tac [expand_if])) 1);

  (* 2 *)
  by (asm_full_simp_tac (ss addsimps transitions) 1);
  by (simp_tac (ss addsimps [Impl.inv3_def]) 1);
  by (strip_tac  1 THEN REPEAT (etac conjE 1));
  by (rtac (imp_or_lem RS iffD2) 1);
  by (rtac impI 1);
  by (forward_tac [rewrite_rule [Impl.inv2_def] (inv2 RS invariantE)] 1);
  by (asm_full_simp_tac ss 1);
  by (REPEAT (etac conjE 1));
  by (res_inst_tac [("j","count (ssent(sen s)) (~sbit(sen s))"),
                    ("k","count (rsent(rec s)) (sbit(sen s))")] le_trans 1);
  by (forward_tac [rewrite_rule [Impl.inv1_def]
                                (inv1 RS invariantE) RS conjunct2] 1);
  by (asm_full_simp_tac (ss addsimps
                         [Impl.hdr_sum_def, Multiset.count_def]) 1);
  by (rtac (less_eq_add_cong RS mp RS mp) 1);
  by (rtac countm_props 1);
  by (simp_tac (ss addsimps [Packet.hdr_def]) 1);
  by (rtac countm_props 1);
  by (simp_tac (ss addsimps [Packet.hdr_def]) 1);
  by (assume_tac 1);

  (* 1 *)
  by (asm_full_simp_tac (ss addsimps 
                  (append_cons::not_hd_append::Impl.inv3_def::transitions)
                  setloop (split_tac [expand_if])) 1);
  by (strip_tac  1 THEN REPEAT (etac conjE 1));
  by (rtac (imp_or_lem RS iffD2) 1);
  by (rtac impI 1);
  by (forward_tac [rewrite_rule [Impl.inv2_def] (inv2 RS invariantE)] 1);
  by (asm_full_simp_tac ss 1);
  by (REPEAT (etac conjE 1));
  by (dtac mp 1);
  by (assume_tac 1);
  by (etac allE 1);
  by (dtac (imp_or_lem RS iffD1) 1);
  by (dtac mp 1);
  by (assume_tac 1);
  by (assume_tac 1);
qed "inv3";


(* INVARIANT 4 *)

goal Impl.thy "invariant impl_ioa inv4";

  by (rtac invariantI 1); 
  (* Base case *)
  by (asm_full_simp_tac (ss addsimps 
                    (Impl.inv4_def :: (receiver_projections 
                                       @ sender_projections @ impl_ioas))) 1);

  by (asm_simp_tac (ss addsimps impl_ioas) 1);
  by (Action.action.induct_tac "a" 1);

  (* 10 *)
  by (asm_full_simp_tac (ss addsimps (append_cons::Impl.inv4_def::transitions)
                  setloop (split_tac [expand_if])) 1);

  (* 9 *)
  by (asm_full_simp_tac (ss addsimps (append_cons::Impl.inv4_def::transitions)
                  setloop (split_tac [expand_if])) 1);

  (* 8 *)
  by (asm_full_simp_tac (ss addsimps (append_cons::Impl.inv4_def::transitions)
                  setloop (split_tac [expand_if])) 1);
  (* 7 *)
  by (asm_full_simp_tac (ss addsimps (append_cons::Impl.inv4_def::transitions)
                  setloop (split_tac [expand_if])) 1);

  (* 6 *)
  by (asm_full_simp_tac (ss addsimps (append_cons::Impl.inv4_def::transitions)
                  setloop (split_tac [expand_if])) 1);

  (* 5 *)
  by (asm_full_simp_tac (ss addsimps (append_cons::Impl.inv4_def::transitions)
                  setloop (split_tac [expand_if])) 1);

  (* 4 *)
  by (asm_full_simp_tac (ss addsimps (append_cons::Impl.inv4_def::transitions)
                  setloop (split_tac [expand_if])) 1);

  (* 3 *)
  by (asm_full_simp_tac (ss addsimps (append_cons::Impl.inv4_def::transitions)
                  setloop (split_tac [expand_if])) 1);

  (* 2 *)
  by (asm_full_simp_tac (ss addsimps (append_cons::Impl.inv4_def::transitions)
                  setloop (split_tac [expand_if])) 1);

  by (strip_tac  1 THEN REPEAT (etac conjE 1));
  by(forward_tac [rewrite_rule [Impl.inv2_def]
                               (inv2 RS invariantE)] 1);
 
  by (Asm_full_simp_tac 1);

  (* 1 *)
  by (asm_full_simp_tac (ss addsimps (append_cons::Impl.inv4_def::transitions)
                  setloop (split_tac [expand_if])) 1);
  by (strip_tac  1 THEN REPEAT (etac conjE 1));
  by (rtac ccontr 1);
  by(forward_tac [rewrite_rule [Impl.inv2_def]
                               (inv2 RS invariantE)] 1);
  by(forward_tac [rewrite_rule [Impl.inv3_def]
                               (inv3 RS invariantE)] 1);
  by (Asm_full_simp_tac 1);
  by (eres_inst_tac [("x","m")] allE 1);
  by (dtac less_le_trans 1);
  by (dtac (left_add_leq RS mp) 1);
  by (Asm_full_simp_tac 1);
  by (Asm_full_simp_tac 1);
qed "inv4";


(* rebind them *)

val inv1 = rewrite_rule [Impl.inv1_def] (inv1 RS invariantE);
val inv2 = rewrite_rule [Impl.inv2_def] (inv2 RS invariantE);
val inv3 = rewrite_rule [Impl.inv3_def] (inv3 RS invariantE);
val inv4 = rewrite_rule [Impl.inv4_def] (inv4 RS invariantE);
