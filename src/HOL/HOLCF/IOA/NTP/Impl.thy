(*  Title:      HOL/HOLCF/IOA/NTP/Impl.thy
    Author:     Tobias Nipkow & Konrad Slind
*)

header {* The implementation *}

theory Impl
imports Sender Receiver Abschannel
begin

type_synonym 'm impl_state
  = "'m sender_state * 'm receiver_state * 'm packet multiset * bool multiset"
  (*  sender_state   *  receiver_state   *    srch_state      * rsch_state *)


definition
  impl_ioa :: "('m action, 'm impl_state)ioa" where
  impl_def: "impl_ioa == (sender_ioa || receiver_ioa || srch_ioa || rsch_ioa)"

definition sen :: "'m impl_state => 'm sender_state" where "sen = fst"
definition rec :: "'m impl_state => 'm receiver_state" where "rec = fst o snd"
definition srch :: "'m impl_state => 'm packet multiset" where "srch = fst o snd o snd"
definition rsch :: "'m impl_state => bool multiset" where "rsch = snd o snd o snd"

definition
  hdr_sum :: "'m packet multiset => bool => nat" where
  "hdr_sum M b == countm M (%pkt. hdr(pkt) = b)"

(* Lemma 5.1 *)
definition
  "inv1(s) ==
     (!b. count (rsent(rec s)) b = count (srcvd(sen s)) b + count (rsch s) b)
   & (!b. count (ssent(sen s)) b
          = hdr_sum (rrcvd(rec s)) b + hdr_sum (srch s) b)"

(* Lemma 5.2 *)
definition
  "inv2(s) ==
  (rbit(rec(s)) = sbit(sen(s)) &
   ssending(sen(s)) &
   count (rsent(rec s)) (~sbit(sen s)) <= count (ssent(sen s)) (~sbit(sen s)) &
   count (ssent(sen s)) (~sbit(sen s)) <= count (rsent(rec s)) (sbit(sen s)))
   |
  (rbit(rec(s)) = (~sbit(sen(s))) &
   rsending(rec(s)) &
   count (ssent(sen s)) (~sbit(sen s)) <= count (rsent(rec s)) (sbit(sen s)) &
   count (rsent(rec s)) (sbit(sen s)) <= count (ssent(sen s)) (sbit(sen s)))"

(* Lemma 5.3 *)
definition
  "inv3(s) ==
   rbit(rec(s)) = sbit(sen(s))
   --> (!m. sq(sen(s))=[] | m ~= hd(sq(sen(s)))
        -->  count (rrcvd(rec s)) (sbit(sen(s)),m)
             + count (srch s) (sbit(sen(s)),m)
            <= count (rsent(rec s)) (~sbit(sen s)))"

(* Lemma 5.4 *)
definition "inv4(s) == rbit(rec(s)) = (~sbit(sen(s))) --> sq(sen(s)) ~= []"


subsection {* Invariants *}

declare le_SucI [simp]

lemmas impl_ioas =
  impl_def sender_ioa_def receiver_ioa_def srch_ioa_thm [THEN eq_reflection]
  rsch_ioa_thm [THEN eq_reflection]

lemmas "transitions" =
  sender_trans_def receiver_trans_def srch_trans_def rsch_trans_def


lemmas [simp] =
  ioa_triple_proj starts_of_par trans_of_par4 in_sender_asig
  in_receiver_asig in_srch_asig in_rsch_asig

declare let_weak_cong [cong]

lemma [simp]:
  "fst(x) = sen(x)"
  "fst(snd(x)) = rec(x)"
  "fst(snd(snd(x))) = srch(x)"
  "snd(snd(snd(x))) = rsch(x)"
  by (simp_all add: sen_def rec_def srch_def rsch_def)

lemma [simp]:
  "a:actions(sender_asig)
  | a:actions(receiver_asig)
  | a:actions(srch_asig)
  | a:actions(rsch_asig)"
  by (induct a) simp_all

declare split_paired_All [simp del]


(* Three Simp_sets in different sizes
----------------------------------------------

1) simpset() does not unfold the transition relations
2) ss unfolds transition relations
3) renname_ss unfolds transitions and the abstract channel *)

ML {*
val ss = @{simpset} addsimps @{thms "transitions"};
val rename_ss = ss addsimps @{thms unfold_renaming};

val tac =
  asm_simp_tac (ss |> Simplifier.add_cong @{thm conj_cong} |> Splitter.add_split @{thm split_if})
val tac_ren =
  asm_simp_tac (rename_ss |> Simplifier.add_cong @{thm conj_cong} |> Splitter.add_split @{thm split_if})
*}


subsubsection {* Invariant 1 *}

lemma raw_inv1: "invariant impl_ioa inv1"

apply (unfold impl_ioas)
apply (rule invariantI)
apply (simp add: inv1_def hdr_sum_def srcvd_def ssent_def rsent_def rrcvd_def)

apply (simp (no_asm) del: trans_of_par4 add: imp_conjR inv1_def)

txt {* Split proof in two *}
apply (rule conjI)

(* First half *)
apply (simp add: Impl.inv1_def split del: split_if)
apply (induct_tac a)

apply (tactic "EVERY1[tac, tac, tac, tac]")
apply (tactic "tac 1")
apply (tactic "tac_ren 1")

txt {* 5 + 1 *}

apply (tactic "tac 1")
apply (tactic "tac_ren 1")

txt {* 4 + 1 *}
apply (tactic {* EVERY1[tac, tac, tac, tac] *})


txt {* Now the other half *}
apply (simp add: Impl.inv1_def split del: split_if)
apply (induct_tac a)
apply (tactic "EVERY1 [tac, tac]")

txt {* detour 1 *}
apply (tactic "tac 1")
apply (tactic "tac_ren 1")
apply (rule impI)
apply (erule conjE)+
apply (simp (no_asm_simp) add: hdr_sum_def Multiset.count_def Multiset.countm_nonempty_def
  split add: split_if)
txt {* detour 2 *}
apply (tactic "tac 1")
apply (tactic "tac_ren 1")
apply (rule impI)
apply (erule conjE)+
apply (simp add: Impl.hdr_sum_def Multiset.count_def Multiset.countm_nonempty_def
  Multiset.delm_nonempty_def split add: split_if)
apply (rule allI)
apply (rule conjI)
apply (rule impI)
apply hypsubst
apply (rule pred_suc [THEN iffD1])
apply (drule less_le_trans)
apply (cut_tac eq_packet_imp_eq_hdr [unfolded Packet.hdr_def, THEN countm_props])
apply assumption
apply assumption

apply (rule countm_done_delm [THEN mp, symmetric])
apply (rule refl)
apply (simp (no_asm_simp) add: Multiset.count_def)

apply (rule impI)
apply (simp add: neg_flip)
apply hypsubst
apply (rule countm_spurious_delm)
apply (simp (no_asm))

apply (tactic "EVERY1 [tac, tac, tac, tac, tac, tac]")

done



subsubsection {* INVARIANT 2 *}

lemma raw_inv2: "invariant impl_ioa inv2"

  apply (rule invariantI1)
  txt {* Base case *}
  apply (simp add: inv2_def receiver_projections sender_projections impl_ioas)

  apply (simp (no_asm_simp) add: impl_ioas split del: split_if)
  apply (induct_tac "a")

  txt {* 10 cases. First 4 are simple, since state doesn't change *}

  ML_prf {* val tac2 = asm_full_simp_tac (ss addsimps [@{thm inv2_def}]) *}

  txt {* 10 - 7 *}
  apply (tactic "EVERY1 [tac2,tac2,tac2,tac2]")
  txt {* 6 *}
  apply (tactic {* forward_tac [rewrite_rule [@{thm Impl.inv1_def}]
                               (@{thm raw_inv1} RS @{thm invariantE}) RS conjunct1] 1 *})

  txt {* 6 - 5 *}
  apply (tactic "EVERY1 [tac2,tac2]")

  txt {* 4 *}
  apply (tactic {* forward_tac [rewrite_rule [@{thm Impl.inv1_def}]
                                (@{thm raw_inv1} RS @{thm invariantE}) RS conjunct1] 1 *})
  apply (tactic "tac2 1")

  txt {* 3 *}
  apply (tactic {* forward_tac [rewrite_rule [@{thm Impl.inv1_def}]
    (@{thm raw_inv1} RS @{thm invariantE})] 1 *})

  apply (tactic "tac2 1")
  apply (tactic {* fold_goals_tac [rewrite_rule [@{thm Packet.hdr_def}]
    (@{thm Impl.hdr_sum_def})] *})
  apply arith

  txt {* 2 *}
  apply (tactic "tac2 1")
  apply (tactic {* forward_tac [rewrite_rule [@{thm Impl.inv1_def}]
                               (@{thm raw_inv1} RS @{thm invariantE}) RS conjunct1] 1 *})
  apply (intro strip)
  apply (erule conjE)+
  apply simp

  txt {* 1 *}
  apply (tactic "tac2 1")
  apply (tactic {* forward_tac [rewrite_rule [@{thm Impl.inv1_def}]
                               (@{thm raw_inv1} RS @{thm invariantE}) RS conjunct2] 1 *})
  apply (intro strip)
  apply (erule conjE)+
  apply (tactic {* fold_goals_tac [rewrite_rule [@{thm Packet.hdr_def}] (@{thm Impl.hdr_sum_def})] *})
  apply simp

  done


subsubsection {* INVARIANT 3 *}

lemma raw_inv3: "invariant impl_ioa inv3"

  apply (rule invariantI)
  txt {* Base case *}
  apply (simp add: Impl.inv3_def receiver_projections sender_projections impl_ioas)

  apply (simp (no_asm_simp) add: impl_ioas split del: split_if)
  apply (induct_tac "a")

  ML_prf {* val tac3 = asm_full_simp_tac (ss addsimps [@{thm inv3_def}]) *}

  txt {* 10 - 8 *}

  apply (tactic "EVERY1[tac3,tac3,tac3]")

  apply (tactic "tac_ren 1")
  apply (intro strip, (erule conjE)+)
  apply hypsubst
  apply (erule exE)
  apply simp

  txt {* 7 *}
  apply (tactic "tac3 1")
  apply (tactic "tac_ren 1")
  apply force

  txt {* 6 - 3 *}

  apply (tactic "EVERY1[tac3,tac3,tac3,tac3]")

  txt {* 2 *}
  apply (tactic "asm_full_simp_tac ss 1")
  apply (simp (no_asm) add: inv3_def)
  apply (intro strip, (erule conjE)+)
  apply (rule imp_disjL [THEN iffD1])
  apply (rule impI)
  apply (tactic {* forward_tac [rewrite_rule [@{thm Impl.inv2_def}]
    (@{thm raw_inv2} RS @{thm invariantE})] 1 *})
  apply simp
  apply (erule conjE)+
  apply (rule_tac j = "count (ssent (sen s)) (~sbit (sen s))" and
    k = "count (rsent (rec s)) (sbit (sen s))" in le_trans)
  apply (tactic {* forward_tac [rewrite_rule [@{thm inv1_def}]
                                (@{thm raw_inv1} RS @{thm invariantE}) RS conjunct2] 1 *})
  apply (simp add: hdr_sum_def Multiset.count_def)
  apply (rule add_le_mono)
  apply (rule countm_props)
  apply (simp (no_asm))
  apply (rule countm_props)
  apply (simp (no_asm))
  apply assumption

  txt {* 1 *}
  apply (tactic "tac3 1")
  apply (intro strip, (erule conjE)+)
  apply (rule imp_disjL [THEN iffD1])
  apply (rule impI)
  apply (tactic {* forward_tac [rewrite_rule [@{thm Impl.inv2_def}]
    (@{thm raw_inv2} RS @{thm invariantE})] 1 *})
  apply simp
  done


subsubsection {* INVARIANT 4 *}

lemma raw_inv4: "invariant impl_ioa inv4"

  apply (rule invariantI)
  txt {* Base case *}
  apply (simp add: Impl.inv4_def receiver_projections sender_projections impl_ioas)

  apply (simp (no_asm_simp) add: impl_ioas split del: split_if)
  apply (induct_tac "a")

  ML_prf {* val tac4 =  asm_full_simp_tac (ss addsimps [@{thm inv4_def}]) *}

  txt {* 10 - 2 *}

  apply (tactic "EVERY1[tac4,tac4,tac4,tac4,tac4,tac4,tac4,tac4,tac4]")

  txt {* 2 b *}

  apply (intro strip, (erule conjE)+)
  apply (tactic {* forward_tac [rewrite_rule [@{thm Impl.inv2_def}]
                               (@{thm raw_inv2} RS @{thm invariantE})] 1 *})
  apply simp

  txt {* 1 *}
  apply (tactic "tac4 1")
  apply (intro strip, (erule conjE)+)
  apply (rule ccontr)
  apply (tactic {* forward_tac [rewrite_rule [@{thm Impl.inv2_def}]
                               (@{thm raw_inv2} RS @{thm invariantE})] 1 *})
  apply (tactic {* forward_tac [rewrite_rule [@{thm Impl.inv3_def}]
                               (@{thm raw_inv3} RS @{thm invariantE})] 1 *})
  apply simp
  apply (erule_tac x = "m" in allE)
  apply simp
  done


text {* rebind them *}

lemmas inv1 = raw_inv1 [THEN invariantE, unfolded inv1_def]
  and inv2 = raw_inv2 [THEN invariantE, unfolded inv2_def]
  and inv3 = raw_inv3 [THEN invariantE, unfolded inv3_def]
  and inv4 = raw_inv4 [THEN invariantE, unfolded inv4_def]

end
