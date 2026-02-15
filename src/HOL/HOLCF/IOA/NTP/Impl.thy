(*  Title:      HOL/HOLCF/IOA/NTP/Impl.thy
    Author:     Tobias Nipkow & Konrad Slind
*)

section \<open>The implementation\<close>

theory Impl
imports Sender Receiver Abschannel
begin

type_synonym 'm impl_state
  = "'m sender_state * 'm receiver_state * 'm packet multiset * bool multiset"
  (*  sender_state   *  receiver_state   *    srch_state      * rsch_state *)


definition
  impl_ioa :: "('m action, 'm impl_state)ioa" where
  impl_def: "impl_ioa == (sender_ioa \<parallel> receiver_ioa \<parallel> srch_ioa \<parallel> rsch_ioa)"

definition sen :: "'m impl_state => 'm sender_state" where "sen = fst"
definition rec :: "'m impl_state => 'm receiver_state" where "rec = fst \<circ> snd"
definition srch :: "'m impl_state => 'm packet multiset" where "srch = fst \<circ> snd \<circ> snd"
definition rsch :: "'m impl_state => bool multiset" where "rsch = snd \<circ> snd \<circ> snd"

definition
  hdr_sum :: "'m packet multiset => bool => nat" where
  "hdr_sum M b == countm M (%pkt. hdr(pkt) = b)"

(* Lemma 5.1 *)
definition
  "inv1(s) \<equiv>
     (\<forall>b. count (rsent(rec s)) b = count (srcvd(sen s)) b + count (rsch s) b)
   \<and> (\<forall>b. count (ssent(sen s)) b
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
  "inv3(s) \<equiv>
   rbit(rec(s)) = sbit(sen(s))
   \<longrightarrow> (\<forall>m. sq(sen(s))=[] | m \<noteq> hd(sq(sen(s)))
        \<longrightarrow>  count (rrcvd(rec s)) (sbit(sen(s)),m)
             + count (srch s) (sbit(sen(s)),m)
            \<le> count (rsent(rec s)) (~sbit(sen s)))"

(* Lemma 5.4 *)
definition "inv4(s) == rbit(rec(s)) = (~sbit(sen(s))) --> sq(sen(s)) ~= []"


subsection \<open>Invariants\<close>

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
  "a\<in>actions(sender_asig)
  \<or> a\<in>actions(receiver_asig)
  \<or> a\<in>actions(srch_asig)
  \<or> a\<in>actions(rsch_asig)"
  by (induct a) simp_all

declare split_paired_All [simp del]


(* Three Simp_sets in different sizes
----------------------------------------------

1) simpset() does not unfold the transition relations
2) ss unfolds transition relations
3) renname_ss unfolds transitions and the abstract channel *)

ML \<open>
val ss = simpset_of (\<^context> addsimps @{thms "transitions"});
val rename_ss = simpset_of (put_simpset ss \<^context> addsimps @{thms unfold_renaming});

fun tac ctxt =
  asm_simp_tac (put_simpset ss ctxt
    |> Simplifier.add_cong @{thm conj_cong} |> Splitter.add_split @{thm if_split})
fun tac_ren ctxt =
  asm_simp_tac (put_simpset rename_ss ctxt
    |> Simplifier.add_cong @{thm conj_cong} |> Splitter.add_split @{thm if_split})
\<close>


subsubsection \<open>Invariant 1\<close>

lemma raw_inv1: "invariant impl_ioa inv1"

apply (unfold impl_ioas)
apply (rule invariantI)
apply (simp add: inv1_def hdr_sum_def srcvd_def ssent_def rsent_def rrcvd_def)

apply (simp (no_asm) del: trans_of_par4 add: imp_conjR inv1_def)

txt \<open>Split proof in two\<close>
apply (rule conjI)

(* First half *)
apply (simp add: Impl.inv1_def split del: if_split)
apply (induct_tac a)

apply (tactic "EVERY1[tac \<^context>, tac \<^context>, tac \<^context>, tac \<^context>]")
apply (tactic "tac \<^context> 1")
apply (tactic "tac_ren \<^context> 1")

txt \<open>5 + 1\<close>

apply (tactic "tac \<^context> 1")
apply (tactic "tac_ren \<^context> 1")

txt \<open>4 + 1\<close>
apply (tactic \<open>EVERY1[tac \<^context>, tac \<^context>, tac \<^context>, tac \<^context>]\<close>)


txt \<open>Now the other half\<close>
apply (simp add: Impl.inv1_def split del: if_split)
apply (induct_tac a)
apply (tactic "EVERY1 [tac \<^context>, tac \<^context>]")

txt \<open>detour 1\<close>
apply (tactic "tac \<^context> 1")
apply (tactic "tac_ren \<^context> 1")
apply (rule impI)
apply (erule conjE)+
apply (simp (no_asm_simp) add: hdr_sum_def Multiset.count_def Multiset.countm_nonempty_def
  split: if_split)
txt \<open>detour 2\<close>
apply (tactic "tac \<^context> 1")
apply (tactic "tac_ren \<^context> 1")
apply (rule impI)
apply (erule conjE)+
apply (simp add: Impl.hdr_sum_def Multiset.count_def Multiset.countm_nonempty_def
  Multiset.delm_nonempty_def split: if_split)
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

apply (tactic "EVERY1 [tac \<^context>, tac \<^context>, tac \<^context>,
  tac \<^context>, tac \<^context>, tac \<^context>]")

done



subsubsection \<open>INVARIANT 2\<close>

lemma raw_inv2: "invariant impl_ioa inv2"

  apply (rule invariantI1)
  txt \<open>Base case\<close>
  apply (simp add: inv2_def receiver_projections sender_projections impl_ioas)

  apply (simp (no_asm_simp) add: impl_ioas split del: if_split)
  apply (induct_tac "a")

  txt \<open>10 cases. First 4 are simple, since state doesn't change\<close>

  ML_prf \<open>val tac2 = asm_full_simp_tac (put_simpset ss \<^context> addsimps [@{thm inv2_def}])\<close>

  txt \<open>10 - 7\<close>
  apply (tactic "EVERY1 [tac2,tac2,tac2,tac2]")
  txt \<open>6\<close>
  apply (tactic \<open>forward_tac \<^context> [rewrite_rule \<^context> [@{thm Impl.inv1_def}]
                               (@{thm raw_inv1} RS @{thm invariantE}) RS conjunct1] 1\<close>)

  txt \<open>6 - 5\<close>
  apply (tactic "EVERY1 [tac2,tac2]")

  txt \<open>4\<close>
  apply (tactic \<open>forward_tac \<^context> [rewrite_rule \<^context> [@{thm Impl.inv1_def}]
                                (@{thm raw_inv1} RS @{thm invariantE}) RS conjunct1] 1\<close>)
  apply (tactic "tac2 1")

  txt \<open>3\<close>
  apply (tactic \<open>forward_tac \<^context> [rewrite_rule \<^context> [@{thm Impl.inv1_def}]
    (@{thm raw_inv1} RS @{thm invariantE})] 1\<close>)

  apply (tactic "tac2 1")
  apply (tactic \<open>Simplifier.fold_goals_tac \<^context> [rewrite_rule \<^context> [@{thm Packet.hdr_def}]
    (@{thm Impl.hdr_sum_def})]\<close>)
  apply arith

  txt \<open>2\<close>
  apply (tactic "tac2 1")
  apply (tactic \<open>forward_tac \<^context> [rewrite_rule \<^context> [@{thm Impl.inv1_def}]
                               (@{thm raw_inv1} RS @{thm invariantE}) RS conjunct1] 1\<close>)
  apply (intro strip)
  apply (erule conjE)+
  apply simp

  txt \<open>1\<close>
  apply (tactic "tac2 1")
  apply (tactic \<open>forward_tac \<^context> [rewrite_rule \<^context> [@{thm Impl.inv1_def}]
                               (@{thm raw_inv1} RS @{thm invariantE}) RS conjunct2] 1\<close>)
  apply (intro strip)
  apply (erule conjE)+
  apply (tactic \<open>Simplifier.fold_goals_tac \<^context>
    [rewrite_rule \<^context> [@{thm Packet.hdr_def}] (@{thm Impl.hdr_sum_def})]\<close>)
  apply simp

  done


subsubsection \<open>INVARIANT 3\<close>

lemma raw_inv3: "invariant impl_ioa inv3"

  apply (rule invariantI)
  txt \<open>Base case\<close>
  apply (simp add: Impl.inv3_def receiver_projections sender_projections impl_ioas)

  apply (simp (no_asm_simp) add: impl_ioas split del: if_split)
  apply (induct_tac "a")

  ML_prf \<open>val tac3 = asm_full_simp_tac (put_simpset ss \<^context> addsimps [@{thm inv3_def}])\<close>

  txt \<open>10 - 8\<close>

  apply (tactic "EVERY1[tac3,tac3,tac3]")

  apply (tactic "tac_ren \<^context> 1")
  apply (intro strip, (erule conjE)+)
  apply hypsubst
  apply (erule exE)
  apply simp

  txt \<open>7\<close>
  apply (tactic "tac3 1")
  apply (tactic "tac_ren \<^context> 1")
  apply force

  txt \<open>6 - 3\<close>

  apply (tactic "EVERY1[tac3,tac3,tac3,tac3]")

  txt \<open>2\<close>
  apply (tactic "asm_full_simp_tac (put_simpset ss \<^context>) 1")
  apply (simp (no_asm) add: inv3_def)
  apply (intro strip, (erule conjE)+)
  apply (rule imp_disjL [THEN iffD1])
  apply (rule impI)
  apply (tactic \<open>forward_tac \<^context> [rewrite_rule \<^context> [@{thm Impl.inv2_def}]
    (@{thm raw_inv2} RS @{thm invariantE})] 1\<close>)
  apply simp
  apply (erule conjE)+
  apply (rule_tac j = "count (ssent (sen s)) (~sbit (sen s))" and
    k = "count (rsent (rec s)) (sbit (sen s))" in le_trans)
  apply (tactic \<open>forward_tac \<^context> [rewrite_rule \<^context> [@{thm inv1_def}]
                                (@{thm raw_inv1} RS @{thm invariantE}) RS conjunct2] 1\<close>)
  apply (simp add: hdr_sum_def Multiset.count_def)
  apply (rule add_le_mono)
  apply (rule countm_props)
  apply (simp (no_asm))
  apply (rule countm_props)
  apply (simp (no_asm))
  apply assumption

  txt \<open>1\<close>
  apply (tactic "tac3 1")
  apply (intro strip, (erule conjE)+)
  apply (rule imp_disjL [THEN iffD1])
  apply (rule impI)
  apply (tactic \<open>forward_tac \<^context> [rewrite_rule \<^context> [@{thm Impl.inv2_def}]
    (@{thm raw_inv2} RS @{thm invariantE})] 1\<close>)
  apply simp
  done


subsubsection \<open>INVARIANT 4\<close>

lemma raw_inv4: "invariant impl_ioa inv4"

  apply (rule invariantI)
  txt \<open>Base case\<close>
  apply (simp add: Impl.inv4_def receiver_projections sender_projections impl_ioas)

  apply (simp (no_asm_simp) add: impl_ioas split del: if_split)
  apply (induct_tac "a")

  ML_prf \<open>val tac4 =  asm_full_simp_tac (put_simpset ss \<^context> addsimps [@{thm inv4_def}])\<close>

  txt \<open>10 - 2\<close>

  apply (tactic "EVERY1[tac4,tac4,tac4,tac4,tac4,tac4,tac4,tac4,tac4]")

  txt \<open>2 b\<close>

  apply (intro strip, (erule conjE)+)
  apply (tactic \<open>forward_tac \<^context> [rewrite_rule \<^context> [@{thm Impl.inv2_def}]
                               (@{thm raw_inv2} RS @{thm invariantE})] 1\<close>)
  apply simp

  txt \<open>1\<close>
  apply (tactic "tac4 1")
  apply (intro strip, (erule conjE)+)
  apply (rule ccontr)
  apply (tactic \<open>forward_tac \<^context> [rewrite_rule \<^context> [@{thm Impl.inv2_def}]
                               (@{thm raw_inv2} RS @{thm invariantE})] 1\<close>)
  apply (tactic \<open>forward_tac \<^context> [rewrite_rule \<^context> [@{thm Impl.inv3_def}]
                               (@{thm raw_inv3} RS @{thm invariantE})] 1\<close>)
  apply simp
  apply (rename_tac m, erule_tac x = "m" in allE)
  apply simp
  done


text \<open>rebind them\<close>

lemmas inv1 = raw_inv1 [THEN invariantE, unfolded inv1_def]
  and inv2 = raw_inv2 [THEN invariantE, unfolded inv2_def]
  and inv3 = raw_inv3 [THEN invariantE, unfolded inv3_def]
  and inv4 = raw_inv4 [THEN invariantE, unfolded inv4_def]

end
