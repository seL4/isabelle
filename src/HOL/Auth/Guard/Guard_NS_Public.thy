(*  Title:      HOL/Auth/Guard/Guard_NS_Public.thy
    Author:     Frederic Blanqui, University of Cambridge Computer Laboratory
    Copyright   2002  University of Cambridge

Incorporating Lowe's fix (inclusion of B's identity in round 2).
*)

section\<open>Needham-Schroeder-Lowe Public-Key Protocol\<close>

theory Guard_NS_Public imports Guard_Public begin

subsection\<open>messages used in the protocol\<close>

abbreviation (input)
  ns1 :: "agent => agent => nat => event" where
  "ns1 A B NA == Says A B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>)"

abbreviation (input)
  ns1' :: "agent => agent => agent => nat => event" where
  "ns1' A' A B NA == Says A' B (Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace>)"

abbreviation (input)
  ns2 :: "agent => agent => nat => nat => event" where
  "ns2 B A NA NB == Says B A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>)"

abbreviation (input)
  ns2' :: "agent => agent => agent => nat => nat => event" where
  "ns2' B' B A NA NB == Says B' A (Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace>)"

abbreviation (input)
  ns3 :: "agent => agent => nat => event" where
  "ns3 A B NB == Says A B (Crypt (pubK B) (Nonce NB))"


subsection\<open>definition of the protocol\<close>

inductive_set nsp :: "event list set"
where

  Nil: "[] \<in> nsp"

| Fake: "[| evs \<in> nsp; X \<in> synth (analz (spies evs)) |] ==> Says Spy B X # evs \<in> nsp"

| NS1: "[| evs1 \<in> nsp; Nonce NA \<notin> used evs1 |] ==> ns1 A B NA # evs1 \<in> nsp"

| NS2: "[| evs2 \<in> nsp; Nonce NB \<notin> used evs2; ns1' A' A B NA \<in> set evs2 |] ==>
  ns2 B A NA NB # evs2 \<in> nsp"

| NS3: "\<And>A B B' NA NB evs3. [| evs3 \<in> nsp; ns1 A B NA \<in> set evs3; ns2' B' B A NA NB \<in> set evs3 |] ==>
  ns3 A B NB # evs3 \<in> nsp"

subsection\<open>declarations for tactics\<close>

declare knows_Spy_partsEs [elim]
declare Fake_parts_insert [THEN subsetD, dest]
declare initState.simps [simp del]

subsection\<open>general properties of nsp\<close>

lemma nsp_has_no_Gets: "evs \<in> nsp \<Longrightarrow> \<forall>A X. Gets A X \<notin> set evs"
by (erule nsp.induct, auto)

lemma nsp_is_Gets_correct [iff]: "Gets_correct nsp"
by (auto simp: Gets_correct_def dest: nsp_has_no_Gets)

lemma nsp_is_one_step [iff]: "one_step nsp"
by (unfold one_step_def, clarify, ind_cases "ev#evs \<in> nsp" for ev evs, auto)

lemma nsp_has_only_Says' [rule_format]: "evs \<in> nsp \<Longrightarrow>
ev \<in> set evs \<longrightarrow> (\<exists>A B X. ev=Says A B X)"
by (erule nsp.induct, auto)

lemma nsp_has_only_Says [iff]: "has_only_Says nsp"
by (auto simp: has_only_Says_def dest: nsp_has_only_Says')

lemma nsp_is_regular [iff]: "regular nsp"
apply (simp only: regular_def, clarify)
by (erule nsp.induct, auto simp: initState.simps knows.simps)

subsection\<open>nonce are used only once\<close>

lemma NA_is_uniq [rule_format]: "evs \<in> nsp \<Longrightarrow>
Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (spies evs)
\<longrightarrow> Crypt (pubK B') \<lbrace>Nonce NA, Agent A'\<rbrace> \<in> parts (spies evs)
\<longrightarrow> Nonce NA \<notin> analz (spies evs) \<longrightarrow> A=A' \<and> B=B'"
apply (erule nsp.induct, simp_all)
by (blast intro: analz_insertI)+

lemma no_Nonce_NS1_NS2 [rule_format]: "evs \<in> nsp \<Longrightarrow>
Crypt (pubK B') \<lbrace>Nonce NA', Nonce NA, Agent A'\<rbrace> \<in> parts (spies evs)
\<longrightarrow> Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (spies evs)
\<longrightarrow> Nonce NA \<in> analz (spies evs)"
apply (erule nsp.induct, simp_all)
by (blast intro: analz_insertI)+

lemma no_Nonce_NS1_NS2' [rule_format]:
"[| Crypt (pubK B') \<lbrace>Nonce NA', Nonce NA, Agent A'\<rbrace> \<in> parts (spies evs);
Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (spies evs); evs \<in> nsp |]
==> Nonce NA \<in> analz (spies evs)"
by (rule no_Nonce_NS1_NS2, auto)
 
lemma NB_is_uniq [rule_format]: "evs \<in> nsp \<Longrightarrow>
Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace> \<in> parts (spies evs)
\<longrightarrow> Crypt (pubK A') \<lbrace>Nonce NA', Nonce NB, Agent B'\<rbrace> \<in> parts (spies evs)
\<longrightarrow> Nonce NB \<notin> analz (spies evs) \<longrightarrow> A=A' \<and> B=B' \<and> NA=NA'"
apply (erule nsp.induct, simp_all)
by (blast intro: analz_insertI)+

subsection\<open>guardedness of NA\<close>

lemma ns1_imp_Guard [rule_format]: "[| evs \<in> nsp; A \<notin> bad; B \<notin> bad |] ==>
ns1 A B NA \<in> set evs \<longrightarrow> Guard NA {priK A,priK B} (spies evs)"
apply (erule nsp.induct)
(* Nil *)
apply simp_all
(* Fake *)
apply safe
apply (erule in_synth_Guard, erule Guard_analz, simp)
(* NS1 *)
apply blast
apply blast
apply blast
apply (drule Nonce_neq, simp+, rule No_Nonce, simp)
(* NS2 *)
apply (frule_tac A=A in Nonce_neq, simp+)
apply (case_tac "NAa=NA")
apply (drule Guard_Nonce_analz, simp+)
apply (drule Says_imp_knows_Spy)+
apply (drule_tac B=B and A'=Aa in NA_is_uniq, auto)
(* NS3 *)
apply (case_tac "NB=NA", clarify)
apply (drule Guard_Nonce_analz, simp+)
apply (drule Says_imp_knows_Spy)+
by (drule no_Nonce_NS1_NS2, auto)

subsection\<open>guardedness of NB\<close>

lemma ns2_imp_Guard [rule_format]: "[| evs \<in> nsp; A \<notin> bad; B \<notin> bad |] ==>
ns2 B A NA NB \<in> set evs \<longrightarrow> Guard NB {priK A,priK B} (spies evs)" 
apply (erule nsp.induct)
(* Nil *)
apply simp_all
(* Fake *)
apply safe
apply (erule in_synth_Guard, erule Guard_analz, simp)
(* NS1 *)
apply (frule Nonce_neq, simp+, blast, rule No_Nonce, simp)
(* NS2 *)
apply blast
apply blast
apply blast
apply (frule_tac A=B and n=NB in Nonce_neq, simp+)
apply (case_tac "NAa=NB")
apply (drule Guard_Nonce_analz, simp+)
apply (drule Says_imp_knows_Spy)+
apply (drule no_Nonce_NS1_NS2, auto)
(* NS3 *)
apply (case_tac "NBa=NB", clarify)
apply (drule Guard_Nonce_analz, simp+)
apply (drule Says_imp_knows_Spy)+
apply (drule_tac A=Aa and A'=A in NB_is_uniq)
apply auto[1]
apply (auto simp add: guard.No_Nonce)
done

subsection\<open>Agents' Authentication\<close>

lemma B_trusts_NS1: "[| evs \<in> nsp; A \<notin> bad; B \<notin> bad |] ==>
Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (spies evs)
\<longrightarrow> Nonce NA \<notin> analz (spies evs) \<longrightarrow> ns1 A B NA \<in> set evs"
apply (erule nsp.induct, simp_all)
by (blast intro: analz_insertI)+

lemma A_trusts_NS2: "[| evs \<in> nsp; A \<notin> bad; B \<notin> bad |] ==> ns1 A B NA \<in> set evs
\<longrightarrow> Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB, Agent B\<rbrace> \<in> parts (spies evs)
\<longrightarrow> ns2 B A NA NB \<in> set evs"
apply (erule nsp.induct, simp_all, safe)
apply (frule_tac B=B in ns1_imp_Guard, simp+)
apply (drule Guard_Nonce_analz, simp+, blast)
apply (frule_tac B=B in ns1_imp_Guard, simp+)
apply (drule Guard_Nonce_analz, simp+, blast)
apply (frule_tac B=B in ns1_imp_Guard, simp+)
by (drule Guard_Nonce_analz, simp+, blast+)

lemma B_trusts_NS3: "[| evs \<in> nsp; A \<notin> bad; B \<notin> bad |] ==> ns2 B A NA NB \<in> set evs
\<longrightarrow> Crypt (pubK B) (Nonce NB) \<in> parts (spies evs) \<longrightarrow> ns3 A B NB \<in> set evs"
apply (erule nsp.induct, simp_all, safe)
apply (frule_tac B=B in ns2_imp_Guard, simp+)
apply (drule Guard_Nonce_analz, simp+, blast)
apply (frule_tac B=B in ns2_imp_Guard, simp+)
apply (drule Guard_Nonce_analz, simp+, blast)
apply (frule_tac B=B in ns2_imp_Guard, simp+)
apply (drule Guard_Nonce_analz, simp+, blast, blast)
apply (frule_tac B=B in ns2_imp_Guard, simp+)
by (drule Guard_Nonce_analz, auto dest: Says_imp_knows_Spy NB_is_uniq)

end
