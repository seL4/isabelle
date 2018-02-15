(*  Title:      HOL/Auth/Guard/Guard_OtwayRees.thy
    Author:     Frederic Blanqui, University of Cambridge Computer Laboratory
    Copyright   2002  University of Cambridge
*)

section\<open>Otway-Rees Protocol\<close>

theory Guard_OtwayRees imports Guard_Shared begin

subsection\<open>messages used in the protocol\<close>

abbreviation
  nil :: "msg" where
  "nil == Number 0"

abbreviation
  or1 :: "agent => agent => nat => event" where
  "or1 A B NA ==
    Says A B \<lbrace>Nonce NA, Agent A, Agent B, Ciph A \<lbrace>Nonce NA, Agent A, Agent B\<rbrace>\<rbrace>"

abbreviation
  or1' :: "agent => agent => agent => nat => msg => event" where
  "or1' A' A B NA X == Says A' B \<lbrace>Nonce NA, Agent A, Agent B, X\<rbrace>"

abbreviation
  or2 :: "agent => agent => nat => nat => msg => event" where
  "or2 A B NA NB X ==
    Says B Server \<lbrace>Nonce NA, Agent A, Agent B, X,
                    Ciph B \<lbrace>Nonce NA, Nonce NB, Agent A, Agent B\<rbrace>\<rbrace>"

abbreviation
  or2' :: "agent => agent => agent => nat => nat => event" where
  "or2' B' A B NA NB ==
    Says B' Server \<lbrace>Nonce NA, Agent A, Agent B,
                     Ciph A \<lbrace>Nonce NA, Agent A, Agent B\<rbrace>,
                     Ciph B \<lbrace>Nonce NA, Nonce NB, Agent A, Agent B\<rbrace>\<rbrace>"

abbreviation
  or3 :: "agent => agent => nat => nat => key => event" where
  "or3 A B NA NB K ==
    Says Server B \<lbrace>Nonce NA, Ciph A \<lbrace>Nonce NA, Key K\<rbrace>,
                    Ciph B \<lbrace>Nonce NB, Key K\<rbrace>\<rbrace>"

abbreviation
  or3':: "agent => msg => agent => agent => nat => nat => key => event" where
  "or3' S Y A B NA NB K ==
    Says S B \<lbrace>Nonce NA, Y, Ciph B \<lbrace>Nonce NB, Key K\<rbrace>\<rbrace>"

abbreviation
  or4 :: "agent => agent => nat => msg => event" where
  "or4 A B NA X == Says B A \<lbrace>Nonce NA, X, nil\<rbrace>"

abbreviation
  or4' :: "agent => agent => nat => key => event" where
  "or4' B' A NA K == Says B' A \<lbrace>Nonce NA, Ciph A \<lbrace>Nonce NA, Key K\<rbrace>, nil\<rbrace>"

subsection\<open>definition of the protocol\<close>

inductive_set or :: "event list set"
where

  Nil: "[] \<in> or"

| Fake: "[| evs \<in> or; X \<in> synth (analz (spies evs)) |] ==> Says Spy B X # evs \<in> or"

| OR1: "[| evs1 \<in> or; Nonce NA \<notin> used evs1 |] ==> or1 A B NA # evs1 \<in> or"

| OR2: "[| evs2 \<in> or; or1' A' A B NA X \<in> set evs2; Nonce NB \<notin> used evs2 |]
  ==> or2 A B NA NB X # evs2 \<in> or"

| OR3: "[| evs3 \<in> or; or2' B' A B NA NB \<in> set evs3; Key K \<notin> used evs3 |]
  ==> or3 A B NA NB K # evs3 \<in> or"

| OR4: "[| evs4 \<in> or; or2 A B NA NB X \<in> set evs4; or3' S Y A B NA NB K \<in> set evs4 |]
  ==> or4 A B NA X # evs4 \<in> or"

subsection\<open>declarations for tactics\<close>

declare knows_Spy_partsEs [elim]
declare Fake_parts_insert [THEN subsetD, dest]
declare initState.simps [simp del]

subsection\<open>general properties of or\<close>

lemma or_has_no_Gets: "evs \<in> or \<Longrightarrow> \<forall>A X. Gets A X \<notin> set evs"
by (erule or.induct, auto)

lemma or_is_Gets_correct [iff]: "Gets_correct or"
by (auto simp: Gets_correct_def dest: or_has_no_Gets)

lemma or_is_one_step [iff]: "one_step or"
by (unfold one_step_def, clarify, ind_cases "ev#evs \<in> or" for ev evs, auto)

lemma or_has_only_Says' [rule_format]: "evs \<in> or \<Longrightarrow>
ev \<in> set evs \<longrightarrow> (\<exists>A B X. ev=Says A B X)"
by (erule or.induct, auto)

lemma or_has_only_Says [iff]: "has_only_Says or"
by (auto simp: has_only_Says_def dest: or_has_only_Says')

subsection\<open>or is regular\<close>

lemma or1'_parts_spies [dest]: "or1' A' A B NA X \<in> set evs
\<Longrightarrow> X \<in> parts (spies evs)"
by blast

lemma or2_parts_spies [dest]: "or2 A B NA NB X \<in> set evs
\<Longrightarrow> X \<in> parts (spies evs)"
by blast

lemma or3_parts_spies [dest]: "Says S B \<lbrace>NA, Y, Ciph B \<lbrace>NB, K\<rbrace>\<rbrace> \<in> set evs
\<Longrightarrow> K \<in> parts (spies evs)"
by blast

lemma or_is_regular [iff]: "regular or"
apply (simp only: regular_def, clarify)
apply (erule or.induct, simp_all add: initState.simps knows.simps)
by (auto dest: parts_sub)

subsection\<open>guardedness of KAB\<close>

lemma Guard_KAB [rule_format]: "[| evs \<in> or; A \<notin> bad; B \<notin> bad |] ==>
or3 A B NA NB K \<in> set evs \<longrightarrow> GuardK K {shrK A,shrK B} (spies evs)" 
apply (erule or.induct)
(* Nil *)
apply simp_all
(* Fake *)
apply (clarify, erule in_synth_GuardK, erule GuardK_analz, simp)
(* OR1 *)
apply blast
(* OR2 *)
apply safe
apply (blast dest: Says_imp_spies, blast)
(* OR3 *)
apply blast
apply (drule_tac A=Server in Key_neq, simp+, rule No_Key, simp)
apply (drule_tac A=Server in Key_neq, simp+, rule No_Key, simp)
(* OR4 *)
by (blast dest: Says_imp_spies in_GuardK_kparts)

subsection\<open>guardedness of NB\<close>

lemma Guard_NB [rule_format]: "[| evs \<in> or; B \<notin> bad |] ==>
or2 A B NA NB X \<in> set evs \<longrightarrow> Guard NB {shrK B} (spies evs)" 
apply (erule or.induct)
(* Nil *)
apply simp_all
(* Fake *)
apply safe
apply (erule in_synth_Guard, erule Guard_analz, simp)
(* OR1 *)
apply (drule_tac n=NB in Nonce_neq, simp+, rule No_Nonce, simp)
apply (drule_tac n=NB in Nonce_neq, simp+, rule No_Nonce, simp)
(* OR2 *)
apply blast
apply (drule_tac n=NA in Nonce_neq, simp+, rule No_Nonce, simp)
apply (blast intro!: No_Nonce dest: used_parts)
apply (drule_tac n=NA in Nonce_neq, simp+, rule No_Nonce, simp)
apply (blast intro!: No_Nonce dest: used_parts)
apply (blast dest: Says_imp_spies)
apply (blast dest: Says_imp_spies)
apply (case_tac "Ba=B", clarsimp)
apply (drule_tac n=NB and A=B in Nonce_neq, simp+)
apply (drule Says_imp_spies)
apply (drule_tac n'=NAa in in_Guard_kparts_neq, simp+, rule No_Nonce, simp)
(* OR3 *)
apply (drule Says_imp_spies)
apply (frule_tac n'=NAa in in_Guard_kparts_neq, simp+, rule No_Nonce, simp)
apply (case_tac "Aa=B", clarsimp)
apply (case_tac "NAa=NB", clarsimp)
apply (drule Says_imp_spies)
apply (drule_tac Y="\<lbrace>Nonce NB, Agent Aa, Agent Ba\<rbrace>"
                 and K="shrK Aa" in in_Guard_kparts_Crypt, simp+)
apply (simp add: No_Nonce) 
apply (case_tac "Ba=B", clarsimp)
apply (case_tac "NBa=NB", clarify)
apply (drule Says_imp_spies)
apply (drule_tac Y="\<lbrace>Nonce NAa, Nonce NB, Agent Aa, Agent Ba\<rbrace>"
                 and K="shrK Ba" in in_Guard_kparts_Crypt, simp+)
apply (simp add: No_Nonce) 
(* OR4 *)
by (blast dest: Says_imp_spies)+

end
