(*  Title:      HOL/Auth/Guard/Guard_Yahalom.thy
    Author:     Frederic Blanqui, University of Cambridge Computer Laboratory
    Copyright   2002  University of Cambridge
*)

section\<open>Yahalom Protocol\<close>

theory Guard_Yahalom imports "../Shared" Guard_Shared begin

subsection\<open>messages used in the protocol\<close>

abbreviation (input)
  ya1 :: "agent => agent => nat => event" where
  "ya1 A B NA == Says A B \<lbrace>Agent A, Nonce NA\<rbrace>"

abbreviation (input)
  ya1' :: "agent => agent => agent => nat => event" where
  "ya1' A' A B NA == Says A' B \<lbrace>Agent A, Nonce NA\<rbrace>"

abbreviation (input)
  ya2 :: "agent => agent => nat => nat => event" where
  "ya2 A B NA NB == Says B Server \<lbrace>Agent B, Ciph B \<lbrace>Agent A, Nonce NA, Nonce NB\<rbrace>\<rbrace>"

abbreviation (input)
  ya2' :: "agent => agent => agent => nat => nat => event" where
  "ya2' B' A B NA NB == Says B' Server \<lbrace>Agent B, Ciph B \<lbrace>Agent A, Nonce NA, Nonce NB\<rbrace>\<rbrace>"

abbreviation (input)
  ya3 :: "agent => agent => nat => nat => key => event" where
  "ya3 A B NA NB K ==
    Says Server A \<lbrace>Ciph A \<lbrace>Agent B, Key K, Nonce NA, Nonce NB\<rbrace>,
                    Ciph B \<lbrace>Agent A, Key K\<rbrace>\<rbrace>"

abbreviation (input)
  ya3':: "agent => msg => agent => agent => nat => nat => key => event" where
  "ya3' S Y A B NA NB K ==
    Says S A \<lbrace>Ciph A \<lbrace>Agent B, Key K, Nonce NA, Nonce NB\<rbrace>, Y\<rbrace>"

abbreviation (input)
  ya4 :: "agent => agent => nat => nat => msg => event" where
  "ya4 A B K NB Y == Says A B \<lbrace>Y, Crypt K (Nonce NB)\<rbrace>"

abbreviation (input)
  ya4' :: "agent => agent => nat => nat => msg => event" where
  "ya4' A' B K NB Y == Says A' B \<lbrace>Y, Crypt K (Nonce NB)\<rbrace>"


subsection\<open>definition of the protocol\<close>

inductive_set ya :: "event list set"
where

  Nil: "[] \<in> ya"

| Fake: "[| evs \<in> ya; X \<in> synth (analz (spies evs)) |] ==> Says Spy B X # evs \<in> ya"

| YA1: "[| evs1 \<in> ya; Nonce NA \<notin> used evs1 |] ==> ya1 A B NA # evs1 \<in> ya"

| YA2: "[| evs2 \<in> ya; ya1' A' A B NA \<in> set evs2; Nonce NB \<notin> used evs2 |]
  ==> ya2 A B NA NB # evs2 \<in> ya"

| YA3: "[| evs3 \<in> ya; ya2' B' A B NA NB \<in> set evs3; Key K \<notin> used evs3 |]
  ==> ya3 A B NA NB K # evs3 \<in> ya"

| YA4: "[| evs4 \<in> ya; ya1 A B NA \<in> set evs4; ya3' S Y A B NA NB K \<in> set evs4 |]
  ==> ya4 A B K NB Y # evs4 \<in> ya"

subsection\<open>declarations for tactics\<close>

declare knows_Spy_partsEs [elim]
declare Fake_parts_insert [THEN subsetD, dest]
declare initState.simps [simp del]

subsection\<open>general properties of ya\<close>

lemma ya_has_no_Gets: "evs \<in> ya \<Longrightarrow> \<forall>A X. Gets A X \<notin> set evs"
by (erule ya.induct, auto)

lemma ya_is_Gets_correct [iff]: "Gets_correct ya"
by (auto simp: Gets_correct_def dest: ya_has_no_Gets)

lemma ya_is_one_step [iff]: "one_step ya"
by (unfold one_step_def, clarify, ind_cases "ev#evs \<in> ya" for ev evs, auto)

lemma ya_has_only_Says' [rule_format]: "evs \<in> ya \<Longrightarrow>
ev \<in> set evs \<longrightarrow> (\<exists>A B X. ev=Says A B X)"
by (erule ya.induct, auto)

lemma ya_has_only_Says [iff]: "has_only_Says ya"
by (auto simp: has_only_Says_def dest: ya_has_only_Says')

lemma ya_is_regular [iff]: "regular ya"
apply (simp only: regular_def, clarify)
apply (erule ya.induct, simp_all add: initState.simps knows.simps)
by (auto dest: parts_sub)

subsection\<open>guardedness of KAB\<close>

lemma Guard_KAB [rule_format]: "[| evs \<in> ya; A \<notin> bad; B \<notin> bad |] ==>
ya3 A B NA NB K \<in> set evs \<longrightarrow> GuardK K {shrK A,shrK B} (spies evs)" 
apply (erule ya.induct)
(* Nil *)
apply simp_all
(* Fake *)
apply (clarify, erule in_synth_GuardK, erule GuardK_analz, simp)
(* YA1 *)
(* YA2 *)
apply safe
apply (blast dest: Says_imp_spies)
(* YA3 *)
apply blast
apply (drule_tac A=Server in Key_neq, simp+, rule No_Key, simp)
apply (drule_tac A=Server in Key_neq, simp+, rule No_Key, simp)
(* YA4 *)
apply (blast dest: Says_imp_spies in_GuardK_kparts)
by blast

subsection\<open>session keys are not symmetric keys\<close>

lemma KAB_isnt_shrK [rule_format]: "evs \<in> ya \<Longrightarrow>
ya3 A B NA NB K \<in> set evs \<longrightarrow> K \<notin> range shrK"
by (erule ya.induct, auto)

lemma ya3_shrK: "evs \<in> ya \<Longrightarrow> ya3 A B NA NB (shrK C) \<notin> set evs"
by (blast dest: KAB_isnt_shrK)

subsection\<open>ya2' implies ya1'\<close>

lemma ya2'_parts_imp_ya1'_parts [rule_format]:
     "[| evs \<in> ya; B \<notin> bad |] ==>
      Ciph B \<lbrace>Agent A, Nonce NA, Nonce NB\<rbrace> \<in> parts (spies evs) \<longrightarrow>
      \<lbrace>Agent A, Nonce NA\<rbrace> \<in> spies evs"
by (erule ya.induct, auto dest: Says_imp_spies intro: parts_parts)

lemma ya2'_imp_ya1'_parts: "[| ya2' B' A B NA NB \<in> set evs; evs \<in> ya; B \<notin> bad |]
==> \<lbrace>Agent A, Nonce NA\<rbrace> \<in> spies evs"
by (blast dest: Says_imp_spies ya2'_parts_imp_ya1'_parts)

subsection\<open>uniqueness of NB\<close>

lemma NB_is_uniq_in_ya2'_parts [rule_format]: "[| evs \<in> ya; B \<notin> bad; B' \<notin> bad |] ==>
Ciph B \<lbrace>Agent A, Nonce NA, Nonce NB\<rbrace> \<in> parts (spies evs) \<longrightarrow>
Ciph B' \<lbrace>Agent A', Nonce NA', Nonce NB\<rbrace> \<in> parts (spies evs) \<longrightarrow>
A=A' \<and> B=B' \<and> NA=NA'"
apply (erule ya.induct, simp_all, clarify)
apply (drule Crypt_synth_insert, simp+)
apply (drule Crypt_synth_insert, simp+, safe)
apply (drule not_used_parts_false, simp+)+
by (drule Says_not_parts, simp+)+

lemma NB_is_uniq_in_ya2': "[| ya2' C A B NA NB \<in> set evs;
ya2' C' A' B' NA' NB \<in> set evs; evs \<in> ya; B \<notin> bad; B' \<notin> bad |]
==> A=A' \<and> B=B' \<and> NA=NA'"
by (drule NB_is_uniq_in_ya2'_parts, auto dest: Says_imp_spies)

subsection\<open>ya3' implies ya2'\<close>

lemma ya3'_parts_imp_ya2'_parts [rule_format]: "[| evs \<in> ya; A \<notin> bad |] ==>
Ciph A \<lbrace>Agent B, Key K, Nonce NA, Nonce NB\<rbrace> \<in> parts (spies evs)
\<longrightarrow> Ciph B \<lbrace>Agent A, Nonce NA, Nonce NB\<rbrace> \<in> parts (spies evs)"
apply (erule ya.induct, simp_all)
apply (clarify, drule Crypt_synth_insert, simp+)
apply (blast intro: parts_sub, blast)
by (auto dest: Says_imp_spies parts_parts)

lemma ya3'_parts_imp_ya2' [rule_format]: "[| evs \<in> ya; A \<notin> bad |] ==>
Ciph A \<lbrace>Agent B, Key K, Nonce NA, Nonce NB\<rbrace> \<in> parts (spies evs)
\<longrightarrow> (\<exists>B'. ya2' B' A B NA NB \<in> set evs)"
apply (erule ya.induct, simp_all, safe)
apply (drule Crypt_synth_insert, simp+)
apply (drule Crypt_synth_insert, simp+, blast)
apply blast
apply blast
by (auto dest: Says_imp_spies2 parts_parts)

lemma ya3'_imp_ya2': "[| ya3' S Y A B NA NB K \<in> set evs; evs \<in> ya; A \<notin> bad |]
==> (\<exists>B'. ya2' B' A B NA NB \<in> set evs)"
by (drule ya3'_parts_imp_ya2', auto dest: Says_imp_spies)

subsection\<open>ya3' implies ya3\<close>

lemma ya3'_parts_imp_ya3 [rule_format]: "[| evs \<in> ya; A \<notin> bad |] ==>
Ciph A \<lbrace>Agent B, Key K, Nonce NA, Nonce NB\<rbrace> \<in> parts(spies evs)
\<longrightarrow> ya3 A B NA NB K \<in> set evs"
apply (erule ya.induct, simp_all, safe)
apply (drule Crypt_synth_insert, simp+)
by (blast dest: Says_imp_spies2 parts_parts)

lemma ya3'_imp_ya3: "[| ya3' S Y A B NA NB K \<in> set evs; evs \<in> ya; A \<notin> bad |]
==> ya3 A B NA NB K \<in> set evs"
by (blast dest: Says_imp_spies ya3'_parts_imp_ya3)

subsection\<open>guardedness of NB\<close>

definition ya_keys :: "agent \<Rightarrow> agent \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> event list \<Rightarrow> key set" where
"ya_keys A B NA NB evs \<equiv> {shrK A,shrK B} \<union> {K. ya3 A B NA NB K \<in> set evs}"

lemma Guard_NB [rule_format]: "[| evs \<in> ya; A \<notin> bad; B \<notin> bad |] ==>
ya2 A B NA NB \<in> set evs \<longrightarrow> Guard NB (ya_keys A B NA NB evs) (spies evs)"
apply (erule ya.induct)
(* Nil *)
apply (simp_all add: ya_keys_def)
(* Fake *)
apply safe
apply (erule in_synth_Guard, erule Guard_analz, simp, clarify)
apply (frule_tac B=B in Guard_KAB, simp+)
apply (drule_tac p=ya in GuardK_Key_analz, simp+)
apply (blast dest: KAB_isnt_shrK, simp)
(* YA1 *)
apply (drule_tac n=NB in Nonce_neq, simp+, rule No_Nonce, simp)
(* YA2 *)
apply blast
apply (drule Says_imp_spies)
apply (drule_tac n=NB in Nonce_neq, simp+)
apply (drule_tac n'=NAa in in_Guard_kparts_neq, simp+)
apply (rule No_Nonce, simp)
(* YA3 *)
apply (rule Guard_extand, simp, blast)
apply (case_tac "NAa=NB", clarify)
apply (frule Says_imp_spies)
apply (frule in_Guard_kparts_Crypt, simp+)
apply (frule_tac A=A and B=B and NA=NA and NB=NB and C=Ba in ya3_shrK, simp)
apply (drule ya2'_imp_ya1'_parts, simp, blast, blast)
apply (case_tac "NBa=NB", clarify)
apply (frule Says_imp_spies)
apply (frule in_Guard_kparts_Crypt, simp+)
apply (frule_tac A=A and B=B and NA=NA and NB=NB and C=Ba in ya3_shrK, simp)
apply (drule NB_is_uniq_in_ya2', simp+, blast, simp+)
apply (simp add: No_Nonce, blast)
(* YA4 *)
apply (blast dest: Says_imp_spies)
apply (case_tac "NBa=NB", clarify)
apply (frule_tac A=S in Says_imp_spies)
apply (frule in_Guard_kparts_Crypt, simp+)
apply (blast dest: Says_imp_spies)
apply (case_tac "NBa=NB", clarify)
apply (frule_tac A=S in Says_imp_spies)
apply (frule in_Guard_kparts_Crypt, simp+, blast, simp+)
apply (frule_tac A=A and B=B and NA=NA and NB=NB and C=Aa in ya3_shrK, simp)
apply (frule ya3'_imp_ya2', simp+, blast, clarify)
apply (frule_tac A=B' in Says_imp_spies)
apply (rotate_tac -1, frule in_Guard_kparts_Crypt, simp+)
apply (frule_tac A=A and B=B and NA=NA and NB=NB and C=Ba in ya3_shrK, simp)
apply (drule NB_is_uniq_in_ya2', simp+, blast, clarify)
apply (drule ya3'_imp_ya3, simp+)
apply (simp add: Guard_Nonce)
apply (simp add: No_Nonce)
done

end
