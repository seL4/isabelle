(*  Title:      HOL/Auth/Guard/Guard.thy
    Author:     Frederic Blanqui, University of Cambridge Computer Laboratory
    Copyright   2002  University of Cambridge
*)

section\<open>Protocol-Independent Confidentiality Theorem on Nonces\<close>

theory Guard imports Analz Extensions begin

(******************************************************************************
messages where all the occurrences of Nonce n are
in a sub-message of the form Crypt (invKey K) X with K:Ks
******************************************************************************)

inductive_set
  guard :: "nat \<Rightarrow> key set \<Rightarrow> msg set"
  for n :: nat and Ks :: "key set"
where
  No_Nonce [intro]: "Nonce n \<notin> parts {X} \<Longrightarrow> X \<in> guard n Ks"
| Guard_Nonce [intro]: "invKey K \<in> Ks \<Longrightarrow> Crypt K X \<in> guard n Ks"
| Crypt [intro]: "X \<in> guard n Ks \<Longrightarrow> Crypt K X \<in> guard n Ks"
| Pair [intro]: "[| X \<in> guard n Ks; Y \<in> guard n Ks |] ==> \<lbrace>X,Y\<rbrace> \<in> guard n Ks"

subsection\<open>basic facts about @{term guard}\<close>

lemma Key_is_guard [iff]: "Key K \<in> guard n Ks"
by auto

lemma Agent_is_guard [iff]: "Agent A \<in> guard n Ks"
by auto

lemma Number_is_guard [iff]: "Number r \<in> guard n Ks"
by auto

lemma Nonce_notin_guard: "X \<in> guard n Ks \<Longrightarrow> X \<noteq> Nonce n"
by (erule guard.induct, auto)

lemma Nonce_notin_guard_iff [iff]: "Nonce n \<notin> guard n Ks"
by (auto dest: Nonce_notin_guard)

lemma guard_has_Crypt [rule_format]: "X \<in> guard n Ks ==> Nonce n \<in> parts {X}
\<longrightarrow> (\<exists>K Y. Crypt K Y \<in> kparts {X} \<and> Nonce n \<in> parts {Y})"
by (erule guard.induct, auto)

lemma Nonce_notin_kparts_msg: "X \<in> guard n Ks \<Longrightarrow> Nonce n \<notin> kparts {X}"
by (erule guard.induct, auto)

lemma Nonce_in_kparts_imp_no_guard: "Nonce n \<in> kparts H
\<Longrightarrow> \<exists>X. X \<in> H \<and> X \<notin> guard n Ks"
apply (drule in_kparts, clarify)
apply (rule_tac x=X in exI, clarify)
by (auto dest: Nonce_notin_kparts_msg)

lemma guard_kparts [rule_format]: "X \<in> guard n Ks \<Longrightarrow>
Y \<in> kparts {X} \<longrightarrow> Y \<in> guard n Ks"
by (erule guard.induct, auto)

lemma guard_Crypt: "[| Crypt K Y \<in> guard n Ks; K \<notin> invKey`Ks |] ==> Y \<in> guard n Ks"
  by (ind_cases "Crypt K Y \<in> guard n Ks") (auto intro!: image_eqI)

lemma guard_MPair [iff]: "(\<lbrace>X,Y\<rbrace> \<in> guard n Ks) = (X \<in> guard n Ks \<and> Y \<in> guard n Ks)"
by (auto, (ind_cases "\<lbrace>X,Y\<rbrace> \<in> guard n Ks", auto)+)

lemma guard_not_guard [rule_format]: "X \<in> guard n Ks \<Longrightarrow>
Crypt K Y \<in> kparts {X} \<longrightarrow> Nonce n \<in> kparts {Y} \<longrightarrow> Y \<notin> guard n Ks"
by (erule guard.induct, auto dest: guard_kparts)

lemma guard_extand: "[| X \<in> guard n Ks; Ks \<subseteq> Ks' |] ==> X \<in> guard n Ks'"
by (erule guard.induct, auto)

subsection\<open>guarded sets\<close>

definition Guard :: "nat \<Rightarrow> key set \<Rightarrow> msg set \<Rightarrow> bool" where
"Guard n Ks H \<equiv> \<forall>X. X \<in> H \<longrightarrow> X \<in> guard n Ks"

subsection\<open>basic facts about @{term Guard}\<close>

lemma Guard_empty [iff]: "Guard n Ks {}"
by (simp add: Guard_def)

lemma notin_parts_Guard [intro]: "Nonce n \<notin> parts G \<Longrightarrow> Guard n Ks G"
apply (unfold Guard_def, clarify)
apply (subgoal_tac "Nonce n \<notin> parts {X}")
by (auto dest: parts_sub)

lemma Nonce_notin_kparts [simplified]: "Guard n Ks H \<Longrightarrow> Nonce n \<notin> kparts H"
by (auto simp: Guard_def dest: in_kparts Nonce_notin_kparts_msg)

lemma Guard_must_decrypt: "[| Guard n Ks H; Nonce n \<in> analz H |] ==>
\<exists>K Y. Crypt K Y \<in> kparts H \<and> Key (invKey K) \<in> kparts H"
apply (drule_tac P="\<lambda>G. Nonce n \<in> G" in analz_pparts_kparts_substD, simp)
by (drule must_decrypt, auto dest: Nonce_notin_kparts)

lemma Guard_kparts [intro]: "Guard n Ks H ==> Guard n Ks (kparts H)"
by (auto simp: Guard_def dest: in_kparts guard_kparts)

lemma Guard_mono: "[| Guard n Ks H; G <= H |] ==> Guard n Ks G"
by (auto simp: Guard_def)

lemma Guard_insert [iff]: "Guard n Ks (insert X H)
= (Guard n Ks H \<and> X \<in> guard n Ks)"
by (auto simp: Guard_def)

lemma Guard_Un [iff]: "Guard n Ks (G Un H) = (Guard n Ks G & Guard n Ks H)"
by (auto simp: Guard_def)

lemma Guard_synth [intro]: "Guard n Ks G ==> Guard n Ks (synth G)"
by (auto simp: Guard_def, erule synth.induct, auto)

lemma Guard_analz [intro]: "[| Guard n Ks G; \<forall>K. K \<in> Ks \<longrightarrow> Key K \<notin> analz G |]
==> Guard n Ks (analz G)"
apply (auto simp: Guard_def)
apply (erule analz.induct, auto)
by (ind_cases "Crypt K Xa \<in> guard n Ks" for K Xa, auto)

lemma in_Guard [dest]: "[| X \<in> G; Guard n Ks G |] ==> X \<in> guard n Ks"
by (auto simp: Guard_def)

lemma in_synth_Guard: "[| X \<in> synth G; Guard n Ks G |] ==> X \<in> guard n Ks"
by (drule Guard_synth, auto)

lemma in_analz_Guard: "[| X \<in> analz G; Guard n Ks G;
\<forall>K. K \<in> Ks \<longrightarrow> Key K \<notin> analz G |] ==> X \<in> guard n Ks"
by (drule Guard_analz, auto)

lemma Guard_keyset [simp]: "keyset G ==> Guard n Ks G"
by (auto simp: Guard_def)

lemma Guard_Un_keyset: "[| Guard n Ks G; keyset H |] ==> Guard n Ks (G \<union> H)"
by auto

lemma in_Guard_kparts: "[| X \<in> G; Guard n Ks G; Y \<in> kparts {X} |] ==> Y \<in> guard n Ks"
by blast

lemma in_Guard_kparts_neq: "[| X \<in> G; Guard n Ks G; Nonce n' \<in> kparts {X} |]
==> n \<noteq> n'"
by (blast dest: in_Guard_kparts)

lemma in_Guard_kparts_Crypt: "[| X \<in> G; Guard n Ks G; is_MPair X;
Crypt K Y \<in> kparts {X}; Nonce n \<in> kparts {Y} |] ==> invKey K \<in> Ks"
apply (drule in_Guard, simp)
apply (frule guard_not_guard, simp+)
apply (drule guard_kparts, simp)
by (ind_cases "Crypt K Y \<in> guard n Ks", auto)

lemma Guard_extand: "[| Guard n Ks G; Ks \<subseteq> Ks' |] ==> Guard n Ks' G"
by (auto simp: Guard_def dest: guard_extand)

lemma guard_invKey [rule_format]: "[| X \<in> guard n Ks; Nonce n \<in> kparts {Y} |] ==>
Crypt K Y \<in> kparts {X} \<longrightarrow> invKey K \<in> Ks"
by (erule guard.induct, auto)

lemma Crypt_guard_invKey [rule_format]: "[| Crypt K Y \<in> guard n Ks;
Nonce n \<in> kparts {Y} |] ==> invKey K \<in> Ks"
by (auto dest: guard_invKey)

subsection\<open>set obtained by decrypting a message\<close>

abbreviation (input)
  decrypt :: "msg set => key => msg => msg set" where
  "decrypt H K Y == insert Y (H - {Crypt K Y})"

lemma analz_decrypt: "[| Crypt K Y \<in> H; Key (invKey K) \<in> H; Nonce n \<in> analz H |]
==> Nonce n \<in> analz (decrypt H K Y)"
apply (drule_tac P="\<lambda>H. Nonce n \<in> analz H" in ssubst [OF insert_Diff])
apply assumption
apply (simp only: analz_Crypt_if, simp)
done

lemma parts_decrypt: "[| Crypt K Y \<in> H; X \<in> parts (decrypt H K Y) |] ==> X \<in> parts H"
by (erule parts.induct, auto intro: parts.Fst parts.Snd parts.Body)

subsection\<open>number of Crypt's in a message\<close>

fun crypt_nb :: "msg => nat"
where
  "crypt_nb (Crypt K X) = Suc (crypt_nb X)"
| "crypt_nb \<lbrace>X,Y\<rbrace> = crypt_nb X + crypt_nb Y"
| "crypt_nb X = 0" (* otherwise *)

subsection\<open>basic facts about @{term crypt_nb}\<close>

lemma non_empty_crypt_msg: "Crypt K Y \<in> parts {X} \<Longrightarrow> crypt_nb X \<noteq> 0"
by (induct X, simp_all, safe, simp_all)

subsection\<open>number of Crypt's in a message list\<close>

primrec cnb :: "msg list => nat"
where
  "cnb [] = 0"
| "cnb (X#l) = crypt_nb X + cnb l"

subsection\<open>basic facts about @{term cnb}\<close>

lemma cnb_app [simp]: "cnb (l @ l') = cnb l + cnb l'"
by (induct l, auto)

lemma mem_cnb_minus: "x \<in> set l ==> cnb l = crypt_nb x + (cnb l - crypt_nb x)"
  by (induct l) auto

lemmas mem_cnb_minus_substI = mem_cnb_minus [THEN ssubst]

lemma cnb_minus [simp]: "x \<in> set l ==> cnb (remove l x) = cnb l - crypt_nb x"
apply (induct l, auto)
apply (erule_tac l=l and x=x in mem_cnb_minus_substI)
apply simp
done

lemma parts_cnb: "Z \<in> parts (set l) \<Longrightarrow>
cnb l = (cnb l - crypt_nb Z) + crypt_nb Z"
by (erule parts.induct, auto simp: in_set_conv_decomp)

lemma non_empty_crypt: "Crypt K Y \<in> parts (set l) \<Longrightarrow> cnb l \<noteq> 0"
by (induct l, auto dest: non_empty_crypt_msg parts_insert_substD)

subsection\<open>list of kparts\<close>

lemma kparts_msg_set: "\<exists>l. kparts {X} = set l \<and> cnb l = crypt_nb X"
apply (induct X, simp_all)
apply (rename_tac agent, rule_tac x="[Agent agent]" in exI, simp)
apply (rename_tac nat, rule_tac x="[Number nat]" in exI, simp)
apply (rename_tac nat, rule_tac x="[Nonce nat]" in exI, simp)
apply (rename_tac nat, rule_tac x="[Key nat]" in exI, simp)
apply (rename_tac X, rule_tac x="[Hash X]" in exI, simp)
apply (clarify, rule_tac x="l@la" in exI, simp)
by (clarify, rename_tac nat X y, rule_tac x="[Crypt nat X]" in exI, simp)

lemma kparts_set: "\<exists>l'. kparts (set l) = set l' \<and> cnb l' = cnb l"
apply (induct l)
apply (rule_tac x="[]" in exI, simp, clarsimp)
apply (rename_tac a b l')
apply (subgoal_tac "\<exists>l''.  kparts {a} = set l'' \<and> cnb l'' = crypt_nb a", clarify)
apply (rule_tac x="l''@l'" in exI, simp)
apply (rule kparts_insert_substI, simp)
by (rule kparts_msg_set)

subsection\<open>list corresponding to "decrypt"\<close>

definition decrypt' :: "msg list => key => msg => msg list" where
"decrypt' l K Y == Y # remove l (Crypt K Y)"

declare decrypt'_def [simp]

subsection\<open>basic facts about @{term decrypt'}\<close>

lemma decrypt_minus: "decrypt (set l) K Y <= set (decrypt' l K Y)"
by (induct l, auto)

subsection\<open>if the analyse of a finite guarded set gives n then it must also gives
one of the keys of Ks\<close>

lemma Guard_invKey_by_list [rule_format]: "\<forall>l. cnb l = p
\<longrightarrow> Guard n Ks (set l) \<longrightarrow> Nonce n \<in> analz (set l)
\<longrightarrow> (\<exists>K. K \<in> Ks \<and> Key K \<in> analz (set l))"
apply (induct p)
(* case p=0 *)
apply (clarify, drule Guard_must_decrypt, simp, clarify)
apply (drule kparts_parts, drule non_empty_crypt, simp)
(* case p>0 *)
apply (clarify, frule Guard_must_decrypt, simp, clarify)
apply (drule_tac P="\<lambda>G. Nonce n \<in> G" in analz_pparts_kparts_substD, simp)
apply (frule analz_decrypt, simp_all)
apply (subgoal_tac "\<exists>l'. kparts (set l) = set l' \<and> cnb l' = cnb l", clarsimp)
apply (drule_tac G="insert Y (set l' - {Crypt K Y})"
and H="set (decrypt' l' K Y)" in analz_sub, rule decrypt_minus)
apply (rule_tac analz_pparts_kparts_substI, simp)
apply (case_tac "K \<in> invKey`Ks")
(* K:invKey`Ks *)
apply (clarsimp, blast)
(* K ~:invKey`Ks *)
apply (subgoal_tac "Guard n Ks (set (decrypt' l' K Y))")
apply (drule_tac x="decrypt' l' K Y" in spec, simp)
apply (subgoal_tac "Crypt K Y \<in> parts (set l)")
apply (drule parts_cnb, rotate_tac -1, simp)
apply (clarify, drule_tac X="Key Ka" and H="insert Y (set l')" in analz_sub)
apply (rule insert_mono, rule set_remove)
apply (simp add: analz_insertD, blast)
(* Crypt K Y:parts (set l) *)
apply (blast dest: kparts_parts)
(* Guard n Ks (set (decrypt' l' K Y)) *)
apply (rule_tac H="insert Y (set l')" in Guard_mono)
apply (subgoal_tac "Guard n Ks (set l')", simp)
apply (rule_tac K=K in guard_Crypt, simp add: Guard_def, simp)
apply (drule_tac t="set l'" in sym, simp)
apply (rule Guard_kparts, simp, simp)
apply (rule_tac B="set l'" in subset_trans, rule set_remove, blast)
by (rule kparts_set)

lemma Guard_invKey_finite: "[| Nonce n \<in> analz G; Guard n Ks G; finite G |]
==> \<exists>K. K \<in> Ks \<and> Key K \<in> analz G"
apply (drule finite_list, clarify)
by (rule Guard_invKey_by_list, auto)

lemma Guard_invKey: "[| Nonce n \<in> analz G; Guard n Ks G |]
==> \<exists>K. K \<in> Ks \<and> Key K \<in> analz G"
by (auto dest: analz_needs_only_finite Guard_invKey_finite)

subsection\<open>if the analyse of a finite guarded set and a (possibly infinite) set of keys
gives n then it must also gives Ks\<close>

lemma Guard_invKey_keyset: "[| Nonce n \<in> analz (G \<union> H); Guard n Ks G; finite G;
keyset H |] ==> \<exists>K. K \<in> Ks \<and> Key K \<in> analz (G \<union> H)"
apply (frule_tac P="\<lambda>G. Nonce n \<in> G" and G=G in analz_keyset_substD, simp_all)
apply (drule_tac G="G Un (H Int keysfor G)" in Guard_invKey_finite)
by (auto simp: Guard_def intro: analz_sub)

end
