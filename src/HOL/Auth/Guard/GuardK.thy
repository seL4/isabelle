(*  Title:      HOL/Auth/Guard/GuardK.thy
    Author:     Frederic Blanqui, University of Cambridge Computer Laboratory
    Copyright   2002  University of Cambridge

Very similar to Guard except:
- Guard is replaced by GuardK, guard by guardK, Nonce by Key
- some scripts are slightly modified (+ keyset_in, kparts_parts)
- the hypothesis Key n ~:G (keyset G) is added
*)

section\<open>protocol-independent confidentiality theorem on keys\<close>

theory GuardK
imports Analz Extensions
begin

(******************************************************************************
messages where all the occurrences of Key n are
in a sub-message of the form Crypt (invKey K) X with K:Ks
******************************************************************************)

inductive_set
  guardK :: "nat => key set => msg set"
  for n :: nat and Ks :: "key set"
where
  No_Key [intro]: "Key n \<notin> parts {X} \<Longrightarrow> X \<in> guardK n Ks"
| Guard_Key [intro]: "invKey K \<in> Ks ==> Crypt K X \<in> guardK n Ks"
| Crypt [intro]: "X \<in> guardK n Ks \<Longrightarrow> Crypt K X \<in> guardK n Ks"
| Pair [intro]: "[| X \<in> guardK n Ks; Y \<in> guardK n Ks |] ==> \<lbrace>X,Y\<rbrace> \<in> guardK n Ks"

subsection\<open>basic facts about @{term guardK}\<close>

lemma Nonce_is_guardK [iff]: "Nonce p \<in> guardK n Ks"
by auto

lemma Agent_is_guardK [iff]: "Agent A \<in> guardK n Ks"
by auto

lemma Number_is_guardK [iff]: "Number r \<in> guardK n Ks"
by auto

lemma Key_notin_guardK: "X \<in> guardK n Ks \<Longrightarrow> X \<noteq> Key n"
by (erule guardK.induct, auto)

lemma Key_notin_guardK_iff [iff]: "Key n \<notin> guardK n Ks"
by (auto dest: Key_notin_guardK)

lemma guardK_has_Crypt [rule_format]: "X \<in> guardK n Ks \<Longrightarrow> Key n \<in> parts {X}
\<longrightarrow> (\<exists>K Y. Crypt K Y \<in> kparts {X} \<and> Key n \<in> parts {Y})"
by (erule guardK.induct, auto)

lemma Key_notin_kparts_msg: "X \<in> guardK n Ks \<Longrightarrow> Key n \<notin> kparts {X}"
by (erule guardK.induct, auto dest: kparts_parts)

lemma Key_in_kparts_imp_no_guardK: "Key n \<in> kparts H
\<Longrightarrow> \<exists>X. X \<in> H \<and> X \<notin> guardK n Ks"
apply (drule in_kparts, clarify)
apply (rule_tac x=X in exI, clarify)
by (auto dest: Key_notin_kparts_msg)

lemma guardK_kparts [rule_format]: "X \<in> guardK n Ks \<Longrightarrow>
Y \<in> kparts {X} \<longrightarrow> Y \<in> guardK n Ks"
by (erule guardK.induct, auto dest: kparts_parts parts_sub)

lemma guardK_Crypt: "[| Crypt K Y \<in> guardK n Ks; K \<notin> invKey`Ks |] ==> Y \<in> guardK n Ks"
  by (ind_cases "Crypt K Y \<in> guardK n Ks") (auto intro!: image_eqI)

lemma guardK_MPair [iff]: "(\<lbrace>X,Y\<rbrace> \<in> guardK n Ks)
= (X \<in> guardK n Ks \<and> Y \<in> guardK n Ks)"
by (auto, (ind_cases "\<lbrace>X,Y\<rbrace> \<in> guardK n Ks", auto)+)

lemma guardK_not_guardK [rule_format]: "X \<in>guardK n Ks \<Longrightarrow>
Crypt K Y \<in> kparts {X} \<longrightarrow> Key n \<in> kparts {Y} \<longrightarrow> Y \<notin> guardK n Ks"
by (erule guardK.induct, auto dest: guardK_kparts)

lemma guardK_extand: "[| X \<in> guardK n Ks; Ks \<subseteq> Ks';
[| K \<in> Ks'; K \<notin> Ks |] ==> Key K \<notin> parts {X} |] ==> X \<in> guardK n Ks'"
by (erule guardK.induct, auto)

subsection\<open>guarded sets\<close>

definition GuardK :: "nat \<Rightarrow> key set \<Rightarrow> msg set \<Rightarrow> bool" where
"GuardK n Ks H \<equiv> \<forall>X. X \<in> H \<longrightarrow> X \<in> guardK n Ks"

subsection\<open>basic facts about @{term GuardK}\<close>

lemma GuardK_empty [iff]: "GuardK n Ks {}"
by (simp add: GuardK_def)

lemma Key_notin_kparts [simplified]: "GuardK n Ks H \<Longrightarrow> Key n \<notin> kparts H"
by (auto simp: GuardK_def dest: in_kparts Key_notin_kparts_msg)

lemma GuardK_must_decrypt: "[| GuardK n Ks H; Key n \<in> analz H |] ==>
\<exists>K Y. Crypt K Y \<in> kparts H \<and> Key (invKey K) \<in> kparts H"
apply (drule_tac P="\<lambda>G. Key n \<in> G" in analz_pparts_kparts_substD, simp)
by (drule must_decrypt, auto dest: Key_notin_kparts)

lemma GuardK_kparts [intro]: "GuardK n Ks H \<Longrightarrow> GuardK n Ks (kparts H)"
by (auto simp: GuardK_def dest: in_kparts guardK_kparts)

lemma GuardK_mono: "[| GuardK n Ks H; G \<subseteq> H |] ==> GuardK n Ks G"
by (auto simp: GuardK_def)

lemma GuardK_insert [iff]: "GuardK n Ks (insert X H)
= (GuardK n Ks H \<and> X \<in> guardK n Ks)"
by (auto simp: GuardK_def)

lemma GuardK_Un [iff]: "GuardK n Ks (G Un H) = (GuardK n Ks G & GuardK n Ks H)"
by (auto simp: GuardK_def)

lemma GuardK_synth [intro]: "GuardK n Ks G \<Longrightarrow> GuardK n Ks (synth G)"
by (auto simp: GuardK_def, erule synth.induct, auto)

lemma GuardK_analz [intro]: "[| GuardK n Ks G; \<forall>K. K \<in> Ks \<longrightarrow> Key K \<notin> analz G |]
==> GuardK n Ks (analz G)"
apply (auto simp: GuardK_def)
apply (erule analz.induct, auto)
by (ind_cases "Crypt K Xa \<in> guardK n Ks" for K Xa, auto)

lemma in_GuardK [dest]: "[| X \<in> G; GuardK n Ks G |] ==> X \<in> guardK n Ks"
by (auto simp: GuardK_def)

lemma in_synth_GuardK: "[| X \<in> synth G; GuardK n Ks G |] ==> X \<in> guardK n Ks"
by (drule GuardK_synth, auto)

lemma in_analz_GuardK: "[| X \<in> analz G; GuardK n Ks G;
\<forall>K. K \<in> Ks \<longrightarrow> Key K \<notin> analz G |] ==> X \<in> guardK n Ks"
by (drule GuardK_analz, auto)

lemma GuardK_keyset [simp]: "[| keyset G; Key n \<notin> G |] ==> GuardK n Ks G"
by (simp only: GuardK_def, clarify, drule keyset_in, auto)

lemma GuardK_Un_keyset: "[| GuardK n Ks G; keyset H; Key n \<notin> H |]
==> GuardK n Ks (G Un H)"
by auto

lemma in_GuardK_kparts: "[| X \<in> G; GuardK n Ks G; Y \<in> kparts {X} |] ==> Y \<in> guardK n Ks"
by blast

lemma in_GuardK_kparts_neq: "[| X \<in> G; GuardK n Ks G; Key n' \<in> kparts {X} |]
==> n \<noteq> n'"
by (blast dest: in_GuardK_kparts)

lemma in_GuardK_kparts_Crypt: "[| X \<in> G; GuardK n Ks G; is_MPair X;
Crypt K Y \<in> kparts {X}; Key n \<in> kparts {Y} |] ==> invKey K \<in> Ks"
apply (drule in_GuardK, simp)
apply (frule guardK_not_guardK, simp+)
apply (drule guardK_kparts, simp)
by (ind_cases "Crypt K Y \<in> guardK n Ks", auto)

lemma GuardK_extand: "[| GuardK n Ks G; Ks \<subseteq> Ks';
[| K \<in> Ks'; K \<notin> Ks |] ==> Key K \<notin> parts G |] ==> GuardK n Ks' G"
by (auto simp: GuardK_def dest: guardK_extand parts_sub)

subsection\<open>set obtained by decrypting a message\<close>

abbreviation (input)
  decrypt :: "msg set \<Rightarrow> key \<Rightarrow> msg \<Rightarrow> msg set" where
  "decrypt H K Y \<equiv> insert Y (H - {Crypt K Y})"

lemma analz_decrypt: "[| Crypt K Y \<in> H; Key (invKey K) \<in> H; Key n \<in> analz H |]
==> Key n \<in> analz (decrypt H K Y)"
apply (drule_tac P="\<lambda>H. Key n \<in> analz H" in ssubst [OF insert_Diff])
apply assumption 
apply (simp only: analz_Crypt_if, simp)
done

lemma parts_decrypt: "[| Crypt K Y \<in> H; X \<in> parts (decrypt H K Y) |] ==> X \<in> parts H"
by (erule parts.induct, auto intro: parts.Fst parts.Snd parts.Body)

subsection\<open>number of Crypt's in a message\<close>

fun crypt_nb :: "msg => nat" where
"crypt_nb (Crypt K X) = Suc (crypt_nb X)" |
"crypt_nb \<lbrace>X,Y\<rbrace> = crypt_nb X + crypt_nb Y" |
"crypt_nb X = 0" (* otherwise *)

subsection\<open>basic facts about @{term crypt_nb}\<close>

lemma non_empty_crypt_msg: "Crypt K Y \<in> parts {X} \<Longrightarrow> crypt_nb X \<noteq> 0"
by (induct X, simp_all, safe, simp_all)

subsection\<open>number of Crypt's in a message list\<close>

primrec cnb :: "msg list => nat" where
"cnb [] = 0" |
"cnb (X#l) = crypt_nb X + cnb l"

subsection\<open>basic facts about @{term cnb}\<close>

lemma cnb_app [simp]: "cnb (l @ l') = cnb l + cnb l'"
by (induct l, auto)

lemma mem_cnb_minus: "x \<in> set l ==> cnb l = crypt_nb x + (cnb l - crypt_nb x)"
by (induct l, auto)

lemmas mem_cnb_minus_substI = mem_cnb_minus [THEN ssubst]

lemma cnb_minus [simp]: "x \<in> set l ==> cnb (remove l x) = cnb l - crypt_nb x"
apply (induct l, auto)
by (erule_tac l=l and x=x in mem_cnb_minus_substI, simp)

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
apply (rule_tac x="[Hash X]" in exI, simp)
apply (clarify, rule_tac x="l@la" in exI, simp)
by (clarify, rename_tac nat X y, rule_tac x="[Crypt nat X]" in exI, simp)

lemma kparts_set: "\<exists>l'. kparts (set l) = set l' & cnb l' = cnb l"
apply (induct l)
apply (rule_tac x="[]" in exI, simp, clarsimp)
apply (rename_tac a b l')
apply (subgoal_tac "\<exists>l''.  kparts {a} = set l'' & cnb l'' = crypt_nb a", clarify)
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

text\<open>if the analysis of a finite guarded set gives n then it must also give
one of the keys of Ks\<close>

lemma GuardK_invKey_by_list [rule_format]: "\<forall>l. cnb l = p
\<longrightarrow> GuardK n Ks (set l) \<longrightarrow> Key n \<in> analz (set l)
\<longrightarrow> (\<exists>K. K \<in> Ks \<and> Key K \<in> analz (set l))"
apply (induct p)
(* case p=0 *)
apply (clarify, drule GuardK_must_decrypt, simp, clarify)
apply (drule kparts_parts, drule non_empty_crypt, simp)
(* case p>0 *)
apply (clarify, frule GuardK_must_decrypt, simp, clarify)
apply (drule_tac P="\<lambda>G. Key n \<in> G" in analz_pparts_kparts_substD, simp)
apply (frule analz_decrypt, simp_all)
apply (subgoal_tac "\<exists>l'. kparts (set l) = set l' \<and> cnb l' = cnb l", clarsimp)
apply (drule_tac G="insert Y (set l' - {Crypt K Y})"
and H="set (decrypt' l' K Y)" in analz_sub, rule decrypt_minus)
apply (rule_tac analz_pparts_kparts_substI, simp)
apply (case_tac "K \<in> invKey`Ks")
(* K:invKey`Ks *)
apply (clarsimp, blast)
(* K ~:invKey`Ks *)
apply (subgoal_tac "GuardK n Ks (set (decrypt' l' K Y))")
apply (drule_tac x="decrypt' l' K Y" in spec, simp)
apply (subgoal_tac "Crypt K Y \<in> parts (set l)")
apply (drule parts_cnb, rotate_tac -1, simp)
apply (clarify, drule_tac X="Key Ka" and H="insert Y (set l')" in analz_sub)
apply (rule insert_mono, rule set_remove)
apply (simp add: analz_insertD, blast)
(* Crypt K Y:parts (set l) *)
apply (blast dest: kparts_parts)
(* GuardK n Ks (set (decrypt' l' K Y)) *)
apply (rule_tac H="insert Y (set l')" in GuardK_mono)
apply (subgoal_tac "GuardK n Ks (set l')", simp)
apply (rule_tac K=K in guardK_Crypt, simp add: GuardK_def, simp)
apply (drule_tac t="set l'" in sym, simp)
apply (rule GuardK_kparts, simp, simp)
apply (rule_tac B="set l'" in subset_trans, rule set_remove, blast)
by (rule kparts_set)

lemma GuardK_invKey_finite: "[| Key n \<in> analz G; GuardK n Ks G; finite G |]
==> \<exists>K. K \<in> Ks \<and> Key K \<in> analz G"
apply (drule finite_list, clarify)
by (rule GuardK_invKey_by_list, auto)

lemma GuardK_invKey: "[| Key n \<in> analz G; GuardK n Ks G |]
==> \<exists>K. K \<in> Ks \<and> Key K \<in> analz G"
by (auto dest: analz_needs_only_finite GuardK_invKey_finite)

text\<open>if the analyse of a finite guarded set and a (possibly infinite) set of
keys gives n then it must also gives Ks\<close>

lemma GuardK_invKey_keyset: "[| Key n \<in> analz (G \<union> H); GuardK n Ks G; finite G;
keyset H; Key n \<notin> H |] ==> \<exists>K. K \<in> Ks \<and> Key K \<in> analz (G \<union> H)"
apply (frule_tac P="\<lambda>G. Key n \<in> G" and G=G in analz_keyset_substD, simp_all)
apply (drule_tac G="G Un (H Int keysfor G)" in GuardK_invKey_finite)
apply (auto simp: GuardK_def intro: analz_sub)
by (drule keyset_in, auto)

end
