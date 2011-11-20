(*  Title:      HOL/Auth/Guard/GuardK.thy
    Author:     Frederic Blanqui, University of Cambridge Computer Laboratory
    Copyright   2002  University of Cambridge

Very similar to Guard except:
- Guard is replaced by GuardK, guard by guardK, Nonce by Key
- some scripts are slightly modified (+ keyset_in, kparts_parts)
- the hypothesis Key n ~:G (keyset G) is added
*)

header{*protocol-independent confidentiality theorem on keys*}

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
  No_Key [intro]: "Key n ~:parts {X} ==> X:guardK n Ks"
| Guard_Key [intro]: "invKey K:Ks ==> Crypt K X:guardK n Ks"
| Crypt [intro]: "X:guardK n Ks ==> Crypt K X:guardK n Ks"
| Pair [intro]: "[| X:guardK n Ks; Y:guardK n Ks |] ==> {|X,Y|}:guardK n Ks"

subsection{*basic facts about @{term guardK}*}

lemma Nonce_is_guardK [iff]: "Nonce p:guardK n Ks"
by auto

lemma Agent_is_guardK [iff]: "Agent A:guardK n Ks"
by auto

lemma Number_is_guardK [iff]: "Number r:guardK n Ks"
by auto

lemma Key_notin_guardK: "X:guardK n Ks ==> X ~= Key n"
by (erule guardK.induct, auto)

lemma Key_notin_guardK_iff [iff]: "Key n ~:guardK n Ks"
by (auto dest: Key_notin_guardK)

lemma guardK_has_Crypt [rule_format]: "X:guardK n Ks ==> Key n:parts {X}
--> (EX K Y. Crypt K Y:kparts {X} & Key n:parts {Y})"
by (erule guardK.induct, auto)

lemma Key_notin_kparts_msg: "X:guardK n Ks ==> Key n ~:kparts {X}"
by (erule guardK.induct, auto dest: kparts_parts)

lemma Key_in_kparts_imp_no_guardK: "Key n:kparts H
==> EX X. X:H & X ~:guardK n Ks"
apply (drule in_kparts, clarify)
apply (rule_tac x=X in exI, clarify)
by (auto dest: Key_notin_kparts_msg)

lemma guardK_kparts [rule_format]: "X:guardK n Ks ==>
Y:kparts {X} --> Y:guardK n Ks"
by (erule guardK.induct, auto dest: kparts_parts parts_sub)

lemma guardK_Crypt: "[| Crypt K Y:guardK n Ks; K ~:invKey`Ks |] ==> Y:guardK n Ks"
by (ind_cases "Crypt K Y:guardK n Ks", auto)

lemma guardK_MPair [iff]: "({|X,Y|}:guardK n Ks)
= (X:guardK n Ks & Y:guardK n Ks)"
by (auto, (ind_cases "{|X,Y|}:guardK n Ks", auto)+)

lemma guardK_not_guardK [rule_format]: "X:guardK n Ks ==>
Crypt K Y:kparts {X} --> Key n:kparts {Y} --> Y ~:guardK n Ks"
by (erule guardK.induct, auto dest: guardK_kparts)

lemma guardK_extand: "[| X:guardK n Ks; Ks <= Ks';
[| K:Ks'; K ~:Ks |] ==> Key K ~:parts {X} |] ==> X:guardK n Ks'"
by (erule guardK.induct, auto)

subsection{*guarded sets*}

definition GuardK :: "nat => key set => msg set => bool" where
"GuardK n Ks H == ALL X. X:H --> X:guardK n Ks"

subsection{*basic facts about @{term GuardK}*}

lemma GuardK_empty [iff]: "GuardK n Ks {}"
by (simp add: GuardK_def)

lemma Key_notin_kparts [simplified]: "GuardK n Ks H ==> Key n ~:kparts H"
by (auto simp: GuardK_def dest: in_kparts Key_notin_kparts_msg)

lemma GuardK_must_decrypt: "[| GuardK n Ks H; Key n:analz H |] ==>
EX K Y. Crypt K Y:kparts H & Key (invKey K):kparts H"
apply (drule_tac P="%G. Key n:G" in analz_pparts_kparts_substD, simp)
by (drule must_decrypt, auto dest: Key_notin_kparts)

lemma GuardK_kparts [intro]: "GuardK n Ks H ==> GuardK n Ks (kparts H)"
by (auto simp: GuardK_def dest: in_kparts guardK_kparts)

lemma GuardK_mono: "[| GuardK n Ks H; G <= H |] ==> GuardK n Ks G"
by (auto simp: GuardK_def)

lemma GuardK_insert [iff]: "GuardK n Ks (insert X H)
= (GuardK n Ks H & X:guardK n Ks)"
by (auto simp: GuardK_def)

lemma GuardK_Un [iff]: "GuardK n Ks (G Un H) = (GuardK n Ks G & GuardK n Ks H)"
by (auto simp: GuardK_def)

lemma GuardK_synth [intro]: "GuardK n Ks G ==> GuardK n Ks (synth G)"
by (auto simp: GuardK_def, erule synth.induct, auto)

lemma GuardK_analz [intro]: "[| GuardK n Ks G; ALL K. K:Ks --> Key K ~:analz G |]
==> GuardK n Ks (analz G)"
apply (auto simp: GuardK_def)
apply (erule analz.induct, auto)
by (ind_cases "Crypt K Xa:guardK n Ks" for K Xa, auto)

lemma in_GuardK [dest]: "[| X:G; GuardK n Ks G |] ==> X:guardK n Ks"
by (auto simp: GuardK_def)

lemma in_synth_GuardK: "[| X:synth G; GuardK n Ks G |] ==> X:guardK n Ks"
by (drule GuardK_synth, auto)

lemma in_analz_GuardK: "[| X:analz G; GuardK n Ks G;
ALL K. K:Ks --> Key K ~:analz G |] ==> X:guardK n Ks"
by (drule GuardK_analz, auto)

lemma GuardK_keyset [simp]: "[| keyset G; Key n ~:G |] ==> GuardK n Ks G"
by (simp only: GuardK_def, clarify, drule keyset_in, auto)

lemma GuardK_Un_keyset: "[| GuardK n Ks G; keyset H; Key n ~:H |]
==> GuardK n Ks (G Un H)"
by auto

lemma in_GuardK_kparts: "[| X:G; GuardK n Ks G; Y:kparts {X} |] ==> Y:guardK n Ks"
by blast

lemma in_GuardK_kparts_neq: "[| X:G; GuardK n Ks G; Key n':kparts {X} |]
==> n ~= n'"
by (blast dest: in_GuardK_kparts)

lemma in_GuardK_kparts_Crypt: "[| X:G; GuardK n Ks G; is_MPair X;
Crypt K Y:kparts {X}; Key n:kparts {Y} |] ==> invKey K:Ks"
apply (drule in_GuardK, simp)
apply (frule guardK_not_guardK, simp+)
apply (drule guardK_kparts, simp)
by (ind_cases "Crypt K Y:guardK n Ks", auto)

lemma GuardK_extand: "[| GuardK n Ks G; Ks <= Ks';
[| K:Ks'; K ~:Ks |] ==> Key K ~:parts G |] ==> GuardK n Ks' G"
by (auto simp: GuardK_def dest: guardK_extand parts_sub)

subsection{*set obtained by decrypting a message*}

abbreviation (input)
  decrypt :: "msg set => key => msg => msg set" where
  "decrypt H K Y == insert Y (H - {Crypt K Y})"

lemma analz_decrypt: "[| Crypt K Y:H; Key (invKey K):H; Key n:analz H |]
==> Key n:analz (decrypt H K Y)"
apply (drule_tac P="%H. Key n:analz H" in ssubst [OF insert_Diff])
apply assumption 
apply (simp only: analz_Crypt_if, simp)
done

lemma parts_decrypt: "[| Crypt K Y:H; X:parts (decrypt H K Y) |] ==> X:parts H"
by (erule parts.induct, auto intro: parts.Fst parts.Snd parts.Body)

subsection{*number of Crypt's in a message*}

fun crypt_nb :: "msg => nat" where
"crypt_nb (Crypt K X) = Suc (crypt_nb X)" |
"crypt_nb {|X,Y|} = crypt_nb X + crypt_nb Y" |
"crypt_nb X = 0" (* otherwise *)

subsection{*basic facts about @{term crypt_nb}*}

lemma non_empty_crypt_msg: "Crypt K Y:parts {X} ==> crypt_nb X \<noteq> 0"
by (induct X, simp_all, safe, simp_all)

subsection{*number of Crypt's in a message list*}

primrec cnb :: "msg list => nat" where
"cnb [] = 0" |
"cnb (X#l) = crypt_nb X + cnb l"

subsection{*basic facts about @{term cnb}*}

lemma cnb_app [simp]: "cnb (l @ l') = cnb l + cnb l'"
by (induct l, auto)

lemma mem_cnb_minus: "x \<in> set l ==> cnb l = crypt_nb x + (cnb l - crypt_nb x)"
by (induct l, auto)

lemmas mem_cnb_minus_substI = mem_cnb_minus [THEN ssubst]

lemma cnb_minus [simp]: "x \<in> set l ==> cnb (remove l x) = cnb l - crypt_nb x"
apply (induct l, auto)
by (erule_tac l=l and x=x in mem_cnb_minus_substI, simp)

lemma parts_cnb: "Z:parts (set l) ==>
cnb l = (cnb l - crypt_nb Z) + crypt_nb Z"
by (erule parts.induct, auto simp: in_set_conv_decomp)

lemma non_empty_crypt: "Crypt K Y:parts (set l) ==> cnb l \<noteq> 0"
by (induct l, auto dest: non_empty_crypt_msg parts_insert_substD)

subsection{*list of kparts*}

lemma kparts_msg_set: "EX l. kparts {X} = set l & cnb l = crypt_nb X"
apply (induct X, simp_all)
apply (rule_tac x="[Agent agent]" in exI, simp)
apply (rule_tac x="[Number nat]" in exI, simp)
apply (rule_tac x="[Nonce nat]" in exI, simp)
apply (rule_tac x="[Key nat]" in exI, simp)
apply (rule_tac x="[Hash X]" in exI, simp)
apply (clarify, rule_tac x="l@la" in exI, simp)
by (clarify, rule_tac x="[Crypt nat X]" in exI, simp)

lemma kparts_set: "EX l'. kparts (set l) = set l' & cnb l' = cnb l"
apply (induct l)
apply (rule_tac x="[]" in exI, simp, clarsimp)
apply (subgoal_tac "EX l''.  kparts {a} = set l'' & cnb l'' = crypt_nb a", clarify)
apply (rule_tac x="l''@l'" in exI, simp)
apply (rule kparts_insert_substI, simp)
by (rule kparts_msg_set)

subsection{*list corresponding to "decrypt"*}

definition decrypt' :: "msg list => key => msg => msg list" where
"decrypt' l K Y == Y # remove l (Crypt K Y)"

declare decrypt'_def [simp]

subsection{*basic facts about @{term decrypt'}*}

lemma decrypt_minus: "decrypt (set l) K Y <= set (decrypt' l K Y)"
by (induct l, auto)

text{*if the analysis of a finite guarded set gives n then it must also give
one of the keys of Ks*}

lemma GuardK_invKey_by_list [rule_format]: "ALL l. cnb l = p
--> GuardK n Ks (set l) --> Key n:analz (set l)
--> (EX K. K:Ks & Key K:analz (set l))"
apply (induct p)
(* case p=0 *)
apply (clarify, drule GuardK_must_decrypt, simp, clarify)
apply (drule kparts_parts, drule non_empty_crypt, simp)
(* case p>0 *)
apply (clarify, frule GuardK_must_decrypt, simp, clarify)
apply (drule_tac P="%G. Key n:G" in analz_pparts_kparts_substD, simp)
apply (frule analz_decrypt, simp_all)
apply (subgoal_tac "EX l'. kparts (set l) = set l' & cnb l' = cnb l", clarsimp)
apply (drule_tac G="insert Y (set l' - {Crypt K Y})"
and H="set (decrypt' l' K Y)" in analz_sub, rule decrypt_minus)
apply (rule_tac analz_pparts_kparts_substI, simp)
apply (case_tac "K:invKey`Ks")
(* K:invKey`Ks *)
apply (clarsimp, blast)
(* K ~:invKey`Ks *)
apply (subgoal_tac "GuardK n Ks (set (decrypt' l' K Y))")
apply (drule_tac x="decrypt' l' K Y" in spec, simp)
apply (subgoal_tac "Crypt K Y:parts (set l)")
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

lemma GuardK_invKey_finite: "[| Key n:analz G; GuardK n Ks G; finite G |]
==> EX K. K:Ks & Key K:analz G"
apply (drule finite_list, clarify)
by (rule GuardK_invKey_by_list, auto)

lemma GuardK_invKey: "[| Key n:analz G; GuardK n Ks G |]
==> EX K. K:Ks & Key K:analz G"
by (auto dest: analz_needs_only_finite GuardK_invKey_finite)

text{*if the analyse of a finite guarded set and a (possibly infinite) set of
keys gives n then it must also gives Ks*}

lemma GuardK_invKey_keyset: "[| Key n:analz (G Un H); GuardK n Ks G; finite G;
keyset H; Key n ~:H |] ==> EX K. K:Ks & Key K:analz (G Un H)"
apply (frule_tac P="%G. Key n:G" and G=G in analz_keyset_substD, simp_all)
apply (drule_tac G="G Un (H Int keysfor G)" in GuardK_invKey_finite)
apply (auto simp: GuardK_def intro: analz_sub)
by (drule keyset_in, auto)

end