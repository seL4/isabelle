(******************************************************************************
date: january 2002
author: Frederic Blanqui
email: blanqui@lri.fr
webpage: http://www.lri.fr/~blanqui/

University of Cambridge, Computer Laboratory
William Gates Building, JJ Thomson Avenue
Cambridge CB3 0FD, United Kingdom
******************************************************************************)

header{*Protocol-Independent Confidentiality Theorem on Nonces*}

theory Guard = Analz + Extensions:

(******************************************************************************
messages where all the occurrences of Nonce n are
in a sub-message of the form Crypt (invKey K) X with K:Ks
******************************************************************************)

consts guard :: "nat => key set => msg set"

inductive "guard n Ks"
intros
No_Nonce [intro]: "Nonce n ~:parts {X} ==> X:guard n Ks"
Guard_Nonce [intro]: "invKey K:Ks ==> Crypt K X:guard n Ks"
Crypt [intro]: "X:guard n Ks ==> Crypt K X:guard n Ks"
Pair [intro]: "[| X:guard n Ks; Y:guard n Ks |] ==> {|X,Y|}:guard n Ks"

subsection{*basic facts about @{term guard}*}

lemma Key_is_guard [iff]: "Key K:guard n Ks"
by auto

lemma Agent_is_guard [iff]: "Agent A:guard n Ks"
by auto

lemma Number_is_guard [iff]: "Number r:guard n Ks"
by auto

lemma Nonce_notin_guard: "X:guard n Ks ==> X ~= Nonce n"
by (erule guard.induct, auto)

lemma Nonce_notin_guard_iff [iff]: "Nonce n ~:guard n Ks"
by (auto dest: Nonce_notin_guard)

lemma guard_has_Crypt [rule_format]: "X:guard n Ks ==> Nonce n:parts {X}
--> (EX K Y. Crypt K Y:kparts {X} & Nonce n:parts {Y})"
by (erule guard.induct, auto)

lemma Nonce_notin_kparts_msg: "X:guard n Ks ==> Nonce n ~:kparts {X}"
by (erule guard.induct, auto)

lemma Nonce_in_kparts_imp_no_guard: "Nonce n:kparts H
==> EX X. X:H & X ~:guard n Ks"
apply (drule in_kparts, clarify)
apply (rule_tac x=X in exI, clarify)
by (auto dest: Nonce_notin_kparts_msg)

lemma guard_kparts [rule_format]: "X:guard n Ks ==>
Y:kparts {X} --> Y:guard n Ks"
by (erule guard.induct, auto)

lemma guard_Crypt: "[| Crypt K Y:guard n Ks; K ~:invKey`Ks |] ==> Y:guard n Ks"
by (ind_cases "Crypt K Y:guard n Ks", auto)

lemma guard_MPair [iff]: "({|X,Y|}:guard n Ks) = (X:guard n Ks & Y:guard n Ks)"
by (auto, (ind_cases "{|X,Y|}:guard n Ks", auto)+)

lemma guard_not_guard [rule_format]: "X:guard n Ks ==>
Crypt K Y:kparts {X} --> Nonce n:kparts {Y} --> Y ~:guard n Ks"
by (erule guard.induct, auto dest: guard_kparts)

lemma guard_extand: "[| X:guard n Ks; Ks <= Ks' |] ==> X:guard n Ks'"
by (erule guard.induct, auto)

subsection{*guarded sets*}

constdefs Guard :: "nat => key set => msg set => bool"
"Guard n Ks H == ALL X. X:H --> X:guard n Ks"

subsection{*basic facts about @{term Guard}*}

lemma Guard_empty [iff]: "Guard n Ks {}"
by (simp add: Guard_def)

lemma notin_parts_Guard [intro]: "Nonce n ~:parts G ==> Guard n Ks G"
apply (unfold Guard_def, clarify)
apply (subgoal_tac "Nonce n ~:parts {X}")
by (auto dest: parts_sub)

lemma Nonce_notin_kparts [simplified]: "Guard n Ks H ==> Nonce n ~:kparts H"
by (auto simp: Guard_def dest: in_kparts Nonce_notin_kparts_msg)

lemma Guard_must_decrypt: "[| Guard n Ks H; Nonce n:analz H |] ==>
EX K Y. Crypt K Y:kparts H & Key (invKey K):kparts H"
apply (drule_tac P="%G. Nonce n:G" in analz_pparts_kparts_substD, simp)
by (drule must_decrypt, auto dest: Nonce_notin_kparts)

lemma Guard_kparts [intro]: "Guard n Ks H ==> Guard n Ks (kparts H)"
by (auto simp: Guard_def dest: in_kparts guard_kparts)

lemma Guard_mono: "[| Guard n Ks H; G <= H |] ==> Guard n Ks G"
by (auto simp: Guard_def)

lemma Guard_insert [iff]: "Guard n Ks (insert X H)
= (Guard n Ks H & X:guard n Ks)"
by (auto simp: Guard_def)

lemma Guard_Un [iff]: "Guard n Ks (G Un H) = (Guard n Ks G & Guard n Ks H)"
by (auto simp: Guard_def)

lemma Guard_synth [intro]: "Guard n Ks G ==> Guard n Ks (synth G)"
by (auto simp: Guard_def, erule synth.induct, auto)

lemma Guard_analz [intro]: "[| Guard n Ks G; ALL K. K:Ks --> Key K ~:analz G |]
==> Guard n Ks (analz G)"
apply (auto simp: Guard_def)
apply (erule analz.induct, auto)
by (ind_cases "Crypt K Xa:guard n Ks", auto)

lemma in_Guard [dest]: "[| X:G; Guard n Ks G |] ==> X:guard n Ks"
by (auto simp: Guard_def)

lemma in_synth_Guard: "[| X:synth G; Guard n Ks G |] ==> X:guard n Ks"
by (drule Guard_synth, auto)

lemma in_analz_Guard: "[| X:analz G; Guard n Ks G;
ALL K. K:Ks --> Key K ~:analz G |] ==> X:guard n Ks"
by (drule Guard_analz, auto)

lemma Guard_keyset [simp]: "keyset G ==> Guard n Ks G"
by (auto simp: Guard_def)

lemma Guard_Un_keyset: "[| Guard n Ks G; keyset H |] ==> Guard n Ks (G Un H)"
by auto

lemma in_Guard_kparts: "[| X:G; Guard n Ks G; Y:kparts {X} |] ==> Y:guard n Ks"
by blast

lemma in_Guard_kparts_neq: "[| X:G; Guard n Ks G; Nonce n':kparts {X} |]
==> n ~= n'"
by (blast dest: in_Guard_kparts)

lemma in_Guard_kparts_Crypt: "[| X:G; Guard n Ks G; is_MPair X;
Crypt K Y:kparts {X}; Nonce n:kparts {Y} |] ==> invKey K:Ks"
apply (drule in_Guard, simp)
apply (frule guard_not_guard, simp+)
apply (drule guard_kparts, simp)
by (ind_cases "Crypt K Y:guard n Ks", auto)

lemma Guard_extand: "[| Guard n Ks G; Ks <= Ks' |] ==> Guard n Ks' G"
by (auto simp: Guard_def dest: guard_extand)

lemma guard_invKey [rule_format]: "[| X:guard n Ks; Nonce n:kparts {Y} |] ==>
Crypt K Y:kparts {X} --> invKey K:Ks"
by (erule guard.induct, auto)

lemma Crypt_guard_invKey [rule_format]: "[| Crypt K Y:guard n Ks;
Nonce n:kparts {Y} |] ==> invKey K:Ks"
by (auto dest: guard_invKey)

subsection{*set obtained by decrypting a message*}

syntax decrypt :: "msg set => key => msg => msg set"

translations "decrypt H K Y" => "insert Y (H - {Crypt K Y})"

lemma analz_decrypt: "[| Crypt K Y:H; Key (invKey K):H; Nonce n:analz H |]
==> Nonce n:analz (decrypt H K Y)"
apply (drule_tac P="%H. Nonce n:analz H" in ssubst [OF insert_Diff])
apply assumption
apply (simp only: analz_Crypt_if, simp)
done

lemma parts_decrypt: "[| Crypt K Y:H; X:parts (decrypt H K Y) |] ==> X:parts H"
by (erule parts.induct, auto intro: parts.Fst parts.Snd parts.Body)

subsection{*number of Crypt's in a message*}

consts crypt_nb :: "msg => nat"

recdef crypt_nb "measure size"
"crypt_nb (Crypt K X) = Suc (crypt_nb X)"
"crypt_nb {|X,Y|} = crypt_nb X + crypt_nb Y"
"crypt_nb X = 0" (* otherwise *)

subsection{*basic facts about @{term crypt_nb}*}

lemma non_empty_crypt_msg: "Crypt K Y:parts {X} ==> 0 < crypt_nb X"
by (induct X, simp_all, safe, simp_all)

subsection{*number of Crypt's in a message list*}

consts cnb :: "msg list => nat"

recdef cnb "measure size"
"cnb [] = 0"
"cnb (X#l) = crypt_nb X + cnb l"

subsection{*basic facts about @{term cnb}*}

lemma cnb_app [simp]: "cnb (l @ l') = cnb l + cnb l'"
by (induct l, auto)

lemma mem_cnb_minus: "x mem l ==> cnb l = crypt_nb x + (cnb l - crypt_nb x)"
by (induct l, auto)

lemmas mem_cnb_minus_substI = mem_cnb_minus [THEN ssubst]

lemma cnb_minus [simp]: "x mem l ==> cnb (minus l x) = cnb l - crypt_nb x"
apply (induct l, auto)
by (erule_tac l1=list and x1=x in mem_cnb_minus_substI, simp)

lemma parts_cnb: "Z:parts (set l) ==>
cnb l = (cnb l - crypt_nb Z) + crypt_nb Z"
by (erule parts.induct, auto simp: in_set_conv_decomp)

lemma non_empty_crypt: "Crypt K Y:parts (set l) ==> 0 < cnb l"
by (induct l, auto dest: non_empty_crypt_msg parts_insert_substD)

subsection{*list of kparts*}

lemma kparts_msg_set: "EX l. kparts {X} = set l & cnb l = crypt_nb X"
apply (induct X, simp_all)
apply (rule_tac x="[Agent agent]" in exI, simp)
apply (rule_tac x="[Number nat]" in exI, simp)
apply (rule_tac x="[Nonce nat]" in exI, simp)
apply (rule_tac x="[Key nat]" in exI, simp)
apply (rule_tac x="[Hash msg]" in exI, simp)
apply (clarify, rule_tac x="l@la" in exI, simp)
by (clarify, rule_tac x="[Crypt nat msg]" in exI, simp)

lemma kparts_set: "EX l'. kparts (set l) = set l' & cnb l' = cnb l"
apply (induct l)
apply (rule_tac x="[]" in exI, simp, clarsimp)
apply (subgoal_tac "EX l.  kparts {a} = set l & cnb l = crypt_nb a", clarify)
apply (rule_tac x="l@l'" in exI, simp)
apply (rule kparts_insert_substI, simp)
by (rule kparts_msg_set)

subsection{*list corresponding to "decrypt"*}

constdefs decrypt' :: "msg list => key => msg => msg list"
"decrypt' l K Y == Y # minus l (Crypt K Y)"

declare decrypt'_def [simp]

subsection{*basic facts about @{term decrypt'}*}

lemma decrypt_minus: "decrypt (set l) K Y <= set (decrypt' l K Y)"
by (induct l, auto)

subsection{*if the analyse of a finite guarded set gives n then it must also gives
one of the keys of Ks*}

lemma Guard_invKey_by_list [rule_format]: "ALL l. cnb l = p
--> Guard n Ks (set l) --> Nonce n:analz (set l)
--> (EX K. K:Ks & Key K:analz (set l))"
apply (induct p)
(* case p=0 *)
apply (clarify, drule Guard_must_decrypt, simp, clarify)
apply (drule kparts_parts, drule non_empty_crypt, simp)
(* case p>0 *)
apply (clarify, frule Guard_must_decrypt, simp, clarify)
apply (drule_tac P="%G. Nonce n:G" in analz_pparts_kparts_substD, simp)
apply (frule analz_decrypt, simp_all)
apply (subgoal_tac "EX l'. kparts (set l) = set l' & cnb l' = cnb l", clarsimp)
apply (drule_tac G="insert Y (set l' - {Crypt K Y})"
and H="set (decrypt' l' K Y)" in analz_sub, rule decrypt_minus)
apply (rule_tac analz_pparts_kparts_substI, simp)
apply (case_tac "K:invKey`Ks")
(* K:invKey`Ks *)
apply (clarsimp, blast)
(* K ~:invKey`Ks *)
apply (subgoal_tac "Guard n Ks (set (decrypt' l' K Y))")
apply (drule_tac x="decrypt' l' K Y" in spec, simp add: set_mem_eq)
apply (subgoal_tac "Crypt K Y:parts (set l)")
apply (drule parts_cnb, rotate_tac -1, simp)
apply (clarify, drule_tac X="Key Ka" and H="insert Y (set l')" in analz_sub)
apply (rule insert_mono, rule set_minus)
apply (simp add: analz_insertD, blast)
(* Crypt K Y:parts (set l) *)
apply (blast dest: kparts_parts)
(* Guard n Ks (set (decrypt' l' K Y)) *)
apply (rule_tac H="insert Y (set l')" in Guard_mono)
apply (subgoal_tac "Guard n Ks (set l')", simp)
apply (rule_tac K=K in guard_Crypt, simp add: Guard_def, simp)
apply (drule_tac t="set l'" in sym, simp)
apply (rule Guard_kparts, simp, simp)
apply (rule_tac B="set l'" in subset_trans, rule set_minus, blast)
by (rule kparts_set)

lemma Guard_invKey_finite: "[| Nonce n:analz G; Guard n Ks G; finite G |]
==> EX K. K:Ks & Key K:analz G"
apply (drule finite_list, clarify)
by (rule Guard_invKey_by_list, auto)

lemma Guard_invKey: "[| Nonce n:analz G; Guard n Ks G |]
==> EX K. K:Ks & Key K:analz G"
by (auto dest: analz_needs_only_finite Guard_invKey_finite)

subsection{*if the analyse of a finite guarded set and a (possibly infinite) set of keys
gives n then it must also gives Ks*}

lemma Guard_invKey_keyset: "[| Nonce n:analz (G Un H); Guard n Ks G; finite G;
keyset H |] ==> EX K. K:Ks & Key K:analz (G Un H)"
apply (frule_tac P="%G. Nonce n:G" and G2=G in analz_keyset_substD, simp_all)
apply (drule_tac G="G Un (H Int keysfor G)" in Guard_invKey_finite)
by (auto simp: Guard_def intro: analz_sub)

end