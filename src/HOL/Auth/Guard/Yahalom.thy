(******************************************************************************
date: march 2002
author: Frederic Blanqui
email: blanqui@lri.fr
webpage: http://www.lri.fr/~blanqui/

University of Cambridge, Computer Laboratory
William Gates Building, JJ Thomson Avenue
Cambridge CB3 0FD, United Kingdom
******************************************************************************)

header{*Yahalom Protocol*}

theory Yahalom = Guard_Shared:

subsection{*messages used in the protocol*}

syntax ya1 :: "agent => agent => nat => event"

translations "ya1 A B NA" => "Says A B {|Agent A, Nonce NA|}"

syntax ya1' :: "agent => agent => agent => nat => event"

translations "ya1' A' A B NA" => "Says A' B {|Agent A, Nonce NA|}"

syntax ya2 :: "agent => agent => nat => nat => event"

translations "ya2 A B NA NB"
=> "Says B Server {|Agent B, Ciph B {|Agent A, Nonce NA, Nonce NB|}|}"

syntax ya2' :: "agent => agent => agent => nat => nat => event"

translations "ya2' B' A B NA NB"
=> "Says B' Server {|Agent B, Ciph B {|Agent A, Nonce NA, Nonce NB|}|}"

syntax ya3 :: "agent => agent => nat => nat => key => event"

translations "ya3 A B NA NB K"
=> "Says Server A {|Ciph A {|Agent B, Key K, Nonce NA, Nonce NB|},
                    Ciph B {|Agent A, Key K|}|}"

syntax ya3':: "agent => msg => agent => agent => nat => nat => key => event"

translations "ya3' S Y A B NA NB K"
=> "Says S A {|Ciph A {|Agent B, Key K, Nonce NA, Nonce NB|}, Y|}"

syntax ya4 :: "agent => agent => nat => nat => msg => event"

translations "ya4 A B K NB Y" => "Says A B {|Y, Crypt K (Nonce NB)|}"

syntax ya4' :: "agent => agent => nat => nat => msg => event"

translations "ya4' A' B K NB Y" => "Says A' B {|Y, Crypt K (Nonce NB)|}"

subsection{*definition of the protocol*}

consts ya :: "event list set"

inductive ya
intros

Nil: "[]:ya"

Fake: "[| evs:ya; X:synth (analz (spies evs)) |] ==> Says Spy B X # evs:ya"

YA1: "[| evs1:ya; Nonce NA ~:used evs1 |] ==> ya1 A B NA # evs1:ya"

YA2: "[| evs2:ya; ya1' A' A B NA:set evs2; Nonce NB ~:used evs2 |]
==> ya2 A B NA NB # evs2:ya"

YA3: "[| evs3:ya; ya2' B' A B NA NB:set evs3; Key K ~:used evs3 |]
==> ya3 A B NA NB K # evs3:ya"

YA4: "[| evs4:ya; ya1 A B NA:set evs4; ya3' S Y A B NA NB K:set evs4 |]
==> ya4 A B K NB Y # evs4:ya"

subsection{*declarations for tactics*}

declare knows_Spy_partsEs [elim]
declare Fake_parts_insert [THEN subsetD, dest]
declare initState.simps [simp del]

subsection{*general properties of ya*}

lemma ya_has_no_Gets: "evs:ya ==> ALL A X. Gets A X ~:set evs"
by (erule ya.induct, auto)

lemma ya_is_Gets_correct [iff]: "Gets_correct ya"
by (auto simp: Gets_correct_def dest: ya_has_no_Gets)

lemma ya_is_one_step [iff]: "one_step ya"
by (unfold one_step_def, clarify, ind_cases "ev#evs:ya", auto)

lemma ya_has_only_Says' [rule_format]: "evs:ya ==>
ev:set evs --> (EX A B X. ev=Says A B X)"
by (erule ya.induct, auto)

lemma ya_has_only_Says [iff]: "has_only_Says ya"
by (auto simp: has_only_Says_def dest: ya_has_only_Says')

lemma ya_is_regular [iff]: "regular ya"
apply (simp only: regular_def, clarify)
apply (erule ya.induct, simp_all add: initState.simps knows.simps)
by (auto dest: parts_sub)

subsection{*guardedness of KAB*}

lemma Guard_KAB [rule_format]: "[| evs:ya; A ~:bad; B ~:bad |] ==>
ya3 A B NA NB K:set evs --> GuardK K {shrK A,shrK B} (spies evs)" 
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

subsection{*session keys are not symmetric keys*}

lemma KAB_isnt_shrK [rule_format]: "evs:ya ==>
ya3 A B NA NB K:set evs --> K ~:range shrK"
by (erule ya.induct, auto)

lemma ya3_shrK: "evs:ya ==> ya3 A B NA NB (shrK C) ~:set evs"
by (blast dest: KAB_isnt_shrK)

subsection{*ya2' implies ya1'*}

lemma ya2'_parts_imp_ya1'_parts [rule_format]:
     "[| evs:ya; B ~:bad |] ==>
      Ciph B {|Agent A, Nonce NA, Nonce NB|}:parts (spies evs) -->
      {|Agent A, Nonce NA|}:spies evs"
by (erule ya.induct, auto dest: Says_imp_spies intro: parts_parts)

lemma ya2'_imp_ya1'_parts: "[| ya2' B' A B NA NB:set evs; evs:ya; B ~:bad |]
==> {|Agent A, Nonce NA|}:spies evs"
by (blast dest: Says_imp_spies ya2'_parts_imp_ya1'_parts)

subsection{*uniqueness of NB*}

lemma NB_is_uniq_in_ya2'_parts [rule_format]: "[| evs:ya; B ~:bad; B' ~:bad |] ==>
Ciph B {|Agent A, Nonce NA, Nonce NB|}:parts (spies evs) -->
Ciph B' {|Agent A', Nonce NA', Nonce NB|}:parts (spies evs) -->
A=A' & B=B' & NA=NA'"
apply (erule ya.induct, simp_all, clarify)
apply (drule Crypt_synth_insert, simp+)
apply (drule Crypt_synth_insert, simp+, safe)
apply (drule not_used_parts_false, simp+)+
by (drule Says_not_parts, simp+)+

lemma NB_is_uniq_in_ya2': "[| ya2' C A B NA NB:set evs;
ya2' C' A' B' NA' NB:set evs; evs:ya; B ~:bad; B' ~:bad |]
==> A=A' & B=B' & NA=NA'"
by (drule NB_is_uniq_in_ya2'_parts, auto dest: Says_imp_spies)

subsection{*ya3' implies ya2'*}

lemma ya3'_parts_imp_ya2'_parts [rule_format]: "[| evs:ya; A ~:bad |] ==>
Ciph A {|Agent B, Key K, Nonce NA, Nonce NB|}:parts (spies evs)
--> Ciph B {|Agent A, Nonce NA, Nonce NB|}:parts (spies evs)"
apply (erule ya.induct, simp_all)
apply (clarify, drule Crypt_synth_insert, simp+)
apply (blast intro: parts_sub, blast)
by (auto dest: Says_imp_spies parts_parts)

lemma ya3'_parts_imp_ya2' [rule_format]: "[| evs:ya; A ~:bad |] ==>
Ciph A {|Agent B, Key K, Nonce NA, Nonce NB|}:parts (spies evs)
--> (EX B'. ya2' B' A B NA NB:set evs)"
apply (erule ya.induct, simp_all, safe)
apply (drule Crypt_synth_insert, simp+)
apply (drule Crypt_synth_insert, simp+, blast)
apply blast
apply blast
by (auto dest: Says_imp_spies2 parts_parts)

lemma ya3'_imp_ya2': "[| ya3' S Y A B NA NB K:set evs; evs:ya; A ~:bad |]
==> (EX B'. ya2' B' A B NA NB:set evs)"
by (drule ya3'_parts_imp_ya2', auto dest: Says_imp_spies)

subsection{*ya3' implies ya3*}

lemma ya3'_parts_imp_ya3 [rule_format]: "[| evs:ya; A ~:bad |] ==>
Ciph A {|Agent B, Key K, Nonce NA, Nonce NB|}:parts(spies evs)
--> ya3 A B NA NB K:set evs"
apply (erule ya.induct, simp_all, safe)
apply (drule Crypt_synth_insert, simp+)
by (blast dest: Says_imp_spies2 parts_parts)

lemma ya3'_imp_ya3: "[| ya3' S Y A B NA NB K:set evs; evs:ya; A ~:bad |]
==> ya3 A B NA NB K:set evs"
by (blast dest: Says_imp_spies ya3'_parts_imp_ya3)

subsection{*guardedness of NB*}

constdefs ya_keys :: "agent => agent => nat => nat => event list => key set"
"ya_keys A B NA NB evs == {shrK A,shrK B} Un {K. ya3 A B NA NB K:set evs}"

lemma Guard_NB [rule_format]: "[| evs:ya; A ~:bad; B ~:bad |] ==>
ya2 A B NA NB:set evs --> Guard NB (ya_keys A B NA NB evs) (spies evs)"
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
apply (frule in_Guard_kparts_Crypt, simp+, blast, simp+)
apply (frule_tac A=A and B=B and NA=NA and NB=NB and C=Ba in ya3_shrK, simp)
apply (drule ya2'_imp_ya1'_parts, simp, blast, blast)
apply (case_tac "NBa=NB", clarify)
apply (frule Says_imp_spies)
apply (frule in_Guard_kparts_Crypt, simp+, blast, simp+)
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
apply (rotate_tac -1, frule in_Guard_kparts_Crypt, simp+, blast, simp+)
apply (frule_tac A=A and B=B and NA=NA and NB=NB and C=Ba in ya3_shrK, simp)
apply (drule NB_is_uniq_in_ya2', simp+, blast, clarify)
apply (drule ya3'_imp_ya3, simp+)
apply (simp add: Guard_Nonce)
apply (simp add: No_Nonce)
done

end
