(******************************************************************************
incorporating Lowe's fix (inclusion of B's identity in round 2)

date: march 2002
author: Frederic Blanqui
email: blanqui@lri.fr
webpage: http://www.lri.fr/~blanqui/

University of Cambridge, Computer Laboratory
William Gates Building, JJ Thomson Avenue
Cambridge CB3 0FD, United Kingdom
******************************************************************************)

header{*Needham-Schroeder-Lowe Public-Key Protocol*}

theory NS_Public = Guard_Public:

subsection{*messages used in the protocol*}

syntax ns1 :: "agent => agent => nat => event"

translations "ns1 A B NA" => "Says A B (Crypt (pubK B) {|Nonce NA, Agent A|})"

syntax ns1' :: "agent => agent => agent => nat => event"

translations "ns1' A' A B NA"
=> "Says A' B (Crypt (pubK B) {|Nonce NA, Agent A|})"

syntax ns2 :: "agent => agent => nat => nat => event"

translations "ns2 B A NA NB"
=> "Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB, Agent B|})"

syntax ns2' :: "agent => agent => agent => nat => nat => event"

translations "ns2' B' B A NA NB"
=> "Says B' A (Crypt (pubK A) {|Nonce NA, Nonce NB, Agent B|})"

syntax ns3 :: "agent => agent => nat => event"

translations "ns3 A B NB" => "Says A B (Crypt (pubK B) (Nonce NB))"

subsection{*definition of the protocol*}

consts nsp :: "event list set"

inductive nsp
intros

Nil: "[]:nsp"

Fake: "[| evs:nsp; X:synth (analz (spies evs)) |] ==> Says Spy B X # evs : nsp"

NS1: "[| evs1:nsp; Nonce NA ~:used evs1 |] ==> ns1 A B NA # evs1 : nsp"

NS2: "[| evs2:nsp; Nonce NB ~:used evs2; ns1' A' A B NA:set evs2 |] ==>
ns2 B A NA NB # evs2:nsp"

NS3: "[| evs3:nsp; ns1 A B NA:set evs3; ns2' B' B A NA NB:set evs3 |] ==>
ns3 A B NB # evs3:nsp"

subsection{*declarations for tactics*}

declare knows_Spy_partsEs [elim]
declare Fake_parts_insert [THEN subsetD, dest]
declare initState.simps [simp del]

subsection{*general properties of nsp*}

lemma nsp_has_no_Gets: "evs:nsp ==> ALL A X. Gets A X ~:set evs"
by (erule nsp.induct, auto)

lemma nsp_is_Gets_correct [iff]: "Gets_correct nsp"
by (auto simp: Gets_correct_def dest: nsp_has_no_Gets)

lemma nsp_is_one_step [iff]: "one_step nsp"
by (unfold one_step_def, clarify, ind_cases "ev#evs:nsp", auto)

lemma nsp_has_only_Says' [rule_format]: "evs:nsp ==>
ev:set evs --> (EX A B X. ev=Says A B X)"
by (erule nsp.induct, auto)

lemma nsp_has_only_Says [iff]: "has_only_Says nsp"
by (auto simp: has_only_Says_def dest: nsp_has_only_Says')

lemma nsp_is_regular [iff]: "regular nsp"
apply (simp only: regular_def, clarify)
by (erule nsp.induct, auto simp: initState.simps knows.simps)

subsection{*nonce are used only once*}

lemma NA_is_uniq [rule_format]: "evs:nsp ==>
Crypt (pubK B) {|Nonce NA, Agent A|}:parts (spies evs)
--> Crypt (pubK B') {|Nonce NA, Agent A'|}:parts (spies evs)
--> Nonce NA ~:analz (spies evs) --> A=A' & B=B'"
apply (erule nsp.induct, simp_all)
by (blast intro: analz_insertI)+

lemma no_Nonce_NS1_NS2 [rule_format]: "evs:nsp ==>
Crypt (pubK B') {|Nonce NA', Nonce NA, Agent A'|}:parts (spies evs)
--> Crypt (pubK B) {|Nonce NA, Agent A|}:parts (spies evs)
--> Nonce NA:analz (spies evs)"
apply (erule nsp.induct, simp_all)
by (blast intro: analz_insertI)+

lemma no_Nonce_NS1_NS2' [rule_format]:
"[| Crypt (pubK B') {|Nonce NA', Nonce NA, Agent A'|}:parts (spies evs);
Crypt (pubK B) {|Nonce NA, Agent A|}:parts (spies evs); evs:nsp |]
==> Nonce NA:analz (spies evs)"
by (rule no_Nonce_NS1_NS2, auto)
 
lemma NB_is_uniq [rule_format]: "evs:nsp ==>
Crypt (pubK A) {|Nonce NA, Nonce NB, Agent B|}:parts (spies evs)
--> Crypt (pubK A') {|Nonce NA', Nonce NB, Agent B'|}:parts (spies evs)
--> Nonce NB ~:analz (spies evs) --> A=A' & B=B' & NA=NA'"
apply (erule nsp.induct, simp_all)
by (blast intro: analz_insertI)+

subsection{*guardedness of NA*}

lemma ns1_imp_Guard [rule_format]: "[| evs:nsp; A ~:bad; B ~:bad |] ==>
ns1 A B NA:set evs --> Guard NA {priK A,priK B} (spies evs)"
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

subsection{*guardedness of NB*}

lemma ns2_imp_Guard [rule_format]: "[| evs:nsp; A ~:bad; B ~:bad |] ==>
ns2 B A NA NB:set evs --> Guard NB {priK A,priK B} (spies evs)" 
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
by (drule_tac A=Aa and A'=A in NB_is_uniq, auto)

subsection{*Agents' Authentication*}

lemma B_trusts_NS1: "[| evs:nsp; A ~:bad; B ~:bad |] ==>
Crypt (pubK B) {|Nonce NA, Agent A|}:parts (spies evs)
--> Nonce NA ~:analz (spies evs) --> ns1 A B NA:set evs"
apply (erule nsp.induct, simp_all)
by (blast intro: analz_insertI)+

lemma A_trusts_NS2: "[| evs:nsp; A ~:bad; B ~:bad |] ==> ns1 A B NA:set evs
--> Crypt (pubK A) {|Nonce NA, Nonce NB, Agent B|}:parts (spies evs)
--> ns2 B A NA NB:set evs"
apply (erule nsp.induct, simp_all, safe)
apply (frule_tac B=B in ns1_imp_Guard, simp+)
apply (drule Guard_Nonce_analz, simp+, blast)
apply (frule_tac B=B in ns1_imp_Guard, simp+)
apply (drule Guard_Nonce_analz, simp+, blast)
apply (frule_tac B=B in ns1_imp_Guard, simp+)
by (drule Guard_Nonce_analz, simp+, blast+)

lemma B_trusts_NS3: "[| evs:nsp; A ~:bad; B ~:bad |] ==> ns2 B A NA NB:set evs
--> Crypt (pubK B) (Nonce NB):parts (spies evs) --> ns3 A B NB:set evs"
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
