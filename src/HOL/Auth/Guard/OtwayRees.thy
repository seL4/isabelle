(******************************************************************************
date: march 2002
author: Frederic Blanqui
email: blanqui@lri.fr
webpage: http://www.lri.fr/~blanqui/

University of Cambridge, Computer Laboratory
William Gates Building, JJ Thomson Avenue
Cambridge CB3 0FD, United Kingdom
******************************************************************************)

header{*Otway-Rees Protocol*}

theory OtwayRees = Guard_Shared:

subsection{*messages used in the protocol*}

syntax nil :: "msg"

translations "nil" == "Number 0"

syntax or1 :: "agent => agent => nat => event"

translations "or1 A B NA"
=> "Says A B {|Nonce NA, Agent A, Agent B,
               Ciph A {|Nonce NA, Agent A, Agent B|}|}"

syntax or1' :: "agent => agent => agent => nat => msg => event"

translations "or1' A' A B NA X"
=> "Says A' B {|Nonce NA, Agent A, Agent B, X|}"

syntax or2 :: "agent => agent => nat => nat => msg => event"

translations "or2 A B NA NB X"
=> "Says B Server {|Nonce NA, Agent A, Agent B, X,
                    Ciph B {|Nonce NA, Nonce NB, Agent A, Agent B|}|}"

syntax or2' :: "agent => agent => agent => nat => nat => event"

translations "or2' B' A B NA NB"
=> "Says B' Server {|Nonce NA, Agent A, Agent B,
                     Ciph A {|Nonce NA, Agent A, Agent B|},
                     Ciph B {|Nonce NA, Nonce NB, Agent A, Agent B|}|}"

syntax or3 :: "agent => agent => nat => nat => key => event"

translations "or3 A B NA NB K"
=> "Says Server B {|Nonce NA, Ciph A {|Nonce NA, Key K|},
                    Ciph B {|Nonce NB, Key K|}|}"

syntax or3':: "agent => msg => agent => agent => nat => nat => key => event"

translations "or3' S Y A B NA NB K"
=> "Says S B {|Nonce NA, Y, Ciph B {|Nonce NB, Key K|}|}"

syntax or4 :: "agent => agent => nat => msg => event"

translations "or4 A B NA X" => "Says B A {|Nonce NA, X, nil|}"

syntax or4' :: "agent => agent => nat => msg => event"

translations "or4' B' A NA K" =>
"Says B' A {|Nonce NA, Ciph A {|Nonce NA, Key K|}, nil|}"

subsection{*definition of the protocol*}

consts or :: "event list set"

inductive or
intros

Nil: "[]:or"

Fake: "[| evs:or; X:synth (analz (spies evs)) |] ==> Says Spy B X # evs:or"

OR1: "[| evs1:or; Nonce NA ~:used evs1 |] ==> or1 A B NA # evs1:or"

OR2: "[| evs2:or; or1' A' A B NA X:set evs2; Nonce NB ~:used evs2 |]
==> or2 A B NA NB X # evs2:or"

OR3: "[| evs3:or; or2' B' A B NA NB:set evs3; Key K ~:used evs3 |]
==> or3 A B NA NB K # evs3:or"

OR4: "[| evs4:or; or2 A B NA NB X:set evs4; or3' S Y A B NA NB K:set evs4 |]
==> or4 A B NA X # evs4:or"

subsection{*declarations for tactics*}

declare knows_Spy_partsEs [elim]
declare Fake_parts_insert [THEN subsetD, dest]
declare initState.simps [simp del]

subsection{*general properties of or*}

lemma or_has_no_Gets: "evs:or ==> ALL A X. Gets A X ~:set evs"
by (erule or.induct, auto)

lemma or_is_Gets_correct [iff]: "Gets_correct or"
by (auto simp: Gets_correct_def dest: or_has_no_Gets)

lemma or_is_one_step [iff]: "one_step or"
by (unfold one_step_def, clarify, ind_cases "ev#evs:or", auto)

lemma or_has_only_Says' [rule_format]: "evs:or ==>
ev:set evs --> (EX A B X. ev=Says A B X)"
by (erule or.induct, auto)

lemma or_has_only_Says [iff]: "has_only_Says or"
by (auto simp: has_only_Says_def dest: or_has_only_Says')

subsection{*or is regular*}

lemma or1'_parts_spies [dest]: "or1' A' A B NA X:set evs
==> X:parts (spies evs)"
by blast

lemma or2_parts_spies [dest]: "or2 A B NA NB X:set evs
==> X:parts (spies evs)"
by blast

lemma or3_parts_spies [dest]: "Says S B {|NA, Y, Ciph B {|NB, K|}|}:set evs
==> K:parts (spies evs)"
by blast

lemma or_is_regular [iff]: "regular or"
apply (simp only: regular_def, clarify)
apply (erule or.induct, simp_all add: initState.simps knows.simps)
by (auto dest: parts_sub)

subsection{*guardedness of KAB*}

lemma Guard_KAB [rule_format]: "[| evs:or; A ~:bad; B ~:bad |] ==>
or3 A B NA NB K:set evs --> GuardK K {shrK A,shrK B} (spies evs)" 
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

subsection{*guardedness of NB*}

lemma Guard_NB [rule_format]: "[| evs:or; B ~:bad |] ==>
or2 A B NA NB X:set evs --> Guard NB {shrK B} (spies evs)" 
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
apply (drule_tac Y="{|Nonce NB, Agent Aa, Agent Ba|}"
                 and K="shrK Aa" in in_Guard_kparts_Crypt, simp+)
apply (simp add: No_Nonce) 
apply (case_tac "Ba=B", clarsimp)
apply (case_tac "NBa=NB", clarify)
apply (drule Says_imp_spies)
apply (drule_tac Y="{|Nonce NAa, Nonce NB, Agent Aa, Agent Ba|}"
                 and K="shrK Ba" in in_Guard_kparts_Crypt, simp+)
apply (simp add: No_Nonce) 
(* OR4 *)
by (blast dest: Says_imp_spies)+

end
