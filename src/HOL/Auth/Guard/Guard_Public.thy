(******************************************************************************
lemmas on guarded messages for public protocols

date: march 2002
author: Frederic Blanqui
email: blanqui@lri.fr
webpage: http://www.lri.fr/~blanqui/

University of Cambridge, Computer Laboratory
William Gates Building, JJ Thomson Avenue
Cambridge CB3 0FD, United Kingdom
******************************************************************************)

theory Guard_Public = Guard + Public + Extensions:

subsection{*Extensions to Theory @{text Public}*}

declare initState.simps [simp del]

subsubsection{*signature*}

constdefs sign :: "agent => msg => msg"
"sign A X == {|Agent A, X, Crypt (priK A) (Hash X)|}"

lemma sign_inj [iff]: "(sign A X = sign A' X') = (A=A' & X=X')"
by (auto simp: sign_def)

subsubsection{*agent associated to a key*}

constdefs agt :: "key => agent"
"agt K == @A. K = priK A | K = pubK A"

lemma agt_priK [simp]: "agt (priK A) = A"
by (simp add: agt_def)

lemma agt_pubK [simp]: "agt (pubK A) = A"
by (simp add: agt_def)

subsubsection{*basic facts about @{term initState}*}

lemma no_Crypt_in_parts_init [simp]: "Crypt K X ~:parts (initState A)"
by (cases A, auto simp: initState.simps)

lemma no_Crypt_in_analz_init [simp]: "Crypt K X ~:analz (initState A)"
by auto

lemma no_priK_in_analz_init [simp]: "A ~:bad
==> Key (priK A) ~:analz (initState Spy)"
by (auto simp: initState.simps)

lemma priK_notin_initState_Friend [simp]: "A ~= Friend C
==> Key (priK A) ~: parts (initState (Friend C))"
by (auto simp: initState.simps)

lemma keyset_init [iff]: "keyset (initState A)"
by (cases A, auto simp: keyset_def initState.simps)

subsubsection{*sets of private keys*}

constdefs priK_set :: "key set => bool"
"priK_set Ks == ALL K. K:Ks --> (EX A. K = priK A)"

lemma in_priK_set: "[| priK_set Ks; K:Ks |] ==> EX A. K = priK A"
by (simp add: priK_set_def)

lemma priK_set1 [iff]: "priK_set {priK A}"
by (simp add: priK_set_def)

lemma priK_set2 [iff]: "priK_set {priK A, priK B}"
by (simp add: priK_set_def)

subsubsection{*sets of good keys*}

constdefs good :: "key set => bool"
"good Ks == ALL K. K:Ks --> agt K ~:bad"

lemma in_good: "[| good Ks; K:Ks |] ==> agt K ~:bad"
by (simp add: good_def)

lemma good1 [simp]: "A ~:bad ==> good {priK A}"
by (simp add: good_def)

lemma good2 [simp]: "[| A ~:bad; B ~:bad |] ==> good {priK A, priK B}"
by (simp add: good_def)

subsubsection{*greatest nonce used in a trace, 0 if there is no nonce*}

consts greatest :: "event list => nat"

recdef greatest "measure size"
"greatest [] = 0"
"greatest (ev # evs) = max (greatest_msg (msg ev)) (greatest evs)"

lemma greatest_is_greatest: "Nonce n:used evs ==> n <= greatest evs"
apply (induct evs, auto simp: initState.simps)
apply (drule used_sub_parts_used, safe)
apply (drule greatest_msg_is_greatest, arith)
by (simp, arith)

subsubsection{*function giving a new nonce*}

constdefs new :: "event list => nat"
"new evs == Suc (greatest evs)"

lemma new_isnt_used [iff]: "Nonce (new evs) ~:used evs"
by (clarify, drule greatest_is_greatest, auto simp: new_def)

subsection{*Proofs About Guarded Messages*}

subsubsection{*small hack necessary because priK is defined as the inverse of pubK*}

lemma pubK_is_invKey_priK: "pubK A = invKey (priK A)"
by simp

lemmas pubK_is_invKey_priK_substI = pubK_is_invKey_priK [THEN ssubst]

lemmas invKey_invKey_substI = invKey [THEN ssubst]

lemma "Nonce n:parts {X} ==> Crypt (pubK A) X:guard n {priK A}"
apply (rule pubK_is_invKey_priK_substI, rule invKey_invKey_substI)
by (rule Guard_Nonce, simp+)

subsubsection{*guardedness results*}

lemma sign_guard [intro]: "X:guard n Ks ==> sign A X:guard n Ks"
by (auto simp: sign_def)

lemma Guard_init [iff]: "Guard n Ks (initState B)"
by (induct B, auto simp: Guard_def initState.simps)

lemma Guard_knows_max': "Guard n Ks (knows_max' C evs)
==> Guard n Ks (knows_max C evs)"
by (simp add: knows_max_def)

lemma Nonce_not_used_Guard_spies [dest]: "Nonce n ~:used evs
==> Guard n Ks (spies evs)"
by (auto simp: Guard_def dest: not_used_not_known parts_sub)

lemma Nonce_not_used_Guard [dest]: "[| evs:p; Nonce n ~:used evs;
Gets_correct p; one_step p |] ==> Guard n Ks (knows (Friend C) evs)"
by (auto simp: Guard_def dest: known_used parts_trans)

lemma Nonce_not_used_Guard_max [dest]: "[| evs:p; Nonce n ~:used evs;
Gets_correct p; one_step p |] ==> Guard n Ks (knows_max (Friend C) evs)"
by (auto simp: Guard_def dest: known_max_used parts_trans)

lemma Nonce_not_used_Guard_max' [dest]: "[| evs:p; Nonce n ~:used evs;
Gets_correct p; one_step p |] ==> Guard n Ks (knows_max' (Friend C) evs)"
apply (rule_tac H="knows_max (Friend C) evs" in Guard_mono)
by (auto simp: knows_max_def)

subsubsection{*regular protocols*}

constdefs regular :: "event list set => bool"
"regular p == ALL evs A. evs:p --> (Key (priK A):parts (spies evs)) = (A:bad)"

lemma priK_parts_iff_bad [simp]: "[| evs:p; regular p |] ==>
(Key (priK A):parts (spies evs)) = (A:bad)"
by (auto simp: regular_def)

lemma priK_analz_iff_bad [simp]: "[| evs:p; regular p |] ==>
(Key (priK A):analz (spies evs)) = (A:bad)"
by auto

lemma Guard_Nonce_analz: "[| Guard n Ks (spies evs); evs:p;
priK_set Ks; good Ks; regular p |] ==> Nonce n ~:analz (spies evs)"
apply (clarify, simp only: knows_decomp)
apply (drule Guard_invKey_keyset, simp+, safe)
apply (drule in_good, simp)
apply (drule in_priK_set, simp+, clarify)
apply (frule_tac A=A in priK_analz_iff_bad)
by (simp add: knows_decomp)+

end