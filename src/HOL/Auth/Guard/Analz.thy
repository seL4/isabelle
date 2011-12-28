(*  Title:      HOL/Auth/Guard/Analz.thy
    Author:     Frederic Blanqui, University of Cambridge Computer Laboratory
    Copyright   2001  University of Cambridge
*)

header{*Decomposition of Analz into two parts*}

theory Analz imports Extensions begin

text{*decomposition of @{term analz} into two parts: 
      @{term pparts} (for pairs) and analz of @{term kparts}*}

subsection{*messages that do not contribute to analz*}

inductive_set
  pparts :: "msg set => msg set"
  for H :: "msg set"
where
  Inj [intro]: "[| X:H; is_MPair X |] ==> X:pparts H"
| Fst [dest]: "[| {|X,Y|}:pparts H; is_MPair X |] ==> X:pparts H"
| Snd [dest]: "[| {|X,Y|}:pparts H; is_MPair Y |] ==> Y:pparts H"

subsection{*basic facts about @{term pparts}*}

lemma pparts_is_MPair [dest]: "X:pparts H ==> is_MPair X"
by (erule pparts.induct, auto)

lemma Crypt_notin_pparts [iff]: "Crypt K X ~:pparts H"
by auto

lemma Key_notin_pparts [iff]: "Key K ~:pparts H"
by auto

lemma Nonce_notin_pparts [iff]: "Nonce n ~:pparts H"
by auto

lemma Number_notin_pparts [iff]: "Number n ~:pparts H"
by auto

lemma Agent_notin_pparts [iff]: "Agent A ~:pparts H"
by auto

lemma pparts_empty [iff]: "pparts {} = {}"
by (auto, erule pparts.induct, auto)

lemma pparts_insertI [intro]: "X:pparts H ==> X:pparts (insert Y H)"
by (erule pparts.induct, auto)

lemma pparts_sub: "[| X:pparts G; G<=H |] ==> X:pparts H"
by (erule pparts.induct, auto)

lemma pparts_insert2 [iff]: "pparts (insert X (insert Y H))
= pparts {X} Un pparts {Y} Un pparts H"
by (rule eq, (erule pparts.induct, auto)+)

lemma pparts_insert_MPair [iff]: "pparts (insert {|X,Y|} H)
= insert {|X,Y|} (pparts ({X,Y} Un H))"
apply (rule eq, (erule pparts.induct, auto)+)
apply (rule_tac Y=Y in pparts.Fst, auto)
apply (erule pparts.induct, auto)
by (rule_tac X=X in pparts.Snd, auto)

lemma pparts_insert_Nonce [iff]: "pparts (insert (Nonce n) H) = pparts H"
by (rule eq, erule pparts.induct, auto)

lemma pparts_insert_Crypt [iff]: "pparts (insert (Crypt K X) H) = pparts H"
by (rule eq, erule pparts.induct, auto)

lemma pparts_insert_Key [iff]: "pparts (insert (Key K) H) = pparts H"
by (rule eq, erule pparts.induct, auto)

lemma pparts_insert_Agent [iff]: "pparts (insert (Agent A) H) = pparts H"
by (rule eq, erule pparts.induct, auto)

lemma pparts_insert_Number [iff]: "pparts (insert (Number n) H) = pparts H"
by (rule eq, erule pparts.induct, auto)

lemma pparts_insert_Hash [iff]: "pparts (insert (Hash X) H) = pparts H"
by (rule eq, erule pparts.induct, auto)

lemma pparts_insert: "X:pparts (insert Y H) ==> X:pparts {Y} Un pparts H"
by (erule pparts.induct, blast+)

lemma insert_pparts: "X:pparts {Y} Un pparts H ==> X:pparts (insert Y H)"
by (safe, erule pparts.induct, auto)

lemma pparts_Un [iff]: "pparts (G Un H) = pparts G Un pparts H"
by (rule eq, erule pparts.induct, auto dest: pparts_sub)

lemma pparts_pparts [iff]: "pparts (pparts H) = pparts H"
by (rule eq, erule pparts.induct, auto)

lemma pparts_insert_eq: "pparts (insert X H) = pparts {X} Un pparts H"
by (rule_tac A=H in insert_Un, rule pparts_Un)

lemmas pparts_insert_substI = pparts_insert_eq [THEN ssubst]

lemma in_pparts: "Y:pparts H ==> EX X. X:H & Y:pparts {X}"
by (erule pparts.induct, auto)

subsection{*facts about @{term pparts} and @{term parts}*}

lemma pparts_no_Nonce [dest]: "[| X:pparts {Y}; Nonce n ~:parts {Y} |]
==> Nonce n ~:parts {X}"
by (erule pparts.induct, simp_all)

subsection{*facts about @{term pparts} and @{term analz}*}

lemma pparts_analz: "X:pparts H ==> X:analz H"
by (erule pparts.induct, auto)

lemma pparts_analz_sub: "[| X:pparts G; G<=H |] ==> X:analz H"
by (auto dest: pparts_sub pparts_analz)

subsection{*messages that contribute to analz*}

inductive_set
  kparts :: "msg set => msg set"
  for H :: "msg set"
where
  Inj [intro]: "[| X:H; not_MPair X |] ==> X:kparts H"
| Fst [intro]: "[| {|X,Y|}:pparts H; not_MPair X |] ==> X:kparts H"
| Snd [intro]: "[| {|X,Y|}:pparts H; not_MPair Y |] ==> Y:kparts H"

subsection{*basic facts about @{term kparts}*}

lemma kparts_not_MPair [dest]: "X:kparts H ==> not_MPair X"
by (erule kparts.induct, auto)

lemma kparts_empty [iff]: "kparts {} = {}"
by (rule eq, erule kparts.induct, auto)

lemma kparts_insertI [intro]: "X:kparts H ==> X:kparts (insert Y H)"
by (erule kparts.induct, auto dest: pparts_insertI)

lemma kparts_insert2 [iff]: "kparts (insert X (insert Y H))
= kparts {X} Un kparts {Y} Un kparts H"
by (rule eq, (erule kparts.induct, auto)+)

lemma kparts_insert_MPair [iff]: "kparts (insert {|X,Y|} H)
= kparts ({X,Y} Un H)"
by (rule eq, (erule kparts.induct, auto)+)

lemma kparts_insert_Nonce [iff]: "kparts (insert (Nonce n) H)
= insert (Nonce n) (kparts H)"
by (rule eq, erule kparts.induct, auto)

lemma kparts_insert_Crypt [iff]: "kparts (insert (Crypt K X) H)
= insert (Crypt K X) (kparts H)"
by (rule eq, erule kparts.induct, auto)

lemma kparts_insert_Key [iff]: "kparts (insert (Key K) H)
= insert (Key K) (kparts H)"
by (rule eq, erule kparts.induct, auto)

lemma kparts_insert_Agent [iff]: "kparts (insert (Agent A) H)
= insert (Agent A) (kparts H)"
by (rule eq, erule kparts.induct, auto)

lemma kparts_insert_Number [iff]: "kparts (insert (Number n) H)
= insert (Number n) (kparts H)"
by (rule eq, erule kparts.induct, auto)

lemma kparts_insert_Hash [iff]: "kparts (insert (Hash X) H)
= insert (Hash X) (kparts H)"
by (rule eq, erule kparts.induct, auto)

lemma kparts_insert: "X:kparts (insert X H) ==> X:kparts {X} Un kparts H"
by (erule kparts.induct, (blast dest: pparts_insert)+)

lemma kparts_insert_fst [rule_format,dest]: "X:kparts (insert Z H) ==>
X ~:kparts H --> X:kparts {Z}"
by (erule kparts.induct, (blast dest: pparts_insert)+)

lemma kparts_sub: "[| X:kparts G; G<=H |] ==> X:kparts H"
by (erule kparts.induct, auto dest: pparts_sub)

lemma kparts_Un [iff]: "kparts (G Un H) = kparts G Un kparts H"
by (rule eq, erule kparts.induct, auto dest: kparts_sub)

lemma pparts_kparts [iff]: "pparts (kparts H) = {}"
by (rule eq, erule pparts.induct, auto)

lemma kparts_kparts [iff]: "kparts (kparts H) = kparts H"
by (rule eq, erule kparts.induct, auto)

lemma kparts_insert_eq: "kparts (insert X H) = kparts {X} Un kparts H"
by (rule_tac A=H in insert_Un, rule kparts_Un)

lemmas kparts_insert_substI = kparts_insert_eq [THEN ssubst]

lemma in_kparts: "Y:kparts H ==> EX X. X:H & Y:kparts {X}"
by (erule kparts.induct, auto dest: in_pparts)

lemma kparts_has_no_pair [iff]: "has_no_pair (kparts H)"
by auto

subsection{*facts about @{term kparts} and @{term parts}*}

lemma kparts_no_Nonce [dest]: "[| X:kparts {Y}; Nonce n ~:parts {Y} |]
==> Nonce n ~:parts {X}"
by (erule kparts.induct, auto)

lemma kparts_parts: "X:kparts H ==> X:parts H"
by (erule kparts.induct, auto dest: pparts_analz)

lemma parts_kparts: "X:parts (kparts H) ==> X:parts H"
by (erule parts.induct, auto dest: kparts_parts
intro: parts.Fst parts.Snd parts.Body)

lemma Crypt_kparts_Nonce_parts [dest]: "[| Crypt K Y:kparts {Z};
Nonce n:parts {Y} |] ==> Nonce n:parts {Z}"
by auto

subsection{*facts about @{term kparts} and @{term analz}*}

lemma kparts_analz: "X:kparts H ==> X:analz H"
by (erule kparts.induct, auto dest: pparts_analz)

lemma kparts_analz_sub: "[| X:kparts G; G<=H |] ==> X:analz H"
by (erule kparts.induct, auto dest: pparts_analz_sub)

lemma analz_kparts [rule_format,dest]: "X:analz H ==>
Y:kparts {X} --> Y:analz H"
by (erule analz.induct, auto dest: kparts_analz_sub)

lemma analz_kparts_analz: "X:analz (kparts H) ==> X:analz H"
by (erule analz.induct, auto dest: kparts_analz)

lemma analz_kparts_insert: "X:analz (kparts (insert Z H)) ==> X:analz (kparts {Z} Un kparts H)"
by (rule analz_sub, auto)

lemma Nonce_kparts_synth [rule_format]: "Y:synth (analz G)
==> Nonce n:kparts {Y} --> Nonce n:analz G"
by (erule synth.induct, auto)

lemma kparts_insert_synth: "[| Y:parts (insert X G); X:synth (analz G);
Nonce n:kparts {Y}; Nonce n ~:analz G |] ==> Y:parts G"
apply (drule parts_insert_substD, clarify)
apply (drule in_sub, drule_tac X=Y in parts_sub, simp)
apply (auto dest: Nonce_kparts_synth)
done

lemma Crypt_insert_synth:
  "[| Crypt K Y:parts (insert X G); X:synth (analz G); Nonce n:kparts {Y}; Nonce n ~:analz G |] 
   ==> Crypt K Y:parts G"
by (metis Fake_parts_insert_in_Un Nonce_kparts_synth UnE analz_conj_parts synth_simps(5))


subsection{*analz is pparts + analz of kparts*}

lemma analz_pparts_kparts: "X:analz H ==> X:pparts H | X:analz (kparts H)"
by (erule analz.induct, auto) 

lemma analz_pparts_kparts_eq: "analz H = pparts H Un analz (kparts H)"
by (rule eq, auto dest: analz_pparts_kparts pparts_analz analz_kparts_analz)

lemmas analz_pparts_kparts_substI = analz_pparts_kparts_eq [THEN ssubst]
lemmas analz_pparts_kparts_substD = analz_pparts_kparts_eq [THEN sym, THEN ssubst]

end
