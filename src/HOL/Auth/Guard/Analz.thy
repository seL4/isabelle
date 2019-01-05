(*  Title:      HOL/Auth/Guard/Analz.thy
    Author:     Frederic Blanqui, University of Cambridge Computer Laboratory
    Copyright   2001  University of Cambridge
*)

section\<open>Decomposition of Analz into two parts\<close>

theory Analz imports Extensions begin

text\<open>decomposition of \<^term>\<open>analz\<close> into two parts: 
      \<^term>\<open>pparts\<close> (for pairs) and analz of \<^term>\<open>kparts\<close>\<close>

subsection\<open>messages that do not contribute to analz\<close>

inductive_set
  pparts :: "msg set => msg set"
  for H :: "msg set"
where
  Inj [intro]: "[| X \<in> H; is_MPair X |] ==> X \<in> pparts H"
| Fst [dest]: "[| \<lbrace>X,Y\<rbrace> \<in> pparts H; is_MPair X |] ==> X \<in> pparts H"
| Snd [dest]: "[| \<lbrace>X,Y\<rbrace> \<in> pparts H; is_MPair Y |] ==> Y \<in> pparts H"

subsection\<open>basic facts about \<^term>\<open>pparts\<close>\<close>

lemma pparts_is_MPair [dest]: "X \<in> pparts H \<Longrightarrow> is_MPair X"
by (erule pparts.induct, auto)

lemma Crypt_notin_pparts [iff]: "Crypt K X \<notin> pparts H"
by auto

lemma Key_notin_pparts [iff]: "Key K \<notin> pparts H"
by auto

lemma Nonce_notin_pparts [iff]: "Nonce n \<notin> pparts H"
by auto

lemma Number_notin_pparts [iff]: "Number n \<notin> pparts H"
by auto

lemma Agent_notin_pparts [iff]: "Agent A \<notin> pparts H"
by auto

lemma pparts_empty [iff]: "pparts {} = {}"
by (auto, erule pparts.induct, auto)

lemma pparts_insertI [intro]: "X \<in> pparts H \<Longrightarrow> X \<in> pparts (insert Y H)"
by (erule pparts.induct, auto)

lemma pparts_sub: "[| X \<in> pparts G; G \<subseteq> H |] ==> X \<in> pparts H"
by (erule pparts.induct, auto)

lemma pparts_insert2 [iff]: "pparts (insert X (insert Y H))
= pparts {X} Un pparts {Y} Un pparts H"
by (rule eq, (erule pparts.induct, auto)+)

lemma pparts_insert_MPair [iff]: "pparts (insert \<lbrace>X,Y\<rbrace> H)
= insert \<lbrace>X,Y\<rbrace> (pparts ({X,Y} \<union> H))"
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

lemma pparts_insert: "X \<in> pparts (insert Y H) \<Longrightarrow> X \<in> pparts {Y} \<union> pparts H"
by (erule pparts.induct, blast+)

lemma insert_pparts: "X \<in> pparts {Y} \<union> pparts H \<Longrightarrow> X \<in> pparts (insert Y H)"
by (safe, erule pparts.induct, auto)

lemma pparts_Un [iff]: "pparts (G \<union> H) = pparts G \<union> pparts H"
by (rule eq, erule pparts.induct, auto dest: pparts_sub)

lemma pparts_pparts [iff]: "pparts (pparts H) = pparts H"
by (rule eq, erule pparts.induct, auto)

lemma pparts_insert_eq: "pparts (insert X H) = pparts {X} Un pparts H"
by (rule_tac A=H in insert_Un, rule pparts_Un)

lemmas pparts_insert_substI = pparts_insert_eq [THEN ssubst]

lemma in_pparts: "Y \<in> pparts H \<Longrightarrow> \<exists>X. X \<in> H \<and> Y \<in> pparts {X}"
by (erule pparts.induct, auto)

subsection\<open>facts about \<^term>\<open>pparts\<close> and \<^term>\<open>parts\<close>\<close>

lemma pparts_no_Nonce [dest]: "[| X \<in> pparts {Y}; Nonce n \<notin> parts {Y} |]
==> Nonce n \<notin> parts {X}"
by (erule pparts.induct, simp_all)

subsection\<open>facts about \<^term>\<open>pparts\<close> and \<^term>\<open>analz\<close>\<close>

lemma pparts_analz: "X \<in> pparts H \<Longrightarrow> X \<in> analz H"
by (erule pparts.induct, auto)

lemma pparts_analz_sub: "[| X \<in> pparts G; G \<subseteq> H |] ==> X \<in> analz H"
by (auto dest: pparts_sub pparts_analz)

subsection\<open>messages that contribute to analz\<close>

inductive_set
  kparts :: "msg set => msg set"
  for H :: "msg set"
where
  Inj [intro]: "[| X \<in> H; not_MPair X |] ==> X \<in> kparts H"
| Fst [intro]: "[| \<lbrace>X,Y\<rbrace> \<in> pparts H; not_MPair X |] ==> X \<in> kparts H"
| Snd [intro]: "[| \<lbrace>X,Y\<rbrace> \<in> pparts H; not_MPair Y |] ==> Y \<in> kparts H"

subsection\<open>basic facts about \<^term>\<open>kparts\<close>\<close>

lemma kparts_not_MPair [dest]: "X \<in> kparts H \<Longrightarrow> not_MPair X"
by (erule kparts.induct, auto)

lemma kparts_empty [iff]: "kparts {} = {}"
by (rule eq, erule kparts.induct, auto)

lemma kparts_insertI [intro]: "X \<in> kparts H \<Longrightarrow> X \<in> kparts (insert Y H)"
by (erule kparts.induct, auto dest: pparts_insertI)

lemma kparts_insert2 [iff]: "kparts (insert X (insert Y H))
= kparts {X} \<union> kparts {Y} \<union> kparts H"
by (rule eq, (erule kparts.induct, auto)+)

lemma kparts_insert_MPair [iff]: "kparts (insert \<lbrace>X,Y\<rbrace> H)
= kparts ({X,Y} \<union> H)"
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

lemma kparts_insert: "X \<in> kparts (insert X H) \<Longrightarrow> X \<in> kparts {X} \<union> kparts H"
by (erule kparts.induct, (blast dest: pparts_insert)+)

lemma kparts_insert_fst [rule_format,dest]: "X \<in> kparts (insert Z H) \<Longrightarrow>
X \<notin> kparts H \<longrightarrow> X \<in> kparts {Z}"
by (erule kparts.induct, (blast dest: pparts_insert)+)

lemma kparts_sub: "[| X \<in> kparts G; G \<subseteq> H |] ==> X \<in> kparts H"
by (erule kparts.induct, auto dest: pparts_sub)

lemma kparts_Un [iff]: "kparts (G \<union> H) = kparts G \<union> kparts H"
by (rule eq, erule kparts.induct, auto dest: kparts_sub)

lemma pparts_kparts [iff]: "pparts (kparts H) = {}"
by (rule eq, erule pparts.induct, auto)

lemma kparts_kparts [iff]: "kparts (kparts H) = kparts H"
by (rule eq, erule kparts.induct, auto)

lemma kparts_insert_eq: "kparts (insert X H) = kparts {X} \<union> kparts H"
by (rule_tac A=H in insert_Un, rule kparts_Un)

lemmas kparts_insert_substI = kparts_insert_eq [THEN ssubst]

lemma in_kparts: "Y \<in> kparts H \<Longrightarrow> \<exists>X. X \<in> H \<and> Y \<in> kparts {X}"
by (erule kparts.induct, auto dest: in_pparts)

lemma kparts_has_no_pair [iff]: "has_no_pair (kparts H)"
by auto

subsection\<open>facts about \<^term>\<open>kparts\<close> and \<^term>\<open>parts\<close>\<close>

lemma kparts_no_Nonce [dest]: "[| X \<in> kparts {Y}; Nonce n \<notin> parts {Y} |]
==> Nonce n \<notin> parts {X}"
by (erule kparts.induct, auto)

lemma kparts_parts: "X \<in> kparts H \<Longrightarrow> X \<in> parts H"
by (erule kparts.induct, auto dest: pparts_analz)

lemma parts_kparts: "X \<in> parts (kparts H) \<Longrightarrow> X \<in> parts H"
by (erule parts.induct, auto dest: kparts_parts
intro: parts.Fst parts.Snd parts.Body)

lemma Crypt_kparts_Nonce_parts [dest]: "[| Crypt K Y \<in> kparts {Z};
Nonce n \<in> parts {Y} |] ==> Nonce n \<in> parts {Z}"
by auto

subsection\<open>facts about \<^term>\<open>kparts\<close> and \<^term>\<open>analz\<close>\<close>

lemma kparts_analz: "X \<in> kparts H \<Longrightarrow> X \<in> analz H"
by (erule kparts.induct, auto dest: pparts_analz)

lemma kparts_analz_sub: "[| X \<in> kparts G; G \<subseteq> H |] ==> X \<in> analz H"
by (erule kparts.induct, auto dest: pparts_analz_sub)

lemma analz_kparts [rule_format,dest]: "X \<in> analz H \<Longrightarrow>
Y \<in> kparts {X} \<longrightarrow> Y \<in> analz H"
by (erule analz.induct, auto dest: kparts_analz_sub)

lemma analz_kparts_analz: "X \<in> analz (kparts H) \<Longrightarrow> X \<in> analz H"
by (erule analz.induct, auto dest: kparts_analz)

lemma analz_kparts_insert: "X \<in> analz (kparts (insert Z H)) \<Longrightarrow> X \<in> analz (kparts {Z} \<union> kparts H)"
by (rule analz_sub, auto)

lemma Nonce_kparts_synth [rule_format]: "Y \<in> synth (analz G)
\<Longrightarrow> Nonce n \<in> kparts {Y} \<longrightarrow> Nonce n \<in> analz G"
by (erule synth.induct, auto)

lemma kparts_insert_synth: "[| Y \<in> parts (insert X G); X \<in> synth (analz G);
Nonce n \<in> kparts {Y}; Nonce n \<notin> analz G |] ==> Y \<in> parts G"
apply (drule parts_insert_substD, clarify)
apply (drule in_sub, drule_tac X=Y in parts_sub, simp)
apply (auto dest: Nonce_kparts_synth)
done

lemma Crypt_insert_synth:
  "[| Crypt K Y \<in> parts (insert X G); X \<in> synth (analz G); Nonce n \<in> kparts {Y}; Nonce n \<notin> analz G |] 
   ==> Crypt K Y \<in> parts G"
by (metis Fake_parts_insert_in_Un Nonce_kparts_synth UnE analz_conj_parts synth_simps(5))


subsection\<open>analz is pparts + analz of kparts\<close>

lemma analz_pparts_kparts: "X \<in> analz H \<Longrightarrow> X \<in> pparts H \<or> X \<in> analz (kparts H)"
by (erule analz.induct, auto) 

lemma analz_pparts_kparts_eq: "analz H = pparts H Un analz (kparts H)"
by (rule eq, auto dest: analz_pparts_kparts pparts_analz analz_kparts_analz)

lemmas analz_pparts_kparts_substI = analz_pparts_kparts_eq [THEN ssubst]
lemmas analz_pparts_kparts_substD = analz_pparts_kparts_eq [THEN sym, THEN ssubst]

end
