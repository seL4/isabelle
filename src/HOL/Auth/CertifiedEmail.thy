(*  Title:      HOL/Auth/CertifiedEmail.thy
    Author:     Giampaolo Bella, Christiano Longo and Lawrence C Paulson
*)

section\<open>The Certified Electronic Mail Protocol by Abadi et al.\<close>

theory CertifiedEmail imports Public begin

abbreviation
  TTP :: agent where
  "TTP == Server"

abbreviation
  RPwd :: "agent \<Rightarrow> key" where
  "RPwd == shrK"

 
(*FIXME: the four options should be represented by pairs of 0 or 1.
  Right now only BothAuth is modelled.*)
consts
  NoAuth   :: nat
  TTPAuth  :: nat
  SAuth    :: nat
  BothAuth :: nat

text\<open>We formalize a fixed way of computing responses.  Could be better.\<close>
definition "response" :: "agent \<Rightarrow> agent \<Rightarrow> nat \<Rightarrow> msg" where
   "response S R q == Hash \<lbrace>Agent S, Key (shrK R), Nonce q\<rbrace>"


inductive_set certified_mail :: "event list set"
  where

  Nil: \<comment> \<open>The empty trace\<close>
     "[] \<in> certified_mail"

| Fake: \<comment> \<open>The Spy may say anything he can say.  The sender field is correct,
          but agents don't use that information.\<close>
      "[| evsf \<in> certified_mail; X \<in> synth(analz(spies evsf))|] 
       ==> Says Spy B X # evsf \<in> certified_mail"

| FakeSSL: \<comment> \<open>The Spy may open SSL sessions with TTP, who is the only agent
    equipped with the necessary credentials to serve as an SSL server.\<close>
         "[| evsfssl \<in> certified_mail; X \<in> synth(analz(spies evsfssl))|]
          ==> Notes TTP \<lbrace>Agent Spy, Agent TTP, X\<rbrace> # evsfssl \<in> certified_mail"

| CM1: \<comment> \<open>The sender approaches the recipient.  The message is a number.\<close>
 "[|evs1 \<in> certified_mail;
    Key K \<notin> used evs1;
    K \<in> symKeys;
    Nonce q \<notin> used evs1;
    hs = Hash\<lbrace>Number cleartext, Nonce q, response S R q, Crypt K (Number m)\<rbrace>;
    S2TTP = Crypt(pubEK TTP) \<lbrace>Agent S, Number BothAuth, Key K, Agent R, hs\<rbrace>|]
  ==> Says S R \<lbrace>Agent S, Agent TTP, Crypt K (Number m), Number BothAuth, 
                 Number cleartext, Nonce q, S2TTP\<rbrace> # evs1 
        \<in> certified_mail"

| CM2: \<comment> \<open>The recipient records \<^term>\<open>S2TTP\<close> while transmitting it and her
     password to \<^term>\<open>TTP\<close> over an SSL channel.\<close>
 "[|evs2 \<in> certified_mail;
    Gets R \<lbrace>Agent S, Agent TTP, em, Number BothAuth, Number cleartext, 
             Nonce q, S2TTP\<rbrace> \<in> set evs2;
    TTP \<noteq> R;  
    hr = Hash \<lbrace>Number cleartext, Nonce q, response S R q, em\<rbrace> |]
  ==> 
   Notes TTP \<lbrace>Agent R, Agent TTP, S2TTP, Key(RPwd R), hr\<rbrace> # evs2
      \<in> certified_mail"

| CM3: \<comment> \<open>\<^term>\<open>TTP\<close> simultaneously reveals the key to the recipient and gives
         a receipt to the sender.  The SSL channel does not authenticate 
         the client (\<^term>\<open>R\<close>), but \<^term>\<open>TTP\<close> accepts the message only 
         if the given password is that of the claimed sender, \<^term>\<open>R\<close>.
         He replies over the established SSL channel.\<close>
 "[|evs3 \<in> certified_mail;
    Notes TTP \<lbrace>Agent R, Agent TTP, S2TTP, Key(RPwd R), hr\<rbrace> \<in> set evs3;
    S2TTP = Crypt (pubEK TTP) 
                     \<lbrace>Agent S, Number BothAuth, Key k, Agent R, hs\<rbrace>;
    TTP \<noteq> R;  hs = hr;  k \<in> symKeys|]
  ==> 
   Notes R \<lbrace>Agent TTP, Agent R, Key k, hr\<rbrace> # 
   Gets S (Crypt (priSK TTP) S2TTP) # 
   Says TTP S (Crypt (priSK TTP) S2TTP) # evs3 \<in> certified_mail"

| Reception:
 "[|evsr \<in> certified_mail; Says A B X \<in> set evsr|]
  ==> Gets B X#evsr \<in> certified_mail"


declare Says_imp_knows_Spy [THEN analz.Inj, dest]
declare analz_into_parts [dest]

(*A "possibility property": there are traces that reach the end*)
lemma "[| Key K \<notin> used []; K \<in> symKeys |] ==> 
       \<exists>S2TTP. \<exists>evs \<in> certified_mail.
           Says TTP S (Crypt (priSK TTP) S2TTP) \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] certified_mail.Nil
                    [THEN certified_mail.CM1, THEN certified_mail.Reception,
                     THEN certified_mail.CM2, 
                     THEN certified_mail.CM3]) 
apply (possibility, auto) 
done


lemma Gets_imp_Says:
 "[| Gets B X \<in> set evs; evs \<in> certified_mail |] ==> \<exists>A. Says A B X \<in> set evs"
apply (erule rev_mp)
apply (erule certified_mail.induct, auto)
done


lemma Gets_imp_parts_knows_Spy:
     "[|Gets A X \<in> set evs; evs \<in> certified_mail|] ==> X \<in> parts(spies evs)"
apply (drule Gets_imp_Says, simp)
apply (blast dest: Says_imp_knows_Spy parts.Inj) 
done

lemma CM2_S2TTP_analz_knows_Spy:
 "[|Gets R \<lbrace>Agent A, Agent B, em, Number AO, Number cleartext, 
              Nonce q, S2TTP\<rbrace> \<in> set evs;
    evs \<in> certified_mail|] 
  ==> S2TTP \<in> analz(spies evs)"
apply (drule Gets_imp_Says, simp) 
apply (blast dest: Says_imp_knows_Spy analz.Inj) 
done

lemmas CM2_S2TTP_parts_knows_Spy = 
    CM2_S2TTP_analz_knows_Spy [THEN analz_subset_parts [THEN subsetD]]

lemma hr_form_lemma [rule_format]:
 "evs \<in> certified_mail
  \<Longrightarrow> hr \<notin> synth (analz (spies evs)) \<longrightarrow>
      (\<forall>S2TTP. Notes TTP \<lbrace>Agent R, Agent TTP, S2TTP, pwd, hr\<rbrace>
          \<in> set evs \<longrightarrow>
      (\<exists>clt q S em. hr = Hash \<lbrace>Number clt, Nonce q, response S R q, em\<rbrace>))"
apply (erule certified_mail.induct)
apply (synth_analz_mono_contra, simp_all, blast+)
done 

text\<open>Cannot strengthen the first disjunct to \<^term>\<open>R\<noteq>Spy\<close> because
the fakessl rule allows Spy to spoof the sender's name.  Maybe can
strengthen the second disjunct with \<^term>\<open>R\<noteq>Spy\<close>.\<close>
lemma hr_form:
 "[|Notes TTP \<lbrace>Agent R, Agent TTP, S2TTP, pwd, hr\<rbrace> \<in> set evs;
    evs \<in> certified_mail|]
  ==> hr \<in> synth (analz (spies evs)) | 
      (\<exists>clt q S em. hr = Hash \<lbrace>Number clt, Nonce q, response S R q, em\<rbrace>)"
by (blast intro: hr_form_lemma) 

lemma Spy_dont_know_private_keys [dest!]:
    "[|Key (privateKey b A) \<in> parts (spies evs); evs \<in> certified_mail|]
     ==> A \<in> bad"
apply (erule rev_mp) 
apply (erule certified_mail.induct, simp_all)
txt\<open>Fake\<close>
apply (blast dest: Fake_parts_insert_in_Un) 
txt\<open>Message 1\<close>
apply blast  
txt\<open>Message 3\<close>
apply (frule_tac hr_form, assumption)
apply (elim disjE exE) 
apply (simp_all add: parts_insert2) 
 apply (force dest!: parts_insert_subset_Un [THEN [2] rev_subsetD] 
                     analz_subset_parts [THEN subsetD], blast) 
done

lemma Spy_know_private_keys_iff [simp]:
    "evs \<in> certified_mail
     ==> (Key (privateKey b A) \<in> parts (spies evs)) = (A \<in> bad)"
by blast 

lemma Spy_dont_know_TTPKey_parts [simp]:
     "evs \<in> certified_mail ==> Key (privateKey b TTP) \<notin> parts(spies evs)" 
by simp

lemma Spy_dont_know_TTPKey_analz [simp]:
     "evs \<in> certified_mail ==> Key (privateKey b TTP) \<notin> analz(spies evs)"
by auto

text\<open>Thus, prove any goal that assumes that \<^term>\<open>Spy\<close> knows a private key
belonging to \<^term>\<open>TTP\<close>\<close>
declare Spy_dont_know_TTPKey_parts [THEN [2] rev_notE, elim!]


lemma CM3_k_parts_knows_Spy:
 "[| evs \<in> certified_mail;
     Notes TTP \<lbrace>Agent A, Agent TTP,
                 Crypt (pubEK TTP) \<lbrace>Agent S, Number AO, Key K, 
                 Agent R, hs\<rbrace>, Key (RPwd R), hs\<rbrace> \<in> set evs|]
  ==> Key K \<in> parts(spies evs)"
apply (rotate_tac 1)
apply (erule rev_mp)
apply (erule certified_mail.induct, simp_all)
   apply (blast  intro:parts_insertI)
txt\<open>Fake SSL\<close>
apply (blast dest: parts.Body) 
txt\<open>Message 2\<close>
apply (blast dest!: Gets_imp_Says elim!: knows_Spy_partsEs)
txt\<open>Message 3\<close>
apply (metis parts_insertI)
done

lemma Spy_dont_know_RPwd [rule_format]:
    "evs \<in> certified_mail ==> Key (RPwd A) \<in> parts(spies evs) \<longrightarrow> A \<in> bad"
apply (erule certified_mail.induct, simp_all) 
txt\<open>Fake\<close>
apply (blast dest: Fake_parts_insert_in_Un) 
txt\<open>Message 1\<close>
apply blast  
txt\<open>Message 3\<close>
apply (frule CM3_k_parts_knows_Spy, assumption)
apply (frule_tac hr_form, assumption)
apply (elim disjE exE) 
apply (simp_all add: parts_insert2) 
apply (force dest!: parts_insert_subset_Un [THEN [2] rev_subsetD]
                    analz_subset_parts [THEN subsetD])
done


lemma Spy_know_RPwd_iff [simp]:
    "evs \<in> certified_mail ==> (Key (RPwd A) \<in> parts(spies evs)) = (A\<in>bad)"
by (auto simp add: Spy_dont_know_RPwd) 

lemma Spy_analz_RPwd_iff [simp]:
    "evs \<in> certified_mail ==> (Key (RPwd A) \<in> analz(spies evs)) = (A\<in>bad)"
by (metis Spy_know_RPwd_iff Spy_spies_bad_shrK analz.Inj analz_into_parts)

text\<open>Unused, but a guarantee of sorts\<close>
theorem CertAutenticity:
     "[|Crypt (priSK TTP) X \<in> parts (spies evs); evs \<in> certified_mail|] 
      ==> \<exists>A. Says TTP A (Crypt (priSK TTP) X) \<in> set evs"
apply (erule rev_mp)
apply (erule certified_mail.induct, simp_all) 
txt\<open>Fake\<close>
apply (blast dest: Spy_dont_know_private_keys Fake_parts_insert_in_Un)
txt\<open>Message 1\<close>
apply blast 
txt\<open>Message 3\<close>
apply (frule_tac hr_form, assumption)
apply (elim disjE exE) 
apply (simp_all add: parts_insert2 parts_insert_knows_A) 
 apply (blast dest!: Fake_parts_sing_imp_Un, blast)
done


subsection\<open>Proving Confidentiality Results\<close>

lemma analz_image_freshK [rule_format]:
 "evs \<in> certified_mail ==>
   \<forall>K KK. invKey (pubEK TTP) \<notin> KK \<longrightarrow>
          (Key K \<in> analz (Key`KK \<union> (spies evs))) =
          (K \<in> KK | Key K \<in> analz (spies evs))"
apply (erule certified_mail.induct)
apply (drule_tac [6] A=TTP in symKey_neq_priEK) 
apply (erule_tac [6] disjE [OF hr_form]) 
apply (drule_tac [5] CM2_S2TTP_analz_knows_Spy) 
prefer 9
apply (elim exE)
apply (simp_all add: synth_analz_insert_eq
                     subset_trans [OF _ subset_insertI]
                     subset_trans [OF _ Un_upper2] 
                del: image_insert image_Un add: analz_image_freshK_simps)
done


lemma analz_insert_freshK:
  "[| evs \<in> certified_mail;  KAB \<noteq> invKey (pubEK TTP) |] ==>
      (Key K \<in> analz (insert (Key KAB) (spies evs))) =
      (K = KAB | Key K \<in> analz (spies evs))"
by (simp only: analz_image_freshK analz_image_freshK_simps)

text\<open>\<^term>\<open>S2TTP\<close> must have originated from a valid sender
    provided \<^term>\<open>K\<close> is secure.  Proof is surprisingly hard.\<close>

lemma Notes_SSL_imp_used:
     "[|Notes B \<lbrace>Agent A, Agent B, X\<rbrace> \<in> set evs|] ==> X \<in> used evs"
by (blast dest!: Notes_imp_used)


(*The weaker version, replacing "used evs" by "parts (spies evs)", 
   isn't inductive: message 3 case can't be proved *)
lemma S2TTP_sender_lemma [rule_format]:
 "evs \<in> certified_mail ==>
    Key K \<notin> analz (spies evs) \<longrightarrow>
    (\<forall>AO. Crypt (pubEK TTP)
           \<lbrace>Agent S, Number AO, Key K, Agent R, hs\<rbrace> \<in> used evs \<longrightarrow>
    (\<exists>m ctxt q. 
        hs = Hash\<lbrace>Number ctxt, Nonce q, response S R q, Crypt K (Number m)\<rbrace> \<and>
        Says S R
           \<lbrace>Agent S, Agent TTP, Crypt K (Number m), Number AO,
             Number ctxt, Nonce q,
             Crypt (pubEK TTP)
              \<lbrace>Agent S, Number AO, Key K, Agent R, hs \<rbrace>\<rbrace> \<in> set evs))" 
apply (erule certified_mail.induct, analz_mono_contra)
apply (drule_tac [5] CM2_S2TTP_parts_knows_Spy, simp)
apply (simp add: used_Nil Crypt_notin_initState, simp_all)
txt\<open>Fake\<close>
apply (blast dest: Fake_parts_sing [THEN subsetD]
             dest!: analz_subset_parts [THEN subsetD])  
txt\<open>Fake SSL\<close>
apply (blast dest: Fake_parts_sing [THEN subsetD]
             dest: analz_subset_parts [THEN subsetD])  
txt\<open>Message 1\<close>
apply (clarsimp, blast)
txt\<open>Message 2\<close>
apply (simp add: parts_insert2, clarify) 
apply (metis parts_cut Un_empty_left usedI)
txt\<open>Message 3\<close> 
apply (blast dest: Notes_SSL_imp_used used_parts_subset_parts) 
done 

lemma S2TTP_sender:
 "[|Crypt (pubEK TTP) \<lbrace>Agent S, Number AO, Key K, Agent R, hs\<rbrace> \<in> used evs;
    Key K \<notin> analz (spies evs);
    evs \<in> certified_mail|]
  ==> \<exists>m ctxt q. 
        hs = Hash\<lbrace>Number ctxt, Nonce q, response S R q, Crypt K (Number m)\<rbrace> \<and>
        Says S R
           \<lbrace>Agent S, Agent TTP, Crypt K (Number m), Number AO,
             Number ctxt, Nonce q,
             Crypt (pubEK TTP)
              \<lbrace>Agent S, Number AO, Key K, Agent R, hs\<rbrace>\<rbrace> \<in> set evs" 
by (blast intro: S2TTP_sender_lemma) 


text\<open>Nobody can have used non-existent keys!\<close>
lemma new_keys_not_used [simp]:
    "[|Key K \<notin> used evs; K \<in> symKeys; evs \<in> certified_mail|]
     ==> K \<notin> keysFor (parts (spies evs))"
apply (erule rev_mp) 
apply (erule certified_mail.induct, simp_all) 
txt\<open>Fake\<close>
apply (force dest!: keysFor_parts_insert) 
txt\<open>Message 1\<close>
apply blast 
txt\<open>Message 3\<close>
apply (frule CM3_k_parts_knows_Spy, assumption)
apply (frule_tac hr_form, assumption) 
apply (force dest!: keysFor_parts_insert)
done


text\<open>Less easy to prove \<^term>\<open>m'=m\<close>.  Maybe needs a separate unicity
theorem for ciphertexts of the form \<^term>\<open>Crypt K (Number m)\<close>, 
where \<^term>\<open>K\<close> is secure.\<close>
lemma Key_unique_lemma [rule_format]:
     "evs \<in> certified_mail ==>
       Key K \<notin> analz (spies evs) \<longrightarrow>
       (\<forall>m cleartext q hs.
        Says S R
           \<lbrace>Agent S, Agent TTP, Crypt K (Number m), Number AO,
             Number cleartext, Nonce q,
             Crypt (pubEK TTP) \<lbrace>Agent S, Number AO, Key K, Agent R, hs\<rbrace>\<rbrace>
          \<in> set evs \<longrightarrow>
       (\<forall>m' cleartext' q' hs'.
       Says S' R'
           \<lbrace>Agent S', Agent TTP, Crypt K (Number m'), Number AO',
             Number cleartext', Nonce q',
             Crypt (pubEK TTP) \<lbrace>Agent S', Number AO', Key K, Agent R', hs'\<rbrace>\<rbrace>
          \<in> set evs \<longrightarrow> R' = R \<and> S' = S \<and> AO' = AO \<and> hs' = hs))" 
apply (erule certified_mail.induct, analz_mono_contra, simp_all)
 prefer 2
 txt\<open>Message 1\<close>
 apply (blast dest!: Says_imp_knows_Spy [THEN parts.Inj] new_keys_not_used Crypt_imp_keysFor)
txt\<open>Fake\<close>
apply (auto dest!: usedI S2TTP_sender analz_subset_parts [THEN subsetD]) 
done

text\<open>The key determines the sender, recipient and protocol options.\<close>
lemma Key_unique:
      "[|Says S R
           \<lbrace>Agent S, Agent TTP, Crypt K (Number m), Number AO,
             Number cleartext, Nonce q,
             Crypt (pubEK TTP) \<lbrace>Agent S, Number AO, Key K, Agent R, hs\<rbrace>\<rbrace>
          \<in> set evs;
         Says S' R'
           \<lbrace>Agent S', Agent TTP, Crypt K (Number m'), Number AO',
             Number cleartext', Nonce q',
             Crypt (pubEK TTP) \<lbrace>Agent S', Number AO', Key K, Agent R', hs'\<rbrace>\<rbrace>
          \<in> set evs;
         Key K \<notin> analz (spies evs);
         evs \<in> certified_mail|]
       ==> R' = R \<and> S' = S \<and> AO' = AO \<and> hs' = hs"
by (rule Key_unique_lemma, assumption+)


subsection\<open>The Guarantees for Sender and Recipient\<close>

text\<open>A Sender's guarantee:
      If Spy gets the key then \<^term>\<open>R\<close> is bad and \<^term>\<open>S\<close> moreover
      gets his return receipt (and therefore has no grounds for complaint).\<close>
theorem S_fairness_bad_R:
      "[|Says S R \<lbrace>Agent S, Agent TTP, Crypt K (Number m), Number AO, 
                     Number cleartext, Nonce q, S2TTP\<rbrace> \<in> set evs;
         S2TTP = Crypt (pubEK TTP) \<lbrace>Agent S, Number AO, Key K, Agent R, hs\<rbrace>;
         Key K \<in> analz (spies evs);
         evs \<in> certified_mail;
         S\<noteq>Spy|]
      ==> R \<in> bad \<and> Gets S (Crypt (priSK TTP) S2TTP) \<in> set evs"
apply (erule rev_mp)
apply (erule ssubst)
apply (erule rev_mp)
apply (erule certified_mail.induct, simp_all)
txt\<open>Fake\<close>
apply spy_analz
txt\<open>Fake SSL\<close>
apply spy_analz
txt\<open>Message 3\<close>
apply (frule_tac hr_form, assumption)
apply (elim disjE exE) 
apply (simp_all add: synth_analz_insert_eq  
                     subset_trans [OF _ subset_insertI]
                     subset_trans [OF _ Un_upper2] 
                del: image_insert image_Un add: analz_image_freshK_simps) 
apply (simp_all add: symKey_neq_priEK analz_insert_freshK)
apply (blast dest: Notes_SSL_imp_used S2TTP_sender Key_unique)+
done

text\<open>Confidentially for the symmetric key\<close>
theorem Spy_not_see_encrypted_key:
      "[|Says S R \<lbrace>Agent S, Agent TTP, Crypt K (Number m), Number AO, 
                     Number cleartext, Nonce q, S2TTP\<rbrace> \<in> set evs;
         S2TTP = Crypt (pubEK TTP) \<lbrace>Agent S, Number AO, Key K, Agent R, hs\<rbrace>;
         evs \<in> certified_mail;
         S\<noteq>Spy; R \<notin> bad|]
      ==> Key K \<notin> analz(spies evs)"
by (blast dest: S_fairness_bad_R) 


text\<open>Agent \<^term>\<open>R\<close>, who may be the Spy, doesn't receive the key
 until \<^term>\<open>S\<close> has access to the return receipt.\<close> 
theorem S_guarantee:
     "[|Says S R \<lbrace>Agent S, Agent TTP, Crypt K (Number m), Number AO, 
                    Number cleartext, Nonce q, S2TTP\<rbrace> \<in> set evs;
        S2TTP = Crypt (pubEK TTP) \<lbrace>Agent S, Number AO, Key K, Agent R, hs\<rbrace>;
        Notes R \<lbrace>Agent TTP, Agent R, Key K, hs\<rbrace> \<in> set evs;
        S\<noteq>Spy;  evs \<in> certified_mail|]
     ==> Gets S (Crypt (priSK TTP) S2TTP) \<in> set evs"
apply (erule rev_mp)
apply (erule ssubst)
apply (erule rev_mp)
apply (erule certified_mail.induct, simp_all)
txt\<open>Message 1\<close>
apply (blast dest: Notes_imp_used) 
txt\<open>Message 3\<close>
apply (blast dest: Notes_SSL_imp_used S2TTP_sender Key_unique S_fairness_bad_R) 
done


text\<open>If \<^term>\<open>R\<close> sends message 2, and a delivery certificate exists, 
 then \<^term>\<open>R\<close> receives the necessary key.  This result is also important
 to \<^term>\<open>S\<close>, as it confirms the validity of the return receipt.\<close>
theorem RR_validity:
  "[|Crypt (priSK TTP) S2TTP \<in> used evs;
     S2TTP = Crypt (pubEK TTP)
               \<lbrace>Agent S, Number AO, Key K, Agent R, 
                 Hash \<lbrace>Number cleartext, Nonce q, r, em\<rbrace>\<rbrace>;
     hr = Hash \<lbrace>Number cleartext, Nonce q, r, em\<rbrace>;
     R\<noteq>Spy;  evs \<in> certified_mail|]
  ==> Notes R \<lbrace>Agent TTP, Agent R, Key K, hr\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule ssubst)
apply (erule ssubst)
apply (erule certified_mail.induct, simp_all)
txt\<open>Fake\<close> 
apply (blast dest: Fake_parts_sing [THEN subsetD]
             dest!: analz_subset_parts [THEN subsetD])  
txt\<open>Fake SSL\<close>
apply (blast dest: Fake_parts_sing [THEN subsetD]
            dest!: analz_subset_parts [THEN subsetD])  
txt\<open>Message 2\<close>
apply (drule CM2_S2TTP_parts_knows_Spy, assumption)
apply (force dest: parts_cut)
txt\<open>Message 3\<close>
apply (frule_tac hr_form, assumption)
apply (elim disjE exE, simp_all) 
apply (blast dest: Fake_parts_sing [THEN subsetD]
             dest!: analz_subset_parts [THEN subsetD]) 
done

end
