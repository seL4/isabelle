(*  Title:      HOL/Auth/CertifiedEmail
    ID:         $Id$
    Author:     Giampaolo Bella, Christiano Longo and Lawrence C Paulson
*)

header{*The Certified Electronic Mail Protocol by Abadi et al.*}

theory CertifiedEmail = Public:

syntax
  TTP        :: agent
  RPwd       :: "agent => key"

translations
  "TTP"   == "Server "
  "RPwd"  == "shrK "

 
(*FIXME: the four options should be represented by pairs of 0 or 1.
  Right now only BothAuth is modelled.*)
consts
  NoAuth   :: nat
  TTPAuth  :: nat
  SAuth    :: nat
  BothAuth :: nat

text{*We formalize a fixed way of computing responses.  Could be better.*}
constdefs
  "response"    :: "agent => agent => nat => msg"
   "response S R q == Hash {|Agent S, Key (shrK R), Nonce q|}"


consts  certified_mail   :: "event list set"
inductive "certified_mail"
  intros 

Nil: --{*The empty trace*}
     "[] \<in> certified_mail"

Fake: --{*The Spy may say anything he can say.  The sender field is correct,
          but agents don't use that information.*}
      "[| evsf \<in> certified_mail; X \<in> synth(analz(spies evsf))|] 
       ==> Says Spy B X # evsf \<in> certified_mail"

FakeSSL: --{*The Spy may open SSL sessions with TTP, who is the only agent
    equipped with the necessary credentials to serve as an SSL server.*}
	 "[| evsfssl \<in> certified_mail; X \<in> synth(analz(spies evsfssl))|]
          ==> Notes TTP {|Agent Spy, Agent TTP, X|} # evsfssl \<in> certified_mail"

CM1: --{*The sender approaches the recipient.  The message is a number.*}
"[|evs1 \<in> certified_mail;
   Key K \<notin> used evs1;
   K \<in> symKeys;
   Nonce q \<notin> used evs1;
   hs = Hash {|Number cleartext, Nonce q, response S R q, Crypt K (Number m)|};
   S2TTP = Crypt (pubEK TTP) {|Agent S, Number BothAuth, Key K, Agent R, hs|}|]
 ==> Says S R {|Agent S, Agent TTP, Crypt K (Number m), Number BothAuth, 
                Number cleartext, Nonce q, S2TTP|} # evs1 
       \<in> certified_mail"

CM2: --{*The recipient records @{term S2TTP'} while transmitting it and her
     password to @{term TTP} over an SSL channel.*}
"[|evs2 \<in> certified_mail;
   Gets R {|Agent S, Agent TTP, em', Number BothAuth, Number cleartext', 
            Nonce q', S2TTP'|} \<in> set evs2;
   TTP \<noteq> R;  
   hr = Hash {|Number cleartext', Nonce q', response S R q', em'|} |]
 ==> 
  Notes TTP {|Agent R, Agent TTP, S2TTP', Key(RPwd R), hr|} # evs2
     \<in> certified_mail"

CM3: --{*@{term TTP} simultaneously reveals the key to the recipient and gives
         a receipt to the sender.  The SSL channel does not authenticate 
         the client (@{term R'}), but @{term TTP} accepts the message only 
         if the given password is that of the claimed sender, @{term R'}.
         He replies over the established SSL channel.*}
 "[|evs3 \<in> certified_mail;
    Notes TTP {|Agent R', Agent TTP, S2TTP'', Key(RPwd R'), hr'|} \<in> set evs3;
    S2TTP'' = Crypt (pubEK TTP) 
                     {|Agent S, Number BothAuth, Key k', Agent R', hs'|};
    TTP \<noteq> R';  hs' = hr';  k' \<in> symKeys|]
 ==> 
  Notes R' {|Agent TTP, Agent R', Key k', hr'|} # 
  Gets S (Crypt (priSK TTP) S2TTP'') # 
  Says TTP S (Crypt (priSK TTP) S2TTP'') # evs3 \<in> certified_mail"

Reception:
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
 "[|Gets R {|Agent A, Agent B, em, Number AO, Number cleartext, 
              Nonce q, S2TTP|} \<in> set evs;
    evs \<in> certified_mail|] 
  ==> S2TTP \<in> analz(spies evs)"
apply (drule Gets_imp_Says, simp) 
apply (blast dest: Says_imp_knows_Spy analz.Inj) 
done

lemmas CM2_S2TTP_parts_knows_Spy = 
    CM2_S2TTP_analz_knows_Spy [THEN analz_subset_parts [THEN subsetD]]

lemma hr_form_lemma [rule_format]:
 "evs \<in> certified_mail
  ==> hr \<notin> synth (analz (spies evs)) --> 
      (\<forall>S2TTP. Notes TTP {|Agent R, Agent TTP, S2TTP, pwd, hr|}
          \<in> set evs --> 
      (\<exists>clt q S em. hr = Hash {|Number clt, Nonce q, response S R q, em|}))"
apply (erule certified_mail.induct)
apply (synth_analz_mono_contra, simp_all, blast+)
done 

text{*Cannot strengthen the first disjunct to @{term "R\<noteq>Spy"} because
the fakessl rule allows Spy to spoof the sender's name.  Maybe can
strengthen the second disjunct with @{term "R\<noteq>Spy"}.*}
lemma hr_form:
 "[|Notes TTP {|Agent R, Agent TTP, S2TTP, pwd, hr|} \<in> set evs;
    evs \<in> certified_mail|]
  ==> hr \<in> synth (analz (spies evs)) | 
      (\<exists>clt q S em. hr = Hash {|Number clt, Nonce q, response S R q, em|})"
by (blast intro: hr_form_lemma) 

lemma Spy_dont_know_private_keys [dest!]:
    "[|Key (privateKey b A) \<in> parts (spies evs); evs \<in> certified_mail|]
     ==> A \<in> bad"
apply (erule rev_mp) 
apply (erule certified_mail.induct, simp_all)
txt{*Fake*}
apply (blast dest: Fake_parts_insert_in_Un); 
txt{*Message 1*}
apply blast  
txt{*Message 3*}
apply (frule_tac hr_form, assumption)
apply (elim disjE exE) 
apply (simp_all add: parts_insert2) 
 apply (force dest!: parts_insert_subset_Un [THEN [2] rev_subsetD] 
                     analz_subset_parts [THEN subsetD], blast) 
done

lemma Spy_know_private_keys_iff [simp]:
    "evs \<in> certified_mail
     ==> (Key (privateKey b A) \<in> parts (spies evs)) = (A \<in> bad)"
by (blast intro: elim:); 

lemma Spy_dont_know_TTPKey_parts [simp]:
     "evs \<in> certified_mail ==> Key (privateKey b TTP) \<notin> parts(spies evs)" 
by simp

lemma Spy_dont_know_TTPKey_analz [simp]:
     "evs \<in> certified_mail ==> Key (privateKey b TTP) \<notin> analz(spies evs)"
by auto

text{*Thus, prove any goal that assumes that @{term Spy} knows a private key
belonging to @{term TTP}*}
declare Spy_dont_know_TTPKey_parts [THEN [2] rev_notE, elim!]


lemma CM3_k_parts_knows_Spy:
 "[| evs \<in> certified_mail;
     Notes TTP {|Agent A, Agent TTP,
                 Crypt (pubEK TTP) {|Agent S, Number AO, Key K, 
                 Agent R, hs|}, Key (RPwd R), hs|} \<in> set evs|]
  ==> Key K \<in> parts(spies evs)"
apply (rotate_tac 1)
apply (erule rev_mp)
apply (erule certified_mail.induct, simp_all)
   apply (blast  intro:parts_insertI)
txt{*Fake SSL*}
apply (blast dest: parts.Body) 
txt{*Message 2*}
apply (blast dest!: Gets_imp_Says elim!: knows_Spy_partsEs)
txt{*Message 3*}
apply (frule_tac hr_form, assumption)
apply (elim disjE exE) 
apply (simp_all add: parts_insert2)
apply (blast intro: subsetD [OF parts_mono [OF Set.subset_insertI]])  
done

lemma Spy_dont_know_RPwd [rule_format]:
    "evs \<in> certified_mail ==> Key (RPwd A) \<in> parts(spies evs) --> A \<in> bad"
apply (erule certified_mail.induct, simp_all) 
txt{*Fake*}
apply (blast dest: Fake_parts_insert_in_Un); 
txt{*Message 1*}
apply blast  
txt{*Message 3*}
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
by (auto simp add: Spy_dont_know_RPwd [OF _ analz_subset_parts [THEN subsetD]])


text{*Unused, but a guarantee of sorts*}
theorem CertAutenticity:
     "[|Crypt (priSK TTP) X \<in> parts (spies evs); evs \<in> certified_mail|] 
      ==> \<exists>A. Says TTP A (Crypt (priSK TTP) X) \<in> set evs"
apply (erule rev_mp)
apply (erule certified_mail.induct, simp_all) 
txt{*Fake*}
apply (blast dest: Spy_dont_know_private_keys Fake_parts_insert_in_Un)
txt{*Message 1*}
apply blast 
txt{*Message 3*}
apply (frule_tac hr_form, assumption)
apply (elim disjE exE) 
apply (simp_all add: parts_insert2 parts_insert_knows_A) 
 apply (blast dest!: Fake_parts_sing_imp_Un)
apply (blast intro: elim:);
done


subsection{*Proving Confidentiality Results*}

lemma analz_image_freshK [rule_format]:
 "evs \<in> certified_mail ==>
   \<forall>K KK. invKey (pubEK TTP) \<notin> KK -->
          (Key K \<in> analz (Key`KK Un (spies evs))) =
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

text{*@{term S2TTP} must have originated from a valid sender
    provided @{term K} is secure.  Proof is surprisingly hard.*}

lemma Notes_SSL_imp_used:
     "[|Notes B {|Agent A, Agent B, X|} \<in> set evs|] ==> X \<in> used evs"
by (blast dest!: Notes_imp_used)


(*The weaker version, replacing "used evs" by "parts (spies evs)", 
   isn't inductive: message 3 case can't be proved *)
lemma S2TTP_sender_lemma [rule_format]:
 "evs \<in> certified_mail ==>
    Key K \<notin> analz (spies evs) -->
    (\<forall>AO. Crypt (pubEK TTP)
	   {|Agent S, Number AO, Key K, Agent R, hs|} \<in> used evs -->
    (\<exists>m ctxt q. 
        hs = Hash{|Number ctxt, Nonce q, response S R q, Crypt K (Number m)|} &
	Says S R
	   {|Agent S, Agent TTP, Crypt K (Number m), Number AO,
	     Number ctxt, Nonce q,
	     Crypt (pubEK TTP)
	      {|Agent S, Number AO, Key K, Agent R, hs |}|} \<in> set evs))" 
apply (erule certified_mail.induct, analz_mono_contra)
apply (drule_tac [5] CM2_S2TTP_parts_knows_Spy, simp)
apply (simp add: used_Nil Crypt_notin_initState, simp_all)
txt{*Fake*}
apply (blast dest: Fake_parts_sing [THEN subsetD]
             dest!: analz_subset_parts [THEN subsetD])  
txt{*Fake SSL*}
apply (blast dest: Fake_parts_sing [THEN subsetD]
             dest: analz_subset_parts [THEN subsetD])  
txt{*Message 1*}
apply (clarsimp, blast)
txt{*Message 2*}
apply (simp add: parts_insert2, clarify) 
apply (drule parts_cut, assumption, simp) 
apply (blast intro: usedI) 
txt{*Message 3*} 
apply (blast dest: Notes_SSL_imp_used used_parts_subset_parts) 
done 

lemma S2TTP_sender:
 "[|Crypt (pubEK TTP) {|Agent S, Number AO, Key K, Agent R, hs|} \<in> used evs;
    Key K \<notin> analz (spies evs);
    evs \<in> certified_mail|]
  ==> \<exists>m ctxt q. 
        hs = Hash{|Number ctxt, Nonce q, response S R q, Crypt K (Number m)|} &
	Says S R
	   {|Agent S, Agent TTP, Crypt K (Number m), Number AO,
	     Number ctxt, Nonce q,
	     Crypt (pubEK TTP)
	      {|Agent S, Number AO, Key K, Agent R, hs |}|} \<in> set evs" 
by (blast intro: S2TTP_sender_lemma) 


text{*Nobody can have used non-existent keys!*}
lemma new_keys_not_used [rule_format, simp]:
    "[|Key K \<notin> used evs; K \<in> symKeys; evs \<in> certified_mail|]
     ==> K \<notin> keysFor (parts (spies evs))"
apply (erule rev_mp) 
apply (erule certified_mail.induct, simp_all) 
txt{*Fake*}
apply (force dest!: keysFor_parts_insert) 
txt{*Message 1*}
apply blast 
txt{*Message 3*}
apply (frule CM3_k_parts_knows_Spy, assumption)
apply (frule_tac hr_form, assumption) 
apply (force dest!: keysFor_parts_insert)
done


text{*Less easy to prove @{term "m'=m"}.  Maybe needs a separate unicity
theorem for ciphertexts of the form @{term "Crypt K (Number m)"}, 
where @{term K} is secure.*}
lemma Key_unique_lemma [rule_format]:
     "evs \<in> certified_mail ==>
       Key K \<notin> analz (spies evs) -->
       (\<forall>m cleartext q hs.
        Says S R
           {|Agent S, Agent TTP, Crypt K (Number m), Number AO,
             Number cleartext, Nonce q,
             Crypt (pubEK TTP) {|Agent S, Number AO, Key K, Agent R, hs|}|}
          \<in> set evs -->
       (\<forall>m' cleartext' q' hs'.
       Says S' R'
           {|Agent S', Agent TTP, Crypt K (Number m'), Number AO',
             Number cleartext', Nonce q',
             Crypt (pubEK TTP) {|Agent S', Number AO', Key K, Agent R', hs'|}|}
          \<in> set evs --> R' = R & S' = S & AO' = AO & hs' = hs))" 
apply (erule certified_mail.induct, analz_mono_contra, simp_all)
 prefer 2
 txt{*Message 1*}
 apply (blast dest!: Says_imp_knows_Spy [THEN parts.Inj] new_keys_not_used Crypt_imp_keysFor)
txt{*Fake*}
apply (auto dest!: usedI S2TTP_sender analz_subset_parts [THEN subsetD]) 
done

text{*The key determines the sender, recipient and protocol options.*}
lemma Key_unique:
      "[|Says S R
           {|Agent S, Agent TTP, Crypt K (Number m), Number AO,
             Number cleartext, Nonce q,
             Crypt (pubEK TTP) {|Agent S, Number AO, Key K, Agent R, hs|}|}
          \<in> set evs;
         Says S' R'
           {|Agent S', Agent TTP, Crypt K (Number m'), Number AO',
             Number cleartext', Nonce q',
             Crypt (pubEK TTP) {|Agent S', Number AO', Key K, Agent R', hs'|}|}
          \<in> set evs;
         Key K \<notin> analz (spies evs);
         evs \<in> certified_mail|]
       ==> R' = R & S' = S & AO' = AO & hs' = hs"
by (rule Key_unique_lemma, assumption+)


subsection{*The Guarantees for Sender and Recipient*}

text{*A Sender's guarantee:
      If Spy gets the key then @{term R} is bad and @{term S} moreover
      gets his return receipt (and therefore has no grounds for complaint).*}
theorem Spy_see_encrypted_key_imp:
      "[|Says S R {|Agent S, Agent TTP, Crypt K (Number m), Number AO, 
                     Number cleartext, Nonce q, S2TTP|} \<in> set evs;
         S2TTP = Crypt (pubEK TTP) {|Agent S, Number AO, Key K, Agent R, hs|};
         Key K \<in> analz(spies evs);
	 evs \<in> certified_mail;
         S\<noteq>Spy|]
      ==> R \<in> bad & Gets S (Crypt (priSK TTP) S2TTP) \<in> set evs"
apply (erule rev_mp)
apply (erule ssubst)
apply (erule rev_mp)
apply (erule certified_mail.induct, simp_all)
txt{*Fake*}
apply spy_analz
txt{*Fake SSL*}
apply spy_analz
txt{*Message 3*}
apply (frule_tac hr_form, assumption)
apply (elim disjE exE) 
apply (simp_all add: synth_analz_insert_eq  
                     subset_trans [OF _ subset_insertI]
                     subset_trans [OF _ Un_upper2] 
                del: image_insert image_Un add: analz_image_freshK_simps) 
apply (simp_all add: symKey_neq_priEK analz_insert_freshK)
apply (blast dest: Notes_SSL_imp_used S2TTP_sender Key_unique)+
done

text{*Confidentially for the symmetric key*}
theorem Spy_not_see_encrypted_key:
      "[|Says S R {|Agent S, Agent TTP, Crypt K (Number m), Number AO, 
                     Number cleartext, Nonce q, S2TTP|} \<in> set evs;
         S2TTP = Crypt (pubEK TTP) {|Agent S, Number AO, Key K, Agent R, hs|};
	 evs \<in> certified_mail;
         S\<noteq>Spy; R \<notin> bad|]
      ==> Key K \<notin> analz(spies evs)"
by (blast dest: Spy_see_encrypted_key_imp) 


text{*Agent @{term R}, who may be the Spy, doesn't receive the key
 until @{term S} has access to the return receipt.*} 
theorem S_guarantee:
      "[|Says S R {|Agent S, Agent TTP, Crypt K (Number m), Number AO, 
                     Number cleartext, Nonce q, S2TTP|} \<in> set evs;
         S2TTP = Crypt (pubEK TTP) {|Agent S, Number AO, Key K, Agent R, hs|};
         Notes R {|Agent TTP, Agent R, Key K, hs|} \<in> set evs;
         S\<noteq>Spy;  evs \<in> certified_mail|]
      ==> Gets S (Crypt (priSK TTP) S2TTP) \<in> set evs"
apply (erule rev_mp)
apply (erule ssubst)
apply (erule rev_mp)
apply (erule certified_mail.induct, simp_all)
txt{*Message 1*}
apply (blast dest: Notes_imp_used) 
txt{*Message 3*} 
apply (blast dest: Notes_SSL_imp_used S2TTP_sender Key_unique 
                   Spy_see_encrypted_key_imp) 
done


text{*Recipient's guarantee: if @{term R} sends message 2, and
     a delivery certificate exists, then @{term R}
     receives the necessary key.*}
theorem R_guarantee:
  "[|Crypt (priSK TTP) S2TTP \<in> used evs;
     S2TTP = Crypt (pubEK TTP)
               {|Agent S, Number AO, Key K, Agent R, 
                 Hash {|Number cleartext, Nonce q, r, em|}|};
     hr = Hash {|Number cleartext, Nonce q, r, em|};
     R\<noteq>Spy;  evs \<in> certified_mail|]
  ==> Notes R {|Agent TTP, Agent R, Key K, hr|} \<in> set evs"
apply (erule rev_mp)
apply (erule ssubst)
apply (erule ssubst)
apply (erule certified_mail.induct, simp_all)
txt{*Fake*} 
apply (blast dest: Fake_parts_sing [THEN subsetD]
             dest!: analz_subset_parts [THEN subsetD])  
txt{*Fake SSL*}
apply (blast dest: Fake_parts_sing [THEN subsetD]
            dest!: analz_subset_parts [THEN subsetD])  
txt{*Message 2*}
apply (drule CM2_S2TTP_parts_knows_Spy, assumption)
apply (force dest: parts_cut)
txt{*Message 3*}
apply (frule_tac hr_form, assumption)
apply (elim disjE exE, simp_all) 
apply (blast dest: Fake_parts_sing [THEN subsetD]
             dest!: analz_subset_parts [THEN subsetD]) 
done

end
