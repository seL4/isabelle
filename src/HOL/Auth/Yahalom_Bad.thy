(*  Title:      HOL/Auth/Yahalom_Bad.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

section\<open>The Yahalom Protocol: A Flawed Version\<close>

theory Yahalom_Bad imports Public begin

text\<open>
Demonstrates of why Oops is necessary.  This protocol can be attacked because
it doesn't keep NB secret, but without Oops it can be "verified" anyway.
The issues are discussed in lcp's LICS 2000 invited lecture.
\<close>

inductive_set yahalom :: "event list set"
  where
         (*Initial trace is empty*)
   Nil:  "[] \<in> yahalom"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
 | Fake: "[| evsf \<in> yahalom;  X \<in> synth (analz (knows Spy evsf)) |]
          ==> Says Spy B X  # evsf \<in> yahalom"

         (*A message that has been sent can be received by the
           intended recipient.*)
 | Reception: "[| evsr \<in> yahalom;  Says A B X \<in> set evsr |]
               ==> Gets B X # evsr \<in> yahalom"

         (*Alice initiates a protocol run*)
 | YM1:  "[| evs1 \<in> yahalom;  Nonce NA \<notin> used evs1 |]
          ==> Says A B \<lbrace>Agent A, Nonce NA\<rbrace> # evs1 \<in> yahalom"

         (*Bob's response to Alice's message.*)
 | YM2:  "[| evs2 \<in> yahalom;  Nonce NB \<notin> used evs2;
             Gets B \<lbrace>Agent A, Nonce NA\<rbrace> \<in> set evs2 |]
          ==> Says B Server
                  \<lbrace>Agent B, Nonce NB, Crypt (shrK B) \<lbrace>Agent A, Nonce NA\<rbrace>\<rbrace>
                # evs2 \<in> yahalom"

         (*The Server receives Bob's message.  He responds by sending a
            new session key to Alice, with a packet for forwarding to Bob.*)
 | YM3:  "[| evs3 \<in> yahalom;  Key KAB \<notin> used evs3;  KAB \<in> symKeys;
             Gets Server
                  \<lbrace>Agent B, Nonce NB, Crypt (shrK B) \<lbrace>Agent A, Nonce NA\<rbrace>\<rbrace>
               \<in> set evs3 |]
          ==> Says Server A
                   \<lbrace>Crypt (shrK A) \<lbrace>Agent B, Key KAB, Nonce NA, Nonce NB\<rbrace>,
                     Crypt (shrK B) \<lbrace>Agent A, Key KAB\<rbrace>\<rbrace>
                # evs3 \<in> yahalom"

         (*Alice receives the Server's (?) message, checks her Nonce, and
           uses the new session key to send Bob his Nonce.  The premise
           A \<noteq> Server is needed to prove Says_Server_not_range.*)
 | YM4:  "[| evs4 \<in> yahalom;  A \<noteq> Server;  K \<in> symKeys;
             Gets A \<lbrace>Crypt(shrK A) \<lbrace>Agent B, Key K, Nonce NA, Nonce NB\<rbrace>, X\<rbrace>
                \<in> set evs4;
             Says A B \<lbrace>Agent A, Nonce NA\<rbrace> \<in> set evs4 |]
          ==> Says A B \<lbrace>X, Crypt K (Nonce NB)\<rbrace> # evs4 \<in> yahalom"


declare Says_imp_knows_Spy [THEN analz.Inj, dest]
declare parts.Body  [dest]
declare Fake_parts_insert_in_Un  [dest]
declare analz_into_parts [dest]


text\<open>A "possibility property": there are traces that reach the end\<close>
lemma "[| A \<noteq> Server; Key K \<notin> used []; K \<in> symKeys |] 
       ==> \<exists>X NB. \<exists>evs \<in> yahalom.
              Says A B \<lbrace>X, Crypt K (Nonce NB)\<rbrace> \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] yahalom.Nil
                    [THEN yahalom.YM1, THEN yahalom.Reception,
                     THEN yahalom.YM2, THEN yahalom.Reception,
                     THEN yahalom.YM3, THEN yahalom.Reception,
                     THEN yahalom.YM4])
apply (possibility, simp add: used_Cons) 
done

subsection\<open>Regularity Lemmas for Yahalom\<close>

lemma Gets_imp_Says:
     "[| Gets B X \<in> set evs; evs \<in> yahalom |] ==> \<exists>A. Says A B X \<in> set evs"
by (erule rev_mp, erule yahalom.induct, auto)

(*Must be proved separately for each protocol*)
lemma Gets_imp_knows_Spy:
     "[| Gets B X \<in> set evs; evs \<in> yahalom |]  ==> X \<in> knows Spy evs"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)

declare Gets_imp_knows_Spy [THEN analz.Inj, dest]


subsection\<open>For reasoning about the encrypted portion of messages\<close>

text\<open>Lets us treat YM4 using a similar argument as for the Fake case.\<close>
lemma YM4_analz_knows_Spy:
     "[| Gets A \<lbrace>Crypt (shrK A) Y, X\<rbrace> \<in> set evs;  evs \<in> yahalom |]
      ==> X \<in> analz (knows Spy evs)"
by blast

lemmas YM4_parts_knows_Spy =
       YM4_analz_knows_Spy [THEN analz_into_parts]


text\<open>Theorems of the form @{term "X \<notin> parts (knows Spy evs)"} imply 
            that NOBODY sends messages containing X!\<close>

text\<open>Spy never sees a good agent's shared key!\<close>
lemma Spy_see_shrK [simp]:
     "evs \<in> yahalom ==> (Key (shrK A) \<in> parts (knows Spy evs)) = (A \<in> bad)"
apply (erule yahalom.induct, force,
       drule_tac [6] YM4_parts_knows_Spy, simp_all, blast+)
done

lemma Spy_analz_shrK [simp]:
     "evs \<in> yahalom ==> (Key (shrK A) \<in> analz (knows Spy evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "[|Key (shrK A) \<in> parts (knows Spy evs);  evs \<in> yahalom|] ==> A \<in> bad"
by (blast dest: Spy_see_shrK)

text\<open>Nobody can have used non-existent keys!
    Needed to apply \<open>analz_insert_Key\<close>\<close>
lemma new_keys_not_used [simp]:
    "[|Key K \<notin> used evs; K \<in> symKeys; evs \<in> yahalom|]
     ==> K \<notin> keysFor (parts (spies evs))"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt\<open>Fake\<close>
apply (force dest!: keysFor_parts_insert, auto)
done


subsection\<open>Secrecy Theorems\<close>

(****
 The following is to prove theorems of the form

  Key K \<in> analz (insert (Key KAB) (knows Spy evs)) ==>
  Key K \<in> analz (knows Spy evs)

 A more general formula must be proved inductively.
****)

subsection\<open>Session keys are not used to encrypt other session keys\<close>

lemma analz_image_freshK [rule_format]:
 "evs \<in> yahalom ==>
   \<forall>K KK. KK \<subseteq> - (range shrK) \<longrightarrow>
          (Key K \<in> analz (Key`KK \<union> (knows Spy evs))) =
          (K \<in> KK | Key K \<in> analz (knows Spy evs))"
by (erule yahalom.induct, 
    drule_tac [7] YM4_analz_knows_Spy, analz_freshK, spy_analz, blast) 

lemma analz_insert_freshK:
     "[| evs \<in> yahalom;  KAB \<notin> range shrK |] ==>
      (Key K \<in> analz (insert (Key KAB) (knows Spy evs))) =
      (K = KAB | Key K \<in> analz (knows Spy evs))"
by (simp only: analz_image_freshK analz_image_freshK_simps)


text\<open>The Key K uniquely identifies the Server's  message.\<close>
lemma unique_session_keys:
     "[| Says Server A
          \<lbrace>Crypt (shrK A) \<lbrace>Agent B, Key K, na, nb\<rbrace>, X\<rbrace> \<in> set evs;
        Says Server A'
          \<lbrace>Crypt (shrK A') \<lbrace>Agent B', Key K, na', nb'\<rbrace>, X'\<rbrace> \<in> set evs;
        evs \<in> yahalom |]
     ==> A=A' \<and> B=B' \<and> na=na' \<and> nb=nb'"
apply (erule rev_mp, erule rev_mp)
apply (erule yahalom.induct, simp_all)
txt\<open>YM3, by freshness, and YM4\<close>
apply blast+
done


text\<open>Crucial secrecy property: Spy does not see the keys sent in msg YM3\<close>
lemma secrecy_lemma:
     "[| A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Says Server A
            \<lbrace>Crypt (shrK A) \<lbrace>Agent B, Key K, na, nb\<rbrace>,
              Crypt (shrK B) \<lbrace>Agent A, Key K\<rbrace>\<rbrace>
           \<in> set evs \<longrightarrow>
          Key K \<notin> analz (knows Spy evs)"
apply (erule yahalom.induct, force, drule_tac [6] YM4_analz_knows_Spy)
apply (simp_all add: pushes analz_insert_eq analz_insert_freshK, spy_analz)  (*Fake*)
apply (blast dest: unique_session_keys)  (*YM3*)
done

text\<open>Final version\<close>
lemma Spy_not_see_encrypted_key:
     "[| Says Server A
            \<lbrace>Crypt (shrK A) \<lbrace>Agent B, Key K, na, nb\<rbrace>,
              Crypt (shrK B) \<lbrace>Agent A, Key K\<rbrace>\<rbrace>
           \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest: secrecy_lemma)


subsection\<open>Security Guarantee for A upon receiving YM3\<close>

text\<open>If the encrypted message appears then it originated with the Server\<close>
lemma A_trusts_YM3:
     "[| Crypt (shrK A) \<lbrace>Agent B, Key K, na, nb\<rbrace> \<in> parts (knows Spy evs);
         A \<notin> bad;  evs \<in> yahalom |]
       ==> Says Server A
            \<lbrace>Crypt (shrK A) \<lbrace>Agent B, Key K, na, nb\<rbrace>,
              Crypt (shrK B) \<lbrace>Agent A, Key K\<rbrace>\<rbrace>
           \<in> set evs"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt\<open>Fake, YM3\<close>
apply blast+
done

text\<open>The obvious combination of \<open>A_trusts_YM3\<close> with
  \<open>Spy_not_see_encrypted_key\<close>\<close>
lemma A_gets_good_key:
     "[| Crypt (shrK A) \<lbrace>Agent B, Key K, na, nb\<rbrace> \<in> parts (knows Spy evs);
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: A_trusts_YM3 Spy_not_see_encrypted_key)

subsection\<open>Security Guarantees for B upon receiving YM4\<close>

text\<open>B knows, by the first part of A's message, that the Server distributed
  the key for A and B.  But this part says nothing about nonces.\<close>
lemma B_trusts_YM4_shrK:
     "[| Crypt (shrK B) \<lbrace>Agent A, Key K\<rbrace> \<in> parts (knows Spy evs);
         B \<notin> bad;  evs \<in> yahalom |]
      ==> \<exists>NA NB. Says Server A
                      \<lbrace>Crypt (shrK A) \<lbrace>Agent B, Key K, Nonce NA, Nonce NB\<rbrace>,
                        Crypt (shrK B) \<lbrace>Agent A, Key K\<rbrace>\<rbrace>
                     \<in> set evs"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt\<open>Fake, YM3\<close>
apply blast+
done

subsection\<open>The Flaw in the Model\<close>

text\<open>Up to now, the reasoning is similar to standard Yahalom.  Now the
    doubtful reasoning occurs.  We should not be assuming that an unknown
    key is secure, but the model allows us to: there is no Oops rule to
    let session keys become compromised.\<close>

text\<open>B knows, by the second part of A's message, that the Server distributed
  the key quoting nonce NB.  This part says nothing about agent names.
  Secrecy of K is assumed; the valid Yahalom proof uses (and later proves)
  the secrecy of NB.\<close>
lemma B_trusts_YM4_newK [rule_format]:
     "[|Key K \<notin> analz (knows Spy evs);  evs \<in> yahalom|]
      ==> Crypt K (Nonce NB) \<in> parts (knows Spy evs) \<longrightarrow>
          (\<exists>A B NA. Says Server A
                      \<lbrace>Crypt (shrK A) \<lbrace>Agent B, Key K,
                                Nonce NA, Nonce NB\<rbrace>,
                        Crypt (shrK B) \<lbrace>Agent A, Key K\<rbrace>\<rbrace>
                     \<in> set evs)"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy)
apply (analz_mono_contra, simp_all)
txt\<open>Fake\<close>
apply blast
txt\<open>YM3\<close>
apply blast
txt\<open>A is uncompromised because NB is secure
  A's certificate guarantees the existence of the Server message\<close>
apply (blast dest!: Gets_imp_Says Crypt_Spy_analz_bad
             dest: Says_imp_spies
                   parts.Inj [THEN parts.Fst, THEN A_trusts_YM3])
done


text\<open>B's session key guarantee from YM4.  The two certificates contribute to a
  single conclusion about the Server's message.\<close>
lemma B_trusts_YM4:
     "[| Gets B \<lbrace>Crypt (shrK B) \<lbrace>Agent A, Key K\<rbrace>,
                  Crypt K (Nonce NB)\<rbrace> \<in> set evs;
         Says B Server
           \<lbrace>Agent B, Nonce NB, Crypt (shrK B) \<lbrace>Agent A, Nonce NA\<rbrace>\<rbrace>
           \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
       ==> \<exists>na nb. Says Server A
                   \<lbrace>Crypt (shrK A) \<lbrace>Agent B, Key K, na, nb\<rbrace>,
                     Crypt (shrK B) \<lbrace>Agent A, Key K\<rbrace>\<rbrace>
             \<in> set evs"
by (blast dest: B_trusts_YM4_newK B_trusts_YM4_shrK Spy_not_see_encrypted_key
                unique_session_keys)


text\<open>The obvious combination of \<open>B_trusts_YM4\<close> with 
  \<open>Spy_not_see_encrypted_key\<close>\<close>
lemma B_gets_good_key:
     "[| Gets B \<lbrace>Crypt (shrK B) \<lbrace>Agent A, Key K\<rbrace>,
                  Crypt K (Nonce NB)\<rbrace> \<in> set evs;
         Says B Server
           \<lbrace>Agent B, Nonce NB, Crypt (shrK B) \<lbrace>Agent A, Nonce NA\<rbrace>\<rbrace>
           \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: B_trusts_YM4 Spy_not_see_encrypted_key)


(*** Authenticating B to A: these proofs are not considered.
     They are irrelevant to showing the need for Oops. ***)


(*** Authenticating A to B using the certificate Crypt K (Nonce NB) ***)

text\<open>Assuming the session key is secure, if both certificates are present then
  A has said NB.  We can't be sure about the rest of A's message, but only
  NB matters for freshness.\<close>
lemma A_Said_YM3_lemma [rule_format]:
     "evs \<in> yahalom
      ==> Key K \<notin> analz (knows Spy evs) \<longrightarrow>
          Crypt K (Nonce NB) \<in> parts (knows Spy evs) \<longrightarrow>
          Crypt (shrK B) \<lbrace>Agent A, Key K\<rbrace> \<in> parts (knows Spy evs) \<longrightarrow>
          B \<notin> bad \<longrightarrow>
          (\<exists>X. Says A B \<lbrace>X, Crypt K (Nonce NB)\<rbrace> \<in> set evs)"
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy)
apply (analz_mono_contra, simp_all)
txt\<open>Fake\<close>
apply blast
txt\<open>YM3: by \<open>new_keys_not_used\<close>, the message
   @{term "Crypt K (Nonce NB)"} could not exist\<close>
apply (force dest!: Crypt_imp_keysFor)
txt\<open>YM4: was @{term "Crypt K (Nonce NB)"} the very last message?
    If not, use the induction hypothesis\<close>
apply (simp add: ex_disj_distrib)
txt\<open>yes: apply unicity of session keys\<close>
apply (blast dest!: Gets_imp_Says A_trusts_YM3 B_trusts_YM4_shrK
                    Crypt_Spy_analz_bad
             dest: Says_imp_knows_Spy [THEN parts.Inj] unique_session_keys)
done

text\<open>If B receives YM4 then A has used nonce NB (and therefore is alive).
  Moreover, A associates K with NB (thus is talking about the same run).
  Other premises guarantee secrecy of K.\<close>
lemma YM4_imp_A_Said_YM3 [rule_format]:
     "[| Gets B \<lbrace>Crypt (shrK B) \<lbrace>Agent A, Key K\<rbrace>,
                  Crypt K (Nonce NB)\<rbrace> \<in> set evs;
         Says B Server
           \<lbrace>Agent B, Nonce NB, Crypt (shrK B) \<lbrace>Agent A, Nonce NA\<rbrace>\<rbrace>
           \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> \<exists>X. Says A B \<lbrace>X, Crypt K (Nonce NB)\<rbrace> \<in> set evs"
by (blast intro!: A_Said_YM3_lemma
          dest: Spy_not_see_encrypted_key B_trusts_YM4 Gets_imp_Says)

end
