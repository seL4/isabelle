(*  Title:      HOL/Auth/Yahalom2.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

section\<open>The Yahalom Protocol, Variant 2\<close>

theory Yahalom2 imports Public begin

text\<open>
This version trades encryption of NB for additional explicitness in YM3.
Also in YM3, care is taken to make the two certificates distinct.

From page 259 of
  Burrows, Abadi and Needham (1989).  A Logic of Authentication.
  Proc. Royal Soc. 426

This theory has the prototypical example of a secrecy relation, KeyCryptNonce.
\<close>

inductive_set yahalom :: "event list set"
  where
         (*Initial trace is empty*)
   Nil:  "[] \<in> yahalom"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
 | Fake: "\<lbrakk>evsf \<in> yahalom;  X \<in> synth (analz (knows Spy evsf))\<rbrakk>
          \<Longrightarrow> Says Spy B X  # evsf \<in> yahalom"

         (*A message that has been sent can be received by the
           intended recipient.*)
 | Reception: "\<lbrakk>evsr \<in> yahalom;  Says A B X \<in> set evsr\<rbrakk>
               \<Longrightarrow> Gets B X # evsr \<in> yahalom"

         (*Alice initiates a protocol run*)
 | YM1:  "\<lbrakk>evs1 \<in> yahalom;  Nonce NA \<notin> used evs1\<rbrakk>
          \<Longrightarrow> Says A B \<lbrace>Agent A, Nonce NA\<rbrace> # evs1 \<in> yahalom"

         (*Bob's response to Alice's message.*)
 | YM2:  "\<lbrakk>evs2 \<in> yahalom;  Nonce NB \<notin> used evs2;
             Gets B \<lbrace>Agent A, Nonce NA\<rbrace> \<in> set evs2\<rbrakk>
          \<Longrightarrow> Says B Server
                  \<lbrace>Agent B, Nonce NB, Crypt (shrK B) \<lbrace>Agent A, Nonce NA\<rbrace>\<rbrace>
                # evs2 \<in> yahalom"

         (*The Server receives Bob's message.  He responds by sending a
           new session key to Alice, with a certificate for forwarding to Bob.
           Both agents are quoted in the 2nd certificate to prevent attacks!*)
 | YM3:  "\<lbrakk>evs3 \<in> yahalom;  Key KAB \<notin> used evs3;
             Gets Server \<lbrace>Agent B, Nonce NB,
                           Crypt (shrK B) \<lbrace>Agent A, Nonce NA\<rbrace>\<rbrace>
               \<in> set evs3\<rbrakk>
          \<Longrightarrow> Says Server A
               \<lbrace>Nonce NB,
                 Crypt (shrK A) \<lbrace>Agent B, Key KAB, Nonce NA\<rbrace>,
                 Crypt (shrK B) \<lbrace>Agent A, Agent B, Key KAB, Nonce NB\<rbrace>\<rbrace>
                 # evs3 \<in> yahalom"

         (*Alice receives the Server's (?) message, checks her Nonce, and
           uses the new session key to send Bob his Nonce.*)
 | YM4:  "\<lbrakk>evs4 \<in> yahalom;
             Gets A \<lbrace>Nonce NB, Crypt (shrK A) \<lbrace>Agent B, Key K, Nonce NA\<rbrace>,
                      X\<rbrace>  \<in> set evs4;
             Says A B \<lbrace>Agent A, Nonce NA\<rbrace> \<in> set evs4\<rbrakk>
          \<Longrightarrow> Says A B \<lbrace>X, Crypt K (Nonce NB)\<rbrace> # evs4 \<in> yahalom"

         (*This message models possible leaks of session keys.  The nonces
           identify the protocol run.  Quoting Server here ensures they are
           correct. *)
 | Oops: "\<lbrakk>evso \<in> yahalom;
             Says Server A \<lbrace>Nonce NB,
                             Crypt (shrK A) \<lbrace>Agent B, Key K, Nonce NA\<rbrace>,
                             X\<rbrace>  \<in> set evso\<rbrakk>
          \<Longrightarrow> Notes Spy \<lbrace>Nonce NA, Nonce NB, Key K\<rbrace> # evso \<in> yahalom"


declare Says_imp_knows_Spy [THEN analz.Inj, dest]
declare parts.Body  [dest]
declare Fake_parts_insert_in_Un  [dest]
declare analz_into_parts [dest]

text\<open>A "possibility property": there are traces that reach the end\<close>
lemma "Key K \<notin> used []
       \<Longrightarrow> \<exists>X NB. \<exists>evs \<in> yahalom.
             Says A B \<lbrace>X, Crypt K (Nonce NB)\<rbrace> \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] yahalom.Nil
                    [THEN yahalom.YM1, THEN yahalom.Reception,
                     THEN yahalom.YM2, THEN yahalom.Reception,
                     THEN yahalom.YM3, THEN yahalom.Reception,
                     THEN yahalom.YM4])
apply (possibility, simp add: used_Cons)
done

lemma Gets_imp_Says:
     "\<lbrakk>Gets B X \<in> set evs; evs \<in> yahalom\<rbrakk> \<Longrightarrow> \<exists>A. Says A B X \<in> set evs"
by (erule rev_mp, erule yahalom.induct, auto)

text\<open>Must be proved separately for each protocol\<close>
lemma Gets_imp_knows_Spy:
     "\<lbrakk>Gets B X \<in> set evs; evs \<in> yahalom\<rbrakk>  \<Longrightarrow> X \<in> knows Spy evs"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)

declare Gets_imp_knows_Spy [THEN analz.Inj, dest]


subsection\<open>Inductive Proofs\<close>

text\<open>Result for reasoning about the encrypted portion of messages.
Lets us treat YM4 using a similar argument as for the Fake case.\<close>
lemma YM4_analz_knows_Spy:
     "\<lbrakk>Gets A \<lbrace>NB, Crypt (shrK A) Y, X\<rbrace> \<in> set evs;  evs \<in> yahalom\<rbrakk>
      \<Longrightarrow> X \<in> analz (knows Spy evs)"
by blast

lemmas YM4_parts_knows_Spy =
       YM4_analz_knows_Spy [THEN analz_into_parts]


(** Theorems of the form X \<notin> parts (knows Spy evs) imply that NOBODY
    sends messages containing X! **)

text\<open>Spy never sees a good agent's shared key!\<close>
lemma Spy_see_shrK [simp]:
     "evs \<in> yahalom \<Longrightarrow> (Key (shrK A) \<in> parts (knows Spy evs)) = (A \<in> bad)"
by (erule yahalom.induct, force,
    drule_tac [6] YM4_parts_knows_Spy, simp_all, blast+)

lemma Spy_analz_shrK [simp]:
     "evs \<in> yahalom \<Longrightarrow> (Key (shrK A) \<in> analz (knows Spy evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "\<lbrakk>Key (shrK A) \<in> parts (knows Spy evs);  evs \<in> yahalom\<rbrakk> \<Longrightarrow> A \<in> bad"
by (blast dest: Spy_see_shrK)

text\<open>Nobody can have used non-existent keys!  
    Needed to apply \<open>analz_insert_Key\<close>\<close>
lemma new_keys_not_used [simp]:
    "\<lbrakk>Key K \<notin> used evs; K \<in> symKeys; evs \<in> yahalom\<rbrakk>
     \<Longrightarrow> K \<notin> keysFor (parts (spies evs))"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
subgoal \<comment>\<open>Fake\<close> by (force dest!: keysFor_parts_insert)
subgoal \<comment>\<open>YM3 \<close>by blast
subgoal \<comment>\<open>YM4\<close> by (fastforce dest!: Gets_imp_knows_Spy [THEN parts.Inj])
done


text\<open>Describes the form of K when the Server sends this message.  Useful for
  Oops as well as main secrecy property.\<close>
lemma Says_Server_message_form:
     "\<lbrakk>Says Server A \<lbrace>nb', Crypt (shrK A) \<lbrace>Agent B, Key K, na\<rbrace>, X\<rbrace>
          \<in> set evs;  evs \<in> yahalom\<rbrakk>
      \<Longrightarrow> K \<notin> range shrK"
by (erule rev_mp, erule yahalom.induct, simp_all)


(****
 The following is to prove theorems of the form

          Key K \<in> analz (insert (Key KAB) (knows Spy evs)) \<Longrightarrow>
          Key K \<in> analz (knows Spy evs)

 A more general formula must be proved inductively.
****)

(** Session keys are not used to encrypt other session keys **)

lemma analz_image_freshK [rule_format]:
 "evs \<in> yahalom \<Longrightarrow>
   \<forall>K KK. KK <= - (range shrK) -->
          (Key K \<in> analz (Key`KK Un (knows Spy evs))) =
          (K \<in> KK | Key K \<in> analz (knows Spy evs))"
apply (erule yahalom.induct)
apply (frule_tac [8] Says_Server_message_form)
apply (drule_tac [7] YM4_analz_knows_Spy, analz_freshK, spy_analz, blast)
done

lemma analz_insert_freshK:
     "\<lbrakk>evs \<in> yahalom;  KAB \<notin> range shrK\<rbrakk> \<Longrightarrow>
      (Key K \<in> analz (insert (Key KAB) (knows Spy evs))) =
      (K = KAB | Key K \<in> analz (knows Spy evs))"
by (simp only: analz_image_freshK analz_image_freshK_simps)


text\<open>The Key K uniquely identifies the Server's  message\<close>
lemma unique_session_keys:
     "\<lbrakk>Says Server A
          \<lbrace>nb, Crypt (shrK A) \<lbrace>Agent B, Key K, na\<rbrace>, X\<rbrace> \<in> set evs;
        Says Server A'
          \<lbrace>nb', Crypt (shrK A') \<lbrace>Agent B', Key K, na'\<rbrace>, X'\<rbrace> \<in> set evs;
        evs \<in> yahalom\<rbrakk>
     \<Longrightarrow> A=A' & B=B' & na=na' & nb=nb'"
apply (erule rev_mp, erule rev_mp)
apply (erule yahalom.induct, simp_all)
txt\<open>YM3, by freshness\<close>
apply blast
done


subsection\<open>Crucial Secrecy Property: Spy Does Not See Key @{term KAB}\<close>

lemma secrecy_lemma:
     "\<lbrakk>A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom\<rbrakk>
      \<Longrightarrow> Says Server A
            \<lbrace>nb, Crypt (shrK A) \<lbrace>Agent B, Key K, na\<rbrace>,
                  Crypt (shrK B) \<lbrace>Agent A, Agent B, Key K, nb\<rbrace>\<rbrace>
           \<in> set evs -->
          Notes Spy \<lbrace>na, nb, Key K\<rbrace> \<notin> set evs -->
          Key K \<notin> analz (knows Spy evs)"
apply (erule yahalom.induct, force, frule_tac [7] Says_Server_message_form,
       drule_tac [6] YM4_analz_knows_Spy)
apply (simp_all add: pushes analz_insert_eq analz_insert_freshK, spy_analz)
apply (blast dest: unique_session_keys)+  (*YM3, Oops*)
done


text\<open>Final version\<close>
lemma Spy_not_see_encrypted_key:
     "\<lbrakk>Says Server A
            \<lbrace>nb, Crypt (shrK A) \<lbrace>Agent B, Key K, na\<rbrace>,
                  Crypt (shrK B) \<lbrace>Agent A, Agent B, Key K, nb\<rbrace>\<rbrace>
         \<in> set evs;
         Notes Spy \<lbrace>na, nb, Key K\<rbrace> \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom\<rbrakk>
      \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
by (blast dest: secrecy_lemma Says_Server_message_form)



text\<open>This form is an immediate consequence of the previous result.  It is
similar to the assertions established by other methods.  It is equivalent
to the previous result in that the Spy already has @{term analz} and
@{term synth} at his disposal.  However, the conclusion
@{term "Key K \<notin> knows Spy evs"} appears not to be inductive: all the cases
other than Fake are trivial, while Fake requires
@{term "Key K \<notin> analz (knows Spy evs)"}.\<close>
lemma Spy_not_know_encrypted_key:
     "\<lbrakk>Says Server A
            \<lbrace>nb, Crypt (shrK A) \<lbrace>Agent B, Key K, na\<rbrace>,
                  Crypt (shrK B) \<lbrace>Agent A, Agent B, Key K, nb\<rbrace>\<rbrace>
         \<in> set evs;
         Notes Spy \<lbrace>na, nb, Key K\<rbrace> \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom\<rbrakk>
      \<Longrightarrow> Key K \<notin> knows Spy evs"
by (blast dest: Spy_not_see_encrypted_key)


subsection\<open>Security Guarantee for A upon receiving YM3\<close>

text\<open>If the encrypted message appears then it originated with the Server.
  May now apply \<open>Spy_not_see_encrypted_key\<close>, subject to its conditions.\<close>
lemma A_trusts_YM3:
     "\<lbrakk>Crypt (shrK A) \<lbrace>Agent B, Key K, na\<rbrace> \<in> parts (knows Spy evs);
         A \<notin> bad;  evs \<in> yahalom\<rbrakk>
      \<Longrightarrow> \<exists>nb. Says Server A
                    \<lbrace>nb, Crypt (shrK A) \<lbrace>Agent B, Key K, na\<rbrace>,
                          Crypt (shrK B) \<lbrace>Agent A, Agent B, Key K, nb\<rbrace>\<rbrace>
                  \<in> set evs"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt\<open>Fake, YM3\<close>
apply blast+
done

text\<open>The obvious combination of \<open>A_trusts_YM3\<close> with 
\<open>Spy_not_see_encrypted_key\<close>\<close>
theorem A_gets_good_key:
     "\<lbrakk>Crypt (shrK A) \<lbrace>Agent B, Key K, na\<rbrace> \<in> parts (knows Spy evs);
         \<forall>nb. Notes Spy \<lbrace>na, nb, Key K\<rbrace> \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom\<rbrakk>
      \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: A_trusts_YM3 Spy_not_see_encrypted_key)


subsection\<open>Security Guarantee for B upon receiving YM4\<close>

text\<open>B knows, by the first part of A's message, that the Server distributed
  the key for A and B, and has associated it with NB.\<close>
lemma B_trusts_YM4_shrK:
     "\<lbrakk>Crypt (shrK B) \<lbrace>Agent A, Agent B, Key K, Nonce NB\<rbrace>
           \<in> parts (knows Spy evs);
         B \<notin> bad;  evs \<in> yahalom\<rbrakk>
  \<Longrightarrow> \<exists>NA. Says Server A
             \<lbrace>Nonce NB,
               Crypt (shrK A) \<lbrace>Agent B, Key K, Nonce NA\<rbrace>,
               Crypt (shrK B) \<lbrace>Agent A, Agent B, Key K, Nonce NB\<rbrace>\<rbrace>
             \<in> set evs"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt\<open>Fake, YM3\<close>
apply blast+
done


text\<open>With this protocol variant, we don't need the 2nd part of YM4 at all:
  Nonce NB is available in the first part.\<close>

text\<open>What can B deduce from receipt of YM4?  Stronger and simpler than Yahalom
  because we do not have to show that NB is secret.\<close>
lemma B_trusts_YM4:
     "\<lbrakk>Gets B \<lbrace>Crypt (shrK B) \<lbrace>Agent A, Agent B, Key K, Nonce NB\<rbrace>,  X\<rbrace>
           \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom\<rbrakk>
  \<Longrightarrow> \<exists>NA. Says Server A
             \<lbrace>Nonce NB,
               Crypt (shrK A) \<lbrace>Agent B, Key K, Nonce NA\<rbrace>,
               Crypt (shrK B) \<lbrace>Agent A, Agent B, Key K, Nonce NB\<rbrace>\<rbrace>
            \<in> set evs"
by (blast dest!: B_trusts_YM4_shrK)


text\<open>The obvious combination of \<open>B_trusts_YM4\<close> with 
\<open>Spy_not_see_encrypted_key\<close>\<close>
theorem B_gets_good_key:
     "\<lbrakk>Gets B \<lbrace>Crypt (shrK B) \<lbrace>Agent A, Agent B, Key K, Nonce NB\<rbrace>, X\<rbrace>
           \<in> set evs;
         \<forall>na. Notes Spy \<lbrace>na, Nonce NB, Key K\<rbrace> \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom\<rbrakk>
      \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: B_trusts_YM4 Spy_not_see_encrypted_key)


subsection\<open>Authenticating B to A\<close>

text\<open>The encryption in message YM2 tells us it cannot be faked.\<close>
lemma B_Said_YM2:
     "\<lbrakk>Crypt (shrK B) \<lbrace>Agent A, Nonce NA\<rbrace> \<in> parts (knows Spy evs);
         B \<notin> bad;  evs \<in> yahalom\<rbrakk>
      \<Longrightarrow> \<exists>NB. Says B Server \<lbrace>Agent B, Nonce NB,
                               Crypt (shrK B) \<lbrace>Agent A, Nonce NA\<rbrace>\<rbrace>
                      \<in> set evs"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt\<open>Fake, YM2\<close>
apply blast+
done


text\<open>If the server sends YM3 then B sent YM2, perhaps with a different NB\<close>
lemma YM3_auth_B_to_A_lemma:
     "\<lbrakk>Says Server A \<lbrace>nb, Crypt (shrK A) \<lbrace>Agent B, Key K, Nonce NA\<rbrace>, X\<rbrace>
           \<in> set evs;
         B \<notin> bad;  evs \<in> yahalom\<rbrakk>
      \<Longrightarrow> \<exists>nb'. Says B Server \<lbrace>Agent B, nb',
                                   Crypt (shrK B) \<lbrace>Agent A, Nonce NA\<rbrace>\<rbrace>
                       \<in> set evs"
apply (erule rev_mp)
apply (erule yahalom.induct, simp_all)
txt\<open>Fake, YM2, YM3\<close>
apply (blast dest!: B_Said_YM2)+
done

text\<open>If A receives YM3 then B has used nonce NA (and therefore is alive)\<close>
theorem YM3_auth_B_to_A:
     "\<lbrakk>Gets A \<lbrace>nb, Crypt (shrK A) \<lbrace>Agent B, Key K, Nonce NA\<rbrace>, X\<rbrace>
           \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom\<rbrakk>
 \<Longrightarrow> \<exists>nb'. Says B Server
                  \<lbrace>Agent B, nb', Crypt (shrK B) \<lbrace>Agent A, Nonce NA\<rbrace>\<rbrace>
               \<in> set evs"
by (blast dest!: A_trusts_YM3 YM3_auth_B_to_A_lemma)


subsection\<open>Authenticating A to B\<close>

text\<open>using the certificate @{term "Crypt K (Nonce NB)"}\<close>

text\<open>Assuming the session key is secure, if both certificates are present then
  A has said NB.  We can't be sure about the rest of A's message, but only
  NB matters for freshness.  Note that @{term "Key K \<notin> analz (knows Spy evs)"}
  must be the FIRST antecedent of the induction formula.\<close>

text\<open>This lemma allows a use of \<open>unique_session_keys\<close> in the next proof,
  which otherwise is extremely slow.\<close>
lemma secure_unique_session_keys:
     "\<lbrakk>Crypt (shrK A) \<lbrace>Agent B, Key K, na\<rbrace> \<in> analz (spies evs);
         Crypt (shrK A') \<lbrace>Agent B', Key K, na'\<rbrace> \<in> analz (spies evs);
         Key K \<notin> analz (knows Spy evs);  evs \<in> yahalom\<rbrakk>
     \<Longrightarrow> A=A' & B=B'"
by (blast dest!: A_trusts_YM3 dest: unique_session_keys Crypt_Spy_analz_bad)


lemma Auth_A_to_B_lemma [rule_format]:
     "evs \<in> yahalom
      \<Longrightarrow> Key K \<notin> analz (knows Spy evs) -->
          K \<in> symKeys -->
          Crypt K (Nonce NB) \<in> parts (knows Spy evs) -->
          Crypt (shrK B) \<lbrace>Agent A, Agent B, Key K, Nonce NB\<rbrace>
            \<in> parts (knows Spy evs) -->
          B \<notin> bad -->
          (\<exists>X. Says A B \<lbrace>X, Crypt K (Nonce NB)\<rbrace> \<in> set evs)"
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy)
apply (analz_mono_contra, simp_all)
  subgoal \<comment>\<open>Fake\<close> by blast
  subgoal \<comment>\<open>YM3 because the message @{term "Crypt K (Nonce NB)"} could not exist\<close>
    by (force dest!: Crypt_imp_keysFor)
  subgoal \<comment>\<open>YM4: was @{term "Crypt K (Nonce NB)"} the very last message? If not, use the induction hypothesis,
             otherwise by unicity of session keys\<close>
    by (blast dest!: B_trusts_YM4_shrK dest: secure_unique_session_keys)
done


text\<open>If B receives YM4 then A has used nonce NB (and therefore is alive).
  Moreover, A associates K with NB (thus is talking about the same run).
  Other premises guarantee secrecy of K.\<close>
theorem YM4_imp_A_Said_YM3 [rule_format]:
     "\<lbrakk>Gets B \<lbrace>Crypt (shrK B) \<lbrace>Agent A, Agent B, Key K, Nonce NB\<rbrace>,
                  Crypt K (Nonce NB)\<rbrace> \<in> set evs;
         (\<forall>NA. Notes Spy \<lbrace>Nonce NA, Nonce NB, Key K\<rbrace> \<notin> set evs);
         K \<in> symKeys;  A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom\<rbrakk>
      \<Longrightarrow> \<exists>X. Says A B \<lbrace>X, Crypt K (Nonce NB)\<rbrace> \<in> set evs"
by (blast intro: Auth_A_to_B_lemma
          dest: Spy_not_see_encrypted_key B_trusts_YM4_shrK)

end
