(*  Title:      HOL/Auth/Yahalom2.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

header{*The Yahalom Protocol, Variant 2*}

theory Yahalom2 imports Public begin

text{*
This version trades encryption of NB for additional explicitness in YM3.
Also in YM3, care is taken to make the two certificates distinct.

From page 259 of
  Burrows, Abadi and Needham (1989).  A Logic of Authentication.
  Proc. Royal Soc. 426

This theory has the prototypical example of a secrecy relation, KeyCryptNonce.
*}

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
          ==> Says A B {|Agent A, Nonce NA|} # evs1 \<in> yahalom"

         (*Bob's response to Alice's message.*)
 | YM2:  "[| evs2 \<in> yahalom;  Nonce NB \<notin> used evs2;
             Gets B {|Agent A, Nonce NA|} \<in> set evs2 |]
          ==> Says B Server
                  {|Agent B, Nonce NB, Crypt (shrK B) {|Agent A, Nonce NA|}|}
                # evs2 \<in> yahalom"

         (*The Server receives Bob's message.  He responds by sending a
           new session key to Alice, with a certificate for forwarding to Bob.
           Both agents are quoted in the 2nd certificate to prevent attacks!*)
 | YM3:  "[| evs3 \<in> yahalom;  Key KAB \<notin> used evs3;
             Gets Server {|Agent B, Nonce NB,
                           Crypt (shrK B) {|Agent A, Nonce NA|}|}
               \<in> set evs3 |]
          ==> Says Server A
               {|Nonce NB,
                 Crypt (shrK A) {|Agent B, Key KAB, Nonce NA|},
                 Crypt (shrK B) {|Agent A, Agent B, Key KAB, Nonce NB|}|}
                 # evs3 \<in> yahalom"

         (*Alice receives the Server's (?) message, checks her Nonce, and
           uses the new session key to send Bob his Nonce.*)
 | YM4:  "[| evs4 \<in> yahalom;
             Gets A {|Nonce NB, Crypt (shrK A) {|Agent B, Key K, Nonce NA|},
                      X|}  \<in> set evs4;
             Says A B {|Agent A, Nonce NA|} \<in> set evs4 |]
          ==> Says A B {|X, Crypt K (Nonce NB)|} # evs4 \<in> yahalom"

         (*This message models possible leaks of session keys.  The nonces
           identify the protocol run.  Quoting Server here ensures they are
           correct. *)
 | Oops: "[| evso \<in> yahalom;
             Says Server A {|Nonce NB,
                             Crypt (shrK A) {|Agent B, Key K, Nonce NA|},
                             X|}  \<in> set evso |]
          ==> Notes Spy {|Nonce NA, Nonce NB, Key K|} # evso \<in> yahalom"


declare Says_imp_knows_Spy [THEN analz.Inj, dest]
declare parts.Body  [dest]
declare Fake_parts_insert_in_Un  [dest]
declare analz_into_parts [dest]

text{*A "possibility property": there are traces that reach the end*}
lemma "Key K \<notin> used []
       ==> \<exists>X NB. \<exists>evs \<in> yahalom.
             Says A B {|X, Crypt K (Nonce NB)|} \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] yahalom.Nil
                    [THEN yahalom.YM1, THEN yahalom.Reception,
                     THEN yahalom.YM2, THEN yahalom.Reception,
                     THEN yahalom.YM3, THEN yahalom.Reception,
                     THEN yahalom.YM4])
apply (possibility, simp add: used_Cons)
done

lemma Gets_imp_Says:
     "[| Gets B X \<in> set evs; evs \<in> yahalom |] ==> \<exists>A. Says A B X \<in> set evs"
by (erule rev_mp, erule yahalom.induct, auto)

text{*Must be proved separately for each protocol*}
lemma Gets_imp_knows_Spy:
     "[| Gets B X \<in> set evs; evs \<in> yahalom |]  ==> X \<in> knows Spy evs"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)

declare Gets_imp_knows_Spy [THEN analz.Inj, dest]


subsection{*Inductive Proofs*}

text{*Result for reasoning about the encrypted portion of messages.
Lets us treat YM4 using a similar argument as for the Fake case.*}
lemma YM4_analz_knows_Spy:
     "[| Gets A {|NB, Crypt (shrK A) Y, X|} \<in> set evs;  evs \<in> yahalom |]
      ==> X \<in> analz (knows Spy evs)"
by blast

lemmas YM4_parts_knows_Spy =
       YM4_analz_knows_Spy [THEN analz_into_parts]


(** Theorems of the form X \<notin> parts (knows Spy evs) imply that NOBODY
    sends messages containing X! **)

text{*Spy never sees a good agent's shared key!*}
lemma Spy_see_shrK [simp]:
     "evs \<in> yahalom ==> (Key (shrK A) \<in> parts (knows Spy evs)) = (A \<in> bad)"
by (erule yahalom.induct, force,
    drule_tac [6] YM4_parts_knows_Spy, simp_all, blast+)

lemma Spy_analz_shrK [simp]:
     "evs \<in> yahalom ==> (Key (shrK A) \<in> analz (knows Spy evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "[|Key (shrK A) \<in> parts (knows Spy evs);  evs \<in> yahalom|] ==> A \<in> bad"
by (blast dest: Spy_see_shrK)

text{*Nobody can have used non-existent keys!  
    Needed to apply @{text analz_insert_Key}*}
lemma new_keys_not_used [simp]:
    "[|Key K \<notin> used evs; K \<in> symKeys; evs \<in> yahalom|]
     ==> K \<notin> keysFor (parts (spies evs))"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt{*Fake*}
apply (force dest!: keysFor_parts_insert)
txt{*YM3*}
apply blast
txt{*YM4*}
apply auto
apply (blast dest!: Gets_imp_knows_Spy [THEN parts.Inj])
done


text{*Describes the form of K when the Server sends this message.  Useful for
  Oops as well as main secrecy property.*}
lemma Says_Server_message_form:
     "[| Says Server A {|nb', Crypt (shrK A) {|Agent B, Key K, na|}, X|}
          \<in> set evs;  evs \<in> yahalom |]
      ==> K \<notin> range shrK"
by (erule rev_mp, erule yahalom.induct, simp_all)


(****
 The following is to prove theorems of the form

          Key K \<in> analz (insert (Key KAB) (knows Spy evs)) ==>
          Key K \<in> analz (knows Spy evs)

 A more general formula must be proved inductively.
****)

(** Session keys are not used to encrypt other session keys **)

lemma analz_image_freshK [rule_format]:
 "evs \<in> yahalom ==>
   \<forall>K KK. KK <= - (range shrK) -->
          (Key K \<in> analz (Key`KK Un (knows Spy evs))) =
          (K \<in> KK | Key K \<in> analz (knows Spy evs))"
apply (erule yahalom.induct)
apply (frule_tac [8] Says_Server_message_form)
apply (drule_tac [7] YM4_analz_knows_Spy, analz_freshK, spy_analz, blast)
done

lemma analz_insert_freshK:
     "[| evs \<in> yahalom;  KAB \<notin> range shrK |] ==>
      (Key K \<in> analz (insert (Key KAB) (knows Spy evs))) =
      (K = KAB | Key K \<in> analz (knows Spy evs))"
by (simp only: analz_image_freshK analz_image_freshK_simps)


text{*The Key K uniquely identifies the Server's  message*}
lemma unique_session_keys:
     "[| Says Server A
          {|nb, Crypt (shrK A) {|Agent B, Key K, na|}, X|} \<in> set evs;
        Says Server A'
          {|nb', Crypt (shrK A') {|Agent B', Key K, na'|}, X'|} \<in> set evs;
        evs \<in> yahalom |]
     ==> A=A' & B=B' & na=na' & nb=nb'"
apply (erule rev_mp, erule rev_mp)
apply (erule yahalom.induct, simp_all)
txt{*YM3, by freshness*}
apply blast
done


subsection{*Crucial Secrecy Property: Spy Does Not See Key @{term KAB}*}

lemma secrecy_lemma:
     "[| A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Says Server A
            {|nb, Crypt (shrK A) {|Agent B, Key K, na|},
                  Crypt (shrK B) {|Agent A, Agent B, Key K, nb|}|}
           \<in> set evs -->
          Notes Spy {|na, nb, Key K|} \<notin> set evs -->
          Key K \<notin> analz (knows Spy evs)"
apply (erule yahalom.induct, force, frule_tac [7] Says_Server_message_form,
       drule_tac [6] YM4_analz_knows_Spy)
apply (simp_all add: pushes analz_insert_eq analz_insert_freshK, spy_analz)
apply (blast dest: unique_session_keys)+  (*YM3, Oops*)
done


text{*Final version*}
lemma Spy_not_see_encrypted_key:
     "[| Says Server A
            {|nb, Crypt (shrK A) {|Agent B, Key K, na|},
                  Crypt (shrK B) {|Agent A, Agent B, Key K, nb|}|}
         \<in> set evs;
         Notes Spy {|na, nb, Key K|} \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest: secrecy_lemma Says_Server_message_form)



text{*This form is an immediate consequence of the previous result.  It is
similar to the assertions established by other methods.  It is equivalent
to the previous result in that the Spy already has @{term analz} and
@{term synth} at his disposal.  However, the conclusion
@{term "Key K \<notin> knows Spy evs"} appears not to be inductive: all the cases
other than Fake are trivial, while Fake requires
@{term "Key K \<notin> analz (knows Spy evs)"}. *}
lemma Spy_not_know_encrypted_key:
     "[| Says Server A
            {|nb, Crypt (shrK A) {|Agent B, Key K, na|},
                  Crypt (shrK B) {|Agent A, Agent B, Key K, nb|}|}
         \<in> set evs;
         Notes Spy {|na, nb, Key K|} \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Key K \<notin> knows Spy evs"
by (blast dest: Spy_not_see_encrypted_key)


subsection{*Security Guarantee for A upon receiving YM3*}

text{*If the encrypted message appears then it originated with the Server.
  May now apply @{text Spy_not_see_encrypted_key}, subject to its conditions.*}
lemma A_trusts_YM3:
     "[| Crypt (shrK A) {|Agent B, Key K, na|} \<in> parts (knows Spy evs);
         A \<notin> bad;  evs \<in> yahalom |]
      ==> \<exists>nb. Says Server A
                    {|nb, Crypt (shrK A) {|Agent B, Key K, na|},
                          Crypt (shrK B) {|Agent A, Agent B, Key K, nb|}|}
                  \<in> set evs"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt{*Fake, YM3*}
apply blast+
done

text{*The obvious combination of @{text A_trusts_YM3} with 
@{text Spy_not_see_encrypted_key}*}
theorem A_gets_good_key:
     "[| Crypt (shrK A) {|Agent B, Key K, na|} \<in> parts (knows Spy evs);
         \<forall>nb. Notes Spy {|na, nb, Key K|} \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: A_trusts_YM3 Spy_not_see_encrypted_key)


subsection{*Security Guarantee for B upon receiving YM4*}

text{*B knows, by the first part of A's message, that the Server distributed
  the key for A and B, and has associated it with NB.*}
lemma B_trusts_YM4_shrK:
     "[| Crypt (shrK B) {|Agent A, Agent B, Key K, Nonce NB|}
           \<in> parts (knows Spy evs);
         B \<notin> bad;  evs \<in> yahalom |]
  ==> \<exists>NA. Says Server A
             {|Nonce NB,
               Crypt (shrK A) {|Agent B, Key K, Nonce NA|},
               Crypt (shrK B) {|Agent A, Agent B, Key K, Nonce NB|}|}
             \<in> set evs"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt{*Fake, YM3*}
apply blast+
done


text{*With this protocol variant, we don't need the 2nd part of YM4 at all:
  Nonce NB is available in the first part.*}

text{*What can B deduce from receipt of YM4?  Stronger and simpler than Yahalom
  because we do not have to show that NB is secret. *}
lemma B_trusts_YM4:
     "[| Gets B {|Crypt (shrK B) {|Agent A, Agent B, Key K, Nonce NB|},  X|}
           \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
  ==> \<exists>NA. Says Server A
             {|Nonce NB,
               Crypt (shrK A) {|Agent B, Key K, Nonce NA|},
               Crypt (shrK B) {|Agent A, Agent B, Key K, Nonce NB|}|}
            \<in> set evs"
by (blast dest!: B_trusts_YM4_shrK)


text{*The obvious combination of @{text B_trusts_YM4} with 
@{text Spy_not_see_encrypted_key}*}
theorem B_gets_good_key:
     "[| Gets B {|Crypt (shrK B) {|Agent A, Agent B, Key K, Nonce NB|}, X|}
           \<in> set evs;
         \<forall>na. Notes Spy {|na, Nonce NB, Key K|} \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: B_trusts_YM4 Spy_not_see_encrypted_key)


subsection{*Authenticating B to A*}

text{*The encryption in message YM2 tells us it cannot be faked.*}
lemma B_Said_YM2:
     "[| Crypt (shrK B) {|Agent A, Nonce NA|} \<in> parts (knows Spy evs);
         B \<notin> bad;  evs \<in> yahalom |]
      ==> \<exists>NB. Says B Server {|Agent B, Nonce NB,
                               Crypt (shrK B) {|Agent A, Nonce NA|}|}
                      \<in> set evs"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt{*Fake, YM2*}
apply blast+
done


text{*If the server sends YM3 then B sent YM2, perhaps with a different NB*}
lemma YM3_auth_B_to_A_lemma:
     "[| Says Server A {|nb, Crypt (shrK A) {|Agent B, Key K, Nonce NA|}, X|}
           \<in> set evs;
         B \<notin> bad;  evs \<in> yahalom |]
      ==> \<exists>nb'. Says B Server {|Agent B, nb',
                                   Crypt (shrK B) {|Agent A, Nonce NA|}|}
                       \<in> set evs"
apply (erule rev_mp)
apply (erule yahalom.induct, simp_all)
txt{*Fake, YM2, YM3*}
apply (blast dest!: B_Said_YM2)+
done

text{*If A receives YM3 then B has used nonce NA (and therefore is alive)*}
theorem YM3_auth_B_to_A:
     "[| Gets A {|nb, Crypt (shrK A) {|Agent B, Key K, Nonce NA|}, X|}
           \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
 ==> \<exists>nb'. Says B Server
                  {|Agent B, nb', Crypt (shrK B) {|Agent A, Nonce NA|}|}
               \<in> set evs"
by (blast dest!: A_trusts_YM3 YM3_auth_B_to_A_lemma)


subsection{*Authenticating A to B*}

text{*using the certificate @{term "Crypt K (Nonce NB)"}*}

text{*Assuming the session key is secure, if both certificates are present then
  A has said NB.  We can't be sure about the rest of A's message, but only
  NB matters for freshness.  Note that @{term "Key K \<notin> analz (knows Spy evs)"}
  must be the FIRST antecedent of the induction formula.*}

text{*This lemma allows a use of @{text unique_session_keys} in the next proof,
  which otherwise is extremely slow.*}
lemma secure_unique_session_keys:
     "[| Crypt (shrK A) {|Agent B, Key K, na|} \<in> analz (spies evs);
         Crypt (shrK A') {|Agent B', Key K, na'|} \<in> analz (spies evs);
         Key K \<notin> analz (knows Spy evs);  evs \<in> yahalom |]
     ==> A=A' & B=B'"
by (blast dest!: A_trusts_YM3 dest: unique_session_keys Crypt_Spy_analz_bad)


lemma Auth_A_to_B_lemma [rule_format]:
     "evs \<in> yahalom
      ==> Key K \<notin> analz (knows Spy evs) -->
          K \<in> symKeys -->
          Crypt K (Nonce NB) \<in> parts (knows Spy evs) -->
          Crypt (shrK B) {|Agent A, Agent B, Key K, Nonce NB|}
            \<in> parts (knows Spy evs) -->
          B \<notin> bad -->
          (\<exists>X. Says A B {|X, Crypt K (Nonce NB)|} \<in> set evs)"
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy)
apply (analz_mono_contra, simp_all)
txt{*Fake*}
apply blast
txt{*YM3: by @{text new_keys_not_used}, the message
   @{term "Crypt K (Nonce NB)"} could not exist*}
apply (force dest!: Crypt_imp_keysFor)
txt{*YM4: was   @{term "Crypt K (Nonce NB)"} the very last message?  If so, 
    apply unicity of session keys; if not, use the induction hypothesis*}
apply (blast dest!: B_trusts_YM4_shrK dest: secure_unique_session_keys)
done


text{*If B receives YM4 then A has used nonce NB (and therefore is alive).
  Moreover, A associates K with NB (thus is talking about the same run).
  Other premises guarantee secrecy of K.*}
theorem YM4_imp_A_Said_YM3 [rule_format]:
     "[| Gets B {|Crypt (shrK B) {|Agent A, Agent B, Key K, Nonce NB|},
                  Crypt K (Nonce NB)|} \<in> set evs;
         (\<forall>NA. Notes Spy {|Nonce NA, Nonce NB, Key K|} \<notin> set evs);
         K \<in> symKeys;  A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> \<exists>X. Says A B {|X, Crypt K (Nonce NB)|} \<in> set evs"
by (blast intro: Auth_A_to_B_lemma
          dest: Spy_not_see_encrypted_key B_trusts_YM4_shrK)

end
