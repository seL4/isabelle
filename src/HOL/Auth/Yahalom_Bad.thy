(*  Title:      HOL/Auth/Yahalom
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "yahalom" for the Yahalom protocol.

Demonstrates of why Oops is necessary.  This protocol can be attacked because
it doesn't keep NB secret, but without Oops it can be "verified" anyway.
The issues are discussed in lcp's LICS 2000 invited lecture.
*)

header{*The Yahalom Protocol: A Flawed Version*}

theory Yahalom_Bad = Shared:

consts  yahalom   :: "event list set"
inductive "yahalom"
  intros
         (*Initial trace is empty*)
   Nil:  "[] \<in> yahalom"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
   Fake: "[| evsf \<in> yahalom;  X \<in> synth (analz (knows Spy evsf)) |]
          ==> Says Spy B X  # evsf \<in> yahalom"

         (*A message that has been sent can be received by the
           intended recipient.*)
   Reception: "[| evsr \<in> yahalom;  Says A B X \<in> set evsr |]
               ==> Gets B X # evsr \<in> yahalom"

         (*Alice initiates a protocol run*)
   YM1:  "[| evs1 \<in> yahalom;  Nonce NA \<notin> used evs1 |]
          ==> Says A B {|Agent A, Nonce NA|} # evs1 \<in> yahalom"

         (*Bob's response to Alice's message.*)
   YM2:  "[| evs2 \<in> yahalom;  Nonce NB \<notin> used evs2;
             Gets B {|Agent A, Nonce NA|} \<in> set evs2 |]
          ==> Says B Server
                  {|Agent B, Nonce NB, Crypt (shrK B) {|Agent A, Nonce NA|}|}
                # evs2 \<in> yahalom"

         (*The Server receives Bob's message.  He responds by sending a
            new session key to Alice, with a packet for forwarding to Bob.*)
   YM3:  "[| evs3 \<in> yahalom;  Key KAB \<notin> used evs3;
             Gets Server
                  {|Agent B, Nonce NB, Crypt (shrK B) {|Agent A, Nonce NA|}|}
               \<in> set evs3 |]
          ==> Says Server A
                   {|Crypt (shrK A) {|Agent B, Key KAB, Nonce NA, Nonce NB|},
                     Crypt (shrK B) {|Agent A, Key KAB|}|}
                # evs3 \<in> yahalom"

         (*Alice receives the Server's (?) message, checks her Nonce, and
           uses the new session key to send Bob his Nonce.  The premise
           A \<noteq> Server is needed to prove Says_Server_not_range.*)
   YM4:  "[| evs4 \<in> yahalom;  A \<noteq> Server;
             Gets A {|Crypt(shrK A) {|Agent B, Key K, Nonce NA, Nonce NB|}, X|}
                \<in> set evs4;
             Says A B {|Agent A, Nonce NA|} \<in> set evs4 |]
          ==> Says A B {|X, Crypt K (Nonce NB)|} # evs4 \<in> yahalom"


declare Says_imp_knows_Spy [THEN analz.Inj, dest]
declare parts.Body  [dest]
declare Fake_parts_insert_in_Un  [dest]
declare analz_into_parts [dest]


(*A "possibility property": there are traces that reach the end*)
lemma "[| A \<noteq> Server; Key K \<notin> used [] |] 
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

(*Must be proved separately for each protocol*)
lemma Gets_imp_knows_Spy:
     "[| Gets B X \<in> set evs; evs \<in> yahalom |]  ==> X \<in> knows Spy evs"
by (blast dest!: Gets_imp_Says Says_imp_knows_Spy)

declare Gets_imp_knows_Spy [THEN analz.Inj, dest]


(**** Inductive proofs about yahalom ****)

(** For reasoning about the encrypted portion of messages **)

(*Lets us treat YM4 using a similar argument as for the Fake case.*)
lemma YM4_analz_knows_Spy:
     "[| Gets A {|Crypt (shrK A) Y, X|} \<in> set evs;  evs \<in> yahalom |]
      ==> X \<in> analz (knows Spy evs)"
by blast

lemmas YM4_parts_knows_Spy =
       YM4_analz_knows_Spy [THEN analz_into_parts, standard]


(** Theorems of the form X \<notin> parts (knows Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees a good agent's shared key!*)
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

(*Nobody can have used non-existent keys!  Needed to apply analz_insert_Key*)
lemma new_keys_not_used [rule_format, simp]:
 "evs \<in> yahalom ==> Key K \<notin> used evs --> K \<notin> keysFor (parts (knows Spy evs))"
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
txt{*Fake*}
apply (force dest!: keysFor_parts_insert)
txt{*YM3, YM4*}
apply blast+
done


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
apply (erule yahalom.induct, force,
       drule_tac [6] YM4_analz_knows_Spy, analz_freshK, spy_analz)
done

lemma analz_insert_freshK: "[| evs \<in> yahalom;  KAB \<notin> range shrK |] ==>
      (Key K \<in> analz (insert (Key KAB) (knows Spy evs))) =
      (K = KAB | Key K \<in> analz (knows Spy evs))"
by (simp only: analz_image_freshK analz_image_freshK_simps)


(*** The Key K uniquely identifies the Server's  message. **)

lemma unique_session_keys:
     "[| Says Server A
          {|Crypt (shrK A) {|Agent B, Key K, na, nb|}, X|} \<in> set evs;
        Says Server A'
          {|Crypt (shrK A') {|Agent B', Key K, na', nb'|}, X'|} \<in> set evs;
        evs \<in> yahalom |]
     ==> A=A' & B=B' & na=na' & nb=nb'"
apply (erule rev_mp, erule rev_mp)
apply (erule yahalom.induct, simp_all)
(*YM3, by freshness, and YM4*)
apply blast+
done


(** Crucial secrecy property: Spy does not see the keys sent in msg YM3 **)

lemma secrecy_lemma:
     "[| A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Says Server A
            {|Crypt (shrK A) {|Agent B, Key K, na, nb|},
              Crypt (shrK B) {|Agent A, Key K|}|}
           \<in> set evs -->
          Key K \<notin> analz (knows Spy evs)"
apply (erule yahalom.induct, force, drule_tac [6] YM4_analz_knows_Spy)
apply (simp_all add: pushes analz_insert_eq analz_insert_freshK, spy_analz)  (*Fake*)
apply (blast dest: unique_session_keys)  (*YM3*)
done

(*Final version*)
lemma Spy_not_see_encrypted_key:
     "[| Says Server A
            {|Crypt (shrK A) {|Agent B, Key K, na, nb|},
              Crypt (shrK B) {|Agent A, Key K|}|}
           \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest: secrecy_lemma)


(** Security Guarantee for A upon receiving YM3 **)

(*If the encrypted message appears then it originated with the Server*)
lemma A_trusts_YM3:
     "[| Crypt (shrK A) {|Agent B, Key K, na, nb|} \<in> parts (knows Spy evs);
         A \<notin> bad;  evs \<in> yahalom |]
       ==> Says Server A
            {|Crypt (shrK A) {|Agent B, Key K, na, nb|},
              Crypt (shrK B) {|Agent A, Key K|}|}
           \<in> set evs"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
(*Fake, YM3*)
apply blast+
done

(*The obvious combination of A_trusts_YM3 with Spy_not_see_encrypted_key*)
lemma A_gets_good_key:
     "[| Crypt (shrK A) {|Agent B, Key K, na, nb|} \<in> parts (knows Spy evs);
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: A_trusts_YM3 Spy_not_see_encrypted_key)

(** Security Guarantees for B upon receiving YM4 **)

(*B knows, by the first part of A's message, that the Server distributed
  the key for A and B.  But this part says nothing about nonces.*)
lemma B_trusts_YM4_shrK:
     "[| Crypt (shrK B) {|Agent A, Key K|} \<in> parts (knows Spy evs);
         B \<notin> bad;  evs \<in> yahalom |]
      ==> \<exists>NA NB. Says Server A
                      {|Crypt (shrK A) {|Agent B, Key K, Nonce NA, Nonce NB|},
                        Crypt (shrK B) {|Agent A, Key K|}|}
                     \<in> set evs"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy, simp_all)
(*Fake, YM3*)
apply blast+
done

(** Up to now, the reasoning is similar to standard Yahalom.  Now the
    doubtful reasoning occurs.  We should not be assuming that an unknown
    key is secure, but the model allows us to: there is no Oops rule to
    let session keys become compromised.*)

(*B knows, by the second part of A's message, that the Server distributed
  the key quoting nonce NB.  This part says nothing about agent names.
  Secrecy of K is assumed; the valid Yahalom proof uses (and later proves)
  the secrecy of NB.*)
lemma B_trusts_YM4_newK [rule_format]:
     "[|Key K \<notin> analz (knows Spy evs);  evs \<in> yahalom|]
      ==> Crypt K (Nonce NB) \<in> parts (knows Spy evs) -->
          (\<exists>A B NA. Says Server A
                      {|Crypt (shrK A) {|Agent B, Key K,
                                Nonce NA, Nonce NB|},
                        Crypt (shrK B) {|Agent A, Key K|}|}
                     \<in> set evs)"
apply (erule rev_mp)
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy)
apply (analz_mono_contra, simp_all)
(*Fake*)
apply blast
(*YM3*)
apply blast
(*A is uncompromised because NB is secure
  A's certificate guarantees the existence of the Server message*)
apply (blast dest!: Gets_imp_Says Crypt_Spy_analz_bad
             dest: Says_imp_spies
                   parts.Inj [THEN parts.Fst, THEN A_trusts_YM3])
done


(*B's session key guarantee from YM4.  The two certificates contribute to a
  single conclusion about the Server's message. *)
lemma B_trusts_YM4:
     "[| Gets B {|Crypt (shrK B) {|Agent A, Key K|},
                  Crypt K (Nonce NB)|} \<in> set evs;
         Says B Server
           {|Agent B, Nonce NB, Crypt (shrK B) {|Agent A, Nonce NA|}|}
           \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
       ==> \<exists>na nb. Says Server A
                   {|Crypt (shrK A) {|Agent B, Key K, na, nb|},
                     Crypt (shrK B) {|Agent A, Key K|}|}
             \<in> set evs"
by (blast dest: B_trusts_YM4_newK B_trusts_YM4_shrK Spy_not_see_encrypted_key
                unique_session_keys)


(*The obvious combination of B_trusts_YM4 with Spy_not_see_encrypted_key*)
lemma B_gets_good_key:
     "[| Gets B {|Crypt (shrK B) {|Agent A, Key K|},
                  Crypt K (Nonce NB)|} \<in> set evs;
         Says B Server
           {|Agent B, Nonce NB, Crypt (shrK B) {|Agent A, Nonce NA|}|}
           \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: B_trusts_YM4 Spy_not_see_encrypted_key)


(*** Authenticating B to A: these proofs are not considered.
     They are irrelevant to showing the need for Oops. ***)


(*** Authenticating A to B using the certificate Crypt K (Nonce NB) ***)

(*Assuming the session key is secure, if both certificates are present then
  A has said NB.  We can't be sure about the rest of A's message, but only
  NB matters for freshness.*)
lemma A_Said_YM3_lemma [rule_format]:
     "evs \<in> yahalom
      ==> Key K \<notin> analz (knows Spy evs) -->
          Crypt K (Nonce NB) \<in> parts (knows Spy evs) -->
          Crypt (shrK B) {|Agent A, Key K|} \<in> parts (knows Spy evs) -->
          B \<notin> bad -->
          (\<exists>X. Says A B {|X, Crypt K (Nonce NB)|} \<in> set evs)"
apply (erule yahalom.induct, force,
       frule_tac [6] YM4_parts_knows_Spy)
apply (analz_mono_contra, simp_all)
(*Fake*)
apply blast
(*YM3: by new_keys_not_used we note that Crypt K (Nonce NB) could not exist*)
apply (force dest!: Crypt_imp_keysFor)
(*YM4: was Crypt K (Nonce NB) the very last message?  If not, use ind. hyp.*)
apply (simp add: ex_disj_distrib)
(*yes: apply unicity of session keys*)
apply (blast dest!: Gets_imp_Says A_trusts_YM3 B_trusts_YM4_shrK
                    Crypt_Spy_analz_bad
             dest: Says_imp_knows_Spy [THEN parts.Inj] unique_session_keys)
done

(*If B receives YM4 then A has used nonce NB (and therefore is alive).
  Moreover, A associates K with NB (thus is talking about the same run).
  Other premises guarantee secrecy of K.*)
lemma YM4_imp_A_Said_YM3 [rule_format]:
     "[| Gets B {|Crypt (shrK B) {|Agent A, Key K|},
                  Crypt K (Nonce NB)|} \<in> set evs;
         Says B Server
           {|Agent B, Nonce NB, Crypt (shrK B) {|Agent A, Nonce NA|}|}
           \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> yahalom |]
      ==> \<exists>X. Says A B {|X, Crypt K (Nonce NB)|} \<in> set evs"
apply (blast intro!: A_Said_YM3_lemma
            dest: Spy_not_see_encrypted_key B_trusts_YM4 Gets_imp_Says)
done

end
