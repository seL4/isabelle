(*  Title:      HOL/Auth/WooLam
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "woolam" for the Woo-Lam protocol.

Simplified version from page 11 of
  Abadi and Needham.  Prudent Engineering Practice for Cryptographic Protocols.
  IEEE Trans. S.E. 22(1), 1996, pages 6-15.

Note: this differs from the Woo-Lam protocol discussed by Lowe in his paper
  Some New Attacks upon Security Protocols.
  Computer Security Foundations Workshop, 1996.
*)

theory WooLam = Shared:

consts  woolam  :: "event list set"
inductive woolam
  intros
         (*Initial trace is empty*)
   Nil:  "[] \<in> woolam"

         (** These rules allow agents to send messages to themselves **)

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
   Fake: "[| evsf \<in> woolam;  X \<in> synth (analz (spies evsf)) |]
          ==> Says Spy B X  # evsf \<in> woolam"

         (*Alice initiates a protocol run*)
   WL1:  "evs1 \<in> woolam ==> Says A B (Agent A) # evs1 \<in> woolam"

         (*Bob responds to Alice's message with a challenge.*)
   WL2:  "[| evs2 \<in> woolam;  Says A' B (Agent A) \<in> set evs2 |]
          ==> Says B A (Nonce NB) # evs2 \<in> woolam"

         (*Alice responds to Bob's challenge by encrypting NB with her key.
           B is *not* properly determined -- Alice essentially broadcasts
           her reply.*)
   WL3:  "[| evs3 \<in> woolam;
             Says A  B (Agent A)  \<in> set evs3;
             Says B' A (Nonce NB) \<in> set evs3 |]
          ==> Says A B (Crypt (shrK A) (Nonce NB)) # evs3 \<in> woolam"

         (*Bob forwards Alice's response to the Server.  NOTE: usually
           the messages are shown in chronological order, for clarity.
           But here, exchanging the two events would cause the lemma
           WL4_analz_spies to pick up the wrong assumption!*)
   WL4:  "[| evs4 \<in> woolam;
             Says A'  B X         \<in> set evs4;
             Says A'' B (Agent A) \<in> set evs4 |]
          ==> Says B Server {|Agent A, Agent B, X|} # evs4 \<in> woolam"

         (*Server decrypts Alice's response for Bob.*)
   WL5:  "[| evs5 \<in> woolam;
             Says B' Server {|Agent A, Agent B, Crypt (shrK A) (Nonce NB)|}
               \<in> set evs5 |]
          ==> Says Server B (Crypt (shrK B) {|Agent A, Nonce NB|})
                 # evs5 \<in> woolam"


declare Says_imp_knows_Spy [THEN analz.Inj, dest]
declare parts.Body  [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un  [dest]


(*A "possibility property": there are traces that reach the end*)
lemma "\<exists>NB. \<exists>evs \<in> woolam.
             Says Server B (Crypt (shrK B) {|Agent A, Nonce NB|}) \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] woolam.Nil
                    [THEN woolam.WL1, THEN woolam.WL2, THEN woolam.WL3,
                     THEN woolam.WL4, THEN woolam.WL5], possibility)
done

(*Could prove forwarding lemmas for WL4, but we do not need them!*)

(**** Inductive proofs about woolam ****)

(** Theorems of the form X \<notin> parts (spies evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees a good agent's shared key!*)
lemma Spy_see_shrK [simp]:
     "evs \<in> woolam ==> (Key (shrK A) \<in> parts (spies evs)) = (A \<in> bad)"
apply (erule woolam.induct, force, simp_all, blast+)
done

lemma Spy_analz_shrK [simp]:
     "evs \<in> woolam ==> (Key (shrK A) \<in> analz (spies evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "[|Key (shrK A) \<in> parts (knows Spy evs);  evs \<in> woolam|] ==> A \<in> bad"
by (blast dest: Spy_see_shrK)


(**** Autheticity properties for Woo-Lam ****)

(*** WL4 ***)

(*If the encrypted message appears then it originated with Alice*)
lemma NB_Crypt_imp_Alice_msg:
     "[| Crypt (shrK A) (Nonce NB) \<in> parts (spies evs);
         A \<notin> bad;  evs \<in> woolam |]
      ==> \<exists>B. Says A B (Crypt (shrK A) (Nonce NB)) \<in> set evs"
apply (erule rev_mp, erule woolam.induct, force, simp_all, blast+)
done

(*Guarantee for Server: if it gets a message containing a certificate from
  Alice, then she originated that certificate.  But we DO NOT know that B
  ever saw it: the Spy may have rerouted the message to the Server.*)
lemma Server_trusts_WL4 [dest]:
     "[| Says B' Server {|Agent A, Agent B, Crypt (shrK A) (Nonce NB)|}
           \<in> set evs;
         A \<notin> bad;  evs \<in> woolam |]
      ==> \<exists>B. Says A B (Crypt (shrK A) (Nonce NB)) \<in> set evs"
by (blast intro!: NB_Crypt_imp_Alice_msg)


(*** WL5 ***)

(*Server sent WL5 only if it received the right sort of message*)
lemma Server_sent_WL5 [dest]:
     "[| Says Server B (Crypt (shrK B) {|Agent A, NB|}) \<in> set evs;
         evs \<in> woolam |]
      ==> \<exists>B'. Says B' Server {|Agent A, Agent B, Crypt (shrK A) NB|}
             \<in> set evs"
apply (erule rev_mp, erule woolam.induct, force, simp_all, blast+)
done

(*If the encrypted message appears then it originated with the Server!*)
lemma NB_Crypt_imp_Server_msg [rule_format]:
     "[| Crypt (shrK B) {|Agent A, NB|} \<in> parts (spies evs);
         B \<notin> bad;  evs \<in> woolam |]
      ==> Says Server B (Crypt (shrK B) {|Agent A, NB|}) \<in> set evs"
apply (erule rev_mp, erule woolam.induct, force, simp_all, blast+)
done

(*Guarantee for B.  If B gets the Server's certificate then A has encrypted
  the nonce using her key.  This event can be no older than the nonce itself.
  But A may have sent the nonce to some other agent and it could have reached
  the Server via the Spy.*)
lemma B_trusts_WL5:
     "[| Says S B (Crypt (shrK B) {|Agent A, Nonce NB|}): set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> woolam  |]
      ==> \<exists>B. Says A B (Crypt (shrK A) (Nonce NB)) \<in> set evs"
by (blast dest!: NB_Crypt_imp_Server_msg)


(*B only issues challenges in response to WL1.  Not used.*)
lemma B_said_WL2:
     "[| Says B A (Nonce NB) \<in> set evs;  B \<noteq> Spy;  evs \<in> woolam |]
      ==> \<exists>A'. Says A' B (Agent A) \<in> set evs"
apply (erule rev_mp, erule woolam.induct, force, simp_all, blast+)
done


(**CANNOT be proved because A doesn't know where challenges come from...*)
lemma "[| A \<notin> bad;  B \<noteq> Spy;  evs \<in> woolam |]
  ==> Crypt (shrK A) (Nonce NB) \<in> parts (spies evs) &
      Says B A (Nonce NB) \<in> set evs
      --> Says A B (Crypt (shrK A) (Nonce NB)) \<in> set evs"
apply (erule rev_mp, erule woolam.induct, force, simp_all, blast, auto)
oops

end
