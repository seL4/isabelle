(*  Title:      HOL/Auth/OtwayRees_Bad
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "otway" for the Otway-Rees protocol.

The FAULTY version omitting encryption of Nonce NB, as suggested on page 247 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)

This file illustrates the consequences of such errors.  We can still prove
impressive-looking properties such as Spy_not_see_encrypted_key, yet the
protocol is open to a middleperson attack.  Attempting to prove some key lemmas
indicates the possibility of this attack.
*)

theory OtwayRees_Bad = Shared:

consts  otway   :: "event list set"
inductive "otway"
  intros
         (*Initial trace is empty*)
   Nil:  "[] \<in> otway"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
   Fake: "[| evsf \<in> otway;  X \<in> synth (analz (knows Spy evsf)) |]
          ==> Says Spy B X  # evsf \<in> otway"

         (*A message that has been sent can be received by the
           intended recipient.*)
   Reception: "[| evsr \<in> otway;  Says A B X \<in>set evsr |]
               ==> Gets B X # evsr \<in> otway"

         (*Alice initiates a protocol run*)
   OR1:  "[| evs1 \<in> otway;  Nonce NA \<notin> used evs1 |]
          ==> Says A B {|Nonce NA, Agent A, Agent B,
                         Crypt (shrK A) {|Nonce NA, Agent A, Agent B|} |}
                 # evs1 \<in> otway"

         (*Bob's response to Alice's message.
           This variant of the protocol does NOT encrypt NB.*)
   OR2:  "[| evs2 \<in> otway;  Nonce NB \<notin> used evs2;
             Gets B {|Nonce NA, Agent A, Agent B, X|} \<in> set evs2 |]
          ==> Says B Server
                  {|Nonce NA, Agent A, Agent B, X, Nonce NB,
                    Crypt (shrK B) {|Nonce NA, Agent A, Agent B|}|}
                 # evs2 \<in> otway"

         (*The Server receives Bob's message and checks that the three NAs
           match.  Then he sends a new session key to Bob with a packet for
           forwarding to Alice.*)
   OR3:  "[| evs3 \<in> otway;  Key KAB \<notin> used evs3;
             Gets Server
                  {|Nonce NA, Agent A, Agent B,
                    Crypt (shrK A) {|Nonce NA, Agent A, Agent B|},
                    Nonce NB,
                    Crypt (shrK B) {|Nonce NA, Agent A, Agent B|}|}
               \<in> set evs3 |]
          ==> Says Server B
                  {|Nonce NA,
                    Crypt (shrK A) {|Nonce NA, Key KAB|},
                    Crypt (shrK B) {|Nonce NB, Key KAB|}|}
                 # evs3 \<in> otway"

         (*Bob receives the Server's (?) message and compares the Nonces with
	   those in the message he previously sent the Server.
           Need B ~= Server because we allow messages to self.*)
   OR4:  "[| evs4 \<in> otway;  B ~= Server;
             Says B Server {|Nonce NA, Agent A, Agent B, X', Nonce NB,
                             Crypt (shrK B) {|Nonce NA, Agent A, Agent B|}|}
               \<in> set evs4;
             Gets B {|Nonce NA, X, Crypt (shrK B) {|Nonce NB, Key K|}|}
               \<in> set evs4 |]
          ==> Says B A {|Nonce NA, X|} # evs4 \<in> otway"

         (*This message models possible leaks of session keys.  The nonces
           identify the protocol run.*)
   Oops: "[| evso \<in> otway;
             Says Server B {|Nonce NA, X, Crypt (shrK B) {|Nonce NB, Key K|}|}
               \<in> set evso |]
          ==> Notes Spy {|Nonce NA, Nonce NB, Key K|} # evso \<in> otway"


declare Says_imp_knows_Spy [THEN analz.Inj, dest]
declare parts.Body  [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un  [dest]

(*A "possibility property": there are traces that reach the end*)
lemma "B \<noteq> Server
      ==> \<exists>K. \<exists>NA. \<exists>evs \<in> otway.
            Says B A {|Nonce NA, Crypt (shrK A) {|Nonce NA, Key K|}|}
              \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] otway.Nil
                    [THEN otway.OR1, THEN otway.Reception,
                     THEN otway.OR2, THEN otway.Reception,
                     THEN otway.OR3, THEN otway.Reception, THEN otway.OR4], possibility)
done

lemma Gets_imp_Says [dest!]:
     "[| Gets B X \<in> set evs; evs \<in> otway |] ==> \<exists>A. Says A B X \<in> set evs"
apply (erule rev_mp)
apply (erule otway.induct, auto)
done


(**** Inductive proofs about otway ****)


(** For reasoning about the encrypted portion of messages **)

lemma OR2_analz_knows_Spy:
     "[| Gets B {|N, Agent A, Agent B, X|} \<in> set evs;  evs \<in> otway |]
      ==> X \<in> analz (knows Spy evs)"
by blast

lemma OR4_analz_knows_Spy:
     "[| Gets B {|N, X, Crypt (shrK B) X'|} \<in> set evs;  evs \<in> otway |]
      ==> X \<in> analz (knows Spy evs)"
by blast

lemma Oops_parts_knows_Spy:
     "Says Server B {|NA, X, Crypt K' {|NB,K|}|} \<in> set evs
      ==> K \<in> parts (knows Spy evs)"
by blast

(*Forwarding lemma: see comments in OtwayRees.thy*)
lemmas OR2_parts_knows_Spy =
    OR2_analz_knows_Spy [THEN analz_into_parts, standard]


(** Theorems of the form X \<notin> parts (knows Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees a good agent's shared key!*)
lemma Spy_see_shrK [simp]:
     "evs \<in> otway ==> (Key (shrK A) \<in> parts (knows Spy evs)) = (A \<in> bad)"
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all, blast+)
done

lemma Spy_analz_shrK [simp]:
     "evs \<in> otway ==> (Key (shrK A) \<in> analz (knows Spy evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "[|Key (shrK A) \<in> parts (knows Spy evs);  evs \<in> otway|] ==> A \<in> bad"
by (blast dest: Spy_see_shrK)


(*** Proofs involving analz ***)

(*Describes the form of K and NA when the Server sends this message.  Also
  for Oops case.*)
lemma Says_Server_message_form:
     "[| Says Server B {|NA, X, Crypt (shrK B) {|NB, Key K|}|} \<in> set evs;
         evs \<in> otway |]
      ==> K \<notin> range shrK & (\<exists>i. NA = Nonce i) & (\<exists>j. NB = Nonce j)"
apply (erule rev_mp)
apply (erule otway.induct, simp_all, blast)
done


(****
 The following is to prove theorems of the form

  Key K \<in> analz (insert (Key KAB) (knows Spy evs)) ==>
  Key K \<in> analz (knows Spy evs)

 A more general formula must be proved inductively.
****)


(** Session keys are not used to encrypt other session keys **)

(*The equality makes the induction hypothesis easier to apply*)
lemma analz_image_freshK [rule_format]:
 "evs \<in> otway ==>
   \<forall>K KK. KK <= -(range shrK) -->
          (Key K \<in> analz (Key`KK Un (knows Spy evs))) =
          (K \<in> KK | Key K \<in> analz (knows Spy evs))"
apply (erule otway.induct, force)
apply (frule_tac [7] Says_Server_message_form)
apply (drule_tac [6] OR4_analz_knows_Spy)
apply (drule_tac [4] OR2_analz_knows_Spy, analz_freshK, spy_analz)
done

lemma analz_insert_freshK:
  "[| evs \<in> otway;  KAB \<notin> range shrK |] ==>
      (Key K \<in> analz (insert (Key KAB) (knows Spy evs))) =
      (K = KAB | Key K \<in> analz (knows Spy evs))"
by (simp only: analz_image_freshK analz_image_freshK_simps)


(*** The Key K uniquely identifies the Server's  message. **)

lemma unique_session_keys:
     "[| Says Server B {|NA, X, Crypt (shrK B) {|NB, K|}|}   \<in> set evs;
         Says Server B' {|NA',X',Crypt (shrK B') {|NB',K|}|} \<in> set evs;
         evs \<in> otway |] ==> X=X' & B=B' & NA=NA' & NB=NB'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule otway.induct, simp_all)
(*Remaining cases: OR3 and OR4*)
apply blast+
done


(** Crucial secrecy property: Spy does not see the keys sent in msg OR3
    Does not in itself guarantee security: an attack could violate
    the premises, e.g. by having A=Spy **)

lemma secrecy_lemma:
 "[| A \<notin> bad;  B \<notin> bad;  evs \<in> otway |]
  ==> Says Server B
        {|NA, Crypt (shrK A) {|NA, Key K|},
          Crypt (shrK B) {|NB, Key K|}|} \<in> set evs -->
      Notes Spy {|NA, NB, Key K|} \<notin> set evs -->
      Key K \<notin> analz (knows Spy evs)"
apply (erule otway.induct, force)
apply (frule_tac [7] Says_Server_message_form)
apply (drule_tac [6] OR4_analz_knows_Spy)
apply (drule_tac [4] OR2_analz_knows_Spy)
apply (simp_all add: analz_insert_eq analz_insert_freshK pushes, spy_analz)  (*Fake*)
(*OR3, OR4, Oops*)
apply (blast dest: unique_session_keys)+
done


lemma Spy_not_see_encrypted_key:
     "[| Says Server B
          {|NA, Crypt (shrK A) {|NA, Key K|},
                Crypt (shrK B) {|NB, Key K|}|} \<in> set evs;
         Notes Spy {|NA, NB, Key K|} \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> otway |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest: Says_Server_message_form secrecy_lemma)


(*** Attempting to prove stronger properties ***)

(*Only OR1 can have caused such a part of a message to appear.
  The premise A \<noteq> B prevents OR2's similar-looking cryptogram from being
  picked up.  Original Otway-Rees doesn't need it.*)
lemma Crypt_imp_OR1 [rule_format]:
     "[| A \<notin> bad;  A \<noteq> B;  evs \<in> otway |]
      ==> Crypt (shrK A) {|NA, Agent A, Agent B|} \<in> parts (knows Spy evs) -->
          Says A B {|NA, Agent A, Agent B,
                     Crypt (shrK A) {|NA, Agent A, Agent B|}|}  \<in> set evs"
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all, blast+)
done


(*Crucial property: If the encrypted message appears, and A has used NA
  to start a run, then it originated with the Server!
  The premise A \<noteq> B allows use of Crypt_imp_OR1*)
(*Only it is FALSE.  Somebody could make a fake message to Server
          substituting some other nonce NA' for NB.*)
lemma "[| A \<notin> bad;  A \<noteq> B;  evs \<in> otway |]
       ==> Crypt (shrK A) {|NA, Key K|} \<in> parts (knows Spy evs) -->
           Says A B {|NA, Agent A, Agent B,
                      Crypt (shrK A) {|NA, Agent A, Agent B|}|}
            \<in> set evs -->
           (\<exists>B NB. Says Server B
                {|NA,
                  Crypt (shrK A) {|NA, Key K|},
                  Crypt (shrK B) {|NB, Key K|}|}  \<in> set evs)"
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all)
(*Fake*)
apply blast
(*OR1: it cannot be a new Nonce, contradiction.*)
apply blast
(*OR3 and OR4*)
apply (simp_all add: ex_disj_distrib)
(*OR4*)
prefer 2 apply (blast intro!: Crypt_imp_OR1)
(*OR3*)
apply clarify
(*The hypotheses at this point suggest an attack in which nonce NB is used
  in two different roles:
          Gets Server
           {|Nonce NA, Agent Aa, Agent A,
             Crypt (shrK Aa) {|Nonce NA, Agent Aa, Agent A|}, Nonce NB,
             Crypt (shrK A) {|Nonce NA, Agent Aa, Agent A|}|}
          \<in> set evs3
          Says A B
           {|Nonce NB, Agent A, Agent B,
             Crypt (shrK A) {|Nonce NB, Agent A, Agent B|}|}
          \<in> set evs3;
*)


(*Thus the key property A_can_trust probably fails too.*)
oops

end
