(*  Title:      HOL/Auth/OtwayRees
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

header{*The Original Otway-Rees Protocol*}

theory OtwayRees = Public:

text{* From page 244 of
  Burrows, Abadi and Needham (1989).  A Logic of Authentication.
  Proc. Royal Soc. 426

This is the original version, which encrypts Nonce NB.*}

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
                 # evs1 : otway"

         (*Bob's response to Alice's message.  Note that NB is encrypted.*)
   OR2:  "[| evs2 \<in> otway;  Nonce NB \<notin> used evs2;
             Gets B {|Nonce NA, Agent A, Agent B, X|} : set evs2 |]
          ==> Says B Server
                  {|Nonce NA, Agent A, Agent B, X,
                    Crypt (shrK B)
                      {|Nonce NA, Nonce NB, Agent A, Agent B|}|}
                 # evs2 : otway"

         (*The Server receives Bob's message and checks that the three NAs
           match.  Then he sends a new session key to Bob with a packet for
           forwarding to Alice.*)
   OR3:  "[| evs3 \<in> otway;  Key KAB \<notin> used evs3;
             Gets Server
                  {|Nonce NA, Agent A, Agent B,
                    Crypt (shrK A) {|Nonce NA, Agent A, Agent B|},
                    Crypt (shrK B) {|Nonce NA, Nonce NB, Agent A, Agent B|}|}
               : set evs3 |]
          ==> Says Server B
                  {|Nonce NA,
                    Crypt (shrK A) {|Nonce NA, Key KAB|},
                    Crypt (shrK B) {|Nonce NB, Key KAB|}|}
                 # evs3 : otway"

         (*Bob receives the Server's (?) message and compares the Nonces with
	   those in the message he previously sent the Server.
           Need B \<noteq> Server because we allow messages to self.*)
   OR4:  "[| evs4 \<in> otway;  B \<noteq> Server;
             Says B Server {|Nonce NA, Agent A, Agent B, X',
                             Crypt (shrK B)
                                   {|Nonce NA, Nonce NB, Agent A, Agent B|}|}
               : set evs4;
             Gets B {|Nonce NA, X, Crypt (shrK B) {|Nonce NB, Key K|}|}
               : set evs4 |]
          ==> Says B A {|Nonce NA, X|} # evs4 : otway"

         (*This message models possible leaks of session keys.  The nonces
           identify the protocol run.*)
   Oops: "[| evso \<in> otway;
             Says Server B {|Nonce NA, X, Crypt (shrK B) {|Nonce NB, Key K|}|}
               : set evso |]
          ==> Notes Spy {|Nonce NA, Nonce NB, Key K|} # evso : otway"


declare Says_imp_knows_Spy [THEN analz.Inj, dest]
declare parts.Body  [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un  [dest]


text{*A "possibility property": there are traces that reach the end*}
lemma "[| B \<noteq> Server; Key K \<notin> used [] |]
      ==> \<exists>evs \<in> otway.
             Says B A {|Nonce NA, Crypt (shrK A) {|Nonce NA, Key K|}|}
               \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] otway.Nil
                    [THEN otway.OR1, THEN otway.Reception,
                     THEN otway.OR2, THEN otway.Reception,
                     THEN otway.OR3, THEN otway.Reception, THEN otway.OR4]) 
apply (possibility, simp add: used_Cons) 
done

lemma Gets_imp_Says [dest!]:
     "[| Gets B X \<in> set evs; evs \<in> otway |] ==> \<exists>A. Says A B X \<in> set evs"
apply (erule rev_mp)
apply (erule otway.induct, auto)
done


(** For reasoning about the encrypted portion of messages **)

lemma OR2_analz_knows_Spy:
     "[| Gets B {|N, Agent A, Agent B, X|} \<in> set evs;  evs \<in> otway |]
      ==> X \<in> analz (knows Spy evs)"
by blast

lemma OR4_analz_knows_Spy:
     "[| Gets B {|N, X, Crypt (shrK B) X'|} \<in> set evs;  evs \<in> otway |]
      ==> X \<in> analz (knows Spy evs)"
by blast

(*These lemmas assist simplification by removing forwarded X-variables.
  We can replace them by rewriting with parts_insert2 and proving using
  dest: parts_cut, but the proofs become more difficult.*)
lemmas OR2_parts_knows_Spy =
    OR2_analz_knows_Spy [THEN analz_into_parts, standard]

(*There could be OR4_parts_knows_Spy and Oops_parts_knows_Spy, but for
  some reason proofs work without them!*)


text{*Theorems of the form @{term "X \<notin> parts (spies evs)"} imply that
NOBODY sends messages containing X! *}

text{*Spy never sees a good agent's shared key!*}
lemma Spy_see_shrK [simp]:
     "evs \<in> otway ==> (Key (shrK A) \<in> parts (knows Spy evs)) = (A \<in> bad)"
by (erule otway.induct, force,
    drule_tac [4] OR2_parts_knows_Spy, simp_all, blast+)


lemma Spy_analz_shrK [simp]:
     "evs \<in> otway ==> (Key (shrK A) \<in> analz (knows Spy evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "[|Key (shrK A) \<in> parts (knows Spy evs);  evs \<in> otway|] ==> A \<in> bad"
by (blast dest: Spy_see_shrK)


subsection{*Towards Secrecy: Proofs Involving @{term analz}*}

(*Describes the form of K and NA when the Server sends this message.  Also
  for Oops case.*)
lemma Says_Server_message_form:
     "[| Says Server B {|NA, X, Crypt (shrK B) {|NB, Key K|}|} \<in> set evs;
         evs \<in> otway |]
      ==> K \<notin> range shrK & (\<exists>i. NA = Nonce i) & (\<exists>j. NB = Nonce j)"
by (erule rev_mp, erule otway.induct, simp_all, blast)


(****
 The following is to prove theorems of the form

  Key K \<in> analz (insert (Key KAB) (knows Spy evs)) ==>
  Key K \<in> analz (knows Spy evs)

 A more general formula must be proved inductively.
****)


text{*Session keys are not used to encrypt other session keys*}

text{*The equality makes the induction hypothesis easier to apply*}
lemma analz_image_freshK [rule_format]:
 "evs \<in> otway ==>
   \<forall>K KK. KK <= -(range shrK) -->
          (Key K \<in> analz (Key`KK Un (knows Spy evs))) =
          (K \<in> KK | Key K \<in> analz (knows Spy evs))"
apply (erule otway.induct)
apply (frule_tac [8] Says_Server_message_form)
apply (drule_tac [7] OR4_analz_knows_Spy)
apply (drule_tac [5] OR2_analz_knows_Spy, analz_freshK, spy_analz, auto) 
done

lemma analz_insert_freshK:
  "[| evs \<in> otway;  KAB \<notin> range shrK |] ==>
      (Key K \<in> analz (insert (Key KAB) (knows Spy evs))) =
      (K = KAB | Key K \<in> analz (knows Spy evs))"
by (simp only: analz_image_freshK analz_image_freshK_simps)


text{*The Key K uniquely identifies the Server's  message. *}
lemma unique_session_keys:
     "[| Says Server B {|NA, X, Crypt (shrK B) {|NB, K|}|}   \<in> set evs;
         Says Server B' {|NA',X',Crypt (shrK B') {|NB',K|}|} \<in> set evs;
         evs \<in> otway |] ==> X=X' & B=B' & NA=NA' & NB=NB'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule otway.induct, simp_all)
apply blast+  --{*OR3 and OR4*}
done


subsection{*Authenticity properties relating to NA*}

text{*Only OR1 can have caused such a part of a message to appear.*}
lemma Crypt_imp_OR1 [rule_format]:
 "[| A \<notin> bad;  evs \<in> otway |]
  ==> Crypt (shrK A) {|NA, Agent A, Agent B|} \<in> parts (knows Spy evs) -->
      Says A B {|NA, Agent A, Agent B,
                 Crypt (shrK A) {|NA, Agent A, Agent B|}|}
        \<in> set evs"
by (erule otway.induct, force,
    drule_tac [4] OR2_parts_knows_Spy, simp_all, blast+)

lemma Crypt_imp_OR1_Gets:
     "[| Gets B {|NA, Agent A, Agent B,
                  Crypt (shrK A) {|NA, Agent A, Agent B|}|} \<in> set evs;
         A \<notin> bad; evs \<in> otway |]
       ==> Says A B {|NA, Agent A, Agent B,
                      Crypt (shrK A) {|NA, Agent A, Agent B|}|}
             \<in> set evs"
by (blast dest: Crypt_imp_OR1)


text{*The Nonce NA uniquely identifies A's message*}
lemma unique_NA:
     "[| Crypt (shrK A) {|NA, Agent A, Agent B|} \<in> parts (knows Spy evs);
         Crypt (shrK A) {|NA, Agent A, Agent C|} \<in> parts (knows Spy evs);
         evs \<in> otway;  A \<notin> bad |]
      ==> B = C"
apply (erule rev_mp, erule rev_mp)
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all, blast+)
done


text{*It is impossible to re-use a nonce in both OR1 and OR2.  This holds because
  OR2 encrypts Nonce NB.  It prevents the attack that can occur in the
  over-simplified version of this protocol: see OtwayRees_Bad.*}
lemma no_nonce_OR1_OR2:
   "[| Crypt (shrK A) {|NA, Agent A, Agent B|} \<in> parts (knows Spy evs);
       A \<notin> bad;  evs \<in> otway |]
    ==> Crypt (shrK A) {|NA', NA, Agent A', Agent A|} \<notin> parts (knows Spy evs)"
apply (erule rev_mp)
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all, blast+)
done

text{*Crucial property: If the encrypted message appears, and A has used NA
  to start a run, then it originated with the Server!*}
lemma NA_Crypt_imp_Server_msg [rule_format]:
     "[| A \<notin> bad;  evs \<in> otway |]
      ==> Says A B {|NA, Agent A, Agent B,
                     Crypt (shrK A) {|NA, Agent A, Agent B|}|} \<in> set evs -->
          Crypt (shrK A) {|NA, Key K|} \<in> parts (knows Spy evs)
          --> (\<exists>NB. Says Server B
                         {|NA,
                           Crypt (shrK A) {|NA, Key K|},
                           Crypt (shrK B) {|NB, Key K|}|} \<in> set evs)"
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all, blast)
apply blast  --{*OR1: by freshness*}
apply (blast dest!: no_nonce_OR1_OR2 intro: unique_NA)  --{*OR3*}
apply (blast intro!: Crypt_imp_OR1)  --{*OR4*}
done


text{*Corollary: if A receives B's OR4 message and the nonce NA agrees
  then the key really did come from the Server!  CANNOT prove this of the
  bad form of this protocol, even though we can prove
  Spy_not_see_encrypted_key*}
lemma A_trusts_OR4:
     "[| Says A  B {|NA, Agent A, Agent B,
                     Crypt (shrK A) {|NA, Agent A, Agent B|}|} \<in> set evs;
         Says B' A {|NA, Crypt (shrK A) {|NA, Key K|}|} \<in> set evs;
     A \<notin> bad;  evs \<in> otway |]
  ==> \<exists>NB. Says Server B
               {|NA,
                 Crypt (shrK A) {|NA, Key K|},
                 Crypt (shrK B) {|NB, Key K|}|}
                 \<in> set evs"
by (blast intro!: NA_Crypt_imp_Server_msg)


text{*Crucial secrecy property: Spy does not see the keys sent in msg OR3
    Does not in itself guarantee security: an attack could violate
    the premises, e.g. by having @{term "A=Spy"}*}
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
apply (simp_all add: analz_insert_eq analz_insert_freshK pushes)
apply spy_analz  --{*Fake*}
apply (blast dest: unique_session_keys)+  --{*OR3, OR4, Oops*}
done

theorem Spy_not_see_encrypted_key:
     "[| Says Server B
          {|NA, Crypt (shrK A) {|NA, Key K|},
                Crypt (shrK B) {|NB, Key K|}|} \<in> set evs;
         Notes Spy {|NA, NB, Key K|} \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> otway |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest: Says_Server_message_form secrecy_lemma)

text{*This form is an immediate consequence of the previous result.  It is 
similar to the assertions established by other methods.  It is equivalent
to the previous result in that the Spy already has @{term analz} and
@{term synth} at his disposal.  However, the conclusion 
@{term "Key K \<notin> knows Spy evs"} appears not to be inductive: all the cases
other than Fake are trivial, while Fake requires 
@{term "Key K \<notin> analz (knows Spy evs)"}. *}
lemma Spy_not_know_encrypted_key:
     "[| Says Server B
          {|NA, Crypt (shrK A) {|NA, Key K|},
                Crypt (shrK B) {|NB, Key K|}|} \<in> set evs;
         Notes Spy {|NA, NB, Key K|} \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> otway |]
      ==> Key K \<notin> knows Spy evs"
by (blast dest: Spy_not_see_encrypted_key)


text{*A's guarantee.  The Oops premise quantifies over NB because A cannot know
  what it is.*}
lemma A_gets_good_key:
     "[| Says A  B {|NA, Agent A, Agent B,
                     Crypt (shrK A) {|NA, Agent A, Agent B|}|} \<in> set evs;
         Says B' A {|NA, Crypt (shrK A) {|NA, Key K|}|} \<in> set evs;
         \<forall>NB. Notes Spy {|NA, NB, Key K|} \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> otway |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: A_trusts_OR4 Spy_not_see_encrypted_key)


subsection{*Authenticity properties relating to NB*}

text{*Only OR2 can have caused such a part of a message to appear.  We do not
  know anything about X: it does NOT have to have the right form.*}
lemma Crypt_imp_OR2:
     "[| Crypt (shrK B) {|NA, NB, Agent A, Agent B|} \<in> parts (knows Spy evs);
         B \<notin> bad;  evs \<in> otway |]
      ==> \<exists>X. Says B Server
                 {|NA, Agent A, Agent B, X,
                   Crypt (shrK B) {|NA, NB, Agent A, Agent B|}|}
                 \<in> set evs"
apply (erule rev_mp)
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all, blast+)
done


text{*The Nonce NB uniquely identifies B's  message*}
lemma unique_NB:
     "[| Crypt (shrK B) {|NA, NB, Agent A, Agent B|} \<in> parts(knows Spy evs);
         Crypt (shrK B) {|NC, NB, Agent C, Agent B|} \<in> parts(knows Spy evs);
           evs \<in> otway;  B \<notin> bad |]
         ==> NC = NA & C = A"
apply (erule rev_mp, erule rev_mp)
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all)
apply blast+  --{*Fake, OR2*}
done

text{*If the encrypted message appears, and B has used Nonce NB,
  then it originated with the Server!  Quite messy proof.*}
lemma NB_Crypt_imp_Server_msg [rule_format]:
 "[| B \<notin> bad;  evs \<in> otway |]
  ==> Crypt (shrK B) {|NB, Key K|} \<in> parts (knows Spy evs)
      --> (\<forall>X'. Says B Server
                     {|NA, Agent A, Agent B, X',
                       Crypt (shrK B) {|NA, NB, Agent A, Agent B|}|}
           \<in> set evs
           --> Says Server B
                {|NA, Crypt (shrK A) {|NA, Key K|},
                      Crypt (shrK B) {|NB, Key K|}|}
                    \<in> set evs)"
apply simp
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all)
apply blast  --{*Fake*}
apply blast  --{*OR2*}
apply (blast dest: unique_NB dest!: no_nonce_OR1_OR2)  --{*OR3*}
apply (blast dest!: Crypt_imp_OR2)  --{*OR4*}
done


text{*Guarantee for B: if it gets a message with matching NB then the Server
  has sent the correct message.*}
theorem B_trusts_OR3:
     "[| Says B Server {|NA, Agent A, Agent B, X',
                         Crypt (shrK B) {|NA, NB, Agent A, Agent B|} |}
           \<in> set evs;
         Gets B {|NA, X, Crypt (shrK B) {|NB, Key K|}|} \<in> set evs;
         B \<notin> bad;  evs \<in> otway |]
      ==> Says Server B
               {|NA,
                 Crypt (shrK A) {|NA, Key K|},
                 Crypt (shrK B) {|NB, Key K|}|}
                 \<in> set evs"
by (blast intro!: NB_Crypt_imp_Server_msg)


text{*The obvious combination of @{text B_trusts_OR3} with 
      @{text Spy_not_see_encrypted_key}*}
lemma B_gets_good_key:
     "[| Says B Server {|NA, Agent A, Agent B, X',
                         Crypt (shrK B) {|NA, NB, Agent A, Agent B|} |}
           \<in> set evs;
         Gets B {|NA, X, Crypt (shrK B) {|NB, Key K|}|} \<in> set evs;
         Notes Spy {|NA, NB, Key K|} \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> otway |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: B_trusts_OR3 Spy_not_see_encrypted_key)


lemma OR3_imp_OR2:
     "[| Says Server B
              {|NA, Crypt (shrK A) {|NA, Key K|},
                Crypt (shrK B) {|NB, Key K|}|} \<in> set evs;
         B \<notin> bad;  evs \<in> otway |]
  ==> \<exists>X. Says B Server {|NA, Agent A, Agent B, X,
                            Crypt (shrK B) {|NA, NB, Agent A, Agent B|} |}
              \<in> set evs"
apply (erule rev_mp)
apply (erule otway.induct, simp_all)
apply (blast dest!: Crypt_imp_OR2)+
done


text{*After getting and checking OR4, agent A can trust that B has been active.
  We could probably prove that X has the expected form, but that is not
  strictly necessary for authentication.*}
theorem A_auths_B:
     "[| Says B' A {|NA, Crypt (shrK A) {|NA, Key K|}|} \<in> set evs;
         Says A  B {|NA, Agent A, Agent B,
                     Crypt (shrK A) {|NA, Agent A, Agent B|}|} \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> otway |]
  ==> \<exists>NB X. Says B Server {|NA, Agent A, Agent B, X,
                               Crypt (shrK B)  {|NA, NB, Agent A, Agent B|} |}
                 \<in> set evs"
by (blast dest!: A_trusts_OR4 OR3_imp_OR2)

end
