(*  Title:      HOL/Auth/OtwayRees_Bad
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)


header{*The Otway-Rees Protocol: The Faulty BAN Version*}

theory OtwayRees_Bad = Public:

text{*The FAULTY version omitting encryption of Nonce NB, as suggested on 
page 247 of
  Burrows, Abadi and Needham (1988).  A Logic of Authentication.
  Proc. Royal Soc. 426

This file illustrates the consequences of such errors.  We can still prove
impressive-looking properties such as @{text Spy_not_see_encrypted_key}, yet
the protocol is open to a middleperson attack.  Attempting to prove some key
lemmas indicates the possibility of this attack.*}

consts  otway   :: "event list set"
inductive "otway"
  intros
   Nil: --{*The empty trace*}
        "[] \<in> otway"

   Fake: --{*The Spy may say anything he can say.  The sender field is correct,
            but agents don't use that information.*}
         "[| evsf \<in> otway;  X \<in> synth (analz (knows Spy evsf)) |]
          ==> Says Spy B X  # evsf \<in> otway"

        
   Reception: --{*A message that has been sent can be received by the
                  intended recipient.*}
	      "[| evsr \<in> otway;  Says A B X \<in>set evsr |]
               ==> Gets B X # evsr \<in> otway"

   OR1:  --{*Alice initiates a protocol run*}
	 "[| evs1 \<in> otway;  Nonce NA \<notin> used evs1 |]
          ==> Says A B {|Nonce NA, Agent A, Agent B,
                         Crypt (shrK A) {|Nonce NA, Agent A, Agent B|} |}
                 # evs1 \<in> otway"

   OR2:  --{*Bob's response to Alice's message.
             This variant of the protocol does NOT encrypt NB.*}
	 "[| evs2 \<in> otway;  Nonce NB \<notin> used evs2;
             Gets B {|Nonce NA, Agent A, Agent B, X|} \<in> set evs2 |]
          ==> Says B Server
                  {|Nonce NA, Agent A, Agent B, X, Nonce NB,
                    Crypt (shrK B) {|Nonce NA, Agent A, Agent B|}|}
                 # evs2 \<in> otway"

   OR3:  --{*The Server receives Bob's message and checks that the three NAs
           match.  Then he sends a new session key to Bob with a packet for
           forwarding to Alice.*}
	 "[| evs3 \<in> otway;  Key KAB \<notin> used evs3;
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

   OR4:  --{*Bob receives the Server's (?) message and compares the Nonces with
	     those in the message he previously sent the Server.
             Need @{term "B \<noteq> Server"} because we allow messages to self.*}
	 "[| evs4 \<in> otway;  B \<noteq> Server;
             Says B Server {|Nonce NA, Agent A, Agent B, X', Nonce NB,
                             Crypt (shrK B) {|Nonce NA, Agent A, Agent B|}|}
               \<in> set evs4;
             Gets B {|Nonce NA, X, Crypt (shrK B) {|Nonce NB, Key K|}|}
               \<in> set evs4 |]
          ==> Says B A {|Nonce NA, X|} # evs4 \<in> otway"

   Oops: --{*This message models possible leaks of session keys.  The nonces
             identify the protocol run.*}
	 "[| evso \<in> otway;
             Says Server B {|Nonce NA, X, Crypt (shrK B) {|Nonce NB, Key K|}|}
               \<in> set evso |]
          ==> Notes Spy {|Nonce NA, Nonce NB, Key K|} # evso \<in> otway"


declare Says_imp_knows_Spy [THEN analz.Inj, dest]
declare parts.Body  [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un  [dest]

text{*A "possibility property": there are traces that reach the end*}
lemma "[| B \<noteq> Server; Key K \<notin> used [] |]
      ==> \<exists>NA. \<exists>evs \<in> otway.
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


subsection{*For reasoning about the encrypted portion of messages *}

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

text{*Forwarding lemma: see comments in OtwayRees.thy*}
lemmas OR2_parts_knows_Spy =
    OR2_analz_knows_Spy [THEN analz_into_parts, standard]


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


subsection{*Proofs involving analz *}

text{*Describes the form of K and NA when the Server sends this message.  Also
  for Oops case.*}
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


text{*Crucial secrecy property: Spy does not see the keys sent in msg OR3
    Does not in itself guarantee security: an attack could violate
    the premises, e.g. by having @{term "A=Spy"} *}
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


lemma Spy_not_see_encrypted_key:
     "[| Says Server B
          {|NA, Crypt (shrK A) {|NA, Key K|},
                Crypt (shrK B) {|NB, Key K|}|} \<in> set evs;
         Notes Spy {|NA, NB, Key K|} \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> otway |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest: Says_Server_message_form secrecy_lemma)


subsection{*Attempting to prove stronger properties *}

text{*Only OR1 can have caused such a part of a message to appear. The premise
  @{term "A \<noteq> B"} prevents OR2's similar-looking cryptogram from being picked 
  up. Original Otway-Rees doesn't need it.*}
lemma Crypt_imp_OR1 [rule_format]:
     "[| A \<notin> bad;  A \<noteq> B;  evs \<in> otway |]
      ==> Crypt (shrK A) {|NA, Agent A, Agent B|} \<in> parts (knows Spy evs) -->
          Says A B {|NA, Agent A, Agent B,
                     Crypt (shrK A) {|NA, Agent A, Agent B|}|}  \<in> set evs"
by (erule otway.induct, force,
    drule_tac [4] OR2_parts_knows_Spy, simp_all, blast+)


text{*Crucial property: If the encrypted message appears, and A has used NA
  to start a run, then it originated with the Server!
  The premise @{term "A \<noteq> B"} allows use of @{text Crypt_imp_OR1}*}
text{*Only it is FALSE.  Somebody could make a fake message to Server
          substituting some other nonce NA' for NB.*}
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
apply blast  --{*Fake*}
apply blast  --{*OR1: it cannot be a new Nonce, contradiction.*}
txt{*OR3 and OR4*}
apply (simp_all add: ex_disj_distrib)
 prefer 2 apply (blast intro!: Crypt_imp_OR1)  --{*OR4*}
txt{*OR3*}
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
