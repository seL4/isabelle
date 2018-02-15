(*  Title:      HOL/Auth/OtwayRees.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

section\<open>The Original Otway-Rees Protocol\<close>

theory OtwayRees imports Public begin

text\<open>From page 244 of
  Burrows, Abadi and Needham (1989).  A Logic of Authentication.
  Proc. Royal Soc. 426

This is the original version, which encrypts Nonce NB.\<close>

inductive_set otway :: "event list set"
  where
         (*Initial trace is empty*)
   Nil:  "[] \<in> otway"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
 | Fake: "\<lbrakk>evsf \<in> otway;  X \<in> synth (analz (knows Spy evsf)) \<rbrakk>
          \<Longrightarrow> Says Spy B X  # evsf \<in> otway"

         (*A message that has been sent can be received by the
           intended recipient.*)
 | Reception: "\<lbrakk>evsr \<in> otway;  Says A B X \<in>set evsr\<rbrakk>
               \<Longrightarrow> Gets B X # evsr \<in> otway"

         (*Alice initiates a protocol run*)
 | OR1:  "\<lbrakk>evs1 \<in> otway;  Nonce NA \<notin> used evs1\<rbrakk>
          \<Longrightarrow> Says A B \<lbrace>Nonce NA, Agent A, Agent B,
                         Crypt (shrK A) \<lbrace>Nonce NA, Agent A, Agent B\<rbrace> \<rbrace>
                 # evs1 \<in> otway"

         (*Bob's response to Alice's message.  Note that NB is encrypted.*)
 | OR2:  "\<lbrakk>evs2 \<in> otway;  Nonce NB \<notin> used evs2;
             Gets B \<lbrace>Nonce NA, Agent A, Agent B, X\<rbrace> \<in> set evs2\<rbrakk>
          \<Longrightarrow> Says B Server
                  \<lbrace>Nonce NA, Agent A, Agent B, X,
                    Crypt (shrK B)
                      \<lbrace>Nonce NA, Nonce NB, Agent A, Agent B\<rbrace>\<rbrace>
                 # evs2 \<in> otway"

         (*The Server receives Bob's message and checks that the three NAs
           match.  Then he sends a new session key to Bob with a packet for
           forwarding to Alice.*)
 | OR3:  "\<lbrakk>evs3 \<in> otway;  Key KAB \<notin> used evs3;
             Gets Server
                  \<lbrace>Nonce NA, Agent A, Agent B,
                    Crypt (shrK A) \<lbrace>Nonce NA, Agent A, Agent B\<rbrace>,
                    Crypt (shrK B) \<lbrace>Nonce NA, Nonce NB, Agent A, Agent B\<rbrace>\<rbrace>
               \<in> set evs3\<rbrakk>
          \<Longrightarrow> Says Server B
                  \<lbrace>Nonce NA,
                    Crypt (shrK A) \<lbrace>Nonce NA, Key KAB\<rbrace>,
                    Crypt (shrK B) \<lbrace>Nonce NB, Key KAB\<rbrace>\<rbrace>
                 # evs3 \<in> otway"

         (*Bob receives the Server's (?) message and compares the Nonces with
           those in the message he previously sent the Server.
           Need B \<noteq> Server because we allow messages to self.*)
 | OR4:  "\<lbrakk>evs4 \<in> otway;  B \<noteq> Server;
             Says B Server \<lbrace>Nonce NA, Agent A, Agent B, X',
                             Crypt (shrK B)
                                   \<lbrace>Nonce NA, Nonce NB, Agent A, Agent B\<rbrace>\<rbrace>
               \<in> set evs4;
             Gets B \<lbrace>Nonce NA, X, Crypt (shrK B) \<lbrace>Nonce NB, Key K\<rbrace>\<rbrace>
               \<in> set evs4\<rbrakk>
          \<Longrightarrow> Says B A \<lbrace>Nonce NA, X\<rbrace> # evs4 \<in> otway"

         (*This message models possible leaks of session keys.  The nonces
           identify the protocol run.*)
 | Oops: "\<lbrakk>evso \<in> otway;
             Says Server B \<lbrace>Nonce NA, X, Crypt (shrK B) \<lbrace>Nonce NB, Key K\<rbrace>\<rbrace>
               \<in> set evso\<rbrakk>
          \<Longrightarrow> Notes Spy \<lbrace>Nonce NA, Nonce NB, Key K\<rbrace> # evso \<in> otway"


declare Says_imp_analz_Spy [dest]
declare parts.Body  [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un  [dest]


text\<open>A "possibility property": there are traces that reach the end\<close>
lemma "\<lbrakk>B \<noteq> Server; Key K \<notin> used []\<rbrakk>
      \<Longrightarrow> \<exists>evs \<in> otway.
             Says B A \<lbrace>Nonce NA, Crypt (shrK A) \<lbrace>Nonce NA, Key K\<rbrace>\<rbrace>
               \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] otway.Nil
                    [THEN otway.OR1, THEN otway.Reception,
                     THEN otway.OR2, THEN otway.Reception,
                     THEN otway.OR3, THEN otway.Reception, THEN otway.OR4]) 
apply (possibility, simp add: used_Cons) 
done

lemma Gets_imp_Says [dest!]:
     "\<lbrakk>Gets B X \<in> set evs; evs \<in> otway\<rbrakk> \<Longrightarrow> \<exists>A. Says A B X \<in> set evs"
apply (erule rev_mp)
apply (erule otway.induct, auto)
done


(** For reasoning about the encrypted portion of messages **)

lemma OR2_analz_knows_Spy:
     "\<lbrakk>Gets B \<lbrace>N, Agent A, Agent B, X\<rbrace> \<in> set evs;  evs \<in> otway\<rbrakk>
      \<Longrightarrow> X \<in> analz (knows Spy evs)"
by blast

lemma OR4_analz_knows_Spy:
     "\<lbrakk>Gets B \<lbrace>N, X, Crypt (shrK B) X'\<rbrace> \<in> set evs;  evs \<in> otway\<rbrakk>
      \<Longrightarrow> X \<in> analz (knows Spy evs)"
by blast

(*These lemmas assist simplification by removing forwarded X-variables.
  We can replace them by rewriting with parts_insert2 and proving using
  dest: parts_cut, but the proofs become more difficult.*)
lemmas OR2_parts_knows_Spy =
    OR2_analz_knows_Spy [THEN analz_into_parts]

(*There could be OR4_parts_knows_Spy and Oops_parts_knows_Spy, but for
  some reason proofs work without them!*)


text\<open>Theorems of the form @{term "X \<notin> parts (spies evs)"} imply that
NOBODY sends messages containing X!\<close>

text\<open>Spy never sees a good agent's shared key!\<close>
lemma Spy_see_shrK [simp]:
     "evs \<in> otway \<Longrightarrow> (Key (shrK A) \<in> parts (knows Spy evs)) = (A \<in> bad)"
by (erule otway.induct, force,
    drule_tac [4] OR2_parts_knows_Spy, simp_all, blast+)


lemma Spy_analz_shrK [simp]:
     "evs \<in> otway \<Longrightarrow> (Key (shrK A) \<in> analz (knows Spy evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "\<lbrakk>Key (shrK A) \<in> parts (knows Spy evs);  evs \<in> otway\<rbrakk> \<Longrightarrow> A \<in> bad"
by (blast dest: Spy_see_shrK)


subsection\<open>Towards Secrecy: Proofs Involving @{term analz}\<close>

(*Describes the form of K and NA when the Server sends this message.  Also
  for Oops case.*)
lemma Says_Server_message_form:
     "\<lbrakk>Says Server B \<lbrace>NA, X, Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace> \<in> set evs;
         evs \<in> otway\<rbrakk>
      \<Longrightarrow> K \<notin> range shrK \<and> (\<exists>i. NA = Nonce i) \<and> (\<exists>j. NB = Nonce j)"
by (erule rev_mp, erule otway.induct, simp_all)


(****
 The following is to prove theorems of the form

  Key K \<in> analz (insert (Key KAB) (knows Spy evs)) \<Longrightarrow>
  Key K \<in> analz (knows Spy evs)

 A more general formula must be proved inductively.
****)


text\<open>Session keys are not used to encrypt other session keys\<close>

text\<open>The equality makes the induction hypothesis easier to apply\<close>
lemma analz_image_freshK [rule_format]:
 "evs \<in> otway \<Longrightarrow>
   \<forall>K KK. KK \<subseteq> -(range shrK) \<longrightarrow>
          (Key K \<in> analz (Key`KK \<union> (knows Spy evs))) =
          (K \<in> KK | Key K \<in> analz (knows Spy evs))"
apply (erule otway.induct)
apply (frule_tac [8] Says_Server_message_form)
apply (drule_tac [7] OR4_analz_knows_Spy)
apply (drule_tac [5] OR2_analz_knows_Spy, analz_freshK, spy_analz, auto) 
done

lemma analz_insert_freshK:
  "\<lbrakk>evs \<in> otway;  KAB \<notin> range shrK\<rbrakk> \<Longrightarrow>
      (Key K \<in> analz (insert (Key KAB) (knows Spy evs))) =
      (K = KAB | Key K \<in> analz (knows Spy evs))"
by (simp only: analz_image_freshK analz_image_freshK_simps)


text\<open>The Key K uniquely identifies the Server's  message.\<close>
lemma unique_session_keys:
     "\<lbrakk>Says Server B \<lbrace>NA, X, Crypt (shrK B) \<lbrace>NB, K\<rbrace>\<rbrace>   \<in> set evs;
         Says Server B' \<lbrace>NA',X',Crypt (shrK B') \<lbrace>NB',K\<rbrace>\<rbrace> \<in> set evs;
         evs \<in> otway\<rbrakk> \<Longrightarrow> X=X' \<and> B=B' \<and> NA=NA' \<and> NB=NB'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule otway.induct, simp_all)
apply blast+  \<comment> \<open>OR3 and OR4\<close>
done


subsection\<open>Authenticity properties relating to NA\<close>

text\<open>Only OR1 can have caused such a part of a message to appear.\<close>
lemma Crypt_imp_OR1 [rule_format]:
 "\<lbrakk>A \<notin> bad;  evs \<in> otway\<rbrakk>
  \<Longrightarrow> Crypt (shrK A) \<lbrace>NA, Agent A, Agent B\<rbrace> \<in> parts (knows Spy evs) \<longrightarrow>
      Says A B \<lbrace>NA, Agent A, Agent B,
                 Crypt (shrK A) \<lbrace>NA, Agent A, Agent B\<rbrace>\<rbrace>
        \<in> set evs"
by (erule otway.induct, force,
    drule_tac [4] OR2_parts_knows_Spy, simp_all, blast+)

lemma Crypt_imp_OR1_Gets:
     "\<lbrakk>Gets B \<lbrace>NA, Agent A, Agent B,
                  Crypt (shrK A) \<lbrace>NA, Agent A, Agent B\<rbrace>\<rbrace> \<in> set evs;
         A \<notin> bad; evs \<in> otway\<rbrakk>
       \<Longrightarrow> Says A B \<lbrace>NA, Agent A, Agent B,
                      Crypt (shrK A) \<lbrace>NA, Agent A, Agent B\<rbrace>\<rbrace>
             \<in> set evs"
by (blast dest: Crypt_imp_OR1)


text\<open>The Nonce NA uniquely identifies A's message\<close>
lemma unique_NA:
     "\<lbrakk>Crypt (shrK A) \<lbrace>NA, Agent A, Agent B\<rbrace> \<in> parts (knows Spy evs);
         Crypt (shrK A) \<lbrace>NA, Agent A, Agent C\<rbrace> \<in> parts (knows Spy evs);
         evs \<in> otway;  A \<notin> bad\<rbrakk>
      \<Longrightarrow> B = C"
apply (erule rev_mp, erule rev_mp)
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all, blast+)
done


text\<open>It is impossible to re-use a nonce in both OR1 and OR2.  This holds because
  OR2 encrypts Nonce NB.  It prevents the attack that can occur in the
  over-simplified version of this protocol: see \<open>OtwayRees_Bad\<close>.\<close>
lemma no_nonce_OR1_OR2:
   "\<lbrakk>Crypt (shrK A) \<lbrace>NA, Agent A, Agent B\<rbrace> \<in> parts (knows Spy evs);
       A \<notin> bad;  evs \<in> otway\<rbrakk>
    \<Longrightarrow> Crypt (shrK A) \<lbrace>NA', NA, Agent A', Agent A\<rbrace> \<notin> parts (knows Spy evs)"
apply (erule rev_mp)
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all, blast+)
done

text\<open>Crucial property: If the encrypted message appears, and A has used NA
  to start a run, then it originated with the Server!\<close>
lemma NA_Crypt_imp_Server_msg [rule_format]:
     "\<lbrakk>A \<notin> bad;  evs \<in> otway\<rbrakk>
      \<Longrightarrow> Says A B \<lbrace>NA, Agent A, Agent B,
                     Crypt (shrK A) \<lbrace>NA, Agent A, Agent B\<rbrace>\<rbrace> \<in> set evs \<longrightarrow>
          Crypt (shrK A) \<lbrace>NA, Key K\<rbrace> \<in> parts (knows Spy evs)
          \<longrightarrow> (\<exists>NB. Says Server B
                         \<lbrace>NA,
                           Crypt (shrK A) \<lbrace>NA, Key K\<rbrace>,
                           Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace> \<in> set evs)"
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all, blast)
  subgoal \<comment> \<open>OR1: by freshness\<close>
    by blast  
  subgoal \<comment> \<open>OR3\<close>
    by (blast dest!: no_nonce_OR1_OR2 intro: unique_NA)
  subgoal \<comment> \<open>OR4\<close>
    by (blast intro!: Crypt_imp_OR1) 
done


text\<open>Corollary: if A receives B's OR4 message and the nonce NA agrees
  then the key really did come from the Server!  CANNOT prove this of the
  bad form of this protocol, even though we can prove
  \<open>Spy_not_see_encrypted_key\<close>\<close>
lemma A_trusts_OR4:
     "\<lbrakk>Says A  B \<lbrace>NA, Agent A, Agent B,
                     Crypt (shrK A) \<lbrace>NA, Agent A, Agent B\<rbrace>\<rbrace> \<in> set evs;
         Says B' A \<lbrace>NA, Crypt (shrK A) \<lbrace>NA, Key K\<rbrace>\<rbrace> \<in> set evs;
     A \<notin> bad;  evs \<in> otway\<rbrakk>
  \<Longrightarrow> \<exists>NB. Says Server B
               \<lbrace>NA,
                 Crypt (shrK A) \<lbrace>NA, Key K\<rbrace>,
                 Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace>
                 \<in> set evs"
by (blast intro!: NA_Crypt_imp_Server_msg)


text\<open>Crucial secrecy property: Spy does not see the keys sent in msg OR3
    Does not in itself guarantee security: an attack could violate
    the premises, e.g. by having @{term "A=Spy"}\<close>
lemma secrecy_lemma:
 "\<lbrakk>A \<notin> bad;  B \<notin> bad;  evs \<in> otway\<rbrakk>
  \<Longrightarrow> Says Server B
        \<lbrace>NA, Crypt (shrK A) \<lbrace>NA, Key K\<rbrace>,
          Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace> \<in> set evs \<longrightarrow>
      Notes Spy \<lbrace>NA, NB, Key K\<rbrace> \<notin> set evs \<longrightarrow>
      Key K \<notin> analz (knows Spy evs)"
  apply (erule otway.induct, force, simp_all)
  subgoal \<comment> \<open>Fake\<close>
    by spy_analz
  subgoal \<comment> \<open>OR2\<close>
    by (drule OR2_analz_knows_Spy) (auto simp: analz_insert_eq)
  subgoal \<comment> \<open>OR3\<close>
    by (auto simp add: analz_insert_freshK pushes)
  subgoal \<comment> \<open>OR4\<close>
    by (drule OR4_analz_knows_Spy) (auto simp: analz_insert_eq)
  subgoal \<comment> \<open>Oops\<close>
    by (auto simp add: Says_Server_message_form analz_insert_freshK unique_session_keys)
  done

theorem Spy_not_see_encrypted_key:
     "\<lbrakk>Says Server B
          \<lbrace>NA, Crypt (shrK A) \<lbrace>NA, Key K\<rbrace>,
                Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace> \<in> set evs;
         Notes Spy \<lbrace>NA, NB, Key K\<rbrace> \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> otway\<rbrakk>
      \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
by (blast dest: Says_Server_message_form secrecy_lemma)

text\<open>This form is an immediate consequence of the previous result.  It is 
similar to the assertions established by other methods.  It is equivalent
to the previous result in that the Spy already has @{term analz} and
@{term synth} at his disposal.  However, the conclusion 
@{term "Key K \<notin> knows Spy evs"} appears not to be inductive: all the cases
other than Fake are trivial, while Fake requires 
@{term "Key K \<notin> analz (knows Spy evs)"}.\<close>
lemma Spy_not_know_encrypted_key:
     "\<lbrakk>Says Server B
          \<lbrace>NA, Crypt (shrK A) \<lbrace>NA, Key K\<rbrace>,
                Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace> \<in> set evs;
         Notes Spy \<lbrace>NA, NB, Key K\<rbrace> \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> otway\<rbrakk>
      \<Longrightarrow> Key K \<notin> knows Spy evs"
by (blast dest: Spy_not_see_encrypted_key)


text\<open>A's guarantee.  The Oops premise quantifies over NB because A cannot know
  what it is.\<close>
lemma A_gets_good_key:
     "\<lbrakk>Says A  B \<lbrace>NA, Agent A, Agent B,
                     Crypt (shrK A) \<lbrace>NA, Agent A, Agent B\<rbrace>\<rbrace> \<in> set evs;
         Says B' A \<lbrace>NA, Crypt (shrK A) \<lbrace>NA, Key K\<rbrace>\<rbrace> \<in> set evs;
         \<forall>NB. Notes Spy \<lbrace>NA, NB, Key K\<rbrace> \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> otway\<rbrakk>
      \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: A_trusts_OR4 Spy_not_see_encrypted_key)


subsection\<open>Authenticity properties relating to NB\<close>

text\<open>Only OR2 can have caused such a part of a message to appear.  We do not
  know anything about X: it does NOT have to have the right form.\<close>
lemma Crypt_imp_OR2:
     "\<lbrakk>Crypt (shrK B) \<lbrace>NA, NB, Agent A, Agent B\<rbrace> \<in> parts (knows Spy evs);
         B \<notin> bad;  evs \<in> otway\<rbrakk>
      \<Longrightarrow> \<exists>X. Says B Server
                 \<lbrace>NA, Agent A, Agent B, X,
                   Crypt (shrK B) \<lbrace>NA, NB, Agent A, Agent B\<rbrace>\<rbrace>
                 \<in> set evs"
apply (erule rev_mp)
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all, blast+)
done


text\<open>The Nonce NB uniquely identifies B's  message\<close>
lemma unique_NB:
     "\<lbrakk>Crypt (shrK B) \<lbrace>NA, NB, Agent A, Agent B\<rbrace> \<in> parts(knows Spy evs);
         Crypt (shrK B) \<lbrace>NC, NB, Agent C, Agent B\<rbrace> \<in> parts(knows Spy evs);
           evs \<in> otway;  B \<notin> bad\<rbrakk>
         \<Longrightarrow> NC = NA \<and> C = A"
apply (erule rev_mp, erule rev_mp)
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all)
apply blast+  \<comment> \<open>Fake, OR2\<close>
done

text\<open>If the encrypted message appears, and B has used Nonce NB,
  then it originated with the Server!  Quite messy proof.\<close>
lemma NB_Crypt_imp_Server_msg [rule_format]:
 "\<lbrakk>B \<notin> bad;  evs \<in> otway\<rbrakk>
  \<Longrightarrow> Crypt (shrK B) \<lbrace>NB, Key K\<rbrace> \<in> parts (knows Spy evs)
      \<longrightarrow> (\<forall>X'. Says B Server
                     \<lbrace>NA, Agent A, Agent B, X',
                       Crypt (shrK B) \<lbrace>NA, NB, Agent A, Agent B\<rbrace>\<rbrace>
           \<in> set evs
           \<longrightarrow> Says Server B
                \<lbrace>NA, Crypt (shrK A) \<lbrace>NA, Key K\<rbrace>,
                      Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace>
                    \<in> set evs)"
apply simp
apply (erule otway.induct, force, simp_all)
  subgoal \<comment> \<open>Fake\<close>
    by blast 
  subgoal \<comment> \<open>OR2\<close>
    by (force dest!: OR2_parts_knows_Spy)
  subgoal \<comment> \<open>OR3\<close>
    by (blast dest: unique_NB dest!: no_nonce_OR1_OR2)  \<comment> \<open>OR3\<close>
  subgoal \<comment> \<open>OR4\<close>
    by (blast dest!: Crypt_imp_OR2) 
done


text\<open>Guarantee for B: if it gets a message with matching NB then the Server
  has sent the correct message.\<close>
theorem B_trusts_OR3:
     "\<lbrakk>Says B Server \<lbrace>NA, Agent A, Agent B, X',
                         Crypt (shrK B) \<lbrace>NA, NB, Agent A, Agent B\<rbrace>\<rbrace>
           \<in> set evs;
         Gets B \<lbrace>NA, X, Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace> \<in> set evs;
         B \<notin> bad;  evs \<in> otway\<rbrakk>
      \<Longrightarrow> Says Server B
               \<lbrace>NA,
                 Crypt (shrK A) \<lbrace>NA, Key K\<rbrace>,
                 Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace>
                 \<in> set evs"
by (blast intro!: NB_Crypt_imp_Server_msg)


text\<open>The obvious combination of \<open>B_trusts_OR3\<close> with 
      \<open>Spy_not_see_encrypted_key\<close>\<close>
lemma B_gets_good_key:
     "\<lbrakk>Says B Server \<lbrace>NA, Agent A, Agent B, X',
                         Crypt (shrK B) \<lbrace>NA, NB, Agent A, Agent B\<rbrace>\<rbrace>
           \<in> set evs;
         Gets B \<lbrace>NA, X, Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace> \<in> set evs;
         Notes Spy \<lbrace>NA, NB, Key K\<rbrace> \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> otway\<rbrakk>
      \<Longrightarrow> Key K \<notin> analz (knows Spy evs)"
by (blast dest!: B_trusts_OR3 Spy_not_see_encrypted_key)


lemma OR3_imp_OR2:
     "\<lbrakk>Says Server B
              \<lbrace>NA, Crypt (shrK A) \<lbrace>NA, Key K\<rbrace>,
                Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace> \<in> set evs;
         B \<notin> bad;  evs \<in> otway\<rbrakk>
  \<Longrightarrow> \<exists>X. Says B Server \<lbrace>NA, Agent A, Agent B, X,
                            Crypt (shrK B) \<lbrace>NA, NB, Agent A, Agent B\<rbrace>\<rbrace>
              \<in> set evs"
apply (erule rev_mp)
apply (erule otway.induct, simp_all)
apply (blast dest!: Crypt_imp_OR2)+
done


text\<open>After getting and checking OR4, agent A can trust that B has been active.
  We could probably prove that X has the expected form, but that is not
  strictly necessary for authentication.\<close>
theorem A_auths_B:
     "\<lbrakk>Says B' A \<lbrace>NA, Crypt (shrK A) \<lbrace>NA, Key K\<rbrace>\<rbrace> \<in> set evs;
         Says A  B \<lbrace>NA, Agent A, Agent B,
                     Crypt (shrK A) \<lbrace>NA, Agent A, Agent B\<rbrace>\<rbrace> \<in> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> otway\<rbrakk>
  \<Longrightarrow> \<exists>NB X. Says B Server \<lbrace>NA, Agent A, Agent B, X,
                               Crypt (shrK B)  \<lbrace>NA, NB, Agent A, Agent B\<rbrace>\<rbrace>
                 \<in> set evs"
by (blast dest!: A_trusts_OR4 OR3_imp_OR2)

end
