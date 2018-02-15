(*  Title:      HOL/Auth/OtwayRees_Bad.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)


section\<open>The Otway-Rees Protocol: The Faulty BAN Version\<close>

theory OtwayRees_Bad imports Public begin

text\<open>The FAULTY version omitting encryption of Nonce NB, as suggested on 
page 247 of
  Burrows, Abadi and Needham (1988).  A Logic of Authentication.
  Proc. Royal Soc. 426

This file illustrates the consequences of such errors.  We can still prove
impressive-looking properties such as \<open>Spy_not_see_encrypted_key\<close>, yet
the protocol is open to a middleperson attack.  Attempting to prove some key
lemmas indicates the possibility of this attack.\<close>

inductive_set otway :: "event list set"
  where
   Nil: \<comment> \<open>The empty trace\<close>
        "[] \<in> otway"

 | Fake: \<comment> \<open>The Spy may say anything he can say.  The sender field is correct,
            but agents don't use that information.\<close>
         "[| evsf \<in> otway;  X \<in> synth (analz (knows Spy evsf)) |]
          ==> Says Spy B X  # evsf \<in> otway"

        
 | Reception: \<comment> \<open>A message that has been sent can be received by the
                  intended recipient.\<close>
              "[| evsr \<in> otway;  Says A B X \<in>set evsr |]
               ==> Gets B X # evsr \<in> otway"

 | OR1:  \<comment> \<open>Alice initiates a protocol run\<close>
         "[| evs1 \<in> otway;  Nonce NA \<notin> used evs1 |]
          ==> Says A B \<lbrace>Nonce NA, Agent A, Agent B,
                         Crypt (shrK A) \<lbrace>Nonce NA, Agent A, Agent B\<rbrace>\<rbrace>
                 # evs1 \<in> otway"

 | OR2:  \<comment> \<open>Bob's response to Alice's message.
             This variant of the protocol does NOT encrypt NB.\<close>
         "[| evs2 \<in> otway;  Nonce NB \<notin> used evs2;
             Gets B \<lbrace>Nonce NA, Agent A, Agent B, X\<rbrace> \<in> set evs2 |]
          ==> Says B Server
                  \<lbrace>Nonce NA, Agent A, Agent B, X, Nonce NB,
                    Crypt (shrK B) \<lbrace>Nonce NA, Agent A, Agent B\<rbrace>\<rbrace>
                 # evs2 \<in> otway"

 | OR3:  \<comment> \<open>The Server receives Bob's message and checks that the three NAs
           match.  Then he sends a new session key to Bob with a packet for
           forwarding to Alice.\<close>
         "[| evs3 \<in> otway;  Key KAB \<notin> used evs3;
             Gets Server
                  \<lbrace>Nonce NA, Agent A, Agent B,
                    Crypt (shrK A) \<lbrace>Nonce NA, Agent A, Agent B\<rbrace>,
                    Nonce NB,
                    Crypt (shrK B) \<lbrace>Nonce NA, Agent A, Agent B\<rbrace>\<rbrace>
               \<in> set evs3 |]
          ==> Says Server B
                  \<lbrace>Nonce NA,
                    Crypt (shrK A) \<lbrace>Nonce NA, Key KAB\<rbrace>,
                    Crypt (shrK B) \<lbrace>Nonce NB, Key KAB\<rbrace>\<rbrace>
                 # evs3 \<in> otway"

 | OR4:  \<comment> \<open>Bob receives the Server's (?) message and compares the Nonces with
             those in the message he previously sent the Server.
             Need @{term "B \<noteq> Server"} because we allow messages to self.\<close>
         "[| evs4 \<in> otway;  B \<noteq> Server;
             Says B Server \<lbrace>Nonce NA, Agent A, Agent B, X', Nonce NB,
                             Crypt (shrK B) \<lbrace>Nonce NA, Agent A, Agent B\<rbrace>\<rbrace>
               \<in> set evs4;
             Gets B \<lbrace>Nonce NA, X, Crypt (shrK B) \<lbrace>Nonce NB, Key K\<rbrace>\<rbrace>
               \<in> set evs4 |]
          ==> Says B A \<lbrace>Nonce NA, X\<rbrace> # evs4 \<in> otway"

 | Oops: \<comment> \<open>This message models possible leaks of session keys.  The nonces
             identify the protocol run.\<close>
         "[| evso \<in> otway;
             Says Server B \<lbrace>Nonce NA, X, Crypt (shrK B) \<lbrace>Nonce NB, Key K\<rbrace>\<rbrace>
               \<in> set evso |]
          ==> Notes Spy \<lbrace>Nonce NA, Nonce NB, Key K\<rbrace> # evso \<in> otway"


declare Says_imp_knows_Spy [THEN analz.Inj, dest]
declare parts.Body  [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un  [dest]

text\<open>A "possibility property": there are traces that reach the end\<close>
lemma "[| B \<noteq> Server; Key K \<notin> used [] |]
      ==> \<exists>NA. \<exists>evs \<in> otway.
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
     "[| Gets B X \<in> set evs; evs \<in> otway |] ==> \<exists>A. Says A B X \<in> set evs"
apply (erule rev_mp)
apply (erule otway.induct, auto)
done


subsection\<open>For reasoning about the encrypted portion of messages\<close>

lemma OR2_analz_knows_Spy:
     "[| Gets B \<lbrace>N, Agent A, Agent B, X\<rbrace> \<in> set evs;  evs \<in> otway |]
      ==> X \<in> analz (knows Spy evs)"
by blast

lemma OR4_analz_knows_Spy:
     "[| Gets B \<lbrace>N, X, Crypt (shrK B) X'\<rbrace> \<in> set evs;  evs \<in> otway |]
      ==> X \<in> analz (knows Spy evs)"
by blast

lemma Oops_parts_knows_Spy:
     "Says Server B \<lbrace>NA, X, Crypt K' \<lbrace>NB,K\<rbrace>\<rbrace> \<in> set evs
      ==> K \<in> parts (knows Spy evs)"
by blast

text\<open>Forwarding lemma: see comments in OtwayRees.thy\<close>
lemmas OR2_parts_knows_Spy =
    OR2_analz_knows_Spy [THEN analz_into_parts]


text\<open>Theorems of the form @{term "X \<notin> parts (spies evs)"} imply that
NOBODY sends messages containing X!\<close>

text\<open>Spy never sees a good agent's shared key!\<close>
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


subsection\<open>Proofs involving analz\<close>

text\<open>Describes the form of K and NA when the Server sends this message.  Also
  for Oops case.\<close>
lemma Says_Server_message_form:
     "[| Says Server B \<lbrace>NA, X, Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace> \<in> set evs;
         evs \<in> otway |]
      ==> K \<notin> range shrK \<and> (\<exists>i. NA = Nonce i) \<and> (\<exists>j. NB = Nonce j)"
apply (erule rev_mp)
apply (erule otway.induct, simp_all)
done


(****
 The following is to prove theorems of the form

  Key K \<in> analz (insert (Key KAB) (knows Spy evs)) ==>
  Key K \<in> analz (knows Spy evs)

 A more general formula must be proved inductively.
****)


text\<open>Session keys are not used to encrypt other session keys\<close>

text\<open>The equality makes the induction hypothesis easier to apply\<close>
lemma analz_image_freshK [rule_format]:
 "evs \<in> otway ==>
   \<forall>K KK. KK \<subseteq> -(range shrK) \<longrightarrow>
          (Key K \<in> analz (Key`KK \<union> (knows Spy evs))) =
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


text\<open>The Key K uniquely identifies the Server's  message.\<close>
lemma unique_session_keys:
     "[| Says Server B \<lbrace>NA, X, Crypt (shrK B) \<lbrace>NB, K\<rbrace>\<rbrace>   \<in> set evs;
         Says Server B' \<lbrace>NA',X',Crypt (shrK B') \<lbrace>NB',K\<rbrace>\<rbrace> \<in> set evs;
         evs \<in> otway |] ==> X=X' \<and> B=B' \<and> NA=NA' \<and> NB=NB'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule otway.induct, simp_all)
apply blast+  \<comment> \<open>OR3 and OR4\<close>
done


text\<open>Crucial secrecy property: Spy does not see the keys sent in msg OR3
    Does not in itself guarantee security: an attack could violate
    the premises, e.g. by having @{term "A=Spy"}\<close>
lemma secrecy_lemma:
 "[| A \<notin> bad;  B \<notin> bad;  evs \<in> otway |]
  ==> Says Server B
        \<lbrace>NA, Crypt (shrK A) \<lbrace>NA, Key K\<rbrace>,
          Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace> \<in> set evs \<longrightarrow>
      Notes Spy \<lbrace>NA, NB, Key K\<rbrace> \<notin> set evs \<longrightarrow>
      Key K \<notin> analz (knows Spy evs)"
apply (erule otway.induct, force)
apply (frule_tac [7] Says_Server_message_form)
apply (drule_tac [6] OR4_analz_knows_Spy)
apply (drule_tac [4] OR2_analz_knows_Spy)
apply (simp_all add: analz_insert_eq analz_insert_freshK pushes)
apply spy_analz  \<comment> \<open>Fake\<close>
apply (blast dest: unique_session_keys)+  \<comment> \<open>OR3, OR4, Oops\<close>
done


lemma Spy_not_see_encrypted_key:
     "[| Says Server B
          \<lbrace>NA, Crypt (shrK A) \<lbrace>NA, Key K\<rbrace>,
                Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace> \<in> set evs;
         Notes Spy \<lbrace>NA, NB, Key K\<rbrace> \<notin> set evs;
         A \<notin> bad;  B \<notin> bad;  evs \<in> otway |]
      ==> Key K \<notin> analz (knows Spy evs)"
by (blast dest: Says_Server_message_form secrecy_lemma)


subsection\<open>Attempting to prove stronger properties\<close>

text\<open>Only OR1 can have caused such a part of a message to appear. The premise
  @{term "A \<noteq> B"} prevents OR2's similar-looking cryptogram from being picked 
  up. Original Otway-Rees doesn't need it.\<close>
lemma Crypt_imp_OR1 [rule_format]:
     "[| A \<notin> bad;  A \<noteq> B;  evs \<in> otway |]
      ==> Crypt (shrK A) \<lbrace>NA, Agent A, Agent B\<rbrace> \<in> parts (knows Spy evs) \<longrightarrow>
          Says A B \<lbrace>NA, Agent A, Agent B,
                     Crypt (shrK A) \<lbrace>NA, Agent A, Agent B\<rbrace>\<rbrace>  \<in> set evs"
by (erule otway.induct, force,
    drule_tac [4] OR2_parts_knows_Spy, simp_all, blast+)


text\<open>Crucial property: If the encrypted message appears, and A has used NA
  to start a run, then it originated with the Server!
  The premise @{term "A \<noteq> B"} allows use of \<open>Crypt_imp_OR1\<close>\<close>
text\<open>Only it is FALSE.  Somebody could make a fake message to Server
          substituting some other nonce NA' for NB.\<close>
lemma "[| A \<notin> bad;  A \<noteq> B;  evs \<in> otway |]
       ==> Crypt (shrK A) \<lbrace>NA, Key K\<rbrace> \<in> parts (knows Spy evs) \<longrightarrow>
           Says A B \<lbrace>NA, Agent A, Agent B,
                      Crypt (shrK A) \<lbrace>NA, Agent A, Agent B\<rbrace>\<rbrace>
            \<in> set evs \<longrightarrow>
           (\<exists>B NB. Says Server B
                \<lbrace>NA,
                  Crypt (shrK A) \<lbrace>NA, Key K\<rbrace>,
                  Crypt (shrK B) \<lbrace>NB, Key K\<rbrace>\<rbrace> \<in> set evs)"
apply (erule otway.induct, force,
       drule_tac [4] OR2_parts_knows_Spy, simp_all)
apply blast  \<comment> \<open>Fake\<close>
apply blast  \<comment> \<open>OR1: it cannot be a new Nonce, contradiction.\<close>
txt\<open>OR3 and OR4\<close>
apply (simp_all add: ex_disj_distrib)
 prefer 2 apply (blast intro!: Crypt_imp_OR1)  \<comment> \<open>OR4\<close>
txt\<open>OR3\<close>
apply clarify
(*The hypotheses at this point suggest an attack in which nonce NB is used
  in two different roles:
          Gets Server
           \<lbrace>Nonce NA, Agent Aa, Agent A,
             Crypt (shrK Aa) \<lbrace>Nonce NA, Agent Aa, Agent A\<rbrace>, Nonce NB,
             Crypt (shrK A) \<lbrace>Nonce NA, Agent Aa, Agent A\<rbrace>\<rbrace>
          \<in> set evs3
          Says A B
           \<lbrace>Nonce NB, Agent A, Agent B,
             Crypt (shrK A) \<lbrace>Nonce NB, Agent A, Agent B\<rbrace>\<rbrace>
          \<in> set evs3;
*)


(*Thus the key property A_can_trust probably fails too.*)
oops

end
