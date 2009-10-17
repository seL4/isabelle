(*  Title:      HOL/Auth/KerberosIV
    ID:         $Id$
    Author:     Giampaolo Bella, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

header{*The Kerberos Protocol, Version IV*}

theory KerberosIV_Gets imports Public begin

text{*The "u" prefix indicates theorems referring to an updated version of the protocol. The "r" suffix indicates theorems where the confidentiality assumptions are relaxed by the corresponding arguments.*}

abbreviation
  Kas :: agent where "Kas == Server"

abbreviation
  Tgs :: agent where "Tgs == Friend 0"


axioms
  Tgs_not_bad [iff]: "Tgs \<notin> bad"
   --{*Tgs is secure --- we already know that Kas is secure*}

constdefs
 (* authKeys are those contained in an authTicket *)
    authKeys :: "event list => key set"
    "authKeys evs == {authK. \<exists>A Peer Ta. Says Kas A
                        (Crypt (shrK A) \<lbrace>Key authK, Agent Peer, Number Ta,
               (Crypt (shrK Peer) \<lbrace>Agent A, Agent Peer, Key authK, Number Ta\<rbrace>)
                  \<rbrace>) \<in> set evs}"

 (* States than an event really appears only once on a trace *)
  Unique :: "[event, event list] => bool" ("Unique _ on _")
   "Unique ev on evs == 
      ev \<notin> set (tl (dropWhile (% z. z \<noteq> ev) evs))"


consts
    (*Duration of the authentication key*)
    authKlife   :: nat

    (*Duration of the service key*)
    servKlife   :: nat

    (*Duration of an authenticator*)
    authlife   :: nat

    (*Upper bound on the time of reaction of a server*)
    replylife   :: nat

specification (authKlife)
  authKlife_LB [iff]: "2 \<le> authKlife"
    by blast

specification (servKlife)
  servKlife_LB [iff]: "2 + authKlife \<le> servKlife"
    by blast

specification (authlife)
  authlife_LB [iff]: "Suc 0 \<le> authlife"
    by blast

specification (replylife)
  replylife_LB [iff]: "Suc 0 \<le> replylife"
    by blast

abbreviation
  (*The current time is just the length of the trace!*)
  CT :: "event list=>nat" where
  "CT == length"

abbreviation
  expiredAK :: "[nat, event list] => bool" where
  "expiredAK Ta evs == authKlife + Ta < CT evs"

abbreviation
  expiredSK :: "[nat, event list] => bool" where
  "expiredSK Ts evs == servKlife + Ts < CT evs"

abbreviation
  expiredA :: "[nat, event list] => bool" where
  "expiredA T evs == authlife + T < CT evs"

abbreviation
  valid :: "[nat, nat] => bool" ("valid _ wrt _") where
  "valid T1 wrt T2 == T1 <= replylife + T2"

(*---------------------------------------------------------------------*)


(* Predicate formalising the association between authKeys and servKeys *)
constdefs
  AKcryptSK :: "[key, key, event list] => bool"
  "AKcryptSK authK servK evs ==
     \<exists>A B Ts.
       Says Tgs A (Crypt authK
                     \<lbrace>Key servK, Agent B, Number Ts,
                       Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace> \<rbrace>)
         \<in> set evs"

inductive_set "kerbIV_gets" :: "event list set"
  where

   Nil:  "[] \<in> kerbIV_gets"

 | Fake: "\<lbrakk> evsf \<in> kerbIV_gets;  X \<in> synth (analz (spies evsf)) \<rbrakk>
          \<Longrightarrow> Says Spy B X  # evsf \<in> kerbIV_gets"

 | Reception: "\<lbrakk> evsr \<in> kerbIV_gets;  Says A B X \<in> set evsr \<rbrakk>
                \<Longrightarrow> Gets B X # evsr \<in> kerbIV_gets"

(* FROM the initiator *)
 | K1:   "\<lbrakk> evs1 \<in> kerbIV_gets \<rbrakk>
          \<Longrightarrow> Says A Kas \<lbrace>Agent A, Agent Tgs, Number (CT evs1)\<rbrace> # evs1
          \<in> kerbIV_gets"

(* Adding the timestamp serves to A in K3 to check that
   she doesn't get a reply too late. This kind of timeouts are ordinary.
   If a server's reply is late, then it is likely to be fake. *)

(*---------------------------------------------------------------------*)

(*FROM Kas *)
 | K2:  "\<lbrakk> evs2 \<in> kerbIV_gets; Key authK \<notin> used evs2; authK \<in> symKeys;
            Gets Kas \<lbrace>Agent A, Agent Tgs, Number T1\<rbrace> \<in> set evs2 \<rbrakk>
          \<Longrightarrow> Says Kas A
                (Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number (CT evs2),
                      (Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK,
                          Number (CT evs2)\<rbrace>)\<rbrace>) # evs2 \<in> kerbIV_gets"
(*
  The internal encryption builds the authTicket.
  The timestamp doesn't change inside the two encryptions: the external copy
  will be used by the initiator in K3; the one inside the
  authTicket by Tgs in K4.
*)

(*---------------------------------------------------------------------*)

(* FROM the initiator *)
 | K3:  "\<lbrakk> evs3 \<in> kerbIV_gets;
            Says A Kas \<lbrace>Agent A, Agent Tgs, Number T1\<rbrace> \<in> set evs3;
            Gets A (Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta,
              authTicket\<rbrace>) \<in> set evs3;
            valid Ta wrt T1
         \<rbrakk>
          \<Longrightarrow> Says A Tgs \<lbrace>authTicket,
                           (Crypt authK \<lbrace>Agent A, Number (CT evs3)\<rbrace>),
                           Agent B\<rbrace> # evs3 \<in> kerbIV_gets"
(*The two events amongst the premises allow A to accept only those authKeys
  that are not issued late. *)

(*---------------------------------------------------------------------*)

(* FROM Tgs *)
(* Note that the last temporal check is not mentioned in the original MIT
   specification. Adding it makes many goals "available" to the peers. 
   Theorems that exploit it have the suffix `_u', which stands for updated 
   protocol.
*)
 | K4:  "\<lbrakk> evs4 \<in> kerbIV_gets; Key servK \<notin> used evs4; servK \<in> symKeys;
            B \<noteq> Tgs;  authK \<in> symKeys;
            Gets Tgs \<lbrace>
             (Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK,
                                 Number Ta\<rbrace>),
             (Crypt authK \<lbrace>Agent A, Number T2\<rbrace>), Agent B\<rbrace>
                \<in> set evs4;
            \<not> expiredAK Ta evs4;
            \<not> expiredA T2 evs4;
            servKlife + (CT evs4) <= authKlife + Ta
         \<rbrakk>
          \<Longrightarrow> Says Tgs A
                (Crypt authK \<lbrace>Key servK, Agent B, Number (CT evs4),
                               Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK,
                                                Number (CT evs4)\<rbrace> \<rbrace>)
                # evs4 \<in> kerbIV_gets"
(* Tgs creates a new session key per each request for a service, without
   checking if there is still a fresh one for that service.
   The cipher under Tgs' key is the authTicket, the cipher under B's key
   is the servTicket, which is built now.
   NOTE that the last temporal check is not present in the MIT specification.

*)

(*---------------------------------------------------------------------*)

(* FROM the initiator *)
 | K5:  "\<lbrakk> evs5 \<in> kerbIV_gets; authK \<in> symKeys; servK \<in> symKeys;
            Says A Tgs
                \<lbrace>authTicket, Crypt authK \<lbrace>Agent A, Number T2\<rbrace>,
                  Agent B\<rbrace>
              \<in> set evs5;
            Gets A
             (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
                \<in> set evs5;
            valid Ts wrt T2 \<rbrakk>
          \<Longrightarrow> Says A B \<lbrace>servTicket,
                         Crypt servK \<lbrace>Agent A, Number (CT evs5)\<rbrace> \<rbrace>
               # evs5 \<in> kerbIV_gets"
(* Checks similar to those in K3. *)

(*---------------------------------------------------------------------*)

(* FROM the responder*)
  | K6:  "\<lbrakk> evs6 \<in> kerbIV_gets;
            Gets B \<lbrace>
              (Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>),
              (Crypt servK \<lbrace>Agent A, Number T3\<rbrace>)\<rbrace>
            \<in> set evs6;
            \<not> expiredSK Ts evs6;
            \<not> expiredA T3 evs6
         \<rbrakk>
          \<Longrightarrow> Says B A (Crypt servK (Number T3))
               # evs6 \<in> kerbIV_gets"
(* Checks similar to those in K4. *)

(*---------------------------------------------------------------------*)

(* Leaking an authK... *)
 | Oops1: "\<lbrakk> evsO1 \<in> kerbIV_gets;  A \<noteq> Spy;
              Says Kas A
                (Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta,
                                  authTicket\<rbrace>)  \<in> set evsO1;
              expiredAK Ta evsO1 \<rbrakk>
          \<Longrightarrow> Says A Spy \<lbrace>Agent A, Agent Tgs, Number Ta, Key authK\<rbrace>
               # evsO1 \<in> kerbIV_gets"

(*---------------------------------------------------------------------*)

(*Leaking a servK... *)
 | Oops2: "\<lbrakk> evsO2 \<in> kerbIV_gets;  A \<noteq> Spy;
              Says Tgs A
                (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
                   \<in> set evsO2;
              expiredSK Ts evsO2 \<rbrakk>
          \<Longrightarrow> Says A Spy \<lbrace>Agent A, Agent B, Number Ts, Key servK\<rbrace>
               # evsO2 \<in> kerbIV_gets"

(*---------------------------------------------------------------------*)

declare Says_imp_knows_Spy [THEN parts.Inj, dest]
declare parts.Body [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un [dest]

subsection{*Lemmas about reception event*}

lemma Gets_imp_Says :
     "\<lbrakk> Gets B X \<in> set evs; evs \<in> kerbIV_gets \<rbrakk> \<Longrightarrow> \<exists>A. Says A B X \<in> set evs"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply auto
done

lemma Gets_imp_knows_Spy: 
     "\<lbrakk> Gets B X \<in> set evs; evs \<in> kerbIV_gets \<rbrakk>  \<Longrightarrow> X \<in> knows Spy evs"
apply (blast dest!: Gets_imp_Says Says_imp_knows_Spy)
done

(*Needed for force to work for example in new_keys_not_used*)
declare Gets_imp_knows_Spy [THEN parts.Inj, dest]

lemma Gets_imp_knows:
     "\<lbrakk> Gets B X \<in> set evs; evs \<in> kerbIV_gets \<rbrakk>  \<Longrightarrow> X \<in> knows B evs"
apply (case_tac "B = Spy")
apply (blast dest!: Gets_imp_knows_Spy)
apply (blast dest!: Gets_imp_knows_agents)
done

subsection{*Lemmas about @{term authKeys}*}

lemma authKeys_empty: "authKeys [] = {}"
apply (unfold authKeys_def)
apply (simp (no_asm))
done

lemma authKeys_not_insert:
 "(\<forall>A Ta akey Peer.
   ev \<noteq> Says Kas A (Crypt (shrK A) \<lbrace>akey, Agent Peer, Ta,
              (Crypt (shrK Peer) \<lbrace>Agent A, Agent Peer, akey, Ta\<rbrace>)\<rbrace>))
       \<Longrightarrow> authKeys (ev # evs) = authKeys evs"
by (unfold authKeys_def, auto)

lemma authKeys_insert:
  "authKeys
     (Says Kas A (Crypt (shrK A) \<lbrace>Key K, Agent Peer, Number Ta,
      (Crypt (shrK Peer) \<lbrace>Agent A, Agent Peer, Key K, Number Ta\<rbrace>)\<rbrace>) # evs)
       = insert K (authKeys evs)"
by (unfold authKeys_def, auto)

lemma authKeys_simp:
   "K \<in> authKeys
    (Says Kas A (Crypt (shrK A) \<lbrace>Key K', Agent Peer, Number Ta,
     (Crypt (shrK Peer) \<lbrace>Agent A, Agent Peer, Key K', Number Ta\<rbrace>)\<rbrace>) # evs)
        \<Longrightarrow> K = K' | K \<in> authKeys evs"
by (unfold authKeys_def, auto)

lemma authKeysI:
   "Says Kas A (Crypt (shrK A) \<lbrace>Key K, Agent Tgs, Number Ta,
     (Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key K, Number Ta\<rbrace>)\<rbrace>) \<in> set evs
        \<Longrightarrow> K \<in> authKeys evs"
by (unfold authKeys_def, auto)

lemma authKeys_used: "K \<in> authKeys evs \<Longrightarrow> Key K \<in> used evs"
by (simp add: authKeys_def, blast)


subsection{*Forwarding Lemmas*}

lemma Says_ticket_parts:
     "Says S A (Crypt K \<lbrace>SesKey, B, TimeStamp, Ticket\<rbrace>) \<in> set evs
      \<Longrightarrow> Ticket \<in> parts (spies evs)"
apply blast
done

lemma Gets_ticket_parts:
     "\<lbrakk>Gets A (Crypt K \<lbrace>SesKey, Peer, Ta, Ticket\<rbrace>) \<in> set evs; evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Ticket \<in> parts (spies evs)"
apply (blast dest: Gets_imp_knows_Spy [THEN parts.Inj])
done

lemma Oops_range_spies1:
     "\<lbrakk> Says Kas A (Crypt KeyA \<lbrace>Key authK, Peer, Ta, authTicket\<rbrace>)
           \<in> set evs ;
         evs \<in> kerbIV_gets \<rbrakk> \<Longrightarrow> authK \<notin> range shrK & authK \<in> symKeys"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct, auto)
done

lemma Oops_range_spies2:
     "\<lbrakk> Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Ts, servTicket\<rbrace>)
           \<in> set evs ;
         evs \<in> kerbIV_gets \<rbrakk> \<Longrightarrow> servK \<notin> range shrK & servK \<in> symKeys"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct, auto)
done


(*Spy never sees another agent's shared key! (unless it's lost at start)*)
lemma Spy_see_shrK [simp]:
     "evs \<in> kerbIV_gets \<Longrightarrow> (Key (shrK A) \<in> parts (spies evs)) = (A \<in> bad)"
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all)
apply (blast+)
done

lemma Spy_analz_shrK [simp]:
     "evs \<in> kerbIV_gets \<Longrightarrow> (Key (shrK A) \<in> analz (spies evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "\<lbrakk> Key (shrK A) \<in> parts (spies evs);  evs \<in> kerbIV_gets \<rbrakk> \<Longrightarrow> A:bad"
by (blast dest: Spy_see_shrK)
lemmas Spy_analz_shrK_D = analz_subset_parts [THEN subsetD, THEN Spy_see_shrK_D, dest!]

text{*Nobody can have used non-existent keys!*}
lemma new_keys_not_used [simp]:
    "\<lbrakk>Key K \<notin> used evs; K \<in> symKeys; evs \<in> kerbIV_gets\<rbrakk>
     \<Longrightarrow> K \<notin> keysFor (parts (spies evs))"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all)
txt{*Fake*}
apply (force dest!: keysFor_parts_insert)
txt{*Others*}
apply (force dest!: analz_shrK_Decrypt)+
done

(*Earlier, all protocol proofs declared this theorem.
  But few of them actually need it! (Another is Yahalom) *)
lemma new_keys_not_analzd:
 "\<lbrakk>evs \<in> kerbIV_gets; K \<in> symKeys; Key K \<notin> used evs\<rbrakk>
  \<Longrightarrow> K \<notin> keysFor (analz (spies evs))"
by (blast dest: new_keys_not_used intro: keysFor_mono [THEN subsetD])


subsection{*Regularity Lemmas*}
text{*These concern the form of items passed in messages*}

text{*Describes the form of all components sent by Kas*}

lemma Says_Kas_message_form:
     "\<lbrakk> Says Kas A (Crypt K \<lbrace>Key authK, Agent Peer, Number Ta, authTicket\<rbrace>)
           \<in> set evs;
         evs \<in> kerbIV_gets \<rbrakk> \<Longrightarrow>  
  K = shrK A  & Peer = Tgs &
  authK \<notin> range shrK & authK \<in> authKeys evs & authK \<in> symKeys & 
  authTicket = (Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>)"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (simp_all (no_asm) add: authKeys_def authKeys_insert)
apply blast+
done


lemma SesKey_is_session_key:
     "\<lbrakk> Crypt (shrK Tgs_B) \<lbrace>Agent A, Agent Tgs_B, Key SesKey, Number T\<rbrace>
            \<in> parts (spies evs); Tgs_B \<notin> bad;
         evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> SesKey \<notin> range shrK"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all, blast)
done

lemma authTicket_authentic:
     "\<lbrakk> Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>
           \<in> parts (spies evs);
         evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Says Kas A (Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta,
                 Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>\<rbrace>)
            \<in> set evs"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all)
txt{*Fake, K4*}
apply (blast+)
done

lemma authTicket_crypt_authK:
     "\<lbrakk> Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>
           \<in> parts (spies evs);
         evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> authK \<in> authKeys evs"
apply (frule authTicket_authentic, assumption)
apply (simp (no_asm) add: authKeys_def)
apply blast
done

lemma Says_Tgs_message_form:
     "\<lbrakk> Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
           \<in> set evs;
         evs \<in> kerbIV_gets \<rbrakk>
  \<Longrightarrow> B \<noteq> Tgs & 
      authK \<notin> range shrK & authK \<in> authKeys evs & authK \<in> symKeys &
      servK \<notin> range shrK & servK \<notin> authKeys evs & servK \<in> symKeys &
      servTicket = (Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>)"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (simp_all add: authKeys_insert authKeys_not_insert authKeys_empty authKeys_simp, blast, auto)
txt{*Three subcases of Message 4*}
apply (blast dest!: SesKey_is_session_key)
apply (blast dest: authTicket_crypt_authK)
apply (blast dest!: authKeys_used Says_Kas_message_form)
done


lemma authTicket_form:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Ta, authTicket\<rbrace>
           \<in> parts (spies evs);
         A \<notin> bad;
         evs \<in> kerbIV_gets \<rbrakk>
    \<Longrightarrow> authK \<notin> range shrK & authK \<in> symKeys & 
        authTicket = Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Ta\<rbrace>"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all)
apply blast+
done

text{* This form holds also over an authTicket, but is not needed below.*}
lemma servTicket_form:
     "\<lbrakk> Crypt authK \<lbrace>Key servK, Agent B, Ts, servTicket\<rbrace>
              \<in> parts (spies evs);
            Key authK \<notin> analz (spies evs);
            evs \<in> kerbIV_gets \<rbrakk>
         \<Longrightarrow> servK \<notin> range shrK & servK \<in> symKeys & 
    (\<exists>A. servTicket = Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Ts\<rbrace>)"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbIV_gets.induct, analz_mono_contra)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all, blast)
done

text{* Essentially the same as @{text authTicket_form} *}
lemma Says_kas_message_form:
     "\<lbrakk> Gets A (Crypt (shrK A)
              \<lbrace>Key authK, Agent Tgs, Ta, authTicket\<rbrace>) \<in> set evs;
         evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> authK \<notin> range shrK & authK \<in> symKeys & 
          authTicket =
                  Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Ta\<rbrace>
          | authTicket \<in> analz (spies evs)"
by (blast dest: analz_shrK_Decrypt authTicket_form
                Gets_imp_knows_Spy [THEN analz.Inj])

lemma Says_tgs_message_form:
 "\<lbrakk> Gets A (Crypt authK \<lbrace>Key servK, Agent B, Ts, servTicket\<rbrace>)
       \<in> set evs;  authK \<in> symKeys;
     evs \<in> kerbIV_gets \<rbrakk>
  \<Longrightarrow> servK \<notin> range shrK &
      (\<exists>A. servTicket =
              Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Ts\<rbrace>)
       | servTicket \<in> analz (spies evs)"
apply (frule Gets_imp_knows_Spy [THEN analz.Inj], auto)
 apply (force dest!: servTicket_form)
apply (frule analz_into_parts)
apply (frule servTicket_form, auto)
done


subsection{*Authenticity theorems: confirm origin of sensitive messages*}

lemma authK_authentic:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Key authK, Peer, Ta, authTicket\<rbrace>
           \<in> parts (spies evs);
         A \<notin> bad;  evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Says Kas A (Crypt (shrK A) \<lbrace>Key authK, Peer, Ta, authTicket\<rbrace>)
            \<in> set evs"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all)
txt{*Fake*}
apply blast
txt{*K4*}
apply (blast dest!: authTicket_authentic [THEN Says_Kas_message_form])
done

text{*If a certain encrypted message appears then it originated with Tgs*}
lemma servK_authentic:
     "\<lbrakk> Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>
           \<in> parts (spies evs);
         Key authK \<notin> analz (spies evs);
         authK \<notin> range shrK;
         evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> \<exists>A. Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
       \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbIV_gets.induct, analz_mono_contra)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all)
txt{*Fake*}
apply blast
txt{*K2*}
apply blast
txt{*K4*}
apply auto
done

lemma servK_authentic_bis:
     "\<lbrakk> Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>
           \<in> parts (spies evs);
         Key authK \<notin> analz (spies evs);
         B \<noteq> Tgs;
         evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> \<exists>A. Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
       \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbIV_gets.induct, analz_mono_contra)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all)
txt{*Fake*}
apply blast
txt{*K4*}
apply blast
done

text{*Authenticity of servK for B*}
lemma servTicket_authentic_Tgs:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs); B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> \<exists>authK.
       Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts,
                   Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>\<rbrace>)
       \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all)
apply blast+
done

text{*Anticipated here from next subsection*}
lemma K4_imp_K2:
"\<lbrakk> Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
      \<in> set evs;  evs \<in> kerbIV_gets\<rbrakk>
   \<Longrightarrow> \<exists>Ta. Says Kas A
        (Crypt (shrK A)
         \<lbrace>Key authK, Agent Tgs, Number Ta,
           Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>\<rbrace>)
        \<in> set evs"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all, auto)
apply (blast dest!: Gets_imp_knows_Spy [THEN parts.Inj, THEN parts.Fst, THEN authTicket_authentic])
done

text{*Anticipated here from next subsection*}
lemma u_K4_imp_K2:
"\<lbrakk> Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
      \<in> set evs; evs \<in> kerbIV_gets\<rbrakk>
   \<Longrightarrow> \<exists>Ta. (Says Kas A (Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta,
           Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>\<rbrace>)
             \<in> set evs
          & servKlife + Ts <= authKlife + Ta)"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all, auto)
apply (blast dest!: Gets_imp_knows_Spy [THEN parts.Inj, THEN parts.Fst, THEN authTicket_authentic])
done

lemma servTicket_authentic_Kas:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);  B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerbIV_gets \<rbrakk>
  \<Longrightarrow> \<exists>authK Ta.
       Says Kas A
         (Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta,
            Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>\<rbrace>)
        \<in> set evs"
apply (blast dest!: servTicket_authentic_Tgs K4_imp_K2)
done

lemma u_servTicket_authentic_Kas:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);  B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerbIV_gets \<rbrakk>
  \<Longrightarrow> \<exists>authK Ta. Says Kas A (Crypt(shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta,
           Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>\<rbrace>)
             \<in> set evs
           & servKlife + Ts <= authKlife + Ta"
apply (blast dest!: servTicket_authentic_Tgs u_K4_imp_K2)
done

lemma servTicket_authentic:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);  B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> \<exists>Ta authK.
     Says Kas A (Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta,
                   Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>\<rbrace>)
       \<in> set evs
     & Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts,
                   Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>\<rbrace>)
       \<in> set evs"
apply (blast dest: servTicket_authentic_Tgs K4_imp_K2)
done

lemma u_servTicket_authentic:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);  B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> \<exists>Ta authK.
     (Says Kas A (Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta,
                   Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>\<rbrace>)
       \<in> set evs
     & Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts,
                   Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>\<rbrace>)
       \<in> set evs
     & servKlife + Ts <= authKlife + Ta)"
apply (blast dest: servTicket_authentic_Tgs u_K4_imp_K2)
done

lemma u_NotexpiredSK_NotexpiredAK:
     "\<lbrakk> \<not> expiredSK Ts evs; servKlife + Ts <= authKlife + Ta \<rbrakk>
      \<Longrightarrow> \<not> expiredAK Ta evs"
apply (blast dest: leI le_trans dest: leD)
done


subsection{* Reliability: friendly agents send something if something else happened*}

lemma K3_imp_K2:
     "\<lbrakk> Says A Tgs
             \<lbrace>authTicket, Crypt authK \<lbrace>Agent A, Number T2\<rbrace>, Agent B\<rbrace>
           \<in> set evs;
         A \<notin> bad;  evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> \<exists>Ta. Says Kas A (Crypt (shrK A)
                      \<lbrace>Key authK, Agent Tgs, Number Ta, authTicket\<rbrace>)
                   \<in> set evs"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all, blast, blast)
apply (blast dest: Gets_imp_knows_Spy [THEN parts.Inj, THEN authK_authentic])
done

text{*Anticipated here from next subsection. An authK is encrypted by one and only one Shared key. A servK is encrypted by one and only one authK.*}
lemma Key_unique_SesKey:
     "\<lbrakk> Crypt K  \<lbrace>Key SesKey,  Agent B, T, Ticket\<rbrace>
           \<in> parts (spies evs);
         Crypt K' \<lbrace>Key SesKey,  Agent B', T', Ticket'\<rbrace>
           \<in> parts (spies evs);  Key SesKey \<notin> analz (spies evs);
         evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> K=K' & B=B' & T=T' & Ticket=Ticket'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbIV_gets.induct, analz_mono_contra)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all)
txt{*Fake, K2, K4*}
apply (blast+)
done

lemma Tgs_authenticates_A:
  "\<lbrakk>  Crypt authK \<lbrace>Agent A, Number T2\<rbrace> \<in> parts (spies evs); 
      Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>
           \<in> parts (spies evs);
      Key authK \<notin> analz (spies evs); A \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> \<exists> B. Says A Tgs \<lbrace>
          Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>,
          Crypt authK \<lbrace>Agent A, Number T2\<rbrace>, Agent B \<rbrace> \<in> set evs"  
apply (drule authTicket_authentic, assumption, rotate_tac 4)
apply (erule rev_mp, erule rev_mp, erule rev_mp)
apply (erule kerbIV_gets.induct, analz_mono_contra)
apply (frule_tac [6] Gets_ticket_parts)
apply (frule_tac [9] Gets_ticket_parts)
apply (simp_all (no_asm_simp) add: all_conj_distrib)
txt{*Fake*}
apply blast
txt{*K2*}
apply (force dest!: Crypt_imp_keysFor)
txt{*K3*}
apply (blast dest: Key_unique_SesKey)
txt{*K5*}
txt{*If authKa were compromised, so would be authK*}
apply (case_tac "Key authKa \<in> analz (spies evs5)")
apply (force dest!: Gets_imp_knows_Spy [THEN analz.Inj, THEN analz.Decrypt, THEN analz.Fst])
txt{*Besides, since authKa originated with Kas anyway...*}
apply (clarify, drule K3_imp_K2, assumption, assumption)
apply (clarify, drule Says_Kas_message_form, assumption)
txt{*...it cannot be a shared key*. Therefore @{term servK_authentic} applies. 
     Contradition: Tgs used authK as a servkey, 
     while Kas used it as an authkey*}
apply (blast dest: servK_authentic Says_Tgs_message_form)
done

lemma Says_K5:
     "\<lbrakk> Crypt servK \<lbrace>Agent A, Number T3\<rbrace> \<in> parts (spies evs);
         Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts,
                                     servTicket\<rbrace>) \<in> set evs;
         Key servK \<notin> analz (spies evs);
         A \<notin> bad; B \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> Says A B \<lbrace>servTicket, Crypt servK \<lbrace>Agent A, Number T3\<rbrace>\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbIV_gets.induct, analz_mono_contra)
apply (frule_tac [6] Gets_ticket_parts)
apply (frule_tac [9] Gets_ticket_parts)
apply (simp_all (no_asm_simp) add: all_conj_distrib)
apply blast
txt{*K3*}
apply (blast dest: authK_authentic Says_Kas_message_form Says_Tgs_message_form)
txt{*K4*}
apply (force dest!: Crypt_imp_keysFor)
txt{*K5*}
apply (blast dest: Key_unique_SesKey)
done

text{*Anticipated here from next subsection*}
lemma unique_CryptKey:
     "\<lbrakk> Crypt (shrK B)  \<lbrace>Agent A,  Agent B,  Key SesKey, T\<rbrace>
           \<in> parts (spies evs);
         Crypt (shrK B') \<lbrace>Agent A', Agent B', Key SesKey, T'\<rbrace>
           \<in> parts (spies evs);  Key SesKey \<notin> analz (spies evs);
         evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> A=A' & B=B' & T=T'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbIV_gets.induct, analz_mono_contra)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all)
txt{*Fake, K2, K4*}
apply (blast+)
done

lemma Says_K6:
     "\<lbrakk> Crypt servK (Number T3) \<in> parts (spies evs);
         Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts,
                                     servTicket\<rbrace>) \<in> set evs;
         Key servK \<notin> analz (spies evs);
         A \<notin> bad; B \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Says B A (Crypt servK (Number T3)) \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbIV_gets.induct, analz_mono_contra)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts)
apply (simp_all (no_asm_simp))
apply blast
apply (force dest!: Crypt_imp_keysFor, clarify)
apply (frule Says_Tgs_message_form, assumption, clarify) (*PROOF FAILED if omitted*)
apply (blast dest: unique_CryptKey)
done

text{*Needs a unicity theorem, hence moved here*}
lemma servK_authentic_ter:
 "\<lbrakk> Says Kas A
    (Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta, authTicket\<rbrace>) \<in> set evs;
     Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>
       \<in> parts (spies evs);
     Key authK \<notin> analz (spies evs);
     evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
       \<in> set evs"
apply (frule Says_Kas_message_form, assumption)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbIV_gets.induct, analz_mono_contra)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all, blast)
txt{*K2 and K4 remain*}
prefer 2 apply (blast dest!: unique_CryptKey)
apply (blast dest!: servK_authentic Says_Tgs_message_form authKeys_used)
done


subsection{*Unicity Theorems*}

text{* The session key, if secure, uniquely identifies the Ticket
   whether authTicket or servTicket. As a matter of fact, one can read
   also Tgs in the place of B.                                     *}


lemma unique_authKeys:
     "\<lbrakk> Says Kas A
              (Crypt Ka \<lbrace>Key authK, Agent Tgs, Ta, X\<rbrace>) \<in> set evs;
         Says Kas A'
              (Crypt Ka' \<lbrace>Key authK, Agent Tgs, Ta', X'\<rbrace>) \<in> set evs;
         evs \<in> kerbIV_gets \<rbrakk> \<Longrightarrow> A=A' & Ka=Ka' & Ta=Ta' & X=X'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all)
txt{*K2*}
apply blast
done

text{* servK uniquely identifies the message from Tgs *}
lemma unique_servKeys:
     "\<lbrakk> Says Tgs A
              (Crypt K \<lbrace>Key servK, Agent B, Ts, X\<rbrace>) \<in> set evs;
         Says Tgs A'
              (Crypt K' \<lbrace>Key servK, Agent B', Ts', X'\<rbrace>) \<in> set evs;
         evs \<in> kerbIV_gets \<rbrakk> \<Longrightarrow> A=A' & B=B' & K=K' & Ts=Ts' & X=X'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all)
txt{*K4*}
apply blast
done

text{* Revised unicity theorems *}

lemma Kas_Unique:
     "\<lbrakk> Says Kas A
              (Crypt Ka \<lbrace>Key authK, Agent Tgs, Ta, authTicket\<rbrace>) \<in> set evs;
        evs \<in> kerbIV_gets \<rbrakk> \<Longrightarrow> 
   Unique (Says Kas A (Crypt Ka \<lbrace>Key authK, Agent Tgs, Ta, authTicket\<rbrace>)) 
   on evs"
apply (erule rev_mp, erule kerbIV_gets.induct, simp_all add: Unique_def)
apply blast
done

lemma Tgs_Unique:
     "\<lbrakk> Says Tgs A
              (Crypt authK \<lbrace>Key servK, Agent B, Ts, servTicket\<rbrace>) \<in> set evs;
        evs \<in> kerbIV_gets \<rbrakk> \<Longrightarrow> 
  Unique (Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Ts, servTicket\<rbrace>)) 
  on evs"
apply (erule rev_mp, erule kerbIV_gets.induct, simp_all add: Unique_def)
apply blast
done


subsection{*Lemmas About the Predicate @{term AKcryptSK}*}

lemma not_AKcryptSK_Nil [iff]: "\<not> AKcryptSK authK servK []"
by (simp add: AKcryptSK_def)

lemma AKcryptSKI:
 "\<lbrakk> Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, X \<rbrace>) \<in> set evs;
     evs \<in> kerbIV_gets \<rbrakk> \<Longrightarrow> AKcryptSK authK servK evs"
apply (unfold AKcryptSK_def)
apply (blast dest: Says_Tgs_message_form)
done

lemma AKcryptSK_Says [simp]:
   "AKcryptSK authK servK (Says S A X # evs) =
     (Tgs = S &
      (\<exists>B Ts. X = Crypt authK
                \<lbrace>Key servK, Agent B, Number Ts,
                  Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace> \<rbrace>)
     | AKcryptSK authK servK evs)"
apply (unfold AKcryptSK_def)
apply (simp (no_asm))
apply blast
done

(*A fresh authK cannot be associated with any other
  (with respect to a given trace). *)
lemma Auth_fresh_not_AKcryptSK:
     "\<lbrakk> Key authK \<notin> used evs; evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> \<not> AKcryptSK authK servK evs"
apply (unfold AKcryptSK_def)
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all, blast)
done

(*A fresh servK cannot be associated with any other
  (with respect to a given trace). *)
lemma Serv_fresh_not_AKcryptSK:
 "Key servK \<notin> used evs \<Longrightarrow> \<not> AKcryptSK authK servK evs"
apply (unfold AKcryptSK_def, blast)
done

lemma authK_not_AKcryptSK:
     "\<lbrakk> Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, tk\<rbrace>
           \<in> parts (spies evs);  evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> \<not> AKcryptSK K authK evs"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all)
txt{*Fake*}
apply blast
txt{*Reception*}
apply (simp add: AKcryptSK_def)
txt{*K2: by freshness*}
apply (simp add: AKcryptSK_def)
txt{*K4*}
apply (blast+)
done

text{*A secure serverkey cannot have been used to encrypt others*}
lemma servK_not_AKcryptSK:
 "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key SK, Number Ts\<rbrace> \<in> parts (spies evs);
     Key SK \<notin> analz (spies evs);  SK \<in> symKeys;
     B \<noteq> Tgs;  evs \<in> kerbIV_gets \<rbrakk>
  \<Longrightarrow> \<not> AKcryptSK SK K evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbIV_gets.induct, analz_mono_contra)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all, blast)
txt{*Reception*}
apply (simp add: AKcryptSK_def)
txt{*K4 splits into distinct subcases*}
apply auto
txt{*servK can't have been enclosed in two certificates*}
 prefer 2 apply (blast dest: unique_CryptKey)
txt{*servK is fresh and so could not have been used, by
   @{text new_keys_not_used}*}
apply (force dest!: Crypt_imp_invKey_keysFor simp add: AKcryptSK_def)
done

text{*Long term keys are not issued as servKeys*}
lemma shrK_not_AKcryptSK:
     "evs \<in> kerbIV_gets \<Longrightarrow> \<not> AKcryptSK K (shrK A) evs"
apply (unfold AKcryptSK_def)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, auto)
done

text{*The Tgs message associates servK with authK and therefore not with any
  other key authK.*}
lemma Says_Tgs_AKcryptSK:
     "\<lbrakk> Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, X \<rbrace>)
           \<in> set evs;
         authK' \<noteq> authK;  evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> \<not> AKcryptSK authK' servK evs"
apply (unfold AKcryptSK_def)
apply (blast dest: unique_servKeys)
done

text{*Equivalently*}
lemma not_different_AKcryptSK:
     "\<lbrakk> AKcryptSK authK servK evs;
        authK' \<noteq> authK;  evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> \<not> AKcryptSK authK' servK evs  \<and> servK \<in> symKeys"
apply (simp add: AKcryptSK_def)
apply (blast dest: unique_servKeys Says_Tgs_message_form)
done

lemma AKcryptSK_not_AKcryptSK:
     "\<lbrakk> AKcryptSK authK servK evs;  evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> \<not> AKcryptSK servK K evs"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts)
txt{*Reception*}
prefer 3 apply (simp add: AKcryptSK_def)
apply (simp_all, safe)
txt{*K4 splits into subcases*}
prefer 4 apply (blast dest!: authK_not_AKcryptSK)
txt{*servK is fresh and so could not have been used, by
   @{text new_keys_not_used}*}
 prefer 2 
 apply (force dest!: Crypt_imp_invKey_keysFor simp add: AKcryptSK_def)
txt{*Others by freshness*}
apply (blast+)
done

text{*The only session keys that can be found with the help of session keys are
  those sent by Tgs in step K4.  *}

text{*We take some pains to express the property
  as a logical equivalence so that the simplifier can apply it.*}
lemma Key_analz_image_Key_lemma:
     "P \<longrightarrow> (Key K \<in> analz (Key`KK Un H)) \<longrightarrow> (K:KK | Key K \<in> analz H)
      \<Longrightarrow>
      P \<longrightarrow> (Key K \<in> analz (Key`KK Un H)) = (K:KK | Key K \<in> analz H)"
by (blast intro: analz_mono [THEN subsetD])


lemma AKcryptSK_analz_insert:
     "\<lbrakk> AKcryptSK K K' evs; K \<in> symKeys; evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Key K' \<in> analz (insert (Key K) (spies evs))"
apply (simp add: AKcryptSK_def, clarify)
apply (drule Says_imp_spies [THEN analz.Inj, THEN analz_insertI], auto)
done

lemma authKeys_are_not_AKcryptSK:
     "\<lbrakk> K \<in> authKeys evs Un range shrK;  evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> \<forall>SK. \<not> AKcryptSK SK K evs \<and> K \<in> symKeys"
apply (simp add: authKeys_def AKcryptSK_def)
apply (blast dest: Says_Kas_message_form Says_Tgs_message_form)
done

lemma not_authKeys_not_AKcryptSK:
     "\<lbrakk> K \<notin> authKeys evs;
         K \<notin> range shrK; evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> \<forall>SK. \<not> AKcryptSK K SK evs"
apply (simp add: AKcryptSK_def)
apply (blast dest: Says_Tgs_message_form)
done


subsection{*Secrecy Theorems*}

text{*For the Oops2 case of the next theorem*}
lemma Oops2_not_AKcryptSK:
     "\<lbrakk> evs \<in> kerbIV_gets;
         Says Tgs A (Crypt authK
                     \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
           \<in> set evs \<rbrakk>
      \<Longrightarrow> \<not> AKcryptSK servK SK evs"
apply (blast dest: AKcryptSKI AKcryptSK_not_AKcryptSK)
done
   
text{* Big simplification law for keys SK that are not crypted by keys in KK
 It helps prove three, otherwise hard, facts about keys. These facts are
 exploited as simplification laws for analz, and also "limit the damage"
 in case of loss of a key to the spy. See ESORICS98. *}
lemma Key_analz_image_Key [rule_format (no_asm)]:
     "evs \<in> kerbIV_gets \<Longrightarrow>
      (\<forall>SK KK. SK \<in> symKeys & KK <= -(range shrK) \<longrightarrow>
       (\<forall>K \<in> KK. \<not> AKcryptSK K SK evs)   \<longrightarrow>
       (Key SK \<in> analz (Key`KK Un (spies evs))) =
       (SK \<in> KK | Key SK \<in> analz (spies evs)))"
apply (erule kerbIV_gets.induct)
apply (frule_tac [11] Oops_range_spies2)
apply (frule_tac [10] Oops_range_spies1)
apply (frule_tac [8] Says_tgs_message_form)
apply (frule_tac [6] Says_kas_message_form)
apply (safe del: impI intro!: Key_analz_image_Key_lemma [THEN impI])
txt{*Case-splits for Oops1 and message 5: the negated case simplifies using
 the induction hypothesis*}
apply (case_tac [12] "AKcryptSK authK SK evsO1")
apply (case_tac [9] "AKcryptSK servK SK evs5")
apply (simp_all del: image_insert
        add: analz_image_freshK_simps AKcryptSK_Says shrK_not_AKcryptSK
             Oops2_not_AKcryptSK Auth_fresh_not_AKcryptSK
       Serv_fresh_not_AKcryptSK Says_Tgs_AKcryptSK Spy_analz_shrK)
  --{*18 seconds on a 1.8GHz machine??*}
txt{*Fake*} 
apply spy_analz
txt{*Reception*}
apply (simp add: AKcryptSK_def)
txt{*K2*}
apply blast 
txt{*K3*}
apply blast 
txt{*K4*}
apply (blast dest!: authK_not_AKcryptSK)
txt{*K5*}
apply (case_tac "Key servK \<in> analz (spies evs5) ")
txt{*If servK is compromised then the result follows directly...*}
apply (simp (no_asm_simp) add: analz_insert_eq Un_upper2 [THEN analz_mono, THEN subsetD])
txt{*...therefore servK is uncompromised.*}
txt{*The AKcryptSK servK SK evs5 case leads to a contradiction.*}
apply (blast elim!: servK_not_AKcryptSK [THEN [2] rev_notE] del: allE ballE)
txt{*Another K5 case*}
apply blast 
txt{*Oops1*}
apply simp 
apply (blast dest!: AKcryptSK_analz_insert)
done

text{* First simplification law for analz: no session keys encrypt
authentication keys or shared keys. *}
lemma analz_insert_freshK1:
     "\<lbrakk> evs \<in> kerbIV_gets;  K \<in> authKeys evs Un range shrK;
        SesKey \<notin> range shrK \<rbrakk>
      \<Longrightarrow> (Key K \<in> analz (insert (Key SesKey) (spies evs))) =
          (K = SesKey | Key K \<in> analz (spies evs))"
apply (frule authKeys_are_not_AKcryptSK, assumption)
apply (simp del: image_insert
            add: analz_image_freshK_simps add: Key_analz_image_Key)
done


text{* Second simplification law for analz: no service keys encrypt any other keys.*}
lemma analz_insert_freshK2:
     "\<lbrakk> evs \<in> kerbIV_gets;  servK \<notin> (authKeys evs); servK \<notin> range shrK;
        K \<in> symKeys \<rbrakk>
      \<Longrightarrow> (Key K \<in> analz (insert (Key servK) (spies evs))) =
          (K = servK | Key K \<in> analz (spies evs))"
apply (frule not_authKeys_not_AKcryptSK, assumption, assumption)
apply (simp del: image_insert
            add: analz_image_freshK_simps add: Key_analz_image_Key)
done


text{* Third simplification law for analz: only one authentication key encrypts a certain service key.*}

lemma analz_insert_freshK3:
 "\<lbrakk> AKcryptSK authK servK evs;
    authK' \<noteq> authK; authK' \<notin> range shrK; evs \<in> kerbIV_gets \<rbrakk>
        \<Longrightarrow> (Key servK \<in> analz (insert (Key authK') (spies evs))) =
                (servK = authK' | Key servK \<in> analz (spies evs))"
apply (drule_tac authK' = authK' in not_different_AKcryptSK, blast, assumption)
apply (simp del: image_insert
            add: analz_image_freshK_simps add: Key_analz_image_Key)
done

lemma analz_insert_freshK3_bis:
 "\<lbrakk> Says Tgs A
            (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
        \<in> set evs; 
     authK \<noteq> authK'; authK' \<notin> range shrK; evs \<in> kerbIV_gets \<rbrakk>
        \<Longrightarrow> (Key servK \<in> analz (insert (Key authK') (spies evs))) =
                (servK = authK' | Key servK \<in> analz (spies evs))"
apply (frule AKcryptSKI, assumption)
apply (simp add: analz_insert_freshK3)
done

text{*a weakness of the protocol*}
lemma authK_compromises_servK:
     "\<lbrakk> Says Tgs A
              (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
           \<in> set evs;  authK \<in> symKeys;
         Key authK \<in> analz (spies evs); evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Key servK \<in> analz (spies evs)"
by (force dest: Says_imp_spies [THEN analz.Inj, THEN analz.Decrypt, THEN analz.Fst])

lemma servK_notin_authKeysD:
     "\<lbrakk> Crypt authK \<lbrace>Key servK, Agent B, Ts,
                      Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Ts\<rbrace>\<rbrace>
           \<in> parts (spies evs);
         Key servK \<notin> analz (spies evs);
         B \<noteq> Tgs; evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> servK \<notin> authKeys evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (simp add: authKeys_def)
apply (erule kerbIV_gets.induct, analz_mono_contra)
apply (frule_tac [8] Gets_ticket_parts)
apply (frule_tac [6] Gets_ticket_parts, simp_all)
apply (blast+)
done


text{*If Spy sees the Authentication Key sent in msg K2, then
    the Key has expired.*}
lemma Confidentiality_Kas_lemma [rule_format]:
     "\<lbrakk> authK \<in> symKeys; A \<notin> bad;  evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Says Kas A
               (Crypt (shrK A)
                  \<lbrace>Key authK, Agent Tgs, Number Ta,
          Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>\<rbrace>)
            \<in> set evs \<longrightarrow>
          Key authK \<in> analz (spies evs) \<longrightarrow>
          expiredAK Ta evs"
apply (erule kerbIV_gets.induct)
apply (frule_tac [11] Oops_range_spies2)
apply (frule_tac [10] Oops_range_spies1)
apply (frule_tac [8] Says_tgs_message_form)
apply (frule_tac [6] Says_kas_message_form)
apply (safe del: impI conjI impCE)
apply (simp_all (no_asm_simp) add: Says_Kas_message_form less_SucI analz_insert_eq not_parts_not_analz analz_insert_freshK1 pushes)
txt{*Fake*}
apply spy_analz
txt{*K2*}
apply blast
txt{*K4*}
apply blast
txt{*Level 8: K5*}
apply (blast dest: servK_notin_authKeysD Says_Kas_message_form intro: less_SucI)
txt{*Oops1*}
apply (blast dest!: unique_authKeys intro: less_SucI)
txt{*Oops2*}
apply (blast dest: Says_Tgs_message_form Says_Kas_message_form)
done

lemma Confidentiality_Kas:
     "\<lbrakk> Says Kas A
              (Crypt Ka \<lbrace>Key authK, Agent Tgs, Number Ta, authTicket\<rbrace>)
           \<in> set evs;
         \<not> expiredAK Ta evs;
         A \<notin> bad;  evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Key authK \<notin> analz (spies evs)"
by (blast dest: Says_Kas_message_form Confidentiality_Kas_lemma)

text{*If Spy sees the Service Key sent in msg K4, then
    the Key has expired.*}

lemma Confidentiality_lemma [rule_format]:
     "\<lbrakk> Says Tgs A
            (Crypt authK
               \<lbrace>Key servK, Agent B, Number Ts,
                 Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>\<rbrace>)
           \<in> set evs;
        Key authK \<notin> analz (spies evs);
        servK \<in> symKeys;
        A \<notin> bad;  B \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Key servK \<in> analz (spies evs) \<longrightarrow>
          expiredSK Ts evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply (rule_tac [10] impI)+;
  --{*The Oops1 case is unusual: must simplify
    @{term "Authkey \<notin> analz (spies (ev#evs))"}, not letting
   @{text analz_mono_contra} weaken it to
   @{term "Authkey \<notin> analz (spies evs)"},
  for we then conclude @{term "authK \<noteq> authKa"}.*}
apply analz_mono_contra
apply (frule_tac [11] Oops_range_spies2)
apply (frule_tac [10] Oops_range_spies1)
apply (frule_tac [8] Says_tgs_message_form)
apply (frule_tac [6] Says_kas_message_form)
apply (safe del: impI conjI impCE)
apply (simp_all add: less_SucI new_keys_not_analzd Says_Kas_message_form Says_Tgs_message_form analz_insert_eq not_parts_not_analz analz_insert_freshK1 analz_insert_freshK2 analz_insert_freshK3_bis pushes)
txt{*Fake*}
apply spy_analz
txt{*K2*}
apply (blast intro: parts_insertI less_SucI)
txt{*K4*}
apply (blast dest: authTicket_authentic Confidentiality_Kas)
txt{*Oops2*}
  prefer 3
  apply (blast dest: Says_imp_spies [THEN parts.Inj] Key_unique_SesKey intro: less_SucI)
txt{*Oops1*}
 prefer 2
apply (blast dest: Says_Kas_message_form Says_Tgs_message_form intro: less_SucI)
txt{*K5. Not clear how this step could be integrated with the main
       simplification step. Done in KerberosV.thy*}
apply clarify
apply (erule_tac V = "Says Aa Tgs ?X \<in> set ?evs" in thin_rl)
apply (frule Gets_imp_knows_Spy [THEN parts.Inj, THEN servK_notin_authKeysD])
apply (assumption, assumption, blast, assumption)
apply (simp add: analz_insert_freshK2)
apply (blast dest: Says_imp_spies [THEN parts.Inj] Key_unique_SesKey intro: less_SucI)
done


text{* In the real world Tgs can't check wheter authK is secure! *}
lemma Confidentiality_Tgs:
     "\<lbrakk> Says Tgs A
              (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
           \<in> set evs;
         Key authK \<notin> analz (spies evs);
         \<not> expiredSK Ts evs;
         A \<notin> bad;  B \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Key servK \<notin> analz (spies evs)"
apply (blast dest: Says_Tgs_message_form Confidentiality_lemma)
done

text{* In the real world Tgs CAN check what Kas sends! *}
lemma Confidentiality_Tgs_bis:
     "\<lbrakk> Says Kas A
               (Crypt Ka \<lbrace>Key authK, Agent Tgs, Number Ta, authTicket\<rbrace>)
           \<in> set evs;
         Says Tgs A
              (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
           \<in> set evs;
         \<not> expiredAK Ta evs; \<not> expiredSK Ts evs;
         A \<notin> bad;  B \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Key servK \<notin> analz (spies evs)"
apply (blast dest!: Confidentiality_Kas Confidentiality_Tgs)
done

text{*Most general form*}
lemmas Confidentiality_Tgs_ter = authTicket_authentic [THEN Confidentiality_Tgs_bis]

lemmas Confidentiality_Auth_A = authK_authentic [THEN Confidentiality_Kas]

text{*Needs a confidentiality guarantee, hence moved here.
      Authenticity of servK for A*}
lemma servK_authentic_bis_r:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta, authTicket\<rbrace>
           \<in> parts (spies evs);
         Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>
           \<in> parts (spies evs);
         \<not> expiredAK Ta evs; A \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow>Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
       \<in> set evs"
apply (blast dest: authK_authentic Confidentiality_Auth_A servK_authentic_ter)
done

lemma Confidentiality_Serv_A:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta, authTicket\<rbrace>
           \<in> parts (spies evs);
         Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>
           \<in> parts (spies evs);
         \<not> expiredAK Ta evs; \<not> expiredSK Ts evs;
         A \<notin> bad;  B \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Key servK \<notin> analz (spies evs)"
apply (drule authK_authentic, assumption, assumption)
apply (blast dest: Confidentiality_Kas Says_Kas_message_form servK_authentic_ter Confidentiality_Tgs_bis)
done

lemma Confidentiality_B:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);
         Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>
           \<in> parts (spies evs);
         Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta, authTicket\<rbrace>
           \<in> parts (spies evs);
         \<not> expiredSK Ts evs; \<not> expiredAK Ta evs;
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Key servK \<notin> analz (spies evs)"
apply (frule authK_authentic)
apply (frule_tac [3] Confidentiality_Kas)
apply (frule_tac [6] servTicket_authentic, auto)
apply (blast dest!: Confidentiality_Tgs_bis dest: Says_Kas_message_form servK_authentic unique_servKeys unique_authKeys)
done

lemma u_Confidentiality_B:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);
         \<not> expiredSK Ts evs;
         A \<notin> bad;  B \<notin> bad;  B \<noteq> Tgs; evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Key servK \<notin> analz (spies evs)"
apply (blast dest: u_servTicket_authentic u_NotexpiredSK_NotexpiredAK Confidentiality_Tgs_bis)
done



subsection{*2. Parties' strong authentication: 
       non-injective agreement on the session key. The same guarantees also
       express key distribution, hence their names*}

text{*Authentication here still is weak agreement - of B with A*}
lemma A_authenticates_B:
     "\<lbrakk> Crypt servK (Number T3) \<in> parts (spies evs);
         Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>
           \<in> parts (spies evs);
         Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta, authTicket\<rbrace>
           \<in> parts (spies evs);
         Key authK \<notin> analz (spies evs); Key servK \<notin> analz (spies evs);
         A \<notin> bad;  B \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
      \<Longrightarrow> Says B A (Crypt servK (Number T3)) \<in> set evs"
apply (frule authK_authentic)
apply assumption+
apply (frule servK_authentic)
prefer 2 apply (blast dest: authK_authentic Says_Kas_message_form)
apply assumption+
apply (blast dest: K4_imp_K2 Key_unique_SesKey intro!: Says_K6)
(*Single command proof: slower!
apply (blast dest: authK_authentic servK_authentic Says_Kas_message_form Key_unique_SesKey K4_imp_K2 intro!: Says_K6)
*)
done

(*These two have never been proved, because never were they needed before!*)
lemma shrK_in_initState_Server[iff]:  "Key (shrK A) \<in> initState Kas"
by (induct_tac "A", auto)
lemma shrK_in_knows_Server [iff]: "Key (shrK A) \<in> knows Kas evs"
by (simp add: initState_subset_knows [THEN subsetD])
(*Because of our simple model of Tgs, the equivalent for it required an axiom*)


lemma A_authenticates_and_keydist_to_Kas:
   "\<lbrakk> Gets A (Crypt (shrK A) \<lbrace>Key authK, Peer, Ta, authTicket\<rbrace>) \<in> set evs;
      A \<notin> bad;  evs \<in> kerbIV_gets \<rbrakk>
  \<Longrightarrow> Says Kas A (Crypt (shrK A) \<lbrace>Key authK, Peer, Ta, authTicket\<rbrace>) \<in> set evs
  \<and> Key authK \<in> analz(knows Kas evs)"
apply (force dest!: authK_authentic Says_imp_knows [THEN analz.Inj, THEN analz.Decrypt, THEN analz.Fst])
done


lemma K3_imp_Gets_evs:
  "\<lbrakk> Says A Tgs \<lbrace>Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>,
                 Crypt authK \<lbrace>Agent A, Number T2\<rbrace>, Agent B\<rbrace> 
      \<in> set evs;  A \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow>  Gets A (Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta, 
                 Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>\<rbrace>)
       \<in> set evs"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply auto
apply (blast dest: authTicket_form)
done

lemma Tgs_authenticates_and_keydist_to_A:
  "\<lbrakk>  Gets Tgs \<lbrace>
          Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>,
          Crypt authK \<lbrace>Agent A, Number T2\<rbrace>, Agent B \<rbrace> \<in> set evs;
      Key authK \<notin> analz (spies evs); A \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> \<exists> B. Says A Tgs \<lbrace>
          Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>,
          Crypt authK \<lbrace>Agent A, Number T2\<rbrace>, Agent B \<rbrace> \<in> set evs
 \<and>  Key authK \<in> analz (knows A evs)"  
apply (frule Gets_imp_knows_Spy [THEN parts.Inj, THEN parts.Fst], assumption)
apply (drule Gets_imp_knows_Spy [THEN parts.Inj, THEN parts.Snd, THEN parts.Fst], assumption)
apply (drule Tgs_authenticates_A, assumption+, simp)
apply (force dest!: K3_imp_Gets_evs Gets_imp_knows [THEN analz.Inj, THEN analz.Decrypt, THEN analz.Fst])
done

lemma K4_imp_Gets:
  "\<lbrakk> Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
       \<in> set evs; evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> \<exists> Ta X. 
     Gets Tgs \<lbrace>Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>, X\<rbrace>
       \<in> set evs"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply auto
done

lemma A_authenticates_and_keydist_to_Tgs:
 "\<lbrakk>  Gets A (Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta, authTicket\<rbrace>)
       \<in> set evs;
     Gets A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
       \<in> set evs;
     Key authK \<notin> analz (spies evs); A \<notin> bad;
     evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> Says Tgs A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>)
       \<in> set evs
  \<and> Key authK \<in> analz (knows Tgs evs)
  \<and> Key servK \<in> analz (knows Tgs evs)"
apply (drule Gets_imp_knows_Spy [THEN parts.Inj], assumption)
apply (drule Gets_imp_knows_Spy [THEN parts.Inj], assumption)
apply (frule authK_authentic, assumption+)
apply (drule servK_authentic_ter, assumption+)
apply (frule K4_imp_Gets, assumption, erule exE, erule exE)
apply (drule Gets_imp_knows [THEN analz.Inj, THEN analz.Fst, THEN analz.Decrypt, THEN analz.Snd, THEN analz.Snd, THEN analz.Fst], assumption, force)
apply (frule Says_imp_knows [THEN analz.Inj, THEN analz.Decrypt, THEN analz.Fst])
apply (force dest!: authK_authentic Says_Kas_message_form)
apply simp
done

lemma K5_imp_Gets:
  "\<lbrakk> Says A B \<lbrace>servTicket, Crypt servK \<lbrace>Agent A, Number T3\<rbrace>\<rbrace> \<in> set evs;
    A \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> \<exists> authK Ts authTicket T2.
    Gets A (Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>) \<in> set evs
 \<and> Says A Tgs \<lbrace>authTicket, Crypt authK \<lbrace>Agent A, Number T2\<rbrace>, Agent B\<rbrace>  \<in> set evs"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply auto
done 

lemma K3_imp_Gets:
  "\<lbrakk> Says A Tgs \<lbrace>authTicket, Crypt authK \<lbrace>Agent A, Number T2\<rbrace>, Agent B\<rbrace>
       \<in> set evs;
    A \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> \<exists> Ta. Gets A (Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta, authTicket\<rbrace>) \<in> set evs";
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply auto
done 

lemma B_authenticates_and_keydist_to_A:
     "\<lbrakk> Gets B \<lbrace>Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>,
                Crypt servK \<lbrace>Agent A, Number T3\<rbrace>\<rbrace> \<in> set evs;
        Key servK \<notin> analz (spies evs);
        A \<notin> bad; B \<notin> bad; B \<noteq> Tgs; evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> Says A B \<lbrace>Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>,
               Crypt servK \<lbrace>Agent A, Number T3\<rbrace>\<rbrace> \<in> set evs
  \<and> Key servK \<in> analz (knows A evs)"
apply (frule Gets_imp_knows_Spy [THEN parts.Inj, THEN parts.Fst, THEN servTicket_authentic_Tgs], assumption+)  
apply (drule Gets_imp_knows_Spy [THEN parts.Inj, THEN parts.Snd], assumption)
apply (erule exE, drule Says_K5, assumption+)
apply (frule K5_imp_Gets, assumption+)
apply clarify
apply (drule K3_imp_Gets, assumption+)
apply (erule exE)
apply (frule Gets_imp_knows_Spy [THEN parts.Inj, THEN authK_authentic, THEN Says_Kas_message_form], assumption+, clarify)
apply (force dest!: Gets_imp_knows [THEN analz.Inj, THEN analz.Decrypt, THEN analz.Fst])
done


lemma K6_imp_Gets:
  "\<lbrakk> Says B A (Crypt servK (Number T3)) \<in> set evs;
     B \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
\<Longrightarrow> \<exists> Ts X. Gets B \<lbrace>Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>,X\<rbrace>
       \<in> set evs"
apply (erule rev_mp)
apply (erule kerbIV_gets.induct)
apply auto
done


lemma A_authenticates_and_keydist_to_B:
  "\<lbrakk> Gets A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts, servTicket\<rbrace>,
             Crypt servK (Number T3)\<rbrace> \<in> set evs;
     Gets A (Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta, authTicket\<rbrace>)
           \<in> set evs;
     Key authK \<notin> analz (spies evs); Key servK \<notin> analz (spies evs);
     A \<notin> bad;  B \<notin> bad; evs \<in> kerbIV_gets \<rbrakk>
 \<Longrightarrow> Says B A (Crypt servK (Number T3)) \<in> set evs 
   \<and> Key servK \<in> analz (knows B evs)"
apply (frule Gets_imp_knows_Spy [THEN parts.Inj, THEN parts.Fst], assumption)
apply (drule Gets_imp_knows_Spy [THEN parts.Inj, THEN parts.Snd], assumption)
apply (drule Gets_imp_knows_Spy [THEN parts.Inj], assumption)
apply (drule A_authenticates_B, assumption+)
apply (force dest!: K6_imp_Gets Gets_imp_knows [THEN analz.Inj, THEN analz.Fst, THEN analz.Decrypt, THEN analz.Snd, THEN analz.Snd, THEN analz.Fst])
done

 

end

