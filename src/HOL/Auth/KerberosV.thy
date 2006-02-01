(*  ID:         $Id$
    Author:     Giampaolo Bella, Catania University
*)

header{*The Kerberos Protocol, Version V*}

theory KerberosV imports Public begin

text{*The "u" prefix indicates theorems referring to an updated version of the protocol. The "r" suffix indicates theorems where the confidentiality assumptions are relaxed by the corresponding arguments.*}

syntax
  Kas :: agent
  Tgs :: agent  --{*the two servers are translations...*}


translations
  "Kas"       == "Server "
  "Tgs"       == "Friend 0"


axioms
  Tgs_not_bad [iff]: "Tgs \<notin> bad"
   --{*Tgs is secure --- we already know that Kas is secure*}

(*The current time is just the length of the trace!*)
syntax
    CT :: "event list=>nat"

    expiredAK :: "[nat, event list] => bool"

    expiredSK :: "[nat, event list] => bool"

    expiredA :: "[nat, event list] => bool"

    valid :: "[nat, nat] => bool"  ("valid _ wrt _")


constdefs
 (* authKeys are those contained in an authTicket *)
    authKeys :: "event list => key set"
    "authKeys evs == {authK. \<exists>A Peer Ta. 
        Says Kas A \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Agent Peer, Ta\<rbrace>,
                     Crypt (shrK Peer) \<lbrace>Agent A, Agent Peer, Key authK, Ta\<rbrace>
                   \<rbrace> \<in> set evs}"

 (* A is the true creator of X if she has sent X and X never appeared on
    the trace before this event. Recall that traces grow from head. *)
  Issues :: "[agent, agent, msg, event list] => bool"
             ("_ Issues _ with _ on _")
   "A Issues B with X on evs ==
      \<exists>Y. Says A B Y \<in> set evs \<and> X \<in> parts {Y} \<and>
      X \<notin> parts (spies (takeWhile (% z. z  \<noteq> Says A B Y) (rev evs)))"


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

translations
   "CT" == "length "

   "expiredAK T evs" == "authKlife + T < CT evs"

   "expiredSK T evs" == "servKlife + T < CT evs"

   "expiredA T evs" == "authlife + T < CT evs"

   "valid T1 wrt T2" == "T1 <= replylife + T2"

(*---------------------------------------------------------------------*)


(* Predicate formalising the association between authKeys and servKeys *)
constdefs
  AKcryptSK :: "[key, key, event list] => bool"
  "AKcryptSK authK servK evs ==
     \<exists>A B tt.
       Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, tt\<rbrace>,
                    Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, tt\<rbrace> \<rbrace>
         \<in> set evs"

consts

kerbV   :: "event list set"
inductive "kerbV"
  intros

   Nil:  "[] \<in> kerbV"

   Fake: "\<lbrakk> evsf \<in> kerbV;  X \<in> synth (analz (spies evsf)) \<rbrakk>
          \<Longrightarrow> Says Spy B X  # evsf \<in> kerbV"


(*Authentication phase*)
   KV1:   "\<lbrakk> evs1 \<in> kerbV \<rbrakk>
          \<Longrightarrow> Says A Kas \<lbrace>Agent A, Agent Tgs, Number (CT evs1)\<rbrace> # evs1
          \<in> kerbV"
   (*Unlike version IV, authTicket is not re-encrypted*)
   KV2:  "\<lbrakk> evs2 \<in> kerbV; Key authK \<notin> used evs2; authK \<in> symKeys;
            Says A' Kas \<lbrace>Agent A, Agent Tgs, Number T1\<rbrace> \<in> set evs2 \<rbrakk>
          \<Longrightarrow> Says Kas A \<lbrace>
          Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number (CT evs2)\<rbrace>,
        Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number (CT evs2)\<rbrace> 
                         \<rbrace> # evs2 \<in> kerbV"


(* Authorisation phase *)
   KV3:  "\<lbrakk> evs3 \<in> kerbV; A \<noteq> Kas; A \<noteq> Tgs;
            Says A Kas \<lbrace>Agent A, Agent Tgs, Number T1\<rbrace> \<in> set evs3;
            Says Kas' A \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>,
                          authTicket\<rbrace> \<in> set evs3;
            valid Ta wrt T1
         \<rbrakk>
          \<Longrightarrow> Says A Tgs \<lbrace>authTicket,
                           (Crypt authK \<lbrace>Agent A, Number (CT evs3)\<rbrace>),
                           Agent B\<rbrace> # evs3 \<in> kerbV"
   (*Unlike version IV, servTicket is not re-encrypted*)
   KV4:  "\<lbrakk> evs4 \<in> kerbV; Key servK \<notin> used evs4; servK \<in> symKeys;
            B \<noteq> Tgs;  authK \<in> symKeys;
            Says A' Tgs \<lbrace>
             (Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK,
				 Number Ta\<rbrace>),
             (Crypt authK \<lbrace>Agent A, Number T2\<rbrace>), Agent B\<rbrace>
	        \<in> set evs4;
            \<not> expiredAK Ta evs4;
            \<not> expiredA T2 evs4;
            servKlife + (CT evs4) <= authKlife + Ta
         \<rbrakk>
          \<Longrightarrow> Says Tgs A \<lbrace>
             Crypt authK \<lbrace>Key servK, Agent B, Number (CT evs4)\<rbrace>,
   Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number (CT evs4)\<rbrace> 
                          \<rbrace> # evs4 \<in> kerbV"


(*Service phase*)
   KV5:  "\<lbrakk> evs5 \<in> kerbV; authK \<in> symKeys; servK \<in> symKeys;
            A \<noteq> Kas; A \<noteq> Tgs;
            Says A Tgs
                \<lbrace>authTicket, Crypt authK \<lbrace>Agent A, Number T2\<rbrace>,
		  Agent B\<rbrace>
              \<in> set evs5;
            Says Tgs' A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>,
                          servTicket\<rbrace>
                \<in> set evs5;
            valid Ts wrt T2 \<rbrakk>
          \<Longrightarrow> Says A B \<lbrace>servTicket,
			 Crypt servK \<lbrace>Agent A, Number (CT evs5)\<rbrace> \<rbrace>
               # evs5 \<in> kerbV"

    KV6:  "\<lbrakk> evs6 \<in> kerbV; B \<noteq> Kas; B \<noteq> Tgs;
            Says A' B \<lbrace>
              (Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>),
              (Crypt servK \<lbrace>Agent A, Number T3\<rbrace>)\<rbrace>
            \<in> set evs6;
            \<not> expiredSK Ts evs6;
            \<not> expiredA T3 evs6
         \<rbrakk>
          \<Longrightarrow> Says B A (Crypt servK (Number Ta2))
               # evs6 \<in> kerbV"



(* Leaking an authK... *)
   Oops1:"\<lbrakk> evsO1 \<in> kerbV;  A \<noteq> Spy;
             Says Kas A \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>,
                          authTicket\<rbrace>  \<in> set evsO1;
              expiredAK Ta evsO1 \<rbrakk>
          \<Longrightarrow> Notes Spy \<lbrace>Agent A, Agent Tgs, Number Ta, Key authK\<rbrace>
               # evsO1 \<in> kerbV"

(*Leaking a servK... *)
   Oops2: "\<lbrakk> evsO2 \<in> kerbV;  A \<noteq> Spy;
              Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>,
                           servTicket\<rbrace>  \<in> set evsO2;
              expiredSK Ts evsO2 \<rbrakk>
          \<Longrightarrow> Notes Spy \<lbrace>Agent A, Agent B, Number Ts, Key servK\<rbrace>
               # evsO2 \<in> kerbV"



declare Says_imp_knows_Spy [THEN parts.Inj, dest]
declare parts.Body [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un [dest]



subsection{*Lemmas about lists, for reasoning about  Issues*}

lemma spies_Says_rev: "spies (evs @ [Says A B X]) = insert X (spies evs)"
apply (induct_tac "evs")
apply (induct_tac [2] "a", auto)
done

lemma spies_Gets_rev: "spies (evs @ [Gets A X]) = spies evs"
apply (induct_tac "evs")
apply (induct_tac [2] "a", auto)
done

lemma spies_Notes_rev: "spies (evs @ [Notes A X]) =
          (if A:bad then insert X (spies evs) else spies evs)"
apply (induct_tac "evs")
apply (induct_tac [2] "a", auto)
done

lemma spies_evs_rev: "spies evs = spies (rev evs)"
apply (induct_tac "evs")
apply (induct_tac [2] "a")
apply (simp_all (no_asm_simp) add: spies_Says_rev spies_Gets_rev spies_Notes_rev)
done

lemmas parts_spies_evs_revD2 = spies_evs_rev [THEN equalityD2, THEN parts_mono]

lemma spies_takeWhile: "spies (takeWhile P evs) <=  spies evs"
apply (induct_tac "evs")
apply (induct_tac [2] "a", auto)
txt{* Resembles @{text"used_subset_append"} in theory Event.*}
done

lemmas parts_spies_takeWhile_mono = spies_takeWhile [THEN parts_mono]


subsection{*Lemmas about @{term authKeys}*}

lemma authKeys_empty: "authKeys [] = {}"
apply (unfold authKeys_def)
apply (simp (no_asm))
done

lemma authKeys_not_insert:
 "(\<forall>A Ta akey Peer.
   ev \<noteq> Says Kas A \<lbrace>Crypt (shrK A) \<lbrace>akey, Agent Peer, Ta\<rbrace>,
                     Crypt (shrK Peer) \<lbrace>Agent A, Agent Peer, akey, Ta\<rbrace> \<rbrace>)
       \<Longrightarrow> authKeys (ev # evs) = authKeys evs"
apply (unfold authKeys_def, auto)
done

lemma authKeys_insert:
  "authKeys
     (Says Kas A \<lbrace>Crypt (shrK A) \<lbrace>Key K, Agent Peer, Number Ta\<rbrace>,
         Crypt (shrK Peer) \<lbrace>Agent A, Agent Peer, Key K, Number Ta\<rbrace> \<rbrace> # evs)
       = insert K (authKeys evs)"
apply (unfold authKeys_def, auto)
done

lemma authKeys_simp:
   "K \<in> authKeys
    (Says Kas A \<lbrace>Crypt (shrK A) \<lbrace>Key K', Agent Peer, Number Ta\<rbrace>,
        Crypt (shrK Peer) \<lbrace>Agent A, Agent Peer, Key K', Number Ta\<rbrace> \<rbrace> # evs)
        \<Longrightarrow> K = K' | K \<in> authKeys evs"
apply (unfold authKeys_def, auto)
done

lemma authKeysI:
   "Says Kas A \<lbrace>Crypt (shrK A) \<lbrace>Key K, Agent Tgs, Number Ta\<rbrace>,
         Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key K, Number Ta\<rbrace> \<rbrace> \<in> set evs
        \<Longrightarrow> K \<in> authKeys evs"
apply (unfold authKeys_def, auto)
done

lemma authKeys_used: "K \<in> authKeys evs \<Longrightarrow> Key K \<in> used evs"
apply (simp add: authKeys_def, blast)
done


subsection{*Forwarding Lemmas*}

lemma Says_ticket_parts:
     "Says S A \<lbrace>Crypt K \<lbrace>SesKey, B, TimeStamp\<rbrace>, Ticket\<rbrace>
               \<in> set evs \<Longrightarrow> Ticket \<in> parts (spies evs)"
apply blast
done

lemma Says_ticket_analz:
     "Says S A \<lbrace>Crypt K \<lbrace>SesKey, B, TimeStamp\<rbrace>, Ticket\<rbrace>
               \<in> set evs \<Longrightarrow> Ticket \<in> analz (spies evs)"
apply (blast dest: Says_imp_knows_Spy [THEN analz.Inj, THEN analz.Snd])
done

lemma Oops_range_spies1:
     "\<lbrakk> Says Kas A \<lbrace>Crypt KeyA \<lbrace>Key authK, Peer, Ta\<rbrace>, authTicket\<rbrace>
           \<in> set evs ;
         evs \<in> kerbV \<rbrakk> \<Longrightarrow> authK \<notin> range shrK & authK \<in> symKeys"
apply (erule rev_mp)
apply (erule kerbV.induct, auto)
done

lemma Oops_range_spies2:
     "\<lbrakk> Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Ts\<rbrace>, servTicket\<rbrace>
           \<in> set evs ;
         evs \<in> kerbV \<rbrakk> \<Longrightarrow> servK \<notin> range shrK \<and> servK \<in> symKeys"
apply (erule rev_mp)
apply (erule kerbV.induct, auto)
done


(*Spy never sees another agent's shared key! (unless it's lost at start)*)
lemma Spy_see_shrK [simp]:
     "evs \<in> kerbV \<Longrightarrow> (Key (shrK A) \<in> parts (spies evs)) = (A \<in> bad)"
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all)
apply (blast+)
done

lemma Spy_analz_shrK [simp]:
     "evs \<in> kerbV \<Longrightarrow> (Key (shrK A) \<in> analz (spies evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "\<lbrakk> Key (shrK A) \<in> parts (spies evs);  evs \<in> kerbV \<rbrakk> \<Longrightarrow> A:bad"
by (blast dest: Spy_see_shrK)
lemmas Spy_analz_shrK_D = analz_subset_parts [THEN subsetD, THEN Spy_see_shrK_D, dest!]

text{*Nobody can have used non-existent keys!*}
lemma new_keys_not_used [simp]:
    "\<lbrakk>Key K \<notin> used evs; K \<in> symKeys; evs \<in> kerbV\<rbrakk>
     \<Longrightarrow> K \<notin> keysFor (parts (spies evs))"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all)
txt{*Fake*}
apply (force dest!: keysFor_parts_insert)
txt{*Others*}
apply (force dest!: analz_shrK_Decrypt)+
done

(*Earlier, all protocol proofs declared this theorem.
  But few of them actually need it! (Another is Yahalom) *)
lemma new_keys_not_analzd:
 "\<lbrakk>evs \<in> kerbV; K \<in> symKeys; Key K \<notin> used evs\<rbrakk>
  \<Longrightarrow> K \<notin> keysFor (analz (spies evs))"
by (blast dest: new_keys_not_used intro: keysFor_mono [THEN subsetD])



subsection{*Regularity Lemmas*}
text{*These concern the form of items passed in messages*}

text{*Describes the form of all components sent by Kas*}
lemma Says_Kas_message_form:
     "\<lbrakk> Says Kas A \<lbrace>Crypt K \<lbrace>Key authK, Agent Peer, Ta\<rbrace>, authTicket\<rbrace>
           \<in> set evs;
         evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> authK \<notin> range shrK \<and> authK \<in> authKeys evs \<and> authK \<in> symKeys \<and> 
  authTicket = (Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Ta\<rbrace>) \<and>
             K = shrK A  \<and> Peer = Tgs"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (simp_all (no_asm) add: authKeys_def authKeys_insert)
apply blast+
done



(*This lemma is essential for proving Says_Tgs_message_form:

  the session key authK
  supplied by Kas in the authentication ticket
  cannot be a long-term key!

  Generalised to any session keys (both authK and servK).
*)
lemma SesKey_is_session_key:
     "\<lbrakk> Crypt (shrK Tgs_B) \<lbrace>Agent A, Agent Tgs_B, Key SesKey, Number T\<rbrace>
            \<in> parts (spies evs); Tgs_B \<notin> bad;
         evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> SesKey \<notin> range shrK"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all, blast)
done

lemma authTicket_authentic:
     "\<lbrakk> Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Ta\<rbrace>
           \<in> parts (spies evs);
         evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> Says Kas A \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Ta\<rbrace>,
                 Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Ta\<rbrace>\<rbrace>
            \<in> set evs"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all)
txt{*Fake, K4*}
apply (blast+)
done

lemma authTicket_crypt_authK:
     "\<lbrakk> Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>
           \<in> parts (spies evs);
         evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> authK \<in> authKeys evs"
apply (frule authTicket_authentic, assumption)
apply (simp (no_asm) add: authKeys_def)
apply blast
done

text{*Describes the form of servK, servTicket and authK sent by Tgs*}
lemma Says_Tgs_message_form:
     "\<lbrakk> Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Ts\<rbrace>, servTicket\<rbrace>
           \<in> set evs;
         evs \<in> kerbV \<rbrakk>
   \<Longrightarrow> B \<noteq> Tgs \<and> 
       servK \<notin> range shrK \<and> servK \<notin> authKeys evs \<and> servK \<in> symKeys \<and>
       servTicket = (Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Ts\<rbrace>) \<and>
       authK \<notin> range shrK \<and> authK \<in> authKeys evs \<and> authK \<in> symKeys"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (simp_all add: authKeys_insert authKeys_not_insert authKeys_empty authKeys_simp, blast, auto)
txt{*Three subcases of Message 4*}
apply (blast dest!: authKeys_used Says_Kas_message_form)
apply (blast dest!: SesKey_is_session_key)
apply (blast dest: authTicket_crypt_authK)
done



(*
lemma authTicket_form:
lemma servTicket_form:
lemma Says_kas_message_form:
lemma Says_tgs_message_form:

cannot be proved for version V, but a new proof strategy can be used in their
place. The new strategy merely says that both the authTicket and the servTicket
are in parts and in analz as soon as they appear, using lemmas Says_ticket_parts and Says_ticket_analz. 
The new strategy always lets the simplifier solve cases K3 and K5, saving on
long dedicated analyses, which seemed unavoidable. For this reason, lemma 
servK_notin_authKeysD is no longer needed.
*)

subsection{*Authenticity theorems: confirm origin of sensitive messages*}

lemma authK_authentic:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Key authK, Peer, Ta\<rbrace>
           \<in> parts (spies evs);
         A \<notin> bad;  evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> \<exists> AT. Says Kas A \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Peer, Ta\<rbrace>, AT\<rbrace>
            \<in> set evs"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all)
apply blast+
done

text{*If a certain encrypted message appears then it originated with Tgs*}
lemma servK_authentic:
     "\<lbrakk> Crypt authK \<lbrace>Key servK, Agent B, Ts\<rbrace>
           \<in> parts (spies evs);
         Key authK \<notin> analz (spies evs);
         authK \<notin> range shrK;
         evs \<in> kerbV \<rbrakk>
 \<Longrightarrow> \<exists>A ST. Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Ts\<rbrace>, ST\<rbrace>
       \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbV.induct, analz_mono_contra)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all)
apply blast+
done

lemma servK_authentic_bis:
     "\<lbrakk> Crypt authK \<lbrace>Key servK, Agent B, Ts\<rbrace>
           \<in> parts (spies evs);
         Key authK \<notin> analz (spies evs);
         B \<noteq> Tgs;
         evs \<in> kerbV \<rbrakk>
 \<Longrightarrow> \<exists>A ST. Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Ts\<rbrace>, ST\<rbrace>
       \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbV.induct, analz_mono_contra)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all, blast+)
done

text{*Authenticity of servK for B*}
lemma servTicket_authentic_Tgs:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Ts\<rbrace>
           \<in> parts (spies evs);  B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerbV \<rbrakk>
 \<Longrightarrow> \<exists>authK.
       Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Ts\<rbrace>,
                    Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Ts\<rbrace>\<rbrace>
       \<in> set evs"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all, blast+)
done

text{*Anticipated here from next subsection*}
lemma K4_imp_K2:
"\<lbrakk> Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>, servTicket\<rbrace>
      \<in> set evs;  evs \<in> kerbV\<rbrakk>
   \<Longrightarrow> \<exists>Ta. Says Kas A
        \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>,
           Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace> \<rbrace>
        \<in> set evs"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all, auto)
apply (blast dest!: Says_imp_spies [THEN parts.Inj, THEN parts.Fst, THEN authTicket_authentic])
done

text{*Anticipated here from next subsection*}
lemma u_K4_imp_K2:
"\<lbrakk> Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>, servTicket\<rbrace>  \<in> set evs; evs \<in> kerbV\<rbrakk>
   \<Longrightarrow> \<exists>Ta. Says Kas A \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>,
             Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace> \<rbrace>
             \<in> set evs
          \<and> servKlife + Ts <= authKlife + Ta"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all, auto)
apply (blast dest!: Says_imp_spies [THEN parts.Inj, THEN parts.Fst, THEN authTicket_authentic])
done

lemma servTicket_authentic_Kas:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);  B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> \<exists>authK Ta.
       Says Kas A
         \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>,
           Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace> \<rbrace>
        \<in> set evs"
apply (blast dest!: servTicket_authentic_Tgs K4_imp_K2)
done

lemma u_servTicket_authentic_Kas:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);  B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> \<exists>authK Ta.
       Says Kas A
         \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>,
           Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace> \<rbrace>
        \<in> set evs \<and> 
      servKlife + Ts <= authKlife + Ta"
apply (blast dest!: servTicket_authentic_Tgs u_K4_imp_K2)
done

lemma servTicket_authentic:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);  B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerbV \<rbrakk>
 \<Longrightarrow> \<exists>Ta authK.
     Says Kas A \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>,
                  Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace> \<rbrace>  \<in> set evs
     \<and> Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>,
                  Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>\<rbrace>
       \<in> set evs"
apply (blast dest: servTicket_authentic_Tgs K4_imp_K2)
done

lemma u_servTicket_authentic:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);  B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerbV \<rbrakk>
 \<Longrightarrow> \<exists>Ta authK.
     Says Kas A \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>,
                  Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>\<rbrace> \<in> set evs
     \<and> Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>,
                 Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>\<rbrace>
       \<in> set evs
     \<and> servKlife + Ts <= authKlife + Ta"
apply (blast dest: servTicket_authentic_Tgs u_K4_imp_K2)
done

lemma u_NotexpiredSK_NotexpiredAK:
     "\<lbrakk> \<not> expiredSK Ts evs; servKlife + Ts <= authKlife + Ta \<rbrakk>
      \<Longrightarrow> \<not> expiredAK Ta evs"
apply (blast dest: leI le_trans dest: leD)
done


subsection{* Reliability: friendly agents send somthing if something else happened*}

lemma K3_imp_K2:
     "\<lbrakk> Says A Tgs
             \<lbrace>authTicket, Crypt authK \<lbrace>Agent A, Number T2\<rbrace>, Agent B\<rbrace>
           \<in> set evs;
         A \<notin> bad;  evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> \<exists>Ta AT. Says Kas A \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Ta\<rbrace>, 
                               AT\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all, blast, blast)
apply (blast dest: Says_imp_spies [THEN parts.Inj, THEN parts.Fst, THEN authK_authentic])
done

text{*Anticipated here from next subsection. An authK is encrypted by one and only one Shared key. A servK is encrypted by one and only one authK.*}
lemma Key_unique_SesKey:
     "\<lbrakk> Crypt K  \<lbrace>Key SesKey,  Agent B, T\<rbrace>
           \<in> parts (spies evs);
         Crypt K' \<lbrace>Key SesKey,  Agent B', T'\<rbrace>
           \<in> parts (spies evs);  Key SesKey \<notin> analz (spies evs);
         evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> K=K' \<and> B=B' \<and> T=T'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbV.induct, analz_mono_contra)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all)
txt{*Fake, K2, K4*}
apply (blast+)
done

text{*This inevitably has an existential form in version V*}
lemma Says_K5:
     "\<lbrakk> Crypt servK \<lbrace>Agent A, Number T3\<rbrace> \<in> parts (spies evs);
         Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>,
                                     servTicket\<rbrace> \<in> set evs;
         Key servK \<notin> analz (spies evs);
         A \<notin> bad; B \<notin> bad; evs \<in> kerbV \<rbrakk>
 \<Longrightarrow> \<exists> ST. Says A B \<lbrace>ST, Crypt servK \<lbrace>Agent A, Number T3\<rbrace>\<rbrace> \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbV.induct, analz_mono_contra)
apply (frule_tac [5] Says_ticket_parts)
apply (frule_tac [7] Says_ticket_parts)
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
         evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> A=A' & B=B' & T=T'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbV.induct, analz_mono_contra)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all)
txt{*Fake, K2, K4*}
apply (blast+)
done

lemma Says_K6:
     "\<lbrakk> Crypt servK (Number T3) \<in> parts (spies evs);
         Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>,
                      servTicket\<rbrace> \<in> set evs;
         Key servK \<notin> analz (spies evs);
         A \<notin> bad; B \<notin> bad; evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> Says B A (Crypt servK (Number T3)) \<in> set evs"
apply (frule Says_Tgs_message_form, assumption, clarify)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbV.induct, analz_mono_contra)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts)
apply (simp_all (no_asm_simp))

txt{*fake*}
apply blast
txt{*K4*}
apply (force dest!: Crypt_imp_keysFor, clarify)
txt{*K6*}
apply (drule  Says_imp_spies [THEN parts.Inj, THEN parts.Fst])
apply (drule  Says_imp_spies [THEN parts.Inj, THEN parts.Snd])
apply (blast dest!: unique_CryptKey)
done

text{*Needs a unicity theorem, hence moved here*}
lemma servK_authentic_ter:
 "\<lbrakk> Says Kas A
       \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Ta\<rbrace>, authTicket\<rbrace> \<in> set evs;
     Crypt authK \<lbrace>Key servK, Agent B, Ts\<rbrace>
       \<in> parts (spies evs);
     Key authK \<notin> analz (spies evs);
     evs \<in> kerbV \<rbrakk>
 \<Longrightarrow> Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Ts\<rbrace>, 
                 Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Ts\<rbrace> \<rbrace>
       \<in> set evs"
apply (frule Says_Kas_message_form, assumption)
apply clarify
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbV.induct, analz_mono_contra)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all, blast)
txt{*K2 and K4 remain*}
apply (blast dest!: servK_authentic Says_Tgs_message_form authKeys_used)
apply (blast dest!: unique_CryptKey)
done


subsection{*Unicity Theorems*}

text{* The session key, if secure, uniquely identifies the Ticket
   whether authTicket or servTicket. As a matter of fact, one can read
   also Tgs in the place of B.                                     *}


lemma unique_authKeys:
     "\<lbrakk> Says Kas A
              \<lbrace>Crypt Ka \<lbrace>Key authK, Agent Tgs, Ta\<rbrace>, X\<rbrace> \<in> set evs;
         Says Kas A'
              \<lbrace>Crypt Ka' \<lbrace>Key authK, Agent Tgs, Ta'\<rbrace>, X'\<rbrace> \<in> set evs;
         evs \<in> kerbV \<rbrakk> \<Longrightarrow> A=A' \<and> Ka=Ka' \<and> Ta=Ta' \<and> X=X'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all)
apply blast+
done

text{* servK uniquely identifies the message from Tgs *}
lemma unique_servKeys:
     "\<lbrakk> Says Tgs A
              \<lbrace>Crypt K \<lbrace>Key servK, Agent B, Ts\<rbrace>, X\<rbrace> \<in> set evs;
         Says Tgs A'
              \<lbrace>Crypt K' \<lbrace>Key servK, Agent B', Ts'\<rbrace>, X'\<rbrace> \<in> set evs;
         evs \<in> kerbV \<rbrakk> \<Longrightarrow> A=A' \<and> B=B' \<and> K=K' \<and> Ts=Ts' \<and> X=X'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all)
apply blast+
done

subsection{*Lemmas About the Predicate @{term AKcryptSK}*}

lemma not_AKcryptSK_Nil [iff]: "\<not> AKcryptSK authK servK []"
apply (simp add: AKcryptSK_def)
done

lemma AKcryptSKI:
 "\<lbrakk> Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, tt\<rbrace>, X \<rbrace> \<in> set evs;
     evs \<in> kerbV \<rbrakk> \<Longrightarrow> AKcryptSK authK servK evs"
apply (unfold AKcryptSK_def)
apply (blast dest: Says_Tgs_message_form)
done

lemma AKcryptSK_Says [simp]:
   "AKcryptSK authK servK (Says S A X # evs) =
     (S = Tgs \<and>
      (\<exists>B tt. X = \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, tt\<rbrace>,
                    Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, tt\<rbrace> \<rbrace>)
     | AKcryptSK authK servK evs)"
apply (unfold AKcryptSK_def)
apply (simp (no_asm))
apply blast
done

lemma AKcryptSK_Notes [simp]:
   "AKcryptSK authK servK (Notes A X # evs) =
      AKcryptSK authK servK evs"
apply (unfold AKcryptSK_def)
apply (simp (no_asm))
done

(*A fresh authK cannot be associated with any other
  (with respect to a given trace). *)
lemma Auth_fresh_not_AKcryptSK:
     "\<lbrakk> Key authK \<notin> used evs; evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> \<not> AKcryptSK authK servK evs"
apply (unfold AKcryptSK_def)
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all, blast)
done

(*A fresh servK cannot be associated with any other
  (with respect to a given trace). *)
lemma Serv_fresh_not_AKcryptSK:
 "Key servK \<notin> used evs \<Longrightarrow> \<not> AKcryptSK authK servK evs"
apply (unfold AKcryptSK_def, blast)
done

lemma authK_not_AKcryptSK:
     "\<lbrakk> Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, tk\<rbrace>
           \<in> parts (spies evs);  evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> \<not> AKcryptSK K authK evs"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all)
txt{*Fake*}
apply blast
txt{*K2: by freshness*}
apply (simp add: AKcryptSK_def)
apply blast
txt{*K4*}
apply blast
done

text{*A secure serverkey cannot have been used to encrypt others*}
lemma servK_not_AKcryptSK:
 "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key SK, tt\<rbrace> \<in> parts (spies evs);
     Key SK \<notin> analz (spies evs);  SK \<in> symKeys;
     B \<noteq> Tgs;  evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> \<not> AKcryptSK SK K evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbV.induct, analz_mono_contra)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all, blast)
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
     "evs \<in> kerbV \<Longrightarrow> \<not> AKcryptSK K (shrK A) evs"
apply (unfold AKcryptSK_def)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, auto)
done

text{*The Tgs message associates servK with authK and therefore not with any
  other key authK.*}
lemma Says_Tgs_AKcryptSK:
     "\<lbrakk> Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, tt\<rbrace>, X \<rbrace>
           \<in> set evs;
         authK' \<noteq> authK;  evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> \<not> AKcryptSK authK' servK evs"
apply (unfold AKcryptSK_def)
apply (blast dest: unique_servKeys)
done

lemma AKcryptSK_not_AKcryptSK:
     "\<lbrakk> AKcryptSK authK servK evs;  evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> \<not> AKcryptSK servK K evs"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts)
apply (simp_all, safe)
txt{*K4 splits into subcases*}
(*apply simp_all*)
prefer 4 apply (blast dest!: authK_not_AKcryptSK)
txt{*servK is fresh and so could not have been used, by
   @{text new_keys_not_used}*}
 prefer 2 
 apply (force dest!: Crypt_imp_invKey_keysFor simp add: AKcryptSK_def)
txt{*Others by freshness*}
apply (blast+)
done

lemma not_different_AKcryptSK:
     "\<lbrakk> AKcryptSK authK servK evs;
        authK' \<noteq> authK;  evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> \<not> AKcryptSK authK' servK evs  \<and> servK \<in> symKeys"
apply (simp add: AKcryptSK_def)
apply (blast dest: unique_servKeys Says_Tgs_message_form)
done

lemma AKcryptSK_not_AKcryptSK:
     "\<lbrakk> AKcryptSK authK servK evs;  evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> \<not> AKcryptSK servK K evs"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts, simp_all, safe)
txt{*K4 splits into subcases*}
apply simp_all
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
     "\<lbrakk> AKcryptSK K K' evs; K \<in> symKeys; evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> Key K' \<in> analz (insert (Key K) (spies evs))"
apply (simp add: AKcryptSK_def, clarify)
apply (drule Says_imp_spies [THEN analz.Inj, THEN analz_insertI], auto)
done

lemma authKeys_are_not_AKcryptSK:
     "\<lbrakk> K \<in> authKeys evs Un range shrK;  evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> \<forall>SK. \<not> AKcryptSK SK K evs \<and> K \<in> symKeys"
apply (simp add: authKeys_def AKcryptSK_def)
apply (blast dest: Says_Kas_message_form Says_Tgs_message_form)
done

lemma not_authKeys_not_AKcryptSK:
     "\<lbrakk> K \<notin> authKeys evs;
         K \<notin> range shrK; evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> \<forall>SK. \<not> AKcryptSK K SK evs"
apply (simp add: AKcryptSK_def)
apply (blast dest: Says_Tgs_message_form)
done


subsection{*Secrecy Theorems*}

text{*For the Oops2 case of the next theorem*}
lemma Oops2_not_AKcryptSK:
     "\<lbrakk> evs \<in> kerbV;
         Says Tgs A \<lbrace>Crypt authK
                     \<lbrace>Key servK, Agent B, Number Ts\<rbrace>, servTicket\<rbrace>
           \<in> set evs \<rbrakk>
      \<Longrightarrow> \<not> AKcryptSK servK SK evs"
apply (blast dest: AKcryptSKI AKcryptSK_not_AKcryptSK)
done
   
text{* Big simplification law for keys SK that are not crypted by keys in KK
 It helps prove three, otherwise hard, facts about keys. These facts are
 exploited as simplification laws for analz, and also "limit the damage"
 in case of loss of a key to the spy. See ESORICS98.*}
lemma Key_analz_image_Key [rule_format (no_asm)]:
     "evs \<in> kerbV \<Longrightarrow>
      (\<forall>SK KK. SK \<in> symKeys & KK <= -(range shrK) \<longrightarrow>
       (\<forall>K \<in> KK. \<not> AKcryptSK K SK evs)   \<longrightarrow>
       (Key SK \<in> analz (Key`KK Un (spies evs))) =
       (SK \<in> KK | Key SK \<in> analz (spies evs)))"
apply (erule kerbV.induct)
apply (frule_tac [10] Oops_range_spies2)
apply (frule_tac [9] Oops_range_spies1)
(*Used to apply Says_tgs_message form, which is no longer available. 
  Instead\<dots>*)
apply (drule_tac [7] Says_ticket_analz)
(*Used to apply Says_kas_message form, which is no longer available. 
  Instead\<dots>*)
apply (drule_tac [5] Says_ticket_analz)
apply (safe del: impI intro!: Key_analz_image_Key_lemma [THEN impI])
txt{*Case-splits for Oops1 and message 5: the negated case simplifies using
 the induction hypothesis*}
apply (case_tac [9] "AKcryptSK authK SK evsO1")
apply (case_tac [7] "AKcryptSK servK SK evs5")
apply (simp_all del: image_insert
          add: analz_image_freshK_simps AKcryptSK_Says shrK_not_AKcryptSK
               Oops2_not_AKcryptSK Auth_fresh_not_AKcryptSK
               Serv_fresh_not_AKcryptSK Says_Tgs_AKcryptSK Spy_analz_shrK)
txt{*Fake*} 
apply spy_analz
txt{*K2*}
apply blast 
txt{*Cases K3 and K5 solved by the simplifier thanks to the ticket being in 
analz - this strategy is new wrt version IV*} 
txt{*K4*}
apply (blast dest!: authK_not_AKcryptSK)
txt{*Oops1*}
apply clarify
apply simp
apply (blast dest!: AKcryptSK_analz_insert)
done

text{* First simplification law for analz: no session keys encrypt
authentication keys or shared keys. *}
lemma analz_insert_freshK1:
     "\<lbrakk> evs \<in> kerbV;  K \<in> authKeys evs Un range shrK;
        SesKey \<notin> range shrK \<rbrakk>
      \<Longrightarrow> (Key K \<in> analz (insert (Key SesKey) (spies evs))) =
          (K = SesKey | Key K \<in> analz (spies evs))"
apply (frule authKeys_are_not_AKcryptSK, assumption)
apply (simp del: image_insert
            add: analz_image_freshK_simps add: Key_analz_image_Key)
done


text{* Second simplification law for analz: no service keys encrypt any other keys.*}
lemma analz_insert_freshK2:
     "\<lbrakk> evs \<in> kerbV;  servK \<notin> (authKeys evs); servK \<notin> range shrK;
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
    authK' \<noteq> authK; authK' \<notin> range shrK; evs \<in> kerbV \<rbrakk>
        \<Longrightarrow> (Key servK \<in> analz (insert (Key authK') (spies evs))) =
                (servK = authK' | Key servK \<in> analz (spies evs))"
apply (drule_tac authK' = authK' in not_different_AKcryptSK, blast, assumption)
apply (simp del: image_insert
            add: analz_image_freshK_simps add: Key_analz_image_Key)
done

lemma analz_insert_freshK3_bis:
 "\<lbrakk> Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>, servTicket\<rbrace>
        \<in> set evs; 
     authK \<noteq> authK'; authK' \<notin> range shrK; evs \<in> kerbV \<rbrakk>
        \<Longrightarrow> (Key servK \<in> analz (insert (Key authK') (spies evs))) =
                (servK = authK' | Key servK \<in> analz (spies evs))"
apply (frule AKcryptSKI, assumption)
apply (simp add: analz_insert_freshK3)
done

text{*a weakness of the protocol*}
lemma authK_compromises_servK:
     "\<lbrakk> Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>, servTicket\<rbrace>
        \<in> set evs;  authK \<in> symKeys;
         Key authK \<in> analz (spies evs); evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> Key servK \<in> analz (spies evs)"
apply (force dest: Says_imp_spies [THEN analz.Inj, THEN analz.Fst, THEN analz.Decrypt, THEN analz.Fst])
done

text{*lemma @{text servK_notin_authKeysD} not needed in version V*}

text{*If Spy sees the Authentication Key sent in msg K2, then
    the Key has expired.*}
lemma Confidentiality_Kas_lemma [rule_format]:
     "\<lbrakk> authK \<in> symKeys; A \<notin> bad;  evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> Says Kas A
               \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>,
          Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key authK, Number Ta\<rbrace>\<rbrace>
            \<in> set evs \<longrightarrow>
          Key authK \<in> analz (spies evs) \<longrightarrow>
          expiredAK Ta evs"
apply (erule kerbV.induct)
apply (frule_tac [10] Oops_range_spies2)
apply (frule_tac [9] Oops_range_spies1)
apply (frule_tac [7] Says_ticket_analz)
apply (frule_tac [5] Says_ticket_analz)
apply (safe del: impI conjI impCE)
apply (simp_all (no_asm_simp) add: Says_Kas_message_form less_SucI analz_insert_eq not_parts_not_analz analz_insert_freshK1 pushes)
txt{*Fake*}
apply spy_analz
txt{*K2*}
apply blast
txt{*K4*}
apply blast
txt{*Oops1*}
apply (blast dest!: unique_authKeys intro: less_SucI)
txt{*Oops2*}
apply (blast dest: Says_Tgs_message_form Says_Kas_message_form)
done

lemma Confidentiality_Kas:
     "\<lbrakk> Says Kas A
              \<lbrace>Crypt Ka \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>, authTicket\<rbrace>
           \<in> set evs;
        \<not> expiredAK Ta evs;
        A \<notin> bad;  evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> Key authK \<notin> analz (spies evs)"
apply (blast dest: Says_Kas_message_form Confidentiality_Kas_lemma)
done

text{*If Spy sees the Service Key sent in msg K4, then
    the Key has expired.*}

lemma Confidentiality_lemma [rule_format]:
     "\<lbrakk> Says Tgs A
	    \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>,
	      Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>\<rbrace>
	   \<in> set evs;
	Key authK \<notin> analz (spies evs);
        servK \<in> symKeys;
	A \<notin> bad;  B \<notin> bad; evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> Key servK \<in> analz (spies evs) \<longrightarrow>
	  expiredSK Ts evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (rule_tac [9] impI)+;
  --{*The Oops1 case is unusual: must simplify
    @{term "Authkey \<notin> analz (spies (ev#evs))"}, not letting
   @{text analz_mono_contra} weaken it to
   @{term "Authkey \<notin> analz (spies evs)"},
  for we then conclude @{term "authK \<noteq> authKa"}.*}
apply analz_mono_contra
apply (frule_tac [10] Oops_range_spies2)
apply (frule_tac [9] Oops_range_spies1)
apply (frule_tac [7] Says_ticket_analz)
apply (frule_tac [5] Says_ticket_analz)
apply (safe del: impI conjI impCE)
apply (simp_all add: less_SucI new_keys_not_analzd Says_Kas_message_form Says_Tgs_message_form analz_insert_eq not_parts_not_analz analz_insert_freshK1 analz_insert_freshK2 analz_insert_freshK3_bis pushes)
txt{*Fake*}
apply spy_analz
txt{*K2*}
apply (blast intro: parts_insertI less_SucI)
txt{*K4*}
apply (blast dest: authTicket_authentic Confidentiality_Kas)
txt{*Oops1*}
 apply (blast dest: Says_Kas_message_form Says_Tgs_message_form intro: less_SucI)
txt{*Oops2*}
  apply (blast dest: Says_imp_spies [THEN parts.Inj] Key_unique_SesKey intro: less_SucI)
done


text{* In the real world Tgs can't check wheter authK is secure! *}
lemma Confidentiality_Tgs:
     "\<lbrakk> Says Tgs A
              \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>, servTicket\<rbrace>
           \<in> set evs;
         Key authK \<notin> analz (spies evs);
         \<not> expiredSK Ts evs;
         A \<notin> bad;  B \<notin> bad; evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> Key servK \<notin> analz (spies evs)"
apply (blast dest: Says_Tgs_message_form Confidentiality_lemma)
done

text{* In the real world Tgs CAN check what Kas sends! *}
lemma Confidentiality_Tgs_bis:
     "\<lbrakk> Says Kas A
               \<lbrace>Crypt Ka \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>, authTicket\<rbrace>
           \<in> set evs;
         Says Tgs A
              \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>, servTicket\<rbrace>
           \<in> set evs;
         \<not> expiredAK Ta evs; \<not> expiredSK Ts evs;
         A \<notin> bad;  B \<notin> bad; evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> Key servK \<notin> analz (spies evs)"
apply (blast dest!: Confidentiality_Kas Confidentiality_Tgs)
done

text{*Most general form*}
lemmas Confidentiality_Tgs_ter = authTicket_authentic [THEN Confidentiality_Tgs_bis]

lemmas Confidentiality_Auth_A = authK_authentic [THEN exE, THEN Confidentiality_Kas]

text{*Needs a confidentiality guarantee, hence moved here.
      Authenticity of servK for A*}
lemma servK_authentic_bis_r:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>
           \<in> parts (spies evs);
         Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>
           \<in> parts (spies evs);
         \<not> expiredAK Ta evs; A \<notin> bad; evs \<in> kerbV \<rbrakk>
 \<Longrightarrow> Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>, 
                 Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace> \<rbrace>
       \<in> set evs"
apply (frule authK_authentic, assumption, assumption)
apply (erule exE)
apply (drule Confidentiality_Auth_A, assumption, assumption)
apply (blast, assumption, assumption, assumption)
apply (blast dest:  servK_authentic_ter)
done

lemma Confidentiality_Serv_A:
     "\<lbrakk> Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>
           \<in> parts (spies evs);
         Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>
           \<in> parts (spies evs);
         \<not> expiredAK Ta evs; \<not> expiredSK Ts evs;
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> Key servK \<notin> analz (spies evs)"
apply (drule authK_authentic, assumption, assumption)
apply (blast dest: Confidentiality_Kas Says_Kas_message_form servK_authentic_ter Confidentiality_Tgs_bis)
done

lemma Confidentiality_B:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);
         Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>
           \<in> parts (spies evs);
         Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>
           \<in> parts (spies evs);
         \<not> expiredSK Ts evs; \<not> expiredAK Ta evs;
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> Key servK \<notin> analz (spies evs)"
apply (frule authK_authentic)
apply (erule_tac [3] exE)
apply (frule_tac [3] Confidentiality_Kas)
apply (frule_tac [6] servTicket_authentic, auto)
apply (blast dest!: Confidentiality_Tgs_bis dest: Says_Kas_message_form servK_authentic unique_servKeys unique_authKeys)
done

lemma u_Confidentiality_B:
     "\<lbrakk> Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);
         \<not> expiredSK Ts evs;
         A \<notin> bad;  B \<notin> bad;  B \<noteq> Tgs; evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> Key servK \<notin> analz (spies evs)"
apply (blast dest: u_servTicket_authentic u_NotexpiredSK_NotexpiredAK Confidentiality_Tgs_bis)
done



subsection{*Parties authentication: each party verifies "the identity of
       another party who generated some data" (quoted from Neuman and Ts'o).*}

text{*These guarantees don't assess whether two parties agree on
      the same session key: sending a message containing a key
      doesn't a priori state knowledge of the key.*}


text{*These didn't have existential form in version IV*}
lemma B_authenticates_A:
     "\<lbrakk> Crypt servK \<lbrace>Agent A, Number T3\<rbrace> \<in> parts (spies evs);
        Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);
        Key servK \<notin> analz (spies evs);
        A \<notin> bad; B \<notin> bad; B \<noteq> Tgs; evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> \<exists> ST. Says A B \<lbrace>ST, Crypt servK \<lbrace>Agent A, Number T3\<rbrace> \<rbrace> \<in> set evs"
apply (blast dest: servTicket_authentic_Tgs intro: Says_K5)
done

text{*The second assumption tells B what kind of key servK is.*}
lemma B_authenticates_A_r:
     "\<lbrakk> Crypt servK \<lbrace>Agent A, Number T3\<rbrace> \<in> parts (spies evs);
         Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);
         Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>
           \<in> parts (spies evs);
         Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>
           \<in> parts (spies evs);
         \<not> expiredSK Ts evs; \<not> expiredAK Ta evs;
         B \<noteq> Tgs; A \<notin> bad;  B \<notin> bad;  evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> \<exists> ST. Says A B \<lbrace>ST, Crypt servK \<lbrace>Agent A, Number T3\<rbrace> \<rbrace> \<in> set evs"
apply (blast intro: Says_K5 dest: Confidentiality_B servTicket_authentic_Tgs)
done

text{* @{text u_B_authenticates_A} would be the same as @{text B_authenticates_A} because the
 servK confidentiality assumption is yet unrelaxed*}

lemma u_B_authenticates_A_r:
     "\<lbrakk> Crypt servK \<lbrace>Agent A, Number T3\<rbrace> \<in> parts (spies evs);
         Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);
         \<not> expiredSK Ts evs;
         B \<noteq> Tgs; A \<notin> bad;  B \<notin> bad;  evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> \<exists> ST. Says A B \<lbrace>ST, Crypt servK \<lbrace>Agent A, Number T3\<rbrace> \<rbrace> \<in> set evs"
apply (blast intro: Says_K5 dest: u_Confidentiality_B servTicket_authentic_Tgs)
done

lemma A_authenticates_B:
     "\<lbrakk> Crypt servK (Number T3) \<in> parts (spies evs);
         Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>
           \<in> parts (spies evs);
         Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>
           \<in> parts (spies evs);
         Key authK \<notin> analz (spies evs); Key servK \<notin> analz (spies evs);
         A \<notin> bad;  B \<notin> bad; evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> Says B A (Crypt servK (Number T3)) \<in> set evs"
apply (frule authK_authentic)
apply assumption+
apply (frule servK_authentic)
prefer 2 apply (blast dest: authK_authentic Says_Kas_message_form)
apply assumption+
apply clarify
apply (blast dest: K4_imp_K2 Key_unique_SesKey intro!: Says_K6)
(*Single command proof: much slower!
apply (blast dest: authK_authentic servK_authentic Says_Kas_message_form Key_unique_SesKey K4_imp_K2 intro!: Says_K6)
*)
done

lemma A_authenticates_B_r:
     "\<lbrakk> Crypt servK (Number T3) \<in> parts (spies evs);
         Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>
           \<in> parts (spies evs);
         Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>
           \<in> parts (spies evs);
         \<not> expiredAK Ta evs; \<not> expiredSK Ts evs;
         A \<notin> bad;  B \<notin> bad; evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> Says B A (Crypt servK (Number T3)) \<in> set evs"
apply (frule authK_authentic)
apply (erule_tac [3] exE)
apply (frule_tac [3] Says_Kas_message_form)
apply (frule_tac [4] Confidentiality_Kas)
apply (frule_tac [7] servK_authentic)
prefer 8 apply blast
apply (erule_tac [9] exE)
apply (erule_tac [9] exE)
apply (frule_tac [9] K4_imp_K2)
apply assumption+
apply (blast dest: Key_unique_SesKey intro!: Says_K6 dest: Confidentiality_Tgs
)
done




subsection{*Parties' knowledge of session keys. 
       An agent knows a session key if he used it to issue a cipher. These
       guarantees can be interpreted both in terms of key distribution
       and of non-injective agreement on the session key.*}

lemma Kas_Issues_A:
   "\<lbrakk> Says Kas A \<lbrace>Crypt (shrK A) \<lbrace>Key authK, Peer, Ta\<rbrace>, authTicket\<rbrace> \<in> set evs;
      evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> Kas Issues A with (Crypt (shrK A) \<lbrace>Key authK, Peer, Ta\<rbrace>)
          on evs"
apply (simp (no_asm) add: Issues_def)
apply (rule exI)
apply (rule conjI, assumption)
apply (simp (no_asm))
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (frule_tac [5] Says_ticket_parts)
apply (frule_tac [7] Says_ticket_parts)
apply (simp_all (no_asm_simp) add: all_conj_distrib)
txt{*K2*}
apply (simp add: takeWhile_tail)
apply (blast dest: authK_authentic parts_spies_takeWhile_mono [THEN subsetD] parts_spies_evs_revD2 [THEN subsetD])
done

lemma A_authenticates_and_keydist_to_Kas:
  "\<lbrakk> Crypt (shrK A) \<lbrace>Key authK, Peer, Ta\<rbrace> \<in> parts (spies evs);
     A \<notin> bad; evs \<in> kerbV \<rbrakk>
 \<Longrightarrow> Kas Issues A with (Crypt (shrK A) \<lbrace>Key authK, Peer, Ta\<rbrace>) 
          on evs"
by (blast dest!: authK_authentic Kas_Issues_A)

lemma Tgs_Issues_A:
    "\<lbrakk> Says Tgs A \<lbrace>Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>, servTicket\<rbrace>
         \<in> set evs; 
       Key authK \<notin> analz (spies evs);  evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> Tgs Issues A with 
          (Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>) on evs"
apply (simp (no_asm) add: Issues_def)
apply (rule exI)
apply (rule conjI, assumption)
apply (simp (no_asm))
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbV.induct, analz_mono_contra)
apply (frule_tac [5] Says_ticket_parts)
apply (frule_tac [7] Says_ticket_parts)
apply (simp_all (no_asm_simp) add: all_conj_distrib)
apply (simp add: takeWhile_tail)
(*Last two thms installed only to derive authK \<notin> range shrK*)
apply (blast dest: servK_authentic parts_spies_takeWhile_mono [THEN subsetD]
      parts_spies_evs_revD2 [THEN subsetD] authTicket_authentic 
      Says_Kas_message_form)
done

lemma A_authenticates_and_keydist_to_Tgs:
     "\<lbrakk> Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>
           \<in> parts (spies evs);
       Key authK \<notin> analz (spies evs); B \<noteq> Tgs; evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> \<exists>A. Tgs Issues A with 
          (Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>) on evs"
by (blast dest: Tgs_Issues_A servK_authentic_bis)

lemma B_Issues_A:
     "\<lbrakk> Says B A (Crypt servK (Number T3)) \<in> set evs;
         Key servK \<notin> analz (spies evs);
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> B Issues A with (Crypt servK (Number T3)) on evs"
apply (simp (no_asm) add: Issues_def)
apply (rule exI)
apply (rule conjI, assumption)
apply (simp (no_asm))
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbV.induct, analz_mono_contra)
apply (simp_all (no_asm_simp) add: all_conj_distrib)
apply blast
txt{*K6 requires numerous lemmas*}
apply (simp add: takeWhile_tail)
apply (blast intro: Says_K6 dest: servTicket_authentic 
        parts_spies_takeWhile_mono [THEN subsetD] 
        parts_spies_evs_revD2 [THEN subsetD])
done

lemma A_authenticates_and_keydist_to_B:
     "\<lbrakk> Crypt servK (Number T3) \<in> parts (spies evs);
         Crypt authK \<lbrace>Key servK, Agent B, Number Ts\<rbrace>
           \<in> parts (spies evs);
         Crypt (shrK A) \<lbrace>Key authK, Agent Tgs, Number Ta\<rbrace>
           \<in> parts (spies evs);
         Key authK \<notin> analz (spies evs); Key servK \<notin> analz (spies evs);
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerbV \<rbrakk>
      \<Longrightarrow> B Issues A with (Crypt servK (Number T3)) on evs"
by (blast dest!: A_authenticates_B B_Issues_A)


(*Must use \<le> rather than =, otherwise it cannot be proved inductively!*)
(*This is too strong for version V but would hold for version IV if only B 
  in K6 said a fresh timestamp.
lemma honest_never_says_newer_timestamp:
     "\<lbrakk> (CT evs) \<le> T ; Number T \<in> parts {X}; evs \<in> kerbV \<rbrakk> 
     \<Longrightarrow> \<forall> A B. A \<noteq> Spy \<longrightarrow> Says A B X \<notin> set evs"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (simp_all)
apply force
apply force
txt{*clarifying case K3*}
apply (rule impI)
apply (rule impI)
apply (frule Suc_leD)
apply (clarify)
txt{*cannot solve K3 or K5 because the spy might send CT evs as authTicket
or servTicket, which the honest agent would forward*}
prefer 2 apply force
prefer 4 apply force
prefer 4 apply force
txt{*cannot solve K6 unless B updates the timestamp - rather than bouncing T3*}
oops
*)


text{*But can prove a less general fact conerning only authenticators!*}
lemma honest_never_says_newer_timestamp_in_auth:
     "\<lbrakk> (CT evs) \<le> T; Number T \<in> parts {X}; A \<notin> bad; evs \<in> kerbV \<rbrakk> 
     \<Longrightarrow> Says A B \<lbrace>Y, X\<rbrace> \<notin> set evs"
apply (erule rev_mp)
apply (erule kerbV.induct)
apply (simp_all)
apply force+
done

lemma honest_never_says_current_timestamp_in_auth:
     "\<lbrakk> (CT evs) = T; Number T \<in> parts {X}; A \<notin> bad; evs \<in> kerbV \<rbrakk> 
     \<Longrightarrow> Says A B \<lbrace>Y, X\<rbrace> \<notin> set evs"
apply (frule eq_imp_le)
apply (blast dest: honest_never_says_newer_timestamp_in_auth)
done



lemma A_Issues_B:
     "\<lbrakk> Says A B \<lbrace>ST, Crypt servK \<lbrace>Agent A, Number T3\<rbrace>\<rbrace> \<in> set evs;
         Key servK \<notin> analz (spies evs);
         B \<noteq> Tgs; A \<notin> bad;  B \<notin> bad;  evs \<in> kerbV \<rbrakk>
   \<Longrightarrow> A Issues B with (Crypt servK \<lbrace>Agent A, Number T3\<rbrace>) on evs"
apply (simp (no_asm) add: Issues_def)
apply (rule exI)
apply (rule conjI, assumption)
apply (simp (no_asm))
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerbV.induct, analz_mono_contra)
apply (frule_tac [7] Says_ticket_parts)
apply (frule_tac [5] Says_ticket_parts)
apply (simp_all (no_asm_simp))
txt{*K5*}
apply auto
apply (simp add: takeWhile_tail)
txt{*Level 15: case study necessary because the assumption doesn't state
  the form of servTicket. The guarantee becomes stronger.*}
prefer 2 apply (simp add: takeWhile_tail)
(**This single command of version IV...
apply (blast dest: Says_imp_spies [THEN analz.Inj, THEN analz_Decrypt']
                   K3_imp_K2 K4_trustworthy'
                   parts_spies_takeWhile_mono [THEN subsetD]
                   parts_spies_evs_revD2 [THEN subsetD]
             intro: Says_Auth)
...expands as follows - including extra exE because of new form of lemmas*)
apply (frule K3_imp_K2, assumption, assumption, erule exE, erule exE)
apply (case_tac "Key authK \<in> analz (spies evs5)")
apply (drule Says_imp_knows_Spy [THEN analz.Inj, THEN analz.Fst, THEN analz_Decrypt', THEN analz.Fst], assumption, assumption, simp)
apply (frule K3_imp_K2, assumption, assumption, erule exE, erule exE)
apply (drule Says_imp_knows_Spy [THEN parts.Inj, THEN parts.Fst])
apply (frule servK_authentic_ter, blast, assumption+)
apply (drule parts_spies_takeWhile_mono [THEN subsetD])
apply (drule parts_spies_evs_revD2 [THEN subsetD])
txt{* @{term Says_K5} closes the proof in version IV because it is clear which 
servTicket an authenticator appears with in msg 5. In version V an authenticator can appear with any item that the spy could replace the servTicket with*}
apply (frule Says_K5, blast, assumption, assumption, assumption, assumption, erule exE)
txt{*We need to state that an honest agent wouldn't send the wrong timestamp
within an authenticator, wathever it is paired with*}
apply (simp add: honest_never_says_current_timestamp_in_auth)
done

lemma B_authenticates_and_keydist_to_A:
     "\<lbrakk> Crypt servK \<lbrace>Agent A, Number T3\<rbrace> \<in> parts (spies evs);
         Crypt (shrK B) \<lbrace>Agent A, Agent B, Key servK, Number Ts\<rbrace>
           \<in> parts (spies evs);
         Key servK \<notin> analz (spies evs);
         B \<noteq> Tgs; A \<notin> bad;  B \<notin> bad;  evs \<in> kerbV \<rbrakk>
   \<Longrightarrow> A Issues B with (Crypt servK \<lbrace>Agent A, Number T3\<rbrace>) on evs"
by (blast dest: B_authenticates_A A_Issues_B)



subsection{*
Novel guarantees, never studied before. Because honest agents always say
the right timestamp in authenticators, we can prove unicity guarantees based 
exactly on timestamps. Classical unicity guarantees are based on nonces.
Of course assuming the agent to be different from the Spy, rather than not in 
bad, would suffice below. Similar guarantees must also hold of
Kerberos IV.*}

text{*Notice that an honest agent can send the same timestamp on two
different traces of the same length, but not on the same trace!*}

lemma unique_timestamp_authenticator1:
     "\<lbrakk> Says A Kas \<lbrace>Agent A, Agent Tgs, Number T1\<rbrace> \<in> set evs;
         Says A Kas' \<lbrace>Agent A, Agent Tgs', Number T1\<rbrace> \<in> set evs;
         A \<notin>bad; evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> Kas=Kas' \<and> Tgs=Tgs'"
apply (erule rev_mp, erule rev_mp)
apply (erule kerbV.induct)
apply (simp_all, blast)
apply auto
apply (simp_all add: honest_never_says_current_timestamp_in_auth)
done

lemma unique_timestamp_authenticator2:
     "\<lbrakk> Says A Tgs \<lbrace>AT, Crypt AK \<lbrace>Agent A, Number T2\<rbrace>, Agent B\<rbrace> \<in> set evs;
     Says A Tgs' \<lbrace>AT', Crypt AK' \<lbrace>Agent A, Number T2\<rbrace>, Agent B'\<rbrace> \<in> set evs;
         A \<notin>bad; evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> Tgs=Tgs' \<and> AT=AT' \<and> AK=AK' \<and> B=B'"
apply (erule rev_mp, erule rev_mp)
apply (erule kerbV.induct)
apply (simp_all, blast)
apply auto
apply (simp_all add: honest_never_says_current_timestamp_in_auth)
done

lemma unique_timestamp_authenticator3:
     "\<lbrakk> Says A B \<lbrace>ST, Crypt SK \<lbrace>Agent A, Number T\<rbrace>\<rbrace> \<in> set evs;
         Says A B' \<lbrace>ST', Crypt SK' \<lbrace>Agent A, Number T\<rbrace>\<rbrace> \<in> set evs;
         A \<notin>bad; evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> B=B' \<and> ST=ST' \<and> SK=SK'"
apply (erule rev_mp, erule rev_mp)
apply (erule kerbV.induct)
apply (simp_all, blast)
apply (auto simp add: honest_never_says_current_timestamp_in_auth)
done

text{*The second part of the message is treated as an authenticator by the last
simplification step, even if it is not an authenticator!*}
lemma unique_timestamp_authticket:
     "\<lbrakk> Says Kas A \<lbrace>X, Crypt (shrK Tgs) \<lbrace>Agent A, Agent Tgs, Key AK, T\<rbrace>\<rbrace> \<in> set evs;
       Says Kas A' \<lbrace>X', Crypt (shrK Tgs') \<lbrace>Agent A', Agent Tgs', Key AK', T\<rbrace>\<rbrace> \<in> set evs;
         evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> A=A' \<and> X=X' \<and> Tgs=Tgs' \<and> AK=AK'"
apply (erule rev_mp, erule rev_mp)
apply (erule kerbV.induct)
apply (auto simp add: honest_never_says_current_timestamp_in_auth)
done

text{*The second part of the message is treated as an authenticator by the last
simplification step, even if it is not an authenticator!*}
lemma unique_timestamp_servticket:
     "\<lbrakk> Says Tgs A \<lbrace>X, Crypt (shrK B) \<lbrace>Agent A, Agent B, Key SK, T\<rbrace>\<rbrace> \<in> set evs;
       Says Tgs A' \<lbrace>X', Crypt (shrK B') \<lbrace>Agent A', Agent B', Key SK', T\<rbrace>\<rbrace> \<in> set evs;
         evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> A=A' \<and> X=X' \<and> B=B' \<and> SK=SK'"
apply (erule rev_mp, erule rev_mp)
apply (erule kerbV.induct)
apply (auto simp add: honest_never_says_current_timestamp_in_auth)
done

(*Uses assumption K6's assumption that B \<noteq> Kas, otherwise B should say
fresh timestamp*)
lemma Kas_never_says_newer_timestamp:
     "\<lbrakk> (CT evs) \<le> T; Number T \<in> parts {X}; evs \<in> kerbV \<rbrakk> 
     \<Longrightarrow> \<forall> A. Says Kas A X \<notin> set evs"
apply (erule rev_mp)
apply (erule kerbV.induct, auto)
done

lemma Kas_never_says_current_timestamp:
     "\<lbrakk> (CT evs) = T; Number T \<in> parts {X}; evs \<in> kerbV \<rbrakk> 
     \<Longrightarrow> \<forall> A. Says Kas A X \<notin> set evs"
apply (frule eq_imp_le)
apply (blast dest: Kas_never_says_newer_timestamp)
done

lemma unique_timestamp_msg2:
     "\<lbrakk> Says Kas A \<lbrace>Crypt (shrK A) \<lbrace>Key AK, Agent Tgs, T\<rbrace>, AT\<rbrace> \<in> set evs;
     Says Kas A' \<lbrace>Crypt (shrK A') \<lbrace>Key AK', Agent Tgs', T\<rbrace>, AT'\<rbrace> \<in> set evs;
         evs \<in> kerbV \<rbrakk>
  \<Longrightarrow> A=A' \<and> AK=AK' \<and> Tgs=Tgs' \<and> AT=AT'"
apply (erule rev_mp, erule rev_mp)
apply (erule kerbV.induct)
apply (auto simp add: Kas_never_says_current_timestamp)
done

(*Uses assumption K6's assumption that B \<noteq> Tgs, otherwise B should say
fresh timestamp*)
lemma Tgs_never_says_newer_timestamp:
     "\<lbrakk> (CT evs) \<le> T; Number T \<in> parts {X}; evs \<in> kerbV \<rbrakk> 
     \<Longrightarrow> \<forall> A. Says Tgs A X \<notin> set evs"
apply (erule rev_mp)
apply (erule kerbV.induct, auto)
done

lemma Tgs_never_says_current_timestamp:
     "\<lbrakk> (CT evs) = T; Number T \<in> parts {X}; evs \<in> kerbV \<rbrakk> 
     \<Longrightarrow> \<forall> A. Says Tgs A X \<notin> set evs"
apply (frule eq_imp_le)
apply (blast dest: Tgs_never_says_newer_timestamp)
done


lemma unique_timestamp_msg4:
     "\<lbrakk> Says Tgs A \<lbrace>Crypt (shrK A) \<lbrace>Key SK, Agent B, T\<rbrace>, ST\<rbrace> \<in> set evs;
       Says Tgs A' \<lbrace>Crypt (shrK A') \<lbrace>Key SK', Agent B', T\<rbrace>, ST'\<rbrace> \<in> set evs;
         evs \<in> kerbV \<rbrakk> 
  \<Longrightarrow> A=A' \<and> SK=SK' \<and> B=B' \<and> ST=ST'"
apply (erule rev_mp, erule rev_mp)
apply (erule kerbV.induct)
apply (auto simp add: Tgs_never_says_current_timestamp)
done
 
end
