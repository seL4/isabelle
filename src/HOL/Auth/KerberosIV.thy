(*  Title:      HOL/Auth/KerberosIV
    ID:         $Id$
    Author:     Giampaolo Bella, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

header{*The Kerberos Protocol, Version IV*}

theory KerberosIV = Public:

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

    ExpirAuth :: "[nat, event list] => bool"

    ExpirServ :: "[nat, event list] => bool"

    ExpirAutc :: "[nat, event list] => bool"

    RecentResp :: "[nat, nat] => bool"


constdefs
 (* AuthKeys are those contained in an AuthTicket *)
    AuthKeys :: "event list => key set"
    "AuthKeys evs == {AuthKey. \<exists>A Peer Tk. Says Kas A
                        (Crypt (shrK A) {|Key AuthKey, Agent Peer, Tk,
                   (Crypt (shrK Peer) {|Agent A, Agent Peer, Key AuthKey, Tk|})
                  |}) \<in> set evs}"

 (* A is the true creator of X if she has sent X and X never appeared on
    the trace before this event. Recall that traces grow from head. *)
  Issues :: "[agent, agent, msg, event list] => bool"
             ("_ Issues _ with _ on _")
   "A Issues B with X on evs ==
      \<exists>Y. Says A B Y \<in> set evs & X \<in> parts {Y} &
      X \<notin> parts (spies (takeWhile (% z. z  \<noteq> Says A B Y) (rev evs)))"


consts
    (*Duration of the authentication key*)
    AuthLife   :: nat

    (*Duration of the service key*)
    ServLife   :: nat

    (*Duration of an authenticator*)
    AutcLife   :: nat

    (*Upper bound on the time of reaction of a server*)
    RespLife   :: nat

specification (AuthLife)
  AuthLife_LB [iff]: "2 \<le> AuthLife"
    by blast

specification (ServLife)
  ServLife_LB [iff]: "2 \<le> ServLife"
    by blast

specification (AutcLife)
  AutcLife_LB [iff]: "Suc 0 \<le> AutcLife"
    by blast

specification (RespLife)
  RespLife_LB [iff]: "Suc 0 \<le> RespLife"
    by blast

translations
   "CT" == "length "

   "ExpirAuth T evs" == "AuthLife + T < CT evs"

   "ExpirServ T evs" == "ServLife + T < CT evs"

   "ExpirAutc T evs" == "AutcLife + T < CT evs"

   "RecentResp T1 T2" == "T1 <= RespLife + T2"

(*---------------------------------------------------------------------*)


(* Predicate formalising the association between AuthKeys and ServKeys *)
constdefs
  KeyCryptKey :: "[key, key, event list] => bool"
  "KeyCryptKey AuthKey ServKey evs ==
     \<exists>A B tt.
       Says Tgs A (Crypt AuthKey
                     {|Key ServKey, Agent B, tt,
                       Crypt (shrK B) {|Agent A, Agent B, Key ServKey, tt|} |})
         \<in> set evs"

consts

kerberos   :: "event list set"
inductive "kerberos"
  intros

   Nil:  "[] \<in> kerberos"

   Fake: "[| evsf \<in> kerberos;  X \<in> synth (analz (spies evsf)) |]
          ==> Says Spy B X  # evsf \<in> kerberos"

(* FROM the initiator *)
   K1:   "[| evs1 \<in> kerberos |]
          ==> Says A Kas {|Agent A, Agent Tgs, Number (CT evs1)|} # evs1
          \<in> kerberos"

(* Adding the timestamp serves to A in K3 to check that
   she doesn't get a reply too late. This kind of timeouts are ordinary.
   If a server's reply is late, then it is likely to be fake. *)

(*---------------------------------------------------------------------*)

(*FROM Kas *)
   K2:  "[| evs2 \<in> kerberos; Key AuthKey \<notin> used evs2; AuthKey \<in> symKeys;
            Says A' Kas {|Agent A, Agent Tgs, Number Ta|} \<in> set evs2 |]
          ==> Says Kas A
                (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number (CT evs2),
                      (Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey,
                          Number (CT evs2)|})|}) # evs2 \<in> kerberos"
(*
  The internal encryption builds the AuthTicket.
  The timestamp doesn't change inside the two encryptions: the external copy
  will be used by the initiator in K3; the one inside the
  AuthTicket by Tgs in K4.
*)

(*---------------------------------------------------------------------*)

(* FROM the initiator *)
   K3:  "[| evs3 \<in> kerberos;
            Says A Kas {|Agent A, Agent Tgs, Number Ta|} \<in> set evs3;
            Says Kas' A (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk,
              AuthTicket|}) \<in> set evs3;
            RecentResp Tk Ta
         |]
          ==> Says A Tgs {|AuthTicket,
                           (Crypt AuthKey {|Agent A, Number (CT evs3)|}),
                           Agent B|} # evs3 \<in> kerberos"
(*The two events amongst the premises allow A to accept only those AuthKeys
  that are not issued late. *)

(*---------------------------------------------------------------------*)

(* FROM Tgs *)
(* Note that the last temporal check is not mentioned in the original MIT
   specification. Adding it strengthens the guarantees assessed by the
   protocol. Theorems that exploit it have the suffix `_refined'
*)
   K4:  "[| evs4 \<in> kerberos; Key ServKey \<notin> used evs4; ServKey \<in> symKeys;
            B \<noteq> Tgs;  AuthKey \<in> symKeys;
            Says A' Tgs {|
             (Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey,
				 Number Tk|}),
             (Crypt AuthKey {|Agent A, Number Ta1|}), Agent B|}
	        \<in> set evs4;
            ~ ExpirAuth Tk evs4;
            ~ ExpirAutc Ta1 evs4;
            ServLife + (CT evs4) <= AuthLife + Tk
         |]
          ==> Says Tgs A
                (Crypt AuthKey {|Key ServKey, Agent B, Number (CT evs4),
			       Crypt (shrK B) {|Agent A, Agent B, Key ServKey,
		 			        Number (CT evs4)|} |})
	        # evs4 \<in> kerberos"
(* Tgs creates a new session key per each request for a service, without
   checking if there is still a fresh one for that service.
   The cipher under Tgs' key is the AuthTicket, the cipher under B's key
   is the ServTicket, which is built now.
   NOTE that the last temporal check is not present in the MIT specification.

*)

(*---------------------------------------------------------------------*)

(* FROM the initiator *)
   K5:  "[| evs5 \<in> kerberos; AuthKey \<in> symKeys; ServKey \<in> symKeys;
            Says A Tgs
                {|AuthTicket, Crypt AuthKey {|Agent A, Number Ta1|},
		  Agent B|}
              \<in> set evs5;
            Says Tgs' A
             (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|})
                \<in> set evs5;
            RecentResp Tt Ta1 |]
          ==> Says A B {|ServTicket,
			 Crypt ServKey {|Agent A, Number (CT evs5)|} |}
               # evs5 \<in> kerberos"
(* Checks similar to those in K3. *)

(*---------------------------------------------------------------------*)

(* FROM the responder*)
    K6:  "[| evs6 \<in> kerberos;
            Says A' B {|
              (Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}),
              (Crypt ServKey {|Agent A, Number Ta2|})|}
            \<in> set evs6;
            ~ ExpirServ Tt evs6;
            ~ ExpirAutc Ta2 evs6
         |]
          ==> Says B A (Crypt ServKey (Number Ta2))
               # evs6 \<in> kerberos"
(* Checks similar to those in K4. *)

(*---------------------------------------------------------------------*)

(* Leaking an AuthKey... *)
   Oops1: "[| evsO1 \<in> kerberos;  A \<noteq> Spy;
              Says Kas A
                (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk,
                                  AuthTicket|})  \<in> set evsO1;
              ExpirAuth Tk evsO1 |]
          ==> Says A Spy {|Agent A, Agent Tgs, Number Tk, Key AuthKey|}
               # evsO1 \<in> kerberos"

(*---------------------------------------------------------------------*)

(*Leaking a ServKey... *)
   Oops2: "[| evsO2 \<in> kerberos;  A \<noteq> Spy;
              Says Tgs A
                (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|})
                   \<in> set evsO2;
              ExpirServ Tt evsO2 |]
          ==> Says A Spy {|Agent A, Agent B, Number Tt, Key ServKey|}
               # evsO2 \<in> kerberos"

(*---------------------------------------------------------------------*)

declare Says_imp_knows_Spy [THEN parts.Inj, dest]
declare parts.Body [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un [dest]


subsection{*Lemmas about Lists*}

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


subsection{*Lemmas about @{term AuthKeys}*}

lemma AuthKeys_empty: "AuthKeys [] = {}"
apply (unfold AuthKeys_def)
apply (simp (no_asm))
done

lemma AuthKeys_not_insert:
 "(\<forall>A Tk akey Peer.
   ev \<noteq> Says Kas A (Crypt (shrK A) {|akey, Agent Peer, Tk,
              (Crypt (shrK Peer) {|Agent A, Agent Peer, akey, Tk|})|}))
       ==> AuthKeys (ev # evs) = AuthKeys evs"
by (unfold AuthKeys_def, auto)

lemma AuthKeys_insert:
  "AuthKeys
     (Says Kas A (Crypt (shrK A) {|Key K, Agent Peer, Number Tk,
      (Crypt (shrK Peer) {|Agent A, Agent Peer, Key K, Number Tk|})|}) # evs)
       = insert K (AuthKeys evs)"
by (unfold AuthKeys_def, auto)

lemma AuthKeys_simp:
   "K \<in> AuthKeys
    (Says Kas A (Crypt (shrK A) {|Key K', Agent Peer, Number Tk,
     (Crypt (shrK Peer) {|Agent A, Agent Peer, Key K', Number Tk|})|}) # evs)
        ==> K = K' | K \<in> AuthKeys evs"
by (unfold AuthKeys_def, auto)

lemma AuthKeysI:
   "Says Kas A (Crypt (shrK A) {|Key K, Agent Tgs, Number Tk,
     (Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key K, Number Tk|})|}) \<in> set evs
        ==> K \<in> AuthKeys evs"
by (unfold AuthKeys_def, auto)

lemma AuthKeys_used: "K \<in> AuthKeys evs ==> Key K \<in> used evs"
by (simp add: AuthKeys_def, blast)


subsection{*Forwarding Lemmas*}

text{*--For reasoning about the encrypted portion of message K3--*}
lemma K3_msg_in_parts_spies:
     "Says Kas' A (Crypt KeyA {|AuthKey, Peer, Tk, AuthTicket|})
               \<in> set evs ==> AuthTicket \<in> parts (spies evs)"
by blast

lemma Oops_range_spies1:
     "[| Says Kas A (Crypt KeyA {|Key AuthKey, Peer, Tk, AuthTicket|})
           \<in> set evs ;
         evs \<in> kerberos |] ==> AuthKey \<notin> range shrK & AuthKey \<in> symKeys"
apply (erule rev_mp)
apply (erule kerberos.induct, auto)
done

text{*--For reasoning about the encrypted portion of message K5--*}
lemma K5_msg_in_parts_spies:
     "Says Tgs' A (Crypt AuthKey {|ServKey, Agent B, Tt, ServTicket|})
               \<in> set evs ==> ServTicket \<in> parts (spies evs)"
by blast

lemma Oops_range_spies2:
     "[| Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|})
           \<in> set evs ;
         evs \<in> kerberos |] ==> ServKey \<notin> range shrK & ServKey \<in> symKeys"
apply (erule rev_mp)
apply (erule kerberos.induct, auto)
done

lemma Says_ticket_in_parts_spies:
     "Says S A (Crypt K {|SesKey, B, TimeStamp, Ticket|}) \<in> set evs
      ==> Ticket \<in> parts (spies evs)"
by blast


(*Spy never sees another agent's shared key! (unless it's lost at start)*)
lemma Spy_see_shrK [simp]:
     "evs \<in> kerberos ==> (Key (shrK A) \<in> parts (spies evs)) = (A \<in> bad)"
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all)
apply (blast+)
done

lemma Spy_analz_shrK [simp]:
     "evs \<in> kerberos ==> (Key (shrK A) \<in> analz (spies evs)) = (A \<in> bad)"
by auto

lemma Spy_see_shrK_D [dest!]:
     "[| Key (shrK A) \<in> parts (spies evs);  evs \<in> kerberos |] ==> A:bad"
by (blast dest: Spy_see_shrK)
lemmas Spy_analz_shrK_D = analz_subset_parts [THEN subsetD, THEN Spy_see_shrK_D, dest!]

text{*Nobody can have used non-existent keys!*}
lemma new_keys_not_used [simp]:
    "[|Key K \<notin> used evs; K \<in> symKeys; evs \<in> kerberos|]
     ==> K \<notin> keysFor (parts (spies evs))"
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all)
txt{*Fake*}
apply (force dest!: keysFor_parts_insert)
txt{*Others*}
apply (force dest!: analz_shrK_Decrypt)+
done

(*Earlier, all protocol proofs declared this theorem.
  But few of them actually need it! (Another is Yahalom) *)
lemma new_keys_not_analzd:
 "[|evs \<in> kerberos; K \<in> symKeys; Key K \<notin> used evs|]
  ==> K \<notin> keysFor (analz (spies evs))"
by (blast dest: new_keys_not_used intro: keysFor_mono [THEN subsetD])


subsection{*Regularity Lemmas*}
text{*These concern the form of items passed in messages*}

text{*Describes the form of AuthKey, AuthTicket, and K sent by Kas*}
lemma Says_Kas_message_form:
     "[| Says Kas A (Crypt K {|Key AuthKey, Agent Peer, Tk, AuthTicket|})
           \<in> set evs;
         evs \<in> kerberos |]
      ==> AuthKey \<notin> range shrK & AuthKey \<in> AuthKeys evs & AuthKey \<in> symKeys & 
  AuthTicket = (Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Tk|}) &
             K = shrK A  & Peer = Tgs"
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (simp_all (no_asm) add: AuthKeys_def AuthKeys_insert)
apply (blast+)
done

(*This lemma is essential for proving Says_Tgs_message_form:

  the session key AuthKey
  supplied by Kas in the authentication ticket
  cannot be a long-term key!

  Generalised to any session keys (both AuthKey and ServKey).
*)
lemma SesKey_is_session_key:
     "[| Crypt (shrK Tgs_B) {|Agent A, Agent Tgs_B, Key SesKey, Number T|}
            \<in> parts (spies evs); Tgs_B \<notin> bad;
         evs \<in> kerberos |]
      ==> SesKey \<notin> range shrK"
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all, blast)
done

lemma A_trusts_AuthTicket:
     "[| Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Tk|}
           \<in> parts (spies evs);
         evs \<in> kerberos |]
      ==> Says Kas A (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Tk,
                 Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Tk|}|})
            \<in> set evs"
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all)
txt{*Fake, K4*}
apply (blast+)
done

lemma AuthTicket_crypt_AuthKey:
     "[| Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}
           \<in> parts (spies evs);
         evs \<in> kerberos |]
      ==> AuthKey \<in> AuthKeys evs"
apply (frule A_trusts_AuthTicket, assumption)
apply (simp (no_asm) add: AuthKeys_def)
apply blast
done

text{*Describes the form of ServKey, ServTicket and AuthKey sent by Tgs*}
lemma Says_Tgs_message_form:
     "[| Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|})
           \<in> set evs;
         evs \<in> kerberos |]
   ==> B \<noteq> Tgs & 
       ServKey \<notin> range shrK & ServKey \<notin> AuthKeys evs & ServKey \<in> symKeys &
       ServTicket = (Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Tt|}) &
       AuthKey \<notin> range shrK & AuthKey \<in> AuthKeys evs & AuthKey \<in> symKeys"
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (simp_all add: AuthKeys_insert AuthKeys_not_insert AuthKeys_empty AuthKeys_simp, blast, auto)
txt{*Three subcases of Message 4*}
apply (blast dest!: AuthKeys_used Says_Kas_message_form)
apply (blast dest!: SesKey_is_session_key)
apply (blast dest: AuthTicket_crypt_AuthKey)
done

text{*Authenticity of AuthKey for A:
     If a certain encrypted message appears then it originated with Kas*}
lemma A_trusts_AuthKey:
     "[| Crypt (shrK A) {|Key AuthKey, Peer, Tk, AuthTicket|}
           \<in> parts (spies evs);
         A \<notin> bad;  evs \<in> kerberos |]
      ==> Says Kas A (Crypt (shrK A) {|Key AuthKey, Peer, Tk, AuthTicket|})
            \<in> set evs"
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all)
txt{*Fake*}
apply blast
txt{*K4*}
apply (blast dest!: A_trusts_AuthTicket [THEN Says_Kas_message_form])
done


text{*If a certain encrypted message appears then it originated with Tgs*}
lemma A_trusts_K4:
     "[| Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|}
           \<in> parts (spies evs);
         Key AuthKey \<notin> analz (spies evs);
         AuthKey \<notin> range shrK;
         evs \<in> kerberos |]
 ==> \<exists>A. Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|})
       \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct, analz_mono_contra)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all)
txt{*Fake*}
apply blast
txt{*K2*}
apply blast
txt{*K4*}
apply auto
done

lemma AuthTicket_form:
     "[| Crypt (shrK A) {|Key AuthKey, Agent Tgs, Tk, AuthTicket|}
           \<in> parts (spies evs);
         A \<notin> bad;
         evs \<in> kerberos |]
    ==> AuthKey \<notin> range shrK & AuthKey \<in> symKeys & 
        AuthTicket = Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Tk|}"
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all)
apply (blast+)
done

text{* This form holds also over an AuthTicket, but is not needed below.*}
lemma ServTicket_form:
     "[| Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|}
              \<in> parts (spies evs);
            Key AuthKey \<notin> analz (spies evs);
            evs \<in> kerberos |]
         ==> ServKey \<notin> range shrK & ServKey \<in> symKeys & 
    (\<exists>A. ServTicket = Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Tt|})"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct, analz_mono_contra)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all, blast)
done

text{* Essentially the same as @{text AuthTicket_form} *}
lemma Says_kas_message_form:
     "[| Says Kas' A (Crypt (shrK A)
              {|Key AuthKey, Agent Tgs, Tk, AuthTicket|}) \<in> set evs;
         evs \<in> kerberos |]
      ==> AuthKey \<notin> range shrK & AuthKey \<in> symKeys & 
          AuthTicket =
                  Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Tk|}
          | AuthTicket \<in> analz (spies evs)"
by (blast dest: analz_shrK_Decrypt AuthTicket_form
                Says_imp_spies [THEN analz.Inj])


lemma Says_tgs_message_form:
 "[| Says Tgs' A (Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|})
       \<in> set evs;  AuthKey \<in> symKeys;
     evs \<in> kerberos |]
  ==> ServKey \<notin> range shrK &
      (\<exists>A. ServTicket =
	      Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Tt|})
       | ServTicket \<in> analz (spies evs)"
apply (frule Says_imp_spies [THEN analz.Inj], auto)
 apply (force dest!: ServTicket_form)
apply (frule analz_into_parts)
apply (frule ServTicket_form, auto)
done

subsection{*Unicity Theorems*}

text{* The session key, if secure, uniquely identifies the Ticket
   whether AuthTicket or ServTicket. As a matter of fact, one can read
   also Tgs in the place of B.                                     *}

lemma unique_CryptKey:
     "[| Crypt (shrK B)  {|Agent A,  Agent B,  Key SesKey, T|}
           \<in> parts (spies evs);
         Crypt (shrK B') {|Agent A', Agent B', Key SesKey, T'|}
           \<in> parts (spies evs);  Key SesKey \<notin> analz (spies evs);
         evs \<in> kerberos |]
      ==> A=A' & B=B' & T=T'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct, analz_mono_contra)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all)
txt{*Fake, K2, K4*}
apply (blast+)
done

text{*An AuthKey is encrypted by one and only one Shared key.
  A ServKey is encrypted by one and only one AuthKey.
*}
lemma Key_unique_SesKey:
     "[| Crypt K  {|Key SesKey,  Agent B, T, Ticket|}
           \<in> parts (spies evs);
         Crypt K' {|Key SesKey,  Agent B', T', Ticket'|}
           \<in> parts (spies evs);  Key SesKey \<notin> analz (spies evs);
         evs \<in> kerberos |]
      ==> K=K' & B=B' & T=T' & Ticket=Ticket'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct, analz_mono_contra)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all)
txt{*Fake, K2, K4*}
apply (blast+)
done


(*
  At reception of any message mentioning A, Kas associates shrK A with
  a new AuthKey. Realistic, as the user gets a new AuthKey at each login.
  Similarly, at reception of any message mentioning an AuthKey
  (a legitimate user could make several requests to Tgs - by K3), Tgs
  associates it with a new ServKey.

  Therefore, a goal like

   "evs \<in> kerberos
     ==> Key Kc \<notin> analz (spies evs) -->
           (\<exists>K' B' T' Ticket'. \<forall>K B T Ticket.
            Crypt Kc {|Key K, Agent B, T, Ticket|}
             \<in> parts (spies evs) --> K=K' & B=B' & T=T' & Ticket=Ticket')"

  would fail on the K2 and K4 cases.
*)

lemma unique_AuthKeys:
     "[| Says Kas A
              (Crypt Ka {|Key AuthKey, Agent Tgs, Tk, X|}) \<in> set evs;
         Says Kas A'
              (Crypt Ka' {|Key AuthKey, Agent Tgs, Tk', X'|}) \<in> set evs;
         evs \<in> kerberos |] ==> A=A' & Ka=Ka' & Tk=Tk' & X=X'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all)
txt{*K2*}
apply blast
done

text{* ServKey uniquely identifies the message from Tgs *}
lemma unique_ServKeys:
     "[| Says Tgs A
              (Crypt K {|Key ServKey, Agent B, Tt, X|}) \<in> set evs;
         Says Tgs A'
              (Crypt K' {|Key ServKey, Agent B', Tt', X'|}) \<in> set evs;
         evs \<in> kerberos |] ==> A=A' & B=B' & K=K' & Tt=Tt' & X=X'"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all)
txt{*K4*}
apply blast
done


subsection{*Lemmas About the Predicate @{term KeyCryptKey}*}

lemma not_KeyCryptKey_Nil [iff]: "~ KeyCryptKey AuthKey ServKey []"
by (simp add: KeyCryptKey_def)

lemma KeyCryptKeyI:
 "[| Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, tt, X |}) \<in> set evs;
     evs \<in> kerberos |] ==> KeyCryptKey AuthKey ServKey evs"
apply (unfold KeyCryptKey_def)
apply (blast dest: Says_Tgs_message_form)
done

lemma KeyCryptKey_Says [simp]:
   "KeyCryptKey AuthKey ServKey (Says S A X # evs) =
     (Tgs = S &
      (\<exists>B tt. X = Crypt AuthKey
                {|Key ServKey, Agent B, tt,
                  Crypt (shrK B) {|Agent A, Agent B, Key ServKey, tt|} |})
     | KeyCryptKey AuthKey ServKey evs)"
apply (unfold KeyCryptKey_def)
apply (simp (no_asm))
apply blast
done

(*A fresh AuthKey cannot be associated with any other
  (with respect to a given trace). *)
lemma Auth_fresh_not_KeyCryptKey:
     "[| Key AuthKey \<notin> used evs; evs \<in> kerberos |]
      ==> ~ KeyCryptKey AuthKey ServKey evs"
apply (unfold KeyCryptKey_def)
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all, blast)
done

(*A fresh ServKey cannot be associated with any other
  (with respect to a given trace). *)
lemma Serv_fresh_not_KeyCryptKey:
 "Key ServKey \<notin> used evs ==> ~ KeyCryptKey AuthKey ServKey evs"
apply (unfold KeyCryptKey_def, blast)
done

lemma AuthKey_not_KeyCryptKey:
     "[| Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, tk|}
           \<in> parts (spies evs);  evs \<in> kerberos |]
      ==> ~ KeyCryptKey K AuthKey evs"
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all)
txt{*Fake*}
apply blast
txt{*K2: by freshness*}
apply (simp add: KeyCryptKey_def)
txt{*K4*}
apply (blast+)
done

text{*A secure serverkey cannot have been used to encrypt others*}
lemma ServKey_not_KeyCryptKey:
 "[| Crypt (shrK B) {|Agent A, Agent B, Key SK, tt|} \<in> parts (spies evs);
     Key SK \<notin> analz (spies evs);  SK \<in> symKeys;
     B \<noteq> Tgs;  evs \<in> kerberos |]
  ==> ~ KeyCryptKey SK K evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct, analz_mono_contra)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all, blast)
txt{*K4 splits into distinct subcases*}
apply auto
txt{*ServKey can't have been enclosed in two certificates*}
 prefer 2 apply (blast dest: unique_CryptKey)
txt{*ServKey is fresh and so could not have been used, by
   @{text new_keys_not_used}*}
apply (force dest!: Crypt_imp_invKey_keysFor simp add: KeyCryptKey_def)
done

text{*Long term keys are not issued as ServKeys*}
lemma shrK_not_KeyCryptKey:
     "evs \<in> kerberos ==> ~ KeyCryptKey K (shrK A) evs"
apply (unfold KeyCryptKey_def)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, auto)
done

text{*The Tgs message associates ServKey with AuthKey and therefore not with any
  other key AuthKey.*}
lemma Says_Tgs_KeyCryptKey:
     "[| Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, tt, X |})
           \<in> set evs;
         AuthKey' \<noteq> AuthKey;  evs \<in> kerberos |]
      ==> ~ KeyCryptKey AuthKey' ServKey evs"
apply (unfold KeyCryptKey_def)
apply (blast dest: unique_ServKeys)
done

lemma KeyCryptKey_not_KeyCryptKey:
     "[| KeyCryptKey AuthKey ServKey evs;  evs \<in> kerberos |]
      ==> ~ KeyCryptKey ServKey K evs"
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all, safe)
txt{*K4 splits into subcases*}
apply simp_all
prefer 4 apply (blast dest!: AuthKey_not_KeyCryptKey)
txt{*ServKey is fresh and so could not have been used, by
   @{text new_keys_not_used}*}
 prefer 2 
 apply (force dest!: Crypt_imp_invKey_keysFor simp add: KeyCryptKey_def)
txt{*Others by freshness*}
apply (blast+)
done

text{*The only session keys that can be found with the help of session keys are
  those sent by Tgs in step K4.  *}

text{*We take some pains to express the property
  as a logical equivalence so that the simplifier can apply it.*}
lemma Key_analz_image_Key_lemma:
     "P --> (Key K \<in> analz (Key`KK Un H)) --> (K:KK | Key K \<in> analz H)
      ==>
      P --> (Key K \<in> analz (Key`KK Un H)) = (K:KK | Key K \<in> analz H)"
by (blast intro: analz_mono [THEN subsetD])


lemma KeyCryptKey_analz_insert:
     "[| KeyCryptKey K K' evs; K \<in> symKeys; evs \<in> kerberos |]
      ==> Key K' \<in> analz (insert (Key K) (spies evs))"
apply (simp add: KeyCryptKey_def, clarify)
apply (drule Says_imp_spies [THEN analz.Inj, THEN analz_insertI], auto)
done

lemma AuthKeys_are_not_KeyCryptKey:
     "[| K \<in> AuthKeys evs Un range shrK;  evs \<in> kerberos |]
      ==> \<forall>SK. ~ KeyCryptKey SK K evs"
apply (simp add: KeyCryptKey_def)
apply (blast dest: Says_Tgs_message_form)
done

lemma not_AuthKeys_not_KeyCryptKey:
     "[| K \<notin> AuthKeys evs;
         K \<notin> range shrK; evs \<in> kerberos |]
      ==> \<forall>SK. ~ KeyCryptKey K SK evs"
apply (simp add: KeyCryptKey_def)
apply (blast dest: Says_Tgs_message_form)
done


subsection{*Secrecy Theorems*}

text{*For the Oops2 case of the next theorem*}
lemma Oops2_not_KeyCryptKey:
     "[| evs \<in> kerberos;
         Says Tgs A (Crypt AuthKey
                     {|Key ServKey, Agent B, Number Tt, ServTicket|})
           \<in> set evs |]
      ==> ~ KeyCryptKey ServKey SK evs"
apply (blast dest: KeyCryptKeyI KeyCryptKey_not_KeyCryptKey)
done


text{* Big simplification law for keys SK that are not crypted by keys in KK
 It helps prove three, otherwise hard, facts about keys. These facts are
 exploited as simplification laws for analz, and also "limit the damage"
 in case of loss of a key to the spy. See ESORICS98.
 [simplified by LCP] *}
lemma Key_analz_image_Key [rule_format (no_asm)]:
     "evs \<in> kerberos ==>
      (\<forall>SK KK. SK \<in> symKeys & KK <= -(range shrK) -->
       (\<forall>K \<in> KK. ~ KeyCryptKey K SK evs)   -->
       (Key SK \<in> analz (Key`KK Un (spies evs))) =
       (SK \<in> KK | Key SK \<in> analz (spies evs)))"
apply (erule kerberos.induct)
apply (frule_tac [10] Oops_range_spies2)
apply (frule_tac [9] Oops_range_spies1)
apply (frule_tac [7] Says_tgs_message_form)
apply (frule_tac [5] Says_kas_message_form)
apply (safe del: impI intro!: Key_analz_image_Key_lemma [THEN impI])
txt{*Case-splits for Oops1 and message 5: the negated case simplifies using
 the induction hypothesis*}
apply (case_tac [11] "KeyCryptKey AuthKey SK evsO1")
apply (case_tac [8] "KeyCryptKey ServKey SK evs5")
apply (simp_all del: image_insert
          add: analz_image_freshK_simps KeyCryptKey_Says)
txt{*Fake*} 
apply spy_analz
apply (simp_all del: image_insert
          add: shrK_not_KeyCryptKey
               Oops2_not_KeyCryptKey Auth_fresh_not_KeyCryptKey
               Serv_fresh_not_KeyCryptKey Says_Tgs_KeyCryptKey Spy_analz_shrK)
  --{*Splitting the @{text simp_all} into two parts makes it faster.*}
txt{*K2*}
apply blast 
txt{*K3*}
apply blast 
txt{*K4*}
apply (blast dest!: AuthKey_not_KeyCryptKey)
txt{*K5*}
apply (case_tac "Key ServKey \<in> analz (spies evs5) ")
txt{*If ServKey is compromised then the result follows directly...*}
apply (simp (no_asm_simp) add: analz_insert_eq Un_upper2 [THEN analz_mono, THEN subsetD])
txt{*...therefore ServKey is uncompromised.*}
txt{*The KeyCryptKey ServKey SK evs5 case leads to a contradiction.*}
apply (blast elim!: ServKey_not_KeyCryptKey [THEN [2] rev_notE] del: allE ballE)
txt{*Another K5 case*}
apply blast 
txt{*Oops1*}
apply simp 
apply (blast dest!: KeyCryptKey_analz_insert)
done

text{* First simplification law for analz: no session keys encrypt
authentication keys or shared keys. *}
lemma analz_insert_freshK1:
     "[| evs \<in> kerberos;  K \<in> (AuthKeys evs) Un range shrK;
         K \<in> symKeys;
         SesKey \<notin> range shrK |]
      ==> (Key K \<in> analz (insert (Key SesKey) (spies evs))) =
          (K = SesKey | Key K \<in> analz (spies evs))"
apply (frule AuthKeys_are_not_KeyCryptKey, assumption)
apply (simp del: image_insert
            add: analz_image_freshK_simps add: Key_analz_image_Key)
done


text{* Second simplification law for analz: no service keys encrypt any other keys.*}
lemma analz_insert_freshK2:
     "[| evs \<in> kerberos;  ServKey \<notin> (AuthKeys evs); ServKey \<notin> range shrK;
         K \<in> symKeys|]
      ==> (Key K \<in> analz (insert (Key ServKey) (spies evs))) =
          (K = ServKey | Key K \<in> analz (spies evs))"
apply (frule not_AuthKeys_not_KeyCryptKey, assumption, assumption)
apply (simp del: image_insert
            add: analz_image_freshK_simps add: Key_analz_image_Key)
done


text{* Third simplification law for analz: only one authentication key encrypts a
certain service key.*}
lemma analz_insert_freshK3:
 "[| Says Tgs A
            (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|})
        \<in> set evs;  ServKey \<in> symKeys;
     AuthKey \<noteq> AuthKey'; AuthKey' \<notin> range shrK; evs \<in> kerberos |]
        ==> (Key ServKey \<in> analz (insert (Key AuthKey') (spies evs))) =
                (ServKey = AuthKey' | Key ServKey \<in> analz (spies evs))"
apply (drule_tac AuthKey' = AuthKey' in Says_Tgs_KeyCryptKey, blast, assumption)
apply (simp del: image_insert
            add: analz_image_freshK_simps add: Key_analz_image_Key)
done


text{*a weakness of the protocol*}
lemma AuthKey_compromises_ServKey:
     "[| Says Tgs A
              (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|})
           \<in> set evs;  AuthKey \<in> symKeys;
         Key AuthKey \<in> analz (spies evs); evs \<in> kerberos |]
      ==> Key ServKey \<in> analz (spies evs)"
by (force dest: Says_imp_spies [THEN analz.Inj, THEN analz.Decrypt, THEN analz.Fst])


subsection{* Guarantees for Kas *}
lemma ServKey_notin_AuthKeysD:
     "[| Crypt AuthKey {|Key ServKey, Agent B, Tt,
                      Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Tt|}|}
           \<in> parts (spies evs);
         Key ServKey \<notin> analz (spies evs);
         B \<noteq> Tgs; evs \<in> kerberos |]
      ==> ServKey \<notin> AuthKeys evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (simp add: AuthKeys_def)
apply (erule kerberos.induct, analz_mono_contra)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all)
apply (blast+)
done


text{*If Spy sees the Authentication Key sent in msg K2, then
    the Key has expired.*}
lemma Confidentiality_Kas_lemma [rule_format]:
     "[| AuthKey \<in> symKeys; A \<notin> bad;  evs \<in> kerberos |]
      ==> Says Kas A
               (Crypt (shrK A)
                  {|Key AuthKey, Agent Tgs, Number Tk,
          Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}|})
            \<in> set evs -->
          Key AuthKey \<in> analz (spies evs) -->
          ExpirAuth Tk evs"
apply (erule kerberos.induct)
apply (frule_tac [10] Oops_range_spies2)
apply (frule_tac [9] Oops_range_spies1)
apply (frule_tac [7] Says_tgs_message_form)
apply (frule_tac [5] Says_kas_message_form)
apply (safe del: impI conjI impCE)
apply (simp_all (no_asm_simp) add: Says_Kas_message_form less_SucI analz_insert_eq not_parts_not_analz analz_insert_freshK1 pushes)
txt{*Fake*}
apply spy_analz
txt{*K2*}
apply blast
txt{*K4*}
apply blast
txt{*Level 8: K5*}
apply (blast dest: ServKey_notin_AuthKeysD Says_Kas_message_form intro: less_SucI)
txt{*Oops1*}
apply (blast dest!: unique_AuthKeys intro: less_SucI)
txt{*Oops2*}
apply (blast dest: Says_Tgs_message_form Says_Kas_message_form)
done

lemma Confidentiality_Kas:
     "[| Says Kas A
              (Crypt Ka {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|})
           \<in> set evs;
         ~ ExpirAuth Tk evs;
         A \<notin> bad;  evs \<in> kerberos |]
      ==> Key AuthKey \<notin> analz (spies evs)"
by (blast dest: Says_Kas_message_form Confidentiality_Kas_lemma)


subsection{* Guarantees for Tgs *}

text{*If Spy sees the Service Key sent in msg K4, then
    the Key has expired.*}

lemma Confidentiality_lemma [rule_format]:
     "[| Says Tgs A
	    (Crypt AuthKey
	       {|Key ServKey, Agent B, Number Tt,
		 Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}|})
	   \<in> set evs;
	Key AuthKey \<notin> analz (spies evs);
        ServKey \<in> symKeys;
	A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerberos |]
      ==> Key ServKey \<in> analz (spies evs) -->
	  ExpirServ Tt evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (rule_tac [9] impI)+;
  --{*The Oops1 case is unusual: must simplify
    @{term "Authkey \<notin> analz (spies (ev#evs))"}, not letting
   @{text analz_mono_contra} weaken it to
   @{term "Authkey \<notin> analz (spies evs)"},
  for we then conclude @{term "AuthKey \<noteq> AuthKeya"}.*}
apply analz_mono_contra
apply (frule_tac [10] Oops_range_spies2)
apply (frule_tac [9] Oops_range_spies1)
apply (frule_tac [7] Says_tgs_message_form)
apply (frule_tac [5] Says_kas_message_form)
apply (safe del: impI conjI impCE)
apply (simp_all add: less_SucI new_keys_not_analzd Says_Kas_message_form Says_Tgs_message_form analz_insert_eq not_parts_not_analz analz_insert_freshK1 analz_insert_freshK2 analz_insert_freshK3 pushes)
txt{*Fake*}
apply spy_analz
txt{*K2*}
apply (blast intro: parts_insertI less_SucI)
txt{*K4*}
apply (blast dest: A_trusts_AuthTicket Confidentiality_Kas)
txt{*Oops2*}
  prefer 3
  apply (blast dest: Says_imp_spies [THEN parts.Inj] Key_unique_SesKey intro: less_SucI)
txt{*Oops1*}
 prefer 2
 apply (blast dest: Says_Kas_message_form Says_Tgs_message_form intro: less_SucI)
txt{*K5.  Not clear how this step could be integrated with the main
       simplification step.*}
apply clarify
apply (erule_tac V = "Says Aa Tgs ?X \<in> set ?evs" in thin_rl)
apply (frule Says_imp_spies [THEN parts.Inj, THEN ServKey_notin_AuthKeysD])
apply (assumption, blast, assumption)
apply (simp add: analz_insert_freshK2)
apply (blast dest: Says_imp_spies [THEN parts.Inj] Key_unique_SesKey intro: less_SucI)
done


text{* In the real world Tgs can't check wheter AuthKey is secure! *}
lemma Confidentiality_Tgs1:
     "[| Says Tgs A
              (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|})
           \<in> set evs;
         Key AuthKey \<notin> analz (spies evs);
         ~ ExpirServ Tt evs;
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerberos |]
      ==> Key ServKey \<notin> analz (spies evs)"
apply (blast dest: Says_Tgs_message_form Confidentiality_lemma)
done

text{* In the real world Tgs CAN check what Kas sends! *}
lemma Confidentiality_Tgs2:
     "[| Says Kas A
               (Crypt Ka {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|})
           \<in> set evs;
         Says Tgs A
              (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|})
           \<in> set evs;
         ~ ExpirAuth Tk evs; ~ ExpirServ Tt evs;
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerberos |]
      ==> Key ServKey \<notin> analz (spies evs)"
apply (blast dest!: Confidentiality_Kas Confidentiality_Tgs1)
done

text{*Most general form*}
lemmas Confidentiality_Tgs3 = A_trusts_AuthTicket [THEN Confidentiality_Tgs2]


subsection{* Guarantees for Alice *}

lemmas Confidentiality_Auth_A = A_trusts_AuthKey [THEN Confidentiality_Kas]

lemma A_trusts_K4_bis:
 "[| Says Kas A
       (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Tk, AuthTicket|}) \<in> set evs;
     Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|}
       \<in> parts (spies evs);
     Key AuthKey \<notin> analz (spies evs);
     evs \<in> kerberos |]
 ==> Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|})
       \<in> set evs"
apply (frule Says_Kas_message_form, assumption)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct, analz_mono_contra)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all, blast)
txt{*K2 and K4 remain*}
prefer 2 apply (blast dest!: unique_CryptKey)
apply (blast dest!: A_trusts_K4 Says_Tgs_message_form AuthKeys_used)
done


lemma Confidentiality_Serv_A:
     "[| Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}
           \<in> parts (spies evs);
         Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}
           \<in> parts (spies evs);
         ~ ExpirAuth Tk evs; ~ ExpirServ Tt evs;
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerberos |]
      ==> Key ServKey \<notin> analz (spies evs)"
apply (drule A_trusts_AuthKey, assumption, assumption)
apply (blast dest: Confidentiality_Kas Says_Kas_message_form A_trusts_K4_bis Confidentiality_Tgs2)
done


subsection{* Guarantees for Bob *}
text{* Theorems for the refined model have suffix "refined"                *}

lemma K4_imp_K2:
"[| Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|})
      \<in> set evs;  evs \<in> kerberos|]
   ==> \<exists>Tk. Says Kas A
        (Crypt (shrK A)
         {|Key AuthKey, Agent Tgs, Number Tk,
           Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}|})
        \<in> set evs"
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all, auto)
apply (blast dest!: Says_imp_spies [THEN parts.Inj, THEN parts.Fst, THEN A_trusts_AuthTicket])
done

lemma K4_imp_K2_refined:
"[| Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|})
      \<in> set evs; evs \<in> kerberos|]
   ==> \<exists>Tk. (Says Kas A (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk,
           Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}|})
             \<in> set evs
          & ServLife + Tt <= AuthLife + Tk)"
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all, auto)
apply (blast dest!: Says_imp_spies [THEN parts.Inj, THEN parts.Fst, THEN A_trusts_AuthTicket])
done

text{*Authenticity of ServKey for B*}
lemma B_trusts_ServKey:
     "[| Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Tt|}
           \<in> parts (spies evs);  B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerberos |]
 ==> \<exists>AuthKey.
       Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Tt,
                   Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Tt|}|})
       \<in> set evs"
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all)
apply (blast+)
done

lemma B_trusts_ServTicket_Kas:
     "[| Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}
           \<in> parts (spies evs);  B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerberos |]
  ==> \<exists>AuthKey Tk.
       Says Kas A
         (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk,
            Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}|})
        \<in> set evs"
by (blast dest!: B_trusts_ServKey K4_imp_K2)

lemma B_trusts_ServTicket_Kas_refined:
     "[| Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}
           \<in> parts (spies evs);  B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerberos |]
  ==> \<exists>AuthKey Tk. Says Kas A (Crypt(shrK A) {|Key AuthKey, Agent Tgs, Number Tk,
           Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}|})
             \<in> set evs
           & ServLife + Tt <= AuthLife + Tk"
by (blast dest!: B_trusts_ServKey K4_imp_K2_refined)

lemma B_trusts_ServTicket:
     "[| Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}
           \<in> parts (spies evs);  B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerberos |]
 ==> \<exists>Tk AuthKey.
     Says Kas A (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk,
                   Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}|})
       \<in> set evs
     & Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Number Tt,
                   Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}|})
       \<in> set evs"
by (blast dest: B_trusts_ServKey K4_imp_K2)

lemma B_trusts_ServTicket_refined:
     "[| Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}
           \<in> parts (spies evs);  B \<noteq> Tgs;  B \<notin> bad;
         evs \<in> kerberos |]
 ==> \<exists>Tk AuthKey.
     (Says Kas A (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk,
                   Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}|})
       \<in> set evs
     & Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Number Tt,
                   Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}|})
       \<in> set evs
     & ServLife + Tt <= AuthLife + Tk)"
by (blast dest: B_trusts_ServKey K4_imp_K2_refined)


lemma NotExpirServ_NotExpirAuth_refined:
     "[| ~ ExpirServ Tt evs; ServLife + Tt <= AuthLife + Tk |]
      ==> ~ ExpirAuth Tk evs"
by (blast dest: leI le_trans elim: leE)


lemma Confidentiality_B:
     "[| Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}
           \<in> parts (spies evs);
         Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}
           \<in> parts (spies evs);
         Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}
           \<in> parts (spies evs);
         ~ ExpirServ Tt evs; ~ ExpirAuth Tk evs;
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerberos |]
      ==> Key ServKey \<notin> analz (spies evs)"
apply (frule A_trusts_AuthKey)
apply (frule_tac [3] Confidentiality_Kas)
apply (frule_tac [6] B_trusts_ServTicket, auto)
apply (blast dest!: Confidentiality_Tgs2 dest: Says_Kas_message_form A_trusts_K4 unique_ServKeys unique_AuthKeys)
done
(*
The proof above is fast.  It can be done in one command in 17 secs:
apply (blast dest: A_trusts_AuthKey A_trusts_K4
                               Says_Kas_message_form B_trusts_ServTicket
                               unique_ServKeys unique_AuthKeys
                               Confidentiality_Kas
                               Confidentiality_Tgs2)
It is very brittle: we can't use this command partway
through the script above.
*)



text{*Most general form -- only for refined model! *}
lemma Confidentiality_B_refined:
     "[| Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}
           \<in> parts (spies evs);
         ~ ExpirServ Tt evs;
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerberos |]
      ==> Key ServKey \<notin> analz (spies evs)"
apply (blast dest: B_trusts_ServTicket_refined NotExpirServ_NotExpirAuth_refined Confidentiality_Tgs2)
done


subsection{* Authenticity theorems *}

text{*1. Session Keys authenticity: they originated with servers.*}

text{*Authenticity of ServKey for A*}
lemma A_trusts_ServKey:
     "[| Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}
           \<in> parts (spies evs);
         Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}
           \<in> parts (spies evs);
         ~ ExpirAuth Tk evs; A \<notin> bad; evs \<in> kerberos |]
 ==>Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|})
       \<in> set evs"
by (blast dest: A_trusts_AuthKey Confidentiality_Auth_A A_trusts_K4_bis)

text{*Note: requires a temporal check*}


(***2. Parties authenticity: each party verifies "the identity of
       another party who generated some data" (quoted from Neuman & Ts'o).***)

       (*These guarantees don't assess whether two parties agree on
         the same session key: sending a message containing a key
         doesn't a priori state knowledge of the key.***)

text{*B checks authenticity of A by theorems @{text A_Authenticity} and
  @{text A_authenticity_refined} *}
lemma Says_Auth:
     "[| Crypt ServKey {|Agent A, Number Ta|} \<in> parts (spies evs);
         Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Number Tt,
                                     ServTicket|}) \<in> set evs;
         Key ServKey \<notin> analz (spies evs);
         A \<notin> bad; B \<notin> bad; evs \<in> kerberos |]
 ==> Says A B {|ServTicket, Crypt ServKey {|Agent A, Number Ta|}|} \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct, analz_mono_contra)
apply (frule_tac [5] Says_ticket_in_parts_spies)
apply (frule_tac [7] Says_ticket_in_parts_spies)
apply (simp_all (no_asm_simp) add: all_conj_distrib)
apply blast
txt{*K3*}
apply (blast dest: A_trusts_AuthKey Says_Kas_message_form Says_Tgs_message_form)
txt{*K4*}
apply (force dest!: Crypt_imp_keysFor)
txt{*K5*}
apply (blast dest: Key_unique_SesKey)
done

text{*The second assumption tells B what kind of key ServKey is.*}
lemma A_Authenticity:
     "[| Crypt ServKey {|Agent A, Number Ta|} \<in> parts (spies evs);
         Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}
           \<in> parts (spies evs);
         Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}
           \<in> parts (spies evs);
         Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}
           \<in> parts (spies evs);
         ~ ExpirServ Tt evs; ~ ExpirAuth Tk evs;
         B \<noteq> Tgs; A \<notin> bad;  B \<notin> bad;  evs \<in> kerberos |]
   ==> Says A B {|Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|},
                  Crypt ServKey {|Agent A, Number Ta|} |} \<in> set evs"
by (blast intro: Says_Auth dest: Confidentiality_B Key_unique_SesKey B_trusts_ServKey)

text{*Stronger form in the refined model*}
lemma A_Authenticity_refined:
     "[| Crypt ServKey {|Agent A, Number Ta2|} \<in> parts (spies evs);
         Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}
           \<in> parts (spies evs);
         ~ ExpirServ Tt evs;
         B \<noteq> Tgs; A \<notin> bad;  B \<notin> bad;  evs \<in> kerberos |]
   ==> Says A B {|Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|},
                  Crypt ServKey {|Agent A, Number Ta2|} |} \<in> set evs"
by (blast dest: Confidentiality_B_refined B_trusts_ServKey Key_unique_SesKey intro: Says_Auth)


text{*A checks authenticity of B by theorem @{text B_authenticity}*}

lemma Says_K6:
     "[| Crypt ServKey (Number Ta) \<in> parts (spies evs);
         Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Number Tt,
                                     ServTicket|}) \<in> set evs;
         Key ServKey \<notin> analz (spies evs);
         A \<notin> bad; B \<notin> bad; evs \<in> kerberos |]
      ==> Says B A (Crypt ServKey (Number Ta)) \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct, analz_mono_contra)
apply (frule_tac [5] Says_ticket_in_parts_spies)
apply (frule_tac [7] Says_ticket_in_parts_spies)
apply (simp_all (no_asm_simp))
apply blast
apply (force dest!: Crypt_imp_keysFor, clarify)
apply (frule Says_Tgs_message_form, assumption, clarify) (*PROOF FAILED if omitted*)
apply (blast dest: unique_CryptKey)
done

lemma K4_trustworthy:
     "[| Crypt AuthKey {|Key ServKey, Agent B, T, ServTicket|}
           \<in> parts (spies evs);
         Key AuthKey \<notin> analz (spies evs);  AuthKey \<notin> range shrK;
         evs \<in> kerberos |]
  ==> \<exists>A. Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, T, ServTicket|})
              \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct, analz_mono_contra)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all)
apply (blast+)
done

lemma B_Authenticity:
     "[| Crypt ServKey (Number Ta) \<in> parts (spies evs);
         Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}
           \<in> parts (spies evs);
         Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}
           \<in> parts (spies evs);
         ~ ExpirAuth Tk evs; ~ ExpirServ Tt evs;
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerberos |]
      ==> Says B A (Crypt ServKey (Number Ta)) \<in> set evs"
apply (frule A_trusts_AuthKey)
apply (frule_tac [3] Says_Kas_message_form)
apply (frule_tac [4] Confidentiality_Kas)
apply (frule_tac [7] K4_trustworthy)
prefer 8 apply blast
apply (erule_tac [9] exE)
apply (frule_tac [9] K4_imp_K2)
txt{*Yes the proof's a mess, but I don't know how to improve it.*}
apply assumption+
apply (blast dest: Key_unique_SesKey intro!: Says_K6 dest: Confidentiality_Tgs1
)
done


(***3. Parties' knowledge of session keys. A knows a session key if she
       used it to build a cipher.***)

lemma B_Knows_B_Knows_ServKey_lemma:
     "[| Says B A (Crypt ServKey (Number Ta)) \<in> set evs;
         Key ServKey \<notin> analz (spies evs);
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerberos |]
      ==> B Issues A with (Crypt ServKey (Number Ta)) on evs"
apply (simp (no_asm) add: Issues_def)
apply (rule exI)
apply (rule conjI, assumption)
apply (simp (no_asm))
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct, analz_mono_contra)
apply (frule_tac [5] Says_ticket_in_parts_spies)
apply (frule_tac [7] Says_ticket_in_parts_spies)
apply (simp_all (no_asm_simp) add: all_conj_distrib)
apply blast
txt{*K6 requires numerous lemmas*}
apply (simp add: takeWhile_tail)
apply (blast dest: B_trusts_ServTicket parts_spies_takeWhile_mono [THEN subsetD] parts_spies_evs_revD2 [THEN subsetD] intro: Says_K6)
done
(*Key ServKey \<notin> analz (spies evs) could be relaxed by Confidentiality_B
  but this is irrelevant because B knows what he knows!                  *)

lemma B_Knows_B_Knows_ServKey:
     "[| Says B A (Crypt ServKey (Number Ta)) \<in> set evs;
         Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}
            \<in> parts (spies evs);
         Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}
            \<in> parts (spies evs);
         Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}
           \<in> parts (spies evs);
         ~ ExpirServ Tt evs; ~ ExpirAuth Tk evs;
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerberos |]
      ==> B Issues A with (Crypt ServKey (Number Ta)) on evs"
by (blast dest!: Confidentiality_B B_Knows_B_Knows_ServKey_lemma)

lemma B_Knows_B_Knows_ServKey_refined:
     "[| Says B A (Crypt ServKey (Number Ta)) \<in> set evs;
         Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}
            \<in> parts (spies evs);
         ~ ExpirServ Tt evs;
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerberos |]
      ==> B Issues A with (Crypt ServKey (Number Ta)) on evs"
by (blast dest!: Confidentiality_B_refined B_Knows_B_Knows_ServKey_lemma)

lemma A_Knows_B_Knows_ServKey:
     "[| Crypt ServKey (Number Ta) \<in> parts (spies evs);
         Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}
           \<in> parts (spies evs);
         Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}
           \<in> parts (spies evs);
         ~ ExpirAuth Tk evs; ~ ExpirServ Tt evs;
         A \<notin> bad;  B \<notin> bad; B \<noteq> Tgs; evs \<in> kerberos |]
      ==> B Issues A with (Crypt ServKey (Number Ta)) on evs"
by (blast dest!: B_Authenticity Confidentiality_Serv_A B_Knows_B_Knows_ServKey_lemma)

lemma K3_imp_K2:
     "[| Says A Tgs
             {|AuthTicket, Crypt AuthKey {|Agent A, Number Ta|}, Agent B|}
           \<in> set evs;
         A \<notin> bad;  evs \<in> kerberos |]
      ==> \<exists>Tk. Says Kas A (Crypt (shrK A)
                      {|Key AuthKey, Agent Tgs, Tk, AuthTicket|})
                   \<in> set evs"
apply (erule rev_mp)
apply (erule kerberos.induct)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all, blast, blast)
apply (blast dest: Says_imp_spies [THEN parts.Inj, THEN A_trusts_AuthKey])
done

lemma K4_trustworthy':
     "[| Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}
           \<in> parts (spies evs);
         Says Kas A (Crypt (shrK A)
                     {|Key AuthKey, Agent Tgs, Tk, AuthTicket|})
         \<in> set evs;
         Key AuthKey \<notin> analz (spies evs);
         B \<noteq> Tgs; A \<notin> bad;  B \<notin> bad;  evs \<in> kerberos |]
   ==> Says Tgs A (Crypt AuthKey
                     {|Key ServKey, Agent B, Number Tt, ServTicket|})
         \<in> set evs"
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct, analz_mono_contra)
apply (frule_tac [7] K5_msg_in_parts_spies)
apply (frule_tac [5] K3_msg_in_parts_spies, simp_all, blast)
apply (force dest!: Crypt_imp_keysFor)
apply (blast dest: Says_imp_spies [THEN parts.Inj, THEN parts.Fst, THEN A_trusts_AuthTicket] unique_AuthKeys)
done

lemma A_Knows_A_Knows_ServKey_lemma:
     "[| Says A B {|ServTicket, Crypt ServKey {|Agent A, Number Ta|}|}
           \<in> set evs;
         Key ServKey \<notin> analz (spies evs);
         B \<noteq> Tgs; A \<notin> bad;  B \<notin> bad;  evs \<in> kerberos |]
   ==> A Issues B with (Crypt ServKey {|Agent A, Number Ta|}) on evs"
apply (simp (no_asm) add: Issues_def)
apply (rule exI)
apply (rule conjI, assumption)
apply (simp (no_asm))
apply (erule rev_mp)
apply (erule rev_mp)
apply (erule kerberos.induct, analz_mono_contra)
apply (frule_tac [5] Says_ticket_in_parts_spies)
apply (frule_tac [7] Says_ticket_in_parts_spies)
apply (simp_all (no_asm_simp))
apply clarify
txt{*K5*}
apply auto
apply (simp add: takeWhile_tail)
txt{*Level 15: case study necessary because the assumption doesn't state
  the form of ServTicket. The guarantee becomes stronger.*}
apply (blast dest: Says_imp_spies [THEN analz.Inj, THEN analz_Decrypt']
                   K3_imp_K2 K4_trustworthy'
                   parts_spies_takeWhile_mono [THEN subsetD]
                   parts_spies_evs_revD2 [THEN subsetD]
             intro: Says_Auth)
apply (simp add: takeWhile_tail)
done

lemma A_Knows_A_Knows_ServKey:
     "[| Says A B {|ServTicket, Crypt ServKey {|Agent A, Number Ta|}|}
           \<in> set evs;
         Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}
           \<in> parts (spies evs);
         Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}
           \<in> parts (spies evs);
         ~ ExpirAuth Tk evs; ~ ExpirServ Tt evs;
         B \<noteq> Tgs; A \<notin> bad;  B \<notin> bad;  evs \<in> kerberos |]
   ==> A Issues B with (Crypt ServKey {|Agent A, Number Ta|}) on evs"
by (blast dest!: Confidentiality_Serv_A A_Knows_A_Knows_ServKey_lemma)

lemma B_Knows_A_Knows_ServKey:
     "[| Crypt ServKey {|Agent A, Number Ta|} \<in> parts (spies evs);
         Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}
           \<in> parts (spies evs);
         Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}
           \<in> parts (spies evs);
         Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}
           \<in> parts (spies evs);
         ~ ExpirServ Tt evs; ~ ExpirAuth Tk evs;
         B \<noteq> Tgs; A \<notin> bad;  B \<notin> bad;  evs \<in> kerberos |]
   ==> A Issues B with (Crypt ServKey {|Agent A, Number Ta|}) on evs"
by (blast dest: A_Authenticity Confidentiality_B A_Knows_A_Knows_ServKey_lemma)


lemma B_Knows_A_Knows_ServKey_refined:
     "[| Crypt ServKey {|Agent A, Number Ta|} \<in> parts (spies evs);
         Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}
           \<in> parts (spies evs);
         ~ ExpirServ Tt evs;
         B \<noteq> Tgs; A \<notin> bad;  B \<notin> bad;  evs \<in> kerberos |]
   ==> A Issues B with (Crypt ServKey {|Agent A, Number Ta|}) on evs"
by (blast dest: A_Authenticity_refined Confidentiality_B_refined A_Knows_A_Knows_ServKey_lemma)

end
