(*  Title:      HOL/Auth/KerberosIV
    ID:         $Id$
    Author:     Giampaolo Bella, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Kerberos protocol, version IV.  Proofs streamlined by lcp.
*)


AddDs  [Says_imp_knows_Spy RS parts.Inj, parts.Body];
AddDs  [impOfSubs analz_subset_parts, impOfSubs Fake_parts_insert];

Pretty.setdepth 20;
set timing;

AddIffs [AuthLife_LB, ServLife_LB, AutcLife_LB, RespLife_LB, Tgs_not_bad];


(** Reversed traces **)

Goal "spies (evs @ [Says A B X]) = insert X (spies evs)";
by (induct_tac "evs" 1);
by (induct_tac "a" 2);
by Auto_tac;
qed "spies_Says_rev";

Goal "spies (evs @ [Gets A X]) = spies evs";
by (induct_tac "evs" 1);
by (induct_tac "a" 2);
by Auto_tac;
qed "spies_Gets_rev";

Goal "spies (evs @ [Notes A X]) = \
\         (if A:bad then insert X (spies evs) else spies evs)";
by (induct_tac "evs" 1);
by (induct_tac "a" 2);
by Auto_tac;
qed "spies_Notes_rev";

Goal "spies evs = spies (rev evs)";
by (induct_tac "evs" 1);
by (induct_tac "a" 2);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps [spies_Says_rev, spies_Gets_rev, 
				       spies_Notes_rev])));
qed "spies_evs_rev";
bind_thm ("parts_spies_evs_revD2", spies_evs_rev RS equalityD2 RS parts_mono);

Goal "spies (takeWhile P evs)  <=  spies evs";
by (induct_tac "evs" 1);
by (induct_tac "a" 2);
by Auto_tac;
(* Resembles "used_subset_append" in Event.ML*)
qed "spies_takeWhile";
bind_thm ("parts_spies_takeWhile_mono", spies_takeWhile RS parts_mono);

Goal "~P(x) --> takeWhile P (xs @ [x]) = takeWhile P xs";
by (induct_tac "xs" 1);
by Auto_tac;
qed "takeWhile_tail";


(*****************LEMMAS ABOUT AuthKeys****************)

Goalw [AuthKeys_def] "AuthKeys [] = {}";
by (Simp_tac 1);
qed "AuthKeys_empty";

Goalw [AuthKeys_def] 
 "(\\<forall>A Tk akey Peer.              \
\  ev \\<noteq> Says Kas A (Crypt (shrK A) {|akey, Agent Peer, Tk,      \
\             (Crypt (shrK Peer) {|Agent A, Agent Peer, akey, Tk|})|}))\ 
\      ==> AuthKeys (ev # evs) = AuthKeys evs";
by Auto_tac;
qed "AuthKeys_not_insert";

Goalw [AuthKeys_def] 
  "AuthKeys \
\    (Says Kas A (Crypt (shrK A) {|Key K, Agent Peer, Number Tk, \
\     (Crypt (shrK Peer) {|Agent A, Agent Peer, Key K, Number Tk|})|}) # evs) \
\      = insert K (AuthKeys evs)";
by Auto_tac;
qed "AuthKeys_insert";

Goalw [AuthKeys_def] 
   "K \\<in> AuthKeys \
\   (Says Kas A (Crypt (shrK A) {|Key K', Agent Peer, Number Tk, \
\    (Crypt (shrK Peer) {|Agent A, Agent Peer, Key K', Number Tk|})|}) # evs) \
\       ==> K = K' | K \\<in> AuthKeys evs";
by Auto_tac;
qed "AuthKeys_simp";

Goalw [AuthKeys_def]  
   "Says Kas A (Crypt (shrK A) {|Key K, Agent Tgs, Number Tk, \
\    (Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key K, Number Tk|})|}) \\<in> set evs \
\       ==> K \\<in> AuthKeys evs";
by Auto_tac;
qed "AuthKeysI";

Goalw [AuthKeys_def] "K \\<in> AuthKeys evs ==> Key K \\<in> used evs";
by (Simp_tac 1);
by (Blast_tac 1);
qed "AuthKeys_used";


(**** FORWARDING LEMMAS ****)

(*--For reasoning about the encrypted portion of message K3--*)
Goal "Says Kas' A (Crypt KeyA {|AuthKey, Peer, Tk, AuthTicket|}) \
\              \\<in> set evs ==> AuthTicket \\<in> parts (spies evs)";
by (Blast_tac 1);
qed "K3_msg_in_parts_spies";

Goal "Says Kas A (Crypt KeyA {|AuthKey, Peer, Tk, AuthTicket|}) \
\              \\<in> set evs ==> AuthKey \\<in> parts (spies evs)";
by (Blast_tac 1);
qed "Oops_parts_spies1";
                              
Goal "[| Says Kas A (Crypt KeyA {|Key AuthKey, Peer, Tk, AuthTicket|}) \
\          \\<in> set evs ;\
\        evs \\<in> kerberos |] ==> AuthKey \\<notin> range shrK";
by (etac rev_mp 1);
by (etac kerberos.induct 1);
by Auto_tac;
qed "Oops_range_spies1";

(*--For reasoning about the encrypted portion of message K5--*)
Goal "Says Tgs' A (Crypt AuthKey {|ServKey, Agent B, Tt, ServTicket|})\
 \             \\<in> set evs ==> ServTicket \\<in> parts (spies evs)";
by (Blast_tac 1);
qed "K5_msg_in_parts_spies";

Goal "Says Tgs A (Crypt AuthKey {|ServKey, Agent B, Tt, ServTicket|})\
\                  \\<in> set evs ==> ServKey \\<in> parts (spies evs)";
by (Blast_tac 1);
qed "Oops_parts_spies2";

Goal "[| Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|}) \
\          \\<in> set evs ;\
\        evs \\<in> kerberos |] ==> ServKey \\<notin> range shrK";
by (etac rev_mp 1);
by (etac kerberos.induct 1);
by Auto_tac;
qed "Oops_range_spies2";

Goal "Says S A (Crypt K {|SesKey, B, TimeStamp, Ticket|}) \\<in> set evs \
\     ==> Ticket \\<in> parts (spies evs)";
by (Blast_tac 1);
qed "Says_ticket_in_parts_spies";
(*Replaces both K3_msg_in_parts_spies and K5_msg_in_parts_spies*)

fun parts_induct_tac i = 
    etac kerberos.induct i  THEN 
    REPEAT (FIRSTGOAL analz_mono_contra_tac)  THEN
    ftac K3_msg_in_parts_spies (i+4)  THEN
    ftac K5_msg_in_parts_spies (i+6)  THEN
    ftac Oops_parts_spies1 (i+8)  THEN
    ftac Oops_parts_spies2 (i+9) THEN
    prove_simple_subgoals_tac 1;


(*Spy never sees another agent's shared key! (unless it's lost at start)*)
Goal "evs \\<in> kerberos ==> (Key (shrK A) \\<in> parts (spies evs)) = (A \\<in> bad)";
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

Goal "evs \\<in> kerberos ==> (Key (shrK A) \\<in> analz (spies evs)) = (A \\<in> bad)";
by Auto_tac;
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

Goal "[| Key (shrK A) \\<in> parts (spies evs);  evs \\<in> kerberos |] ==> A:bad";
by (blast_tac (claset() addDs [Spy_see_shrK]) 1);
qed "Spy_see_shrK_D";
bind_thm ("Spy_analz_shrK_D", analz_subset_parts RS subsetD RS Spy_see_shrK_D);
AddSDs [Spy_see_shrK_D, Spy_analz_shrK_D];

(*Nobody can have used non-existent keys!*)
Goal "evs \\<in> kerberos ==>      \
\     Key K \\<notin> used evs --> K \\<notin> keysFor (parts (spies evs))";
by (parts_induct_tac 1);
(*Fake*)
by (blast_tac (claset() addSDs [keysFor_parts_insert]) 1);
(*Others*)
by (ALLGOALS Blast_tac);
qed_spec_mp "new_keys_not_used";
Addsimps [new_keys_not_used];

(*Earlier, all protocol proofs declared this theorem.  
  But few of them actually need it! (Another is Yahalom) *)
bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);


(*********************** REGULARITY LEMMAS ***********************)
(*       concerning the form of items passed in messages         *)
(*****************************************************************)

(*Describes the form of AuthKey, AuthTicket, and K sent by Kas*)
Goal "[| Says Kas A (Crypt K {|Key AuthKey, Agent Peer, Tk, AuthTicket|}) \
\          \\<in> set evs;                 \
\        evs \\<in> kerberos |]             \
\     ==> AuthKey \\<notin> range shrK & AuthKey \\<in> AuthKeys evs & \
\ AuthTicket = (Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Tk|} ) &\
\            K = shrK A  & Peer = Tgs";
by (etac rev_mp 1);
by (etac kerberos.induct 1);
by (ALLGOALS (simp_tac (simpset() addsimps [AuthKeys_def, AuthKeys_insert])));
by (ALLGOALS Blast_tac);
qed "Says_Kas_message_form";

(*This lemma is essential for proving Says_Tgs_message_form: 
  
  the session key AuthKey
  supplied by Kas in the authentication ticket
  cannot be a long-term key!

  Generalised to any session keys (both AuthKey and ServKey).
*)
Goal "[| Crypt (shrK Tgs_B) {|Agent A, Agent Tgs_B, Key SesKey, Number T|}\
\           \\<in> parts (spies evs); Tgs_B \\<notin> bad;\
\        evs \\<in> kerberos |]    \
\     ==> SesKey \\<notin> range shrK";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Blast_tac 1);
qed "SesKey_is_session_key";

Goal "[| Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Tk|}  \
\          \\<in> parts (spies evs);                              \
\        evs \\<in> kerberos |]                          \
\     ==> Says Kas A (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Tk, \
\                Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Tk|}|})  \
\           \\<in> set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*Fake, K4*)
by (ALLGOALS Blast_tac);
qed "A_trusts_AuthTicket";

Goal "[| Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}\
\          \\<in> parts (spies evs);\
\        evs \\<in> kerberos |]    \
\     ==> AuthKey \\<in> AuthKeys evs";
by (ftac A_trusts_AuthTicket 1);
by (assume_tac 1);
by (simp_tac (simpset() addsimps [AuthKeys_def]) 1);
by (Blast_tac 1);
qed "AuthTicket_crypt_AuthKey";

(*Describes the form of ServKey, ServTicket and AuthKey sent by Tgs*)
Goal "[| Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|})\
\          \\<in> set evs; \
\        evs \\<in> kerberos |]    \
\  ==> B \\<noteq> Tgs & ServKey \\<notin> range shrK & ServKey \\<notin> AuthKeys evs &\
\      ServTicket = (Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Tt|} ) & \
\      AuthKey \\<notin> range shrK & AuthKey \\<in> AuthKeys evs";
by (etac rev_mp 1);
by (etac kerberos.induct 1);
by (ALLGOALS
    (asm_full_simp_tac
     (simpset() addsimps [AuthKeys_insert, AuthKeys_not_insert,
			  AuthKeys_empty, AuthKeys_simp])));
by (blast_tac (claset()) 1);
by Auto_tac;
by (blast_tac (claset() addSDs [AuthKeys_used, Says_Kas_message_form]) 1);
by (blast_tac (claset() addSDs [SesKey_is_session_key]) 1);
by (blast_tac (claset() addDs [AuthTicket_crypt_AuthKey]) 1);
qed "Says_Tgs_message_form";

(*If a certain encrypted message appears then it originated with Kas*)
Goal "[| Crypt (shrK A) {|Key AuthKey, Peer, Tk, AuthTicket|}  \
\          \\<in> parts (spies evs);                              \
\        A \\<notin> bad;  evs \\<in> kerberos |]                        \
\     ==> Says Kas A (Crypt (shrK A) {|Key AuthKey, Peer, Tk, AuthTicket|})  \
\           \\<in> set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*Fake*)
by (Blast_tac 1);
(*K4*)
by (blast_tac (claset() addSDs [A_trusts_AuthTicket RS Says_Kas_message_form])
    1);
qed "A_trusts_AuthKey";


(*If a certain encrypted message appears then it originated with Tgs*)
Goal "[| Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|}     \
\          \\<in> parts (spies evs);                                     \
\        Key AuthKey \\<notin> analz (spies evs);           \
\        AuthKey \\<notin> range shrK;                      \
\        evs \\<in> kerberos |]         \
\==> \\<exists>A. Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|})\
\      \\<in> set evs";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*Fake*)
by (Blast_tac 1);
(*K2*)
by (Blast_tac 1);
(*K4*)
by Auto_tac;
qed "A_trusts_K4";

Goal "[| Crypt (shrK A) {|Key AuthKey, Agent Tgs, Tk, AuthTicket|} \
\          \\<in> parts (spies evs);          \
\        A \\<notin> bad;                       \
\        evs \\<in> kerberos |]                \
\   ==> AuthKey \\<notin> range shrK &               \
\       AuthTicket = Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Tk|}";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "AuthTicket_form";

(* This form holds also over an AuthTicket, but is not needed below.     *)
Goal "[| Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|} \
\             \\<in> parts (spies evs); \
\           Key AuthKey \\<notin> analz (spies evs);  \
\           evs \\<in> kerberos |]                                       \
\        ==> ServKey \\<notin> range shrK &  \
\   (\\<exists>A. ServTicket = Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Tt|})";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Blast_tac 1);
qed "ServTicket_form";

Goal "[| Says Kas' A (Crypt (shrK A) \
\             {|Key AuthKey, Agent Tgs, Tk, AuthTicket|} ) \\<in> set evs; \
\        evs \\<in> kerberos |]    \
\     ==> AuthKey \\<notin> range shrK & \
\         AuthTicket = \
\                 Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Tk|}\
\         | AuthTicket \\<in> analz (spies evs)";
by (blast_tac (claset() addDs [Says_imp_spies RS analz.Inj, 
                               AuthTicket_form]) 1);
qed "Says_kas_message_form";
(* Essentially the same as AuthTicket_form *)

Goal "[| Says Tgs' A (Crypt AuthKey \
\             {|Key ServKey, Agent B, Tt, ServTicket|} ) \\<in> set evs; \
\        evs \\<in> kerberos |]    \
\     ==> ServKey \\<notin> range shrK & \
\         (\\<exists>A. ServTicket = \
\                 Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Tt|})  \
\          | ServTicket \\<in> analz (spies evs)";
by (blast_tac (claset() addDs [Says_imp_spies RS analz.Inj, 
                               ServTicket_form]) 1);
qed "Says_tgs_message_form";
(* This form MUST be used in analz_sees_tac below *)


(*****************UNICITY THEOREMS****************)

(* The session key, if secure, uniquely identifies the Ticket
   whether AuthTicket or ServTicket. As a matter of fact, one can read
   also Tgs in the place of B.                                     *)

Goal "[| Crypt (shrK B)  {|Agent A,  Agent B,  Key SesKey, T|}        \
\          \\<in> parts (spies evs);            \
\        Crypt (shrK B') {|Agent A', Agent B', Key SesKey, T'|}     \
\          \\<in> parts (spies evs);  Key SesKey \\<notin> analz (spies evs);   \
\        evs \\<in> kerberos |]  \
\     ==> A=A' & B=B' & T=T'";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*Fake, K2, K4*)
by (ALLGOALS Blast_tac); 
qed "unique_CryptKey";

(*An AuthKey is encrypted by one and only one Shared key.
  A ServKey is encrypted by one and only one AuthKey.
*)
Goal "[| Crypt K  {|Key SesKey,  Agent B, T, Ticket|}        \
\          \\<in> parts (spies evs);            \
\        Crypt K' {|Key SesKey,  Agent B', T', Ticket'|}     \
\          \\<in> parts (spies evs);  Key SesKey \\<notin> analz (spies evs);            \
\        evs \\<in> kerberos |]  \
\     ==> K=K' & B=B' & T=T' & Ticket=Ticket'";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*Fake, K2, K4*)
by (ALLGOALS Blast_tac); 
qed "Key_unique_SesKey";


(*
  At reception of any message mentioning A, Kas associates shrK A with
  a new AuthKey. Realistic, as the user gets a new AuthKey at each login.
  Similarly, at reception of any message mentioning an AuthKey
  (a legitimate user could make several requests to Tgs - by K3), Tgs 
  associates it with a new ServKey.

  Therefore, a goal like

   "evs \\<in> kerberos \
  \  ==> Key Kc \\<notin> analz (spies evs) -->   \
  \        (\\<exists>K' B' T' Ticket'. \\<forall>K B T Ticket.                          \
  \         Crypt Kc {|Key K, Agent B, T, Ticket|}    \
  \          \\<in> parts (spies evs) --> K=K' & B=B' & T=T' & Ticket=Ticket')";

  would fail on the K2 and K4 cases.
*)

Goal "[| Says Kas A                                          \
\             (Crypt Ka {|Key AuthKey, Agent Tgs, Tk, X|}) \\<in> set evs;     \ 
\        Says Kas A'                                         \
\             (Crypt Ka' {|Key AuthKey, Agent Tgs, Tk', X'|}) \\<in> set evs;   \
\        evs \\<in> kerberos |] ==> A=A' & Ka=Ka' & Tk=Tk' & X=X'";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*K2*)
by (Blast_tac 1); 
qed "unique_AuthKeys";

(* ServKey uniquely identifies the message from Tgs *)
Goal "[| Says Tgs A                                             \
\             (Crypt K {|Key ServKey, Agent B, Tt, X|}) \\<in> set evs; \ 
\        Says Tgs A'                                                 \
\             (Crypt K' {|Key ServKey, Agent B', Tt', X'|}) \\<in> set evs; \
\        evs \\<in> kerberos |] ==> A=A' & B=B' & K=K' & Tt=Tt' & X=X'";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*K4*)
by (Blast_tac 1); 
qed "unique_ServKeys";


(*****************LEMMAS ABOUT the predicate KeyCryptKey****************)

Goalw [KeyCryptKey_def] "~ KeyCryptKey AuthKey ServKey []";
by (Simp_tac 1);
qed "not_KeyCryptKey_Nil";
AddIffs [not_KeyCryptKey_Nil];

Goalw [KeyCryptKey_def]
 "[| Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, tt, X |}) \
\             \\<in> set evs;    \
\           evs \\<in> kerberos |] ==> KeyCryptKey AuthKey ServKey evs";
by (blast_tac (claset() addDs [Says_Tgs_message_form]) 1); 
qed "KeyCryptKeyI";

Goalw [KeyCryptKey_def]
   "KeyCryptKey AuthKey ServKey (Says S A X # evs) =                       \
\    (Tgs = S &                                                            \
\     (\\<exists>B tt. X = Crypt AuthKey        \
\               {|Key ServKey, Agent B, tt,  \
\                 Crypt (shrK B) {|Agent A, Agent B, Key ServKey, tt|} |}) \
\    | KeyCryptKey AuthKey ServKey evs)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "KeyCryptKey_Says";
Addsimps [KeyCryptKey_Says];

(*A fresh AuthKey cannot be associated with any other
  (with respect to a given trace). *)
Goalw [KeyCryptKey_def]
 "[| Key AuthKey \\<notin> used evs; evs \\<in> kerberos |] \
\        ==> ~ KeyCryptKey AuthKey ServKey evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed "Auth_fresh_not_KeyCryptKey";

(*A fresh ServKey cannot be associated with any other
  (with respect to a given trace). *)
Goalw [KeyCryptKey_def]
 "Key ServKey \\<notin> used evs ==> ~ KeyCryptKey AuthKey ServKey evs";
by (Blast_tac 1);
qed "Serv_fresh_not_KeyCryptKey";

Goal
 "[| Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, tk|}\
\             \\<in> parts (spies evs);  evs \\<in> kerberos |] \
\        ==> ~ KeyCryptKey K AuthKey evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*K4*)
by (Blast_tac 3);
(*K2: by freshness*)
by (asm_full_simp_tac (simpset() addsimps [KeyCryptKey_def]) 2); 
by (ALLGOALS Blast_tac); 
qed "AuthKey_not_KeyCryptKey";

(*A secure serverkey cannot have been used to encrypt others*)
Goal
 "[| Crypt (shrK B) {|Agent A, Agent B, Key SK, tt|} \\<in> parts (spies evs); \
\    Key SK \\<notin> analz (spies evs);             \
\    B \\<noteq> Tgs;  evs \\<in> kerberos |] \
\ ==> ~ KeyCryptKey SK K evs";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Blast_tac 1);
(*K4 splits into distinct subcases*)
by Auto_tac;  
(*ServKey can't have been enclosed in two certificates*)
by (blast_tac (claset() addDs [unique_CryptKey]) 2);
(*ServKey is fresh and so could not have been used, by new_keys_not_used*)
by (force_tac (claset() addSDs [Crypt_imp_invKey_keysFor],
	       simpset() addsimps [KeyCryptKey_def]) 1); 
qed "ServKey_not_KeyCryptKey";

(*Long term keys are not issued as ServKeys*)
Goalw [KeyCryptKey_def]
 "evs \\<in> kerberos ==> ~ KeyCryptKey K (shrK A) evs";
by (parts_induct_tac 1);
qed "shrK_not_KeyCryptKey";

(*The Tgs message associates ServKey with AuthKey and therefore not with any 
  other key AuthKey.*)
Goalw [KeyCryptKey_def]
 "[| Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, tt, X |}) \
\      \\<in> set evs;                                         \
\    AuthKey' \\<noteq> AuthKey;  evs \\<in> kerberos |]                      \
\ ==> ~ KeyCryptKey AuthKey' ServKey evs";
by (blast_tac (claset() addDs [unique_ServKeys]) 1);
qed "Says_Tgs_KeyCryptKey";

Goal "[| KeyCryptKey AuthKey ServKey evs;  evs \\<in> kerberos |] \
\     ==> ~ KeyCryptKey ServKey K evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Step_tac 1);
by (ALLGOALS Asm_full_simp_tac);
(*K4 splits into subcases*)
by (blast_tac (claset() addSDs [AuthKey_not_KeyCryptKey]) 4);
(*ServKey is fresh and so could not have been used, by new_keys_not_used*)
by (force_tac (claset() addSDs [Says_imp_spies RS parts.Inj,
				Crypt_imp_invKey_keysFor],
               simpset() addsimps [KeyCryptKey_def]) 2); 
(*Others by freshness*)
by (ALLGOALS Blast_tac);
qed "KeyCryptKey_not_KeyCryptKey";

(*The only session keys that can be found with the help of session keys are
  those sent by Tgs in step K4.  *)

(*We take some pains to express the property
  as a logical equivalence so that the simplifier can apply it.*)
Goal "P --> (Key K \\<in> analz (Key`KK Un H)) --> (K:KK | Key K \\<in> analz H)  \
\     ==>       \
\     P --> (Key K \\<in> analz (Key`KK Un H)) = (K:KK | Key K \\<in> analz H)";
by (blast_tac (claset() addIs [impOfSubs analz_mono]) 1);
qed "Key_analz_image_Key_lemma";

Goal "[| KeyCryptKey K K' evs; evs \\<in> kerberos |] \
\     ==> Key K' \\<in> analz (insert (Key K) (spies evs))";
by (full_simp_tac (simpset() addsimps [KeyCryptKey_def]) 1);
by (Clarify_tac 1);
by (dresolve_tac [Says_imp_spies RS analz.Inj RS analz_insertI] 1);
by Auto_tac;
qed "KeyCryptKey_analz_insert";

Goal "[| K \\<in> AuthKeys evs Un range shrK;  evs \\<in> kerberos |]  \
\     ==> \\<forall>SK. ~ KeyCryptKey SK K evs";
by (asm_full_simp_tac (simpset() addsimps [KeyCryptKey_def]) 1);
by (blast_tac (claset() addDs [Says_Tgs_message_form]) 1);
qed "AuthKeys_are_not_KeyCryptKey";

Goal "[| K \\<notin> AuthKeys evs; \
\        K \\<notin> range shrK; evs \\<in> kerberos |]  \
\     ==> \\<forall>SK. ~ KeyCryptKey K SK evs";
by (asm_full_simp_tac (simpset() addsimps [KeyCryptKey_def]) 1);
by (blast_tac (claset() addDs [Says_Tgs_message_form]) 1);
qed "not_AuthKeys_not_KeyCryptKey";


(*****************SECRECY THEOREMS****************)

(*For proofs involving analz.*)
val analz_sees_tac = 
  EVERY 
   [REPEAT (FIRSTGOAL analz_mono_contra_tac),
    ftac Oops_range_spies2 10, 
    ftac Oops_range_spies1 9, 
    ftac Says_tgs_message_form 7,
    ftac Says_kas_message_form 5, 
    REPEAT_FIRST (eresolve_tac [asm_rl, conjE, disjE, exE]
		  ORELSE' hyp_subst_tac)];

(*For the Oops2 case of the next theorem*)
Goal "[| evs \\<in> kerberos;  \
\        Says Tgs A (Crypt AuthKey \
\                    {|Key ServKey, Agent B, Number Tt, ServTicket|}) \
\          \\<in> set evs |] \
\     ==> ~ KeyCryptKey ServKey SK evs";
by (blast_tac (claset() addDs [KeyCryptKeyI, KeyCryptKey_not_KeyCryptKey]) 1);
qed "Oops2_not_KeyCryptKey";


(* Big simplification law for keys SK that are not crypted by keys in KK   *)
(* It helps prove three, otherwise hard, facts about keys. These facts are *)
(* exploited as simplification laws for analz, and also "limit the damage" *)
(* in case of loss of a key to the spy. See ESORICS98.                     *)
(* [simplified by LCP]                                                     *)
Goal "evs \\<in> kerberos ==>                                         \
\     (\\<forall>SK KK. KK <= -(range shrK) -->                   \
\     (\\<forall>K \\<in> KK. ~ KeyCryptKey K SK evs)   -->           \
\     (Key SK \\<in> analz (Key`KK Un (spies evs))) =        \
\     (SK \\<in> KK | Key SK \\<in> analz (spies evs)))";
by (etac kerberos.induct 1);
by analz_sees_tac;
by (REPEAT_FIRST (rtac allI));
by (REPEAT_FIRST (rtac (Key_analz_image_Key_lemma RS impI)));
(*Case-splits for Oops1 & 5: the negated case simplifies using the ind hyp*)
by (case_tac "KeyCryptKey AuthKey SK evsO1" 11); 
by (case_tac "KeyCryptKey ServKey SK evs5" 8);
by (ALLGOALS  
    (asm_simp_tac 
     (analz_image_freshK_ss addsimps
        [KeyCryptKey_Says, shrK_not_KeyCryptKey, Oops2_not_KeyCryptKey,
	 Auth_fresh_not_KeyCryptKey, Serv_fresh_not_KeyCryptKey, 
	 Says_Tgs_KeyCryptKey, Spy_analz_shrK])));
(*Fake*) 
by (spy_analz_tac 1);
(* Base + K2 done by the simplifier! *)
(*K3*)
by (Blast_tac 1);
(*K4*)
by (blast_tac (claset() addSDs [AuthKey_not_KeyCryptKey]) 1);
(*K5*)
by (case_tac "Key ServKey \\<in> analz (spies evs5)" 1);
(*If ServKey is compromised then the result follows directly...*)
by (asm_simp_tac 
     (simpset() addsimps [analz_insert_eq, 
			 impOfSubs (Un_upper2 RS analz_mono)]) 1);
(*...therefore ServKey is uncompromised.*)
(*The KeyCryptKey ServKey SK evs5 case leads to a contradiction.*)
by (blast_tac (claset() addSEs [ServKey_not_KeyCryptKey RSN(2, rev_notE)]
		        delrules [allE, ballE]) 1);
(** Level 13: Oops1 **)
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addSDs [KeyCryptKey_analz_insert]) 1);
qed_spec_mp "Key_analz_image_Key";


(* First simplification law for analz: no session keys encrypt  *)
(* authentication keys or shared keys.                          *)
Goal "[| evs \\<in> kerberos;  K \\<in> (AuthKeys evs) Un range shrK;      \
\        SesKey \\<notin> range shrK |]                                 \
\     ==> Key K \\<in> analz (insert (Key SesKey) (spies evs)) = \
\         (K = SesKey | Key K \\<in> analz (spies evs))";
by (ftac AuthKeys_are_not_KeyCryptKey 1 THEN assume_tac 1);
by (asm_full_simp_tac (analz_image_freshK_ss addsimps [Key_analz_image_Key]) 1);
qed "analz_insert_freshK1";


(* Second simplification law for analz: no service keys encrypt *)
(* any other keys.					        *)
Goal "[| evs \\<in> kerberos;  ServKey \\<notin> (AuthKeys evs); ServKey \\<notin> range shrK|]\
\     ==> Key K \\<in> analz (insert (Key ServKey) (spies evs)) = \
\         (K = ServKey | Key K \\<in> analz (spies evs))";
by (ftac not_AuthKeys_not_KeyCryptKey 1 
    THEN assume_tac 1
    THEN assume_tac 1);
by (asm_full_simp_tac (analz_image_freshK_ss addsimps [Key_analz_image_Key]) 1);
qed "analz_insert_freshK2";


(* Third simplification law for analz: only one authentication key *)
(* encrypts a certain service key.                                 *)
Goal  
 "[| Says Tgs A    \
\           (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}) \
\             \\<in> set evs;          \ 
\           AuthKey \\<noteq> AuthKey'; AuthKey' \\<notin> range shrK; evs \\<in> kerberos |]    \
\       ==> Key ServKey \\<in> analz (insert (Key AuthKey') (spies evs)) =  \
\               (ServKey = AuthKey' | Key ServKey \\<in> analz (spies evs))";
by (dres_inst_tac [("AuthKey'","AuthKey'")] Says_Tgs_KeyCryptKey 1);
by (Blast_tac 1);
by (assume_tac 1);
by (asm_full_simp_tac (analz_image_freshK_ss addsimps [Key_analz_image_Key]) 1);
qed "analz_insert_freshK3";


(*a weakness of the protocol*)
Goal "[| Says Tgs A    \
\             (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}) \
\          \\<in> set evs;          \ 
\        Key AuthKey \\<in> analz (spies evs); evs \\<in> kerberos |]    \
\     ==> Key ServKey \\<in> analz (spies evs)";
by (force_tac (claset() addDs [Says_imp_spies RS analz.Inj RS 
			       analz.Decrypt RS analz.Fst],
	       simpset()) 1);
qed "AuthKey_compromises_ServKey";


(********************** Guarantees for Kas *****************************)
Goal "[| Crypt AuthKey {|Key ServKey, Agent B, Tt, \
\                     Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Tt|}|}\
\          \\<in> parts (spies evs); \
\        Key ServKey \\<notin> analz (spies evs);                          \
\        B \\<noteq> Tgs; evs \\<in> kerberos |]                            \
\     ==> ServKey \\<notin> AuthKeys evs";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (asm_full_simp_tac (simpset() addsimps [AuthKeys_def]) 1);
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
bind_thm ("ServKey_notin_AuthKeys", result() RSN (2, rev_notE));
bind_thm ("ServKey_notin_AuthKeysD", result());


(** If Spy sees the Authentication Key sent in msg K2, then 
    the Key has expired  **)
Goal "[| A \\<notin> bad;  evs \\<in> kerberos |]           \
\     ==> Says Kas A                             \
\              (Crypt (shrK A)                      \
\                 {|Key AuthKey, Agent Tgs, Number Tk,     \
\         Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}|})\
\           \\<in> set evs -->                 \
\         Key AuthKey \\<in> analz (spies evs) -->                       \
\         ExpirAuth Tk evs";
by (etac kerberos.induct 1);
by analz_sees_tac;
by (ALLGOALS 
    (asm_simp_tac 
     (simpset() addsimps ([Says_Kas_message_form, less_SucI,
			   analz_insert_eq, not_parts_not_analz, 
			   analz_insert_freshK1] @ pushes))));
(*Fake*) 
by (spy_analz_tac 1);
(*K2*)
by (Blast_tac 1);
(*K4*)
by (Blast_tac 1);
(*Level 8: K5*)
by (blast_tac (claset() addEs [ServKey_notin_AuthKeys]
                        addDs [Says_Kas_message_form]
                        addIs [less_SucI]) 1);
(*Oops1*)
by (blast_tac (claset() addSDs [unique_AuthKeys] addIs [less_SucI]) 1);
(*Oops2*)
by (blast_tac (claset() addDs [Says_Tgs_message_form,
                               Says_Kas_message_form]) 1);
val lemma = result() RS mp RS mp RSN(1,rev_notE);


Goal "[| Says Kas A                                             \
\             (Crypt Ka {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|})  \
\          \\<in> set evs;                                \
\        ~ ExpirAuth Tk evs;                         \
\        A \\<notin> bad;  evs \\<in> kerberos |]            \
\     ==> Key AuthKey \\<notin> analz (spies evs)";
by (blast_tac (claset() addDs [Says_Kas_message_form, lemma]) 1);
qed "Confidentiality_Kas";


(********************** Guarantees for Tgs *****************************)

(** If Spy sees the Service Key sent in msg K4, then 
    the Key has expired  **)
Goal "[| A \\<notin> bad;  B \\<notin> bad; B \\<noteq> Tgs; evs \\<in> kerberos |]           \
\  ==> Key AuthKey \\<notin> analz (spies evs) --> \
\      Says Tgs A            \
\        (Crypt AuthKey                      \
\           {|Key ServKey, Agent B, Number Tt,     \
\             Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}|})\
\        \\<in> set evs -->                 \
\      Key ServKey \\<in> analz (spies evs) -->                       \
\      ExpirServ Tt evs";
by (etac kerberos.induct 1);
(*The Oops1 case is unusual: must simplify Authkey \\<notin> analz (spies (ev#evs))
  rather than weakening it to Authkey \\<notin> analz (spies evs), for we then
  conclude AuthKey \\<noteq> AuthKeya.*)
by (Clarify_tac 9);
by analz_sees_tac;
by (rotate_tac ~1 11);
by (ALLGOALS 
    (asm_full_simp_tac 
     (simpset() addsimps [less_SucI, new_keys_not_analzd,
			  Says_Kas_message_form, Says_Tgs_message_form,
			  analz_insert_eq, not_parts_not_analz, 
			  analz_insert_freshK1, analz_insert_freshK2] 
			 @ pushes)));
(*Fake*) 
by (spy_analz_tac 1);
(*K2*)
by (blast_tac (claset()
            addIs [parts_insertI, less_SucI]) 1);
(*K4*)
by (blast_tac (claset() addDs [A_trusts_AuthTicket, Confidentiality_Kas]) 1);
by (ALLGOALS Clarify_tac);
(*Oops2*)
by (blast_tac (claset() addDs [Says_imp_spies RS parts.Inj, 
                               Key_unique_SesKey] addIs [less_SucI]) 3);
(** Level 10 **)
(*Oops1*)
by (blast_tac (claset() addDs [analz_insert_freshK3,
			       Says_Kas_message_form, Says_Tgs_message_form] 
                        addIs  [less_SucI]) 2);
(*K5*)
by (thin_tac "Says Aa Tgs ?X \\<in> set ?evs" 1);
by (forward_tac [Says_imp_spies RS parts.Inj RS ServKey_notin_AuthKeysD] 1);
by (assume_tac 1 THEN Blast_tac 1 THEN assume_tac 1);
by (rotate_tac ~1 1);
by (asm_full_simp_tac (simpset() addsimps [analz_insert_freshK2]) 1);
by (blast_tac (claset() addDs [Says_imp_spies RS parts.Inj, Key_unique_SesKey] 
                        addIs  [less_SucI]) 1);
val lemma = result() RS mp RS mp RS mp RSN(1,rev_notE);


(* In the real world Tgs can't check wheter AuthKey is secure! *)
Goal 
 "[| Says Tgs A      \
\             (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}) \
\             \\<in> set evs;              \
\           Key AuthKey \\<notin> analz (spies evs);        \
\           ~ ExpirServ Tt evs;                         \
\           A \\<notin> bad;  B \\<notin> bad; B \\<noteq> Tgs; evs \\<in> kerberos |]            \
\        ==> Key ServKey \\<notin> analz (spies evs)";
by (blast_tac (claset() addDs [Says_Tgs_message_form, lemma]) 1);
qed "Confidentiality_Tgs1";

(* In the real world Tgs CAN check what Kas sends! *)
Goal 
 "[| Says Kas A                                             \
\              (Crypt Ka {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|})  \
\             \\<in> set evs;                                \
\           Says Tgs A      \
\             (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}) \
\             \\<in> set evs;              \
\           ~ ExpirAuth Tk evs; ~ ExpirServ Tt evs;                         \
\           A \\<notin> bad;  B \\<notin> bad; B \\<noteq> Tgs; evs \\<in> kerberos |]            \
\        ==> Key ServKey \\<notin> analz (spies evs)";
by (blast_tac (claset() addSDs [Confidentiality_Kas,
                                Confidentiality_Tgs1]) 1);
qed "Confidentiality_Tgs2";

(*Most general form*)
val Confidentiality_Tgs3 = A_trusts_AuthTicket RS Confidentiality_Tgs2;


(********************** Guarantees for Alice *****************************)

val Confidentiality_Auth_A = A_trusts_AuthKey RS Confidentiality_Kas;

Goal
 "[| Says Kas A \
\      (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Tk, AuthTicket|}) \\<in> set evs;\
\    Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|}     \
\      \\<in> parts (spies evs);                                       \
\    Key AuthKey \\<notin> analz (spies evs);            \
\    evs \\<in> kerberos |]         \
\==> Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Tt, ServTicket|})\
\      \\<in> set evs";
by (ftac Says_Kas_message_form 1 THEN assume_tac 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Blast_tac 1);
(*K2 and K4 remain*)
by (blast_tac (claset() addSDs [unique_CryptKey]) 2);
by (blast_tac (claset() addSDs [A_trusts_K4, Says_Tgs_message_form, 
				AuthKeys_used]) 1);
qed "A_trusts_K4_bis";


Goal "[| Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}  \
\          \\<in> parts (spies evs);                              \
\        Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}     \
\          \\<in> parts (spies evs);                                       \
\        ~ ExpirAuth Tk evs; ~ ExpirServ Tt evs;                         \
\        A \\<notin> bad;  B \\<notin> bad; B \\<noteq> Tgs; evs \\<in> kerberos |]            \
\     ==> Key ServKey \\<notin> analz (spies evs)";
by (dtac A_trusts_AuthKey 1);
by (assume_tac 1);
by (assume_tac 1);
by (blast_tac (claset() addDs [Confidentiality_Kas, 
                               Says_Kas_message_form,
                               A_trusts_K4_bis, Confidentiality_Tgs2]) 1);
qed "Confidentiality_Serv_A";


(********************** Guarantees for Bob *****************************)
(* Theorems for the refined model have suffix "refined"                *)

Goal
"[| Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|})\
\            \\<in> set evs; evs \\<in> kerberos|]  \
\  ==> \\<exists>Tk. Says Kas A (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk,\
\          Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}|})\
\            \\<in> set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by Auto_tac;
by (blast_tac (claset() addSDs [Says_imp_spies RS parts.Inj RS parts.Fst RS
                               A_trusts_AuthTicket]) 1);
qed "K4_imp_K2";

Goal
"[| Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|})\
\     \\<in> set evs; evs \\<in> kerberos|]  \
\  ==> \\<exists>Tk. (Says Kas A (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk,\
\          Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}|})\
\            \\<in> set evs   \
\         & ServLife + Tt <= AuthLife + Tk)";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by Auto_tac;
by (blast_tac (claset() addSDs [Says_imp_spies RS parts.Inj RS parts.Fst RS
                               A_trusts_AuthTicket]) 1);
qed "K4_imp_K2_refined";

Goal "[| Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Tt|}  \
\          \\<in> parts (spies evs);  B \\<noteq> Tgs;  B \\<notin> bad;       \
\        evs \\<in> kerberos |]                        \
\==> \\<exists>AuthKey. \
\      Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Tt,  \
\                  Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Tt|}|}) \
\      \\<in> set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "B_trusts_ServKey";

Goal "[| Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}  \
\          \\<in> parts (spies evs);  B \\<noteq> Tgs;  B \\<notin> bad;       \
\        evs \\<in> kerberos |]                        \
\  ==> \\<exists>AuthKey Tk. Says Kas A (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk,\
\          Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}|})\
\            \\<in> set evs";
by (blast_tac (claset() addSDs [B_trusts_ServKey, K4_imp_K2]) 1);
qed "B_trusts_ServTicket_Kas";

Goal "[| Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}  \
\          \\<in> parts (spies evs); B \\<noteq> Tgs; B \\<notin> bad;       \
\        evs \\<in> kerberos |]                        \
\  ==> \\<exists>AuthKey Tk. (Says Kas A (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk,\
\          Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}|})\
\            \\<in> set evs            \
\          & ServLife + Tt <= AuthLife + Tk)";
by (blast_tac (claset() addSDs [B_trusts_ServKey,K4_imp_K2_refined]) 1);
qed "B_trusts_ServTicket_Kas_refined";

Goal "[| Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}  \
\          \\<in> parts (spies evs); B \\<noteq> Tgs; B \\<notin> bad;        \
\        evs \\<in> kerberos |]                        \
\==> \\<exists>Tk AuthKey.        \
\    Says Kas A (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, \
\                  Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}|})\
\      \\<in> set evs         \ 
\    & Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Number Tt,  \
\                  Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}|}) \
\      \\<in> set evs";
by (blast_tac (claset() addDs [B_trusts_ServKey, K4_imp_K2]) 1);
qed "B_trusts_ServTicket";

Goal "[| Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}  \
\          \\<in> parts (spies evs); B \\<noteq> Tgs; B \\<notin> bad;        \
\        evs \\<in> kerberos |]                        \
\==> \\<exists>Tk AuthKey.        \
\    (Says Kas A (Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, \
\                  Crypt (shrK Tgs) {|Agent A, Agent Tgs, Key AuthKey, Number Tk|}|})\
\      \\<in> set evs         \ 
\    & Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Number Tt,  \
\                  Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}|}) \
\      \\<in> set evs         \
\    & ServLife + Tt <= AuthLife + Tk)";
by (blast_tac (claset() addDs [B_trusts_ServKey, K4_imp_K2_refined]) 1);
qed "B_trusts_ServTicket_refined";


Goal "[| ~ ExpirServ Tt evs; ServLife + Tt <= AuthLife + Tk |]        \
\  ==> ~ ExpirAuth Tk evs";
by (blast_tac (claset() addDs [leI,le_trans] addEs [leE]) 1);
qed "NotExpirServ_NotExpirAuth_refined";


Goal "[| Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|} \
\          \\<in> parts (spies evs);                                        \
\        Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|} \
\          \\<in> parts (spies evs);                                         \
\        Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}\
\          \\<in> parts (spies evs);                     \
\        ~ ExpirServ Tt evs; ~ ExpirAuth Tk evs;     \
\        A \\<notin> bad;  B \\<notin> bad; B \\<noteq> Tgs; evs \\<in> kerberos |]            \
\     ==> Key ServKey \\<notin> analz (spies evs)";
by (ftac A_trusts_AuthKey 1);
by (ftac Confidentiality_Kas 3);
by (ftac B_trusts_ServTicket 6);
by (blast_tac (claset() addSDs [Confidentiality_Tgs2]
			addDs [Says_Kas_message_form, A_trusts_K4, 
                               unique_ServKeys, unique_AuthKeys]) 9);
by (ALLGOALS assume_tac);
(*
The proof above is fast.  It can be done in one command in 50 secs:
by (blast_tac (claset() addDs [A_trusts_AuthKey, A_trusts_K4,
                               Says_Kas_message_form, B_trusts_ServTicket,
                               unique_ServKeys, unique_AuthKeys,
                               Confidentiality_Kas, 
                               Confidentiality_Tgs2]) 1);
*)
qed "Confidentiality_B";


(*Most general form -- only for refined model! *)
Goal "[| Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}  \
\          \\<in> parts (spies evs);                      \
\        ~ ExpirServ Tt evs;                         \
\        A \\<notin> bad;  B \\<notin> bad; B \\<noteq> Tgs; evs \\<in> kerberos |]            \
\     ==> Key ServKey \\<notin> analz (spies evs)";
by (blast_tac (claset() addDs [B_trusts_ServTicket_refined,
			       NotExpirServ_NotExpirAuth_refined, 
                               Confidentiality_Tgs2]) 1);
qed "Confidentiality_B_refined";


(********************** Authenticity theorems *****************************)

(***1. Session Keys authenticity: they originated with servers.***)

(*Authenticity of AuthKey for A: "A_trusts_AuthKey"*)

(*Authenticity of ServKey for A: "A_trusts_ServKey"*)
Goal "[| Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|} \
\          \\<in> parts (spies evs);                                     \
\        Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}   \
\          \\<in> parts (spies evs);                                        \
\        ~ ExpirAuth Tk evs; A \\<notin> bad; evs \\<in> kerberos |]         \
\==>Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|})\
\      \\<in> set evs";
by (blast_tac (claset() addDs [A_trusts_AuthKey, Confidentiality_Auth_A, 
                               A_trusts_K4_bis]) 1);
qed "A_trusts_ServKey"; 
(*Note: requires a temporal check*)


(*Authenticity of ServKey for B: "B_trusts_ServKey"*)

(***2. Parties authenticity: each party verifies "the identity of
       another party who generated some data" (quoted from Neuman & Ts'o).***)
       
       (*These guarantees don't assess whether two parties agree on 
         the same session key: sending a message containing a key
         doesn't a priori state knowledge of the key.***)

(*B checks authenticity of A: theorems "A_Authenticity", 
                                       "A_authenticity_refined" *)
Goal "[| Crypt ServKey {|Agent A, Number Ta|} \\<in> parts (spies evs);  \
\        Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, \
\                                    ServTicket|}) \\<in> set evs;       \
\        Key ServKey \\<notin> analz (spies evs);                \
\        A \\<notin> bad; B \\<notin> bad; evs \\<in> kerberos |]   \
\==> Says A B {|ServTicket, Crypt ServKey {|Agent A, Number Ta|}|} \\<in> set evs";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac kerberos.induct 1);
by (ftac Says_ticket_in_parts_spies 5);
by (ftac Says_ticket_in_parts_spies 7);
by (REPEAT (FIRSTGOAL analz_mono_contra_tac));
by (ALLGOALS (asm_simp_tac (simpset() addsimps [all_conj_distrib])));
by (Blast_tac 1);
(*K3*)
by (blast_tac (claset() addDs [A_trusts_AuthKey,
                               Says_Kas_message_form, 
                               Says_Tgs_message_form]) 1);
(*K4*)
by (force_tac (claset() addSDs [Crypt_imp_keysFor], simpset()) 1); 
(*K5*)
by (blast_tac (claset() addDs [Key_unique_SesKey]) 1);
qed "Says_Auth";

(*The second assumption tells B what kind of key ServKey is.*)
Goal "[| Crypt ServKey {|Agent A, Number Ta|} \\<in> parts (spies evs);     \
\        Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}       \
\          \\<in> parts (spies evs);                                         \
\        Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}  \ 
\          \\<in> parts (spies evs);                                          \
\        Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}  \
\          \\<in> parts (spies evs);                                            \
\        ~ ExpirServ Tt evs; ~ ExpirAuth Tk evs;  \
\        B \\<noteq> Tgs; A \\<notin> bad;  B \\<notin> bad;  evs \\<in> kerberos |]         \
\  ==> Says A B {|Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|},\
\                 Crypt ServKey {|Agent A, Number Ta|} |} \\<in> set evs";
by (blast_tac (claset() addIs [Says_Auth]
                        addDs [Confidentiality_B, Key_unique_SesKey,
                               B_trusts_ServKey]) 1);
qed "A_Authenticity";

(*Stronger form in the refined model*)
Goal "[| Crypt ServKey {|Agent A, Number Ta2|} \\<in> parts (spies evs);     \
\        Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}       \
\          \\<in> parts (spies evs);                                         \
\        ~ ExpirServ Tt evs;                                        \
\        B \\<noteq> Tgs; A \\<notin> bad;  B \\<notin> bad;  evs \\<in> kerberos |]         \
\  ==> Says A B {|Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|},\
\                 Crypt ServKey {|Agent A, Number Ta2|} |} \\<in> set evs";
by (blast_tac (claset() addDs [Confidentiality_B_refined, B_trusts_ServKey, 
                               Key_unique_SesKey]
                        addIs [Says_Auth]) 1);
qed "A_Authenticity_refined";


(*A checks authenticity of B: theorem "B_authenticity"*)

Goal "[| Crypt ServKey (Number Ta) \\<in> parts (spies evs);  \
\        Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, Number Tt, \
\                                    ServTicket|}) \\<in> set evs;       \
\        Key ServKey \\<notin> analz (spies evs);                \
\        A \\<notin> bad; B \\<notin> bad; evs \\<in> kerberos |]   \
\     ==> Says B A (Crypt ServKey (Number Ta)) \\<in> set evs";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac kerberos.induct 1);
by (ftac Says_ticket_in_parts_spies 5);
by (ftac Says_ticket_in_parts_spies 7);
by (REPEAT (FIRSTGOAL analz_mono_contra_tac));
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
by (force_tac (claset() addSDs [Crypt_imp_keysFor], simpset()) 1); 
by (Clarify_tac 1);
by (ftac Says_Tgs_message_form 1 THEN assume_tac 1);
by (Clarify_tac 1);  (*PROOF FAILED if omitted*)
by (blast_tac (claset() addDs [unique_CryptKey]) 1);
qed "Says_K6";

Goal "[| Crypt AuthKey {|Key ServKey, Agent B, T, ServTicket|}   \
\          \\<in> parts (spies evs);    \
\        Key AuthKey \\<notin> analz (spies evs); AuthKey \\<notin> range shrK;  \
\        evs \\<in> kerberos |]              \
\ ==> \\<exists>A. Says Tgs A (Crypt AuthKey {|Key ServKey, Agent B, T, ServTicket|})\
\             \\<in> set evs";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Blast_tac 1);
by (Blast_tac 1);
by (Blast_tac 1);
qed "K4_trustworthy";

Goal "[| Crypt ServKey (Number Ta) \\<in> parts (spies evs);           \
\        Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|} \
\          \\<in> parts (spies evs);                                        \ 
\        Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}\
\          \\<in> parts (spies evs);                                          \
\        ~ ExpirAuth Tk evs; ~ ExpirServ Tt evs;                         \
\        A \\<notin> bad;  B \\<notin> bad; B \\<noteq> Tgs; evs \\<in> kerberos |]            \
\     ==> Says B A (Crypt ServKey (Number Ta)) \\<in> set evs";
by (ftac A_trusts_AuthKey 1);
by (ftac Says_Kas_message_form 3);
by (ftac Confidentiality_Kas 4);
by (ftac K4_trustworthy 7);
by (Blast_tac 8);
by (etac exE 9);
by (ftac K4_imp_K2 9);
(*Yes the proof's a mess, but I don't know how to improve it.*)
by (blast_tac (claset() addDs [Key_unique_SesKey]
                        addSIs [Says_K6]
                        addDs [Confidentiality_Tgs1]) 10);
by (ALLGOALS assume_tac);
qed "B_Authenticity";


(***3. Parties' knowledge of session keys. A knows a session key if she
       used it to build a cipher.***)

Goal "[| Says B A (Crypt ServKey (Number Ta)) \\<in> set evs;           \
\        Key ServKey \\<notin> analz (spies evs);                          \
\        A \\<notin> bad;  B \\<notin> bad; B \\<noteq> Tgs; evs \\<in> kerberos |]            \
\     ==> B Issues A with (Crypt ServKey (Number Ta)) on evs";
by (simp_tac (simpset() addsimps [Issues_def]) 1);
by (rtac exI 1);
by (rtac conjI 1);
by (assume_tac 1);
by (Simp_tac 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac kerberos.induct 1);
by (ftac Says_ticket_in_parts_spies 5);
by (ftac Says_ticket_in_parts_spies 7);
by (REPEAT (FIRSTGOAL analz_mono_contra_tac));
by (ALLGOALS (asm_simp_tac (simpset() addsimps [all_conj_distrib])));
by (Blast_tac 1);
(*K6 requires numerous lemmas*)
by (asm_full_simp_tac (simpset() addsimps [takeWhile_tail]) 1);
by (blast_tac (claset() addDs [B_trusts_ServTicket,
                               impOfSubs parts_spies_takeWhile_mono,
                               impOfSubs parts_spies_evs_revD2]
                        addIs [Says_K6]) 1);
qed "B_Knows_B_Knows_ServKey_lemma";
(*Key ServKey \\<notin> analz (spies evs) could be relaxed by Confidentiality_B
  but this is irrelevant because B knows what he knows!                  *)

Goal "[| Says B A (Crypt ServKey (Number Ta)) \\<in> set evs;           \
\        Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}\
\           \\<in> parts (spies evs);\
\        Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}\
\           \\<in> parts (spies evs);\
\        Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}\
\          \\<in> parts (spies evs);     \
\        ~ ExpirServ Tt evs; ~ ExpirAuth Tk evs;              \
\        A \\<notin> bad;  B \\<notin> bad; B \\<noteq> Tgs; evs \\<in> kerberos |]            \
\     ==> B Issues A with (Crypt ServKey (Number Ta)) on evs";
by (blast_tac (claset() addSDs [Confidentiality_B,
	                       B_Knows_B_Knows_ServKey_lemma]) 1);
qed "B_Knows_B_Knows_ServKey";

Goal "[| Says B A (Crypt ServKey (Number Ta)) \\<in> set evs;           \
\        Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}\
\           \\<in> parts (spies evs);\
\        ~ ExpirServ Tt evs;            \
\        A \\<notin> bad;  B \\<notin> bad; B \\<noteq> Tgs; evs \\<in> kerberos |]            \
\     ==> B Issues A with (Crypt ServKey (Number Ta)) on evs";
by (blast_tac (claset() addSDs [Confidentiality_B_refined,
	                       B_Knows_B_Knows_ServKey_lemma]) 1);
qed "B_Knows_B_Knows_ServKey_refined";


Goal "[| Crypt ServKey (Number Ta) \\<in> parts (spies evs);           \
\        Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|} \
\          \\<in> parts (spies evs);                                        \ 
\        Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}\
\          \\<in> parts (spies evs);                                          \
\        ~ ExpirAuth Tk evs; ~ ExpirServ Tt evs;                         \
\        A \\<notin> bad;  B \\<notin> bad; B \\<noteq> Tgs; evs \\<in> kerberos |]            \
\     ==> B Issues A with (Crypt ServKey (Number Ta)) on evs";
by (blast_tac (claset() addSDs [B_Authenticity, Confidentiality_Serv_A,
                                B_Knows_B_Knows_ServKey_lemma]) 1);
qed "A_Knows_B_Knows_ServKey";

Goal "[| Says A Tgs     \
\            {|AuthTicket, Crypt AuthKey {|Agent A, Number Ta|}, Agent B|}\
\          \\<in> set evs;      \
\        A \\<notin> bad;  evs \\<in> kerberos |]         \
\     ==> \\<exists>Tk. Says Kas A (Crypt (shrK A) \
\                     {|Key AuthKey, Agent Tgs, Tk, AuthTicket|}) \
\                  \\<in> set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Blast_tac 1);
by (Blast_tac 1);
by (blast_tac (claset() addDs [Says_imp_spies RS parts.Inj RS 
			       A_trusts_AuthKey]) 1);
qed "K3_imp_K2";

Goal "[| Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}   \
\          \\<in> parts (spies evs);                    \
\        Says Kas A (Crypt (shrK A) \
\                    {|Key AuthKey, Agent Tgs, Tk, AuthTicket|}) \
\        \\<in> set evs;    \
\        Key AuthKey \\<notin> analz (spies evs);       \
\        B \\<noteq> Tgs; A \\<notin> bad;  B \\<notin> bad;  evs \\<in> kerberos |]         \
\  ==> Says Tgs A (Crypt AuthKey        \ 
\                    {|Key ServKey, Agent B, Number Tt, ServTicket|})  \
\        \\<in> set evs";      
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Blast_tac 1);
by (force_tac (claset() addSDs [Crypt_imp_keysFor], simpset()) 1); 
by (blast_tac (claset() addDs [Says_imp_spies RS parts.Inj RS parts.Fst RS
                               A_trusts_AuthTicket, unique_AuthKeys]) 1);
qed "K4_trustworthy'";

Goal "[| Says A B {|ServTicket, Crypt ServKey {|Agent A, Number Ta|}|} \
\          \\<in> set evs;       \
\        Key ServKey \\<notin> analz (spies evs);       \
\        B \\<noteq> Tgs; A \\<notin> bad;  B \\<notin> bad;  evs \\<in> kerberos |]         \
\  ==> A Issues B with (Crypt ServKey {|Agent A, Number Ta|}) on evs";
by (simp_tac (simpset() addsimps [Issues_def]) 1);
by (rtac exI 1);
by (rtac conjI 1);
by (assume_tac 1);
by (Simp_tac 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac kerberos.induct 1);
by (ftac Says_ticket_in_parts_spies 5);
by (ftac Says_ticket_in_parts_spies 7);
by (REPEAT (FIRSTGOAL analz_mono_contra_tac));
by (ALLGOALS Asm_simp_tac);
by (Clarify_tac 1);
(*K6*)
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [takeWhile_tail]) 1);
(*Level 15: case study necessary because the assumption doesn't state
  the form of ServTicket. The guarantee becomes stronger.*)
by (blast_tac (claset() addDs [Says_imp_spies RS analz.Inj RS analz_Decrypt',
                               K3_imp_K2, K4_trustworthy',
                               impOfSubs parts_spies_takeWhile_mono,
                               impOfSubs parts_spies_evs_revD2]
                        addIs [Says_Auth]) 1);
by (asm_full_simp_tac (simpset() addsimps [takeWhile_tail]) 1);
qed "A_Knows_A_Knows_ServKey_lemma";

Goal "[| Says A B {|ServTicket, Crypt ServKey {|Agent A, Number Ta|}|} \
\          \\<in> set evs;       \
\        Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}\
\          \\<in> parts (spies evs);\
\        Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}\
\          \\<in> parts (spies evs);                                        \
\        ~ ExpirAuth Tk evs; ~ ExpirServ Tt evs;\
\        B \\<noteq> Tgs; A \\<notin> bad;  B \\<notin> bad;  evs \\<in> kerberos |]         \
\  ==> A Issues B with (Crypt ServKey {|Agent A, Number Ta|}) on evs";
by (blast_tac (claset() addSDs [Confidentiality_Serv_A,
	                       A_Knows_A_Knows_ServKey_lemma]) 1);
qed "A_Knows_A_Knows_ServKey";

Goal "[| Crypt ServKey {|Agent A, Number Ta|} \\<in> parts (spies evs);     \
\        Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}       \
\          \\<in> parts (spies evs);                                         \
\        Crypt AuthKey {|Key ServKey, Agent B, Number Tt, ServTicket|}  \ 
\          \\<in> parts (spies evs);                                          \
\        Crypt (shrK A) {|Key AuthKey, Agent Tgs, Number Tk, AuthTicket|}  \
\          \\<in> parts (spies evs);                                            \
\        ~ ExpirServ Tt evs; ~ ExpirAuth Tk evs;  \
\        B \\<noteq> Tgs; A \\<notin> bad;  B \\<notin> bad;  evs \\<in> kerberos |]         \
\  ==> A Issues B with (Crypt ServKey {|Agent A, Number Ta|}) on evs";
by (blast_tac (claset() addDs [A_Authenticity, Confidentiality_B,
	                       A_Knows_A_Knows_ServKey_lemma]) 1);
qed "B_Knows_A_Knows_ServKey";


Goal "[| Crypt ServKey {|Agent A, Number Ta|} \\<in> parts (spies evs);     \
\        Crypt (shrK B) {|Agent A, Agent B, Key ServKey, Number Tt|}       \
\          \\<in> parts (spies evs);                                         \
\        ~ ExpirServ Tt evs;                                        \
\        B \\<noteq> Tgs; A \\<notin> bad;  B \\<notin> bad;  evs \\<in> kerberos |]         \
\  ==> A Issues B with (Crypt ServKey {|Agent A, Number Ta|}) on evs";
by (blast_tac (claset() addDs [A_Authenticity_refined, 
                               Confidentiality_B_refined,
	                       A_Knows_A_Knows_ServKey_lemma]) 1);
qed "B_Knows_A_Knows_ServKey_refined";
