(*  Title:      HOL/Auth/Kerberos_BAN
    ID:         $Id$
    Author:     Giampaolo Bella, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Kerberos protocol, BAN version.

From page 251 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)

  Confidentiality (secrecy) and authentication properties rely on 
  temporal checks: strong guarantees in a little abstracted - but
  very realistic - model (see .thy).

Tidied by lcp.
*)

AddEs spies_partsEs;
AddDs [impOfSubs analz_subset_parts];
AddDs [impOfSubs Fake_parts_insert];

AddIffs [SesKeyLife_LB, AutLife_LB];


(*A "possibility property": there are traces that reach the end.*)
Goal "EX Timestamp K. EX evs: kerberos_ban.    \
\            Says B A (Crypt K (Number Timestamp)) \
\                 : set evs";
by (cut_facts_tac [SesKeyLife_LB] 1);
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (kerberos_ban.Nil RS kerberos_ban.Kb1 RS kerberos_ban.Kb2 RS 
          kerberos_ban.Kb3 RS kerberos_ban.Kb4) 2);
by possibility_tac;
by (ALLGOALS Asm_simp_tac);
result();



(**** Inductive proofs about kerberos_ban ****)

(*Forwarding Lemma for reasoning about the encrypted portion of message Kb3*)
Goal "Says S A (Crypt KA {|Timestamp, B, K, X|}) : set evs \
\             ==> X : parts (spies evs)";
by (Blast_tac 1);
qed "Kb3_msg_in_parts_spies";
                              
Goal "Says Server A (Crypt (shrK A) {|Timestamp, B, K, X|}) : set evs \
\        ==> K : parts (spies evs)";
by (Blast_tac 1);
qed "Oops_parts_spies";

(*For proving the easier theorems about X ~: parts (spies evs).*)
fun parts_induct_tac i = 
    etac kerberos_ban.induct i  THEN 
    ftac Oops_parts_spies (i+6)  THEN
    ftac Kb3_msg_in_parts_spies (i+4)     THEN
    prove_simple_subgoals_tac i;


(*Spy never sees another agent's shared key! (unless it's bad at start)*)
Goal "evs : kerberos_ban ==> (Key (shrK A) : parts (spies evs)) = (A : bad)";
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];


Goal "evs : kerberos_ban ==> (Key (shrK A) : analz (spies evs)) = (A : bad)";
by Auto_tac;
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

Goal  "[| Key (shrK A) : parts (spies evs);       \
\               evs : kerberos_ban |] ==> A:bad";
by (blast_tac (claset() addDs [Spy_see_shrK]) 1);
qed "Spy_see_shrK_D";

bind_thm ("Spy_analz_shrK_D", analz_subset_parts RS subsetD RS Spy_see_shrK_D);
AddSDs [Spy_see_shrK_D, Spy_analz_shrK_D];


(*Nobody can have used non-existent keys!*)
Goal "evs : kerberos_ban ==>      \
\      Key K ~: used evs --> K ~: keysFor (parts (spies evs))";
by (parts_induct_tac 1);
(*Fake*)
by (blast_tac (claset() addSDs [keysFor_parts_insert]) 1);
(*Kb2, Kb3, Kb4*)
by (ALLGOALS Blast_tac);
qed_spec_mp "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];


(** Lemmas concerning the form of items passed in messages **)

(*Describes the form of K, X and K' when the Server sends this message.*)
Goal "[| Says Server A (Crypt K' {|Number Ts, Agent B, Key K, X|})  \
\        : set evs; evs : kerberos_ban |]                           \
\     ==> K ~: range shrK &                                         \
\         X = (Crypt (shrK B) {|Number Ts, Agent A, Key K|}) &      \
\         K' = shrK A";
by (etac rev_mp 1);
by (etac kerberos_ban.induct 1);
by Auto_tac;
qed "Says_Server_message_form";


(*If the encrypted message appears then it originated with the Server
  PROVIDED that A is NOT compromised!

  This shows implicitly the FRESHNESS OF THE SESSION KEY to A
*)
Goal "[| Crypt (shrK A) {|Number Ts, Agent B, Key K, X|} \
\          : parts (spies evs);                          \
\        A ~: bad;  evs : kerberos_ban |]                \
\      ==> Says Server A (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|}) \
\            : set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Blast_tac 1);
qed "A_trusts_K_by_Kb2";


(*If the TICKET appears then it originated with the Server*)
(*FRESHNESS OF THE SESSION KEY to B*)
Goal "[| Crypt (shrK B) {|Number Ts, Agent A, Key K|} : parts (spies evs); \
\        B ~: bad;  evs : kerberos_ban |]                        \
\      ==> Says Server A                                         \
\           (Crypt (shrK A) {|Number Ts, Agent B, Key K,                   \
\                         Crypt (shrK B) {|Number Ts, Agent A, Key K|}|})  \
\          : set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Blast_tac 1);
qed "B_trusts_K_by_Kb3";


(*EITHER describes the form of X when the following message is sent, 
  OR     reduces it to the Fake case.
  Use Says_Server_message_form if applicable.*)
Goal "[| Says S A (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|})     \
\           : set evs;                                                  \
\        evs : kerberos_ban |]                                          \
\==> (K ~: range shrK & X = (Crypt (shrK B) {|Number Ts, Agent A, Key K|}))\
\         | X : analz (spies evs)";
by (case_tac "A : bad" 1);
by (fast_tac (claset() addSDs [Says_imp_spies RS analz.Inj]
                      addss (simpset())) 1);
by (forward_tac [Says_imp_spies RS parts.Inj] 1);
by (blast_tac (claset() addSDs [A_trusts_K_by_Kb2, 
				Says_Server_message_form]) 1);
qed "Says_S_message_form";


(*For proofs involving analz.*)
val analz_spies_tac = 
    ftac Says_Server_message_form 7 THEN
    ftac Says_S_message_form 5 THEN 
    REPEAT_FIRST (eresolve_tac [asm_rl, conjE, disjE] ORELSE' hyp_subst_tac);


(****
 The following is to prove theorems of the form

  Key K : analz (insert (Key KAB) (spies evs)) ==>
  Key K : analz (spies evs)

 A more general formula must be proved inductively.

****)


(** Session keys are not used to encrypt other session keys **)

Goal "evs : kerberos_ban ==>                          \
\  ALL K KK. KK <= - (range shrK) -->                 \
\         (Key K : analz (Key`KK Un (spies evs))) =  \
\         (K : KK | Key K : analz (spies evs))";
by (etac kerberos_ban.induct 1);
by analz_spies_tac;
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_freshK_lemma));
(*Takes 5 secs*)
by (ALLGOALS (asm_simp_tac analz_image_freshK_ss));
(*Fake*) 
by (spy_analz_tac 1);
qed_spec_mp "analz_image_freshK";


Goal "[| evs : kerberos_ban;  KAB ~: range shrK |] ==>     \
\     Key K : analz (insert (Key KAB) (spies evs)) =       \
\     (K = KAB | Key K : analz (spies evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(** The session key K uniquely identifies the message **)

Goal "evs : kerberos_ban ==>                                         \
\   EX A' Ts' B' X'. ALL A Ts B X.                                   \
\    Says Server A (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|}) \
\          : set evs \
\    -->         A=A' & Ts=Ts' & B=B' & X=X'";
by (etac kerberos_ban.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [all_conj_distrib])));
by Safe_tac;
(*Kb2: it can't be a new key*)
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
by (blast_tac (claset() delrules [conjI]) 1);
val lemma = result();

(*In messages of this form, the session key uniquely identifies the rest*)
Goal "[| Says Server A                                    \
\          (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|}) : set evs; \ 
\        Says Server A'                                   \
\         (Crypt (shrK A') {|Number Ts', Agent B', Key K, X'|}) : set evs;\
\        evs : kerberos_ban |] ==> A=A' & Ts=Ts' & B=B' & X = X'";
by (prove_unique_tac lemma 1);
qed "unique_session_keys";


(** Lemma: the session key sent in msg Kb2 would be EXPIRED
    if the spy could see it!
**)

Goal "[| A ~: bad;  B ~: bad;  evs : kerberos_ban |]           \
\ ==> Says Server A                                            \
\         (Crypt (shrK A) {|Number Ts, Agent B, Key K,         \
\                           Crypt (shrK B) {|Number Ts, Agent A, Key K|}|})\
\        : set evs -->                                         \
\     Key K : analz (spies evs) --> Expired Ts evs"; 
by (etac kerberos_ban.induct 1);
by analz_spies_tac;
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [less_SucI, analz_insert_eq, 
				       analz_insert_freshK]
		                      @ pushes)));
(*Oops*)
by (blast_tac (claset() addDs [unique_session_keys] addIs [less_SucI]) 4);
(*Kb2*)
by (blast_tac (claset() addIs [parts_insertI, less_SucI]) 2);
(*Fake*) 
by (spy_analz_tac 1);
(**LEVEL 6 **)
(*Kb3*)
by (case_tac "Aa : bad" 1);
by (blast_tac (claset() addDs [A_trusts_K_by_Kb2, unique_session_keys]) 2);
by (blast_tac (claset() addDs [Says_imp_spies RS analz.Inj,
                               Crypt_Spy_analz_bad, analz.Fst, analz.Snd]
                        addIs [less_SucI]) 1);
qed_spec_mp "lemma2";


(** CONFIDENTIALITY for the SERVER:
                     Spy does not see the keys sent in msg Kb2 
                     as long as they have NOT EXPIRED
**)
Goal "[| Says Server A                                           \
\         (Crypt K' {|Number T, Agent B, Key K, X|}) : set evs;  \
\        ~ Expired T evs;                                        \
\        A ~: bad;  B ~: bad;  evs : kerberos_ban                \
\     |] ==> Key K ~: analz (spies evs)";
by (ftac Says_Server_message_form 1 THEN assume_tac 1);
by (blast_tac (claset() addIs [lemma2]) 1);
qed "Confidentiality_S";

(**** THE COUNTERPART OF CONFIDENTIALITY 
      [|...; Expired Ts evs; ...|] ==> Key K : analz (spies evs)
      WOULD HOLD ONLY IF AN OOPS OCCURRED! ---> Nothing to prove!   ****)


(** CONFIDENTIALITY for ALICE: **)
(** Also A_trusts_K_by_Kb2 RS Confidentiality_S **)
Goal "[| Crypt (shrK A) {|Number T, Agent B, Key K, X|} : parts (spies evs);\
\        ~ Expired T evs;          \
\        A ~: bad;  B ~: bad;  evs : kerberos_ban                \
\     |] ==> Key K ~: analz (spies evs)";
by (blast_tac (claset() addSDs [A_trusts_K_by_Kb2, Confidentiality_S]) 1);
qed "Confidentiality_A";


(** CONFIDENTIALITY for BOB: **)
(** Also B_trusts_K_by_Kb3 RS Confidentiality_S **)
Goal "[| Crypt (shrK B) {|Number Tk, Agent A, Key K|} \
\         : parts (spies evs);              \
\       ~ Expired Tk evs;          \
\       A ~: bad;  B ~: bad;  evs : kerberos_ban                \
\     |] ==> Key K ~: analz (spies evs)";             
by (blast_tac (claset() addSDs [B_trusts_K_by_Kb3, 
                                Confidentiality_S]) 1);
qed "Confidentiality_B";


Goal "[| B ~: bad;  evs : kerberos_ban |]                        \
\     ==> Key K ~: analz (spies evs) -->                    \
\         Says Server A (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|}) \
\         : set evs -->                                             \
\         Crypt K (Number Ta) : parts (spies evs) -->        \
\         Says B A (Crypt K (Number Ta)) : set evs";
by (etac kerberos_ban.induct 1);
by (ftac Says_S_message_form 5 THEN assume_tac 5);     
by (dtac Kb3_msg_in_parts_spies 5);
by (ftac Oops_parts_spies 7);
by (REPEAT (FIRSTGOAL analz_mono_contra_tac));
by (ALLGOALS (asm_simp_tac (simpset() addsimps [all_conj_distrib])));
(**LEVEL 6**)
by (Blast_tac 1);
by (Clarify_tac 1);
(*
Subgoal 1: contradiction from the assumptions  
Key K ~: used evs2  and Crypt K (Number Ta) : parts (spies evs2)
*)
by (dtac Crypt_imp_invKey_keysFor 1);
by (Asm_full_simp_tac 1);
(* the two tactics above detect the contradiction*)
by (case_tac "Ba : bad" 1);  (*splits up the subgoal by the stated case*)
by (blast_tac (claset() addDs [Says_imp_spies RS parts.Inj RS parts.Fst RS 
                              B_trusts_K_by_Kb3, 
			      unique_session_keys]) 2);
by (blast_tac (claset() addDs [Says_imp_spies RS analz.Inj RS analz.Fst RS 
			      Crypt_Spy_analz_bad]) 1);
val lemma_B = result();


(*AUTHENTICATION OF B TO A*)
Goal "[| Crypt K (Number Ta) : parts (spies evs);           \
\        Crypt (shrK A) {|Number Ts, Agent B, Key K, X|}    \
\        : parts (spies evs);                               \
\        ~ Expired Ts evs;                                  \
\        A ~: bad;  B ~: bad;  evs : kerberos_ban |]        \
\     ==> Says B A (Crypt K (Number Ta)) : set evs";
by (blast_tac (claset() addSDs [A_trusts_K_by_Kb2]
                        addSIs [lemma_B RS mp RS mp RS mp]
                        addSEs [Confidentiality_S RSN (2,rev_notE)]) 1);
qed "Authentication_B";


Goal "[| A ~: bad; B ~: bad; evs : kerberos_ban |]      ==>         \ 
\        Key K ~: analz (spies evs) -->         \
\        Says Server A (Crypt (shrK A) {|Number Ts, Agent B, Key K, X|})  \
\        : set evs -->  \
\         Crypt K {|Agent A, Number Ta|} : parts (spies evs) -->\
\        Says A B {|X, Crypt K {|Agent A, Number Ta|}|}  \
\            : set evs";
by (etac kerberos_ban.induct 1);
by (ftac Says_S_message_form 5 THEN assume_tac 5);     
by (ftac Kb3_msg_in_parts_spies 5);
by (ftac Oops_parts_spies 7);
by (REPEAT (FIRSTGOAL analz_mono_contra_tac));
by (ALLGOALS (asm_simp_tac (simpset() addsimps [all_conj_distrib])));
(**LEVEL 6**)
by (Blast_tac 1);
by (Clarify_tac 1);
by (dtac Crypt_imp_invKey_keysFor 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addDs [A_trusts_K_by_Kb2, unique_session_keys]) 1);
val lemma_A = result();


(*AUTHENTICATION OF A TO B*)
Goal "[| Crypt K {|Agent A, Number Ta|} : parts (spies evs);  \
\        Crypt (shrK B) {|Number Ts, Agent A, Key K|}         \
\        : parts (spies evs);                                 \
\        ~ Expired Ts evs;                                    \
\        A ~: bad;  B ~: bad;  evs : kerberos_ban |]          \
\     ==> Says A B {|Crypt (shrK B) {|Number Ts, Agent A, Key K|}, \    
\                    Crypt K {|Agent A, Number Ta|}|} : set evs";
by (blast_tac (claset() addSDs [B_trusts_K_by_Kb3]
                        addSIs [lemma_A RS mp RS mp RS mp]
                        addSEs [Confidentiality_S RSN (2,rev_notE)]) 1);
qed "Authentication_A";
