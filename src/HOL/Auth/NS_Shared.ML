(*  Title:      HOL/Auth/NS_Shared
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "ns_shared" for Needham-Schroeder Shared-Key protocol.

From page 247 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

open NS_Shared;

set proof_timing;
HOL_quantifiers := false;

AddEs spies_partsEs;
AddDs [impOfSubs analz_subset_parts];
AddDs [impOfSubs Fake_parts_insert];


(*A "possibility property": there are traces that reach the end*)
goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]       \
\        ==> EX N K. EX evs: ns_shared.               \
\               Says A B (Crypt K {|Nonce N, Nonce N|}) : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (ns_shared.Nil RS ns_shared.NS1 RS ns_shared.NS2 RS 
          ns_shared.NS3 RS ns_shared.NS4 RS ns_shared.NS5) 2);
by possibility_tac;
result();

goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]       \
\        ==> EX evs: ns_shared.          \
\               Says A B (Crypt ?K {|Nonce ?N, Nonce ?N|}) : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (ns_shared.Nil RS ns_shared.NS1 RS ns_shared.NS2 RS 
          ns_shared.NS3 RS ns_shared.NS4 RS ns_shared.NS5) 2);
by possibility_tac;

(**** Inductive proofs about ns_shared ****)

(*Nobody sends themselves messages*)
goal thy "!!evs. evs : ns_shared ==> ALL A X. Says A A X ~: set evs";
by (etac ns_shared.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];

(*For reasoning about the encrypted portion of message NS3*)
goal thy "!!evs. Says S A (Crypt KA {|N, B, K, X|}) : set evs \
\                ==> X : parts (spies evs)";
by (Blast_tac 1);
qed "NS3_msg_in_parts_spies";
                              
goal thy
    "!!evs. Says Server A (Crypt (shrK A) {|NA, B, K, X|}) : set evs \
\           ==> K : parts (spies evs)";
by (Blast_tac 1);
qed "Oops_parts_spies";

(*For proving the easier theorems about X ~: parts (spies evs).*)
fun parts_induct_tac i = 
  EVERY [etac ns_shared.induct i,
	 REPEAT (FIRSTGOAL analz_mono_contra_tac),
	 forward_tac [Oops_parts_spies] (i+7),
	 forward_tac [NS3_msg_in_parts_spies] (i+4),
	 prove_simple_subgoals_tac i];


(** Theorems of the form X ~: parts (spies evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's shared key! (unless it's bad at start)*)
goal thy 
 "!!evs. evs : ns_shared ==> (Key (shrK A) : parts (spies evs)) = (A : bad)";
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

goal thy 
 "!!evs. evs : ns_shared ==> (Key (shrK A) : analz (spies evs)) = (A : bad)";
by (Auto_tac());
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

AddSDs [Spy_see_shrK RSN (2, rev_iffD1), 
	Spy_analz_shrK RSN (2, rev_iffD1)];


(*Nobody can have used non-existent keys!*)
goal thy "!!evs. evs : ns_shared ==>      \
\         Key K ~: used evs --> K ~: keysFor (parts (spies evs))";
by (parts_induct_tac 1);
(*Fake*)
by (best_tac
      (claset() addSDs [impOfSubs (parts_insert_subset_Un RS keysFor_mono)]
                addIs  [impOfSubs analz_subset_parts]
                addDs  [impOfSubs (analz_subset_parts RS keysFor_mono)]
                addss  (simpset())) 1);
(*NS2, NS4, NS5*)
by (ALLGOALS (Blast_tac));
qed_spec_mp "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];


(** Lemmas concerning the form of items passed in messages **)

(*Describes the form of K, X and K' when the Server sends this message.*)
goal thy 
 "!!evs. [| Says Server A (Crypt K' {|N, Agent B, Key K, X|}) : set evs; \
\           evs : ns_shared |]                           \
\        ==> K ~: range shrK &                           \
\            X = (Crypt (shrK B) {|Key K, Agent A|}) &   \
\            K' = shrK A";
by (etac rev_mp 1);
by (etac ns_shared.induct 1);
by (Auto_tac());
qed "Says_Server_message_form";


(*If the encrypted message appears then it originated with the Server*)
goal thy
 "!!evs. [| Crypt (shrK A) {|NA, Agent B, Key K, X|} : parts (spies evs); \
\           A ~: bad;  evs : ns_shared |]                                 \
\         ==> Says Server A (Crypt (shrK A) {|NA, Agent B, Key K, X|})    \
\               : set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Blast_tac 1);
qed "A_trusts_NS2";


goal thy
 "!!evs. [| Crypt (shrK A) {|NA, Agent B, Key K, X|} : parts (spies evs); \
\           A ~: bad;  evs : ns_shared |]                                 \
\         ==> K ~: range shrK &  X = (Crypt (shrK B) {|Key K, Agent A|})";
by (blast_tac (claset() addSDs [A_trusts_NS2, Says_Server_message_form]) 1);
qed "cert_A_form";


(*EITHER describes the form of X when the following message is sent, 
  OR     reduces it to the Fake case.
  Use Says_Server_message_form if applicable.*)
goal thy 
 "!!evs. [| Says S A (Crypt (shrK A) {|Nonce NA, Agent B, Key K, X|})      \
\              : set evs;                                                  \
\           evs : ns_shared |]                                             \
\        ==> (K ~: range shrK & X = (Crypt (shrK B) {|Key K, Agent A|}))   \
\            | X : analz (spies evs)";
by (case_tac "A : bad" 1);
by (fast_tac (claset() addSDs [Says_imp_spies RS analz.Inj]
                       addss (simpset())) 1);
by (blast_tac (claset() addSDs [cert_A_form]) 1);
qed "Says_S_message_form";


(*For proofs involving analz.*)
val analz_spies_tac = 
    forward_tac [Says_Server_message_form] 8 THEN
    forward_tac [Says_S_message_form] 5 THEN 
    REPEAT_FIRST (eresolve_tac [asm_rl, conjE, disjE] ORELSE' hyp_subst_tac);


(****
 The following is to prove theorems of the form

  Key K : analz (insert (Key KAB) (spies evs)) ==>
  Key K : analz (spies evs)

 A more general formula must be proved inductively.
****)


(*NOT useful in this form, but it says that session keys are not used
  to encrypt messages containing other keys, in the actual protocol.
  We require that agents should behave like this subsequently also.*)
goal thy 
 "!!evs. [| evs : ns_shared;  Kab ~: range shrK |] ==>  \
\           (Crypt KAB X) : parts (spies evs) &         \
\           Key K : parts {X} --> Key K : parts (spies evs)";
by (parts_induct_tac 1);
(*Fake*)
by (blast_tac (claset() addSEs partsEs
                        addDs [impOfSubs parts_insert_subset_Un]) 1);
(*Base, NS4 and NS5*)
by (Auto_tac());
result();


(** Session keys are not used to encrypt other session keys **)

(*The equality makes the induction hypothesis easier to apply*)
goal thy  
 "!!evs. evs : ns_shared ==>                             \
\  ALL K KK. KK <= Compl (range shrK) -->                \
\            (Key K : analz (Key``KK Un (spies evs))) =  \
\            (K : KK | Key K : analz (spies evs))";
by (etac ns_shared.induct 1);
by analz_spies_tac;
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_freshK_lemma));
(*Takes 9 secs*)
by (ALLGOALS (asm_simp_tac analz_image_freshK_ss));
(*Fake*) 
by (spy_analz_tac 1);
qed_spec_mp "analz_image_freshK";


goal thy
 "!!evs. [| evs : ns_shared;  KAB ~: range shrK |] ==>  \
\        Key K : analz (insert (Key KAB) (spies evs)) = \
\        (K = KAB | Key K : analz (spies evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(** The session key K uniquely identifies the message **)

goal thy 
 "!!evs. evs : ns_shared ==>                                               \
\      EX A' NA' B' X'. ALL A NA B X.                                      \
\       Says Server A (Crypt (shrK A) {|NA, Agent B, Key K, X|}) : set evs \
\       -->         A=A' & NA=NA' & B=B' & X=X'";
by (etac ns_shared.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [all_conj_distrib])));
by Safe_tac;
(*NS3*)
by (ex_strip_tac 2);
by (Blast_tac 2);
(*NS2: it can't be a new key*)
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
by (Blast_tac 1);
val lemma = result();

(*In messages of this form, the session key uniquely identifies the rest*)
goal thy 
 "!!evs. [| Says Server A                                               \
\             (Crypt (shrK A) {|NA, Agent B, Key K, X|}) : set evs;     \ 
\           Says Server A'                                              \
\             (Crypt (shrK A') {|NA', Agent B', Key K, X'|}) : set evs; \
\           evs : ns_shared |] ==> A=A' & NA=NA' & B=B' & X = X'";
by (prove_unique_tac lemma 1);
qed "unique_session_keys";


(** Crucial secrecy property: Spy does not see the keys sent in msg NS2 **)

goal thy 
 "!!evs. [| A ~: bad;  B ~: bad;  evs : ns_shared |]                   \
\        ==> Says Server A                                             \
\              (Crypt (shrK A) {|NA, Agent B, Key K,                   \
\                                Crypt (shrK B) {|Key K, Agent A|}|})  \
\             : set evs -->                                            \
\        (ALL NB. Says A Spy {|NA, NB, Key K|} ~: set evs) -->         \
\        Key K ~: analz (spies evs)";
by (etac ns_shared.induct 1);
by analz_spies_tac;
by (ALLGOALS 
    (asm_simp_tac 
     (simpset() addsimps ([analz_insert_eq, analz_insert_freshK] @ 
			  pushes @ expand_ifs))));
(*Oops*)
by (blast_tac (claset() addDs [unique_session_keys]) 5);
(*NS3, replay sub-case*) 
by (Blast_tac 4);
(*NS2*)
by (Blast_tac 2);
(*Fake*) 
by (spy_analz_tac 1);
(*NS3, Server sub-case*) (**LEVEL 6 **)
by (clarify_tac (claset() delrules [impCE]) 1);
by (forward_tac [Says_imp_spies RS parts.Inj RS A_trusts_NS2] 1);
by (assume_tac 2);
by (blast_tac (claset() addDs [Says_imp_spies RS analz.Inj RS
			       Crypt_Spy_analz_bad]) 1);
by (blast_tac (claset() addDs [unique_session_keys]) 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);


(*Final version: Server's message in the most abstract form*)
goal thy 
 "!!evs. [| Says Server A                                        \
\              (Crypt K' {|NA, Agent B, Key K, X|}) : set evs;   \
\           ALL NB. Says A Spy {|NA, NB, Key K|} ~: set evs;     \
\           A ~: bad;  B ~: bad;  evs : ns_shared                \
\        |] ==> Key K ~: analz (spies evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (blast_tac (claset() addSDs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


(**** Guarantees available at various stages of protocol ***)

A_trusts_NS2 RS Spy_not_see_encrypted_key;


(*If the encrypted message appears then it originated with the Server*)
goal thy
 "!!evs. [| Crypt (shrK B) {|Key K, Agent A|} : parts (spies evs);     \
\           B ~: bad;  evs : ns_shared |]                              \
\         ==> EX NA. Says Server A                                     \
\              (Crypt (shrK A) {|NA, Agent B, Key K,                   \
\                                Crypt (shrK B) {|Key K, Agent A|}|})  \
\             : set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "B_trusts_NS3";


goal thy
 "!!evs. [| Crypt K (Nonce NB) : parts (spies evs);                   \
\           Says Server A (Crypt (shrK A) {|NA, Agent B, Key K, X|})  \
\              : set evs;                                             \
\           Key K ~: analz (spies evs);                               \
\           evs : ns_shared |]                  \
\        ==> Says B A (Crypt K (Nonce NB)) : set evs";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*NS3*)
by (Blast_tac 3);
by (Blast_tac 1);
(*NS2: contradiction from the assumptions  
  Key K ~: used evs2  and Crypt K (Nonce NB) : parts (spies evs2) *)
by (blast_tac (claset() addSEs [new_keys_not_used RSN (2,rev_notE)]
			addSDs [Crypt_imp_keysFor]) 1);
(**LEVEL 7**)
(*NS4*)
by (Clarify_tac 1);
by (not_bad_tac "Ba" 1);
by (blast_tac (claset() addDs [B_trusts_NS3, unique_session_keys]) 1);
qed "A_trusts_NS4_lemma";


(*This version no longer assumes that K is secure*)
goal thy
 "!!evs. [| Crypt K (Nonce NB) : parts (spies evs);                   \
\           Crypt (shrK A) {|NA, Agent B, Key K, X|} : parts (spies evs); \
\           ALL NB. Says A Spy {|NA, NB, Key K|} ~: set evs;          \
\           A ~: bad;  B ~: bad;  evs : ns_shared |]                  \
\        ==> Says B A (Crypt K (Nonce NB)) : set evs";
by (blast_tac (claset() addSIs [A_trusts_NS2, A_trusts_NS4_lemma]
	         addSEs [Spy_not_see_encrypted_key RSN (2,rev_notE)]) 1);
qed "A_trusts_NS4";


(*If the session key has been used in NS4 then somebody has forwarded
  component X in some instance of NS4.  Perhaps an interesting property, 
  but not needed (after all) for the proofs below.*)
goal thy
 "!!evs. [| Crypt K (Nonce NB) : parts (spies evs);     \
\           Says Server A (Crypt (shrK A) {|NA, Agent B, Key K, X|})  \
\             : set evs;                                              \
\           Key K ~: analz (spies evs);                               \
\           evs : ns_shared |]                              \
\        ==> EX A'. Says A' B X : set evs";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [ex_disj_distrib])));
by (ALLGOALS Clarify_tac);
by (Blast_tac 1);
(**LEVEL 7**)
(*NS2*)
by (blast_tac (claset() addSEs [new_keys_not_used RSN (2,rev_notE)]
			addSDs [Crypt_imp_keysFor]) 1);
(*NS4*)
by (not_bad_tac "Ba" 1);
by (Asm_full_simp_tac 1);
by (forward_tac [Says_imp_spies RS parts.Inj RS B_trusts_NS3] 1);
by (ALLGOALS Clarify_tac);
by (blast_tac (claset() addDs [unique_session_keys]) 1);
qed "NS4_implies_NS3";


goal thy
 "!!evs. [| B ~: bad;  evs : ns_shared |]                              \
\        ==> Key K ~: analz (spies evs) -->                            \
\            Says Server A                                     \
\              (Crypt (shrK A) {|NA, Agent B, Key K,                   \
\                                Crypt (shrK B) {|Key K, Agent A|}|})  \
\             : set evs -->         \
\            Says B A (Crypt K (Nonce NB))  : set evs -->  \
\            Crypt K {|Nonce NB, Nonce NB|} : parts (spies evs) --> \
\            Says A B (Crypt K {|Nonce NB, Nonce NB|}) : set evs";
by (parts_induct_tac 1);
(*NS4*)
by (Blast_tac 4);
(*NS3*)
by (blast_tac (claset() addSDs [cert_A_form]) 3);
(*NS2*)
by (blast_tac (claset() addSEs [new_keys_not_used RSN (2,rev_notE)]
			addSDs [Crypt_imp_keysFor]) 2);
by (Blast_tac 1);
(**LEVEL 5**)
(*NS5*)
by (Clarify_tac 1);
by (not_bad_tac "Aa" 1);
by (blast_tac (claset() addDs [A_trusts_NS2, unique_session_keys]) 1);
val lemma = result();


(*Very strong Oops condition reveals protocol's weakness*)
goal thy
 "!!evs. [| Crypt K {|Nonce NB, Nonce NB|} : parts (spies evs);      \
\           Says B A (Crypt K (Nonce NB))  : set evs;                \
\           Crypt (shrK B) {|Key K, Agent A|} : parts (spies evs);   \
\           ALL NA NB. Says A Spy {|NA, NB, Key K|} ~: set evs;      \
\           A ~: bad;  B ~: bad;  evs : ns_shared |]                 \
\        ==> Says A B (Crypt K {|Nonce NB, Nonce NB|}) : set evs";
by (dtac B_trusts_NS3 1);
by (ALLGOALS Clarify_tac);
by (blast_tac (claset() addSIs [normalize_thm [RSspec, RSmp] lemma]
	         addSEs [Spy_not_see_encrypted_key RSN (2,rev_notE)]) 1);
qed "B_trusts_NS5";
