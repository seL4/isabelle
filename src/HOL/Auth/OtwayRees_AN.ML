(*  Title:      HOL/Auth/OtwayRees_AN
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "otway" for the Otway-Rees protocol.

Abadi-Needham version: minimal encryption, explicit messages

From page 11 of
  Abadi and Needham.  Prudent Engineering Practice for Cryptographic Protocols.
  IEEE Trans. SE 22 (1), 1996
*)

AddDs  [Says_imp_knows_Spy RS parts.Inj, parts.Body];
AddDs  [impOfSubs analz_subset_parts, impOfSubs Fake_parts_insert];


(*A "possibility property": there are traces that reach the end*)
Goal "[| B ~= Server |]   \
\     ==> EX K. EX NA. EX evs: otway.                                      \
\          Says B A (Crypt (shrK A) {|Nonce NA, Agent A, Agent B, Key K|}) \
\            : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (otway.Nil RS 
          otway.OR1 RS otway.Reception RS
          otway.OR2 RS otway.Reception RS 
          otway.OR3 RS otway.Reception RS otway.OR4) 2);
by possibility_tac;
result();

Goal "[| Gets B X : set evs; evs : otway |] ==> EX A. Says A B X : set evs";
by (etac rev_mp 1);
by (etac otway.induct 1);
by Auto_tac;
qed"Gets_imp_Says";

(*Must be proved separately for each protocol*)
Goal "[| Gets B X : set evs; evs : otway |]  ==> X : knows Spy evs";
by (blast_tac (claset() addSDs [Gets_imp_Says, Says_imp_knows_Spy]) 1);
qed"Gets_imp_knows_Spy";
AddDs [Gets_imp_knows_Spy RS parts.Inj];


(**** Inductive proofs about otway ****)

(** For reasoning about the encrypted portion of messages **)

Goal "[| Gets B {|X, Crypt(shrK B) X'|} : set evs;  evs : otway |] ==> \
\          X : analz (knows Spy evs)";
by (blast_tac (claset() addSDs [Gets_imp_knows_Spy RS analz.Inj]) 1);
qed "OR4_analz_knows_Spy";

Goal "Says Server B {|X, Crypt K' {|NB, a, Agent B, K|}|} : set evs \
\     ==> K : parts (knows Spy evs)";
by (Blast_tac 1);
qed "Oops_parts_knows_Spy";

bind_thm ("OR4_parts_knows_Spy",
          OR4_analz_knows_Spy RS (impOfSubs analz_subset_parts));

(*For proving the easier theorems about X ~: parts (knows Spy evs).*)
fun parts_induct_tac i = 
    etac otway.induct i			THEN 
    ftac Oops_parts_knows_Spy (i+7) THEN
    ftac OR4_parts_knows_Spy (i+6) THEN
    prove_simple_subgoals_tac  i;


(** Theorems of the form X ~: parts (knows Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees a good agent's shared key!*)
Goal "evs : otway ==> (Key (shrK A) : parts (knows Spy evs)) = (A : bad)";
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

Goal "evs : otway ==> (Key (shrK A) : analz (knows Spy evs)) = (A : bad)";
by (auto_tac(claset() addDs [impOfSubs analz_subset_parts], simpset()));
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

AddSDs [Spy_see_shrK RSN (2, rev_iffD1), 
	Spy_analz_shrK RSN (2, rev_iffD1)];


(*Nobody can have used non-existent keys!*)
Goal "evs : otway ==> Key K ~: used evs --> K ~: keysFor (parts (knows Spy evs))";
by (parts_induct_tac 1);
(*Fake*)
by (blast_tac (claset() addSDs [keysFor_parts_insert]) 1);
(*OR3*)
by (Blast_tac 1);
qed_spec_mp "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];



(*** Proofs involving analz ***)

(*Describes the form of K and NA when the Server sends this message.*)
Goal "[| Says Server B                                           \
\           {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},    \
\             Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}   \
\          : set evs;                                            \
\        evs : otway |]                                          \
\     ==> K ~: range shrK & (EX i. NA = Nonce i) & (EX j. NB = Nonce j)";
by (etac rev_mp 1);
by (etac otway.induct 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed "Says_Server_message_form";


(*For proofs involving analz.*)
val analz_knows_Spy_tac = 
    dtac OR4_analz_knows_Spy 7 THEN assume_tac 7 THEN
    ftac Says_Server_message_form 8 THEN assume_tac 8 THEN
    REPEAT ((eresolve_tac [exE, conjE] ORELSE' hyp_subst_tac) 8);


(****
 The following is to prove theorems of the form

  Key K : analz (insert (Key KAB) (knows Spy evs)) ==>
  Key K : analz (knows Spy evs)

 A more general formula must be proved inductively.
****)


(** Session keys are not used to encrypt other session keys **)

(*The equality makes the induction hypothesis easier to apply*)
Goal "evs : otway ==>                                 \
\  ALL K KK. KK <= -(range shrK) -->                  \
\         (Key K : analz (Key`KK Un (knows Spy evs))) =  \
\         (K : KK | Key K : analz (knows Spy evs))";
by (etac otway.induct 1);
by analz_knows_Spy_tac;
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_freshK_lemma ));
by (ALLGOALS (asm_simp_tac analz_image_freshK_ss));
(*Fake*) 
by (spy_analz_tac 1);
qed_spec_mp "analz_image_freshK";


Goal "[| evs : otway;  KAB ~: range shrK |] ==>       \
\     Key K : analz (insert (Key KAB) (knows Spy evs)) =  \
\     (K = KAB | Key K : analz (knows Spy evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(*** The Key K uniquely identifies the Server's message. **)

Goal "[| Says Server B                                           \
\         {|Crypt (shrK A) {|NA, Agent A, Agent B, K|},         \
\           Crypt (shrK B) {|NB, Agent A, Agent B, K|}|}        \
\        : set evs;                                             \
\       Says Server B'                                          \
\         {|Crypt (shrK A') {|NA', Agent A', Agent B', K|},     \
\           Crypt (shrK B') {|NB', Agent A', Agent B', K|}|}    \
\        : set evs;                                             \
\       evs : otway |]                                          \
\    ==> A=A' & B=B' & NA=NA' & NB=NB'";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac otway.induct 1);
by (ALLGOALS Asm_simp_tac);
(*Remaining cases: OR3 and OR4*)
by (REPEAT (Blast_tac 1)); 
qed "unique_session_keys";



(**** Authenticity properties relating to NA ****)

(*If the encrypted message appears then it originated with the Server!*)
Goal "[| A ~: bad;  A ~= B;  evs : otway |]                 \
\     ==> Crypt (shrK A) {|NA, Agent A, Agent B, Key K|} : parts (knows Spy evs) \
\      --> (EX NB. Says Server B                                          \
\                   {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},     \
\                     Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}    \
\                   : set evs)";
by (parts_induct_tac 1);
by (Blast_tac 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [ex_disj_distrib])));
(*OR3*)
by (Blast_tac 1);
qed_spec_mp "NA_Crypt_imp_Server_msg";


(*Corollary: if A receives B's OR4 message then it originated with the Server.
  Freshness may be inferred from nonce NA.*)
Goal "[| Gets A (Crypt (shrK A) {|NA, Agent A, Agent B, Key K|})  \
\         : set evs;                                                 \
\        A ~: bad;  A ~= B;  evs : otway |]                          \
\     ==> EX NB. Says Server B                                       \
\                 {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},  \
\                   Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|} \
\                : set evs";
by (blast_tac (claset() addSIs [NA_Crypt_imp_Server_msg]) 1);
qed "A_trusts_OR4";


(** Crucial secrecy property: Spy does not see the keys sent in msg OR3
    Does not in itself guarantee security: an attack could violate 
    the premises, e.g. by having A=Spy **)

Goal "[| A ~: bad;  B ~: bad;  evs : otway |]                   \
\     ==> Says Server B                                         \
\          {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},    \
\            Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}   \
\         : set evs -->                                         \
\         Notes Spy {|NA, NB, Key K|} ~: set evs -->            \
\         Key K ~: analz (knows Spy evs)";
by (etac otway.induct 1);
by analz_knows_Spy_tac;
by (ALLGOALS
    (asm_simp_tac (simpset() addcongs [conj_cong] 
                             addsimps [analz_insert_eq, analz_insert_freshK]
                                      @ pushes @ split_ifs)));
(*Oops*)
by (blast_tac (claset() addSDs [unique_session_keys]) 4);
(*OR4*) 
by (Blast_tac 3);
(*OR3*)
by (Blast_tac 2);
(*Fake*) 
by (spy_analz_tac 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);

Goal "[| Says Server B                                           \
\           {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},    \
\             Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}   \
\          : set evs;                                            \
\        Notes Spy {|NA, NB, Key K|} ~: set evs;                 \
\        A ~: bad;  B ~: bad;  evs : otway |]                    \
\     ==> Key K ~: analz (knows Spy evs)";
by (ftac Says_Server_message_form 1 THEN assume_tac 1);
by (blast_tac (claset() addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


(*A's guarantee.  The Oops premise quantifies over NB because A cannot know
  what it is.*)
Goal "[| Gets A (Crypt (shrK A) {|NA, Agent A, Agent B, Key K|})  \
\         : set evs;                                                 \
\        ALL NB. Notes Spy {|NA, NB, Key K|} ~: set evs;             \
\        A ~: bad;  B ~: bad;  A ~= B;  evs : otway |]               \
\     ==> Key K ~: analz (knows Spy evs)";
by (blast_tac (claset() addSDs [A_trusts_OR4, Spy_not_see_encrypted_key]) 1);
qed "A_gets_good_key";


(**** Authenticity properties relating to NB ****)

(*If the encrypted message appears then it originated with the Server!*)
Goal "[| B ~: bad;  A ~= B;  evs : otway |]                              \
\ ==> Crypt (shrK B) {|NB, Agent A, Agent B, Key K|} : parts (knows Spy evs) \
\     --> (EX NA. Says Server B                                          \
\                  {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},     \
\                    Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}    \
\                  : set evs)";
by (parts_induct_tac 1);
by (Blast_tac 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [ex_disj_distrib])));
(*OR3*)
by (Blast_tac 1);
qed_spec_mp "NB_Crypt_imp_Server_msg";


(*Guarantee for B: if it gets a well-formed certificate then the Server
  has sent the correct message in round 3.*)
Goal "[| Gets B {|X, Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|} \
\          : set evs;                                                    \
\        B ~: bad;  A ~= B;  evs : otway |]                              \
\     ==> EX NA. Says Server B                                           \
\                  {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},     \
\                    Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}    \
\                  : set evs";
by (blast_tac (claset() addSIs [NB_Crypt_imp_Server_msg]) 1);
qed "B_trusts_OR3";


(*The obvious combination of B_trusts_OR3 with Spy_not_see_encrypted_key*)
Goal "[| Gets B {|X, Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|} \
\         : set evs;                                                     \
\        ALL NA. Notes Spy {|NA, NB, Key K|} ~: set evs;                 \
\        A ~: bad;  B ~: bad;  A ~= B;  evs : otway |]                   \
\     ==> Key K ~: analz (knows Spy evs)";
by (blast_tac (claset() addDs [B_trusts_OR3, Spy_not_see_encrypted_key]) 1);
qed "B_gets_good_key";
