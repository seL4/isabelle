(*  Title:      HOL/Auth/OtwayRees
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "otway" for the Otway-Rees protocol.

Version that encrypts Nonce NB

From page 244 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

AddEs knows_Spy_partsEs;
AddDs [impOfSubs analz_subset_parts];
AddDs [impOfSubs Fake_parts_insert];


(*A "possibility property": there are traces that reach the end*)
Goal "[| B ~= Server |]   \
\     ==> EX NA K. EX evs: otway.          \
\            Says B A {|Nonce NA, Crypt (shrK A) {|Nonce NA, Key K|}|} \
\              : set evs";
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

Goal "[| Gets B {|N, Agent A, Agent B, X|} : set evs;  evs : otway |]  \
\     ==> X : analz (knows Spy evs)";
by (blast_tac (claset() addSDs [Gets_imp_knows_Spy RS analz.Inj]) 1);
qed "OR2_analz_knows_Spy";

Goal "[| Gets B {|N, X, Crypt (shrK B) X'|} : set evs;  evs : otway |] \
\     ==> X : analz (knows Spy evs)";
by (blast_tac (claset() addSDs [Gets_imp_knows_Spy RS analz.Inj]) 1);
qed "OR4_analz_knows_Spy";

Goal "Says Server B {|NA, X, Crypt K' {|NB,K|}|} : set evs \
\     ==> K : parts (knows Spy evs)";
by (Blast_tac 1);
qed "Oops_parts_knows_Spy";

bind_thm ("OR2_parts_knows_Spy",
          OR2_analz_knows_Spy RS (impOfSubs analz_subset_parts));
bind_thm ("OR4_parts_knows_Spy",
          OR4_analz_knows_Spy RS (impOfSubs analz_subset_parts));

(*For proving the easier theorems about X ~: parts (knows Spy evs).*)
fun parts_induct_tac i = 
    etac otway.induct i			THEN 
    ftac Oops_parts_knows_Spy (i+7) THEN
    ftac OR4_parts_knows_Spy (i+6) THEN
    ftac OR2_parts_knows_Spy (i+4) THEN 
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
Goal "evs: otway ==> Key K ~: used evs --> K ~: keysFor(parts(knows Spy evs))";
by (parts_induct_tac 1);
(*Fake*)
by (blast_tac (claset() addSDs [keysFor_parts_insert]) 1);
(*OR2, OR3*)
by (ALLGOALS Blast_tac);
qed_spec_mp "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];



(*** Proofs involving analz ***)

(*Describes the form of K and NA when the Server sends this message.  Also
  for Oops case.*)
Goal "[| Says Server B {|NA, X, Crypt (shrK B) {|NB, Key K|}|} : set evs; \
\        evs : otway |]                                           \
\     ==> K ~: range shrK & (EX i. NA = Nonce i) & (EX j. NB = Nonce j)";
by (etac rev_mp 1);
by (etac otway.induct 1);
by (ALLGOALS Simp_tac);
by (ALLGOALS Blast_tac);
qed "Says_Server_message_form";


(*For proofs involving analz.*)
val analz_knows_Spy_tac = 
    dtac OR2_analz_knows_Spy 5 THEN assume_tac 5 THEN 
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
Goal "evs : otway ==> ALL K KK. KK <= - (range shrK) -->           \
\                      (Key K : analz (Key``KK Un (knows Spy evs))) =  \
\                      (K : KK | Key K : analz (knows Spy evs))";
by (etac otway.induct 1);
by analz_knows_Spy_tac;
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_freshK_lemma));
by (ALLGOALS (asm_simp_tac analz_image_freshK_ss));
(*Fake*) 
by (spy_analz_tac 1);
qed_spec_mp "analz_image_freshK";


Goal "[| evs : otway;  KAB ~: range shrK |]               \
\     ==> Key K : analz (insert (Key KAB) (knows Spy evs)) =  \
\         (K = KAB | Key K : analz (knows Spy evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(*** The Key K uniquely identifies the Server's  message. **)

Goal "evs : otway ==>                                                  \
\     EX B' NA' NB' X'. ALL B NA NB X.                                 \
\     Says Server B {|NA, X, Crypt (shrK B) {|NB, K|}|} : set evs -->  \
\     B=B' & NA=NA' & NB=NB' & X=X'";
by (etac otway.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [all_conj_distrib])));
by (ALLGOALS Clarify_tac);
(*Remaining cases: OR3 and OR4*)
by (ex_strip_tac 2);
by (Best_tac 2);	(*Blast_tac's too slow (in reconstruction)*)
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
(*...we assume X is a recent message, and handle this case by contradiction*)
by (blast_tac (claset() addSEs knows_Spy_partsEs) 1);
val lemma = result();

Goal "[| Says Server B {|NA, X, Crypt (shrK B) {|NB, K|}|}   : set evs; \ 
\        Says Server B' {|NA',X',Crypt (shrK B') {|NB',K|}|} : set evs; \
\        evs : otway |] ==> X=X' & B=B' & NA=NA' & NB=NB'";
by (prove_unique_tac lemma 1);
qed "unique_session_keys";


(**** Authenticity properties relating to NA ****)

(*Only OR1 can have caused such a part of a message to appear.*)
Goal "[| A ~: bad;  evs : otway |]                             \
\ ==> Crypt (shrK A) {|NA, Agent A, Agent B|} : parts (knows Spy evs) --> \
\     Says A B {|NA, Agent A, Agent B,                      \
\                Crypt (shrK A) {|NA, Agent A, Agent B|}|}  \
\       : set evs";
by (parts_induct_tac 1);
by (Blast_tac 1);
qed_spec_mp "Crypt_imp_OR1";

Goal "[| Gets B {|NA, Agent A, Agent B,                      \
\                 Crypt (shrK A) {|NA, Agent A, Agent B|}|} : set evs; \
\        A ~: bad; evs : otway |]                             \
\      ==> Says A B {|NA, Agent A, Agent B,                      \
\                     Crypt (shrK A) {|NA, Agent A, Agent B|}|}  \
\            : set evs";
by (blast_tac (claset() addDs [Crypt_imp_OR1]) 1);
qed"Crypt_imp_OR1_Gets";


(** The Nonce NA uniquely identifies A's message. **)

Goal "[| evs : otway; A ~: bad |]               \
\ ==> EX B'. ALL B.                                 \
\        Crypt (shrK A) {|NA, Agent A, Agent B|} : parts (knows Spy evs) \
\        --> B = B'";
by (parts_induct_tac 1);
by (Blast_tac 1);
by (simp_tac (simpset() addsimps [all_conj_distrib]) 1); 
(*OR1: creation of new Nonce.  Move assertion into global context*)
by (expand_case_tac "NA = ?y" 1);
by (Blast_tac 1);
val lemma = result();

Goal "[| Crypt (shrK A) {|NA, Agent A, Agent B|}: parts (knows Spy evs); \
\        Crypt (shrK A) {|NA, Agent A, Agent C|}: parts (knows Spy evs); \
\        evs : otway;  A ~: bad |]                                   \
\     ==> B = C";
by (prove_unique_tac lemma 1);
qed "unique_NA";


(*It is impossible to re-use a nonce in both OR1 and OR2.  This holds because
  OR2 encrypts Nonce NB.  It prevents the attack that can occur in the
  over-simplified version of this protocol: see OtwayRees_Bad.*)
Goal "[| A ~: bad;  evs : otway |]                      \
\     ==> Crypt (shrK A) {|NA, Agent A, Agent B|} : parts (knows Spy evs) --> \
\         Crypt (shrK A) {|NA', NA, Agent A', Agent A|}  \
\           ~: parts (knows Spy evs)";
by (parts_induct_tac 1);
by Auto_tac;
qed_spec_mp "no_nonce_OR1_OR2";

val nonce_OR1_OR2_E = no_nonce_OR1_OR2 RSN (2, rev_notE);

(*Crucial property: If the encrypted message appears, and A has used NA
  to start a run, then it originated with the Server!*)
Goal "[| A ~: bad;  evs : otway |]                                  \
\     ==> Crypt (shrK A) {|NA, Key K|} : parts (knows Spy evs)          \
\         --> Says A B {|NA, Agent A, Agent B,                          \
\                        Crypt (shrK A) {|NA, Agent A, Agent B|}|}      \
\               : set evs -->                                           \
\             (EX NB. Says Server B                                     \
\                  {|NA,                                                \
\                    Crypt (shrK A) {|NA, Key K|},                      \
\                    Crypt (shrK B) {|NB, Key K|}|}                     \
\                    : set evs)";
by (parts_induct_tac 1);
by (Blast_tac 1);
(*OR1: it cannot be a new Nonce, contradiction.*)
by (Blast_tac 1);
(*OR3 and OR4*)
by (asm_simp_tac (simpset() addsimps [ex_disj_distrib]) 1);
by (rtac conjI 1);
by (ALLGOALS Clarify_tac);
(*OR4*)
by (blast_tac (claset() addSIs [Crypt_imp_OR1]) 3);
(*OR3, two cases*)  (** LEVEL 7 **)
by (blast_tac (claset() addSEs  [nonce_OR1_OR2_E]
                        delrules [conjI] (*stop split-up into 4 subgoals*)) 2);
by (blast_tac (claset() addIs [unique_NA]) 1);
qed_spec_mp "NA_Crypt_imp_Server_msg";


(*Corollary: if A receives B's OR4 message and the nonce NA agrees
  then the key really did come from the Server!  CANNOT prove this of the
  bad form of this protocol, even though we can prove
  Spy_not_see_encrypted_key*)
Goal "[| Says A  B {|NA, Agent A, Agent B,                       \
\                Crypt (shrK A) {|NA, Agent A, Agent B|}|} : set evs; \
\        Gets A {|NA, Crypt (shrK A) {|NA, Key K|}|} : set evs; \
\    A ~: bad;  evs : otway |]                              \
\ ==> EX NB. Says Server B                                  \
\              {|NA,                                        \
\                Crypt (shrK A) {|NA, Key K|},              \
\                Crypt (shrK B) {|NB, Key K|}|}             \
\                : set evs";
by (blast_tac (claset() addSIs [NA_Crypt_imp_Server_msg]) 1);
qed "A_trusts_OR4";


(** Crucial secrecy property: Spy does not see the keys sent in msg OR3
    Does not in itself guarantee security: an attack could violate 
    the premises, e.g. by having A=Spy **)

Goal "[| A ~: bad;  B ~: bad;  evs : otway |]                  \
\ ==> Says Server B                                            \
\       {|NA, Crypt (shrK A) {|NA, Key K|},                    \
\         Crypt (shrK B) {|NB, Key K|}|} : set evs -->         \
\     Notes Spy {|NA, NB, Key K|} ~: set evs -->               \
\     Key K ~: analz (knows Spy evs)";
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
\         {|NA, Crypt (shrK A) {|NA, Key K|},                    \
\               Crypt (shrK B) {|NB, Key K|}|} : set evs;        \
\        Notes Spy {|NA, NB, Key K|} ~: set evs;                 \
\        A ~: bad;  B ~: bad;  evs : otway |]                    \
\     ==> Key K ~: analz (knows Spy evs)";
by (ftac Says_Server_message_form 1 THEN assume_tac 1);
by (blast_tac (claset() addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


(*A's guarantee.  The Oops premise quantifies over NB because A cannot know
  what it is.*)
Goal "[| Says A  B {|NA, Agent A, Agent B,                       \
\                    Crypt (shrK A) {|NA, Agent A, Agent B|}|} : set evs; \
\        Gets A {|NA, Crypt (shrK A) {|NA, Key K|}|} : set evs; \
\        ALL NB. Notes Spy {|NA, NB, Key K|} ~: set evs;         \
\        A ~: bad;  B ~: bad;  evs : otway |]                    \
\     ==> Key K ~: analz (knows Spy evs)";
by (blast_tac (claset() addSDs [A_trusts_OR4, Spy_not_see_encrypted_key]) 1);
qed "A_gets_good_key";


(**** Authenticity properties relating to NB ****)

(*Only OR2 can have caused such a part of a message to appear.  We do not
  know anything about X: it does NOT have to have the right form.*)
Goal "[| Crypt (shrK B) {|NA, NB, Agent A, Agent B|}       \
\          : parts (knows Spy evs);  \
\        B ~: bad;  evs : otway |]                         \
\     ==> EX X. Says B Server                              \
\                {|NA, Agent A, Agent B, X,                       \
\                  Crypt (shrK B) {|NA, NB, Agent A, Agent B|}|}  \
\                : set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "Crypt_imp_OR2";


(** The Nonce NB uniquely identifies B's  message. **)

Goal "[| evs : otway; B ~: bad |]  \
\ ==> EX NA' A'. ALL NA A.            \
\      Crypt (shrK B) {|NA, NB, Agent A, Agent B|} : parts(knows Spy evs) \
\      --> NA = NA' & A = A'";
by (parts_induct_tac 1);
by (Blast_tac 1);
by (simp_tac (simpset() addsimps [all_conj_distrib]) 1); 
(*OR2: creation of new Nonce.  Move assertion into global context*)
by (expand_case_tac "NB = ?y" 1);
by (Blast_tac 1);
val lemma = result();

Goal "[| Crypt (shrK B) {|NA, NB, Agent A, Agent B|} : parts(knows Spy evs); \
\        Crypt (shrK B) {|NC, NB, Agent C, Agent B|} : parts(knows Spy evs); \
\          evs : otway;  B ~: bad |]             \
\        ==> NC = NA & C = A";
by (prove_unique_tac lemma 1);
qed "unique_NB";

(*If the encrypted message appears, and B has used Nonce NB,
  then it originated with the Server!*)
Goal "[| B ~: bad;  evs : otway |]                                    \
\ ==> Crypt (shrK B) {|NB, Key K|} : parts (knows Spy evs)            \
\     --> (ALL X'. Says B Server                                      \
\                    {|NA, Agent A, Agent B, X',                      \
\                      Crypt (shrK B) {|NA, NB, Agent A, Agent B|}|}  \
\          : set evs                                                  \
\          --> Says Server B                                          \
\               {|NA, Crypt (shrK A) {|NA, Key K|},                   \
\                     Crypt (shrK B) {|NB, Key K|}|}                  \
\                   : set evs)";
by (parts_induct_tac 1);
by (Blast_tac 1);
(*OR1: it cannot be a new Nonce, contradiction.*)
by (Blast_tac 1);
(*OR4*)
by (blast_tac (claset() addSDs [Crypt_imp_OR2]) 2);
(*OR3*)
(*Provable in 38s by the single command
    by (blast_tac (claset() addDs  [unique_NB] addEs[nonce_OR1_OR2_E]) 1);
*)
by (safe_tac (claset() delrules [disjCI, impCE]));
by (Blast_tac 3); 
by (blast_tac (claset() addSDs  [unique_NB]
                        delrules [impCE] (*stop split-up*)) 2);
by (blast_tac (claset() addSEs [nonce_OR1_OR2_E]
                        delrules [conjI] (*stop split-up*)) 1);
qed_spec_mp "NB_Crypt_imp_Server_msg";


(*Guarantee for B: if it gets a message with matching NB then the Server
  has sent the correct message.*)
Goal "[| Says B Server {|NA, Agent A, Agent B, X',              \
\                        Crypt (shrK B) {|NA, NB, Agent A, Agent B|} |} \
\          : set evs;                                           \
\        Gets B {|NA, X, Crypt (shrK B) {|NB, Key K|}|} : set evs;   \
\        B ~: bad;  evs : otway |]                              \
\     ==> Says Server B                                         \
\              {|NA,                                            \
\                Crypt (shrK A) {|NA, Key K|},                  \
\                Crypt (shrK B) {|NB, Key K|}|}                 \
\                : set evs";
by (blast_tac (claset() addSIs [NB_Crypt_imp_Server_msg]) 1);
qed "B_trusts_OR3";


(*The obvious combination of B_trusts_OR3 with Spy_not_see_encrypted_key*)
Goal "[| Says B Server {|NA, Agent A, Agent B, X',              \
\                        Crypt (shrK B) {|NA, NB, Agent A, Agent B|} |} \
\          : set evs;                                           \
\        Gets B {|NA, X, Crypt (shrK B) {|NB, Key K|}|} : set evs;   \
\        Notes Spy {|NA, NB, Key K|} ~: set evs;                \
\        A ~: bad;  B ~: bad;  evs : otway |]                   \
\     ==> Key K ~: analz (knows Spy evs)";
by (blast_tac (claset() addSDs [B_trusts_OR3, Spy_not_see_encrypted_key]) 1);
qed "B_gets_good_key";


Goal "[| Says Server B                                       \
\           {|NA, Crypt (shrK A) {|NA, Key K|},              \
\             Crypt (shrK B) {|NB, Key K|}|} : set evs;      \
\        B ~: bad;  evs : otway |]                           \
\ ==> EX X. Says B Server {|NA, Agent A, Agent B, X,         \
\                           Crypt (shrK B) {|NA, NB, Agent A, Agent B|} |} \
\             : set evs";
by (etac rev_mp 1);
by (etac otway.induct 1);
by (ALLGOALS Asm_simp_tac);
by (blast_tac (claset() addSDs [Crypt_imp_OR2]) 3);
by (ALLGOALS Blast_tac);
qed "OR3_imp_OR2";


(*After getting and checking OR4, agent A can trust that B has been active.
  We could probably prove that X has the expected form, but that is not
  strictly necessary for authentication.*)
Goal "[| Gets A {|NA, Crypt (shrK A) {|NA, Key K|}|} : set evs;        \
\        Says A  B {|NA, Agent A, Agent B,                                \
\                    Crypt (shrK A) {|NA, Agent A, Agent B|}|} : set evs; \
\        A ~: bad;  B ~: bad;  evs : otway |]                             \
\ ==> EX NB X. Says B Server {|NA, Agent A, Agent B, X,               \
\                              Crypt (shrK B)  {|NA, NB, Agent A, Agent B|} |}\
\                : set evs";
by (blast_tac (claset() addSDs [A_trusts_OR4, OR3_imp_OR2]) 1);
qed "A_auths_B";
