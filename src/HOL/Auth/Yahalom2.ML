(*  Title:      HOL/Auth/Yahalom2
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "yahalom" for the Yahalom protocol, Variant 2.

This version trades encryption of NB for additional explicitness in YM3.

From page 259 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

AddEs knows_Spy_partsEs;
AddDs [impOfSubs analz_subset_parts];
AddDs [impOfSubs Fake_parts_insert];


(*A "possibility property": there are traces that reach the end*)
Goal "EX X NB K. EX evs: yahalom.          \
\            Says A B {|X, Crypt K (Nonce NB)|} : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (yahalom.Nil RS 
          yahalom.YM1 RS yahalom.Reception RS
          yahalom.YM2 RS yahalom.Reception RS 
          yahalom.YM3 RS yahalom.Reception RS yahalom.YM4) 2);
by possibility_tac;
result();

Goal "[| Gets B X : set evs; evs : yahalom |] ==> EX A. Says A B X : set evs";
by (etac rev_mp 1);
by (etac yahalom.induct 1);
by Auto_tac;
qed "Gets_imp_Says";

(*Must be proved separately for each protocol*)
Goal "[| Gets B X : set evs; evs : yahalom |]  ==> X : knows Spy evs";
by (blast_tac (claset() addSDs [Gets_imp_Says, Says_imp_knows_Spy]) 1);
qed"Gets_imp_knows_Spy";
AddDs [Gets_imp_knows_Spy RS parts.Inj];


(**** Inductive proofs about yahalom ****)

(** For reasoning about the encrypted portion of messages **)

(*Lets us treat YM4 using a similar argument as for the Fake case.*)
Goal "[| Gets A {|NB, Crypt (shrK A) Y, X|} : set evs;  evs : yahalom |]  \
\     ==> X : analz (knows Spy evs)";
by (blast_tac (claset() addSDs [Gets_imp_knows_Spy RS analz.Inj]) 1);
qed "YM4_analz_knows_Spy";

bind_thm ("YM4_parts_knows_Spy",
          YM4_analz_knows_Spy RS (impOfSubs analz_subset_parts));

(*For Oops*)
Goal "Says Server A {|NB, Crypt (shrK A) {|B,K,NA|}, X|} : set evs \
\     ==> K : parts (knows Spy evs)";
by (blast_tac (claset() addSEs partsEs
                        addSDs [Says_imp_knows_Spy RS parts.Inj]) 1);
qed "YM4_Key_parts_knows_Spy";

(*For proving the easier theorems about X ~: parts (knows Spy evs).*)
fun parts_knows_Spy_tac i = 
  EVERY
   [ftac YM4_Key_parts_knows_Spy (i+7),
    ftac YM4_parts_knows_Spy (i+6), assume_tac (i+6),
    prove_simple_subgoals_tac i];

(*Induction for regularity theorems.  If induction formula has the form
   X ~: analz (knows Spy evs) --> ... then it shortens the proof by discarding
   needless information about analz (insert X (knows Spy evs))  *)
fun parts_induct_tac i = 
    etac yahalom.induct i
    THEN 
    REPEAT (FIRSTGOAL analz_mono_contra_tac)
    THEN  parts_knows_Spy_tac i;


(** Theorems of the form X ~: parts (knows Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's shared key! (unless it's bad at start)*)
Goal "evs : yahalom ==> (Key (shrK A) : parts (knows Spy evs)) = (A : bad)";
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

Goal "evs : yahalom ==> (Key (shrK A) : analz (knows Spy evs)) = (A : bad)";
by Auto_tac;
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

AddSDs [Spy_see_shrK RSN (2, rev_iffD1), 
	Spy_analz_shrK RSN (2, rev_iffD1)];


(*Nobody can have used non-existent keys!  Needed to apply analz_insert_Key*)
Goal "evs : yahalom ==>          \
\      Key K ~: used evs --> K ~: keysFor (parts (knows Spy evs))";
by (parts_induct_tac 1);
(*YM4: Key K is not fresh!*)
by (Blast_tac 3);
(*YM3*)
by (blast_tac (claset() addss (simpset())) 2);
(*Fake*)
by (blast_tac (claset() addSDs [keysFor_parts_insert]) 1);
qed_spec_mp "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];

(*Describes the form of K when the Server sends this message.  Useful for
  Oops as well as main secrecy property.*)
Goal "[| Says Server A {|nb', Crypt (shrK A) {|Agent B, Key K, na|}, X|} \
\         : set evs;                                            \
\        evs : yahalom |]                                       \
\     ==> K ~: range shrK";
by (etac rev_mp 1);
by (etac yahalom.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "Says_Server_message_form";


(*For proofs involving analz.*)
val analz_knows_Spy_tac = 
    dtac YM4_analz_knows_Spy 7 THEN assume_tac 7 THEN
    ftac Says_Server_message_form 8 THEN
    assume_tac 8 THEN
    REPEAT ((etac conjE ORELSE' hyp_subst_tac) 8);


(****
 The following is to prove theorems of the form

          Key K : analz (insert (Key KAB) (knows Spy evs)) ==>
          Key K : analz (knows Spy evs)

 A more general formula must be proved inductively.

****)

(** Session keys are not used to encrypt other session keys **)

Goal "evs : yahalom ==>                               \
\  ALL K KK. KK <= - (range shrK) -->                 \
\         (Key K : analz (Key`KK Un (knows Spy evs))) =  \
\         (K : KK | Key K : analz (knows Spy evs))";
by (etac yahalom.induct 1);
by analz_knows_Spy_tac;
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_freshK_lemma));
by (ALLGOALS (asm_simp_tac analz_image_freshK_ss));
(*Fake*) 
by (spy_analz_tac 1);
qed_spec_mp "analz_image_freshK";

Goal "[| evs : yahalom;  KAB ~: range shrK |] ==>     \
\     Key K : analz (insert (Key KAB) (knows Spy evs)) =  \
\     (K = KAB | Key K : analz (knows Spy evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(*** The Key K uniquely identifies the Server's  message. **)

Goal "evs : yahalom ==>                                     \
\   EX A' B' na' nb' X'. ALL A B na nb X.                   \
\       Says Server A                                       \
\        {|nb, Crypt (shrK A) {|Agent B, Key K, na|}, X|}   \
\       : set evs --> A=A' & B=B' & na=na' & nb=nb' & X=X'";
by (etac yahalom.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [all_conj_distrib])));
by (Clarify_tac 1);
(*Remaining case: YM3*)
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
(*...we assume X is a recent message and handle this case by contradiction*)
by (blast_tac (claset() delrules [conjI]    (*prevent splitup into 4 subgoals*)
                        addss (simpset() addsimps [parts_insertI])) 1);
val lemma = result();

Goal "[| Says Server A                                            \
\         {|nb, Crypt (shrK A) {|Agent B, Key K, na|}, X|} : set evs; \
\       Says Server A'                                           \
\         {|nb', Crypt (shrK A') {|Agent B', Key K, na'|}, X'|} : set evs; \
\       evs : yahalom |]                                         \
\    ==> A=A' & B=B' & na=na' & nb=nb'";
by (prove_unique_tac lemma 1);
qed "unique_session_keys";


(** Crucial secrecy property: Spy does not see the keys sent in msg YM3 **)

Goal "[| A ~: bad;  B ~: bad;  evs : yahalom |]              \
\     ==> Says Server A                                      \
\           {|nb, Crypt (shrK A) {|Agent B, Key K, na|},     \
\                 Crypt (shrK B) {|Agent A, Agent B, Key K, nb|}|} \
\          : set evs -->                                     \
\         Notes Spy {|na, nb, Key K|} ~: set evs -->         \
\         Key K ~: analz (knows Spy evs)";
by (etac yahalom.induct 1);
by analz_knows_Spy_tac;
by (ALLGOALS
    (asm_simp_tac 
     (simpset() addsimps split_ifs
	        addsimps [analz_insert_eq, analz_insert_freshK])));
(*Oops*)
by (blast_tac (claset() addDs [unique_session_keys]) 3);
(*YM3: delete a useless induction hypothesis*)
by (thin_tac "?P-->?Q" 2);
by (Blast_tac 2);
(*Fake*) 
by (spy_analz_tac 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);


(*Final version*)
Goal "[| Says Server A                                    \
\           {|nb, Crypt (shrK A) {|Agent B, Key K, na|},  \
\                 Crypt (shrK B) {|Agent A, Agent B, Key K, nb|}|}    \
\        : set evs;                                       \
\        Notes Spy {|na, nb, Key K|} ~: set evs;          \
\        A ~: bad;  B ~: bad;  evs : yahalom |]           \
\     ==> Key K ~: analz (knows Spy evs)";
by (ftac Says_Server_message_form 1 THEN assume_tac 1);
by (blast_tac (claset() addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


(** Security Guarantee for A upon receiving YM3 **)

(*If the encrypted message appears then it originated with the Server.
  May now apply Spy_not_see_encrypted_key, subject to its conditions.*)
Goal "[| Crypt (shrK A) {|Agent B, Key K, na|}                      \
\         : parts (knows Spy evs);                                      \
\        A ~: bad;  evs : yahalom |]                                \
\      ==> EX nb. Says Server A                                     \
\                   {|nb, Crypt (shrK A) {|Agent B, Key K, na|},    \
\                         Crypt (shrK B) {|Agent A, Agent B, Key K, nb|}|} \
\                 : set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "A_trusts_YM3";

(*The obvious combination of A_trusts_YM3 with Spy_not_see_encrypted_key*)
Goal "[| Crypt (shrK A) {|Agent B, Key K, na|} : parts (knows Spy evs); \
\        ALL nb. Notes Spy {|na, nb, Key K|} ~: set evs;            \
\        A ~: bad;  B ~: bad;  evs : yahalom |]                     \
\     ==> Key K ~: analz (knows Spy evs)";
by (blast_tac (claset() addSDs [A_trusts_YM3, Spy_not_see_encrypted_key]) 1);
qed "A_gets_good_key";


(** Security Guarantee for B upon receiving YM4 **)

(*B knows, by the first part of A's message, that the Server distributed 
  the key for A and B, and has associated it with NB.*)
Goal "[| Crypt (shrK B) {|Agent A, Agent B, Key K, Nonce NB|} \
\          : parts (knows Spy evs);                               \
\        B ~: bad;  evs : yahalom |]                          \
\ ==> EX NA. Says Server A                                       \
\            {|Nonce NB,                                      \
\              Crypt (shrK A) {|Agent B, Key K, Nonce NA|},   \
\              Crypt (shrK B) {|Agent A, Agent B, Key K, Nonce NB|}|} \
\            : set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "B_trusts_YM4_shrK";


(*With this protocol variant, we don't need the 2nd part of YM4 at all:
  Nonce NB is available in the first part.*)

(*What can B deduce from receipt of YM4?  Stronger and simpler than Yahalom
  because we do not have to show that NB is secret. *)
Goal "[| Gets B {|Crypt (shrK B) {|Agent A, Agent B, Key K, Nonce NB|}, \
\                    X|}                                         \
\          : set evs;                                            \
\        A ~: bad;  B ~: bad;  evs : yahalom |]                  \
\ ==> EX NA. Says Server A                                          \
\            {|Nonce NB,                                         \
\              Crypt (shrK A) {|Agent B, Key K, Nonce NA|},      \
\              Crypt (shrK B) {|Agent A, Agent B, Key K, Nonce NB|}|} \
\           : set evs";
by (blast_tac (claset() addSDs [B_trusts_YM4_shrK]) 1);
qed "B_trusts_YM4";


(*The obvious combination of B_trusts_YM4 with Spy_not_see_encrypted_key*)
Goal "[| Gets B {|Crypt (shrK B) {|Agent A, Agent B, Key K, Nonce NB|}, \
\                    X|}                                         \
\          : set evs;                                            \
\        ALL na. Notes Spy {|na, Nonce NB, Key K|} ~: set evs;   \
\        A ~: bad;  B ~: bad;  evs : yahalom |]                  \
\     ==> Key K ~: analz (knows Spy evs)";
by (blast_tac (claset() addSDs [B_trusts_YM4, Spy_not_see_encrypted_key]) 1);
qed "B_gets_good_key";



(*** Authenticating B to A ***)

(*The encryption in message YM2 tells us it cannot be faked.*)
Goal "[| Crypt (shrK B) {|Agent A, Nonce NA|} : parts (knows Spy evs);  \
\        B ~: bad;  evs : yahalom                                   \
\     |] ==> EX NB. Says B Server {|Agent B, Nonce NB,              \
\                            Crypt (shrK B) {|Agent A, Nonce NA|}|} \
\                     : set evs";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "B_Said_YM2";


(*If the server sends YM3 then B sent YM2, perhaps with a different NB*)
Goal "[| Says Server A                                              \
\            {|nb, Crypt (shrK A) {|Agent B, Key K, Nonce NA|}, X|} \
\          : set evs;                                               \
\        B ~: bad;  evs : yahalom                                   \
\     |] ==> EX nb'. Says B Server {|Agent B, nb',                  \
\                            Crypt (shrK B) {|Agent A, Nonce NA|}|} \
\                      : set evs";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac yahalom.induct 1);
by (ALLGOALS Asm_simp_tac);
(*YM3*)
by (blast_tac (claset() addSDs [B_Said_YM2]) 3);
(*Fake, YM2*)
by (ALLGOALS Blast_tac);
val lemma = result();

(*If A receives YM3 then B has used nonce NA (and therefore is alive)*)
Goal "[| Gets A {|nb, Crypt (shrK A) {|Agent B, Key K, Nonce NA|}, X|}   \
\          : set evs;                                                    \
\        A ~: bad;  B ~: bad;  evs : yahalom |]                          \
\==> EX nb'. Says B Server                                               \
\                 {|Agent B, nb', Crypt (shrK B) {|Agent A, Nonce NA|}|} \
\              : set evs";
by (blast_tac (claset() addSDs [A_trusts_YM3, lemma]) 1);
qed "YM3_auth_B_to_A";


(*** Authenticating A to B using the certificate Crypt K (Nonce NB) ***)

(*Assuming the session key is secure, if both certificates are present then
  A has said NB.  We can't be sure about the rest of A's message, but only
  NB matters for freshness.  Note that  Key K ~: analz (knows Spy evs)  must be
  the FIRST antecedent of the induction formula.*)  
Goal "evs : yahalom                                     \
\     ==> Key K ~: analz (knows Spy evs) -->                \
\         Crypt K (Nonce NB) : parts (knows Spy evs) -->    \
\         Crypt (shrK B) {|Agent A, Agent B, Key K, Nonce NB|}      \
\           : parts (knows Spy evs) -->                     \
\         B ~: bad -->                                  \
\         (EX X. Says A B {|X, Crypt K (Nonce NB)|} : set evs)";
by (parts_induct_tac 1);
(*Fake*)
by (Blast_tac 1);
(*YM3: by new_keys_not_used we note that Crypt K (Nonce NB) could not exist*)
by (force_tac (claset() addSDs [Crypt_imp_keysFor], simpset()) 1); 
(*YM4: was Crypt K (Nonce NB) the very last message?  If not, use ind. hyp.*)
by (asm_simp_tac (simpset() addsimps [ex_disj_distrib]) 1);
(*yes: delete a useless induction hypothesis; apply unicity of session keys*)
by (thin_tac "?P-->?Q" 1);
by (ftac Gets_imp_Says 1 THEN assume_tac 1);
by (not_bad_tac "Aa" 1);
by (blast_tac (claset() addSDs [A_trusts_YM3, B_trusts_YM4_shrK]
			addDs  [unique_session_keys]) 1);
qed_spec_mp "Auth_A_to_B_lemma";


(*If B receives YM4 then A has used nonce NB (and therefore is alive).
  Moreover, A associates K with NB (thus is talking about the same run).
  Other premises guarantee secrecy of K.*)
Goal "[| Gets B {|Crypt (shrK B) {|Agent A, Agent B, Key K, Nonce NB|}, \
\                    Crypt K (Nonce NB)|} : set evs;                 \
\        (ALL NA. Notes Spy {|Nonce NA, Nonce NB, Key K|} ~: set evs); \
\        A ~: bad;  B ~: bad;  evs : yahalom |]                    \
\     ==> EX X. Says A B {|X, Crypt K (Nonce NB)|} : set evs";
by (subgoal_tac "Key K ~: analz (knows Spy evs)" 1);
by (blast_tac (claset() addIs [Auth_A_to_B_lemma]) 1);
by (blast_tac (claset() addDs  [Spy_not_see_encrypted_key,
				B_trusts_YM4_shrK]) 1);
qed_spec_mp "YM4_imp_A_Said_YM3";
