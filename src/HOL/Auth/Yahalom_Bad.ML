(*  Title:      HOL/Auth/Yahalom
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "yahalom" for the Yahalom protocol.

From page 257 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

(*A "possibility property": there are traces that reach the end*)
Goal "A \\<noteq> Server \
\     ==> \\<exists>X NB K. \\<exists>evs \\<in> yahalom.          \
\            Says A B {|X, Crypt K (Nonce NB)|} \\<in> set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (yahalom.Nil RS 
          yahalom.YM1 RS yahalom.Reception RS
          yahalom.YM2 RS yahalom.Reception RS 
          yahalom.YM3 RS yahalom.Reception RS yahalom.YM4) 2);
by possibility_tac;
result();

Goal "[| Gets B X \\<in> set evs; evs \\<in> yahalom |] ==> \\<exists>A. Says A B X \\<in> set evs";
by (etac rev_mp 1);
by (etac yahalom.induct 1);
by Auto_tac;
qed "Gets_imp_Says";

(*Must be proved separately for each protocol*)
Goal "[| Gets B X \\<in> set evs; evs \\<in> yahalom |]  ==> X \\<in> knows Spy evs";
by (blast_tac (claset() addSDs [Gets_imp_Says, Says_imp_knows_Spy]) 1);
qed"Gets_imp_knows_Spy";
AddDs [Gets_imp_knows_Spy RS parts.Inj];


(**** Inductive proofs about yahalom ****)


(** For reasoning about the encrypted portion of messages **)

(*Lets us treat YM4 using a similar argument as for the Fake case.*)
Goal "[| Gets A {|Crypt (shrK A) Y, X|} \\<in> set evs;  evs \\<in> yahalom |]  \
\     ==> X \\<in> analz (knows Spy evs)";
by (blast_tac (claset() addSDs [Gets_imp_knows_Spy RS analz.Inj]) 1);
qed "YM4_analz_knows_Spy";

bind_thm ("YM4_parts_knows_Spy",
          YM4_analz_knows_Spy RS (impOfSubs analz_subset_parts));

(*For proving the easier theorems about X \\<notin> parts (knows Spy evs).*)
fun parts_knows_Spy_tac i = 
  EVERY
   [ftac YM4_parts_knows_Spy (i+6), assume_tac (i+6),
    prove_simple_subgoals_tac i];

(*Induction for regularity theorems.  If induction formula has the form
   X \\<notin> analz (knows Spy evs) --> ... then it shortens the proof by discarding
   needless information about analz (insert X (knows Spy evs))  *)
fun parts_induct_tac i = 
    etac yahalom.induct i
    THEN 
    REPEAT (FIRSTGOAL analz_mono_contra_tac)
    THEN  parts_knows_Spy_tac i;


(** Theorems of the form X \\<notin> parts (knows Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's shared key! (unless it's bad at start)*)
Goal "evs \\<in> yahalom ==> (Key (shrK A) \\<in> parts (knows Spy evs)) = (A \\<in> bad)";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
by (ALLGOALS Blast_tac);
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

Goal "evs \\<in> yahalom ==> (Key (shrK A) \\<in> analz (knows Spy evs)) = (A \\<in> bad)";
by (auto_tac(claset() addDs [impOfSubs analz_subset_parts], simpset()));
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

AddSDs [Spy_see_shrK RSN (2, rev_iffD1), 
	Spy_analz_shrK RSN (2, rev_iffD1)];


(*Nobody can have used non-existent keys!  Needed to apply analz_insert_Key*)
Goal "evs \\<in> yahalom ==>          \
\      Key K \\<notin> used evs --> K \\<notin> keysFor (parts (knows Spy evs))";
by (parts_induct_tac 1);
(*Fake*)
by (blast_tac (claset() addSDs [keysFor_parts_insert]) 1);
(*YM2-4: Because Key K is not fresh, etc.*)
by (REPEAT (blast_tac (claset() addSEs knows_Spy_partsEs) 1));
qed_spec_mp "new_keys_not_used";
Addsimps [new_keys_not_used];


(*For proofs involving analz.*)
val analz_knows_Spy_tac = 
    ftac YM4_analz_knows_Spy 7 THEN assume_tac 7;

(****
 The following is to prove theorems of the form

  Key K \\<in> analz (insert (Key KAB) (knows Spy evs)) ==>
  Key K \\<in> analz (knows Spy evs)

 A more general formula must be proved inductively.
****)

(** Session keys are not used to encrypt other session keys **)

Goal "evs \\<in> yahalom ==>                              \
\  \\<forall>K KK. KK <= - (range shrK) -->                \
\         (Key K \\<in> analz (Key`KK Un (knows Spy evs))) = \
\         (K \\<in> KK | Key K \\<in> analz (knows Spy evs))";
by (etac yahalom.induct 1);
by analz_knows_Spy_tac;
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_freshK_lemma));
by (ALLGOALS (asm_simp_tac analz_image_freshK_ss));
(*Fake*) 
by (spy_analz_tac 1);
qed_spec_mp "analz_image_freshK";

Goal "[| evs \\<in> yahalom;  KAB \\<notin> range shrK |]                  \
\      ==> Key K \\<in> analz (insert (Key KAB) (knows Spy evs)) =  \
\          (K = KAB | Key K \\<in> analz (knows Spy evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(*** The Key K uniquely identifies the Server's  message. **)

Goal "[| Says Server A                                                 \
\         {|Crypt (shrK A) {|Agent B, Key K, na, nb|}, X|} \\<in> set evs;  \
\       Says Server A'                                                 \
\         {|Crypt (shrK A') {|Agent B', Key K, na', nb'|}, X'|} \\<in> set evs; \
\       evs \\<in> yahalom |]                                    \
\    ==> A=A' & B=B' & na=na' & nb=nb'";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (etac yahalom.induct 1);
by (ALLGOALS Asm_simp_tac);
(*YM4*)
by (Blast_tac 2);
(*YM3, by freshness*)
by (blast_tac (claset() addSEs knows_Spy_partsEs) 1);
qed "unique_session_keys";


(** Crucial secrecy property: Spy does not see the keys sent in msg YM3 **)

Goal "[| A \\<notin> bad;  B \\<notin> bad;  evs \\<in> yahalom |]                \
\     ==> Says Server A                                        \
\           {|Crypt (shrK A) {|Agent B, Key K, na, nb|},       \
\             Crypt (shrK B) {|Agent A, Key K|}|}              \
\          \\<in> set evs -->                                       \
\         Key K \\<notin> analz (knows Spy evs)";
by (etac yahalom.induct 1);
by analz_knows_Spy_tac;
by (ALLGOALS
    (asm_simp_tac 
     (simpset() addsimps split_ifs @ pushes @
                         [analz_insert_eq, analz_insert_freshK])));
(*YM3*)
by (blast_tac (claset() delrules [impCE]
                        addSEs knows_Spy_partsEs
                        addIs [impOfSubs analz_subset_parts]) 2);
(*Fake*) 
by (spy_analz_tac 1);
val lemma = result() RS mp RSN(2,rev_notE);


(*Final version*)
Goal "[| Says Server A                                         \
\           {|Crypt (shrK A) {|Agent B, Key K, na, nb|},       \
\             Crypt (shrK B) {|Agent A, Key K|}|}              \
\          \\<in> set evs;                                          \
\        A \\<notin> bad;  B \\<notin> bad;  evs \\<in> yahalom |]                \
\     ==> Key K \\<notin> analz (knows Spy evs)";
by (blast_tac (claset() addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


(** Security Guarantee for A upon receiving YM3 **)

(*If the encrypted message appears then it originated with the Server*)
Goal "[| Crypt (shrK A) {|Agent B, Key K, na, nb|} \\<in> parts (knows Spy evs); \
\        A \\<notin> bad;  evs \\<in> yahalom |]                          \
\      ==> Says Server A                                      \
\           {|Crypt (shrK A) {|Agent B, Key K, na, nb|},      \
\             Crypt (shrK B) {|Agent A, Key K|}|}             \
\          \\<in> set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
qed "A_trusts_YM3";

(*The obvious combination of A_trusts_YM3 with Spy_not_see_encrypted_key*)
Goal "[| Crypt (shrK A) {|Agent B, Key K, na, nb|} \\<in> parts (knows Spy evs); \
\        A \\<notin> bad;  B \\<notin> bad;  evs \\<in> yahalom |]                \
\     ==> Key K \\<notin> analz (knows Spy evs)";
by (blast_tac (claset() addSDs [A_trusts_YM3, Spy_not_see_encrypted_key]) 1);
qed "A_gets_good_key";

(** Security Guarantees for B upon receiving YM4 **)

(*B knows, by the first part of A's message, that the Server distributed 
  the key for A and B.  But this part says nothing about nonces.*)
Goal "[| Crypt (shrK B) {|Agent A, Key K|} \\<in> parts (knows Spy evs);  \
\        B \\<notin> bad;  evs \\<in> yahalom |]                                 \
\     ==> \\<exists>NA NB. Says Server A                                    \
\                     {|Crypt (shrK A) {|Agent B, Key K,             \
\                                        Nonce NA, Nonce NB|},       \
\                       Crypt (shrK B) {|Agent A, Key K|}|}          \
\                    \\<in> set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
(*YM3*)
by (Blast_tac 1);
qed "B_trusts_YM4_shrK";

(** Up to now, the reasoning is similar to standard Yahalom.  Now the
    doubtful reasoning occurs.  We should not be assuming that an unknown
    key is secure, but the model allows us to: there is no Oops rule to
    let session keys go.*)

(*B knows, by the second part of A's message, that the Server distributed 
  the key quoting nonce NB.  This part says nothing about agent names. 
  Secrecy of K is assumed; the valid Yahalom proof uses (and later proves)
  the secrecy of NB.*)
Goal "evs \\<in> yahalom                                          \
\     ==> Key K \\<notin> analz (knows Spy evs) -->                 \
\         Crypt K (Nonce NB) \\<in> parts (knows Spy evs) -->     \
\         (\\<exists>A B NA. Says Server A                          \
\                     {|Crypt (shrK A) {|Agent B, Key K,     \
\                               Nonce NA, Nonce NB|},        \
\                       Crypt (shrK B) {|Agent A, Key K|}|}  \
\                    \\<in> set evs)";
by (parts_induct_tac 1);
by (ALLGOALS Clarify_tac);
(*YM3 & Fake*)
by (Blast_tac 2);
by (Fake_parts_insert_tac 1);
(*YM4*)
(*A is uncompromised because NB is secure;
  A's certificate guarantees the existence of the Server message*)
by (blast_tac (claset() addSDs [Gets_imp_Says, Crypt_Spy_analz_bad]
			addDs  [Says_imp_spies, analz.Inj, 
			        parts.Inj RS parts.Fst RS A_trusts_YM3]) 1);
bind_thm ("B_trusts_YM4_newK", result() RS mp RSN (2, rev_mp));


(*B's session key guarantee from YM4.  The two certificates contribute to a
  single conclusion about the Server's message. *)
Goal "[| Gets B {|Crypt (shrK B) {|Agent A, Key K|},                    \
\                 Crypt K (Nonce NB)|} \\<in> set evs;                       \
\        Says B Server                                                  \
\          {|Agent B, Nonce NB, Crypt (shrK B) {|Agent A, Nonce NA|}|}  \
\          \\<in> set evs;                                                   \
\        A \\<notin> bad;  B \\<notin> bad;  evs \\<in> yahalom |]                         \
\      ==> \\<exists>na nb. Says Server A                                      \
\                  {|Crypt (shrK A) {|Agent B, Key K, na, nb|},         \
\                    Crypt (shrK B) {|Agent A, Key K|}|}                \
\            \\<in> set evs";
by (blast_tac (claset() addDs [B_trusts_YM4_newK, B_trusts_YM4_shrK, 
                          Spy_not_see_encrypted_key, unique_session_keys]) 1);
qed "B_trusts_YM4";


(*The obvious combination of B_trusts_YM4 with Spy_not_see_encrypted_key*)
Goal "[| Gets B {|Crypt (shrK B) {|Agent A, Key K|},                   \
\                    Crypt K (Nonce NB)|} \\<in> set evs;                   \
\        Says B Server                                                 \
\          {|Agent B, Nonce NB, Crypt (shrK B) {|Agent A, Nonce NA|}|} \
\          \\<in> set evs;                                                  \
\        A \\<notin> bad;  B \\<notin> bad;  evs \\<in> yahalom |]                \
\     ==> Key K \\<notin> analz (knows Spy evs)";
by (blast_tac (claset() addSDs [B_trusts_YM4, Spy_not_see_encrypted_key]) 1);
qed "B_gets_good_key";


(*** Authenticating B to A: these proofs are not considered.
     They are irrelevant to showing the need for Oops. ***)


(*** Authenticating A to B using the certificate Crypt K (Nonce NB) ***)

(*Assuming the session key is secure, if both certificates are present then
  A has said NB.  We can't be sure about the rest of A's message, but only
  NB matters for freshness.*)  
Goal "evs \\<in> yahalom                                              \
\     ==> Key K \\<notin> analz (knows Spy evs) -->                     \
\         Crypt K (Nonce NB) \\<in> parts (knows Spy evs) -->         \
\         Crypt (shrK B) {|Agent A, Key K|} \\<in> parts (knows Spy evs) --> \
\         B \\<notin> bad -->                                           \
\         (\\<exists>X. Says A B {|X, Crypt K (Nonce NB)|} \\<in> set evs)";
by (parts_induct_tac 1);
(*Fake*)
by (Fake_parts_insert_tac 1);
(*YM3: by new_keys_not_used we note that Crypt K (Nonce NB) could not exist*)
by (force_tac (claset() addSDs [Crypt_imp_keysFor], simpset()) 1); 
(*YM4: was Crypt K (Nonce NB) the very last message?  If not, use ind. hyp.*)
by (asm_simp_tac (simpset() addsimps [ex_disj_distrib]) 1);
(*yes: apply unicity of session keys*)
by (blast_tac (claset() addSDs [Gets_imp_Says, A_trusts_YM3, B_trusts_YM4_shrK,
                                Crypt_Spy_analz_bad]
		addDs  [Says_imp_knows_Spy RS parts.Inj, 
                        Says_imp_spies RS analz.Inj, unique_session_keys]) 1);
qed_spec_mp "A_Said_YM3_lemma";

(*If B receives YM4 then A has used nonce NB (and therefore is alive).
  Moreover, A associates K with NB (thus is talking about the same run).
  Other premises guarantee secrecy of K.*)
Goal "[| Gets B {|Crypt (shrK B) {|Agent A, Key K|},                   \
\                 Crypt K (Nonce NB)|} \\<in> set evs;                      \
\        Says B Server                                                 \
\          {|Agent B, Nonce NB, Crypt (shrK B) {|Agent A, Nonce NA|}|} \
\          \\<in> set evs;                                                  \
\        A \\<notin> bad;  B \\<notin> bad;  evs \\<in> yahalom |]       \
\     ==> \\<exists>X. Says A B {|X, Crypt K (Nonce NB)|} \\<in> set evs";
by (blast_tac (claset() addSIs [A_Said_YM3_lemma]
                   addDs [Spy_not_see_encrypted_key, B_trusts_YM4,
                          Gets_imp_Says, Says_imp_knows_Spy RS parts.Inj]) 1);
qed_spec_mp "YM4_imp_A_Said_YM3";
