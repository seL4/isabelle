(*  Title:      HOL/Auth/Yahalom
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "yahalom" for the Yahalom protocol.

From page 257 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

Pretty.setdepth 25;


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

(*For Oops*)
Goal "Says Server A {|Crypt (shrK A) {|B,K,NA,NB|}, X|} \\<in> set evs \
\     ==> K \\<in> parts (knows Spy evs)";
by (blast_tac (claset() addSDs [parts.Body, 
                  Says_imp_knows_Spy RS parts.Inj]) 1);
qed "YM4_Key_parts_knows_Spy";

(*For proving the easier theorems about X \\<notin> parts (knows Spy evs).*)
fun parts_knows_Spy_tac i = 
  EVERY
   [ftac YM4_Key_parts_knows_Spy (i+7),
    ftac YM4_parts_knows_Spy (i+6), assume_tac (i+6),
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

(*Earlier, \\<forall>protocol proofs declared this theorem.  
  But Yahalom and Kerberos IV are the only ones that need it!*)
bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);


(*Describes the form of K when the Server sends this message.  Useful for
  Oops as well as main secrecy property.*)
Goal "[| Says Server A {|Crypt (shrK A) {|Agent B, Key K, na, nb|}, X|} \
\          \\<in> set evs;   evs \\<in> yahalom |]                                \
\     ==> K \\<notin> range shrK";
by (etac rev_mp 1);
by (etac yahalom.induct 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed "Says_Server_not_range";

Addsimps [Says_Server_not_range];


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
by (ALLGOALS (asm_simp_tac
	      (analz_image_freshK_ss addsimps [Says_Server_not_range])));
(*Fake*) 
by (spy_analz_tac 1);
qed_spec_mp "analz_image_freshK";

Goal "[| evs \\<in> yahalom;  KAB \\<notin> range shrK |]              \
\      ==> Key K \\<in> analz (insert (Key KAB) (knows Spy evs)) =  \
\          (K = KAB | Key K \\<in> analz (knows Spy evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(*** The Key K uniquely identifies the Server's  message. **)


Goal "[| Says Server A                                                 \
\         {|Crypt (shrK A) {|Agent B, Key K, na, nb|}, X|} \\<in> set evs; \
\       Says Server A'                                                \
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
\         Notes Spy {|na, nb, Key K|} \\<notin> set evs -->           \
\         Key K \\<notin> analz (knows Spy evs)";
by (etac yahalom.induct 1);
by analz_knows_Spy_tac;
by (ALLGOALS
    (asm_simp_tac 
     (simpset() addsimps split_ifs @ pushes @
                         [analz_insert_eq, analz_insert_freshK])));
(*Oops*)
by (blast_tac (claset() addDs [unique_session_keys]) 3);
(*YM3*)
by (blast_tac (claset() delrules [impCE]
                        addSEs knows_Spy_partsEs
                        addIs [impOfSubs analz_subset_parts]) 2);
(*Fake*) 
by (spy_analz_tac 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);


(*Final version*)
Goal "[| Says Server A                                         \
\           {|Crypt (shrK A) {|Agent B, Key K, na, nb|},       \
\             Crypt (shrK B) {|Agent A, Key K|}|}              \
\          \\<in> set evs;                                          \
\        Notes Spy {|na, nb, Key K|} \\<notin> set evs;               \
\        A \\<notin> bad;  B \\<notin> bad;  evs \\<in> yahalom |]                \
\     ==> Key K \\<notin> analz (knows Spy evs)";
by (blast_tac (claset() addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


(** Security Guarantee for A upon receiving YM3 **)

(*If the encrypted message appears then it originated with the Server*)
Goal "[| Crypt (shrK A) {|Agent B, Key K, na, nb|} \\<in> parts (knows Spy evs); \
\        A \\<notin> bad;  evs \\<in> yahalom |]                          \
\      ==> Says Server A                                            \
\           {|Crypt (shrK A) {|Agent B, Key K, na, nb|},            \
\             Crypt (shrK B) {|Agent A, Key K|}|}                   \
\          \\<in> set evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
qed "A_trusts_YM3";

(*The obvious combination of A_trusts_YM3 with Spy_not_see_encrypted_key*)
Goal "[| Crypt (shrK A) {|Agent B, Key K, na, nb|} \\<in> parts (knows Spy evs); \
\        Notes Spy {|na, nb, Key K|} \\<notin> set evs;               \
\        A \\<notin> bad;  B \\<notin> bad;  evs \\<in> yahalom |]                \
\     ==> Key K \\<notin> analz (knows Spy evs)";
by (blast_tac (claset() addSDs [A_trusts_YM3, Spy_not_see_encrypted_key]) 1);
qed "A_gets_good_key";

(** Security Guarantees for B upon receiving YM4 **)

(*B knows, by the first part of A's message, that the Server distributed 
  the key for A and B.  But this part says nothing about nonces.*)
Goal "[| Crypt (shrK B) {|Agent A, Key K|} \\<in> parts (knows Spy evs);      \
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

(*B knows, by the second part of A's message, that the Server distributed 
  the key quoting nonce NB.  This part says nothing about agent names. 
  Secrecy of NB is crucial.  Note that  Nonce NB \\<notin> analz(knows Spy evs)  must
  be the FIRST antecedent of the induction formula.*)
Goal "evs \\<in> yahalom                                          \
\     ==> Nonce NB \\<notin> analz (knows Spy evs) -->                  \
\         Crypt K (Nonce NB) \\<in> parts (knows Spy evs) -->         \
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


(**** Towards proving secrecy of Nonce NB ****)

(** Lemmas about the predicate KeyWithNonce **)

Goalw [KeyWithNonce_def]
 "Says Server A                                              \
\         {|Crypt (shrK A) {|Agent B, Key K, na, Nonce NB|}, X|} \
\       \\<in> set evs ==> KeyWithNonce K NB evs";
by (Blast_tac 1);
qed "KeyWithNonceI";

Goalw [KeyWithNonce_def]
   "KeyWithNonce K NB (Says S A X # evs) =                                    \
\ (Server = S &                                                            \
\  (\\<exists>B n X'. X = {|Crypt (shrK A) {|Agent B, Key K, n, Nonce NB|}, X'|}) \
\ | KeyWithNonce K NB evs)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "KeyWithNonce_Says";
Addsimps [KeyWithNonce_Says];

Goalw [KeyWithNonce_def]
   "KeyWithNonce K NB (Notes A X # evs) = KeyWithNonce K NB evs";
by (Simp_tac 1);
qed "KeyWithNonce_Notes";
Addsimps [KeyWithNonce_Notes];

Goalw [KeyWithNonce_def]
   "KeyWithNonce K NB (Gets A X # evs) = KeyWithNonce K NB evs";
by (Simp_tac 1);
qed "KeyWithNonce_Gets";
Addsimps [KeyWithNonce_Gets];

(*A fresh key cannot be associated with any nonce 
  (with respect to a given trace). *)
Goalw [KeyWithNonce_def]
 "Key K \\<notin> used evs ==> ~ KeyWithNonce K NB evs";
by (blast_tac (claset() addSEs knows_Spy_partsEs) 1);
qed "fresh_not_KeyWithNonce";

(*The Server message associates K with NB' and therefore not with any 
  other nonce NB.*)
Goalw [KeyWithNonce_def]
 "[| Says Server A                                                \
\             {|Crypt (shrK A) {|Agent B, Key K, na, Nonce NB'|}, X|} \
\          \\<in> set evs;                                                 \
\        NB \\<noteq> NB';  evs \\<in> yahalom |]                                 \
\     ==> ~ KeyWithNonce K NB evs";
by (blast_tac (claset() addDs [unique_session_keys]) 1);
qed "Says_Server_KeyWithNonce";


(*The only nonces that can be found with the help of session keys are
  those distributed as nonce NB by the Server.  The form of the theorem
  recalls analz_image_freshK, but it is much more complicated.*)


(*As with analz_image_freshK, we take some pains to express the property
  as a logical equivalence so that the simplifier can apply it.*)
Goal "P --> (X \\<in> analz (G Un H)) --> (X \\<in> analz H)  ==> \
\     P --> (X \\<in> analz (G Un H)) = (X \\<in> analz H)";
by (blast_tac (claset() addIs [impOfSubs analz_mono]) 1);
val Nonce_secrecy_lemma = result();

Goal "evs \\<in> yahalom ==>                                      \
\     (\\<forall>KK. KK <= - (range shrK) -->                      \
\          (\\<forall>K \\<in> KK. ~ KeyWithNonce K NB evs)   -->        \
\          (Nonce NB \\<in> analz (Key`KK Un (knows Spy evs))) =     \
\          (Nonce NB \\<in> analz (knows Spy evs)))";
by (etac yahalom.induct 1);
by analz_knows_Spy_tac;
by (REPEAT_FIRST (resolve_tac [impI RS allI]));
by (REPEAT_FIRST (rtac Nonce_secrecy_lemma));
(*For Oops, simplification proves NBa\\<noteq>NB.  By Says_Server_KeyWithNonce,
  we get (~ KeyWithNonce K NB evs); then simplification can apply the
  induction hypothesis with KK = {K}.*)
by (ALLGOALS  (*4 seconds*)
    (asm_simp_tac 
     (analz_image_freshK_ss 
       addsimps split_ifs
       addsimps [all_conj_distrib, ball_conj_distrib, analz_image_freshK,
		 KeyWithNonce_Says, KeyWithNonce_Notes, KeyWithNonce_Gets,
		 fresh_not_KeyWithNonce, Says_Server_not_range,
		 imp_disj_not1,		     (*Moves NBa\\<noteq>NB to the front*)
		 Says_Server_KeyWithNonce])));
(*Fake*) 
by (spy_analz_tac 1);
(*YM4*)  (** LEVEL 6 **)
by (thin_tac "\\<forall>KK. ?P KK" 1);
by (Clarify_tac 1);  
(*If A:bad then NBa is known, therefore NBa \\<noteq> NB.  Previous two steps make
  the next step faster.*)
by (blast_tac (claset() addSDs [Gets_imp_Says, Says_imp_spies, 
                                Crypt_Spy_analz_bad]
           addDs [analz.Inj,
                  parts.Inj RS parts.Fst RS A_trusts_YM3 RS KeyWithNonceI]) 1);
qed_spec_mp "Nonce_secrecy";


(*Version required below: if NB can be decrypted using a session key then it
  was distributed with that key.  The more general form above is required
  for the induction to carry through.*)
Goal "[| Says Server A                                               \
\         {|Crypt (shrK A) {|Agent B, Key KAB, na, Nonce NB'|}, X|}  \
\        \\<in> set evs;                                                  \
\        NB \\<noteq> NB';  KAB \\<notin> range shrK;  evs \\<in> yahalom |]            \
\     ==> (Nonce NB \\<in> analz (insert (Key KAB) (knows Spy evs))) =        \
\         (Nonce NB \\<in> analz (knows Spy evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps 
		  [Nonce_secrecy, Says_Server_KeyWithNonce]) 1);
qed "single_Nonce_secrecy";


(*** The Nonce NB uniquely identifies B's message. ***)

Goal "[| Crypt (shrK B) {|Agent A, Nonce NA, nb|} \\<in> parts (knows Spy evs);    \
\        Crypt (shrK B') {|Agent A', Nonce NA', nb|} \\<in> parts (knows Spy evs); \
\       evs \\<in> yahalom;  B \\<notin> bad;  B' \\<notin> bad |]  \
\     ==> NA' = NA & A' = A & B' = B";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
(*YM2, by freshness*)
by (blast_tac (claset() addSEs knows_Spy_partsEs) 1);
qed "unique_NB";


(*Variant useful for proving secrecy of NB.  Because nb is assumed to be 
  secret, we no longer must assume B, B' not bad.*)
Goal "[| Says C S   {|X,  Crypt (shrK B) {|Agent A, Nonce NA, nb|}|}    \
\          \\<in> set evs;                          \
\        Gets S' {|X', Crypt (shrK B') {|Agent A', Nonce NA', nb|}|}    \
\          \\<in> set evs;                                                   \
\        nb \\<notin> analz (knows Spy evs);  evs \\<in> yahalom |]                 \
\     ==> NA' = NA & A' = A & B' = B";
by (blast_tac (claset() addSDs [Gets_imp_Says, Crypt_Spy_analz_bad]
			addDs  [Says_imp_spies, unique_NB, parts.Inj, 
                                analz.Inj]) 1);
qed "Says_unique_NB";


(** A nonce value is never used both as NA and as NB **)

Goal "evs \\<in> yahalom                     \
\ ==> Nonce NB \\<notin> analz (knows Spy evs) -->    \
\  Crypt (shrK B') {|Agent A', Nonce NB, nb'|} \\<in> parts(knows Spy evs) --> \
\  Crypt (shrK B)  {|Agent A, na, Nonce NB|} \\<notin> parts(knows Spy evs)";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
by (blast_tac (claset() addDs [Gets_imp_knows_Spy RS analz.Inj]
                        addSIs [parts_insertI]
                        addSDs [parts.Body]) 1);
bind_thm ("no_nonce_YM1_YM2", result() RS mp RSN (2,rev_mp) RSN (2,rev_notE));

(*more readable version cited in Yahalom paper*)
standard (result() RS mp RSN (2,rev_mp));

(*The Server sends YM3 only in response to YM2.*)
Goal "[| Says Server A                                                \
\         {|Crypt (shrK A) {|Agent B, k, na, nb|}, X|} \\<in> set evs;     \
\        evs \\<in> yahalom |]                                             \
\     ==> Gets Server {| Agent B, Crypt (shrK B) {|Agent A, na, nb|} |} \
\            \\<in> set evs";
by (etac rev_mp 1);
by (etac yahalom.induct 1);
by Auto_tac;
qed "Says_Server_imp_YM2";


(*A vital theorem for B, that nonce NB remains secure from the Spy.*)
Goal "[| A \\<notin> bad;  B \\<notin> bad;  evs \\<in> yahalom |]  \
\ ==> (\\<forall>k. Notes Spy {|Nonce NA, Nonce NB, k|} \\<notin> set evs) -->      \
\  Says B Server                                                    \
\       {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|} \
\  \\<in> set evs -->                                                    \
\  Nonce NB \\<notin> analz (knows Spy evs)";
by (etac yahalom.induct 1);
by analz_knows_Spy_tac;
by (ALLGOALS
    (asm_simp_tac 
     (simpset() addsimps split_ifs @ pushes @
               [new_keys_not_analzd, analz_insert_eq, analz_insert_freshK])));
(*Prove YM3 by showing that no NB can also be an NA*)
by (blast_tac (claset() addDs [Says_imp_knows_Spy RS parts.Inj]
	                addSEs [no_nonce_YM1_YM2, MPair_parts]
		        addDs  [Gets_imp_Says, Says_unique_NB]) 4);
(*YM2: similar freshness reasoning*) 
by (blast_tac (claset() addSDs [parts.Body]
		        addDs  [Gets_imp_Says,
				Says_imp_knows_Spy RS analz.Inj,
				impOfSubs analz_subset_parts]) 3);
(*YM1: NB=NA is impossible anyway, but NA is secret because it is fresh!*)
by (blast_tac (claset() addSIs [parts_insertI]
                        addSEs knows_Spy_partsEs) 2);
(*Fake*)
by (spy_analz_tac 1);
(** LEVEL 7: YM4 and Oops remain **)
by (ALLGOALS (Clarify_tac THEN' 
	      full_simp_tac (simpset() addsimps [all_conj_distrib])));
(*YM4: key K is visible to Spy, contradicting session key secrecy theorem*) 
(*Case analysis on Aa:bad; PROOF FAILED problems;
  use Says_unique_NB to identify message components: Aa=A, Ba=B*)  
by (blast_tac (claset() addSDs [Says_unique_NB, 
                                parts.Inj RS parts.Fst RS A_trusts_YM3]
			addDs [Gets_imp_knows_Spy RS analz.Inj, Gets_imp_Says,
                               Says_imp_spies, Says_Server_imp_YM2,
			       Spy_not_see_encrypted_key]) 1);
(** LEVEL 9 **)
(*Oops case: if the nonce is betrayed now, show that the Oops event is 
  covered by the quantified Oops assumption.*)
by (ftac Says_Server_imp_YM2 1 THEN assume_tac 1);  
by (case_tac "NB = NBa" 1);
(*If NB=NBa then all other components of the Oops message agree*)
by (blast_tac (claset() addDs [Says_unique_NB]) 1);
(*case NB \\<noteq> NBa*)
by (asm_simp_tac (simpset() addsimps [single_Nonce_secrecy]) 1);
by (blast_tac (claset() addSEs [no_nonce_YM1_YM2] (*to prove NB\\<noteq>NAa*)
		        addDs  [Says_imp_knows_Spy RS parts.Inj]) 1);
bind_thm ("Spy_not_see_NB", result() RSN(2,rev_mp) RSN(2,rev_mp));


(*B's session key guarantee from YM4.  The two certificates contribute to a
  single conclusion about the Server's message.  Note that the "Notes Spy"
  assumption must quantify over \\<forall>POSSIBLE keys instead of our particular K.
  If this run is broken and the spy substitutes a certificate containing an
  old key, B has no means of telling.*)
Goal "[| Gets B {|Crypt (shrK B) {|Agent A, Key K|},                  \
\                    Crypt K (Nonce NB)|} \\<in> set evs;                     \
\        Says B Server                                                   \
\          {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}   \
\          \\<in> set evs;                                                    \
\        \\<forall>k. Notes Spy {|Nonce NA, Nonce NB, k|} \\<notin> set evs;          \
\        A \\<notin> bad;  B \\<notin> bad;  evs \\<in> yahalom |]       \
\      ==> Says Server A                                                 \
\                  {|Crypt (shrK A) {|Agent B, Key K,                    \
\                            Nonce NA, Nonce NB|},                       \
\                    Crypt (shrK B) {|Agent A, Key K|}|}                 \
\            \\<in> set evs";
by (blast_tac (claset() addDs [Spy_not_see_NB, Says_unique_NB,
                               Says_Server_imp_YM2, B_trusts_YM4_newK]) 1);
qed "B_trusts_YM4";


(*The obvious combination of B_trusts_YM4 with Spy_not_see_encrypted_key*)
Goal "[| Gets B {|Crypt (shrK B) {|Agent A, Key K|},                  \
\                    Crypt K (Nonce NB)|} \\<in> set evs;                     \
\        Says B Server                                                   \
\          {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}   \
\          \\<in> set evs;                                                    \
\        \\<forall>k. Notes Spy {|Nonce NA, Nonce NB, k|} \\<notin> set evs;          \
\        A \\<notin> bad;  B \\<notin> bad;  evs \\<in> yahalom |]                \
\     ==> Key K \\<notin> analz (knows Spy evs)";
by (blast_tac (claset() addSDs [B_trusts_YM4, Spy_not_see_encrypted_key]) 1);
qed "B_gets_good_key";


(*** Authenticating B to A ***)

(*The encryption in message YM2 tells us it cannot be faked.*)
Goal "evs \\<in> yahalom                                            \
\  ==> Crypt (shrK B) {|Agent A, Nonce NA, nb|} \\<in> parts (knows Spy evs) --> \
\   B \\<notin> bad -->                                              \
\   Says B Server {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, nb|}|}  \
\      \\<in> set evs";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
bind_thm ("B_Said_YM2", result() RSN (2, rev_mp) RS mp);

(*If the server sends YM3 then B sent YM2*)
Goal "evs \\<in> yahalom                                                      \
\  ==> Says Server A {|Crypt (shrK A) {|Agent B, Key K, Nonce NA, nb|}, X|} \
\      \\<in> set evs -->                                                     \
\   B \\<notin> bad -->                                                        \
\   Says B Server {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, nb|}|}  \
\              \\<in> set evs";
by (etac yahalom.induct 1);
by (ALLGOALS Asm_simp_tac);
(*YM4*)
by (Blast_tac 2);
(*YM3*)
by (blast_tac (claset() addSDs [B_Said_YM2, 
                                Says_imp_knows_Spy RS parts.Inj]) 1);
val lemma = result() RSN (2, rev_mp) RS mp |> standard;

(*If A receives YM3 then B has used nonce NA (and therefore is alive)*)
Goal "[| Gets A {|Crypt (shrK A) {|Agent B, Key K, Nonce NA, nb|}, X|} \
\          \\<in> set evs;                                                    \
\        A \\<notin> bad;  B \\<notin> bad;  evs \\<in> yahalom |]                        \
\==> Says B Server {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, nb|}|} \
\      \\<in> set evs";
by (blast_tac (claset() addSDs [A_trusts_YM3, lemma]
		        addEs knows_Spy_partsEs) 1);
qed "YM3_auth_B_to_A";


(*** Authenticating A to B using the certificate Crypt K (Nonce NB) ***)

(*Assuming the session key is secure, if both certificates are present then
  A has said NB.  We can't be sure about the rest of A's message, but only
  NB matters for freshness.*)  
Goal "evs \\<in> yahalom                                             \
\     ==> Key K \\<notin> analz (knows Spy evs) -->                     \
\         Crypt K (Nonce NB) \\<in> parts (knows Spy evs) -->         \
\         Crypt (shrK B) {|Agent A, Key K|} \\<in> parts (knows Spy evs) --> \
\         B \\<notin> bad -->                                         \
\         (\\<exists>X. Says A B {|X, Crypt K (Nonce NB)|} \\<in> set evs)";
by (parts_induct_tac 1);
(*Fake*)
by (Fake_parts_insert_tac 1);
(*YM3: by new_keys_not_used we note that Crypt K (Nonce NB) could not exist*)
by (fast_tac (claset() addSDs [Crypt_imp_keysFor] addss (simpset())) 1); 
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
Goal "[| Gets B {|Crypt (shrK B) {|Agent A, Key K|},                  \
\                 Crypt K (Nonce NB)|} \\<in> set evs;                     \
\        Says B Server                                                   \
\          {|Agent B, Crypt (shrK B) {|Agent A, Nonce NA, Nonce NB|}|}   \
\          \\<in> set evs;                                                    \
\        (\\<forall>NA k. Notes Spy {|Nonce NA, Nonce NB, k|} \\<notin> set evs);     \
\        A \\<notin> bad;  B \\<notin> bad;  evs \\<in> yahalom |]       \
\     ==> \\<exists>X. Says A B {|X, Crypt K (Nonce NB)|} \\<in> set evs";
by (blast_tac (claset() addSIs [A_Said_YM3_lemma]
                   addDs [Spy_not_see_encrypted_key, B_trusts_YM4,
                          Gets_imp_Says, Says_imp_knows_Spy RS parts.Inj]) 1);
qed_spec_mp "YM4_imp_A_Said_YM3";
