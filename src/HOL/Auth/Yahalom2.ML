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

open Yahalom2;

proof_timing:=true;
HOL_quantifiers := false;

(*Replacing the variable by a constant improves speed*)
val Says_imp_sees_Spy' = read_instantiate [("lost","lost")] Says_imp_sees_Spy;


(*A "possibility property": there are traces that reach the end*)
goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]        \
\        ==> EX X NB K. EX evs: yahalom lost.          \
\               Says A B {|X, Crypt K (Nonce NB)|} : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (yahalom.Nil RS yahalom.YM1 RS yahalom.YM2 RS yahalom.YM3 RS 
          yahalom.YM4) 2);
by possibility_tac;
result();


(**** Inductive proofs about yahalom ****)

(*Monotonicity*)
goal thy "!!evs. lost' <= lost ==> yahalom lost' <= yahalom lost";
by (rtac subsetI 1);
by (etac yahalom.induct 1);
by (REPEAT_FIRST
    (blast_tac (!claset addIs (impOfSubs(sees_mono RS analz_mono RS synth_mono)
			       :: yahalom.intrs))));
qed "yahalom_mono";


(*Nobody sends themselves messages*)
goal thy "!!evs. evs: yahalom lost ==> ALL A X. Says A A X ~: set evs";
by (etac yahalom.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(** For reasoning about the encrypted portion of messages **)

(*Lets us treat YM4 using a similar argument as for the Fake case.*)
goal thy "!!evs. Says S A {|NB, Crypt (shrK A) Y, X|} : set evs ==> \
\                X : analz (sees lost Spy evs)";
by (blast_tac (!claset addSDs [Says_imp_sees_Spy' RS analz.Inj]) 1);
qed "YM4_analz_sees_Spy";

bind_thm ("YM4_parts_sees_Spy",
          YM4_analz_sees_Spy RS (impOfSubs analz_subset_parts));

(*Relates to both YM4 and Oops*)
goal thy "!!evs. Says S A {|NB, Crypt (shrK A) {|B,K,NA|}, X|} : set evs ==> \
\                K : parts (sees lost Spy evs)";
by (blast_tac (!claset addSEs partsEs
                       addSDs [Says_imp_sees_Spy' RS parts.Inj]) 1);
qed "YM4_Key_parts_sees_Spy";

(*For proving the easier theorems about X ~: parts (sees lost Spy evs).
  We instantiate the variable to "lost" since leaving it as a Var would
  interfere with simplification.*)
val parts_sees_tac = 
    forw_inst_tac [("lost","lost")] YM4_parts_sees_Spy 6     THEN
    forw_inst_tac [("lost","lost")] YM4_Key_parts_sees_Spy 7 THEN
    prove_simple_subgoals_tac  1;

val parts_induct_tac = 
    etac yahalom.induct 1 THEN parts_sees_tac;


(** Theorems of the form X ~: parts (sees lost Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's shared key! (unless it's lost at start)*)
goal thy 
 "!!evs. evs : yahalom lost \
\        ==> (Key (shrK A) : parts (sees lost Spy evs)) = (A : lost)";
by parts_induct_tac;
by (Fake_parts_insert_tac 1);
by (Blast_tac 1);
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

goal thy 
 "!!evs. evs : yahalom lost \
\        ==> (Key (shrK A) : analz (sees lost Spy evs)) = (A : lost)";
by (auto_tac(!claset addDs [impOfSubs analz_subset_parts], !simpset));
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

goal thy  "!!A. [| Key (shrK A) : parts (sees lost Spy evs);       \
\                  evs : yahalom lost |] ==> A:lost";
by (blast_tac (!claset addDs [Spy_see_shrK]) 1);
qed "Spy_see_shrK_D";

bind_thm ("Spy_analz_shrK_D", analz_subset_parts RS subsetD RS Spy_see_shrK_D);
AddSDs [Spy_see_shrK_D, Spy_analz_shrK_D];


(*Nobody can have used non-existent keys!  Needed to apply analz_insert_Key*)
goal thy "!!evs. evs : yahalom lost ==>          \
\         Key K ~: used evs --> K ~: keysFor (parts (sees lost Spy evs))";
by parts_induct_tac;
(*YM4: Key K is not fresh!*)
by (blast_tac (!claset addSEs sees_Spy_partsEs) 3);
(*YM3*)
by (blast_tac (!claset addss (!simpset)) 2);
(*Fake*)
by (best_tac
      (!claset addIs [impOfSubs analz_subset_parts]
               addDs [impOfSubs (analz_subset_parts RS keysFor_mono),
                      impOfSubs (parts_insert_subset_Un RS keysFor_mono)]
               addss (!simpset)) 1);
qed_spec_mp "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];

(*Describes the form of K when the Server sends this message.  Useful for
  Oops as well as main secrecy property.*)
goal thy 
 "!!evs. [| Says Server A {|nb', Crypt (shrK A) {|Agent B, Key K, na|}, X|} \
\            : set evs;                                                 \
\           evs : yahalom lost |]                                       \
\        ==> K ~: range shrK & A ~= B";
by (etac rev_mp 1);
by (etac yahalom.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "Says_Server_message_form";


(*For proofs involving analz.  We again instantiate the variable to "lost".*)
val analz_sees_tac = 
    dres_inst_tac [("lost","lost")] YM4_analz_sees_Spy 6 THEN
    forw_inst_tac [("lost","lost")] Says_Server_message_form 7 THEN
    assume_tac 7 THEN
    REPEAT ((etac conjE ORELSE' hyp_subst_tac) 7);


(****
 The following is to prove theorems of the form

          Key K : analz (insert (Key KAB) (sees lost Spy evs)) ==>
          Key K : analz (sees lost Spy evs)

 A more general formula must be proved inductively.

****)

(** Session keys are not used to encrypt other session keys **)

goal thy  
 "!!evs. evs : yahalom lost ==>                                  \
\  ALL K KK. KK <= Compl (range shrK) -->                        \
\            (Key K : analz (Key``KK Un (sees lost Spy evs))) =  \
\            (K : KK | Key K : analz (sees lost Spy evs))";
by (etac yahalom.induct 1);
by analz_sees_tac;
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_freshK_lemma ));
by (ALLGOALS (asm_simp_tac analz_image_freshK_ss));
(*Fake*) 
by (spy_analz_tac 2);
(*Base*)
by (Blast_tac 1);
qed_spec_mp "analz_image_freshK";

goal thy
 "!!evs. [| evs : yahalom lost;  KAB ~: range shrK |] ==>             \
\        Key K : analz (insert (Key KAB) (sees lost Spy evs)) =       \
\        (K = KAB | Key K : analz (sees lost Spy evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(*** The Key K uniquely identifies the Server's  message. **)

goal thy 
 "!!evs. evs : yahalom lost ==>                                     \
\      EX A' B' na' nb' X'. ALL A B na nb X.                        \
\          Says Server A                                            \
\           {|nb, Crypt (shrK A) {|Agent B, Key K, na|}, X|}        \
\          : set evs --> A=A' & B=B' & na=na' & nb=nb' & X=X'";
by (etac yahalom.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib])));
by (Step_tac 1);
(*Remaining case: YM3*)
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
(*...we assume X is a recent message and handle this case by contradiction*)
by (blast_tac (!claset addSEs sees_Spy_partsEs
                      delrules [conjI]    (*prevent split-up into 4 subgoals*)
                      addss (!simpset addsimps [parts_insertI])) 1);
val lemma = result();

goal thy 
"!!evs. [| Says Server A                                            \
\           {|nb, Crypt (shrK A) {|Agent B, Key K, na|}, X|}        \
\           : set evs;                                              \
\          Says Server A'                                           \
\           {|nb', Crypt (shrK A') {|Agent B', Key K, na'|}, X'|}   \
\           : set evs;                                              \
\          evs : yahalom lost |]                                    \
\       ==> A=A' & B=B' & na=na' & nb=nb'";
by (prove_unique_tac lemma 1);
qed "unique_session_keys";


(** Crucial secrecy property: Spy does not see the keys sent in msg YM3 **)

goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  A ~= B;                          \
\           evs : yahalom lost |]                                    \
\        ==> Says Server A                                           \
\              {|nb, Crypt (shrK A) {|Agent B, Key K, na|},          \
\                    Crypt (shrK B) {|nb, Key K, Agent A|}|}         \
\             : set evs -->                                          \
\            Says A Spy {|na, nb, Key K|} ~: set evs -->             \
\            Key K ~: analz (sees lost Spy evs)";
by (etac yahalom.induct 1);
by analz_sees_tac;
by (ALLGOALS
    (asm_simp_tac 
     (!simpset addsimps [analz_insert_eq, not_parts_not_analz, 
			 analz_insert_freshK]
               setloop split_tac [expand_if])));
(*Oops*)
by (blast_tac (!claset addDs [unique_session_keys]) 3);
(*YM3*)
by (blast_tac (!claset delrules [impCE]
                       addSEs sees_Spy_partsEs
                       addIs [impOfSubs analz_subset_parts]) 2);
(*Fake*) 
by (spy_analz_tac 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);


(*Final version*)
goal thy 
 "!!evs. [| Says Server A                                         \
\              {|nb, Crypt (shrK A) {|Agent B, Key K, na|},       \
\                    Crypt (shrK B) {|nb, Key K, Agent A|}|}      \
\           : set evs;                                            \
\           Says A Spy {|na, nb, Key K|} ~: set evs;              \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |]         \
\        ==> Key K ~: analz (sees lost Spy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (blast_tac (!claset addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


(*And other agents don't see the key either.*)
goal thy 
 "!!evs. [| C ~: {A,B,Server};                                    \
\           Says Server A                                         \
\              {|nb, Crypt (shrK A) {|Agent B, Key K, na|},       \
\                    Crypt (shrK B) {|nb, Key K, Agent A|}|}      \
\           : set evs;                                            \
\           Says A Spy {|na, nb, Key K|} ~: set evs;              \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |]         \
\        ==> Key K ~: analz (sees lost C evs)";
by (rtac (subset_insertI RS sees_mono RS analz_mono RS contra_subsetD) 1);
by (rtac (sees_lost_agent_subset_sees_Spy RS analz_mono RS contra_subsetD) 1);
by (FIRSTGOAL (rtac Spy_not_see_encrypted_key));
by (REPEAT_FIRST (blast_tac (!claset addIs [yahalom_mono RS subsetD])));
qed "Agent_not_see_encrypted_key";


(** Security Guarantee for A upon receiving YM3 **)

(*If the encrypted message appears then it originated with the Server.
  May now apply Spy_not_see_encrypted_key, subject to its conditions.*)
goal thy
 "!!evs. [| Crypt (shrK A) {|Agent B, Key K, na|}                      \
\            : parts (sees lost Spy evs);                              \
\           A ~: lost;  evs : yahalom lost |]                          \
\         ==> EX nb. Says Server A                                     \
\                      {|nb, Crypt (shrK A) {|Agent B, Key K, na|},    \
\                            Crypt (shrK B) {|nb, Key K, Agent A|}|}   \
\                    : set evs";
by (etac rev_mp 1);
by parts_induct_tac;
by (Fake_parts_insert_tac 1);
by (Blast_tac 1);
qed "A_trusts_YM3";


(** Security Guarantee for B upon receiving YM4 **)

(*B knows, by the first part of A's message, that the Server distributed 
  the key for A and B, and has associated it with NB. *)
goal thy 
 "!!evs. [| Crypt (shrK B) {|Nonce NB, Key K, Agent A|}              \
\            : parts (sees lost Spy evs);                            \
\           B ~: lost;  evs : yahalom lost |]                        \
\        ==> EX NA. Says Server A                                    \
\                    {|Nonce NB,                                     \
\                      Crypt (shrK A) {|Agent B, Key K, Nonce NA|},  \
\                      Crypt (shrK B) {|Nonce NB, Key K, Agent A|}|} \
\                       : set evs";
by (etac rev_mp 1);
by parts_induct_tac;
by (Fake_parts_insert_tac 1);
(*YM3*)
by (Blast_tac 1);
qed "B_trusts_YM4_shrK";


(*With this protocol variant, we don't need the 2nd part of YM4 at all:
  Nonce NB is available in the first part.*)

(*What can B deduce from receipt of YM4?  Stronger and simpler than Yahalom
  because we do not have to show that NB is secret. *)
goal thy 
 "!!evs. [| Says A' B {|Crypt (shrK B) {|Nonce NB, Key K, Agent A|}, X|} \
\             : set evs;                                                 \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |]                \
\        ==> EX NA. Says Server A                                        \
\                    {|Nonce NB,                                         \
\                      Crypt (shrK A) {|Agent B, Key K, Nonce NA|},      \
\                      Crypt (shrK B) {|Nonce NB, Key K, Agent A|}|}     \
\                   : set evs";
by (etac (Says_imp_sees_Spy' RS parts.Inj RS MPair_parts) 1);
by (blast_tac (!claset addSDs [B_trusts_YM4_shrK]) 1);
qed "B_trusts_YM4";



(*** Authenticating B to A ***)

(*The encryption in message YM2 tells us it cannot be faked.*)
goal thy 
 "!!evs. evs : yahalom lost                                            \
\  ==> Crypt (shrK B) {|Agent A, Nonce NA|} : parts (sees lost Spy evs) -->  \
\      B ~: lost -->                                                   \
\      (EX NB. Says B Server {|Agent B, Nonce NB,                      \
\                              Crypt (shrK B) {|Agent A, Nonce NA|}|}  \
\         : set evs)";
by parts_induct_tac;
by (Fake_parts_insert_tac 1);
(*YM2*)
by (Blast_tac 1);
bind_thm ("B_Said_YM2", result() RSN (2, rev_mp) RS mp);

(*If the server sends YM3 then B sent YM2, perhaps with a different NB*)
goal thy 
 "!!evs. evs : yahalom lost                                              \
\  ==> Says Server A {|nb, Crypt (shrK A) {|Agent B, Key K, Nonce NA|}, X|} \
\         : set evs -->                                                  \
\      B ~: lost -->                                                     \
\      (EX nb'. Says B Server {|Agent B, nb',                            \
\                               Crypt (shrK B) {|Agent A, Nonce NA|}|}   \
\                 : set evs)";
by (etac yahalom.induct 1);
by (ALLGOALS Asm_simp_tac);
(*YM3*)
by (blast_tac (!claset addSDs [B_Said_YM2]
		       addSEs [MPair_parts]
		       addDs [Says_imp_sees_Spy' RS parts.Inj]) 3);
(*Fake, YM2*)
by (ALLGOALS Blast_tac);
val lemma = result() RSN (2, rev_mp) RS mp |> standard;

(*If A receives YM3 then B has used nonce NA (and therefore is alive)*)
goal thy
 "!!evs. [| Says S A {|nb, Crypt (shrK A) {|Agent B, Key K, Nonce NA|}, X|} \
\             : set evs;                                                    \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |]                   \
\   ==> EX nb'. Says B Server                                               \
\                    {|Agent B, nb', Crypt (shrK B) {|Agent A, Nonce NA|}|} \
\                 : set evs";
by (blast_tac (!claset addSDs [A_trusts_YM3, lemma]
		       addEs sees_Spy_partsEs) 1);
qed "YM3_auth_B_to_A";


(*** Authenticating A to B using the certificate Crypt K (Nonce NB) ***)

(*Induction for theorems of the form X ~: analz (sees lost Spy evs) --> ...
  It simplifies the proof by discarding needless information about
	analz (insert X (sees lost Spy evs)) 
*)
val analz_mono_parts_induct_tac = 
    etac yahalom.induct 1 
    THEN 
    REPEAT_FIRST  
      (rtac impI THEN' 
       dtac (sees_subset_sees_Says RS analz_mono RS contra_subsetD) THEN'
       mp_tac)  
    THEN  parts_sees_tac;

(*Assuming the session key is secure, if both certificates are present then
  A has said NB.  We can't be sure about the rest of A's message, but only
  NB matters for freshness.*)  
goal thy 
 "!!evs. evs : yahalom lost                                             \
\        ==> Key K ~: analz (sees lost Spy evs) -->                     \
\            Crypt K (Nonce NB) : parts (sees lost Spy evs) -->         \
\            Crypt (shrK B) {|Nonce NB, Key K, Agent A|}                \
\              : parts (sees lost Spy evs) -->                          \
\            B ~: lost -->                                              \
\             (EX X. Says A B {|X, Crypt K (Nonce NB)|} : set evs)";
by analz_mono_parts_induct_tac;
(*Fake*)
by (Fake_parts_insert_tac 1);
(*YM3: by new_keys_not_used we note that Crypt K (Nonce NB) could not exist*)
by (fast_tac (!claset addSDs [Crypt_imp_invKey_keysFor] addss (!simpset)) 1); 
(*YM4: was Crypt K (Nonce NB) the very last message?  If not, use ind. hyp.*)
by (asm_simp_tac (!simpset addsimps [ex_disj_distrib]) 1);
(*yes: apply unicity of session keys*)
by (not_lost_tac "Aa" 1);
by (blast_tac (!claset addSEs [MPair_parts]
                       addSDs [A_trusts_YM3, B_trusts_YM4_shrK]
		       addDs  [Says_imp_sees_Spy' RS parts.Inj,
			       unique_session_keys]) 1);
val lemma = normalize_thm [RSspec, RSmp] (result()) |> standard;

(*If B receives YM4 then A has used nonce NB (and therefore is alive).
  Moreover, A associates K with NB (thus is talking about the same run).
  Other premises guarantee secrecy of K.*)
goal thy 
 "!!evs. [| Says A' B {|Crypt (shrK B) {|Nonce NB, Key K, Agent A|},    \
\                       Crypt K (Nonce NB)|} : set evs;                 \
\           (ALL NA. Says A Spy {|Nonce NA, Nonce NB, Key K|} ~: set evs); \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |]               \
\        ==> EX X. Says A B {|X, Crypt K (Nonce NB)|} : set evs";
by (etac (Says_imp_sees_Spy' RS parts.Inj RS MPair_parts) 1);
by (dtac B_trusts_YM4_shrK 1);
by (safe_tac (!claset));
by (rtac lemma 1);
by (rtac Spy_not_see_encrypted_key 2);
by (REPEAT_FIRST assume_tac);
by (ALLGOALS (blast_tac (!claset addSEs [MPair_parts]
			         addDs [Says_imp_sees_Spy' RS parts.Inj])));
qed_spec_mp "YM4_imp_A_Said_YM3";
