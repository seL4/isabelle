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


(*A "possibility property": there are traces that reach the end*)
goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\        ==> EX X NB K. EX evs: yahalom lost.          \
\               Says A B {|X, Crypt K (Nonce NB)|} : set_of_list evs";
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
    (best_tac (!claset addIs (impOfSubs (sees_mono RS analz_mono RS synth_mono)
                              :: yahalom.intrs))));
qed "yahalom_mono";


(*Nobody sends themselves messages*)
goal thy "!!evs. evs: yahalom lost ==> ALL A X. Says A A X ~: set_of_list evs";
by (etac yahalom.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(** For reasoning about the encrypted portion of messages **)

(*Lets us treat YM4 using a similar argument as for the Fake case.*)
goal thy "!!evs. Says S A {|NB, Crypt (shrK A) Y, X|} : set_of_list evs ==> \
\                X : analz (sees lost Spy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]) 1);
qed "YM4_analz_sees_Spy";

bind_thm ("YM4_parts_sees_Spy",
          YM4_analz_sees_Spy RS (impOfSubs analz_subset_parts));

(*Relates to both YM4 and Oops*)
goal thy "!!evs. Says S A {|NB, Crypt (shrK A) {|B, K, NA|}, X|} \
\                  : set_of_list evs ==> \
\                K : parts (sees lost Spy evs)";
by (fast_tac (!claset addSEs partsEs
                      addSDs [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "YM4_Key_parts_sees_Spy";

(*We instantiate the variable to "lost".  Leaving it as a Var makes proofs
  harder: the simplifier does less.*)
val parts_Fake_tac = 
    forw_inst_tac [("lost","lost")] YM4_parts_sees_Spy 6 THEN
    forw_inst_tac [("lost","lost")] YM4_Key_parts_sees_Spy 7;

(*For proving the easier theorems about X ~: parts (sees lost Spy evs) *)
fun parts_induct_tac i = SELECT_GOAL
    (DETERM (etac yahalom.induct 1 THEN parts_Fake_tac THEN
             (*Fake message*)
             TRY (best_tac (!claset addDs [impOfSubs analz_subset_parts,
                                           impOfSubs Fake_parts_insert]
                                    addss (!simpset)) 2)) THEN
     (*Base case*)
     fast_tac (!claset addss (!simpset)) 1 THEN
     ALLGOALS Asm_simp_tac) i;


(** Theorems of the form X ~: parts (sees lost Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's shared key! (unless it's lost at start)*)
goal thy 
 "!!evs. evs : yahalom lost \
\        ==> (Key (shrK A) : parts (sees lost Spy evs)) = (A : lost)";
by (parts_induct_tac 1);
by (Auto_tac());
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
by (fast_tac (!claset addDs [Spy_see_shrK]) 1);
qed "Spy_see_shrK_D";

bind_thm ("Spy_analz_shrK_D", analz_subset_parts RS subsetD RS Spy_see_shrK_D);
AddSDs [Spy_see_shrK_D, Spy_analz_shrK_D];


(*Nobody can have used non-existent keys!*)
goal thy "!!evs. evs : yahalom lost ==>          \
\         Key K ~: used evs --> K ~: keysFor (parts (sees lost Spy evs))";
by (parts_induct_tac 1);
(*YM4: Key K is not fresh!*)
by (fast_tac (!claset addSEs sees_Spy_partsEs) 3);
(*YM3*)
by (fast_tac (!claset addss (!simpset)) 2);
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
 "!!evs. [| Says Server A {|NB', Crypt (shrK A) {|Agent B, Key K, NA|}, X|} \
\            : set_of_list evs;                                         \
\           evs : yahalom lost |]                                       \
\        ==> K ~: range shrK & A ~= B";
by (etac rev_mp 1);
by (etac yahalom.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "Says_Server_message_form";


(*For proofs involving analz.  We again instantiate the variable to "lost".*)
val analz_Fake_tac = 
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
 "!!evs. evs : yahalom lost ==> \
\  ALL K KK. KK <= Compl (range shrK) -->                      \
\            (Key K : analz (Key``KK Un (sees lost Spy evs))) = \
\            (K : KK | Key K : analz (sees lost Spy evs))";
by (etac yahalom.induct 1);
by analz_Fake_tac;
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_freshK_lemma ));
by (ALLGOALS (asm_simp_tac analz_image_freshK_ss));
(*Base*)
by (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1);
(*YM4, Fake*) 
by (REPEAT (spy_analz_tac 1));
qed_spec_mp "analz_image_freshK";

goal thy
 "!!evs. [| evs : yahalom lost;  KAB ~: range shrK |] ==>             \
\        Key K : analz (insert (Key KAB) (sees lost Spy evs)) = \
\        (K = KAB | Key K : analz (sees lost Spy evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(*** The Key K uniquely identifies the Server's  message. **)

goal thy 
 "!!evs. evs : yahalom lost ==>                                     \
\      EX A' B' NA' NB' X'. ALL A B NA NB X.                        \
\          Says Server A                                            \
\           {|NB, Crypt (shrK A) {|Agent B, Key K, NA|}, X|}        \
\          : set_of_list evs --> A=A' & B=B' & NA=NA' & NB=NB' & X=X'";
by (etac yahalom.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib])));
by (Step_tac 1);
(*Remaining case: YM3*)
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
(*...we assume X is a recent message and handle this case by contradiction*)
by (fast_tac (!claset addSEs sees_Spy_partsEs
                      delrules [conjI]    (*prevent split-up into 4 subgoals*)
                      addss (!simpset addsimps [parts_insertI])) 1);
val lemma = result();

goal thy 
"!!evs. [| Says Server A                                            \
\           {|NB, Crypt (shrK A) {|Agent B, Key K, NA|}, X|}        \
\           : set_of_list evs;                                      \
\          Says Server A'                                           \
\           {|NB', Crypt (shrK A') {|Agent B', Key K, NA'|}, X'|}   \
\           : set_of_list evs;                                      \
\          evs : yahalom lost |]                                    \
\       ==> A=A' & B=B' & NA=NA' & NB=NB'";
by (prove_unique_tac lemma 1);
qed "unique_session_keys";


(** Crucial secrecy property: Spy does not see the keys sent in msg YM3 **)

goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  A ~= B;                          \
\           evs : yahalom lost |]            \
\        ==> Says Server A                                           \
\              {|NB, Crypt (shrK A) {|Agent B, Key K, NA|},           \
\                    Crypt (shrK B) {|NB, Key K, Agent A|}|}          \
\             : set_of_list evs -->                               \
\            Says A Spy {|NA, NB, Key K|} ~: set_of_list evs -->  \
\            Key K ~: analz (sees lost Spy evs)";
by (etac yahalom.induct 1);
by analz_Fake_tac;
by (ALLGOALS
    (asm_simp_tac 
     (!simpset addsimps [not_parts_not_analz, analz_insert_freshK]
               setloop split_tac [expand_if])));
(*YM3*)
by (fast_tac (!claset delrules [impCE]
                      addSEs sees_Spy_partsEs
                      addIs [impOfSubs analz_subset_parts]
                      addss (!simpset addsimps [parts_insert2])) 2);
(*OR4, Fake*) 
by (REPEAT_FIRST spy_analz_tac);
(*Oops*)
by (fast_tac (!claset delrules [disjE] 
                      addDs [unique_session_keys]
                      addss (!simpset)) 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);


(*Final version: Server's message in the most abstract form*)
goal thy 
 "!!evs. [| Says Server A                                         \
\              {|NB, Crypt (shrK A) {|Agent B, Key K, NA|},       \
\                    Crypt (shrK B) {|NB, Key K, Agent A|}|}      \
\           : set_of_list evs;                                    \
\           Says A Spy {|NA, NB, Key K|} ~: set_of_list evs;      \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |]         \
\        ==> Key K ~: analz (sees lost Spy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (fast_tac (!claset addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


goal thy 
 "!!evs. [| C ~: {A,B,Server};                                    \
\           Says Server A                                         \
\              {|NB, Crypt (shrK A) {|Agent B, Key K, NA|},       \
\                    Crypt (shrK B) {|NB, Key K, Agent A|}|}      \
\           : set_of_list evs;                                    \
\           Says A Spy {|NA, NB, Key K|} ~: set_of_list evs;      \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |]         \
\        ==> Key K ~: analz (sees lost C evs)";
by (rtac (subset_insertI RS sees_mono RS analz_mono RS contra_subsetD) 1);
by (rtac (sees_lost_agent_subset_sees_Spy RS analz_mono RS contra_subsetD) 1);
by (FIRSTGOAL (rtac Spy_not_see_encrypted_key));
by (REPEAT_FIRST (fast_tac (!claset addIs [yahalom_mono RS subsetD])));
qed "Agent_not_see_encrypted_key";


(*** Security Guarantees for A and B ***)

(*If the encrypted message appears then it originated with the Server.*)
goal thy
 "!!evs. [| Crypt (shrK A) {|Agent B, Key K, NA|}                \
\            : parts (sees lost Spy evs);                              \
\           A ~: lost;  evs : yahalom lost |]                          \
\         ==> EX NB. Says Server A                                     \
\                      {|NB, Crypt (shrK A) {|Agent B, Key K, NA|},    \
\                            Crypt (shrK B) {|NB, Key K, Agent A|}|}   \
\                    : set_of_list evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*The nested conjunctions are entirely useless*)
by (REPEAT_FIRST (rtac conjI ORELSE' fast_tac (!claset delrules [conjI])));
qed "A_trusts_YM3";


(*B knows, by the first part of A's message, that the Server distributed 
  the key for A and B. *)
goal thy 
 "!!evs. [| Crypt (shrK B) {|Nonce NB, Key K, Agent A|}              \
\            : parts (sees lost Spy evs);                            \
\           B ~: lost;  evs : yahalom lost |]                        \
\        ==> EX NA. Says Server A                                    \
\                    {|Nonce NB,                                     \
\                      Crypt (shrK A) {|Agent B, Key K, Nonce NA|},  \
\                      Crypt (shrK B) {|Nonce NB, Key K, Agent A|}|} \
\                       : set_of_list evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*YM3*)
by (Fast_tac 1);
qed "B_trusts_YM4_shrK";

(*With this variant we don't bother to use the 2nd part of YM4 at all, since
  Nonce NB is available in the first part.  However the 2nd part does assure B
  of A's existence.*)

(*What can B deduce from receipt of YM4?  Stronger and simpler than Yahalom
  because we do not have to show that NB is secret. *)
goal thy 
 "!!evs. [| Says A' B {|Crypt (shrK B) {|Nonce NB, Key K, Agent A|},    \
\                       Crypt K (Nonce NB)|} : set_of_list evs;         \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |]               \
\        ==> EX NA. Says Server A                                       \
\                    {|Nonce NB,                                        \
\                      Crypt (shrK A) {|Agent B, Key K, Nonce NA|},     \
\                      Crypt (shrK B) {|Nonce NB, Key K, Agent A|}|}    \
\                   : set_of_list evs";
by (etac (Says_imp_sees_Spy RS parts.Inj RS MPair_parts) 1);
by (fast_tac (!claset addSDs [B_trusts_YM4_shrK]) 1);
qed "B_trusts_YM4";
