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


(*Weak liveness: there are traces that reach the end*)

goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\        ==> EX X NB K. EX evs: yahalom lost.          \
\               Says A B {|X, Crypt (Nonce NB) K|} : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (yahalom.Nil RS yahalom.YM1 RS yahalom.YM2 RS yahalom.YM3 RS yahalom.YM4) 2);
by (ALLGOALS (simp_tac (!simpset setsolver safe_solver)));
by (ALLGOALS Fast_tac);
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
goal thy "!!evs. Says S A {|NB, Crypt Y (shrK A), X|} : set_of_list evs ==> \
\                X : analz (sees lost Spy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]) 1);
qed "YM4_analz_sees_Spy";

bind_thm ("YM4_parts_sees_Spy",
          YM4_analz_sees_Spy RS (impOfSubs analz_subset_parts));

(*Relates to both YM4 and Oops*)
goal thy "!!evs. Says S A {|NB, Crypt {|B, K, NA|} (shrK A), X|} \
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

(*Spy never sees another agent's shared key! (unless it is leaked at start)*)
goal thy 
 "!!evs. [| evs : yahalom lost;  A ~: lost |]    \
\        ==> Key (shrK A) ~: parts (sees lost Spy evs)";
by (parts_induct_tac 1);
by (Auto_tac());
qed "Spy_not_see_shrK";

bind_thm ("Spy_not_analz_shrK",
          [analz_subset_parts, Spy_not_see_shrK] MRS contra_subsetD);

Addsimps [Spy_not_see_shrK, Spy_not_analz_shrK];

(*We go to some trouble to preserve R in the 3rd and 4th subgoals
  As usual fast_tac cannot be used because it uses the equalities too soon*)
val major::prems = 
goal thy  "[| Key (shrK A) : parts (sees lost Spy evs);       \
\             evs : yahalom lost;                               \
\             A:lost ==> R                                  \
\           |] ==> R";
by (rtac ccontr 1);
by (rtac ([major, Spy_not_see_shrK] MRS rev_notE) 1);
by (swap_res_tac prems 2);
by (ALLGOALS (fast_tac (!claset addIs prems)));
qed "Spy_see_shrK_E";

bind_thm ("Spy_analz_shrK_E", 
          analz_subset_parts RS subsetD RS Spy_see_shrK_E);

AddSEs [Spy_see_shrK_E, Spy_analz_shrK_E];


(*** Future keys can't be seen or used! ***)

(*Nobody can have SEEN keys that will be generated in the future. *)
goal thy "!!evs. evs : yahalom lost ==> \
\                length evs <= length evs' --> \
\                Key (newK evs') ~: parts (sees lost Spy evs)";
by (parts_induct_tac 1);
by (REPEAT_FIRST (best_tac (!claset addEs [leD RS notE]
				    addDs [impOfSubs analz_subset_parts,
                                           impOfSubs parts_insert_subset_Un,
                                           Suc_leD]
                                    addss (!simpset))));
qed_spec_mp "new_keys_not_seen";
Addsimps [new_keys_not_seen];

(*Variant: old messages must contain old keys!*)
goal thy 
 "!!evs. [| Says A B X : set_of_list evs;  \
\           Key (newK evt) : parts {X};    \
\           evs : yahalom lost                 \
\        |] ==> length evt < length evs";
by (rtac ccontr 1);
by (dtac leI 1);
by (fast_tac (!claset addSDs [new_keys_not_seen, Says_imp_sees_Spy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_keys";


(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : yahalom lost ==> \
\                length evs <= length evs' --> \
\                newK evs' ~: keysFor (parts (sees lost Spy evs))";
by (parts_induct_tac 1);
by (dtac YM4_Key_parts_sees_Spy 5);
(*YM1, YM2 and YM3*)
by (EVERY (map (fast_tac (!claset addDs [Suc_leD] addss (!simpset))) [4,3,2]));
(*Fake and Oops: these messages send unknown (X) components*)
by (EVERY
    (map (fast_tac
          (!claset addDs [impOfSubs analz_subset_parts,
                          impOfSubs (analz_subset_parts RS keysFor_mono),
                          impOfSubs (parts_insert_subset_Un RS keysFor_mono),
                          Suc_leD]
                   addss (!simpset))) [3,1]));
(*YM4: if K was used then it had been seen, contradicting new_keys_not_seen*)
by (fast_tac
      (!claset addSEs partsEs
               addSDs [Says_imp_sees_Spy RS parts.Inj]
               addEs [new_keys_not_seen RSN(2,rev_notE)]
               addDs [Suc_leD]) 1);
qed_spec_mp "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];


(*Describes the form of K when the Server sends this message.  Useful for
  Oops as well as main secrecy property.*)
goal thy 
 "!!evs. [| Says Server A {|NB', Crypt {|Agent B, K, NA|} (shrK A), X|} \
\            : set_of_list evs;                                         \
\           evs : yahalom lost |]                                       \
\        ==> (EX evt: yahalom lost. K = Key(newK evt)) & A ~= B";
by (etac rev_mp 1);
by (etac yahalom.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "Says_Server_message_form";


(*For proofs involving analz.  We again instantiate the variable to "lost".*)
val analz_Fake_tac = 
    dres_inst_tac [("lost","lost")] YM4_analz_sees_Spy 6 THEN
    forw_inst_tac [("lost","lost")] Says_Server_message_form 7 THEN
    assume_tac 7 THEN Full_simp_tac 7 THEN
    REPEAT ((eresolve_tac [bexE,conjE] ORELSE' hyp_subst_tac) 7);


(****
 The following is to prove theorems of the form

          Key K : analz (insert (Key (newK evt)) (sees lost Spy evs)) ==>
          Key K : analz (sees lost Spy evs)

 A more general formula must be proved inductively.

****)

(** Session keys are not used to encrypt other session keys **)

goal thy  
 "!!evs. evs : yahalom lost ==> \
\  ALL K E. (Key K : analz (Key``(newK``E) Un (sees lost Spy evs))) = \
\           (K : newK``E | Key K : analz (sees lost Spy evs))";
by (etac yahalom.induct 1);
by analz_Fake_tac;
by (REPEAT_FIRST (resolve_tac [allI, analz_image_newK_lemma]));
by (ALLGOALS  (*Takes 26 secs*)
    (asm_simp_tac 
     (!simpset addsimps ([insert_Key_singleton, insert_Key_image, pushKey_newK]
                         @ pushes)
               setloop split_tac [expand_if])));
(*YM4, Fake*) 
by (EVERY (map spy_analz_tac [4, 2]));
(*Oops, YM3, Base*)
by (REPEAT (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1));
qed_spec_mp "analz_image_newK";

goal thy
 "!!evs. evs : yahalom lost ==>                               \
\        Key K : analz (insert (Key (newK evt)) (sees lost Spy evs)) = \
\        (K = newK evt | Key K : analz (sees lost Spy evs))";
by (asm_simp_tac (HOL_ss addsimps [pushKey_newK, analz_image_newK, 
                                   insert_Key_singleton]) 1);
by (Fast_tac 1);
qed "analz_insert_Key_newK";


(*** The Key K uniquely identifies the Server's  message. **)

goal thy 
 "!!evs. evs : yahalom lost ==>                                     \
\      EX A' B' NA' NB' X'. ALL A B NA NB X.                        \
\          Says Server A                                            \
\           {|NB, Crypt {|Agent B, Key K, NA|} (shrK A), X|}        \
\          : set_of_list evs --> A=A' & B=B' & NA=NA' & NB=NB' & X=X'";
by (etac yahalom.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib])));
by (Step_tac 1);
(*Remaining case: YM3*)
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
(*...we assume X is a very new message, and handle this case by contradiction*)
by (fast_tac (!claset addEs [Says_imp_old_keys RS less_irrefl]
                      delrules [conjI]    (*prevent split-up into 4 subgoals*)
                      addss (!simpset addsimps [parts_insertI])) 1);
val lemma = result();

goal thy 
"!!evs. [| Says Server A                                            \
\           {|NB, Crypt {|Agent B, Key K, NA|} (shrK A), X|}        \
\           : set_of_list evs;                                      \
\          Says Server A'                                           \
\           {|NB', Crypt {|Agent B', Key K, NA'|} (shrK A'), X'|}   \
\           : set_of_list evs;                                      \
\          evs : yahalom lost |]                                    \
\       ==> A=A' & B=B' & NA=NA' & NB=NB'";
by (dtac lemma 1);
by (REPEAT (etac exE 1));
(*Duplicate the assumption*)
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
by (fast_tac (!claset addSDs [spec]) 1);
qed "unique_session_keys";


(** Crucial secrecy property: Spy does not see the keys sent in msg YM3 **)

goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  A ~= B;                          \
\           evs : yahalom lost |]            \
\        ==> Says Server A                                           \
\              {|NB, Crypt {|Agent B, Key K, NA|} (shrK A),           \
\                    Crypt {|NB, Key K, Agent A|} (shrK B)|}          \
\             : set_of_list evs -->                               \
\            Says A Spy {|NA, NB, Key K|} ~: set_of_list evs -->  \
\            Key K ~: analz (sees lost Spy evs)";
by (etac yahalom.induct 1);
by analz_Fake_tac;
by (ALLGOALS
    (asm_simp_tac 
     (!simpset addsimps ([analz_subset_parts RS contra_subsetD,
                          analz_insert_Key_newK] @ pushes)
               setloop split_tac [expand_if])));
(*YM3*)
by (fast_tac (!claset addIs [parts_insertI]
                      addEs [Says_imp_old_keys RS less_irrefl]
                      addss (!simpset)) 2);
(*OR4, Fake*) 
by (REPEAT_FIRST (resolve_tac [conjI, impI] ORELSE' spy_analz_tac));
(*Oops*)
by (fast_tac (!claset delrules [disjE] 
                      addDs [unique_session_keys]
                      addss (!simpset)) 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);


(*Final version: Server's message in the most abstract form*)
goal thy 
 "!!evs. [| Says Server A                                         \
\              {|NB, Crypt {|Agent B, K, NA|} (shrK A),           \
\                    Crypt {|NB, K, Agent A|} (shrK B)|}          \
\           : set_of_list evs;                                    \
\           Says A Spy {|NA, NB, K|} ~: set_of_list evs;          \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |]         \
\        ==> K ~: analz (sees lost Spy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (fast_tac (!claset addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


goal thy 
 "!!evs. [| C ~: {A,B,Server};                                    \
\           Says Server A                                         \
\              {|NB, Crypt {|Agent B, K, NA|} (shrK A),           \
\                    Crypt {|NB, K, Agent A|} (shrK B)|}          \
\           : set_of_list evs;                                    \
\           Says A Spy {|NA, NB, K|} ~: set_of_list evs;          \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |]         \
\        ==> K ~: analz (sees lost C evs)";
by (rtac (subset_insertI RS sees_mono RS analz_mono RS contra_subsetD) 1);
by (rtac (sees_lost_agent_subset_sees_Spy RS analz_mono RS contra_subsetD) 1);
by (FIRSTGOAL (rtac Spy_not_see_encrypted_key));
by (REPEAT_FIRST (fast_tac (!claset addIs [yahalom_mono RS subsetD])));
qed "Agent_not_see_encrypted_key";


(*** Security Guarantees for A and B ***)

(*If the encrypted message appears then it originated with the Server.*)
goal thy
 "!!evs. [| Crypt {|Agent B, Key K, NA|} (shrK A)                \
\            : parts (sees lost Spy evs);                              \
\           A ~: lost;  evs : yahalom lost |]                          \
\         ==> EX NB. Says Server A                                     \
\                      {|NB, Crypt {|Agent B, Key K, NA|} (shrK A),    \
\                            Crypt {|NB, Key K, Agent A|} (shrK B)|}   \
\                    : set_of_list evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*The nested conjunctions are entirely useless*)
by (REPEAT_FIRST (rtac conjI ORELSE' fast_tac (!claset delrules [conjI])));
qed "A_trust_YM3";


(*B knows, by the first part of A's message, that the Server distributed 
  the key for A and B. *)
goal thy 
 "!!evs. [| Crypt {|Nonce NB, Key K, Agent A|} (shrK B)              \
\            : parts (sees lost Spy evs);                            \
\           B ~: lost;  evs : yahalom lost |]                        \
\        ==> EX NA. Says Server A                                    \
\                    {|Nonce NB,                                     \
\                      Crypt {|Agent B, Key K, Nonce NA|} (shrK A),  \
\                      Crypt {|Nonce NB, Key K, Agent A|} (shrK B)|} \
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
 "!!evs. [| Says A' B {|Crypt {|Nonce NB, Key K, Agent A|} (shrK B),    \
\                       Crypt (Nonce NB) K|} : set_of_list evs;         \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |]               \
\        ==> EX NA. Says Server A                                       \
\                    {|Nonce NB,                                        \
\                      Crypt {|Agent B, Key K, Nonce NA|} (shrK A),     \
\                      Crypt {|Nonce NB, Key K, Agent A|} (shrK B)|}    \
\                   : set_of_list evs";
by (etac (Says_imp_sees_Spy RS parts.Inj RS MPair_parts) 1);
by (fast_tac (!claset addSDs [B_trusts_YM4_shrK]) 1);
qed "B_trust_YM4";
