(*  Title:      HOL/Auth/OtwayRees
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "otway" for the Otway-Rees protocol.

Simplified version with minimal encryption but explicit messages

From page 11 of
  Abadi and Needham.  Prudent Engineering Practice for Cryptographic Protocols.
  IEEE Trans. SE 22 (1), 1996
*)

open OtwayRees_AN;

proof_timing:=true;
HOL_quantifiers := false;


(*A "possibility property": there are traces that reach the end*)
goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]                               \
\        ==> EX K. EX NA. EX evs: otway lost.                                 \
\             Says B A (Crypt (shrK A) {|Nonce NA, Agent A, Agent B, Key K|}) \
\             : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (otway.Nil RS otway.OR1 RS otway.OR2 RS otway.OR3 RS otway.OR4) 2);
by (ALLGOALS (simp_tac (!simpset setsolver safe_solver)));
by (REPEAT_FIRST (resolve_tac [refl, conjI]));
by (REPEAT_FIRST (fast_tac (!claset addss (!simpset setsolver safe_solver))));
result();


(**** Inductive proofs about otway ****)

(*Monotonicity*)
goal thy "!!evs. lost' <= lost ==> otway lost' <= otway lost";
by (rtac subsetI 1);
by (etac otway.induct 1);
by (REPEAT_FIRST
    (best_tac (!claset addIs (impOfSubs (sees_mono RS analz_mono RS synth_mono)
                              :: otway.intrs))));
qed "otway_mono";

(*Nobody sends themselves messages*)
goal thy "!!evs. evs : otway lost ==> ALL A X. Says A A X ~: set_of_list evs";
by (etac otway.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(** For reasoning about the encrypted portion of messages **)

goal thy "!!evs. Says S B {|X, X'|} : set_of_list evs ==> \
\                X : analz (sees lost Spy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]) 1);
qed "OR4_analz_sees_Spy";

goal thy "!!evs. Says Server B {|X, Crypt K' {|NB, a, Agent B, K|}|} \
\                  : set_of_list evs ==> K : parts (sees lost Spy evs)";
by (fast_tac (!claset addSEs partsEs
                      addSDs [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "Oops_parts_sees_Spy";

(*OR4_analz_sees_Spy lets us treat those cases using the same 
  argument as for the Fake case.  This is possible for most, but not all,
  proofs, since Fake messages originate from the Spy. *)

bind_thm ("OR4_parts_sees_Spy",
          OR4_analz_sees_Spy RS (impOfSubs analz_subset_parts));

(*We instantiate the variable to "lost".  Leaving it as a Var makes proofs
  harder to complete, since simplification does less for us.*)
val parts_Fake_tac = 
    forw_inst_tac [("lost","lost")] OR4_parts_sees_Spy 6 THEN
    forw_inst_tac [("lost","lost")] Oops_parts_sees_Spy 7;

(*For proving the easier theorems about X ~: parts (sees lost Spy evs) *)
fun parts_induct_tac i = SELECT_GOAL
    (DETERM (etac otway.induct 1 THEN parts_Fake_tac THEN
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
 "!!evs. evs : otway lost \
\        ==> (Key (shrK A) : parts (sees lost Spy evs)) = (A : lost)";
by (parts_induct_tac 1);
by (Auto_tac());
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

goal thy 
 "!!evs. evs : otway lost \
\        ==> (Key (shrK A) : analz (sees lost Spy evs)) = (A : lost)";
by (auto_tac(!claset addDs [impOfSubs analz_subset_parts], !simpset));
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

goal thy  "!!A. [| Key (shrK A) : parts (sees lost Spy evs);       \
\                  evs : otway lost |] ==> A:lost";
by (fast_tac (!claset addDs [Spy_see_shrK]) 1);
qed "Spy_see_shrK_D";

bind_thm ("Spy_analz_shrK_D", analz_subset_parts RS subsetD RS Spy_see_shrK_D);
AddSDs [Spy_see_shrK_D, Spy_analz_shrK_D];


(*** Future keys can't be seen or used! ***)

(*Nobody can have SEEN keys that will be generated in the future. *)
goal thy "!!evs. evs : otway lost ==>             \
\                length evs <= length evs' -->    \
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
\           evs : otway lost               \
\        |] ==> length evt < length evs";
by (rtac ccontr 1);
by (dtac leI 1);
by (fast_tac (!claset addSDs [new_keys_not_seen, Says_imp_sees_Spy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_keys";


(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : otway lost ==>          \
\                length evs <= length evs' --> \
\                newK evs' ~: keysFor (parts (sees lost Spy evs))";
by (parts_induct_tac 1);
(*Fake, OR4: these messages send unknown (X) components*)
by (EVERY
    (map 
     (best_tac
      (!claset addDs [impOfSubs (analz_subset_parts RS keysFor_mono),
                      impOfSubs (parts_insert_subset_Un RS keysFor_mono),
                      Suc_leD]
               addEs [new_keys_not_seen RS not_parts_not_analz RSN(2,rev_notE)]
               addss (!simpset))) [5,1]));
(*Remaining subgoals*)
by (REPEAT (fast_tac (!claset addDs [Suc_leD] addss (!simpset)) 1));
qed_spec_mp "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];



(*** Proofs involving analz ***)

(*Describes the form of K and NA when the Server sends this message.*)
goal thy 
 "!!evs. [| Says Server B \
\           {|Crypt (shrK A) {|NA, Agent A, Agent B, K|},                     \
\             Crypt (shrK B) {|NB, Agent A, Agent B, K|}|} : set_of_list evs; \
\           evs : otway lost |]                                               \
\        ==> (EX evt: otway lost. K = Key(newK evt)) & \
\            (EX i. NA = Nonce i) &                    \
\            (EX j. NB = Nonce j)";
by (etac rev_mp 1);
by (etac otway.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "Says_Server_message_form";


(*For proofs involving analz.  We again instantiate the variable to "lost".*)
val analz_Fake_tac = 
    dres_inst_tac [("lost","lost")] OR4_analz_sees_Spy 6 THEN
    forw_inst_tac [("lost","lost")] Says_Server_message_form 7 THEN
    assume_tac 7 THEN Full_simp_tac 7 THEN
    REPEAT ((eresolve_tac [bexE, exE, conjE] ORELSE' hyp_subst_tac) 7);


(****
 The following is to prove theorems of the form

          Key K : analz (insert (Key (newK evt)) (sees lost Spy evs)) ==>
          Key K : analz (sees lost Spy evs)

 A more general formula must be proved inductively.

****)


(** Session keys are not used to encrypt other session keys **)

(*The equality makes the induction hypothesis easier to apply*)
goal thy  
 "!!evs. evs : otway lost ==>                                         \
\  ALL K E. (Key K : analz (Key``(newK``E) Un (sees lost Spy evs))) = \
\           (K : newK``E | Key K : analz (sees lost Spy evs))";
by (etac otway.induct 1);
by analz_Fake_tac;
by (REPEAT_FIRST (ares_tac [allI, analz_image_newK_lemma]));
by (ALLGOALS (*Takes 28 secs*)
    (asm_simp_tac 
     (!simpset addsimps ([insert_Key_singleton, insert_Key_image, pushKey_newK]
                         @ pushes)
               setloop split_tac [expand_if])));
(** LEVEL 5 **)
(*OR4, Fake*) 
by (EVERY (map spy_analz_tac [4,2]));
(*Oops, OR3, Base*)
by (REPEAT (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1));
qed_spec_mp "analz_image_newK";


goal thy
 "!!evs. evs : otway lost ==>                                          \
\        Key K : analz (insert (Key (newK evt)) (sees lost Spy evs)) = \
\        (K = newK evt | Key K : analz (sees lost Spy evs))";
by (asm_simp_tac (HOL_ss addsimps [pushKey_newK, analz_image_newK, 
                                   insert_Key_singleton]) 1);
by (Fast_tac 1);
qed "analz_insert_Key_newK";


(*** The Key K uniquely identifies the Server's  message. **)

goal thy 
 "!!evs. evs : otway lost ==>                              \
\      EX A' B' NA' NB'. ALL A B NA NB.                    \
\       Says Server B \
\         {|Crypt (shrK A) {|NA, Agent A, Agent B, K|},                     \
\           Crypt (shrK B) {|NB, Agent A, Agent B, K|}|} : set_of_list evs  \
\       --> A=A' & B=B' & NA=NA' & NB=NB'";
by (etac otway.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib])));
by (Step_tac 1);
(*Remaining cases: OR3 and OR4*)
by (ex_strip_tac 2);
by (Fast_tac 2);
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
(*...we assume X is a very new message, and handle this case by contradiction*)
by (fast_tac (!claset addEs [Says_imp_old_keys RS less_irrefl]
                      delrules [conjI]    (*prevent split-up into 4 subgoals*)
                      addss (!simpset addsimps [parts_insertI])) 1);
val lemma = result();


goal thy 
"!!evs. [| Says Server B                                           \
\            {|Crypt (shrK A) {|NA, Agent A, Agent B, K|},         \
\              Crypt (shrK B) {|NB, Agent A, Agent B, K|}|}        \
\           : set_of_list evs;                                     \
\          Says Server B'                                          \
\            {|Crypt (shrK A') {|NA', Agent A', Agent B', K|},     \
\              Crypt (shrK B') {|NB', Agent A', Agent B', K|}|}    \
\           : set_of_list evs;                                     \
\          evs : otway lost |]                                     \
\       ==> A=A' & B=B' & NA=NA' & NB=NB'";
by (dtac lemma 1);
by (REPEAT (etac exE 1));
(*Duplicate the assumption*)
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
by (fast_tac (!claset addSDs [spec]) 1);
qed "unique_session_keys";



(**** Authenticity properties relating to NA ****)

(*If the encrypted message appears then it originated with the Server!*)
goal thy 
 "!!evs. [| A ~: lost;  evs : otway lost |]                 \
\ ==> Crypt (shrK A) {|NA, Agent A, Agent B, Key K|}        \
\      : parts (sees lost Spy evs)                          \
\     --> (EX NB. Says Server B                                          \
\                  {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},     \
\                    Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}    \
\                  : set_of_list evs)";
by (parts_induct_tac 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [ex_disj_distrib])));
(*OR3*)
by (Fast_tac 1);
qed_spec_mp "NA_Crypt_imp_Server_msg";


(*Corollary: if A receives B's OR4 message and the nonce NA agrees
  then the key really did come from the Server!  CANNOT prove this of the
  bad form of this protocol, even though we can prove
  Spy_not_see_encrypted_key.  (We can implicitly infer freshness of
  the Server's message from its nonce NA.)*)
goal thy 
 "!!evs. [| Says B' A (Crypt (shrK A) {|NA, Agent A, Agent B, Key K|})  \
\            : set_of_list evs;                                         \
\           A ~: lost;  evs : otway lost |]                             \
\        ==> EX NB. Says Server B                                       \
\                    {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},  \
\                      Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|} \
\                   : set_of_list evs";
by (fast_tac (!claset addSIs [NA_Crypt_imp_Server_msg]
                      addEs  partsEs
                      addDs  [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "A_trusts_OR4";


(** Crucial secrecy property: Spy does not see the keys sent in msg OR3
    Does not in itself guarantee security: an attack could violate 
    the premises, e.g. by having A=Spy **)

goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  evs : otway lost |]                    \
\        ==> Says Server B                                                 \
\             {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},            \
\               Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}           \
\            : set_of_list evs -->                                         \
\            Says B Spy {|NA, NB, Key K|} ~: set_of_list evs -->           \
\            Key K ~: analz (sees lost Spy evs)";
by (etac otway.induct 1);
by analz_Fake_tac;
by (ALLGOALS
    (asm_simp_tac (!simpset addsimps ([not_parts_not_analz,
				       analz_insert_Key_newK] @ pushes)
		            setloop split_tac [expand_if])));
(*OR3*)
by (fast_tac (!claset addEs [Says_imp_old_keys RS less_irrefl]
                      addss (!simpset addsimps [parts_insert2])) 2);
(*OR4, Fake*) 
by (REPEAT_FIRST spy_analz_tac);
(*Oops*) 
by (fast_tac (!claset addDs [unique_session_keys] addss (!simpset)) 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);

goal thy 
 "!!evs. [| Says Server B                                                     \
\            {|Crypt (shrK A) {|NA, Agent A, Agent B, K|},                    \
\              Crypt (shrK B) {|NB, Agent A, Agent B, K|}|} : set_of_list evs;\
\           Says B Spy {|NA, NB, K|} ~: set_of_list evs;                      \
\           A ~: lost;  B ~: lost;  evs : otway lost |]                       \
\        ==> K ~: analz (sees lost Spy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (fast_tac (!claset addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


goal thy 
 "!!evs. [| C ~: {A,B,Server};                                                \
\           Says Server B                                                     \
\            {|Crypt (shrK A) {|NA, Agent A, Agent B, K|},                    \
\              Crypt (shrK B) {|NB, Agent A, Agent B, K|}|} : set_of_list evs;\
\           Says B Spy {|NA, NB, K|} ~: set_of_list evs;                 \
\           A ~: lost;  B ~: lost;  evs : otway lost |]                  \
\        ==> K ~: analz (sees lost C evs)";
by (rtac (subset_insertI RS sees_mono RS analz_mono RS contra_subsetD) 1);
by (rtac (sees_lost_agent_subset_sees_Spy RS analz_mono RS contra_subsetD) 1);
by (FIRSTGOAL (rtac Spy_not_see_encrypted_key));
by (REPEAT_FIRST (fast_tac (!claset addIs [otway_mono RS subsetD])));
qed "Agent_not_see_encrypted_key";


(**** Authenticity properties relating to NB ****)

(*If the encrypted message appears then it originated with the Server!*)
goal thy 
 "!!evs. [| B ~: lost;  evs : otway lost |]                                 \
\    ==> Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}                     \
\         : parts (sees lost Spy evs)                                       \
\        --> (EX NA. Says Server B                                          \
\                     {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},     \
\                       Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}    \
\                     : set_of_list evs)";
by (parts_induct_tac 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [ex_disj_distrib])));
(*OR3*)
by (Fast_tac 1);
qed_spec_mp "NB_Crypt_imp_Server_msg";


(*Guarantee for B: if it gets a message with matching NB then the Server
  has sent the correct message.*)
goal thy 
 "!!evs. [| B ~: lost;  evs : otway lost;                                   \
\           Says S B {|X, Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}  \
\            : set_of_list evs |]                                           \
\        ==> EX NA. Says Server B                                           \
\                     {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},     \
\                       Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}    \
\                     : set_of_list evs";
by (fast_tac (!claset addSIs [NB_Crypt_imp_Server_msg]
                      addEs  partsEs
                      addDs  [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "B_trusts_OR3";
