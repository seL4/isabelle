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

proof_timing:=true;
HOL_quantifiers := false;


(*A "possibility property": there are traces that reach the end*)
goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\        ==> EX N K. EX evs: ns_shared lost.          \
\               Says A B (Crypt K {|Nonce N, Nonce N|}) : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (ns_shared.Nil RS ns_shared.NS1 RS ns_shared.NS2 RS ns_shared.NS3 RS ns_shared.NS4 RS ns_shared.NS5) 2);
by (ALLGOALS (simp_tac (!simpset setsolver safe_solver)));
by (REPEAT_FIRST (resolve_tac [refl, conjI]));
by (ALLGOALS (fast_tac (!claset addss (!simpset setsolver safe_solver))));
result();


(**** Inductive proofs about ns_shared ****)

(*Monotonicity*)
goal thy "!!evs. lost' <= lost ==> ns_shared lost' <= ns_shared lost";
by (rtac subsetI 1);
by (etac ns_shared.induct 1);
by (REPEAT_FIRST
    (best_tac (!claset addIs (impOfSubs (sees_mono RS analz_mono RS synth_mono)
                              :: ns_shared.intrs))));
qed "ns_shared_mono";


(*Nobody sends themselves messages*)
goal thy "!!evs. evs : ns_shared lost ==> ALL A X. Says A A X ~: set_of_list evs";
by (etac ns_shared.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];

(*For reasoning about the encrypted portion of message NS3*)
goal thy "!!evs. Says S A (Crypt KA {|N, B, K, X|}) : set_of_list evs \
\                ==> X : parts (sees lost Spy evs)";
by (fast_tac (!claset addSEs partsEs
                      addSDs [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "NS3_msg_in_parts_sees_Spy";
                              
goal thy
    "!!evs. Says Server A (Crypt (shrK A) {|NA, B, K, X|}) : set_of_list evs \
\           ==> K : parts (sees lost Spy evs)";
by (fast_tac (!claset addSEs partsEs
                      addSDs [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "Oops_parts_sees_Spy";

val parts_Fake_tac = 
    dres_inst_tac [("lost","lost")] NS3_msg_in_parts_sees_Spy 5 THEN
    forw_inst_tac [("lost","lost")] Oops_parts_sees_Spy 8;

(*For proving the easier theorems about X ~: parts (sees lost Spy evs) *)
fun parts_induct_tac i = SELECT_GOAL
    (DETERM (etac ns_shared.induct 1 THEN parts_Fake_tac THEN
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
 "!!evs. evs : ns_shared lost \
\        ==> (Key (shrK A) : parts (sees lost Spy evs)) = (A : lost)";
by (parts_induct_tac 1);
by (Auto_tac());
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

goal thy 
 "!!evs. evs : ns_shared lost \
\        ==> (Key (shrK A) : analz (sees lost Spy evs)) = (A : lost)";
by (auto_tac(!claset addDs [impOfSubs analz_subset_parts], !simpset));
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

goal thy  "!!A. [| Key (shrK A) : parts (sees lost Spy evs);       \
\                  evs : ns_shared lost |] ==> A:lost";
by (fast_tac (!claset addDs [Spy_see_shrK]) 1);
qed "Spy_see_shrK_D";

bind_thm ("Spy_analz_shrK_D", analz_subset_parts RS subsetD RS Spy_see_shrK_D);
AddSDs [Spy_see_shrK_D, Spy_analz_shrK_D];


(*** Future keys can't be seen or used! ***)

(*Nobody can have SEEN keys that will be generated in the future. *)
goal thy "!!evs. evs : ns_shared lost ==>      \
\                length evs <= length evs' --> \
\                Key (newK evs') ~: parts (sees lost Spy evs)";
by (parts_induct_tac 1);
by (ALLGOALS (fast_tac (!claset addEs [leD RS notE]
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
\           evs : ns_shared lost           \
\        |] ==> length evt < length evs";
by (rtac ccontr 1);
by (dtac leI 1);
by (fast_tac (!claset addSDs [new_keys_not_seen, Says_imp_sees_Spy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_keys";



(*** Future nonces can't be seen or used! ***)

goal thy "!!evs. evs : ns_shared lost ==>     \
\                length evs <= length evt --> \
\                Nonce (newN evt) ~: parts (sees lost Spy evs)";
by (parts_induct_tac 1);
by (REPEAT_FIRST
    (fast_tac (!claset addSEs partsEs
                       addSDs  [Says_imp_sees_Spy RS parts.Inj]
                       addEs [leD RS notE]
				addDs  [impOfSubs analz_subset_parts,
                               impOfSubs parts_insert_subset_Un, Suc_leD]
                       addss (!simpset))));
qed_spec_mp "new_nonces_not_seen";
Addsimps [new_nonces_not_seen];


(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : ns_shared lost ==>      \
\                length evs <= length evs' --> \
\                newK evs' ~: keysFor (parts (sees lost Spy evs))";
by (parts_induct_tac 1);
(*NS1 and NS2*)
by (EVERY (map (fast_tac (!claset addDs [Suc_leD] addss (!simpset))) [3,2]));
(*Fake and NS3*)
by (EVERY 
    (map
     (best_tac
      (!claset addDs [impOfSubs (analz_subset_parts RS keysFor_mono),
                      impOfSubs (parts_insert_subset_Un RS keysFor_mono),
                      Suc_leD]
               addEs [new_keys_not_seen RS not_parts_not_analz RSN(2,rev_notE)]
               addss (!simpset)))
     [2,1]));
(*NS4 and NS5: nonce exchange*)
by (ALLGOALS (deepen_tac (!claset addSDs [Says_imp_old_keys]
                                  addIs  [less_SucI, impOfSubs keysFor_mono]
                                  addss (!simpset addsimps [le_def])) 1));
qed_spec_mp "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];


(** Lemmas concerning the form of items passed in messages **)

(*Describes the form of K, X and K' when the Server sends this message.*)
goal thy 
 "!!evs. [| Says Server A (Crypt K' {|N, Agent B, K, X|}) : set_of_list evs; \
\           evs : ns_shared lost |]    \
\        ==> (EX evt: ns_shared lost. \
\                  K = Key(newK evt) & \
\                  X = (Crypt (shrK B) {|K, Agent A|}) & \
\                  K' = shrK A)";
by (etac rev_mp 1);
by (etac ns_shared.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "Says_Server_message_form";


(*If the encrypted message appears then it originated with the Server*)
goal thy
 "!!evs. [| Crypt (shrK A) {|NA, Agent B, Key K, X|}                   \
\            : parts (sees lost Spy evs);                              \
\           A ~: lost;  evs : ns_shared lost |]                        \
\         ==> X = (Crypt (shrK B) {|Key K, Agent A|}) &                \
\             Says Server A                                            \
\              (Crypt (shrK A) {|NA, Agent B, Key K,                   \
\                                Crypt (shrK B) {|Key K, Agent A|}|})  \
\             : set_of_list evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Auto_tac());
qed "A_trusts_NS2";


(*EITHER describes the form of X when the following message is sent, 
  OR     reduces it to the Fake case.
  Use Says_Server_message_form if applicable.*)
goal thy 
 "!!evs. [| Says S A (Crypt (shrK A) {|Nonce NA, Agent B, Key K, X|})      \
\            : set_of_list evs;  evs : ns_shared lost |]                   \
\        ==> (EX evt: ns_shared lost. K = newK evt &                       \
\                               length evt < length evs &                  \
\                               X = (Crypt (shrK B) {|Key K, Agent A|}))   \
\          | X : analz (sees lost Spy evs)";
by (case_tac "A : lost" 1);
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]
                      addss (!simpset)) 1);
by (forward_tac [Says_imp_sees_Spy RS parts.Inj] 1);
by (fast_tac (!claset addEs  partsEs
                      addSDs [A_trusts_NS2, Says_Server_message_form]
                      addIs [Says_imp_old_keys]
                      addss (!simpset)) 1);
qed "Says_S_message_form";


(*For proofs involving analz.  We again instantiate the variable to "lost".*)
val analz_Fake_tac = 
    forw_inst_tac [("lost","lost")] Says_Server_message_form 8 THEN
    forw_inst_tac [("lost","lost")] Says_S_message_form 5 THEN 
    Full_simp_tac 7 THEN
    REPEAT_FIRST (eresolve_tac [asm_rl, bexE, disjE] ORELSE' hyp_subst_tac);


(****
 The following is to prove theorems of the form

          Key K : analz (insert (Key (newK evt)) (sees lost Spy evs)) ==>
          Key K : analz (sees lost Spy evs)

 A more general formula must be proved inductively.

****)


(*NOT useful in this form, but it says that session keys are not used
  to encrypt messages containing other keys, in the actual protocol.
  We require that agents should behave like this subsequently also.*)
goal thy 
 "!!evs. evs : ns_shared lost ==> \
\        (Crypt (newK evt) X) : parts (sees lost Spy evs) & \
\        Key K : parts {X} --> Key K : parts (sees lost Spy evs)";
by (etac ns_shared.induct 1);
by parts_Fake_tac;
by (ALLGOALS Asm_simp_tac);
(*Deals with Faked messages*)
by (best_tac (!claset addSEs partsEs
                      addDs [impOfSubs parts_insert_subset_Un]
                      addss (!simpset)) 2);
(*Base, NS4 and NS5*)
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
result();


(** Session keys are not used to encrypt other session keys **)

(*The equality makes the induction hypothesis easier to apply*)
goal thy  
 "!!evs. evs : ns_shared lost ==> \
\  ALL K E. (Key K : analz (Key``(newK``E) Un (sees lost Spy evs))) = \
\           (K : newK``E | Key K : analz (sees lost Spy evs))";
by (etac ns_shared.induct 1);
by analz_Fake_tac;
by (REPEAT_FIRST (resolve_tac [allI, analz_image_newK_lemma]));
by (ALLGOALS 
    (asm_simp_tac 
     (!simpset addsimps ([insert_Key_singleton, insert_Key_image, pushKey_newK]
                         @ pushes)
               setloop split_tac [expand_if])));
(*NS3, Fake*) 
by (EVERY (map spy_analz_tac [5,2]));
by (REPEAT (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1));
(*NS3, NS2, Base*)
by (REPEAT (Fast_tac 3));
qed_spec_mp "analz_image_newK";


goal thy
 "!!evs. evs : ns_shared lost ==>                               \
\        Key K : analz (insert (Key (newK evt)) (sees lost Spy evs)) = \
\        (K = newK evt | Key K : analz (sees lost Spy evs))";
by (asm_simp_tac (HOL_ss addsimps [pushKey_newK, analz_image_newK, 
                                   insert_Key_singleton]) 1);
by (Fast_tac 1);
qed "analz_insert_Key_newK";


(** The session key K uniquely identifies the message, if encrypted
    with a secure key **)

goal thy 
 "!!evs. evs : ns_shared lost ==>                                            \
\      EX A' NA' B' X'. ALL A NA B X.                                        \
\       Says Server A (Crypt (shrK A) {|NA, Agent B, Key K, X|})         \
\       : set_of_list evs --> A=A' & NA=NA' & B=B' & X=X'";
by (etac ns_shared.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib])));
by (Step_tac 1);
(*NS3*)
by (ex_strip_tac 2);
by (Fast_tac 2);
(*NS2: it can't be a new key*)
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
by (fast_tac (!claset addEs [Says_imp_old_keys RS less_irrefl]
                      delrules [conjI]    (*prevent split-up into 4 subgoals*)
                      addss (!simpset addsimps [parts_insertI])) 1);
val lemma = result();

(*In messages of this form, the session key uniquely identifies the rest*)
goal thy 
 "!!evs. [| Says Server A                                    \
\             (Crypt (shrK A) {|NA, Agent B, Key K, X|})     \
\                  : set_of_list evs;                        \ 
\           Says Server A'                                   \
\             (Crypt (shrK A') {|NA', Agent B', Key K, X'|}) \
\                  : set_of_list evs;                        \
\           evs : ns_shared lost |] ==> A=A' & NA=NA' & B=B' & X = X'";
by (dtac lemma 1);
by (REPEAT (etac exE 1));
(*Duplicate the assumption*)
by (forw_inst_tac [("psi", "ALL A.?P(A)")] asm_rl 1);
by (fast_tac (!claset addSDs [ spec] 
                      delrules [conjI] addss (!simpset)) 1);
qed "unique_session_keys";


(** Crucial secrecy property: Spy does not see the keys sent in msg NS2 **)

goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  evs : ns_shared lost |]            \
\        ==> Says Server A                                             \
\              (Crypt (shrK A) {|NA, Agent B, Key K,                   \
\                                Crypt (shrK B) {|Key K, Agent A|}|})  \
\             : set_of_list evs -->                                    \
\        (ALL NB. Says A Spy {|NA, NB, Key K|} ~: set_of_list evs) --> \
\        Key K ~: analz (sees lost Spy evs)";
by (etac ns_shared.induct 1);
by analz_Fake_tac;
by (ALLGOALS 
    (asm_simp_tac 
     (!simpset addsimps ([not_parts_not_analz,
                          analz_insert_Key_newK] @ pushes)
               setloop split_tac [expand_if])));
(*NS2*)
by (fast_tac (!claset addIs [parts_insertI]
                      addEs [Says_imp_old_keys RS less_irrefl]
                      addss (!simpset)) 2);
(*OR4, OR2, Fake*) 
by (REPEAT_FIRST spy_analz_tac);
(*NS3 and Oops subcases*) (**LEVEL 7 **)
by (step_tac (!claset delrules [impCE]) 1);
by (full_simp_tac (!simpset addsimps [all_conj_distrib]) 2);
by (etac conjE 2);
by (mp_tac 2);
(**LEVEL 11 **)
by (forward_tac [Says_imp_sees_Spy RS parts.Inj RS A_trusts_NS2] 2);
by (assume_tac 3);
by (fast_tac (!claset addSEs [Says_Crypt_not_lost]) 2);
by (fast_tac (!claset addDs [unique_session_keys] addss (!simpset)) 2);
(*NS3*)
by (forward_tac [Says_imp_sees_Spy RS parts.Inj RS A_trusts_NS2] 1);
by (assume_tac 2);
by (fast_tac (!claset addSEs [Says_Crypt_not_lost]) 1);
by (fast_tac (!claset addDs [unique_session_keys] addss (!simpset)) 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);


(*Final version: Server's message in the most abstract form*)
goal thy 
 "!!evs. [| Says Server A                                               \
\            (Crypt K' {|NA, Agent B, K, X|}) : set_of_list evs;        \
\           (ALL NB. Says A Spy {|NA, NB, K|} ~: set_of_list evs);      \
\           A ~: lost;  B ~: lost;  evs : ns_shared lost                \
\        |] ==> K ~: analz (sees lost Spy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (fast_tac (!claset addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


goal thy 
 "!!evs. [| C ~: {A,B,Server};                                          \
\           Says Server A                                               \
\            (Crypt K' {|NA, Agent B, K, X|}) : set_of_list evs;        \
\           (ALL NB. Says A Spy {|NA, NB, K|} ~: set_of_list evs);      \
\           A ~: lost;  B ~: lost;  evs : ns_shared lost |]             \
\        ==> K ~: analz (sees lost C evs)";
by (rtac (subset_insertI RS sees_mono RS analz_mono RS contra_subsetD) 1);
by (rtac (sees_lost_agent_subset_sees_Spy RS analz_mono RS contra_subsetD) 1);
by (FIRSTGOAL (rtac Spy_not_see_encrypted_key));
by (REPEAT_FIRST (fast_tac (!claset addIs [ns_shared_mono RS subsetD])));
qed "Agent_not_see_encrypted_key";



(**** Guarantees available at various stages of protocol ***)

A_trusts_NS2 RS conjunct2 RS Spy_not_see_encrypted_key;


(*If the encrypted message appears then it originated with the Server*)
goal thy
 "!!evs. [| Crypt (shrK B) {|Key K, Agent A|} : parts (sees lost Spy evs); \
\           B ~: lost;  evs : ns_shared lost |]                        \
\         ==> EX NA. Says Server A                                     \
\              (Crypt (shrK A) {|NA, Agent B, Key K,                   \
\                                Crypt (shrK B) {|Key K, Agent A|}|})  \
\             : set_of_list evs";
by (etac rev_mp 1);
by (etac ns_shared.induct 1);
by parts_Fake_tac;
(*Fake case*)
by (best_tac (!claset addSDs [impOfSubs Fake_parts_insert]
                      addDs  [impOfSubs analz_subset_parts]
                      addss  (!simpset)) 2);
by (Auto_tac());
qed "B_trusts_NS3";


goal thy
 "!!evs. [| B ~: lost;  evs : ns_shared lost |]            \
\        ==> Key K ~: analz (sees lost Spy evs) -->             \
\            Says Server A (Crypt (shrK A) {|NA, Agent B, Key K, X|})  \
\            : set_of_list evs --> \
\            Crypt K (Nonce NB) : parts (sees lost Spy evs) -->            \
\            Says B A (Crypt K (Nonce NB)) : set_of_list evs";
by (etac ns_shared.induct 1);
by (forward_tac [Says_S_message_form] 5 THEN assume_tac 5);     
by parts_Fake_tac;
by (TRYALL (rtac impI));
by (REPEAT_FIRST
    (dtac (sees_subset_sees_Says RS analz_mono RS contra_subsetD)));
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib])));
(**LEVEL 6**)
by (fast_tac (!claset addSDs [Crypt_Fake_parts_insert]
                      addDs [impOfSubs analz_subset_parts]) 1);
by (Fast_tac 2);
by (REPEAT_FIRST (rtac impI ORELSE' etac conjE ORELSE' hyp_subst_tac));
(*Contradiction from the assumption   
   Crypt (newK evsa) (Nonce NB) : parts (sees lost Spy evsa) *)
by (dtac Crypt_imp_invKey_keysFor 1);
(**LEVEL 10**)
by (Asm_full_simp_tac 1);
by (rtac disjI1 1);
by (thin_tac "?PP-->?QQ" 1);
by (case_tac "Ba : lost" 1);
by (dtac Says_Crypt_lost 1 THEN assume_tac 1 THEN Fast_tac 1);
by (dtac (Says_imp_sees_Spy RS parts.Inj RS B_trusts_NS3) 1 THEN 
    REPEAT (assume_tac 1));
by (fast_tac (!claset addDs [unique_session_keys]) 1);
val lemma = result();

goal thy
 "!!evs. [| Crypt K (Nonce NB) : parts (sees lost Spy evs);           \
\           Says Server A (Crypt (shrK A) {|NA, Agent B, Key K, X|})  \
\           : set_of_list evs;                                        \
\           ALL NB. Says A Spy {|NA, NB, Key K|} ~: set_of_list evs;  \
\           A ~: lost;  B ~: lost;  evs : ns_shared lost |]           \
\        ==> Says B A (Crypt K (Nonce NB)) : set_of_list evs";
by (fast_tac (!claset addSIs [lemma RS mp RS mp RS mp]
                      addSEs [Spy_not_see_encrypted_key RSN (2, rev_notE)]) 1);
qed "A_trusts_NS4";
