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


(*Weak liveness: there are traces that reach the end*)
goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\        ==> EX N K. EX evs: ns_shared lost.          \
\               Says A B (Crypt {|Nonce N, Nonce N|} K) : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (ns_shared.Nil RS ns_shared.NS1 RS ns_shared.NS2 RS ns_shared.NS3 RS ns_shared.NS4 RS ns_shared.NS5) 2);
by (ALLGOALS (simp_tac (!simpset setsolver safe_solver)));
by (REPEAT_FIRST (resolve_tac [refl, conjI]));
by (ALLGOALS (fast_tac (!claset addss (!simpset setsolver safe_solver))));
result();


(**** Inductive proofs about ns_shared ****)

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
goal thy "!!evs. (Says S A (Crypt {|N, B, K, X|} KA)) : set_of_list evs ==> \
\                X : parts (sees lost Spy evs)";
by (fast_tac (!claset addSEs partsEs
                      addSDs [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "NS3_msg_in_parts_sees_Spy";
                              
val parts_Fake_tac = 
    dres_inst_tac [("lost","lost")] NS3_msg_in_parts_sees_Spy 5;

(** Theorems of the form X ~: parts (sees lost Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees lost another agent's shared key!*)
goal thy 
 "!!evs. [| evs : ns_shared lost; A ~: lost |]    \
\        ==> Key (shrK A) ~: parts (sees lost Spy evs)";
by (etac ns_shared.induct 1);
by parts_Fake_tac;
by (Auto_tac());
(*Deals with Fake message*)
by (best_tac (!claset addDs [impOfSubs analz_subset_parts,
                             impOfSubs Fake_parts_insert]) 1);
qed "Spy_not_see_shrK";

bind_thm ("Spy_not_analz_shrK",
          [analz_subset_parts, Spy_not_see_shrK] MRS contra_subsetD);

Addsimps [Spy_not_see_shrK, Spy_not_analz_shrK];

(*We go to some trouble to preserve R in the 3rd and 4th subgoals
  As usual fast_tac cannot be used because it uses the equalities too soon*)
val major::prems = 
goal thy  "[| Key (shrK A) : parts (sees lost Spy evs);       \
\             evs : ns_shared lost;                             \
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


goal thy  
 "!!evs. evs : ns_shared lost ==>                              \
\        (Key (shrK A) : analz (sees lost Spy evs)) = (A : lost)";
by (best_tac (!claset addIs [impOfSubs (subset_insertI RS analz_mono)]
                      addss (!simpset)) 1);
qed "shrK_mem_analz";

Addsimps [shrK_mem_analz];


(*** Future keys can't be seen or used! ***)

(*Nobody can have SEEN keys that will be generated in the future.
  This has to be proved anew for each protocol description,
  but should go by similar reasoning every time.  Hardest case is the
  standard Fake rule.  
      The length comparison, and Union over C, are essential for the 
  induction! *)
goal thy "!!evs. evs : ns_shared lost ==> \
\                length evs <= length evs' --> \
\                          Key (newK evs') ~: (UN C. parts (sees lost C evs))";
by (etac ns_shared.induct 1);
by parts_Fake_tac;
(*auto_tac does not work here, as it performs safe_tac first*)
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (fast_tac (!claset addDs [impOfSubs analz_subset_parts,
                                       impOfSubs parts_insert_subset_Un,
                                       Suc_leD]
                                addss (!simpset))));
val lemma = result();

(*Variant needed for the main theorem below*)
goal thy 
 "!!evs. [| evs : ns_shared lost;  length evs <= length evs' |]    \
\        ==> Key (newK evs') ~: parts (sees lost C evs)";
by (fast_tac (!claset addDs [lemma]) 1);
qed "new_keys_not_seen";
Addsimps [new_keys_not_seen];

(*Another variant: old messages must contain old keys!*)
goal thy 
 "!!evs. [| Says A B X : set_of_list evs;  \
\           Key (newK evt) : parts {X};    \
\           evs : ns_shared lost                 \
\        |] ==> length evt < length evs";
by (rtac ccontr 1);
by (dtac leI 1);
by (fast_tac (!claset addSDs [new_keys_not_seen, Says_imp_sees_Spy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_keys";


(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : ns_shared lost ==> \
\                length evs <= length evs' --> \
\                newK evs' ~: keysFor (UN C. parts (sees lost C evs))";
by (etac ns_shared.induct 1);
by parts_Fake_tac;
by (ALLGOALS Asm_simp_tac);
(*NS1 and NS2*)
map (by o fast_tac (!claset addDs [Suc_leD] addss (!simpset))) [3,2];
(*Fake and NS3*)
map (by o best_tac
     (!claset addDs [impOfSubs (analz_subset_parts RS keysFor_mono),
                     impOfSubs (parts_insert_subset_Un RS keysFor_mono),
                     Suc_leD]
              addEs [new_keys_not_seen RS not_parts_not_analz RSN (2,rev_notE)]
              addss (!simpset)))
    [2,1];
(*NS4 and NS5: nonce exchange*)
by (ALLGOALS (deepen_tac (!claset addSDs [Says_imp_old_keys]
                                  addIs  [less_SucI, impOfSubs keysFor_mono]
                                  addss (!simpset addsimps [le_def])) 0));
val lemma = result();

goal thy 
 "!!evs. [| evs : ns_shared lost;  length evs <= length evs' |]    \
\        ==> newK evs' ~: keysFor (parts (sees lost C evs))";
by (fast_tac (!claset addSDs [lemma] addss (!simpset)) 1);
qed "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];


(** Lemmas concerning the form of items passed in messages **)

(*Describes the form of K, X and K' when the Server sends this message.*)
goal thy 
 "!!evs. [| Says Server A (Crypt {|N, Agent B, K, X|} K') : set_of_list evs; \
\           evs : ns_shared lost |]    \
\        ==> (EX evt: ns_shared lost. \
\                  K = Key(newK evt) & \
\                  X = (Crypt {|K, Agent A|} (shrK B)) & \
\                  K' = shrK A)";
by (etac rev_mp 1);
by (etac ns_shared.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "Says_Server_message_form";


(*Describes the form of X when the following message is sent.  The use of
  "parts" strengthens the induction hyp for proving the Fake case.  The
  assumptions on A are needed to prevent its being a Faked message.*)
goal thy
 "!!evs. evs : ns_shared lost ==>                                         \
\            Crypt {|Nonce NA, Agent B, Key K, X|} (shrK A)               \
\               : parts (sees lost Spy evs) &                           \
\            A ~: lost -->                                                \
\          (EX evt: ns_shared lost. K = newK evt & \
\                             X = (Crypt {|Key K, Agent A|} (shrK B)))";
by (etac ns_shared.induct 1);
by parts_Fake_tac;
(*Fake case*)
by (best_tac (!claset addSDs [impOfSubs Fake_parts_insert]
                      addDs  [impOfSubs analz_subset_parts]
                      addss  (!simpset)) 2);
by (Auto_tac());
val lemma = result() RS mp;


(*The following theorem is proved by cases.  If the message was sent with a
  bad key then the Spy reads it -- even if he didn't send it in the first
  place.*)


(*EITHER describes the form of X when the following message is sent, 
  OR     reduces it to the Fake case.
  Use Says_Server_message_form if applicable.*)
goal thy 
 "!!evs. [| Says S A (Crypt {|Nonce NA, Agent B, Key K, X|} (shrK A))    \
\            : set_of_list evs;  evs : ns_shared lost |]                      \
\        ==> (EX evt: ns_shared lost. K = newK evt & length evt < length evs & \
\                               X = (Crypt {|Key K, Agent A|} (shrK B))) | \
\            X : analz (sees lost Spy evs)";
by (excluded_middle_tac "A : lost" 1);
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]
                      addss (!simpset)) 2);
by (forward_tac [lemma] 1);
by (fast_tac (!claset addEs  partsEs
                      addSDs [Says_imp_sees_Spy RS parts.Inj]) 1);
by (fast_tac (!claset addIs [Says_imp_old_keys] addss (!simpset)) 1);
qed "Says_S_message_form";



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
\        (Crypt X (newK evt)) : parts (sees lost Spy evs) & \
\        Key K : parts {X} --> Key K : parts (sees lost Spy evs)";
by (etac ns_shared.induct 1);
by parts_Fake_tac;
by (ALLGOALS (asm_simp_tac (!simpset addsimps pushes)));
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
by (forward_tac [Says_S_message_form] 5 THEN assume_tac 5);     
by (REPEAT ((eresolve_tac [bexE, conjE, disjE] ORELSE' hyp_subst_tac) 5));
by (REPEAT_FIRST (resolve_tac [allI, analz_image_newK_lemma]));
by (ALLGOALS 
    (asm_simp_tac 
     (!simpset addsimps ([insert_Key_singleton, insert_Key_image, pushKey_newK]
                         @ pushes)
               setloop split_tac [expand_if])));
(** LEVEL 5 **)
(*NS3, Fake subcase*)
by (spy_analz_tac 5);
(*Cases NS2 and NS3!!  Simple, thanks to auto case splits*)
by (REPEAT (Fast_tac 3));
(*Fake case*) (** LEVEL 7 **)
by (spy_analz_tac 2);
(*Base case*)
by (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1);
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

fun ex_strip_tac i = REPEAT (ares_tac [exI, conjI] i) THEN assume_tac (i+1);

goal thy 
 "!!evs. evs : ns_shared lost ==>                             \
\      EX X'. ALL A X N B.                               \
\       A ~: lost -->                                     \
\       Crypt {|N, Agent B, Key K, X|} (shrK A) : parts (sees lost Spy evs) --> \
\       X=X'";
by (Simp_tac 1);        (*Miniscoping*)
by (etac ns_shared.induct 1);
by (forward_tac [Says_S_message_form] 5 THEN assume_tac 5);     
by (ALLGOALS 
    (asm_simp_tac (!simpset addsimps [all_conj_distrib, ex_disj_distrib,
                                      imp_conj_distrib, parts_insert_sees])));
by (REPEAT_FIRST (eresolve_tac [exE,disjE]));
(*NS2: Cextraction of K = newK evsa to global context...*) 
(** LEVEL 5 **)
by (excluded_middle_tac "K = newK evsa" 3);
by (Asm_simp_tac 3);
by (etac exI 3);
(*...we assume X is a very new message, and handle this case by contradiction*)
by (fast_tac (!claset addSEs partsEs
                      addEs [Says_imp_old_keys RS less_irrefl]
                      addss (!simpset)) 3);
(*Base, Fake, NS3*) (** LEVEL 9 **)
by (REPEAT_FIRST ex_strip_tac);
by (dtac synth.Inj 4);
by (REPEAT_FIRST (best_tac (!claset addDs [impOfSubs Fake_parts_insert]
                                    addss (!simpset))));
val lemma = result();

(*In messages of this form, the session key uniquely identifies the rest*)
goal thy 
 "!!evs. [| Says S A          \
\             (Crypt {|N, Agent B, Key K, X|} (shrK C))     \
\                  : set_of_list evs; \ 
\           Says S' A'                                         \
\             (Crypt {|N', Agent B', Key K, X'|} (shrK C')) \
\                  : set_of_list evs;                         \
\           evs : ns_shared lost;  C ~: lost;  C' ~: lost |] ==> X = X'";
by (dtac lemma 1);
by (etac exE 1);
(*Duplicate the assumption*)
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "unique_session_keys";



(** Crucial secrecy property: Spy does not see the keys sent in msg NS2 **)

goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  \
\           evs : ns_shared lost;  evt: ns_shared lost |]  \
\        ==> Says Server A                                             \
\              (Crypt {|N, Agent B, Key K,                     \
\                       Crypt {|Key K, Agent A|} (shrK B)|} (shrK A)) \
\             : set_of_list evs --> \
\        Key K ~: analz (sees lost Spy evs)";
by (etac ns_shared.induct 1);
by (ALLGOALS 
    (asm_simp_tac 
     (!simpset addsimps ([analz_subset_parts RS contra_subsetD,
                          analz_insert_Key_newK] @ pushes)
               setloop split_tac [expand_if])));
(*NS2*)
by (fast_tac (!claset addIs [parts_insertI]
                      addEs [Says_imp_old_keys RS less_irrefl]
                      addss (!simpset)) 2);
(*Fake case*)
by (spy_analz_tac 1);
(*NS3: that message from the Server was sent earlier*)
by (forward_tac [Says_S_message_form] 1 THEN assume_tac 1);
by (Step_tac 1);
by (REPEAT_FIRST assume_tac);
by (spy_analz_tac 2);           (*Prove the Fake subcase*)
by (asm_full_simp_tac
    (!simpset addsimps (mem_if::analz_insert_Key_newK::pushes)) 1);
by (Step_tac 1);
(**LEVEL 10 **)
by (excluded_middle_tac "Aa : lost" 1);
(*But this contradicts Key(newK evt) ~: analz (sees lost Spy evsa) *)
by (dtac (Says_imp_sees_Spy RS analz.Inj) 2);
by (fast_tac (!claset addSDs [analz.Decrypt]
                      addss (!simpset)) 2);
(*So now we have  Aa ~: lost *)
by (dtac unique_session_keys 1);
by (Auto_tac ());
val lemma = result() RS mp RSN(2,rev_notE);


(*Final version: Server's message in the most abstract form*)
goal thy 
 "!!evs. [| Says Server A                                                \
\            (Crypt {|N, Agent B, K, X|} K') : set_of_list evs;          \
\           A ~: lost;  B ~: lost;  evs : ns_shared lost                        \
\        |] ==>                                                          \
\     K ~: analz (sees lost Spy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (fast_tac (!claset addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


goal thy 
 "!!evs. [| C ~: {A,B,Server}; \
\           Says Server A                                                \
\            (Crypt {|N, Agent B, K, X|} K') : set_of_list evs;          \
\           A ~: lost;  B ~: lost;  evs : ns_shared lost |]                  \
\        ==> K ~: analz (sees lost C evs)";
by (rtac (subset_insertI RS sees_mono RS analz_mono RS contra_subsetD) 1);
by (rtac (sees_lost_agent_subset_sees_Spy RS analz_mono RS contra_subsetD) 1);
by (FIRSTGOAL (rtac Spy_not_see_encrypted_key));
by (REPEAT_FIRST (fast_tac (!claset addIs [ns_shared_mono RS subsetD])));
qed "Agent_not_see_encrypted_key";
