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

(**** Inductive proofs about ns_shared ****)

(*The Enemy can see more than anybody else, except for their initial state*)
goal thy 
 "!!evs. evs : ns_shared ==> \
\     sees A evs <= initState A Un sees Enemy evs";
be ns_shared.induct 1;
by (ALLGOALS (fast_tac (!claset addDs [sees_Says_subset_insert RS subsetD] 
			        addss (!simpset))));
qed "sees_agent_subset_sees_Enemy";


(*Nobody sends themselves messages*)
goal thy "!!evs. evs : ns_shared ==> ALL A X. Says A A X ~: set_of_list evs";
be ns_shared.induct 1;
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];

goal thy "!!evs. evs : ns_shared ==> Notes A X ~: set_of_list evs";
be ns_shared.induct 1;
by (Auto_tac());
qed "not_Notes";
Addsimps [not_Notes];
AddSEs   [not_Notes RSN (2, rev_notE)];


(*For reasoning about the encrypted portion of message NS3*)
goal thy "!!evs. (Says S A (Crypt {|N, B, K, X|} KA)) : set_of_list evs ==> \
\                X : parts (sees Enemy evs)";
by (fast_tac (!claset addSEs partsEs
	              addSDs [Says_imp_sees_Enemy RS parts.Inj]) 1);
qed "NS3_msg_in_parts_sees_Enemy";
			      

(*** Shared keys are not betrayed ***)

(*Enemy never sees another agent's shared key!*)
goal thy 
 "!!evs. [| evs : ns_shared; A ~= Enemy; A ~: Friend``leaked |] ==> \
\        Key (shrK A) ~: parts (sees Enemy evs)";
be ns_shared.induct 1;
bd NS3_msg_in_parts_sees_Enemy 5;
by (Auto_tac());
(*Deals with Fake message*)
by (best_tac (!claset addDs [impOfSubs analz_subset_parts,
			     impOfSubs Fake_parts_insert]) 1);
qed "Enemy_not_see_shrK";

bind_thm ("Enemy_not_analz_shrK",
	  [analz_subset_parts, Enemy_not_see_shrK] MRS contra_subsetD);

Addsimps [Enemy_not_see_shrK, 
	  not_sym RSN (2, Enemy_not_see_shrK), 
	  Enemy_not_analz_shrK, 
	  not_sym RSN (2, Enemy_not_analz_shrK)];

(*We go to some trouble to preserve R in the 3rd and 4th subgoals
  As usual fast_tac cannot be used because it uses the equalities too soon
  REDO USING 'BAD' SET TO AVOID CASE SPLIT!*)
val major::prems = 
goal thy  "[| Key (shrK A) : parts (sees Enemy evs);       \
\             evs : ns_shared;                             \
\             A=Enemy ==> R;                               \
\             !!i. [| A = Friend i; i: leaked |] ==> R     \
\           |] ==> R";
br ccontr 1;
br ([major, Enemy_not_see_shrK] MRS rev_notE) 1;
br notI 3;
be imageE 3;
by (swap_res_tac prems 2);
by (swap_res_tac prems 3 THEN ALLGOALS (fast_tac (!claset addIs prems)));
qed "Enemy_see_shrK_E";

bind_thm ("Enemy_analz_shrK_E", 
	  analz_subset_parts RS subsetD RS Enemy_see_shrK_E);

(*Classical reasoner doesn't need the not_sym versions (with swapped ~=) *)
AddSEs [Enemy_see_shrK_E, Enemy_analz_shrK_E];


(*Not for Addsimps -- it can cause goals to blow up!*)
goal thy  
 "!!evs. evs : ns_shared ==>                              \
\        (Key (shrK A) : analz (sees Enemy evs)) =        \
\          (A=Enemy | A : Friend``leaked)";
by (best_tac (!claset addDs [impOfSubs analz_subset_parts]
		      addIs [impOfSubs (subset_insertI RS analz_mono)]
	              addss (!simpset)) 1);
qed "shrK_mem_analz";


(*** Future keys can't be seen or used! ***)

(*Nobody can have SEEN keys that will be generated in the future.
  This has to be proved anew for each protocol description,
  but should go by similar reasoning every time.  Hardest case is the
  standard Fake rule.  
      The length comparison, and Union over C, are essential for the 
  induction! *)
goal thy "!!evs. evs : ns_shared ==> \
\                length evs <= length evs' --> \
\                          Key (newK evs') ~: (UN C. parts (sees C evs))";
be ns_shared.induct 1;
bd NS3_msg_in_parts_sees_Enemy 5;
(*auto_tac does not work here, as it performs safe_tac first*)
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (best_tac (!claset addDs [impOfSubs analz_subset_parts,
				       impOfSubs parts_insert_subset_Un,
				       Suc_leD]
			        addss (!simpset))));
val lemma = result();

(*Variant needed for the main theorem below*)
goal thy 
 "!!evs. [| evs : ns_shared;  length evs <= length evs' |] ==> \
\        Key (newK evs') ~: parts (sees C evs)";
by (fast_tac (!claset addDs [lemma]) 1);
qed "new_keys_not_seen";
Addsimps [new_keys_not_seen];

(*Another variant: old messages must contain old keys!*)
goal thy 
 "!!evs. [| Says A B X : set_of_list evs;  \
\           Key (newK evt) : parts {X};    \
\           evs : ns_shared                 \
\        |] ==> length evt < length evs";
br ccontr 1;
by (fast_tac (!claset addSDs [new_keys_not_seen, Says_imp_sees_Enemy]
	              addIs [impOfSubs parts_mono, leI]) 1);
qed "Says_imp_old_keys";


(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : ns_shared ==> \
\                length evs <= length evs' --> \
\                newK evs' ~: keysFor (UN C. parts (sees C evs))";
be ns_shared.induct 1;
bd NS3_msg_in_parts_sees_Enemy 5;
by (ALLGOALS Asm_simp_tac);
(*NS1 and NS2*)
map (by o fast_tac (!claset addDs [Suc_leD] addss (!simpset))) [3,2];
(*Fake and NS3*)
map (by o best_tac
     (!claset addSDs [newK_invKey]
	      addDs [impOfSubs (analz_subset_parts RS keysFor_mono),
		     impOfSubs (parts_insert_subset_Un RS keysFor_mono),
		     Suc_leD]
	      addEs [new_keys_not_seen RS not_parts_not_analz RSN (2,rev_notE)]
	      addss (!simpset)))
    [2,1];
(*NS4 and NS5: nonce exchange*)
by (ALLGOALS (deepen_tac (!claset addSDs [newK_invKey, Says_imp_old_keys]
	                          addIs  [less_SucI, impOfSubs keysFor_mono]
		                  addss (!simpset addsimps [le_def])) 0));
val lemma = result();

goal thy 
 "!!evs. [| evs : ns_shared;  length evs <= length evs' |] ==> \
\        newK evs' ~: keysFor (parts (sees C evs))";
by (fast_tac (!claset addSDs [lemma] addss (!simpset)) 1);
qed "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
	  [analz_subset_parts RS keysFor_mono,
	   new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];


(** Lemmas concerning the form of items passed in messages **)

(*Describes the form *and age* of K, and the form of X,
  when the following message is sent*)
goal thy 
 "!!evs. [| Says Server A (Crypt {|N, Agent B, K, X|} K') : set_of_list evs; \
\           evs : ns_shared    \
\        |] ==> (EX evt:ns_shared. \
\                         K = Key(newK evt) & \
\                         X = (Crypt {|K, Agent A|} (shrK B)) & \
\                         K' = shrK A & \
\                         length evt < length evs)";
be rev_mp 1;
be ns_shared.induct 1;
by (ALLGOALS (fast_tac (!claset addIs [less_SucI] addss (!simpset))));
qed "Says_Server_message_form";


(*Describes the form of X when the following message is sent.  The use of
  "parts" strengthens the induction hyp for proving the Fake case.  The
  assumptions on A are needed to prevent its being a Faked message.*)
goal thy
 "!!evs. evs : ns_shared ==>                                              \
\        ALL A NA B K X.                                                  \
\            (Crypt {|Nonce NA, Agent B, Key K, X|} (shrK A))             \
\               : parts (sees Enemy evs) &                                \
\            A ~= Enemy & A ~: Friend``leaked --> \
\          (EX evt:ns_shared. K = newK evt & \
\                             X = (Crypt {|Key K, Agent A|} (shrK B)))";
be ns_shared.induct 1;
bd NS3_msg_in_parts_sees_Enemy 5;
by (Step_tac 1);
by (ALLGOALS Asm_full_simp_tac);
by (fast_tac (!claset addss (!simpset)) 1);
(*Remaining cases are Fake and NS2*)
by (fast_tac (!claset addSDs [spec]) 2);
(*Now for the Fake case*)
by (best_tac (!claset addSDs  [impOfSubs Fake_parts_insert]
	              addDs [impOfSubs analz_subset_parts]
	              addss (!simpset)) 1);
qed_spec_mp "encrypted_form";


(*If such a message is sent with a bad key then the Enemy sees it (even if
  he didn't send it in the first place).*)
goal thy
 "!!evs. [| Says S A (Crypt {|Nonce NA, Agent B, Key K, X|} (shrK A))     \
\             : set_of_list evs;                                          \
\           A = Enemy | A : Friend``leaked |]                             \
\        ==> X : analz (sees Enemy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Enemy RS analz.Inj]
	              addss (!simpset)) 1);
qed_spec_mp "bad_encrypted_form";



(*EITHER describes the form of X when the following message is sent, 
  OR     reduces it to the Fake case.
  Use Says_Server_message_form if applicable.*)
goal thy 
 "!!evs. [| Says S A (Crypt {|Nonce NA, Agent B, Key K, X|} (shrK A))    \
\            : set_of_list evs;  evs : ns_shared |]                      \
\        ==> (EX evt:ns_shared. K = newK evt & length evt < length evs & \
\                               X = (Crypt {|Key K, Agent A|} (shrK B))) | \
\            X : analz (sees Enemy evs)";
by (excluded_middle_tac "A = Enemy | A : Friend``leaked" 1);
by (fast_tac (!claset addIs [bad_encrypted_form]) 2);
by (forward_tac [encrypted_form] 1);
br (parts.Inj RS conjI) 1;
by (auto_tac (!claset addIs [Says_imp_old_keys], !simpset));
qed "Says_S_message_form";



(****
 The following is to prove theorems of the form

          Key K : analz (insert (Key (newK evt)) (sees Enemy evs)) ==>
          Key K : analz (sees Enemy evs)

 A more general formula must be proved inductively.

****)


(*NOT useful in this form, but it says that session keys are not used
  to encrypt messages containing other keys, in the actual protocol.
  We require that agents should behave like this subsequently also.*)
goal thy 
 "!!evs. evs : ns_shared ==> \
\        (Crypt X (newK evt)) : parts (sees Enemy evs) & \
\        Key K : parts {X} --> Key K : parts (sees Enemy evs)";
be ns_shared.induct 1;
bd NS3_msg_in_parts_sees_Enemy 5;
by (ALLGOALS (asm_simp_tac (!simpset addsimps pushes)));
(*Deals with Faked messages*)
by (best_tac (!claset addSEs partsEs
		      addDs [impOfSubs analz_subset_parts,
                             impOfSubs parts_insert_subset_Un]
                      addss (!simpset)) 2);
(*Base, NS4 and NS5*)
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
result();


(** Specialized rewriting for this proof **)

Delsimps [image_insert];
Addsimps [image_insert RS sym];

Delsimps [image_Un];
Addsimps [image_Un RS sym];

goal thy "insert (Key (newK x)) (sees A evs) = \
\         Key `` (newK``{x}) Un (sees A evs)";
by (Fast_tac 1);
val insert_Key_singleton = result();

goal thy "insert (Key (f x)) (Key``(f``E) Un C) = \
\         Key `` (f `` (insert x E)) Un C";
by (Fast_tac 1);
val insert_Key_image = result();


(** Session keys are not used to encrypt other session keys **)

(*Lemma for the trivial direction of the if-and-only-if*)
goal thy  
 "!!evs. (Key K : analz (Key``nE Un sEe)) --> \
\         (K : nE | Key K : analz sEe)  ==>     \
\        (Key K : analz (Key``nE Un sEe)) = (K : nE | Key K : analz sEe)";
by (fast_tac (!claset addSEs [impOfSubs analz_mono]) 1);
val lemma = result();

(*Copied from OtwayRees.ML*)
val enemy_analz_tac =
  SELECT_GOAL 
   (EVERY [REPEAT (resolve_tac [impI,notI] 1),
	   dtac (impOfSubs Fake_analz_insert) 1,
	   eresolve_tac [asm_rl, synth.Inj] 1,
	   Fast_tac 1,
	   Asm_full_simp_tac 1,
	   IF_UNSOLVED (deepen_tac (!claset addIs [impOfSubs analz_mono]) 0 1)
	   ]);

goal thy  
 "!!evs. evs : ns_shared ==> \
\  ALL K E. (Key K : analz (Key``(newK``E) Un (sees Enemy evs))) = \
\           (K : newK``E | Key K : analz (sees Enemy evs))";
be ns_shared.induct 1;
by (forward_tac [Says_S_message_form] 5 THEN assume_tac 5);	
by (REPEAT ((eresolve_tac [bexE, conjE, disjE] ORELSE' hyp_subst_tac) 5));
by (REPEAT_FIRST (resolve_tac [allI, lemma]));
by (ALLGOALS 
    (asm_simp_tac 
     (!simpset addsimps ([insert_Key_singleton, insert_Key_image, pushKey_newK]
			 @ pushes)
               setloop split_tac [expand_if])));
(** LEVEL 5 **)
(*NS3, Fake subcase*)
by (enemy_analz_tac 5);
(*Cases NS2 and NS3!!  Simple, thanks to auto case splits*)
by (REPEAT (Fast_tac 3));
(*Fake case*) (** LEVEL 7 **)
by (res_inst_tac [("y1","X"), ("A1", "?G Un (?H::msg set)")] 
    (insert_commute RS ssubst) 2);
by (enemy_analz_tac 2);
(*Base case*)
by (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1);
qed_spec_mp "analz_image_newK";


goal thy
 "!!evs. evs : ns_shared ==>                               \
\        Key K : analz (insert (Key (newK evt)) (sees Enemy evs)) = \
\        (K = newK evt | Key K : analz (sees Enemy evs))";
by (asm_simp_tac (HOL_ss addsimps [pushKey_newK, analz_image_newK, 
				   insert_Key_singleton]) 1);
by (Fast_tac 1);
qed "analz_insert_Key_newK";


(** First, two lemmas for the Fake and NS3 cases **)

goal thy 
 "!!evs. [| X : synth (analz (sees Enemy evs));                \
\           Crypt X' (shrK C) : parts{X};                      \
\           C ~= Enemy;  C ~: Friend``leaked;  evs : ns_shared |]  \
\        ==> Crypt X' (shrK C) : parts (sees Enemy evs)";
by (best_tac (!claset addSEs [impOfSubs analz_subset_parts]
	              addDs [impOfSubs parts_insert_subset_Un]
                      addss (!simpset)) 1);
qed "Crypt_Fake_parts";

goal thy 
 "!!evs. [| Crypt X' K : parts (sees A evs);  evs : ns_shared |]  \
\        ==> EX S S' Y. Says S S' Y : set_of_list evs &       \
\            Crypt X' K : parts {Y}";
bd parts_singleton 1;
by (fast_tac (!claset addSDs [seesD] addss (!simpset)) 1);
qed "Crypt_parts_singleton";

fun ex_strip_tac i = REPEAT (ares_tac [exI, conjI] i) THEN assume_tac (i+1);

(*This says that the Key, K, uniquely identifies the message.
    But if Enemy knows C's key then he could send all sorts of nonsense.*)
goal thy 
 "!!evs. evs : ns_shared ==>                      \
\      EX X'. ALL C.               \
\       C ~= Enemy & C ~: Friend``leaked -->                       \
\        (ALL S A Y. Says S A Y : set_of_list evs -->     \
\         (ALL N B X. Crypt {|N, Agent B, Key K, X|} (shrK C) : parts{Y} --> \
\          X=X'))";
be ns_shared.induct 1;
by (forward_tac [Says_S_message_form] 5 THEN assume_tac 5);	
by (ALLGOALS 
    (asm_simp_tac (!simpset addsimps [all_conj_distrib, imp_conj_distrib])));
by (REPEAT_FIRST (eresolve_tac [exE,disjE]));
(*NS3: Fake (compromised) case*)
by (ex_strip_tac 4);
by (fast_tac (!claset addSDs [synth.Inj RS Crypt_Fake_parts, 
			      Crypt_parts_singleton]) 4);
(*NS3: Good case, no relevant messages*)
by (fast_tac (!claset addSEs [exI] addss (!simpset)) 3);
(*NS2: Case split propagates some context to other subgoal...*)
by (excluded_middle_tac "K = newK evsa" 2);
by (Asm_simp_tac 2);
be exI 2;
(*...we assume X is a very new message, and handle this case by contradiction*)
by (fast_tac (!claset addIs [impOfSubs (subset_insertI RS parts_mono)]
		      addSEs partsEs
		      addEs [Says_imp_old_keys RS less_irrefl]
	              addss (!simpset)) 2);
(*Fake*) (** LEVEL 11 **)
by (ex_strip_tac 1);
by (fast_tac (!claset addSDs [Crypt_Fake_parts, Crypt_parts_singleton]) 1);
val lemma = result();


(*In messages of this form, the session key uniquely identifies the rest*)
goal thy 
 "!!evs. [| Says S A          \
\             (Crypt {|N, Agent B, Key K, X|} (shrK C))     \
\                  : set_of_list evs; \ 
\           Says S' A'                                         \
\             (Crypt {|N', Agent B', Key K, X'|} (shrK C')) \
\                  : set_of_list evs;                         \
\           evs : ns_shared;  C ~= Enemy;  C ~: Friend``leaked;  C' ~= Enemy;  C' ~: Friend``leaked |] ==> X = X'";
bd lemma 1;
be exE 1;
(*Duplicate the assumption*)
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
(*Are these instantiations essential?*)
by (dres_inst_tac [("x","C")] spec 1);
by (dres_inst_tac [("x","C'")] spec 1);
by (fast_tac (!claset addSDs [spec]) 1);
qed "unique_session_keys";



(*Crucial secrecy property: Enemy does not see the keys sent in msg NS2*)
goal thy 
 "!!evs. [| Says Server (Friend i)                                       \
\            (Crypt {|N, Agent(Friend j), K, X|} K') : set_of_list evs;  \
\           i ~: leaked;  j ~: leaked;  evs : ns_shared                  \
\        |] ==>                                                          \
\     K ~: analz (sees Enemy evs)";
be rev_mp 1;
be ns_shared.induct 1;
by (ALLGOALS Asm_simp_tac);
(*Next 3 steps infer that K has the form "Key (newK evs'" ... *)
by (REPEAT_FIRST (resolve_tac [conjI, impI]));
by (TRYALL (forward_tac [Says_Server_message_form] THEN' assume_tac));
by (REPEAT_FIRST (eresolve_tac [bexE, conjE] ORELSE' hyp_subst_tac));
by (ALLGOALS 
    (asm_full_simp_tac 
     (!simpset addsimps ([analz_subset_parts RS contra_subsetD,
			  analz_insert_Key_newK] @ pushes)
               setloop split_tac [expand_if])));
(*NS2*)
by (fast_tac (!claset addSEs [less_irrefl]) 2);
(*Fake case*) (** LEVEL 8 **)
by (enemy_analz_tac 1);
(*NS3: that message from the Server was sent earlier*)
by (mp_tac 1);
by (forward_tac [Says_S_message_form] 1 THEN assume_tac 1);
by (REPEAT_FIRST (eresolve_tac [bexE, conjE, disjE] ORELSE' hyp_subst_tac));
by (enemy_analz_tac 2);		(*Prove the Fake subcase*)
by (asm_full_simp_tac
    (!simpset addsimps (mem_if::analz_insert_Key_newK::pushes)) 1);
(**************** by (Step_tac 1); ****************)
by (step_tac HOL_cs 1);
(**LEVEL 15 **)
by (excluded_middle_tac "ia : leaked" 1);
bd (Says_imp_sees_Enemy RS analz.Inj) 2;
bd analz.Decrypt 2;
by (asm_full_simp_tac (!simpset addsimps [shrK_mem_analz]) 2);
by (Fast_tac 2);
(*So now we know that Friend ia is a good agent*)
bd unique_session_keys 1;
by (REPEAT_FIRST assume_tac);
by (ALLGOALS Full_simp_tac);
by (Step_tac 1);
by (auto_tac (!claset, !simpset addsimps [shrK_mem_analz]));
qed "Enemy_not_see_encrypted_key";

