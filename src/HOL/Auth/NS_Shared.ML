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


(*For reasoning about message NS3*)
goal thy "!!evs. (Says S A (Crypt {|N, B, K, X|} KA)) : set_of_list evs ==> \
\                X : parts (sees Enemy evs)";
by (fast_tac (!claset addSEs partsEs
	              addSDs [Says_imp_sees_Enemy RS parts.Inj]) 1);
qed "NS3_msg_in_parts_sees_Enemy";
			      

(*** Server keys are not betrayed ***)

(*Enemy never sees another agent's server key!*)
goal thy 
 "!!evs. [| evs : ns_shared; A ~= Enemy |] ==> \
\        Key (serverKey A) ~: parts (sees Enemy evs)";
be ns_shared.induct 1;
bd NS3_msg_in_parts_sees_Enemy 5;
by (Auto_tac());
(*Deals with Fake message*)
by (best_tac (!claset addDs [impOfSubs analz_subset_parts,
			     impOfSubs synth_analz_parts_insert_subset_Un]) 1);
qed "Enemy_not_see_serverKey";

bind_thm ("Enemy_not_analz_serverKey",
	  [analz_subset_parts, Enemy_not_see_serverKey] MRS contra_subsetD);

Addsimps [Enemy_not_see_serverKey, 
	  not_sym RSN (2, Enemy_not_see_serverKey), 
	  Enemy_not_analz_serverKey, 
	  not_sym RSN (2, Enemy_not_analz_serverKey)];

(*We go to some trouble to preserve R in the 3rd subgoal*)
val major::prems = 
goal thy  "[| Key (serverKey A) : parts (sees Enemy evs);    \
\             evs : ns_shared;                                  \
\             A=Enemy ==> R                                  \
\           |] ==> R";
br ccontr 1;
br ([major, Enemy_not_see_serverKey] MRS rev_notE) 1;
by (swap_res_tac prems 2);
by (ALLGOALS (fast_tac (!claset addIs prems)));
qed "Enemy_see_serverKey_E";

bind_thm ("Enemy_analz_serverKey_E", 
	  analz_subset_parts RS subsetD RS Enemy_see_serverKey_E);

(*Classical reasoner doesn't need the not_sym versions (with swapped ~=) *)
AddSEs [Enemy_see_serverKey_E, Enemy_analz_serverKey_E];


(*No Friend will ever see another agent's server key 
  (excluding the Enemy, who might transmit his).
  The Server, of course, knows all server keys.*)
goal thy 
 "!!evs. [| evs : ns_shared; A ~= Enemy;  A ~= Friend j |] ==> \
\        Key (serverKey A) ~: parts (sees (Friend j) evs)";
br (sees_agent_subset_sees_Enemy RS parts_mono RS contra_subsetD) 1;
by (ALLGOALS Asm_simp_tac);
qed "Friend_not_see_serverKey";


(*Not for Addsimps -- it can cause goals to blow up!*)
goal thy  
 "!!evs. evs : ns_shared ==>                                  \
\        (Key (serverKey A) \
\           : analz (insert (Key (serverKey B)) (sees Enemy evs))) =  \
\        (A=B | A=Enemy)";
by (best_tac (!claset addDs [impOfSubs analz_subset_parts]
		      addIs [impOfSubs (subset_insertI RS analz_mono)]
	              addss (!simpset)) 1);
qed "serverKey_mem_analz";


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
\                         X = (Crypt {|K, Agent A|} (serverKey B)) & \
\                         K' = serverKey A & \
\                         length evt < length evs)";
be rev_mp 1;
be ns_shared.induct 1;
by (ALLGOALS (fast_tac (!claset addIs [less_SucI] addss (!simpset))));
qed "Says_Server_message_form";


(*Describes the form of X when the following message is sent*)
goal thy
 "!!evs. evs : ns_shared ==>                             \
\        ALL A NA B K X.                            \
\            (Crypt {|Nonce NA, Agent B, Key K, X|} (serverKey A)) \
\            : parts (sees Enemy evs) & A ~= Enemy  -->   \
\          (EX evt:ns_shared. K = newK evt & \
\                          X = (Crypt {|Key K, Agent A|} (serverKey B)))";
be ns_shared.induct 1;
bd NS3_msg_in_parts_sees_Enemy 5;
by (Step_tac 1);
by (ALLGOALS Asm_full_simp_tac);
(*Remaining cases are Fake and NS2*)
by (fast_tac (!claset addSDs [spec]) 2);
(*Now for the Fake case*)
by (best_tac (!claset addDs [impOfSubs analz_subset_parts,
			     impOfSubs synth_analz_parts_insert_subset_Un]
	              addss (!simpset)) 1);
qed_spec_mp "encrypted_form";


(*For eliminating the A ~= Enemy condition from the previous result*)
goal thy 
 "!!evs. evs : ns_shared ==>                             \
\        ALL S A NA B K X.                            \
\            Says S A (Crypt {|Nonce NA, Agent B, Key K, X|} (serverKey A)) \
\            : set_of_list evs  -->   \
\        S = Server | S = Enemy";
be ns_shared.induct 1;
by (ALLGOALS Asm_simp_tac);
(*We are left with NS3*)
by (subgoal_tac "S = Server | S = Enemy" 1);
(*First justify this assumption!*)
by (fast_tac (!claset addSEs [allE, mp] addss (!simpset)) 2);
by (Step_tac 1);
bd Says_Server_message_form 1;
by (ALLGOALS Full_simp_tac);
(*Final case.  Clear out needless quantifiers to speed the following step*)
by (eres_inst_tac [("V","ALL x. ?P(x)")] thin_rl 1);
bd encrypted_form 1;
br (parts.Inj RS conjI) 1;
auto();
qed_spec_mp "Server_or_Enemy";


(*Describes the form of X when the following message is sent;
  use Says_Server_message_form if applicable*)
goal thy 
 "!!evs. [| Says S A (Crypt {|Nonce NA, Agent B, Key K, X|} (serverKey A)) \
\            : set_of_list evs;                              \
\           evs : ns_shared               \
\        |] ==> (EX evt:ns_shared. K = newK evt & length evt < length evs & \
\                               X = (Crypt {|Key K, Agent A|} (serverKey B)))";
by (forward_tac [Server_or_Enemy] 1);
ba 1;
by (Step_tac 1);
by (fast_tac (!claset addSDs [Says_Server_message_form] addss (!simpset)) 1);
by (forward_tac [encrypted_form] 1);
br (parts.Inj RS conjI) 1;
by (auto_tac (!claset addIs [Says_imp_old_keys], !simpset));
qed "Says_S_message_form";



(****
 The following is to prove theorems of the form

          Key K : analz (insert (Key (newK evt)) 
	                   (insert (Key (serverKey C)) (sees Enemy evs))) ==>
          Key K : analz (insert (Key (serverKey C)) (sees Enemy evs))

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
                      addss (!simpset)) 1);
(*NS4 and NS5*)
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
result();


(** Specialized rewriting for this proof **)

Delsimps [image_insert];
Addsimps [image_insert RS sym];

goal thy "insert (Key (newK x)) (sees A evs) = \
\         Key `` (newK``{x}) Un (sees A evs)";
by (Fast_tac 1);
val insert_Key_singleton = result();

goal thy "insert (Key (f x)) (Key``(f``E) Un C) = \
\         Key `` (f `` (insert x E)) Un C";
by (Fast_tac 1);
val insert_Key_image = result();


(** Session keys are not used to encrypt other session keys **)

goal thy  
 "!!evs. evs : ns_shared ==> \
\  ALL K E. (Key K : analz (insert (Key (serverKey C)) \
\                             (Key``(newK``E) Un (sees Enemy evs)))) = \
\           (K : newK``E |  \
\            Key K : analz (insert (Key (serverKey C)) \
\                             (sees Enemy evs)))";
be ns_shared.induct 1;
by (forward_tac [Says_S_message_form] 5 THEN assume_tac 5);	
by (REPEAT ((eresolve_tac [bexE, conjE] ORELSE' hyp_subst_tac) 5));
by (ALLGOALS 
    (asm_simp_tac 
     (!simpset addsimps ([insert_Key_singleton, insert_Key_image, pushKey_newK]
			 @ pushes)
               setloop split_tac [expand_if])));
(*Cases NS2 and NS3!!  Simple, thanks to auto case splits*)
by (REPEAT (Fast_tac 3));
(*Base case*)
by (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1);
(** LEVEL 7 **)
(*Fake case*)
by (REPEAT (Safe_step_tac 1));
by (fast_tac (!claset addSEs [impOfSubs analz_mono]) 2);
by (subgoal_tac 
    "Key K : analz \
\             (synth \
\              (analz (insert (Key (serverKey C)) \
\                        (Key``(newK``E) Un (sees Enemy evsa)))))" 1);
(*First, justify this subgoal*)
(*Discard formulae for better speed*)
by (eres_inst_tac [("V","ALL S.?P(S)")] thin_rl 2);
by (eres_inst_tac [("V","?Q ~: ?QQ")] thin_rl 2);
by (best_tac (!claset addIs [impOfSubs (analz_mono RS synth_mono)]
                      addSEs [impOfSubs analz_mono]) 2);
by (Asm_full_simp_tac 1);
by (deepen_tac (!claset addIs [impOfSubs analz_mono]) 0 1);
qed_spec_mp "analz_image_newK";


goal thy
 "!!evs. evs : ns_shared ==>                               \
\        Key K : analz (insert (Key (newK evt))            \
\                         (insert (Key (serverKey C))      \
\                          (sees Enemy evs))) =            \
\             (K = newK evt |                              \
\              Key K : analz (insert (Key (serverKey C))   \
\                               (sees Enemy evs)))";
by (asm_simp_tac (HOL_ss addsimps [pushKey_newK, analz_image_newK, 
				   insert_Key_singleton]) 1);
by (Fast_tac 1);
qed "analz_insert_Key_newK";



(*This says that the Key, K, uniquely identifies the message.
    But if C=Enemy then he could send all sorts of nonsense.*)
goal thy 
 "!!evs. evs : ns_shared ==>                      \
\      EX X'. ALL C S A Y N B X.               \
\         C ~= Enemy -->                       \
\         Says S A Y : set_of_list evs -->     \
\         ((Crypt {|N, Agent B, Key K, X|} (serverKey C)) : parts{Y} --> \
\       (X = X'))";
be ns_shared.induct 1;
by (forward_tac [Says_S_message_form] 5 THEN assume_tac 5);	
by (ALLGOALS 
    (asm_simp_tac (!simpset addsimps [all_conj_distrib, imp_conj_distrib])));
(*NS2: Case split propagates some context to other subgoal...*)
by (excluded_middle_tac "K = newK evsa" 2);
by (Asm_simp_tac 2);
(*...we assume X is a very new message, and handle this case by contradiction*)
by (fast_tac (!claset addIs [impOfSubs (subset_insertI RS parts_mono)]
		      addSEs partsEs
		      addEs [Says_imp_old_keys RS less_irrefl]
	              addss (!simpset)) 2);
(*NS3: No relevant messages*)
by (fast_tac (!claset addSEs [exI] addss (!simpset)) 2);
(*Fake*)
by (Step_tac 1);
br exI 1;
br conjI 1;
ba 2;
by (Step_tac 1);
(** LEVEL 12 **)
by (subgoal_tac "Crypt {|N, Agent Ba, Key K, Xa|} (serverKey C) \
\                  : parts (sees Enemy evsa)" 1);
by (eres_inst_tac [("V","ALL S.?P(S)")] thin_rl 2);
by (best_tac (!claset addSEs [impOfSubs analz_subset_parts]
	              addDs [impOfSubs parts_insert_subset_Un]
                      addss (!simpset)) 2);
by (eres_inst_tac [("V","?aa : parts {X}")] thin_rl 1);
bd parts_singleton 1;
by (Step_tac 1);
bd seesD 1;
by (Step_tac 1);
by (Full_simp_tac 2);
by (fast_tac (!claset addSDs [spec]) 1);
val lemma = result();


(*In messages of this form, the session key uniquely identifies the rest*)
goal thy 
 "!!evs. [| Says S A          \
\             (Crypt {|N, Agent B, Key K, X|} (serverKey C))     \
\                  : set_of_list evs; \
 \          Says S' A'                                         \
\             (Crypt {|N', Agent B', Key K, X'|} (serverKey C')) \
\                  : set_of_list evs;                         \
\           evs : ns_shared;  C ~= Enemy;  C' ~= Enemy    |] ==> X = X'";
bd lemma 1;
be exE 1;
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
by (Fast_tac 1);
qed "unique_session_keys";



(*Crucial secrecy property: Enemy does not see the keys sent in msg NS2
   -- even if another key is compromised*)
goal thy 
 "!!evs. [| Says Server (Friend i) \
\            (Crypt {|N, Agent(Friend j), K, X|} K') : set_of_list evs;  \
\           evs : ns_shared;  Friend i ~= C;  Friend j ~= C              \
\        |] ==>                                                       \
\     K ~: analz (insert (Key (serverKey C)) (sees Enemy evs))";
be rev_mp 1;
be ns_shared.induct 1;
by (ALLGOALS (asm_simp_tac (!simpset addsimps pushes)));
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
(** LEVEL 8 **)
(*Now for the Fake case*)
br notI 1;
by (subgoal_tac 
    "Key (newK evt) : \
\    analz (synth (analz (insert (Key (serverKey C)) \
\                                  (sees Enemy evsa))))" 1);
be (impOfSubs analz_mono) 2;
by (deepen_tac (!claset addIs [analz_mono RS synth_mono RSN (2,rev_subsetD),
			       impOfSubs synth_increasing,
			       impOfSubs analz_increasing]) 0 2);
(*Proves the Fake goal*)
by (fast_tac (!claset addss (!simpset)) 1);

(**LEVEL 13**)
(*NS3: that message from the Server was sent earlier*)
by (mp_tac 1);
by (forward_tac [Says_S_message_form] 1 THEN assume_tac 1);
by (REPEAT_FIRST (eresolve_tac [bexE, conjE] ORELSE' hyp_subst_tac));
by (asm_full_simp_tac
    (!simpset addsimps (mem_if::analz_insert_Key_newK::pushes)) 1);
by (Step_tac 1);
(**LEVEL 18 **)
bd unique_session_keys 1;
by (REPEAT_FIRST assume_tac);
by (ALLGOALS Full_simp_tac);
by (Step_tac 1);
by (asm_full_simp_tac (!simpset addsimps [serverKey_mem_analz]) 1);
qed "Enemy_not_see_encrypted_key";




