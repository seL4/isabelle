(*  Title:      HOL/Auth/Message
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatype of events;
inductive relation "traces" for Needham-Schroeder (shared keys)
*)


open Event;

(* invKey (serverKey A) = serverKey A *)
bind_thm ("invKey_serverKey", rewrite_rule [isSymKey_def] isSym_serverKey);

(* invKey (newK(A,evs)) = newK(A,evs) *)
bind_thm ("invKey_newK", rewrite_rule [isSymKey_def] isSym_newK);
Addsimps [invKey_serverKey, invKey_newK];


(*New keys and nonces are fresh*)
val serverKey_inject = inj_serverKey RS injD;
val newN_inject = inj_newN RS injD RS Pair_inject
and newK_inject = inj_newK RS injD RS Pair_inject;
AddSEs [serverKey_inject, newN_inject, newK_inject,
	fresh_newK RS notE, fresh_newN RS notE];
Addsimps [inj_serverKey RS inj_eq, inj_newN RS inj_eq, inj_newK RS inj_eq];
Addsimps [fresh_newN, fresh_newK];

goal thy "newK (A,evs) ~= serverKey B";
by (subgoal_tac "newK (A,evs) = serverKey B --> \
\                Key (newK(A,evs)) : parts (initState B)" 1);
by (Fast_tac 1);
by (agent.induct_tac "B" 1);
by (auto_tac (!claset addIs [range_eqI], !simpset));
qed "newK_neq_serverKey";

Addsimps [newK_neq_serverKey, newK_neq_serverKey RS not_sym];

(*Good for talking about Server's initial state*)
goal thy "parts (range (Key o f)) = range (Key o f)";
by (auto_tac (!claset addIs [range_eqI], !simpset));
be parts.induct 1;
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "parts_range_Key";

goal thy "analyze (range (Key o f)) = range (Key o f)";
by (auto_tac (!claset addIs [range_eqI], !simpset));
be analyze.induct 1;
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "analyze_range_Key";

Addsimps [parts_range_Key, analyze_range_Key];

goalw thy [keysFor_def] "keysFor (parts (initState C)) = {}";
by (agent.induct_tac "C" 1);
by (auto_tac (!claset addIs [range_eqI], !simpset));
qed "keysFor_parts_initState";
Addsimps [keysFor_parts_initState];


(**** Inductive relation "traces" -- basic properties ****)

val mk_cases = traces.mk_cases (list.simps @ agent.simps @ event.simps);

val Says_tracesE        = mk_cases "Says A B X # evs: traces";
val Says_Server_tracesE = mk_cases "Says Server B X # evs: traces";
val Says_Enemy_tracesE  = mk_cases "Says Enemy B X # evs: traces";
val Says_to_Server_tracesE = mk_cases "Says A Server X # evs: traces";
val Notes_tracesE       = mk_cases "Notes A X # evs: traces";


(*The tail of a trace is a trace*)
goal thy "!!ev evs. ev#evs : traces ==> evs : traces";
by (fast_tac (!claset addEs [mk_cases "ev#evs:traces"]) 1);
qed "traces_ConsE";

(** Specialized rewrite rules for (sees A (Says...#evs)) **)

goal thy "sees A (Says A B X # evs) = insert X (sees A evs)";
by (Simp_tac 1);
by (Fast_tac 1);
qed "sees_own";

goal thy "!!A. Server ~= A ==> \
\              sees Server (Says A B X # evs) = sees Server evs";
by (Asm_simp_tac 1);
qed "sees_Server";

goal thy "!!A. Friend i ~= A ==> \
\              sees (Friend i) (Says A B X # evs) = sees (Friend i) evs";
by (Asm_simp_tac 1);
qed "sees_Friend";

goal thy "sees Enemy (Says A B X # evs) = insert X (sees Enemy evs)";
by (Simp_tac 1);
by (Fast_tac 1);
qed "sees_Enemy";

goal thy "sees A (Says A' B X # evs) <= insert X (sees A evs)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Fast_tac 1);
qed "sees_subset";

(*Pushing Unions into parts; one of the A's equals B, and thus sees Y*)
goal thy "(UN A. parts (sees A (Says B C Y # evs))) = \
\         parts {Y} Un (UN A. parts (sees A evs))";
by (Step_tac 1);
be rev_mp 1;	(*for some reason, split_tac does not work on assumptions*)
val ss = (!simpset addsimps [parts_Un, sees_Cons] 
	           setloop split_tac [expand_if]);
by (ALLGOALS (fast_tac (!claset addss ss)));
qed "UN_parts_sees_Says";


Addsimps [UN_parts_sees_Says, sees_own, sees_Server, sees_Friend, sees_Enemy];
Delsimps [sees_Cons];


(**** Inductive proofs about traces ****)

(*The Enemy can see more than anybody else, except for their initial state*)
goal thy 
 "!!evs. evs : traces ==> \
\     sees A evs <= initState A Un sees Enemy evs";
be traces.induct 1;
be subst 4;	(*simply DISCARD evsa = Says A Server... as irrelevant!*)
by (ALLGOALS (fast_tac (!claset addDs [sees_subset RS subsetD] 
			        addss (!simpset))));
qed "sees_agent_subset_sees_Enemy";


(*** Server keys are not betrayed ***)

(*No Enemy will ever see a Friend's server key
   -- even if another friend's key is compromised.
  The UN is essential to handle the Fake rule in the induction.*)
goal thy 
 "!!evs. [| evs : traces;  i~=j |] ==> \
\        Key (serverKey (Friend i)) ~: \
\        parts (initState (Friend j) Un sees Enemy evs)";
be traces.induct 1;
be subst 4;	(*DISCARD evsa = Says A Server...#evs'a as irrelevant!*)
by (Auto_tac());
(*Deals with Faked messages*)
by (best_tac (!claset addDs [imp_of_subset analyze_subset_parts,
			     imp_of_subset parts_insert_subset_Un]
	              addss (!simpset)) 1);
qed "Enemy_not_see_serverKey";

(*No Friend will ever see another Friend's server key.*)
goal thy 
 "!!evs. [| evs : traces;  i~=j |] ==> \
\        Key (serverKey (Friend i)) ~: parts (sees (Friend j) evs)";
br (sees_agent_subset_sees_Enemy RS parts_mono RS contra_subsetD) 1;
by (REPEAT (ares_tac [Enemy_not_see_serverKey] 1));
qed "Friend_not_see_serverKey";

(*Variant needed for the theorem below*)
goal thy 
 "!!evs. evs : traces ==> \
\        Key (serverKey (Friend i)) ~: analyze (sees Enemy evs)";
bd Enemy_not_see_serverKey 1;
br n_not_Suc_n 1;
by (Full_simp_tac 1);
by (fast_tac (!claset addDs [imp_of_subset analyze_subset_parts]) 1);
qed "serverKeys_not_analyzed";


(*** Future keys can't be seen or used! ***)

(*Nobody can have SEEN keys that will be generated in the future.
  This has to be proved anew for each protocol description,
  but should go by similar reasoning every time.  Hardest case is the
  standard Fake rule.  
      The length comparison, and Union over C, are essential for the 
  induction! *)
goal thy "!!evs. evs : traces ==> \
\                length evs <= length evs' --> \
\                          Key (newK (A,evs')) ~: (UN C. parts (sees C evs))";
be traces.induct 1;
be subst 4;	(*DISCARD evsa = Says A Server...#evs'a as irrelevant!*)
by (ALLGOALS (asm_full_simp_tac
	      (!simpset addsimps [de_Morgan_disj,Suc_le_eq])));
(*Initial state?  New keys cannot clash*)
by (Fast_tac 1);
(*Rule NS1 in protocol*)
by (fast_tac (!claset addDs [less_imp_le]) 2);
(*Rule NS2 in protocol*)
by (fast_tac (!claset addIs [less_imp_le] addss (!simpset)) 2);
(*Rule Fake: where an Enemy agent can say practically anything*)
by (best_tac (!claset addDs [imp_of_subset analyze_subset_parts,
			     imp_of_subset parts_insert_subset_Un,
			     less_imp_le]
	              addss (!simpset)) 1);
val lemma = result();

(*Variant needed for the main theorem below*)
goal thy 
 "!!evs. [| evs : traces;  length evs <= length evs' |] ==> \
\        Key (newK (A,evs')) ~: parts (sees C evs)";
by (fast_tac (!claset addDs [lemma]) 1);
qed "new_keys_not_seen";

goal thy "!!K. newK(A,evs) = invKey K ==> newK(A,evs) = K";
br (invKey_eq RS iffD1) 1;
by (Simp_tac 1);
val newK_invKey = result();

(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : traces ==> \
\                length evs <= length evs' --> \
\                newK (A,evs') ~: keysFor (UN C. parts (sees C evs))";
be traces.induct 1;
be subst 4;	(*DISCARD evsa = Says A Server...#evs'a as irrelevant!*)
by (ALLGOALS (asm_full_simp_tac
	      (!simpset addsimps [de_Morgan_disj,Suc_le_eq])));
(*Rule NS1 in protocol*)
by (fast_tac (!claset addDs [less_imp_le]) 2);
(*Rule NS2 in protocol*)
by (fast_tac (!claset addDs [less_imp_le]) 2);
(*Rule Fake: where an Enemy agent can say practically anything*)
by (best_tac 
    (!claset addSDs [newK_invKey]
	     addDs [imp_of_subset (analyze_subset_parts RS keysFor_mono),
		    imp_of_subset (parts_insert_subset_Un RS keysFor_mono),
		    less_imp_le]
             addEs [new_keys_not_seen RS not_parts_not_analyze RSN (2,rev_notE)]
	     addss (!simpset)) 1);
val lemma = result();

goal thy 
 "!!evs. [| evs : traces;  length evs <= length evs' |] ==> \
\        newK (A,evs') ~: keysFor (parts (sees C evs))";
by (fast_tac (!claset addSDs [lemma] addss (!simpset)) 1);
qed "new_keys_not_used";

bind_thm ("new_keys_not_used_analyze",
	  [analyze_subset_parts RS keysFor_mono,
	   new_keys_not_used] MRS contra_subsetD);


(*Pushes Crypt events in so that others might be pulled out*)
goal thy "insert (Crypt X K) (insert y evs) = \
\         insert y (insert (Crypt X K) evs)";
by (Fast_tac 1);
qed "insert_Crypt_delay";

goal thy "insert (Key K) (insert y evs) = \
\         insert y (insert (Key K) evs)";
by (Fast_tac 1);
qed "insert_Key_delay";

(** Lemmas concerning the form of items passed in messages **)

(*Describes the form *and age* of K when the following message is sent*)
goal thy 
 "!!evs. [| Says Server A (Crypt {|Agent A, Agent B, K, N|} K') \
\               : setOfList evs;  \
\           evs : traces          \
\        |] ==> (EX evs'. K = Key (newK(Server,evs')) & \
\                         length evs' < length evs)";
be rev_mp 1;
be traces.induct 1;
be subst 4;	(*DISCARD evsa = Says A Server...#evs'a as irrelevant!*)
by (ALLGOALS (fast_tac (!claset addIs [less_SucI] addss (!simpset))));
qed "Says_Server_imp_Key_newK";

Addsimps [serverKeys_not_analyzed, 
	  new_keys_not_seen RS not_parts_not_analyze,
	  new_keys_not_used_analyze];


goal thy 
 "!!evs. evs : traces ==> \
\     Says Server (Friend i) \
\          (Crypt {|Agent(Friend i), Agent B, K, N|} K') : setOfList evs  \
\     --> K ~: analyze (sees Enemy evs)";
be traces.induct 1;
be subst 4;	(*simply DISCARD evsa = Says A Server... as irrelevant!*)
by (ALLGOALS Asm_full_simp_tac);
(*We infer that K has the form "Key (newK(Server,evs')" ... *)
br conjI 3;
by (REPEAT_FIRST (resolve_tac [impI]));
by (TRYALL (forward_tac [Says_Server_imp_Key_newK] THEN' assume_tac));
(*NS1, subgoal concerns "(Says A Server
                          {|Agent A, Agent B, Nonce (newN (A, evsa))|}"*)
(*... thus it cannot equal any components of A's message above.*)
by (fast_tac (!claset addss (!simpset)) 2);
(*NS2, the subcase where that message was the most recently sent;
  it holds because here K' = serverKey(Friend i), which Enemies can't see*)
by (fast_tac (!claset addss (!simpset)) 2);
(*NS2, other subcase!*)
by (fast_tac 
    (!claset addSEs [less_irrefl]
             addDs [imp_of_subset analyze_insert_Crypt_subset]
	     addss (!simpset addsimps [new_keys_not_used_analyze])) 2);
(*Now for the Fake case*)
be exE 1;
br notI 1;
by (REPEAT (etac conjE 1));
by (REPEAT (hyp_subst_tac 1));
by (subgoal_tac "Key (newK (Server, evs')) : analyze (synthesize (analyze (sees Enemy evsa)))" 1);
be (imp_of_subset analyze_mono) 2;
by (best_tac (!claset addIs [analyze_mono RS synthesize_mono RSN 
			     (2,rev_subsetD),
			     imp_of_subset synthesize_increasing,
			     imp_of_subset analyze_increasing]) 2);
(*Proves the Fake goal*)
by (Auto_tac());
qed "encrypted_key_not_seen";



XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX;

(*Nobody can have SEEN keys that will be generated in the future.
  This has to be proved anew for each protocol description,
  but should go by similar reasoning every time.  Hardest case is the
  standard Fake rule.  
      The length comparison, and Union over C, are essential for the 
  induction! *)
goal thy "!!evs. evs : traces ==> \
\                length evs <= length evs' --> \
\                          Key (newK (A,evs')) ~: (UN C. parts (sees C evs))";
be traces.induct 1;
be subst 4;	(*DISCARD evsa = Says A Server...#evs'a as irrelevant!*)
by (ALLGOALS (asm_full_simp_tac
	      (!simpset addsimps [de_Morgan_disj,Suc_le_eq])));
(*Initial state?  New keys cannot clash*)
by (Fast_tac 1);
(*Rule NS1 in protocol*)
by (fast_tac (!claset addDs [less_imp_le]) 2);
(*Rule NS2 in protocol*)
by (fast_tac (!claset addIs [less_imp_le] addss (!simpset)) 2);
(*Rule Fake: where an Enemy agent can say practically anything*)
by (best_tac (!claset addDs [imp_of_subset analyze_subset_parts,
			     imp_of_subset parts_insert_subset_Un,
			     less_imp_le]
	              addss (!simpset)) 1);
val lemma = result();



goal thy 
 "!!evs. [| evs : traces;  i~=j |] ==> \
\     Says Server (Friend i) \
\          (Crypt {|Agent(Friend i), Agent B, K, N|} K') : setOfList evs  \
\     --> K ~: analyze (initState (Friend j) Un sees Enemy evs)";
be traces.induct 1;
be subst 4;	(*simply DISCARD evsa = Says A Server... as irrelevant!*)
by (ALLGOALS Asm_full_simp_tac);
(*We infer that K has the form "Key (newK(Server,evs')" ... *)
br conjI 3;
by (REPEAT_FIRST (resolve_tac [impI]));
by (TRYALL (forward_tac [Says_Server_imp_Key_newK] THEN' assume_tac));
(*NS1, subgoal concerns "(Says A Server
                          {|Agent A, Agent B, Nonce (newN (A, evsa))|}"*)
(*... thus it cannot equal any components of A's message above.*)

by (full_simp_tac (!simpset addsimps [insert_Key_delay, insert_is_Un RS sym]) 2);

by (fast_tac (!claset addss (!simpset)) 2);
(*NS2, the subcase where that message was the most recently sent;
  it holds because here K' = serverKey(Friend i), which Enemies can't see*)
by (full_simp_tac (!simpset addsimps [insert_Key_delay, insert_is_Un RS sym]) 2);
by (Safe_step_tac 2);

by (stac analyze_insert_Crypt 2);

by (fast_tac (!claset addss (!simpset)) 2);
(*NS2, other subcase!*)

by (full_simp_tac (!simpset addsimps [insert_Key_delay, insert_is_Un RS sym]) 2);
by (fast_tac 
    (!claset addSEs [less_irrefl]
             addDs [imp_of_subset analyze_insert_Crypt_subset]
	     addss (!simpset addsimps [new_keys_not_used_analyze])) 2);
(*Now for the Fake case*)
be exE 1;
br notI 1;
by (REPEAT (etac conjE 1));
by (REPEAT (hyp_subst_tac 1));
by (subgoal_tac "Key (newK (Server, evs')) : analyze (synthesize (analyze (sees Enemy evsa)))" 1);
be (imp_of_subset analyze_mono) 2;
by (best_tac (!claset addIs [analyze_mono RS synthesize_mono RSN 
			     (2,rev_subsetD),
			     imp_of_subset synthesize_increasing,
			     imp_of_subset analyze_increasing]) 2);
(*Proves the Fake goal*)
by (Auto_tac());
qed "encrypted_key_not_seen";




(*Bet this requires the premise   A = Friend i *)
goal thy "[| evs : traces;  \
\            (Says Server A (Crypt {|Agent A, Agent B, K, N|} K')) \
\            : setOfList evs  \
\         |] ==> knownBy evs K <= {A,Server}";


XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX;

(*NEEDED??*)

goal thy "!!A. X ~= Y ==> (X : sees A (Says B C Y # evs)) = (X : sees A evs)";
by (asm_simp_tac (!simpset addsimps [sees_Cons] 
                           setloop split_tac [expand_if]) 1); 
qed "in_sees_Says";

goal thy "!!A. X ~: parts {Y} ==> \
\              (X : parts (sees A (Says B C Y # evs))) = \
\              (X : parts (sees A evs))";
by (asm_simp_tac (!simpset addsimps [sees_Cons] 
                           setloop split_tac [expand_if]) 1); 
by (asm_simp_tac (!simpset addsimps [parts_Un]) 1); 
qed "in_parts_sees_Says";

goal thy "!!evs. length evs < length evs' ==> newK (A,evs) ~= newK (A',evs')";
by (fast_tac (!claset addSEs [less_irrefl]) 1);
qed "length_less_newK_neq";


(*Initially
goal thy "knownBy [] X = \
\         {A. X = Key (invKey (serverKey A)) | (? i. X = Key (serverKey i))}";
by (simp_tac (!simpset addsimps [knownBy_def, analyze_trivial, range_def]) 1);
qed "knownBy_Nil";

goal thy "!!X. knownBy (x#l) X = ?F(knownBy l X)";
by (simp_tac (!simpset addsimps [knownBy_def, analyze_trivial, range_def]) 1);
********************)

goal thy "insert (Crypt x) (insert {|X,Y|} evs) = \
\         insert {|X,Y|} (insert (Crypt x) evs)";
by (Fast_tac 1);
qed "insert_Crypt_MPair_delay";



WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW;

goal thy 
 "!!evs. evs : traces ==> \
\     Says Server A       \
\          (Crypt {|Agent A, Agent B, K, N|} K') : setOfList evs  \
\     --> (EX evs'. K = Key (newK(Server,evs')))";
be traces.induct 1;
by (ALLGOALS Asm_simp_tac);
by (Fast_tac 1);
val Says_Server_lemma = result();

goal thy 
 "!!evs. [| Says Server A (Crypt {|Agent A, Agent B, K, N|} K') \
\               : setOfList evs;  \
\           evs : traces          \
\        |] ==> (EX evs'. K = Key (newK(Server,evs')))";
bd Says_Server_lemma 1;
by (Fast_tac 1);
qed "Says_Server_imp_Key_newK";


goal thy 
 "!!evs. evs : traces ==> \
\     Says Server A \
\          (Crypt {|Agent A, Agent B, K, N|} K') : setOfList evs  \
\     --> (EX evs'. N = Nonce (newN(A,evs')))";
be traces.induct 1;
by (ALLGOALS Asm_simp_tac);
by (Fast_tac 1);
val Says_Server_lemma = result();


YYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYY;

goalw thy [keysFor_def]
    "!!X. Crypt X K: H ==> invKey K : keysFor H";
by (Fast_tac 1);
qed "keysFor_I";
AddSIs [keysFor_I];

goalw thy [keysFor_def]
    "!!K. K : keysFor H ==> EX X K'. K=invKey K' & Crypt X K': H";
by (Fast_tac 1);
qed "keysFor_D";
AddSDs [keysFor_D];


