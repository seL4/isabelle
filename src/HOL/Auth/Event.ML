(*  Title:      HOL/Auth/Message
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatype of events;
inductive relation "traces" for Needham-Schroeder (shared keys)

Rewrites should not refer to	 initState (Friend i)    -- not in normal form
*)


open Event;

(*Rewrite using   {a} Un A = insert a A *)
Addsimps [insert_is_Un RS sym];


(*** Basic properties of serverKey and newK ***)

(* invKey (serverKey A) = serverKey A *)
bind_thm ("invKey_serverKey", rewrite_rule [isSymKey_def] isSym_serverKey);

(* invKey (newK evs) = newK evs *)
bind_thm ("invKey_newK", rewrite_rule [isSymKey_def] isSym_newK);
Addsimps [invKey_serverKey, invKey_newK];


(*New keys and nonces are fresh*)
val serverKey_inject = inj_serverKey RS injD;
val newN_inject = inj_newN RS injD
and newK_inject = inj_newK RS injD;
AddSEs [serverKey_inject, newN_inject, newK_inject,
	fresh_newK RS notE, fresh_newN RS notE];
Addsimps [inj_serverKey RS inj_eq, inj_newN RS inj_eq, inj_newK RS inj_eq];
Addsimps [fresh_newN, fresh_newK];

goal thy "newK evs ~= serverKey B";
by (subgoal_tac "newK evs = serverKey B --> \
\                Key (newK evs) : parts (initState B)" 1);
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
qed "sees_Enemy";

goal thy "sees A (Says A' B X # evs) <= insert X (sees A evs)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Fast_tac 1);
qed "sees_Says_subset_insert";

goal thy "sees A evs <= sees A (Says A' B X # evs)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Fast_tac 1);
qed "sees_subset_sees_Says";

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
Delsimps [sees_Cons];	(**** NOTE REMOVAL -- laws above are cleaner ****)


(**** Inductive proofs about traces ****)

(*The Enemy can see more than anybody else, except for their initial state*)
goal thy 
 "!!evs. evs : traces ==> \
\     sees A evs <= initState A Un sees Enemy evs";
be traces.induct 1;
be subst 4;	(*NS2: discard evsa = Says A Server... as irrelevant!*)
be subst 5;	(*NS3: discard evsa = Says S Aa... as irrelevant!*)
by (ALLGOALS (fast_tac (!claset addDs [sees_Says_subset_insert RS subsetD] 
			        addss (!simpset))));
qed "sees_agent_subset_sees_Enemy";


goal thy "!!evs. evs : traces ==> ALL A X. Says A A X ~: setOfList evs";
be traces.induct 1;
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(*** Server keys are not betrayed ***)

(*Enemy never sees another agent's server key!*)
goal thy 
 "!!evs. [| evs : traces; A ~= Enemy |] ==> \
\        Key (serverKey A) ~: parts (sees Enemy evs)";
be traces.induct 1;
be subst 4;	(*NS2: discard evsa = Says A Server...#evs'a as irrelevant!*)
by (auto_tac(!claset, !simpset addsimps [parts_insert2]));
(*Deals with Faked messages*)
by (best_tac (!claset addDs [impOfSubs analyze_subset_parts,
			     impOfSubs parts_insert_subset_Un]
	              addss (!simpset)) 1);
qed "Enemy_not_see_serverKey";

bind_thm ("Enemy_not_analyze_serverKey",
	  [analyze_subset_parts, Enemy_not_see_serverKey] MRS contra_subsetD);

Addsimps [Enemy_not_see_serverKey, Enemy_not_analyze_serverKey];


(*No Friend will ever see another agent's server key 
  (excluding the Enemy, who might transmit his).*)
goal thy 
 "!!evs. [| evs : traces; A ~= Enemy;  A ~= Friend j |] ==> \
\        Key (serverKey A) ~: parts (sees (Friend j) evs)";
br (sees_agent_subset_sees_Enemy RS parts_mono RS contra_subsetD) 1;
by (ALLGOALS Asm_simp_tac);
qed "Friend_not_see_serverKey";


(*** Future keys can't be seen or used! ***)

(*Nobody can have SEEN keys that will be generated in the future.
  This has to be proved anew for each protocol description,
  but should go by similar reasoning every time.  Hardest case is the
  standard Fake rule.  
      The length comparison, and Union over C, are essential for the 
  induction! *)
goal thy "!!evs. evs : traces ==> \
\                length evs <= length evs' --> \
\                          Key (newK evs') ~: (UN C. parts (sees C evs))";
be traces.induct 1;
be subst 4;	(*NS2: discard evsa = Says A Server...#evs'a as irrelevant!*)
by (ALLGOALS (asm_full_simp_tac
	      (!simpset addsimps [de_Morgan_disj,Suc_le_eq])));
(*Initial state?  New keys cannot clash*)
by (Fast_tac 1);
(*Rule NS1 in protocol*)
by (fast_tac (!claset addDs [less_imp_le]) 2);
(*Rule NS2 in protocol*)
by (fast_tac (!claset addIs [less_imp_le] addss (!simpset)) 2);
(*Rule NS3 in protocol*)
by (fast_tac (!claset addIs [less_imp_le] addss (!simpset)) 2);
(*Rule Fake: where an Enemy agent can say practically anything*)
by (best_tac (!claset addDs [impOfSubs analyze_subset_parts,
			     impOfSubs parts_insert_subset_Un,
			     less_imp_le]
	              addss (!simpset)) 1);
val lemma = result();

(*Variant needed for the main theorem below*)
goal thy 
 "!!evs. [| evs : traces;  length evs <= length evs' |] ==> \
\        Key (newK evs') ~: parts (sees C evs)";
by (fast_tac (!claset addDs [lemma]) 1);
qed "new_keys_not_seen";

goal thy "!!K. newK evs = invKey K ==> newK evs = K";
br (invKey_eq RS iffD1) 1;
by (Simp_tac 1);
val newK_invKey = result();


val keysFor_parts_mono = parts_mono RS keysFor_mono;

(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : traces ==> \
\                length evs <= length evs' --> \
\                newK evs' ~: keysFor (UN C. parts (sees C evs))";
be traces.induct 1;
be subst 4;	(*NS2: discard evsa = Says A Server...#evs'a as irrelevant!*)
by (ALLGOALS (asm_full_simp_tac
	      (!simpset addsimps [de_Morgan_disj,Suc_le_eq])));
(*Rule NS1 in protocol*)
by (fast_tac (!claset addDs [less_imp_le]) 2);
(*Rule NS2 in protocol*)
by (fast_tac (!claset addDs [less_imp_le]) 2);
(*Rule Fake: where an Enemy agent can say practically anything*)
by (best_tac 
    (!claset addSDs [newK_invKey]
	     addDs [impOfSubs (analyze_subset_parts RS keysFor_mono),
		    impOfSubs (parts_insert_subset_Un RS keysFor_mono),
		    less_imp_le]
             addEs [new_keys_not_seen RS not_parts_not_analyze RSN (2,rev_notE)]
	     addss (!simpset)) 1);
(*Rule NS3: quite messy...*)
by (hyp_subst_tac 1);
by (full_simp_tac (!simpset addcongs [conj_cong]) 1);
br impI 1;
bd mp 1;
by (fast_tac (!claset addDs [less_imp_le]) 1);
by (best_tac (!claset addIs 
	      [impOfSubs (sees_subset_sees_Says RS keysFor_parts_mono),
	       impOfSubs (sees_own RS equalityD2 RS keysFor_parts_mono),
	       impOfSubs (empty_subsetI RS insert_mono RS keysFor_parts_mono)]
              addss (!simpset)) 1);
val lemma = result();

goal thy 
 "!!evs. [| evs : traces;  length evs <= length evs' |] ==> \
\        newK evs' ~: keysFor (parts (sees C evs))";
by (fast_tac (!claset addSDs [lemma] addss (!simpset)) 1);
qed "new_keys_not_used";
Addsimps [new_keys_not_used];

bind_thm ("new_keys_not_analyzed",
	  [analyze_subset_parts RS keysFor_mono,
	   new_keys_not_used] MRS contra_subsetD);


(*Maybe too specific to be of much use...*)
goal thy 
 "!!evs. [| Says Server A (Crypt {|Nonce NA, Agent B, Key K, X|} \
\                                (serverKey A))                  \
\               : setOfList evs;                                 \
\           evs : traces    \
\        |] ==> (EX evs'. X = (Crypt {|Key(newK evs'), Agent A|} (serverKey B)))";
be rev_mp 1;
be traces.induct 1;
be subst 4;	(*NS2: discard evsa = Says A Server...#evs'a as irrelevant!*)
be subst 5;	(*NS3: discard evsa = Says S Aa... as irrelevant!*)
by (ALLGOALS Asm_full_simp_tac);
by (Fast_tac 1);	(*Proves the NS2 case*)
qed "Says_Server_imp_X_eq_Crypt";


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
 "!!evs. [| Says Server A (Crypt {|N, Agent B, K, X|} K') \
\               : setOfList evs;  \
\           evs : traces          \
\        |] ==> (EX evs'. K = Key (newK evs') & length evs' < length evs)";
be rev_mp 1;
be traces.induct 1;
be subst 4;	(*NS2: discard evsa = Says A Server...#evs'a as irrelevant!*)
by (ALLGOALS (fast_tac (!claset addIs [less_SucI] addss (!simpset))));
qed "Says_Server_imp_Key_newK";

(* c ~: keysFor (parts H) ==> c ~: keysFor (analyze H) *)
bind_thm ("not_parts_not_keysFor_analyze", 
	  analyze_subset_parts RS keysFor_mono RS contra_subsetD);


XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX;

ZZZZZZZZZZZZZZZZ;


(*Fake case below may need something like this...*)
goal thy 
 "!!evs. evs : traces ==>                             \
\        ALL B X. Crypt X (serverKey B) : analyze (sees Enemy evs)  -->   \
\        (EX A A'. Says A A' (Crypt X (serverKey B)) : setOfList evs";

goal thy 
 "!!evs. evs : traces ==>                             \
\        ALL NA B K X. Crypt {|Nonce NA, Agent B, Key K, X|} (serverKey B) :
                       analyze (sees Enemy evs)  -->   \
\        (EX A A'. Says A A' (Crypt {|Nonce NA, Agent B, Key K, X|} (serverKey B)) : setOfList evs";



(*Describes the form of X when the following message is sent*)
goal thy 
 "!!evs. evs : traces ==>                             \
\        ALL S A NA B K X.                            \
\            Says S A (Crypt {|Nonce NA, Agent B, Key K, X|} (serverKey A)) \
\            : setOfList evs  -->   \
\        (EX evs'. X = (Crypt {|Key(newK evs'), Agent A|} (serverKey B)))";
be traces.induct 1;
be subst 4;	(*NS2: discard evsa = Says A Server...#evs'a as irrelevant!*)
by (Step_tac 1);
by (ALLGOALS Asm_full_simp_tac);
(*Remaining cases are Fake, NS2 and NS3*)
by (Fast_tac 2);	(*Solves the NS2 case*)
(*The NS3 case needs the induction hypothesis twice!
    One application is to the X component of the most recent message.*)
by (full_simp_tac (!simpset addsimps [all_conj_distrib]) 2);
be conjE 2;
by (subgoal_tac "? evs'. X = Crypt {|Key (newK evs'), Agent (Friend i)|} (serverKey B)" 2);
by (eres_inst_tac [("V","?P|?Q")] thin_rl 3);	(*speeds the following step*)
by (Fast_tac 3);
(*DELETE the first quantified formula: it's now useless*)
by (eres_inst_tac [("V","ALL S.?P(S)")] thin_rl 2);
by (fast_tac (!claset addss (!simpset)) 2);
(*Now for the Fake case*)
be disjE 1;
(*The subcase of Fake, where the message in question is NOT the most recent*)
by (Best_tac 2);
(*The subcase of Fake proved because server keys are kept secret*)
by (REPEAT_FIRST (etac conjE ORELSE' hyp_subst_tac));
be Crypt_synthesize 1;
be Key_synthesize 2;
by (Asm_full_simp_tac 2);



 1. !!evs B X evsa S A NA Ba K Xa.
       [| evsa : traces;
          ! S A NA B K X.
             Says S A (Crypt {|Nonce NA, Agent B, Key K, X|} (serverKey A)) :
             setOfList evsa -->
             (? evs'. X = Crypt {|Key (newK evs'), Agent A|} (serverKey B));
          B ~= Enemy;
          Crypt {|Nonce NA, Agent Ba, Key K, Xa|} (serverKey B) :
          analyze (sees Enemy evsa) |] ==>
       ? evs'. Xa = Crypt {|Key (newK evs'), Agent B|} (serverKey Ba)


(*Split up the possibilities of that message being synthesized...*)
by (Step_tac 1);
by (Best_tac 6);




by (Safe_step_tac 1);
by (Safe_step_tac 2);
by (ALLGOALS Asm_full_simp_tac);
by (REPEAT_FIRST (etac disjE));
by (REPEAT_FIRST (etac conjE ORELSE' hyp_subst_tac));


by (hyp_subst_tac 5);





by (REPEAT (dtac spec 3));
fe conjE;
fe mp ;
by (REPEAT (resolve_tac [refl, conjI] 3));
by (REPEAT_FIRST (etac conjE));
by (REPEAT_FIRST (etac conjE ORELSE' hyp_subst_tac));


by (subgoal_tac "? evs'. Xa = Crypt {|Key (newK evs'), Agent Aa|} (serverKey Ba)" 2);
by (Fast_tac 3);



be subst 5;	(*NS3: discard evsa = Says S Aa... as irrelevant!*)


auto();
by (ALLGOALS
    (asm_full_simp_tac (!simpset addsimps [de_Morgan_disj,de_Morgan_conj])));
by (REPEAT_FIRST (etac conjE ORELSE' hyp_subst_tac));

by (REPEAT (Safe_step_tac 1));

qed "Says_Crypt_Nonce_imp_msg_Crypt";

goal thy 
 "!!evs. [| Says S A (Crypt {|Nonce NA, Agent B, Key K, X|} (serverKey A)) \
\               : setOfList evs;  \
\           evs : traces                             \
\        |] ==> (EX evs'. X = (Crypt {|Key(newK evs'), Agent A|} (serverKey B)))";


YYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYY;


WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW;

(*If a message is sent, encrypted with a Friend's server key, then either
  that Friend or the Server originally sent it.*)
goal thy 
 "!!evs. evs : traces ==>                             \
\    ALL A B X i. Says A B (Crypt X (serverKey (Friend i))) \
\        : setOfList evs  -->   \
\    (EX B'. Says Server B' (Crypt X (serverKey (Friend i))) : setOfList evs | \
\            Says (Friend i) B' (Crypt X (serverKey (Friend i))) : setOfList evs)";
be traces.induct 1;
be subst 4;	(*NS2: discard evsa = Says A Server...#evs'a as irrelevant!*)
by (Step_tac 1);
by (ALLGOALS Asm_full_simp_tac);
(*Remaining cases are Fake, NS2 and NS3*)
by (Fast_tac 2);	(*Proves the NS2 case*)

by (REPEAT (dtac spec 2));
fe conjE;
bd mp 2;

by (REPEAT (resolve_tac [refl, conjI] 2));
by (ALLGOALS Asm_full_simp_tac);




by (full_simp_tac (!simpset addsimps [all_conj_distrib]) 2);
be conjE 2;
by ((dtac spec THEN' dtac spec THEN' dtac spec THEN' dtac spec)2);

(*The NS3 case needs the induction hypothesis twice!
    One application is to the X component of the most recent message.*)
by (subgoal_tac "? evs'. X = Crypt {|Key (newK evs'), Agent A|} (serverKey B)" 2);
by (Fast_tac 3);
by (full_simp_tac (!simpset addsimps [all_conj_distrib]) 2);
be conjE 2;
(*DELETE the first quantified formula: it's now useless*)
by (eres_inst_tac [("V","ALL S.?P(S)")] thin_rl 2);
by (fast_tac (!claset addss (!simpset)) 2);
(*Now for the Fake case*)
be disjE 1;
(*The subcase of Fake, where the message in question is NOT the most recent*)
by (Best_tac 2);

by (REPEAT_FIRST (etac conjE ORELSE' hyp_subst_tac));
be Crypt_synthesize 1;
be Key_synthesize 2;

(*Split up the possibilities of that message being synthesized...*)
by (Step_tac 1);
by (Best_tac 6);





 (*The NS3 case needs the induction hypothesis twice!
    One application is to the X component of the most recent message.*)

????????????????????????????????????????????????????????????????
by (subgoal_tac "? evs'. X = Crypt {|Key (newK evs'), Agent A|} (serverKey B)" 1);
by (Fast_tac 2);

by (full_simp_tac (!simpset addsimps [all_conj_distrib]) 1);

be conjE 1;
(*DELETE the first quantified formula: it's now useless*)
by (eres_inst_tac [("V","ALL S.?P(S)")] thin_rl 1);
by (fast_tac (!claset addss (!simpset)) 1);


(*Now for the Fake case*)
be disjE 1;
(*The subcase of Fake, where the message in question is NOT the most recent*)
by (Best_tac 2);

WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW;


Addsimps [new_keys_not_seen];

(*Crucial security property: Enemy does not see the keys sent in msg NS2
   -- even if another friend's key is compromised*)
goal thy 
 "!!evs. [| Says Server (Friend i) \
\          (Crypt {|N, Agent B, K, X|} K') : setOfList evs;  \
\          evs : traces;  i~=j |] ==> \
\       \
\     K ~: analyze (insert (Key (serverKey (Friend j))) (sees Enemy evs))";
be rev_mp 1;
be traces.induct 1;
be subst 4;	(*NS2: discard evsa = Says A Server... as irrelevant!*)
by (ALLGOALS Asm_full_simp_tac);
(*The two simplifications cannot be combined -- they loop!*)
by (ALLGOALS (full_simp_tac (!simpset addsimps [insert_Key_delay])));
(*Next 3 steps infer that K has the form "Key (newK evs'" ... *)
br conjI 3;
by (REPEAT_FIRST (resolve_tac [impI]));
by (TRYALL (forward_tac [Says_Server_imp_Key_newK] THEN' assume_tac));
(*NS1, subgoal concerns "(Says A Server
                          {|Agent A, Agent B, Nonce (newN evsa)|}"*)
(*... thus it cannot equal any components of A's message above.*)
by (fast_tac (!claset addss (!simpset)) 2);
(*NS2, the subcase where that message was the most recently sent;
  it holds because here K' = serverKey(Friend i), which Enemies can't see,
  AND because nobody can know about a brand new key*)
by (fast_tac (!claset addss (!simpset addsimps [not_parts_not_analyze])) 2);
(*NS2, other subcase.  K is an old key, and thus not in the latest message.*)
by (fast_tac 
    (!claset addSEs [less_irrefl]
             addDs [impOfSubs analyze_insert_Crypt_subset]
	     addss (!simpset addsimps [not_parts_not_keysFor_analyze])) 2);
(*Now for the Fake case*)
be exE 1;
br notI 1;
by (REPEAT (etac conjE 1));
by (REPEAT (hyp_subst_tac 1));
by (subgoal_tac 
    "Key (newK evs') : \
\    analyze (synthesize (analyze (insert (Key (serverKey (Friend j))) \
\                                  (sees Enemy evsa))))" 1);
be (impOfSubs analyze_mono) 2;
by (best_tac (!claset addIs [analyze_mono RS synthesize_mono RSN 
			     (2,rev_subsetD),
			     impOfSubs synthesize_increasing,
			     impOfSubs analyze_increasing]) 2);
(*Proves the Fake goal*)
by (Auto_tac());
qed "Enemy_not_see_encrypted_key";


goal thy 
 "!!evs. [| Says Server (Friend i) \
\             (Crypt {|N, Agent B, K|} K') : setOfList evs;  \
\           evs : traces;  i~=j    \
\         |] ==> K ~: analyze (sees (Friend j) evs)";
br (sees_agent_subset_sees_Enemy RS analyze_mono RS contra_subsetD) 1;
by (ALLGOALS (asm_simp_tac (!simpset addsimps [Enemy_not_see_encrypted_key])));
qed "Friend_not_see_encrypted_key";

goal thy 
 "!!evs. [| Says Server (Friend i) \
\             (Crypt {|N, Agent B, K|} K') : setOfList evs;  \
\           A ~: {Friend i, Server};  \
\           evs : traces    \
\        |] ==>  K ~: analyze (sees A evs)";
by (eres_inst_tac [("P", "A~:?X")] rev_mp 1);
by (agent.induct_tac "A" 1);
by (ALLGOALS Simp_tac);
by (asm_simp_tac (!simpset addsimps [eq_sym_conv, 
				     Friend_not_see_encrypted_key]) 1);
br ([analyze_mono, Enemy_not_see_encrypted_key] MRS contra_subsetD) 1;
(*  hyp_subst_tac would deletes the equality assumption... *)
by (ALLGOALS (rtac n_not_Suc_n ORELSE' Fast_tac));
qed "Agent_not_see_encrypted_key";


(*Neatly packaged, perhaps in a useless form*)
goalw thy [knownBy_def]
 "!!evs. [| Says Server (Friend i) \
\             (Crypt {|N, Agent B, K|} K') : setOfList evs;  \
\           evs : traces    \
\        |] ==>  knownBy evs K <= {Friend i, Server}";

by (Step_tac 1);
br ccontr 1;
by (fast_tac (!claset addDs [Agent_not_see_encrypted_key]) 1);
qed "knownBy_encrypted_key";




XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX;





goal thy 
 "!!evs. evs : traces ==> \
\     Says Server A \
\          (Crypt {|Agent A, Agent B, K, N|} K') : setOfList evs  \
\     --> (EX evs'. N = Nonce (newN evs'))";
be traces.induct 1;
by (ALLGOALS Asm_simp_tac);
by (Fast_tac 1);
val Says_Server_lemma = result();


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

goal thy "!!evs. length evs < length evs' ==> newK  evs ~= newK (A',evs')";
by (fast_tac (!claset addSEs [less_irrefl]) 1);
qed "length_less_newK_neq";



goal thy "insert (Crypt x) (insert {|X,Y|} evs) = \
\         insert {|X,Y|} (insert (Crypt x) evs)";
by (Fast_tac 1);
qed "insert_Crypt_MPair_delay";



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


