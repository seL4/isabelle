(*  Title:      HOL/Auth/Message
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Datatype of events;
inductive relation "traces" for Needham-Schroeder (shared keys)

Rewrites should not refer to     initState (Friend i)    -- not in normal form
*)

Addsimps [parts_cut_eq];


(*INSTALLED ON NAT.ML*)
goalw Nat.thy [le_def] "(m <= n) = (m < Suc n)";
by (rtac not_less_eq 1);
qed "le_eq_less_Suc";

proof_timing:=true;

(*FOR LIST.ML??*)
goal List.thy "x : set_of_list (x#xs)";
by (Simp_tac 1);
qed "set_of_list_I1";

goal List.thy "!!x. xs = x#xs' ==> x : set_of_list xs";
by (Asm_simp_tac 1);
qed "set_of_list_eqI1";

(*FUN.ML??  WE NEED A NOTION OF INVERSE IMAGE, OR GRAPH!!*)
goal Set.thy "!!f. B <= range f = (B = f`` {x. f x: B})";
by (fast_tac (!claset addEs [equalityE]) 1);
val subset_range_iff = result();


open Event;

Addsimps [Un_insert_left, Un_insert_right];

(*By default only o_apply is built-in.  But in the presence of eta-expansion
  this means that some terms displayed as (f o g) will be rewritten, and others
  will not!*)
Addsimps [o_def];

(*** Basic properties of shrK and newK ***)

(* invKey (shrK A) = shrK A *)
bind_thm ("invKey_shrK", rewrite_rule [isSymKey_def] isSym_shrK);

(* invKey (newK evs) = newK evs *)
bind_thm ("invKey_newK", rewrite_rule [isSymKey_def] isSym_newK);
Addsimps [invKey_shrK, invKey_newK];


(*New keys and nonces are fresh*)
val shrK_inject = inj_shrK RS injD;
val newN_inject = inj_newN RS injD
and newK_inject = inj_newK RS injD;
AddSEs [shrK_inject, newN_inject, newK_inject,
        fresh_newK RS notE, fresh_newN RS notE];
Addsimps [inj_shrK RS inj_eq, inj_newN RS inj_eq, inj_newK RS inj_eq];
Addsimps [fresh_newN, fresh_newK];

goal thy "newK evs ~= shrK B";
by (subgoal_tac "newK evs = shrK B --> \
\                Key (newK evs) : parts (initState B)" 1);
by (Fast_tac 1);
by (agent.induct_tac "B" 1);
by (auto_tac (!claset addIs [range_eqI], !simpset));
qed "newK_neq_shrK";

Addsimps [newK_neq_shrK, newK_neq_shrK RS not_sym];

(*Good for talking about Server's initial state*)
goal thy "!!H. H <= Key``E ==> parts H = H";
by (Auto_tac ());
by (etac parts.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "parts_image_subset";

bind_thm ("parts_image_Key", subset_refl RS parts_image_subset);

goal thy "!!H. H <= Key``E ==> analz H = H";
by (Auto_tac ());
by (etac analz.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "analz_image_subset";

bind_thm ("analz_image_Key", subset_refl RS analz_image_subset);

Addsimps [parts_image_Key, analz_image_Key];

goalw thy [keysFor_def] "keysFor (parts (initState C)) = {}";
by (agent.induct_tac "C" 1);
by (auto_tac (!claset addIs [range_eqI] delrules partsEs, !simpset));
qed "keysFor_parts_initState";
Addsimps [keysFor_parts_initState];

goalw thy [keysFor_def] "keysFor (Key``E) = {}";
by (Auto_tac ());
qed "keysFor_image_Key";
Addsimps [keysFor_image_Key];

goal thy "shrK A ~: newK``E";
by (agent.induct_tac "A" 1);
by (Auto_tac ());
qed "shrK_notin_image_newK";
Addsimps [shrK_notin_image_newK];


(*Agents see their own shrKs!*)
goal thy "Key (shrK A) : analz (sees A evs)";
by (list.induct_tac "evs" 1);
by (asm_simp_tac (!simpset addsimps [impOfSubs(Un_upper2 RS analz_mono)]) 2);
by (agent.induct_tac "A" 1);
by (auto_tac (!claset addIs [range_eqI], !simpset));
qed "analz_own_shrK";

bind_thm ("parts_own_shrK",
          [analz_subset_parts, analz_own_shrK] MRS subsetD);

Addsimps [analz_own_shrK, parts_own_shrK];



(**** Inductive relation "traces" -- basic properties ****)

val mk_cases = traces.mk_cases (list.simps @ agent.simps @ event.simps);

val Says_tracesE        = mk_cases "Says A B X # evs: traces";
val Says_Server_tracesE = mk_cases "Says Server B X # evs: traces";
val Says_Spy_tracesE  = mk_cases "Says Spy B X # evs: traces";
val Says_to_Server_tracesE = mk_cases "Says A Server X # evs: traces";
val Notes_tracesE       = mk_cases "Notes A X # evs: traces";

(*The tail of a trace is a trace*)
goal thy "!!ev evs. ev#evs : traces ==> evs : traces";
by (fast_tac (!claset addEs [mk_cases "ev#evs:traces"]) 1);
qed "traces_ConsE";

goal thy "!!ev evs. [| evs = ev#evs'; evs : traces |] ==> evs' : traces";
by (fast_tac (!claset addEs [mk_cases "ev#evs:traces"]) 1);
qed "traces_eq_ConsE";


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

goal thy "sees Spy (Says A B X # evs) = insert X (sees Spy evs)";
by (Simp_tac 1);
qed "sees_Spy";

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
by (etac rev_mp 1);     (*for some reason, split_tac does not work on assumptions*)
val ss = (!simpset addsimps [parts_Un, sees_Cons] 
                   setloop split_tac [expand_if]);
by (ALLGOALS (fast_tac (!claset addss ss)));
qed "UN_parts_sees_Says";

goal thy "Says A B X : set_of_list evs --> X : sees Spy evs";
by (list.induct_tac "evs" 1);
by (Auto_tac ());
qed_spec_mp "Says_imp_sees_Spy";

Addsimps [Says_imp_sees_Spy];
AddIs    [Says_imp_sees_Spy];

goal thy "initState C <= Key `` range shrK";
by (agent.induct_tac "C" 1);
by (Auto_tac ());
qed "initState_subset";

goal thy "X : sees C evs --> \
\          (EX A B. Says A B X : set_of_list evs) | \
\          (EX A. Notes A X : set_of_list evs) | \
\          (EX A. X = Key (shrK A))";
by (list.induct_tac "evs" 1);
by (ALLGOALS Asm_simp_tac);
by (fast_tac (!claset addDs [impOfSubs initState_subset]) 1);
by (rtac conjI 1);
by (Fast_tac 2);
by (event.induct_tac "a" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [mem_if])));
by (ALLGOALS Fast_tac);
qed_spec_mp "seesD";


Addsimps [UN_parts_sees_Says, sees_own, sees_Server, sees_Friend, sees_Spy];
Delsimps [sees_Cons];   (**** NOTE REMOVAL -- laws above are cleaner ****)


(**** Inductive proofs about traces ****)

(*The Spy can see more than anybody else, except for their initial state*)
goal thy 
 "!!evs. evs : traces ==> \
\     sees A evs <= initState A Un sees Spy evs";
by (etac traces.induct 1);
by (ALLGOALS (fast_tac (!claset addDs [sees_Says_subset_insert RS subsetD] 
                                addss (!simpset))));
qed "sees_agent_subset_sees_Spy";


(*Nobody sends themselves messages*)
goal thy "!!evs. evs : traces ==> ALL A X. Says A A X ~: set_of_list evs";
by (etac traces.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];

goal thy "!!evs. evs : traces ==> Notes A X ~: set_of_list evs";
by (etac traces.induct 1);
by (Auto_tac());
qed "not_Notes";
Addsimps [not_Notes];
AddSEs   [not_Notes RSN (2, rev_notE)];


goal thy "!!evs. (Says S A (Crypt {|N, B, K, X|} KA)) : set_of_list evs ==> \
\                X : parts (sees Spy evs)";
by (fast_tac (!claset addSEs partsEs
                      addSDs [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "NS3_msg_in_parts_sees_Spy";
                              

(*** Server keys are not betrayed ***)

(*Spy never sees another agent's server key!*)
goal thy 
 "!!evs. [| evs : traces; A ~= Spy |] ==> \
\        Key (shrK A) ~: parts (sees Spy evs)";
by (etac traces.induct 1);
by (dtac NS3_msg_in_parts_sees_Spy 5);
by (Auto_tac());
(*Deals with Fake message*)
by (best_tac (!claset addDs [impOfSubs analz_subset_parts,
                             impOfSubs synth_analz_parts_insert_subset_Un]) 1);
qed "Spy_not_see_shrK";

bind_thm ("Spy_not_analz_shrK",
          [analz_subset_parts, Spy_not_see_shrK] MRS contra_subsetD);

Addsimps [Spy_not_see_shrK, 
          not_sym RSN (2, Spy_not_see_shrK), 
          Spy_not_analz_shrK, 
          not_sym RSN (2, Spy_not_analz_shrK)];

(*We go to some trouble to preserve R in the 3rd subgoal*)
val major::prems = 
goal thy  "[| Key (shrK A) : parts (sees Spy evs);    \
\             evs : traces;                                  \
\             A=Spy ==> R                                  \
\           |] ==> R";
by (rtac ccontr 1);
by (rtac ([major, Spy_not_see_shrK] MRS rev_notE) 1);
by (swap_res_tac prems 2);
by (ALLGOALS (fast_tac (!claset addIs prems)));
qed "Spy_see_shrK_E";

bind_thm ("Spy_analz_shrK_E", 
          analz_subset_parts RS subsetD RS Spy_see_shrK_E);

(*Classical reasoner doesn't need the not_sym versions (with swapped ~=) *)
AddSEs [Spy_see_shrK_E, Spy_analz_shrK_E];


(*No Friend will ever see another agent's server key 
  (excluding the Spy, who might transmit his).
  The Server, of course, knows all server keys.*)
goal thy 
 "!!evs. [| evs : traces; A ~= Spy;  A ~= Friend j |] ==> \
\        Key (shrK A) ~: parts (sees (Friend j) evs)";
by (rtac (sees_agent_subset_sees_Spy RS parts_mono RS contra_subsetD) 1);
by (ALLGOALS Asm_simp_tac);
qed "Friend_not_see_shrK";


(*Not for Addsimps -- it can cause goals to blow up!*)
goal thy  
 "!!evs. evs : traces ==>                                  \
\        (Key (shrK A) \
\           : analz (insert (Key (shrK B)) (sees Spy evs))) =  \
\        (A=B | A=Spy)";
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
goal thy "!!evs. evs : traces ==> \
\                length evs <= length evs' --> \
\                          Key (newK evs') ~: (UN C. parts (sees C evs))";
by (etac traces.induct 1);
by (dtac NS3_msg_in_parts_sees_Spy 5);
(*auto_tac does not work here, as it performs safe_tac first*)
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (best_tac (!claset addDs [impOfSubs analz_subset_parts,
                                       impOfSubs parts_insert_subset_Un,
                                       Suc_leD]
                                addss (!simpset))));
val lemma = result();

(*Variant needed for the main theorem below*)
goal thy 
 "!!evs. [| evs : traces;  length evs <= length evs' |] ==> \
\        Key (newK evs') ~: parts (sees C evs)";
by (fast_tac (!claset addDs [lemma]) 1);
qed "new_keys_not_seen";
Addsimps [new_keys_not_seen];

(*Another variant: old messages must contain old keys!*)
goal thy 
 "!!evs. [| Says A B X : set_of_list evs;  \
\           Key (newK evt) : parts {X};    \
\           evs : traces                 \
\        |] ==> length evt < length evs";
by (rtac ccontr 1);
by (fast_tac (!claset addSDs [new_keys_not_seen, Says_imp_sees_Spy]
                      addIs [impOfSubs parts_mono, leI]) 1);
qed "Says_imp_old_keys";


goal thy "!!K. newK evs = invKey K ==> newK evs = K";
by (rtac (invKey_eq RS iffD1) 1);
by (Simp_tac 1);
val newK_invKey = result();


val keysFor_parts_mono = parts_mono RS keysFor_mono;

(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : traces ==> \
\                length evs <= length evs' --> \
\                newK evs' ~: keysFor (UN C. parts (sees C evs))";
by (etac traces.induct 1);
by (dtac NS3_msg_in_parts_sees_Spy 5);
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
 "!!evs. [| evs : traces;  length evs <= length evs' |] ==> \
\        newK evs' ~: keysFor (parts (sees C evs))";
by (fast_tac (!claset addSDs [lemma] addss (!simpset)) 1);
qed "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];


(** Rewrites to push in Key and Crypt messages, so that other messages can
    be pulled out using the analz_insert rules **)

fun insComm x y = read_instantiate_sg (sign_of thy) [("x",x), ("y",y)] 
                      insert_commute;

val pushKeys = map (insComm "Key ?K") 
                  ["Agent ?C", "Nonce ?N", "MPair ?X ?Y", "Crypt ?X ?K'"];

val pushCrypts = map (insComm "Crypt ?X ?K") 
                    ["Agent ?C", "Nonce ?N", "MPair ?X' ?Y"];

(*Cannot be added with Addsimps -- we don't always want to re-order messages*)
val pushes = pushKeys@pushCrypts;

val pushKey_newK = insComm "Key (newK ?evs)"  "Key (shrK ?C)";


(** Lemmas concerning the form of items passed in messages **)

(*Describes the form *and age* of K, and the form of X,
  when the following message is sent*)
goal thy 
 "!!evs. [| Says Server A (Crypt {|N, Agent B, K, X|} K') : set_of_list evs; \
\           evs : traces    \
\        |] ==> (EX evt:traces. \
\                         K = Key(newK evt) & \
\                         X = (Crypt {|K, Agent A|} (shrK B)) & \
\                         K' = shrK A & \
\                         length evt < length evs)";
by (etac rev_mp 1);
by (etac traces.induct 1);
by (ALLGOALS (fast_tac (!claset addIs [less_SucI] addss (!simpset))));
qed "Says_Server_message_form";

(* c ~: keysFor (parts H) ==> c ~: keysFor (analz H) *)
bind_thm ("not_parts_not_keysFor_analz", 
          analz_subset_parts RS keysFor_mono RS contra_subsetD);



(*USELESS for NS3, case 1, as the ind hyp says the same thing!
goal thy 
 "!!evs. [| evs = Says Server (Friend i) \
\                 (Crypt {|N, Agent(Friend j), K, X|} K') # evs';  \
\           evs : traces;  i~=k                                    \
\        |] ==>                                                    \
\     K ~: analz (insert (Key (shrK (Friend k))) (sees Spy evs))";
by (etac rev_mp 1);
by (etac traces.induct 1);
by (ALLGOALS (asm_full_simp_tac (!simpset addsimps pushes)));
by (Step_tac 1);
by (asm_full_simp_tac (!simpset addsimps[analz_subset_parts RS contra_subsetD]) 1);
val Spy_not_see_encrypted_key_lemma = result();
*)


(*Describes the form of X when the following message is sent*)
goal thy
 "!!evs. evs : traces ==>                             \
\        ALL A NA B K X.                            \
\            (Crypt {|Nonce NA, Agent B, Key K, X|} (shrK A)) \
\            : parts (sees Spy evs) & A ~= Spy  -->   \
\          (EX evt:traces. K = newK evt & \
\                          X = (Crypt {|Key K, Agent A|} (shrK B)))";
by (etac traces.induct 1);
by (dtac NS3_msg_in_parts_sees_Spy 5);
by (Step_tac 1);
by (ALLGOALS Asm_full_simp_tac);
(*Remaining cases are Fake and NS2*)
by (fast_tac (!claset addSDs [spec]) 2);
(*Now for the Fake case*)
by (best_tac (!claset addDs [impOfSubs analz_subset_parts,
                             impOfSubs synth_analz_parts_insert_subset_Un]
                      addss (!simpset)) 1);
qed_spec_mp "encrypted_form";


(*For eliminating the A ~= Spy condition from the previous result*)
goal thy 
 "!!evs. evs : traces ==>                             \
\        ALL S A NA B K X.                            \
\            Says S A (Crypt {|Nonce NA, Agent B, Key K, X|} (shrK A)) \
\            : set_of_list evs  -->   \
\        S = Server | S = Spy";
by (etac traces.induct 1);
by (ALLGOALS Asm_simp_tac);
(*We are left with NS3*)
by (subgoal_tac "S = Server | S = Spy" 1);
(*First justify this assumption!*)
by (fast_tac (!claset addSEs [allE, mp] addss (!simpset)) 2);
by (Step_tac 1);
by (dtac Says_Server_message_form 1);
by (ALLGOALS Full_simp_tac);
(*Final case.  Clear out needless quantifiers to speed the following step*)
by (eres_inst_tac [("V","ALL x. ?P(x)")] thin_rl 1);
by (dtac encrypted_form 1);
by (rtac (parts.Inj RS conjI) 1);
auto();
qed_spec_mp "Server_or_Spy";


(*Describes the form of X when the following message is sent;
  use Says_Server_message_form if applicable*)
goal thy 
 "!!evs. [| Says S A (Crypt {|Nonce NA, Agent B, Key K, X|} (shrK A)) \
\            : set_of_list evs;                              \
\           evs : traces               \
\        |] ==> (EX evt:traces. K = newK evt & length evt < length evs & \
\                               X = (Crypt {|Key K, Agent A|} (shrK B)))";
by (forward_tac [Server_or_Spy] 1);
by (assume_tac 1);
by (Step_tac 1);
by (fast_tac (!claset addSDs [Says_Server_message_form] addss (!simpset)) 1);
by (forward_tac [encrypted_form] 1);
by (rtac (parts.Inj RS conjI) 1);
by (auto_tac (!claset addIs [Says_imp_old_keys], !simpset));
qed "Says_S_message_form";

(*Currently unused.  Needed only to reason about the VERY LAST message.*)
goal thy 
 "!!evs. [| evs = Says S A (Crypt {|Nonce NA, Agent B, Key K, X|}   \
\                           (shrK A)) # evs';                  \
\           evs : traces                                           \
\        |] ==> (EX evt:traces. evs' : traces & length evt < length evs & \
\                               K = newK evt & \
\                               X = (Crypt {|Key K, Agent A|} (shrK B)))";
by (forward_tac [traces_eq_ConsE] 1);
by (dtac (set_of_list_eqI1 RS Says_S_message_form) 2);
by (Auto_tac());        
qed "Says_S_message_form_eq";



(****
 The following is to prove theorems of the form

          Key K : analz (insert (Key (newK evt)) 
                           (insert (Key (shrK C)) (sees Spy evs))) ==>
          Key K : analz (insert (Key (shrK C)) (sees Spy evs))

 A more general formula must be proved inductively.

****)


(*NOT useful in this form, but it says that session keys are not used
  to encrypt messages containing other keys, in the actual protocol.
  We require that agents should behave like this subsequently also.*)
goal thy 
 "!!evs. evs : traces ==> \
\        (Crypt X (newK evt)) : parts (sees Spy evs) & \
\        Key K : parts {X} --> Key K : parts (sees Spy evs)";
by (etac traces.induct 1);
by (dtac NS3_msg_in_parts_sees_Spy 5);
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
 "!!evs. evs : traces ==> \
\  ALL K E. (Key K : analz (insert (Key (shrK C)) \
\                             (Key``(newK``E) Un (sees Spy evs)))) = \
\           (K : newK``E |  \
\            Key K : analz (insert (Key (shrK C)) \
\                             (sees Spy evs)))";
by (etac traces.induct 1);
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
\              (analz (insert (Key (shrK C)) \
\                        (Key``(newK``E) Un (sees Spy evsa)))))" 1);
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
 "!!evs. evs : traces ==>                                  \
\        Key K : analz (insert (Key (newK evt))            \
\                         (insert (Key (shrK C))      \
\                          (sees Spy evs))) =            \
\             (K = newK evt |                              \
\              Key K : analz (insert (Key (shrK C))   \
\                               (sees Spy evs)))";
by (asm_simp_tac (HOL_ss addsimps [pushKey_newK, analz_image_newK, 
                                   insert_Key_singleton]) 1);
by (Fast_tac 1);
qed "analz_insert_Key_newK";



(*This says that the Key, K, uniquely identifies the message.
    But if C=Spy then he could send all sorts of nonsense.*)
goal thy 
 "!!evs. evs : traces ==>                      \
\      EX X'. ALL C S A Y N B X.               \
\         C ~= Spy -->                       \
\         Says S A Y : set_of_list evs -->     \
\         ((Crypt {|N, Agent B, Key K, X|} (shrK C)) : parts{Y} --> \
\       (X = X'))";
by (etac traces.induct 1);
by (forward_tac [Says_S_message_form] 5 THEN assume_tac 5);     
by (ALLGOALS 
    (asm_simp_tac (!simpset addsimps [all_conj_distrib, imp_conjR])));
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
by (rtac exI 1);
by (rtac conjI 1);
by (assume_tac 2);
by (Step_tac 1);
(** LEVEL 12 **)
by (subgoal_tac "Crypt {|N, Agent Ba, Key K, Xa|} (shrK C) \
\                  : parts (sees Spy evsa)" 1);
by (eres_inst_tac [("V","ALL S.?P(S)")] thin_rl 2);
by (best_tac (!claset addSEs [impOfSubs analz_subset_parts]
                      addDs [impOfSubs parts_insert_subset_Un]
                      addss (!simpset)) 2);
by (eres_inst_tac [("V","?aa : parts {X}")] thin_rl 1);
by (dtac parts_singleton 1);
by (Step_tac 1);
by (dtac seesD 1);
by (Step_tac 1);
by (Full_simp_tac 2);
by (fast_tac (!claset addSDs [spec]) 1);
val lemma = result();


(*In messages of this form, the session key uniquely identifies the rest*)
goal thy 
 "!!evs. [| Says S A          \
\             (Crypt {|N, Agent B, Key K, X|} (shrK C))     \
\                  : set_of_list evs; \
 \          Says S' A'                                         \
\             (Crypt {|N', Agent B', Key K, X'|} (shrK C')) \
\                  : set_of_list evs;                         \
\           evs : traces;  C ~= Spy;  C' ~= Spy    |] ==> X = X'";
by (dtac lemma 1);
by (etac exE 1);
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
by (Fast_tac 1);
qed "unique_session_keys";



(*Crucial security property: Spy does not see the keys sent in msg NS2
   -- even if another key is compromised*)
goal thy 
 "!!evs. [| Says Server (Friend i) \
\            (Crypt {|N, Agent(Friend j), K, X|} K') : set_of_list evs;  \
\           evs : traces;  Friend i ~= C;  Friend j ~= C              \
\        |] ==>                                                       \
\     K ~: analz (insert (Key (shrK C)) (sees Spy evs))";
by (etac rev_mp 1);
by (etac traces.induct 1);
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
by (rtac notI 1);
by (subgoal_tac 
    "Key (newK evt) : \
\    analz (synth (analz (insert (Key (shrK C)) \
\                                  (sees Spy evsa))))" 1);
by (etac (impOfSubs analz_mono) 2);
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
by (dtac unique_session_keys 1);
by (REPEAT_FIRST assume_tac);
by (ALLGOALS Full_simp_tac);
by (Step_tac 1);
by (asm_full_simp_tac (!simpset addsimps [shrK_mem_analz]) 1);
qed "Spy_not_see_encrypted_key";




XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX;


goals_limit:=4;



goal thy 
 "!!evs. [| Says Server (Friend i) \
\             (Crypt {|N, Agent B, K|} K') : set_of_list evs;  \
\           evs : traces;  i~=j    \
\         |] ==> K ~: analz (sees (Friend j) evs)";
by (rtac (sees_agent_subset_sees_Spy RS analz_mono RS contra_subsetD) 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [Spy_not_see_encrypted_key])));
qed "Friend_not_see_encrypted_key";

goal thy 
 "!!evs. [| Says Server (Friend i) \
\             (Crypt {|N, Agent B, K|} K') : set_of_list evs;  \
\           A ~: {Friend i, Server};  \
\           evs : traces    \
\        |] ==>  K ~: analz (sees A evs)";
by (eres_inst_tac [("P", "A~:?X")] rev_mp 1);
by (agent.induct_tac "A" 1);
by (ALLGOALS Simp_tac);
by (asm_simp_tac (!simpset addsimps [eq_sym_conv, 
                                     Friend_not_see_encrypted_key]) 1);
by (rtac ([analz_mono, Spy_not_see_encrypted_key] MRS contra_subsetD) 1);
(*  hyp_subst_tac would deletes the equality assumption... *)
by (ALLGOALS (rtac n_not_Suc_n ORELSE' Fast_tac));
qed "Agent_not_see_encrypted_key";


(*Neatly packaged, perhaps in a useless form*)
goalw thy [knownBy_def]
 "!!evs. [| Says Server (Friend i) \
\             (Crypt {|N, Agent B, K|} K') : set_of_list evs;  \
\           evs : traces    \
\        |] ==>  knownBy evs K <= {Friend i, Server}";

by (Step_tac 1);
by (rtac ccontr 1);
by (fast_tac (!claset addDs [Agent_not_see_encrypted_key]) 1);
qed "knownBy_encrypted_key";







push_proof();
goal thy 
 "!!evs. [| evs = Says S (Friend i) \
\                 (Crypt {|N, Agent(Friend j), K, X|} K') # evs';  \
\           evs : traces;  i~=k                                    \
\        |] ==>                                                    \
\     K ~: analz (insert (Key (shrK (Friend k))) (sees Spy evs))";
by (etac rev_mp 1);
by (etac traces.induct 1);
by (ALLGOALS (asm_full_simp_tac (!simpset addsimps pushes)));
by (Step_tac 1);
by (asm_full_simp_tac (!simpset addsimps[analz_subset_parts RS contra_subsetD]) 1);
val Spy_not_see_encrypted_key_lemma = result();







(*Precisely formulated as needed below.  Perhaps redundant, as simplification
  with the aid of  analz_subset_parts RS contra_subsetD  might do the
  same thing.*)
goal thy 
 "!!evs. [| evs : traces; A ~= Spy;  A ~= Friend j |] ==> \
\        Key (shrK A) ~:                               \
\          analz (insert (Key (shrK (Friend j))) (sees Spy evs))";
by (rtac (analz_subset_parts RS contra_subsetD) 1);
by (Asm_simp_tac 1);
qed "insert_not_analz_shrK";




XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX;
proof_timing:=true;



YYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYY;



(*If a message is sent, encrypted with a Friend's server key, then either
  that Friend or the Server originally sent it.*)
goal thy 
 "!!evs. evs : traces ==>                             \
\    ALL A B X i. Says A B (Crypt X (shrK (Friend i))) \
\        : set_of_list evs  -->   \
\    (EX B'. Says Server B' (Crypt X (shrK (Friend i))) : set_of_list evs | \
\            Says (Friend i) B' (Crypt X (shrK (Friend i))) : set_of_list evs)";
by (etac traces.induct 1);
by (Step_tac 1);
by (ALLGOALS Asm_full_simp_tac);
(*Remaining cases are Fake, NS2 and NS3*)
by (Fast_tac 2);        (*Proves the NS2 case*)

by (REPEAT (dtac spec 2));
fe conjE;
by (dtac mp 2);

by (REPEAT (resolve_tac [refl, conjI] 2));
by (ALLGOALS Asm_full_simp_tac);




by (full_simp_tac (!simpset addsimps [all_conj_distrib]) 2);
by (etac conjE 2);
by ((dtac spec THEN' dtac spec THEN' dtac spec THEN' dtac spec)2);

(*The NS3 case needs the induction hypothesis twice!
    One application is to the X component of the most recent message.*)
by (subgoal_tac "? evs'. X = Crypt {|Key (newK evs'), Agent A|} (shrK B)" 2);
by (Fast_tac 3);
by (full_simp_tac (!simpset addsimps [all_conj_distrib]) 2);
by (etac conjE 2);
(*DELETE the first quantified formula: it's now useless*)
by (eres_inst_tac [("V","ALL S.?P(S)")] thin_rl 2);
by (fast_tac (!claset addss (!simpset)) 2);
(*Now for the Fake case*)
by (etac disjE 1);
(*The subcase of Fake, where the message in question is NOT the most recent*)
by (Best_tac 2);

by (REPEAT_FIRST (etac conjE ORELSE' hyp_subst_tac));
by (etac Crypt_synth 1);
by (etac Key_synth 2);

(*Split up the possibilities of that message being synthd...*)
by (Step_tac 1);
by (Best_tac 6);





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


