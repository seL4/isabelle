(*  Title:      HOL/Auth/Shared
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Shared Keys (common to all symmetric-key protocols)

Server keys; initial states of agents; new nonces and keys; function "sees" 
*)


open Shared;

(*Holds because Friend is injective: thus cannot prove for all f*)
goal thy "(Friend x : Friend``A) = (x:A)";
by (Auto_tac());
qed "Friend_image_eq";
Addsimps [Friend_image_eq];

Addsimps [Un_insert_left, Un_insert_right];

(*By default only o_apply is built-in.  But in the presence of eta-expansion
  this means that some terms displayed as (f o g) will be rewritten, and others
  will not!*)
Addsimps [o_def];

(*** Basic properties of shrK and newK ***)

(*Injectiveness and freshness of new keys and nonces*)
AddIffs [inj_shrK RS inj_eq, inj_newN RS inj_eq, 
	 inj_newK RS inj_eq, inj_nPair RS inj_eq];

(* invKey (shrK A) = shrK A *)
bind_thm ("invKey_shrK", rewrite_rule [isSymKey_def] isSym_shrK);

(* invKey (newK i) = newK i *)
bind_thm ("invKey_newK", rewrite_rule [isSymKey_def] isSym_newK);
Addsimps [invKey_shrK, invKey_newK];

goal thy "!!K. newK i = invKey K ==> newK i = K";
by (rtac (invKey_eq RS iffD1) 1);
by (Simp_tac 1);
val newK_invKey = result();

AddSDs [newK_invKey, sym RS newK_invKey];

Addsimps [newK_neq_shrK, newK_neq_shrK RS not_sym];

(** Rewrites should not refer to  initState(Friend i) 
    -- not in normal form! **)

goal thy "Key (newK i) ~: parts (initState lost B)";
by (agent.induct_tac "B" 1);
by (Auto_tac ());
qed "newK_notin_initState";

goal thy "Nonce (newN i) ~: parts (initState lost B)";
by (agent.induct_tac "B" 1);
by (Auto_tac ());
qed "newN_notin_initState";

AddIffs [newK_notin_initState, newN_notin_initState];

goalw thy [keysFor_def] "keysFor (parts (initState lost C)) = {}";
by (agent.induct_tac "C" 1);
by (auto_tac (!claset addIs [range_eqI], !simpset));
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


(*** Function "sees" ***)

goal thy
    "!!evs. lost' <= lost ==> sees lost' A evs <= sees lost A evs";
by (list.induct_tac "evs" 1);
by (agent.induct_tac "A" 1);
by (event.induct_tac "a" 2);
by (Auto_tac ());
qed "sees_mono";

(*Agents see their own shared keys!*)
goal thy "A ~= Spy --> Key (shrK A) : sees lost A evs";
by (list.induct_tac "evs" 1);
by (agent.induct_tac "A" 1);
by (Auto_tac ());
qed_spec_mp "sees_own_shrK";

(*Spy sees shared keys of lost agents!*)
goal thy "!!A. A: lost ==> Key (shrK A) : sees lost Spy evs";
by (list.induct_tac "evs" 1);
by (Auto_tac());
qed "Spy_sees_lost";

AddSIs [sees_own_shrK, Spy_sees_lost];

(*Added for Yahalom/lost_tac*)
goal thy "!!A. [| Crypt (shrK A) X : analz (sees lost Spy evs);  A: lost |] \
\              ==> X : analz (sees lost Spy evs)";
by (fast_tac (!claset addSDs [analz.Decrypt] addss (!simpset)) 1);
qed "Crypt_Spy_analz_lost";

(** Specialized rewrite rules for (sees lost A (Says...#evs)) **)

goal thy "sees lost B (Says A B X # evs) = insert X (sees lost B evs)";
by (Simp_tac 1);
qed "sees_own";

goal thy "!!A. Server ~= B ==> \
\          sees lost Server (Says A B X # evs) = sees lost Server evs";
by (Asm_simp_tac 1);
qed "sees_Server";

goal thy "!!A. Friend i ~= B ==> \
\          sees lost (Friend i) (Says A B X # evs) = sees lost (Friend i) evs";
by (Asm_simp_tac 1);
qed "sees_Friend";

goal thy "sees lost Spy (Says A B X # evs) = insert X (sees lost Spy evs)";
by (Simp_tac 1);
qed "sees_Spy";

goal thy "sees lost A (Says A' B X # evs) <= insert X (sees lost A evs)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Fast_tac 1);
qed "sees_Says_subset_insert";

goal thy "sees lost A evs <= sees lost A (Says A' B X # evs)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Fast_tac 1);
qed "sees_subset_sees_Says";

(*Pushing Unions into parts.  One of the agents A is B, and thus sees Y.
  Once used to prove new_keys_not_seen; now obsolete.*)
goal thy "(UN A. parts (sees lost A (Says B C Y # evs))) = \
\         parts {Y} Un (UN A. parts (sees lost A evs))";
by (Step_tac 1);
by (etac rev_mp 1);     (*split_tac does not work on assumptions*)
by (ALLGOALS
    (fast_tac (!claset addss (!simpset addsimps [parts_Un, sees_Cons] 
                       setloop split_tac [expand_if]))));
qed "UN_parts_sees_Says";

goal thy "Says A B X : set_of_list evs --> X : sees lost Spy evs";
by (list.induct_tac "evs" 1);
by (Auto_tac ());
qed_spec_mp "Says_imp_sees_Spy";

goal thy  
 "!!evs. [| Says A B (Crypt (shrK C) X) : set_of_list evs;  C : lost |] \
\        ==> X : analz (sees lost Spy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]
                      addss (!simpset)) 1);
qed "Says_Crypt_lost";

goal thy  
 "!!evs. [| Says A B (Crypt (shrK C) X) : set_of_list evs;        \
\           X ~: analz (sees lost Spy evs) |]                     \
\        ==> C ~: lost";
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]
                      addss (!simpset)) 1);
qed "Says_Crypt_not_lost";

(*NEEDED??*)
goal thy "initState lost C <= Key `` range shrK";
by (agent.induct_tac "C" 1);
by (Auto_tac ());
qed "initState_subset";

(*NEEDED??*)
goal thy "X : sees lost C evs --> \
\          (EX A B. Says A B X : set_of_list evs) | (EX A. X = Key (shrK A))";
by (list.induct_tac "evs" 1);
by (ALLGOALS Asm_simp_tac);
by (fast_tac (!claset addDs [impOfSubs initState_subset]) 1);
by (rtac conjI 1);
by (Fast_tac 2);
by (event.induct_tac "a" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [mem_if])));
by (ALLGOALS Fast_tac);
qed_spec_mp "seesD";

Addsimps [sees_own, sees_Server, sees_Friend, sees_Spy];
Delsimps [sees_Cons];   (**** NOTE REMOVAL -- laws above are cleaner ****)


(** Power of the Spy **)

(*The Spy can see more than anybody else, except for their initial state*)
goal thy "sees lost A evs <= initState lost A Un sees lost Spy evs";
by (list.induct_tac "evs" 1);
by (event.induct_tac "a" 2);
by (ALLGOALS (fast_tac (!claset addDs [sees_Says_subset_insert RS subsetD] 
                                addss (!simpset))));
qed "sees_agent_subset_sees_Spy";

(*The Spy can see more than anybody else who's lost their key!*)
goal thy "A: lost --> A ~= Server --> sees lost A evs <= sees lost Spy evs";
by (list.induct_tac "evs" 1);
by (event.induct_tac "a" 2);
by (agent.induct_tac "A" 1);
by (auto_tac (!claset addDs [sees_Says_subset_insert RS subsetD], (!simpset)));
qed_spec_mp "sees_lost_agent_subset_sees_Spy";


(** Simplifying   parts (insert X (sees lost A evs))
      = parts {X} Un parts (sees lost A evs) -- since general case loops*)

val parts_insert_sees = 
    parts_insert |> read_instantiate_sg (sign_of thy)
                                        [("H", "sees lost A evs")]
                 |> standard;


(*** Specialized rewriting for analz_insert_Key_newK ***)

(*Push newK applications in, allowing other keys to be pulled out*)
val pushKey_newK = insComm thy "Key (newK ?evs)"  "Key (shrK ?C)";

Delsimps [image_insert];
Addsimps [image_insert RS sym];

Delsimps [image_Un];
Addsimps [image_Un RS sym];

goal thy "insert (Key (newK x)) H = Key `` (newK``{x}) Un H";
by (Fast_tac 1);
qed "insert_Key_singleton";

goal thy "insert (Key (f x)) (Key``(f``E) Un C) = \
\         Key `` (f `` (insert x E)) Un C";
by (Fast_tac 1);
qed "insert_Key_image";


(*Lemma for the trivial direction of the if-and-only-if*)
goal thy  
 "!!evs. (Key K : analz (Key``nE Un H)) --> (K : nE | Key K : analz H)  ==> \
\        (Key K : analz (Key``nE Un H)) = (K : nE | Key K : analz H)";
by (fast_tac (!claset addSEs [impOfSubs analz_mono]) 1);
qed "analz_image_newK_lemma";
