(*  Title:      HOL/Auth/Message
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Shared Keys (common to all symmetric-key protocols)

Server keys; initial states of agents; new nonces and keys; function "sees" 


*)

Addsimps [parts_cut_eq];

proof_timing:=true;

(*IN SET.ML*)
goal Set.thy "(a : (if Q then x else y)) = ((Q --> a:x) & (~Q --> a : y))";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
qed "mem_if";

(*FUN.ML??  WE NEED A NOTION OF INVERSE IMAGE, OR GRAPH!!*)
goal Set.thy "!!f. B <= range f = (B = f`` {x. f x: B})";
by (fast_tac (!claset addEs [equalityE]) 1);
val subset_range_iff = result();


open Shared;

Addsimps [Un_insert_left, Un_insert_right];

(*By default only o_apply is built-in.  But in the presence of eta-expansion
  this means that some terms displayed as (f o g) will be rewritten, and others
  will not!*)
Addsimps [o_def];

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

(** Rewrites should not refer to  initState(Friend i) 
    -- not in normal form! **)

goal thy "newK evs ~= serverKey B";
by (subgoal_tac "newK evs = serverKey B --> \
\                Key (newK evs) : parts (initState B)" 1);
by (Fast_tac 1);
by (agent.induct_tac "B" 1);
by (auto_tac (!claset addIs [range_eqI], !simpset));
qed "newK_neq_serverKey";

Addsimps [newK_neq_serverKey, newK_neq_serverKey RS not_sym];

(*Good for talking about Server's initial state*)
goal thy "!!H. H <= Key``E ==> parts H = H";
by (Auto_tac ());
be parts.induct 1;
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "parts_image_subset";

bind_thm ("parts_image_Key", subset_refl RS parts_image_subset);

goal thy "!!H. H <= Key``E ==> analz H = H";
by (Auto_tac ());
be analz.induct 1;
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

goal thy "serverKey A ~: newK``E";
by (agent.induct_tac "A" 1);
by (Auto_tac ());
qed "serverKey_notin_image_newK";
Addsimps [serverKey_notin_image_newK];


(*Agents see their own serverKeys!*)
goal thy "Key (serverKey A) : analz (sees A evs)";
by (list.induct_tac "evs" 1);
by (asm_simp_tac (!simpset addsimps [impOfSubs(Un_upper2 RS analz_mono)]) 2);
by (agent.induct_tac "A" 1);
by (auto_tac (!claset addIs [range_eqI], !simpset));
qed "analz_own_serverKey";

bind_thm ("parts_own_serverKey",
	  [analz_subset_parts, analz_own_serverKey] MRS subsetD);

Addsimps [analz_own_serverKey, parts_own_serverKey];



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

goal thy "Says A B X : set_of_list evs --> X : sees Enemy evs";
by (list.induct_tac "evs" 1);
by (Auto_tac ());
qed_spec_mp "Says_imp_sees_Enemy";

Addsimps [Says_imp_sees_Enemy];
AddIs    [Says_imp_sees_Enemy];

goal thy "initState C <= Key `` range serverKey";
by (agent.induct_tac "C" 1);
by (Auto_tac ());
qed "initState_subset";

goal thy "X : sees C evs --> \
\          (EX A B. Says A B X : set_of_list evs) | \
\          (EX A. Notes A X : set_of_list evs) | \
\          (EX A. X = Key (serverKey A))";
by (list.induct_tac "evs" 1);
by (ALLGOALS Asm_simp_tac);
by (fast_tac (!claset addDs [impOfSubs initState_subset]) 1);
br conjI 1;
by (Fast_tac 2);
by (event.induct_tac "a" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [mem_if])));
by (ALLGOALS Fast_tac);
qed_spec_mp "seesD";


Addsimps [UN_parts_sees_Says, sees_own, sees_Server, sees_Friend, sees_Enemy];
Delsimps [sees_Cons];	(**** NOTE REMOVAL -- laws above are cleaner ****)


goal thy "!!K. newK evs = invKey K ==> newK evs = K";
br (invKey_eq RS iffD1) 1;
by (Simp_tac 1);
val newK_invKey = result();


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

val pushKey_newK = insComm "Key (newK ?evs)"  "Key (serverKey ?C)";


