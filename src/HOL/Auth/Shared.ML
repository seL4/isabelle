(*  Title:      HOL/Auth/Message
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Shared Keys (common to all symmetric-key protocols)

Server keys; initial states of agents; new nonces and keys; function "sees" 
*)



(*GOALS.ML??*)
fun prlim n = (goals_limit:=n; pr());

(*FUN.ML??  WE NEED A NOTION OF INVERSE IMAGE, OR GRAPH!!*)
goal Set.thy "!!f. B <= range f = (B = f`` {x. f x: B})";
by (fast_tac (!claset addEs [equalityE]) 1);
val subset_range_iff = result();


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

(* invKey (shrK A) = shrK A *)
bind_thm ("invKey_shrK", rewrite_rule [isSymKey_def] isSym_shrK);

(* invKey (newK evs) = newK evs *)
bind_thm ("invKey_newK", rewrite_rule [isSymKey_def] isSym_newK);
Addsimps [invKey_shrK, invKey_newK];


(*Injectiveness and freshness of new keys and nonces*)
AddIffs [inj_shrK RS inj_eq, inj_newN RS inj_eq, inj_newK RS inj_eq];

(** Rewrites should not refer to  initState(Friend i) 
    -- not in normal form! **)

Addsimps [newK_neq_shrK, newK_neq_shrK RS not_sym];

goal thy "Key (newK evs) ~: parts (initState lost B)";
by (agent.induct_tac "B" 1);
by (Auto_tac ());
qed "newK_notin_initState";

goal thy "Nonce (newN evs) ~: parts (initState lost B)";
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


(** Specialized rewrite rules for (sees lost A (Says...#evs)) **)

goal thy "sees lost A (Says A B X # evs) = insert X (sees lost A evs)";
by (Simp_tac 1);
qed "sees_own";

goal thy "!!A. Server ~= A ==> \
\              sees lost Server (Says A B X # evs) = sees lost Server evs";
by (Asm_simp_tac 1);
qed "sees_Server";

goal thy "!!A. Friend i ~= A ==> \
\              sees lost (Friend i) (Says A B X # evs) = sees lost (Friend i) evs";
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

(*Pushing Unions into parts; one of the A's equals B, and thus sees lost Y*)
goal thy "(UN A. parts (sees lost A (Says B C Y # evs))) = \
\         parts {Y} Un (UN A. parts (sees lost A evs))";
by (Step_tac 1);
by (etac rev_mp 1);     (*for some reason, split_tac does not work on assumptions*)
val ss = (!simpset addsimps [parts_Un, sees_Cons] 
                   setloop split_tac [expand_if]);
by (ALLGOALS (fast_tac (!claset addss ss)));
qed "UN_parts_sees_Says";

goal thy "Says A B X : set_of_list evs --> X : sees lost Spy evs";
by (list.induct_tac "evs" 1);
by (Auto_tac ());
qed_spec_mp "Says_imp_sees_Spy";

Addsimps [Says_imp_sees_Spy];
AddIs    [Says_imp_sees_Spy];

goal thy "initState lost C <= Key `` range shrK";
by (agent.induct_tac "C" 1);
by (Auto_tac ());
qed "initState_subset";

goal thy "X : sees lost C evs --> \
\          (EX A B. Says A B X : set_of_list evs) | \
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


goal thy "!!K. newK evs = invKey K ==> newK evs = K";
by (rtac (invKey_eq RS iffD1) 1);
by (Simp_tac 1);
val newK_invKey = result();

AddSDs [newK_invKey];

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


(*No premature instantiation of variables.  For proving weak liveness.*)
fun safe_solver prems =
    match_tac (TrueI::refl::prems) ORELSE' eq_assume_tac
    ORELSE' etac FalseE;

(*Analysis of Fake cases and of messages that forward unknown parts
  Abstraction over i is ESSENTIAL: it delays the dereferencing of claset*)
fun spy_analz_tac i =
  SELECT_GOAL 
   (EVERY [  (*push in occurrences of X...*)
           (REPEAT o CHANGED)
             (res_inst_tac [("x1","X")] (insert_commute RS ssubst) 1),
             (*...allowing further simplifications*)
           simp_tac (!simpset setloop split_tac [expand_if]) 1,
           REPEAT (resolve_tac [impI,notI] 1),
           dtac (impOfSubs Fake_analz_insert) 1,
           eresolve_tac [asm_rl, synth.Inj] 1,
           Fast_tac 1,
           Asm_full_simp_tac 1,
           IF_UNSOLVED (deepen_tac (!claset addIs [impOfSubs analz_mono]) 0 1)
           ]) i;


(** Simplifying   parts (insert X (sees lost A evs))
      = parts {X} Un parts (sees lost A evs) -- since general case loops*)

val parts_insert_sees = 
    parts_insert |> read_instantiate_sg (sign_of thy)
                                        [("H", "sees lost A evs")]
                 |> standard;


(** Specialized rewriting for  **)

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


