(*  Title:      HOL/Auth/Public
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Public Keys (common to all symmetric-key protocols)

Server keys; initial states of agents; new nonces and keys; function "sees" 
*)


open Public;

(*Injectiveness of new nonces*)
AddIffs [inj_newN RS inj_eq];

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

goalw thy [keysFor_def] "keysFor (parts (initState lost C)) = {}";
by (agent.induct_tac "C" 1);
by (auto_tac (!claset addIs [range_eqI], !simpset));
qed "keysFor_parts_initState";
Addsimps [keysFor_parts_initState];

goalw thy [keysFor_def] "keysFor (Key``E) = {}";
by (Auto_tac ());
qed "keysFor_image_Key";
Addsimps [keysFor_image_Key];


(*** Function "sees" ***)

goal thy
    "!!evs. lost' <= lost ==> sees lost' A evs <= sees lost A evs";
by (list.induct_tac "evs" 1);
by (agent.induct_tac "A" 1);
by (event.induct_tac "a" 2);
by (Auto_tac ());
qed "sees_mono";

(*** Basic properties of pubK & priK ***)

AddIffs [inj_pubK RS inj_eq];
Addsimps [priK_neq_pubK, priK_neq_pubK RS not_sym];

(*Agents see their own private keys!*)
goal thy "A ~= Spy --> Key (priK A) : sees lost A evs";
by (list.induct_tac "evs" 1);
by (agent.induct_tac "A" 1);
by (Auto_tac ());
qed_spec_mp "sees_own_priK";

(*All public keys are visible*)
goal thy "Key (pubK A) : sees lost A evs";
by (list.induct_tac "evs" 1);
by (agent.induct_tac "A" 1);
by (Auto_tac ());
qed_spec_mp "sees_pubK";

(*Spy sees private keys of lost agents!*)
goal thy "!!A. A: lost ==> Key (priK A) : sees lost Spy evs";
by (list.induct_tac "evs" 1);
by (Auto_tac());
qed "Spy_sees_lost";

AddIffs [sees_pubK];
AddSIs  [sees_own_priK, Spy_sees_lost];

(*Added for Yahalom/lost_tac*)
goal thy "!!A. [| Crypt (pubK A) X : analz (sees lost Spy evs);  A: lost |] \
\              ==> X : analz (sees lost Spy evs)";
by (blast_tac (!claset addSDs [analz.Decrypt]) 1);
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
    (fast_tac (!claset unsafe_addss (!simpset addsimps [parts_Un, sees_Cons] 
				            setloop split_tac [expand_if]))));
qed "UN_parts_sees_Says";

goal thy "Says A B X : set_of_list evs --> X : sees lost Spy evs";
by (list.induct_tac "evs" 1);
by (Auto_tac ());
qed_spec_mp "Says_imp_sees_Spy";

(*Use with addSEs to derive contradictions from old Says events containing
  items known to be fresh*)
val sees_Spy_partsEs = make_elim (Says_imp_sees_Spy RS parts.Inj):: partsEs;

goal thy  
 "!!evs. [| Says A B (Crypt (pubK C) X) : set_of_list evs;  C : lost |] \
\        ==> X : analz (sees lost Spy evs)";
by (blast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]) 1);
qed "Says_Crypt_lost";

goal thy  
 "!!evs. [| Says A B (Crypt (pubK C) X) : set_of_list evs;        \
\           X ~: analz (sees lost Spy evs) |]                     \
\        ==> C ~: lost";
by (blast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]) 1);
qed "Says_Crypt_not_lost";

Addsimps [sees_own, sees_Server, sees_Friend, sees_Spy];
Delsimps [sees_Cons];   (**** NOTE REMOVAL -- laws above are cleaner ****)


(*** Fresh nonces ***)

goal thy "Nonce N ~: parts (initState lost B)";
by (agent.induct_tac "B" 1);
by (Auto_tac ());
qed "Nonce_notin_initState";

AddIffs [Nonce_notin_initState];

goalw thy [used_def] "!!X. X: parts (sees lost B evs) ==> X: used evs";
by (etac (impOfSubs parts_mono) 1);
by (Fast_tac 1);
qed "usedI";

AddIs [usedI];

(** A supply of fresh nonces for possibility theorems. **)

goalw thy [used_def] "EX N. ALL n. N<=n --> Nonce n ~: used evs";
by (list.induct_tac "evs" 1);
by (res_inst_tac [("x","0")] exI 1);
by (Step_tac 1);
by (Full_simp_tac 1);
(*Inductive step*)
by (event.induct_tac "a" 1);
by (full_simp_tac (!simpset addsimps [UN_parts_sees_Says]) 1);
by (msg.induct_tac "msg" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [exI, parts_insert2])));
by (Step_tac 1);
(*MPair case*)
by (res_inst_tac [("x","Na+Nb")] exI 2);
by (fast_tac (!claset addSEs [add_leE]) 2);
(*Nonce case*)
by (res_inst_tac [("x","N + Suc nat")] exI 1);
by (fast_tac (!claset addSEs [add_leE] addaltern trans_tac) 1);
val lemma = result();

goal thy "Nonce (@ N. Nonce N ~: used evs) ~: used evs";
by (rtac (lemma RS exE) 1);
by (rtac selectI 1);
by (Fast_tac 1);
qed "Nonce_supply";

(*Tactic for possibility theorems*)
val possibility_tac =
    REPEAT 
    (ALLGOALS (simp_tac (!simpset setSolver safe_solver))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' 
                   resolve_tac [refl, conjI, Nonce_supply]));

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
