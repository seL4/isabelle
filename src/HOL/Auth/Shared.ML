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
bind_thm ("invKey_id", rewrite_rule [isSymKey_def] isSym_keys);

Addsimps [invKey_id];

goal thy "!!K. newK i = invKey K ==> newK i = K";
by (rtac (invKey_eq RS iffD1) 1);
by (Full_simp_tac 1);
val newK_invKey = result();

AddSDs [newK_invKey, sym RS newK_invKey];

Addsimps [newK_neq_shrK, newK_neq_shrK RS not_sym];

(** Rewrites should not refer to  initState(Friend i) 
    -- not in normal form! **)

goal thy "Key (newK i) ~: parts (initState lost B)";
by (agent.induct_tac "B" 1);
by (Auto_tac ());
qed "newK_notin_initState";

AddIffs [newK_notin_initState];

goalw thy [keysFor_def] "keysFor (parts (initState lost C)) = {}";
by (agent.induct_tac "C" 1);
by (Auto_tac ());
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
by (Blast_tac 1);
qed "sees_Says_subset_insert";

goal thy "sees lost A evs <= sees lost A (Says A' B X # evs)";
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Blast_tac 1);
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

(*Use with addSEs to derive contradictions from old Says events containing
  items known to be fresh*)
val sees_Spy_partsEs = make_elim (Says_imp_sees_Spy RS parts.Inj):: partsEs;

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
by (blast_tac (!claset addDs [impOfSubs initState_subset]) 1);
by (rtac conjI 1);
by (Blast_tac 2);
by (event.induct_tac "a" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [mem_if])));
by (ALLGOALS Blast_tac);
qed_spec_mp "seesD";

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
by (Blast_tac 1);
qed "usedI";

AddIs [usedI];

(** Fresh keys never clash with long-term shared keys **)

goal thy "Key (shrK A) : used evs";
by (Blast_tac 1);
qed "shrK_in_used";
AddIffs [shrK_in_used];

(*Used in parts_induct_tac and analz_Fake_tac to distinguish session keys
  from long-term shared keys*)
goal thy "!!K. Key K ~: used evs ==> K ~: range shrK";
by (Blast_tac 1);
qed "Key_not_used";

(*A session key cannot clash with a long-term shared key*)
goal thy "!!K. K ~: range shrK ==> shrK B ~= K";
by (Blast_tac 1);
qed "shrK_neq";

Addsimps [Key_not_used, shrK_neq, shrK_neq RS not_sym];


goal thy "used (Says A B X # evs) = parts{X} Un used evs";
by (simp_tac (!simpset addsimps [used_def, UN_parts_sees_Says]) 1);
qed "used_Says";
Addsimps [used_Says];

goal thy "used [] <= used l";
by (list.induct_tac "l" 1);
by (event.induct_tac "a" 2);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed "used_nil_subset";

goal thy "used l <= used (l@l')";
by (list.induct_tac "l" 1);
by (simp_tac (!simpset addsimps [used_nil_subset]) 1);
by (event.induct_tac "a" 1);
by (Asm_simp_tac 1);
by (Blast_tac 1);
qed "used_subset_append";


(*** Supply fresh nonces for possibility theorems. ***)

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
by (blast_tac (!claset addSEs [add_leE]) 2);
(*Nonce case*)
by (res_inst_tac [("x","N + Suc nat")] exI 1);
by (fast_tac (!claset addSEs [add_leE] addaltern trans_tac) 1);
val lemma = result();

goal thy "EX N. Nonce N ~: used evs";
by (rtac (lemma RS exE) 1);
by (Blast_tac 1);
qed "Nonce_supply1";

goal thy "EX N N'. Nonce N ~: used evs & Nonce N' ~: used evs' & N ~= N'";
by (cut_inst_tac [("evs","evs")] lemma 1);
by (cut_inst_tac [("evs","evs'")] lemma 1);
by (Step_tac 1);
by (res_inst_tac [("x","N")] exI 1);
by (res_inst_tac [("x","Suc (N+Na)")] exI 1);
by (asm_simp_tac (!simpset addsimps [less_not_refl2 RS not_sym, 
				     le_add2, le_add1, 
				     le_eq_less_Suc RS sym]) 1);
qed "Nonce_supply2";

goal thy "EX N N' N''. Nonce N ~: used evs & Nonce N' ~: used evs' & \
\                   Nonce N'' ~: used evs'' & N ~= N' & N' ~= N'' & N ~= N''";
by (cut_inst_tac [("evs","evs")] lemma 1);
by (cut_inst_tac [("evs","evs'")] lemma 1);
by (cut_inst_tac [("evs","evs''")] lemma 1);
by (Step_tac 1);
by (res_inst_tac [("x","N")] exI 1);
by (res_inst_tac [("x","Suc (N+Na)")] exI 1);
by (res_inst_tac [("x","Suc (Suc (N+Na+Nb))")] exI 1);
by (asm_simp_tac (!simpset addsimps [less_not_refl2 RS not_sym, 
				     le_add2, le_add1, 
				     le_eq_less_Suc RS sym]) 1);
by (rtac (less_trans RS less_not_refl2 RS not_sym) 1);
by (stac (le_eq_less_Suc RS sym) 1);
by (asm_simp_tac (!simpset addsimps [le_eq_less_Suc RS sym]) 2);
by (REPEAT (rtac le_add1 1));
qed "Nonce_supply3";

goal thy "Nonce (@ N. Nonce N ~: used evs) ~: used evs";
by (rtac (lemma RS exE) 1);
by (rtac selectI 1);
by (Blast_tac 1);
qed "Nonce_supply";

(*** Supply fresh keys for possibility theorems. ***)

goal thy "EX K. Key K ~: used evs";
by (rtac (Fin.emptyI RS Key_supply_ax RS exE) 1);
by (Blast_tac 1);
qed "Key_supply1";

val Fin_UNIV_insertI = UNIV_I RS Fin.insertI;

goal thy "EX K K'. Key K ~: used evs & Key K' ~: used evs' & K ~= K'";
by (cut_inst_tac [("evs","evs")] (Fin.emptyI RS Key_supply_ax) 1);
by (etac exE 1);
by (cut_inst_tac [("evs","evs'")] 
    (Fin.emptyI RS Fin_UNIV_insertI RS Key_supply_ax) 1);
by (Auto_tac());
qed "Key_supply2";

goal thy "EX K K' K''. Key K ~: used evs & Key K' ~: used evs' & \
\                      Key K'' ~: used evs'' & K ~= K' & K' ~= K'' & K ~= K''";
by (cut_inst_tac [("evs","evs")] (Fin.emptyI RS Key_supply_ax) 1);
by (etac exE 1);
by (cut_inst_tac [("evs","evs'")] 
    (Fin.emptyI RS Fin_UNIV_insertI RS Key_supply_ax) 1);
by (etac exE 1);
by (cut_inst_tac [("evs","evs''")] 
    (Fin.emptyI RS Fin_UNIV_insertI RS Fin_UNIV_insertI RS Key_supply_ax) 1);
by (Step_tac 1);
by (Full_simp_tac 1);
by (fast_tac (!claset addSEs [allE]) 1);
qed "Key_supply3";

goal thy "Key (@ K. Key K ~: used evs) ~: used evs";
by (rtac (Fin.emptyI RS Key_supply_ax RS exE) 1);
by (rtac selectI 1);
by (Blast_tac 1);
qed "Key_supply";

(*** Tactics for possibility theorems ***)

val possibility_tac =
    REPEAT (*omit used_Says so that Nonces, Keys start from different traces!*)
    (ALLGOALS (simp_tac 
               (!simpset delsimps [used_Says] setSolver safe_solver))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' 
                   resolve_tac [refl, conjI, Nonce_supply, Key_supply]));

(*For harder protocols (such as Recur) where we have to set up some
  nonces and keys initially*)
val basic_possibility_tac =
    REPEAT 
    (ALLGOALS (asm_simp_tac (!simpset setSolver safe_solver))
     THEN
     REPEAT_FIRST (resolve_tac [refl, conjI]));


(** Power of the Spy **)

(*The Spy can see more than anybody else, except for their initial state*)
goal thy "sees lost A evs <= initState lost A Un sees lost Spy evs";
by (list.induct_tac "evs" 1);
by (event.induct_tac "a" 2);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (blast_tac (!claset addDs [sees_Says_subset_insert RS subsetD])));
qed "sees_agent_subset_sees_Spy";

(*The Spy can see more than anybody else who's lost their key!*)
goal thy "A: lost --> A ~= Server --> sees lost A evs <= sees lost Spy evs";
by (list.induct_tac "evs" 1);
by (event.induct_tac "a" 2);
by (agent.induct_tac "A" 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (blast_tac (!claset addDs [sees_Says_subset_insert RS subsetD])));
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

goal thy "!!A. A <= Compl (range shrK) ==> shrK x ~: A";
by (Blast_tac 1);
qed "subset_Compl_range";

goal thy "insert (Key K) H = Key `` {K} Un H";
by (Blast_tac 1);
qed "insert_Key_singleton";

goal thy "insert (Key K) (Key``KK Un C) = Key `` (insert K KK) Un C";
by (Blast_tac 1);
qed "insert_Key_image";

val analz_image_freshK_ss = 
     !simpset delsimps [image_insert, image_Un]
              addsimps ([image_insert RS sym, image_Un RS sym,
                         Key_not_used, 
                         insert_Key_singleton, subset_Compl_range,
                         insert_Key_image, Un_assoc RS sym]
                        @disj_comms)
              setloop split_tac [expand_if];

(*Lemma for the trivial direction of the if-and-only-if*)
goal thy  
 "!!evs. (Key K : analz (Key``nE Un H)) --> (K : nE | Key K : analz H)  ==> \
\        (Key K : analz (Key``nE Un H)) = (K : nE | Key K : analz H)";
by (blast_tac (!claset addIs [impOfSubs analz_mono]) 1);
qed "analz_image_freshK_lemma";
