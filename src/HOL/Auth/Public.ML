(*  Title:      HOL/Auth/Public
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Public Keys (common to all symmetric-key protocols)

Server keys; initial states of agents; new nonces and keys; function "sees" 
*)


open Public;

(*** Basic properties of pubK & priK ***)

AddIffs [inj_pubK RS inj_eq];

goal thy "!!A B. (priK A = priK B) = (A=B)";
by (Step_tac 1);
by (dres_inst_tac [("f","invKey")] arg_cong 1);
by (Full_simp_tac 1);
qed "priK_inj_eq";

AddIffs [priK_inj_eq];
AddIffs [priK_neq_pubK, priK_neq_pubK RS not_sym];

goalw thy [isSymKey_def] "~ isSymKey (pubK A)";
by (Simp_tac 1);
qed "not_isSymKey_pubK";

goalw thy [isSymKey_def] "~ isSymKey (priK A)";
by (Simp_tac 1);
qed "not_isSymKey_priK";

AddIffs [not_isSymKey_pubK, not_isSymKey_priK];

(** Rewrites should not refer to  initState(Friend i) 
    -- not in normal form! **)

goalw thy [keysFor_def] "keysFor (parts (initState C)) = {}";
by (agent.induct_tac "C" 1);
by (auto_tac (!claset addIs [range_eqI], !simpset));
qed "keysFor_parts_initState";
Addsimps [keysFor_parts_initState];


(*** Function "sees" ***)

(*Agents see their own private keys!*)
goal thy "A ~= Spy --> Key (priK A) : sees A evs";
by (list.induct_tac "evs" 1);
by (agent.induct_tac "A" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [sees_Cons])));
qed_spec_mp "sees_own_priK";

(*All public keys are visible to all*)
goal thy "Key (pubK A) : sees B evs";
by (list.induct_tac "evs" 1);
by (agent.induct_tac "B" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [sees_Cons])));
by (Auto_tac ());
qed_spec_mp "sees_pubK";

(*Spy sees private keys of agents!*)
goal thy "!!A. A: lost ==> Key (priK A) : sees Spy evs";
by (list.induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [sees_Cons])));
by (Blast_tac 1);
qed "Spy_sees_lost";

AddIffs [sees_pubK, sees_pubK RS analz.Inj];
AddSIs  [sees_own_priK, Spy_sees_lost];


(*For not_lost_tac*)
goal thy "!!A. [| Crypt (pubK A) X : analz (sees Spy evs);  A: lost |] \
\              ==> X : analz (sees Spy evs)";
by (blast_tac (!claset addSDs [analz.Decrypt]) 1);
qed "Crypt_Spy_analz_lost";

(*Prove that the agent is uncompromised by the confidentiality of 
  a component of a message she's said.*)
fun not_lost_tac s =
    case_tac ("(" ^ s ^ ") : lost") THEN'
    SELECT_GOAL 
      (REPEAT_DETERM (dtac (Says_imp_sees_Spy RS analz.Inj) 1) THEN
       REPEAT_DETERM (etac MPair_analz 1) THEN
       THEN_BEST_FIRST 
         (dres_inst_tac [("A", s)] Crypt_Spy_analz_lost 1 THEN assume_tac 1)
         (has_fewer_prems 1, size_of_thm)
         (Step_tac 1));


(*** Fresh nonces ***)

goal thy "Nonce N ~: parts (initState B)";
by (agent.induct_tac "B" 1);
by (Auto_tac ());
qed "Nonce_notin_initState";
AddIffs [Nonce_notin_initState];

goal thy "Nonce N ~: used []";
by (simp_tac (!simpset addsimps [used_def]) 1);
qed "Nonce_notin_used_empty";
Addsimps [Nonce_notin_used_empty];


(*** Supply fresh nonces for possibility theorems. ***)

goalw thy [used_def] "EX N. ALL n. N<=n --> Nonce n ~: used evs";
by (list.induct_tac "evs" 1);
by (res_inst_tac [("x","0")] exI 1);
by (Step_tac 1);
by (Full_simp_tac 1);
(*Inductive step*)
by (event.induct_tac "a" 1);
by (ALLGOALS (full_simp_tac 
	      (!simpset delsimps [sees_Notes]
		        addsimps [UN_parts_sees_Says,
				  UN_parts_sees_Notes])));
by (ALLGOALS (rtac (msg_Nonce_supply RS exE)));
by (ALLGOALS (blast_tac (!claset addSEs [add_leE])));
val lemma = result();

goal thy "Nonce (@ N. Nonce N ~: used evs) ~: used evs";
by (rtac (lemma RS exE) 1);
by (rtac selectI 1);
by (Fast_tac 1);
qed "Nonce_supply";

(*Tactic for possibility theorems*)
fun possibility_tac st = st |>
    REPEAT (*omit used_Says so that Nonces, Keys start from different traces!*)
    (ALLGOALS (simp_tac (!simpset delsimps [used_Says] setSolver safe_solver))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' 
                   resolve_tac [refl, conjI, Nonce_supply]));


(*** Specialized rewriting for the analz_image_... theorems ***)

goal thy "insert (Key K) H = Key `` {K} Un H";
by (Blast_tac 1);
qed "insert_Key_singleton";

goal thy "insert (Key K) (Key``KK Un C) = Key `` (insert K KK) Un C";
by (Blast_tac 1);
qed "insert_Key_image";

(*Reverse the normal simplification of "image" to build up (not break down)
  the set of keys.  Based on analz_image_freshK_ss, but simpler.*)
val analz_image_keys_ss = 
     !simpset delsimps [image_insert, image_Un]
              addsimps [image_insert RS sym, image_Un RS sym,
			rangeI, 
			insert_Key_singleton, 
			insert_Key_image, Un_assoc RS sym]
              setloop split_tac [expand_if];

