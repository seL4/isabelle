(*  Title:      HOL/Auth/Public
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Public Keys (common to all symmetric-key protocols)

Server keys; initial states of agents; new nonces and keys; function "sees" 
*)

(*** Basic properties of pubK & priK ***)

AddIffs [inj_pubK RS inj_eq];

Goal "(priK A = priK B) = (A=B)";
by Safe_tac;
by (dres_inst_tac [("f","invKey")] arg_cong 1);
by (Full_simp_tac 1);
qed "priK_inj_eq";

AddIffs [priK_inj_eq];
AddIffs [priK_neq_pubK, priK_neq_pubK RS not_sym];

Goalw [isSymKey_def] "~ isSymKey (pubK A)";
by (Simp_tac 1);
qed "not_isSymKey_pubK";

Goalw [isSymKey_def] "~ isSymKey (priK A)";
by (Simp_tac 1);
qed "not_isSymKey_priK";

AddIffs [not_isSymKey_pubK, not_isSymKey_priK];


(** "Image" equations that hold for injective functions **)

Goal "(invKey x : invKey``A) = (x:A)";
by Auto_tac;
qed "invKey_image_eq";

(*holds because invKey is injective*)
Goal "(pubK x : pubK``A) = (x:A)";
by Auto_tac;
qed "pubK_image_eq";

Goal "(priK x ~: pubK``A)";
by Auto_tac;
qed "priK_pubK_image_eq";
Addsimps [invKey_image_eq, pubK_image_eq, priK_pubK_image_eq];


(** Rewrites should not refer to  initState(Friend i) 
    -- not in normal form! **)

Goalw [keysFor_def] "keysFor (parts (initState C)) = {}";
by (induct_tac "C" 1);
by (auto_tac (claset() addIs [range_eqI], simpset()));
qed "keysFor_parts_initState";
Addsimps [keysFor_parts_initState];


(*** Function "spies" ***)

(*Agents see their own private keys!*)
Goal "Key (priK A) : initState A";
by (induct_tac "A" 1);
by Auto_tac;
qed "priK_in_initState";
AddIffs [priK_in_initState];

(*All public keys are visible*)
Goal "Key (pubK A) : spies evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac
	      (simpset() addsimps [imageI, knows_Cons]
	                addsplits [expand_event_case])));
qed_spec_mp "spies_pubK";

(*Spy sees private keys of bad agents!*)
Goal "A: bad ==> Key (priK A) : spies evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac
	      (simpset() addsimps [imageI, knows_Cons]
	                addsplits [expand_event_case])));
qed "Spy_spies_bad";

AddIffs [spies_pubK, spies_pubK RS analz.Inj];
AddSIs  [Spy_spies_bad];


(*For not_bad_tac*)
Goal "[| Crypt (pubK A) X : analz (spies evs);  A: bad |] \
\           ==> X : analz (spies evs)";
by (blast_tac (claset() addSDs [analz.Decrypt]) 1);
qed "Crypt_Spy_analz_bad";

(*Prove that the agent is uncompromised by the confidentiality of 
  a component of a message she's said.*)
fun not_bad_tac s =
    case_tac ("(" ^ s ^ ") : bad") THEN'
    SELECT_GOAL 
      (REPEAT_DETERM (dtac (Says_imp_spies RS analz.Inj) 1) THEN
       REPEAT_DETERM (etac MPair_analz 1) THEN
       THEN_BEST_FIRST 
         (dres_inst_tac [("A", s)] Crypt_Spy_analz_bad 1 THEN assume_tac 1)
         (has_fewer_prems 1, size_of_thm)
         Safe_tac);


(*** Fresh nonces ***)

Goal "Nonce N ~: parts (initState B)";
by (induct_tac "B" 1);
by Auto_tac;
qed "Nonce_notin_initState";
AddIffs [Nonce_notin_initState];

Goal "Nonce N ~: used []";
by (simp_tac (simpset() addsimps [used_Nil]) 1);
qed "Nonce_notin_used_empty";
Addsimps [Nonce_notin_used_empty];


(*** Supply fresh nonces for possibility theorems. ***)

(*In any trace, there is an upper bound N on the greatest nonce in use.*)
Goal "EX N. ALL n. N<=n --> Nonce n ~: used evs";
by (induct_tac "evs" 1);
by (res_inst_tac [("x","0")] exI 1);
by (ALLGOALS (asm_simp_tac
	      (simpset() addsimps [used_Cons]
			addsplits [expand_event_case])));
by Safe_tac;
by (ALLGOALS (rtac (msg_Nonce_supply RS exE)));
by (ALLGOALS (blast_tac (claset() addSEs [add_leE])));
val lemma = result();

Goal "EX N. Nonce N ~: used evs";
by (rtac (lemma RS exE) 1);
by (Blast_tac 1);
qed "Nonce_supply1";

Goal "Nonce (@ N. Nonce N ~: used evs) ~: used evs";
by (rtac (lemma RS exE) 1);
by (rtac selectI 1);
by (Fast_tac 1);
qed "Nonce_supply";

(*Tactic for possibility theorems*)
fun possibility_tac st = st |>
    REPEAT (*omit used_Says so that Nonces start from different traces!*)
    (ALLGOALS (simp_tac (simpset() delsimps [used_Says] setSolver safe_solver))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' 
                   resolve_tac [refl, conjI, Nonce_supply]));


(*** Specialized rewriting for the analz_image_... theorems ***)

Goal "insert (Key K) H = Key `` {K} Un H";
by (Blast_tac 1);
qed "insert_Key_singleton";

Goal "insert (Key K) (Key``KK Un C) = Key `` (insert K KK) Un C";
by (Blast_tac 1);
qed "insert_Key_image";

(*Reverse the normal simplification of "image" to build up (not break down)
  the set of keys.  Based on analz_image_freshK_ss, but simpler.*)
val analz_image_keys_ss = 
     simpset() addcongs [if_weak_cong]
	      delsimps [image_insert, image_Un]
              delsimps [imp_disjL]    (*reduces blow-up*)
              addsimps [image_insert RS sym, image_Un RS sym,
			rangeI, 
			insert_Key_singleton, 
			insert_Key_image, Un_assoc RS sym];

