(*  Title:      HOL/Auth/Shared
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Shared Keys (common to all symmetric-key protocols)

Shared, long-term keys; initial states of agents
*)

val inj_shrK      = thm "inj_shrK";
val isSym_keys    = thm "isSym_keys";
val Key_supply_ax = thm "Key_supply_ax";

(*** Basic properties of shrK ***)

(*Injectiveness: Agents' long-term keys are distinct.*)
AddIffs [inj_shrK RS inj_eq];

(* invKey(shrK A) = shrK A *)
Addsimps [rewrite_rule [isSymKey_def] isSym_keys];

(** Rewrites should not refer to  initState(Friend i) 
    -- not in normal form! **)

Goalw [keysFor_def] "keysFor (parts (initState C)) = {}";
by (induct_tac "C" 1);
by Auto_tac;
qed "keysFor_parts_initState";
Addsimps [keysFor_parts_initState];

(*Specialized to shared-key model: no need for addss in protocol proofs*)
Goal "[| K: keysFor (parts (insert X H));  X : synth (analz H) |] \
\              ==> K : keysFor (parts H) | Key K : parts H";
by (force_tac
      (claset() addSDs [impOfSubs (parts_insert_subset_Un RS keysFor_mono),
			impOfSubs (analz_subset_parts RS keysFor_mono)]
		addIs  [impOfSubs analz_subset_parts],
       simpset()) 1);
qed "keysFor_parts_insert";

Goal "Crypt K X : H ==> K : keysFor H";
by (dtac Crypt_imp_invKey_keysFor 1);
by (Asm_full_simp_tac 1);
qed "Crypt_imp_keysFor";


(*** Function "knows" ***)

(*Spy sees shared keys of agents!*)
Goal "A: bad ==> Key (shrK A) : knows Spy evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac
	      (simpset() addsimps [imageI, knows_Cons]
	                addsplits [expand_event_case])));
qed "Spy_knows_Spy_bad";
AddSIs [Spy_knows_Spy_bad];

(*For not_bad_tac*)
Goal "[| Crypt (shrK A) X : analz (knows Spy evs);  A: bad |] \
\              ==> X : analz (knows Spy evs)";
by (force_tac (claset() addSDs [analz.Decrypt], simpset()) 1);
qed "Crypt_Spy_analz_bad";

(*Prove that the agent is uncompromised by the confidentiality of 
  a component of a message she's said.*)
fun not_bad_tac s =
    case_tac ("(" ^ s ^ ") : bad") THEN'
    SELECT_GOAL 
      (REPEAT_DETERM (etac exE 1) THEN
       REPEAT_DETERM (dtac (Says_imp_spies RS analz.Inj) 1) THEN
       REPEAT_DETERM (etac MPair_analz 1) THEN
       THEN_BEST_FIRST 
         (dres_inst_tac [("A", s)] Crypt_Spy_analz_bad 1 THEN assume_tac 1)
         (has_fewer_prems 1, size_of_thm)
         (Step_tac 1));


(** Fresh keys never clash with long-term shared keys **)

(*Agents see their own shared keys!*)
Goal "Key (shrK A) : initState A";
by (induct_tac "A" 1);
by Auto_tac;
qed "shrK_in_initState";
AddIffs [shrK_in_initState];

Goal "Key (shrK A) : used evs";
by (rtac initState_into_used 1);
by (Blast_tac 1);
qed "shrK_in_used";
AddIffs [shrK_in_used];

(*Used in parts_induct_tac and analz_Fake_tac to distinguish session keys
  from long-term shared keys*)
Goal "Key K ~: used evs ==> K ~: range shrK";
by (Blast_tac 1);
qed "Key_not_used";

Goal "Key K ~: used evs ==> shrK B ~= K";
by (Blast_tac 1);
qed "shrK_neq";

Addsimps [Key_not_used, shrK_neq, shrK_neq RS not_sym];


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

Goal "EX N N'. Nonce N ~: used evs & Nonce N' ~: used evs' & N ~= N'";
by (cut_inst_tac [("evs","evs")] lemma 1);
by (cut_inst_tac [("evs","evs'")] lemma 1);
by (Clarify_tac 1);
by (res_inst_tac [("x","N")] exI 1);
by (res_inst_tac [("x","Suc (N+Na)")] exI 1);
by (asm_simp_tac (simpset() addsimps [less_not_refl3, le_add1, le_add2,
				      less_Suc_eq_le]) 1);
qed "Nonce_supply2";

Goal "EX N N' N''. Nonce N ~: used evs & Nonce N' ~: used evs' & \
\                   Nonce N'' ~: used evs'' & N ~= N' & N' ~= N'' & N ~= N''";
by (cut_inst_tac [("evs","evs")] lemma 1);
by (cut_inst_tac [("evs","evs'")] lemma 1);
by (cut_inst_tac [("evs","evs''")] lemma 1);
by (Clarify_tac 1);
by (res_inst_tac [("x","N")] exI 1);
by (res_inst_tac [("x","Suc (N+Na)")] exI 1);
by (res_inst_tac [("x","Suc (Suc (N+Na+Nb))")] exI 1);
by (asm_simp_tac (simpset() addsimps [less_not_refl3, le_add1, le_add2,
				      less_Suc_eq_le]) 1);
qed "Nonce_supply3";

Goal "Nonce (@ N. Nonce N ~: used evs) ~: used evs";
by (rtac (lemma RS exE) 1);
by (rtac someI 1);
by (Blast_tac 1);
qed "Nonce_supply";

(*** Supply fresh keys for possibility theorems. ***)

Goal "EX K. Key K ~: used evs";
by (rtac (Finites.emptyI RS Key_supply_ax RS exE) 1);
by (Blast_tac 1);
qed "Key_supply1";

Goal "EX K K'. Key K ~: used evs & Key K' ~: used evs' & K ~= K'";
by (cut_inst_tac [("evs","evs")] (Finites.emptyI RS Key_supply_ax) 1);
by (etac exE 1);
by (cut_inst_tac [("evs","evs'")] 
    (Finites.emptyI RS Finites.insertI RS Key_supply_ax) 1);
by (Asm_full_simp_tac 1 THEN depth_tac (claset()) 2 1); (* replaces Auto_tac *)
qed "Key_supply2";

Goal "EX K K' K''. Key K ~: used evs & Key K' ~: used evs' & \
\                      Key K'' ~: used evs'' & K ~= K' & K' ~= K'' & K ~= K''";
by (cut_inst_tac [("evs","evs")] (Finites.emptyI RS Key_supply_ax) 1);
by (etac exE 1);
(*Blast_tac requires instantiation of the keys for some reason*)
by (cut_inst_tac [("evs","evs'"), ("a1","K")] 
    (Finites.emptyI RS Finites.insertI RS Key_supply_ax) 1);
by (etac exE 1);
by (cut_inst_tac [("evs","evs''"), ("a1","Ka"), ("a2","K")] 
    (Finites.emptyI RS Finites.insertI RS Finites.insertI RS Key_supply_ax) 1);
by (Blast_tac 1);
qed "Key_supply3";

Goal "Key (@ K. Key K ~: used evs) ~: used evs";
by (rtac (Finites.emptyI RS Key_supply_ax RS exE) 1);
by (rtac someI 1);
by (Blast_tac 1);
qed "Key_supply";

(*** Tactics for possibility theorems ***)

(*Omitting used_Says makes the tactic much faster: it leaves expressions
    such as  Nonce ?N ~: used evs that match Nonce_supply*)
fun possibility_tac st = st |>
   (REPEAT 
    (ALLGOALS (simp_tac (simpset() delsimps [used_Says, used_Notes, used_Gets] 
                         setSolver safe_solver))
     THEN
     REPEAT_FIRST (eq_assume_tac ORELSE' 
                   resolve_tac [refl, conjI, Nonce_supply, Key_supply])));

(*For harder protocols (such as Recur) where we have to set up some
  nonces and keys initially*)
fun basic_possibility_tac st = st |>
    REPEAT 
    (ALLGOALS (asm_simp_tac (simpset() setSolver safe_solver))
     THEN
     REPEAT_FIRST (resolve_tac [refl, conjI]));


(*** Specialized rewriting for analz_insert_freshK ***)

Goal "A <= - (range shrK) ==> shrK x ~: A";
by (Blast_tac 1);
qed "subset_Compl_range";

Goal "insert (Key K) H = Key ` {K} Un H";
by (Blast_tac 1);
qed "insert_Key_singleton";

Goal "insert (Key K) (Key`KK Un C) = Key ` (insert K KK) Un C";
by (Blast_tac 1);
qed "insert_Key_image";

(** Reverse the normal simplification of "image" to build up (not break down)
    the set of keys.  Use analz_insert_eq with (Un_upper2 RS analz_mono) to
    erase occurrences of forwarded message components (X). **)

bind_thms ("analz_image_freshK_simps",
           simp_thms @ mem_simps @  (*these two allow its use with only:*)
           disj_comms @
           [image_insert RS sym, image_Un RS sym, empty_subsetI, insert_subset,
            analz_insert_eq, impOfSubs (Un_upper2 RS analz_mono),
	    insert_Key_singleton, subset_Compl_range,
            Key_not_used, insert_Key_image, Un_assoc RS sym]);

val analz_image_freshK_ss = 
     simpset() delsimps [image_insert, image_Un]
	       delsimps [imp_disjL]    (*reduces blow-up*)
	       addsimps analz_image_freshK_simps;

(*Lemma for the trivial direction of the if-and-only-if*)
Goal "(Key K : analz (Key`nE Un H)) --> (K : nE | Key K : analz H)  ==> \
\        (Key K : analz (Key`nE Un H)) = (K : nE | Key K : analz H)";
by (blast_tac (claset() addIs [impOfSubs analz_mono]) 1);
qed "analz_image_freshK_lemma";

