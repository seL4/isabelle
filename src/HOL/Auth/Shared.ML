(*  Title:      HOL/Auth/Shared
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Theory of Shared Keys (common to all symmetric-key protocols)

Shared, long-term keys; initial states of agents
*)


open Shared;

(*** Basic properties of shrK ***)

(*Injectiveness: Agents' long-term keys are distinct.*)
AddIffs [inj_shrK RS inj_eq];

(* invKey(shrK A) = shrK A *)
Addsimps [rewrite_rule [isSymKey_def] isSym_keys];

(** Rewrites should not refer to  initState(Friend i) 
    -- not in normal form! **)

goalw thy [keysFor_def] "keysFor (parts (initState C)) = {}";
by (induct_tac "C" 1);
by Auto_tac;
qed "keysFor_parts_initState";
Addsimps [keysFor_parts_initState];

goal thy "!!H. Crypt K X : H ==> K : keysFor H";
by (dtac Crypt_imp_invKey_keysFor 1);
by (Asm_full_simp_tac 1);
qed "Crypt_imp_keysFor";


(*** Function "spies" ***)

(*Spy sees shared keys of agents!*)
goal thy "!!A. A: bad ==> Key (shrK A) : spies evs";
by (induct_tac "evs" 1);
by (ALLGOALS (asm_simp_tac
	      (simpset() addsimps [imageI, spies_Cons]
	                addsplits [expand_event_case, expand_if])));
qed "Spy_spies_bad";

AddSIs [Spy_spies_bad];

(*For not_bad_tac*)
goal thy "!!A. [| Crypt (shrK A) X : analz (spies evs);  A: bad |] \
\              ==> X : analz (spies evs)";
by (fast_tac (claset() addSDs [analz.Decrypt] addss (simpset())) 1);
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
         (Step_tac 1));


(** Fresh keys never clash with long-term shared keys **)

(*Agents see their own shared keys!*)
goal thy "Key (shrK A) : initState A";
by (induct_tac "A" 1);
by Auto_tac;
qed "shrK_in_initState";
AddIffs [shrK_in_initState];

goal thy "Key (shrK A) : used evs";
by (rtac initState_into_used 1);
by (Blast_tac 1);
qed "shrK_in_used";
AddIffs [shrK_in_used];

(*Used in parts_induct_tac and analz_Fake_tac to distinguish session keys
  from long-term shared keys*)
goal thy "!!K. Key K ~: used evs ==> K ~: range shrK";
by (Blast_tac 1);
qed "Key_not_used";

goal thy "!!K. Key K ~: used evs ==> shrK B ~= K";
by (Blast_tac 1);
qed "shrK_neq";

Addsimps [Key_not_used, shrK_neq, shrK_neq RS not_sym];


(*** Fresh nonces ***)

goal thy "Nonce N ~: parts (initState B)";
by (induct_tac "B" 1);
by Auto_tac;
qed "Nonce_notin_initState";
AddIffs [Nonce_notin_initState];

goal thy "Nonce N ~: used []";
by (simp_tac (simpset() addsimps [used_Nil]) 1);
qed "Nonce_notin_used_empty";
Addsimps [Nonce_notin_used_empty];


(*** Supply fresh nonces for possibility theorems. ***)

(*In any trace, there is an upper bound N on the greatest nonce in use.*)
goal thy "EX N. ALL n. N<=n --> Nonce n ~: used evs";
by (induct_tac "evs" 1);
by (res_inst_tac [("x","0")] exI 1);
by (ALLGOALS (asm_simp_tac
	      (simpset() addsimps [used_Cons]
			addsplits [expand_event_case, expand_if])));
by Safe_tac;
by (ALLGOALS (rtac (msg_Nonce_supply RS exE)));
by (ALLGOALS (blast_tac (claset() addSEs [add_leE])));
val lemma = result();

goal thy "EX N. Nonce N ~: used evs";
by (rtac (lemma RS exE) 1);
by (Blast_tac 1);
qed "Nonce_supply1";

goal thy "EX N N'. Nonce N ~: used evs & Nonce N' ~: used evs' & N ~= N'";
by (cut_inst_tac [("evs","evs")] lemma 1);
by (cut_inst_tac [("evs","evs'")] lemma 1);
by (Clarify_tac 1);
by (res_inst_tac [("x","N")] exI 1);
by (res_inst_tac [("x","Suc (N+Na)")] exI 1);
by (asm_simp_tac (simpset() addsimps [less_not_refl2 RS not_sym, 
				     le_add2, le_add1, 
				     le_eq_less_Suc RS sym]) 1);
qed "Nonce_supply2";

goal thy "EX N N' N''. Nonce N ~: used evs & Nonce N' ~: used evs' & \
\                   Nonce N'' ~: used evs'' & N ~= N' & N' ~= N'' & N ~= N''";
by (cut_inst_tac [("evs","evs")] lemma 1);
by (cut_inst_tac [("evs","evs'")] lemma 1);
by (cut_inst_tac [("evs","evs''")] lemma 1);
by (Clarify_tac 1);
by (res_inst_tac [("x","N")] exI 1);
by (res_inst_tac [("x","Suc (N+Na)")] exI 1);
by (res_inst_tac [("x","Suc (Suc (N+Na+Nb))")] exI 1);
by (asm_simp_tac (simpset() addsimps [less_not_refl2 RS not_sym, 
				     le_add2, le_add1, 
				     le_eq_less_Suc RS sym]) 1);
qed "Nonce_supply3";

goal thy "Nonce (@ N. Nonce N ~: used evs) ~: used evs";
by (rtac (lemma RS exE) 1);
by (rtac selectI 1);
by (Blast_tac 1);
qed "Nonce_supply";

(*** Supply fresh keys for possibility theorems. ***)

goal thy "EX K. Key K ~: used evs";
by (rtac (Finites.emptyI RS Key_supply_ax RS exE) 1);
by (Blast_tac 1);
qed "Key_supply1";

goal thy "EX K K'. Key K ~: used evs & Key K' ~: used evs' & K ~= K'";
by (cut_inst_tac [("evs","evs")] (Finites.emptyI RS Key_supply_ax) 1);
by (etac exE 1);
by (cut_inst_tac [("evs","evs'")] 
    (Finites.emptyI RS Finites.insertI RS Key_supply_ax) 1);
by Auto_tac;
qed "Key_supply2";

goal thy "EX K K' K''. Key K ~: used evs & Key K' ~: used evs' & \
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

goal thy "Key (@ K. Key K ~: used evs) ~: used evs";
by (rtac (Finites.emptyI RS Key_supply_ax RS exE) 1);
by (rtac selectI 1);
by (Blast_tac 1);
qed "Key_supply";

(*** Tactics for possibility theorems ***)

(*Omitting used_Says makes the tactic much faster: it leaves expressions
    such as  Nonce ?N ~: used evs that match Nonce_supply*)
fun possibility_tac st = st |>
   (REPEAT 
    (ALLGOALS (simp_tac (simpset() delsimps [used_Says] setSolver safe_solver))
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

goal thy "!!A. A <= Compl (range shrK) ==> shrK x ~: A";
by (Blast_tac 1);
qed "subset_Compl_range";

goal thy "insert (Key K) H = Key `` {K} Un H";
by (Blast_tac 1);
qed "insert_Key_singleton";

goal thy "insert (Key K) (Key``KK Un C) = Key `` (insert K KK) Un C";
by (Blast_tac 1);
qed "insert_Key_image";

(*Reverse the normal simplification of "image" to build up (not break down)
  the set of keys.  Use analz_insert_eq with (Un_upper2 RS analz_mono) to
  erase occurrences of forwarded message components (X).*)
val analz_image_freshK_ss = 
     simpset() addcongs [if_weak_cong]
	      delsimps [image_insert, image_Un]
              delsimps [imp_disjL]    (*reduces blow-up*)
              addsimps ([image_insert RS sym, image_Un RS sym,
                         analz_insert_eq, impOfSubs (Un_upper2 RS analz_mono),
                         insert_Key_singleton, subset_Compl_range,
                         Key_not_used, insert_Key_image, Un_assoc RS sym]
                        @disj_comms)
              addsplits [expand_if];

(*Lemma for the trivial direction of the if-and-only-if*)
goal thy  
 "!!evs. (Key K : analz (Key``nE Un H)) --> (K : nE | Key K : analz H)  ==> \
\        (Key K : analz (Key``nE Un H)) = (K : nE | Key K : analz H)";
by (blast_tac (claset() addIs [impOfSubs analz_mono]) 1);
qed "analz_image_freshK_lemma";
