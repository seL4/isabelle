(*  Title:      HOL/Auth/OtwayRees
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "otway" for the Otway-Rees protocol.

From page 244 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

open OtwayRees;

proof_timing:=true;
HOL_quantifiers := false;


(** Weak liveness: there are traces that reach the end **)

goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\        ==> EX K. EX evs: otway.          \
\               Says A B (Crypt (Agent A) K) : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
br (otway.Nil RS otway.OR1 RS otway.OR2 RS otway.OR3 RS otway.OR4 RS 
    otway.OR5) 2;
by (ALLGOALS (simp_tac (!simpset setsolver safe_solver)));
by (REPEAT_FIRST (resolve_tac [refl, conjI]));
by (ALLGOALS (fast_tac (!claset addss (!simpset setsolver safe_solver))));
qed "weak_liveness";


(**** Inductive proofs about otway ****)

(*The Enemy can see more than anybody else, except for their initial state*)
goal thy 
 "!!evs. evs : otway ==> \
\     sees A evs <= initState A Un sees Enemy evs";
be otway.induct 1;
by (ALLGOALS (fast_tac (!claset addDs [sees_Says_subset_insert RS subsetD] 
			        addss (!simpset))));
qed "sees_agent_subset_sees_Enemy";


(*Nobody sends themselves messages*)
goal thy "!!evs. evs : otway ==> ALL A X. Says A A X ~: set_of_list evs";
be otway.induct 1;
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];

goal thy "!!evs. evs : otway ==> Notes A X ~: set_of_list evs";
be otway.induct 1;
by (Auto_tac());
qed "not_Notes";
Addsimps [not_Notes];
AddSEs   [not_Notes RSN (2, rev_notE)];


(** For reasoning about the encrypted portion of messages **)

goal thy "!!evs. Says A' B {|N, Agent A, Agent B, X|} : set_of_list evs ==> \
\                X : analz (sees Enemy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Enemy RS analz.Inj]) 1);
qed "OR2_analz_sees_Enemy";

goal thy "!!evs. Says S B {|N, X, X'|} : set_of_list evs ==> \
\                X : analz (sees Enemy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Enemy RS analz.Inj]) 1);
qed "OR4_analz_sees_Enemy";

goal thy "!!evs. Says B' A {|N, Crypt {|N,K|} K'|} : set_of_list evs ==> \
\                K : parts (sees Enemy evs)";
by (fast_tac (!claset addSEs partsEs
	              addSDs [Says_imp_sees_Enemy RS parts.Inj]) 1);
qed "OR5_parts_sees_Enemy";

(*OR2_analz... and OR4_analz... let us treat those cases using the same 
  argument as for the Fake case.  This is possible for most, but not all,
  proofs: Fake does not invent new nonces (as in OR2), and of course Fake
  messages originate from the Enemy. *)

val OR2_OR4_tac = 
    dtac (OR2_analz_sees_Enemy RS (impOfSubs analz_subset_parts)) 4 THEN
    dtac (OR4_analz_sees_Enemy RS (impOfSubs analz_subset_parts)) 6;


(*** Shared keys are not betrayed ***)

(*Enemy never sees another agent's shared key! (unless it is leaked at start)*)
goal thy 
 "!!evs. [| evs : otway;  A ~: bad |] ==> \
\        Key (shrK A) ~: parts (sees Enemy evs)";
be otway.induct 1;
by OR2_OR4_tac;
by (Auto_tac());
(*Deals with Fake message*)
by (best_tac (!claset addDs [impOfSubs analz_subset_parts,
			     impOfSubs Fake_parts_insert]) 1);
qed "Enemy_not_see_shrK";

bind_thm ("Enemy_not_analz_shrK",
	  [analz_subset_parts, Enemy_not_see_shrK] MRS contra_subsetD);

Addsimps [Enemy_not_see_shrK, Enemy_not_analz_shrK];

(*We go to some trouble to preserve R in the 3rd and 4th subgoals
  As usual fast_tac cannot be used because it uses the equalities too soon*)
val major::prems = 
goal thy  "[| Key (shrK A) : parts (sees Enemy evs);       \
\             evs : otway;                                 \
\             A:bad ==> R                                  \
\           |] ==> R";
br ccontr 1;
br ([major, Enemy_not_see_shrK] MRS rev_notE) 1;
by (swap_res_tac prems 2);
by (ALLGOALS (fast_tac (!claset addIs prems)));
qed "Enemy_see_shrK_E";

bind_thm ("Enemy_analz_shrK_E", 
	  analz_subset_parts RS subsetD RS Enemy_see_shrK_E);

AddSEs [Enemy_see_shrK_E, Enemy_analz_shrK_E];


(*** Future keys can't be seen or used! ***)

(*Nobody can have SEEN keys that will be generated in the future.
  This has to be proved anew for each protocol description,
  but should go by similar reasoning every time.  Hardest case is the
  standard Fake rule.  
      The length comparison, and Union over C, are essential for the 
  induction! *)
goal thy "!!evs. evs : otway ==> \
\                length evs <= length evs' --> \
\                          Key (newK evs') ~: (UN C. parts (sees C evs))";
be otway.induct 1;
by OR2_OR4_tac;
(*auto_tac does not work here, as it performs safe_tac first*)
by (ALLGOALS Asm_simp_tac);
by (REPEAT_FIRST (best_tac (!claset addDs [impOfSubs analz_subset_parts,
				       impOfSubs parts_insert_subset_Un,
				       Suc_leD]
			        addss (!simpset))));
val lemma = result();

(*Variant needed for the main theorem below*)
goal thy 
 "!!evs. [| evs : otway;  length evs <= length evs' |] ==> \
\        Key (newK evs') ~: parts (sees C evs)";
by (fast_tac (!claset addDs [lemma]) 1);
qed "new_keys_not_seen";
Addsimps [new_keys_not_seen];

(*Another variant: old messages must contain old keys!*)
goal thy 
 "!!evs. [| Says A B X : set_of_list evs;  \
\           Key (newK evt) : parts {X};    \
\           evs : otway                 \
\        |] ==> length evt < length evs";
br ccontr 1;
by (fast_tac (!claset addSDs [new_keys_not_seen, Says_imp_sees_Enemy]
	              addIs [impOfSubs parts_mono, leI]) 1);
qed "Says_imp_old_keys";


(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : otway ==> \
\                length evs <= length evs' --> \
\                newK evs' ~: keysFor (UN C. parts (sees C evs))";
be otway.induct 1;
by OR2_OR4_tac;
bd OR5_parts_sees_Enemy 7;
by (ALLGOALS Asm_simp_tac);
(*OR1 and OR3*)
by (EVERY (map (fast_tac (!claset addDs [Suc_leD] addss (!simpset))) [4,2]));
(*Fake, OR2, OR4: these messages send unknown (X) components*)
by (EVERY 
    (map
     (best_tac
      (!claset addDs [impOfSubs (analz_subset_parts RS keysFor_mono),
		      impOfSubs (parts_insert_subset_Un RS keysFor_mono),
		      Suc_leD]
	       addEs [new_keys_not_seen RS not_parts_not_analz RSN(2,rev_notE)]
	       addss (!simpset)))
     [3,2,1]));
(*OR5: dummy message*)
by (best_tac (!claset addEs  [new_keys_not_seen RSN(2,rev_notE)]
		      addIs  [less_SucI, impOfSubs keysFor_mono]
		      addss (!simpset addsimps [le_def])) 1);
val lemma = result();

goal thy 
 "!!evs. [| evs : otway;  length evs <= length evs' |] ==> \
\        newK evs' ~: keysFor (parts (sees C evs))";
by (fast_tac (!claset addSDs [lemma] addss (!simpset)) 1);
qed "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
	  [analz_subset_parts RS keysFor_mono,
	   new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];


(** Lemmas concerning the form of items passed in messages **)


(****
 The following is to prove theorems of the form

          Key K : analz (insert (Key (newK evt)) (sees Enemy evs)) ==>
          Key K : analz (sees Enemy evs)

 A more general formula must be proved inductively.

****)


(*NOT useful in this form, but it says that session keys are not used
  to encrypt messages containing other keys, in the actual protocol.
  We require that agents should behave like this subsequently also.*)
goal thy 
 "!!evs. evs : otway ==> \
\        (Crypt X (newK evt)) : parts (sees Enemy evs) & \
\        Key K : parts {X} --> Key K : parts (sees Enemy evs)";
be otway.induct 1;
by OR2_OR4_tac;
by (ALLGOALS (asm_simp_tac (!simpset addsimps pushes)));
(*Deals with Faked messages*)
by (best_tac (!claset addSEs partsEs
		      addDs [impOfSubs analz_subset_parts,
                             impOfSubs parts_insert_subset_Un]
                      addss (!simpset)) 2);
(*Base case and OR5*)
by (Auto_tac());
result();


(** Specialized rewriting for this proof **)

Delsimps [image_insert];
Addsimps [image_insert RS sym];

Delsimps [image_Un];
Addsimps [image_Un RS sym];

goal thy "insert (Key (newK x)) (sees A evs) = \
\         Key `` (newK``{x}) Un (sees A evs)";
by (Fast_tac 1);
val insert_Key_singleton = result();

goal thy "insert (Key (f x)) (Key``(f``E) Un C) = \
\         Key `` (f `` (insert x E)) Un C";
by (Fast_tac 1);
val insert_Key_image = result();


(*This lets us avoid analyzing the new message -- unless we have to!*)
(*NEEDED??*)
goal thy "synth (analz (sees Enemy evs)) <=   \
\         synth (analz (sees Enemy (Says A B X # evs)))";
by (Simp_tac 1);
br (subset_insertI RS analz_mono RS synth_mono) 1;
qed "synth_analz_thin";

AddIs [impOfSubs synth_analz_thin];



(** Session keys are not used to encrypt other session keys **)

(*Lemma for the trivial direction of the if-and-only-if*)
goal thy  
 "!!evs. (Key K : analz (Key``nE Un sEe)) --> \
\         (K : nE | Key K : analz sEe)  ==>     \
\        (Key K : analz (Key``nE Un sEe)) = (K : nE | Key K : analz sEe)";
by (fast_tac (!claset addSEs [impOfSubs analz_mono]) 1);
val lemma = result();


goal thy  
 "!!evs. evs : otway ==> \
\  ALL K E. (Key K : analz (Key``(newK``E) Un (sees Enemy evs))) = \
\           (K : newK``E | Key K : analz (sees Enemy evs))";
be otway.induct 1;
bd OR2_analz_sees_Enemy 4;
bd OR4_analz_sees_Enemy 6;
by (REPEAT_FIRST (resolve_tac [allI, lemma]));
by (ALLGOALS (*Takes 35 secs*)
    (asm_simp_tac 
     (!simpset addsimps ([insert_Key_singleton, insert_Key_image, pushKey_newK]
			 @ pushes)
               setloop split_tac [expand_if])));
(*OR4, OR2, Fake*) 
by (EVERY (map enemy_analz_tac [5,3,2]));
(*OR3*)
by (Fast_tac 2);
(*Base case*) 
by (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1);
qed_spec_mp "analz_image_newK";


goal thy
 "!!evs. evs : otway ==>                               \
\        Key K : analz (insert (Key (newK evt)) (sees Enemy evs)) = \
\        (K = newK evt | Key K : analz (sees Enemy evs))";
by (asm_simp_tac (HOL_ss addsimps [pushKey_newK, analz_image_newK, 
				   insert_Key_singleton]) 1);
by (Fast_tac 1);
qed "analz_insert_Key_newK";


(*Describes the form *and age* of K when the following message is sent*)
goal thy 
 "!!evs. [| Says Server B \
\            {|NA, Crypt {|NA, K|} (shrK A),                      \
\                  Crypt {|NB, K|} (shrK B)|} : set_of_list evs;  \
\           evs : otway |]                                        \
\        ==> (EX evt:otway. K = Key(newK evt) & \
\                           length evt < length evs) &            \
\            (EX i. NA = Nonce i)";
be rev_mp 1;
be otway.induct 1;
by (ALLGOALS (fast_tac (!claset addIs [less_SucI] addss (!simpset))));
qed "Says_Server_message_form";


(*Crucial secrecy property: Enemy does not see the keys sent in msg OR3*)
goal thy 
 "!!evs. [| Says Server A \
\            {|NA, Crypt {|NA, K|} (shrK B),                      \
\                  Crypt {|NB, K|} (shrK A)|} : set_of_list evs;  \
\           A ~: bad;  B ~: bad;  evs : otway |] ==>              \
\     K ~: analz (sees Enemy evs)";
be rev_mp 1;
be otway.induct 1;
bd OR2_analz_sees_Enemy 4;
bd OR4_analz_sees_Enemy 6;
by (ALLGOALS Asm_simp_tac);
(*Next 3 steps infer that K has the form "Key (newK evs'" ... *)
by (REPEAT_FIRST (resolve_tac [conjI, impI]));
by (TRYALL (forward_tac [Says_Server_message_form] THEN' assume_tac));
by (REPEAT_FIRST (eresolve_tac [bexE, exE, conjE] ORELSE' hyp_subst_tac));
by (ALLGOALS
    (asm_full_simp_tac 
     (!simpset addsimps ([analz_subset_parts RS contra_subsetD,
			  analz_insert_Key_newK] @ pushes)
               setloop split_tac [expand_if])));
(*OR4, OR2, Fake*) 
by (EVERY (map enemy_analz_tac [4,2,1]));
(*OR3*)
by (fast_tac (!claset addSEs [less_irrefl]) 1);
qed "Enemy_not_see_encrypted_key";



(*** Session keys are issued at most once, and identify the principals ***)

(** First, two lemmas for the Fake, OR2 and OR4 cases **)

goal thy 
 "!!evs. [| X : synth (analz (sees Enemy evs));                \
\           Crypt X' (shrK C) : parts{X};                      \
\           C ~: bad;  evs : otway |]  \
\        ==> Crypt X' (shrK C) : parts (sees Enemy evs)";
by (best_tac (!claset addSEs [impOfSubs analz_subset_parts]
	              addDs [impOfSubs parts_insert_subset_Un]
                      addss (!simpset)) 1);
qed "Crypt_Fake_parts";

goal thy 
 "!!evs. [| Crypt X' K : parts (sees A evs);  evs : otway |]  \
\        ==> EX S S' Y. Says S S' Y : set_of_list evs &       \
\            Crypt X' K : parts {Y}";
bd parts_singleton 1;
by (fast_tac (!claset addSDs [seesD] addss (!simpset)) 1);
qed "Crypt_parts_singleton";

fun ex_strip_tac i = REPEAT (ares_tac [exI, conjI] i) THEN assume_tac (i+1);

(*The Key K uniquely identifies a pair of senders in the message encrypted by
  C, but if C=Enemy then he could send all sorts of nonsense.*)
goal thy 
 "!!evs. evs : otway ==>                                     \
\      EX A B. ALL C.                                        \
\         C ~: bad -->                                       \
\         (ALL S S' X. Says S S' X : set_of_list evs -->     \
\           (EX NA. Crypt {|NA, Key K|} (shrK C) : parts{X}) --> C=A | C=B)";
by (Simp_tac 1);
be otway.induct 1;
bd OR2_analz_sees_Enemy 4;
bd OR4_analz_sees_Enemy 6;
by (ALLGOALS 
    (asm_simp_tac (!simpset addsimps [all_conj_distrib, imp_conj_distrib])));
by (REPEAT_FIRST (etac exE));
(*OR4*)
by (ex_strip_tac 4);
by (fast_tac (!claset addSDs [synth.Inj RS Crypt_Fake_parts, 
			      Crypt_parts_singleton]) 4);
(*OR3: Case split propagates some context to other subgoal...*)
	(** LEVEL 8 **)
by (excluded_middle_tac "K = newK evsa" 3);
by (Asm_simp_tac 3);
by (REPEAT (ares_tac [exI] 3));
(*...we prove this case by contradiction: the key is too new!*)
by (fast_tac (!claset addIs [impOfSubs (subset_insertI RS parts_mono)]
		      addSEs partsEs
		      addEs [Says_imp_old_keys RS less_irrefl]
	              addss (!simpset)) 3);
(*OR2*) (** LEVEL 12 **)
(*enemy_analz_tac just does not work here: it is an entirely different proof!*)
by (ex_strip_tac 2);
by (res_inst_tac [("x1","X")] (insert_commute RS ssubst) 2);
by (Simp_tac 2);
by (fast_tac (!claset addSDs [synth.Inj RS Crypt_Fake_parts, 
			      Crypt_parts_singleton]) 2);
(*Fake*) (** LEVEL 16 **)
by (ex_strip_tac 1);
by (fast_tac (!claset addSDs [Crypt_Fake_parts, Crypt_parts_singleton]) 1);
qed "unique_session_keys";

(*It seems strange but this theorem is NOT needed to prove the main result!*)
