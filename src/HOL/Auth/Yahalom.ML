(*  Title:      HOL/Auth/Yahalom
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "otway" for the Yahalom protocol.

From page 257 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

open Yahalom;

proof_timing:=true;
HOL_quantifiers := false;


(*Weak liveness: there are traces that reach the end*)

goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\        ==> EX X NB K. EX evs: yahalom.          \
\               Says A B {|X, Crypt (Nonce NB) K|} : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
br (yahalom.Nil RS yahalom.YM1 RS yahalom.YM2 RS yahalom.YM3 RS yahalom.YM4) 2;
by (ALLGOALS (simp_tac (!simpset setsolver safe_solver)));
by (ALLGOALS Fast_tac);
result();


(**** Inductive proofs about yahalom ****)

(*The Enemy can see more than anybody else, except for their initial state*)
goal thy 
 "!!evs. evs : yahalom ==> \
\     sees A evs <= initState A Un sees Enemy evs";
be yahalom.induct 1;
by (ALLGOALS (fast_tac (!claset addDs [sees_Says_subset_insert RS subsetD] 
			        addss (!simpset))));
qed "sees_agent_subset_sees_Enemy";


(*Nobody sends themselves messages*)
goal thy "!!evs. evs : yahalom ==> ALL A X. Says A A X ~: set_of_list evs";
be yahalom.induct 1;
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(** For reasoning about the encrypted portion of messages **)

(*Lets us treat YM4 using a similar argument as for the Fake case.*)
goal thy "!!evs. Says S A {|Crypt Y (shrK A), X|} : set_of_list evs ==> \
\                X : analz (sees Enemy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Enemy RS analz.Inj]) 1);
qed "YM4_analz_sees_Enemy";

goal thy "!!evs. Says S A {|Crypt {|B, K, NA, NB|} (shrK A), X|} \
\                  : set_of_list evs ==> \
\                K : parts (sees Enemy evs)";
by (fast_tac (!claset addSEs partsEs
	              addSDs [Says_imp_sees_Enemy RS parts.Inj]) 1);
qed "YM4_parts_sees_Enemy";



(** Theorems of the form X ~: parts (sees Enemy evs) imply that NOBODY
    sends messages containing X! **)

(*Enemy never sees another agent's shared key! (unless it is leaked at start)*)
goal thy 
 "!!evs. [| evs : yahalom;  A ~: bad |]    \
\        ==> Key (shrK A) ~: parts (sees Enemy evs)";
be yahalom.induct 1;
bd (YM4_analz_sees_Enemy RS synth.Inj) 6;
by (ALLGOALS Asm_simp_tac);
by (stac insert_commute 3);
by (Auto_tac());
(*Fake and YM4 are similar*)
by (ALLGOALS (best_tac (!claset addSDs [impOfSubs analz_subset_parts,
					impOfSubs Fake_parts_insert])));
qed "Enemy_not_see_shrK";

bind_thm ("Enemy_not_analz_shrK",
	  [analz_subset_parts, Enemy_not_see_shrK] MRS contra_subsetD);

Addsimps [Enemy_not_see_shrK, Enemy_not_analz_shrK];

(*We go to some trouble to preserve R in the 3rd and 4th subgoals
  As usual fast_tac cannot be used because it uses the equalities too soon*)
val major::prems = 
goal thy  "[| Key (shrK A) : parts (sees Enemy evs);       \
\             evs : yahalom;                               \
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
goal thy "!!evs. evs : yahalom ==> \
\                length evs <= length evs' --> \
\                          Key (newK evs') ~: (UN C. parts (sees C evs))";
be yahalom.induct 1;
bd (YM4_analz_sees_Enemy RS synth.Inj) 6;
by (REPEAT_FIRST (best_tac (!claset addDs [impOfSubs analz_subset_parts,
					   impOfSubs parts_insert_subset_Un,
					   Suc_leD]
			            addss (!simpset))));
val lemma = result();

(*Variant needed for the main theorem below*)
goal thy 
 "!!evs. [| evs : yahalom;  length evs <= length evs' |]    \
\        ==> Key (newK evs') ~: parts (sees C evs)";
by (fast_tac (!claset addDs [lemma]) 1);
qed "new_keys_not_seen";
Addsimps [new_keys_not_seen];

(*Another variant: old messages must contain old keys!*)
goal thy 
 "!!evs. [| Says A B X : set_of_list evs;  \
\           Key (newK evt) : parts {X};    \
\           evs : yahalom                 \
\        |] ==> length evt < length evs";
br ccontr 1;
bd leI 1;
by (fast_tac (!claset addSDs [new_keys_not_seen, Says_imp_sees_Enemy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_keys";


(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : yahalom ==> \
\                length evs <= length evs' --> \
\                newK evs' ~: keysFor (UN C. parts (sees C evs))";
be yahalom.induct 1;
by (forward_tac [YM4_parts_sees_Enemy] 6);
bd (YM4_analz_sees_Enemy RS synth.Inj) 6;
by (ALLGOALS Asm_full_simp_tac);
(*YM1, YM2 and YM3*)
by (EVERY (map (fast_tac (!claset addDs [Suc_leD] addss (!simpset))) [4,3,2]));
(*Fake and YM4: these messages send unknown (X) components*)
by (stac insert_commute 2);
by (Simp_tac 2);
(*YM4: the only way K could have been used is if it had been seen,
  contradicting new_keys_not_seen*)
by (ALLGOALS
     (best_tac
      (!claset addDs [impOfSubs analz_subset_parts,
		      impOfSubs (analz_subset_parts RS keysFor_mono),
		      impOfSubs (parts_insert_subset_Un RS keysFor_mono),
		      Suc_leD]
	       addEs [new_keys_not_seen RSN(2,rev_notE)]
	       addss (!simpset))));
val lemma = result();

goal thy 
 "!!evs. [| evs : yahalom;  length evs <= length evs' |]    \
\        ==> newK evs' ~: keysFor (parts (sees C evs))";
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
 "!!evs. evs : yahalom ==> \
\        (Crypt X (newK evt)) : parts (sees Enemy evs) & \
\        Key K : parts {X} --> Key K : parts (sees Enemy evs)";
be yahalom.induct 1;
bd (YM4_analz_sees_Enemy RS synth.Inj) 6;
by (ALLGOALS (asm_simp_tac (!simpset addsimps pushes)));
(*Deals with Faked messages*)
by (EVERY 
    (map (best_tac (!claset addSEs partsEs
			    addDs [impOfSubs parts_insert_subset_Un]
			    addss (!simpset)))
     [3,2]));
(*Base case*)
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
 "!!evs. evs : yahalom ==> \
\  ALL K E. (Key K : analz (Key``(newK``E) Un (sees Enemy evs))) = \
\           (K : newK``E | Key K : analz (sees Enemy evs))";
be yahalom.induct 1;
bd YM4_analz_sees_Enemy 6;
by (REPEAT_FIRST (resolve_tac [allI, lemma]));
by (ALLGOALS 
    (asm_simp_tac 
     (!simpset addsimps ([insert_Key_singleton, insert_Key_image, pushKey_newK]
			 @ pushes)
               setloop split_tac [expand_if])));
(*YM4*) 
by (enemy_analz_tac 4);
(*YM3*)
by (Fast_tac 3);
(*Fake case*)
by (enemy_analz_tac 2);
(*Base case*)
by (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1);
qed_spec_mp "analz_image_newK";

goal thy
 "!!evs. evs : yahalom ==>                               \
\        Key K : analz (insert (Key (newK evt)) (sees Enemy evs)) = \
\        (K = newK evt | Key K : analz (sees Enemy evs))";
by (asm_simp_tac (HOL_ss addsimps [pushKey_newK, analz_image_newK, 
				   insert_Key_singleton]) 1);
by (Fast_tac 1);
qed "analz_insert_Key_newK";


(*Describes the form of K when the Server sends this message.*)
goal thy 
 "!!evs. [| Says Server A                                           \
\            {|Crypt {|Agent B, K, NA, NB|} (shrK A),               \
\              Crypt {|Agent A, K|} (shrK B)|} : set_of_list evs;   \
\           evs : yahalom |]                                        \
\        ==> (EX evt:yahalom. K = Key(newK evt))";
be rev_mp 1;
be yahalom.induct 1;
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "Says_Server_message_form";


(** Crucial secrecy property: Enemy does not see the keys sent in msg YM3
    As with Otway-Rees, proof does not need uniqueness of session keys. **)

goal thy 
 "!!evs. [| A ~: bad;  B ~: bad;  evs : yahalom;  evt : yahalom |]        \
\        ==> Says Server A                                                \
\              {|Crypt {|Agent B, Key(newK evt), NA, NB|} (shrK A),       \
\                Crypt {|Agent A, Key(newK evt)|} (shrK B)|}              \
\             : set_of_list evs -->    \
\            Key(newK evt) ~: analz (sees Enemy evs)";
be yahalom.induct 1;
bd YM4_analz_sees_Enemy 6;
by (ALLGOALS
    (asm_simp_tac 
     (!simpset addsimps ([analz_subset_parts RS contra_subsetD,
			  analz_insert_Key_newK] @ pushes)
               setloop split_tac [expand_if])));
(*YM4*)
by (enemy_analz_tac 3);
(*YM3*)
by (fast_tac (!claset addIs [parts_insertI]
		      addEs [Says_imp_old_keys RS less_irrefl]
	              addss (!simpset)) 2);
(*Fake*) (** LEVEL 10 **)
by (enemy_analz_tac 1);
val lemma = result() RS mp RSN(2,rev_notE);


(*Final version: Server's message in the most abstract form*)
goal thy 
 "!!evs. [| Says Server A \
\            {|Crypt {|Agent B, K, NA, NB|} (shrK A),                   \
\              Crypt {|Agent A, K|} (shrK B)|} : set_of_list evs;       \
\           A ~: bad;  B ~: bad;  evs : yahalom |] ==>                  \
\     K ~: analz (sees Enemy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (fast_tac (!claset addSEs [lemma]) 1);
qed "Enemy_not_see_encrypted_key";


(** Towards proofs of stronger authenticity properties **)

goal thy 
 "!!evs. [| Crypt {|Agent A, Key K|} (shrK B) : parts (sees Enemy evs); \
\           B ~: bad;  evs : yahalom |]                                 \
\        ==> EX NA NB. Says Server A                                    \
\                        {|Crypt {|Agent B, Key K,                      \
\                                  Nonce NA, Nonce NB|} (shrK A),       \
\                          Crypt {|Agent A, Key K|} (shrK B)|}          \
\                       : set_of_list evs";
be rev_mp 1;
be yahalom.induct 1;
bd (YM4_analz_sees_Enemy RS synth.Inj) 6;
by (ALLGOALS Asm_simp_tac);
(*YM3*)
by (Fast_tac 3);
(*Base case*)
by (fast_tac (!claset addss (!simpset)) 1);
(*Prepare YM4*)
by (stac insert_commute 2 THEN Simp_tac 2);
(*Fake and YM4 are similar*)
by (ALLGOALS (best_tac (!claset addSDs [impOfSubs analz_subset_parts,
					impOfSubs Fake_parts_insert])));
qed "Crypt_imp_Server_msg";


(*What can B deduce from receipt of YM4?  
  NOT THAT THE NONCES AGREE (in this version).  But what does the Nonce
	give us??*)
goal thy 
 "!!evs. [| Says A' B {|Crypt {|Agent A, Key K|} (shrK B),              \
\                       Crypt (Nonce NB) K|} : set_of_list evs;         \
\           B ~: bad;  evs : yahalom |]                                 \
\        ==> EX NA NB. Says Server A                                    \
\                     {|Crypt {|Agent B, Key K,                         \
\                               Nonce NA, Nonce NB|} (shrK A),          \
\                       Crypt {|Agent A, Key K|} (shrK B)|}             \
\                   : set_of_list evs";
be rev_mp 1;
be yahalom.induct 1;
by (dresolve_tac [YM4_analz_sees_Enemy] 6);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS (fast_tac (!claset addSDs [impOfSubs analz_subset_parts RS
					Crypt_imp_Server_msg])));
qed "YM4_imp_Says_Server_A";



goal thy 
 "!!evs. [| Says A' B {|Crypt {|Agent A, Key K|} (shrK B),              \
\                       Crypt (Nonce NB) K|} : set_of_list evs;         \
\           A ~: bad;  B ~: bad;  evs : yahalom |]                      \
\        ==> Key K ~: analz (sees Enemy evs)";
by (fast_tac (!claset addSDs [YM4_imp_Says_Server_A,
			      Enemy_not_see_encrypted_key]) 1);
qed "B_gets_secure_key";
