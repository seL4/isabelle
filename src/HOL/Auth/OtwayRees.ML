(*  Title:      HOL/Auth/OtwayRees
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "otway" for the Otway-Rees protocol.

Version that encrypts Nonce NB

From page 244 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)


open OtwayRees;

proof_timing:=true;
HOL_quantifiers := false;


(*Weak liveness: there are traces that reach the end*)
goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\        ==> EX K. EX NA. EX evs: otway.          \
\               Says B A {|Nonce NA, Crypt {|Nonce NA, Key K|} (shrK A)|} \
\                 : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
br (otway.Nil RS otway.OR1 RS otway.OR2 RS otway.OR3 RS otway.OR4) 2;
by (ALLGOALS (simp_tac (!simpset setsolver safe_solver)));
by (REPEAT_FIRST (resolve_tac [refl, conjI]));
by (ALLGOALS (fast_tac (!claset addss (!simpset setsolver safe_solver))));
result();


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
qed "Reveal_parts_sees_Enemy";

(*OR2_analz... and OR4_analz... let us treat those cases using the same 
  argument as for the Fake case.  This is possible for most, but not all,
  proofs: Fake does not invent new nonces (as in OR2), and of course Fake
  messages originate from the Enemy. *)

val parts_Fake_tac = 
    forward_tac [OR2_analz_sees_Enemy RS (impOfSubs analz_subset_parts)] 4 THEN
    forward_tac [OR4_analz_sees_Enemy RS (impOfSubs analz_subset_parts)] 6 THEN
    forward_tac [Reveal_parts_sees_Enemy] 7;


(** Theorems of the form X ~: parts (sees Enemy evs) imply that NOBODY
    sends messages containing X! **)

(*Enemy never sees another agent's shared key! (unless it is leaked at start)*)
goal thy 
 "!!evs. [| evs : otway;  A ~: bad |]    \
\        ==> Key (shrK A) ~: parts (sees Enemy evs)";
be otway.induct 1;
by parts_Fake_tac;
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
      The Union over C is essential for the induction! *)
goal thy "!!evs. evs : otway ==> \
\                length evs <= length evs' --> \
\                          Key (newK evs') ~: (UN C. parts (sees C evs))";
be otway.induct 1;
by parts_Fake_tac;
(*auto_tac does not work here, as it performs safe_tac first*)
by (ALLGOALS Asm_simp_tac);
by (REPEAT_FIRST (best_tac (!claset addDs [impOfSubs analz_subset_parts,
					   impOfSubs parts_insert_subset_Un,
					   Suc_leD]
			            addss (!simpset))));
val lemma = result();

(*Variant needed for the main theorem below*)
goal thy 
 "!!evs. [| evs : otway;  length evs <= length evs' |]    \
\        ==> Key (newK evs') ~: parts (sees C evs)";
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
bd leI 1;
by (fast_tac (!claset addSDs [new_keys_not_seen, Says_imp_sees_Enemy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_keys";


(*** Future nonces can't be seen or used! [proofs resemble those above] ***)

goal thy "!!evs. evs : otway ==> \
\                length evs <= length evt --> \
\                          Nonce (newN evt) ~: (UN C. parts (sees C evs))";
be otway.induct 1;
(*auto_tac does not work here, as it performs safe_tac first*)
by (ALLGOALS (asm_simp_tac (!simpset addsimps [ parts_insert2]
                                     addcongs [disj_cong])));
by (REPEAT_FIRST (fast_tac (!claset 
			      addSEs partsEs
			      addSDs  [Says_imp_sees_Enemy RS parts.Inj]
			      addDs  [impOfSubs analz_subset_parts,
				      impOfSubs parts_insert_subset_Un,
				      Suc_leD]
			      addss (!simpset))));
val lemma = result();

(*Variant needed for the main theorem below*)
goal thy 
 "!!evs. [| evs : otway;  length evs <= length evs' |]    \
\        ==> Nonce (newN evs') ~: parts (sees C evs)";
by (fast_tac (!claset addDs [lemma]) 1);
qed "new_nonces_not_seen";
Addsimps [new_nonces_not_seen];

(*Another variant: old messages must contain old nonces!*)
goal thy 
 "!!evs. [| Says A B X : set_of_list evs;  \
\           Nonce (newN evt) : parts {X};    \
\           evs : otway                 \
\        |] ==> length evt < length evs";
br ccontr 1;
bd leI 1;
by (fast_tac (!claset addSDs [new_nonces_not_seen, Says_imp_sees_Enemy]
	              addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_nonces";


(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : otway ==> \
\                length evs <= length evs' --> \
\                newK evs' ~: keysFor (UN C. parts (sees C evs))";
be otway.induct 1;
by parts_Fake_tac;
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
(*Reveal: dummy message*)
by (best_tac (!claset addEs  [new_keys_not_seen RSN(2,rev_notE)]
		      addIs  [less_SucI, impOfSubs keysFor_mono]
		      addss (!simpset addsimps [le_def])) 1);
val lemma = result();

goal thy 
 "!!evs. [| evs : otway;  length evs <= length evs' |]    \
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
 "!!evs. evs : otway ==> \
\        (Crypt X (newK evt)) : parts (sees Enemy evs) & \
\        Key K : parts {X} --> Key K : parts (sees Enemy evs)";
be otway.induct 1;
by parts_Fake_tac;
by (ALLGOALS (asm_simp_tac (!simpset addsimps pushes)));
(*Deals with Faked messages*)
by (best_tac (!claset addSEs partsEs
		      addDs [impOfSubs parts_insert_subset_Un]
                      addss (!simpset)) 2);
(*Base case and Reveal*)
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

(*Describes the form of Key K when the following message is sent.  The use of
  "parts" strengthens the induction hyp for proving the Fake case.  The
  assumptions on A are needed to prevent its being a Faked message.  (Based
  on NS_Shared/Says_S_message_form) *)
goal thy
 "!!evs. evs: otway ==>                                           \
\          Crypt {|N, Key K|} (shrK A) : parts (sees Enemy evs) & \
\          A ~: bad -->                                           \
\        (EX evt:otway. K = newK evt)";
be otway.induct 1;
by parts_Fake_tac;
by (Auto_tac());
(*Deals with Fake message*)
by (best_tac (!claset addDs [impOfSubs analz_subset_parts,
			     impOfSubs Fake_parts_insert]) 1);
val lemma = result() RS mp;


(*EITHER describes the form of Key K when the following message is sent, 
  OR     reduces it to the Fake case.*)
goal thy 
 "!!evs. [| Says B' A {|N, Crypt {|N, Key K|} (shrK A)|} : set_of_list evs;  \
\           evs : otway |]                      \
\        ==> (EX evt:otway. K = newK evt) | Key K : analz (sees Enemy evs)";
by (excluded_middle_tac "A : bad" 1);
by (fast_tac (!claset addSDs [Says_imp_sees_Enemy RS analz.Inj]
	              addss (!simpset)) 2);
by (forward_tac [lemma] 1);
by (fast_tac (!claset addEs  partsEs
	              addSDs [Says_imp_sees_Enemy RS parts.Inj]) 1);
by (Fast_tac 1);
qed "Reveal_message_form";


(*Lemma for the trivial direction of the if-and-only-if*)
goal thy  
 "!!evs. (Key K : analz (Key``nE Un sEe)) --> \
\         (K : nE | Key K : analz sEe)  ==>     \
\        (Key K : analz (Key``nE Un sEe)) = (K : nE | Key K : analz sEe)";
by (fast_tac (!claset addSEs [impOfSubs analz_mono]) 1);
val lemma = result();


(*The equality makes the induction hypothesis easier to apply*)
goal thy  
 "!!evs. evs : otway ==> \
\  ALL K E. (Key K : analz (Key``(newK``E) Un (sees Enemy evs))) = \
\           (K : newK``E | Key K : analz (sees Enemy evs))";
be otway.induct 1;
bd OR2_analz_sees_Enemy 4;
bd OR4_analz_sees_Enemy 6;
bd Reveal_message_form 7;
by (REPEAT_FIRST (ares_tac [allI, lemma]));
by (REPEAT ((eresolve_tac [bexE, disjE] ORELSE' hyp_subst_tac) 7));
by (ALLGOALS (*Takes 28 secs*)
    (asm_simp_tac 
     (!simpset addsimps ([insert_Key_singleton, insert_Key_image, pushKey_newK]
			 @ pushes)
               setloop split_tac [expand_if])));
(** LEVEL 7 **)
(*Reveal case 2, OR4, OR2, Fake*) 
by (EVERY (map enemy_analz_tac [7,5,3,2]));
(*Reveal case 1, OR3, Base*)
by (Auto_tac());
qed_spec_mp "analz_image_newK";


goal thy
 "!!evs. evs : otway ==>                               \
\        Key K : analz (insert (Key (newK evt)) (sees Enemy evs)) = \
\        (K = newK evt | Key K : analz (sees Enemy evs))";
by (asm_simp_tac (HOL_ss addsimps [pushKey_newK, analz_image_newK, 
				   insert_Key_singleton]) 1);
by (Fast_tac 1);
qed "analz_insert_Key_newK";


(*** The Key K uniquely identifies the Server's  message. **)

fun ex_strip_tac i = REPEAT (ares_tac [exI, conjI] i) THEN assume_tac (i+1);

goal thy 
 "!!evs. evs : otway ==>                      \
\      EX A' B' NA' NB'. ALL A B NA NB.                    \
\       Says Server B \
\            {|NA, Crypt {|NA, K|} (shrK A),                      \
\                  Crypt {|NB, K|} (shrK B)|} : set_of_list evs --> \
\       A=A' & B=B' & NA=NA' & NB=NB'";
be otway.induct 1;
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib])));
by (Step_tac 1);
(*Remaining cases: OR3 and OR4*)
by (ex_strip_tac 2);
by (Fast_tac 2);
by (excluded_middle_tac "K = Key(newK evsa)" 1);
by (Asm_simp_tac 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 1));
(*...we assume X is a very new message, and handle this case by contradiction*)
by (fast_tac (!claset addEs [Says_imp_old_keys RS less_irrefl]
	              delrules [conjI]    (*prevent split-up into 4 subgoals*)
	              addss (!simpset addsimps [parts_insertI])) 1);
val lemma = result();

goal thy 
 "!!evs. [| Says Server B                                          \
\              {|NA, Crypt {|NA, K|} (shrK A),                     \
\                    Crypt {|NB, K|} (shrK B)|}                    \
\            : set_of_list evs;                                    \ 
\           Says Server B'                                         \
\              {|NA', Crypt {|NA', K|} (shrK A'),                  \
\                     Crypt {|NB', K|} (shrK B')|}                 \
\            : set_of_list evs;                                    \
\           evs : otway |]                                         \
\        ==> A=A' & B=B' & NA=NA' & NB=NB'";
bd lemma 1;
by (REPEAT (etac exE 1));
(*Duplicate the assumption*)
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
by (fast_tac (!claset addSDs [spec]) 1);
qed "unique_session_keys";



(**** Towards proving stronger authenticity properties ****)

(*Only OR1 can have caused such a part of a message to appear.*)
goal thy 
 "!!evs. [| A ~: bad;  evs : otway |]               \
\        ==> Crypt {|NA, Agent A, Agent B|} (shrK A)        \
\             : parts (sees Enemy evs) -->                  \
\            Says A B {|NA, Agent A, Agent B,               \
\                       Crypt {|NA, Agent A, Agent B|} (shrK A)|}  \
\             : set_of_list evs";
be otway.induct 1;
by parts_Fake_tac;
by (ALLGOALS Asm_simp_tac);
(*Fake*)
by (best_tac (!claset addSDs [impOfSubs analz_subset_parts,
			      impOfSubs Fake_parts_insert]) 2);
by (Auto_tac());
qed_spec_mp "Crypt_imp_OR1";


(** The Nonce NA uniquely identifies A's  message. **)

goal thy 
 "!!evs. [| evs : otway; A ~: bad |]               \
\ ==> EX B'. ALL B.    \
\        Crypt {|NA, Agent A, Agent B|} (shrK A) : parts (sees Enemy evs) --> \
\        B = B'";
be otway.induct 1;
by parts_Fake_tac;
by (ALLGOALS Asm_simp_tac);
(*Fake*)
by (best_tac (!claset addSDs [impOfSubs analz_subset_parts,
			      impOfSubs Fake_parts_insert]) 2);
(*Base case*)
by (fast_tac (!claset addss (!simpset)) 1);
by (Step_tac 1);
(*OR1: creation of new Nonce.  Move assertion into global context*)
by (excluded_middle_tac "NA = Nonce (newN evsa)" 1);
by (Asm_simp_tac 1);
by (Fast_tac 1);
by (best_tac (!claset addSEs partsEs
	              addEs  [new_nonces_not_seen RSN(2,rev_notE)]) 1);
val lemma = result();

goal thy 
 "!!evs.[| Crypt {|NA, Agent A, Agent B|} (shrK A) : parts (sees Enemy evs); \ 
\          Crypt {|NA, Agent A, Agent C|} (shrK A) : parts (sees Enemy evs); \ 
\          evs : otway;  A ~: bad |]                                         \
\        ==> B = C";
bd lemma 1;
ba 1;
by (etac exE 1);
(*Duplicate the assumption*)
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
by (fast_tac (!claset addSDs [spec]) 1);
qed "unique_OR1_nonce";


val nonce_not_seen_now = le_refl RSN (2, new_nonces_not_seen) RSN (2,rev_notE);

(*It is impossible to re-use a nonce in both OR1 and OR2.  This holds because
  OR2 encrypts Nonce NB.  It prevents the attack that can occur in the
  over-simplified version of this protocol: see OtwayRees_Bad.*)
goal thy 
 "!!evs. [| A ~: bad;  evs : otway |]                            \
\        ==> Crypt {|NA, Agent A, Agent B|} (shrK A)             \
\             : parts (sees Enemy evs) -->                       \
\            Crypt {|NA', NA, Agent A', Agent A|} (shrK A)       \
\             ~: parts (sees Enemy evs)";
be otway.induct 1;
by (ALLGOALS (asm_simp_tac (!simpset addsimps [parts_insert2])));
(*It is hard to generate this proof in a reasonable amount of time*)
by (step_tac (!claset addSEs [MPair_parts, nonce_not_seen_now]
                      addSDs [Says_imp_sees_Enemy RS parts.Inj]) 1);
by (REPEAT_FIRST (fast_tac (!claset (*40 seconds??*)
			    addSDs  [impOfSubs analz_subset_parts,
				     impOfSubs parts_insert_subset_Un]
			    addss  (!simpset))));
by (REPEAT_FIRST (fast_tac (!claset 
			      addSEs (partsEs@[nonce_not_seen_now])
                              addSDs  [impOfSubs parts_insert_subset_Un]
                              addss (!simpset))));
qed_spec_mp"no_nonce_OR1_OR2";



(*If the encrypted message appears, and A has used Nonce NA to start a run,
  then it originated with the Server!*)
goal thy 
 "!!evs. [| A ~: bad;  evs : otway |]                                        \
\        ==> Crypt {|Nonce NA, Key K|} (shrK A) : parts (sees Enemy evs) --> \
\            Says A B {|Nonce NA, Agent A, Agent B,                          \
\                       Crypt {|Nonce NA, Agent A, Agent B|} (shrK A)|}      \
\             : set_of_list evs -->                                          \
\            (EX NB. Says Server B                                           \
\                 {|Nonce NA,                                                \
\                   Crypt {|Nonce NA, Key K|} (shrK A),                      \
\                   Crypt {|Nonce NB, Key K|} (shrK B)|}                     \
\                   : set_of_list evs)";
be otway.induct 1;
by parts_Fake_tac;
by (ALLGOALS Asm_simp_tac);
(*Fake*)
by (best_tac (!claset addSDs [impOfSubs analz_subset_parts,
			      impOfSubs Fake_parts_insert]) 1);
(*OR1: it cannot be a new Nonce, contradiction.*)
by (fast_tac (!claset addSIs [parts_insertI]
		      addSEs partsEs
		      addEs [Says_imp_old_nonces RS less_irrefl]
	              addss (!simpset)) 1);
(*OR3 and OR4*)  (** LEVEL 5 **)
(*OR4*)
by (REPEAT (Safe_step_tac 2));
by (REPEAT (best_tac (!claset addSDs [parts_cut]) 3));
by (fast_tac (!claset addSIs [Crypt_imp_OR1]
		      addEs  partsEs
	              addDs [Says_imp_sees_Enemy RS parts.Inj]) 2);
(*OR3*)  (** LEVEL 8 **)
by (ALLGOALS (asm_simp_tac (!simpset addsimps [ex_disj_distrib])));
by (step_tac (!claset delrules [disjCI, impCE]) 1);
by (fast_tac (!claset addSDs [Says_imp_sees_Enemy RS parts.Inj]
                      addSEs [MPair_parts]
                      addEs  [unique_OR1_nonce]) 1);
by (fast_tac (!claset addSEs [MPair_parts]
                      addSDs [Says_imp_sees_Enemy RS parts.Inj]
                      addEs  [no_nonce_OR1_OR2 RSN (2, rev_notE)]
	              delrules [conjI] (*stop split-up into 4 subgoals*)) 1);
qed_spec_mp "Crypt_imp_Server_msg";


(*Crucial property: if A receives B's OR4 message and the nonce NA agrees
  then the key really did come from the Server!  CANNOT prove this of the
  bad form of this protocol, even though we can prove
  Enemy_not_see_encrypted_key*)
goal thy 
 "!!evs. [| A ~: bad;  evs : otway |]                                    \
\        ==> Says B' A {|Nonce NA, Crypt {|Nonce NA, Key K|} (shrK A)|}  \
\             : set_of_list evs -->                                      \
\            Says A B {|Nonce NA, Agent A, Agent B,                      \
\                       Crypt {|Nonce NA, Agent A, Agent B|} (shrK A)|}  \
\             : set_of_list evs -->                                      \
\            (EX NB. Says Server B                                       \
\                     {|Nonce NA,                                        \
\                       Crypt {|Nonce NA, Key K|} (shrK A),              \
\                       Crypt {|Nonce NB, Key K|} (shrK B)|}             \
\                       : set_of_list evs)";
be otway.induct 1;
by (ALLGOALS (asm_simp_tac (!simpset addcongs [conj_cong])));
(*OR2*)
by (Fast_tac 3);
(*OR1: it cannot be a new Nonce, contradiction.*)
by (fast_tac (!claset addSIs [parts_insertI]
		      addEs [Says_imp_old_nonces RS less_irrefl]
	              addss (!simpset)) 2);
(*Fake, OR4*) (** LEVEL 4 **)
by (step_tac (!claset delrules [impCE]) 1);
by (ALLGOALS Asm_simp_tac);
by (Fast_tac 4);
by (fast_tac (!claset addSIs [Crypt_imp_OR1]
		      addEs  partsEs
	              addDs [Says_imp_sees_Enemy RS parts.Inj]) 3);
(** LEVEL 8 **)
(*Still subcases of Fake and OR4*)
by (fast_tac (!claset addSIs [Crypt_imp_Server_msg]
	              addDs  [impOfSubs analz_subset_parts]) 1);
by (fast_tac (!claset addSIs [Crypt_imp_Server_msg]
	              addEs  partsEs
	              addDs  [Says_imp_sees_Enemy RS parts.Inj]) 1);
val lemma = result();

val OR4_imp_Says_Server_A = 
    lemma RSN (2, rev_mp) RS mp |> standard;



(*Describes the form of K and NA when the Server sends this message.*)
goal thy 
 "!!evs. [| Says Server B \
\            {|NA, Crypt {|NA, K|} (shrK A),                      \
\                  Crypt {|NB, K|} (shrK B)|} : set_of_list evs;  \
\           evs : otway |]                                        \
\        ==> (EX evt:otway. K = Key(newK evt)) &                  \
\            (EX i. NA = Nonce i)";
be rev_mp 1;
be otway.induct 1;
by (ALLGOALS (fast_tac (!claset addIs [less_SucI] addss (!simpset))));
qed "Says_Server_message_form";


(** Crucial secrecy property: Enemy does not see the keys sent in msg OR3 **)

goal thy 
 "!!evs. [| A ~: bad;  B ~: bad;  evs : otway;  evt : otway |]         \
\        ==> Says Server B                                             \
\              {|Nonce NA, Crypt {|Nonce NA, Key(newK evt)|} (shrK A), \
\                Crypt {|NB, Key(newK evt)|} (shrK B)|} : set_of_list evs --> \
\            Says A Enemy {|Nonce NA, Key(newK evt)|} ~: set_of_list evs --> \
\            Key(newK evt) ~: analz (sees Enemy evs)";
be otway.induct 1;
bd OR2_analz_sees_Enemy 4;
bd OR4_analz_sees_Enemy 6;
by (forward_tac [Reveal_message_form] 7);
by (REPEAT_FIRST (eresolve_tac [asm_rl, bexE, disjE] ORELSE' hyp_subst_tac));
by (ALLGOALS
    (asm_full_simp_tac 
     (!simpset addsimps ([analz_subset_parts RS contra_subsetD,
			  analz_insert_Key_newK] @ pushes)
               setloop split_tac [expand_if])));
(** LEVEL 6 **)
(*OR3*)
by (fast_tac (!claset addSIs [parts_insertI]
		      addEs [Says_imp_old_keys RS less_irrefl]
	              addss (!simpset)) 3);
(*Reveal case 2, OR4, OR2, Fake*) 
by (REPEAT_FIRST (resolve_tac [conjI, impI] ORELSE' enemy_analz_tac));
(*Reveal case 1*) (** LEVEL 8 **)
by (excluded_middle_tac "Aa : bad" 1);
(*But this contradicts Key(newK evt) ~: analz (sees Enemy evsa) *)
bd (Says_imp_sees_Enemy RS analz.Inj) 2;
by (fast_tac (!claset addSDs [analz.Decrypt] addss (!simpset)) 2);
(*So now we have  Aa ~: bad *)
by (dresolve_tac [OR4_imp_Says_Server_A] 1);
by (REPEAT (assume_tac 1));
by (fast_tac (!claset addDs [unique_session_keys] addss (!simpset)) 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);

goal thy 
 "!!evs. [| Says Server B \
\            {|NA, Crypt {|NA, K|} (shrK A),                      \
\                  Crypt {|NB, K|} (shrK B)|} : set_of_list evs;  \
\           Says A Enemy {|NA, K|} ~: set_of_list evs;            \
\           A ~: bad;  B ~: bad;  evs : otway |]                  \
\        ==> K ~: analz (sees Enemy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (fast_tac (!claset addSEs [lemma]) 1);
qed "Enemy_not_see_encrypted_key";



(** A session key uniquely identifies a pair of senders in the message
    encrypted by a good agent C. **)
goal thy 
 "!!evs. evs : otway ==>                                           \
\      EX A B. ALL C N.                                            \
\         C ~: bad -->                                             \
\         Crypt {|N, Key K|} (shrK C) : parts (sees Enemy evs) --> \
\         C=A | C=B";
by (Simp_tac 1);	(*Miniscoping*)
be otway.induct 1;
bd OR2_analz_sees_Enemy 4;
bd OR4_analz_sees_Enemy 6;
(*enemy_analz_tac just does not work here: it is an entirely different proof!*)
by (ALLGOALS 
    (asm_simp_tac (!simpset addsimps [all_conj_distrib, ex_disj_distrib,
				      imp_conj_distrib, parts_insert_sees,
				      parts_insert2])));
by (REPEAT_FIRST (etac exE));
(*OR3: extraction of K = newK evsa to global context...*) (** LEVEL 6 **)
by (excluded_middle_tac "K = newK evsa" 4);
by (Asm_simp_tac 4);
by (REPEAT (ares_tac [exI] 4));
(*...we prove this case by contradiction: the key is too new!*)
by (fast_tac (!claset addSEs partsEs
		      addEs [Says_imp_old_keys RS less_irrefl]
	              addss (!simpset)) 4);
(*Base, Fake, OR2, OR4*)
by (REPEAT_FIRST ex_strip_tac);
bd synth.Inj 4;
bd synth.Inj 3;
(*Now in effect there are three Fake cases*)
by (REPEAT_FIRST (best_tac (!claset addDs [impOfSubs Fake_parts_insert]
			            addss (!simpset))));
qed "key_identifies_senders";
