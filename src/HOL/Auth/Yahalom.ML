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
Pretty.setdepth 20;


(*Weak liveness: there are traces that reach the end*)

goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\        ==> EX X NB K. EX evs: yahalom lost.          \
\               Says A B {|X, Crypt (Nonce NB) K|} : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (yahalom.Nil RS yahalom.YM1 RS yahalom.YM2 RS yahalom.YM3 RS yahalom.YM4) 2);
by (ALLGOALS (simp_tac (!simpset setsolver safe_solver)));
by (ALLGOALS Fast_tac);
result();


(**** Inductive proofs about yahalom ****)

(*Monotonicity*)
goal thy "!!evs. lost' <= lost ==> yahalom lost' <= yahalom lost";
by (rtac subsetI 1);
by (etac yahalom.induct 1);
by (REPEAT_FIRST
    (best_tac (!claset addIs (impOfSubs (sees_mono RS analz_mono RS synth_mono)
                              :: yahalom.intrs))));
qed "yahalom_mono";


(*Nobody sends themselves messages*)
goal thy "!!evs. evs: yahalom lost ==> ALL A X. Says A A X ~: set_of_list evs";
by (etac yahalom.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(** For reasoning about the encrypted portion of messages **)

(*Lets us treat YM4 using a similar argument as for the Fake case.*)
goal thy "!!evs. Says S A {|Crypt Y (shrK A), X|} : set_of_list evs ==> \
\                X : analz (sees lost Spy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]) 1);
qed "YM4_analz_sees_Spy";

bind_thm ("YM4_parts_sees_Spy",
          YM4_analz_sees_Spy RS (impOfSubs analz_subset_parts));

(*Relates to both YM4 and Oops*)
goal thy "!!evs. Says S A {|Crypt {|B, K, NA, NB|} (shrK A), X|} \
\                  : set_of_list evs ==> \
\                K : parts (sees lost Spy evs)";
by (fast_tac (!claset addSEs partsEs
                      addSDs [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "YM4_Key_parts_sees_Spy";

(*We instantiate the variable to "lost".  Leaving it as a Var makes proofs
  harder: the simplifier does less.*)
val parts_Fake_tac = 
    forw_inst_tac [("lost","lost")] YM4_parts_sees_Spy 6 THEN
    forw_inst_tac [("lost","lost")] YM4_Key_parts_sees_Spy 7;

(*For proving the easier theorems about X ~: parts (sees lost Spy evs) *)
fun parts_induct_tac i = SELECT_GOAL
    (DETERM (etac yahalom.induct 1 THEN parts_Fake_tac THEN
	     (*Fake message*)
	     TRY (best_tac (!claset addDs [impOfSubs analz_subset_parts,
					   impOfSubs Fake_parts_insert]
                                    addss (!simpset)) 2)) THEN
     (*Base case*)
     fast_tac (!claset addss (!simpset)) 1 THEN
     ALLGOALS Asm_simp_tac) i;


(** Theorems of the form X ~: parts (sees lost Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's shared key! (unless it's lost at start)*)
goal thy 
 "!!evs. evs : yahalom lost \
\        ==> (Key (shrK A) : parts (sees lost Spy evs)) = (A : lost)";
by (parts_induct_tac 1);
by (Auto_tac());
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

goal thy 
 "!!evs. evs : yahalom lost \
\        ==> (Key (shrK A) : analz (sees lost Spy evs)) = (A : lost)";
by (auto_tac(!claset addDs [impOfSubs analz_subset_parts], !simpset));
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

goal thy  "!!A. [| Key (shrK A) : parts (sees lost Spy evs);       \
\                  evs : yahalom lost |] ==> A:lost";
by (fast_tac (!claset addDs [Spy_see_shrK]) 1);
qed "Spy_see_shrK_D";

bind_thm ("Spy_analz_shrK_D", analz_subset_parts RS subsetD RS Spy_see_shrK_D);
AddSDs [Spy_see_shrK_D, Spy_analz_shrK_D];


(*** Future keys can't be seen or used! ***)

(*Nobody can have SEEN keys that will be generated in the future. *)
goal thy "!!evs. evs : yahalom lost ==> \
\                length evs <= length evs' --> \
\                Key (newK evs') ~: parts (sees lost Spy evs)";
by (parts_induct_tac 1);
by (REPEAT_FIRST (best_tac (!claset addDs [impOfSubs analz_subset_parts,
                                           impOfSubs parts_insert_subset_Un,
                                           Suc_leD]
                                    addss (!simpset))));
qed_spec_mp "new_keys_not_seen";
Addsimps [new_keys_not_seen];

(*Variant: old messages must contain old keys!*)
goal thy 
 "!!evs. [| Says A B X : set_of_list evs;  \
\           Key (newK evt) : parts {X};    \
\           evs : yahalom lost                 \
\        |] ==> length evt < length evs";
by (rtac ccontr 1);
by (dtac leI 1);
by (fast_tac (!claset addSDs [new_keys_not_seen, Says_imp_sees_Spy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_keys";


(*Ready-made for the classical reasoner*)
goal thy "!!evs. [| Says A B {|Crypt {|b, Key (newK evs), na, nb|} K, X|}  \
\                   : set_of_list evs;  evs : yahalom lost |]              \
\                ==> R";
by (fast_tac (!claset addEs [Says_imp_old_keys RS less_irrefl]
                      addss (!simpset addsimps [parts_insertI])) 1);
qed "Says_too_new_key";
AddSEs [Says_too_new_key];


(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : yahalom lost ==> \
\                length evs <= length evs' --> \
\                newK evs' ~: keysFor (parts (sees lost Spy evs))";
by (parts_induct_tac 1);
(*YM1, YM2 and YM3*)
by (EVERY (map (fast_tac (!claset addDs [Suc_leD] addss (!simpset))) [4,3,2]));
(*Fake and Oops: these messages send unknown (X) components*)
by (EVERY
    (map (fast_tac
	  (!claset addDs [impOfSubs analz_subset_parts,
			  impOfSubs (analz_subset_parts RS keysFor_mono),
			  impOfSubs (parts_insert_subset_Un RS keysFor_mono),
			  Suc_leD]
                   addss (!simpset))) [3,1]));
(*YM4: if K was used then it had been seen, contradicting new_keys_not_seen*)
by (fast_tac
      (!claset addSEs partsEs
               addSDs [Says_imp_sees_Spy RS parts.Inj]
               addEs [new_keys_not_seen RSN(2,rev_notE)]
               addDs [Suc_leD]) 1);
qed_spec_mp "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];


(*Describes the form of K when the Server sends this message.  Useful for
  Oops as well as main secrecy property.*)
goal thy 
 "!!evs. [| Says Server A                                           \
\            {|Crypt {|Agent B, K, NA, NB|} (shrK A), X|} : set_of_list evs; \
\           evs : yahalom lost |]                                   \
\        ==> (EX evt: yahalom lost. K = Key(newK evt))";
by (etac rev_mp 1);
by (etac yahalom.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "Says_Server_message_form";


(*For proofs involving analz.  We again instantiate the variable to "lost".*)
val analz_Fake_tac = 
    forw_inst_tac [("lost","lost")] YM4_analz_sees_Spy 6 THEN
    forw_inst_tac [("lost","lost")] Says_Server_message_form 7 THEN
    assume_tac 7 THEN Full_simp_tac 7 THEN
    REPEAT ((etac bexE ORELSE' hyp_subst_tac) 7);


(****
 The following is to prove theorems of the form

          Key K : analz (insert (Key (newK evt)) (sees lost Spy evs)) ==>
          Key K : analz (sees lost Spy evs)

 A more general formula must be proved inductively.

****)


(*NOT useful in this form, but it says that session keys are not used
  to encrypt messages containing other keys, in the actual protocol.
  We require that agents should behave like this subsequently also.*)
goal thy 
 "!!evs. evs : yahalom lost ==> \
\        (Crypt X (newK evt)) : parts (sees lost Spy evs) & \
\        Key K : parts {X} --> Key K : parts (sees lost Spy evs)";
by (etac yahalom.induct 1);
by parts_Fake_tac;
by (ALLGOALS Asm_simp_tac);
(*Deals with Faked messages*)
by (best_tac (!claset addSEs partsEs
                      addDs [impOfSubs parts_insert_subset_Un]
                      addss (!simpset)) 2);
(*Base case*)
by (Auto_tac());
result();


(** Session keys are not used to encrypt other session keys **)

goal thy  
 "!!evs. evs : yahalom lost ==> \
\  ALL K E. (Key K : analz (Key``(newK``E) Un (sees lost Spy evs))) = \
\           (K : newK``E | Key K : analz (sees lost Spy evs))";
by (etac yahalom.induct 1);
by analz_Fake_tac;
by (REPEAT_FIRST (resolve_tac [allI, analz_image_newK_lemma]));
by (ALLGOALS
    (asm_simp_tac 
     (!simpset addsimps ([insert_Key_singleton, insert_Key_image, pushKey_newK]
                         @ pushes)
               setloop split_tac [expand_if])));
(** LEVEL 5 **)
(*YM4, Fake*) 
by (EVERY (map spy_analz_tac [4, 2]));
(*Oops, YM3, Base*)
by (REPEAT (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1));
qed_spec_mp "analz_image_newK";

goal thy
 "!!evs. evs : yahalom lost ==>                               \
\        Key K : analz (insert (Key (newK evt)) (sees lost Spy evs)) = \
\        (K = newK evt | Key K : analz (sees lost Spy evs))";
by (asm_simp_tac (HOL_ss addsimps [analz_image_newK, 
                                   insert_Key_singleton]) 1);
by (Fast_tac 1);
qed "analz_insert_Key_newK";


(*** The Key K uniquely identifies the Server's  message. **)

goal thy 
 "!!evs. evs : yahalom lost ==>                                     \
\      EX A' B' NA' NB' X'. ALL A B NA NB X.                             \
\          Says Server A                                            \
\           {|Crypt {|Agent B, Key K, NA, NB|} (shrK A), X|}        \
\          : set_of_list evs --> A=A' & B=B' & NA=NA' & NB=NB' & X=X'";
by (etac yahalom.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib])));
by (Step_tac 1);
by (ex_strip_tac 2);
by (Fast_tac 2);
(*Remaining case: YM3*)
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
(*...we assume X is a very new message, and handle this case by contradiction*)
by (Fast_tac 1);  (*uses Says_too_new_key*)
val lemma = result();

goal thy 
"!!evs. [| Says Server A                                            \
\           {|Crypt {|Agent B, Key K, NA, NB|} (shrK A), X|}        \
\           : set_of_list evs;                                      \
\          Says Server A'                                           \
\           {|Crypt {|Agent B', Key K, NA', NB'|} (shrK A'), X'|}   \
\           : set_of_list evs;                                      \
\          evs : yahalom lost |]                                    \
\       ==> A=A' & B=B' & NA=NA' & NB=NB'";
by (dtac lemma 1);
by (REPEAT (etac exE 1));
(*Duplicate the assumption*)
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
by (fast_tac (!claset addSDs [spec]) 1);
qed "unique_session_keys";


(*If the encrypted message appears then it originated with the Server*)
goal thy
 "!!evs. [| Crypt {|Agent B, Key K, NA, NB|} (shrK A)                  \
\            : parts (sees lost Spy evs);                              \
\           A ~: lost;  evs : yahalom lost |]                          \
\         ==> Says Server A                                            \
\              {|Crypt {|Agent B, Key K, NA, NB|} (shrK A),            \
\                Crypt {|Agent A, Key K|} (shrK B)|}                   \
\             : set_of_list evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
qed "A_trust_YM3";


(** Crucial secrecy property: Spy does not see the keys sent in msg YM3 **)

goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  evs : yahalom lost |]         \
\        ==> Says Server A                                        \
\              {|Crypt {|Agent B, Key K, NA, NB|} (shrK A),       \
\                Crypt {|Agent A, Key K|} (shrK B)|}              \
\             : set_of_list evs -->                               \
\            Says A Spy {|NA, NB, Key K|} ~: set_of_list evs -->  \
\            Key K ~: analz (sees lost Spy evs)";
by (etac yahalom.induct 1);
by analz_Fake_tac;
by (ALLGOALS
    (asm_simp_tac 
     (!simpset addsimps ([analz_subset_parts RS contra_subsetD,
                          analz_insert_Key_newK] @ pushes)
               setloop split_tac [expand_if])));
(*YM3*)
by (Fast_tac 2);  (*uses Says_too_new_key*)
(*OR4, Fake*) 
by (REPEAT_FIRST (resolve_tac [conjI, impI] ORELSE' spy_analz_tac));
(*Oops*) (** LEVEL 6 **)
by (fast_tac (!claset delrules [disjE] 
		      addDs [unique_session_keys]
	              addss (!simpset)) 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);


(*Final version: Server's message in the most abstract form*)
goal thy 
 "!!evs. [| Says Server A                                               \
\            {|Crypt {|Agent B, K, NA, NB|} (shrK A),                   \
\              Crypt {|Agent A, K|} (shrK B)|} : set_of_list evs;       \
\           Says A Spy {|NA, NB, K|} ~: set_of_list evs;                \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |] ==>           \
\     K ~: analz (sees lost Spy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (fast_tac (!claset addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


goal thy 
 "!!evs. [| C ~: {A,B,Server};                                          \
\           Says Server A                                               \
\            {|Crypt {|Agent B, K, NA, NB|} (shrK A),                   \
\              Crypt {|Agent A, K|} (shrK B)|} : set_of_list evs;       \
\           Says A Spy {|NA, NB, K|} ~: set_of_list evs;                \
\           A ~: lost;  B ~: lost;  evs : yahalom lost |] ==>           \
\     K ~: analz (sees lost C evs)";
by (rtac (subset_insertI RS sees_mono RS analz_mono RS contra_subsetD) 1);
by (rtac (sees_lost_agent_subset_sees_Spy RS analz_mono RS contra_subsetD) 1);
by (FIRSTGOAL (rtac Spy_not_see_encrypted_key));
by (REPEAT_FIRST (fast_tac (!claset addIs [yahalom_mono RS subsetD])));
qed "Agent_not_see_encrypted_key";


(*** Security Guarantee for B upon receiving YM4 ***)

(*B knows, by the first part of A's message, that the Server distributed 
  the key for A and B.  But this part says nothing about nonces.*)
goal thy 
 "!!evs. [| Crypt {|Agent A, Key K|} (shrK B) : parts (sees lost Spy evs); \
\           B ~: lost;  evs : yahalom lost |]                           \
\        ==> EX NA NB. Says Server A                                    \
\                        {|Crypt {|Agent B, Key K,                      \
\                                  Nonce NA, Nonce NB|} (shrK A),       \
\                          Crypt {|Agent A, Key K|} (shrK B)|}          \
\                       : set_of_list evs";
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*YM3*)
by (Fast_tac 1);
qed "B_trusts_YM4_shrK";


(*** General properties of nonces ***)

goal thy "!!evs. evs : yahalom lost ==> \
\                length evs <= length evt --> \
\                Nonce (newN evt) ~: parts (sees lost Spy evs)";
by (parts_induct_tac 1);
by (REPEAT_FIRST (fast_tac (!claset 
                              addSEs partsEs
                              addSDs  [Says_imp_sees_Spy RS parts.Inj]
                              addDs  [impOfSubs analz_subset_parts,
                                      impOfSubs parts_insert_subset_Un,
                                      Suc_leD]
                              addss (!simpset))));
qed_spec_mp "new_nonces_not_seen";
Addsimps [new_nonces_not_seen];

(*Variant: old messages must contain old nonces!*)
goal thy 
 "!!evs. [| Says A B X : set_of_list evs;      \
\           Nonce (newN evt) : parts {X};      \
\           evs : yahalom lost                 \
\        |] ==> length evt < length evs";
by (rtac ccontr 1);
by (dtac leI 1);
by (fast_tac (!claset addSDs [new_nonces_not_seen, Says_imp_sees_Spy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_nonces";


(** The Nonce NB uniquely identifies B's message. **)

val nonce_not_seen_now = le_refl RSN (2, new_nonces_not_seen) RSN (2,rev_notE);

goal thy 
 "!!evs. evs : yahalom lost ==> EX NA' A' B'. ALL NA A B. \
\      Crypt {|Agent A, Nonce NA, NB|} (shrK B) : parts(sees lost Spy evs) \
\      --> B ~: lost --> NA = NA' & A = A' & B = B'";
by (parts_induct_tac 1);  (*100 seconds??*)
by (simp_tac (!simpset addsimps [all_conj_distrib]) 1); 
(*YM2: creation of new Nonce.  Move assertion into global context*)
by (expand_case_tac "NB = ?y" 1);
by (fast_tac (!claset addSEs (nonce_not_seen_now::partsEs)) 1);
val lemma = result();

goal thy 
 "!!evs.[| Crypt {|Agent A, Nonce NA, NB|} (shrK B) \
\                  : parts (sees lost Spy evs);         \
\          Crypt {|Agent A', Nonce NA', NB|} (shrK B') \
\                  : parts (sees lost Spy evs);         \
\          evs : yahalom lost;  B ~: lost;  B' ~: lost |]  \
\        ==> NA' = NA & A' = A & B' = B";
by (dtac lemma 1);
by (REPEAT (etac exE 1));
(*Duplicate the assumption*)
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
by (fast_tac (!claset addSDs [spec]) 1);
qed "unique_NB";

fun lost_tac s =
    case_tac ("(" ^ s ^ ") : lost") THEN'
    SELECT_GOAL 
      (REPEAT_DETERM (dtac (Says_imp_sees_Spy RS analz.Inj) 1) THEN
       REPEAT_DETERM (etac MPair_analz 1) THEN
       dres_inst_tac [("A", s)] Crypt_Spy_analz_lost 1 THEN
       assume_tac 1 THEN Fast_tac 1);

fun lost_tac s =
    case_tac ("(" ^ s ^ ") : lost") THEN'
    SELECT_GOAL 
      (REPEAT_DETERM (dtac (Says_imp_sees_Spy RS analz.Inj) 1) THEN
       REPEAT_DETERM (etac MPair_analz 1) THEN
       THEN_BEST_FIRST 
         (dres_inst_tac [("A", s)] Crypt_Spy_analz_lost 1 THEN assume_tac 1)
 	 (has_fewer_prems 1, size_of_thm)
	 (Step_tac 1));


(*Variant useful for proving secrecy of NB*)
goal thy 
 "!!evs.[| Says C D   {|X,  Crypt {|Agent A, Nonce NA, NB|} (shrK B)|} \
\          : set_of_list evs;  B ~: lost;         \
\          Says C' D' {|X', Crypt {|Agent A', Nonce NA', NB|} (shrK B')|} \
\          : set_of_list evs;                           \
\          NB ~: analz (sees lost Spy evs);             \
\          evs : yahalom lost |]  \
\        ==> NA' = NA & A' = A & B' = B";
by (lost_tac "B'" 1);
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS parts.Inj]
                      addSEs [MPair_parts]
                      addDs  [unique_NB]) 1);
qed "Says_unique_NB";

goal thy 
 "!!evs. [| B ~: lost;  evs : yahalom lost  |]               \
\ ==>  Nonce NB ~: analz (sees lost Spy evs) -->  \
\      Crypt {|Agent A, Nonce NA, Nonce NB|} (shrK B) : parts (sees lost Spy evs) \
\ --> Crypt {|Agent A', Nonce NB, NB'|} (shrK B') ~: parts (sees lost Spy evs)";
by (etac yahalom.induct 1);
by parts_Fake_tac;
by (REPEAT_FIRST 
    (rtac impI THEN' 
     dtac (sees_subset_sees_Says RS analz_mono RS contra_subsetD) THEN'
     mp_tac));
by (best_tac (!claset addDs [impOfSubs analz_subset_parts,
			     impOfSubs Fake_parts_insert]
	              addss (!simpset)) 2);
by (ALLGOALS Asm_simp_tac);
by (fast_tac (!claset addss (!simpset)) 1);
by (fast_tac (!claset addDs [Says_imp_sees_Spy RS analz.Inj]
	              addSIs [parts_insertI]
                      addSEs partsEs
                      addEs [Says_imp_old_nonces RS less_irrefl]
                      addss (!simpset)) 1);
val no_nonce_YM1_YM2 = standard (result() RS mp RSN (2, rev_mp) RS notE);



(**** Towards proving secrecy of Nonce NB ****)

(*B knows, by the second part of A's message, that the Server distributed 
  the key quoting nonce NB.  This part says nothing about agent names. 
  Secrecy of NB is crucial.*)
goal thy 
 "!!evs. evs : yahalom lost                                             \
\        ==> Nonce NB ~: analz (sees lost Spy evs) -->                  \
\            Crypt (Nonce NB) K : parts (sees lost Spy evs) -->         \
\            (EX A B NA. Says Server A                                  \
\                        {|Crypt {|Agent B, Key K,                      \
\                                  Nonce NA, Nonce NB|} (shrK A),       \
\                          Crypt {|Agent A, Key K|} (shrK B)|}          \
\                       : set_of_list evs)";
by (etac yahalom.induct 1);
by parts_Fake_tac;
by (fast_tac (!claset addss (!simpset)) 1);
by (REPEAT_FIRST
    (rtac impI THEN'
     dtac (sees_subset_sees_Says RS analz_mono RS contra_subsetD)));
by (ALLGOALS Asm_simp_tac);
(*Fake, YM3, YM4*)
by (Fast_tac 2);
by (fast_tac (!claset addSDs [impOfSubs Fake_parts_insert]
                      addDs [impOfSubs analz_subset_parts]
                      addss (!simpset)) 1);
(*YM4*)
by (Step_tac 1);
by (lost_tac "A" 1);
by (fast_tac (!claset addDs [Says_imp_sees_Spy RS parts.Inj RS parts.Fst RS
			     A_trust_YM3]) 1);
val B_trusts_YM4_newK = result() RS mp RSN (2, rev_mp);


(*This is the original version of the result above.  But it is of little
  value because it assumes secrecy of K, which we cannot be assured of
  until we know that K is fresh -- which we do not know at the point this
  result is applied.*)
goal thy 
 "!!evs. evs : yahalom lost                                             \
\        ==> Key K ~: analz (sees lost Spy evs) -->                     \
\            Crypt (Nonce NB) K : parts (sees lost Spy evs) -->         \
\            (EX A B NA. Says Server A                                  \
\                        {|Crypt {|Agent B, Key K,                      \
\                                  Nonce NA, Nonce NB|} (shrK A),       \
\                          Crypt {|Agent A, Key K|} (shrK B)|}          \
\                       : set_of_list evs)";
by (etac yahalom.induct 1);
by parts_Fake_tac;
by (fast_tac (!claset addss (!simpset)) 1);
by (TRYALL (rtac impI));
by (REPEAT_FIRST
    (dtac (sees_subset_sees_Says RS analz_mono RS contra_subsetD)));
by (ALLGOALS Asm_simp_tac);
(*Fake, YM3, YM4*)
by (fast_tac (!claset addSDs [Crypt_Fake_parts_insert]
                      addDs  [impOfSubs analz_subset_parts]) 1);
by (Fast_tac 1);
(*YM4*)
by (Step_tac 1);
by (lost_tac "A" 1);
by (fast_tac (!claset addDs [Says_imp_sees_Spy RS parts.Inj RS parts.Fst RS
			     A_trust_YM3]) 1);
result() RS mp RSN (2, rev_mp);


(*YM3 can only be triggered by YM2*)
goal thy 
 "!!evs. [| Says Server A                                           \
\            {|Crypt {|Agent B, k, na, nb|} (shrK A), X|} : set_of_list evs; \
\           evs : yahalom lost |]                                        \
\        ==> EX B'. Says B' Server                                       \
\                      {| Agent B, Crypt {|Agent A, na, nb|} (shrK B) |} \
\                   : set_of_list evs";
by (etac rev_mp 1);
by (etac yahalom.induct 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS Fast_tac);
qed "Says_Server_imp_YM2";


(** Dedicated tactics for the nonce secrecy proofs **)

val no_nonce_tac = SELECT_GOAL
   (REPEAT (resolve_tac [impI, notI] 1) THEN
    REPEAT (hyp_subst_tac 1) THEN
    etac (Says_imp_sees_Spy RS parts.Inj RS parts.Snd RS no_nonce_YM1_YM2) 1
    THEN
    etac (Says_imp_sees_Spy RS parts.Inj RS parts.Snd) 4
    THEN 
    REPEAT_FIRST assume_tac);

val not_analz_insert = subset_insertI RS analz_mono RS contra_subsetD;

fun grind_tac i = 
 SELECT_GOAL
  (REPEAT_FIRST 
   (Safe_step_tac ORELSE' (dtac spec THEN' mp_tac) ORELSE'
    assume_tac ORELSE'
    depth_tac (!claset delrules [conjI]
		       addSIs [exI, impOfSubs (subset_insertI RS analz_mono),
			       impOfSubs (Un_upper2 RS analz_mono)]) 2)) i;

(*The only nonces that can be found with the help of session keys are
  those distributed as nonce NB by the Server.  The form of the theorem
  recalls analz_image_newK, but it is much more complicated.*)
goal thy 
 "!!evs. evs : yahalom lost ==>                                           \
\     ALL E. Nonce NB : analz (Key``(newK``E) Un (sees lost Spy evs)) --> \
\     (EX K: newK``E. EX A B na X.                                        \
\            Says Server A                                                \
\                {|Crypt {|Agent B, Key K, na, Nonce NB|} (shrK A), X|}   \
\            : set_of_list evs)  |  Nonce NB : analz (sees lost Spy evs)";
by (etac yahalom.induct 1);
by analz_Fake_tac;
by (ALLGOALS  (*28 seconds*)
    (asm_simp_tac 
     (!simpset addsimps ([analz_subset_parts RS contra_subsetD,
                          analz_image_newK,
			  insert_Key_singleton, insert_Key_image]
			 @ pushes)
               setloop split_tac [expand_if])));
(*Base*)
by (fast_tac (!claset addss (!simpset)) 1);
(*Fake*) (** LEVEL 4 **)
by (spy_analz_tac 1);
(*YM1-YM3*) (*29 seconds*)
by (EVERY (map grind_tac [3,2,1]));
(*Oops*)
by (Full_simp_tac 2);
by (REPEAT ((eresolve_tac [bexE] ORELSE' hyp_subst_tac) 2));
by (simp_tac (!simpset addsimps [insert_Key_image]) 2);
by (grind_tac 2);
by (fast_tac (!claset delrules [bexI] 
		      addDs [unique_session_keys]
	              addss (!simpset)) 2);
(*YM4*)
(** LEVEL 11 **)
br (impI RS allI) 1;
by (dtac (impOfSubs Fake_analz_insert) 1 THEN etac synth.Inj 1 THEN 
    Fast_tac 1);
by (eres_inst_tac [("P","Nonce NB : ?HH")] rev_mp 1);
by (asm_simp_tac (!simpset addsimps [analz_image_newK]
	                   setloop split_tac [expand_if]) 1);
(** LEVEL 15 **)
by (grind_tac 1);
by (REPEAT (dtac not_analz_insert 1));
by (lost_tac "A" 1);
by (dtac (Says_imp_sees_Spy RS parts.Inj RS parts.Fst RS A_trust_YM3) 1
    THEN REPEAT (assume_tac 1));
by (fast_tac (!claset delrules [allE, conjI] addSIs [bexI, exI]) 1);
by (fast_tac (!claset delrules [conjI]
	              addIs [impOfSubs (subset_insertI RS analz_mono)]
		      addss (!simpset)) 1);
val Nonce_secrecy = result() RS spec RSN (2, rev_mp) |> standard;


(*Version required below: if NB can be decrypted using a session key then it
  was distributed with that key.  The more general form above is required
  for the induction to carry through.*)
goal thy 
 "!!evs. [| Says Server A                                                     \
\            {|Crypt {|Agent B, Key (newK evt), na, Nonce NB'|} (shrK A), X|} \
\           : set_of_list evs;                                                \
\           Nonce NB : analz (insert (Key (newK evt)) (sees lost Spy evs));   \
\           evs : yahalom lost |]                                             \
\ ==> Nonce NB : analz (sees lost Spy evs) | NB = NB'";
by (asm_full_simp_tac (HOL_ss addsimps [insert_Key_singleton]) 1);
by (dtac Nonce_secrecy 1 THEN assume_tac 1);
by (fast_tac (!claset addDs [unique_session_keys]
	              addss (!simpset)) 1);
val single_Nonce_secrecy = result();


goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  Spy: lost;  evs : yahalom lost |]  \
\ ==> Says B Server                                                    \
\          {|Agent B, Crypt {|Agent A, Nonce NA, Nonce NB|} (shrK B)|} \
\     : set_of_list evs -->                               \
\     (ALL k. Says A Spy {|Nonce NA, Nonce NB, k|} ~: set_of_list evs) -->  \
\     Nonce NB ~: analz (sees lost Spy evs)";
by (etac yahalom.induct 1);
by analz_Fake_tac;
by (ALLGOALS
    (asm_simp_tac 
     (!simpset addsimps ([analz_subset_parts RS contra_subsetD,
                          analz_insert_Key_newK] @ pushes)
               setloop split_tac [expand_if])));
by (fast_tac (!claset addSIs [parts_insertI]
                      addSEs partsEs
                      addEs [Says_imp_old_nonces RS less_irrefl]
                      addss (!simpset)) 2);
(*Proof of YM2*) (** LEVEL 5 **)
by (REPEAT (Safe_step_tac 2 ORELSE Fast_tac 2)); 
by (fast_tac (!claset addIs [parts_insertI]
                      addSEs partsEs
                      addEs [Says_imp_old_nonces RS less_irrefl]
                      addss (!simpset)) 3);
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]) 2);
(*Prove YM3 by showing that no NB can also be an NA*)
by (REPEAT (Safe_step_tac 2 ORELSE no_nonce_tac 2));
by (deepen_tac (!claset addDs [Says_unique_NB]) 1 2);
(*Fake*) (** LEVEL 10 **)
by (SELECT_GOAL (REPEAT (Safe_step_tac 1 ORELSE spy_analz_tac 1)) 1);
(*YM4*)
by (res_inst_tac [("x1","X")] (insert_commute RS ssubst) 1);
by (simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (SELECT_GOAL (REPEAT_FIRST (Safe_step_tac ORELSE' spy_analz_tac)) 1);
(** LEVEL 14 **)
by (lost_tac "Aa" 1);
bd (Says_imp_sees_Spy RS parts.Inj RS parts.Fst RS A_trust_YM3) 1;
by (forward_tac [Says_Server_message_form] 3);
by (forward_tac [Says_Server_imp_YM2] 4);
by (REPEAT_FIRST ((eresolve_tac [asm_rl, bexE, exE, disjE])));
by (Full_simp_tac 1);
(** LEVEL 20 **)
by (REPEAT_FIRST hyp_subst_tac);
by (lost_tac "Ba" 1);
bd (Says_imp_sees_Spy RS parts.Inj RS parts.Snd RS unique_NB) 1;
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS parts.Inj]
                      addSEs [MPair_parts]) 1);
by (REPEAT (assume_tac 1 ORELSE Safe_step_tac 1)); 
bd Spy_not_see_encrypted_key 1;
by (REPEAT (assume_tac 1 ORELSE Fast_tac 1)); 
by (spy_analz_tac 1);
(*Oops case*) (** LEVEL 28 **)
by (full_simp_tac (!simpset addsimps [all_conj_distrib]) 1);
by (step_tac (!claset delrules [disjE, conjI]) 1);
by (forward_tac [Says_Server_imp_YM2] 1 THEN assume_tac 1 THEN etac exE 1);
by (expand_case_tac "NB = NBa" 1);
by (deepen_tac (!claset addDs [Says_unique_NB]) 1 1);
br conjI 1;
by (no_nonce_tac 1);
(** LEVEL 35 **)
by (thin_tac "?PP|?QQ" 1);  (*subsumption!*)
by (fast_tac (!claset addSDs [single_Nonce_secrecy]) 1);
val Spy_not_see_NB = result() RSN(2,rev_mp) RSN(2,rev_mp) |> standard;


(*What can B deduce from receipt of YM4?  Note how the two components of
  the message contribute to a single conclusion about the Server's message.
  It's annoying that the "Says A Spy" assumption must quantify over 
  ALL POSSIBLE keys instead of our particular K (though at least the
  nonces are forced to agree with NA and NB). *)
goal thy 
 "!!evs. [| Says B Server                                        \
\            {|Agent B, Crypt {|Agent A, Nonce NA, Nonce NB|} (shrK B)|}  \
\           : set_of_list evs;       \
\           Says A' B {|Crypt {|Agent A, Key K|} (shrK B),              \
\                       Crypt (Nonce NB) K|} : set_of_list evs;         \
\           ALL k. Says A Spy {|Nonce NA, Nonce NB, k|} ~: set_of_list evs; \
\           A ~: lost;  B ~: lost;  Spy: lost;  evs : yahalom lost |]   \
\         ==> Says Server A                                       \
\                     {|Crypt {|Agent B, Key K,                         \
\                               Nonce NA, Nonce NB|} (shrK A),          \
\                       Crypt {|Agent A, Key K|} (shrK B)|}             \
\                   : set_of_list evs";
by (forward_tac [Spy_not_see_NB] 1 THEN REPEAT (assume_tac 1));
by (etac (Says_imp_sees_Spy RS parts.Inj RS MPair_parts) 1 THEN
    dtac B_trusts_YM4_shrK 1);
bd B_trusts_YM4_newK 3;
by (REPEAT_FIRST (eresolve_tac [asm_rl, exE]));
by (forward_tac [Says_Server_imp_YM2] 1 THEN assume_tac 1);
by (dresolve_tac [unique_session_keys] 1 THEN REPEAT (assume_tac 1));
by (deepen_tac (!claset addDs [Says_unique_NB] addss (!simpset)) 0 1);
qed "B_trust_YM4";



