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
\        ==> EX K. EX NA. EX evs: otway lost.          \
\               Says B A {|Nonce NA, Crypt {|Nonce NA, Key K|} (shrK A)|} \
\                 : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (otway.Nil RS otway.OR1 RS otway.OR2 RS otway.OR3 RS otway.OR4) 2);
by (ALLGOALS (simp_tac (!simpset setsolver safe_solver)));
by (REPEAT_FIRST (resolve_tac [refl, conjI]));
by (ALLGOALS (fast_tac (!claset addss (!simpset setsolver safe_solver))));
result();


(**** Inductive proofs about otway ****)

goal thy "!!evs. lost' <= lost ==> otway lost' <= otway lost";
by (rtac subsetI 1);
by (etac otway.induct 1);
by (REPEAT_FIRST
    (best_tac (!claset addIs (impOfSubs (sees_mono RS analz_mono RS synth_mono)
                              :: otway.intrs))));
qed "otway_mono";

(*The Spy can see more than anybody else, except for their initial state*)
goal thy 
 "!!evs. evs : otway lost ==> \
\     sees lost A evs <= initState lost A Un sees lost Spy evs";
by (etac otway.induct 1);
by (ALLGOALS (fast_tac (!claset addDs [sees_Says_subset_insert RS subsetD] 
                                addss (!simpset))));
qed "sees_agent_subset_sees_Spy";

(*The Spy can see more than anybody else who's lost their key!*)
goal thy 
 "!!evs. evs : otway lost ==> \
\        A: lost --> A ~= Server --> sees lost A evs <= sees lost Spy evs";
by (etac otway.induct 1);
by (agent.induct_tac "A" 1);
by (auto_tac (!claset addDs [sees_Says_subset_insert RS subsetD], (!simpset)));
qed_spec_mp "sees_lost_agent_subset_sees_Spy";


(*Nobody sends themselves messages*)
goal thy "!!evs. evs : otway lost ==> ALL A X. Says A A X ~: set_of_list evs";
by (etac otway.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(** For reasoning about the encrypted portion of messages **)

goal thy "!!evs. Says A' B {|N, Agent A, Agent B, X|} : set_of_list evs ==> \
\                X : analz (sees lost Spy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]) 1);
qed "OR2_analz_sees_Spy";

goal thy "!!evs. Says S B {|N, X, X'|} : set_of_list evs ==> \
\                X : analz (sees lost Spy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]) 1);
qed "OR4_analz_sees_Spy";

goal thy "!!evs. Says B' A {|N, Crypt {|N,K|} K'|} : set_of_list evs ==> \
\                K : parts (sees lost Spy evs)";
by (fast_tac (!claset addSEs partsEs
                      addSDs [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "Reveal_parts_sees_Spy";

(*OR2_analz... and OR4_analz... let us treat those cases using the same 
  argument as for the Fake case.  This is possible for most, but not all,
  proofs: Fake does not invent new nonces (as in OR2), and of course Fake
  messages originate from the Spy. *)

bind_thm ("OR2_parts_sees_Spy",
          OR2_analz_sees_Spy RS (impOfSubs analz_subset_parts));
bind_thm ("OR4_parts_sees_Spy",
          OR4_analz_sees_Spy RS (impOfSubs analz_subset_parts));

(*We instantiate the variable to "lost".  Leaving it as a Var makes proofs
  harder to complete, since simplification does less for us.*)
val parts_Fake_tac = 
    let val tac = forw_inst_tac [("lost","lost")] 
    in  tac OR2_parts_sees_Spy 4 THEN 
        tac OR4_parts_sees_Spy 6 THEN
        tac Reveal_parts_sees_Spy 7
    end;


(** Theorems of the form X ~: parts (sees lost Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees lost another agent's shared key! (unless it is leaked at start)*)
goal thy 
 "!!evs. [| evs : otway lost;  A ~: lost |]    \
\        ==> Key (shrK A) ~: parts (sees lost Spy evs)";
by (etac otway.induct 1);
by parts_Fake_tac;
by (Auto_tac());
(*Deals with Fake message*)
by (best_tac (!claset addDs [impOfSubs analz_subset_parts,
                             impOfSubs Fake_parts_insert]) 1);
qed "Spy_not_see_shrK";

bind_thm ("Spy_not_analz_shrK",
          [analz_subset_parts, Spy_not_see_shrK] MRS contra_subsetD);

Addsimps [Spy_not_see_shrK, Spy_not_analz_shrK];

(*We go to some trouble to preserve R in the 3rd and 4th subgoals
  As usual fast_tac cannot be used because it uses the equalities too soon*)
val major::prems = 
goal thy  "[| Key (shrK A) : parts (sees lost Spy evs);       \
\             evs : otway lost;                                 \
\             A:lost ==> R                                  \
\           |] ==> R";
by (rtac ccontr 1);
by (rtac ([major, Spy_not_see_shrK] MRS rev_notE) 1);
by (swap_res_tac prems 2);
by (ALLGOALS (fast_tac (!claset addIs prems)));
qed "Spy_see_shrK_E";

bind_thm ("Spy_analz_shrK_E", 
          analz_subset_parts RS subsetD RS Spy_see_shrK_E);

AddSEs [Spy_see_shrK_E, Spy_analz_shrK_E];


(*** Future keys can't be seen or used! ***)

(*Nobody can have SEEN keys that will be generated in the future.
  This has to be proved anew for each protocol description,
  but should go by similar reasoning every time.  Hardest case is the
  standard Fake rule.  
      The Union over C is essential for the induction! *)
goal thy "!!evs. evs : otway lost ==> \
\                length evs <= length evs' --> \
\                          Key (newK evs') ~: (UN C. parts (sees lost C evs))";
by (etac otway.induct 1);
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
 "!!evs. [| evs : otway lost;  length evs <= length evs' |]    \
\        ==> Key (newK evs') ~: parts (sees lost C evs)";
by (fast_tac (!claset addDs [lemma]) 1);
qed "new_keys_not_seen";
Addsimps [new_keys_not_seen];

(*Another variant: old messages must contain old keys!*)
goal thy 
 "!!evs. [| Says A B X : set_of_list evs;  \
\           Key (newK evt) : parts {X};    \
\           evs : otway lost                 \
\        |] ==> length evt < length evs";
by (rtac ccontr 1);
by (dtac leI 1);
by (fast_tac (!claset addSDs [new_keys_not_seen, Says_imp_sees_Spy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_keys";


(*** Future nonces can't be seen or used! [proofs resemble those above] ***)

goal thy "!!evs. evs : otway lost ==> \
\                length evs <= length evt --> \
\                Nonce (newN evt) ~: (UN C. parts (sees lost C evs))";
by (etac otway.induct 1);
(*auto_tac does not work here, as it performs safe_tac first*)
by (ALLGOALS (asm_simp_tac (!simpset addsimps [parts_insert2]
                                     addcongs [disj_cong])));
by (REPEAT_FIRST (fast_tac (!claset 
                              addSEs partsEs
                              addSDs  [Says_imp_sees_Spy RS parts.Inj]
                              addDs  [impOfSubs analz_subset_parts,
                                      impOfSubs parts_insert_subset_Un,
                                      Suc_leD]
                              addss (!simpset))));
val lemma = result();

(*Variant needed for the main theorem below*)
goal thy 
 "!!evs. [| evs : otway lost;  length evs <= length evs' |]    \
\        ==> Nonce (newN evs') ~: parts (sees lost C evs)";
by (fast_tac (!claset addDs [lemma]) 1);
qed "new_nonces_not_seen";
Addsimps [new_nonces_not_seen];

(*Another variant: old messages must contain old nonces!*)
goal thy 
 "!!evs. [| Says A B X : set_of_list evs;  \
\           Nonce (newN evt) : parts {X};    \
\           evs : otway lost                 \
\        |] ==> length evt < length evs";
by (rtac ccontr 1);
by (dtac leI 1);
by (fast_tac (!claset addSDs [new_nonces_not_seen, Says_imp_sees_Spy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_nonces";


(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : otway lost ==> \
\                length evs <= length evs' --> \
\                newK evs' ~: keysFor (UN C. parts (sees lost C evs))";
by (etac otway.induct 1);
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
 "!!evs. [| evs : otway lost;  length evs <= length evs' |]    \
\        ==> newK evs' ~: keysFor (parts (sees lost C evs))";
by (fast_tac (!claset addSDs [lemma] addss (!simpset)) 1);
qed "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];


(** Lemmas concerning the form of items passed in messages **)


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
 "!!evs. evs : otway lost ==> \
\        (Crypt X (newK evt)) : parts (sees lost Spy evs) & \
\        Key K : parts {X} --> Key K : parts (sees lost Spy evs)";
by (etac otway.induct 1);
by parts_Fake_tac;
by (ALLGOALS Asm_simp_tac);
(*Deals with Faked messages*)
by (best_tac (!claset addSEs partsEs
                      addDs [impOfSubs parts_insert_subset_Un]
                      addss (!simpset)) 2);
(*Base case and Reveal*)
by (Auto_tac());
result();


(** Session keys are not used to encrypt other session keys **)

(*Describes the form of Key K when the following message is sent.  The use of
  "parts" strengthens the induction hyp for proving the Fake case.  The
  assumptions on A are needed to prevent its being a Faked message.  (Based
  on NS_Shared/Says_S_message_form) *)
goal thy
 "!!evs. evs: otway lost ==>                                           \
\          Crypt {|N, Key K|} (shrK A) : parts (sees lost Spy evs) & \
\          A ~: lost -->                                           \
\        (EX evt: otway lost. K = newK evt)";
by (etac otway.induct 1);
by parts_Fake_tac;
by (ALLGOALS Asm_simp_tac);
(*Deals with Fake message*)
by (best_tac (!claset addDs [impOfSubs analz_subset_parts,
                             impOfSubs Fake_parts_insert]) 2);
by (Auto_tac());
val lemma = result() RS mp;


(*EITHER describes the form of Key K when the following message is sent, 
  OR     reduces it to the Fake case.*)
goal thy 
 "!!evs. [| Says B' A {|N, Crypt {|N, Key K|} (shrK A)|} : set_of_list evs;  \
\           evs : otway lost |]                      \
\        ==> (EX evt: otway lost. K = newK evt)          \
\          | Key K : analz (sees lost Spy evs)";
by (excluded_middle_tac "A : lost" 1);
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]
                      addss (!simpset)) 2);
by (forward_tac [lemma] 1);
by (fast_tac (!claset addEs  partsEs
                      addSDs [Says_imp_sees_Spy RS parts.Inj]) 1);
by (Fast_tac 1);
qed "Reveal_message_form";


(*The equality makes the induction hypothesis easier to apply*)
goal thy  
 "!!evs. evs : otway lost ==> \
\  ALL K E. (Key K : analz (Key``(newK``E) Un (sees lost Spy evs))) = \
\           (K : newK``E | Key K : analz (sees lost Spy evs))";
by (etac otway.induct 1);
by (dtac OR2_analz_sees_Spy 4);
by (dtac OR4_analz_sees_Spy 6);
by (dtac Reveal_message_form 7);
by (REPEAT_FIRST (ares_tac [allI, analz_image_newK_lemma]));
by (REPEAT ((eresolve_tac [bexE, disjE] ORELSE' hyp_subst_tac) 7));
by (ALLGOALS (*Takes 28 secs*)
    (asm_simp_tac 
     (!simpset addsimps ([insert_Key_singleton, insert_Key_image, pushKey_newK]
                         @ pushes)
               setloop split_tac [expand_if])));
(** LEVEL 7 **)
(*Reveal case 2, OR4, OR2, Fake*) 
by (EVERY (map spy_analz_tac [7,5,3,2]));
(*Reveal case 1, OR3, Base*)
by (Auto_tac());
qed_spec_mp "analz_image_newK";


goal thy
 "!!evs. evs : otway lost ==>                               \
\        Key K : analz (insert (Key (newK evt)) (sees lost Spy evs)) = \
\        (K = newK evt | Key K : analz (sees lost Spy evs))";
by (asm_simp_tac (HOL_ss addsimps [pushKey_newK, analz_image_newK, 
                                   insert_Key_singleton]) 1);
by (Fast_tac 1);
qed "analz_insert_Key_newK";


(*** The Key K uniquely identifies the Server's  message. **)

fun ex_strip_tac i = REPEAT (ares_tac [exI, conjI] i) THEN assume_tac (i+1);

goal thy 
 "!!evs. evs : otway lost ==>                      \
\      EX A' B' NA' NB'. ALL A B NA NB.                    \
\       Says Server B \
\            {|NA, Crypt {|NA, K|} (shrK A),                      \
\                  Crypt {|NB, K|} (shrK B)|} : set_of_list evs --> \
\       A=A' & B=B' & NA=NA' & NB=NB'";
by (etac otway.induct 1);
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
\           evs : otway lost |]                                         \
\        ==> A=A' & B=B' & NA=NA' & NB=NB'";
by (dtac lemma 1);
by (REPEAT (etac exE 1));
(*Duplicate the assumption*)
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
by (fast_tac (!claset addSDs [spec]) 1);
qed "unique_session_keys";



(**** Towards proving stronger authenticity properties ****)

(*Only OR1 can have caused such a part of a message to appear.*)
goal thy 
 "!!evs. [| A ~: lost;  evs : otway lost |]               \
\        ==> Crypt {|NA, Agent A, Agent B|} (shrK A)        \
\             : parts (sees lost Spy evs) -->                  \
\            Says A B {|NA, Agent A, Agent B,               \
\                       Crypt {|NA, Agent A, Agent B|} (shrK A)|}  \
\             : set_of_list evs";
by (etac otway.induct 1);
by parts_Fake_tac;
by (ALLGOALS Asm_simp_tac);
(*Fake*)
by (best_tac (!claset addSDs [impOfSubs analz_subset_parts,
                              impOfSubs Fake_parts_insert]) 2);
by (Auto_tac());
qed_spec_mp "Crypt_imp_OR1";


(** The Nonce NA uniquely identifies A's  message. **)

goal thy 
 "!!evs. [| evs : otway lost; A ~: lost |]               \
\ ==> EX B'. ALL B.    \
\        Crypt {|NA, Agent A, Agent B|} (shrK A) : parts (sees lost Spy evs) --> \
\        B = B'";
by (etac otway.induct 1);
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
 "!!evs.[| Crypt {|NA, Agent A, Agent B|} (shrK A) : parts (sees lost Spy evs); \ 
\          Crypt {|NA, Agent A, Agent C|} (shrK A) : parts (sees lost Spy evs); \ 
\          evs : otway lost;  A ~: lost |]                                         \
\        ==> B = C";
by (dtac lemma 1);
by (assume_tac 1);
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
 "!!evs. [| A ~: lost;  evs : otway lost |]                            \
\        ==> Crypt {|NA, Agent A, Agent B|} (shrK A)             \
\             : parts (sees lost Spy evs) -->                       \
\            Crypt {|NA', NA, Agent A', Agent A|} (shrK A)       \
\             ~: parts (sees lost Spy evs)";
by (etac otway.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [parts_insert2])));
(*It is hard to generate this proof in a reasonable amount of time*)
by (step_tac (!claset addSEs [MPair_parts, nonce_not_seen_now]
                      addSDs [Says_imp_sees_Spy RS parts.Inj]) 1);
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
 "!!evs. [| A ~: lost;  A ~= Spy;  evs : otway lost |]                     \
\        ==> Crypt {|Nonce NA, Key K|} (shrK A) : parts (sees lost Spy evs) --> \
\            Says A B {|Nonce NA, Agent A, Agent B,                          \
\                       Crypt {|Nonce NA, Agent A, Agent B|} (shrK A)|}      \
\             : set_of_list evs -->                                          \
\            (EX NB. Says Server B                                           \
\                 {|Nonce NA,                                                \
\                   Crypt {|Nonce NA, Key K|} (shrK A),                      \
\                   Crypt {|Nonce NB, Key K|} (shrK B)|}                     \
\                   : set_of_list evs)";
by (etac otway.induct 1);
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
                      addDs [Says_imp_sees_Spy RS parts.Inj]) 2);
(*OR3*)  (** LEVEL 8 **)
by (ALLGOALS (asm_simp_tac (!simpset addsimps [ex_disj_distrib])));
by (step_tac (!claset delrules [disjCI, impCE]) 1);
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS parts.Inj]
                      addSEs [MPair_parts]
                      addEs  [unique_OR1_nonce]) 1);
by (fast_tac (!claset addSEs [MPair_parts]
                      addSDs [Says_imp_sees_Spy RS parts.Inj]
                      addEs  [no_nonce_OR1_OR2 RSN (2, rev_notE)]
                      delrules [conjI] (*stop split-up into 4 subgoals*)) 1);
qed_spec_mp "Crypt_imp_Server_msg";


(*Crucial property: if A receives B's OR4 message and the nonce NA agrees
  then the key really did come from the Server!  CANNOT prove this of the
  lost form of this protocol, even though we can prove
  Spy_not_see_encrypted_key*)
goal thy 
 "!!evs. [| A ~: lost;  A ~= Spy;  evs : otway lost |]                 \
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
by (etac otway.induct 1);
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
                      addDs [Says_imp_sees_Spy RS parts.Inj]) 3);
(** LEVEL 8 **)
(*Still subcases of Fake and OR4*)
by (fast_tac (!claset addSIs [Crypt_imp_Server_msg]
                      addDs  [impOfSubs analz_subset_parts]) 1);
by (fast_tac (!claset addSIs [Crypt_imp_Server_msg]
                      addEs  partsEs
                      addDs  [Says_imp_sees_Spy RS parts.Inj]) 1);
val OR4_imp_Says_Server_A = 
    result() RSN (2, rev_mp) RS mp |> standard;



(*Describes the form of K and NA when the Server sends this message.*)
goal thy 
 "!!evs. [| Says Server B \
\            {|NA, Crypt {|NA, K|} (shrK A),                      \
\                  Crypt {|NB, K|} (shrK B)|} : set_of_list evs;  \
\           evs : otway lost |]                                        \
\        ==> (EX evt: otway lost. K = Key(newK evt)) &                  \
\            (EX i. NA = Nonce i)";
by (etac rev_mp 1);
by (etac otway.induct 1);
by (ALLGOALS (fast_tac (!claset addIs [less_SucI] addss (!simpset))));
qed "Says_Server_message_form";


(** Crucial secrecy property: Spy does not see the keys sent in msg OR3 **)

goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  evs : otway lost;  evt : otway lost |] \
\        ==> Says Server B                                             \
\              {|Nonce NA, Crypt {|Nonce NA, Key(newK evt)|} (shrK A), \
\                Crypt {|NB, Key(newK evt)|} (shrK B)|} : set_of_list evs --> \
\            Says A Spy {|Nonce NA, Key(newK evt)|} ~: set_of_list evs --> \
\            Key(newK evt) ~: analz (sees lost Spy evs)";
by (etac otway.induct 1);
by (dtac OR2_analz_sees_Spy 4);
by (dtac OR4_analz_sees_Spy 6);
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
by (REPEAT_FIRST (resolve_tac [conjI, impI] ORELSE' spy_analz_tac));
(*Reveal case 1*) (** LEVEL 8 **)
by (excluded_middle_tac "Aa : lost" 1);
(*But this contradicts Key(newK evt) ~: analz (sees lost Spy evsa) *)
by (dtac (Says_imp_sees_Spy RS analz.Inj) 2);
by (fast_tac (!claset addSDs [analz.Decrypt] addss (!simpset)) 2);
(*So now we have  Aa ~: lost *)
by (dtac OR4_imp_Says_Server_A 1);
by (REPEAT (assume_tac 1));
by (fast_tac (!claset addDs [unique_session_keys] addss (!simpset)) 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);

goal thy 
 "!!evs. [| Says Server B \
\            {|NA, Crypt {|NA, K|} (shrK A),                      \
\                  Crypt {|NB, K|} (shrK B)|} : set_of_list evs;  \
\           Says A Spy {|NA, K|} ~: set_of_list evs;            \
\           A ~: lost;  B ~: lost;  evs : otway lost |]                  \
\        ==> K ~: analz (sees lost Spy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (fast_tac (!claset addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


goal thy 
 "!!evs. [| C ~: {A,B,Server}; \
\           Says Server B \
\            {|NA, Crypt {|NA, K|} (shrK A),                      \
\                  Crypt {|NB, K|} (shrK B)|} : set_of_list evs;  \
\           Says A Spy {|NA, K|} ~: set_of_list evs;            \
\           A ~: lost;  B ~: lost;  evs : otway lost |]                  \
\        ==> K ~: analz (sees lost C evs)";
by (rtac (subset_insertI RS sees_mono RS analz_mono RS contra_subsetD) 1);
by (rtac (sees_lost_agent_subset_sees_Spy RS analz_mono RS contra_subsetD) 1);
by (FIRSTGOAL (rtac Spy_not_see_encrypted_key));
by (REPEAT_FIRST (fast_tac (!claset addIs [otway_mono RS subsetD])));
qed "Agent_not_see_encrypted_key";


(** A session key uniquely identifies a pair of senders in the message
    encrypted by a good agent C. **)
goal thy 
 "!!evs. evs : otway lost ==>                                           \
\      EX A B. ALL C N.                                            \
\         C ~: lost -->                                             \
\         Crypt {|N, Key K|} (shrK C) : parts (sees lost Spy evs) --> \
\         C=A | C=B";
by (Simp_tac 1);        (*Miniscoping*)
by (etac otway.induct 1);
by (dres_inst_tac [("lost","lost")] OR2_analz_sees_Spy 4);
by (dres_inst_tac [("lost","lost")] OR4_analz_sees_Spy 6);
(*spy_analz_tac just does not work here: it is an entirely different proof!*)
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
by (dtac synth.Inj 4);
by (dtac synth.Inj 3);
(*Now in effect there are three Fake cases*)
by (REPEAT_FIRST (best_tac (!claset addDs [impOfSubs Fake_parts_insert]
                                    delrules [disjCI, disjE]
                                    addss (!simpset))));
qed "key_identifies_senders";


