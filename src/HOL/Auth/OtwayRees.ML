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
Pretty.setdepth 15;


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
by (REPEAT_FIRST (fast_tac (!claset addss (!simpset setsolver safe_solver))));
result();


(**** Inductive proofs about otway ****)

(*Monotonicity*)
goal thy "!!evs. lost' <= lost ==> otway lost' <= otway lost";
by (rtac subsetI 1);
by (etac otway.induct 1);
by (REPEAT_FIRST
    (best_tac (!claset addIs (impOfSubs (sees_mono RS analz_mono RS synth_mono)
                              :: otway.intrs))));
qed "otway_mono";

(*Nobody sends themselves messages*)
goal thy "!!evs. evs : otway lost ==> ALL A X. Says A A X ~: set_of_list evs";
by (etac otway.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(** For reasoning about the encrypted portion of messages **)

goal thy "!!evs. Says A' B {|N, Agent A, Agent B, X|} : set_of_list evs \
\                ==> X : analz (sees lost Spy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]) 1);
qed "OR2_analz_sees_Spy";

goal thy "!!evs. Says S B {|N, X, X'|} : set_of_list evs \
\                ==> X : analz (sees lost Spy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]) 1);
qed "OR4_analz_sees_Spy";

goal thy "!!evs. Says Server B {|NA, X, Crypt {|NB,K|} K'|} : set_of_list evs \
\                 ==> K : parts (sees lost Spy evs)";
by (fast_tac (!claset addSEs partsEs
                      addSDs [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "Oops_parts_sees_Spy";

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
        tac Oops_parts_sees_Spy 7
    end;

(*For proving the easier theorems about X ~: parts (sees lost Spy evs) *)
fun parts_induct_tac i = SELECT_GOAL
    (DETERM (etac otway.induct 1 THEN parts_Fake_tac THEN
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
 "!!evs. evs : otway lost \
\        ==> (Key (shrK A) : parts (sees lost Spy evs)) = (A : lost)";
by (parts_induct_tac 1);
by (Auto_tac());
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

goal thy 
 "!!evs. evs : otway lost \
\        ==> (Key (shrK A) : analz (sees lost Spy evs)) = (A : lost)";
by (auto_tac(!claset addDs [impOfSubs analz_subset_parts], !simpset));
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

goal thy  "!!A. [| Key (shrK A) : parts (sees lost Spy evs);       \
\                  evs : otway lost |] ==> A:lost";
by (fast_tac (!claset addDs [Spy_see_shrK]) 1);
qed "Spy_see_shrK_D";

bind_thm ("Spy_analz_shrK_D", analz_subset_parts RS subsetD RS Spy_see_shrK_D);
AddSDs [Spy_see_shrK_D, Spy_analz_shrK_D];


(*** Future keys can't be seen or used! ***)

(*Nobody can have SEEN keys that will be generated in the future. *)
goal thy "!!evs. evs : otway lost ==> \
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
\           evs : otway lost                 \
\        |] ==> length evt < length evs";
by (rtac ccontr 1);
by (dtac leI 1);
by (fast_tac (!claset addSDs [new_keys_not_seen, Says_imp_sees_Spy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_keys";


(*** Future nonces can't be seen or used! ***)

goal thy "!!evs. evs : otway lost ==> \
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
goal thy "!!evs. [| Says A B X : set_of_list evs;    \
\                   Nonce (newN evt) : parts {X};    \
\                   evs : otway lost                 \
\                |] ==> length evt < length evs";
by (rtac ccontr 1);
by (dtac leI 1);
by (fast_tac (!claset addSDs [new_nonces_not_seen, Says_imp_sees_Spy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_nonces";


(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : otway lost ==>          \
\                length evs <= length evs' --> \
\                newK evs' ~: keysFor (parts (sees lost Spy evs))";
by (parts_induct_tac 1);
(*OR1 and OR3*)
by (EVERY (map (fast_tac (!claset addDs [Suc_leD] addss (!simpset))) [4,2]));
(*Fake, OR2, OR4: these messages send unknown (X) components*)
by (REPEAT
    (best_tac
      (!claset addDs [impOfSubs (analz_subset_parts RS keysFor_mono),
                      impOfSubs (parts_insert_subset_Un RS keysFor_mono),
                      Suc_leD]
               addEs [new_keys_not_seen RS not_parts_not_analz RSN(2,rev_notE)]
               addss (!simpset)) 1));
qed_spec_mp "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];



(*** Proofs involving analz ***)

(*Describes the form of K and NA when the Server sends this message.  Also
  for Oops case.*)
goal thy 
 "!!evs. [| Says Server B \
\            {|NA, X, Crypt {|NB, K|} (shrK B)|} : set_of_list evs;  \
\           evs : otway lost |]                                   \
\        ==> (EX evt: otway lost. K = Key(newK evt)) &            \
\            (EX i. NA = Nonce i) & (EX j. NB = Nonce j)";
by (etac rev_mp 1);
by (etac otway.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "Says_Server_message_form";


(*For proofs involving analz.  We again instantiate the variable to "lost".*)
val analz_Fake_tac = 
    dres_inst_tac [("lost","lost")] OR2_analz_sees_Spy 4 THEN 
    dres_inst_tac [("lost","lost")] OR4_analz_sees_Spy 6 THEN
    forw_inst_tac [("lost","lost")] Says_Server_message_form 7 THEN
    assume_tac 7 THEN Full_simp_tac 7 THEN
    REPEAT ((eresolve_tac [bexE, exE, conjE] ORELSE' hyp_subst_tac) 7);


(****
 The following is to prove theorems of the form

          Key K : analz (insert (Key (newK evt)) (sees lost Spy evs)) ==>
          Key K : analz (sees lost Spy evs)

 A more general formula must be proved inductively.
****)


(** Session keys are not used to encrypt other session keys **)

(*The equality makes the induction hypothesis easier to apply*)
goal thy  
 "!!evs. evs : otway lost ==> \
\  ALL K E. (Key K : analz (Key``(newK``E) Un (sees lost Spy evs))) = \
\           (K : newK``E | Key K : analz (sees lost Spy evs))";
by (etac otway.induct 1);
by analz_Fake_tac;
by (REPEAT_FIRST (ares_tac [allI, analz_image_newK_lemma]));
by (ALLGOALS (*Takes 14 secs*)
    (asm_simp_tac 
     (!simpset addsimps ([insert_Key_singleton, insert_Key_image, pushKey_newK]
                         @ pushes)
               setloop split_tac [expand_if])));
(*OR4, OR2, Fake*) 
by (EVERY (map spy_analz_tac [5,3,2]));
(*Oops, OR3, Base*)
by (REPEAT (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1));
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

goal thy 
 "!!evs. evs : otway lost ==>                                                 \
\   EX B' NA' NB' X'. ALL B NA NB X.                                          \
\     Says Server B {|NA, X, Crypt {|NB, K|} (shrK B)|} : set_of_list evs --> \
\     B=B' & NA=NA' & NB=NB' & X=X'";
by (etac otway.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib])));
by (Step_tac 1);
(*Remaining cases: OR3 and OR4*)
by (ex_strip_tac 2);
by (Fast_tac 2);
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
(*...we assume X is a very new message, and handle this case by contradiction*)
by (fast_tac (!claset addEs [Says_imp_old_keys RS less_irrefl]
                      delrules [conjI]    (*prevent split-up into 4 subgoals*)
                      addss (!simpset addsimps [parts_insertI])) 1);
val lemma = result();

goal thy 
 "!!evs. [| Says Server B {|NA, X, Crypt {|NB, K|} (shrK B)|}      \
\            : set_of_list evs;                                    \ 
\           Says Server B' {|NA',X',Crypt {|NB',K|} (shrK B')|}    \
\            : set_of_list evs;                                    \
\           evs : otway lost |] ==> X=X' & B=B' & NA=NA' & NB=NB'";
by (dtac lemma 1);
by (REPEAT (etac exE 1));
(*Duplicate the assumption*)
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
by (fast_tac (!claset addSDs [spec]) 1);
qed "unique_session_keys";



(**** Authenticity properties relating to NA ****)

(*Only OR1 can have caused such a part of a message to appear.*)
goal thy 
 "!!evs. [| A ~: lost;  evs : otway lost |]                        \
\        ==> Crypt {|NA, Agent A, Agent B|} (shrK A)               \
\             : parts (sees lost Spy evs) -->                      \
\            Says A B {|NA, Agent A, Agent B,                      \
\                       Crypt {|NA, Agent A, Agent B|} (shrK A)|}  \
\             : set_of_list evs";
by (parts_induct_tac 1);
qed_spec_mp "Crypt_imp_OR1";


(** The Nonce NA uniquely identifies A's message. **)

goal thy 
 "!!evs. [| evs : otway lost; A ~: lost |]               \
\ ==> EX B'. ALL B.    \
\        Crypt {|NA, Agent A, Agent B|} (shrK A) : parts (sees lost Spy evs) \
\        --> B = B'";
by (parts_induct_tac 1);
by (simp_tac (!simpset addsimps [all_conj_distrib]) 1); 
(*OR1: creation of new Nonce.  Move assertion into global context*)
by (expand_case_tac "NA = ?y" 1);
by (best_tac (!claset addSEs partsEs
                      addEs  [new_nonces_not_seen RSN(2,rev_notE)]) 1);
val lemma = result();

goal thy 
 "!!evs.[| Crypt {|NA, Agent A, Agent B|} (shrK A): parts(sees lost Spy evs); \
\          Crypt {|NA, Agent A, Agent C|} (shrK A): parts(sees lost Spy evs); \
\          evs : otway lost;  A ~: lost |]                                    \
\        ==> B = C";
by (dtac lemma 1);
by (assume_tac 1);
by (etac exE 1);
(*Duplicate the assumption*)
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
by (fast_tac (!claset addSDs [spec]) 1);
qed "unique_NA";


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
by (parts_induct_tac 1);
by (REPEAT (fast_tac (!claset addSEs (partsEs@[nonce_not_seen_now])
                              addSDs  [impOfSubs parts_insert_subset_Un]
                              addss (!simpset)) 1));
qed_spec_mp"no_nonce_OR1_OR2";


(*Crucial property: If the encrypted message appears, and A has used NA
  to start a run, then it originated with the Server!*)
goal thy 
 "!!evs. [| A ~: lost;  A ~= Spy;  evs : otway lost |]                 \
\    ==> Crypt {|NA, Key K|} (shrK A) : parts (sees lost Spy evs)      \
\        --> Says A B {|NA, Agent A, Agent B,                          \
\                       Crypt {|NA, Agent A, Agent B|} (shrK A)|}      \
\             : set_of_list evs -->                                    \
\            (EX NB. Says Server B                                     \
\                 {|NA,                                                \
\                   Crypt {|NA, Key K|} (shrK A),                      \
\                   Crypt {|NB, Key K|} (shrK B)|}                     \
\                   : set_of_list evs)";
by (parts_induct_tac 1);
(*OR1: it cannot be a new Nonce, contradiction.*)
by (fast_tac (!claset addSIs [parts_insertI]
                      addSEs partsEs
                      addEs [Says_imp_old_nonces RS less_irrefl]
                      addss (!simpset)) 1);
(*OR3 and OR4*) 
(*OR4*)
by (REPEAT (Safe_step_tac 2));
by (REPEAT (best_tac (!claset addSDs [parts_cut]) 3));
by (fast_tac (!claset addSIs [Crypt_imp_OR1]
                      addEs  partsEs
                      addDs [Says_imp_sees_Spy RS parts.Inj]) 2);
(*OR3*)  (** LEVEL 5 **)
by (asm_simp_tac (!simpset addsimps [ex_disj_distrib]) 1);
by (step_tac (!claset delrules [disjCI, impCE]) 1);
by (fast_tac (!claset addSEs [MPair_parts]
                      addSDs [Says_imp_sees_Spy RS parts.Inj]
                      addEs  [no_nonce_OR1_OR2 RSN (2, rev_notE)]
                      delrules [conjI] (*stop split-up into 4 subgoals*)) 2);
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS parts.Inj]
                      addSEs [MPair_parts]
                      addEs  [unique_NA]) 1);
qed_spec_mp "NA_Crypt_imp_Server_msg";


(*Corollary: if A receives B's OR4 message and the nonce NA agrees
  then the key really did come from the Server!  CANNOT prove this of the
  bad form of this protocol, even though we can prove
  Spy_not_see_encrypted_key*)
goal thy 
 "!!evs. [| Says B' A {|NA, Crypt {|NA, Key K|} (shrK A)|}         \
\            : set_of_list evs;                                    \
\           Says A B {|NA, Agent A, Agent B,                       \
\                      Crypt {|NA, Agent A, Agent B|} (shrK A)|}   \
\            : set_of_list evs;                                    \
\           A ~: lost;  A ~= Spy;  evs : otway lost |]             \
\        ==> EX NB. Says Server B                                  \
\                     {|NA,                                        \
\                       Crypt {|NA, Key K|} (shrK A),              \
\                       Crypt {|NB, Key K|} (shrK B)|}             \
\                       : set_of_list evs";
by (fast_tac (!claset addSIs [NA_Crypt_imp_Server_msg]
                      addEs  partsEs
                      addDs  [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "A_trust_OR4";


(** Crucial secrecy property: Spy does not see the keys sent in msg OR3
    Does not in itself guarantee security: an attack could violate 
    the premises, e.g. by having A=Spy **)

goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  evs : otway lost |]                    \
\        ==> Says Server B                                                 \
\              {|NA, Crypt {|NA, Key K|} (shrK A),                         \
\                Crypt {|NB, Key K|} (shrK B)|} : set_of_list evs -->      \
\            Says B Spy {|NA, NB, Key K|} ~: set_of_list evs -->           \
\            Key K ~: analz (sees lost Spy evs)";
by (etac otway.induct 1);
by analz_Fake_tac;
by (ALLGOALS
    (asm_full_simp_tac 
     (!simpset addsimps ([analz_subset_parts RS contra_subsetD,
                          analz_insert_Key_newK] @ pushes)
               setloop split_tac [expand_if])));
(*OR3*)
by (fast_tac (!claset addEs [Says_imp_old_keys RS less_irrefl]
                      addss (!simpset addsimps [parts_insert2])) 3);
(*OR4, OR2, Fake*) 
by (REPEAT_FIRST (resolve_tac [conjI, impI] ORELSE' spy_analz_tac));
(*Oops*) (** LEVEL 5 **)
by (fast_tac (!claset delrules [disjE]
                      addDs [unique_session_keys] addss (!simpset)) 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);

goal thy 
 "!!evs. [| Says Server B \
\            {|NA, Crypt {|NA, K|} (shrK A),                             \
\                  Crypt {|NB, K|} (shrK B)|} : set_of_list evs;         \
\           Says B Spy {|NA, NB, K|} ~: set_of_list evs;                 \
\           A ~: lost;  B ~: lost;  evs : otway lost |]                  \
\        ==> K ~: analz (sees lost Spy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (fast_tac (!claset addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


goal thy 
 "!!evs. [| C ~: {A,B,Server};                                           \
\           Says Server B                                                \
\            {|NA, Crypt {|NA, K|} (shrK A),                             \
\                  Crypt {|NB, K|} (shrK B)|} : set_of_list evs;         \
\           Says B Spy {|NA, NB, K|} ~: set_of_list evs;                 \
\           A ~: lost;  B ~: lost;  evs : otway lost |]                  \
\        ==> K ~: analz (sees lost C evs)";
by (rtac (subset_insertI RS sees_mono RS analz_mono RS contra_subsetD) 1);
by (rtac (sees_lost_agent_subset_sees_Spy RS analz_mono RS contra_subsetD) 1);
by (FIRSTGOAL (rtac Spy_not_see_encrypted_key));
by (REPEAT_FIRST (fast_tac (!claset addIs [otway_mono RS subsetD])));
qed "Agent_not_see_encrypted_key";


(**** Authenticity properties relating to NB ****)

(*Only OR2 can have caused such a part of a message to appear.  We do not
  know anything about X: it does NOT have to have the right form.*)
goal thy 
 "!!evs. [| B ~: lost;  evs : otway lost |]                    \
\        ==> Crypt {|NA, NB, Agent A, Agent B|} (shrK B)       \
\             : parts (sees lost Spy evs) -->                  \
\            (EX X. Says B Server                              \
\             {|NA, Agent A, Agent B, X,                       \
\               Crypt {|NA, NB, Agent A, Agent B|} (shrK B)|}  \
\             : set_of_list evs)";
by (parts_induct_tac 1);
by (auto_tac (!claset, !simpset addcongs [conj_cong]));
bind_thm ("Crypt_imp_OR2", result() RSN (2,rev_mp) RS exE);


(** The Nonce NB uniquely identifies B's  message. **)

goal thy 
 "!!evs. [| evs : otway lost; B ~: lost |]               \
\ ==> EX NA' A'. ALL NA A.                               \
\      Crypt {|NA, NB, Agent A, Agent B|} (shrK B) : parts(sees lost Spy evs) \
\      --> NA = NA' & A = A'";
by (parts_induct_tac 1);
by (simp_tac (!simpset addsimps [all_conj_distrib]) 1); 
(*OR2: creation of new Nonce.  Move assertion into global context*)
by (expand_case_tac "NB = ?y" 1);
by (fast_tac (!claset addSEs (nonce_not_seen_now::partsEs)) 1);
val lemma = result();

goal thy 
 "!!evs.[| Crypt {|NA, NB, Agent A, Agent B|} (shrK B) \
\                  : parts(sees lost Spy evs);         \
\          Crypt {|NC, NB, Agent C, Agent B|} (shrK B) \
\                  : parts(sees lost Spy evs);         \
\          evs : otway lost;  B ~: lost |]             \
\        ==> NC = NA & C = A";
by (dtac lemma 1);
by (assume_tac 1);
by (REPEAT (etac exE 1));
(*Duplicate the assumption*)
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
by (fast_tac (!claset addSDs [spec]) 1);
qed "unique_NB";


(*If the encrypted message appears, and B has used Nonce NB,
  then it originated with the Server!*)
goal thy 
 "!!evs. [| B ~: lost;  B ~= Spy;  evs : otway lost |]                   \
\    ==> Crypt {|NB, Key K|} (shrK B) : parts (sees lost Spy evs)        \
\        --> (ALL X'. Says B Server                                      \
\                       {|NA, Agent A, Agent B, X',                      \
\                         Crypt {|NA, NB, Agent A, Agent B|} (shrK B)|}  \
\             : set_of_list evs                                          \
\             --> Says Server B                                          \
\                  {|NA, Crypt {|NA, Key K|} (shrK A),                   \
\                        Crypt {|NB, Key K|} (shrK B)|}                  \
\                   : set_of_list evs)";
by (parts_induct_tac 1);
(*OR1: it cannot be a new Nonce, contradiction.*)
by (fast_tac (!claset addSIs [parts_insertI]
                      addSEs partsEs
                      addEs [Says_imp_old_nonces RS less_irrefl]
                      addss (!simpset)) 1);
(*OR4*)
by (fast_tac (!claset addSEs [MPair_parts, Crypt_imp_OR2]) 2);
(*OR3*)
by (step_tac (!claset delrules [disjCI, impCE]) 1);
by (fast_tac (!claset delrules [conjI] (*stop split-up*)) 3); 
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS parts.Inj]
                      addSEs [MPair_parts]
                      addDs  [unique_NB]) 2);
by (fast_tac (!claset addSEs [MPair_parts]
                      addSDs [Says_imp_sees_Spy RS parts.Inj]
                      addSEs  [no_nonce_OR1_OR2 RSN (2, rev_notE)]
                      delrules [conjI, impCE] (*stop split-up*)) 1);
qed_spec_mp "NB_Crypt_imp_Server_msg";


(*Guarantee for B: if it gets a message with matching NB then the Server
  has sent the correct message.*)
goal thy 
 "!!evs. [| B ~: lost;  B ~= Spy;  evs : otway lost;               \
\           Says S B {|NA, X, Crypt {|NB, Key K|} (shrK B)|}       \
\            : set_of_list evs;                                    \
\           Says B Server {|NA, Agent A, Agent B, X',              \
\                           Crypt {|NA, NB, Agent A, Agent B|}     \
\                                 (shrK B)|}                       \
\            : set_of_list evs |]                                  \
\        ==> Says Server B                                         \
\                 {|NA,                                            \
\                   Crypt {|NA, Key K|} (shrK A),                  \
\                   Crypt {|NB, Key K|} (shrK B)|}                 \
\                   : set_of_list evs";
by (fast_tac (!claset addSIs [NB_Crypt_imp_Server_msg]
                      addEs  partsEs
                      addDs  [Says_imp_sees_Spy RS parts.Inj]) 1);
qed "B_trust_OR3";


B_trust_OR3 RS Spy_not_see_encrypted_key;


goal thy 
 "!!evs. [| B ~: lost;  evs : otway lost |]                    \
\        ==> Says Server B                                                 \
\              {|NA, Crypt {|NA, Key K|} (shrK A),                         \
\                Crypt {|NB, Key K|} (shrK B)|} : set_of_list evs -->      \
\            (EX X. Says B Server {|NA, Agent A, Agent B, X,              \
\                            Crypt {|NA, NB, Agent A, Agent B|}     \
\                                  (shrK B)|}                       \
\            : set_of_list evs)";
by (etac otway.induct 1);
by (Auto_tac());
bd (Says_imp_sees_Spy RS parts.Inj) 1;
by (fast_tac (!claset addSEs [MPair_parts, Crypt_imp_OR2]) 1);
bind_thm ("OR3_imp_OR2", result() RSN (2,rev_mp) RS exE);


(*After getting and checking OR4, agent A can trust that B has been active.
  We could probably prove that X has the expected form, but that is not
  strictly necessary for authentication.*)
goal thy 
 "!!evs. [| Says B' A {|NA, Crypt {|NA, Key K|} (shrK A)|}         \
\            : set_of_list evs;                                    \
\           Says A B {|NA, Agent A, Agent B,                       \
\                      Crypt {|NA, Agent A, Agent B|} (shrK A)|}   \
\            : set_of_list evs;                                    \
\           A ~: lost;  A ~= Spy;  B ~: lost;  evs : otway lost |] \
\        ==> EX NB X. Says B Server {|NA, Agent A, Agent B, X,     \
\                            Crypt {|NA, NB, Agent A, Agent B|}    \
\                                  (shrK B)|}                      \
\            : set_of_list evs";
by (fast_tac (!claset addSDs  [A_trust_OR4]
	              addSEs [OR3_imp_OR2]) 1);
qed "A_auths_B";


