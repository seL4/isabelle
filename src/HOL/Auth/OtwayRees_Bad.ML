(*  Title:      HOL/Auth/OtwayRees_Bad
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "otway" for the Otway-Rees protocol.

The FAULTY version omitting encryption of Nonce NB, as suggested on page 247 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)

This file illustrates the consequences of such errors.  We can still prove
impressive-looking properties such as Spy_not_see_encrypted_key, yet the
protocol is open to a middleperson attack.  Attempting to prove some key lemmas
indicates the possibility of this attack.
*)

open OtwayRees_Bad;

proof_timing:=true;
HOL_quantifiers := false;


(*Weak liveness: there are traces that reach the end*)
goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\        ==> EX K. EX NA. EX evs: otway.          \
\               Says B A {|Nonce NA, Crypt {|Nonce NA, Key K|} (shrK A)|} \
\                 : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (otway.Nil RS otway.OR1 RS otway.OR2 RS otway.OR3 RS otway.OR4) 2);
by (ALLGOALS (simp_tac (!simpset setsolver safe_solver)));
by (REPEAT_FIRST (resolve_tac [refl, conjI]));
by (ALLGOALS (fast_tac (!claset addss (!simpset setsolver safe_solver))));
result();


(**** Inductive proofs about otway ****)

(*The Spy can see more than anybody else, except for their initial state*)
goal thy 
 "!!evs. evs : otway ==> \
\     sees lost A evs <= initState lost A Un sees lost Spy evs";
by (etac otway.induct 1);
by (ALLGOALS (fast_tac (!claset addDs [sees_Says_subset_insert RS subsetD] 
                                addss (!simpset))));
qed "sees_agent_subset_sees_Spy";


(*Nobody sends themselves messages*)
goal thy "!!evs. evs : otway ==> ALL A X. Says A A X ~: set_of_list evs";
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

val parts_Fake_tac = 
    forward_tac [OR2_parts_sees_Spy] 4 THEN 
    forward_tac [OR4_parts_sees_Spy] 6 THEN
    forward_tac [Oops_parts_sees_Spy] 7;

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
 "!!evs. evs : otway \
\        ==> (Key (shrK A) : parts (sees lost Spy evs)) = (A : lost)";
by (parts_induct_tac 1);
by (Auto_tac());
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

goal thy 
 "!!evs. evs : otway \
\        ==> (Key (shrK A) : analz (sees lost Spy evs)) = (A : lost)";
by (auto_tac(!claset addDs [impOfSubs analz_subset_parts], !simpset));
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

goal thy  "!!A. [| Key (shrK A) : parts (sees lost Spy evs);       \
\                  evs : otway |] ==> A:lost";
by (fast_tac (!claset addDs [Spy_see_shrK]) 1);
qed "Spy_see_shrK_D";

bind_thm ("Spy_analz_shrK_D", analz_subset_parts RS subsetD RS Spy_see_shrK_D);
AddSDs [Spy_see_shrK_D, Spy_analz_shrK_D];


(*** Future keys can't be seen or used! ***)

(*Nobody can have SEEN keys that will be generated in the future.
  This has to be proved anew for each protocol description,
  but should go by similar reasoning every time.  Hardest case is the
  standard Fake rule.  
      The Union over C is essential for the induction! *)
goal thy "!!evs. evs : otway ==> \
\                length evs <= length evs' --> \
\                          Key (newK evs') ~: (UN C. parts (sees lost C evs))";
by (parts_induct_tac 1);
by (REPEAT_FIRST (best_tac (!claset addDs [impOfSubs analz_subset_parts,
                                       impOfSubs parts_insert_subset_Un,
                                       Suc_leD]
                                addss (!simpset))));
val lemma = result();

(*Variant needed for the main theorem below*)
goal thy 
 "!!evs. [| evs : otway;  length evs <= length evs' |]    \
\        ==> Key (newK evs') ~: parts (sees lost C evs)";
by (fast_tac (!claset addDs [lemma]) 1);
qed "new_keys_not_seen";
Addsimps [new_keys_not_seen];

(*Another variant: old messages must contain old keys!*)
goal thy 
 "!!evs. [| Says A B X : set_of_list evs;  \
\           Key (newK evt) : parts {X};    \
\           evs : otway                 \
\        |] ==> length evt < length evs";
by (rtac ccontr 1);
by (dtac leI 1);
by (fast_tac (!claset addSDs [new_keys_not_seen, Says_imp_sees_Spy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_keys";


(*** Future nonces can't be seen or used! [proofs resemble those above] ***)

goal thy "!!evs. evs : otway ==> \
\                length evs <= length evs' --> \
\                      Nonce (newN evs') ~: (UN C. parts (sees lost C evs))";
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
 "!!evs. [| evs : otway;  length evs <= length evs' |]    \
\        ==> Nonce (newN evs') ~: parts (sees lost C evs)";
by (fast_tac (!claset addDs [lemma]) 1);
qed "new_nonces_not_seen";
Addsimps [new_nonces_not_seen];

(*Another variant: old messages must contain old nonces!*)
goal thy 
 "!!evs. [| Says A B X : set_of_list evs;  \
\           Nonce (newN evt) : parts {X};    \
\           evs : otway                 \
\        |] ==> length evt < length evs";
by (rtac ccontr 1);
by (dtac leI 1);
by (fast_tac (!claset addSDs [new_nonces_not_seen, Says_imp_sees_Spy]
                      addIs  [impOfSubs parts_mono]) 1);
qed "Says_imp_old_nonces";


(*Nobody can have USED keys that will be generated in the future.
  ...very like new_keys_not_seen*)
goal thy "!!evs. evs : otway ==> \
\                length evs <= length evs' --> \
\                newK evs' ~: keysFor (UN C. parts (sees lost C evs))";
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
val lemma = result();

goal thy 
 "!!evs. [| evs : otway;  length evs <= length evs' |]    \
\        ==> newK evs' ~: keysFor (parts (sees lost C evs))";
by (fast_tac (!claset addSDs [lemma] addss (!simpset)) 1);
qed "new_keys_not_used";

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
\           evs : otway |]                                   \
\        ==> (EX evt: otway. K = Key(newK evt)) &            \
\            (EX i. NA = Nonce i) & (EX j. NB = Nonce j)";
by (etac rev_mp 1);
by (etac otway.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "Says_Server_message_form";


(*For proofs involving analz.*)
val analz_Fake_tac = 
    dtac OR2_analz_sees_Spy 4 THEN 
    dtac OR4_analz_sees_Spy 6 THEN
    forward_tac [Says_Server_message_form] 7 THEN
    assume_tac 7 THEN Full_simp_tac 7 THEN
    REPEAT ((eresolve_tac [bexE, exE, conjE] ORELSE' hyp_subst_tac) 7);


(****
 The following is to prove theorems of the form

          Key K : analz (insert (Key (newK evt)) (sees lost Spy evs)) ==>
          Key K : analz (sees lost Spy evs)

 A more general formula must be proved inductively.

****)


(** Session keys are not used to encrypt other session keys **)

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
\  ALL K E. (Key K : analz (Key``(newK``E) Un (sees lost Spy evs))) = \
\           (K : newK``E | Key K : analz (sees lost Spy evs))";
by (etac otway.induct 1);
by analz_Fake_tac;
by (REPEAT_FIRST (ares_tac [allI, lemma]));
by (ALLGOALS
    (asm_simp_tac 
     (!simpset addsimps ([insert_Key_singleton, insert_Key_image, pushKey_newK]
                         @ pushes)
               setloop split_tac [expand_if])));
(** LEVEL 7 **)
(*OR4, OR2, Fake*) 
by (EVERY (map spy_analz_tac [5,3,2]));
(*Oops, OR3, Base*)
by (REPEAT (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1));
qed_spec_mp "analz_image_newK";


goal thy
 "!!evs. evs : otway ==>                               \
\        Key K : analz (insert (Key (newK evt)) (sees lost Spy evs)) = \
\        (K = newK evt | Key K : analz (sees lost Spy evs))";
by (asm_simp_tac (HOL_ss addsimps [pushKey_newK, analz_image_newK, 
                                   insert_Key_singleton]) 1);
by (Fast_tac 1);
qed "analz_insert_Key_newK";


(*** The Key K uniquely identifies the Server's  message. **)

goal thy 
 "!!evs. evs : otway ==>                                                 \
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
\           evs : otway |] ==> X=X' & B=B' & NA=NA' & NB=NB'";
by (dtac lemma 1);
by (REPEAT (etac exE 1));
(*Duplicate the assumption*)
by (forw_inst_tac [("psi", "ALL C.?P(C)")] asm_rl 1);
by (fast_tac (!claset addSDs [spec]) 1);
qed "unique_session_keys";


(*Crucial security property, but not itself enough to guarantee correctness!*)
goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  evs : otway;  evt : otway |]        \
\    ==> Says Server B \
\          {|NA, Crypt {|NA, Key K|} (shrK A), \
\            Crypt {|NB, Key K|} (shrK B)|} : set_of_list evs --> \
\            Says B Spy {|NA, NB, Key K|} ~: set_of_list evs -->           \
\        Key K ~: analz (sees lost Spy evs)";
by (etac otway.induct 1);
by analz_Fake_tac;
by (ALLGOALS
    (asm_full_simp_tac 
     (!simpset addsimps ([analz_subset_parts RS contra_subsetD,
                          analz_insert_Key_newK] @ pushes)
               setloop split_tac [expand_if])));
(*OR3*)
by (fast_tac (!claset addSIs [parts_insertI]
                      addEs [Says_imp_old_keys RS less_irrefl]
                      addss (!simpset addsimps [parts_insert2])) 3);
(*OR4, OR2, Fake*) 
by (REPEAT_FIRST (resolve_tac [conjI, impI] ORELSE' spy_analz_tac));
(*Oops*) (** LEVEL 5 **)
by (fast_tac (!claset delrules [disjE]
		      addDs [unique_session_keys] addss (!simpset)) 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);


goal thy 
 "!!evs. [| Says Server B                                         \
\            {|NA, Crypt {|NA, K|} (shrK A),                      \
\                  Crypt {|NB, K|} (shrK B)|} : set_of_list evs;  \
\            Says B Spy {|NA, NB, K|} ~: set_of_list evs;         \
\           A ~: lost;  B ~: lost;  evs : otway |]                \
\        ==> K ~: analz (sees lost Spy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (fast_tac (!claset addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


(*** Attempting to prove stronger properties ***)

(*Only OR1 can have caused such a part of a message to appear.
  I'm not sure why A ~= B premise is needed: OtwayRees.ML doesn't need it.
  Perhaps it's because OR2 has two similar-looking encrypted messages in
	this version.*)
goal thy 
 "!!evs. [| A ~: lost;  A ~= B; evs : otway |]                 \
\        ==> Crypt {|NA, Agent A, Agent B|} (shrK A)           \
\             : parts (sees lost Spy evs) -->                  \
\            Says A B {|NA, Agent A, Agent B,                  \
\                       Crypt {|NA, Agent A, Agent B|} (shrK A)|}  \
\             : set_of_list evs";
by (parts_induct_tac 1);
by (Fast_tac 1);
qed_spec_mp "Crypt_imp_OR1";


(*Crucial property: If the encrypted message appears, and A has used NA
  to start a run, then it originated with the Server!*)
(*Only it is FALSE.  Somebody could make a fake message to Server
          substituting some other nonce NA' for NB.*)
goal thy 
 "!!evs. [| A ~: lost;  A ~= Spy;  evs : otway |]                        \
\        ==> Crypt {|NA, Key K|} (shrK A) : parts (sees lost Spy evs) --> \
\            Says A B {|NA, Agent A, Agent B,                  \
\                       Crypt {|NA, Agent A, Agent B|} (shrK A)|}  \
\             : set_of_list evs -->                            \
\            (EX B NB. Says Server B                           \
\                 {|NA,                                        \
\                   Crypt {|NA, Key K|} (shrK A),              \
\                   Crypt {|NB, Key K|} (shrK B)|}             \
\                   : set_of_list evs)";
by (parts_induct_tac 1);
(*OR1: it cannot be a new Nonce, contradiction.*)
by (fast_tac (!claset addSIs [parts_insertI]
                      addSEs partsEs
                      addEs [Says_imp_old_nonces RS less_irrefl]
                      addss (!simpset)) 1);
(*OR4*)
by (REPEAT (Safe_step_tac 2));
by (REPEAT (best_tac (!claset addSDs [parts_cut]) 3));
by (fast_tac (!claset addSIs [Crypt_imp_OR1]
                      addEs  partsEs
                      addDs [Says_imp_sees_Spy RS parts.Inj]) 2);
(*OR3*)  (** LEVEL 5 **)
by (ALLGOALS (asm_simp_tac (!simpset addsimps [ex_disj_distrib])));
by (step_tac (!claset delrules [disjCI, impCE]) 1);
(*The hypotheses at this point suggest an attack in which nonce NA is used
  in two different roles:
          Says B' Server
           {|Nonce NAa, Agent Aa, Agent A,
             Crypt {|Nonce NAa, Agent Aa, Agent A|} (shrK Aa), Nonce NA,
             Crypt {|Nonce NAa, Agent Aa, Agent A|} (shrK A)|}
          : set_of_list evsa;
          Says A B
           {|Nonce NA, Agent A, Agent B,
             Crypt {|Nonce NA, Agent A, Agent B|} (shrK A)|}
          : set_of_list evsa 
*)
writeln "GIVE UP! on NA_Crypt_imp_Server_msg";


(*Thus the key property A_can_trust probably fails too.*)
