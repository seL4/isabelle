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

(*Replacing the variable by a constant improves search speed by 50%!*)
val Says_imp_sees_Spy' = read_instantiate [("lost","lost")] Says_imp_sees_Spy;


(*A "possibility property": there are traces that reach the end*)
goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\        ==> EX K. EX NA. EX evs: otway lost.          \
\               Says B A {|Nonce NA, Crypt (shrK A) {|Nonce NA, Key K|}|} \
\                 : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (otway.Nil RS otway.OR1 RS otway.OR2 RS otway.OR3 RS otway.OR4) 2);
by possibility_tac;
result();


(**** Inductive proofs about otway ****)

(*Monotonicity*)
goal thy "!!evs. lost' <= lost ==> otway lost' <= otway lost";
by (rtac subsetI 1);
by (etac otway.induct 1);
by (ALLGOALS
    (blast_tac (!claset addIs (impOfSubs(sees_mono RS analz_mono RS synth_mono)
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
by (blast_tac (!claset addSDs [Says_imp_sees_Spy' RS analz.Inj]) 1);
qed "OR2_analz_sees_Spy";

goal thy "!!evs. Says S' B {|N, X, Crypt (shrK B) X'|} : set_of_list evs \
\                ==> X : analz (sees lost Spy evs)";
by (blast_tac (!claset addSDs [Says_imp_sees_Spy' RS analz.Inj]) 1);
qed "OR4_analz_sees_Spy";

goal thy "!!evs. Says Server B {|NA, X, Crypt K' {|NB,K|}|} : set_of_list evs \
\                 ==> K : parts (sees lost Spy evs)";
by (blast_tac (!claset addSEs sees_Spy_partsEs) 1);
qed "Oops_parts_sees_Spy";

(*OR2_analz... and OR4_analz... let us treat those cases using the same 
  argument as for the Fake case.  This is possible for most, but not all,
  proofs: Fake does not invent new nonces (as in OR2), and of course Fake
  messages originate from the Spy. *)

bind_thm ("OR2_parts_sees_Spy",
          OR2_analz_sees_Spy RS (impOfSubs analz_subset_parts));
bind_thm ("OR4_parts_sees_Spy",
          OR4_analz_sees_Spy RS (impOfSubs analz_subset_parts));

(*For proving the easier theorems about X ~: parts (sees lost Spy evs).
  We instantiate the variable to "lost" since leaving it as a Var would
  interfere with simplification.*)
val parts_induct_tac = 
    let val tac = forw_inst_tac [("lost","lost")] 
    in  etac otway.induct	   1 THEN 
	tac OR2_parts_sees_Spy     4 THEN 
        tac OR4_parts_sees_Spy     6 THEN
        tac Oops_parts_sees_Spy    7 THEN
	prove_simple_subgoals_tac  1
    end;


(** Theorems of the form X ~: parts (sees lost Spy evs) imply that NOBODY
    sends messages containing X! **)


(*Spy never sees another agent's shared key! (unless it's lost at start)*)
goal thy 
 "!!evs. evs : otway lost \
\        ==> (Key (shrK A) : parts (sees lost Spy evs)) = (A : lost)";
by parts_induct_tac;
by (Fake_parts_insert_tac 1);
by (Blast_tac 1);
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
by (blast_tac (!claset addDs [Spy_see_shrK]) 1);
qed "Spy_see_shrK_D";

bind_thm ("Spy_analz_shrK_D", analz_subset_parts RS subsetD RS Spy_see_shrK_D);
AddSDs [Spy_see_shrK_D, Spy_analz_shrK_D];


(*Nobody can have used non-existent keys!*)
goal thy "!!evs. evs : otway lost ==>          \
\         Key K ~: used evs --> K ~: keysFor (parts (sees lost Spy evs))";
by parts_induct_tac;
(*Fake*)
by (best_tac
      (!claset addIs [impOfSubs analz_subset_parts]
               addDs [impOfSubs (analz_subset_parts RS keysFor_mono),
                      impOfSubs (parts_insert_subset_Un RS keysFor_mono)]
               addss (!simpset)) 1);
by (ALLGOALS Blast_tac);
qed_spec_mp "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];



(*** Proofs involving analz ***)

(*Describes the form of K and NA when the Server sends this message.  Also
  for Oops case.*)
goal thy 
 "!!evs. [| Says Server B                                                 \
\            {|NA, X, Crypt (shrK B) {|NB, Key K|}|} : set_of_list evs;   \
\           evs : otway lost |]                                           \
\     ==> K ~: range shrK & (EX i. NA = Nonce i) & (EX j. NB = Nonce j)";
by (etac rev_mp 1);
by (etac otway.induct 1);
by (ALLGOALS Simp_tac);
by (ALLGOALS Blast_tac);
qed "Says_Server_message_form";


(*For proofs involving analz.  We again instantiate the variable to "lost".*)
val analz_sees_tac = 
    dres_inst_tac [("lost","lost")] OR2_analz_sees_Spy 4 THEN 
    dres_inst_tac [("lost","lost")] OR4_analz_sees_Spy 6 THEN
    forw_inst_tac [("lost","lost")] Says_Server_message_form 7 THEN
    assume_tac 7 THEN
    REPEAT ((eresolve_tac [exE, conjE] ORELSE' hyp_subst_tac) 7);


(****
 The following is to prove theorems of the form

  Key K : analz (insert (Key KAB) (sees lost Spy evs)) ==>
  Key K : analz (sees lost Spy evs)

 A more general formula must be proved inductively.
****)


(** Session keys are not used to encrypt other session keys **)

(*The equality makes the induction hypothesis easier to apply*)
goal thy  
 "!!evs. evs : otway lost ==>                                         \
\  ALL K KK. KK <= Compl (range shrK) -->                      \
\            (Key K : analz (Key``KK Un (sees lost Spy evs))) = \
\            (K : KK | Key K : analz (sees lost Spy evs))";
by (etac otway.induct 1);
by analz_sees_tac;
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_freshK_lemma ));
by (ALLGOALS (asm_simp_tac analz_image_freshK_ss));
(*Fake*) 
by (spy_analz_tac 2);
(*Base*)
by (Blast_tac 1);
qed_spec_mp "analz_image_freshK";


goal thy
 "!!evs. [| evs : otway lost;  KAB ~: range shrK |] ==>             \
\        Key K : analz (insert (Key KAB) (sees lost Spy evs)) = \
\        (K = KAB | Key K : analz (sees lost Spy evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(*** The Key K uniquely identifies the Server's  message. **)

goal thy 
 "!!evs. evs : otway lost ==>                                                 \
\   EX B' NA' NB' X'. ALL B NA NB X.                                          \
\     Says Server B {|NA, X, Crypt (shrK B) {|NB, K|}|} : set_of_list evs --> \
\     B=B' & NA=NA' & NB=NB' & X=X'";
by (etac otway.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib])));
by (Step_tac 1);
(*Remaining cases: OR3 and OR4*)
by (ex_strip_tac 2);
by (Best_tac 2);
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
(*...we assume X is a recent message, and handle this case by contradiction*)
by (blast_tac (!claset addSEs sees_Spy_partsEs
                       delrules [conjI] (*no split-up into 4 subgoals*)) 1);
val lemma = result();

goal thy 
 "!!evs. [| Says Server B {|NA, X, Crypt (shrK B) {|NB, K|}|}      \
\            : set_of_list evs;                                    \ 
\           Says Server B' {|NA',X',Crypt (shrK B') {|NB',K|}|}    \
\            : set_of_list evs;                                    \
\           evs : otway lost |] ==> X=X' & B=B' & NA=NA' & NB=NB'";
by (prove_unique_tac lemma 1);
qed "unique_session_keys";



(**** Authenticity properties relating to NA ****)

(*Only OR1 can have caused such a part of a message to appear.*)
goal thy 
 "!!evs. [| A ~: lost;  evs : otway lost |]                        \
\        ==> Crypt (shrK A) {|NA, Agent A, Agent B|}               \
\             : parts (sees lost Spy evs) -->                      \
\            Says A B {|NA, Agent A, Agent B,                      \
\                       Crypt (shrK A) {|NA, Agent A, Agent B|}|}  \
\             : set_of_list evs";
by parts_induct_tac;
by (Fake_parts_insert_tac 1);
qed_spec_mp "Crypt_imp_OR1";


(** The Nonce NA uniquely identifies A's message. **)

goal thy 
 "!!evs. [| evs : otway lost; A ~: lost |]               \
\ ==> EX B'. ALL B.    \
\        Crypt (shrK A) {|NA, Agent A, Agent B|} : parts (sees lost Spy evs) \
\        --> B = B'";
by parts_induct_tac;
by (Fake_parts_insert_tac 1);
by (simp_tac (!simpset addsimps [all_conj_distrib]) 1); 
(*OR1: creation of new Nonce.  Move assertion into global context*)
by (expand_case_tac "NA = ?y" 1);
by (blast_tac (!claset addSEs sees_Spy_partsEs) 1);
val lemma = result();

goal thy 
 "!!evs.[| Crypt (shrK A) {|NA, Agent A, Agent B|}: parts(sees lost Spy evs); \
\          Crypt (shrK A) {|NA, Agent A, Agent C|}: parts(sees lost Spy evs); \
\          evs : otway lost;  A ~: lost |]                                    \
\        ==> B = C";
by (prove_unique_tac lemma 1);
qed "unique_NA";


(*It is impossible to re-use a nonce in both OR1 and OR2.  This holds because
  OR2 encrypts Nonce NB.  It prevents the attack that can occur in the
  over-simplified version of this protocol: see OtwayRees_Bad.*)
goal thy 
 "!!evs. [| A ~: lost;  evs : otway lost |]                      \
\        ==> Crypt (shrK A) {|NA, Agent A, Agent B|}             \
\             : parts (sees lost Spy evs) -->                    \
\            Crypt (shrK A) {|NA', NA, Agent A', Agent A|}       \
\             ~: parts (sees lost Spy evs)";
by parts_induct_tac;
by (Fake_parts_insert_tac 1);
by (REPEAT (blast_tac (!claset addSEs sees_Spy_partsEs
                               addSDs  [impOfSubs parts_insert_subset_Un]) 1));
qed_spec_mp"no_nonce_OR1_OR2";


(*Crucial property: If the encrypted message appears, and A has used NA
  to start a run, then it originated with the Server!*)
goal thy 
 "!!evs. [| A ~: lost;  A ~= Spy;  evs : otway lost |]                 \
\    ==> Crypt (shrK A) {|NA, Key K|} : parts (sees lost Spy evs)      \
\        --> Says A B {|NA, Agent A, Agent B,                          \
\                       Crypt (shrK A) {|NA, Agent A, Agent B|}|}      \
\             : set_of_list evs -->                                    \
\            (EX NB. Says Server B                                     \
\                 {|NA,                                                \
\                   Crypt (shrK A) {|NA, Key K|},                      \
\                   Crypt (shrK B) {|NB, Key K|}|}                     \
\                   : set_of_list evs)";
by parts_induct_tac;
by (Fake_parts_insert_tac 1);
(*OR1: it cannot be a new Nonce, contradiction.*)
by (blast_tac (!claset addSIs [parts_insertI] addSEs sees_Spy_partsEs) 1);
(*OR3 and OR4*) 
(*OR4*)
by (REPEAT (Safe_step_tac 2));
by (REPEAT (blast_tac (!claset addSDs [parts_cut]) 3));
by (fast_tac (!claset addSIs [Crypt_imp_OR1]
                      addEs  sees_Spy_partsEs) 2);
(*OR3*)  (** LEVEL 5 **)
by (asm_simp_tac (!simpset addsimps [ex_disj_distrib]) 1);
by (step_tac (!claset delrules [disjCI, impCE]) 1);
by (blast_tac (!claset addSEs [MPair_parts]
                      addSDs [Says_imp_sees_Spy' RS parts.Inj]
                      addEs  [no_nonce_OR1_OR2 RSN (2, rev_notE)]
                      delrules [conjI] (*stop split-up into 4 subgoals*)) 2);
by (blast_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
                      addSEs [MPair_parts]
                      addIs  [unique_NA]) 1);
qed_spec_mp "NA_Crypt_imp_Server_msg";


(*Corollary: if A receives B's OR4 message and the nonce NA agrees
  then the key really did come from the Server!  CANNOT prove this of the
  bad form of this protocol, even though we can prove
  Spy_not_see_encrypted_key*)
goal thy 
 "!!evs. [| Says B' A {|NA, Crypt (shrK A) {|NA, Key K|}|}         \
\            : set_of_list evs;                                    \
\           Says A B {|NA, Agent A, Agent B,                       \
\                      Crypt (shrK A) {|NA, Agent A, Agent B|}|}   \
\            : set_of_list evs;                                    \
\           A ~: lost;  A ~= Spy;  evs : otway lost |]             \
\        ==> EX NB. Says Server B                                  \
\                     {|NA,                                        \
\                       Crypt (shrK A) {|NA, Key K|},              \
\                       Crypt (shrK B) {|NB, Key K|}|}             \
\                       : set_of_list evs";
by (blast_tac (!claset addSIs [NA_Crypt_imp_Server_msg]
                       addEs  sees_Spy_partsEs) 1);
qed "A_trusts_OR4";


(** Crucial secrecy property: Spy does not see the keys sent in msg OR3
    Does not in itself guarantee security: an attack could violate 
    the premises, e.g. by having A=Spy **)

goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  evs : otway lost |]                    \
\        ==> Says Server B                                                 \
\              {|NA, Crypt (shrK A) {|NA, Key K|},                         \
\                Crypt (shrK B) {|NB, Key K|}|} : set_of_list evs -->      \
\            Says B Spy {|NA, NB, Key K|} ~: set_of_list evs -->           \
\            Key K ~: analz (sees lost Spy evs)";
by (etac otway.induct 1);
by analz_sees_tac;
by (ALLGOALS
    (asm_simp_tac (!simpset addcongs [conj_cong] 
                            addsimps [analz_insert_eq, not_parts_not_analz, 
				      analz_insert_freshK]
                            setloop split_tac [expand_if])));
(*Oops*)
by (blast_tac (!claset addSDs [unique_session_keys]) 4);
(*OR4*) 
by (Blast_tac 3);
(*OR3*)
by (blast_tac (!claset addSEs sees_Spy_partsEs
                       addIs [impOfSubs analz_subset_parts]) 2);
(*Fake*) 
by (spy_analz_tac 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);

goal thy 
 "!!evs. [| Says Server B                                                \
\            {|NA, Crypt (shrK A) {|NA, Key K|},                         \
\                  Crypt (shrK B) {|NB, Key K|}|} : set_of_list evs;     \
\           Says B Spy {|NA, NB, Key K|} ~: set_of_list evs;             \
\           A ~: lost;  B ~: lost;  evs : otway lost |]                  \
\        ==> Key K ~: analz (sees lost Spy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (blast_tac (!claset addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


goal thy 
 "!!evs. [| C ~: {A,B,Server};                                           \
\           Says Server B                                                \
\            {|NA, Crypt (shrK A) {|NA, Key K|},                         \
\                  Crypt (shrK B) {|NB, Key K|}|} : set_of_list evs;     \
\           Says B Spy {|NA, NB, Key K|} ~: set_of_list evs;             \
\           A ~: lost;  B ~: lost;  evs : otway lost |]                  \
\        ==> Key K ~: analz (sees lost C evs)";
by (rtac (subset_insertI RS sees_mono RS analz_mono RS contra_subsetD) 1);
by (rtac (sees_lost_agent_subset_sees_Spy RS analz_mono RS contra_subsetD) 1);
by (FIRSTGOAL (rtac Spy_not_see_encrypted_key));
by (REPEAT_FIRST (blast_tac (!claset addIs [otway_mono RS subsetD])));
qed "Agent_not_see_encrypted_key";


(**** Authenticity properties relating to NB ****)

(*Only OR2 can have caused such a part of a message to appear.  We do not
  know anything about X: it does NOT have to have the right form.*)
goal thy 
 "!!evs. [| B ~: lost;  evs : otway lost |]                    \
\        ==> Crypt (shrK B) {|NA, NB, Agent A, Agent B|}       \
\             : parts (sees lost Spy evs) -->                  \
\            (EX X. Says B Server                              \
\             {|NA, Agent A, Agent B, X,                       \
\               Crypt (shrK B) {|NA, NB, Agent A, Agent B|}|}  \
\             : set_of_list evs)";
by parts_induct_tac;
by (Fake_parts_insert_tac 1);
by (ALLGOALS Blast_tac);
bind_thm ("Crypt_imp_OR2", result() RSN (2,rev_mp) RS exE);


(** The Nonce NB uniquely identifies B's  message. **)

goal thy 
 "!!evs. [| evs : otway lost; B ~: lost |]               \
\ ==> EX NA' A'. ALL NA A.                               \
\      Crypt (shrK B) {|NA, NB, Agent A, Agent B|} : parts(sees lost Spy evs) \
\      --> NA = NA' & A = A'";
by parts_induct_tac;
by (Fake_parts_insert_tac 1);
by (simp_tac (!simpset addsimps [all_conj_distrib]) 1); 
(*OR2: creation of new Nonce.  Move assertion into global context*)
by (expand_case_tac "NB = ?y" 1);
by (blast_tac (!claset addSEs sees_Spy_partsEs) 1);
val lemma = result();

goal thy 
 "!!evs.[| Crypt (shrK B) {|NA, NB, Agent A, Agent B|} \
\                  : parts(sees lost Spy evs);         \
\          Crypt (shrK B) {|NC, NB, Agent C, Agent B|} \
\                  : parts(sees lost Spy evs);         \
\          evs : otway lost;  B ~: lost |]             \
\        ==> NC = NA & C = A";
by (prove_unique_tac lemma 1);
qed "unique_NB";


(*If the encrypted message appears, and B has used Nonce NB,
  then it originated with the Server!*)
goal thy 
 "!!evs. [| B ~: lost;  B ~= Spy;  evs : otway lost |]                   \
\    ==> Crypt (shrK B) {|NB, Key K|} : parts (sees lost Spy evs)        \
\        --> (ALL X'. Says B Server                                      \
\                       {|NA, Agent A, Agent B, X',                      \
\                         Crypt (shrK B) {|NA, NB, Agent A, Agent B|}|}  \
\             : set_of_list evs                                          \
\             --> Says Server B                                          \
\                  {|NA, Crypt (shrK A) {|NA, Key K|},                   \
\                        Crypt (shrK B) {|NB, Key K|}|}                  \
\                   : set_of_list evs)";
by parts_induct_tac;
by (Fake_parts_insert_tac 1);
(*OR1: it cannot be a new Nonce, contradiction.*)
by (blast_tac (!claset addSIs [parts_insertI] addSEs sees_Spy_partsEs) 1);
(*OR4*)
by (blast_tac (!claset addSEs [MPair_parts, Crypt_imp_OR2]) 2);
(*OR3*)
by (step_tac (!claset delrules [disjCI, impCE]) 1);
by (blast_tac (!claset delrules [conjI] (*stop split-up*)) 3); 
by (blast_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
                       addSEs [MPair_parts]
                       addDs  [unique_NB]) 2);
by (blast_tac (!claset addSEs [MPair_parts, no_nonce_OR1_OR2 RSN (2, rev_notE)]
                       addSDs [Says_imp_sees_Spy' RS parts.Inj]
                       delrules [conjI, impCE] (*stop split-up*)) 1);
qed_spec_mp "NB_Crypt_imp_Server_msg";


(*Guarantee for B: if it gets a message with matching NB then the Server
  has sent the correct message.*)
goal thy 
 "!!evs. [| B ~: lost;  B ~= Spy;  evs : otway lost;               \
\           Says S' B {|NA, X, Crypt (shrK B) {|NB, Key K|}|}      \
\            : set_of_list evs;                                    \
\           Says B Server {|NA, Agent A, Agent B, X',              \
\                           Crypt (shrK B) {|NA, NB, Agent A, Agent B|} |} \
\            : set_of_list evs |]                                  \
\        ==> Says Server B                                         \
\                 {|NA,                                            \
\                   Crypt (shrK A) {|NA, Key K|},                  \
\                   Crypt (shrK B) {|NB, Key K|}|}                 \
\                   : set_of_list evs";
by (blast_tac (!claset addSIs [NB_Crypt_imp_Server_msg]
                       addSEs sees_Spy_partsEs) 1);
qed "B_trusts_OR3";


B_trusts_OR3 RS Spy_not_see_encrypted_key;


goal thy 
 "!!evs. [| B ~: lost;  evs : otway lost |]                           \
\        ==> Says Server B                                            \
\              {|NA, Crypt (shrK A) {|NA, Key K|},                    \
\                Crypt (shrK B) {|NB, Key K|}|} : set_of_list evs --> \
\            (EX X. Says B Server {|NA, Agent A, Agent B, X,          \
\                            Crypt (shrK B) {|NA, NB, Agent A, Agent B|} |} \
\            : set_of_list evs)";
by (etac otway.induct 1);
by (ALLGOALS Asm_simp_tac);
by (blast_tac (!claset addDs [Says_imp_sees_Spy' RS parts.Inj]
		       addSEs [MPair_parts, Crypt_imp_OR2]) 3);
by (ALLGOALS Blast_tac);
bind_thm ("OR3_imp_OR2", result() RSN (2,rev_mp) RS exE);


(*After getting and checking OR4, agent A can trust that B has been active.
  We could probably prove that X has the expected form, but that is not
  strictly necessary for authentication.*)
goal thy 
 "!!evs. [| Says B' A {|NA, Crypt (shrK A) {|NA, Key K|}|}         \
\            : set_of_list evs;                                    \
\           Says A B {|NA, Agent A, Agent B,                       \
\                      Crypt (shrK A) {|NA, Agent A, Agent B|}|}   \
\            : set_of_list evs;                                    \
\           A ~: lost;  A ~= Spy;  B ~: lost;  evs : otway lost |] \
\        ==> EX NB X. Says B Server {|NA, Agent A, Agent B, X,     \
\                              Crypt (shrK B)  {|NA, NB, Agent A, Agent B|} |}\
\            : set_of_list evs";
by (blast_tac (!claset addSDs  [A_trusts_OR4]
                       addSEs [OR3_imp_OR2]) 1);
qed "A_auths_B";
