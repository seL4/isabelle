(*  Title:      HOL/Auth/OtwayRees
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "otway" for the Otway-Rees protocol.

Simplified version with minimal encryption but explicit messages

From page 11 of
  Abadi and Needham.  Prudent Engineering Practice for Cryptographic Protocols.
  IEEE Trans. SE 22 (1), 1996
*)

open OtwayRees_AN;

proof_timing:=true;
HOL_quantifiers := false;


(*A "possibility property": there are traces that reach the end*)
goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]                               \
\        ==> EX K. EX NA. EX evs: otway lost.                                 \
\             Says B A (Crypt (shrK A) {|Nonce NA, Agent A, Agent B, Key K|}) \
\             : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (otway.Nil RS otway.OR1 RS otway.OR2 RS otway.OR3 RS otway.OR4) 2);
by possibility_tac;
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

goal thy "!!evs. Says S B {|X, Crypt(shrK B) X'|} : set_of_list evs ==> \
\                X : analz (sees lost Spy evs)";
by (fast_tac (!claset addSDs [Says_imp_sees_Spy RS analz.Inj]) 1);
qed "OR4_analz_sees_Spy";

goal thy "!!evs. Says Server B {|X, Crypt K' {|NB, a, Agent B, K|}|} \
\                  : set_of_list evs ==> K : parts (sees lost Spy evs)";
by (fast_tac (!claset addSEs sees_Spy_partsEs) 1);
qed "Oops_parts_sees_Spy";

(*OR4_analz_sees_Spy lets us treat those cases using the same 
  argument as for the Fake case.  This is possible for most, but not all,
  proofs, since Fake messages originate from the Spy. *)

bind_thm ("OR4_parts_sees_Spy",
          OR4_analz_sees_Spy RS (impOfSubs analz_subset_parts));

(*We instantiate the variable to "lost".  Leaving it as a Var makes proofs
  harder to complete, since simplification does less for us.*)
val parts_Fake_tac = 
    forw_inst_tac [("lost","lost")] OR4_parts_sees_Spy 6 THEN
    forw_inst_tac [("lost","lost")] Oops_parts_sees_Spy 7;

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


(*Nobody can have used non-existent keys!*)
goal thy "!!evs. evs : otway lost ==>          \
\         Key K ~: used evs --> K ~: keysFor (parts (sees lost Spy evs))";
by (parts_induct_tac 1);
(*Fake*)
by (best_tac
      (!claset addIs [impOfSubs analz_subset_parts]
               addDs [impOfSubs (analz_subset_parts RS keysFor_mono),
                      impOfSubs (parts_insert_subset_Un RS keysFor_mono)]
               addss (!simpset)) 1);
(*OR3*)
by (fast_tac (!claset addss (!simpset)) 1);
qed_spec_mp "new_keys_not_used";

bind_thm ("new_keys_not_analzd",
          [analz_subset_parts RS keysFor_mono,
           new_keys_not_used] MRS contra_subsetD);

Addsimps [new_keys_not_used, new_keys_not_analzd];



(*** Proofs involving analz ***)

(*Describes the form of K and NA when the Server sends this message.*)
goal thy 
 "!!evs. [| Says Server B                                           \
\              {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},    \
\                Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}   \
\             : set_of_list evs;                                    \
\           evs : otway lost |]                                     \
\        ==> K ~: range shrK & (EX i. NA = Nonce i) & (EX j. NB = Nonce j)";
by (etac rev_mp 1);
by (etac otway.induct 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "Says_Server_message_form";


(*For proofs involving analz.  We again instantiate the variable to "lost".*)
val analz_Fake_tac = 
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
by analz_Fake_tac;
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_freshK_lemma ));
(*14 seconds*)
by (ALLGOALS (asm_simp_tac analz_image_freshK_ss));
(*OR4, Fake*) 
by (EVERY (map spy_analz_tac [3,2]));
(*Base*)
by (fast_tac (!claset addIs [image_eqI] addss (!simpset)) 1);
qed_spec_mp "analz_image_freshK";


goal thy
 "!!evs. [| evs : otway lost;  KAB ~: range shrK |] ==>             \
\        Key K : analz (insert (Key KAB) (sees lost Spy evs)) = \
\        (K = KAB | Key K : analz (sees lost Spy evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(*** The Key K uniquely identifies the Server's  message. **)

goal thy 
 "!!evs. evs : otway lost ==>                              \
\      EX A' B' NA' NB'. ALL A B NA NB.                    \
\       Says Server B \
\         {|Crypt (shrK A) {|NA, Agent A, Agent B, K|},                     \
\           Crypt (shrK B) {|NB, Agent A, Agent B, K|}|} : set_of_list evs  \
\       --> A=A' & B=B' & NA=NA' & NB=NB'";
by (etac otway.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib])));
by (Step_tac 1);
(*Remaining cases: OR3 and OR4*)
by (ex_strip_tac 2);
by (Fast_tac 2);
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
(*...we assume X is a recent message and handle this case by contradiction*)
by (fast_tac (!claset addSEs sees_Spy_partsEs
                      delrules [conjI]    (*prevent split-up into 4 subgoals*)
                      addss (!simpset addsimps [parts_insertI])) 1);
val lemma = result();


goal thy 
"!!evs. [| Says Server B                                           \
\            {|Crypt (shrK A) {|NA, Agent A, Agent B, K|},         \
\              Crypt (shrK B) {|NB, Agent A, Agent B, K|}|}        \
\           : set_of_list evs;                                     \
\          Says Server B'                                          \
\            {|Crypt (shrK A') {|NA', Agent A', Agent B', K|},     \
\              Crypt (shrK B') {|NB', Agent A', Agent B', K|}|}    \
\           : set_of_list evs;                                     \
\          evs : otway lost |]                                     \
\       ==> A=A' & B=B' & NA=NA' & NB=NB'";
by (prove_unique_tac lemma 1);
qed "unique_session_keys";



(**** Authenticity properties relating to NA ****)

(*If the encrypted message appears then it originated with the Server!*)
goal thy 
 "!!evs. [| A ~: lost;  evs : otway lost |]                 \
\ ==> Crypt (shrK A) {|NA, Agent A, Agent B, Key K|}        \
\      : parts (sees lost Spy evs)                          \
\     --> (EX NB. Says Server B                                          \
\                  {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},     \
\                    Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}    \
\                  : set_of_list evs)";
by (parts_induct_tac 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [ex_disj_distrib])));
(*OR3*)
by (Fast_tac 1);
qed_spec_mp "NA_Crypt_imp_Server_msg";


(*Corollary: if A receives B's OR4 message then it originated with the Server.
  Freshness may be inferred from nonce NA.*)
goal thy 
 "!!evs. [| Says B' A (Crypt (shrK A) {|NA, Agent A, Agent B, Key K|})  \
\            : set_of_list evs;                                         \
\           A ~: lost;  evs : otway lost |]                             \
\        ==> EX NB. Says Server B                                       \
\                    {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},  \
\                      Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|} \
\                   : set_of_list evs";
by (fast_tac (!claset addSIs [NA_Crypt_imp_Server_msg]
                      addEs  sees_Spy_partsEs) 1);
qed "A_trusts_OR4";


(** Crucial secrecy property: Spy does not see the keys sent in msg OR3
    Does not in itself guarantee security: an attack could violate 
    the premises, e.g. by having A=Spy **)

goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  evs : otway lost |]                    \
\        ==> Says Server B                                                 \
\             {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},            \
\               Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}           \
\            : set_of_list evs -->                                         \
\            Says B Spy {|NA, NB, Key K|} ~: set_of_list evs -->           \
\            Key K ~: analz (sees lost Spy evs)";
by (etac otway.induct 1);
by analz_Fake_tac;
by (ALLGOALS
    (asm_simp_tac (!simpset addcongs [conj_cong] 
                            addsimps [not_parts_not_analz,
                                      analz_insert_freshK]
                            setloop split_tac [expand_if])));
(*OR3*)
by (fast_tac (!claset delrules [impCE]
                      addSEs sees_Spy_partsEs
                      addIs [impOfSubs analz_subset_parts]
                      addss (!simpset addsimps [parts_insert2])) 2);
(*Oops*) 
by (best_tac (!claset addDs [unique_session_keys] addss (!simpset)) 3);
(*OR4, Fake*) 
by (REPEAT_FIRST spy_analz_tac);
val lemma = result() RS mp RS mp RSN(2,rev_notE);

goal thy 
 "!!evs. [| Says Server B                                           \
\              {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},    \
\                Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}   \
\             : set_of_list evs;                                    \
\           Says B Spy {|NA, NB, Key K|} ~: set_of_list evs;        \
\           A ~: lost;  B ~: lost;  evs : otway lost |]             \
\        ==> Key K ~: analz (sees lost Spy evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (fast_tac (!claset addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


goal thy 
 "!!evs. [| C ~: {A,B,Server};                                      \
\           Says Server B                                           \
\              {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},    \
\                Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}   \
\             : set_of_list evs;                                    \
\           Says B Spy {|NA, NB, Key K|} ~: set_of_list evs;        \
\           A ~: lost;  B ~: lost;  evs : otway lost |]             \
\        ==> Key K ~: analz (sees lost C evs)";
by (rtac (subset_insertI RS sees_mono RS analz_mono RS contra_subsetD) 1);
by (rtac (sees_lost_agent_subset_sees_Spy RS analz_mono RS contra_subsetD) 1);
by (FIRSTGOAL (rtac Spy_not_see_encrypted_key));
by (REPEAT_FIRST (fast_tac (!claset addIs [otway_mono RS subsetD])));
qed "Agent_not_see_encrypted_key";


(**** Authenticity properties relating to NB ****)

(*If the encrypted message appears then it originated with the Server!*)
goal thy 
 "!!evs. [| B ~: lost;  evs : otway lost |]                                 \
\    ==> Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}                     \
\         : parts (sees lost Spy evs)                                       \
\        --> (EX NA. Says Server B                                          \
\                     {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},     \
\                       Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}    \
\                     : set_of_list evs)";
by (parts_induct_tac 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [ex_disj_distrib])));
(*OR3*)
by (Fast_tac 1);
qed_spec_mp "NB_Crypt_imp_Server_msg";


(*Guarantee for B: if it gets a well-formed certificate then the Server
  has sent the correct message in round 3.*)
goal thy 
 "!!evs. [| B ~: lost;  evs : otway lost;                                   \
\           Says S B {|X, Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}  \
\            : set_of_list evs |]                                           \
\        ==> EX NA. Says Server B                                           \
\                     {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},     \
\                       Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}    \
\                     : set_of_list evs";
by (fast_tac (!claset addSIs [NB_Crypt_imp_Server_msg]
                      addEs  sees_Spy_partsEs) 1);
qed "B_trusts_OR3";
