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
\        ==> EX K. EX NA. EX evs: otway.                                      \
\             Says B A (Crypt (shrK A) {|Nonce NA, Agent A, Agent B, Key K|}) \
\             : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (otway.Nil RS otway.OR1 RS otway.OR2 RS otway.OR3 RS otway.OR4) 2);
by possibility_tac;
result();


(**** Inductive proofs about otway ****)

(*Nobody sends themselves messages*)
goal thy "!!evs. evs : otway ==> ALL A X. Says A A X ~: set evs";
by (etac otway.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(** For reasoning about the encrypted portion of messages **)

goal thy "!!evs. Says S' B {|X, Crypt(shrK B) X'|} : set evs ==> \
\                X : analz (spies evs)";
by (blast_tac (!claset addSDs [Says_imp_spies RS analz.Inj]) 1);
qed "OR4_analz_spies";

goal thy "!!evs. Says Server B {|X, Crypt K' {|NB, a, Agent B, K|}|} \
\                  : set evs ==> K : parts (spies evs)";
by (blast_tac (!claset addSEs spies_partsEs) 1);
qed "Oops_parts_spies";

(*OR4_analz_spies lets us treat those cases using the same 
  argument as for the Fake case.  This is possible for most, but not all,
  proofs, since Fake messages originate from the Spy. *)

bind_thm ("OR4_parts_spies",
          OR4_analz_spies RS (impOfSubs analz_subset_parts));

(*For proving the easier theorems about X ~: parts (spies evs).*)
fun parts_induct_tac i = 
    etac otway.induct i			THEN 
    forward_tac [Oops_parts_spies] (i+6) THEN
    forward_tac [OR4_parts_spies]  (i+5) THEN
    prove_simple_subgoals_tac  i;


(** Theorems of the form X ~: parts (spies evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's shared key! (unless it's bad at start)*)
goal thy 
 "!!evs. evs : otway ==> (Key (shrK A) : parts (spies evs)) = (A : bad)";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
by (Blast_tac 1);
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

goal thy 
 "!!evs. evs : otway ==> (Key (shrK A) : analz (spies evs)) = (A : bad)";
by (auto_tac(!claset addDs [impOfSubs analz_subset_parts], !simpset));
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

goal thy  "!!A. [| Key (shrK A) : parts (spies evs); evs : otway |] ==> A:bad";
by (blast_tac (!claset addDs [Spy_see_shrK]) 1);
qed "Spy_see_shrK_D";

bind_thm ("Spy_analz_shrK_D", analz_subset_parts RS subsetD RS Spy_see_shrK_D);
AddSDs [Spy_see_shrK_D, Spy_analz_shrK_D];


(*Nobody can have used non-existent keys!*)
goal thy "!!evs. evs : otway ==>          \
\         Key K ~: used evs --> K ~: keysFor (parts (spies evs))";
by (parts_induct_tac 1);
(*Fake*)
by (best_tac
      (!claset addIs [impOfSubs analz_subset_parts]
               addDs [impOfSubs (analz_subset_parts RS keysFor_mono),
                      impOfSubs (parts_insert_subset_Un RS keysFor_mono)]
               addss (!simpset)) 1);
(*OR3*)
by (Blast_tac 1);
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
\             : set evs;                                            \
\           evs : otway |]                                          \
\        ==> K ~: range shrK & (EX i. NA = Nonce i) & (EX j. NB = Nonce j)";
by (etac rev_mp 1);
by (etac otway.induct 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed "Says_Server_message_form";


(*For proofs involving analz.*)
val analz_spies_tac = 
    dtac OR4_analz_spies 6 THEN
    forward_tac [Says_Server_message_form] 7 THEN
    assume_tac 7 THEN
    REPEAT ((eresolve_tac [exE, conjE] ORELSE' hyp_subst_tac) 7);


(****
 The following is to prove theorems of the form

  Key K : analz (insert (Key KAB) (spies evs)) ==>
  Key K : analz (spies evs)

 A more general formula must be proved inductively.
****)


(** Session keys are not used to encrypt other session keys **)

(*The equality makes the induction hypothesis easier to apply*)
goal thy  
 "!!evs. evs : otway ==>                                    \
\  ALL K KK. KK <= Compl (range shrK) -->                   \
\            (Key K : analz (Key``KK Un (spies evs))) =  \
\            (K : KK | Key K : analz (spies evs))";
by (etac otway.induct 1);
by analz_spies_tac;
by (REPEAT_FIRST (resolve_tac [allI, impI]));
by (REPEAT_FIRST (rtac analz_image_freshK_lemma ));
by (ALLGOALS (asm_simp_tac analz_image_freshK_ss));
(*Fake*) 
by (spy_analz_tac 2);
(*Base*)
by (Blast_tac 1);
qed_spec_mp "analz_image_freshK";


goal thy
 "!!evs. [| evs : otway;  KAB ~: range shrK |] ==>          \
\        Key K : analz (insert (Key KAB) (spies evs)) =  \
\        (K = KAB | Key K : analz (spies evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(*** The Key K uniquely identifies the Server's  message. **)

goal thy 
 "!!evs. evs : otway ==>                                            \
\      EX A' B' NA' NB'. ALL A B NA NB.                             \
\       Says Server B                                               \
\         {|Crypt (shrK A) {|NA, Agent A, Agent B, K|},             \
\           Crypt (shrK B) {|NB, Agent A, Agent B, K|}|} : set evs  \
\       --> A=A' & B=B' & NA=NA' & NB=NB'";
by (etac otway.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib])));
by (ALLGOALS Clarify_tac);
(*Remaining cases: OR3 and OR4*)
by (ex_strip_tac 2);
by (Blast_tac 2);
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
(*...we assume X is a recent message and handle this case by contradiction*)
by (blast_tac (!claset addSEs spies_partsEs
                       delrules[conjI] (*prevent splitup into 4 subgoals*)) 1);
val lemma = result();


goal thy 
"!!evs. [| Says Server B                                           \
\            {|Crypt (shrK A) {|NA, Agent A, Agent B, K|},         \
\              Crypt (shrK B) {|NB, Agent A, Agent B, K|}|}        \
\           : set evs;                                             \
\          Says Server B'                                          \
\            {|Crypt (shrK A') {|NA', Agent A', Agent B', K|},     \
\              Crypt (shrK B') {|NB', Agent A', Agent B', K|}|}    \
\           : set evs;                                             \
\          evs : otway |]                                          \
\       ==> A=A' & B=B' & NA=NA' & NB=NB'";
by (prove_unique_tac lemma 1);
qed "unique_session_keys";



(**** Authenticity properties relating to NA ****)

(*If the encrypted message appears then it originated with the Server!*)
goal thy 
 "!!evs. [| A ~: bad;  evs : otway |]                 \
\ ==> Crypt (shrK A) {|NA, Agent A, Agent B, Key K|} : parts (spies evs) \
\     --> (EX NB. Says Server B                                          \
\                  {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},     \
\                    Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}    \
\                  : set evs)";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [ex_disj_distrib])));
(*OR3*)
by (Blast_tac 1);
qed_spec_mp "NA_Crypt_imp_Server_msg";


(*Corollary: if A receives B's OR4 message then it originated with the Server.
  Freshness may be inferred from nonce NA.*)
goal thy 
 "!!evs. [| Says B' A (Crypt (shrK A) {|NA, Agent A, Agent B, Key K|})  \
\            : set evs;                                                 \
\           A ~: bad;  evs : otway |]                                  \
\        ==> EX NB. Says Server B                                       \
\                    {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},  \
\                      Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|} \
\                   : set evs";
by (blast_tac (!claset addSIs [NA_Crypt_imp_Server_msg]
                      addEs  spies_partsEs) 1);
qed "A_trusts_OR4";


(** Crucial secrecy property: Spy does not see the keys sent in msg OR3
    Does not in itself guarantee security: an attack could violate 
    the premises, e.g. by having A=Spy **)

goal thy 
 "!!evs. [| A ~: bad;  B ~: bad;  evs : otway |]                 \
\        ==> Says Server B                                         \
\             {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},    \
\               Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}   \
\            : set evs -->                                         \
\            Says B Spy {|NA, NB, Key K|} ~: set evs -->           \
\            Key K ~: analz (spies evs)";
by (etac otway.induct 1);
by analz_spies_tac;
by (ALLGOALS
    (asm_simp_tac (!simpset addcongs [conj_cong, if_weak_cong] 
                            addsimps [analz_insert_eq, analz_insert_freshK]
                            setloop split_tac [expand_if])));
(*Oops*)
by (blast_tac (!claset addSDs [unique_session_keys]) 4);
(*OR4*) 
by (Blast_tac 3);
(*OR3*)
by (blast_tac (!claset addSEs spies_partsEs
                       addIs [impOfSubs analz_subset_parts]) 2);
(*Fake*) 
by (spy_analz_tac 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);

goal thy 
 "!!evs. [| Says Server B                                           \
\              {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},    \
\                Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}   \
\             : set evs;                                            \
\           Says B Spy {|NA, NB, Key K|} ~: set evs;                \
\           A ~: bad;  B ~: bad;  evs : otway |]                  \
\        ==> Key K ~: analz (spies evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (blast_tac (!claset addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


(**** Authenticity properties relating to NB ****)

(*If the encrypted message appears then it originated with the Server!*)
goal thy 
 "!!evs. [| B ~: bad;  evs : otway |]                                 \
\    ==> Crypt (shrK B) {|NB, Agent A, Agent B, Key K|} : parts (spies evs) \
\        --> (EX NA. Says Server B                                          \
\                     {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},     \
\                       Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}    \
\                     : set evs)";
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [ex_disj_distrib])));
(*OR3*)
by (Blast_tac 1);
qed_spec_mp "NB_Crypt_imp_Server_msg";


(*Guarantee for B: if it gets a well-formed certificate then the Server
  has sent the correct message in round 3.*)
goal thy 
 "!!evs. [| B ~: bad;  evs : otway;                                        \
\           Says S' B {|X, Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|} \
\            : set evs |]                                                   \
\        ==> EX NA. Says Server B                                           \
\                     {|Crypt (shrK A) {|NA, Agent A, Agent B, Key K|},     \
\                       Crypt (shrK B) {|NB, Agent A, Agent B, Key K|}|}    \
\                     : set evs";
by (blast_tac (!claset addSIs [NB_Crypt_imp_Server_msg]
                       addEs  spies_partsEs) 1);
qed "B_trusts_OR3";
