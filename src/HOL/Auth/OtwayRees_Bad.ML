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

set proof_timing;
HOL_quantifiers := false;

AddEs spies_partsEs;
AddDs [impOfSubs analz_subset_parts];
AddDs [impOfSubs Fake_parts_insert];


(*A "possibility property": there are traces that reach the end*)
goal thy 
 "!!A B. [| A ~= B; A ~= Server; B ~= Server |]   \
\        ==> EX K. EX NA. EX evs: otway.          \
\               Says B A {|Nonce NA, Crypt (shrK A) {|Nonce NA, Key K|}|} \
\                 : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (otway.Nil RS otway.OR1 RS otway.OR2 RS otway.OR3 RS otway.OR4) 2);
by possibility_tac;
result();


(**** Inductive proofs about otway ****)

(*Nobody sends themselves messages*)
goal thy "!!evs. evs : otway ==> ALL A X. Says A A X ~: set evs";
by (etac otway.induct 1);
by Auto_tac;
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(** For reasoning about the encrypted portion of messages **)

goal thy "!!evs. Says A' B {|N, Agent A, Agent B, X|} : set evs \
\                ==> X : analz (spies evs)";
by (dtac (Says_imp_spies RS analz.Inj) 1);
by (Blast_tac 1);
qed "OR2_analz_spies";

goal thy "!!evs. Says S' B {|N, X, Crypt (shrK B) X'|} : set evs \
\                ==> X : analz (spies evs)";
by (dtac (Says_imp_spies RS analz.Inj) 1);
by (Blast_tac 1);
qed "OR4_analz_spies";

goal thy "!!evs. Says Server B {|NA, X, Crypt K' {|NB,K|}|} : set evs \
\                ==> K : parts (spies evs)";
by (Blast_tac 1);
qed "Oops_parts_spies";

bind_thm ("OR2_parts_spies",
          OR2_analz_spies RS (impOfSubs analz_subset_parts));
bind_thm ("OR4_parts_spies",
          OR4_analz_spies RS (impOfSubs analz_subset_parts));

(*For proving the easier theorems about X ~: parts (spies evs).*)
fun parts_induct_tac i = 
    etac otway.induct i			THEN 
    forward_tac [Oops_parts_spies] (i+6) THEN
    forward_tac [OR4_parts_spies]  (i+5) THEN
    forward_tac [OR2_parts_spies]  (i+3) THEN 
    prove_simple_subgoals_tac  i;


(** Theorems of the form X ~: parts (spies evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees a good agent's shared key!*)
goal thy 
 "!!evs. evs : otway ==> (Key (shrK A) : parts (spies evs)) = (A : bad)";
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "Spy_see_shrK";
Addsimps [Spy_see_shrK];

goal thy 
 "!!evs. evs : otway ==> (Key (shrK A) : analz (spies evs)) = (A : bad)";
by (auto_tac(claset() addDs [impOfSubs analz_subset_parts], simpset()));
qed "Spy_analz_shrK";
Addsimps [Spy_analz_shrK];

AddSDs [Spy_see_shrK RSN (2, rev_iffD1), 
	Spy_analz_shrK RSN (2, rev_iffD1)];


(*Nobody can have used non-existent keys!*)
goal thy "!!evs. evs : otway ==>          \
\         Key K ~: used evs --> K ~: keysFor (parts (spies evs))";
by (parts_induct_tac 1);
(*Fake*)
by (blast_tac (claset() addSDs [keysFor_parts_insert]) 1);
(*OR2, OR3*)
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
 "!!evs. [| Says Server B {|NA, X, Crypt (shrK B) {|NB, Key K|}|} : set evs; \
\           evs : otway |]                                           \
\     ==> K ~: range shrK & (EX i. NA = Nonce i) & (EX j. NB = Nonce j)";
by (etac rev_mp 1);
by (etac otway.induct 1);
by (ALLGOALS Simp_tac);
by (ALLGOALS Blast_tac);
qed "Says_Server_message_form";


(*For proofs involving analz.*)
val analz_spies_tac = 
    dtac OR2_analz_spies 4 THEN 
    dtac OR4_analz_spies 6 THEN
    forward_tac [Says_Server_message_form] 7 THEN assume_tac 7 THEN
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
by (spy_analz_tac 1);
qed_spec_mp "analz_image_freshK";


goal thy
 "!!evs. [| evs : otway;  KAB ~: range shrK |] ==>          \
\        Key K : analz (insert (Key KAB) (spies evs)) =  \
\        (K = KAB | Key K : analz (spies evs))";
by (asm_simp_tac (analz_image_freshK_ss addsimps [analz_image_freshK]) 1);
qed "analz_insert_freshK";


(*** The Key K uniquely identifies the Server's  message. **)

goal thy 
 "!!evs. evs : otway ==>                                                  \
\   EX B' NA' NB' X'. ALL B NA NB X.                                      \
\     Says Server B {|NA, X, Crypt (shrK B) {|NB, K|}|} : set evs -->     \
\     B=B' & NA=NA' & NB=NB' & X=X'";
by (etac otway.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [all_conj_distrib])));
by (ALLGOALS Clarify_tac);
(*Remaining cases: OR3 and OR4*)
by (ex_strip_tac 2);
by (Best_tac 2);	(*Blast_tac's too slow (in reconstruction)*)
by (expand_case_tac "K = ?y" 1);
by (REPEAT (ares_tac [refl,exI,impI,conjI] 2));
(*...we assume X is a recent message, and handle this case by contradiction*)
by (blast_tac (claset() addSEs spies_partsEs) 1);
val lemma = result();

goal thy 
 "!!evs. [| Says Server B {|NA, X, Crypt (shrK B) {|NB, K|}|}   : set evs; \ 
\           Says Server B' {|NA',X',Crypt (shrK B') {|NB',K|}|} : set evs; \
\           evs : otway |] ==> X=X' & B=B' & NA=NA' & NB=NB'";
by (prove_unique_tac lemma 1);
qed "unique_session_keys";


(** Crucial secrecy property: Spy does not see the keys sent in msg OR3
    Does not in itself guarantee security: an attack could violate 
    the premises, e.g. by having A=Spy **)

goal thy 
 "!!evs. [| A ~: bad;  B ~: bad;  evs : otway |]                      \
\        ==> Says Server B                                            \
\              {|NA, Crypt (shrK A) {|NA, Key K|},                    \
\                Crypt (shrK B) {|NB, Key K|}|} : set evs -->         \
\            Notes Spy {|NA, NB, Key K|} ~: set evs -->               \
\            Key K ~: analz (spies evs)";
by (etac otway.induct 1);
by analz_spies_tac;
by (ALLGOALS
    (asm_simp_tac (simpset() addcongs [conj_cong] 
                             addsimps [analz_insert_eq, analz_insert_freshK]
                             addsimps (pushes@split_ifs))));
(*Oops*)
by (blast_tac (claset() addSDs [unique_session_keys]) 4);
(*OR4*) 
by (Blast_tac 3);
(*OR3*)
by (Blast_tac 2);
(*Fake*) 
by (spy_analz_tac 1);
val lemma = result() RS mp RS mp RSN(2,rev_notE);

goal thy 
 "!!evs. [| Says Server B                                           \
\            {|NA, Crypt (shrK A) {|NA, Key K|},                    \
\                  Crypt (shrK B) {|NB, Key K|}|} : set evs;        \
\           Notes Spy {|NA, NB, Key K|} ~: set evs;                 \
\           A ~: bad;  B ~: bad;  evs : otway |]                    \
\        ==> Key K ~: analz (spies evs)";
by (forward_tac [Says_Server_message_form] 1 THEN assume_tac 1);
by (blast_tac (claset() addSEs [lemma]) 1);
qed "Spy_not_see_encrypted_key";


(*** Attempting to prove stronger properties ***)

(*Only OR1 can have caused such a part of a message to appear.
  I'm not sure why A ~= B premise is needed: OtwayRees.ML doesn't need it.
  Perhaps it's because OR2 has two similar-looking encrypted messages in
        this version.*)
goal thy 
 "!!evs. [| A ~: bad;  A ~= B;  evs : otway |]                \
\        ==> Crypt (shrK A) {|NA, Agent A, Agent B|} : parts (spies evs) --> \
\            Says A B {|NA, Agent A, Agent B,                  \
\                       Crypt (shrK A) {|NA, Agent A, Agent B|}|}  : set evs";
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed_spec_mp "Crypt_imp_OR1";


(*Crucial property: If the encrypted message appears, and A has used NA
  to start a run, then it originated with the Server!*)
(*Only it is FALSE.  Somebody could make a fake message to Server
          substituting some other nonce NA' for NB.*)
goal thy 
 "!!evs. [| A ~: bad;  evs : otway |]                                \
\        ==> Crypt (shrK A) {|NA, Key K|} : parts (spies evs) -->    \
\            Says A B {|NA, Agent A, Agent B,                        \
\                       Crypt (shrK A) {|NA, Agent A, Agent B|}|}    \
\             : set evs -->                                          \
\            (EX B NB. Says Server B                                 \
\                 {|NA,                                              \
\                   Crypt (shrK A) {|NA, Key K|},                    \
\                   Crypt (shrK B) {|NB, Key K|}|}  : set evs)";
by (parts_induct_tac 1);
(*Fake*)
by (Blast_tac 1);
(*OR1: it cannot be a new Nonce, contradiction.*)
by (Blast_tac 1);
(*OR3 and OR4*)
by (ALLGOALS (asm_simp_tac (simpset() addsimps [ex_disj_distrib])));
by (ALLGOALS Clarify_tac);
(*OR4*)
by (blast_tac (claset() addSIs [Crypt_imp_OR1]) 2);
(*OR3*)  (** LEVEL 5 **)
(*The hypotheses at this point suggest an attack in which nonce NB is used
  in two different roles:
          Says B' Server
           {|Nonce NA, Agent Aa, Agent A,
             Crypt (shrK Aa) {|Nonce NA, Agent Aa, Agent A|}, Nonce NB,
             Crypt (shrK A) {|Nonce NA, Agent Aa, Agent A|}|}
          : set evs3;
          Says A B
           {|Nonce NB, Agent A, Agent B,
             Crypt (shrK A) {|Nonce NB, Agent A, Agent B|}|}
          : set evs3;
*)
writeln "GIVE UP! on NA_Crypt_imp_Server_msg";


(*Thus the key property A_can_trust probably fails too.*)
