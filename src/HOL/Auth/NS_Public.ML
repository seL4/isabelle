(*  Title:      HOL/Auth/NS_Public
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "ns_public" for the Needham-Schroeder Public-Key protocol.
Version incorporating Lowe's fix (inclusion of B's identify in round 2).

This version is experimental.  It adds many more rules to the claset and even
replaces Fake_parts_insert_tac by Blast_tac.
*)

open NS_Public;

set proof_timing;
HOL_quantifiers := false;

AddEs spies_partsEs;
AddDs [impOfSubs analz_subset_parts];
AddDs [impOfSubs Fake_parts_insert];

AddIffs [Spy_in_bad];

(*A "possibility property": there are traces that reach the end*)
goal thy 
 "!!A B. A ~= B ==> EX NB. EX evs: ns_public.               \
\                     Says A B (Crypt (pubK B) (Nonce NB)) : set evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (ns_public.Nil RS ns_public.NS1 RS ns_public.NS2 RS ns_public.NS3) 2);
by possibility_tac;
result();


(**** Inductive proofs about ns_public ****)

(*Nobody sends themselves messages*)
goal thy "!!evs. evs : ns_public ==> ALL A X. Says A A X ~: set evs";
by (etac ns_public.induct 1);
by Auto_tac;
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(*Induction for regularity theorems.  If induction formula has the form
   X ~: analz (spies evs) --> ... then it shortens the proof by discarding
   needless information about analz (insert X (spies evs))  *)
fun parts_induct_tac i = 
    etac ns_public.induct i
    THEN 
    REPEAT (FIRSTGOAL analz_mono_contra_tac)
    THEN 
    prove_simple_subgoals_tac i;


(** Theorems of the form X ~: parts (spies evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's private key! (unless it's bad at start)*)
goal thy 
 "!!A. evs: ns_public ==> (Key (priK A) : parts (spies evs)) = (A : bad)";
by (parts_induct_tac 1);
by (Blast_tac 1);
qed "Spy_see_priK";
Addsimps [Spy_see_priK];

goal thy 
 "!!A. evs: ns_public ==> (Key (priK A) : analz (spies evs)) = (A : bad)";
by Auto_tac;
qed "Spy_analz_priK";
Addsimps [Spy_analz_priK];

AddSDs [Spy_see_priK RSN (2, rev_iffD1), 
	Spy_analz_priK RSN (2, rev_iffD1)];


(**** Authenticity properties obtained from NS2 ****)

(*It is impossible to re-use a nonce in both NS1 and NS2, provided the nonce
  is secret.  (Honest users generate fresh nonces.)*)
goal thy 
 "!!evs. [| Crypt (pubK B) {|Nonce NA, Agent A|} : parts (spies evs); \
\           Nonce NA ~: analz (spies evs);       \
\           evs : ns_public |]                      \
\ ==> Crypt (pubK C) {|NA', Nonce NA, Agent D|} ~: parts (spies evs)";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "no_nonce_NS1_NS2";

(*Adding it to the claset slows down proofs...*)
val nonce_NS1_NS2_E = no_nonce_NS1_NS2 RSN (2, rev_notE);


(*Unicity for NS1: nonce NA identifies agents A and B*)
goal thy 
 "!!evs. [| Nonce NA ~: analz (spies evs);  evs : ns_public |]      \
\ ==> EX A' B'. ALL A B.                                            \
\      Crypt (pubK B) {|Nonce NA, Agent A|} : parts (spies evs) --> \
\      A=A' & B=B'";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [all_conj_distrib,
				       parts_insert_spies])));
(*NS1*)
by (expand_case_tac "NA = ?y" 2 THEN Blast_tac 2);
(*Fake*)
by (Clarify_tac 1);
by (ex_strip_tac 1);
by (Blast_tac 1);
val lemma = result();

goal thy 
 "!!evs. [| Crypt(pubK B)  {|Nonce NA, Agent A|}  : parts(spies evs); \
\           Crypt(pubK B') {|Nonce NA, Agent A'|} : parts(spies evs); \
\           Nonce NA ~: analz (spies evs);                            \
\           evs : ns_public |]                                        \
\        ==> A=A' & B=B'";
by (prove_unique_tac lemma 1);
qed "unique_NA";


(*Tactic for proving secrecy theorems*)
fun analz_induct_tac i = 
    etac ns_public.induct i   THEN
    ALLGOALS (asm_simp_tac (simpset() addsplits [expand_if]));


(*Secrecy: Spy does not see the nonce sent in msg NS1 if A and B are secure*)
goal thy 
 "!!evs. [| Says A B (Crypt(pubK B) {|Nonce NA, Agent A|}) : set evs;         \
\           A ~: bad;  B ~: bad;  evs : ns_public |]                        \
\        ==>  Nonce NA ~: analz (spies evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*NS3*)
by (blast_tac (claset() addEs [nonce_NS1_NS2_E]) 4);
(*NS2*)
by (blast_tac (claset() addDs [unique_NA]) 3);
(*NS1*)
by (Blast_tac 2);
(*Fake*)
by (spy_analz_tac 1);
qed "Spy_not_see_NA";


(*Authentication for A: if she receives message 2 and has used NA
  to start a run, then B has sent message 2.*)
goal thy 
 "!!evs. [| Says A B (Crypt (pubK B) {|Nonce NA, Agent A|}) : set evs;  \
\           Says B' A (Crypt(pubK A) {|Nonce NA, Nonce NB, Agent B|})   \
\             : set evs;                                                \
\           A ~: bad;  B ~: bad;  evs : ns_public |]                  \
\        ==> Says B A (Crypt(pubK A) {|Nonce NA, Nonce NB, Agent B|})   \
\              : set evs";
by (etac rev_mp 1);
(*prepare induction over Crypt (pubK A) {|NA,NB,B|} : parts H*)
by (etac (Says_imp_spies RS parts.Inj RS rev_mp) 1);
by (etac ns_public.induct 1);
by (ALLGOALS Asm_simp_tac);
(*NS1*)
by (Blast_tac 2);
(*Fake*)
by (blast_tac (claset() addDs [Spy_not_see_NA]) 1);
qed "A_trusts_NS2";

(*If the encrypted message appears then it originated with Alice in NS1*)
goal thy 
 "!!evs. [| Crypt (pubK B) {|Nonce NA, Agent A|} : parts (spies evs); \
\           Nonce NA ~: analz (spies evs);                 \
\           evs : ns_public |]                             \
\   ==> Says A B (Crypt (pubK B) {|Nonce NA, Agent A|}) : set evs";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Blast_tac 1);
qed "B_trusts_NS1";



(**** Authenticity properties obtained from NS2 ****)

(*Unicity for NS2: nonce NB identifies nonce NA and agents A, B 
  [unicity of B makes Lowe's fix work]
  [proof closely follows that for unique_NA] *)
goal thy 
 "!!evs. [| Nonce NB ~: analz (spies evs);  evs : ns_public |]            \
\ ==> EX A' NA' B'. ALL A NA B.                                           \
\      Crypt (pubK A) {|Nonce NA, Nonce NB, Agent B|} : parts (spies evs) \
\         -->  A=A' & NA=NA' & B=B'";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [all_conj_distrib, 
				       parts_insert_spies])));
(*NS2*)
by (expand_case_tac "NB = ?y" 2 THEN Blast_tac 2);
(*Fake*)
by (Clarify_tac 1);
by (ex_strip_tac 1);
by (Blast_tac 1);
val lemma = result();

goal thy 
 "!!evs. [| Crypt(pubK A)  {|Nonce NA, Nonce NB, Agent B|}   \
\             : parts(spies evs);                            \
\           Crypt(pubK A') {|Nonce NA', Nonce NB, Agent B'|} \
\             : parts(spies evs);                            \
\           Nonce NB ~: analz (spies evs);                   \
\           evs : ns_public |]                               \
\        ==> A=A' & NA=NA' & B=B'";
by (prove_unique_tac lemma 1);
qed "unique_NB";

AddDs [unique_NB];


(*Secrecy: Spy does not see the nonce sent in msg NS2 if A and B are secure*)
goal thy 
 "!!evs. [| Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB, Agent B|}) \
\             : set evs;                                              \
\           A ~: bad;  B ~: bad;  evs : ns_public |]                \
\ ==> Nonce NB ~: analz (spies evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*NS3*)
by (Blast_tac 4);
(*NS2: by freshness and unicity of NB*)
by (blast_tac (claset() addEs [nonce_NS1_NS2_E]) 3);
(*NS1*)
by (Blast_tac 2);
(*Fake*)
by (spy_analz_tac 1);
qed "Spy_not_see_NB";

AddDs [Spy_not_see_NB];


(*Authentication for B: if he receives message 3 and has used NB
  in message 2, then A has sent message 3.*)
goal thy 
 "!!evs. [| Says B A  (Crypt (pubK A) {|Nonce NA, Nonce NB, Agent B|}) \
\             : set evs;                                               \
\           Says A' B (Crypt (pubK B) (Nonce NB)): set evs;            \
\           A ~: bad;  B ~: bad;  evs : ns_public |]                   \
\        ==> Says A B (Crypt (pubK B) (Nonce NB)) : set evs";
by (etac rev_mp 1);
(*prepare induction over Crypt (pubK B) NB : parts H*)
by (etac (Says_imp_spies RS parts.Inj RS rev_mp) 1);
by (parts_induct_tac 1);
by (ALLGOALS Clarify_tac);
by (ALLGOALS Blast_tac);
qed "B_trusts_NS3";


(**** Overall guarantee for B*)

(*Matches only NS2, not NS1 (or NS3)*)
val Says_imp_spies' = 
    read_instantiate [("X","Crypt ?K {|?XX,?YY,?ZZ|}")] Says_imp_spies;


(*If B receives NS3 and the nonce NB agrees with the nonce he joined with
  NA, then A initiated the run using NA.  SAME proof as B_trusts_NS3!*)
goal thy 
 "!!evs. [| Says B A  (Crypt (pubK A) {|Nonce NA, Nonce NB, Agent B|}) \
\             : set evs;                                               \
\           Says A' B (Crypt (pubK B) (Nonce NB)): set evs;            \
\           A ~: bad;  B ~: bad;  evs : ns_public |]                 \
\    ==> Says A B (Crypt (pubK B) {|Nonce NA, Agent A|}) : set evs";
by (etac rev_mp 1);
(*prepare induction over Crypt (pubK B) {|NB|} : parts H*)
by (etac (Says_imp_spies RS parts.Inj RS rev_mp) 1);
by (etac ns_public.induct 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS Clarify_tac);
(*NS3 holds because NB determines A and NA*)
by (ALLGOALS Blast_tac);
qed "B_trusts_protocol";

