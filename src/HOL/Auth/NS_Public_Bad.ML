(*  Title:      HOL/Auth/NS_Public_Bad
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "ns_public" for the Needham-Schroeder Public-Key protocol.
Flawed version, vulnerable to Lowe's attack.

From page 260 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

open NS_Public_Bad;

set proof_timing;
HOL_quantifiers := false;

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
by (Auto_tac());
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
by (Fake_parts_insert_tac 1);
qed "Spy_see_priK";
Addsimps [Spy_see_priK];

goal thy 
 "!!A. evs: ns_public ==> (Key (priK A) : analz (spies evs)) = (A : bad)";
by (auto_tac(claset() addDs [impOfSubs analz_subset_parts], simpset()));
qed "Spy_analz_priK";
Addsimps [Spy_analz_priK];

goal thy  "!!A. [| Key (priK A) : parts (spies evs);       \
\                  evs : ns_public |] ==> A:bad";
by (blast_tac (claset() addDs [Spy_see_priK]) 1);
qed "Spy_see_priK_D";

bind_thm ("Spy_analz_priK_D", analz_subset_parts RS subsetD RS Spy_see_priK_D);
AddSDs [Spy_see_priK_D, Spy_analz_priK_D];


(**** Authenticity properties obtained from NS2 ****)

(*It is impossible to re-use a nonce in both NS1 and NS2, provided the nonce
  is secret.  (Honest users generate fresh nonces.)*)
goal thy 
 "!!evs. [| Crypt (pubK B) {|Nonce NA, Agent A|} : parts (spies evs); \
\           Nonce NA ~: analz (spies evs);   evs : ns_public |]       \
\ ==> Crypt (pubK C) {|NA', Nonce NA|} ~: parts (spies evs)";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
(*NS3*)
by (blast_tac (claset() addSEs partsEs) 3);
(*NS2*)
by (blast_tac (claset() addSEs partsEs) 2);
by (Fake_parts_insert_tac 1);
qed "no_nonce_NS1_NS2";


(*Unicity for NS1: nonce NA identifies agents A and B*)
goal thy 
 "!!evs. [| Nonce NA ~: analz (spies evs);  evs : ns_public |]      \
\ ==> EX A' B'. ALL A B.                                            \
\      Crypt (pubK B) {|Nonce NA, Agent A|} : parts (spies evs) --> \
\      A=A' & B=B'";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [all_conj_distrib, parts_insert_spies])));
(*NS1*)
by (expand_case_tac "NA = ?y" 2 THEN blast_tac (claset() addSEs partsEs) 2);
(*Fake*)
by (Clarify_tac 1);
by (ex_strip_tac 1);
by (Fake_parts_insert_tac 1);
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
 "!!evs. [| Says A B (Crypt(pubK B) {|Nonce NA, Agent A|}) : set evs;   \
\           A ~: bad;  B ~: bad;  evs : ns_public |]                    \
\        ==>  Nonce NA ~: analz (spies evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*NS3*)
by (blast_tac (claset() addDs  [Says_imp_spies RS parts.Inj]
                       addEs  [no_nonce_NS1_NS2 RSN (2, rev_notE)]) 4);
(*NS2*)
by (blast_tac (claset() addSEs [MPair_parts]
		       addDs  [Says_imp_spies RS parts.Inj,
			       parts.Body, unique_NA]) 3);
(*NS1*)
by (blast_tac (claset() addSEs spies_partsEs
                       addIs  [impOfSubs analz_subset_parts]) 2);
(*Fake*)
by (spy_analz_tac 1);
qed "Spy_not_see_NA";


(*Authentication for A: if she receives message 2 and has used NA
  to start a run, then B has sent message 2.*)
goal thy 
 "!!evs. [| Says A B (Crypt (pubK B) {|Nonce NA, Agent A|}) : set evs;  \
\           Says B' A (Crypt(pubK A) {|Nonce NA, Nonce NB|}): set evs;  \
\           A ~: bad;  B ~: bad;  evs : ns_public |]                    \
\        ==> Says B A (Crypt(pubK A) {|Nonce NA, Nonce NB|}): set evs";
by (etac rev_mp 1);
(*prepare induction over Crypt (pubK A) {|NA,NB|} : parts H*)
by (etac (Says_imp_spies RS parts.Inj RS rev_mp) 1);
by (etac ns_public.induct 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS Clarify_tac);
(*NS2*)
by (blast_tac (claset() addDs [Says_imp_spies RS parts.Inj,
			      Spy_not_see_NA, unique_NA]) 3);
(*NS1*)
by (blast_tac (claset() addSEs spies_partsEs) 2);
(*Fake*)
by (blast_tac (claset() addSDs [impOfSubs Fake_parts_insert]
                       addDs  [Spy_not_see_NA, 
			       impOfSubs analz_subset_parts]) 1);
qed "A_trusts_NS2";

(*If the encrypted message appears then it originated with Alice in NS1*)
goal thy 
 "!!evs. [| Crypt (pubK B) {|Nonce NA, Agent A|} : parts (spies evs); \
\           Nonce NA ~: analz (spies evs);                            \
\           evs : ns_public |]                                        \
\   ==> Says A B (Crypt (pubK B) {|Nonce NA, Agent A|}) : set evs";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Fake_parts_insert_tac 1);
qed "B_trusts_NS1";



(**** Authenticity properties obtained from NS2 ****)

(*Unicity for NS2: nonce NB identifies agent A and nonce NA
  [proof closely follows that for unique_NA] *)
goal thy 
 "!!evs. [| Nonce NB ~: analz (spies evs);  evs : ns_public |]  \
\ ==> EX A' NA'. ALL A NA.                                      \
\      Crypt (pubK A) {|Nonce NA, Nonce NB|}                    \
\        : parts (spies evs)  -->  A=A' & NA=NA'";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [all_conj_distrib, parts_insert_spies])));
(*NS2*)
by (expand_case_tac "NB = ?y" 2 THEN blast_tac (claset() addSEs partsEs) 2);
(*Fake*)
by (Clarify_tac 1);
by (ex_strip_tac 1);
by (Fake_parts_insert_tac 1);
val lemma = result();

goal thy 
 "!!evs. [| Crypt(pubK A) {|Nonce NA, Nonce NB|}  : parts(spies evs); \
\           Crypt(pubK A'){|Nonce NA', Nonce NB|} : parts(spies evs); \
\           Nonce NB ~: analz (spies evs);                            \
\           evs : ns_public |]                                        \
\        ==> A=A' & NA=NA'";
by (prove_unique_tac lemma 1);
qed "unique_NB";


(*NB remains secret PROVIDED Alice never responds with round 3*)
goal thy 
 "!!evs.[| Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set evs;  \
\          ALL C. Says A C (Crypt (pubK C) (Nonce NB)) ~: set evs;      \
\          A ~: bad;  B ~: bad;  evs : ns_public |]                     \
\       ==> Nonce NB ~: analz (spies evs)";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (analz_induct_tac 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [all_conj_distrib])));
by (ALLGOALS Clarify_tac);
(*NS3: because NB determines A*)
by (blast_tac (claset() addDs [Says_imp_spies RS parts.Inj, unique_NB]) 4);
(*NS2: by freshness and unicity of NB*)
by (blast_tac (claset() addDs [Says_imp_spies RS parts.Inj]
                       addEs [no_nonce_NS1_NS2 RSN (2, rev_notE)]
                       addEs partsEs
		       addIs [impOfSubs analz_subset_parts]) 3);
(*NS1: by freshness*)
by (blast_tac (claset() addSEs spies_partsEs) 2);
(*Fake*)
by (spy_analz_tac 1);
qed "Spy_not_see_NB";



(*Authentication for B: if he receives message 3 and has used NB
  in message 2, then A has sent message 3--to somebody....*)
goal thy 
 "!!evs. [| Says B A  (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set evs; \
\           Says A' B (Crypt (pubK B) (Nonce NB)): set evs;              \
\           A ~: bad;  B ~: bad;  evs : ns_public |]                   \
\        ==> EX C. Says A C (Crypt (pubK C) (Nonce NB)) : set evs";
by (etac rev_mp 1);
(*prepare induction over Crypt (pubK B) NB : parts H*)
by (etac (Says_imp_spies RS parts.Inj RS rev_mp) 1);
by (parts_induct_tac 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [ex_disj_distrib])));
by (ALLGOALS Clarify_tac);
(*NS3: because NB determines A (this use of unique_NB is more robust) *)
by (blast_tac (claset() addDs [Says_imp_spies RS parts.Inj, Spy_not_see_NB]
			addIs [unique_NB RS conjunct1]) 3);
(*NS1: by freshness*)
by (blast_tac (claset() addSEs spies_partsEs) 2);
(*Fake*)
by (blast_tac (claset() addSDs [impOfSubs Fake_parts_insert]
                       addDs  [Spy_not_see_NB, 
			       impOfSubs analz_subset_parts]) 1);
qed "B_trusts_NS3";


(*Can we strengthen the secrecy theorem?  NO*)
goal thy 
 "!!evs. [| A ~: bad;  B ~: bad;  evs : ns_public |]           \
\ ==> Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set evs \
\     --> Nonce NB ~: analz (spies evs)";
by (analz_induct_tac 1);
by (ALLGOALS Clarify_tac);
(*NS2: by freshness and unicity of NB*)
by (blast_tac (claset() addDs [Says_imp_spies RS parts.Inj]
                       addEs [no_nonce_NS1_NS2 RSN (2, rev_notE)]
                       addEs partsEs
		       addIs [impOfSubs analz_subset_parts]) 3);
(*NS1: by freshness*)
by (blast_tac (claset() addSEs spies_partsEs) 2);
(*Fake*)
by (spy_analz_tac 1);
(*NS3: unicity of NB identifies A and NA, but not B*)
by (forw_inst_tac [("A'","A")] (Says_imp_spies RS parts.Inj RS unique_NB) 1
    THEN REPEAT (eresolve_tac [asm_rl, Says_imp_spies RS parts.Inj] 1));
by (Auto_tac());
by (rename_tac "C B' evs3" 1);

(*
THIS IS THE ATTACK!
Level 8
!!evs. [| A ~: bad; B ~: bad; evs : ns_public |]
       ==> Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set evs -->
           Nonce NB ~: analz (spies evs)
 1. !!C B' evs3.
       [| A ~: bad; B ~: bad; evs3 : ns_public;
          Says A C (Crypt (pubK C) {|Nonce NA, Agent A|}) : set evs3;
          Says B' A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set evs3; C : bad;
          Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set evs3;
          Nonce NB ~: analz (spies evs3) |]
       ==> False
*)
