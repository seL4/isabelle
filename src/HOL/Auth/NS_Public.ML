(*  Title:      HOL/Auth/NS_Public
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "ns_public" for the Needham-Schroeder Public-Key protocol.
Version incorporating Lowe's fix (inclusion of B's identify in round 2).
*)

open NS_Public;

proof_timing:=true;
HOL_quantifiers := false;

AddIffs [Spy_in_lost];

(*Replacing the variable by a constant improves search speed by 50%!*)
val Says_imp_sees_Spy' = 
    read_instantiate_sg (sign_of thy) [("lost","lost")] Says_imp_sees_Spy;

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


(** Theorems of the form X ~: parts (sees lost Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's private key! (unless it's lost at start)*)
goal thy 
 "!!evs. evs : ns_public \
\        ==> (Key (priK A) : parts (sees lost Spy evs)) = (A : lost)";
by (etac ns_public.induct 1);
by (prove_simple_subgoals_tac 1);
by (Fake_parts_insert_tac 1);
qed "Spy_see_priK";
Addsimps [Spy_see_priK];

goal thy 
 "!!evs. evs : ns_public \
\        ==> (Key (priK A) : analz (sees lost Spy evs)) = (A : lost)";
by (auto_tac(!claset addDs [impOfSubs analz_subset_parts], !simpset));
qed "Spy_analz_priK";
Addsimps [Spy_analz_priK];

goal thy  "!!A. [| Key (priK A) : parts (sees lost Spy evs);       \
\                  evs : ns_public |] ==> A:lost";
by (blast_tac (!claset addDs [Spy_see_priK]) 1);
qed "Spy_see_priK_D";

bind_thm ("Spy_analz_priK_D", analz_subset_parts RS subsetD RS Spy_see_priK_D);
AddSDs [Spy_see_priK_D, Spy_analz_priK_D];


fun analz_induct_tac i = 
    etac ns_public.induct i   THEN
    ALLGOALS (asm_simp_tac 
              (!simpset addsimps [not_parts_not_analz]
                        setloop split_tac [expand_if]));

(**** Authenticity properties obtained from NS2 ****)

(*It is impossible to re-use a nonce in both NS1 and NS2, provided the nonce
  is secret.  (Honest users generate fresh nonces.)*)
goal thy 
 "!!evs. [| Nonce NA ~: analz (sees lost Spy evs);  \
\           Crypt (pubK B) {|Nonce NA, Agent A|} : parts (sees lost Spy evs); \
\           evs : ns_public |]                      \
\ ==> Crypt (pubK C) {|NA', Nonce NA, Agent D|} ~: parts (sees lost Spy evs)";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*NS3*)
by (blast_tac (!claset addSEs partsEs) 4);
(*NS2*)
by (blast_tac (!claset addSEs partsEs) 3);
(*Fake*)
by (blast_tac (!claset addSIs [analz_insertI]
                        addDs [impOfSubs analz_subset_parts,
			       impOfSubs Fake_parts_insert]) 2);
(*Base*)
by (Blast_tac 1);
qed "no_nonce_NS1_NS2";


(*Unicity for NS1: nonce NA identifies agents A and B*)
goal thy 
 "!!evs. [| Nonce NA ~: analz (sees lost Spy evs);  evs : ns_public |]      \
\ ==> EX A' B'. ALL A B.                                                    \
\      Crypt (pubK B) {|Nonce NA, Agent A|} : parts (sees lost Spy evs) --> \
\      A=A' & B=B'";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*NS1*)
by (simp_tac (!simpset addsimps [all_conj_distrib]) 3);
by (expand_case_tac "NA = ?y" 3 THEN
    REPEAT (blast_tac (!claset addSEs partsEs) 3));
(*Base*)
by (Blast_tac 1);
(*Fake*)
by (simp_tac (!simpset addsimps [all_conj_distrib, parts_insert_sees]) 1);
by (step_tac (!claset addSIs [analz_insertI]) 1);
by (ex_strip_tac 1);
by (blast_tac (!claset delrules [conjI]
                      addSDs [impOfSubs Fake_parts_insert]
                      addDs  [impOfSubs analz_subset_parts]) 1);
val lemma = result();

goal thy 
 "!!evs. [| Crypt(pubK B)  {|Nonce NA, Agent A|}  : parts(sees lost Spy evs); \
\           Crypt(pubK B') {|Nonce NA, Agent A'|} : parts(sees lost Spy evs); \
\           Nonce NA ~: analz (sees lost Spy evs);                            \
\           evs : ns_public |]                                                \
\        ==> A=A' & B=B'";
by (prove_unique_tac lemma 1);
qed "unique_NA";


(*Secrecy: Spy does not see the nonce sent in msg NS1 if A and B are secure*)
goal thy 
 "!!evs. [| Says A B (Crypt(pubK B) {|Nonce NA, Agent A|}) : set evs; \
\           A ~: lost;  B ~: lost;  evs : ns_public |]                        \
\        ==>  Nonce NA ~: analz (sees lost Spy evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*NS3*)
by (blast_tac (!claset addDs  [Says_imp_sees_Spy' RS parts.Inj]
                       addEs  [no_nonce_NS1_NS2 RSN (2, rev_notE)]) 4);
(*NS2*)
by (blast_tac (!claset addSEs [MPair_parts]
		       addDs  [Says_imp_sees_Spy' RS parts.Inj,
			       parts.Body, unique_NA]) 3);
(*NS1*)
by (blast_tac (!claset addSEs sees_Spy_partsEs
                      addIs  [impOfSubs analz_subset_parts]) 2);
(*Fake*)
by (spy_analz_tac 1);
qed "Spy_not_see_NA";


(*Authentication for A: if she receives message 2 and has used NA
  to start a run, then B has sent message 2.*)
goal thy 
 "!!evs. [| Says A B (Crypt (pubK B) {|Nonce NA, Agent A|}) : set evs;\
\           Says B' A (Crypt(pubK A) {|Nonce NA, Nonce NB, Agent B|}) \
\             : set evs;\
\           A ~: lost;  B ~: lost;  evs : ns_public |]  \
\        ==> Says B A (Crypt(pubK A) {|Nonce NA, Nonce NB, Agent B|}) \
\              : set evs";
by (etac rev_mp 1);
(*prepare induction over Crypt (pubK A) {|NA,NB,B|} : parts H*)
by (etac (Says_imp_sees_Spy' RS parts.Inj RS rev_mp) 1);
by (etac ns_public.induct 1);
by (ALLGOALS Asm_simp_tac);
(*NS1*)
by (blast_tac (!claset addSEs sees_Spy_partsEs) 2);
(*Fake*)
by (blast_tac (!claset addSDs [impOfSubs Fake_parts_insert]
                       addDs  [Spy_not_see_NA, 
			       impOfSubs analz_subset_parts]) 1);
qed "A_trusts_NS2";

(*If the encrypted message appears then it originated with Alice in NS1*)
goal thy 
 "!!evs. [| Crypt (pubK B) {|Nonce NA, Agent A|} : parts (sees lost Spy evs); \
\           Nonce NA ~: analz (sees lost Spy evs);                 \
\           evs : ns_public |]                                     \
\   ==> Says A B (Crypt (pubK B) {|Nonce NA, Agent A|}) : set evs";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*Fake*)
by (blast_tac (!claset addSDs [impOfSubs Fake_parts_insert]
                       addIs  [analz_insertI]
                       addDs  [impOfSubs analz_subset_parts]) 2);
(*Base*)
by (Blast_tac 1);
qed "B_trusts_NS1";



(**** Authenticity properties obtained from NS2 ****)

(*Unicity for NS2: nonce NB identifies nonce NA and agents A, B 
  [unicity of B makes Lowe's fix work]
  [proof closely follows that for unique_NA] *)
goal thy 
 "!!evs. [| Nonce NB ~: analz (sees lost Spy evs);  evs : ns_public |]      \
\ ==> EX A' NA' B'. ALL A NA B.                                             \
\      Crypt (pubK A) {|Nonce NA, Nonce NB, Agent B|}                       \
\        : parts (sees lost Spy evs)  -->  A=A' & NA=NA' & B=B'";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*NS2*)
by (simp_tac (!simpset addsimps [all_conj_distrib]) 3);
by (expand_case_tac "NB = ?y" 3 THEN
    REPEAT (blast_tac (!claset addSEs partsEs) 3));
(*Base*)
by (Blast_tac 1);
(*Fake*)
by (simp_tac (!simpset addsimps [all_conj_distrib, parts_insert_sees]) 1);
by (step_tac (!claset addSIs [analz_insertI]) 1);
by (ex_strip_tac 1);
by (blast_tac (!claset delrules [conjI]
                      addSDs [impOfSubs Fake_parts_insert]
                      addDs  [impOfSubs analz_subset_parts]) 1);
val lemma = result();

goal thy 
 "!!evs. [| Crypt(pubK A)  {|Nonce NA, Nonce NB, Agent B|}   \
\             : parts(sees lost Spy evs);                    \
\           Crypt(pubK A') {|Nonce NA', Nonce NB, Agent B'|} \
\             : parts(sees lost Spy evs);                    \
\           Nonce NB ~: analz (sees lost Spy evs);           \
\           evs : ns_public |]                               \
\        ==> A=A' & NA=NA' & B=B'";
by (prove_unique_tac lemma 1);
qed "unique_NB";


(*Secrecy: Spy does not see the nonce sent in msg NS2 if A and B are secure*)
goal thy 
 "!!evs. [| Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB, Agent B|}) \
\             : set evs;                                      \
\           A ~: lost;  B ~: lost;  evs : ns_public |]                \
\ ==> Nonce NB ~: analz (sees lost Spy evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*NS3*)
by (blast_tac (!claset addDs [Says_imp_sees_Spy' RS parts.Inj,
			      unique_NB]) 4);
(*NS1*)
by (blast_tac (!claset addSEs sees_Spy_partsEs) 2);
(*Fake*)
by (spy_analz_tac 1);
(*NS2*)
by (Step_tac 1);
by (blast_tac (!claset addSEs sees_Spy_partsEs) 3);
by (blast_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
                       addEs  [no_nonce_NS1_NS2 RSN (2, rev_notE)]) 2);
by (blast_tac (!claset addSIs [impOfSubs analz_subset_parts]) 1);
qed "Spy_not_see_NB";


(*Authentication for B: if he receives message 3 and has used NB
  in message 2, then A has sent message 3.*)
goal thy 
 "!!evs. [| Says B A  (Crypt (pubK A) {|Nonce NA, Nonce NB, Agent B|}) \
\             : set evs;                                       \
\           Says A' B (Crypt (pubK B) (Nonce NB)): set evs;    \
\           A ~: lost;  B ~: lost;  evs : ns_public |]                 \
\        ==> Says A B (Crypt (pubK B) (Nonce NB)) : set evs";
by (etac rev_mp 1);
(*prepare induction over Crypt (pubK B) NB : parts H*)
by (etac (Says_imp_sees_Spy' RS parts.Inj RS rev_mp) 1);
by (analz_induct_tac 1);
(*NS1*)
by (blast_tac (!claset addSEs sees_Spy_partsEs) 2);
(*Fake*)
by (blast_tac (!claset addSDs [impOfSubs Fake_parts_insert]
                       addDs  [Spy_not_see_NB, 
			       impOfSubs analz_subset_parts]) 1);
(*NS3; not clear why blast_tac needs to be preceeded by Step_tac*)
by (Step_tac 1);
by (blast_tac (!claset addDs [Says_imp_sees_Spy' RS parts.Inj,
			      Spy_not_see_NB, unique_NB]) 1);
qed "B_trusts_NS3";


(**** Overall guarantee for B*)

(*Matches only NS2, not NS1 (or NS3)*)
val Says_imp_sees_Spy'' = 
    read_instantiate [("X","Crypt ?K {|?XX,?YY,?ZZ|}")] Says_imp_sees_Spy';


(*If B receives NS3 and the nonce NB agrees with the nonce he joined with
  NA, then A initiated the run using NA.  SAME proof as B_trusts_NS3!*)
goal thy 
 "!!evs. [| Says B A  (Crypt (pubK A) {|Nonce NA, Nonce NB, Agent B|}) \
\             : set evs;                                       \
\           Says A' B (Crypt (pubK B) (Nonce NB)): set evs;    \
\           A ~: lost;  B ~: lost;  evs : ns_public |]                 \
\    ==> Says A B (Crypt (pubK B) {|Nonce NA, Agent A|}) : set evs";
by (etac rev_mp 1);
(*prepare induction over Crypt (pubK B) {|NB|} : parts H*)
by (etac (Says_imp_sees_Spy' RS parts.Inj RS rev_mp) 1);
by (etac ns_public.induct 1);
by (ALLGOALS Asm_simp_tac);
(*Fake, NS2, NS3*)
(*NS1*)
by (blast_tac (!claset addSEs sees_Spy_partsEs) 2);
(*Fake*)
by (REPEAT_FIRST (resolve_tac [impI, conjI]));
by (Blast_tac 1);
by (forward_tac [Spy_not_see_NB] 1 THEN REPEAT (assume_tac 1));
by (blast_tac (!claset addSIs [disjI2]
                      addDs [impOfSubs analz_subset_parts,
                             impOfSubs Fake_parts_insert]) 1);
(*NS3*)
by (Step_tac 1);
by (forward_tac [Spy_not_see_NB] 1 THEN REPEAT (assume_tac 1));
by (blast_tac (!claset addSDs [Says_imp_sees_Spy'' RS parts.Inj]
                       addDs  [unique_NB]) 1);
qed "B_trusts_protocol";

