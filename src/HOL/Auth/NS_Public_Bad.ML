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

proof_timing:=true;
HOL_quantifiers := false;

val op addss = op unsafe_addss;

AddIffs [Spy_in_lost];

(*Replacing the variable by a constant improves search speed by 50%!*)
val Says_imp_sees_Spy' = 
    read_instantiate_sg (sign_of thy) [("lost","lost")] Says_imp_sees_Spy;


(*A "possibility property": there are traces that reach the end*)
goal thy 
 "!!A B. A ~= B ==> EX NB. EX evs: ns_public.               \
\                     Says A B (Crypt (pubK B) (Nonce NB)) : set_of_list evs";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (rtac (ns_public.Nil RS ns_public.NS1 RS ns_public.NS2 RS ns_public.NS3) 2);
by possibility_tac;
result();


(**** Inductive proofs about ns_public ****)

(*Nobody sends themselves messages*)
goal thy "!!evs. evs : ns_public ==> ALL A X. Says A A X ~: set_of_list evs";
by (etac ns_public.induct 1);
by (Auto_tac());
qed_spec_mp "not_Says_to_self";
Addsimps [not_Says_to_self];
AddSEs   [not_Says_to_self RSN (2, rev_notE)];


(*For proving the easier theorems about X ~: parts (sees lost Spy evs) *)
fun parts_induct_tac i = SELECT_GOAL
    (DETERM (etac ns_public.induct 1 THEN 
             (*Fake message*)
             TRY (best_tac (!claset addDs [impOfSubs analz_subset_parts,
                                           impOfSubs Fake_parts_insert]
                                    addss (!simpset)) 2)) THEN
     (*Base case*)
     fast_tac (!claset addss (!simpset)) 1 THEN
     ALLGOALS Asm_simp_tac) i;

(** Theorems of the form X ~: parts (sees lost Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's private key! (unless it's lost at start)*)
goal thy 
 "!!evs. evs : ns_public \
\        ==> (Key (priK A) : parts (sees lost Spy evs)) = (A : lost)";
by (parts_induct_tac 1);
by (Auto_tac());
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
by (fast_tac (!claset addDs [Spy_see_priK]) 1);
qed "Spy_see_priK_D";

bind_thm ("Spy_analz_priK_D", analz_subset_parts RS subsetD RS Spy_see_priK_D);
AddSDs [Spy_see_priK_D, Spy_analz_priK_D];


fun analz_induct_tac i = 
    etac ns_public.induct i     THEN
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
\ ==> Crypt (pubK C) {|NA', Nonce NA|} ~: parts (sees lost Spy evs)";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*NS3*)
by (fast_tac (!claset addSEs partsEs) 4);
(*NS2*)
by (fast_tac (!claset addSEs partsEs) 3);
(*Fake*)
by (deepen_tac (!claset addSIs [analz_insertI]
                        addDs [impOfSubs analz_subset_parts,
			       impOfSubs Fake_parts_insert]
			addss (!simpset)) 0 2);
(*Base*)
by (fast_tac (!claset addss (!simpset)) 1);
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
    REPEAT (fast_tac (!claset addSEs partsEs) 3));
(*Base*)
by (fast_tac (!claset addss (!simpset)) 1);
(*Fake*)
by (simp_tac (!simpset addsimps [all_conj_distrib, parts_insert_sees]) 1);
by (step_tac (!claset addSIs [analz_insertI]) 1);
by (ex_strip_tac 1);
by (best_tac (!claset delrules [conjI]
                      addSDs [impOfSubs Fake_parts_insert]
                      addDs  [impOfSubs analz_subset_parts]
                      addss (!simpset)) 1);
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
 "!!evs. [| Says A B (Crypt(pubK B) {|Nonce NA, Agent A|}) : set_of_list evs; \
\           A ~: lost;  B ~: lost;  evs : ns_public |]                        \
\        ==>  Nonce NA ~: analz (sees lost Spy evs)";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*NS3*)
by (fast_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
                      addEs  [no_nonce_NS1_NS2 RSN (2, rev_notE)]) 4);
(*NS2*)
by (deepen_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
                        addSEs [MPair_parts]
			addDs  [parts.Body, unique_NA]) 0 3);
(*NS1*)
by (fast_tac (!claset addSEs sees_Spy_partsEs
                      addIs  [impOfSubs analz_subset_parts]) 2);
(*Fake*)
by (spy_analz_tac 1);
qed "Spy_not_see_NA";


(*Authentication for A: if she receives message 2 and has used NA
  to start a run, then B has sent message 2.*)
goal thy 
 "!!evs. [| Says A B (Crypt (pubK B) {|Nonce NA, Agent A|}) : set_of_list evs;\
\           Says B' A (Crypt(pubK A) {|Nonce NA, Nonce NB|}): set_of_list evs;\
\           A ~: lost;  B ~: lost;  evs : ns_public |]  \
\        ==> Says B A (Crypt(pubK A) {|Nonce NA, Nonce NB|}): set_of_list evs";
by (etac rev_mp 1);
(*prepare induction over Crypt (pubK A) {|NA,NB|} : parts H*)
by (etac (Says_imp_sees_Spy' RS parts.Inj RS rev_mp) 1);
by (etac ns_public.induct 1);
by (ALLGOALS Asm_simp_tac);
(*NS1*)
by (fast_tac (!claset addSEs sees_Spy_partsEs) 2);
(*Fake*)
by (REPEAT_FIRST (resolve_tac [impI, conjI]));
by (fast_tac (!claset addss (!simpset)) 1);
by (forward_tac [Spy_not_see_NA] 1 THEN REPEAT (assume_tac 1));
by (best_tac (!claset addSIs [disjI2]
                      addSDs [impOfSubs Fake_parts_insert]
                      addDs  [impOfSubs analz_subset_parts]
                      addss (!simpset)) 1);
(*NS2*)
by (Step_tac 1);
by (forward_tac [Spy_not_see_NA] 1 THEN REPEAT (assume_tac 1));
by (deepen_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
                        addDs  [unique_NA]) 1 1);
qed "A_trusts_NS2";

(*If the encrypted message appears then it originated with Alice in NS1*)
goal thy 
 "!!evs. [| Crypt (pubK B) {|Nonce NA, Agent A|} : parts (sees lost Spy evs); \
\           Nonce NA ~: analz (sees lost Spy evs);                 \
\           evs : ns_public |]                                     \
\   ==> Says A B (Crypt (pubK B) {|Nonce NA, Agent A|}) : set_of_list evs";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*Fake*)
by (best_tac (!claset addSIs [disjI2]
                      addSDs [impOfSubs Fake_parts_insert]
                      addIs  [analz_insertI]
                      addDs  [impOfSubs analz_subset_parts]
                      addss (!simpset)) 2);
(*Base*)
by (fast_tac (!claset addss (!simpset)) 1);
qed_spec_mp "B_trusts_NS1";



(**** Authenticity properties obtained from NS2 ****)

(*Unicity for NS2: nonce NB identifies agent A and nonce NA
  [proof closely follows that for unique_NA] *)
goal thy 
 "!!evs. [| Nonce NB ~: analz (sees lost Spy evs);  evs : ns_public |]      \
\ ==> EX A' NA'. ALL A NA.                                                  \
\      Crypt (pubK A) {|Nonce NA, Nonce NB|}                                \
\        : parts (sees lost Spy evs)  -->  A=A' & NA=NA'";
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*NS2*)
by (simp_tac (!simpset addsimps [all_conj_distrib]) 3);
by (expand_case_tac "NB = ?y" 3 THEN
    REPEAT (fast_tac (!claset addSEs partsEs) 3));
(*Base*)
by (fast_tac (!claset addss (!simpset)) 1);
(*Fake*)
by (simp_tac (!simpset addsimps [all_conj_distrib, parts_insert_sees]) 1);
by (step_tac (!claset addSIs [analz_insertI]) 1);
by (ex_strip_tac 1);
by (best_tac (!claset delrules [conjI]
                      addSDs [impOfSubs Fake_parts_insert]
                      addDs  [impOfSubs analz_subset_parts] 
                      addss (!simpset)) 1);
val lemma = result();

goal thy 
 "!!evs. [| Crypt(pubK A) {|Nonce NA, Nonce NB|}  : parts(sees lost Spy evs); \
\           Crypt(pubK A'){|Nonce NA', Nonce NB|} : parts(sees lost Spy evs); \
\           Nonce NB ~: analz (sees lost Spy evs);                            \
\           evs : ns_public |]                                                \
\        ==> A=A' & NA=NA'";
by (prove_unique_tac lemma 1);
qed "unique_NB";


(*NB remains secret PROVIDED Alice never responds with round 3*)
goal thy 
 "!!evs.[| Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set_of_list evs;\
\          (ALL C. Says A C (Crypt (pubK C) (Nonce NB)) ~: set_of_list evs);  \
\          A ~: lost;  B ~: lost;  evs : ns_public |]   \
\       ==> Nonce NB ~: analz (sees lost Spy evs)";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (analz_induct_tac 1);
(*NS1*)
by (fast_tac (!claset addSEs sees_Spy_partsEs) 2);
(*Fake*)
by (spy_analz_tac 1);
(*NS2 and NS3*)
by (ALLGOALS (asm_simp_tac (!simpset addsimps [all_conj_distrib])));
by (step_tac (!claset delrules [allI]) 1);
by (Fast_tac 5);
by (fast_tac (!claset addSIs [impOfSubs analz_subset_parts]) 1);
(*NS2*)
by (fast_tac (!claset addSEs sees_Spy_partsEs) 2);
by (fast_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
                      addEs  [no_nonce_NS1_NS2 RSN (2, rev_notE)]) 1);
(*NS3*)
by (forw_inst_tac [("A'","A")] (Says_imp_sees_Spy' RS parts.Inj RS unique_NB) 1
    THEN REPEAT (eresolve_tac [asm_rl, Says_imp_sees_Spy' RS parts.Inj] 1));
by (Fast_tac 1);
qed "Spy_not_see_NB";



(*Authentication for B: if he receives message 3 and has used NB
  in message 2, then A has sent message 3--to somebody....*)
goal thy 
 "!!evs. [| Says B A  (Crypt (pubK A) {|Nonce NA, Nonce NB|})          \
\             : set_of_list evs;                                       \
\           Says A' B (Crypt (pubK B) (Nonce NB)): set_of_list evs;    \
\           A ~: lost;  B ~: lost;  evs : ns_public |]                 \
\        ==> EX C. Says A C (Crypt (pubK C) (Nonce NB)) : set_of_list evs";
by (etac rev_mp 1);
(*prepare induction over Crypt (pubK B) NB : parts H*)
by (etac (Says_imp_sees_Spy' RS parts.Inj RS rev_mp) 1);
by (analz_induct_tac 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [ex_disj_distrib])));
(*NS1*)
by (fast_tac (!claset addSEs sees_Spy_partsEs) 2);
(*Fake*)
by (REPEAT_FIRST (resolve_tac [impI, conjI]));
by (fast_tac (!claset addss (!simpset)) 1);
by (rtac (ccontr RS disjI2) 1);
by (forward_tac [Spy_not_see_NB] 1 THEN (REPEAT_FIRST assume_tac)
    THEN Fast_tac 1);
by (best_tac (!claset addSDs [impOfSubs Fake_parts_insert]
                      addDs  [impOfSubs analz_subset_parts] 
                      addss (!simpset)) 1);
(*NS3*)
by (Step_tac 1);
by (forward_tac [Spy_not_see_NB] 1 THEN (REPEAT_FIRST assume_tac)
    THEN Fast_tac 1);
by (best_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
                      addDs  [unique_NB]) 1);
qed "B_trusts_NS3";


(*Can we strengthen the secrecy theorem?  NO*)
goal thy 
 "!!evs. [| A ~: lost;  B ~: lost;  evs : ns_public |]   \
\ ==> Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set_of_list evs \
\     --> Nonce NB ~: analz (sees lost Spy evs)";
by (analz_induct_tac 1);
(*NS1*)
by (fast_tac (!claset addSEs partsEs
                      addSDs [Says_imp_sees_Spy' RS parts.Inj]) 2);
(*Fake*)
by (spy_analz_tac 1);
(*NS2 and NS3*)
by (Step_tac 1);
by (fast_tac (!claset addSIs [impOfSubs analz_subset_parts, usedI]) 1);
(*NS2*)
by (fast_tac (!claset addSEs partsEs
                      addSDs [Says_imp_sees_Spy' RS parts.Inj]) 2);
by (fast_tac (!claset addSDs [Says_imp_sees_Spy' RS parts.Inj]
                      addEs  [no_nonce_NS1_NS2 RSN (2, rev_notE)]) 1);
(*NS3*)
by (forw_inst_tac [("A'","A")] (Says_imp_sees_Spy' RS parts.Inj RS unique_NB) 1
    THEN REPEAT (eresolve_tac [asm_rl, Says_imp_sees_Spy' RS parts.Inj] 1));
by (Step_tac 1);

(*
THIS IS THE ATTACK!
Level 9
!!evs. [| A ~: lost; B ~: lost; evs : ns_public |]
       ==> Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|})
           : set_of_list evs -->
           Nonce NB ~: analz (sees lost Spy evs)
 1. !!evs Aa Ba B' NAa NBa evsa.
       [| A ~: lost; B ~: lost; evsa : ns_public; A ~= Ba;
          Says B' A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set_of_list evsa;
          Says A Ba (Crypt (pubK Ba) {|Nonce NA, Agent A|}) : set_of_list evsa;
          Ba : lost;
          Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set_of_list evsa;
          Nonce NB ~: analz (sees lost Spy evsa) |]
       ==> False
*)



