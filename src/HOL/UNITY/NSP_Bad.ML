(*  Title:      HOL/Auth/NSP_Bad
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Inductive relation "ns_public" for the Needham-Schroeder Public-Key protocol.
Flawed version, vulnerable to Lowe's attack.

From page 260 of
  Burrows, Abadi and Needham.  A Logic of Authentication.
  Proc. Royal Soc. 426 (1989)
*)

AddEs spies_partsEs;
AddDs [impOfSubs analz_subset_parts];
AddDs [impOfSubs Fake_parts_insert];

AddIffs [Spy_in_bad];

(*For other theories, e.g. Mutex and Lift, using AddIffs slows proofs down.
  Here, it facilitates re-use of the Auth proofs.*)

AddIffs (map simp_of_act [Fake_def, NS1_def, NS2_def, NS3_def]);

Addsimps [Nprg_def RS def_prg_simps];


(*A "possibility property": there are traces that reach the end*)
Goal "A ~= B ==> EX NB. EX s: reachable Nprg.                \
\                  Says A B (Crypt (pubK B) (Nonce NB)) : set s";
by (REPEAT (resolve_tac [exI,bexI] 1));
by (res_inst_tac [("act", "NS3")] reachable.Acts 2);
by (res_inst_tac [("act", "NS2")] reachable.Acts 3);
by (res_inst_tac [("act", "NS1")] reachable.Acts 4);
by (rtac reachable.Init 5);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [Nprg_def])));
by (REPEAT_FIRST (rtac exI ));
by possibility_tac;
result();


(**** Inductive proofs about ns_public ****)

(*can be used to simulate analz_mono_contra_tac
val analz_impI = read_instantiate_sg (sign_of thy)
                [("P", "?Y ~: analz (spies ?evs)")] impI;

val spies_Says_analz_contraD = 
    spies_subset_spies_Says RS analz_mono RS contra_subsetD;

by (rtac analz_impI 2);
by (auto_tac (claset() addSDs [spies_Says_analz_contraD], simpset()));
*)

val parts_induct_tac = 
  (SELECT_GOAL o EVERY)
     [etac reachable.induct 1,
      Force_tac 1,
      Full_simp_tac 1,
      safe_tac (claset() delrules [impI,impCE]),
      REPEAT (FIRSTGOAL analz_mono_contra_tac),
      ALLGOALS Asm_simp_tac];


(** Theorems of the form X ~: parts (spies evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's private key! (unless it's bad at start)*)
(*
    Goal "Nprg : Always {s. (Key (priK A) : parts (spies s)) = (A : bad)}";
    by (rtac AlwaysI 1);
    by (Force_tac 1);
    by (constrains_tac 1);
    by Auto_tac;
    qed "Spy_see_priK";
*)

Goal "s : reachable Nprg ==> (Key (priK A) : parts (spies s)) = (A : bad)";
by (etac reachable.induct 1);
by (ALLGOALS Force_tac);
qed "Spy_see_priK";
Addsimps [Spy_see_priK];

Goal "s : reachable Nprg ==> (Key (priK A) : analz (spies s)) = (A : bad)";
by Auto_tac;
qed "Spy_analz_priK";
Addsimps [Spy_analz_priK];

AddSDs [Spy_see_priK RSN (2, rev_iffD1), 
	Spy_analz_priK RSN (2, rev_iffD1)];


(**** Authenticity properties obtained from NS2 ****)

(*It is impossible to re-use a nonce in both NS1 and NS2, provided the nonce
  is secret.  (Honest users generate fresh nonces.)*)
Goal "[| Crypt (pubK B) {|Nonce NA, Agent A|} : parts (spies s); \
\        Nonce NA ~: analz (spies s);   s : reachable Nprg |]       \
\     ==> Crypt (pubK C) {|NA', Nonce NA|} ~: parts (spies s)";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS Blast_tac);
qed "no_nonce_NS1_NS2";

(*Adding it to the claset slows down proofs...*)
val nonce_NS1_NS2_E = no_nonce_NS1_NS2 RSN (2, rev_notE);


(*Unicity for NS1: nonce NA identifies agents A and B*)
Goal "[| Nonce NA ~: analz (spies s);  s : reachable Nprg |]      \
\     ==> EX A' B'. ALL A B.                                            \
\            Crypt (pubK B) {|Nonce NA, Agent A|} : parts (spies s) --> \
\               A=A' & B=B'";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS (simp_tac (simpset() addsimps [all_conj_distrib])));
(*NS1*)
by (expand_case_tac "NA = ?y" 2 THEN Blast_tac 2);
(*Fake*)
by (Blast_tac 1);
val lemma = result();

Goal "[| Crypt(pubK B)  {|Nonce NA, Agent A|}  : parts(spies s); \
\        Crypt(pubK B') {|Nonce NA, Agent A'|} : parts(spies s); \
\        Nonce NA ~: analz (spies s);                            \
\        s : reachable Nprg |]                                   \
\     ==> A=A' & B=B'";
by (prove_unique_tac lemma 1);
qed "unique_NA";


(*Tactic for proving secrecy theorems*)
val analz_induct_tac = 
  (SELECT_GOAL o EVERY)
     [etac reachable.induct 1,
      Force_tac 1,
      Full_simp_tac 1,
      safe_tac (claset() delrules [impI,impCE]),
      ALLGOALS Asm_simp_tac];



(*Secrecy: Spy does not see the nonce sent in msg NS1 if A and B are secure*)
Goal "[| Says A B (Crypt(pubK B) {|Nonce NA, Agent A|}) : set s;   \
\        A ~: bad;  B ~: bad;  s : reachable Nprg |]                    \
\     ==>  Nonce NA ~: analz (spies s)";
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
Goal "[| Says A  B (Crypt(pubK B) {|Nonce NA, Agent A|}) : set s;  \
\        Says B' A (Crypt(pubK A) {|Nonce NA, Nonce NB|}): set s;  \
\        A ~: bad;  B ~: bad;  s : reachable Nprg |]                    \
\     ==> Says B A (Crypt(pubK A) {|Nonce NA, Nonce NB|}): set s";
by (etac rev_mp 1);
(*prepare induction over Crypt (pubK A) {|NA,NB|} : parts H*)
by (etac (Says_imp_spies RS parts.Inj RS rev_mp) 1);
by (parts_induct_tac 1);
by (ALLGOALS Clarify_tac);
(*NS2*)
by (blast_tac (claset() addDs [Spy_not_see_NA, unique_NA]) 3);
(*NS1*)
by (Blast_tac 2);
(*Fake*)
by (blast_tac (claset() addDs [Spy_not_see_NA]) 1);
qed "A_trusts_NS2";


(*If the encrypted message appears then it originated with Alice in NS1*)
Goal "[| Crypt (pubK B) {|Nonce NA, Agent A|} : parts (spies s); \
\        Nonce NA ~: analz (spies s);                            \
\        s : reachable Nprg |]                                        \
\     ==> Says A B (Crypt (pubK B) {|Nonce NA, Agent A|}) : set s";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (Blast_tac 1);
qed "B_trusts_NS1";



(**** Authenticity properties obtained from NS2 ****)

(*Unicity for NS2: nonce NB identifies nonce NA and agent A
  [proof closely follows that for unique_NA] *)
Goal "[| Nonce NB ~: analz (spies s);  s : reachable Nprg |]         \
\     ==> EX A' NA'. ALL A NA.                                       \
\           Crypt (pubK A) {|Nonce NA, Nonce NB|} : parts (spies s)  \
\                -->  A=A' & NA=NA'";
by (etac rev_mp 1);
by (parts_induct_tac 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [all_conj_distrib])));
(*NS2*)
by (expand_case_tac "NB = ?y" 2 THEN Blast_tac 2);
(*Fake*)
by (Blast_tac 1);
val lemma = result();

Goal "[| Crypt(pubK A) {|Nonce NA, Nonce NB|}  : parts(spies s); \
\        Crypt(pubK A'){|Nonce NA', Nonce NB|} : parts(spies s); \
\        Nonce NB ~: analz (spies s);                            \
\        s : reachable Nprg |]                                        \
\     ==> A=A' & NA=NA'";
by (prove_unique_tac lemma 1);
qed "unique_NB";


(*NB remains secret PROVIDED Alice never responds with round 3*)
Goal "[| Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set s;  \
\       ALL C. Says A C (Crypt (pubK C) (Nonce NB)) ~: set s;      \
\       A ~: bad;  B ~: bad;  s : reachable Nprg |]                     \
\    ==> Nonce NB ~: analz (spies s)";
by (etac rev_mp 1);
by (etac rev_mp 1);
by (analz_induct_tac 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [all_conj_distrib])));
by (ALLGOALS Clarify_tac);
(*NS3: because NB determines A*)
by (blast_tac (claset() addDs [unique_NB]) 4);
(*NS2: by freshness and unicity of NB*)
by (blast_tac (claset() addEs [nonce_NS1_NS2_E]) 3);
(*NS1: by freshness*)
by (Blast_tac 2);
(*Fake*)
by (spy_analz_tac 1);
qed "Spy_not_see_NB";



(*Authentication for B: if he receives message 3 and has used NB
  in message 2, then A has sent message 3--to somebody....*)
Goal "[| Says B A  (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set s; \
\        Says A' B (Crypt (pubK B) (Nonce NB)): set s;              \
\        A ~: bad;  B ~: bad;  s : reachable Nprg |]                \
\     ==> EX C. Says A C (Crypt (pubK C) (Nonce NB)) : set s";
by (etac rev_mp 1);
(*prepare induction over Crypt (pubK B) NB : parts H*)
by (etac (Says_imp_spies RS parts.Inj RS rev_mp) 1);
by (parts_induct_tac 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [ex_disj_distrib])));
by (ALLGOALS Clarify_tac);
(*NS3: because NB determines A (this use of unique_NB is more robust) *)
by (blast_tac (claset() addDs [Spy_not_see_NB]
			addIs [unique_NB RS conjunct1]) 3);
(*NS1: by freshness*)
by (Blast_tac 2);
(*Fake*)
by (blast_tac (claset() addDs [Spy_not_see_NB]) 1);
qed "B_trusts_NS3";


(*Can we strengthen the secrecy theorem?  NO*)
Goal "[| A ~: bad;  B ~: bad;  s : reachable Nprg |]           \
\     ==> Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set s \
\           --> Nonce NB ~: analz (spies s)";
by (analz_induct_tac 1);
by (ALLGOALS Clarify_tac);
(*NS2: by freshness and unicity of NB*)
by (blast_tac (claset() addEs [nonce_NS1_NS2_E]) 3);
(*NS1: by freshness*)
by (Blast_tac 2);
(*Fake*)
by (spy_analz_tac 1);
(*NS3: unicity of NB identifies A and NA, but not B*)
by (forw_inst_tac [("A'","A")] (Says_imp_spies RS parts.Inj RS unique_NB) 1
    THEN REPEAT (eresolve_tac [asm_rl, Says_imp_spies RS parts.Inj] 1));
by Auto_tac;
by (rename_tac "s B' C" 1);

(*
THIS IS THE ATTACK!
Level 8
!!s. [| A ~: bad; B ~: bad; s : reachable Nprg |]
       ==> Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set s -->
           Nonce NB ~: analz (spies s)
 1. !!s B' C.
       [| A ~: bad; B ~: bad; s : reachable Nprg;
          Says A C (Crypt (pubK C) {|Nonce NA, Agent A|}) : set s;
          Says B' A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set s; C : bad;
          Says B A (Crypt (pubK A) {|Nonce NA, Nonce NB|}) : set s;
          Nonce NB ~: analz (spies s) |]
       ==> False
*)
