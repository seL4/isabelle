(*  Title:      HOL/UNITY/Common
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Common Meeting Time example from Misra (1994)

The state is identified with the one variable in existence.

From Misra, "A Logic for Concurrent Programming" (1994), sections 5.1 and 13.1.
*)


open Common;

(*Misra's property CMT4: t exceeds no common meeting time*)
goal thy
  "!!Acts. [| ALL m. constrains Acts {m} (maxfg m); n: common |] \
\           ==> stable Acts (atMost n)";
by (dres_inst_tac [("P", "%t. t<=n")] elimination_sing 1);
by (asm_full_simp_tac
    (simpset() addsimps [atMost_def, stable_def, common_def, maxfg_def,
			 constrains_def, le_max_iff_disj]) 1);
by (Clarify_tac 1);
by (dtac bspec 1);
by (assume_tac 1);
by (blast_tac (claset() addSEs [subsetCE]
			addIs [order_eq_refl, fmono, gmono, le_trans]) 1);
qed "common_stable";

goal thy
  "!!Acts. [| ALL m. constrains Acts {m} (maxfg m); n: common |] \
\           ==> reachable {0} Acts <= atMost n";
by (rtac strongest_invariant 1);
by (asm_simp_tac (simpset() addsimps [common_stable]) 2);
by (simp_tac (simpset() addsimps [atMost_def]) 1);
qed "common_invariant";


(*** Some programs that implement the safety property above ***)

(*This one is just Skip*)
goal thy "constrains {id} {m} (maxfg m)";
by (simp_tac (simpset() addsimps [constrains_def, maxfg_def, le_max_iff_disj,
				  fasc, gasc]) 1);
result();

(*This one is  t := ftime t || t := gtime t    really needs Skip too*)
goal thy "constrains {range(%t.(t,ftime t)), range(%t.(t,gtime t))} \
\                    {m} (maxfg m)";
by (simp_tac (simpset() addsimps [constrains_def, maxfg_def, 
				  le_max_iff_disj]) 1);
by (Blast_tac 1);
result();

(*This one is  t := max (ftime t) (gtime t)    really needs Skip too*)
goal thy "constrains {range(%t.(t, max (ftime t) (gtime t)))} \
\                    {m} (maxfg m)";
by (simp_tac (simpset() addsimps [constrains_def, maxfg_def]) 1);
by (Blast_tac 1);
result();

(*This one is  t := t+1 if t <max (ftime t) (gtime t) *)
goalw thy [constrains_def, maxfg_def] 
    "constrains { {(t, Suc t) | t. t < max (ftime t) (gtime t)} } \
\               {m} (maxfg m)";
by (blast_tac (claset() addIs [Suc_leI]) 1);
result();


(*It remans to prove that they satisfy CMT3': t does not decrease,
  and that CMT3' implies that t stops changing once common(t) holds.*)


(*** Progress under weak fairness ***)

Addsimps [atMost_Int_atLeast];

goal thy
    "!!Acts. [| ALL m. constrains Acts {m} (maxfg m); \
\               ALL m: lessThan n. leadsTo Acts {m} (greaterThan m); \
\               n: common;  id: Acts |]  \
\            ==> leadsTo Acts (atMost n) common";
by (rtac leadsTo_weaken_R 1);
by (res_inst_tac [("f","%x. x"), ("l", "n")] greaterThan_bounded_induct 1);
by (ALLGOALS Asm_simp_tac);
by (rtac subset_refl 2);
by (blast_tac (claset() addDs [PSP_stable2] 
                        addIs [common_stable, leadsTo_weaken_R]) 1);
val lemma = result();

(*The "ALL m: Compl common" form echoes CMT6.*)
goal thy
    "!!Acts. [| ALL m. constrains Acts {m} (maxfg m); \
\               ALL m: Compl common. leadsTo Acts {m} (greaterThan m); \
\               n: common;  id: Acts |]  \
\            ==> leadsTo Acts (atMost (LEAST n. n: common)) common";
by (rtac lemma 1);
by (ALLGOALS Asm_simp_tac);
by (etac LeastI 2);
by (blast_tac (claset() addSDs [not_less_Least]) 1);
qed "leadsTo_common";
