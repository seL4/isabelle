(*  Title:      HOL/UNITY/Common
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Common Meeting Time example from Misra (1994)

The state is identified with the one variable in existence.

From Misra, "A Logic for Concurrent Programming" (1994), sections 5.1 and 13.1.
*)

(*Misra's property CMT4: t exceeds no common meeting time*)
Goal "[| ALL m. Constrains prg {m} (maxfg m); n: common |] \
\     ==> Stable prg (atMost n)";
by (dres_inst_tac [("M", "{t. t<=n}")] Elimination_sing 1);
by (asm_full_simp_tac
    (simpset() addsimps [atMost_def, Stable_def, common_def, maxfg_def,
			 le_max_iff_disj]) 1);
by (etac Constrains_weaken_R 1);
by (blast_tac (claset() addIs [order_eq_refl, fmono, gmono, le_trans]) 1);
qed "common_stable";

Goal "[| Init prg <= atMost n;  \
\        ALL m. Constrains prg {m} (maxfg m); n: common |] \
\     ==> Invariant prg (atMost n)";
by (asm_simp_tac (simpset() addsimps [InvariantI, common_stable]) 1);
qed "common_Invariant";


(*** Some programs that implement the safety property above ***)

(*This one is just Skip*)
Goal "constrains {Id} {m} (maxfg m)";
by (simp_tac (simpset() addsimps [constrains_def, maxfg_def, le_max_iff_disj,
				  fasc, gasc]) 1);
result();

(*This one is  t := ftime t || t := gtime t    really needs Skip too*)
Goal "constrains {range(%t.(t,ftime t)), range(%t.(t,gtime t))} \
\                    {m} (maxfg m)";
by (simp_tac (simpset() addsimps [constrains_def, maxfg_def, 
				  le_max_iff_disj]) 1);
by (Blast_tac 1);
result();

(*This one is  t := max (ftime t) (gtime t)    really needs Skip too*)
Goal "constrains {range(%t.(t, max (ftime t) (gtime t)))} \
\                    {m} (maxfg m)";
by (simp_tac (simpset() addsimps [constrains_def, maxfg_def]) 1);
by (Blast_tac 1);
result();

(*This one is  t := t+1 if t <max (ftime t) (gtime t) *)
Goalw [constrains_def, maxfg_def] 
    "constrains { {(t, Suc t) | t. t < max (ftime t) (gtime t)} } \
\               {m} (maxfg m)";
by (blast_tac (claset() addIs [Suc_leI]) 1);
result();


(*It remans to prove that they satisfy CMT3': t does not decrease,
  and that CMT3' implies that t stops changing once common(t) holds.*)


(*** Progress under weak fairness ***)

Addsimps [atMost_Int_atLeast];

Goal "[| ALL m. Constrains prg {m} (maxfg m); \
\               ALL m: lessThan n. LeadsTo prg {m} (greaterThan m); \
\               n: common |]  \
\            ==> LeadsTo prg (atMost n) common";
by (rtac LeadsTo_weaken_R 1);
by (res_inst_tac [("f","%x. x"), ("l", "n")] GreaterThan_bounded_induct 1);
by (ALLGOALS Asm_simp_tac);
by (rtac subset_refl 2);
by (blast_tac (claset() addDs [PSP_stable2] 
                        addIs [common_stable, LeadsTo_weaken_R]) 1);
val lemma = result();

(*The "ALL m: -common" form echoes CMT6.*)
Goal "[| ALL m. Constrains prg {m} (maxfg m); \
\               ALL m: -common. LeadsTo prg {m} (greaterThan m); \
\               n: common |]  \
\            ==> LeadsTo prg (atMost (LEAST n. n: common)) common";
by (rtac lemma 1);
by (ALLGOALS Asm_simp_tac);
by (etac LeastI 2);
by (blast_tac (claset() addSDs [not_less_Least]) 1);
qed "leadsTo_common";
