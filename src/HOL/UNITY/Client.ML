(*  Title:      HOL/UNITY/Client
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Distributed Resource Management System: the Client
*)


(*Perhaps move to SubstAx.ML*)
Goal "[| F : Stable A;  F : transient C;  \
\        reachable F <= (-A Un B Un C) |] ==> F : LeadsTo A B";
by (etac reachable_LeadsTo_weaken 1);
by (rtac LeadsTo_Diff 1);
by (etac (transient_imp_leadsTo RS leadsTo_imp_LeadsTo RS PSP_stable2) 2);
by (ALLGOALS (blast_tac (claset() addIs [subset_imp_LeadsTo])));
qed "Stable_transient_reachable_LeadsTo";



(*split_all_tac causes a big blow-up*)
claset_ref() := claset() delSWrapper "split_all_tac";

Addsimps [Cli_prg_def RS def_prg_Init];
program_defs_ref := [Cli_prg_def];

Addsimps (map simp_of_act [rel_act_def, tok_act_def, ask_act_def]);

(*Simplification for records*)
Addsimps (thms"state.update_defs");

(*CAN THIS be generalized?
  Importantly, the second case considers actions that are in G
  and NOT in Cli_prg (needed to use localTo_imp_equals) *)
Goal "(act : Acts (Cli_prg Join G)) = \
\      (act : {Id, rel_act, tok_act, ask_act} | \
\       act : Acts G & act ~: Acts Cli_prg)";
by (asm_full_simp_tac (simpset() addsimps [Cli_prg_def, Acts_Join]) 1);
(*don't unfold definitions of actions*)
by (blast_tac HOL_cs 1);
qed "Acts_Cli_Join_eq";


fun invariant_tac i = 
    rtac invariantI i  THEN
    constrains_tac (i+1);

(*Safety property 1(a): ask is nondecreasing*)
Goalw [increasing_def] "Cli_prg: increasing ask";
by (Clarify_tac 1);
by (constrains_tac 1);
by Auto_tac;
qed "increasing_ask";

(*Safety property 1(b): rel is nondecreasing*)
Goalw [increasing_def] "Cli_prg: increasing rel";
by (Clarify_tac 1);
by (constrains_tac 1);
by Auto_tac;
qed "increasing_rel";

Addsimps [nth_append, append_one_prefix];

Goal "Cli_prg: invariant {s. tok s <= Max}";
by (invariant_tac 1);
by Auto_tac;
qed "tok_bounded";

(*Safety property 3: no client requests "too many" tokens.
      With no Substitution Axiom, we must prove the two invariants 
  simultaneously.  Could combine tok_bounded, stable_constrains_stable 
  and a rule invariant_implies_stable...
*)
Goal "Cli_prg:                             \
\       invariant ({s. tok s <= Max}  Int  \
\                  {s. ALL n: lessThan (length (ask s)). ask s!n <= Max})";
by (invariant_tac 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
qed "ask_bounded";


(*We no longer need constrains_tac to expand the program definition, and 
  expanding it is extremely expensive!  Instead, Acts_Cli_Join_eq expands
  the program.*)
program_defs_ref := [];

(*Safety property 2: clients return the right number of tokens*)
Goalw [increasing_def]
      "Cli_prg : (increasing giv Int (rel localTo Cli_prg))  \
\                guarantees invariant {s. rel s <= giv s}";
by (rtac guaranteesI 1);
by (invariant_tac 1);
by (Force_tac 1);
by (subgoal_tac "rel s <= giv s'" 1);
by (force_tac (claset(),
	       simpset() addsimps [stable_def, constrains_def]) 2);
by (dtac (Acts_Cli_Join_eq RS iffD1) 1);
(*we note that "rel" is local to Client*)
by (auto_tac (claset() addD2 ("x",localTo_imp_equals), simpset()));
qed "ok_guar_rel_prefix_giv";


(*** Towards proving the liveness property ***)

Goal "Cli_prg Join G   \
\       : transient {s. length (giv s) = Suc k &  \
\                       length (rel s) = k & ask s ! k <= giv s ! k}";
by (res_inst_tac [("act", "rel_act")] transient_mem 1);
by (auto_tac (claset(),
	      simpset() addsimps [Domain_def, Acts_Join, Cli_prg_def]));
qed "transient_lemma";

Goal "Cli_prg : \
\      (increasing giv Int (rel localTo Cli_prg) Int (ask localTo Cli_prg) \
\                 Int invariant giv_meets_ask) \
\      guarantees invariant {s. length (ask s) <= Suc (length (rel s)) & \
\                               length (rel s) <= length (giv s)}";
by (rtac guaranteesI 1);
by (Clarify_tac 1);
by (dtac (impOfSubs increasing_length) 1);
by (invariant_tac 1);
by (Force_tac 1);
by (dtac (Acts_Cli_Join_eq RS iffD1) 1);
by (auto_tac (claset() addD2 ("x",localTo_imp_equals), simpset()));
by (force_tac (claset(),
	       simpset() addsimps [increasing_def, Acts_Join, stable_def, 
				   constrains_def]) 1);
val lemma1 = result();


Goal "Cli_prg : \
\      (increasing giv Int (rel localTo Cli_prg) Int (ask localTo Cli_prg) \
\                 Int invariant giv_meets_ask) \
\      guarantees (LeadsTo {s. k < length (giv s)}    \
\                          {s. k < length (rel s)})";
by (rtac guaranteesI 1);
by (Clarify_tac 1);
by (rtac Stable_transient_reachable_LeadsTo 1);
by (res_inst_tac [("k", "k")] transient_lemma 2);
by (rtac stable_imp_Stable 1);
by (dtac (impOfSubs increasing_length) 1);
by (force_tac (claset(),
	       simpset() addsimps [increasing_def, 
				   stable_def, constrains_def]) 1);
(** LEVEL 7 **)
(*         Invariant (Cli_prg Join G)
              (- {s. k < length (giv s)} Un {s. k < length (rel s)} Un
               {s. length (giv s) = Suc k &
                   length (rel s) = k & ask s ! k <= giv s ! k})
*)
by (rtac (make_elim (lemma1 RS guaranteesD)) 1);
by (Blast_tac 1);
by (auto_tac (claset() addSDs [invariant_includes_reachable],
	      simpset() addsimps [giv_meets_ask_def]));
qed "client_correct";
