(*  Title:      HOL/UNITY/Client
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Distributed Resource Management System: the Client
*)


Addsimps [Cli_prg_def RS def_prg_Init];
program_defs_ref := [Cli_prg_def];

Addsimps (map simp_of_act [rel_act_def, tok_act_def, ask_act_def]);


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
\                  {s. ALL n: lessThan (size (ask s)). ask s!n <= Max})";
by (invariant_tac 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
qed "ask_bounded";

(** Several facts used to prove Lemma 1 **)

Goal "Cli_prg: stable {s. rel s <= giv s}";
by (constrains_tac 1);
by Auto_tac;
qed "stable_rel_le_giv";

Goal "Cli_prg: stable {s. size (rel s) <= size (giv s)}";
by (constrains_tac 1);
by Auto_tac;
qed "stable_size_rel_le_giv";

Goal "Cli_prg: stable {s. size (ask s) <= Suc (size (rel s))}";
by (constrains_tac 1);
by Auto_tac;
qed "stable_size_ask_le_rel";


(*We no longer need constrains_tac to expand the program definition, and 
  expanding it is extremely expensive!*)
program_defs_ref := [];

(*Safety property 2: clients return the right number of tokens*)
Goal "Cli_prg : (Increasing giv Int (rel localTo[UNIV] Cli_prg))  \
\               guarantees Always {s. rel s <= giv s}";
by (rtac guaranteesI 1);
by (rtac AlwaysI 1);
by (Force_tac 1);
by (full_simp_tac (simpset() addsimps [Join_localTo, self_localTo]) 1);
by (blast_tac (claset() addIs [Increasing_localTo_Stable, 
			       stable_rel_le_giv]) 1);
qed "ok_guar_rel_prefix_giv";


(*** Towards proving the liveness property ***)

Goal "Cli_prg Join G   \
\       : transient {s. size (giv s) = Suc k &  \
\                       size (rel s) = k & ask s ! k <= giv s ! k}";
by (res_inst_tac [("act", "rel_act")] transient_mem 1);
by (auto_tac (claset(),
	      simpset() addsimps [Domain_def, Cli_prg_def]));
qed "transient_lemma";



val rewrite_o = rewrite_rule [o_def];

val Increasing_length = mono_length RS mono_Increasing_o;

Goal "Cli_prg : \
\      (Increasing giv Int (rel localTo[UNIV] Cli_prg) Int (ask localTo[UNIV] Cli_prg)) \
\      guarantees Always ({s. size (ask s) <= Suc (size (rel s))} Int \
\                            {s. size (rel s) <= size (giv s)})";
by (rtac guaranteesI 1);
by (Clarify_tac 1);
by (dtac (impOfSubs (rewrite_o Increasing_length)) 1);
by (rtac AlwaysI 1);
by (Force_tac 1);
by (rtac Stable_Int 1);
by (full_simp_tac (simpset() addsimps [Join_localTo, self_localTo]) 2);
by (fast_tac (claset() addEs [impOfSubs (rewrite_o localTo_imp_o_localTo)]
	               addIs [Increasing_localTo_Stable, 
			      stable_size_rel_le_giv]) 2);
by (full_simp_tac (simpset() addsimps [Join_localTo]) 1);
by (fast_tac (claset() addEs [impOfSubs (rewrite_o localTo_imp_o_localTo)]
	               addIs [stable_localTo_stable2 RS stable_imp_Stable,
			      stable_size_ask_le_rel]) 1);
val lemma1 = result();


Goal "Cli_prg : \
\      (Increasing giv Int (rel localTo[UNIV] Cli_prg) Int (ask localTo[UNIV] Cli_prg) \
\                 Int Always giv_meets_ask) \
\      guarantees ({s. k < size (giv s)} LeadsTo {s. k < size (rel s)})";
by (rtac guaranteesI 1);
by (Clarify_tac 1);
by (rtac Stable_transient_Always_LeadsTo 1);
by (res_inst_tac [("k", "k")] transient_lemma 2);
by (force_tac (claset() addDs [impOfSubs Increasing_length,
			       impOfSubs Increasing_Stable_less],
	       simpset()) 1);
by (rtac (make_elim (lemma1 RS guaranteesD)) 1);
by (Blast_tac 1);
by (force_tac (claset(), 
	       simpset() addsimps [Always_eq_includes_reachable, 
				  giv_meets_ask_def]) 1);
qed "client_correct";
