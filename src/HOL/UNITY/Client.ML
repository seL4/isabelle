(*  Title:      HOL/UNITY/Client
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Distributed Resource Management System: the Client
*)


 (*MOVE higher-up: UNITY.thy or Traces.thy ???*)

(*[| stable acts C; constrains acts (C Int A) A |] ==> stable acts (C Int A)*)
bind_thm ("stable_constrains_stable", stable_constrains_Int RS stableI);


(*"raw" notion of invariant.  Yields a SET of programs*)
Goal "[| Init F<=A;  stable (Acts F) A |] ==> F : invariant A";
by (asm_simp_tac (simpset() addsimps [invariant_def]) 1);
qed "invariantI";

Goalw [Invariant_def, invariant_def, Stable_def, Constrains_def, stable_def]
     "F : invariant A ==> Invariant F A";
by (blast_tac (claset() addIs [constrains_reachable_Int]) 1);
qed "invariant_imp_Invariant";


(*Could also say "invariant A Int invariant B <= invariant (A Int B)"*)
Goal "[| F : invariant A;  F : invariant B |] ==> F : invariant (A Int B)";
by (auto_tac (claset(), simpset() addsimps [invariant_def, stable_Int]));
qed "invariant_Int";

Goalw [Invariant_def, invariant_def, Stable_def, Constrains_def, stable_def]
     "Invariant F A = (F : invariant (reachable F Int A))";
by (blast_tac (claset() addIs reachable.intrs) 1);
qed "Invariant_eq_invariant_reachable";


bind_thm ("invariant_includes_reachable",
	  invariant_imp_Invariant RS Invariant_includes_reachable);

Goalw [always_def] "always A = (UN I: Pow A. invariant I)";
by (blast_tac (claset() addIs [invariantI, impOfSubs Init_subset_reachable, 
                               stable_reachable,
			       impOfSubs invariant_includes_reachable]) 1);
qed "always_eq_UN_invariant";

Goal "F : always A = (EX I. F: invariant I & I <= A)";
by (simp_tac (simpset() addsimps [always_eq_UN_invariant]) 1);
by (Blast_tac 1);
qed "always_iff_ex_invariant";


Goalw [increasing_def, stable_def, constrains_def]
     "increasing f <= increasing (length o f)";
by Auto_tac;
by (blast_tac (claset() addIs [prefix_length_le, le_trans]) 1);
qed "increasing_length";


Goalw [increasing_def]
     "increasing f <= {F. ALL z::nat. stable (Acts F) {s. z < f s}}";
by (simp_tac (simpset() addsimps [Suc_le_eq RS sym]) 1);
by (Blast_tac 1);
qed "increasing_less";


Goal "[| F Join G : f localTo F;  (s,s') : act;  \
\        act : Acts G; act ~: Acts F |] ==> f s' = f s";
by (asm_full_simp_tac 
    (simpset() addsimps [localTo_def, Acts_Join, stable_def, 
			 constrains_def]) 1);
by (Blast_tac 1);
qed "localTo_imp_equals";


Goal "[| Stable F A;  transient (Acts F) C;  \
\        reachable F <= (-A Un B Un C) |] ==> LeadsTo F A B";
by (etac reachable_LeadsTo_weaken 1);
by (rtac LeadsTo_Diff 1);
by (etac (transient_imp_leadsTo RS leadsTo_imp_LeadsTo RS PSP_stable2) 2);
by (ALLGOALS (blast_tac (claset() addIs [subset_imp_LeadsTo])));
qed "Stable_transient_reachable_LeadsTo";


(**** things that definitely belong in Client.ML ****)

(*split_all_tac causes a big blow-up*)
claset_ref() := claset() delSWrapper "split_all_tac";

val Client_simp = Cli_prg_def RS def_prg_simps;

Addsimps (map simp_of_act [rel_act_def, tok_act_def, ask_act_def]);

DelIffs [length_Suc_conv];

(*Simplification for records*)
Addsimps (thms"state.update_defs");


(*CAN THIS be generalized?
  Importantly, the second case considers actions that are in G
  and NOT in Cli_prg (needed to use localTo_imp_equals) *)
Goal "(act : Acts (Cli_prg Join G)) = \
\      (act : {Id, rel_act, tok_act, ask_act} | \
\       act : Acts G & act ~: Acts Cli_prg)";
by (asm_full_simp_tac (simpset() addsimps [Client_simp, Acts_Join]) 1);
(*don't unfold definitions of actions*)
by (blast_tac HOL_cs 1);
qed "Acts_Cli_Join_eq";


fun invariant_tac i = 
    rtac invariantI i  THEN
    auto_tac (claset(), simpset() addsimps [Client_simp])  THEN
    constrains_tac i;

(*Safety property 1(a): ask is nondecreasing*)
Goalw [increasing_def] "Cli_prg: increasing ask";
by (auto_tac (claset(), simpset() addsimps [Client_simp]));
by (constrains_tac 1);
by Auto_tac;
qed "increasing_ask";

(*Safety property 1(b): rel is nondecreasing*)
Goalw [increasing_def] "Cli_prg: increasing rel";
by (auto_tac (claset(), simpset() addsimps [Client_simp]));
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


(*Safety property 2: clients return the right number of tokens*)
Goalw [increasing_def]
      "Cli_prg : (increasing giv Int (rel localTo Cli_prg))  \
\                guarantees invariant {s. rel s <= giv s}";
by (rtac guaranteesI 1);
by (Clarify_tac 1);
by (invariant_tac 1);
by (subgoal_tac "rel s <= giv s'" 1);
by (force_tac (claset(),
	       simpset() addsimps [stable_def, constrains_def]) 2);
by (dtac (Acts_Cli_Join_eq RS iffD1) 1);
(*we note that "rel" is local to Client*)
by (auto_tac (claset() addD2 ("x",localTo_imp_equals), simpset()));
qed "ok_guar_rel_prefix_giv";


(*** Towards proving the liveness property ***)

Goal "transient (Acts (Cli_prg Join G))   \
\               {s. length (giv s) = Suc k &  \
\                   length (rel s) = k & ask s ! k <= giv s ! k}";
by (res_inst_tac [("act", "rel_act")] transient_mem 1);
by (auto_tac (claset(),
	      simpset() addsimps [Domain_def, Acts_Join, Client_simp]));
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
by (dtac (Acts_Cli_Join_eq RS iffD1) 1);
by (auto_tac (claset() addD2 ("x",localTo_imp_equals), simpset()));
by (force_tac (claset(),
	       simpset() addsimps [increasing_def, Acts_Join, stable_def, 
				   constrains_def]) 1);
val lemma1 = result();


Goal "Cli_prg : \
\      (increasing giv Int (rel localTo Cli_prg) Int (ask localTo Cli_prg) \
\                 Int invariant giv_meets_ask) \
\      guarantees {F. LeadsTo F {s. k < length (giv s)}    \
\                               {s. k < length (rel s)}}";
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
