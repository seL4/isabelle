(*  Title:      HOL/UNITY/Client
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Distributed Resource Management System: the Client
*)

Addsimps [Client_def RS def_prg_Init];
program_defs_ref := [Client_def];

Addsimps (map simp_of_act [rel_act_def, tok_act_def, ask_act_def]);


fun invariant_tac i = 
    rtac invariantI i  THEN
    constrains_tac (i+1);


(*Safety property 1: ask, rel are increasing*)
Goal "Client: UNIV guarantees[funPair rel ask] \
\             Increasing ask Int Increasing rel";
by (safe_tac (claset() addSIs [guaranteesI,increasing_imp_Increasing]));
by (auto_tac
    (claset(),
     simpset() addsimps [impOfSubs preserves_subset_increasing,
			 Join_increasing]));
by (auto_tac (claset(), simpset() addsimps [increasing_def]));
by (ALLGOALS constrains_tac);
by Auto_tac;
qed "increasing_ask_rel";


Addsimps [nth_append, append_one_prefix];


(*Safety property 2: the client never requests too many tokens.
      With no Substitution Axiom, we must prove the two invariants 
  simultaneously.
*)
Goal "G : preserves (funPair ask tok)  \
\     ==> Client Join G :  \
\             Always ({s. tok s <= NbT}  Int  \
\                     {s. ALL elt : set (ask s). elt <= NbT})";
by (rtac (invariantI RS stable_Join_Always2) 1);
by (fast_tac (claset() addSEs [impOfSubs preserves_subset_stable]
		       addSIs [stable_Int]) 3);
by (constrains_tac 2);
by (cut_inst_tac [("m", "tok s")] (NbT_pos RS mod_less_divisor) 2);
by Auto_tac;
qed "ask_bounded_lemma";

(*export version, with no mention of tok in the postcondition, but
  unfortunately tok must be declared local.*)
Goal "Client: UNIV guarantees[funPair ask tok] \
\             Always {s. ALL elt : set (ask s). elt <= NbT}";
by (rtac guaranteesI 1);
by (etac (ask_bounded_lemma RS Always_weaken) 1);
by (rtac Int_lower2 1);
qed "ask_bounded";


(*** Towards proving the liveness property ***)

Goal "Client: stable {s. rel s <= giv s}";
by (constrains_tac 1);
by Auto_tac;
qed "stable_rel_le_giv";

Goal "[| Client Join G : Increasing giv;  G : preserves rel |] \
\     ==> Client Join G : Stable {s. rel s <= giv s}";
by (rtac (stable_rel_le_giv RS Increasing_preserves_Stable) 1);
by Auto_tac;
qed "Join_Stable_rel_le_giv";

Goal "[| Client Join G : Increasing giv;  G : preserves rel |] \
\     ==> Client Join G : Always {s. rel s <= giv s}";
by (rtac AlwaysI 1);
by (rtac Join_Stable_rel_le_giv 2);
by Auto_tac;
qed "Join_Always_rel_le_giv";

Goal "Client : transient {s. rel s = k & k<h & h <= giv s & h pfixGe ask s}";
by (res_inst_tac [("act", "rel_act")] transientI 1);
by (auto_tac (claset(),
	      simpset() addsimps [Domain_def, Client_def]));
by (blast_tac (claset() addIs [less_le_trans, prefix_length_le,
			       strict_prefix_length_less]) 1);
by (auto_tac (claset(), 
	      simpset() addsimps [prefix_def, genPrefix_iff_nth, Ge_def]));
by (blast_tac (claset() addIs [strict_prefix_length_less]) 1);
qed "transient_lemma";


Goal "[| Client Join G : Increasing giv;  G : preserves (funPair rel ask) |] \
\ ==> Client Join G : {s. rel s = k & k<h & h <= giv s & h pfixGe ask s}  \
\                     LeadsTo {s. k < rel s & rel s <= giv s & \
\                                 h <= giv s & h pfixGe ask s}";
by (rtac single_LeadsTo_I 1);
by (ftac (increasing_ask_rel RS guaranteesD) 1);
by Auto_tac;
by (rtac (transient_lemma RS Join_transient_I1 RS transient_imp_leadsTo RS 
	  leadsTo_imp_LeadsTo RS PSP_Stable RS LeadsTo_weaken) 1);
by (rtac (Stable_Int RS Stable_Int RS Stable_Int) 1);
by (eres_inst_tac [("f", "giv"), ("x", "giv s")] IncreasingD 1);
by (eres_inst_tac [("f", "ask"), ("x", "ask s")] IncreasingD 1);
by (eres_inst_tac [("f", "rel"), ("x", "rel s")] IncreasingD 1);
by (etac Join_Stable_rel_le_giv 1);
by (Blast_tac 1);
by (blast_tac (claset() addIs [sym, order_less_le RS iffD2, 
			       order_trans, prefix_imp_pfixGe, 
			       pfixGe_trans]) 2);
by (blast_tac (claset() addIs [order_less_imp_le, order_trans]) 1);
qed "induct_lemma";


Goal "[| Client Join G : Increasing giv;  G : preserves (funPair rel ask) |] \
\ ==> Client Join G : {s. rel s < h & h <= giv s & h pfixGe ask s}  \
\                     LeadsTo {s. h <= rel s}";
by (res_inst_tac [("f", "%s. size h - size (rel s)")] LessThan_induct 1);
by (auto_tac (claset(), simpset() addsimps [vimage_def]));
by (rtac single_LeadsTo_I 1);
by (rtac (induct_lemma RS LeadsTo_weaken) 1);
by Auto_tac;
by (blast_tac (claset() addIs [order_less_le RS iffD2]
			addDs [common_prefix_linear]) 1);
by (REPEAT (dtac strict_prefix_length_less 1));
by (arith_tac 1);
qed "rel_progress_lemma";


Goal "[| Client Join G : Increasing giv;  G : preserves (funPair rel ask) |] \
\ ==> Client Join G : {s. h <= giv s & h pfixGe ask s}  \
\                     LeadsTo {s. h <= rel s}";
by (rtac (Join_Always_rel_le_giv RS Always_LeadsToI) 1);
by (rtac ([rel_progress_lemma, subset_refl RS subset_imp_LeadsTo] MRS 
    LeadsTo_Un RS LeadsTo_weaken_L) 3);
by Auto_tac;
by (blast_tac (claset() addIs [order_less_le RS iffD2]
			addDs [common_prefix_linear]) 1);
qed "client_progress_lemma";

(*Progress property: all tokens that are given will be released*)
Goal "Client : \
\      Increasing giv  guarantees[funPair rel ask]  \
\      (INT h. {s. h <= giv s & h pfixGe ask s} LeadsTo {s. h <= rel s})";
by (rtac guaranteesI 1);
by (Clarify_tac 1);
by (blast_tac (claset() addIs [client_progress_lemma]) 1);
qed "client_progress";

Goal "Client : preserves extra";
by (rewtac preserves_def);
by Auto_tac;
by (constrains_tac 1);
by Auto_tac;
qed "client_preserves_extra";

Goal "bij client_map";
by (auto_tac (claset() addSWrapper record_split_wrapper, 
	      simpset() addsimps [client_map_def, non_extra_def, bij_def, 
				  inj_on_def, surj_def]));
by (res_inst_tac 
    [("x", "(|giv=?a, ask=?b, rel=?c, tok=?d, extra=?e|)")] exI 1);
by (Force_tac 1);
qed "bij_client_map";

Goal "rename client_map Client : preserves snd";
by (asm_simp_tac (simpset() addsimps [bij_client_map RS rename_preserves]) 1);
by (asm_simp_tac (simpset() addsimps [client_map_def]) 1);
by (rtac client_preserves_extra 1);
qed "client_preserves_extra";


(** Obsolete lemmas from first version of the Client **)

Goal "Client: stable {s. size (rel s) <= size (giv s)}";
by (constrains_tac 1);
by Auto_tac;
qed "stable_size_rel_le_giv";

(*clients return the right number of tokens*)
Goal "Client : Increasing giv  guarantees[rel]  Always {s. rel s <= giv s}";
by (rtac guaranteesI 1);
by (rtac AlwaysI 1);
by (Force_tac 1);
by (blast_tac (claset() addIs [Increasing_preserves_Stable, 
			       stable_rel_le_giv]) 1);
qed "ok_guar_rel_prefix_giv";
