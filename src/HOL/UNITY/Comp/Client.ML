(*  Title:      HOL/UNITY/Client
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Distributed Resource Management System: the Client
*)

Addsimps [Client_def RS def_prg_Init, 
          Client_def RS def_prg_AllowedActs];
Addsimps (map simp_of_act [rel_act_def, tok_act_def, ask_act_def]);

Goal "(Client ok G) = \
\     (G : preserves rel & G : preserves ask & G : preserves tok &\
\      Client : Allowed G)";
by (auto_tac (claset(), 
    simpset() addsimps [ok_iff_Allowed, Client_def RS def_total_prg_Allowed]));
qed "Client_ok_iff";
AddIffs [Client_ok_iff];


(*Safety property 1: ask, rel are increasing*)
Goal "Client: UNIV guarantees Increasing ask Int Increasing rel";
by (auto_tac
    (claset() addSIs [increasing_imp_Increasing],
     simpset() addsimps [guar_def, impOfSubs preserves_subset_increasing]));
by (auto_tac (claset(), simpset() addsimps [Client_def, increasing_def]));
by (ALLGOALS constrains_tac);
by Auto_tac;
qed "increasing_ask_rel";

Addsimps [nth_append, append_one_prefix];


(*Safety property 2: the client never requests too many tokens.
      With no Substitution Axiom, we must prove the two invariants 
  simultaneously.
*)
Goal "Client ok G  \
\     ==> Client Join G :  \
\             Always ({s. tok s <= NbT}  Int  \
\                     {s. ALL elt : set (ask s). elt <= NbT})";
by Auto_tac;  
by (rtac (invariantI RS stable_Join_Always2) 1);
by (fast_tac (claset() addSEs [impOfSubs preserves_subset_stable]
		       addSIs [stable_Int]) 3);
by (asm_full_simp_tac (simpset() addsimps [Client_def]) 2);
by (constrains_tac 2);
by (cut_inst_tac [("m", "tok s")] (NbT_pos RS mod_less_divisor) 2);
by Auto_tac;
qed "ask_bounded_lemma";

(*export version, with no mention of tok in the postcondition, but
  unfortunately tok must be declared local.*)
Goal "Client: UNIV guarantees Always {s. ALL elt : set (ask s). elt <= NbT}";
by (rtac guaranteesI 1);
by (etac (ask_bounded_lemma RS Always_weaken) 1);
by (rtac Int_lower2 1);
qed "ask_bounded";


(*** Towards proving the liveness property ***)

Goal "Client: stable {s. rel s <= giv s}";
by (asm_full_simp_tac (simpset() addsimps [Client_def]) 1); 
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
by (force_tac (claset() addIs [AlwaysI, Join_Stable_rel_le_giv], simpset()) 1);
qed "Join_Always_rel_le_giv";

Goal "Client : transient {s. rel s = k & k<h & h <= giv s & h pfixGe ask s}";
by (simp_tac (simpset() addsimps [Client_def, mk_total_program_def]) 1);
by (res_inst_tac [("act", "rel_act")] totalize_transientI 1);
by (auto_tac (claset(),
	      simpset() addsimps [Domain_def, Client_def]));
by (blast_tac (claset() addIs [less_le_trans, prefix_length_le,
			       strict_prefix_length_less]) 1);
by (auto_tac (claset(), 
	      simpset() addsimps [prefix_def, genPrefix_iff_nth, Ge_def]));
by (blast_tac (claset() addIs [strict_prefix_length_less]) 1);
qed "transient_lemma";


Goal "[| Client Join G : Increasing giv;  Client ok G |] \
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


Goal "[| Client Join G : Increasing giv;  Client ok G |] \
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


Goal "[| Client Join G : Increasing giv;  Client ok G |] \
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
\      Increasing giv  guarantees  \
\      (INT h. {s. h <= giv s & h pfixGe ask s} LeadsTo {s. h <= rel s})";
by (rtac guaranteesI 1);
by (Clarify_tac 1);
by (blast_tac (claset() addIs [client_progress_lemma]) 1);
qed "client_progress";

(*This shows that the Client won't alter other variables in any state
  that it is combined with*)
Goal "Client : preserves dummy";
by (asm_full_simp_tac (simpset() addsimps [Client_def, preserves_def]) 1);
by (Clarify_tac 1); 
by (constrains_tac 1);
by Auto_tac;
qed "client_preserves_dummy";


(** Obsolete lemmas from first version of the Client **)

Goal "Client: stable {s. size (rel s) <= size (giv s)}";
by (asm_full_simp_tac (simpset() addsimps [Client_def]) 1);
by (constrains_tac 1);
by Auto_tac;
qed "stable_size_rel_le_giv";

(*clients return the right number of tokens*)
Goal "Client : Increasing giv  guarantees  Always {s. rel s <= giv s}";
by (rtac guaranteesI 1);
by (rtac AlwaysI 1);
by (Force_tac 1);
by (blast_tac (claset() addIs [Increasing_preserves_Stable, 
			       stable_rel_le_giv]) 1);
qed "ok_guar_rel_prefix_giv";
