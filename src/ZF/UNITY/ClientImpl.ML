(*  Title:      ZF/UNITY/Client.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

Distributed Resource Management System: the Client
*)
Addsimps [type_assumes, default_val_assumes];
(* This part should be automated *)

Goalw [state_def] "s:state ==> s`ask:list(nat)";
by (dres_inst_tac [("a", "ask")] apply_type 1);
by Auto_tac;
qed "ask_value_type";
AddTCs [ask_value_type];
Addsimps [ask_value_type];

Goalw [state_def] "s:state ==> s`giv:list(nat)";
by (dres_inst_tac [("a", "giv")] apply_type 1);
by Auto_tac;
qed "giv_value_type";
AddTCs [giv_value_type];
Addsimps [giv_value_type];

Goalw [state_def]
"s:state ==> s`rel:list(nat)";
by (dres_inst_tac [("a", "rel")] apply_type 1);
by Auto_tac;
qed "rel_value_type";
AddTCs [rel_value_type];
Addsimps [rel_value_type];

Goalw [state_def] "s:state ==> s`tok:nat";
by (dres_inst_tac [("a", "tok")] apply_type 1);
by Auto_tac;
qed "tok_value_type";
AddTCs [tok_value_type];
Addsimps [tok_value_type];

(** The Client Program **)

Goalw [client_prog_def] "client_prog:program";
by (Simp_tac 1);
qed "client_type";
Addsimps [client_type];
AddTCs [client_type];

Addsimps [client_prog_def RS def_prg_Init, 
          client_prog_def RS def_prg_AllowedActs];
program_defs_ref := [client_prog_def];

Addsimps (map simp_of_act [client_rel_act_def, 
client_tok_act_def, client_ask_act_def]);

Goal "ALL G:program. (client_prog ok G) <-> \
\  (G:preserves(lift(rel)) & G:preserves(lift(ask)) & \
\   G:preserves(lift(tok)) &  client_prog:Allowed(G))";
by (auto_tac (claset(), 
     simpset() addsimps [ok_iff_Allowed, client_prog_def RS def_prg_Allowed]));  
qed "client_prog_ok_iff";

Goal "client_prog:(INT x:var-{ask, rel, tok}. preserves(lift(x)))";
by (rtac Inter_var_DiffI 1);
by (rtac ballI 2);
by (rtac preservesI 2);
by (constrains_tac 2);
by Auto_tac;
qed "client_prog_preserves";


(*Safety property 1: ask, rel are increasing : (24) *)
Goalw [guar_def]
"client_prog: program guarantees Incr(lift(ask)) Int Incr(lift(rel))";
by (auto_tac (claset() addSIs [increasing_imp_Increasing],
        simpset() addsimps [client_prog_ok_iff, increasing_def]));
by (ALLGOALS(constrains_tac));
by (ALLGOALS(thin_tac "mk_program(?u, ?v, ?w):Allowed(?x)"));
by (auto_tac (claset() addDs [ActsD], simpset()));
by (dres_inst_tac [("f", "lift(rel)")] preserves_imp_eq 2);
by (dres_inst_tac [("f", "lift(ask)")] preserves_imp_eq 1);
by (TRYALL(assume_tac));
by (ALLGOALS(dtac ActsD));
by (TRYALL(assume_tac));
by (ALLGOALS(Clarify_tac));
by (ALLGOALS(rotate_tac ~2));
by Auto_tac;
qed "client_prog_Increasing_ask_rel";

Addsimps [nth_append, append_one_prefix];

Goal  "0<NbT";
by (cut_facts_tac [NbT_pos] 1);
by (resolve_tac [Ord_0_lt] 1);
by Auto_tac;
qed "NbT_pos2";

(*Safety property 2: the client never requests too many tokens.
With no Substitution Axiom, we must prove the two invariants simultaneously. *)

Goal 
"[| client_prog ok G; G:program |]\
\     ==> client_prog Join G :  \
\             Always({s:state. s`tok le NbT}  Int  \
\                     {s:state. ALL elt:set_of_list(s`ask). elt le NbT})";
by (rotate_tac ~1 1);
by (auto_tac (claset(), simpset() addsimps [client_prog_ok_iff]));
by (rtac (invariantI RS stable_Join_Always2) 1);
by (ALLGOALS(Clarify_tac));
by (ALLGOALS(Asm_full_simp_tac)); 
by (rtac stable_Int 2);
by (dres_inst_tac [("f", "lift(ask)")] preserves_imp_stable 3);
by (dres_inst_tac [("f", "lift(tok)")] preserves_imp_stable 2);
by (REPEAT(Force_tac 2));
by (constrains_tac 1);
by (auto_tac (claset() addDs [ActsD], simpset()));
by (cut_facts_tac [NbT_pos] 1);
by (resolve_tac [NbT_pos2 RS mod_less_divisor] 1);
by (auto_tac (claset() addDs [ActsD, preserves_imp_eq], 
               simpset() addsimps [set_of_list_append]));
qed "ask_Bounded_lemma";

(* Export version, with no mention of tok in the postcondition, but
  unfortunately tok must be declared local.*)
Goal 
"client_prog: program guarantees \
\            Always({s:state. ALL elt: set_of_list(s`ask). elt le NbT})";
by (rtac guaranteesI 1);
by (etac (ask_Bounded_lemma RS Always_weaken) 1);
by Auto_tac;
qed "client_prog_ask_Bounded";

(*** Towards proving the liveness property ***)

Goal 
"client_prog: stable({s:state. <s`rel, s`giv>:prefix(nat)})";
by (constrains_tac 1);
by Auto_tac;
qed "client_prog_stable_rel_le_giv";

Goal
"[| client_prog Join G: Incr(lift(giv)); G:preserves(lift(rel)) |] \
\   ==> client_prog Join G:  Stable({s:state. <s`rel, s`giv>:prefix(nat)})";
by (rtac (client_prog_stable_rel_le_giv RS Increasing_preserves_Stable) 1);
by (auto_tac (claset(), simpset() addsimps [lift_def]));
qed "client_prog_Join_Stable_rel_le_giv";

Goal "[| client_prog Join G: Incr(lift(giv)); G:preserves(lift(rel)) |] \
\   ==> client_prog Join G : Always({s:state. <s`rel, s`giv>:prefix(nat)})";
by (force_tac (claset() addSIs [AlwaysI, client_prog_Join_Stable_rel_le_giv], 
            simpset()) 1);
qed "client_prog_Join_Always_rel_le_giv";

Goal "xs:list(A) ==> xs@[a]=xs --> False";
by (etac list.induct 1);
by Auto_tac;
qed "list_app_lemma";

Goal "A == {<s, t>:state*state. P(s, t)} ==> A={<s, t>:state*state. P(s, t)}";
by Auto_tac;
qed "def_act_eq";

Goal "A={<s,t>:state*state. P(s, t)} ==> A<=state*state";
by Auto_tac;
qed "act_subset";

Goal 
"client_prog: \
\ transient({s:state. s`rel = k & <k, h>:strict_prefix(nat) \
\  & <h, s`giv>:prefix(nat) & h pfixGe s`ask})";
by (res_inst_tac [("act", "client_rel_act")] transientI 1);
by (simp_tac (simpset() addsimps 
                 [client_prog_def RS def_prg_Acts]) 1);
by (simp_tac (simpset() addsimps 
             [client_rel_act_def RS def_act_eq RS act_subset]) 1);
by (auto_tac (claset(),
              simpset() addsimps [client_prog_def RS def_prg_Acts,domain_def]));
by (resolve_tac [ReplaceI] 1);
by (res_inst_tac [("x", "x(rel:= x`rel @\
        \            [nth(length(x`rel), x`giv)])")] exI 1);
by (auto_tac (claset() addSIs [state_update_type, 
                               app_type, length_type, nth_type], 
              simpset()));
by Auto_tac;
by (blast_tac (claset() addIs [lt_trans2, prefix_length_le,
                               strict_prefix_length_lt]) 1);
by (blast_tac (claset() addIs [lt_trans2, prefix_length_le,
                               strict_prefix_length_lt]) 1);
by (full_simp_tac (simpset() addsimps [gen_prefix_iff_nth]) 1);
by (ALLGOALS(subgoal_tac "h:list(nat)"));
by (ALLGOALS(asm_simp_tac (simpset() addsimps [prefix_type RS subsetD RS SigmaD1])));
by (auto_tac (claset(), 
              simpset() addsimps [prefix_def, Ge_def]));
by (dtac strict_prefix_length_lt 1);
by (dres_inst_tac [("x", "length(x`rel)")] bspec 1);
by Auto_tac;
by (full_simp_tac (simpset() addsimps [gen_prefix_iff_nth]) 1);
by (auto_tac (claset(), simpset() addsimps [id_def, lam_def]));
qed "transient_lemma";

Goalw [strict_prefix_def,id_def, lam_def]
"<xs, ys>:strict_prefix(A) <->  <xs, ys>:prefix(A) & xs~=ys";
by (auto_tac (claset() addDs [prefix_type RS subsetD], simpset()));
qed "strict_prefix_is_prefix";

Goal 
"[| client_prog Join G: Incr(lift(giv)); client_prog ok G; G:program |] \
\ ==> client_prog Join G: \
\ {s:state. s`rel = k & <k,h>:strict_prefix(nat) \
\  & <h , s`giv>:prefix(nat) & h pfixGe s`ask}  \
\       LeadsTo {s:state. <k, s`rel>:strict_prefix(nat) \
\                         & <s`rel, s`giv>:prefix(nat) & \
\                                 <h, s`giv>:prefix(nat) & \
\               h pfixGe s`ask}";
by (rtac single_LeadsTo_I 1);
by (Asm_simp_tac 2);
by (ftac (client_prog_Increasing_ask_rel RS guaranteesD) 1);
by (rotate_tac 2 3);
by (auto_tac (claset(), simpset() addsimps [client_prog_ok_iff]));
by (rtac (transient_lemma RS Join_transient_I1 RS transient_imp_leadsTo RS 
          leadsTo_imp_LeadsTo RS PSP_Stable RS LeadsTo_weaken) 1);
by (rtac (Stable_Int RS Stable_Int RS Stable_Int) 1);
by (eres_inst_tac [("f", "lift(giv)"), ("a", "s`giv")] Increasing_imp_Stable 1);
by (Asm_simp_tac 1);
by (eres_inst_tac [("f", "lift(ask)"), ("a", "s`ask")] Increasing_imp_Stable 1);
by (Asm_simp_tac 1);
by (eres_inst_tac [("f", "lift(rel)"), ("a", "s`rel")] Increasing_imp_Stable 1);
by (Asm_simp_tac 1);
by (etac client_prog_Join_Stable_rel_le_giv 1);
by (Blast_tac 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 2);
by (blast_tac (claset() addIs [sym, strict_prefix_is_prefix RS iffD2, 
                               prefix_trans, prefix_imp_pfixGe, 
                               pfixGe_trans]) 2);
by (auto_tac (claset() addIs [strict_prefix_is_prefix RS iffD1 RS conjunct1, 
                               prefix_trans], simpset()));
qed "induct_lemma";

Goal 
"[| client_prog Join G : Incr(lift(giv)); client_prog ok G; G:program |] \
\ ==> client_prog Join G : \
\    {s:state. <s`rel, h>:strict_prefix(nat) \
\          & <h, s`giv>:prefix(nat) & h pfixGe s`ask}  \
\                     LeadsTo {s:state. <h, s`rel>:prefix(nat)}";
by (res_inst_tac [("f", "lam x:state. length(h) #- length(x`rel)")] 
                                 LessThan_induct 1);
by (auto_tac (claset(), simpset() addsimps [vimage_def]));
by (rtac single_LeadsTo_I 1);
by (rtac (induct_lemma RS LeadsTo_weaken) 1);
by Auto_tac;
by (resolve_tac [imageI] 3);
by (resolve_tac [converseI] 3);
by (asm_simp_tac (simpset() addsimps [lam_def]) 3);
by (asm_simp_tac (simpset() addsimps [length_type]) 3);
by (etac swap 2);
by (resolve_tac [imageI] 2);
by (resolve_tac [converseI] 2);
by (asm_full_simp_tac (simpset() addsimps [lam_def]) 2);
by (REPEAT (dtac strict_prefix_length_lt 2));
by (asm_full_simp_tac (simpset() addsimps [length_type, lam_def]) 2);
by (ALLGOALS(subgoal_tac "h:list(nat)"));
by (ALLGOALS(asm_simp_tac (simpset() addsimps [prefix_type RS subsetD RS SigmaD1])));
by (dtac less_imp_succ_add 2);
by (dtac less_imp_succ_add 3);
by (ALLGOALS(Clarify_tac));
by (ALLGOALS(Asm_simp_tac));
by (etac (diff_le_self RS ltD) 2); 
by (asm_full_simp_tac (simpset() addsimps [length_type, lam_def]) 1);
by (auto_tac (claset() addIs [strict_prefix_is_prefix RS iffD2]
                        addDs [rotate_prems 2 common_prefix_linear,
                               prefix_type RS subsetD], simpset()));
qed "rel_progress_lemma";

Goal 
"[| client_prog Join G: Incr(lift(giv)); client_prog ok G; G:program |] ==> \
\ client_prog Join G : \
\  {s:state. <h, s`giv>:prefix(nat) & h pfixGe s`ask}  \
\              LeadsTo {s:state. <h, s`rel>:prefix(nat)}";
by (rtac (client_prog_Join_Always_rel_le_giv RS Always_LeadsToI) 1);
by (rtac ([rel_progress_lemma, subset_refl RS subset_imp_LeadsTo] MRS 
    LeadsTo_Un RS LeadsTo_weaken_L) 3);
by Auto_tac;
by (auto_tac (claset() addIs [strict_prefix_is_prefix RS iffD2]
                        addDs [rotate_prems 3 common_prefix_linear,
                               prefix_type RS subsetD], simpset()));
by (rotate_tac ~1 1);
by (force_tac (claset(), simpset() addsimps [client_prog_ok_iff]) 1);
qed "progress_lemma";

(*Progress property: all tokens that are given will be released*)
Goal 
"client_prog: Incr(lift(giv))  guarantees  \
\     (INT h:list(nat). {s:state. <h, s`giv>:prefix(nat) &\
\             h pfixGe s`ask} LeadsTo {s:state. <h, s`rel>:prefix(nat)})";
by (rtac guaranteesI 1);
by (Clarify_tac 1);
by (blast_tac (claset() addIs [progress_lemma]) 1);
by Auto_tac;
qed "client_prog_progress";

Goal "Allowed(client_prog) = \
\ preserves(lift(rel)) Int preserves(lift(ask)) Int preserves(lift(tok))";
by (cut_facts_tac [inst "v"  "lift(ask)" preserves_type] 1);
by (auto_tac (claset(), 
              simpset() addsimps [Allowed_def, 
               client_prog_def RS def_prg_Allowed, 
                  cons_Int_distrib, safety_prop_Acts_iff]));
qed "client_prog_Allowed";

