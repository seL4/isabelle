(*  Title:      HOL/UNITY/Handshake
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Handshake Protocol

From Misra, "Asynchronous Compositions of Programs", Section 5.3.2
*)

(*split_all_tac causes a big blow-up*)
claset_ref() := claset() delSWrapper record_split_name;

Addsimps [F_def RS def_prg_Init, G_def RS def_prg_Init];
program_defs_ref := [F_def, G_def];

Addsimps (map simp_of_act [cmdF_def, cmdG_def]);

(*Simplification for records*)
Addsimps (thms"state.update_defs");
Addsimps [simp_of_set invFG_def];


Goal "(F Join G) : Invariant invFG";
by (rtac InvariantI 1);
by (Force_tac 1);
by (rtac (constrains_imp_Constrains RS StableI) 1);
by (auto_tac (claset(), simpset() addsimps [constrains_Join]));
by (constrains_tac 2);
by (auto_tac (claset() addIs [le_anti_sym] addSEs [le_SucE], simpset()));
by (constrains_tac 1);
qed "invFG";

Goal "(F Join G) : LeadsTo ({s. NF s = k} - {s. BB s}) \
\                          ({s. NF s = k} Int {s. BB s})";
by (rtac (ensures_stable_Join1 RS leadsTo_Basis RS leadsTo_imp_LeadsTo) 1);
by (ensures_tac "cmdG" 2);
by (constrains_tac 1);
by Auto_tac;
qed "lemma2_1";

Goal "(F Join G) : LeadsTo ({s. NF s = k} Int {s. BB s}) {s. k < NF s}";
by (rtac (ensures_stable_Join2 RS leadsTo_Basis RS leadsTo_imp_LeadsTo) 1);
by (constrains_tac 2);
by (ensures_tac "cmdF" 1);
by Auto_tac;
qed "lemma2_2";


Goal "(F Join G) : LeadsTo UNIV {s. m < NF s}";
by (rtac LeadsTo_weaken_R 1);
by (res_inst_tac [("f", "NF"), ("l","Suc m"), ("B","{}")] 
    GreaterThan_bounded_induct 1);
by (auto_tac (claset(), simpset() addsimps [vimage_def]));
(*The inductive step: (F Join G) : LeadsTo {x. NF x = ma} {x. ma < NF x}*)
by (rtac LeadsTo_Diff 1);
by (rtac lemma2_2 2);
by (rtac LeadsTo_Trans 1);
by (rtac lemma2_2 2);
by (rtac lemma2_1 1);
qed "progress";
