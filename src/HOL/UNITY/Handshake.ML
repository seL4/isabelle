(*  Title:      HOL/UNITY/Handshake
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Handshake Protocol

From Misra, "Asynchronous Compositions of Programs", Section 5.3.2
*)

Addsimps [F_def RS def_prg_Init, G_def RS def_prg_Init];
program_defs_ref := [F_def, G_def];

Addsimps (map simp_of_act [cmdF_def, cmdG_def]);
Addsimps [simp_of_set invFG_def];


Goal "(F Join G) : Always invFG";
by (rtac AlwaysI 1);
by (Force_tac 1);
by (rtac (constrains_imp_Constrains RS StableI) 1);
by (auto_tac (claset(), simpset() addsimps [constrains_Join]));
by (constrains_tac 2);
by (auto_tac (claset() addIs [order_antisym] addSEs [le_SucE], simpset()));
by (constrains_tac 1);
qed "invFG";

Goal "(F Join G) : ({s. NF s = k} - {s. BB s}) LeadsTo \
\                  ({s. NF s = k} Int {s. BB s})";
by (rtac (ensures_stable_Join1 RS leadsTo_Basis RS leadsTo_imp_LeadsTo) 1);
by (ensures_tac "cmdG" 2);
by (constrains_tac 1);
qed "lemma2_1";

Goal "(F Join G) : ({s. NF s = k} Int {s. BB s}) LeadsTo {s. k < NF s}";
by (rtac (ensures_stable_Join2 RS leadsTo_Basis RS leadsTo_imp_LeadsTo) 1);
by (constrains_tac 2);
by (ensures_tac "cmdF" 1);
qed "lemma2_2";


Goal "(F Join G) : UNIV LeadsTo {s. m < NF s}";
by (rtac LeadsTo_weaken_R 1);
by (res_inst_tac [("f", "NF"), ("l","Suc m"), ("B","{}")] 
    GreaterThan_bounded_induct 1);
(*The inductive step is (F Join G) : {x. NF x = ma} LeadsTo {x. ma < NF x}*)
by (auto_tac (claset() addSIs [lemma2_1, lemma2_2] 
	               addIs[LeadsTo_Trans, LeadsTo_Diff], 
	      simpset() addsimps [vimage_def]));
qed "progress";
