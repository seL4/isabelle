(*  Title:      HOL/UNITY/Handshake
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Handshake Protocol

From Misra, "Asynchronous Compositions of Programs", Section 5.3.2
*)

(*split_all_tac causes a big blow-up*)
claset_ref() := claset() delSWrapper "split_all_tac";

Addsimps [prgF_def RS def_prg_simps];
Addsimps [prgG_def RS def_prg_simps];
Addsimps (map simp_of_act [cmdF_def, cmdG_def]);

(*Simplification for records*)
Addsimps (thms"state.update_defs");
Addsimps [simp_of_set invFG_def];


Goal "Invariant (Join prgF prgG) invFG";
by (rtac InvariantI 1);
by (Force_tac 1);
by (rtac (constrains_imp_Constrains RS StableI) 1);
by (auto_tac (claset(), simpset() addsimps [constrains_Join]));
by (constrains_tac 2);
by (auto_tac (claset() addIs [le_anti_sym] addSEs [le_SucE], simpset()));
by (constrains_tac 1);
qed "invFG";

Goal "LeadsTo (Join prgF prgG) ({s. NF s = k} - {s. BB s}) \
\                              ({s. NF s = k} Int {s. BB s})";
by (rtac (ensures_stable_Join1 RS leadsTo_Basis RS leadsTo_imp_LeadsTo) 1);
by (ensures_tac "cmdG" 2);
by (constrains_tac 1);
qed "lemma2_1";

Goal "LeadsTo (Join prgF prgG) ({s. NF s = k} Int {s. BB s}) {s. k < NF s}";
by (rtac (ensures_stable_Join2 RS leadsTo_Basis RS leadsTo_imp_LeadsTo) 1);
by (constrains_tac 2);
by (ensures_tac "cmdF" 1);
qed "lemma2_2";


Goal "LeadsTo (Join prgF prgG) UNIV {s. m < NF s}";
by (rtac LeadsTo_weaken_R 1);
by (res_inst_tac [("f", "NF"), ("l","Suc m"), ("B","{}")] 
    GreaterThan_bounded_induct 1);
by (auto_tac (claset(), simpset() addsimps [vimage_def]));
(*The inductive step: LeadsTo (Join prgF prgG) {x. NF x = ma} {x. ma < NF x}*)
by (rtac LeadsTo_Diff 1);
by (rtac lemma2_2 2);
by (rtac LeadsTo_Trans 1);
by (rtac lemma2_2 2);
by (rtac lemma2_1 1);
qed "progress";
