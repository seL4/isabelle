(*  Title:      HOL/UNITY/Handshake
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Handshake Protocol

From Misra, "Asynchronous Compositions of Programs", Section 5.3.2
*)

(*split_all_tac causes a big blow-up*)
claset_ref() := claset() delSWrapper "split_all_tac";

(*Simplification for records*)
Addsimps (thms"state.update_defs");
Addsimps [invFG_def];


Goalw [prgF_def, Join_def] "id : Acts (Join prgF prgG) ";
by (Simp_tac 1);
qed "id_in_Acts";
AddIffs [id_in_Acts];


Goalw [prgF_def, prgG_def] "Invariant (Join prgF prgG) invFG";
by (rtac InvariantI 1);
by (Force_tac 1);
by (rtac (constrains_imp_Constrains RS StableI) 1);
by (auto_tac (claset(), simpset() addsimps [constrains_Join]));
by (constrains_tac [prgG_def,cmdG_def] 2);
by (auto_tac (claset() addIs [le_anti_sym] addSEs [le_SucE], simpset()));
by (constrains_tac [prgF_def,cmdF_def] 1);
qed "invFG";

Goal "LeadsTo (Join prgF prgG) {s. NF s = k & ~ BB s} {s. NF s = k & BB s}";
by (rtac (ensures_stable_Join1 RS leadsTo_Basis RS leadsTo_imp_LeadsTo) 1);
by (ensures_tac [prgG_def,cmdG_def] "cmdG" 2);
by (constrains_tac [prgF_def,cmdF_def] 1);
qed "lemma2_1";

Goal "LeadsTo (Join prgF prgG) {s. NF s = k & BB s} {s. k < NF s}";
by (rtac (ensures_stable_Join2 RS leadsTo_Basis RS leadsTo_imp_LeadsTo) 1);
by (constrains_tac [prgG_def,cmdG_def] 2);
by (ensures_tac [prgF_def,cmdF_def] "cmdF" 1);
qed "lemma2_2";


Goal "LeadsTo (Join prgF prgG) UNIV {s. m < NF s}";
by (rtac LeadsTo_weaken_R 1);
by (res_inst_tac [("f", "NF"), ("l","Suc m"), ("B","{}")] 
    GreaterThan_bounded_induct 1);
by (auto_tac (claset(), simpset() addsimps [vimage_def]));
by (trans_tac 2);
(*The inductive step: LeadsTo (Join prgF prgG) {x. NF x = ma} {x. ma < NF x}*)
by (rtac LeadsTo_Diff 1);
by (rtac lemma2_2 2);
by (rtac LeadsTo_Trans 1);
by (rtac lemma2_2 2);
by (rtac (lemma2_1 RS LeadsTo_weaken_L) 1);
by Auto_tac;
qed "progress";
