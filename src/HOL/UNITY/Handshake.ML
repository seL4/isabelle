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


Goalw [prgF_def, prgG_def] "invariant (Join prgF prgG) invFG";
by (rtac invariantI 1);
by (force_tac (claset(), 
	       simpset() addsimps [Join_def]) 1);
by (auto_tac (claset(), simpset() addsimps [stable_Join]));
by (constrains_tac [prgG_def,cmdG_def] 2);
by (auto_tac (claset() addIs [le_anti_sym] addSEs [le_SucE], simpset()));
by (constrains_tac [prgF_def,cmdF_def] 1);
qed "invFG";

Goal "LeadsTo (Join prgF prgG) {s. NF s = k & ~ BB s} {s. NF s = k & BB s}";
br (ensures_stable_Join1 RS leadsTo_Basis RS leadsTo_imp_LeadsTo) 1;
by (ensures_tac [prgG_def,cmdG_def] "cmdG" 2);
by (constrains_tac [prgF_def,cmdF_def] 1);
qed "lemma2_1";

Goal "LeadsTo (Join prgF prgG) {s. NF s = k & BB s} {s. k < NF s}";
br (ensures_stable_Join2 RS leadsTo_Basis RS leadsTo_imp_LeadsTo) 1;
by (constrains_tac [prgG_def,cmdG_def] 2);
by (ensures_tac [prgF_def,cmdF_def] "cmdF" 1);
qed "lemma2_2";


Goal "LeadsTo (Join prgF prgG) {s. NF s = k} {s. k < NF s}";
br LeadsTo_Diff 1;
br lemma2_2 2;
br LeadsTo_Trans 1;
br lemma2_2 2;
br (lemma2_1 RS LeadsTo_weaken_L) 1;
by Auto_tac;
val lemma = result();


Goal "LeadsTo (Join prgF prgG) UNIV {s. m < NF s}";
by (res_inst_tac [("f", "NF")] R_lessThan_induct 1);
auto();
br (lemma RS LeadsTo_weaken) 1;
auto();
