(*  Title:      HOL/BCV/Types.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM
*)

Goalw [semilat_def,le_typ,plus_typ] "semilat (UNIV::typ set)";
by (Auto_tac);
qed "semilat_typ";
AddIffs [semilat_typ];

Goal "{(x,y::'a::order). y<x}^+ = {(x,y::'a::order). y<x}";
by (Auto_tac);
 by (etac trancl_induct 1);
 by (Blast_tac 1);
 by (blast_tac (claset() addIs [order_less_trans]) 1);
by (blast_tac (claset() addIs [r_into_trancl]) 1);
qed "trancl_order1_conv";
Addsimps [trancl_order1_conv];

Goalw [acyclic_def] "acyclic{(x,y::'a::order). y<x}";
by (Simp_tac 1);
qed "acyclic_order1";
AddIffs [acyclic_order1];

Goalw [acc_def] "acc(UNIV::typ set)";
by (rtac finite_acyclic_wf 1);
 by (fast_tac (claset() addIs [finite_SigmaI RSN (2,finite_subset)]) 1);
by (blast_tac (claset() addIs [acyclic_subset]) 1);
qed "acc_UNIV_typ";
AddIffs [acc_UNIV_typ];
