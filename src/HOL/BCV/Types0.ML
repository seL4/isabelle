(*  Title:      HOL/BCV/Types0.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM
*)

Goalw [le_typ] "(t::typ) <= t";
by (Blast_tac 1);
qed "le_typ_refl";

Goalw [le_typ] "[| (t1::typ) <= t2; t2<=t3 |] ==> t1<=t3";
by (Blast_tac 1);
qed "le_typ_trans";

Goalw [le_typ] "[| (t1::typ) <= t2; t2<=t1 |] ==> t1=t2";
by (Blast_tac 1);
qed "le_typ_antisym";

Goalw [less_typ] "(t1::typ) < t2 = (t1<=t2 & t1 ~= t2)";
by (rtac refl 1);
qed "less_le_typ";

Goal "(UNIV::typ set) = {Atyp,Btyp,Ctyp,Top}";
by (Auto_tac);
by (rename_tac "t" 1);
by (exhaust_tac "t" 1);
by (Auto_tac);
qed "UNIV_typ_enum";

Goal "finite(UNIV::typ set)";
by (simp_tac (simpset() addsimps [UNIV_typ_enum]) 1);
qed "finite_UNIV_typ";
AddIffs [finite_UNIV_typ];
