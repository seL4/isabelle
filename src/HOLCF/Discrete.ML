(*  Title:      HOLCF/Discrete.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TUM
*)

goalw thy [undiscr_def] "undiscr(Discr x) = x";
by (Simp_tac 1);
qed "undiscr_Discr";
Addsimps [undiscr_Discr];

goal thy
 "!!S::nat=>('a::term)discr. chain(S) ==> range(%i. f(S i)) = {f(S 0)}";
by (fast_tac (claset() addDs [discr_chain0] addEs [arg_cong]) 1);
qed "discr_chain_f_range0";

goalw thy [cont,is_lub,is_ub] "cont(%x::('a::term)discr. f x)";
by (simp_tac (simpset() addsimps [discr_chain_f_range0]) 1);
qed "cont_discr";
AddIffs [cont_discr];
