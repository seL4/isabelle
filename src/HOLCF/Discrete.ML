(*  Title:      HOLCF/Discrete.ML
    ID:         $Id$
    Author:     Tobias Nipkow
*)

Goalw [undiscr_def] "undiscr(Discr x) = x";
by (Simp_tac 1);
qed "undiscr_Discr";
Addsimps [undiscr_Discr];

Goal
 "!!S::nat=>('a::type)discr. chain(S) ==> range(%i. f(S i)) = {f(S 0)}";
by (fast_tac (claset() addDs [discr_chain0] addEs [arg_cong]) 1);
qed "discr_chain_f_range0";

Goalw [cont,is_lub_def,is_ub_def] "cont(%x::('a::type)discr. f x)";
by (simp_tac (simpset() addsimps [discr_chain_f_range0]) 1);
qed "cont_discr";
AddIffs [cont_discr];
