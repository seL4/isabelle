(*  Title:      HOLCF/Discrete1.ML
    ID:         $Id$
    Author:     Tobias Nipkow

Proves that 'a discr is a cpo
*)

Goalw [less_discr_def] "((x::('a::type)discr) << y) = (x=y)";
by (rtac refl 1);
qed "discr_less_eq";
AddIffs [discr_less_eq];

Goalw [chain_def]
 "!!S::nat=>('a::type)discr. chain S ==> S i = S 0";
by (induct_tac "i" 1);
by (rtac refl 1);
by (etac subst 1);
by (rtac sym 1);
by (Fast_tac 1);
qed "discr_chain0";

Goal
 "!!S::nat=>('a::type)discr. chain(S) ==> range(S) = {S 0}";
by (fast_tac (claset() addEs [discr_chain0]) 1);
qed "discr_chain_range0";
Addsimps [discr_chain_range0];

Goalw [is_lub_def,is_ub_def]
 "!!S. chain S ==> ? x::('a::type)discr. range(S) <<| x";
by (Asm_simp_tac 1);
qed "discr_cpo";
