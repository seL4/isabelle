(*  Title:      LCF/pair
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1992  University of Cambridge

Theory of ordered pairs and products
*)

val expand_all_PROD = prove_goal LCF.thy
        "(ALL p. P(p)) <-> (ALL x y. P(<x,y>))"
        (fn _ => [rtac iffI 1, fast_tac FOL_cs 1, rtac allI 1,
                  rtac (surj_pairing RS subst) 1, fast_tac FOL_cs 1]);

local
val ppair = read_instantiate [("z","p::'a*'b")] surj_pairing;
val qpair = read_instantiate [("z","q::'a*'b")] surj_pairing;
in
val PROD_less = prove_goal LCF.thy
        "(p::'a*'b) << q <-> FST(p) << FST(q) & SND(p) << SND(q)"
        (fn _ => [EVERY1[rtac iffI,
                  rtac conjI, etac less_ap_term, etac less_ap_term,
                  rtac (ppair RS subst), rtac (qpair RS subst),
                  etac conjE, rtac mono, etac less_ap_term, atac]]);
end;

val PROD_eq = prove_goal LCF.thy "p=q <-> FST(p)=FST(q) & SND(p)=SND(q)"
        (fn _ => [rtac iffI 1, asm_simp_tac LCF_ss 1,
                  rewtac eq_def,
                  asm_simp_tac (LCF_ss addsimps [PROD_less]) 1]);

val PAIR_less = prove_goal LCF.thy "<a,b> << <c,d> <-> a<<c & b<<d"
        (fn _ => [simp_tac (LCF_ss addsimps [PROD_less])1]);

val PAIR_eq = prove_goal LCF.thy "<a,b> = <c,d> <-> a=c & b=d"
        (fn _ => [simp_tac (LCF_ss addsimps [PROD_eq])1]);

val UU_is_UU_UU = prove_goal LCF.thy "<UU,UU> << UU"
                (fn _ => [simp_tac (LCF_ss addsimps [PROD_less]) 1])
        RS less_UU RS sym;

val LCF_ss = LCF_ss addsimps [PAIR_less,PAIR_eq,UU_is_UU_UU];
