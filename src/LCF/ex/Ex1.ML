
simpset_ref() := LCF_ss;

Addsimps [P_strict,K];

val H_unfold = prove_goal thy "H = K(H)"
 (fn _ => [stac H 1, rtac (FIX_eq RS sym) 1]);

bind_thm ("H_unfold", H_unfold);


val H_strict = prove_goal thy "H(UU)=UU"
 (fn _ => [stac H_unfold 1, Simp_tac 1]);

bind_thm ("H_strict", H_strict);
Addsimps [H_strict];

goal thy "ALL x. H(FIX(K,x)) = FIX(K,x)";
by (induct_tac "K" 1);
by (Simp_tac 1);
by (simp_tac (simpset() setloop (split_tac [COND_cases_iff])) 1);
by (strip_tac 1);
by (stac H_unfold 1);
by (Asm_simp_tac 1);
qed "H_idemp_lemma";

val H_idemp = rewrite_rule [mk_meta_eq (H RS sym)] H_idemp_lemma;
bind_thm ("H_idemp", H_idemp);
