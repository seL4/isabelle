val make_imp_tac = EVERY'[rtac mp, fn i => atac (i+1), etac thin_rl];

Goalw [body_def] "finite (dom body)";
by (rtac finite_dom_map_of 1);
qed "finite_dom_body";

Goalw [WT_bodies_def, body_def] "[| WT_bodies; body pn = Some b |] ==> WT b";
by (dtac map_of_SomeD 1);
by (Fast_tac 1);
qed "WT_bodiesD";

val WTs_elim_cases = map WTs.mk_cases
   ["WT SKIP", "WT (X:==a)", "WT (LOCAL Y:=a IN c)", 
    "WT (c1;;c2)","WT (IF b THEN c1 ELSE c2)", "WT (WHILE b DO c)",
    "WT (BODY P)", "WT (X:=CALL P(a))"];

AddSEs WTs_elim_cases;
