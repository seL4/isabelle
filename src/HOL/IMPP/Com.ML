Goalw [dom_def] "m a = Some b ==> a : dom m";
by Auto_tac;
qed "domI";

Goalw [dom_def] "a : dom m ==> ? b. m a = Some b";
by Auto_tac;
qed "domD";
AddSDs [domD];

val make_imp_tac = EVERY'[rtac mp, fn i => atac (i+1), etac thin_rl];

Goalw [body_def] "finite (dom body)";
br finite_dom_map_of 1;
qed "finite_dom_body";

Goalw [WT_bodies_def, body_def] "[| WT_bodies; body pn = Some b |] ==> WT b";
bd map_of_SomeD 1;
by (Fast_tac 1);
qed "WT_bodiesD";

val WTs_elim_cases = map WTs.mk_cases
   ["WT SKIP", "WT (X:==a)", "WT (LOCAL Y:=a IN c)", 
    "WT (c1;;c2)","WT (IF b THEN c1 ELSE c2)", "WT (WHILE b DO c)",
    "WT (BODY P)", "WT (X:=CALL P(a))"];

AddSEs WTs_elim_cases;
