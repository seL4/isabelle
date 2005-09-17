(* $Id$ *)

val make_imp_tac = EVERY'[rtac mp, fn i => atac (i+1), etac thin_rl];

Goalw [body_def] "finite (dom body)";
by (rtac (thm"finite_dom_map_of") 1);
qed "finite_dom_body";

Goalw [WT_bodies_def, body_def] "[| WT_bodies; body pn = Some b |] ==> WT b";
by (dtac (thm"map_of_SomeD") 1);
by (Fast_tac 1);
qed "WT_bodiesD";

AddSEs WTs_elim_cases;
