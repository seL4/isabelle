(* 
    File:	 Stfun.ML
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

Lemmas and tactics for states and state functions.
*)

(* A stronger version of existential elimination (goal needn't be boolean) *)
qed_goalw "exE_prop" HOL.thy [Ex_def]
  "[| ? x::'a. P(x); !!x. P(x) ==> PROP R |] ==> PROP R"
  (fn prems => [REPEAT(resolve_tac prems 1)]);

(* Might as well use that version in automated proofs *)
AddSEs [exE_prop];

(*  [| base_var v; !!x. v x = c ==> PROP R |] ==> PROP R  *)
bind_thm("baseE", (standard (base_var RS exE_prop)));

qed_goal "PairVarE" Stfun.thy
  "[| <v,w> u = (x,y); [| v u = x; w u = y |] ==> PROP R |] ==> PROP R"
  (fn prems => [cut_facts_tac prems 1, resolve_tac prems 1,
		ALLGOALS (asm_full_simp_tac (!simpset addsimps [pairSF_def]))
               ]);

