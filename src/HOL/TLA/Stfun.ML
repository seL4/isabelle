(* 
    File:	 Stfun.ML
    Author:      Stephan Merz
    Copyright:   1998 University of Munich

Lemmas and tactics for states and state functions.
*)

Goalw [basevars_def] "!!vs. basevars vs ==> EX u. vs u = c";
by (res_inst_tac [("b","c"),("f","vs")] rangeE 1);
by Auto_tac;
qed "basevars";

Goal "!!x y. basevars (x,y) ==> basevars x";
by (simp_tac (simpset() addsimps [basevars_def]) 1);
by (rtac equalityI 1);
 by (rtac subset_UNIV 1);
by (rtac subsetI 1);
by (dres_inst_tac [("c", "(xa, arbitrary)")] basevars 1);
by Auto_tac;
qed "base_pair1";

Goal "!!x y. basevars (x,y) ==> basevars y";
by (simp_tac (simpset() addsimps [basevars_def]) 1);
by (rtac equalityI 1);
 by (rtac subset_UNIV 1);
by (rtac subsetI 1);
by (dres_inst_tac [("c", "(arbitrary, xa)")] basevars 1);
by Auto_tac;
qed "base_pair2";

Goal "!!x y. basevars (x,y) ==> basevars x & basevars y";
by (rtac conjI 1);
by (etac base_pair1 1);
by (etac base_pair2 1);
qed "base_pair";

(* Since the unit type has just one value, any state function can be
   regarded as "base". The following axiom can sometimes be useful
   because it gives a trivial solution for "basevars" premises.
*)
Goalw [basevars_def] "basevars (v::unit stfun)";
by Auto_tac;
qed "unit_base";

(*  [| basevars v; !!x. v x = c ==> Q |] ==> Q  *)
bind_thm("baseE", (standard (basevars RS exE)));

(* -------------------------------------------------------------------------------
   The following shows that there should not be duplicates in a "stvars" tuple:

Goal "!!v. basevars (v::bool stfun, v) ==> False";
by (etac baseE 1);
by (subgoal_tac "(LIFT (v,v)) x = (True, False)" 1); 
by (atac 2);
by (Asm_full_simp_tac 1);

------------------------------------------------------------------------------- *)
