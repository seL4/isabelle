(* 
    File:	 Stfun.ML
    Author:      Stephan Merz
    Copyright:   1998 University of Munich

Lemmas and tactics for states and state functions.
*)

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
