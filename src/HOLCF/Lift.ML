(*  Title:      HOLCF/Lift.ML
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1997 Technische Universitaet Muenchen

Theorems for Lift.thy
*)


(* ---------------------------------------------------------- *)
    section"Continuity Proofs for flift1, flift2, if";
(* ---------------------------------------------------------- *)
(* need the instance into flat *)


(* flift1 is continuous in its argument itself*)
goal thy "cont (lift_case UU f)"; 
by (rtac flatdom_strict2cont 1);
by (Simp_tac 1);
qed"cont_flift1_arg";

(* flift1 is continuous in a variable that occurs only 
   in the Def branch *)

goal thy "!!f. [| !! a. cont (%y. (f y) a) |] ==> \
\          cont (%y. lift_case UU (f y))";
by (rtac cont2cont_CF1L_rev 1);
by (strip_tac 1);
by (res_inst_tac [("x","y")] Lift_cases 1);
by (Asm_simp_tac 1);
by (fast_tac (HOL_cs addss !simpset) 1);
qed"cont_flift1_not_arg";

(* flift1 is continuous in a variable that occurs either 
   in the Def branch or in the argument *)

goal thy "!!f. [| !! a. cont (%y. (f y) a); cont g|] ==> \
\   cont (%y. lift_case UU (f y) (g y))";
by (rtac cont2cont_app 1);
back();
by (safe_tac set_cs);
by (rtac cont_flift1_not_arg 1);
by (Auto_tac());
by (rtac cont_flift1_arg 1);
qed"cont_flift1_arg_and_not_arg";

(* flift2 is continuous in its argument itself *)

goal thy "cont (lift_case UU (%y. Def (f y)))";
by (rtac flatdom_strict2cont 1);
by (Simp_tac 1);
qed"cont_flift2_arg";


(* ---------------------------------------------------------- *)
(*    Extension of cont_tac and installation of simplifier    *)
(* ---------------------------------------------------------- *)

bind_thm("cont2cont_CF1L_rev2",allI RS cont2cont_CF1L_rev);

val cont_lemmas_ext = [cont_flift1_arg,cont_flift2_arg,
                       cont_flift1_arg_and_not_arg,cont2cont_CF1L_rev2, 
                       cont_fapp_app,cont_fapp_app_app,cont_if];

val cont_lemmas2 =  cont_lemmas1 @ cont_lemmas_ext;
                 
Addsimps cont_lemmas_ext;         

fun cont_tac  i = resolve_tac cont_lemmas2 i;
fun cont_tacR i = REPEAT (cont_tac i);

fun cont_tacRs i = simp_tac (!simpset addsimps [flift1_def,flift2_def]) i THEN
                  REPEAT (cont_tac i);


simpset := !simpset addSolver (K (DEPTH_SOLVE_1 o cont_tac));



(* ---------------------------------------------------------- *)
              section"flift1, flift2";
(* ---------------------------------------------------------- *)


goal thy "flift1 f`(Def x) = (f x)";
by (simp_tac (!simpset addsimps [flift1_def]) 1);
qed"flift1_Def";

goal thy "flift2 f`(Def x) = Def (f x)";
by (simp_tac (!simpset addsimps [flift2_def]) 1);
qed"flift2_Def";

goal thy "flift1 f`UU = UU";
by (simp_tac (!simpset addsimps [flift1_def]) 1);
qed"flift1_UU";

goal thy "flift2 f`UU = UU";
by (simp_tac (!simpset addsimps [flift2_def]) 1);
qed"flift2_UU";

Addsimps [flift1_Def,flift2_Def,flift1_UU,flift2_UU];

goal thy "!!x. x~=UU ==> (flift2 f)`x~=UU";
by (def_tac 1);
qed"flift2_nUU";

Addsimps [flift2_nUU];


