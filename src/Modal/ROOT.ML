(*  Title: 	91/Modal/ROOT
    ID:         $Id$
    Author: 	Martin Coen
    Copyright   1991  University of Cambridge
*)

val banner = "Modal Logic (over LK)";
writeln banner;

use_thy "Modal0";

structure Modal0_rls = 
struct

val rewrite_rls = [Modal0.strimp_def,Modal0.streqv_def];

local
  val iffR = prove_goal thy 
      "[| $H,P |- $E,Q,$F;  $H,Q |- $E,P,$F |] ==> $H |- $E, P <-> Q, $F"
   (fn prems=>
    [ (rewrite_goals_tac [iff_def]),
      (REPEAT (resolve_tac (prems@[conjR,impR]) 1)) ]);

  val iffL = prove_goal thy 
     "[| $H,$G |- $E,P,Q;  $H,Q,P,$G |- $E |] ==> $H, P <-> Q, $G |- $E"
   (fn prems=>
    [ rewrite_goals_tac [iff_def],
      (REPEAT (resolve_tac (prems@[conjL,impL,basic]) 1)) ])
in
val safe_rls   = [basic,conjL,conjR,disjL,disjR,impL,impR,notL,notR,iffL,iffR];
val unsafe_rls = [allR,exL];
val bound_rls  = [allL,exR];
end

end;

use "prover.ML";

use_thy"T";

local open Modal0_rls T
in structure MP_Rule : MODAL_PROVER_RULE =
   struct
    val rewrite_rls = rewrite_rls
    val safe_rls    = safe_rls
    val unsafe_rls  = unsafe_rls @ [boxR,diaL]
    val bound_rls   = bound_rls @ [boxL,diaR]
    val aside_rls   = [lstar0,lstar1,lstar2,rstar0,rstar1,rstar2]
   end
end;
structure T_Prover = Modal_ProverFun(MP_Rule);  

use_thy"S4";

local open Modal0_rls S4
in structure MP_Rule : MODAL_PROVER_RULE =
   struct
    val rewrite_rls = rewrite_rls
    val safe_rls    = safe_rls
    val unsafe_rls  = unsafe_rls @ [boxR,diaL]
    val bound_rls   = bound_rls @ [boxL,diaR]
    val aside_rls   = [lstar0,lstar1,lstar2,rstar0,rstar1,rstar2]
   end;
end;
structure S4_Prover = Modal_ProverFun(MP_Rule);

use_thy"S43";

local open Modal0_rls S43
in structure MP_Rule : MODAL_PROVER_RULE =
   struct
    val rewrite_rls = rewrite_rls
    val safe_rls    = safe_rls
    val unsafe_rls  = unsafe_rls @ [pi1,pi2]
    val bound_rls   = bound_rls @ [boxL,diaR]
    val aside_rls   = [lstar0,lstar1,lstar2,rstar0,rstar1,rstar2,S43pi0,S43pi1,S43pi2]
   end;
end;
structure S43_Prover = Modal_ProverFun(MP_Rule);  

make_chart ();   (*make HTML chart*)

val Modal_build_completed = ();	(*indicate successful build*)

(*printing functions are inherited from LK*)
