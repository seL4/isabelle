(*  Title:      Modal/modal0
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1991  University of Cambridge
*)

structure Modal0_rls = 
struct

val rewrite_rls = [Modal0.strimp_def,Modal0.streqv_def];

local
  val iffR = prove_goal thy 
      "[| $H,P |- $E,Q,$F;  $H,Q |- $E,P,$F |] ==> $H |- $E, P <-> Q, $F"
   (fn prems=>
    [ (rewtac iff_def),
      (REPEAT (resolve_tac (prems@[conjR,impR]) 1)) ]);

  val iffL = prove_goal thy 
     "[| $H,$G |- $E,P,Q;  $H,Q,P,$G |- $E |] ==> $H, P <-> Q, $G |- $E"
   (fn prems=>
    [ rewtac iff_def,
      (REPEAT (resolve_tac (prems@[conjL,impL,basic]) 1)) ])
in
val safe_rls   = [basic,conjL,conjR,disjL,disjR,impL,impR,notL,notR,iffL,iffR];
val unsafe_rls = [allR,exL];
val bound_rls  = [allL,exR];
end

end;
