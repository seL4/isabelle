(*  Title:      Modal/S43
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1991  University of Cambridge

This implements Rajeev Gore's sequent calculus for S43.
*)

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
