(*  Title:      Modal/S4
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1991  University of Cambridge
*)

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
