(*  Title:      HOL/Auth/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Root file for protocol proofs.
*)

HOL_build_completed;    (*Make examples fail if HOL did*)

writeln"Root file for HOL/Auth";
proof_timing := true;
goals_limit := 1;

(*Shared-key protocols*)
time_use_thy "NS_Shared";
time_use_thy "OtwayRees";
time_use_thy "OtwayRees_AN";
time_use_thy "OtwayRees_Bad";
time_use_thy "WooLam";
time_use_thy "Recur";
time_use_thy "Yahalom";
time_use_thy "Yahalom2";

(*Public-key protocols*)
time_use_thy "NS_Public_Bad";
time_use_thy "NS_Public";

