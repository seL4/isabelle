(*  Title:      HOL/Auth/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Root file for protocol proofs.
*)

writeln"Root file for HOL/Auth";

set proof_timing;
goals_limit := 1;
HOL_quantifiers := false;

(*Shared-key protocols*)
time_use_thy "NS_Shared";
time_use_thy "Kerberos_BAN";
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
time_use_thy "TLS";
