(*  Title:      HOL/Auth/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Root file for protocol proofs.
*)

goals_limit := 1;

(*Shared-key protocols*)
time_use_thy "NS_Shared";
time_use_thy "Kerberos_BAN";
time_use_thy "KerberosIV";
time_use_thy "OtwayRees";
time_use_thy "OtwayRees_AN";
time_use_thy "OtwayRees_Bad";
time_use_thy "WooLam";
time_use_thy "Recur";
time_use_thy "Yahalom";
time_use_thy "Yahalom2";
time_use_thy "Yahalom_Bad";

(*Public-key protocols*)
time_use_thy "NS_Public_Bad";
time_use_thy "NS_Public";
time_use_thy "TLS";

(*Blanqui's "guard" concept: protocol-independent secrecy*)
time_use_thy "Guard/P1";
time_use_thy "Guard/P2";
time_use_thy "Guard/NS_Public";
time_use_thy "Guard/OtwayRees";
time_use_thy "Guard/Yahalom";
time_use_thy "Guard/Proto";
