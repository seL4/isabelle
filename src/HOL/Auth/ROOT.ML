(*  Title:      HOL/Auth/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Root file for protocol proofs.
*)

no_document use_thy "NatPair";

set timing;

(* Conventional protocols: rely on 
   conventional Message, Event and Public *)

(*Shared-key protocols*)
time_use_thy "NS_Shared";
time_use_thy "Kerberos_BAN";
time_use_thy "Kerberos_BAN_Gets";
time_use_thy "KerberosIV";
time_use_thy "KerberosIV_Gets";
time_use_thy "KerberosV";
time_use_thy "OtwayRees";
time_use_thy "OtwayRees_AN";
time_use_thy "OtwayRees_Bad";
time_use_thy "OtwayReesBella";
time_use_thy "WooLam";
time_use_thy "Recur";
time_use_thy "Yahalom";
time_use_thy "Yahalom2";
time_use_thy "Yahalom_Bad";
time_use_thy "ZhouGollmann";

(*Public-key protocols*)
time_use_thy "NS_Public_Bad";
time_use_thy "NS_Public";
time_use_thy "TLS";
time_use_thy "CertifiedEmail";

(*Smartcard protocols: rely on conventional Message and on new
  EventSC and Smartcard *)

with_path "Smartcard" time_use_thy "ShoupRubin";
with_path "Smartcard" time_use_thy "ShoupRubinBella";

(*Blanqui's "guard" concept: protocol-independent secrecy*)
with_path "Guard" (app time_use_thy)
  ["P1", "P2", "Guard_NS_Public", "Guard_OtwayRees", "Guard_Yahalom", "Proto"];
