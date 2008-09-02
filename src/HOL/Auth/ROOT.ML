(*  Title:      HOL/Auth/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Root file for protocol proofs.
*)

use_thys [

(* Conventional protocols: rely on 
   conventional Message, Event and Public *)

(*Shared-key protocols*)
  "NS_Shared",
  "Kerberos_BAN",
  "Kerberos_BAN_Gets",
  "KerberosIV",
  "KerberosIV_Gets",
  "KerberosV",
  "OtwayRees",
  "OtwayRees_AN",
  "OtwayRees_Bad",
  "OtwayReesBella",
  "WooLam",
  "Recur",
  "Yahalom",
  "Yahalom2",
  "Yahalom_Bad",
  "ZhouGollmann",

(*Public-key protocols*)
  "NS_Public_Bad",
  "NS_Public",
  "TLS",
  "CertifiedEmail",

(*Smartcard protocols: rely on conventional Message and on new
  EventSC and Smartcard *)

  "Smartcard/ShoupRubin",
  "Smartcard/ShoupRubinBella",

(*Blanqui's "guard" concept: protocol-independent secrecy*)
  "Guard/P1",
  "Guard/P2",
  "Guard/Guard_NS_Public",
  "Guard/Guard_OtwayRees",
  "Guard/Guard_Yahalom",
  "Guard/Proto"
];
