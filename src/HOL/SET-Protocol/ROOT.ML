(*  Title:      HOL/SET-Protocol/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2003  University of Cambridge

Root file for the SET protocol proofs.
*)

goals_limit := 1;
set timing;

no_document use_thy "NatPair";
time_use_thy "Cardholder_Registration";
time_use_thy "Merchant_Registration";
time_use_thy "Purchase";

