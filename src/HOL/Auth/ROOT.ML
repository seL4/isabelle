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

use_thy "Shared";
use_thy "NS_Shared";
use_thy "OtwayRees";
use_thy "OtwayRees_AN";
use_thy "OtwayRees_Bad";
use_thy "Yahalom";
use_thy "Yahalom2";

