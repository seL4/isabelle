(*  Title: 	ZF/IMP/Assign.ML
    ID:         $Id$
    Author: 	Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

open Assign;

val assign_type = prove_goalw Assign.thy [assign_def]
	"[| sigma:loc -> nat; n:nat |] ==> sigma[n/x] : loc -> nat"
    (fn prems => [(fast_tac  
                   (ZF_cs addIs [apply_type,lam_type,if_type]@prems) 1)]);
