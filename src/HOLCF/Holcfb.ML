(*  Title:      HOLCF/holcfb.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Changed by: David von Oheimb
    Copyright   1993  Technische Universitaet Muenchen
*)


open Holcfb;

(* ------------------------------------------------------------------------ *)
(* Some lemmas in HOL.thy                                                   *)
(* ------------------------------------------------------------------------ *)



val classical3 = (notE RS notI); (* [| ?P ==> ~ ?P1; ?P ==> ?P1 |] ==> ~ ?P *)
