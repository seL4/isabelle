(*  Title:      HOLCF/Porder0.ML
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

    derive the characteristic axioms for the characteristic constants 
*)

AddIffs [refl_less];

(* ------------------------------------------------------------------------ *)
(* minimal fixes least element                                              *)
(* ------------------------------------------------------------------------ *)
Goal "!x::'a::po. uu<<x ==> uu=(@u.!y. u<<y)";
by (blast_tac (claset() addIs [selectI2,antisym_less]) 1);
bind_thm ("minimal2UU", allI RS result());

(* ------------------------------------------------------------------------ *)
(* the reverse law of anti--symmetrie of <<                                 *)
(* ------------------------------------------------------------------------ *)

Goal "(x::'a::po)=y ==> x << y & y << x";
by (Blast_tac 1);
qed "antisym_less_inverse";


Goal "[| (a::'a::po) << b; c << a; b << d|] ==> c << d";
by (etac trans_less 1);
by (etac trans_less 1);
by (atac 1);
qed "box_less";

Goal "((x::'a::po)=y) = (x << y & y << x)";
by (fast_tac (HOL_cs addSEs [antisym_less_inverse] addSIs [antisym_less]) 1);
qed "po_eq_conv";
