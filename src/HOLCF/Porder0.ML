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
by (rtac antisym_less 1);
by (etac spec 1);
by (res_inst_tac [("a","uu")] selectI2 1);
by (atac 1);
by (etac spec 1);
bind_thm ("minimal2UU", allI RS result());

(* ------------------------------------------------------------------------ *)
(* the reverse law of anti--symmetrie of <<                                 *)
(* ------------------------------------------------------------------------ *)

Goal "(x::'a::po)=y ==> x << y & y << x";
by (rtac conjI 1);
by ((rtac subst 1) THEN (rtac refl_less 2) THEN (atac 1));
by ((rtac subst 1) THEN (rtac refl_less 2) THEN (etac sym 1));
qed "antisym_less_inverse";


Goal "[| (a::'a::po) << b; c << a; b << d|] ==> c << d";
by (etac trans_less 1);
by (etac trans_less 1);
by (atac 1);
qed "box_less";

Goal "((x::'a::po)=y) = (x << y & y << x)";
by (fast_tac (HOL_cs addSEs [antisym_less_inverse] addSIs [antisym_less]) 1);
qed "po_eq_conv";
