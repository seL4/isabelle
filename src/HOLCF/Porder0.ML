(*  Title:      HOLCF/Porder0.ML
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

    derive the characteristic axioms for the characteristic constants *)

open Porder0;

qed_goalw "refl_less" thy [ po_def ] "x << x"
(fn prems =>
        [
        (fast_tac (HOL_cs addSIs [ax_refl_less]) 1)
        ]);

qed_goalw "antisym_less" thy [ po_def ] "[| x << y; y << x |] ==> x = y"
(fn prems =>
        [
        (fast_tac (HOL_cs addSIs prems@[ax_antisym_less]) 1)
        ]);

qed_goalw "trans_less" thy [ po_def ] "[| x << y; y << z |] ==> x << z"
(fn prems =>
        [
        (fast_tac (HOL_cs addIs prems@[ax_trans_less]) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* minimal fixes least element                                              *)
(* ------------------------------------------------------------------------ *)
bind_thm("minimal2UU",allI RS (prove_goal thy "!x.uu<<x==>uu=(@u.!y.u<<y)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac antisym_less 1),
        (etac spec 1),
        (res_inst_tac [("a","uu")] selectI2 1),
	(atac 1),
	(etac spec 1)
        ])));
