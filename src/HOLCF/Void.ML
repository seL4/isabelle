(*  Title:      HOLCF/void.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Lemmas for void.thy.

These lemmas are prototype lemmas for class porder 
see class theory porder.thy
*)

open Void;

(* ------------------------------------------------------------------------ *)
(* A non-emptyness result for Void                                          *)
(* ------------------------------------------------------------------------ *)

qed_goalw "VoidI" Void.thy [UU_void_Rep_def,Void_def] 
 " UU_void_Rep : Void"
(fn prems =>
        [
        (rtac (mem_Collect_eq RS ssubst) 1),
        (rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* less_void is a partial ordering on void                                  *)
(* ------------------------------------------------------------------------ *)

qed_goalw "refl_less_void" Void.thy [ less_void_def ] "less_void x x"
(fn prems =>
        [
        (fast_tac HOL_cs 1)
        ]);

qed_goalw "antisym_less_void" Void.thy [ less_void_def ] 
        "[|less_void x y; less_void y x|] ==> x = y"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (Rep_Void_inverse RS subst) 1),
        (etac subst 1),
        (rtac (Rep_Void_inverse RS sym) 1)
        ]);

qed_goalw "trans_less_void" Void.thy [ less_void_def ] 
        "[|less_void x y; less_void y z|] ==> less_void x z"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (fast_tac HOL_cs 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* a technical lemma about void:                                            *)
(* every element in void is represented by UU_void_Rep                      *)
(* ------------------------------------------------------------------------ *)

qed_goal "unique_void" Void.thy "Rep_Void(x) = UU_void_Rep"
(fn prems =>
        [
        (rtac (mem_Collect_eq RS subst) 1), 
        (fold_goals_tac [Void_def]),
        (rtac Rep_Void 1)
        ]);

        


