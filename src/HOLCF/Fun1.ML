(*  Title:      HOLCF/Fun1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Lemmas for fun1.thy 
*)

open Fun1;

(* ------------------------------------------------------------------------ *)
(* less_fun is a partial order on 'a => 'b                                  *)
(* ------------------------------------------------------------------------ *)

qed_goalw "refl_less_fun" thy [less_fun_def] "less(f::'a::term =>'b::po) f"
(fn prems =>
        [
        (fast_tac (HOL_cs addSIs [refl_less]) 1)
        ]);

qed_goalw "antisym_less_fun" Fun1.thy [less_fun_def] 
        "[|less (f1::'a::term =>'b::po) f2; less f2 f1|] ==> f1 = f2"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (stac expand_fun_eq 1),
        (fast_tac (HOL_cs addSIs [antisym_less]) 1)
        ]);

qed_goalw "trans_less_fun" Fun1.thy [less_fun_def] 
        "[|less (f1::'a::term =>'b::po) f2; less f2 f3 |] ==> less f1 f3"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (strip_tac 1),
        (rtac trans_less 1),
        (etac allE 1),
        (atac 1),
        ((etac allE 1) THEN (atac 1))
        ]);
