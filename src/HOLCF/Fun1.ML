(*  Title:      HOLCF/Fun1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Definition of the partial ordering for the type of all functions => (fun)
*)

(* ------------------------------------------------------------------------ *)
(* less_fun is a partial order on 'a => 'b                                  *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [less_fun_def] "(f::'a::term =>'b::po) << f";
by (fast_tac (HOL_cs addSIs [refl_less]) 1);
qed "refl_less_fun";

val prems = goalw Fun1.thy [less_fun_def] 
        "[|(f1::'a::term =>'b::po) << f2; f2 << f1|] ==> f1 = f2";
by (cut_facts_tac prems 1);
by (stac expand_fun_eq 1);
by (fast_tac (HOL_cs addSIs [antisym_less]) 1);
qed "antisym_less_fun";

val prems = goalw Fun1.thy [less_fun_def] 
        "[|(f1::'a::term =>'b::po) << f2; f2 << f3 |] ==> f1 << f3";
by (cut_facts_tac prems 1);
by (strip_tac 1);
by (rtac trans_less 1);
by (etac allE 1);
by (atac 1);
by ((etac allE 1) THEN (atac 1));
qed "trans_less_fun";
