(*  Title: 	ZF/Coind/Language.ML
    ID:         $Id$
    Author: 	Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

(* ############################################################ *)
(* General lemmas                                               *)
(* ############################################################ *)

goal ZF.thy "!!a.~a=b ==> ~a:{b}";
by (fast_tac ZF_cs 1);    
qed "notsingletonI";

goal ZF.thy "!!a.~a:{b} ==> ~a=b";
by (fast_tac ZF_cs 1);    
qed "notsingletonD";

val prems = goal ZF.thy "[| a~:{b}; a~=b ==> P |] ==> P";
by (cut_facts_tac prems 1);
by (resolve_tac prems 1);
by (fast_tac ZF_cs 1);    
qed "notsingletonE";

goal ZF.thy "!!x. x : A Un B ==> x: B Un A";
by (fast_tac ZF_cs 1);
qed "lem_fix";

goal ZF.thy "!!A.[| x~:A; x=y |] ==> y~:A";
by (fast_tac ZF_cs 1);
qed "map_lem1";


open Language;

(* ############################################################ *)
(* Inclusion in Quine Universes                                 *)
(* ############################################################ *)

goal Language.thy "!!c.c:Const ==> c:quniv(A)";
by (fast_tac (ZF_cs addIs [univ_subset_quniv RS subsetD,constU]) 1);
qed "constQU";

goal Language.thy "!!x.x:ExVar ==> x:quniv(A)";
by (fast_tac (ZF_cs addIs [univ_subset_quniv RS subsetD,exvarU]) 1);
qed "exvarQU";

goal Language.thy "!!e.e:Exp ==> e:quniv(0)";
by (rtac subsetD 1);
by (rtac subset_trans 1);
by (rtac Exp.dom_subset 1);
by (rtac univ_subset_quniv 1);
by (assume_tac 1);
qed "expQU";

