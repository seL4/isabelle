(*  Title:      ZF/AC/first.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Lemmas involving the first element of a well ordered set
*)

open first;

goalw thy [first_def] "!!b. first(b,B,r) ==> b:B";
by (fast_tac AC_cs 1);
val first_is_elem = result();

goalw thy [well_ord_def, wf_on_def, wf_def,     first_def] 
        "!!r. [| well_ord(A,r); B<=A; B~=0 |] ==> (EX! b. first(b,B,r))";
by (REPEAT (eresolve_tac [conjE,allE,disjE] 1));
by (contr_tac 1);
by (etac bexE 1);
by (res_inst_tac [("a","x")] ex1I 1);
by (fast_tac ZF_cs 2);
by (rewrite_goals_tac [tot_ord_def, linear_def]);
by (fast_tac ZF_cs 1);
val well_ord_imp_ex1_first = result();

goal thy "!!r. [| well_ord(A,r); B<=A; B~=0 |] ==> (THE b. first(b,B,r)) : B";
by (dtac well_ord_imp_ex1_first 1 THEN REPEAT (assume_tac 1));
by (rtac first_is_elem 1);
by (etac theI 1);
val the_first_in = result();
