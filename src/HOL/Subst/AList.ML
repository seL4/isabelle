(*  Title:      Subst/AList.ML
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Association lists.
*)

open AList;

val prems = goal AList.thy
    "[| P([]);   \
\       !!x y xs. P(xs) ==> P((x,y)#xs) |]  ==> P(l)";
by (induct_tac "l" 1);
by (split_all_tac 2);
by (REPEAT (ares_tac prems 1));
qed "alist_induct";

(*Perform induction on xs. *)
fun alist_ind_tac a M = 
    EVERY [induct_thm_tac alist_induct a M,
           rename_last_tac a ["1"] (M+1)];
