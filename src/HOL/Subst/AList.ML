(*  Title: 	Substitutions/AList.ML
    Author: 	Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For AList.thy.
*)

open AList;

val al_rews = 
  let fun mk_thm s = prove_goalw AList.thy [alist_rec_def,assoc_def] s 
                            (fn _ => [Simp_tac 1])
  in map mk_thm 
     ["alist_rec [] c d = c",
      "alist_rec ((a,b)#al) c d = d a b al (alist_rec al c d)",
      "assoc v d [] = d",
      "assoc v d ((a,b)#al) = (if v=a then b else assoc v d al)"] end;

val prems = goal AList.thy
    "[| P([]);   \
\       !!x y xs. P(xs) ==> P((x,y)#xs) |]  ==> P(l)";
by (list.induct_tac "l" 1);
by (resolve_tac prems 1);
by (rtac PairE 1);
by (etac ssubst 1);
by (resolve_tac prems 1);
by (assume_tac 1);
qed "alist_induct";

(*Perform induction on xs. *)
fun alist_ind_tac a M = 
    EVERY [res_inst_tac [("l",a)] alist_induct M,
	   rename_last_tac a ["1"] (M+1)];
