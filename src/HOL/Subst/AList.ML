(*  Title:      Substitutions/AList.ML
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For AList.thy.
*)

open AList;

let fun prove s = prove_goalw AList.thy [alist_rec_def,assoc_def] s 
			  (fn _ => [Simp_tac 1])
in 
Addsimps 
 (
   map prove 
   ["alist_rec [] c d = c",
    "alist_rec ((a,b)#al) c d = d a b al (alist_rec al c d)",
    "assoc v d [] = d",
    "assoc v d ((a,b)#al) = (if v=a then b else assoc v d al)"] 
 )
end;


val prems = goal AList.thy
    "[| P([]);   \
\       !!x y xs. P(xs) ==> P((x,y)#xs) |]  ==> P(l)";
by (induct_tac "l" 1);
by (split_all_tac 2);
by (REPEAT (ares_tac prems 1));
qed "alist_induct";

(*Perform induction on xs. *)
fun alist_ind_tac a M = 
    EVERY [res_inst_tac [("l",a)] alist_induct M,
           rename_last_tac a ["1"] (M+1)];
