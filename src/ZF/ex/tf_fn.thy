(*  Title: 	ZF/ex/TF.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Trees & forests, a mutually recursive type definition.
*)

TF_Fn = TF + ListFn +
consts
  TF_rec	 ::	"[i, [i,i,i]=>i, i, [i,i,i,i]=>i] => i"
  TF_map      	 ::      "[i=>i, i] => i"
  TF_size 	 ::      "i=>i"
  TF_preorder 	 ::      "i=>i"
  list_of_TF 	 ::      "i=>i"
  TF_of_list 	 ::      "i=>i"

rules
  TF_rec_def
    "TF_rec(z,b,c,d) == Vrec(z,  			\
\      %z r. tree_forest_case(%x tf. b(x, tf, r`tf), 	\
\                             c, 			\
\		              %t tf. d(t, tf, r`t, r`tf), z))"

  list_of_TF_def
    "list_of_TF(z) == TF_rec(z, %x tf r. [Tcons(x,tf)], [], \
\		             %t tf r1 r2. Cons(t, r2))"

  TF_of_list_def
    "TF_of_list(tf) == list_rec(tf, Fnil,  %t tf r. Fcons(t,r))"

  TF_map_def
    "TF_map(h,z) == TF_rec(z, %x tf r.Tcons(h(x),r), Fnil, \
\                           %t tf r1 r2. Fcons(r1,r2))"

  TF_size_def
    "TF_size(z) == TF_rec(z, %x tf r.succ(r), 0, %t tf r1 r2. r1#+r2)"

  TF_preorder_def
    "TF_preorder(z) == TF_rec(z, %x tf r.Cons(x,r), Nil, %t tf r1 r2. r1@r2)"

end
