(*  Title: 	CCL/ex/stream
    ID:         $Id$
    Author: 	Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For stream.thy.

Proving properties about infinite lists using coinduction:
    Lists(A)  is the set of all finite and infinite lists of elements of A.
    ILists(A) is the set of infinite lists of elements of A.
*)

open Stream;

(*** Map of composition is composition of maps ***)

val prems = goal Stream.thy "l:Lists(A) ==> map(f o g,l) = map(f,map(g,l))";
by (eq_coinduct3_tac 
       "{p. EX x y.p=<x,y> & (EX l:Lists(A).x=map(f o g,l) & y=map(f,map(g,l)))}"  1);
by (fast_tac (ccl_cs addSIs prems) 1);
by (safe_tac type_cs);
be (XH_to_E ListsXH) 1;
by (EQgen_tac list_ss [] 1);
by (simp_tac list_ss 1);
by (fast_tac ccl_cs 1);
val map_comp = result();

(*** Mapping the identity function leaves a list unchanged ***)

val prems = goal Stream.thy "l:Lists(A) ==> map(%x.x,l) = l";
by (eq_coinduct3_tac 
       "{p. EX x y.p=<x,y> & (EX l:Lists(A).x=map(%x.x,l) & y=l)}"  1);
by (fast_tac (ccl_cs addSIs prems) 1);
by (safe_tac type_cs);
be (XH_to_E ListsXH) 1;
by (EQgen_tac list_ss [] 1);
by (fast_tac ccl_cs 1);
val map_id = result();

(*** Mapping distributes over append ***)

val prems = goal Stream.thy 
        "[| l:Lists(A); m:Lists(A) |] ==> map(f,l@m) = map(f,l) @ map(f,m)";
by (eq_coinduct3_tac "{p. EX x y.p=<x,y> & (EX l:Lists(A).EX m:Lists(A). \
\                                           x=map(f,l@m) & y=map(f,l) @ map(f,m))}"  1);
by (fast_tac (ccl_cs addSIs prems) 1);
by (safe_tac type_cs);
be (XH_to_E ListsXH) 1;
by (EQgen_tac list_ss [] 1);
be (XH_to_E ListsXH) 1;
by (EQgen_tac list_ss [] 1);
by (fast_tac ccl_cs 1);
val map_append = result();

(*** Append is associative ***)

val prems = goal Stream.thy 
        "[| k:Lists(A); l:Lists(A); m:Lists(A) |] ==> k @ l @ m = (k @ l) @ m";
by (eq_coinduct3_tac "{p. EX x y.p=<x,y> & (EX k:Lists(A).EX l:Lists(A).EX m:Lists(A). \
\                                                   x=k @ l @ m & y=(k @ l) @ m)}"  1);
by (fast_tac (ccl_cs addSIs prems) 1);
by (safe_tac type_cs);
be (XH_to_E ListsXH) 1;
by (EQgen_tac list_ss [] 1);
be (XH_to_E ListsXH) 1;back();
by (EQgen_tac list_ss [] 1);
be (XH_to_E ListsXH) 1;
by (EQgen_tac list_ss [] 1);
by (fast_tac ccl_cs 1);
val append_assoc = result();

(*** Appending anything to an infinite list doesn't alter it ****)

val prems = goal Stream.thy "l:ILists(A) ==> l @ m = l";
by (eq_coinduct3_tac "{p. EX x y.p=<x,y> & (EX l:ILists(A).EX m.x=l@m & y=l)}" 1);
by (fast_tac (ccl_cs addSIs prems) 1);
by (safe_tac set_cs);
be (XH_to_E IListsXH) 1;
by (EQgen_tac list_ss [] 1);
by (fast_tac ccl_cs 1);
val ilist_append = result();

(*** The equivalance of two versions of an iteration function       ***)
(*                                                                    *)
(*        fun iter1(f,a) = a.iter1(f,f(a))                            *)
(*        fun iter2(f,a) = a.map(f,iter2(f,a))                        *)

goalw Stream.thy [iter1_def] "iter1(f,a) = a.iter1(f,f(a))";
br (letrecB RS trans) 1;
by (simp_tac term_ss 1);
val iter1B = result();

goalw Stream.thy [iter2_def] "iter2(f,a) = a . map(f,iter2(f,a))";
br (letrecB RS trans) 1;
br refl 1;
val iter2B = result();

val [prem] =goal Stream.thy
   "n:Nat ==> map(f) ^ n ` iter2(f,a) = f ^ n ` a . map(f) ^ n ` map(f,iter2(f,a))";
br (iter2B RS ssubst) 1;back();back();
by (simp_tac (list_ss addsimps [prem RS nmapBcons]) 1);
val iter2Blemma = result();

goal Stream.thy "iter1(f,a) = iter2(f,a)";
by (eq_coinduct3_tac 
    "{p. EX x y.p=<x,y> & (EX n:Nat.x=iter1(f,f^n`a) & y=map(f)^n`iter2(f,a))}"
    1);
by (fast_tac (type_cs addSIs [napplyBzero RS sym,
			      napplyBzero RS sym RS arg_cong]) 1);
by (EQgen_tac list_ss [iter1B,iter2Blemma] 1);
by (rtac (napply_f RS ssubst) 1 THEN atac 1);
by (res_inst_tac [("f1","f")] (napplyBsucc RS subst) 1);
by (fast_tac type_cs 1);
val iter1_iter2_eq = result();
