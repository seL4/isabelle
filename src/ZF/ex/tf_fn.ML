(*  Title: 	ZF/ex/tf.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

For tf.thy.  Trees & forests, a mutually recursive type definition.

Still needs

"TF_reflect == (%z. TF_rec(z, %x ts r. Tcons(x,r), 0, 
               %t ts r1 r2. TF_of_list(list_of_TF(r2) @ <r1,0>)))"
*)

open TF_Fn;


(*** TF_rec -- by Vset recursion ***)

(*Used only to verify TF_rec*)
val TF_congs = mk_typed_congs TF.thy 
		   [("b", "[i,i,i]=>i"), ("d", "[i,i,i,i]=>i")];

(** conversion rules **)

goal TF_Fn.thy "TF_rec(Tcons(a,tf), b, c, d) = b(a, tf, TF_rec(tf,b,c,d))";
by (rtac (TF_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac TF.con_defs);
by (SIMP_TAC (rank_ss addcongs TF_congs) 1);
val TF_rec_Tcons = result();

goal TF_Fn.thy "TF_rec(Fnil, b, c, d) = c";
by (rtac (TF_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac TF.con_defs);
by (SIMP_TAC rank_ss 1);
val TF_rec_Fnil = result();

goal TF_Fn.thy "TF_rec(Fcons(t,tf), b, c, d) = \
\      d(t, tf, TF_rec(t, b, c, d), TF_rec(tf, b, c, d))";
by (rtac (TF_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac TF.con_defs);
by (SIMP_TAC (rank_ss addcongs TF_congs) 1);
val TF_rec_Fcons = result();

(*list_ss includes list operations as well as arith_ss*)
val TF_rec_ss = list_ss addrews
  [TF_rec_Tcons, TF_rec_Fnil, TF_rec_Fcons, TconsI, FnilI, FconsI];

(** Type checking **)

val major::prems = goal TF_Fn.thy
    "[| z: tree_forest(A);  \
\       !!x tf r. [| x: A;  tf: forest(A);  r: C(tf) 		\
\                 |] ==> b(x,tf,r): C(Tcons(x,tf));     	\
\	c : C(Fnil);        					\
\       !!t tf r1 r2. [| t: tree(A);  tf: forest(A);  r1: C(t); r2: C(tf) \
\                     |] ==> d(t,tf,r1,r2): C(Fcons(t,tf))    	\
\    |] ==> TF_rec(z,b,c,d) : C(z)";
by (rtac (major RS TF.induct) 1);
by (ALLGOALS (ASM_SIMP_TAC (TF_rec_ss addrews prems)));
val TF_rec_type = result();

(*Mutually recursive version*)
val prems = goal TF_Fn.thy
    "[| !!x tf r. [| x: A;  tf: forest(A);  r: D(tf) 		\
\                 |] ==> b(x,tf,r): C(Tcons(x,tf));     	\
\	c : D(Fnil);        					\
\       !!t tf r1 r2. [| t: tree(A);  tf: forest(A);  r1: C(t); r2: D(tf) \
\                     |] ==> d(t,tf,r1,r2): D(Fcons(t,tf))    	\
\    |] ==> (ALL t:tree(A).    TF_rec(t,b,c,d)  : C(t)) &  	\
\           (ALL tf: forest(A). TF_rec(tf,b,c,d) : D(tf))";
by (rewtac Ball_def);
by (rtac TF.mutual_induct 1);
by (ALLGOALS (ASM_SIMP_TAC (TF_rec_ss addrews prems)));
val tree_forest_rec_type = result();


(** Versions for use with definitions **)

val [rew] = goal TF_Fn.thy
    "[| !!z. j(z)==TF_rec(z,b,c,d) |] ==> j(Tcons(a,tf)) = b(a,tf,j(tf))";
by (rewtac rew);
by (rtac TF_rec_Tcons 1);
val def_TF_rec_Tcons = result();

val [rew] = goal TF_Fn.thy
    "[| !!z. j(z)==TF_rec(z,b,c,d) |] ==> j(Fnil) = c";
by (rewtac rew);
by (rtac TF_rec_Fnil 1);
val def_TF_rec_Fnil = result();

val [rew] = goal TF_Fn.thy
    "[| !!z. j(z)==TF_rec(z,b,c,d) |] ==> j(Fcons(t,tf)) = d(t,tf,j(t),j(tf))";
by (rewtac rew);
by (rtac TF_rec_Fcons 1);
val def_TF_rec_Fcons = result();

fun TF_recs def = map standard 
    	([def] RL [def_TF_rec_Tcons, def_TF_rec_Fnil, def_TF_rec_Fcons]);


(** list_of_TF and TF_of_list **)

val [list_of_TF_Tcons, list_of_TF_Fnil, list_of_TF_Fcons] =
	TF_recs list_of_TF_def;

goalw TF_Fn.thy [list_of_TF_def]
    "!!z A. z: tree_forest(A) ==> list_of_TF(z) : list(tree(A))";
by (REPEAT (ares_tac ([TF_rec_type,TconsI] @ list_typechecks) 1));
val list_of_TF_type = result();

val [TF_of_list_Nil,TF_of_list_Cons] = list_recs TF_of_list_def;

goalw TF_Fn.thy [TF_of_list_def] 
    "!!l A. l: list(tree(A)) ==> TF_of_list(l) : forest(A)";
by (REPEAT (ares_tac [list_rec_type, FnilI, FconsI] 1));
val TF_of_list_type = result();


(** TF_map **)

val [TF_map_Tcons, TF_map_Fnil, TF_map_Fcons] = TF_recs TF_map_def;

val prems = goalw TF_Fn.thy [TF_map_def]
    "[| !!x. x: A ==> h(x): B |] ==> \
\      (ALL t:tree(A). TF_map(h,t) : tree(B)) &  \
\      (ALL tf: forest(A). TF_map(h,tf) : forest(B))";
by (REPEAT
    (ares_tac ([tree_forest_rec_type, TconsI, FnilI, FconsI] @ prems) 1));
val TF_map_type = result();


(** TF_size **)

val [TF_size_Tcons, TF_size_Fnil, TF_size_Fcons] = TF_recs TF_size_def;

goalw TF_Fn.thy [TF_size_def]
    "!!z A. z: tree_forest(A) ==> TF_size(z) : nat";
by (REPEAT (ares_tac [TF_rec_type, add_type, nat_0I, nat_succI] 1));
val TF_size_type = result();


(** TF_preorder **)

val [TF_preorder_Tcons, TF_preorder_Fnil, TF_preorder_Fcons] =
	TF_recs TF_preorder_def;

goalw TF_Fn.thy [TF_preorder_def]
    "!!z A. z: tree_forest(A) ==> TF_preorder(z) : list(A)";
by (REPEAT (ares_tac [TF_rec_type, app_type,NilI, ConsI] 1));
val TF_preorder_type = result();


(** Term simplification **)

val treeI = tree_subset_TF RS subsetD
and forestI = forest_subset_TF RS subsetD;

val TF_typechecks =
    [TconsI, FnilI, FconsI, treeI, forestI,
     list_of_TF_type, TF_map_type, TF_size_type, TF_preorder_type];

val TF_congs = TF.congs @ 
    mk_congs TF_Fn.thy
    ["TF_rec", "list_of_TF", "TF_of_list", "TF_map", "TF_size", "TF_preorder"];

val TF_rewrites =
   [TF_rec_Tcons, TF_rec_Fnil, TF_rec_Fcons,
    list_of_TF_Tcons, list_of_TF_Fnil, list_of_TF_Fcons,
    TF_of_list_Nil,TF_of_list_Cons,
    TF_map_Tcons, TF_map_Fnil, TF_map_Fcons,
    TF_size_Tcons, TF_size_Fnil, TF_size_Fcons,
    TF_preorder_Tcons, TF_preorder_Fnil, TF_preorder_Fcons];

val TF_ss = list_ss addcongs TF_congs 
		    addrews (TF_rewrites@TF_typechecks);

(** theorems about list_of_TF and TF_of_list **)

(*essentially the same as list induction*)
val major::prems = goal TF_Fn.thy 
    "[| tf: forest(A);  \
\       R(Fnil);        \
\       !!t tf. [| t: tree(A);  tf: forest(A);  R(tf) |] ==> R(Fcons(t,tf))  \
\    |] ==> R(tf)";
by (rtac (major RS (TF.mutual_induct RS conjunct2 RS spec RSN (2,rev_mp))) 1);
by (REPEAT (ares_tac (TrueI::prems) 1));
val forest_induct = result();

goal TF_Fn.thy "!!tf A. tf: forest(A) ==> TF_of_list(list_of_TF(tf)) = tf";
by (etac forest_induct 1);
by (ALLGOALS (ASM_SIMP_TAC TF_ss));
val forest_iso = result();

goal TF_Fn.thy
    "!!ts. ts: list(tree(A)) ==> list_of_TF(TF_of_list(ts)) = ts";
by (etac List.induct 1);
by (ALLGOALS (ASM_SIMP_TAC TF_ss));
val tree_list_iso = result();

(** theorems about TF_map **)

goal TF_Fn.thy "!!z A. z: tree_forest(A) ==> TF_map(%u.u, z) = z";
by (etac TF.induct 1);
by (ALLGOALS (ASM_SIMP_TAC TF_ss));
val TF_map_ident = result();

goal TF_Fn.thy
 "!!z A. z: tree_forest(A) ==> TF_map(h, TF_map(j,z)) = TF_map(%u.h(j(u)), z)";
by (etac TF.induct 1);
by (ALLGOALS (ASM_SIMP_TAC TF_ss));
val TF_map_compose = result();

(** theorems about TF_size **)

goal TF_Fn.thy
    "!!z A. z: tree_forest(A) ==> TF_size(TF_map(h,z)) = TF_size(z)";
by (etac TF.induct 1);
by (ALLGOALS (ASM_SIMP_TAC TF_ss));
val TF_size_TF_map = result();

goal TF_Fn.thy
    "!!z A. z: tree_forest(A) ==> TF_size(z) = length(TF_preorder(z))";
by (etac TF.induct 1);
by (ALLGOALS (ASM_SIMP_TAC (TF_ss addrews [length_app])));
val TF_size_length = result();

(** theorems about TF_preorder **)

goal TF_Fn.thy "!!z A. z: tree_forest(A) ==> \
\                      TF_preorder(TF_map(h,z)) = map(h, TF_preorder(z))";
by (etac TF.induct 1);
by (ALLGOALS (ASM_SIMP_TAC (TF_ss addrews [map_app_distrib])));
val TF_preorder_TF_map = result();
