(*  Title: 	ZF/ex/tf.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Trees & forests, a mutually recursive type definition.

Still needs

"TF_reflect == (%z. TF_rec(z, %x ts r. Tcons(x,r), 0, 
               %t ts r1 r2. TF_of_list(list_of_TF(r2) @ <r1,0>)))"
*)

open TF;

val [TconsI, FnilI, FconsI] = tree_forest.intrs;

(** tree_forest(A) as the union of tree(A) and forest(A) **)

goalw TF.thy (tl tree_forest.defs) "tree(A) <= tree_forest(A)";
by (rtac Part_subset 1);
val tree_subset_TF = result();

goalw TF.thy (tl tree_forest.defs) "forest(A) <= tree_forest(A)";
by (rtac Part_subset 1);
val forest_subset_TF = result();

goalw TF.thy (tl tree_forest.defs) "tree(A) Un forest(A) = tree_forest(A)";
by (rtac (tree_forest.dom_subset RS Part_sum_equality) 1);
val TF_equals_Un = result();

(** NOT useful, but interesting... **)

goalw TF.thy (tl tree_forest.defs) 
    "tree_forest(A) = (A*forest(A)) + ({0} + tree(A)*forest(A))";
let open tree_forest;  
    val rew = rewrite_rule (con_defs @ tl defs) in  
by (fast_tac (sum_cs addSIs (equalityI :: PartI :: (map rew intrs RL [PartD1]))
                     addEs [PartE, rew elim]) 1)
end;
val tree_forest_unfold = result();

val tree_forest_unfold' = rewrite_rule (tl tree_forest.defs) 
                          tree_forest_unfold;

goalw TF.thy (tl tree_forest.defs)
    "tree(A) = {Inl(x). x: A*forest(A)}";
by (rtac (Part_Inl RS subst) 1);
by (rtac (tree_forest_unfold' RS subst_context) 1);
val tree_unfold = result();

goalw TF.thy (tl tree_forest.defs)
    "forest(A) = {Inr(x). x: {0} + tree(A)*forest(A)}";
by (rtac (Part_Inr RS subst) 1);
by (rtac (tree_forest_unfold' RS subst_context) 1);
val forest_unfold = result();


(*** TF_rec -- by Vset recursion ***)

(** conversion rules **)

goal TF.thy "TF_rec(Tcons(a,f), b, c, d) = b(a, f, TF_rec(f,b,c,d))";
by (rtac (TF_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac tree_forest.con_defs);
by (simp_tac rank_ss 1);
val TF_rec_Tcons = result();

goal TF.thy "TF_rec(Fnil, b, c, d) = c";
by (rtac (TF_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac tree_forest.con_defs);
by (simp_tac rank_ss 1);
val TF_rec_Fnil = result();

goal TF.thy "TF_rec(Fcons(t,f), b, c, d) = \
\      d(t, f, TF_rec(t, b, c, d), TF_rec(f, b, c, d))";
by (rtac (TF_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac tree_forest.con_defs);
by (simp_tac rank_ss 1);
val TF_rec_Fcons = result();

(*list_ss includes list operations as well as arith_ss*)
val TF_rec_ss = list_ss addsimps
  [TF_rec_Tcons, TF_rec_Fnil, TF_rec_Fcons, TconsI, FnilI, FconsI];

(** Type checking **)

val major::prems = goal TF.thy
    "[| z: tree_forest(A);  \
\       !!x f r. [| x: A;  f: forest(A);  r: C(f) 		\
\                 |] ==> b(x,f,r): C(Tcons(x,f));     	\
\	c : C(Fnil);        					\
\       !!t f r1 r2. [| t: tree(A);  f: forest(A);  r1: C(t); r2: C(f) \
\                     |] ==> d(t,f,r1,r2): C(Fcons(t,f))    	\
\    |] ==> TF_rec(z,b,c,d) : C(z)";
by (rtac (major RS tree_forest.induct) 1);
by (ALLGOALS (asm_simp_tac (TF_rec_ss addsimps prems)));
val TF_rec_type = result();

(*Mutually recursive version*)
val prems = goal TF.thy
    "[| !!x f r. [| x: A;  f: forest(A);  r: D(f) 		\
\                 |] ==> b(x,f,r): C(Tcons(x,f));    	 	\
\	c : D(Fnil);        					\
\       !!t f r1 r2. [| t: tree(A);  f: forest(A);  r1: C(t); r2: D(f) \
\                     |] ==> d(t,f,r1,r2): D(Fcons(t,f))    	\
\    |] ==> (ALL t:tree(A).    TF_rec(t,b,c,d)  : C(t)) &  	\
\           (ALL f: forest(A). TF_rec(f,b,c,d) : D(f))";
by (rewtac Ball_def);
by (rtac tree_forest.mutual_induct 1);
by (ALLGOALS (asm_simp_tac (TF_rec_ss addsimps prems)));
val tree_forest_rec_type = result();


(** Versions for use with definitions **)

val [rew] = goal TF.thy
    "[| !!z. j(z)==TF_rec(z,b,c,d) |] ==> j(Tcons(a,f)) = b(a,f,j(f))";
by (rewtac rew);
by (rtac TF_rec_Tcons 1);
val def_TF_rec_Tcons = result();

val [rew] = goal TF.thy
    "[| !!z. j(z)==TF_rec(z,b,c,d) |] ==> j(Fnil) = c";
by (rewtac rew);
by (rtac TF_rec_Fnil 1);
val def_TF_rec_Fnil = result();

val [rew] = goal TF.thy
    "[| !!z. j(z)==TF_rec(z,b,c,d) |] ==> j(Fcons(t,f)) = d(t,f,j(t),j(f))";
by (rewtac rew);
by (rtac TF_rec_Fcons 1);
val def_TF_rec_Fcons = result();

fun TF_recs def = map standard 
    	([def] RL [def_TF_rec_Tcons, def_TF_rec_Fnil, def_TF_rec_Fcons]);


(** list_of_TF and TF_of_list **)

val [list_of_TF_Tcons, list_of_TF_Fnil, list_of_TF_Fcons] =
	TF_recs list_of_TF_def;

goalw TF.thy [list_of_TF_def]
    "!!z A. z: tree_forest(A) ==> list_of_TF(z) : list(tree(A))";
by (REPEAT (ares_tac ([TF_rec_type,TconsI] @ list_typechecks) 1));
val list_of_TF_type = result();

val [TF_of_list_Nil,TF_of_list_Cons] = list_recs TF_of_list_def;

goalw TF.thy [TF_of_list_def] 
    "!!l A. l: list(tree(A)) ==> TF_of_list(l) : forest(A)";
by (REPEAT (ares_tac [list_rec_type, FnilI, FconsI] 1));
val TF_of_list_type = result();


(** TF_map **)

val [TF_map_Tcons, TF_map_Fnil, TF_map_Fcons] = TF_recs TF_map_def;

val prems = goalw TF.thy [TF_map_def]
    "[| !!x. x: A ==> h(x): B |] ==> \
\      (ALL t:tree(A). TF_map(h,t) : tree(B)) &  \
\      (ALL f: forest(A). TF_map(h,f) : forest(B))";
by (REPEAT
    (ares_tac ([tree_forest_rec_type, TconsI, FnilI, FconsI] @ prems) 1));
val TF_map_type = result();


(** TF_size **)

val [TF_size_Tcons, TF_size_Fnil, TF_size_Fcons] = TF_recs TF_size_def;

goalw TF.thy [TF_size_def]
    "!!z A. z: tree_forest(A) ==> TF_size(z) : nat";
by (REPEAT (ares_tac [TF_rec_type, add_type, nat_0I, nat_succI] 1));
val TF_size_type = result();


(** TF_preorder **)

val [TF_preorder_Tcons, TF_preorder_Fnil, TF_preorder_Fcons] =
	TF_recs TF_preorder_def;

goalw TF.thy [TF_preorder_def]
    "!!z A. z: tree_forest(A) ==> TF_preorder(z) : list(A)";
by (REPEAT (ares_tac ([TF_rec_type, app_type] @ list.intrs) 1));
val TF_preorder_type = result();


(** Term simplification **)

val treeI = tree_subset_TF RS subsetD
and forestI = forest_subset_TF RS subsetD;

val TF_typechecks =
    [TconsI, FnilI, FconsI, treeI, forestI,
     list_of_TF_type, TF_map_type, TF_size_type, TF_preorder_type];

val TF_rewrites =
   [TF_rec_Tcons, TF_rec_Fnil, TF_rec_Fcons,
    list_of_TF_Tcons, list_of_TF_Fnil, list_of_TF_Fcons,
    TF_of_list_Nil,TF_of_list_Cons,
    TF_map_Tcons, TF_map_Fnil, TF_map_Fcons,
    TF_size_Tcons, TF_size_Fnil, TF_size_Fcons,
    TF_preorder_Tcons, TF_preorder_Fnil, TF_preorder_Fcons];

val TF_ss = list_ss addsimps TF_rewrites
                    setsolver type_auto_tac (list_typechecks@TF_typechecks);

(** theorems about list_of_TF and TF_of_list **)

(*essentially the same as list induction*)
val major::prems = goal TF.thy 
    "[| f: forest(A);  	\
\       R(Fnil);        \
\       !!t f. [| t: tree(A);  f: forest(A);  R(f) |] ==> R(Fcons(t,f))  \
\    |] ==> R(f)";
by (rtac (major RS (tree_forest.mutual_induct RS conjunct2 RS spec RSN (2,rev_mp))) 1);
by (REPEAT (ares_tac (TrueI::prems) 1));
val forest_induct = result();

goal TF.thy "!!f A. f: forest(A) ==> TF_of_list(list_of_TF(f)) = f";
by (etac forest_induct 1);
by (ALLGOALS (asm_simp_tac TF_ss));
val forest_iso = result();

goal TF.thy
    "!!ts. ts: list(tree(A)) ==> list_of_TF(TF_of_list(ts)) = ts";
by (etac list.induct 1);
by (ALLGOALS (asm_simp_tac TF_ss));
val tree_list_iso = result();

(** theorems about TF_map **)

goal TF.thy "!!z A. z: tree_forest(A) ==> TF_map(%u.u, z) = z";
by (etac tree_forest.induct 1);
by (ALLGOALS (asm_simp_tac TF_ss));
val TF_map_ident = result();

goal TF.thy
 "!!z A. z: tree_forest(A) ==> TF_map(h, TF_map(j,z)) = TF_map(%u.h(j(u)), z)";
by (etac tree_forest.induct 1);
by (ALLGOALS (asm_simp_tac TF_ss));
val TF_map_compose = result();

(** theorems about TF_size **)

goal TF.thy
    "!!z A. z: tree_forest(A) ==> TF_size(TF_map(h,z)) = TF_size(z)";
by (etac tree_forest.induct 1);
by (ALLGOALS (asm_simp_tac TF_ss));
val TF_size_TF_map = result();

goal TF.thy
    "!!z A. z: tree_forest(A) ==> TF_size(z) = length(TF_preorder(z))";
by (etac tree_forest.induct 1);
by (ALLGOALS (asm_simp_tac (TF_ss addsimps [length_app])));
val TF_size_length = result();

(** theorems about TF_preorder **)

goal TF.thy "!!z A. z: tree_forest(A) ==> \
\                      TF_preorder(TF_map(h,z)) = map(h, TF_preorder(z))";
by (etac tree_forest.induct 1);
by (ALLGOALS (asm_simp_tac (TF_ss addsimps [map_app_distrib])));
val TF_preorder_TF_map = result();
