(*  Title:      ZF/ex/tf.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Trees & forests, a mutually recursive type definition.
*)

Addsimps tree_forest.intrs;
AddTCs   tree_forest.intrs;

(** tree_forest(A) as the union of tree(A) and forest(A) **)

val [_, tree_def, forest_def] = tree_forest.defs;

Goalw [tree_def] "tree(A) <= tree_forest(A)";
by (rtac Part_subset 1);
qed "tree_subset_TF";

Goalw [forest_def] "forest(A) <= tree_forest(A)";
by (rtac Part_subset 1);
qed "forest_subset_TF";

Goal "tree(A) Un forest(A) = tree_forest(A)";
by (safe_tac (subset_cs addSIs [equalityI, tree_subset_TF, forest_subset_TF]));
by (fast_tac (claset() addSIs tree_forest.intrs addEs [tree_forest.elim]) 1);
qed "TF_equals_Un";

(** NOT useful, but interesting... **)

Goalw [tree_def, forest_def] 
    "tree_forest(A) = (A*forest(A)) + ({0} + tree(A)*forest(A))";
let open tree_forest;  
    val rew = rewrite_rule (con_defs @ tl defs) in  
by (fast_tac (claset() addSIs (map rew intrs RL [PartD1]) addEs [rew elim]) 1)
end;
qed "tree_forest_unfold";

val tree_forest_unfold' = rewrite_rule [tree_def, forest_def] 
                          tree_forest_unfold;

Goalw [tree_def, forest_def]
    "tree(A) = {Inl(x). x: A*forest(A)}";
by (rtac (Part_Inl RS subst) 1);
by (rtac (tree_forest_unfold' RS subst_context) 1);
qed "tree_unfold";

Goalw [tree_def, forest_def]
    "forest(A) = {Inr(x). x: {0} + tree(A)*forest(A)}";
by (rtac (Part_Inr RS subst) 1);
by (rtac (tree_forest_unfold' RS subst_context) 1);
qed "forest_unfold";


(** Type checking for recursor: Not needed; possibly interesting (??) **)

val major::prems = goal TF.thy
    "[| z: tree_forest(A);  \
\       !!x f r. [| x: A;  f: forest(A);  r: C(f)               \
\                 |] ==> b(x,f,r): C(Tcons(x,f));       \
\       c : C(Fnil);                                            \
\       !!t f r1 r2. [| t: tree(A);  f: forest(A);  r1: C(t); r2: C(f) \
\                     |] ==> d(t,f,r1,r2): C(Fcons(t,f))        \
\    |] ==> tree_forest_rec(b,c,d,z) : C(z)";
by (rtac (major RS tree_forest.induct) 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps prems)));
qed "TF_rec_type";

(*Mutually recursive version*)
val prems = goal TF.thy
    "[| !!x f r. [| x: A;  f: forest(A);  r: D(f)               \
\                 |] ==> b(x,f,r): C(Tcons(x,f));               \
\       c : D(Fnil);                                            \
\       !!t f r1 r2. [| t: tree(A);  f: forest(A);  r1: C(t); r2: D(f) \
\                     |] ==> d(t,f,r1,r2): D(Fcons(t,f))        \
\    |] ==> (ALL t:tree(A).    tree_forest_rec(b,c,d,t)  : C(t)) &       \
\           (ALL f: forest(A). tree_forest_rec(b,c,d,f) : D(f))";
by (rewtac Ball_def);
by (rtac tree_forest.mutual_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps prems)));
qed "tree_forest_rec_type";


(** list_of_TF and of_list **)

Goal "z: tree_forest(A) ==> list_of_TF(z) : list(tree(A))";
by (etac tree_forest.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "list_of_TF_type";

Goal "l: list(tree(A)) ==> of_list(l) : forest(A)";
by (etac list.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "of_list_type";


(** map **)

val prems = Goal
    "[| !!x. x: A ==> h(x): B |] ==> \
\      (ALL t:tree(A). map(h,t) : tree(B)) &  \
\      (ALL f: forest(A). map(h,f) : forest(B))";
by (rewtac Ball_def);
by (rtac tree_forest.mutual_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps prems)));
qed "map_type";


(** size **)

Goal "z: tree_forest(A) ==> size(z) : nat";
by (etac tree_forest.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "size_type";


(** preorder **)

Goal "z: tree_forest(A) ==> preorder(z) : list(A)";
by (etac tree_forest.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "preorder_type";


(** Term simplification **)

val treeI = tree_subset_TF RS subsetD
and forestI = forest_subset_TF RS subsetD;

val typechecks =
    [treeI, forestI,
     list_of_TF_type, map_type, size_type, preorder_type];

Addsimps typechecks;

(** theorems about list_of_TF and of_list **)

(*essentially the same as list induction*)
val major::prems = Goal
    "[| f: forest(A);   \
\       R(Fnil);        \
\       !!t f. [| t: tree(A);  f: forest(A);  R(f) |] ==> R(Fcons(t,f))  \
\    |] ==> R(f)";
by (rtac (major RS (tree_forest.mutual_induct RS conjunct2 RS spec RSN (2,rev_mp))) 1);
by (REPEAT (ares_tac (TrueI::prems) 1));
qed "forest_induct";

Goal "f: forest(A) ==> of_list(list_of_TF(f)) = f";
by (etac forest_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "forest_iso";

Goal "ts: list(tree(A)) ==> list_of_TF(of_list(ts)) = ts";
by (etac list.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "tree_list_iso";

(** theorems about map **)

Goal "z: tree_forest(A) ==> map(%u. u, z) = z";
by (etac tree_forest.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "map_ident";

Goal "z: tree_forest(A) ==> map(h, map(j,z)) = map(%u. h(j(u)), z)";
by (etac tree_forest.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "map_compose";

(** theorems about size **)

Goal "z: tree_forest(A) ==> size(map(h,z)) = size(z)";
by (etac tree_forest.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "size_map";

Goal "z: tree_forest(A) ==> size(z) = length(preorder(z))";
by (etac tree_forest.induct 1);
by (ALLGOALS   (*TYPECHECKING: why so explicit?*)
    (asm_simp_tac
     (simpset() addsimps [treeI RS preorder_type RS length_app])));
qed "size_length";

(** theorems about preorder **)

Goal "z: tree_forest(A) ==> preorder(TF.map(h,z)) = List.map(h, preorder(z))";
by (etac tree_forest.induct 1);
by (ALLGOALS  (*TYPECHECKING: why so explicit?*)
    (asm_simp_tac
     (simpset() addsimps [treeI RS preorder_type RS map_app_distrib])));
qed "preorder_map";
