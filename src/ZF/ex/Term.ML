(*  Title:      ZF/ex/Term.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype definition of terms over an alphabet.
Illustrates the list functor (essentially the same type as in Trees & Forests)
*)

AddTCs [term.Apply_I];

Goal "term(A) = A * list(term(A))";
let open term;  val rew = rewrite_rule con_defs in  
by (fast_tac (claset() addSIs (map rew intrs) addEs [rew elim]) 1)
end;
qed "term_unfold";

(*Induction on term(A) followed by induction on List *)
val major::prems = Goal
    "[| t \\<in> term(A);  \
\       !!x.      [| x \\<in> A |] ==> P(Apply(x,Nil));  \
\       !!x z zs. [| x \\<in> A;  z \\<in> term(A);  zs: list(term(A));  P(Apply(x,zs))  \
\                 |] ==> P(Apply(x, Cons(z,zs)))  \
\    |] ==> P(t)";
by (rtac (major RS term.induct) 1);
by (etac list.induct 1);
by (etac CollectE 2);
by (REPEAT (ares_tac (prems@[list_CollectD]) 1));
qed "term_induct2";

(*Induction on term(A) to prove an equation*)
val major::prems = Goal
    "[| t \\<in> term(A);  \
\       !!x zs. [| x \\<in> A;  zs: list(term(A));  map(f,zs) = map(g,zs) |] ==> \
\               f(Apply(x,zs)) = g(Apply(x,zs))  \
\    |] ==> f(t)=g(t)";
by (rtac (major RS term.induct) 1);
by (resolve_tac prems 1);
by (REPEAT (eresolve_tac [asm_rl, map_list_Collect, list_CollectD] 1));
qed "term_induct_eqn";

(**  Lemmas to justify using "term" in other recursive type definitions **)

Goalw term.defs "A \\<subseteq> B ==> term(A) \\<subseteq> term(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac term.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::basic_monos) 1));
qed "term_mono";

(*Easily provable by induction also*)
Goalw (term.defs@term.con_defs) "term(univ(A)) \\<subseteq> univ(A)";
by (rtac lfp_lowerbound 1);
by (rtac (A_subset_univ RS univ_mono) 2);
by Safe_tac;
by (REPEAT (ares_tac [Pair_in_univ, list_univ RS subsetD] 1));
qed "term_univ";

val term_subset_univ = 
    term_mono RS (term_univ RSN (2,subset_trans)) |> standard;

Goal "[| t \\<in> term(A);  A \\<subseteq> univ(B) |] ==> t \\<in> univ(B)";
by (REPEAT (ares_tac [term_subset_univ RS subsetD] 1));
qed "term_into_univ";


(*** term_rec -- by Vset recursion ***)

(*Lemma: map works correctly on the underlying list of terms*)
Goal "[| l \\<in> list(A);  Ord(i) |] ==>  \
\     rank(l)<i --> map(%z. (\\<lambda>x \\<in> Vset(i).h(x)) ` z, l) = map(h,l)";
by (etac list.induct 1);
by (Simp_tac 1);
by (rtac impI 1);
by (subgoal_tac "rank(a)<i & rank(l) < i" 1);
by (asm_simp_tac (simpset() addsimps [rank_of_Ord]) 1);
by (full_simp_tac (simpset() addsimps list.con_defs) 1);
by (blast_tac (claset() addDs (rank_rls RL [lt_trans])) 1);
qed "map_lemma";

(*Typing premise is necessary to invoke map_lemma*)
Goal "ts \\<in> list(A) ==> \
\     term_rec(Apply(a,ts), d) = d(a, ts, map (%z. term_rec(z,d), ts))";
by (rtac (term_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac term.con_defs);
by (asm_simp_tac (simpset() addsimps [rank_pair2, map_lemma]) 1);;
qed "term_rec";

(*Slightly odd typing condition on r in the second premise!*)
val major::prems = Goal
    "[| t \\<in> term(A);                                     \
\       !!x zs r. [| x \\<in> A;  zs: list(term(A));          \
\                    r \\<in> list(\\<Union>t \\<in> term(A). C(t)) |]     \
\                 ==> d(x, zs, r): C(Apply(x,zs))       \
\    |] ==> term_rec(t,d) \\<in> C(t)";
by (rtac (major RS term.induct) 1);
by (ftac list_CollectD 1);
by (stac term_rec 1);
by (REPEAT (ares_tac prems 1));
by (etac list.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [term_rec])));
by Auto_tac;
qed "term_rec_type";

val [rew,tslist] = Goal
    "[| !!t. j(t)==term_rec(t,d);  ts: list(A) |] ==> \
\    j(Apply(a,ts)) = d(a, ts, map(%Z. j(Z), ts))";
by (rewtac rew);
by (rtac (tslist RS term_rec) 1);
qed "def_term_rec";

val prems = Goal
    "[| t \\<in> term(A);                                          \
\       !!x zs r. [| x \\<in> A;  zs: list(term(A));  r \\<in> list(C) |]  \
\                 ==> d(x, zs, r): C                 \
\    |] ==> term_rec(t,d) \\<in> C";
by (REPEAT (ares_tac (term_rec_type::prems) 1));
by (etac (subset_refl RS UN_least RS list_mono RS subsetD) 1);
qed "term_rec_simple_type";

AddTCs [term_rec_simple_type];

(** term_map **)

bind_thm ("term_map", term_map_def RS def_term_rec);

val prems = Goalw [term_map_def]
    "[| t \\<in> term(A);  !!x. x \\<in> A ==> f(x): B |] ==> term_map(f,t) \\<in> term(B)";
by (REPEAT (ares_tac ([term_rec_simple_type, term.Apply_I] @ prems) 1));
qed "term_map_type";

Goal "t \\<in> term(A) ==> term_map(f,t) \\<in> term({f(u). u \\<in> A})";
by (etac term_map_type 1);
by (etac RepFunI 1);
qed "term_map_type2";


(** term_size **)

bind_thm ("term_size", term_size_def RS def_term_rec);

Goalw [term_size_def] "t \\<in> term(A) ==> term_size(t) \\<in> nat";
by Auto_tac;
qed "term_size_type";


(** reflect **)

bind_thm ("reflect", reflect_def RS def_term_rec);

Goalw [reflect_def] "t \\<in> term(A) ==> reflect(t) \\<in> term(A)";
by Auto_tac;
qed "reflect_type";

(** preorder **)

bind_thm ("preorder", preorder_def RS def_term_rec);

Goalw [preorder_def] "t \\<in> term(A) ==> preorder(t) \\<in> list(A)";
by Auto_tac;
qed "preorder_type";

(** postorder **)

bind_thm ("postorder", postorder_def RS def_term_rec);

Goalw [postorder_def] "t \\<in> term(A) ==> postorder(t) \\<in> list(A)";
by Auto_tac;
qed "postorder_type";


(** Term simplification **)

AddTCs [term_map_type, term_map_type2, term_size_type, 
	reflect_type, preorder_type, postorder_type];

(*map_type2 and term_map_type2 instantiate variables*)
Addsimps [term_rec, term_map, term_size, reflect, preorder, postorder];


(** theorems about term_map **)

Addsimps [thm "List.map_compose"];  (*there is also TF.map_compose*)

Goal "t \\<in> term(A) ==> term_map(%u. u, t) = t";
by (etac term_induct_eqn 1);
by (Asm_simp_tac 1);
qed "term_map_ident";

Goal "t \\<in> term(A) ==> term_map(f, term_map(g,t)) = term_map(%u. f(g(u)), t)";
by (etac term_induct_eqn 1);
by (Asm_simp_tac 1);
qed "term_map_compose";

Goal "t \\<in> term(A) ==> term_map(f, reflect(t)) = reflect(term_map(f,t))";
by (etac term_induct_eqn 1);
by (asm_simp_tac (simpset() addsimps [rev_map_distrib RS sym]) 1);
qed "term_map_reflect";


(** theorems about term_size **)

Goal "t \\<in> term(A) ==> term_size(term_map(f,t)) = term_size(t)";
by (etac term_induct_eqn 1);
by (Asm_simp_tac 1);
qed "term_size_term_map";

Goal "t \\<in> term(A) ==> term_size(reflect(t)) = term_size(t)";
by (etac term_induct_eqn 1);
by (asm_simp_tac(simpset() addsimps [rev_map_distrib RS sym, list_add_rev]) 1);
qed "term_size_reflect";

Goal "t \\<in> term(A) ==> term_size(t) = length(preorder(t))";
by (etac term_induct_eqn 1);
by (asm_simp_tac (simpset() addsimps [length_flat]) 1);
qed "term_size_length";


(** theorems about reflect **)

Goal "t \\<in> term(A) ==> reflect(reflect(t)) = t";
by (etac term_induct_eqn 1);
by (asm_simp_tac (simpset() addsimps [rev_map_distrib]) 1);
qed "reflect_reflect_ident";


(** theorems about preorder **)

Goal "t \\<in> term(A) ==> preorder(term_map(f,t)) = map(f, preorder(t))";
by (etac term_induct_eqn 1);
by (asm_simp_tac (simpset() addsimps [map_flat]) 1);
qed "preorder_term_map";

Goal "t \\<in> term(A) ==> preorder(reflect(t)) = rev(postorder(t))";
by (etac term_induct_eqn 1);
by (asm_simp_tac(simpset() addsimps [rev_app_distrib, rev_flat, 
				     rev_map_distrib RS sym]) 1);
qed "preorder_reflect_eq_rev_postorder";


writeln"Reached end of file.";
