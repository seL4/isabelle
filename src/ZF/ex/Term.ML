(*  Title:      ZF/ex/Term.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype definition of terms over an alphabet.
Illustrates the list functor (essentially the same type as in Trees & Forests)
*)

open Term;

goal Term.thy "term(A) = A * list(term(A))";
let open term;  val rew = rewrite_rule con_defs in  
by (fast_tac (!claset addSIs (equalityI :: map rew intrs)
                     addEs [rew elim]) 1)
end;
qed "term_unfold";

(*Induction on term(A) followed by induction on List *)
val major::prems = goal Term.thy
    "[| t: term(A);  \
\       !!x.      [| x: A |] ==> P(Apply(x,Nil));  \
\       !!x z zs. [| x: A;  z: term(A);  zs: list(term(A));  P(Apply(x,zs))  \
\                 |] ==> P(Apply(x, Cons(z,zs)))  \
\    |] ==> P(t)";
by (rtac (major RS term.induct) 1);
by (etac list.induct 1);
by (etac CollectE 2);
by (REPEAT (ares_tac (prems@[list_CollectD]) 1));
qed "term_induct2";

(*Induction on term(A) to prove an equation*)
val major::prems = goal Term.thy
    "[| t: term(A);  \
\       !!x zs. [| x: A;  zs: list(term(A));  map(f,zs) = map(g,zs) |] ==> \
\               f(Apply(x,zs)) = g(Apply(x,zs))  \
\    |] ==> f(t)=g(t)";
by (rtac (major RS term.induct) 1);
by (resolve_tac prems 1);
by (REPEAT (eresolve_tac [asm_rl, map_list_Collect, list_CollectD] 1));
qed "term_induct_eqn";

(**  Lemmas to justify using "term" in other recursive type definitions **)

goalw Term.thy term.defs "!!A B. A<=B ==> term(A) <= term(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac term.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::basic_monos) 1));
qed "term_mono";

(*Easily provable by induction also*)
goalw Term.thy (term.defs@term.con_defs) "term(univ(A)) <= univ(A)";
by (rtac lfp_lowerbound 1);
by (rtac (A_subset_univ RS univ_mono) 2);
by (safe_tac (!claset));
by (REPEAT (ares_tac [Pair_in_univ, list_univ RS subsetD] 1));
qed "term_univ";

val term_subset_univ = 
    term_mono RS (term_univ RSN (2,subset_trans)) |> standard;

goal Term.thy "!!t A B. [| t: term(A);  A <= univ(B) |] ==> t: univ(B)";
by (REPEAT (ares_tac [term_subset_univ RS subsetD] 1));
qed "term_into_univ";


(*** term_rec -- by Vset recursion ***)

(*Lemma: map works correctly on the underlying list of terms*)
val [major,ordi] = goal list.thy
    "[| l: list(A);  Ord(i) |] ==>  \
\    rank(l)<i --> map(%z. (lam x:Vset(i).h(x)) ` z, l) = map(h,l)";
by (rtac (major RS list.induct) 1);
by (Simp_tac 1);
by (rtac impI 1);
by (forward_tac [rank_Cons1 RS lt_trans] 1);
by (dtac (rank_Cons2 RS lt_trans) 1);
by (asm_simp_tac (!simpset addsimps [ordi, VsetI]) 1);
qed "map_lemma";

(*Typing premise is necessary to invoke map_lemma*)
val [prem] = goal Term.thy
    "ts: list(A) ==> \
\    term_rec(Apply(a,ts), d) = d(a, ts, map (%z. term_rec(z,d), ts))";
by (rtac (term_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac term.con_defs);
by (simp_tac (!simpset addsimps [Ord_rank, rank_pair2, prem RS map_lemma]) 1);;
qed "term_rec";

(*Slightly odd typing condition on r in the second premise!*)
val major::prems = goal Term.thy
    "[| t: term(A);                                     \
\       !!x zs r. [| x: A;  zs: list(term(A));          \
\                    r: list(UN t:term(A). C(t)) |]     \
\                 ==> d(x, zs, r): C(Apply(x,zs))       \
\    |] ==> term_rec(t,d) : C(t)";
by (rtac (major RS term.induct) 1);
by (forward_tac [list_CollectD] 1);
by (stac term_rec 1);
by (REPEAT (ares_tac prems 1));
by (etac list.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [term_rec])));
by (etac CollectE 1);
by (REPEAT (ares_tac [list.Cons_I, UN_I] 1));
qed "term_rec_type";

val [rew,tslist] = goal Term.thy
    "[| !!t. j(t)==term_rec(t,d);  ts: list(A) |] ==> \
\    j(Apply(a,ts)) = d(a, ts, map(%Z.j(Z), ts))";
by (rewtac rew);
by (rtac (tslist RS term_rec) 1);
qed "def_term_rec";

val prems = goal Term.thy
    "[| t: term(A);                                          \
\       !!x zs r. [| x: A;  zs: list(term(A));  r: list(C) |]  \
\                 ==> d(x, zs, r): C                 \
\    |] ==> term_rec(t,d) : C";
by (REPEAT (ares_tac (term_rec_type::prems) 1));
by (etac (subset_refl RS UN_least RS list_mono RS subsetD) 1);
qed "term_rec_simple_type";


(** term_map **)

bind_thm ("term_map", (term_map_def RS def_term_rec));

val prems = goalw Term.thy [term_map_def]
    "[| t: term(A);  !!x. x: A ==> f(x): B |] ==> term_map(f,t) : term(B)";
by (REPEAT (ares_tac ([term_rec_simple_type, term.Apply_I] @ prems) 1));
qed "term_map_type";

val [major] = goal Term.thy
    "t: term(A) ==> term_map(f,t) : term({f(u). u:A})";
by (rtac (major RS term_map_type) 1);
by (etac RepFunI 1);
qed "term_map_type2";


(** term_size **)

bind_thm ("term_size", (term_size_def RS def_term_rec));

goalw Term.thy [term_size_def] "!!t A. t: term(A) ==> term_size(t) : nat";
by (REPEAT (ares_tac [term_rec_simple_type, list_add_type, nat_succI] 1));
qed "term_size_type";


(** reflect **)

bind_thm ("reflect", (reflect_def RS def_term_rec));

goalw Term.thy [reflect_def] "!!t A. t: term(A) ==> reflect(t) : term(A)";
by (REPEAT (ares_tac [term_rec_simple_type, rev_type, term.Apply_I] 1));
qed "reflect_type";

(** preorder **)

bind_thm ("preorder", (preorder_def RS def_term_rec));

goalw Term.thy [preorder_def]
    "!!t A. t: term(A) ==> preorder(t) : list(A)";
by (REPEAT (ares_tac [term_rec_simple_type, list.Cons_I, flat_type] 1));
qed "preorder_type";


(** Term simplification **)

val term_typechecks =
    [term.Apply_I, term_map_type, term_map_type2, term_size_type, 
     reflect_type, preorder_type];

(*map_type2 and term_map_type2 instantiate variables*)
simpset := !simpset
      addsimps [term_rec, term_map, term_size, reflect, preorder]
      setsolver type_auto_tac (list_typechecks@term_typechecks);


(** theorems about term_map **)

goal Term.thy "!!t A. t: term(A) ==> term_map(%u.u, t) = t";
by (etac term_induct_eqn 1);
by (asm_simp_tac (!simpset addsimps [map_ident]) 1);
qed "term_map_ident";

goal Term.thy
  "!!t A. t: term(A) ==> term_map(f, term_map(g,t)) = term_map(%u.f(g(u)), t)";
by (etac term_induct_eqn 1);
by (asm_simp_tac (!simpset addsimps [map_compose]) 1);
qed "term_map_compose";

goal Term.thy
    "!!t A. t: term(A) ==> term_map(f, reflect(t)) = reflect(term_map(f,t))";
by (etac term_induct_eqn 1);
by (asm_simp_tac (!simpset addsimps [rev_map_distrib RS sym, map_compose]) 1);
qed "term_map_reflect";


(** theorems about term_size **)

goal Term.thy
    "!!t A. t: term(A) ==> term_size(term_map(f,t)) = term_size(t)";
by (etac term_induct_eqn 1);
by (asm_simp_tac (!simpset addsimps [map_compose]) 1);
qed "term_size_term_map";

goal Term.thy "!!t A. t: term(A) ==> term_size(reflect(t)) = term_size(t)";
by (etac term_induct_eqn 1);
by (asm_simp_tac (!simpset addsimps [rev_map_distrib RS sym, map_compose,
                                    list_add_rev]) 1);
qed "term_size_reflect";

goal Term.thy "!!t A. t: term(A) ==> term_size(t) = length(preorder(t))";
by (etac term_induct_eqn 1);
by (asm_simp_tac (!simpset addsimps [length_flat, map_compose]) 1);
qed "term_size_length";


(** theorems about reflect **)

goal Term.thy "!!t A. t: term(A) ==> reflect(reflect(t)) = t";
by (etac term_induct_eqn 1);
by (asm_simp_tac (!simpset addsimps [rev_map_distrib, map_compose,
                                    map_ident, rev_rev_ident]) 1);
qed "reflect_reflect_ident";


(** theorems about preorder **)

goal Term.thy
    "!!t A. t: term(A) ==> preorder(term_map(f,t)) = map(f, preorder(t))";
by (etac term_induct_eqn 1);
by (asm_simp_tac (!simpset addsimps [map_compose, map_flat]) 1);
qed "preorder_term_map";

(** preorder(reflect(t)) = rev(postorder(t)) **)

writeln"Reached end of file.";
