(*  Title: 	ZF/ex/term
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Terms over a given alphabet -- function applications; illustrates list functor
  (essentially the same type as in Trees & Forests)
*)

writeln"File ZF/ex/term-fn.";

open TermFn;

(*** term_rec -- by Vset recursion ***)

(*Lemma: map works correctly on the underlying list of terms*)
val [major,ordi] = goal ListFn.thy
    "[| l: list(A);  Ord(i) |] ==>  \
\    rank(l)<i --> map(%z. (lam x:Vset(i).h(x)) ` z, l) = map(h,l)";
by (rtac (major RS List.induct) 1);
by (simp_tac list_ss 1);
by (rtac impI 1);
by (forward_tac [rank_Cons1 RS lt_trans] 1);
by (dtac (rank_Cons2 RS lt_trans) 1);
by (asm_simp_tac (list_ss addsimps [ordi, VsetI]) 1);
val map_lemma = result();

(*Typing premise is necessary to invoke map_lemma*)
val [prem] = goal TermFn.thy
    "ts: list(A) ==> \
\    term_rec(Apply(a,ts), d) = d(a, ts, map (%z. term_rec(z,d), ts))";
by (rtac (term_rec_def RS def_Vrec RS trans) 1);
by (rewrite_goals_tac Term.con_defs);
val term_rec_ss = ZF_ss addsimps [Ord_rank, rank_pair2, prem RS map_lemma];
by (simp_tac term_rec_ss 1);
val term_rec = result();

(*Slightly odd typing condition on r in the second premise!*)
val major::prems = goal TermFn.thy
    "[| t: term(A);					\
\       !!x zs r. [| x: A;  zs: list(term(A)); 		\
\                    r: list(UN t:term(A). C(t)) |]	\
\                 ==> d(x, zs, r): C(Apply(x,zs))  	\
\    |] ==> term_rec(t,d) : C(t)";
by (rtac (major RS Term.induct) 1);
by (forward_tac [list_CollectD] 1);
by (rtac (term_rec RS ssubst) 1);
by (REPEAT (ares_tac prems 1));
by (etac List.induct 1);
by (ALLGOALS (asm_simp_tac (list_ss addsimps [term_rec])));
by (etac CollectE 1);
by (REPEAT (ares_tac [ConsI, UN_I] 1));
val term_rec_type = result();

val [rew,tslist] = goal TermFn.thy
    "[| !!t. j(t)==term_rec(t,d);  ts: list(A) |] ==> \
\    j(Apply(a,ts)) = d(a, ts, map(%Z.j(Z), ts))";
by (rewtac rew);
by (rtac (tslist RS term_rec) 1);
val def_term_rec = result();

val prems = goal TermFn.thy
    "[| t: term(A);					     \
\       !!x zs r. [| x: A;  zs: list(term(A));  r: list(C) |]  \
\                 ==> d(x, zs, r): C  		     \
\    |] ==> term_rec(t,d) : C";
by (REPEAT (ares_tac (term_rec_type::prems) 1));
by (etac (subset_refl RS UN_least RS list_mono RS subsetD) 1);
val term_rec_simple_type = result();


(** term_map **)

val term_map = standard (term_map_def RS def_term_rec);

val prems = goalw TermFn.thy [term_map_def]
    "[| t: term(A);  !!x. x: A ==> f(x): B |] ==> term_map(f,t) : term(B)";
by (REPEAT (ares_tac ([term_rec_simple_type, ApplyI] @ prems) 1));
val term_map_type = result();

val [major] = goal TermFn.thy
    "t: term(A) ==> term_map(f,t) : term({f(u). u:A})";
by (rtac (major RS term_map_type) 1);
by (etac RepFunI 1);
val term_map_type2 = result();


(** term_size **)

val term_size = standard (term_size_def RS def_term_rec);

goalw TermFn.thy [term_size_def] "!!t A. t: term(A) ==> term_size(t) : nat";
by (REPEAT (ares_tac [term_rec_simple_type, list_add_type, nat_succI] 1));
val term_size_type = result();


(** reflect **)

val reflect = standard (reflect_def RS def_term_rec);

goalw TermFn.thy [reflect_def] "!!t A. t: term(A) ==> reflect(t) : term(A)";
by (REPEAT (ares_tac [term_rec_simple_type, rev_type, ApplyI] 1));
val reflect_type = result();

(** preorder **)

val preorder = standard (preorder_def RS def_term_rec);

goalw TermFn.thy [preorder_def]
    "!!t A. t: term(A) ==> preorder(t) : list(A)";
by (REPEAT (ares_tac [term_rec_simple_type, ConsI, flat_type] 1));
val preorder_type = result();


(** Term simplification **)

val term_typechecks =
    [ApplyI, term_map_type, term_map_type2, term_size_type, reflect_type, 
     preorder_type];

(*map_type2 and term_map_type2 instantiate variables*)
val term_ss = list_ss 
      addsimps [term_rec, term_map, term_size, reflect, preorder]
      setsolver type_auto_tac (list_typechecks@term_typechecks);


(** theorems about term_map **)

goal TermFn.thy "!!t A. t: term(A) ==> term_map(%u.u, t) = t";
by (etac term_induct_eqn 1);
by (asm_simp_tac (term_ss addsimps [map_ident]) 1);
val term_map_ident = result();

goal TermFn.thy
  "!!t A. t: term(A) ==> term_map(f, term_map(g,t)) = term_map(%u.f(g(u)), t)";
by (etac term_induct_eqn 1);
by (asm_simp_tac (term_ss addsimps [map_compose]) 1);
val term_map_compose = result();

goal TermFn.thy
    "!!t A. t: term(A) ==> term_map(f, reflect(t)) = reflect(term_map(f,t))";
by (etac term_induct_eqn 1);
by (asm_simp_tac (term_ss addsimps [rev_map_distrib RS sym, map_compose]) 1);
val term_map_reflect = result();


(** theorems about term_size **)

goal TermFn.thy
    "!!t A. t: term(A) ==> term_size(term_map(f,t)) = term_size(t)";
by (etac term_induct_eqn 1);
by (asm_simp_tac (term_ss addsimps [map_compose]) 1);
val term_size_term_map = result();

goal TermFn.thy "!!t A. t: term(A) ==> term_size(reflect(t)) = term_size(t)";
by (etac term_induct_eqn 1);
by (asm_simp_tac (term_ss addsimps [rev_map_distrib RS sym, map_compose,
				    list_add_rev]) 1);
val term_size_reflect = result();

goal TermFn.thy "!!t A. t: term(A) ==> term_size(t) = length(preorder(t))";
by (etac term_induct_eqn 1);
by (asm_simp_tac (term_ss addsimps [length_flat, map_compose]) 1);
val term_size_length = result();


(** theorems about reflect **)

goal TermFn.thy "!!t A. t: term(A) ==> reflect(reflect(t)) = t";
by (etac term_induct_eqn 1);
by (asm_simp_tac (term_ss addsimps [rev_map_distrib, map_compose,
				    map_ident, rev_rev_ident]) 1);
val reflect_reflect_ident = result();


(** theorems about preorder **)

goal TermFn.thy
    "!!t A. t: term(A) ==> preorder(term_map(f,t)) = map(f, preorder(t))";
by (etac term_induct_eqn 1);
by (asm_simp_tac (term_ss addsimps [map_compose, map_flat]) 1);
val preorder_term_map = result();

(** preorder(reflect(t)) = rev(postorder(t)) **)

writeln"Reached end of file.";
