(*  Title: 	ZF/ex/term.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Datatype definition of terms over an alphabet.
Illustrates the list functor (essentially the same type as in Trees & Forests)
*)

structure Term = Datatype_Fun
 (val thy = List.thy;
  val rec_specs = 
      [("term", "univ(A)",
	  [(["Apply"], "[i,i]=>i")])];
  val rec_styp = "i=>i";
  val ext = None
  val sintrs = ["[| a: A;  l: list(term(A)) |] ==> Apply(a,l) : term(A)"];
  val monos = [list_mono];
  val type_intrs = datatype_intrs;
  val type_elims = [make_elim (list_univ RS subsetD)]);

val [ApplyI] = Term.intrs;

(*Note that Apply is the identity function*)
goal Term.thy "term(A) = A * list(term(A))";
by (rtac (Term.unfold RS trans) 1);
bws Term.con_defs;
by (fast_tac (sum_cs addIs ([equalityI] @ datatype_intrs)
 	             addDs [Term.dom_subset RS subsetD]
 	             addEs [A_into_univ, list_into_univ]) 1);
val term_unfold = result();

(*Induction on term(A) followed by induction on List *)
val major::prems = goal Term.thy
    "[| t: term(A);  \
\       !!x.      [| x: A |] ==> P(Apply(x,Nil));  \
\       !!x z zs. [| x: A;  z: term(A);  zs: list(term(A));  P(Apply(x,zs))  \
\                 |] ==> P(Apply(x, Cons(z,zs)))  \
\    |] ==> P(t)";
by (rtac (major RS Term.induct) 1);
by (etac List.induct 1);
by (etac CollectE 2);
by (REPEAT (ares_tac (prems@[list_CollectD]) 1));
val term_induct2 = result();

(*Induction on term(A) to prove an equation*)
val major::prems = goal (merge_theories(Term.thy,ListFn.thy))
    "[| t: term(A);  \
\       !!x zs. [| x: A;  zs: list(term(A));  map(f,zs) = map(g,zs) |] ==> \
\               f(Apply(x,zs)) = g(Apply(x,zs))  \
\    |] ==> f(t)=g(t)";
by (rtac (major RS Term.induct) 1);
by (resolve_tac prems 1);
by (REPEAT (eresolve_tac [asm_rl, map_list_Collect, list_CollectD] 1));
val term_induct_eqn = result();

(**  Lemmas to justify using "term" in other recursive type definitions **)

goalw Term.thy Term.defs "!!A B. A<=B ==> term(A) <= term(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac Term.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::basic_monos) 1));
val term_mono = result();

(*Easily provable by induction also*)
goalw Term.thy (Term.defs@Term.con_defs) "term(univ(A)) <= univ(A)";
by (rtac lfp_lowerbound 1);
by (rtac (A_subset_univ RS univ_mono) 2);
by (safe_tac ZF_cs);
by (REPEAT (ares_tac [Pair_in_univ, list_univ RS subsetD] 1));
val term_univ = result();

val term_subset_univ = 
    term_mono RS (term_univ RSN (2,subset_trans)) |> standard;

goal Term.thy "!!t A B. [| t: term(A);  A <= univ(B) |] ==> t: univ(B)";
by (REPEAT (ares_tac [term_subset_univ RS subsetD] 1));
val term_into_univ = result();
