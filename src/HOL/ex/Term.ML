(*  Title:      HOL/ex/Term
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Terms over a given alphabet -- function applications; illustrates list functor
  (essentially the same type as in Trees & Forests)
*)

open Term;

(*** Monotonicity and unfolding of the function ***)

goal Term.thy "term(A) = A <*> list(term(A))";
by (fast_tac (univ_cs addSIs (equalityI :: term.intrs)
                      addEs [term.elim]) 1);
qed "term_unfold";

(*This justifies using term in other recursive type definitions*)
goalw Term.thy term.defs "!!A B. A<=B ==> term(A) <= term(B)";
by (REPEAT (ares_tac ([lfp_mono, list_mono] @ basic_monos) 1));
qed "term_mono";

(** Type checking -- term creates well-founded sets **)

goalw Term.thy term.defs "term(sexp) <= sexp";
by (rtac lfp_lowerbound 1);
by (fast_tac (univ_cs addIs [sexp.SconsI, list_sexp RS subsetD]) 1);
qed "term_sexp";

(* A <= sexp ==> term(A) <= sexp *)
bind_thm ("term_subset_sexp", ([term_mono, term_sexp] MRS subset_trans));


(** Elimination -- structural induction on the set term(A) **)

(*Induction for the set term(A) *)
val [major,minor] = goal Term.thy 
    "[| M: term(A);  \
\       !!x zs. [| x: A;  zs: list(term(A));  zs: list({x.R(x)}) \
\               |] ==> R(x$zs)  \
\    |] ==> R(M)";
by (rtac (major RS term.induct) 1);
by (REPEAT (eresolve_tac ([minor] @
                ([Int_lower1,Int_lower2] RL [list_mono RS subsetD])) 1));
(*Proof could also use  mono_Int RS subsetD RS IntE *)
qed "Term_induct";

(*Induction on term(A) followed by induction on list *)
val major::prems = goal Term.thy
    "[| M: term(A);  \
\       !!x.      [| x: A |] ==> R(x$NIL);  \
\       !!x z zs. [| x: A;  z: term(A);  zs: list(term(A));  R(x$zs)  \
\                 |] ==> R(x $ CONS z zs)  \
\    |] ==> R(M)";
by (rtac (major RS Term_induct) 1);
by (etac list.induct 1);
by (REPEAT (ares_tac prems 1));
qed "Term_induct2";

(*** Structural Induction on the abstract type 'a term ***)

val Rep_term_in_sexp =
    Rep_term RS (range_Leaf_subset_sexp RS term_subset_sexp RS subsetD);

(*Induction for the abstract type 'a term*)
val prems = goalw Term.thy [App_def,Rep_Tlist_def,Abs_Tlist_def]
    "[| !!x ts. list_all R ts ==> R(App x ts)  \
\    |] ==> R(t)";
by (rtac (Rep_term_inverse RS subst) 1);   (*types force good instantiation*)
by (res_inst_tac [("P","Rep_term(t) : sexp")] conjunct2 1);
by (rtac (Rep_term RS Term_induct) 1);
by (REPEAT (ares_tac [conjI, sexp.SconsI, term_subset_sexp RS 
    list_subset_sexp, range_Leaf_subset_sexp] 1
     ORELSE etac rev_subsetD 1));
by (eres_inst_tac [("A1","term(?u)"), ("f1","Rep_term"), ("g1","Abs_term")]
        (Abs_map_inverse RS subst) 1);
by (rtac (range_Leaf_subset_sexp RS term_subset_sexp) 1);
by (etac Abs_term_inverse 1);
by (etac rangeE 1);
by (hyp_subst_tac 1);
by (resolve_tac prems 1);
by (etac list.induct 1);
by (etac CollectE 2);
by (stac Abs_map_CONS 2);
by (etac conjunct1 2);
by (etac rev_subsetD 2);
by (rtac list_subset_sexp 2);
by (fast_tac set_cs 2);
by (ALLGOALS Asm_simp_tac);
qed "term_induct";

(*Induction for the abstract type 'a term*)
val prems = goal Term.thy 
    "[| !!x. R(App x Nil);  \
\       !!x t ts. R(App x ts) ==> R(App x (t#ts))  \
\    |] ==> R(t)";
by (rtac term_induct 1);  (*types force good instantiation*)
by (etac rev_mp 1);
by (rtac list_induct2 1);  (*types force good instantiation*)
by (ALLGOALS (asm_simp_tac (!simpset addsimps prems)));
qed "term_induct2";

(*Perform induction on xs. *)
fun term_ind2_tac a i = 
    EVERY [res_inst_tac [("t",a)] term_induct2 i,
           rename_last_tac a ["1","s"] (i+1)];



(*** Term_rec -- by wf recursion on pred_sexp ***)

val Term_rec_unfold =
    wf_pred_sexp RS wf_trancl RS (Term_rec_def RS def_wfrec);

(** conversion rules **)

val [prem] = goal Term.thy
    "N: list(term(A)) ==>  \
\    !M. (N,M): pred_sexp^+ --> \
\        Abs_map (cut h (pred_sexp^+) M) N = \
\        Abs_map h N";
by (rtac (prem RS list.induct) 1);
by (Simp_tac 1);
by (strip_tac 1);
by (etac (pred_sexp_CONS_D RS conjE) 1);
by (asm_simp_tac (!simpset addsimps [trancl_pred_sexpD1]) 1);
qed "Abs_map_lemma";

val [prem1,prem2,A_subset_sexp] = goal Term.thy
    "[| M: sexp;  N: list(term(A));  A<=sexp |] ==> \
\    Term_rec (M$N) d = d M N (Abs_map (%Z. Term_rec Z d) N)";
by (rtac (Term_rec_unfold RS trans) 1);
by (simp_tac (HOL_ss addsimps
      [Split,
       prem2 RS Abs_map_lemma RS spec RS mp, pred_sexpI2 RS r_into_trancl,
       prem1, prem2 RS rev_subsetD, list_subset_sexp,
       term_subset_sexp, A_subset_sexp]) 1);
qed "Term_rec";

(*** term_rec -- by Term_rec ***)

local
  val Rep_map_type1 = read_instantiate_sg (sign_of Term.thy)
                        [("f","Rep_term")] Rep_map_type;
  val Rep_Tlist = Rep_term RS Rep_map_type1;
  val Rep_Term_rec = range_Leaf_subset_sexp RSN (2,Rep_Tlist RSN(2,Term_rec));

  (*Now avoids conditional rewriting with the premise N: list(term(A)),
    since A will be uninstantiated and will cause rewriting to fail. *)
  val term_rec_ss = HOL_ss
      addsimps [Rep_Tlist RS (rangeI RS term.APP_I RS Abs_term_inverse),  
                Rep_term_in_sexp, Rep_Term_rec, Rep_term_inverse, inj_Leaf,
                Inv_f_f, Abs_Rep_map, map_ident2, sexp.LeafI]
in

val term_rec = prove_goalw Term.thy
         [term_rec_def, App_def, Rep_Tlist_def, Abs_Tlist_def]
    "term_rec (App f ts) d = d f ts (map (%t. term_rec t d) ts)"
 (fn _ => [simp_tac term_rec_ss 1])

end;
