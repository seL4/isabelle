(*  Title:      HOL/ex/Simult.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Primitives for simultaneous recursive type definitions
  includes worked example of trees & forests

This is essentially the same data structure that on ex/term.ML, which is
simpler because it uses list as a new type former.  The approach in this
file may be superior for other simultaneous recursions.
*)

open Simult;

(*** Monotonicity and unfolding of the function ***)

goal Simult.thy "mono(%Z.  A <*> Part Z In1 \
\                      <+> ({Numb(0)} <+> Part Z In0 <*> Part Z In1))";
by (REPEAT (ares_tac [monoI, subset_refl, usum_mono, uprod_mono,
                      Part_mono] 1));
qed "TF_fun_mono";

val TF_unfold = TF_fun_mono RS (TF_def RS def_lfp_Tarski);

goalw Simult.thy [TF_def] "!!A B. A<=B ==> TF(A) <= TF(B)";
by (REPEAT (ares_tac [lfp_mono, subset_refl, usum_mono, uprod_mono] 1));
qed "TF_mono";

goalw Simult.thy [TF_def] "TF(sexp) <= sexp";
by (rtac lfp_lowerbound 1);
by (fast_tac (univ_cs addIs  sexp.intrs@[sexp_In0I, sexp_In1I]
                      addSEs [PartE]) 1);
qed "TF_sexp";

(* A <= sexp ==> TF(A) <= sexp *)
val TF_subset_sexp = standard
    (TF_mono RS (TF_sexp RSN (2,subset_trans)));


(** Elimination -- structural induction on the set TF **)

val TF_Rep_defs = [TCONS_def,FNIL_def,FCONS_def,NIL_def,CONS_def];

val major::prems = goalw Simult.thy TF_Rep_defs
 "[| i: TF(A);  \
\    !!M N. [| M: A;  N: Part (TF A) In1;  R(N) |] ==> R(TCONS M N);    \
\    R(FNIL);                   \
\    !!M N. [| M:  Part (TF A) In0;  N: Part (TF A) In1;  R(M);  R(N) \
\            |] ==> R(FCONS M N)    \
\    |] ==> R(i)";
by (rtac ([TF_def, TF_fun_mono, major] MRS def_induct) 1);
by (fast_tac (set_cs addIs (prems@[PartI])
                       addEs [usumE, uprodE, PartE]) 1);
qed "TF_induct";

(*This lemma replaces a use of subgoal_tac to prove tree_forest_induct*)
val prems = goalw Simult.thy [Part_def]
 "! M: TF(A). (M: Part (TF A) In0 --> P(M)) & (M: Part (TF A) In1 --> Q(M)) \
\ ==> (! M: Part (TF A) In0. P(M)) & (! M: Part (TF A) In1. Q(M))";
by (cfast_tac prems 1);
qed "TF_induct_lemma";

val uplus_cs = set_cs addSIs [PartI]
                      addSDs [In0_inject, In1_inject]
                      addSEs [In0_neq_In1, In1_neq_In0, PartE];

(*Could prove  ~ TCONS M N : Part (TF A) In1  etc. *)

(*Induction on TF with separate predicates P, Q*)
val prems = goalw Simult.thy TF_Rep_defs
    "[| !!M N. [| M: A;  N: Part (TF A) In1;  Q(N) |] ==> P(TCONS M N); \
\       Q(FNIL);        \
\       !!M N. [| M:  Part (TF A) In0;  N: Part (TF A) In1;  P(M);  Q(N) \
\               |] ==> Q(FCONS M N)     \
\    |] ==> (! M: Part (TF A) In0. P(M)) & (! N: Part (TF A) In1. Q(N))";
by (rtac (ballI RS TF_induct_lemma) 1);
by (etac TF_induct 1);
by (rewrite_goals_tac TF_Rep_defs);
by (ALLGOALS (fast_tac (uplus_cs addIs prems)));
(*29 secs??*)
qed "Tree_Forest_induct";

(*Induction for the abstract types 'a tree, 'a forest*)
val prems = goalw Simult.thy [Tcons_def,Fnil_def,Fcons_def]
    "[| !!x ts. Q(ts) ==> P(Tcons x ts);     \
\       Q(Fnil);        \
\       !!t ts. [| P(t);  Q(ts) |] ==> Q(Fcons t ts)    \
\    |] ==> (! t. P(t)) & (! ts. Q(ts))";
by (res_inst_tac [("P1","%z.P(Abs_Tree(z))"),
                  ("Q1","%z.Q(Abs_Forest(z))")] 
    (Tree_Forest_induct RS conjE) 1);
(*Instantiates ?A1 to range(Leaf). *)
by (fast_tac (set_cs addSEs [Rep_Tree_inverse RS subst, 
                             Rep_Forest_inverse RS subst] 
                     addSIs [Rep_Tree,Rep_Forest]) 4);
(*Cannot use simplifier: the rewrites work in the wrong direction!*)
by (ALLGOALS (fast_tac (set_cs addSEs [Abs_Tree_inverse RS subst,
                          Abs_Forest_inverse RS subst] 
                     addSIs prems)));
qed "tree_forest_induct";



(*** Isomorphisms ***)

goal Simult.thy "inj(Rep_Tree)";
by (rtac inj_inverseI 1);
by (rtac Rep_Tree_inverse 1);
qed "inj_Rep_Tree";

goal Simult.thy "inj_onto Abs_Tree (Part (TF(range Leaf)) In0)";
by (rtac inj_onto_inverseI 1);
by (etac Abs_Tree_inverse 1);
qed "inj_onto_Abs_Tree";

goal Simult.thy "inj(Rep_Forest)";
by (rtac inj_inverseI 1);
by (rtac Rep_Forest_inverse 1);
qed "inj_Rep_Forest";

goal Simult.thy "inj_onto Abs_Forest (Part (TF(range Leaf)) In1)";
by (rtac inj_onto_inverseI 1);
by (etac Abs_Forest_inverse 1);
qed "inj_onto_Abs_Forest";

(** Introduction rules for constructors **)

(* c : A <*> Part (TF A) In1 
        <+> {Numb(0)} <+> Part (TF A) In0 <*> Part (TF A) In1 ==> c : TF(A) *)
val TF_I = TF_unfold RS equalityD2 RS subsetD;

(*For reasoning about the representation*)
val TF_Rep_cs = uplus_cs addIs [TF_I, uprodI, usum_In0I, usum_In1I]
                         addSEs [Scons_inject];

val prems = goalw Simult.thy TF_Rep_defs
    "[| a: A;  M: Part (TF A) In1 |] ==> TCONS a M : Part (TF A) In0";
by (fast_tac (TF_Rep_cs addIs prems) 1);
qed "TCONS_I";

(* FNIL is a TF(A) -- this also justifies the type definition*)
goalw Simult.thy TF_Rep_defs "FNIL: Part (TF A) In1";
by (fast_tac TF_Rep_cs 1);
qed "FNIL_I";

val prems = goalw Simult.thy TF_Rep_defs
    "[| M: Part (TF A) In0;  N: Part (TF A) In1 |] ==> \
\    FCONS M N : Part (TF A) In1";
by (fast_tac (TF_Rep_cs addIs prems) 1);
qed "FCONS_I";

(** Injectiveness of TCONS and FCONS **)

goalw Simult.thy TF_Rep_defs "(TCONS K M=TCONS L N) = (K=L & M=N)";
by (fast_tac TF_Rep_cs 1);
qed "TCONS_TCONS_eq";
bind_thm ("TCONS_inject", (TCONS_TCONS_eq RS iffD1 RS conjE));

goalw Simult.thy TF_Rep_defs "(FCONS K M=FCONS L N) = (K=L & M=N)";
by (fast_tac TF_Rep_cs 1);
qed "FCONS_FCONS_eq";
bind_thm ("FCONS_inject", (FCONS_FCONS_eq RS iffD1 RS conjE));

(** Distinctness of TCONS, FNIL and FCONS **)

goalw Simult.thy TF_Rep_defs "TCONS M N ~= FNIL";
by (fast_tac TF_Rep_cs 1);
qed "TCONS_not_FNIL";
bind_thm ("FNIL_not_TCONS", (TCONS_not_FNIL RS not_sym));

bind_thm ("TCONS_neq_FNIL", (TCONS_not_FNIL RS notE));
val FNIL_neq_TCONS = sym RS TCONS_neq_FNIL;

goalw Simult.thy TF_Rep_defs "FCONS M N ~= FNIL";
by (fast_tac TF_Rep_cs 1);
qed "FCONS_not_FNIL";
bind_thm ("FNIL_not_FCONS", (FCONS_not_FNIL RS not_sym));

bind_thm ("FCONS_neq_FNIL", (FCONS_not_FNIL RS notE));
val FNIL_neq_FCONS = sym RS FCONS_neq_FNIL;

goalw Simult.thy TF_Rep_defs "TCONS M N ~= FCONS K L";
by (fast_tac TF_Rep_cs 1);
qed "TCONS_not_FCONS";
bind_thm ("FCONS_not_TCONS", (TCONS_not_FCONS RS not_sym));

bind_thm ("TCONS_neq_FCONS", (TCONS_not_FCONS RS notE));
val FCONS_neq_TCONS = sym RS TCONS_neq_FCONS;

(*???? Too many derived rules ????
  Automatically generate symmetric forms?  Always expand TF_Rep_defs? *)

(** Injectiveness of Tcons and Fcons **)

(*For reasoning about abstract constructors*)
val TF_cs = set_cs addSIs [Rep_Tree, Rep_Forest, TCONS_I, FNIL_I, FCONS_I]
                   addSEs [TCONS_inject, FCONS_inject,
                           TCONS_neq_FNIL, FNIL_neq_TCONS,
                           FCONS_neq_FNIL, FNIL_neq_FCONS,
                           TCONS_neq_FCONS, FCONS_neq_TCONS]
                   addSDs [inj_onto_Abs_Tree RS inj_ontoD,
                           inj_onto_Abs_Forest RS inj_ontoD,
                           inj_Rep_Tree RS injD, inj_Rep_Forest RS injD,
                           Leaf_inject];

goalw Simult.thy [Tcons_def] "(Tcons x xs=Tcons y ys) = (x=y & xs=ys)";
by (fast_tac TF_cs 1);
qed "Tcons_Tcons_eq";
bind_thm ("Tcons_inject", (Tcons_Tcons_eq RS iffD1 RS conjE));

goalw Simult.thy [Fcons_def,Fnil_def] "Fcons x xs ~= Fnil";
by (fast_tac TF_cs 1);
qed "Fcons_not_Fnil";

bind_thm ("Fcons_neq_Fnil", Fcons_not_Fnil RS notE);
val Fnil_neq_Fcons = sym RS Fcons_neq_Fnil;


(** Injectiveness of Fcons **)

goalw Simult.thy [Fcons_def] "(Fcons x xs=Fcons y ys) = (x=y & xs=ys)";
by (fast_tac TF_cs 1);
qed "Fcons_Fcons_eq";
bind_thm ("Fcons_inject", Fcons_Fcons_eq RS iffD1 RS conjE);


(*** TF_rec -- by wf recursion on pred_sexp ***)

val TF_rec_unfold =
    wf_pred_sexp RS wf_trancl RS (TF_rec_def RS def_wfrec);

(** conversion rules for TF_rec **)

goalw Simult.thy [TCONS_def]
    "!!M N. [| M: sexp;  N: sexp |] ==>         \
\           TF_rec (TCONS M N) b c d = b M N (TF_rec N b c d)";
by (rtac (TF_rec_unfold RS trans) 1);
by (simp_tac (!simpset addsimps [Case_In0, Split]) 1);
by (asm_simp_tac (!simpset addsimps [In0_def]) 1);
qed "TF_rec_TCONS";

goalw Simult.thy [FNIL_def] "TF_rec FNIL b c d = c";
by (rtac (TF_rec_unfold RS trans) 1);
by (simp_tac (HOL_ss addsimps [Case_In1, List_case_NIL]) 1);
qed "TF_rec_FNIL";

goalw Simult.thy [FCONS_def]
 "!!M N. [| M: sexp;  N: sexp |] ==>    \
\        TF_rec (FCONS M N) b c d = d M N (TF_rec M b c d) (TF_rec N b c d)";
by (rtac (TF_rec_unfold RS trans) 1);
by (simp_tac (HOL_ss addsimps [Case_In1, List_case_CONS]) 1);
by (asm_simp_tac (!simpset addsimps [CONS_def,In1_def]) 1);
qed "TF_rec_FCONS";


(*** tree_rec, forest_rec -- by TF_rec ***)

val Rep_Tree_in_sexp =
    [range_Leaf_subset_sexp RS TF_subset_sexp RS (Part_subset RS subset_trans),
     Rep_Tree] MRS subsetD;
val Rep_Forest_in_sexp =
    [range_Leaf_subset_sexp RS TF_subset_sexp RS (Part_subset RS subset_trans),
     Rep_Forest] MRS subsetD;

val tf_rec_ss = HOL_ss addsimps
  [TF_rec_TCONS, TF_rec_FNIL, TF_rec_FCONS,
   TCONS_I, FNIL_I, FCONS_I, Rep_Tree, Rep_Forest,
   Rep_Tree_inverse, Rep_Forest_inverse,
   Abs_Tree_inverse, Abs_Forest_inverse,
   inj_Leaf, Inv_f_f, sexp.LeafI, range_eqI,
   Rep_Tree_in_sexp, Rep_Forest_in_sexp];

goalw Simult.thy [tree_rec_def, forest_rec_def, Tcons_def]
    "tree_rec (Tcons a tf) b c d = b a tf (forest_rec tf b c d)";
by (simp_tac tf_rec_ss 1);
qed "tree_rec_Tcons";

goalw Simult.thy [forest_rec_def, Fnil_def] "forest_rec Fnil b c d = c";
by (simp_tac tf_rec_ss 1);
qed "forest_rec_Fnil";

goalw Simult.thy [tree_rec_def, forest_rec_def, Fcons_def]
    "forest_rec (Fcons t tf) b c d = \
\    d t tf (tree_rec t b c d) (forest_rec tf b c d)";
by (simp_tac tf_rec_ss 1);
qed "forest_rec_Cons";
