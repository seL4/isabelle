(*  Title:      ZF/ex/CoUnit.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Trivial codatatype definitions, one of which goes wrong!

See discussion in 
  L C Paulson.  A Concrete Final Coalgebra Theorem for ZF Set Theory.
  Report 334,  Cambridge University Computer Laboratory.  1994.
*)

(*USELESS because folding on Con(?xa) == ?xa fails*)
val ConE = counit.mk_cases "Con(x) : counit";

(*Proving freeness results*)
val Con_iff = counit.mk_free "Con(x)=Con(y) <-> x=y";

(*Should be a singleton, not everything!*)
Goal "counit = quniv(0)";
by (rtac (counit.dom_subset RS equalityI) 1);
by (rtac subsetI 1);
by (etac counit.coinduct 1);
by (rtac subset_refl 1);
by (rewrite_goals_tac counit.con_defs);
by (Fast_tac 1);
qed "counit_eq_univ";


(*A similar example, but the constructor is non-degenerate and it works!
  The resulting set is a singleton.
*)

val Con2E = counit2.mk_cases "Con2(x,y) : counit2";

(*Proving freeness results*)
val Con2_iff = counit2.mk_free "Con2(x,y)=Con2(x',y') <-> x=x' & y=y'";

Goalw counit2.con_defs "bnd_mono(univ(0), %x. Con2(x,x))";
by (rtac bnd_monoI 1);
by (REPEAT (ares_tac [subset_refl, QPair_subset_univ, QPair_mono] 1));
qed "Con2_bnd_mono";

Goal "lfp(univ(0), %x. Con2(x,x)) : counit2";
by (rtac (singletonI RS counit2.coinduct) 1);
by (rtac (qunivI RS singleton_subsetI) 1);
by (rtac ([lfp_subset, empty_subsetI RS univ_mono] MRS subset_trans) 1);
by (fast_tac (claset() addSIs [Con2_bnd_mono RS lfp_Tarski]) 1);
qed "lfp_Con2_in_counit2";

(*Lemma for proving finality.  Borrowed from ex/llist_eq.ML!*)
Goal "Ord(i) ==> ALL x y. x: counit2 & y: counit2 --> x Int Vset(i) <= y";
by (etac trans_induct 1);
by (safe_tac subset_cs);
by (etac counit2.elim 1);
by (etac counit2.elim 1);
by (rewrite_goals_tac counit2.con_defs);
by (fast_tac (subset_cs
	      addSIs [QPair_Int_Vset_subset_UN RS subset_trans, QPair_mono]
	      addSEs [Ord_in_Ord, Pair_inject]) 1);
qed "counit2_Int_Vset_subset_lemma";

val counit2_Int_Vset_subset = standard
        (counit2_Int_Vset_subset_lemma RS spec RS spec RS mp);

Goal "[| x: counit2;  y: counit2 |] ==> x=y";
by (rtac equalityI 1);
by (REPEAT (ares_tac [conjI, counit2_Int_Vset_subset RS Int_Vset_subset] 1));
qed "counit2_implies_equal";

Goal "counit2 = {lfp(univ(0), %x. Con2(x,x))}";
by (rtac equalityI 1);
by (rtac (lfp_Con2_in_counit2 RS singleton_subsetI) 2);
by (rtac subsetI 1);
by (dtac (lfp_Con2_in_counit2 RS counit2_implies_equal) 1);
by (etac subst 1);
by (rtac singletonI 1);
qed "counit2_eq_univ";
