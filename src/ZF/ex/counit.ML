(*  Title: 	ZF/ex/counit.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Trivial codatatype definitions, one of which goes wrong!

Need to find sufficient conditions for codatatypes to work correctly!
*)

(*This degenerate definition does not work well because the one constructor's
  definition is trivial!  The same thing occurs with Aczel's Special Final
  Coalgebra Theorem
*)
structure CoUnit = CoDatatype_Fun
 (val thy = QUniv.thy;
  val rec_specs = 
      [("counit", "quniv(0)",
	  [(["Con"],	"i=>i")])];
  val rec_styp = "i";
  val ext = None
  val sintrs = ["x: counit ==> Con(x) : counit"];
  val monos = [];
  val type_intrs = codatatype_intrs
  val type_elims = codatatype_elims);
  
val [ConI] = CoUnit.intrs;

(*USELESS because folding on Con(?xa) == ?xa fails*)
val ConE = CoUnit.mk_cases CoUnit.con_defs "Con(x) : counit";

(*Proving freeness results*)
val Con_iff = CoUnit.mk_free "Con(x)=Con(y) <-> x=y";

(*Should be a singleton, not everything!*)
goal CoUnit.thy "counit = quniv(0)";
by (rtac (CoUnit.dom_subset RS equalityI) 1);
by (rtac subsetI 1);
by (etac CoUnit.coinduct 1);
by (rtac subset_refl 1);
by (rewrite_goals_tac CoUnit.con_defs);
by (fast_tac ZF_cs 1);
val counit_eq_univ = result();


(*****************************************************************)

(*A similar example, but the constructor is non-degenerate and it works!
  The resulting set is a singleton.
*)

structure CoUnit2 = CoDatatype_Fun
 (val thy = QUniv.thy;
  val rec_specs = 
      [("counit2", "quniv(0)",
	  [(["Con2"],	"[i,i]=>i")])];
  val rec_styp = "i";
  val ext = None
  val sintrs = ["[| x: counit2;  y: counit2 |] ==> Con2(x,y) : counit2"];
  val monos = [];
  val type_intrs = codatatype_intrs
  val type_elims = codatatype_elims);

val [Con2I] = CoUnit2.intrs;

val Con2E = CoUnit2.mk_cases CoUnit2.con_defs "Con2(x,y) : counit2";

(*Proving freeness results*)
val Con2_iff = CoUnit2.mk_free "Con2(x,y)=Con2(x',y') <-> x=x' & y=y'";

goalw CoUnit2.thy CoUnit2.con_defs "bnd_mono(univ(0), %x. Con2(x,x))";
by (rtac bnd_monoI 1);
by (REPEAT (ares_tac [subset_refl, QPair_subset_univ, QPair_mono] 1));
val Con2_bnd_mono = result();

goal CoUnit2.thy "lfp(univ(0), %x. Con2(x,x)) : counit2";
by (rtac (singletonI RS CoUnit2.coinduct) 1);
by (rtac (qunivI RS singleton_subsetI) 1);
by (rtac ([lfp_subset, empty_subsetI RS univ_mono] MRS subset_trans) 1);
by (fast_tac (ZF_cs addSIs [Con2_bnd_mono RS lfp_Tarski]) 1);
val lfp_Con2_in_counit2 = result();

(*Lemma for proving finality.  Borrowed from ex/llist_eq.ML!*)
goal CoUnit2.thy
    "!!i. Ord(i) ==> ALL x y. x: counit2 & y: counit2 --> x Int Vset(i) <= y";
by (etac trans_induct 1);
by (safe_tac subset_cs);
by (etac CoUnit2.elim 1);
by (etac CoUnit2.elim 1);
by (rewrite_goals_tac CoUnit2.con_defs);
by (fast_tac lleq_cs 1);
val counit2_Int_Vset_subset_lemma = result();

val counit2_Int_Vset_subset = standard
	(counit2_Int_Vset_subset_lemma RS spec RS spec RS mp);

goal CoUnit2.thy "!!x y. [| x: counit2;  y: counit2 |] ==> x=y";
by (rtac equalityI 1);
by (REPEAT (ares_tac [conjI, counit2_Int_Vset_subset RS Int_Vset_subset] 1));
val counit2_implies_equal = result();

goal CoUnit2.thy "counit2 = {lfp(univ(0), %x. Con2(x,x))}";
by (rtac equalityI 1);
by (rtac (lfp_Con2_in_counit2 RS singleton_subsetI) 2);
by (rtac subsetI 1);
by (dtac (lfp_Con2_in_counit2 RS counit2_implies_equal) 1);
by (etac subst 1);
by (rtac singletonI 1);
val counit2_eq_univ = result();
