(*  Title: 	ZF/ex/llist.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Co-Datatype definition of Lazy Lists

Needs a "take-lemma" to prove llist_subset_quniv and to justify co-induction
for proving equality
*)

structure LList = Co_Datatype_Fun
 (val thy = QUniv.thy;
  val rec_specs = 
      [("llist", "quniv(A)",
	  [(["LNil"],	"i"), 
	   (["LCons"],	"[i,i]=>i")])];
  val rec_styp = "i=>i";
  val ext = None
  val sintrs = 
      ["LNil : llist(A)",
       "[| a: A;  l: llist(A) |] ==> LCons(a,l) : llist(A)"];
  val monos = [];
  val type_intrs = co_datatype_intrs
  val type_elims = []);
  
val [LNilI, LConsI] = LList.intrs;

(*An elimination rule, for type-checking*)
val LConsE = LList.mk_cases LList.con_defs "LCons(a,l) : llist(A)";

(*Proving freeness results*)
val LCons_iff      = LList.mk_free "LCons(a,l)=LCons(a',l') <-> a=a' & l=l'";
val LNil_LCons_iff = LList.mk_free "~ LNil=LCons(a,l)";

(*** Lemmas to justify using "llist" in other recursive type definitions ***)

goalw LList.thy LList.defs "!!A B. A<=B ==> llist(A) <= llist(B)";
by (rtac gfp_mono 1);
by (REPEAT (rtac LList.bnd_mono 1));
by (REPEAT (ares_tac (quniv_mono::basic_monos) 1));
val llist_mono = result();

(** Closure of quniv(A) under llist -- why so complex?  Its a gfp... **)

val in_quniv_rls =
 [Transset_quniv, QPair_Int_quniv_in_quniv, Int_Vfrom_0_in_quniv, 
  zero_Int_in_quniv, one_Int_in_quniv,
  QPair_Int_Vfrom_succ_in_quniv, QPair_Int_Vfrom_in_quniv];

val quniv_cs = ZF_cs addSIs in_quniv_rls 
                     addIs (Int_quniv_in_quniv::co_datatype_intrs);

(*Keep unfolding the lazy list until the induction hypothesis applies*)
goal LList.thy
   "!!i. i : nat ==> 	\
\        ALL l: llist(quniv(A)). l Int Vfrom(quniv(A), i) : quniv(A)";
by (etac complete_induct 1);
by (rtac ballI 1);
by (etac LList.elim 1);
by (rewrite_goals_tac ([QInl_def,QInr_def]@LList.con_defs));
by (fast_tac quniv_cs 1);
by (etac natE 1 THEN REPEAT_FIRST hyp_subst_tac);
by (fast_tac quniv_cs 1);
by (fast_tac quniv_cs 1);
val llist_quniv_lemma = result();

goal LList.thy "llist(quniv(A)) <= quniv(A)";
by (rtac subsetI 1);
by (rtac quniv_Int_Vfrom 1);
by (etac (LList.dom_subset RS subsetD) 1);
by (REPEAT (ares_tac [llist_quniv_lemma RS bspec] 1));
val llist_quniv = result();

val llist_subset_quniv = standard
    (llist_mono RS (llist_quniv RSN (2,subset_trans)));

(* Definition and use of LList_Eq has been moved to llist_eq.ML to allow
   automatic association between theory name and filename. *)
