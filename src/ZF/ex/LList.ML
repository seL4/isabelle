(*  Title: 	ZF/ex/llist.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Codatatype definition of Lazy Lists
*)

structure LList = CoDatatype_Fun
 (val thy        = QUniv.thy
  val thy_name   = "LList"
  val rec_specs  = [("llist", "quniv(A)",
                      [(["LNil"],   "i",	NoSyn), 
                       (["LCons"],  "[i,i]=>i",	NoSyn)])]
  val rec_styp   = "i=>i"
  val sintrs     = ["LNil : llist(A)",
                    "[| a: A;  l: llist(A) |] ==> LCons(a,l) : llist(A)"]
  val monos      = []
  val type_intrs = codatatype_intrs
  val type_elims = codatatype_elims);

val [LNilI, LConsI] = LList.intrs;

(*An elimination rule, for type-checking*)
val LConsE = LList.mk_cases LList.con_defs "LCons(a,l) : llist(A)";

(*Proving freeness results*)
val LCons_iff      = LList.mk_free "LCons(a,l)=LCons(a',l') <-> a=a' & l=l'";
val LNil_LCons_iff = LList.mk_free "~ LNil=LCons(a,l)";

goal LList.thy "llist(A) = {0} <+> (A <*> llist(A))";
by (rtac (LList.unfold RS trans) 1);
bws LList.con_defs;
by (fast_tac (qsum_cs addIs ([equalityI] @ codatatype_intrs)
		      addDs [LList.dom_subset RS subsetD]
 	              addEs [A_into_quniv]
                      addSEs [QSigmaE]) 1);
val llist_unfold = result();

(*** Lemmas to justify using "llist" in other recursive type definitions ***)

goalw LList.thy LList.defs "!!A B. A<=B ==> llist(A) <= llist(B)";
by (rtac gfp_mono 1);
by (REPEAT (rtac LList.bnd_mono 1));
by (REPEAT (ares_tac (quniv_mono::basic_monos) 1));
val llist_mono = result();

(** Closure of quniv(A) under llist -- why so complex?  Its a gfp... **)

val quniv_cs = subset_cs addSIs [QPair_Int_Vset_subset_UN RS subset_trans, 
				 QPair_subset_univ,
				 empty_subsetI, one_in_quniv RS qunivD]
                 addIs  [Int_lower1 RS subset_trans]
		 addSDs [qunivD]
                 addSEs [Ord_in_Ord];

goal LList.thy
   "!!i. Ord(i) ==> ALL l: llist(quniv(A)). l Int Vset(i) <= univ(eclose(A))";
by (etac trans_induct 1);
by (rtac ballI 1);
by (etac LList.elim 1);
by (rewrite_goals_tac ([QInl_def,QInr_def]@LList.con_defs));
(*LNil case*)
by (fast_tac quniv_cs 1);
(*LCons case*)
by (safe_tac quniv_cs);
by (ALLGOALS (fast_tac (quniv_cs addSEs [Ord_trans, make_elim bspec])));
val llist_quniv_lemma = result();

goal LList.thy "llist(quniv(A)) <= quniv(A)";
by (rtac (qunivI RS subsetI) 1);
by (rtac Int_Vset_subset 1);
by (REPEAT (ares_tac [llist_quniv_lemma RS bspec] 1));
val llist_quniv = result();

val llist_subset_quniv = standard
    (llist_mono RS (llist_quniv RSN (2,subset_trans)));

(* Definition and use of LList_Eq has been moved to llist_eq.ML to allow
   automatic association between theory name and filename. *)
