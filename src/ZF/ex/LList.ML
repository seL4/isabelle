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
  val thy = QUniv.thy;
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
  val type_intrs = co_data_typechecks
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
                     addIs (Int_quniv_in_quniv::co_data_typechecks);

(*Keep unfolding the lazy list until the induction hypothesis applies*)
goal LList.thy
   "!!i. i : nat ==> 	\
\        ALL l: llist(quniv(A)). l Int Vfrom(quniv(A), i) : quniv(A)";
be complete_induct 1;
br ballI 1;
be LList.elim 1;
bws ([QInl_def,QInr_def]@LList.con_defs);
by (fast_tac quniv_cs 1);
by (etac natE 1 THEN REPEAT_FIRST hyp_subst_tac);
by (fast_tac quniv_cs 1);
by (fast_tac quniv_cs 1);
val llist_quniv_lemma = result();

goal LList.thy "llist(quniv(A)) <= quniv(A)";
br subsetI 1;
br quniv_Int_Vfrom 1;
be (LList.dom_subset RS subsetD) 1;
by (REPEAT (ares_tac [llist_quniv_lemma RS bspec] 1));
val llist_quniv = result();

val llist_subset_quniv = standard
    (llist_mono RS (llist_quniv RSN (2,subset_trans)));

(*** Equality for llist(A) as a greatest fixed point ***)

structure LList_Eq = Co_Inductive_Fun
 (val thy = LList.thy addconsts [(["lleq"],"i=>i")];
  val rec_doms = [("lleq","llist(A) <*> llist(A)")];
  val sintrs = 
      ["<LNil; LNil> : lleq(A)",
       "[| a:A;  <l; l'>: lleq(A) |] ==> <LCons(a,l); LCons(a,l')> : lleq(A)"];
  val monos = [];
  val con_defs = [];
  val type_intrs = LList.intrs@[QSigmaI];
  val type_elims = [QSigmaE2]);

(** Alternatives for above:
  val con_defs = LList.con_defs
  val type_intrs = co_data_typechecks
  val type_elims = [quniv_QPair_E]
**)

val lleq_cs = subset_cs
	addSIs [succI1, Int_Vset_0_subset,
		QPair_Int_Vset_succ_subset_trans,
		QPair_Int_Vset_subset_trans];

(*Keep unfolding the lazy list until the induction hypothesis applies*)
goal LList_Eq.thy
   "!!i. Ord(i) ==> ALL l l'. <l;l'> : lleq(A) --> l Int Vset(i) <= l'";
be trans_induct 1;
by (safe_tac subset_cs);
be LList_Eq.elim 1;
by (safe_tac (subset_cs addSEs [QPair_inject]));
bws LList.con_defs;
by (etac Ord_cases 1 THEN REPEAT_FIRST hyp_subst_tac);
(*0 case*)
by (fast_tac lleq_cs 1);
(*succ(j) case*)
bw QInr_def;
by (fast_tac lleq_cs 1);
(*Limit(i) case*)
be (Limit_Vfrom_eq RS ssubst) 1;
br (Int_UN_distrib RS ssubst) 1;
by (fast_tac lleq_cs 1);
val lleq_Int_Vset_subset_lemma = result();

val lleq_Int_Vset_subset = standard
	(lleq_Int_Vset_subset_lemma RS spec RS spec RS mp);


(*lleq(A) is a symmetric relation because qconverse(lleq(A)) is a fixedpoint*)
val [prem] = goal LList_Eq.thy "<l;l'> : lleq(A) ==> <l';l> : lleq(A)";
br (prem RS qconverseI RS LList_Eq.co_induct) 1;
br (LList_Eq.dom_subset RS qconverse_type) 1;
by (safe_tac qconverse_cs);
be LList_Eq.elim 1;
by (ALLGOALS (fast_tac qconverse_cs));
val lleq_symmetric = result();

goal LList_Eq.thy "!!l l'. <l;l'> : lleq(A) ==> l=l'";
br equalityI 1;
by (REPEAT (ares_tac [lleq_Int_Vset_subset RS Int_Vset_subset] 1
     ORELSE etac lleq_symmetric 1));
val lleq_implies_equal = result();

val [eqprem,lprem] = goal LList_Eq.thy
    "[| l=l';  l: llist(A) |] ==> <l;l'> : lleq(A)";
by (res_inst_tac [("X", "{<l;l>. l: llist(A)}")] LList_Eq.co_induct 1);
br (lprem RS RepFunI RS (eqprem RS subst)) 1;
by (safe_tac qpair_cs);
be LList.elim 1;
by (ALLGOALS (fast_tac qpair_cs));
val equal_llist_implies_leq = result();


