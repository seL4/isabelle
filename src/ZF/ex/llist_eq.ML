(*  Title: 	ZF/ex/llist_eq.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Equality for llist(A) as a greatest fixed point
***)

(*Previously used <*> in the domain and variant pairs as elements.  But
  standard pairs work just as well.  To use variant pairs, must change prefix
  a q/Q to the Sigma, Pair and converse rules.*)

structure LList_Eq = CoInductive_Fun
 (val thy = LList.thy addconsts [(["lleq"],"i=>i")];
  val rec_doms = [("lleq", "llist(A) * llist(A)")];
  val sintrs = 
      ["<LNil, LNil> : lleq(A)",
       "[| a:A;  <l, l'>: lleq(A) |] ==> <LCons(a,l), LCons(a,l')> : lleq(A)"];
  val monos = [];
  val con_defs = [];
  val type_intrs = LList.intrs@[SigmaI];
  val type_elims = [SigmaE2]);

(** Alternatives for above:
  val con_defs = LList.con_defs
  val type_intrs = codatatype_intrs
  val type_elims = [quniv_QPair_E]
**)

val lleq_cs = subset_cs
	addSIs [succI1, Int_Vset_0_subset,
		QPair_Int_Vset_succ_subset_trans,
		QPair_Int_Vset_subset_trans];

(** Some key feature of this proof needs to be made a general theorem! **)

(*Keep unfolding the lazy list until the induction hypothesis applies*)
goal LList_Eq.thy
   "!!i. Ord(i) ==> ALL l l'. <l,l'> : lleq(A) --> l Int Vset(i) <= l'";
by (etac trans_induct 1);
by (safe_tac subset_cs);
by (etac LList_Eq.elim 1);
by (safe_tac (subset_cs addSEs [Pair_inject]));
by (rewrite_goals_tac LList.con_defs);
by (etac Ord_cases 1 THEN REPEAT_FIRST hyp_subst_tac);
(*0 case*)
by (fast_tac lleq_cs 1);
(*succ(j) case*)
by (rewtac QInr_def);
by (fast_tac lleq_cs 1);
(*Limit(i) case*)
by (etac (Limit_Vfrom_eq RS ssubst) 1);
by (rtac (Int_UN_distrib RS ssubst) 1);
by (fast_tac lleq_cs 1);
val lleq_Int_Vset_subset_lemma = result();

val lleq_Int_Vset_subset = standard
	(lleq_Int_Vset_subset_lemma RS spec RS spec RS mp);


(*lleq(A) is a symmetric relation because qconverse(lleq(A)) is a fixedpoint*)
val [prem] = goal LList_Eq.thy "<l,l'> : lleq(A) ==> <l',l> : lleq(A)";
by (rtac (prem RS converseI RS LList_Eq.coinduct) 1);
by (rtac (LList_Eq.dom_subset RS converse_type) 1);
by (safe_tac converse_cs);
by (etac LList_Eq.elim 1);
by (ALLGOALS (fast_tac qconverse_cs));
val lleq_symmetric = result();

goal LList_Eq.thy "!!l l'. <l,l'> : lleq(A) ==> l=l'";
by (rtac equalityI 1);
by (REPEAT (ares_tac [lleq_Int_Vset_subset RS Int_Vset_subset] 1
     ORELSE etac lleq_symmetric 1));
val lleq_implies_equal = result();

val [eqprem,lprem] = goal LList_Eq.thy
    "[| l=l';  l: llist(A) |] ==> <l,l'> : lleq(A)";
by (res_inst_tac [("X", "{<l,l>. l: llist(A)}")] LList_Eq.coinduct 1);
by (rtac (lprem RS RepFunI RS (eqprem RS subst)) 1);
by (safe_tac qpair_cs);
by (etac LList.elim 1);
by (ALLGOALS (fast_tac pair_cs));
val equal_llist_implies_leq = result();

