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
 (val thy 	 = LList.thy |> add_consts [("lleq","i=>i",NoSyn)]
  val thy_name 	 = "LList_Eq"
  val rec_doms   = [("lleq", "llist(A) * llist(A)")]
  val sintrs     = 
        ["<LNil, LNil> : lleq(A)",
         "[| a:A; <l,l'>: lleq(A) |] ==> <LCons(a,l), LCons(a,l')>: lleq(A)"]
  val monos      = []
  val con_defs   = []
  val type_intrs = LList.intrs
  val type_elims = []);

(** Alternatives for above:
  val con_defs = LList.con_defs
  val type_intrs = codatatype_intrs
  val type_elims = [quniv_QPair_E]
**)

val lleq_cs = subset_cs
	addSIs [QPair_Int_Vset_subset_UN RS subset_trans, QPair_mono]
        addSEs [Ord_in_Ord, Pair_inject];

(*Lemma for proving finality.  Unfold the lazy list; use induction hypothesis*)
goal LList_Eq.thy
   "!!i. Ord(i) ==> ALL l l'. <l,l'> : lleq(A) --> l Int Vset(i) <= l'";
by (etac trans_induct 1);
by (REPEAT (resolve_tac [allI, impI] 1));
by (etac LList_Eq.elim 1);
by (rewrite_goals_tac (QInr_def::LList.con_defs));
by (safe_tac lleq_cs);
by (fast_tac (subset_cs addSEs [Ord_trans, make_elim bspec]) 1);
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

