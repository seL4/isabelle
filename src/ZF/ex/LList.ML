(*  Title: 	ZF/ex/LList.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Codatatype definition of Lazy Lists
*)

open LList;

(*An elimination rule, for type-checking*)
val LConsE = llist.mk_cases llist.con_defs "LCons(a,l) : llist(A)";

(*Proving freeness results*)
val LCons_iff      = llist.mk_free "LCons(a,l)=LCons(a',l') <-> a=a' & l=l'";
val LNil_LCons_iff = llist.mk_free "~ LNil=LCons(a,l)";

goal LList.thy "llist(A) = {0} <+> (A <*> llist(A))";
let open llist;  val rew = rewrite_rule con_defs in  
by (fast_tac (qsum_cs addSIs (equalityI :: map rew intrs)
                      addEs [rew elim]) 1)
end;
val llist_unfold = result();

(*** Lemmas to justify using "llist" in other recursive type definitions ***)

goalw LList.thy llist.defs "!!A B. A<=B ==> llist(A) <= llist(B)";
by (rtac gfp_mono 1);
by (REPEAT (rtac llist.bnd_mono 1));
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
by (etac llist.elim 1);
by (rewrite_goals_tac ([QInl_def,QInr_def]@llist.con_defs));
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


(*** Lazy List Equality: lleq ***)

val lleq_cs = subset_cs
	addSIs [QPair_Int_Vset_subset_UN RS subset_trans, QPair_mono]
        addSEs [Ord_in_Ord, Pair_inject];

(*Lemma for proving finality.  Unfold the lazy list; use induction hypothesis*)
goal LList.thy
   "!!i. Ord(i) ==> ALL l l'. <l,l'> : lleq(A) --> l Int Vset(i) <= l'";
by (etac trans_induct 1);
by (REPEAT (resolve_tac [allI, impI] 1));
by (etac lleq.elim 1);
by (rewrite_goals_tac (QInr_def::llist.con_defs));
by (safe_tac lleq_cs);
by (fast_tac (subset_cs addSEs [Ord_trans, make_elim bspec]) 1);
val lleq_Int_Vset_subset_lemma = result();

val lleq_Int_Vset_subset = standard
	(lleq_Int_Vset_subset_lemma RS spec RS spec RS mp);


(*lleq(A) is a symmetric relation because qconverse(lleq(A)) is a fixedpoint*)
val [prem] = goal LList.thy "<l,l'> : lleq(A) ==> <l',l> : lleq(A)";
by (rtac (prem RS converseI RS lleq.coinduct) 1);
by (rtac (lleq.dom_subset RS converse_type) 1);
by (safe_tac converse_cs);
by (etac lleq.elim 1);
by (ALLGOALS (fast_tac qconverse_cs));
val lleq_symmetric = result();

goal LList.thy "!!l l'. <l,l'> : lleq(A) ==> l=l'";
by (rtac equalityI 1);
by (REPEAT (ares_tac [lleq_Int_Vset_subset RS Int_Vset_subset] 1
     ORELSE etac lleq_symmetric 1));
val lleq_implies_equal = result();

val [eqprem,lprem] = goal LList.thy
    "[| l=l';  l: llist(A) |] ==> <l,l'> : lleq(A)";
by (res_inst_tac [("X", "{<l,l>. l: llist(A)}")] lleq.coinduct 1);
by (rtac (lprem RS RepFunI RS (eqprem RS subst)) 1);
by (safe_tac qpair_cs);
by (etac llist.elim 1);
by (ALLGOALS (fast_tac pair_cs));
val equal_llist_implies_leq = result();


(*** Lazy List Functions ***)

(*Examples of coinduction for type-checking and to prove llist equations*)

(*** lconst -- defined directly using lfp, but equivalent to a LList_corec ***)

goalw LList.thy llist.con_defs "bnd_mono(univ(a), %l. LCons(a,l))";
by (rtac bnd_monoI 1);
by (REPEAT (ares_tac [subset_refl, QInr_mono, QPair_mono] 2));
by (REPEAT (ares_tac [subset_refl, A_subset_univ, 
		      QInr_subset_univ, QPair_subset_univ] 1));
val lconst_fun_bnd_mono = result();

(* lconst(a) = LCons(a,lconst(a)) *)
val lconst = standard 
    ([lconst_def, lconst_fun_bnd_mono] MRS def_lfp_Tarski);

val lconst_subset = lconst_def RS def_lfp_subset;

val member_subset_Union_eclose = standard (arg_into_eclose RS Union_upper);

goal LList.thy "!!a A. a : A ==> lconst(a) : quniv(A)";
by (rtac (lconst_subset RS subset_trans RS qunivI) 1);
by (etac (arg_into_eclose RS eclose_subset RS univ_mono) 1);
val lconst_in_quniv = result();

goal LList.thy "!!a A. a:A ==> lconst(a): llist(A)";
by (rtac (singletonI RS llist.coinduct) 1);
by (etac (lconst_in_quniv RS singleton_subsetI) 1);
by (fast_tac (ZF_cs addSIs [lconst]) 1);
val lconst_type = result();

(*** flip --- equations merely assumed; certain consequences proved ***)

val flip_ss = ZF_ss addsimps [flip_LNil, flip_LCons, not_type];

goal QUniv.thy "!!b. b:bool ==> b Int X <= univ(eclose(A))";
by (fast_tac (quniv_cs addSEs [boolE]) 1);
val bool_Int_subset_univ = result();

val flip_cs = quniv_cs addSIs [not_type]
                       addIs  [bool_Int_subset_univ];

(*Reasoning borrowed from lleq.ML; a similar proof works for all
  "productive" functions -- cf Coquand's "Infinite Objects in Type Theory".*)
goal LList.thy
   "!!i. Ord(i) ==> ALL l: llist(bool). flip(l) Int Vset(i) <= \
\                   univ(eclose(bool))";
by (etac trans_induct 1);
by (rtac ballI 1);
by (etac llist.elim 1);
by (asm_simp_tac flip_ss 1);
by (asm_simp_tac flip_ss 2);
by (rewrite_goals_tac ([QInl_def,QInr_def]@llist.con_defs));
(*LNil case*)
by (fast_tac flip_cs 1);
(*LCons case*)
by (safe_tac flip_cs);
by (ALLGOALS (fast_tac (flip_cs addSEs [Ord_trans, make_elim bspec])));
val flip_llist_quniv_lemma = result();

goal LList.thy "!!l. l: llist(bool) ==> flip(l) : quniv(bool)";
by (rtac (flip_llist_quniv_lemma RS bspec RS Int_Vset_subset RS qunivI) 1);
by (REPEAT (assume_tac 1));
val flip_in_quniv = result();

val [prem] = goal LList.thy "l : llist(bool) ==> flip(l): llist(bool)";
by (res_inst_tac [("X", "{flip(l) . l:llist(bool)}")]
       llist.coinduct 1);
by (rtac (prem RS RepFunI) 1);
by (fast_tac (ZF_cs addSIs [flip_in_quniv]) 1);
by (etac RepFunE 1);
by (etac llist.elim 1);
by (asm_simp_tac flip_ss 1);
by (asm_simp_tac flip_ss 1);
by (fast_tac (ZF_cs addSIs [not_type]) 1);
val flip_type = result();

val [prem] = goal LList.thy
    "l : llist(bool) ==> flip(flip(l)) = l";
by (res_inst_tac [("X1", "{<flip(flip(l)),l> . l:llist(bool)}")]
       (lleq.coinduct RS lleq_implies_equal) 1);
by (rtac (prem RS RepFunI) 1);
by (fast_tac (ZF_cs addSIs [flip_type]) 1);
by (etac RepFunE 1);
by (etac llist.elim 1);
by (asm_simp_tac flip_ss 1);
by (asm_simp_tac (flip_ss addsimps [flip_type, not_not]) 1);
by (fast_tac (ZF_cs addSIs [not_type]) 1);
val flip_flip = result();
