(*  Title: 	ZF/ex/llist-fn.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Functions for Lazy Lists in Zermelo-Fraenkel Set Theory 

Examples of coinduction for type-checking and to prove llist equations
*)

open LListFn;

(*** lconst -- defined directly using lfp, but equivalent to a LList_corec ***)

goalw LListFn.thy LList.con_defs "bnd_mono(univ(a), %l. LCons(a,l))";
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

goal LListFn.thy "!!a A. a : A ==> lconst(a) : quniv(A)";
by (rtac (lconst_subset RS subset_trans RS qunivI) 1);
by (etac (arg_into_eclose RS eclose_subset RS univ_mono) 1);
val lconst_in_quniv = result();

goal LListFn.thy "!!a A. a:A ==> lconst(a): llist(A)";
by (rtac (singletonI RS LList.coinduct) 1);
by (fast_tac (ZF_cs addSIs [lconst_in_quniv]) 1);
by (fast_tac (ZF_cs addSIs [lconst]) 1);
val lconst_type = result();

(*** flip --- equations merely assumed; certain consequences proved ***)

val flip_ss = ZF_ss addsimps [flip_LNil, flip_LCons, not_type];

goal QUniv.thy "!!b. b:bool ==> b Int X : quniv(A)";
by (etac boolE 1);
by (REPEAT (resolve_tac [one_Int_in_quniv, zero_Int_in_quniv] 1
     ORELSE etac ssubst 1));
val bool_Int_into_quniv = result();

(* (!!x. x : A ==> B(x) : quniv(C)) ==> (UN x:A. B(x)) : quniv(C) *)
val UN_in_quniv = standard (qunivD RS UN_least RS qunivI);

val Int_Vset_in_quniv = qunivD RS Int_Vset_subset RS qunivI;

val flip_cs = 
  ZF_cs addSIs [not_type,
		QPair_in_quniv, QInl_in_quniv, QInr_in_quniv, 
		zero_in_quniv, Int_Vset_0_subset RS qunivI,
		Transset_0,
		zero_Int_in_quniv, one_Int_in_quniv,
		QPair_Int_Vfrom_succ_in_quniv, QPair_Int_Vfrom_in_quniv]
        addIs  [bool_Int_into_quniv, Int_quniv_in_quniv];

(*Reasoning borrowed from llist_eq.ML; a similar proof works for all
  "productive" functions -- cf Coquand's "Infinite Objects in Type Theory".*)
goal LListFn.thy
   "!!i. Ord(i) ==> ALL l: llist(bool). flip(l) Int Vset(i) : quniv(bool)";
by (etac trans_induct 1);
by (safe_tac ZF_cs);
by (etac LList.elim 1);
by (asm_simp_tac flip_ss 1);
by (asm_simp_tac flip_ss 2);
by (rewrite_goals_tac ([QInl_def,QInr_def]@LList.con_defs));
by (fast_tac flip_cs 1);
by (etac Ord_cases 1 THEN REPEAT_FIRST hyp_subst_tac);
(*0 case*)
by (fast_tac flip_cs 1);
(*succ(j) case*)
by (fast_tac flip_cs 1);
(*Limit(i) case*)
by (etac (Limit_Vfrom_eq RS ssubst) 1);
by (rtac (Int_UN_distrib RS ssubst) 1);
by (rtac UN_in_quniv 1);
by (fast_tac flip_cs 1);
val flip_llist_quniv_lemma = result();

goal LListFn.thy "!!l. l: llist(bool) ==> flip(l) : quniv(bool)";
by (rtac (flip_llist_quniv_lemma RS bspec RS Int_Vset_in_quniv) 1);
by (REPEAT (assume_tac 1));
val flip_in_quniv = result();

val [prem] = goal LListFn.thy "l : llist(bool) ==> flip(l): llist(bool)";
by (res_inst_tac [("X", "{flip(l) . l:llist(bool)}")]
       LList.coinduct 1);
by (rtac (prem RS RepFunI) 1);
by (fast_tac (ZF_cs addSIs [flip_in_quniv]) 1);
by (etac RepFunE 1);
by (etac LList.elim 1);
by (asm_simp_tac flip_ss 1);
by (asm_simp_tac flip_ss 1);
by (fast_tac (ZF_cs addSIs [not_type]) 1);
val flip_type = result();

val [prem] = goal LListFn.thy
    "l : llist(bool) ==> flip(flip(l)) = l";
by (res_inst_tac [("X1", "{<flip(flip(l)),l> . l:llist(bool)}")]
       (LList_Eq.coinduct RS lleq_implies_equal) 1);
by (rtac (prem RS RepFunI) 1);
by (fast_tac (ZF_cs addSIs [flip_type]) 1);
by (etac RepFunE 1);
by (etac LList.elim 1);
by (asm_simp_tac flip_ss 1);
by (asm_simp_tac (flip_ss addsimps [flip_type, not_not]) 1);
by (fast_tac (ZF_cs addSIs [not_type]) 1);
val flip_flip = result();
