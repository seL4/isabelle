(*  Title: 	ZF/ex/llist-fn.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Functions for Lazy Lists in Zermelo-Fraenkel Set Theory 
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
by (rtac (singletonI RS LList.co_induct) 1);
by (fast_tac (ZF_cs addSIs [lconst_in_quniv]) 1);
by (fast_tac (ZF_cs addSIs [lconst]) 1);
val lconst_type = result();
