(*  Title:      HOL/SetInterval.ML
    ID:         $Id$
    Author:     Clemens Ballarin
    Copyright   2002  TU Muenchen
*)

(* Legacy ML bindings *)

val Compl_atLeast = thm "Compl_atLeast";
val Compl_atMost = thm "Compl_atMost";
val Compl_greaterThan = thm "Compl_greaterThan";
val Compl_lessThan = thm "Compl_lessThan";
val INT_greaterThan_UNIV = thm "INT_greaterThan_UNIV";
val UN_atLeast_UNIV = thm "UN_atLeast_UNIV";
val UN_atMost_UNIV = thm "UN_atMost_UNIV";
val UN_lessThan_UNIV = thm "UN_lessThan_UNIV";
val atLeastAtMost_def = thm "atLeastAtMost_def";
val atLeastAtMost_iff = thm "atLeastAtMost_iff";
val atLeastLessThan_def  = thm "atLeastLessThan_def";
val atLeastLessThan_iff = thm "atLeastLessThan_iff";
val atLeast_0 = thm "atLeast_0";
val atLeast_Suc = thm "atLeast_Suc";
val atLeast_def      = thm "atLeast_def";
val atLeast_iff = thm "atLeast_iff";
val atMost_0 = thm "atMost_0";
val atMost_Int_atLeast = thm "atMost_Int_atLeast";
val atMost_Suc = thm "atMost_Suc";
val atMost_def       = thm "atMost_def";
val atMost_iff = thm "atMost_iff";
val greaterThanAtMost_def  = thm "greaterThanAtMost_def";
val greaterThanAtMost_iff = thm "greaterThanAtMost_iff";
val greaterThanLessThan_def  = thm "greaterThanLessThan_def";
val greaterThanLessThan_iff = thm "greaterThanLessThan_iff";
val greaterThan_0 = thm "greaterThan_0";
val greaterThan_Suc = thm "greaterThan_Suc";
val greaterThan_def  = thm "greaterThan_def";
val greaterThan_iff = thm "greaterThan_iff";
val ivl_disj_int = thms "ivl_disj_int";
val ivl_disj_int_one = thms "ivl_disj_int_one";
val ivl_disj_int_singleton = thms "ivl_disj_int_singleton";
val ivl_disj_int_two = thms "ivl_disj_int_two";
val ivl_disj_un = thms "ivl_disj_un";
val ivl_disj_un_one = thms "ivl_disj_un_one";
val ivl_disj_un_singleton = thms "ivl_disj_un_singleton";
val ivl_disj_un_two = thms "ivl_disj_un_two";
val lessThan_0 = thm "lessThan_0";
val lessThan_Suc = thm "lessThan_Suc";
val lessThan_Suc_atMost = thm "lessThan_Suc_atMost";
val lessThan_def     = thm "lessThan_def";
val lessThan_iff = thm "lessThan_iff";
val single_Diff_lessThan = thm "single_Diff_lessThan";

val bounded_nat_set_is_finite = thm "bounded_nat_set_is_finite";
val finite_atMost = thm "finite_atMost";
val finite_lessThan = thm "finite_lessThan";
