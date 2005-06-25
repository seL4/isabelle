(*  Title:      HOL/OrderedGroup.ML
    ID:         $Id$
    Author:     Steven Obua, Tobias Nipkow, Technische Universität München
*)

structure ab_group_add_cancel_data :> ABEL_CANCEL  = 
struct

(*** Term order for abelian groups ***)

fun agrp_ord a = find_index_eq a ["0", "op +", "uminus", "op -"];

fun termless_agrp (a, b) = (Term.term_lpo agrp_ord (a, b) = LESS);

val cancel_ss = HOL_basic_ss settermless termless_agrp addsimps
  [thm "add_assoc", thm "add_commute", thm "add_left_commute",
   thm "add_0", thm "add_0_right",
   thm "diff_def", thm "minus_add_distrib",
   thm "minus_minus", thm "minus_zero",
   thm "right_minus", thm "left_minus",
   thm "add_minus_cancel", thm "minus_add_cancel"];
  
  val eq_reflection = thm "eq_reflection"
  
  val thy_ref = Theory.self_ref (theory "OrderedGroup")

  val T = TFree("'a", ["OrderedGroup.ab_group_add"])

  val eqI_rules = [thm "less_eqI", thm "le_eqI", thm "eq_eqI"]
  fun dest_eqI th = 
      #1 (HOLogic.dest_bin "op =" HOLogic.boolT 
	      (HOLogic.dest_Trueprop (concl_of th)))  
end;

structure ab_group_add_cancel = Abel_Cancel (ab_group_add_cancel_data);

Addsimprocs [ab_group_add_cancel.sum_conv, ab_group_add_cancel.rel_conv];
