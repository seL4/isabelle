(*  Title:      HOL/OrderedGroup.ML
    ID:         $Id$
    Author:     Steven Obua, Technische Universität München
*)

structure ab_group_add_cancel_data :> ABEL_CANCEL  = 
struct
  val ss = simpset_of HOL.thy
  val eq_reflection = thm "eq_reflection"
  
  val sg_ref = Sign.self_ref (sign_of (theory "OrderedGroup"))

  val T = TFree("'a", ["OrderedGroup.ab_group_add"])
  
  val restrict_to_left = thm "restrict_to_left"
  val add_cancel_21 = thm "add_cancel_21"
  val add_cancel_end = thm "add_cancel_end"
  val add_left_cancel = thm "add_left_cancel"
  val add_assoc = thm "add_assoc"
  val add_commute = thm "add_commute"
  val add_left_commute = thm "add_left_commute"
  val add_0 = thm "add_0"
  val add_0_right = thm "add_0_right"
  
  val eq_diff_eq = thm "eq_diff_eq"
  
  val eqI_rules = [thm "less_eqI", thm "le_eqI", thm "eq_eqI"]
  fun dest_eqI th = 
      #1 (HOLogic.dest_bin "op =" HOLogic.boolT 
	      (HOLogic.dest_Trueprop (concl_of th)))  

  val diff_def		= thm "diff_def"
  val minus_add_distrib	= thm "minus_add_distrib"
  val minus_minus	= thm "minus_minus"
  val minus_0		= thm "minus_zero"
  val add_inverses	= [thm "right_minus", thm "left_minus"]
  val cancel_simps	= [thm "add_minus_cancel", thm "minus_add_cancel"]
end;

structure ab_group_add_cancel = Abel_Cancel (ab_group_add_cancel_data);

Addsimprocs [ab_group_add_cancel.sum_conv, ab_group_add_cancel.rel_conv];
