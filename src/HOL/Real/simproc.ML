(*  Title:      HOL/Real/simproc.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Apply Abel_Cancel to the reals
*)

(*** Two lemmas needed for the simprocs ***)

(*Deletion of other terms in the formula, seeking the -x at the front of z*)
Goal "((x::real) + (y + z) = y + u) = ((x + z) = u)";
by (stac real_add_left_commute 1);
by (rtac real_add_left_cancel 1);
qed "real_add_cancel_21";

(*A further rule to deal with the case that
  everything gets cancelled on the right.*)
Goal "((x::real) + (y + z) = y) = (x = -z)";
by (stac real_add_left_commute 1);
by (res_inst_tac [("t", "y")] (real_add_zero_right RS subst) 1
    THEN stac real_add_left_cancel 1);
by (simp_tac (simpset() addsimps [real_eq_diff_eq RS sym]) 1);
qed "real_add_cancel_end";


structure Real_Cancel_Data =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection

  val thy		= RealDef.thy
  val T			= Type ("RealDef.real", [])
  val zero		= Const ("RealDef.0r", T)
  val restrict_to_left  = restrict_to_left
  val add_cancel_21	= real_add_cancel_21
  val add_cancel_end	= real_add_cancel_end
  val add_left_cancel	= real_add_left_cancel
  val add_assoc		= real_add_assoc
  val add_commute	= real_add_commute
  val add_left_commute	= real_add_left_commute
  val add_0		= real_add_zero_left
  val add_0_right	= real_add_zero_right

  val eq_diff_eq	= real_eq_diff_eq
  val eqI_rules		= [real_less_eqI, real_eq_eqI, real_le_eqI]
  fun dest_eqI th = 
      #1 (HOLogic.dest_bin "op =" HOLogic.boolT 
	      (HOLogic.dest_Trueprop (concl_of th)))

  val diff_def		= real_diff_def
  val minus_add_distrib	= real_minus_add_distrib
  val minus_minus	= real_minus_minus
  val minus_0		= real_minus_zero
  val add_inverses	= [real_add_minus, real_add_minus_left];
  val cancel_simps	= [real_add_minus_cancel, real_minus_add_cancel]
end;

structure Real_Cancel = Abel_Cancel (Real_Cancel_Data);

Addsimprocs [Real_Cancel.sum_conv, Real_Cancel.rel_conv];

