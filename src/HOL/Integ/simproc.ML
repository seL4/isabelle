(*  Title:      HOL/Integ/simproc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Apply Abel_Cancel to the integers
*)


(*** Lemmas needed for the simprocs ***)

(*Deletion of other terms in the formula, seeking the -x at the front of z*)
Goal "((x::int) + (y + z) = y + u) = ((x + z) = u)";
by (stac zadd_left_commute 1);
by (rtac zadd_left_cancel 1);
qed "zadd_cancel_21";

(*A further rule to deal with the case that
  everything gets cancelled on the right.*)
Goal "((x::int) + (y + z) = y) = (x = -z)";
by (stac zadd_left_commute 1);
by (res_inst_tac [("t", "y")] (zadd_int0_right RS subst) 1
    THEN stac zadd_left_cancel 1);
by (simp_tac (simpset() addsimps [eq_zdiff_eq RS sym]) 1);
qed "zadd_cancel_end";




structure Int_Cancel_Data =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection

  val thy	= IntDef.thy
  val T		= HOLogic.intT
  val zero	= Const ("IntDef.int", HOLogic.natT --> T) $ HOLogic.zero
  val restrict_to_left  = restrict_to_left
  val add_cancel_21	= zadd_cancel_21
  val add_cancel_end	= zadd_cancel_end
  val add_left_cancel	= zadd_left_cancel
  val add_assoc		= zadd_assoc
  val add_commute	= zadd_commute
  val add_left_commute	= zadd_left_commute
  val add_0		= zadd_int0
  val add_0_right	= zadd_int0_right

  val eq_diff_eq	= eq_zdiff_eq
  val eqI_rules		= [zless_eqI, zeq_eqI, zle_eqI]
  fun dest_eqI th = 
      #1 (HOLogic.dest_bin "op =" HOLogic.boolT 
	      (HOLogic.dest_Trueprop (concl_of th)))

  val diff_def		= zdiff_def
  val minus_add_distrib	= zminus_zadd_distrib
  val minus_minus	= zminus_zminus
  val minus_0		= zminus_int0
  val add_inverses	= [zadd_zminus_inverse, zadd_zminus_inverse2];
  val cancel_simps	= [zadd_zminus_cancel, zminus_zadd_cancel]
end;

structure Int_Cancel = Abel_Cancel (Int_Cancel_Data);

Addsimprocs [Int_Cancel.sum_conv, Int_Cancel.rel_conv];


