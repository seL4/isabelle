(*  Title:      HOL/Integ/bin_simproc
    ID:         $Id$
    Author:    Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Installation of simprocs that work on numeric literals
*)


(** Combining of literal coefficients in sums of products **)

Goal "(x < y) = (x-y < (#0::int))";
by (simp_tac (simpset() addsimps zcompare_rls) 1);
qed "zless_iff_zdiff_zless_0";

Goal "(x = y) = (x-y = (#0::int))";
by (simp_tac (simpset() addsimps zcompare_rls) 1);
qed "eq_iff_zdiff_eq_0";

Goal "(x <= y) = (x-y <= (#0::int))";
by (simp_tac (simpset() addsimps zcompare_rls) 1);
qed "zle_iff_zdiff_zle_0";


structure Int_CC_Data : COMBINE_COEFF_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val thy	= Bin.thy
  val T		= Type ("IntDef.int", [])

  val trans		= trans
  val add_ac		= zadd_ac
  val diff_def		= zdiff_def
  val minus_add_distrib	= zminus_zadd_distrib
  val minus_minus	= zminus_zminus
  val mult_commute	= zmult_commute
  val mult_1_right	= zmult_1_right
  val add_mult_distrib = zadd_zmult_distrib2
  val diff_mult_distrib = zdiff_zmult_distrib2
  val mult_minus_right = zmult_zminus_right

  val rel_iff_rel_0_rls = [zless_iff_zdiff_zless_0, eq_iff_zdiff_eq_0, 
			   zle_iff_zdiff_zle_0]
  fun dest_eqI th = 
      #1 (HOLogic.dest_bin "op =" HOLogic.boolT 
	      (HOLogic.dest_Trueprop (concl_of th)))

end;

structure Int_CC = Combine_Coeff (Int_CC_Data);

Addsimprocs [Int_CC.sum_conv, Int_CC.rel_conv];


(** Constant folding for integer plus and times **)

(*We do not need
    structure Int_Plus_Assoc = Assoc_Fold (Int_Plus_Assoc_Data);
  because cancel_coeffs does the same thing*)

structure Int_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val thy    = Bin.thy
  val T	     = HOLogic.intT
  val plus   = Const ("op *", [HOLogic.intT,HOLogic.intT] ---> HOLogic.intT);
  val add_ac = zmult_ac
end;

structure Int_Times_Assoc = Assoc_Fold (Int_Times_Assoc_Data);

Addsimprocs [Int_Times_Assoc.conv];


(** The same for the naturals **)

structure Nat_Plus_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val thy    = Bin.thy
  val T	     = HOLogic.natT
  val plus   = Const ("op +", [HOLogic.natT,HOLogic.natT] ---> HOLogic.natT);
  val add_ac = add_ac
end;

structure Nat_Plus_Assoc = Assoc_Fold (Nat_Plus_Assoc_Data);

structure Nat_Times_Assoc_Data : ASSOC_FOLD_DATA =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection
  val thy    = Bin.thy
  val T	     = HOLogic.natT
  val plus   = Const ("op *", [HOLogic.natT,HOLogic.natT] ---> HOLogic.natT);
  val add_ac = mult_ac
end;

structure Nat_Times_Assoc = Assoc_Fold (Nat_Times_Assoc_Data);

Addsimprocs [Nat_Plus_Assoc.conv, Nat_Times_Assoc.conv];

