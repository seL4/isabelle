(*  Title:      HOL/OrderedGroup.ML
    ID:         $Id$
    Author:     Steven Obua, Tobias Nipkow, Technische Universitaet Mnchen
*)

structure ab_group_add_cancel_data :> ABEL_CANCEL  = 
struct

(*** Term order for abelian groups ***)

fun agrp_ord a = find_index (fn a' => a = a') ["0", "HOL.plus", "HOL.uminus", "HOL.minus"];

fun termless_agrp (a, b) = (Term.term_lpo agrp_ord (a, b) = LESS);

local
  val ac1 = mk_meta_eq (thm "add_assoc");
  val ac2 = mk_meta_eq (thm "add_commute");
  val ac3 = mk_meta_eq (thm "add_left_commute");
  fun solve_add_ac thy _ (_ $ (Const ("HOL.plus",_) $ _ $ _) $ _) =
        SOME ac1
    | solve_add_ac thy _ (_ $ x $ (Const ("HOL.plus",_) $ y $ z)) =
        if termless_agrp (y, x) then SOME ac3 else NONE
    | solve_add_ac thy _ (_ $ x $ y) =
        if termless_agrp (y, x) then SOME ac2 else NONE
    | solve_add_ac thy _ _ = NONE
in
  val add_ac_proc = Simplifier.simproc (the_context ())
    "add_ac_proc" ["x + y::'a::ab_semigroup_add"] solve_add_ac;
end;

val cancel_ss = HOL_basic_ss settermless termless_agrp
  addsimprocs [add_ac_proc] addsimps
  [thm "add_0", thm "add_0_right",
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
