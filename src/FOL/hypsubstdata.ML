
(** Applying HypsubstFun to generate hyp_subst_tac **)
structure Hypsubst_Data =
  struct
  structure Simplifier = Simplifier
    (*These destructors  Match!*)
  fun dest_eq (Const("op =",T)  $ t $ u) = (t, u, domain_type T)
  val dest_Trueprop = FOLogic.dest_Trueprop
  val dest_imp = FOLogic.dest_imp
  val eq_reflection = eq_reflection
  val rev_eq_reflection = meta_eq_to_obj_eq
  val imp_intr = impI
  val rev_mp = rev_mp
  val subst = subst
  val sym = sym
  val thin_refl = prove_goal (the_context ())
		  "!!X. [|x=x; PROP W|] ==> PROP W" (K [atac 1]);
  end;

structure Hypsubst = HypsubstFun(Hypsubst_Data);
open Hypsubst;
