
(** Applying HypsubstFun to generate hyp_subst_tac **)
structure Hypsubst_Data =
struct
  structure Simplifier = Simplifier
  val dest_eq = FOLogic.dest_eq
  val dest_Trueprop = FOLogic.dest_Trueprop
  val dest_imp = FOLogic.dest_imp
  val eq_reflection = thm "eq_reflection"
  val rev_eq_reflection = thm "meta_eq_to_obj_eq"
  val imp_intr = thm "impI"
  val rev_mp = thm "rev_mp"
  val subst = thm "subst"
  val sym = thm "sym"
  val thin_refl = thm "thin_refl"
  val prop_subst = @{lemma "PROP P(t) ==> PROP prop (x = t ==> PROP P(x))"
                     by (unfold prop_def) (drule eq_reflection, unfold)}
end;

structure Hypsubst = HypsubstFun(Hypsubst_Data);
open Hypsubst;
