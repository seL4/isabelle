(*  Title:      TLA/cladata.ML
    Author:     Stephan Merz (mostly stolen from Isabelle/HOL)

Setting up the classical reasoner for TLA.

The classical prover for TLA uses a different hyp_subst_tac that substitutes 
somewhat more liberally for state variables. Unfortunately, this requires
either generating a new prover or redefining the basic proof tactics.
We take the latter approach, because otherwise there would be a type conflict
between standard HOL and TLA classical sets, and we would have to redefine
even more things (e.g., blast_tac), and try to keep track of which rules 
have been active in setting up a new default claset.

*)


(* Generate a different hyp_subst_tac
   that substitutes for x(s) if s is a bound variable of "world" type. 
   This is useful to solve equations that contain state variables.
*)

use "hypsubst.ML";           (* local version! *)

structure ActHypsubst_Data =
  struct
  structure Simplifier = Simplifier
  (*Take apart an equality judgement; otherwise raise Match!*)
  fun dest_eq (Const("Trueprop",_) $ (Const("op =",_)  $ t $ u)) = (t,u);
  val eq_reflection = eq_reflection
  val imp_intr = impI
  val rev_mp = rev_mp
  val subst = subst
  val sym = sym
  end;

structure ActHypsubst = ActHypsubstFun(ActHypsubst_Data);
open ActHypsubst;


(**
  Define the basic classical set and clasimpset for the action part of TLA.
  Add the new hyp_subst_tac to the wrapper (also for the default claset).
**)

val action_css = (HOL_cs addSIs [actionI,intI] addSEs [exE_prop] 
		  addDs  [actionD,intD] 
		  addSaltern ("action_hyp_subst_tac", action_hyp_subst_tac),
		 simpset());
val action_cs = op addss action_css;


AddSIs [actionI,intI];
AddDs  [actionD,intD];
Addss  (simpset());



