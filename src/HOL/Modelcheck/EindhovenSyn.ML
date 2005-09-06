(*  Title:      HOL/Modelcheck/EindhovenSyn.ML
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

fun mc_eindhoven_tac i state = SUBGOAL (fn (goal, _) =>
  let
    val thy = Thm.theory_of_thm state;
    val assertion = mc_eindhoven_oracle thy (Logic.strip_imp_concl goal);
  in cut_facts_tac [assertion] i THEN atac i end) i state;

Goalw [split_def] "(f::'a*'b=>'c) = (%(x, y). f (x, y))";
  by (rtac ext 1);
  by (stac (surjective_pairing RS sym) 1);
  by (rtac refl 1);
qed "pair_eta_expand";

val pair_eta_expand_proc =
  Simplifier.simproc (the_context ()) "pair_eta_expand" ["f::'a*'b=>'c"]
  (fn _ => fn _ => fn t => case t of Abs _ => SOME (mk_meta_eq pair_eta_expand) | _ => NONE);

val Eindhoven_ss =
  simpset() addsimprocs [pair_eta_expand_proc] addsimps [Let_def];

(*check if user has pmu installed*)
fun eindhoven_enabled () = getenv "EINDHOVEN_HOME" <> "";
fun if_eindhoven_enabled f x = if eindhoven_enabled () then f x else ();
