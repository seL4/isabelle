(*  Title:      HOL/Modelcheck/EindhovenSyn.ML
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)








fun mc_eindhoven_tac i state =
let val sign = #sign (rep_thm state)
in 
case drop(i-1,prems_of state) of
   [] => Seq.empty |
   subgoal::_ => 
	let val concl = Logic.strip_imp_concl subgoal;
	    val OraAss = invoke_oracle EindhovenSyn.thy "eindhoven_mc" (sign,EindhovenOracleExn concl);
	in
	((cut_facts_tac [OraAss] i) THEN (atac i)) state
        end
end;


Goalw [split_def] "(f::'a*'b=>'c) = (%(x, y). f (x, y))";
  by (rtac ext 1);
  by (stac (surjective_pairing RS sym) 1);
  by (rtac refl 1);
qed "pair_eta_expand";

local
  val lhss = [read_cterm (sign_of thy) ("f::'a*'b=>'c", TVar (("'a", 0), []))];
  val rew = mk_meta_eq pair_eta_expand;

  fun proc _ _ (Abs _) = Some rew
    | proc _ _ _ = None;
in
  val pair_eta_expand_proc = Simplifier.mk_simproc "pair_eta_expand" lhss proc;
end;


val Eindhoven_ss =
  simpset() addsimprocs [pair_eta_expand_proc]
    addsimps [split_paired_Ex, Let_def];
