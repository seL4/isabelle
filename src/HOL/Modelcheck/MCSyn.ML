(*  Title:      HOL/Modelcheck/MCSyn.ML
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

fun mc_tac i state = 
let val sign = #sign (rep_thm state)
in 
case drop(i-1,prems_of state) of
   [] => Sequence.null |
   subgoal::_ => 
	let val concl = Logic.strip_imp_concl subgoal;
	    val OraAss = invoke_oracle(MCSyn.thy,sign,MCOracleExn concl);
	in
	((cut_facts_tac [OraAss] i) THEN (atac i)) state
        end
end;


goal Prod.thy "(? x. P x) = (? a b. P(a,b))";
by (Auto_tac());
by (split_all_tac 1);
by (Auto_tac());
qed "split_paired_Ex";


goalw thy [split_def] "(f::'a*'b=>'c) = (%(x, y). f (x, y))";
  by (rtac ext 1);
  by (stac (surjective_pairing RS sym) 1);
  by (rtac refl 1);
qed "pair_eta_expand";

local
  val lhss = [cterm_of (sign_of thy) (read "f::'a*'b=>'c")];
  val rew = mk_meta_eq pair_eta_expand;

  fun proc _ (Abs _) = Some rew
    | proc _ _ = None;
in
  val pair_eta_expand_proc = Simplifier.mk_simproc "pair_eta_expand" lhss proc;
end;


val MC_ss = (!simpset addsimprocs [pair_eta_expand_proc]) 
                      addsimps [split_paired_Ex,Let_def];
