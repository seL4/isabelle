(*  Title:      HOL/Subst/UTLemmas.ML
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For UTLemmas.thy.  
*)

open UTLemmas;

(***********)

val utlemmas_defs = [vars_of_def, occs_def];

local fun mk_thm s = prove_goalw UTLemmas.thy utlemmas_defs s 
                                 (fn _ => [Simp_tac 1])
in val utlemmas_rews = map mk_thm 
      ["vars_of(Const(c)) = {}",
       "vars_of(Var(x)) = {x}",
       "vars_of(Comb t u) = vars_of(t) Un vars_of(u)",
       "t <: Const(c) = False",
       "t <: Var(x) = False",
       "t <: Comb u v = (t=u | t=v | t <: u | t <: v)"];
end;

Addsimps (setplus_rews @ uterm_rews @ utlemmas_rews);

(****  occs irrefl ****)

goal UTLemmas.thy  "t <: u & u <: v --> t <: v";
by (uterm_ind_tac "v" 1);
by (ALLGOALS Simp_tac);
by (fast_tac HOL_cs 1);
val occs_trans  = store_thm("occs_trans", conjI RS (result() RS mp));

goal UTLemmas.thy   "~ t <: v --> ~ t <: u | ~ u <: v";
by (fast_tac (HOL_cs addIs [occs_trans]) 1);
val contr_occs_trans  = store_thm("contr_occs_trans", result() RS mp);

goal UTLemmas.thy   "t <: Comb t u";
by (Simp_tac 1);
qed "occs_Comb1";

goal UTLemmas.thy  "u <: Comb t u";
by (Simp_tac 1);
qed "occs_Comb2";

goal HOL.thy  "(~(P|Q)) = (~P & ~Q)";
by (fast_tac HOL_cs 1);
qed "demorgan_disj";

goal UTLemmas.thy  "~ t <: t";
by (uterm_ind_tac "t" 1);
by (ALLGOALS (simp_tac (!simpset addsimps [demorgan_disj])));
by (REPEAT (resolve_tac [impI,conjI] 1 ORELSE
            (etac contrapos 1 THEN etac subst 1 THEN 
             resolve_tac [occs_Comb1,occs_Comb2] 1) ORELSE
            (etac (contr_occs_trans RS disjE) 1 THEN assume_tac 2) ORELSE
            eresolve_tac ([occs_Comb1,occs_Comb2] RLN(2,[notE])) 1));
qed "occs_irrefl";

goal UTLemmas.thy  "t <: u --> ~t=u";
by (fast_tac (HOL_cs addEs [occs_irrefl RS notE]) 1);
val occs_irrefl2  = store_thm("occs_irrefl2", result() RS mp);


(**** vars_of lemmas  ****)

goal UTLemmas.thy "(v : vars_of(Var(w))) = (w=v)";
by (Simp_tac 1);
by (fast_tac HOL_cs 1);
qed "vars_var_iff";

goal UTLemmas.thy  "(x : vars_of(t)) = (Var(x) <: t | Var(x) = t)";
by (uterm_ind_tac "t" 1);
by (ALLGOALS Simp_tac);
by (fast_tac HOL_cs 1);
qed "vars_iff_occseq";
