(*  Title:      HOL/IMP/Natural.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Larry Paulson, TUM
    Copyright   1996 TUM
*)

open Natural;

val evalc_elim_cases = map (evalc.mk_cases com.simps)
   ["<SKIP,s> -c-> t", "<x:=a,s> -c-> t", "<c1;c2, s> -c-> t",
    "<IF b THEN c1 ELSE c2, s> -c-> t"];

val evalc_WHILE_case = evalc.mk_cases com.simps "<WHILE b DO c,s> -c-> t";

val evalc_cs = set_cs addSEs evalc_elim_cases
                      addEs  [evalc_WHILE_case];

(* evaluation of com is deterministic *)
goal Natural.thy "!c s t. <c,s> -c-> t --> (!u. <c,s> -c-> u --> u=t)";
by (rtac evalc.mutual_induct 1);
by (eres_inst_tac [("V", "<?c,s2> -c-> s1")] thin_rl 7);
by (ALLGOALS (deepen_tac evalc_cs 4));
qed_spec_mp "com_det";
