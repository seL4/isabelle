(*  Title:      HOL/UNITY/Traces
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Definitions of
  * traces: the possible execution traces
  * reachable: the set of reachable states

*)

Goal "reachable prg = {s. EX evs. (s,evs): traces (Init prg) (Acts prg)}";
by Safe_tac;
by (etac traces.induct 2);
be reachable.induct 1;
by (ALLGOALS (blast_tac (claset() addIs (reachable.intrs @ traces.intrs))));
qed "reachable_equiv_traces";

Goal "acts <= Acts prg ==> stable acts (reachable prg)";
by (blast_tac (claset() addIs ([stableI, constrainsI] @ reachable.intrs)) 1);
qed "stable_reachable";

Goal "(act : Acts(|Init=init, Acts=acts|)) = (act:acts)";
auto();
qed "Acts_eq";

Goal "(s : Init(|Init=init, Acts=acts|)) = (s:init)";
auto();
qed "Init_eq";

AddIffs [Acts_eq, Init_eq];
