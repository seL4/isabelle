(*  Title:      HOL/UNITY/Traces
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Definitions of
  * traces: the possible execution traces
  * reachable: the set of reachable states

*)

Goal "id: Acts prg";
by (simp_tac (simpset() addsimps [Acts_def]) 1);
qed "id_in_Acts";
AddIffs [id_in_Acts];



Goal "reachable prg = {s. EX evs. (s,evs): traces (Init prg) (Acts prg)}";
by Safe_tac;
by (etac traces.induct 2);
by (etac reachable.induct 1);
by (ALLGOALS (blast_tac (claset() addIs (reachable.intrs @ traces.intrs))));
qed "reachable_equiv_traces";

Goal "acts <= Acts prg ==> stable acts (reachable prg)";
by (blast_tac (claset() addIs ([stableI, constrainsI] @ reachable.intrs)) 1);
qed "stable_reachable";

Goalw [Acts_def]
     "(act : Acts(|Init=init, Acts0=acts|)) = (act=id | act : acts)";
by Auto_tac;
qed "Acts_eq";

Goal "(s : Init(|Init=init, Acts0=acts|)) = (s:init)";
by Auto_tac;
qed "Init_eq";

AddIffs [Acts_eq, Init_eq];


(*** These three rules allow "lazy" definition expansion ***)

val [rew] = goal thy
    "[| prg == (|Init=init, Acts0=acts|) |] \
\    ==> Init prg = init & Acts prg = insert id acts";
by (rewtac rew);
by Auto_tac;
qed "def_prg_simps";

val [rew] = goal thy
    "[| act == {(s,s'). P s s'} |] ==> ((s,s') : act) = P s s'";
by (rewtac rew);
by Auto_tac;
qed "def_act_simp";

fun simp_of_act def = def RS def_act_simp;

val [rew] = goal thy
    "[| A == B |] ==> (x : A) = (x : B)";
by (rewtac rew);
by Auto_tac;
qed "def_set_simp";

fun simp_of_set def = def RS def_set_simp;

