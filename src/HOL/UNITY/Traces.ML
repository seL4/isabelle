(*  Title:      HOL/UNITY/Traces
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Definitions of
  * traces: the possible execution traces
  * reachable: the set of reachable states

*)


(*** The abstract type of programs ***)

val rep_ss = simpset() addsimps 
                [Init_def, Acts_def, mk_program_def, Program_def, Rep_Program, 
		 Rep_Program_inverse, Abs_Program_inverse];


Goal "Id: Acts F";
by (cut_inst_tac [("x", "F")] Rep_Program 1);
by (auto_tac (claset(), rep_ss));
qed "Id_in_Acts";
AddIffs [Id_in_Acts];


Goal "Init (mk_program (init,acts)) = init";
by (auto_tac (claset(), rep_ss));
qed "Init_eq";

Goal "Acts (mk_program (init,acts)) = insert Id acts";
by (auto_tac (claset(), rep_ss));
qed "Acts_eq";

Addsimps [Acts_eq, Init_eq];


Goal "[| Init F = Init G; Acts F = Acts G |] ==> F = G";
by (cut_inst_tac [("p", "Rep_Program F")] surjective_pairing 1);
by (auto_tac (claset(), rep_ss));
by (dres_inst_tac [("f", "Abs_Program")] arg_cong 1);
by (full_simp_tac (rep_ss addsimps [surjective_pairing RS sym]) 1);
qed "program_equalityI";

val [major,minor] =
Goal "[| F = G; [| Init F = Init G; Acts F = Acts G |] ==> P |] ==> P";
by (rtac minor 1);
by (auto_tac (claset(), simpset() addsimps [major]));
qed "program_equalityE";

(*** These rules allow "lazy" definition expansion ***)

(*The program is not expanded, but its Init is*)
val [rew] = goal thy
    "[| F == mk_program (init,acts) |] \
\    ==> Init F = init";
by (rewtac rew);
by Auto_tac;
qed "def_prg_Init";

(*The program is not expanded, but its Init and Acts are*)
val [rew] = goal thy
    "[| F == mk_program (init,acts) |] \
\    ==> Init F = init & Acts F = insert Id acts";
by (rewtac rew);
by Auto_tac;
qed "def_prg_simps";

(*An action is expanded only if a pair of states is being tested against it*)
val [rew] = goal thy
    "[| act == {(s,s'). P s s'} |] ==> ((s,s') : act) = P s s'";
by (rewtac rew);
by Auto_tac;
qed "def_act_simp";

fun simp_of_act def = def RS def_act_simp;

(*A set is expanded only if an element is being tested against it*)
val [rew] = goal thy
    "A == B ==> (x : A) = (x : B)";
by (rewtac rew);
by Auto_tac;
qed "def_set_simp";

fun simp_of_set def = def RS def_set_simp;


(*** traces and reachable ***)

Goal "reachable F = {s. EX evs. (s,evs): traces (Init F) (Acts F)}";
by Safe_tac;
by (etac traces.induct 2);
by (etac reachable.induct 1);
by (ALLGOALS (blast_tac (claset() addIs reachable.intrs @ traces.intrs)));
qed "reachable_equiv_traces";
