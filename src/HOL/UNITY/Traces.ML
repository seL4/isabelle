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


Goal "Id : Acts F";
by (cut_inst_tac [("x", "F")] Rep_Program 1);
by (auto_tac (claset(), rep_ss));
qed "Id_in_Acts";
AddIffs [Id_in_Acts];

Goal "insert Id (Acts F) = Acts F";
by (simp_tac (simpset() addsimps [insert_absorb, Id_in_Acts]) 1);
qed "insert_Id_Acts";
AddIffs [insert_Id_Acts];

(** Inspectors for type "program" **)

Goal "Init (mk_program (init,acts)) = init";
by (auto_tac (claset(), rep_ss));
qed "Init_eq";

Goal "Acts (mk_program (init,acts)) = insert Id acts";
by (auto_tac (claset(), rep_ss));
qed "Acts_eq";

Addsimps [Acts_eq, Init_eq];


(** The notation of equality for type "program" **)

Goal "[| Init F = Init G; Acts F = Acts G |] ==> F = G";
by (subgoals_tac ["EX x. Rep_Program F = x",
		  "EX x. Rep_Program G = x"] 1);
by (REPEAT (Blast_tac 2));
by (Clarify_tac 1);
by (auto_tac (claset(), rep_ss));
by (REPEAT (dres_inst_tac [("f", "Abs_Program")] arg_cong 1));
by (asm_full_simp_tac rep_ss 1);
qed "program_equalityI";

val [major,minor] =
Goal "[| F = G; [| Init F = Init G; Acts F = Acts G |] ==> P |] ==> P";
by (rtac minor 1);
by (auto_tac (claset(), simpset() addsimps [major]));
qed "program_equalityE";


(*** These rules allow "lazy" definition expansion 
     They avoid expanding the full program, which is a large expression
***)

Goal "F == mk_program (init,acts) ==> Init F = init";
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
Goal "[| act == {(s,s'). P s s'} |] ==> ((s,s') : act) = P s s'";
by Auto_tac;
qed "def_act_simp";

fun simp_of_act def = def RS def_act_simp;

(*A set is expanded only if an element is being tested against it*)
Goal "A == B ==> (x : A) = (x : B)";
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
