(*  Title:      HOL/UNITY/Traces
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Definitions of
  * traces: the possible execution traces
  * reachable: the set of reachable states

*)


(*** The abstract type of programs ***)

Goalw [restrict_rel_def] "restrict_rel A Id = diag A";
by (Blast_tac 1);
qed "restrict_rel_Id";
Addsimps [restrict_rel_Id];

Goalw [restrict_rel_def] "restrict_rel A (diag B) = diag (A Int B)";
by (Blast_tac 1);
qed "restrict_rel_diag";
Addsimps [restrict_rel_diag];

Goalw [restrict_rel_def]
    "restrict_rel A (restrict_rel B r) = restrict_rel (A Int B) r";
by (Blast_tac 1);
qed "restrict_rel_restrict_rel";
Addsimps [restrict_rel_restrict_rel];

Goalw [restrict_rel_def] "restrict_rel A r <= A Times A";
by (Blast_tac 1);
qed "restrict_rel_subset";
Addsimps [restrict_rel_subset];

Goalw [restrict_rel_def]
    "((x,y) : restrict_rel A r) = ((x,y): r & x: A & y: A)";
by (Blast_tac 1);
qed "restrict_rel_iff";
Addsimps [restrict_rel_iff];

Goalw [restrict_rel_def] "r <= A Times A ==> restrict_rel A r = r";
by (Blast_tac 1);
qed "restrict_rel_eq";
Addsimps [restrict_rel_eq];

Goal "acts <= Pow (A Times A) ==> restrict_rel A `` acts = acts";
by Auto_tac;
by (rtac image_eqI 1);
by (assume_tac 2);
by (set_mp_tac 1);
by (Force_tac 1);
qed "restrict_rel_image";

Goalw [restrict_rel_def] "Domain (restrict_rel A r) <= A Int Domain r";
by (Blast_tac 1);
qed "Domain_restrict_rel";

Goalw [restrict_rel_def] "restrict_rel A r ^^ B <= A Int (r ^^ B)";
by (Blast_tac 1);
qed "Image_restrict_rel";

Addsimps [diag_iff];

val rep_ss = simpset() addsimps 
                [Int_lower1, image_subset_iff, diag_subset_Times,
		 States_def, Init_def, Acts_def, 
		 mk_program_def, Program_def, Rep_Program, 
		 Rep_Program_inverse, Abs_Program_inverse];


(** Basic laws guaranteed by the abstract type "program" **)

Goal "Init F <= States F";
by (cut_inst_tac [("x", "F")] Rep_Program 1);
by (auto_tac (claset(), rep_ss));
qed "Init_subset_States";

Goal "Acts F <= Pow(States F Times States F)";
by (cut_inst_tac [("x", "F")] Rep_Program 1);
by (force_tac (claset(),rep_ss) 1);
qed "Acts_subset_Pow_States";

Goal "diag (States F) : Acts F";
by (cut_inst_tac [("x", "F")] Rep_Program 1);
by (auto_tac (claset(), rep_ss));
qed "diag_in_Acts";
AddIffs [diag_in_Acts];


(** Inspectors for type "program" **)

Goal "States (mk_program (states,init,acts)) = states";
by (auto_tac (claset(), rep_ss));
qed "States_eq";

Goal "Init (mk_program (states,init,acts)) = states Int init";
by (auto_tac (claset(), rep_ss));
qed "Init_eq";

Goal "Acts (mk_program (states,init,acts)) = \
\     insert (diag states) (restrict_rel states `` acts)";
by (auto_tac (claset(), rep_ss));
qed "Acts_eq_raw";

Goal "acts <= Pow(states Times states) \
\     ==> Acts (mk_program (states,init,acts)) = insert (diag states) acts";
by (asm_simp_tac (simpset() addsimps [Acts_eq_raw, restrict_rel_image]) 1);
qed "Acts_eq";

Addsimps [States_eq, Acts_eq, Init_eq];


(** The notation of equality for type "program" **)

Goal "[| States F = States G; Init F = Init G; Acts F = Acts G |] ==> F = G";
by (subgoals_tac ["EX x. Rep_Program F = x",
		  "EX x. Rep_Program G = x"] 1);
by (REPEAT (Blast_tac 2));
by (Clarify_tac 1);
by (auto_tac (claset(), rep_ss));
by (REPEAT (dres_inst_tac [("f", "Abs_Program")] arg_cong 1));
by (asm_full_simp_tac rep_ss 1);
qed "program_equalityI";

val [major,minor] =
Goal "[| F = G; \
\        [| States F = States G; Init F = Init G; Acts F = Acts G |] ==> P \
\     |] ==> P";
by (rtac minor 1);
by (auto_tac (claset(), simpset() addsimps [major]));
qed "program_equalityE";

(*** These rules allow "lazy" definition expansion 
     They avoid expanding the full program, which is a large expression
***)

Goal "[| F == mk_program (states,init,acts) |] \
\     ==> States F = states";
by Auto_tac;
qed "def_prg_States";

Goal "[| F == mk_program (states,init,acts); init <= states |] \
\     ==> Init F = init";
by Auto_tac;
qed "def_prg_Init";

Goal "[| F == mk_program (states,init,acts); \
\        acts <= Pow(states Times states) |] \
\     ==> Acts F = insert (diag states) acts";
by (asm_simp_tac (simpset() addsimps [restrict_rel_image]) 1);
qed "def_prg_Acts";

(*The program is not expanded, but its Init and Acts are*)
Goal "[| F == mk_program (states,init,acts); \
\        init <= states;  acts <= Pow(states Times states) |] \
\     ==> Init F = init & Acts F = insert (diag states) acts";
by (asm_simp_tac (HOL_ss addsimps [def_prg_Init, def_prg_Acts]) 1);
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

Goal "reachable F <= States F";
by Safe_tac;
by (etac reachable.induct 1);
by (blast_tac (claset() addDs [impOfSubs Acts_subset_Pow_States]) 2);
by (blast_tac (claset() addIs [impOfSubs Init_subset_States]) 1);
qed "reachable_subset_States";

Goal "reachable F = {s. EX evs. (s,evs): traces (Init F) (Acts F)}";
by Safe_tac;
by (etac traces.induct 2);
by (etac reachable.induct 1);
by (ALLGOALS (blast_tac (claset() addIs reachable.intrs @ traces.intrs)));
qed "reachable_equiv_traces";
