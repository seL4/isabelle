(*  Title:      HOLCF/IOA/meta_theory/Deadlock.ML
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1997 TU Muenchen

Deadlock freedom of I/O Automata
*)   

(********************************************************************************
               input actions may always be added to a schedule
**********************************************************************************)

goal thy "!! sch. [| Filter (%x.x:act A)`sch : schedules A; a:inp A; IOA A; Finite sch|] \
\         ==> Filter (%x.x:act A)`sch @@ a>>nil : schedules A";
by (asm_full_simp_tac (!simpset addsimps [schedules_def,has_schedule_def]) 1);
by (safe_tac set_cs);
by (forward_tac  [inp_is_act] 1);
by (asm_full_simp_tac (!simpset addsimps [executions_def]) 1);
by (pair_tac "ex" 1);
ren "sch s ex" 1;
by (subgoal_tac "Finite ex" 1);
by (asm_full_simp_tac (!simpset addsimps [filter_act_def]) 2);
br (Map2Finite RS iffD1) 2;
by (res_inst_tac [("t","Map fst`ex")] subst 2);
ba 2;
be FiniteFilter 2;
(* subgoal 1 *)
by (forward_tac [exists_laststate] 1);
be allE 1;
be exE 1;
(* using input-enabledness *)
by (asm_full_simp_tac (!simpset addsimps [ioa_def,input_enabled_def]) 1);
by (REPEAT (etac conjE 1));
by (eres_inst_tac [("x","a")] allE 1);
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("x","u")] allE 1);
be exE 1;
(* instantiate execution *)
by (res_inst_tac [("x","(s,ex @@ (a,s2)>>nil)")] exI 1);
by (asm_full_simp_tac (!simpset addsimps [filter_act_def,MapConc]) 1);
by (eres_inst_tac [("t","u")] lemma_2_1 1);
by (Asm_full_simp_tac 1);
br sym 1;
ba 1;
qed"scheds_input_enabled";

(********************************************************************************
               Deadlock freedom: component B cannot block an out or int action
                                 of component A in every schedule
    Needs compositionality on schedule level, input-enabledness, compatibility
                    and distributivity of is_exec_frag over @@
**********************************************************************************)

goal thy "!! sch. [| a : local A; Finite sch; sch : schedules (A||B); \
\            Filter (%x.x:act A)`(sch @@ a>>nil) : schedules A; compatible A B; IOA B |] \
\          ==> (sch @@ a>>nil) : schedules (A||B)";

by (asm_full_simp_tac (!simpset addsimps [compositionality_sch,locals_def]) 1);
br conjI 1;
(* a : act (A||B) *)
by (asm_full_simp_tac (!simpset addsimps [actions_of_par]) 2);
br disjI1 2;
be disjE 2;
be int_is_act 2;
be out_is_act 2;
(* Filter B (sch@@[a]) : schedules B *)

by (case_tac "a:int A" 1);
bd intA_is_not_actB 1;
ba 1;  (* --> a~:act B *)
by (Asm_full_simp_tac 1);

(* case a~:int A , i.e. a:out A *)
by (case_tac "a~:act B" 1);
by (Asm_full_simp_tac 1);
(* case a:act B *)
by (Asm_full_simp_tac 1);
by (subgoal_tac "a:out A" 1);
by (Fast_tac 2);
bd  outAactB_is_inpB 1;
ba 1;
ba 1;
br scheds_input_enabled 1;
by (Asm_full_simp_tac 1);
by (REPEAT (atac 1));
qed"IOA_deadlock_free";





