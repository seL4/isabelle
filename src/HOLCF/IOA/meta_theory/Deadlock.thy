(*  Title:      HOLCF/IOA/meta_theory/Deadlock.thy
    ID:         $Id$
    Author:     Olaf Müller
*)

header {* Deadlock freedom of I/O Automata *}

theory Deadlock
imports RefCorrectness CompoScheds
begin

text {* input actions may always be added to a schedule *}

lemma scheds_input_enabled:
  "[| Filter (%x. x:act A)$sch : schedules A; a:inp A; input_enabled A; Finite sch|]  
          ==> Filter (%x. x:act A)$sch @@ a>>nil : schedules A"
apply (simp add: schedules_def has_schedule_def)
apply (tactic "safe_tac set_cs")
apply (frule inp_is_act)
apply (simp add: executions_def)
apply (tactic {* pair_tac "ex" 1 *})
apply (rename_tac s ex)
apply (subgoal_tac "Finite ex")
prefer 2
apply (simp add: filter_act_def)
defer
apply (rule_tac [2] Map2Finite [THEN iffD1])
apply (rule_tac [2] t = "Map fst$ex" in subst)
prefer 2 apply (assumption)
apply (erule_tac [2] FiniteFilter)
(* subgoal 1 *)
apply (frule exists_laststate)
apply (erule allE)
apply (erule exE)
(* using input-enabledness *)
apply (simp add: input_enabled_def)
apply (erule conjE)+
apply (erule_tac x = "a" in allE)
apply simp
apply (erule_tac x = "u" in allE)
apply (erule exE)
(* instantiate execution *)
apply (rule_tac x = " (s,ex @@ (a,s2) >>nil) " in exI)
apply (simp add: filter_act_def MapConc)
apply (erule_tac t = "u" in lemma_2_1)
apply simp
apply (rule sym)
apply assumption
done

text {*
               Deadlock freedom: component B cannot block an out or int action
                                 of component A in every schedule.
    Needs compositionality on schedule level, input-enabledness, compatibility
                    and distributivity of is_exec_frag over @@
*}

declare split_if [split del]
lemma IOA_deadlock_free: "[| a : local A; Finite sch; sch : schedules (A||B);  
             Filter (%x. x:act A)$(sch @@ a>>nil) : schedules A; compatible A B; input_enabled B |]  
           ==> (sch @@ a>>nil) : schedules (A||B)"
apply (simp add: compositionality_sch locals_def)
apply (rule conjI)
(* a : act (A||B) *)
prefer 2
apply (simp add: actions_of_par)
apply (blast dest: int_is_act out_is_act)

(* Filter B (sch@@[a]) : schedules B *)

apply (case_tac "a:int A")
apply (drule intA_is_not_actB)
apply (assumption) (* --> a~:act B *)
apply simp

(* case a~:int A , i.e. a:out A *)
apply (case_tac "a~:act B")
apply simp
(* case a:act B *)
apply simp
apply (subgoal_tac "a:out A")
prefer 2 apply (blast)
apply (drule outAactB_is_inpB)
apply assumption
apply assumption
apply (rule scheds_input_enabled)
apply simp
apply assumption+
done

declare split_if [split]

end
