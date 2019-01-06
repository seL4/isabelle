(*  Title:      HOL/Eisbach/Eisbach.thy
    Author:     Daniel Matichuk, NICTA/UNSW

Main entry point for Eisbach proof method language.
*)

theory Eisbach
imports Pure
keywords
  "method" :: thy_decl and
  "conclusion"
  "declares"
  "methods"
  "\<bar>" "\<Rightarrow>"
  "uses"
begin

ML_file \<open>parse_tools.ML\<close>
ML_file \<open>method_closure.ML\<close>
ML_file \<open>eisbach_rule_insts.ML\<close>
ML_file \<open>match_method.ML\<close>


method solves methods m = (m; fail)

method repeat_new methods m = (m ; (repeat_new \<open>m\<close>)?)


section \<open>Debugging methods\<close>

method_setup print_raw_goal = \<open>Scan.succeed (fn ctxt => fn facts =>
  (fn (ctxt, st) => (
     Output.writeln (Thm.string_of_thm ctxt st);
     Seq.make_results (Seq.single (ctxt, st)))))\<close>

method_setup print_headgoal =
  \<open>Scan.succeed (fn ctxt => fn _ => fn (ctxt', thm) =>
    ((SUBGOAL (fn (t,_) =>
     (Output.writeln
     (Pretty.string_of (Syntax.pretty_term ctxt t)); all_tac)) 1 thm);
     (Seq.make_results (Seq.single (ctxt', thm)))))\<close>

ML \<open>fun method_evaluate text ctxt facts =
  Method.NO_CONTEXT_TACTIC ctxt
    (Method.evaluate_runtime text ctxt facts)\<close>

method_setup timeit =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun timed_tac st seq = Seq.make (fn () => Option.map (apsnd (timed_tac st))
       (timeit (fn () => (Seq.pull seq))));

     fun tac st' =
       timed_tac st' (method_evaluate m ctxt facts st');

   in SIMPLE_METHOD tac [] end)
\<close>


section \<open>Simple Combinators\<close>

method_setup defer_tac = \<open>Scan.succeed (fn _ => SIMPLE_METHOD (defer_tac 1))\<close>
method_setup prefer_last = \<open>Scan.succeed (fn _ => SIMPLE_METHOD (PRIMITIVE (Thm.permute_prems 0 ~1)))\<close>

method_setup all =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac i st' =
       Goal.restrict i 1 st'
       |> method_evaluate m ctxt facts
       |> Seq.map (Goal.unrestrict i)

   in SIMPLE_METHOD (ALLGOALS tac) facts end)
\<close>

method_setup determ =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (DETERM tac) facts end)
\<close>

method_setup changed =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (CHANGED tac) facts end)
\<close>


text \<open>The following \<open>fails\<close> and \<open>succeeds\<close> methods protect the goal from the effect
      of a method, instead simply determining whether or not it can be applied to the current goal.
      The \<open>fails\<close> method inverts success, only succeeding if the given method would fail.\<close>

method_setup fails =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun fail_tac st' =
       (case Seq.pull (method_evaluate m ctxt facts st') of
          SOME _ => Seq.empty
        | NONE => Seq.single st')

   in SIMPLE_METHOD fail_tac facts end)
\<close>

method_setup succeeds =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun can_tac st' =
       (case Seq.pull (method_evaluate m ctxt facts st') of
          SOME (st'',_) => Seq.single st'
        | NONE => Seq.empty)

   in SIMPLE_METHOD can_tac facts end)
\<close>



text \<open>Finding a goal based on successful application of a method\<close>

method_setup find_goal =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun prefer_first i = SELECT_GOAL
       (fn st' =>
         (case Seq.pull (method_evaluate m ctxt facts st') of
           SOME (st'',_) => Seq.single st''
         | NONE => Seq.empty)) i THEN prefer_tac i

   in SIMPLE_METHOD (FIRSTGOAL prefer_first) facts end)\<close>


end
