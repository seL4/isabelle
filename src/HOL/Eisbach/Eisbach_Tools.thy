(*  Title:      HOL/Eisbach/Eisbach_Tools.thy
    Author:     Daniel Matichuk, NICTA/UNSW

Usability tools for Eisbach.
*)

theory Eisbach_Tools
imports Eisbach
begin

ML \<open>
local

fun trace_method parser print =
  Scan.lift (Args.mode "dummy") -- parser >>
    (fn (dummy, x) => fn ctxt => SIMPLE_METHOD (fn st =>
      (if dummy orelse not (Method.detect_closure_state st)
       then tracing (print ctxt x) else ();
       all_tac st)));

fun setup_trace_method binding parser print =
  Method.setup binding
    (trace_method parser (fn ctxt => fn x => Binding.name_of binding ^ ": " ^ print ctxt x))
    "";

in

val _ =
  Theory.setup
   (setup_trace_method @{binding print_fact}
      (Scan.lift (Scan.ahead Parse.not_eof) -- Attrib.thms)
      (fn ctxt => fn (tok, thms) =>
        (* FIXME proper formatting!? *)
        Token.unparse tok ^ ": " ^ commas (map (Thm.string_of_thm ctxt) thms)) #>
    setup_trace_method @{binding print_term}
      (Scan.lift (Scan.ahead Parse.not_eof) -- Args.term)
      (fn ctxt => fn (tok, t) =>
        (* FIXME proper formatting!? *)
        Token.unparse tok ^ ": " ^ Syntax.string_of_term ctxt t) #>
    setup_trace_method @{binding print_type}
      (Scan.lift (Scan.ahead Parse.not_eof) -- Args.typ)
      (fn ctxt => fn (tok, t) =>
        (* FIXME proper formatting!? *)
        Token.unparse tok ^ ": " ^ Syntax.string_of_typ ctxt t));

end
\<close>

ML \<open>
  fun try_map v seq =
    (case try Seq.pull seq of
      SOME (SOME (x, seq')) => Seq.make (fn () => SOME(x, try_map v seq'))
    | SOME NONE => Seq.empty
    | NONE => v);
\<close>

method_setup catch = \<open>
  Method.text_closure -- Method.text_closure >>
    (fn (text, text') => fn ctxt => fn using => fn st =>
      let
        val method = Method.evaluate_runtime text ctxt using;
        val backup_results = Method.evaluate_runtime text' ctxt using st;
      in
        (case try method st of
          SOME seq => try_map backup_results seq
        | NONE => backup_results)
      end)
\<close>

ML \<open>
  fun uncurry_rule thm = Conjunction.uncurry_balanced (Thm.nprems_of thm) thm;
  fun curry_rule thm =
    if Thm.no_prems thm then thm
    else
      let val conjs = Logic.dest_conjunctions (Thm.major_prem_of thm);
      in Conjunction.curry_balanced (length conjs) thm end;
\<close>

attribute_setup uncurry = \<open>Scan.succeed (Thm.rule_attribute [] (K uncurry_rule))\<close>
attribute_setup curry = \<open>Scan.succeed (Thm.rule_attribute [] (K curry_rule))\<close>

end
