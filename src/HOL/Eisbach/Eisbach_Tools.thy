(*  Title:      Eisbach_Tools.thy
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
      (if dummy orelse not (Method_Closure.is_dummy st) then tracing (print ctxt x) else ();
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
        Token.unparse tok ^ ": " ^ commas (map (Display.string_of_thm ctxt) thms)) #>
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

end
