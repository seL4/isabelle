(*  Title:      HOL/ex/Commands.thy
    Author:     Makarius
*)

section \<open>Some Isar command definitions\<close>

theory Commands
imports Main
keywords
  "print_test" :: diag and
  "global_test" :: thy_decl and
  "local_test" :: thy_decl
begin

subsection \<open>Diagnostic command: no state change\<close>

ML \<open>
  Outer_Syntax.command @{command_spec "print_test"} "print term test"
    (Parse.term >> (fn s => Toplevel.keep (fn st =>
      let
        val ctxt = Toplevel.context_of st;
        val t = Syntax.read_term ctxt s;
      in Pretty.writeln (Syntax.pretty_term ctxt t) end)));
\<close>

print_test x
print_test "\<lambda>x. x = a"


subsection \<open>Old-style global theory declaration\<close>

ML \<open>
  Outer_Syntax.command @{command_spec "global_test"} "test constant declaration"
    (Parse.binding >> (fn b => Toplevel.theory (fn thy =>
      let
        val thy' = Sign.add_consts [(b, @{typ 'a}, NoSyn)] thy;
      in thy' end)));
\<close>

global_test a
global_test b
print_test a


subsection \<open>Local theory specification\<close>

ML \<open>
  Outer_Syntax.local_theory @{command_spec "local_test"} "test local definition"
    (Parse.binding -- (@{keyword "="} |-- Parse.term) >> (fn (b, s) => fn lthy =>
      let
        val t = Syntax.read_term lthy s;
        val (def, lthy') = Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, []), t)) lthy;
      in lthy' end));
\<close>

local_test true = True
print_test true
thm true_def

local_test identity = "\<lambda>x. x"
print_test "identity x"
thm identity_def

context fixes x y :: nat
begin

local_test test = "x + y"
print_test test
thm test_def

end

print_test "test 0 1"
thm test_def

end
