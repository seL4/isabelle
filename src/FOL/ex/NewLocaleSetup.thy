(*  Title:      FOL/ex/NewLocaleSetup.thy
    Author:     Clemens Ballarin, TU Muenchen

Testing environment for locale expressions --- experimental.
*)

theory NewLocaleSetup
imports FOL
begin

ML {*

local

structure P = OuterParse and K = OuterKeyword;
val opt_bang = Scan.optional (P.$$$ "!" >> K true) false;

val locale_val =
  SpecParse.locale_expression --
    Scan.optional (P.$$$ "+" |-- P.!!! (Scan.repeat1 SpecParse.context_element)) [] ||
  Scan.repeat1 SpecParse.context_element >> pair ([], []);

in

val _ =
  OuterSyntax.command "locale" "define named proof context" K.thy_decl
    (P.name -- Scan.optional (P.$$$ "=" |-- P.!!! locale_val) (([], []), []) -- P.opt_begin
      >> (fn ((name, (expr, elems)), begin) =>
          (begin ? Toplevel.print) o Toplevel.begin_local_theory begin
            (Expression.add_locale_cmd name name expr elems #>
              (fn ((target, notes), ctxt) => TheoryTarget.begin target ctxt |>
                fold (fn (kind, facts) => LocalTheory.notes kind facts #> snd) notes))));

val _ =
  OuterSyntax.improper_command "print_locales" "print locales of this theory" K.diag
    (Scan.succeed (Toplevel.no_timing o (Toplevel.unknown_theory o
  Toplevel.keep (NewLocale.print_locales o Toplevel.theory_of))));

val _ = OuterSyntax.improper_command "print_locale" "print named locale in this theory" K.diag
  (opt_bang -- P.xname >> (Toplevel.no_timing oo (fn (show_facts, name) =>
   Toplevel.unknown_theory o Toplevel.keep (fn state =>
     NewLocale.print_locale (Toplevel.theory_of state) show_facts name))));

val _ =
  OuterSyntax.command "interpretation"
    "prove interpretation of locale expression in theory" K.thy_goal
    (P.!!! SpecParse.locale_expression --
      Scan.optional (P.$$$ "where" |-- P.and_list1 (SpecParse.opt_thm_name ":" -- P.prop)) []
        >> (fn (expr, mixin) => Toplevel.print o
            Toplevel.theory_to_proof (Expression.interpretation_cmd expr mixin)));

val _ =
  OuterSyntax.command "interpret"
    "prove interpretation of locale expression in proof context"
    (K.tag_proof K.prf_goal)
    (P.!!! SpecParse.locale_expression
        >> (fn expr => Toplevel.print o
            Toplevel.proof' (fn int => Expression.interpret_cmd expr int)));

end

*}

end
