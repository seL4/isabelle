(*  Title:      Pure/pure_syn.ML
    Author:     Makarius

Outer syntax for bootstrapping Isabelle/Pure.
*)

structure Pure_Syn: sig end =
struct

val _ =
  Outer_Syntax.markup_command Outer_Syntax.Markup ("header", @{here}) "theory header"
    (Parse.document_source >> Thy_Output.header_markup);

val _ =
  Outer_Syntax.markup_command Outer_Syntax.Markup ("chapter", @{here}) "chapter heading"
    (Parse.opt_target -- Parse.document_source >> Thy_Output.heading_markup);

val _ =
  Outer_Syntax.markup_command Outer_Syntax.Markup ("section", @{here}) "section heading"
    (Parse.opt_target -- Parse.document_source >> Thy_Output.heading_markup);

val _ =
  Outer_Syntax.markup_command Outer_Syntax.Markup ("subsection", @{here}) "subsection heading"
    (Parse.opt_target -- Parse.document_source >> Thy_Output.heading_markup);

val _ =
  Outer_Syntax.markup_command Outer_Syntax.Markup ("subsubsection", @{here}) "subsubsection heading"
    (Parse.opt_target -- Parse.document_source >> Thy_Output.heading_markup);

val _ =
  Outer_Syntax.command ("theory", @{here}) "begin theory"
    (Thy_Header.args >>
      (fn _ => Toplevel.init_theory (fn () => error "Missing theory initialization")));

end;

