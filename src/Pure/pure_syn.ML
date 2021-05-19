(*  Title:      Pure/pure_syn.ML
    Author:     Makarius

Outer syntax for bootstrapping: commands that are accessible outside a
regular theory context.
*)

signature PURE_SYN =
sig
  val document_command: {markdown: bool} -> (xstring * Position.T) option * Input.source ->
    Toplevel.transition -> Toplevel.transition
  val bootstrap_thy: theory
end;

structure Pure_Syn: PURE_SYN =
struct

val semi = Scan.option (Parse.$$$ ";");

val output_document =
  Thy_Output.output_document_report o Toplevel.presentation_context;

fun document_command markdown (loc, txt) =
  Toplevel.keep (fn state =>
    (case loc of
      NONE => ignore (output_document state markdown txt)
    | SOME (_, pos) =>
        error ("Illegal target specification -- not a theory context" ^ Position.here pos))) o
  Toplevel.present_local_theory loc (fn state =>
    ignore (output_document state markdown txt));

val _ =
  Outer_Syntax.command ("chapter", \<^here>) "chapter heading"
    (Parse.opt_target -- Parse.document_source --| semi >> document_command {markdown = false});

val _ =
  Outer_Syntax.command ("section", \<^here>) "section heading"
    (Parse.opt_target -- Parse.document_source --| semi >> document_command {markdown = false});

val _ =
  Outer_Syntax.command ("subsection", \<^here>) "subsection heading"
    (Parse.opt_target -- Parse.document_source --| semi >> document_command {markdown = false});

val _ =
  Outer_Syntax.command ("subsubsection", \<^here>) "subsubsection heading"
    (Parse.opt_target -- Parse.document_source --| semi >> document_command {markdown = false});

val _ =
  Outer_Syntax.command ("paragraph", \<^here>) "paragraph heading"
    (Parse.opt_target -- Parse.document_source --| semi >> document_command {markdown = false});

val _ =
  Outer_Syntax.command ("subparagraph", \<^here>) "subparagraph heading"
    (Parse.opt_target -- Parse.document_source --| semi >> document_command {markdown = false});

val _ =
  Outer_Syntax.command ("text", \<^here>) "formal comment (primary style)"
    (Parse.opt_target -- Parse.document_source >> document_command {markdown = true});

val _ =
  Outer_Syntax.command ("txt", \<^here>) "formal comment (secondary style)"
    (Parse.opt_target -- Parse.document_source >> document_command {markdown = true});

val _ =
  Outer_Syntax.command ("text_raw", \<^here>) "LaTeX text (without surrounding environment)"
    (Parse.opt_target -- Parse.document_source >> document_command {markdown = true});

val _ =
  Outer_Syntax.command ("theory", \<^here>) "begin theory"
    (Thy_Header.args >>
      (fn _ => Toplevel.init_theory (fn () => error "Missing theory initialization")));


val bootstrap_thy = Context.the_global_context ();

val _ = Theory.setup (Config.put_global Outer_Syntax.bootstrap false);

end;
