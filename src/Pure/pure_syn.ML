(*  Title:      Pure/pure_syn.ML
    Author:     Makarius

Outer syntax for bootstrapping: commands that are accessible outside a
regular theory context.
*)

signature PURE_SYN =
sig
  val bootstrap_thy: theory
end;

structure Pure_Syn: PURE_SYN =
struct

fun document_heading (name, pos) =
  Outer_Syntax.command (name, pos) (name ^ " heading")
    (Parse.opt_target -- Parse.document_source --| Scan.option (Parse.$$$ ";") >>
      Document_Output.document_output
        {markdown = false, markup = fn body => [XML.Elem (Markup.latex_heading name, body)]});

fun document_body ((name, pos), description) =
  Outer_Syntax.command (name, pos) description
    (Parse.opt_target -- Parse.document_source >>
      Document_Output.document_output
        {markdown = true, markup = fn body => [XML.Elem (Markup.latex_body name, body)]});

val _ =
  List.app document_heading
   [("chapter", \<^here>),
    ("section", \<^here>),
    ("subsection", \<^here>),
    ("subsubsection", \<^here>),
    ("paragraph", \<^here>),
    ("subparagraph", \<^here>)];

val _ =
  List.app document_body
   [(("text", \<^here>), "formal comment (primary style)"),
    (("txt", \<^here>), "formal comment (secondary style)")];

val _ =
  Outer_Syntax.command ("text_raw", \<^here>) "LaTeX text (without surrounding environment)"
    (Parse.opt_target -- Parse.document_source >>
      Document_Output.document_output
        {markdown = true, markup = XML.enclose "%\n" "\n"});

val _ =
  Outer_Syntax.command ("theory", \<^here>) "begin theory"
    (Thy_Header.args >>
      (fn _ => Toplevel.init_theory (fn () => error "Missing theory initialization")));


val bootstrap_thy = Context.the_global_context ();

val _ = Theory.setup (Config.put_global Outer_Syntax.bootstrap false);

end;
