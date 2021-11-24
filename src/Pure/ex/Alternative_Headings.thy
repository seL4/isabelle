(*  Title:      Pure/ex/Alternative_Headings.thy
    Author:     Makarius
*)

chapter \<open>Alternative document headings\<close>

theory Alternative_Headings
  imports Pure
  keywords
    "chapter*" "section*" "subsection*" "subsubsection*" :: document_heading
begin

ML \<open>
local

fun alternative_heading name body =
  [XML.Elem (Markup.latex_heading (unsuffix "*" name) |> Markup.optional_argument "*", body)];

fun document_heading (name, pos) =
  Outer_Syntax.command (name, pos) (name ^ " heading")
    (Parse.opt_target -- Parse.document_source --| Scan.option (Parse.$$$ ";") >>
      Document_Output.document_output
        {markdown = false, markup = alternative_heading name});

val _ =
  List.app document_heading
   [\<^command_keyword>\<open>chapter*\<close>,
    \<^command_keyword>\<open>section*\<close>,
    \<^command_keyword>\<open>subsection*\<close>,
    \<^command_keyword>\<open>subsubsection*\<close>];

in end\<close>

end
