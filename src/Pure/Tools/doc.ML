(*  Title:      Pure/Tools/doc.ML
    Author:     Makarius

Access to Isabelle documentation.
*)

signature DOC =
sig
  val check: Proof.context -> string * Position.T -> string
end;

structure Doc: DOC =
struct

fun check ctxt arg =
  Completion.check_item "documentation" (Markup.doc o #1)
    (\<^scala>\<open>doc_names\<close> "" |> split_lines |> map (rpair ())) ctxt arg;

val _ =
  Theory.setup
   (Thy_Output.antiquotation_verbatim_embedded \<^binding>\<open>doc\<close>
      (Scan.lift Parse.embedded_position) check);

end;
