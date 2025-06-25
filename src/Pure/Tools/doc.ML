(*  Title:      Pure/Tools/doc.ML
    Author:     Makarius

Access to Isabelle documentation.
*)

signature DOC =
sig
  val names: unit -> string list
  val check: Proof.context -> string * Position.T -> string
end;

structure Doc: DOC =
struct

fun names () = split_lines (\<^scala>\<open>doc_names\<close> ML_System.platform);

fun check ctxt arg =
  Completion.check_item "documentation" (Markup.doc o #1)
    (map (rpair ()) (names ())) ctxt arg;

val _ =
  Theory.setup
   (Document_Output.antiquotation_verbatim_embedded \<^binding>\<open>doc\<close>
      (Scan.lift Parse.embedded_position) check);

end;
