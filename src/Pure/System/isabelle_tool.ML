(*  Title:      Pure/System/isabelle_tool.ML
    Author:     Makarius

Support for Isabelle system tools.
*)

signature ISABELLE_TOOL =
sig
  val isabelle_tools: unit -> (string * Position.T) list
  val check: Proof.context -> string * Position.T -> string
end;

structure Isabelle_Tool: ISABELLE_TOOL =
struct

(* list tools *)

fun symbolic_file (a, b) =
  if a = Markup.fileN
  then (a, Path.explode b |> Path.implode_symbolic)
  else (a, b);

fun isabelle_tools () =
  \<^scala>\<open>isabelle_tools\<close> ""
  |> YXML.parse_body
  |> let open XML.Decode in list (pair string properties) end
  |> map (apsnd (map symbolic_file #> Position.of_properties));


(* check *)

fun check ctxt arg =
  Completion.check_item Markup.toolN
    (fn (name, pos) =>
      Markup.entity Markup.toolN name
      |> Markup.properties (Position.def_properties_of pos))
    (isabelle_tools ()) ctxt arg;

val _ =
  Theory.setup
   (Thy_Output.antiquotation_verbatim_embedded \<^binding>\<open>tool\<close>
      (Scan.lift Parse.embedded_position) check);

end;
