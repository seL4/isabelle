(*  Title:      Pure/Tools/print_operation.ML
    Author:     Makarius

Print operations as asynchronous query.
*)


signature PRINT_OPERATION =
sig
  val register: string -> string -> (Toplevel.state -> string) -> unit
end;

structure Print_Operation: PRINT_OPERATION =
struct

(* maintain print operations *)

local

val print_operations =
  Synchronized.var "print_operations"
    ([]: (string * (string * (Toplevel.state -> string))) list);

fun report () =
  Output.try_protocol_message Markup.print_operations
    let
      val yxml =
        Synchronized.value print_operations
        |> map (fn (x, (y, _)) => (x, y)) |> rev
        |> let open XML.Encode in list (pair string string) end
        |> YXML.string_of_body;
    in [yxml] end;

val _ = Isabelle_Process.protocol_command "print_operations" (fn [] => report ());

val _ = Session.protocol_handler "isabelle.Print_Operation$Handler";

in

fun register name description pr =
 (Synchronized.change print_operations (fn tab =>
   (if not (AList.defined (op =) tab name) then ()
    else warning ("Redefining print operation: " ^ quote name);
    AList.update (op =) (name, (description, pr)) tab));
  report ());

val _ =
  Query_Operation.register "print_operation" (fn {state, args, output_result} =>
    let
      val [name] = args;
      val pr =
        (case AList.lookup (op =) (Synchronized.value print_operations) name of
          SOME (_, pr) => pr
        | NONE => error ("Unknown print operation: " ^ quote name));
      val result = pr state handle Toplevel.UNDEF => error "Unknown context";
    in output_result result end);

end;


(* common print operations *)

val _ =
  register "context" "main context"
    (Pretty.string_of o Pretty.chunks o Toplevel.pretty_state_context);

val _ =
  register "cases" "cases of proof context"
    (Pretty.string_of o Pretty.chunks o Proof_Context.pretty_cases o Toplevel.context_of);

val _ =
  register "binds" "term bindings of proof context"
    (Pretty.string_of o Pretty.chunks o Proof_Context.pretty_binds o Toplevel.context_of);

val _ =
  register "facts" "facts of proof context"
    (fn st =>
      Proof_Context.pretty_local_facts (Toplevel.context_of st) false
      |> Pretty.chunks |> Pretty.string_of);

val _ =
  register "state" "proof state"
    (Pretty.string_of o Pretty.chunks o Toplevel.pretty_state true);

end;

