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
    (Symtab.empty: (string * (Toplevel.state -> string)) Symtab.table);

fun report () =
  Output.try_protocol_message Markup.print_operations
    let
      val yxml =
        Symtab.fold (fn (x, (y, _)) => cons (x, y)) (Synchronized.value print_operations) []
        |> sort_wrt #1
        |> let open XML.Encode in list (pair string string) end
        |> YXML.string_of_body;
    in [yxml] end;

val _ = Isabelle_Process.protocol_command "print_operations" (fn [] => report ());

val _ = Session.protocol_handler "isabelle.Print_Operation$Handler";

in

fun register name description pr =
 (Synchronized.change print_operations (fn tab =>
   (if not (Symtab.defined tab name) then ()
    else warning ("Redefining print operation: " ^ quote name);
    Symtab.update (name, (description, pr)) tab));
  report ());

val _ =
  Query_Operation.register "print_operation" (fn {state, args, output_result} =>
    let
      val [name] = args;
      val pr =
        (case Symtab.lookup (Synchronized.value print_operations) name of
          SOME (_, pr) => pr
        | NONE => error ("Unknown print operation: " ^ quote name));
      val result = pr state handle Toplevel.UNDEF => error "Unknown context";
    in output_result result end);

end;


(* common print operations *)

val _ =
  register "facts" "print facts of proof context"
    (fn st =>
      Proof_Context.pretty_local_facts (Toplevel.context_of st) false
      |> Pretty.chunks |> Pretty.string_of);

end;

