(*  Title:      Pure/PIDE/query_operation.ML
    Author:     Makarius

One-shot query operations via asynchronous print functions and temporary
document overlays.
*)

signature QUERY_OPERATION =
sig
  val register: {name: string, pri: int} ->
    ({state: Toplevel.state, args: string list,
      output_result: string list -> unit,
      writelns_result: string list -> unit,
      writeln_result: string -> unit} -> unit) -> unit
end;

structure Query_Operation: QUERY_OPERATION =
struct

fun register {name, pri} f =
  Command.print_function (name ^ "_query")
    (fn {args = instance :: args, ...} =>
      SOME {delay = NONE, pri = pri, persistent = false, strict = false,
        print_fn = fn _ => Thread_Attributes.uninterruptible (fn run => fn state =>
          let
            fun output_result ss = Output.result [(Markup.instanceN, instance)] ss;
            fun status m = output_result [YXML.output_markup_only m];
            fun writelns_result ss = output_result (Markup.markup_strings Markup.writeln ss);
            val writeln_result = writelns_result o single;
            fun toplevel_error exn =
              output_result [Markup.markup Markup.error (Runtime.exn_message exn)];

            val _ = status Markup.running;
            fun main () =
              f {state = state, args = args, output_result = output_result,
                  writelns_result = writelns_result, writeln_result = writeln_result};
            val _ =
              (case Exn.capture_body (*sic!*) (run main) of
                Exn.Res () => ()
              | Exn.Exn exn => toplevel_error exn);
            val _ = status Markup.finished;
          in () end)}
    | _ => NONE);

end;

(* print_state *)

val _ =
  Query_Operation.register {name = "print_state", pri = Task_Queue.urgent_pri}
    (fn {state = st, output_result, ...} =>
      if Toplevel.is_proof st
      then
        Toplevel.pretty_state st
        |> Pretty.chunks
        |> Pretty.strings_of
        |> Markup.markup_strings Markup.state
        |> output_result
      else ());
