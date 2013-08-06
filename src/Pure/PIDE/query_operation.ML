(*  Title:      Pure/PIDE/query_operation.ML
    Author:     Makarius

One-shot query operations via asynchronous print functions and temporary
document overlay.
*)

signature QUERY_OPERATION =
sig
  val register_parallel: string -> (Toplevel.state -> string list -> (unit -> string) list) -> unit
  val register: string -> (Toplevel.state -> string list -> string) -> unit
end;

structure Query_Operation: QUERY_OPERATION =
struct

fun register_parallel name f =
  Command.print_function name
    (fn {args = instance :: args, ...} =>
        SOME {delay = NONE, pri = 0, persistent = false,
          print_fn = fn _ => fn state =>
            let
              fun result s = Output.result [(Markup.instanceN, instance)] s;
              fun status m = result (Markup.markup_only m);
              fun error_msg exn =
                if Exn.is_interrupt exn then reraise exn
                else
                  XML.Elem ((Markup.errorN, []), [XML.Text (ML_Compiler.exn_message exn)])
                  |> YXML.string_of |> result;

              val _ = status Markup.running;
              val outputs = f state args handle exn => (error_msg exn; []);
              val _ = outputs |> Par_List.map (fn out =>
                (case Exn.capture out () of
                  Exn.Res s =>
                    result (YXML.string_of (XML.Elem ((Markup.writelnN, []), [XML.Text s])))
                | Exn.Exn exn => error_msg exn));
              val _ = status Markup.finished;
            in () end}
      | _ => NONE);

fun register name f =
  register_parallel name (fn st => fn args => [fn () => f st args]);

end;

