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
        SOME {delay = NONE, pri = 0, persistent = false, strict = false,
          print_fn = fn _ => uninterruptible (fn restore_attributes => fn state =>
            let
              fun result s = Output.result [(Markup.instanceN, instance)] s;
              fun status m = result (Markup.markup_only m);
              fun toplevel_error exn =
                result (Markup.markup (Markup.errorN, []) (ML_Compiler.exn_message exn));

              val _ = status Markup.running;
              val outputs =
                Multithreading.interruptible (fn () => f state args) ()
                  handle exn (*sic!*) => (toplevel_error exn; []);
              val _ = outputs |> Par_List.map (fn out =>
                (case Exn.capture (restore_attributes out) () (*sic!*) of
                  Exn.Res s => result (Markup.markup (Markup.writelnN, []) s)
                | Exn.Exn exn => toplevel_error exn));
              val _ = status Markup.finished;
            in () end)}
      | _ => NONE);

fun register name f =
  register_parallel name (fn st => fn args => [fn () => f st args]);

end;

