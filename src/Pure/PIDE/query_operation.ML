(*  Title:      Pure/PIDE/query_operation.ML
    Author:     Makarius

One-shot query operations via asynchronous print functions and temporary
document overlay.
*)

signature QUERY_OPERATION =
sig
  val register: string -> (Toplevel.state -> string list -> string) -> unit
end;

structure Query_Operation: QUERY_OPERATION =
struct

fun register name f =
  Command.print_function name
    (fn {args = instance :: args, ...} =>
        SOME {delay = NONE, pri = 0, persistent = false,
          print_fn = fn _ => fn state =>
            let
              fun result s = Output.result [(Markup.instanceN, instance)] s;
              fun status m = result (Markup.markup_only m);

              val _ = status Markup.running;
              val msg = XML.Elem ((Markup.writelnN, []), [XML.Text (f state args)])
                handle exn =>
                  if Exn.is_interrupt exn then reraise exn
                  else XML.Elem ((Markup.errorN, []), [XML.Text (ML_Compiler.exn_message exn)]);
              val _ = result (YXML.string_of msg);
              val _ = status Markup.finished;
            in () end}
      | _ => NONE);

end;

