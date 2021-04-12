(*  Title:      Pure/System/scala.ML
    Author:     Makarius

Invoke Scala functions from the ML runtime.
*)

signature SCALA =
sig
  exception Null
  val function: string -> string list -> string list
  val function1: string -> string -> string
end;

structure Scala: SCALA =
struct

exception Null;

local

val new_id = string_of_int o Counter.make ();

val results =
  Synchronized.var "Scala.results" (Symtab.empty: string list Exn.result Symtab.table);

val _ =
  Protocol_Command.define "Scala.result"
    (fn id :: args =>
      let
        val result =
          (case args of
            ["0"] => Exn.Exn Null
          | "1" :: rest => Exn.Res rest
          | ["2", msg] => Exn.Exn (ERROR msg)
          | ["3", msg] => Exn.Exn (Fail msg)
          | ["4"] => Exn.Exn Exn.Interrupt
          | _ => raise Fail "Malformed Scala.result");
      in Synchronized.change results (Symtab.map_entry id (K result)) end);

in

fun function name args =
  Thread_Attributes.uninterruptible (fn restore_attributes => fn () =>
    let
      val id = new_id ();
      fun invoke () =
       (Synchronized.change results (Symtab.update (id, Exn.Exn Match));
        Output.protocol_message (Markup.invoke_scala name id) (map (single o XML.Text) args));
      fun cancel () =
       (Synchronized.change results (Symtab.delete_safe id);
        Output.protocol_message (Markup.cancel_scala id) []);
      fun await_result () =
        Synchronized.guarded_access results
          (fn tab =>
            (case Symtab.lookup tab id of
              SOME (Exn.Exn Match) => NONE
            | SOME result => SOME (result, Symtab.delete id tab)
            | NONE => SOME (Exn.Exn Exn.Interrupt, tab)));
    in
      invoke ();
      Exn.release (restore_attributes await_result ())
        handle exn => (if Exn.is_interrupt exn then cancel () else (); Exn.reraise exn)
    end) ();

val function1 = singleton o function;

end;

end;
