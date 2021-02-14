(*  Title:      Pure/System/scala.ML
    Author:     Makarius

Invoke Scala functions from the ML runtime.
*)

signature SCALA =
sig
  exception Null
  val function: string -> string -> string
  val function_thread: string -> string -> string
end;

structure Scala: SCALA =
struct

exception Null;

local

val new_id = string_of_int o Counter.make ();

val results =
  Synchronized.var "Scala.results" (Symtab.empty: string Exn.result Symtab.table);

val _ =
  Protocol_Command.define "Scala.result"
    (fn [id, tag, res] =>
      let
        val result =
          (case tag of
            "0" => Exn.Exn Null
          | "1" => Exn.Res res
          | "2" => Exn.Exn (ERROR res)
          | "3" => Exn.Exn (Fail res)
          | "4" => Exn.Exn Exn.Interrupt
          | _ => raise Fail ("Bad tag: " ^ tag));
      in Synchronized.change results (Symtab.map_entry id (K result)) end);

fun gen_function thread name arg =
  Thread_Attributes.uninterruptible (fn restore_attributes => fn () =>
    let
      val id = new_id ();
      fun invoke () =
       (Synchronized.change results (Symtab.update (id, Exn.Exn Match));
        Output.protocol_message (Markup.invoke_scala name id thread) [XML.Text arg]);
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

in

val function = gen_function false;
val function_thread = gen_function true;

end;

end;
