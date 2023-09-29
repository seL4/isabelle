(*  Title:      Pure/System/scala.ML
    Author:     Makarius

Invoke Scala functions from the ML runtime.
*)

signature SCALA =
sig
  exception Null
  val function_bytes: string -> Bytes.T list -> Bytes.T list
  val function1_bytes: string -> Bytes.T -> Bytes.T
  val function: string -> string list -> string list
  val function1: string -> string -> string
end;

structure Scala: SCALA =
struct

exception Null;

local

val new_id = string_of_int o Counter.make ();

val results =
  Synchronized.var "Scala.results" (Symtab.empty: Bytes.T list Exn.result Symtab.table);

val _ =
  Protocol_Command.define_bytes "Scala.result"
    (fn id :: tag :: rest =>
      let
        val result =
          (case (Bytes.content tag, rest) of
            ("0", []) => Exn.Exn Null
          | ("1", _) => Exn.Res rest
          | ("2", [msg]) => Exn.Exn (ERROR (Bytes.content msg))
          | ("3", [msg]) => Exn.Exn (Fail (Bytes.content msg))
          | ("4", []) => Isabelle_Thread.interrupt_exn
          | _ => raise Fail "Malformed Scala.result");
      in Synchronized.change results (Symtab.map_entry (Bytes.content id) (K result)) end);

in

fun function_bytes name args =
  Thread_Attributes.uninterruptible_body (fn run =>
    let
      val id = new_id ();
      fun invoke () =
       (Synchronized.change results (Symtab.update (id, Exn.Exn Match));
        Output.protocol_message (Markup.invoke_scala name id) (map Bytes.contents_blob args));
      fun cancel () =
       (Synchronized.change results (Symtab.delete_safe id);
        Output.protocol_message (Markup.cancel_scala id) []);
      fun await_result () =
        Synchronized.guarded_access results
          (fn tab =>
            (case Symtab.lookup tab id of
              SOME (Exn.Exn Match) => NONE
            | SOME result => SOME (result, Symtab.delete id tab)
            | NONE => SOME (Isabelle_Thread.interrupt_exn, tab)));
    in
      invoke ();
      (case Exn.capture (fn () => Exn.release (run await_result ())) () of
        Exn.Res res => res
      | Exn.Exn exn => (if Exn.is_interrupt exn then cancel () else (); Exn.reraise exn))
    end);

val function1_bytes = singleton o function_bytes;

fun function name = map Bytes.string #> function_bytes name #> map Bytes.content;

val function1 = singleton o function;

end;

end;
