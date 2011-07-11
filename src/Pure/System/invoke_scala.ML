(*  Title:      Pure/System/invoke_scala.ML
    Author:     Makarius

JVM method invocation service via Scala layer.

TODO: proper cancellation!
*)

signature INVOKE_SCALA =
sig
  val method: string -> string -> string future
  exception Null
  val fulfill_method: string -> string -> string -> unit
end;

structure Invoke_Scala: INVOKE_SCALA =
struct

(* pending promises *)

val new_id = string_of_int o Synchronized.counter ();

val promises =
  Synchronized.var "Invoke_Scala.promises" (Symtab.empty: string future Symtab.table);


(* method invocation *)

fun method name arg =
  let
    val id = new_id ();
    val promise = Future.promise () : string future;
    val _ = Synchronized.change promises (Symtab.update (id, promise));
    val _ = Output.raw_message (Markup.invoke_scala name id) arg;
  in promise end;


(* fulfill method *)

exception Null;

fun fulfill_method id tag res =
  let
    val result =
      (case tag of
        "0" => Exn.Exn Null
      | "1" => Exn.Result res
      | "2" => Exn.Exn (ERROR res)
      | "3" => Exn.Exn (Fail res)
      | _ => raise Fail "Bad tag");
    val promise =
      Synchronized.change_result promises
        (fn tab => (the (Symtab.lookup tab id), Symtab.delete id tab));
    val _ = Future.fulfill_result promise result;
  in () end;

end;

