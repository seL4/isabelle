(*  Title:      Pure/System/invoke_scala.ML
    Author:     Makarius

JVM method invocation service via Isabelle/Scala.

TODO: proper cancellation!
*)

signature INVOKE_SCALA =
sig
  exception Null
  val method: string -> string -> string
  val promise_method: string -> string -> string future
  val fulfill_method: string -> string -> string -> unit
end;

structure Invoke_Scala: INVOKE_SCALA =
struct

exception Null;


(* pending promises *)

val new_id = string_of_int o Synchronized.counter ();

val promises =
  Synchronized.var "Invoke_Scala.promises" (Symtab.empty: string future Symtab.table);


(* method invocation *)

fun promise_method name arg =
  let
    val id = new_id ();
    fun abort () = Output.protocol_message (Isabelle_Markup.cancel_scala id) "";
    val promise = Future.promise abort : string future;
    val _ = Synchronized.change promises (Symtab.update (id, promise));
    val _ = Output.protocol_message (Isabelle_Markup.invoke_scala name id) arg;
  in promise end;

fun method name arg = Future.join (promise_method name arg);


(* fulfill method *)

fun fulfill_method id tag res =
  let
    val result =
      (case tag of
        "0" => Exn.Exn Null
      | "1" => Exn.Res res
      | "2" => Exn.Exn (ERROR res)
      | "3" => Exn.Exn (Fail res)
      | _ => raise Fail "Bad tag");
    val promise =
      Synchronized.change_result promises
        (fn tab => (the (Symtab.lookup tab id), Symtab.delete id tab));
    val _ = Future.fulfill_result promise result;
  in () end;

end;

