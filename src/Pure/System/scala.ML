(*  Title:      Pure/System/scala.ML
    Author:     Makarius

Support for Scala at runtime.
*)

signature SCALA =
sig
  val functions: unit -> string list
  val check_function: Proof.context -> string * Position.T -> string
  val promise_function: string -> string -> string future
  val function: string -> string -> string
  exception Null
end;

structure Scala: SCALA =
struct

(** invoke Scala functions from ML **)

val _ = Session.protocol_handler "isabelle.Scala";


(* pending promises *)

val new_id = string_of_int o Counter.make ();

val promises =
  Synchronized.var "Scala.promises" (Symtab.empty: string future Symtab.table);


(* invoke function *)

fun promise_function name arg =
  let
    val _ = if Resources.is_pide () then () else raise Fail "PIDE session required";
    val id = new_id ();
    fun abort () = Output.protocol_message (Markup.cancel_scala id) [];
    val promise = Future.promise_name "invoke_scala" abort : string future;
    val _ = Synchronized.change promises (Symtab.update (id, promise));
    val _ = Output.protocol_message (Markup.invoke_scala name id) [XML.Text arg];
  in promise end;

fun function name arg = Future.join (promise_function name arg);


(* fulfill *)

exception Null;

fun fulfill id tag res =
  let
    val result =
      (case tag of
        "0" => Exn.Exn Null
      | "1" => Exn.Res res
      | "2" => Exn.Exn (ERROR res)
      | "3" => Exn.Exn (Fail res)
      | "4" => Exn.Exn Exn.Interrupt
      | _ => raise Fail "Bad tag");
    val promise =
      Synchronized.change_result promises
        (fn tab => (the (Symtab.lookup tab id), Symtab.delete id tab));
    val _ = Future.fulfill_result promise result;
  in () end;

val _ =
  Isabelle_Process.protocol_command "Scala.fulfill"
    (fn [id, tag, res] =>
      fulfill id tag res
        handle exn => if Exn.is_interrupt exn then () else Exn.reraise exn);


(* registered functions *)

fun functions () = space_explode "," (getenv "ISABELLE_SCALA_FUNCTIONS");

fun check_function ctxt arg =
  Completion.check_item Markup.scala_functionN (Markup.scala_function o #1)
    (functions () |> sort_strings |> map (rpair ())) ctxt arg;

val _ = Theory.setup
 (ML_Antiquotation.inline_embedded \<^binding>\<open>scala_function\<close>
    (Args.context -- Scan.lift Parse.embedded_position
      >> (uncurry check_function #> ML_Syntax.print_string)) #>
  ML_Antiquotation.value_embedded \<^binding>\<open>scala\<close>
    (Args.context -- Scan.lift Args.embedded_position >> (fn (ctxt, arg) =>
      let val name = check_function ctxt arg
      in ML_Syntax.atomic ("Scala.function " ^ ML_Syntax.print_string name) end)));

end;
