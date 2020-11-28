(*  Title:      Pure/System/scala.ML
    Author:     Makarius

Support for Scala at runtime.
*)

signature SCALA =
sig
  exception Null
  val function: string -> string -> string
  val function_thread: string -> string -> string
  val functions: unit -> string list
  val check_function: Proof.context -> string * Position.T -> string
end;

structure Scala: SCALA =
struct

(** protocol for Scala function invocation from ML **)

exception Null;

local

val new_id = string_of_int o Counter.make ();

val results =
  Synchronized.var "Scala.results" (Symtab.empty: string Exn.result Symtab.table);

val _ =
  Isabelle_Process.protocol_command "Scala.result"
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
            | NONE => SOME (Exn.Exn Exn.Interrupt, tab)))
        handle exn => (if Exn.is_interrupt exn then cancel () else (); Exn.reraise exn);
    in
      invoke ();
      Exn.release (restore_attributes await_result ())
    end) ();

in

val function = gen_function false;
val function_thread = gen_function true;

end;



(** registered Scala functions **)

fun functions () = space_explode "," (getenv "ISABELLE_SCALA_FUNCTIONS");

fun check_function ctxt arg =
  Completion.check_entity Markup.scala_functionN
    (functions () |> sort_strings |> map (fn a => (a, Resources.scala_function_pos a))) ctxt arg;

val _ = Theory.setup
 (ML_Antiquotation.inline_embedded \<^binding>\<open>scala_function\<close>
    (Args.context -- Scan.lift Parse.embedded_position
      >> (uncurry check_function #> ML_Syntax.print_string)) #>
  ML_Antiquotation.value_embedded \<^binding>\<open>scala\<close>
    (Args.context -- Scan.lift Args.embedded_position >> (fn (ctxt, arg) =>
      let val name = check_function ctxt arg
      in ML_Syntax.atomic ("Scala.function " ^ ML_Syntax.print_string name) end)) #>
  ML_Antiquotation.value_embedded \<^binding>\<open>scala_thread\<close>
    (Args.context -- Scan.lift Args.embedded_position >> (fn (ctxt, arg) =>
      let val name = check_function ctxt arg
      in ML_Syntax.atomic ("Scala.function_thread " ^ ML_Syntax.print_string name) end)));

end;
