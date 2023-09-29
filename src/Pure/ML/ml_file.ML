(*  Title:      Pure/ML/ml_file.ML
    Author:     Makarius

Commands to load ML files.
*)

signature ML_FILE =
sig
  val command: string -> bool -> bool option -> (theory -> Token.file) ->
    Toplevel.transition -> Toplevel.transition
  val ML: bool option -> (theory -> Token.file) -> Toplevel.transition -> Toplevel.transition
  val SML: bool option -> (theory -> Token.file) -> Toplevel.transition -> Toplevel.transition
end;

structure ML_File: ML_FILE =
struct

fun command environment catch_all debug get_file = Toplevel.generic_theory (fn gthy =>
  let
    val file = get_file (Context.theory_of gthy);
    val provide = Resources.provide_file file;
    val source = Token.file_source file;

    val _ = Document_Output.check_comments (Context.proof_of gthy) (Input.source_explode source);

    val flags: ML_Compiler.flags =
      {environment = environment, redirect = true, verbose = true, catch_all = catch_all,
        debug = debug, writeln = writeln, warning = warning};
  in
    gthy
    |> Local_Theory.touch_ml_env
    |> ML_Context.exec (fn () => ML_Context.eval_source flags source)
    |> Local_Theory.propagate_ml_env
    |> Context.mapping provide (Local_Theory.background_theory provide)
  end);

val ML = command "" false;
val SML = command ML_Env.SML true;

end;
