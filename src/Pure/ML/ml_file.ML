(*  Title:      Pure/ML/ml_file.ML
    Author:     Makarius

Commands to load ML files.
*)

signature ML_FILE =
sig
  val command: string -> bool option -> (theory -> Token.file) ->
    Toplevel.transition -> Toplevel.transition
  val ML: bool option -> (theory -> Token.file) -> Toplevel.transition -> Toplevel.transition
  val SML: bool option -> (theory -> Token.file) -> Toplevel.transition -> Toplevel.transition
end;

structure ML_File: ML_FILE =
struct

fun command environment debug get_file = Toplevel.generic_theory (fn gthy =>
  let
    val file = get_file (Context.theory_of gthy);
    val provide = Resources.provide_file file;
    val source = Token.file_source file;

    val _ = Thy_Output.check_comments (Context.proof_of gthy) (Input.source_explode source);

    val flags: ML_Compiler.flags =
      {environment = environment, redirect = true, verbose = true,
        debug = debug, writeln = writeln, warning = warning};
  in
    gthy
    |> ML_Context.exec (fn () => ML_Context.eval_source flags source)
    |> Local_Theory.propagate_ml_env
    |> Context.mapping provide (Local_Theory.background_theory provide)
  end);

val ML = command "";
val SML = command ML_Env.SML;

end;
