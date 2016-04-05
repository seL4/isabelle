(*  Title:      Pure/ML/ml_file.ML
    Author:     Makarius

Commands to load ML files.
*)

signature ML_FILE =
sig
  val ML: bool option -> (theory -> Token.file list) -> Toplevel.transition -> Toplevel.transition
  val SML: bool option -> (theory -> Token.file list) -> Toplevel.transition -> Toplevel.transition
  val use: bool option -> (theory -> Token.file list) -> Toplevel.transition -> Toplevel.transition
end;

structure ML_File: ML_FILE =
struct

fun command SML debug files = Toplevel.generic_theory (fn gthy =>
  let
    val [{src_path, lines, digest, pos}: Token.file] = files (Context.theory_of gthy);
    val provide = Resources.provide (src_path, digest);
    val source = Input.source true (cat_lines lines) (pos, pos);
    val (SML_syntax, SML_env) = SML src_path;
    val flags =
      {SML_syntax = SML_syntax, SML_env = SML_env, exchange = false, redirect = true,
        verbose = true, debug = debug, writeln = writeln, warning = warning};
  in
    gthy
    |> ML_Context.exec (fn () => ML_Context.eval_source flags source)
    |> Local_Theory.propagate_ml_env
    |> Context.mapping provide (Local_Theory.background_theory provide)
  end);

val ML = command (K (false, false));
val SML = command (K (true, true));

val use =
  command (fn path =>
    (case try (#2 o Path.split_ext) path of
      SOME "ML" => (false, true)
    | SOME "sml" => (true, true)
    | SOME "sig" => (true, true)
    | _ =>
        error ("Bad file name " ^ Path.print path ^
          "\nExpected .ML for Isabelle/ML or .sml/.sig for Standard ML")));

end;
