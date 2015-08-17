(*  Title:      Pure/ML/ml_file.ML
    Author:     Makarius

The 'ML_file' command.
*)

structure ML_File: sig end =
struct

fun ML_file_cmd debug files = Toplevel.generic_theory (fn gthy =>
  let
    val [{src_path, lines, digest, pos}: Token.file] = files (Context.theory_of gthy);
    val provide = Resources.provide (src_path, digest);
    val source = Input.source true (cat_lines lines) (pos, pos);
    val flags: ML_Compiler.flags =
      {SML = false, exchange = false, redirect = true, verbose = true,
        debug = debug, writeln = writeln, warning = warning};
  in
    gthy
    |> ML_Context.exec (fn () => ML_Context.eval_source flags source)
    |> Local_Theory.propagate_ml_env
    |> Context.mapping provide (Local_Theory.background_theory provide)
  end);

val _ =
  Outer_Syntax.command ("ML_file", @{here}) "read and evaluate Isabelle/ML file"
    (Resources.parse_files "ML_file" >> ML_file_cmd NONE);

val _ =
  Outer_Syntax.command ("ML_file_debug", @{here})
    "read and evaluate Isabelle/ML file (with debugger information)"
    (Resources.parse_files "ML_file_debug" >> ML_file_cmd (SOME true));

val _ =
  Outer_Syntax.command ("ML_file_no_debug", @{here})
    "read and evaluate Isabelle/ML file (no debugger information)"
    (Resources.parse_files "ML_file_no_debug" >> ML_file_cmd (SOME false));

end;
