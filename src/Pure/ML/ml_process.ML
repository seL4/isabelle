(*  Title:      Pure/ML/ml_process.ML
    Author:     Makarius

Command-line arguments for external ML process.
*)

signature ML_PROCESS =
sig
  type args
  val cwd: Path.T -> args -> args
  val include_dir: Path.T -> args -> args
  val eval_expr: string -> args -> args
  val eval_file: Path.T -> args -> args
  val logic: string -> args -> args
  val print_mode: string -> args -> args
  val system_option: string -> args -> args
  val redirect: args -> args
  val args: args
  val command_line: args -> string list
end;

structure ML_Process: ML_PROCESS =
struct

val absolute_path = Path.implode o File.absolute_path;

abstype args = Rev of string list
with

fun add1 arg (Rev args) = Rev (arg :: args);
fun add2 arg1 arg2 (Rev args) = Rev (arg2 :: arg1 :: args);

val cwd = add2 "-C" o absolute_path;
val include_dir = add2 "-d" o absolute_path;
val eval_expr = add2 "-e";
val eval_file = add2 "-f" o absolute_path;
val logic = add2 "-l";
val print_mode = add2 "-m";
val system_option = add2 "-o";
val redirect = add1 "-r";

val args = Rev [] |> system_option ("ML_platform=" ^ ML_System.platform)

fun command_line (Rev args) = rev args;

end;

end;
