(*  Title:      Pure/System/isabelle_system.ML
    Author:     Makarius

Isabelle system support.
*)

signature ISABELLE_SYSTEM =
sig
  val bash_process:
    {script: string, input: string, redirect: bool, timeout: Time.time} -> Process_Result.T
  val bash_process_script: string -> Process_Result.T
  val bash_output: string -> string * int
  val bash: string -> int
  val bash_functions: unit -> string list
  val check_bash_function: Proof.context -> string * Position.T -> string
  val absolute_path: Path.T -> string
  val make_directory: Path.T -> Path.T
  val copy_dir: Path.T -> Path.T -> unit
  val copy_file: Path.T -> Path.T -> unit
  val copy_file_base: Path.T * Path.T -> Path.T -> unit
  val create_tmp_path: string -> string -> Path.T
  val with_tmp_file: string -> string -> (Path.T -> 'a) -> 'a
  val rm_tree: Path.T -> unit
  val with_tmp_dir: string -> (Path.T -> 'a) -> 'a
  val download: string -> string
  val download_file: string -> Path.T -> unit
  val decode_base64: string -> string
  val encode_base64: string -> string
  val isabelle_id: unit -> string
  val isabelle_identifier: unit -> string option
  val isabelle_heading: unit -> string
  val isabelle_name: unit -> string
  val identification: unit -> string
end;

structure Isabelle_System: ISABELLE_SYSTEM =
struct

(* bash *)

fun bash_process {script, input, redirect, timeout} =
  Scala.function "bash_process"
   ["export ISABELLE_TMP=" ^ Bash.string (getenv "ISABELLE_TMP") ^ "\n" ^ script,
    input, Value.print_bool redirect, Value.print_int (Time.toMilliseconds timeout)]
  |> (fn [] => raise Exn.Interrupt
      | [err] => error err
      | a :: b :: c :: d :: lines =>
          let
            val rc = Value.parse_int a;
            val (elapsed, cpu) = apply2 (Time.fromMilliseconds o Value.parse_int) (b, c);
            val (out_lines, err_lines) = chop (Value.parse_int d) lines;
          in
            if rc = Process_Result.timeout_rc then raise Timeout.TIMEOUT elapsed else ();
            Process_Result.make
             {rc = rc,
              out_lines = out_lines,
              err_lines = err_lines,
              timing = {elapsed = elapsed, cpu = cpu, gc = Time.zeroTime}}
         end
      | _ => raise Fail "Malformed Isabelle/Scala result");

fun bash_process_script script =
  bash_process {script = script, input = "", redirect = false, timeout = Time.zeroTime};

fun bash script =
  bash_process_script script
  |> Process_Result.print
  |> Process_Result.rc;

fun bash_output s =
  let
    val res = bash_process_script s;
    val _ = warning (Process_Result.err res);
  in (Process_Result.out res, Process_Result.rc res) end;


(* bash functions *)

fun bash_functions () =
  bash_process_script "declare -Fx"
  |> Process_Result.check
  |> Process_Result.out_lines
  |> map_filter (space_explode " " #> try List.last);

fun check_bash_function ctxt arg =
  Completion.check_entity Markup.bash_functionN
    (bash_functions () |> map (rpair Position.none)) ctxt arg;


(* directory and file operations *)

val absolute_path = Path.implode o File.absolute_path;
fun scala_function name = ignore o Scala.function name o map absolute_path;

fun make_directory path = (scala_function "make_directory" [path]; path);

fun copy_dir src dst = scala_function "copy_dir" [src, dst];

fun copy_file src dst = scala_function "copy_file" [src, dst];

fun copy_file_base (base_dir, src) target_dir =
  ignore (Scala.function "copy_file_base"
    [absolute_path base_dir, Path.implode src, absolute_path target_dir]);


(* tmp files *)

fun create_tmp_path name ext =
  let
    val path = File.tmp_path (Path.basic (name ^ serial_string ()) |> Path.ext ext);
    val _ = File.exists path andalso
      raise Fail ("Temporary file already exists: " ^ Path.print path);
  in path end;

fun with_tmp_file name ext f =
  let val path = create_tmp_path name ext
  in Exn.release (Exn.capture f path before ignore (try File.rm path)) end;


(* tmp dirs *)

fun rm_tree path = scala_function "rm_tree" [path];

fun with_tmp_dir name f =
  let val path = create_tmp_path name ""
  in Exn.release (Exn.capture f (make_directory path) before ignore (try rm_tree path)) end;


(* download file *)

val download = Scala.function1 "download";

fun download_file url path = File.write path (download url);


(* base64 *)

val decode_base64 = Scala.function1 "decode_base64";
val encode_base64 = Scala.function1 "encode_base64";


(* Isabelle distribution identification *)

fun isabelle_id () = Scala.function1 "isabelle_id" "";

fun isabelle_identifier () = try getenv_strict "ISABELLE_IDENTIFIER";

fun isabelle_heading () =
  (case isabelle_identifier () of
    NONE => ""
  | SOME version => " (" ^ version ^ ")");

fun isabelle_name () = getenv_strict "ISABELLE_NAME";

fun identification () = "Isabelle/" ^ isabelle_id () ^ isabelle_heading ();

end;
