(*  Title:      Pure/System/isabelle_system.ML
    Author:     Makarius

Isabelle system support.
*)

signature ISABELLE_SYSTEM =
sig
  val ML_process: string list -> Process_Result.T
  val bash_process: Bash.params -> Process_Result.T
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
  val download: string -> Bytes.T
  val download_file: string -> Path.T -> unit
  val isabelle_id: unit -> string
  val isabelle_identifier: unit -> string option
  val isabelle_heading: unit -> string
  val isabelle_name: unit -> string
  val identification: unit -> string
end;

structure Isabelle_System: ISABELLE_SYSTEM =
struct

(* bash *)

val absolute_path = Path.implode o File.absolute_path;

local

fun bash_process_result args =
  (case args of
    a :: b :: c :: d :: lines =>
      let
        val rc = Value.parse_int a;
        val (elapsed, cpu) = apply2 (Time.fromMilliseconds o Value.parse_int) (b, c);
        val (out_lines, err_lines) = chop (Value.parse_int d) lines;
      in
        if rc = Process_Result.timeout_rc then raise Timeout.TIMEOUT elapsed
        else
          Process_Result.make
           {rc = rc,
            out_lines = out_lines,
            err_lines = err_lines,
            timing = {elapsed = elapsed, cpu = cpu, gc = Time.zeroTime}}
       end
  | _ => raise Fail ("Bad number of process results " ^ string_of_int (length args)));

in

fun ML_process args =
  Scala.function "ML_process" ("-o" :: ("ML_platform=" ^ ML_System.platform) :: args)
  |> bash_process_result;

fun bash_process params =
  let
    val {script, input, cwd, putenv, redirect, timeout, description} =
      Bash.dest_params params;
    val server_run =
     [Bytes.string Bash.server_run,
      Bytes.string script,
      input,
      let open XML.Encode in YXML.bytes_of_body (option (string o absolute_path) cwd) end,
      let open XML.Encode in YXML.bytes_of_body o list (pair string string) end
        (("ISABELLE_TMP", getenv "ISABELLE_TMP") :: putenv),
      Bytes.string (Value.print_bool redirect),
      Bytes.string (Value.print_real (Time.toReal timeout)),
      Bytes.string description];

    val address = Options.default_string \<^system_option>\<open>bash_process_address\<close>;
    val password = Options.default_string \<^system_option>\<open>bash_process_password\<close>;

    val _ = address = "" andalso raise Fail "Bad bash_process server address";
    fun with_streams f = Socket_IO.with_streams' f address password;

    fun kill (SOME uuid) =
          with_streams (fn s => Byte_Message.write_message_string (#2 s) [Bash.server_kill, uuid])
      | kill NONE = ();
  in
    Thread_Attributes.uninterruptible_body (fn run =>
      let
        fun err () = raise Fail "Malformed result from bash_process server";
        fun loop_body s =
          (case run Byte_Message.read_message_string (#1 s) of
            SOME (head :: args) =>
              if head = Bash.server_uuid andalso length args = 1 then
                loop (SOME (hd args)) s
              else if head = Bash.server_interrupt andalso null args then
                Isabelle_Thread.raise_interrupt ()
              else if head = Bash.server_failure andalso length args = 1 then
                raise Fail (hd args)
              else if head = Bash.server_result andalso length args >= 4 then
                bash_process_result args
              else err ()
          | _ => err ())
        and loop maybe_uuid s =
          (case Exn.capture_body (fn () => loop_body s) of
            Exn.Res res => res
          | Exn.Exn exn => (kill maybe_uuid; Exn.reraise exn));
      in
        with_streams (fn s => (Byte_Message.write_message (#2 s) server_run; loop NONE s))
      end)
  end;

end;

val bash = Bash.script #> bash_process #> Process_Result.print #> Process_Result.rc;

fun bash_output s =
  let
    val res = bash_process (Bash.script s);
    val _ = warning (Process_Result.err res);
  in (Process_Result.out res, Process_Result.rc res) end;


(* bash functions *)

fun bash_functions () = Scala.function "bash_functions" [];

fun check_bash_function ctxt arg =
  Completion.check_entity Markup.bash_functionN
    (bash_functions () |> map (rpair Position.none)) ctxt arg;


(* directory and file operations *)

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

fun with_tmp_file name ext = Thread_Attributes.uninterruptible (fn run => fn f =>
  let
    val path = create_tmp_path name ext;
    val result = Exn.capture (run f) path;
    val _ = try File.rm path;
  in Exn.release result end);


(* tmp dirs *)

fun rm_tree path = scala_function "rm_tree" [path];

fun with_tmp_dir name = Thread_Attributes.uninterruptible (fn run => fn f =>
  let
    val path = create_tmp_path name "";
    val _ = make_directory path;
    val result = Exn.capture (run f) path;
    val _ = try rm_tree path;
  in Exn.release result end);


(* download file *)

val download = Bytes.string #> Scala.function1_bytes "download";

fun download_file url path = Bytes.write path (download url);


(* Isabelle distribution identification *)

fun isabelle_id () = Scala.function1 "isabelle_id" "";

fun isabelle_identifier () = try getenv_strict "ISABELLE_IDENTIFIER";

fun isabelle_heading () =
  (case isabelle_identifier () of
    NONE => ""
  | SOME version => " (" ^ version ^ ")");

fun isabelle_name () = getenv_strict "ISABELLE_NAME";

fun identification () =
  "Isabelle" ^ (case try isabelle_id () of SOME id => "/" ^ id | NONE => "") ^ isabelle_heading ();

end;
