(*  Title:      Pure/System/isabelle_system.ML
    Author:     Makarius

Isabelle system support.
*)

signature ISABELLE_SYSTEM =
sig
  val bash_process: string -> Process_Result.T
  val bash_output: string -> string * int
  val bash: string -> int
  val bash_functions: unit -> string list
  val check_bash_function: Proof.context -> string * Position.T -> string
  val rm_tree: Path.T -> unit
  val make_directory: Path.T -> Path.T
  val mkdir: Path.T -> unit
  val copy_dir: Path.T -> Path.T -> unit
  val copy_file: Path.T -> Path.T -> unit
  val copy_file_base: Path.T * Path.T -> Path.T -> unit
  val create_tmp_path: string -> string -> Path.T
  val with_tmp_file: string -> string -> (Path.T -> 'a) -> 'a
  val with_tmp_dir: string -> (Path.T -> 'a) -> 'a
  val download: string -> string
end;

structure Isabelle_System: ISABELLE_SYSTEM =
struct

(* bash *)

fun bash_process script =
  Scala.function_thread "bash_process"
    ("export ISABELLE_TMP=" ^ Bash.string (getenv "ISABELLE_TMP") ^ "\n" ^ script)
  |> space_explode "\000"
  |> (fn [] => raise Exn.Interrupt
      | [err] => error err
      | a :: b :: c :: d :: lines =>
          let
            val rc = Value.parse_int a;
            val (elapsed, cpu) = apply2 (Time.fromMilliseconds o Value.parse_int) (b, c);
            val (out_lines, err_lines) = chop (Value.parse_int d) lines;
          in
            Process_Result.make
             {rc = rc,
              out_lines = out_lines,
              err_lines = err_lines,
              timing = {elapsed = elapsed, cpu = cpu, gc = Time.zeroTime}}
         end
      | _ => raise Fail "Malformed Isabelle/Scala result");

val bash = bash_process #> Process_Result.print #> Process_Result.rc;

fun bash_output s =
  let
    val res = bash_process s;
    val _ = warning (Process_Result.err res);
  in (Process_Result.out res, Process_Result.rc res) end;


(* bash functions *)

fun bash_functions () =
  bash_process "declare -Fx"
  |> Process_Result.check
  |> Process_Result.out_lines
  |> map_filter (space_explode " " #> try List.last);

fun check_bash_function ctxt arg =
  Completion.check_entity Markup.bash_functionN
    (bash_functions () |> map (rpair Position.none)) ctxt arg;


(* directory operations *)

fun system_command cmd =
  if bash cmd <> 0 then error ("System command failed: " ^ cmd) else ();

fun rm_tree path = system_command ("rm -r -f " ^ File.bash_path path);

fun make_directory path =
  (Scala.function "make_directory" (Path.implode (File.absolute_path path)); path);

fun mkdir path =
  if File.is_dir path then () else OS.FileSys.mkDir (File.platform_path path);

fun copy_dir src dst =
  if File.eq (src, dst) then ()
  else (system_command ("cp -p -R -f " ^ File.bash_path src ^ "/. " ^ File.bash_path dst); ());

fun copy_file src0 dst0 =
  let
    val src = Path.expand src0;
    val dst = Path.expand dst0;
    val target = if File.is_dir dst then dst + Path.base src else dst;
  in
    if File.eq (src, target) then ()
    else
      ignore (system_command ("cp -p -f " ^ File.bash_path src ^ " " ^ File.bash_path target))
  end;

fun copy_file_base (base_dir, src0) target_dir =
  let
    val src = Path.expand src0;
    val src_dir = Path.dir src;
    val _ =
      if Path.starts_basic src then ()
      else error ("Illegal path specification " ^ Path.print src ^ " beyond base directory");
  in copy_file (base_dir + src) (make_directory (target_dir + src_dir)) end;


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

fun with_tmp_dir name f =
  let val path = create_tmp_path name ""
  in Exn.release (Exn.capture f (make_directory path) before ignore (try rm_tree path)) end;


(* download file *)

fun download url =
  with_tmp_file "download" "" (fn path =>
    let
      val s = "curl --fail --silent --location " ^ Bash.string url ^ " > " ^ File.bash_path path;
      val res = bash_process s;
    in
      if Process_Result.ok res then File.read path
      else cat_error ("Failed to download " ^ quote url) (Process_Result.err res)
    end);

end;
