(*  Title:      Pure/System/isabelle_system.ML
    Author:     Makarius

Isabelle system support.
*)

signature ISABELLE_SYSTEM =
sig
  type process_result =
   {rc: int,
    out_lines: string list,
    err_lines: string list,
    out: string,
    err: string,
    timing: Timing.timing}
  val bash_process: string -> process_result
  val bash_output_check: string -> string
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

type process_result =
 {rc: int,
  out_lines: string list,
  err_lines: string list,
  out: string,
  err: string,
  timing: Timing.timing};

fun bash_process script : process_result =
  Scala.function_thread "bash_process"
    ("export ISABELLE_TMP=" ^ Bash.string (getenv "ISABELLE_TMP") ^ "\n" ^ script)
  |> space_explode "\000"
  |> (fn [] => raise Exn.Interrupt
      | [err] => error err
      | a :: b :: c :: d :: lines =>
          let
            val rc = Value.parse_int a;
            val (elapsed, cpu) = apply2 (Time.fromMilliseconds o Value.parse_int) (b, c);
            val ((out, err), (out_lines, err_lines)) =
              chop (Value.parse_int d) lines |> `(apply2 cat_lines);
          in
           {rc = rc,
            out_lines = out_lines,
            err_lines = err_lines,
            out = out,
            err = err,
            timing = {elapsed = elapsed, cpu = cpu, gc = Time.zeroTime}}
         end
      | _ => raise Fail "Malformed Isabelle/Scala result");

fun bash_output_check s =
  (case bash_process s of
    {rc = 0, out, ...} => trim_line out
  | {err, ...} => error (trim_line err));

fun bash_output s =
  let
    val {out, err, rc, ...} = bash_process s;
    val _ = warning (trim_line err);
  in (out, rc) end;

fun bash s =
  let
    val (out, rc) = bash_output s;
    val _ = writeln (trim_line out);
  in rc end;


(* bash functions *)

fun bash_functions () =
  bash_output_check "declare -Fx"
  |> split_lines |> map_filter (space_explode " " #> try List.last);

fun check_bash_function ctxt arg =
  Completion.check_entity Markup.bash_functionN
    (bash_functions () |> map (rpair Position.none)) ctxt arg;


(* directory operations *)

fun system_command cmd =
  if bash cmd <> 0 then error ("System command failed: " ^ cmd) else ();

fun rm_tree path = system_command ("rm -r -f " ^ File.bash_path path);

fun make_directory path =
  let
    val _ =
      if File.is_dir path then ()
      else
       (bash ("perl -e \"use File::Path make_path; make_path('" ^ File.standard_path path ^ "');\"");
        if File.is_dir path then () else error ("Failed to create directory: " ^ Path.print path));
  in path end;

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
    ("curl --fail --silent --location " ^ Bash.string url ^ " > " ^ File.bash_path path)
    |> bash_process
    |> (fn {rc = 0, ...} => File.read path
         | {err, ...} => cat_error ("Failed to download " ^ quote url) err));

end;
