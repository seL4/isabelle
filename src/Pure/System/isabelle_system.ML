(*  Title:      Pure/System/isabelle_system.ML
    Author:     Makarius

Isabelle system support.
*)

signature ISABELLE_SYSTEM =
sig
  val isabelle_tool: string -> string -> int
  val mkdirs: Path.T -> unit
  val mkdir: Path.T -> unit
  val copy_dir: Path.T -> Path.T -> unit
  val with_tmp_file: string -> (Path.T -> 'a) -> 'a
  val with_tmp_dir: string -> (Path.T -> 'a) -> 'a
end;

structure Isabelle_System: ISABELLE_SYSTEM =
struct

(* system commands *)

fun isabelle_tool name args =
  (case space_explode ":" (getenv "ISABELLE_TOOLS") |> get_first (fn dir =>
      let val path = dir ^ "/" ^ name in
        if can OS.FileSys.modTime path andalso
          not (OS.FileSys.isDir path) andalso
          OS.FileSys.access (path, [OS.FileSys.A_READ, OS.FileSys.A_EXEC])
        then SOME path
        else NONE
      end handle OS.SysErr _ => NONE) of
    SOME path => bash (File.shell_quote path ^ " " ^ args)
  | NONE => (writeln ("Unknown Isabelle tool: " ^ name); 2));

fun system_command cmd =
  if bash cmd <> 0 then error ("System command failed: " ^ cmd)
  else ();


(* directory operations *)

fun mkdirs path = system_command ("mkdir -p " ^ File.shell_path path);

fun mkdir path =
  if File.is_dir path then () else OS.FileSys.mkDir (File.platform_path path);

fun copy_dir src dst =
  if File.eq (src, dst) then ()
  else (system_command ("cp -r -f " ^ File.shell_path src ^ "/. " ^ File.shell_path dst); ());


(* unique tmp files *)

local

fun fresh_path name =
  let
    val path = File.tmp_path (Path.basic (name ^ serial_string ()));
    val _ = File.exists path andalso
      raise Fail ("Temporary file already exists: " ^ quote (Path.implode path));
  in path end;

fun rm_tree path = system_command ("rm -r -f " ^ File.shell_path path);

in

fun with_tmp_file name f =
  let val path = fresh_path name
  in Exn.release (Exn.capture f path before try File.rm path) end;

fun with_tmp_dir name f =
  let
    val path = fresh_path name;
    val _ = mkdirs path;
  in Exn.release (Exn.capture f path before try rm_tree path) end;

end;

end;

