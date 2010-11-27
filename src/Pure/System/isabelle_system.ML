(*  Title:      Pure/System/isabelle_system.ML
    Author:     Makarius

Isabelle system support.
*)

signature ISABELLE_SYSTEM =
sig
  val isabelle_tool: string -> string -> int
  val rm_tree: Path.T -> unit
  val mkdirs: Path.T -> unit
  val mkdir: Path.T -> unit
  val copy_dir: Path.T -> Path.T -> unit
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

fun rm_tree path = system_command ("rm -r " ^ File.shell_path path);

fun mkdirs path = system_command ("mkdir -p " ^ File.shell_path path);

val mkdir = OS.FileSys.mkDir o File.platform_path;

fun copy_dir src dst =
  if File.eq (src, dst) then ()
  else (system_command ("cp -r -f " ^ File.shell_path src ^ "/. " ^ File.shell_path dst); ());

end;

