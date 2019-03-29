(*  Title:      Pure/Thy/export.ML
    Author:     Makarius

Manage theory exports: compressed blobs.
*)

signature EXPORT =
sig
  val check_name: Path.T -> string
  type params = {theory: theory, path: Path.T, executable: bool, compress: bool}
  val export_params: params -> string list -> unit
  val export: theory -> Path.T -> string list -> unit
  val export_executable: theory -> Path.T -> string list -> unit
  val export_file: theory -> Path.T -> Path.T -> unit
  val export_executable_file: theory -> Path.T -> Path.T -> unit
  val markup: theory -> Path.T -> Markup.T
  val message: theory -> Path.T -> string
end;

structure Export: EXPORT =
struct

(* export *)

fun check_name path =
  let
    val name = Path.implode path;
    val _ =
      if not (Path.is_current path) andalso Path.all_basic path then ()
      else error ("Bad export name: " ^ quote name);
  in name end;

type params = {theory: theory, path: Path.T, executable: bool, compress: bool};

fun export_params ({theory, path, executable, compress}: params) blob =
  (Output.try_protocol_message o Markup.export)
   {id = Position.get_id (Position.thread_data ()),
    serial = serial (),
    theory_name = Context.theory_long_name theory,
    name = check_name path,
    executable = executable,
    compress = compress} blob;

fun export thy path blob =
  export_params {theory = thy, path = path, executable = false, compress = true} blob;

fun export_executable thy path blob =
  export_params {theory = thy, path = path, executable = true, compress = true} blob;

fun export_file thy path file = export thy path [File.read file];
fun export_executable_file thy path file = export_executable thy path [File.read file];


(* information message *)

fun markup thy path =
  let
    val thy_path = Path.append (Path.basic (Context.theory_long_name thy)) path;
    val name = (Markup.nameN, Path.implode thy_path);
  in Active.make_markup Markup.theory_exportsN {implicit = false, properties = [name]} end;

fun message thy path =
  "See " ^ Markup.markup (markup thy path) "theory exports";

end;
