(*  Title:      Pure/Thy/export.ML
    Author:     Makarius

Manage theory exports: compressed blobs.
*)

signature EXPORT =
sig
  val report_export: theory -> Path.binding -> unit
  type params =
    {theory: theory, binding: Path.binding, executable: bool, compress: bool, strict: bool}
  val export_params: params -> XML.body -> unit
  val export: theory -> Path.binding -> XML.body -> unit
  val export_executable: theory -> Path.binding -> XML.body -> unit
  val export_file: theory -> Path.binding -> Path.T -> unit
  val export_executable_file: theory -> Path.binding -> Path.T -> unit
  val markup: theory -> Path.T -> Markup.T
  val message: theory -> Path.T -> string
end;

structure Export: EXPORT =
struct

(* export *)

fun report_export thy binding =
  let
    val theory_name = Context.theory_long_name thy;
    val (path, pos) = Path.dest_binding binding;
    val markup = Markup.export_path (Path.implode (Path.basic theory_name + path));
  in Context_Position.report_generic (Context.Theory thy) pos markup end;

type params =
  {theory: theory, binding: Path.binding, executable: bool, compress: bool, strict: bool};

fun export_params ({theory = thy, binding, executable, compress, strict}: params) body =
 (report_export thy binding;
  (Output.try_protocol_message o Markup.export)
   {id = Position.get_id (Position.thread_data ()),
    serial = serial (),
    theory_name = Context.theory_long_name thy,
    name = Path.implode_binding (tap Path.proper_binding binding),
    executable = executable,
    compress = compress,
    strict = strict} [body]);

fun export thy binding body =
  export_params
    {theory = thy, binding = binding, executable = false, compress = true, strict = true} body;

fun export_executable thy binding body =
  export_params
    {theory = thy, binding = binding, executable = true, compress = true, strict = true} body;

fun export_file thy binding file =
  export thy binding [XML.Text (File.read file)];

fun export_executable_file thy binding file =
  export_executable thy binding [XML.Text (File.read file)];


(* information message *)

fun markup thy path =
  let
    val thy_path = Path.basic (Context.theory_long_name thy) + path;
    val name = (Markup.nameN, Path.implode thy_path);
  in Active.make_markup Markup.theory_exportsN {implicit = false, properties = [name]} end;

fun message thy path =
  "See " ^ Markup.markup (markup thy path) "theory exports";

end;
