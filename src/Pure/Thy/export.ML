(*  Title:      Pure/Thy/export.ML
    Author:     Makarius

Manage theory exports: compressed blobs.
*)

signature EXPORT =
sig
  val report_export: theory -> Path.binding -> unit
  type params =
    {theory: theory, binding: Path.binding, executable: bool, compress: bool, strict: bool}
  val export_params: params -> string list -> unit
  val export: theory -> Path.binding -> string list -> unit
  val export_executable: theory -> Path.binding -> string list -> unit
  val export_file: theory -> Path.binding -> Path.T -> unit
  val export_executable_file: theory -> Path.binding -> Path.T -> unit
  val markup: theory -> Path.T -> Markup.T
  val message: theory -> Path.T -> string
  val protocol_message: Properties.T -> string list -> unit
end;

structure Export: EXPORT =
struct

(* export *)

fun report_export thy binding =
  let
    val theory_name = Context.theory_long_name thy;
    val (path, pos) = Path.dest_binding binding;
    val markup = Markup.export_path (Path.implode (Path.append (Path.basic theory_name) path));
  in Context_Position.report_generic (Context.Theory thy) pos markup end;

type params =
  {theory: theory, binding: Path.binding, executable: bool, compress: bool, strict: bool};

fun export_params ({theory = thy, binding, executable, compress, strict}: params) blob =
 (report_export thy binding;
  (Output.try_protocol_message o Markup.export)
   {id = Position.get_id (Position.thread_data ()),
    serial = serial (),
    theory_name = Context.theory_long_name thy,
    name = Path.implode_binding (tap Path.proper_binding binding),
    executable = executable,
    compress = compress,
    strict = strict} blob);

fun export thy binding blob =
  export_params
    {theory = thy, binding = binding, executable = false, compress = true, strict = true} blob;

fun export_executable thy binding blob =
  export_params
    {theory = thy, binding = binding, executable = true, compress = true, strict = true} blob;

fun export_file thy binding file = export thy binding [File.read file];
fun export_executable_file thy binding file = export_executable thy binding [File.read file];


(* information message *)

fun markup thy path =
  let
    val thy_path = Path.append (Path.basic (Context.theory_long_name thy)) path;
    val name = (Markup.nameN, Path.implode thy_path);
  in Active.make_markup Markup.theory_exportsN {implicit = false, properties = [name]} end;

fun message thy path =
  "See " ^ Markup.markup (markup thy path) "theory exports";


(* protocol message (bootstrap) *)

fun protocol_message props output =
  (case props of
    function :: args =>
      if function = (Markup.functionN, Markup.exportN) andalso
        not (null args) andalso #1 (hd args) = Markup.idN
      then
        let
          val path = Path.expand (Path.explode ("$ISABELLE_EXPORT_TMP/export" ^ serial_string ()));
          val _ = File.write_list path output;
        in Protocol_Message.inline (#2 function) (tl args @ [(Markup.fileN, Path.implode path)]) end
      else raise Output.Protocol_Message props
  | [] => raise Output.Protocol_Message props);

val _ =
  if Thread_Data.is_virtual then ()
  else Private_Output.protocol_message_fn := protocol_message;

end;
