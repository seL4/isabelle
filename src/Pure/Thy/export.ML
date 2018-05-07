(*  Title:      Pure/Thy/export.ML
    Author:     Makarius

Manage theory exports: compressed blobs.
*)

signature EXPORT =
sig
  val export: theory -> string -> string -> unit
  val export_raw: theory -> string -> string list -> unit
end;

structure Export: EXPORT =
struct

fun check_name name =
  let
    fun err () = error ("Bad export name " ^ quote name);
    fun check_elem elem =
      if member (op =) ["", ".", ".."] elem then err ()
      else ignore (Path.basic elem handle ERROR _ => err ());

    val elems = space_explode "/" name;
    val _ = null elems andalso err ();
    val _ = List.app check_elem elems;
  in name end;

fun gen_export compress thy name body =
  (Output.try_protocol_message o Markup.export)
   {id = Position.get_id (Position.thread_data ()),
    serial = serial (),
    theory_name = Context.theory_long_name thy,
    name = check_name name,
    compress = compress} body;

fun export thy name body = gen_export (size body > 60) thy name [body];
fun export_raw thy name body = gen_export false thy name body;

end;
