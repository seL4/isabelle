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

fun gen_export compress thy name body =
  (Output.try_protocol_message o Markup.export)
   {id = Position.get_id (Position.thread_data ()),
    serial = serial (),
    theory_name = Context.theory_long_name thy,
    name = name,
    compress = compress} body;

fun export thy name body = gen_export (size body > 60) thy name [body];
fun export_raw thy name body = gen_export false thy name body;

end;
