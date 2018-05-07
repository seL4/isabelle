(*  Title:      Pure/Thy/export.ML
    Author:     Makarius

Manage theory exports.
*)

signature EXPORT =
sig
  val export: theory -> string -> Output.output -> unit
  val export_uncompressed: theory -> string -> Output.output -> unit
end;

structure Export: EXPORT =
struct

fun gen_export compress thy name output =
  (Output.try_protocol_message o Markup.export)
   {id = Position.get_id (Position.thread_data ()),
    serial = serial (),
    theory_name = Context.theory_long_name thy,
    name = name,
    compress = compress} [output];

val export = gen_export true;
val export_uncompressed = gen_export false;

end;
