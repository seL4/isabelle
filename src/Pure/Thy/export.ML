(*  Title:      Pure/Thy/export.ML
    Author:     Makarius

Manage theory exports: compressed blobs.
*)

signature EXPORT =
sig
  val export: theory -> string -> string list -> unit
  val export_raw: theory -> string -> string list -> unit
end;

structure Export: EXPORT =
struct

fun check_name name =
  let
    val _ =
      (case space_explode "/" name of
        [] => error "Empty export name"
      | elems => List.app Path.check_elem elems);
  in name end;

fun gen_export compress thy name body =
  (Output.try_protocol_message o Markup.export)
   {id = Position.get_id (Position.thread_data ()),
    serial = serial (),
    theory_name = Context.theory_long_name thy,
    name = check_name name,
    compress = compress} body;

val export = gen_export true;
val export_raw = gen_export false;

end;
