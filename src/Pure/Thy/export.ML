(*  Title:      Pure/Thy/export.ML
    Author:     Makarius

Manage theory exports: compressed blobs.
*)

signature EXPORT =
sig
  val export: theory -> Path.T -> string list -> unit
  val export_raw: theory -> Path.T -> string list -> unit
  val markup: theory -> string -> Markup.T
  val message: theory -> string -> string
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

fun gen_export compress thy path body =
  (Output.try_protocol_message o Markup.export)
   {id = Position.get_id (Position.thread_data ()),
    serial = serial (),
    theory_name = Context.theory_long_name thy,
    name = check_name path,
    compress = compress} body;

val export = gen_export true;
val export_raw = gen_export false;


(* information message *)

fun markup thy s =
  let val name = (Markup.nameN, Context.theory_long_name thy ^ (if s = "" then "" else "/" ^ s))
  in Active.make_markup Markup.theory_exportsN {implicit = false, properties = [name]} end;

fun message thy s =
  "See " ^ Markup.markup (markup thy s) "theory exports";

end;
