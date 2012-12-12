(*  Title:      Pure/PIDE/active.ML
    Author:     Makarius

Active areas within the document (see also Tools/jEdit/src/active.scala).
*)

signature ACTIVE =
sig
  val make_markup: string -> {implicit: bool, properties: Properties.T} -> Markup.T
  val markup_implicit: string -> string -> string
  val markup: string -> string -> string
  val sendback_markup_implicit: string -> string
  val sendback_markup: string -> string
  val dialog: unit -> (string -> Markup.T) * string future
  val dialog_result: string -> string -> unit
end;

structure Active: ACTIVE =
struct

(* active markup *)

fun explicit_id () =
  (case Position.get_id (Position.thread_data ()) of
    SOME id => [(Markup.idN, id)]
  | NONE => []);

fun make_markup name {implicit, properties} =
  (name, [])
  |> not implicit ? (fn markup => Markup.properties (explicit_id ()) markup)
  |> Markup.properties properties;

fun markup_implicit name s = Markup.markup (make_markup name {implicit = true, properties = []}) s;
fun markup name s = Markup.markup (make_markup name {implicit = false, properties = []}) s;


(* sendback area *)

val sendback_markup_implicit = markup_implicit Markup.sendbackN;
val sendback_markup = markup Markup.sendbackN;


(* dialog via document content *)

val new_name = string_of_int o Synchronized.counter ();

val dialogs = Synchronized.var "Active.dialogs" (Symtab.empty: string future Symtab.table);

fun dialog () =
  let
    val name = new_name ();
    fun abort () = Synchronized.change dialogs (Symtab.delete_safe name);
    val promise = Future.promise abort : string future;
    val _ = Synchronized.change dialogs (Symtab.update_new (name, promise));
    fun mk_markup result = Markup.properties (explicit_id ()) (Markup.dialog name result);
  in (mk_markup, promise) end;

fun dialog_result name result =
  Synchronized.change_result dialogs
    (fn tab => (Symtab.lookup tab name, Symtab.delete_safe name tab))
  |> (fn NONE => () | SOME promise => Future.fulfill promise result);

end;

