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
end;

structure Active: ACTIVE =
struct

fun make_markup name {implicit, properties} =
  (name, [])
  |> not implicit ? (fn markup =>
      let
        val props =
          (case Position.get_id (Position.thread_data ()) of
            SOME id => [(Markup.idN, id)]
          | NONE => []);
      in Markup.properties props markup end)
  |> Markup.properties properties;

fun markup_implicit name s = Markup.markup (make_markup name {implicit = true, properties = []}) s;
fun markup name s = Markup.markup (make_markup name {implicit = false, properties = []}) s;

val sendback_markup_implicit = markup_implicit Markup.sendbackN;
val sendback_markup = markup Markup.sendbackN;

end;

