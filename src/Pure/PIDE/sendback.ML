(*  Title:      Pure/PIDE/sendback.ML
    Author:     Makarius

Clickable "sendback" areas within the source text (see also
Tools/jEdit/src/sendback.scala).
*)

signature SENDBACK =
sig
  val make_markup: {implicit: bool, properties: Properties.T} -> Markup.T
  val markup_implicit: string -> string
  val markup: string -> string
end;

structure Sendback: SENDBACK =
struct

fun make_markup {implicit, properties} =
  Markup.sendback
  |> not implicit ? (fn markup =>
      let
        val props =
          (case Position.get_id (Position.thread_data ()) of
            SOME id => [(Markup.idN, id)]
          | NONE => []);
      in Markup.properties props markup end)
  |> Markup.properties properties;

fun markup_implicit s = Markup.markup (make_markup {implicit = true, properties = []}) s;
fun markup s = Markup.markup (make_markup {implicit = false, properties = []}) s;

end;

