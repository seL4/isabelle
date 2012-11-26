(*  Title:      Pure/PIDE/sendback.ML
    Author:     Makarius

Clickable "sendback" areas within the source text (see also
Tools/jEdit/src/sendback.scala).
*)

signature SENDBACK =
sig
  val make_markup: {implicit: bool} -> Markup.T
  val markup_implicit: string -> string
  val markup: string -> string
end;

structure Sendback: SENDBACK =
struct

fun make_markup {implicit} =
  if implicit then Markup.sendback
  else
    let
      val props =
        (case Position.get_id (Position.thread_data ()) of
          SOME id => [(Markup.idN, id)]
        | NONE => []);
    in Markup.properties props Markup.sendback end;

fun markup_implicit s = Markup.markup (make_markup {implicit = true}) s;
fun markup s = Markup.markup (make_markup {implicit = false}) s;

end;

