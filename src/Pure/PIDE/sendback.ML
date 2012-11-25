(*  Title:      Pure/PIDE/sendback.ML
    Author:     Makarius

Clickable "sendback" areas within the source text (see also
Tools/jEdit/src/sendback.scala).
*)

signature SENDBACK =
sig
  val make_markup: unit -> Markup.T
  val markup: string -> string
  val markup_implicit: string -> string
end;

structure Sendback: SENDBACK =
struct

fun make_markup () =
  let
    val props =
      (case Position.get_id (Position.thread_data ()) of
        SOME id => [(Markup.idN, id)]
      | NONE => []);
  in Markup.properties props Markup.sendback end;

fun markup s = Markup.markup (make_markup ()) s;

fun markup_implicit s = Markup.markup Markup.sendback s;

end;

