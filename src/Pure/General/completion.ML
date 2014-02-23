(*  Title:      Pure/Isar/completion.ML
    Author:     Makarius

Semantic completion within the formal context.
*)

signature COMPLETION =
sig
  type T
  val names: Position.T -> (string * string) list -> T
  val none: T
  val report: T -> unit
end;

structure Completion: COMPLETION =
struct

abstype T = Completion of {pos: Position.T, total: int, names: (string * string) list}
with

fun dest (Completion args) = args;

fun names pos names =
  Completion
   {pos = pos,
    total = length names,
    names = take (Options.default_int "completion_limit") names};

end;

val none = names Position.none [];

fun report completion =
  let val {pos, total, names} = dest completion in
    if Position.is_reported pos andalso not (null names) then
      let
        val markup = Position.markup pos Markup.completion;
        val body = (total, names) |>
          let open XML.Encode in pair int (list (pair string string)) end;
      in Output.report (YXML.string_of (XML.Elem (markup, body))) end
    else ()
  end;

end;
