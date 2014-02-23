(*  Title:      Pure/Isar/completion.ML
    Author:     Makarius

Semantic completion within the formal context.
*)

signature COMPLETION =
sig
  type T
  val make: Position.T -> string list -> T
  val none: T
  val report: T -> unit
end;

structure Completion: COMPLETION =
struct

abstype T = Completion of {pos: Position.T, total: int, names: string list}
with

fun dest (Completion args) = args;

fun make pos names =
  Completion
   {pos = pos,
    total = length names,
    names = take (Options.default_int "completion_limit") names};

end;

val none = make Position.none [];

fun report completion =
  let val {pos, total, names} = dest completion in
    if Position.is_reported pos andalso not (null names) then
      let
        val props =
          (Markup.totalN, Markup.print_int total) ::
            (map Markup.print_int (1 upto length names) ~~ names);
        val markup = (Markup.completionN, Position.properties_of pos @ props);
      in Output.report (Markup.markup markup "") end
    else ()
  end;

end;
