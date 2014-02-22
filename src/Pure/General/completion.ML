(*  Title:      Pure/Isar/completion.ML
    Author:     Makarius

Semantic completion within the formal context.
*)

signature COMPLETION =
sig
  val limit: unit -> int
  type T = {original: string, replacements: string list}
  val none: T
  val reported_text: Position.T -> T -> string
  val report: Position.T -> T -> unit
end;

structure Completion: COMPLETION =
struct

fun limit () = Options.default_int "completion_limit";


type T = {original: string, replacements: string list};

val none: T = {original = "", replacements = []};

fun encode ({original, replacements}: T) =
  (original, replacements)
  |> let open XML.Encode in pair string (list string) end;

fun reported_text pos (completion: T) =
  if null (#replacements completion) then ""
  else Position.reported_text pos Markup.completion (YXML.string_of_body (encode completion));

fun report pos completion =
  Output.report (reported_text pos completion);

end;
