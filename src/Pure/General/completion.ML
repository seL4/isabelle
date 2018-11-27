(*  Title:      Pure/General/completion.ML
    Author:     Makarius

Semantic completion within the formal context.
*)

signature COMPLETION =
sig
  type name = string * (string * string)
  type T
  val names: Position.T -> name list -> T
  val none: T
  val make: string * Position.T -> ((string -> bool) -> name list) -> T
  val encode: T -> XML.body
  val markup_element: T -> (Markup.T * XML.body) option
  val markup_report: T list -> string
  val make_report: string * Position.T -> ((string -> bool) -> name list) -> string
  val suppress_abbrevs: string -> Markup.T list
  val check_option: Options.T -> Proof.context -> string * Position.T -> string
  val check_option_value:
    Proof.context -> string * Position.T -> string * Position.T -> Options.T -> string * Options.T
end;

structure Completion: COMPLETION =
struct

(* completion of names *)

type name = string * (string * string);  (*external name, kind, internal name*)

abstype T = Completion of {pos: Position.T, total: int, names: name list}
with

fun dest (Completion args) = args;

fun names pos names =
  Completion
   {pos = pos,
    total = length names,
    names = take (Options.default_int "completion_limit") names};

end;

val none = names Position.none [];

fun make (name, pos) make_names =
  if Position.is_reported pos andalso name <> "" andalso name <> "_"
  then names pos (make_names (String.isPrefix (Name.clean name)))
  else none;

fun encode completion =
  let
    val {total, names, ...} = dest completion;
    open XML.Encode;
  in pair int (list (pair string (pair string string))) (total, names) end;

fun markup_element completion =
  let val {pos, names, ...} = dest completion in
    if Position.is_reported pos andalso not (null names) then
      SOME (Position.markup pos Markup.completion, encode completion)
    else NONE
  end;

val markup_report =
  map_filter markup_element #> map XML.Elem #> YXML.string_of_body #> Markup.markup_report;

val make_report = markup_report oo (single oo make);


(* suppress short abbreviations *)

fun suppress_abbrevs s =
  if not (Symbol.is_ascii_identifier s) andalso (length (Symbol.explode s) <= 1 orelse s = "::")
  then [Markup.no_completion]
  else [];


(* system options *)

fun check_option options ctxt (name, pos) =
  let
    val markup =
      Options.markup options (name, pos) handle ERROR msg =>
        let
          val completion_report =
            make_report (name, pos) (fn completed =>
                Options.names options
                |> filter completed
                |> map (fn a => (a, ("system_option", a))));
        in error (msg ^ completion_report) end;
    val _ = Context_Position.report ctxt pos markup;
  in name end;

fun check_option_value ctxt (name, pos) (value, pos') options =
  let
    val _ = check_option options ctxt (name, pos);
    val options' =
      Options.update name value options
        handle ERROR msg => error (msg ^ Position.here pos');
  in (name, options') end;

end;
