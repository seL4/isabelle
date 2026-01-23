(*  Title:      Pure/General/position.ML
    Author:     Makarius

Source positions starting from 1; values <= 0 mean "absent". Count Isabelle
symbols, not UTF8 bytes nor UTF16 characters. Position range specifies a
right-open interval offset .. end_offset (exclusive).
*)

signature POSITION =
sig
  eqtype T
  val ord: T ord
  val make0: int -> int -> int -> string -> string -> string -> T
  val make: Thread_Position.T -> T
  val dest: T -> Thread_Position.T
  val line_of: T -> int option
  val offset_of: T -> int option
  val end_offset_of: T -> int option
  val label_of: T -> string option
  val file_of: T -> string option
  val id_of: T -> string option
  val symbol: Symbol.symbol -> T -> T
  val symbol_explode: string -> T -> T
  val distance_of: T * T -> int option
  val none: T
  val start: T
  val label: string -> T -> T
  val label_interpreted: T -> T
  val file_only: string -> T
  val file: string -> T
  val line_file_only: int -> string -> T
  val line_file: int -> string -> T
  val line: int -> T
  val id: string -> T
  val id_only: string -> T
  val put_id: string -> T -> T
  val copy_id: T -> T -> T
  val parse_id: T -> int option
  val shift_offsets: {remove_id: bool} -> int -> T -> T
  val adjust_offsets: (int -> int option) -> T -> T
  val of_props: {line: int, offset: int, end_offset: int, props: Properties.T} -> T
  val of_properties: Properties.T -> T
  val properties_of: T -> Properties.T
  val def_properties_of: T -> Properties.T
  val entity_markup: string -> string * T -> Markup.T
  val make_entity_markup: {def: bool} -> serial -> string -> string * T -> Markup.T
  val markup_properties: T -> Markup.T -> Markup.T
  val markup: T -> Markup.T
  val is_reported: T -> bool
  val is_reported_range: T -> bool
  val reported_text: T -> Markup.T -> string -> string
  val report_text: T -> Markup.T -> string -> unit
  val report: T -> Markup.T -> unit
  type report = T * Markup.T
  type report_text = report * string
  val reports_text: report_text list -> unit
  val reports: report list -> unit
  val append_reports: report_text list Unsynchronized.ref -> report list -> unit
  val here_strs: T -> string * string
  val here: T -> string
  val here_list: T list -> string
  type range = T * T
  val range_ord: range ord
  val no_range: range
  val no_range_position: T -> T
  val range_position: range -> T
  val range: T * T -> range
  val range_of_properties: Properties.T -> range
  val properties_of_range: range -> Properties.T
  val thread_data: unit -> T
  val setmp_thread_data: T -> ('a -> 'b) -> 'a -> 'b
  val setmp_thread_data_label: string -> ('a -> 'b) -> 'a -> 'b
  val default: T -> bool * T
end;

structure Position: POSITION =
struct

(* datatype position *)

datatype T = Pos of Thread_Position.T;

fun make0 line offset end_offset label file id =
  Pos {line = line, offset = offset, end_offset = end_offset,
    props = {label = label, file = file, id = id}};

val make = Pos;
fun dest (Pos args) = args;

val ord =
  pointer_eq_ord
   (int_ord o apply2 (#line o dest) |||
    int_ord o apply2 (#offset o dest) |||
    int_ord o apply2 (#end_offset o dest) |||
    fast_string_ord o apply2 (#label o #props o dest) |||
    fast_string_ord o apply2 (#file o #props o dest) |||
    fast_string_ord o apply2 (#id o #props o dest));


(* fields *)

fun valid (i: int) = i > 0;
fun maybe_valid i = if valid i then SOME i else NONE;

val invalid = not o valid;
fun invalid_pos (Pos {line, offset, ...}) = invalid line andalso invalid offset;

val line_of = maybe_valid o #line o dest;
val offset_of = maybe_valid o #offset o dest;
val end_offset_of = maybe_valid o #end_offset o dest;

fun label_of (Pos {props = {label, ...}, ...}) = if label = "" then NONE else SOME label;
fun file_of (Pos {props = {file, ...}, ...}) = if file = "" then NONE else SOME file;
fun id_of (Pos {props = {id, ...}, ...}) = if id = "" then NONE else SOME id;


(* symbol positions *)

fun symbols [] pos = pos
  | symbols ss (pos as Pos {line, offset, end_offset, props}) =
      let
        val line' = if valid line then fold (fn s => s = "\n" ? Integer.add 1) ss line else line;
        val offset' =
          if valid offset then fold (fn s => Symbol.not_eof s ? Integer.add 1) ss offset else offset;
      in
        if line = line' andalso offset = offset' then pos
        else Pos {line = line', offset = offset', end_offset = end_offset, props = props}
      end;

val symbol = symbols o single;

fun symbol_explode str pos =
  if str = "" orelse invalid_pos pos then pos
  else fold symbol (Symbol.explode str) pos;


(* distance of adjacent positions *)

fun distance_of (Pos {offset, ...}, Pos {offset = offset', ...}) =
  if valid offset andalso valid offset' then SOME (offset' - offset) else NONE;


(* make position *)

type props = {label: string, file: string, id: string};

val no_props: props = {label = "", file = "", id = ""};

fun file_props name : props =
  if name = "" then no_props else {label = "", file = name, id = ""};

fun id_props id : props =
  if id = "" then no_props else {label = "", file = "", id = id};


val none = Pos {line = 0, offset = 0, end_offset = 0, props = no_props};
val start = Pos {line = 1, offset = 1, end_offset = 0, props = no_props};

fun label label (Pos {line, offset, end_offset, props = {label = _, file, id}}) =
  Pos {line = line, offset = offset, end_offset = end_offset,
    props = {label = label, file = file, id = id}};

val label_interpreted = label Markup.interpretedN;

fun file_only name = Pos {line = 0, offset = 0, end_offset = 0, props = file_props name};
fun file name = Pos {line = 1, offset = 1, end_offset = 0, props = file_props name};

fun line_file_only line name = Pos {line = line, offset = 0, end_offset = 0, props = file_props name};
fun line_file line name = Pos {line = line, offset = 1, end_offset = 0, props = file_props name};
fun line line = line_file line "";

fun id id = Pos {line = 0, offset = 1, end_offset = 0, props = id_props id};
fun id_only id = Pos {line = 0, offset = 0, end_offset = 0, props = id_props id};

fun put_id id' (pos as Pos {line, offset, end_offset, props = {label, file, id}}) =
  if id = id' then pos
  else Pos {line = line, offset = offset, end_offset = end_offset,
    props = {label = label, file = file, id = id'}};

fun copy_id pos = (case id_of pos of NONE => I | SOME id => put_id id);

fun parse_id pos = Option.map Value.parse_int (id_of pos);


(* adjust offsets *)

fun shift_offsets {remove_id} shift (pos as Pos {line, offset, end_offset, props}) =
  if shift < 0 then raise Fail "Illegal offset shift"
  else if shift > 0 andalso valid line then raise Fail "Illegal line position"
  else
    let
      val offset' = if valid offset then offset + shift else offset;
      val end_offset' = if valid end_offset then end_offset + shift else end_offset;
      val props' = if remove_id then file_props (#file props) else props;
    in
      if offset = offset' andalso end_offset = end_offset' andalso props = props' then pos
      else Pos {line = line, offset = offset', end_offset = end_offset', props = props'}
    end;

fun adjust_offsets adjust pos =
  if is_none (file_of pos) then
    (case parse_id pos of
      SOME id =>
        (case adjust id of
          SOME shift => shift_offsets {remove_id = true} shift pos
        | NONE => pos)
    | NONE => pos)
  else pos;


(* markup properties *)

fun of_props {line, offset, end_offset, props} =
  Pos {line = line, offset = offset, end_offset = end_offset,
    props =
     {label = Properties.get_string props Markup.labelN,
      file = Properties.get_string props Markup.fileN,
      id = Properties.get_string props Markup.idN}};

fun of_properties props =
  of_props {
    line = Properties.get_int props Markup.lineN,
    offset = Properties.get_int props Markup.offsetN,
    end_offset = Properties.get_int props Markup.end_offsetN,
    props = props};

fun properties_of (Pos {line, offset, end_offset, props = {label, file, id}}) =
  Properties.make_int Markup.lineN line @
  Properties.make_int Markup.offsetN offset @
  Properties.make_int Markup.end_offsetN end_offset @
  Properties.make_string Markup.labelN label @
  Properties.make_string Markup.fileN file @
  Properties.make_string Markup.idN id;

val def_properties_of = properties_of #> map (apfst Markup.def_name);

fun entity_markup kind (name, pos) =
  Markup.entity kind name |> Markup.properties (def_properties_of pos);

fun make_entity_markup {def} serial kind (name, pos) =
  let
    val props =
      if def then (Markup.defN, Value.print_int serial) :: properties_of pos
      else (Markup.refN, Value.print_int serial) :: def_properties_of pos;
  in Markup.entity kind name |> Markup.properties props end;

val markup_properties = Markup.properties o properties_of;
fun markup pos = markup_properties pos Markup.position;


(* reports *)

fun is_reported pos = is_some (offset_of pos) andalso is_some (id_of pos);
fun is_reported_range pos = is_reported pos andalso is_some (end_offset_of pos);

fun reported_text pos m txt =
  if is_reported pos then Markup.markup (markup_properties pos m) txt else "";

fun report_text pos markup txt =
  if Print_Mode.PIDE_enabled () then Output.report [reported_text pos markup txt] else ();

fun report pos markup = report_text pos markup "";

type report = T * Markup.T;
type report_text = report * string;

fun reports_text args =
  if Print_Mode.PIDE_enabled () then
    Output.report (args |> map (fn ((pos, m), txt) =>
      if is_reported pos then Markup.markup (markup_properties pos m) txt else ""))
  else ();

val reports = map (rpair "") #> reports_text;

fun append_reports (r: report_text list Unsynchronized.ref) reports =
  Unsynchronized.change r (append (map (rpair "") reports));


(* here: user output *)

fun here_strs pos =
  (case (line_of pos, file_of pos) of
    (SOME i, NONE) => (" ", "(line " ^ Value.print_int i ^ ")")
  | (SOME i, SOME name) => (" ", "(line " ^ Value.print_int i ^ " of " ^ quote name ^ ")")
  | (NONE, SOME name) => (" ", "(file " ^ quote name ^ ")")
  | _ => if is_reported pos then ("", "\092<^here>") else ("", ""));

fun here pos =
  let val (s1, s2) = here_strs pos
  in if s2 = "" then "" else s1 ^ Markup.markup (markup pos) s2 end;

val here_list = map here #> distinct (op =) #> implode;


(* range *)

type range = T * T;

val range_ord = prod_ord ord ord;

val no_range = (none, none);

fun no_range_position (Pos {line, offset, end_offset = _, props}) =
  Pos {line = line, offset = offset, end_offset = 0, props = props};

fun range_position (Pos {line, offset, end_offset = _, props}, Pos {offset = offset', ...}) =
  Pos {line = line, offset = offset, end_offset = offset', props = props};

fun range (pos, pos') = (range_position (pos, pos'), no_range_position pos');

fun range_of_properties props =
  let
    val pos = of_properties props;
    val pos' =
      of_props {line = Properties.get_int props Markup.end_lineN,
        offset = Properties.get_int props Markup.end_offsetN,
        end_offset = 0,
        props = props};
  in (pos, pos') end;

fun properties_of_range (pos, pos') =
  properties_of pos @ Properties.make_int Markup.end_lineN (the_default 0 (line_of pos'));


(* thread data *)

val thread_data = Pos o Thread_Position.get;
fun setmp_thread_data pos = Thread_Position.setmp (dest pos);

fun setmp_thread_data_label a f x =
  if a = "" then f x
  else setmp_thread_data (label a (thread_data ())) f x;

fun default pos =
  if pos = none then (false, thread_data ())
  else (true, pos);

end;
