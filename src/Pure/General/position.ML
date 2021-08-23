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
  val make: Thread_Position.T -> T
  val dest: T -> Thread_Position.T
  val line_of: T -> int option
  val offset_of: T -> int option
  val end_offset_of: T -> int option
  val file_of: T -> string option
  val id_of: T -> string option
  val symbol: Symbol.symbol -> T -> T
  val symbol_explode: string -> T -> T
  val advance_offsets: int -> T -> T
  val distance_of: T * T -> int option
  val none: T
  val start: T
  val file_name: string -> Properties.T
  val file_only: string -> T
  val file: string -> T
  val line_file_only: int -> string -> T
  val line_file: int -> string -> T
  val line: int -> T
  val get_props: T -> Properties.T
  val id: string -> T
  val id_only: string -> T
  val put_id: string -> T -> T
  val copy_id: T -> T -> T
  val id_properties_of: T -> Properties.T
  val parse_id: T -> int option
  val adjust_offsets: (int -> int option) -> T -> T
  val of_properties: Properties.T -> T
  val properties_of: T -> Properties.T
  val offset_properties_of: T -> Properties.T
  val def_properties_of: T -> Properties.T
  val entity_markup: string -> string * T -> Markup.T
  val entity_properties_of: bool -> serial -> T -> Properties.T
  val markup: T -> Markup.T -> Markup.T
  val is_reported: T -> bool
  val is_reported_range: T -> bool
  val reported_text: T -> Markup.T -> string -> string
  val report_text: T -> Markup.T -> string -> unit
  val report: T -> Markup.T -> unit
  type report = T * Markup.T
  type report_text = report * string
  val reports_text: report_text list -> unit
  val reports: report list -> unit
  val store_reports: report_text list Unsynchronized.ref ->
    T list -> ('a -> Markup.T list) -> 'a -> unit
  val append_reports: report_text list Unsynchronized.ref -> report list -> unit
  val here_strs: T -> string * string
  val here: T -> string
  val here_list: T list -> string
  type range = T * T
  val no_range: range
  val no_range_position: T -> T
  val range_position: range -> T
  val range: T * T -> range
  val range_of_properties: Properties.T -> range
  val properties_of_range: range -> Properties.T
  val thread_data: unit -> T
  val setmp_thread_data: T -> ('a -> 'b) -> 'a -> 'b
  val default: T -> bool * T
end;

structure Position: POSITION =
struct

(* datatype position *)

datatype T = Pos of (int * int * int) * Properties.T;

fun dest2 f = apply2 (fn Pos p => f p);

val ord =
  pointer_eq_ord
   (int_ord o dest2 (#1 o #1) |||
    int_ord o dest2 (#2 o #1) |||
    int_ord o dest2 (#3 o #1) |||
    Properties.ord o dest2 #2);

fun norm_props (props: Properties.T) =
  maps (fn a => the_list (find_first (fn (b, _) => a = b) props))
    [Markup.fileN, Markup.idN];

fun make {line = i, offset = j, end_offset = k, props} = Pos ((i, j, k), norm_props props);
fun dest (Pos ((i, j, k), props)) = {line = i, offset = j, end_offset = k, props = props};

fun valid (i: int) = i > 0;
fun maybe_valid i = if valid i then SOME i else NONE;
fun if_valid i i' = if valid i then i' else i;


(* fields *)

fun line_of (Pos ((i, _, _), _)) = maybe_valid i;
fun offset_of (Pos ((_, j, _), _)) = maybe_valid j;
fun end_offset_of (Pos ((_, _, k), _)) = maybe_valid k;

fun file_of (Pos (_, props)) = Properties.get props Markup.fileN;
fun id_of (Pos (_, props)) = Properties.get props Markup.idN;


(* count position *)

fun count_symbol "\n" (i: int, j: int, k: int) =
      (if_valid i (i + 1), if_valid j (j + 1), k)
  | count_symbol s (i, j, k) =
      if Symbol.not_eof s then (i, if_valid j (j + 1), k) else (i, j, k);

fun invalid_count (i, j, _: int) =
  not (valid i orelse valid j);

fun symbol sym (pos as (Pos (count, props))) =
  if invalid_count count then pos else Pos (count_symbol sym count, props);

val symbol_explode = fold symbol o Symbol.explode;


(* advance offsets *)

fun advance_offsets offset (pos as (Pos (count as (i, j, k), props))) =
  if offset = 0 orelse invalid_count count then pos
  else if offset < 0 then raise Fail "Illegal offset"
  else if valid i then raise Fail "Illegal line position"
  else Pos ((i, if_valid j (j + offset), if_valid k (k + offset)), props);


(* distance of adjacent positions *)

fun distance_of (Pos ((_, j, _), _), Pos ((_, j', _), _)) =
  if valid j andalso valid j' then SOME (j' - j) else NONE;


(* make position *)

val none = Pos ((0, 0, 0), []);
val start = Pos ((1, 1, 0), []);


fun file_name "" = []
  | file_name name = [(Markup.fileN, name)];

fun file_only name = Pos ((0, 0, 0), file_name name);
fun file name = Pos ((1, 1, 0), file_name name);

fun line_file_only i name = Pos ((i, 0, 0), file_name name);
fun line_file i name = Pos ((i, 1, 0), file_name name);
fun line i = line_file i "";

fun get_props (Pos (_, props)) = props;

fun id id = Pos ((0, 1, 0), [(Markup.idN, id)]);
fun id_only id = Pos ((0, 0, 0), [(Markup.idN, id)]);

fun put_id id (Pos (count, props)) = Pos (count, norm_props (Properties.put (Markup.idN, id) props));
fun copy_id pos = (case id_of pos of NONE => I | SOME id => put_id id);

fun parse_id pos = Option.map Value.parse_int (id_of pos);

fun id_properties_of pos =
  (case id_of pos of
    SOME id => [(Markup.idN, id)]
  | NONE => []);

fun adjust_offsets adjust (pos as Pos (_, props)) =
  if is_none (file_of pos) then
    (case parse_id pos of
      SOME id =>
        (case adjust id of
          SOME offset =>
            let val Pos (count, _) = advance_offsets offset pos
            in Pos (count, Properties.remove Markup.idN props) end
        | NONE => pos)
    | NONE => pos)
  else pos;


(* markup properties *)

fun get props name =
  (case Properties.get props name of
    NONE => 0
  | SOME s => Value.parse_int s);

fun of_properties props =
  make {line = get props Markup.lineN,
    offset = get props Markup.offsetN,
    end_offset = get props Markup.end_offsetN,
    props = props};

fun value k i = if valid i then [(k, Value.print_int i)] else [];

fun properties_of (Pos ((i, j, k), props)) =
  value Markup.lineN i @ value Markup.offsetN j @ value Markup.end_offsetN k @ props;

fun offset_properties_of (Pos ((_, j, k), _)) =
  value Markup.offsetN j @ value Markup.end_offsetN k;

val def_properties_of = properties_of #> map (fn (x, y) => ("def_" ^ x, y));

fun entity_markup kind (name, pos) =
  Markup.entity kind name |> Markup.properties (def_properties_of pos);

fun entity_properties_of def serial pos =
  if def then (Markup.defN, Value.print_int serial) :: properties_of pos
  else (Markup.refN, Value.print_int serial) :: def_properties_of pos;

val markup = Markup.properties o properties_of;


(* reports *)

fun is_reported pos = is_some (offset_of pos) andalso is_some (id_of pos);
fun is_reported_range pos = is_reported pos andalso is_some (end_offset_of pos);

fun reported_text pos m txt = if is_reported pos then Markup.markup (markup pos m) txt else "";
fun report_text pos markup txt = Output.report [reported_text pos markup txt];
fun report pos markup = report_text pos markup "";

type report = T * Markup.T;
type report_text = report * string;

val reports_text =
  map (fn ((pos, m), txt) => if is_reported pos then Markup.markup (markup pos m) txt else "")
  #> Output.report;

val reports = map (rpair "") #> reports_text;

fun store_reports _ [] _ _ = ()
  | store_reports (r: report_text list Unsynchronized.ref) ps markup x =
      let val ms = markup x
      in Unsynchronized.change r (fold (fn p => fold (fn m => cons ((p, m), "")) ms) ps) end;

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
  let
    val props = properties_of pos;
    val (s1, s2) = here_strs pos;
  in
    if s2 = "" then ""
    else s1 ^ Markup.markup (Markup.properties props Markup.position) s2
  end;

val here_list = map here #> distinct (op =) #> implode;


(* range *)

type range = T * T;

val no_range = (none, none);

fun no_range_position (Pos ((i, j, _), props)) = Pos ((i, j, 0), props);
fun range_position (Pos ((i, j, _), props), Pos ((_, j', _), _)) = Pos ((i, j, j'), props);
fun range (pos, pos') = (range_position (pos, pos'), no_range_position pos');

fun range_of_properties props =
  let
    val pos = of_properties props;
    val pos' =
      make {line = get props Markup.end_lineN,
        offset = get props Markup.end_offsetN,
        end_offset = 0,
        props = props};
  in (pos, pos') end;

fun properties_of_range (pos, pos') =
  properties_of pos @ value Markup.end_lineN (the_default 0 (line_of pos'));


(* thread data *)

val thread_data = make o Thread_Position.get;
fun setmp_thread_data pos = Thread_Position.setmp (dest pos);

fun default pos =
  if pos = none then (false, thread_data ())
  else (true, pos);

end;
