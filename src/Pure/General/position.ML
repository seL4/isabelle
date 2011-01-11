(*  Title:      Pure/General/position.ML
    Author:     Markus Wenzel, TU Muenchen

Source positions: counting Isabelle symbols, starting from 1.
*)

signature POSITION =
sig
  eqtype T
  val make: {line: int, column: int, offset: int, end_offset: int, props: Properties.T} -> T
  val dest: T -> {line: int, column: int, offset: int, end_offset: int, props: Properties.T}
  val line_of: T -> int option
  val column_of: T -> int option
  val offset_of: T -> int option
  val end_offset_of: T -> int option
  val file_of: T -> string option
  val advance: Symbol.symbol -> T -> T
  val distance_of: T -> T -> int
  val none: T
  val start: T
  val file_name: string -> Properties.T
  val file: string -> T
  val line: int -> T
  val line_file: int -> string -> T
  val id: string -> T
  val id_only: string -> T
  val get_id: T -> string option
  val put_id: string -> T -> T
  val of_properties: Properties.T -> T
  val properties_of: T -> Properties.T
  val default_properties: T -> Properties.T -> Properties.T
  val markup: T -> Markup.T -> Markup.T
  val is_reported: T -> bool
  val reported_text: T -> Markup.T -> string -> string
  val report_text: T -> Markup.T -> string -> unit
  val report: T -> Markup.T -> unit
  val str_of: T -> string
  type range = T * T
  val no_range: range
  val set_range: range -> T
  val reset_range: T -> T
  val range: T -> T -> range
  val thread_data: unit -> T
  val setmp_thread_data: T -> ('a -> 'b) -> 'a -> 'b
  val default: T -> T
end;

structure Position: POSITION =
struct

(* datatype position *)

datatype T = Pos of (int * int * int * int) * Properties.T;

fun norm_props (props: Properties.T) =
  maps (fn a => the_list (find_first (fn (b, _) => a = b) props)) Markup.position_properties';

fun make {line = i, column = j, offset = k, end_offset = l, props} =
  Pos ((i, j, k, l), norm_props props);

fun dest (Pos ((i, j, k, l), props)) =
  {line = i, column = j, offset = k, end_offset = l, props = props};


fun valid (i: int) = i > 0;
fun if_valid i i' = if valid i then i' else i;


(* fields *)

fun line_of (Pos ((i, _, _, _), _)) = if valid i then SOME i else NONE;
fun column_of (Pos ((_, j, _, _), _)) = if valid j then SOME j else NONE;
fun offset_of (Pos ((_, _, k, _), _)) = if valid k then SOME k else NONE;
fun end_offset_of (Pos ((_, _, _, l), _)) = if valid l then SOME l else NONE;

fun file_of (Pos (_, props)) = Properties.get props Markup.fileN;


(* advance *)

fun advance_count "\n" (i: int, j: int, k: int, l: int) =
      (if_valid i (i + 1), if_valid j 1, if_valid k (k + 1), l)
  | advance_count s (i, j, k, l) =
      if Symbol.is_regular s then (i, if_valid j (j + 1), if_valid k (k + 1), l)
      else (i, j, k, l);

fun invalid_count (i, j, k, _: int) =
  not (valid i orelse valid j orelse valid k);

fun advance sym (pos as (Pos (count, props))) =
  if invalid_count count then pos else Pos (advance_count sym count, props);


(* distance of adjacent positions *)

fun distance_of (Pos ((_, j, k, _), _)) (Pos ((_, j', k', _), _)) =
  if valid j andalso valid j' then j' - j
  else if valid k andalso valid k' then k' - k
  else 0;


(* make position *)

val none = Pos ((0, 0, 0, 0), []);
val start = Pos ((1, 1, 1, 0), []);


fun file_name "" = []
  | file_name name = [(Markup.fileN, name)];

fun file name = Pos ((1, 1, 1, 0), file_name name);

fun line_file i name = Pos ((i, 0, 0, 0), file_name name);
fun line i = line_file i "";

fun id id = Pos ((0, 0, 1, 0), [(Markup.idN, id)]);
fun id_only id = Pos ((0, 0, 0, 0), [(Markup.idN, id)]);

fun get_id (Pos (_, props)) = Properties.get props Markup.idN;
fun put_id id (Pos (count, props)) = Pos (count, Properties.put (Markup.idN, id) props);


(* markup properties *)

fun of_properties props =
  let
    fun get name =
      (case Properties.get props name of
        NONE => 0
      | SOME s => the_default 0 (Int.fromString s));
  in
    make {line = get Markup.lineN, column = get Markup.columnN,
      offset = get Markup.offsetN, end_offset = get Markup.end_offsetN, props = props}
  end;


fun value k i = if valid i then [(k, string_of_int i)] else [];

fun properties_of (Pos ((i, j, k, l), props)) =
  value Markup.lineN i @ value Markup.columnN j @
  value Markup.offsetN k @ value Markup.end_offsetN l @ props;

fun default_properties default props =
  if exists (member (op =) Markup.position_properties o #1) props then props
  else properties_of default @ props;

val markup = Markup.properties o properties_of;


(* reports *)

fun is_reported pos = is_some (offset_of pos) andalso is_some (get_id pos);

fun reported_text pos m txt = if is_reported pos then Markup.markup (markup pos m) txt else "";
fun report_text pos markup txt = Output.report (reported_text pos markup txt);
fun report pos markup = report_text pos markup "";


(* str_of *)

fun str_of pos =
  let
    val props = properties_of pos;
    val s =
      (case (line_of pos, file_of pos) of
        (SOME i, NONE) => "(line " ^ string_of_int i ^ ")"
      | (SOME i, SOME name) => "(line " ^ string_of_int i ^ " of " ^ quote name ^ ")"
      | _ => "");
  in
    if null props then ""
    else (if s = "" then "" else " ") ^ Markup.markup (Markup.properties props Markup.position) s
  end;


(* range *)

type range = T * T;

val no_range = (none, none);

fun set_range (Pos ((i, j, k, _), props), Pos ((_, _, k', _), _)) = Pos ((i, j, k, k'), props);
fun reset_range (Pos ((i, j, k, _), props)) = Pos ((i, j, k, 0), props);

fun range pos pos' = (set_range (pos, pos'), pos');


(* thread data *)

local val tag = Universal.tag () : T Universal.tag in

fun thread_data () = the_default none (Thread.getLocal tag);

fun setmp_thread_data pos = Library.setmp_thread_data tag (thread_data ()) pos;

end;

fun default pos =
  if pos = none then thread_data ()
  else pos;

end;
