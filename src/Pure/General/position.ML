(*  Title:      Pure/General/position.ML
    Author:     Markus Wenzel, TU Muenchen

Source positions: counting Isabelle symbols, starting from 1.
*)

signature POSITION =
sig
  type T
  val line_of: T -> int option
  val column_of: T -> int option
  val offset_of: T -> int option
  val file_of: T -> string option
  val advance: Symbol.symbol -> T -> T
  val distance_of: T -> T -> int
  val none: T
  val start: T
  val file: string -> T
  val line: int -> T
  val line_file: int -> string -> T
  val id: string -> T
  val get_id: T -> string option
  val put_id: string -> T -> T
  val of_properties: Properties.T -> T
  val properties_of: T -> Properties.T
  val default_properties: T -> Properties.T -> Properties.T
  val report_text: Markup.T -> T -> string -> unit
  val report: Markup.T -> T -> unit
  val str_of: T -> string
  type range = T * T
  val no_range: range
  val encode_range: range -> T
  val reset_range: T -> T
  val range: T -> T -> range
  val thread_data: unit -> T
  val setmp_thread_data: T -> ('a -> 'b) -> 'a -> 'b
  val setmp_thread_data_seq: T -> ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq
end;

structure Position: POSITION =
struct

(* datatype position *)

datatype T = Pos of (int * int * int) * Properties.T;

fun valid (i: int) = i > 0;
fun if_valid i i' = if valid i then i' else i;

fun value k i = if valid i then [(k, string_of_int i)] else [];


(* fields *)

fun line_of (Pos ((i, _, _), _)) = if valid i then SOME i else NONE;
fun column_of (Pos ((_, j, _), _)) = if valid j then SOME j else NONE;
fun offset_of (Pos ((_, _, k), _)) = if valid k then SOME k else NONE;

fun file_of (Pos (_, props)) = Properties.get props Markup.fileN;


(* advance *)

fun advance_count "\n" (i: int, j: int, k: int) =
      (if_valid i (i + 1), if_valid j 1, if_valid k (k + 1))
  | advance_count s (i, j, k) =
      if Symbol.is_regular s andalso not (Symbol.is_utf8_trailer s)
      then (i, if_valid j (j + 1), if_valid k (k + 1)) else (i, j, k);

fun invalid_count (i, j, k) =
  not (valid i orelse valid j orelse valid k);

fun advance sym (pos as (Pos (count, props))) =
  if invalid_count count then pos else Pos (advance_count sym count, props);


(* distance of adjacent positions *)

fun distance_of (Pos ((_, j, k), _)) (Pos ((_, j', k'), _)) =
  if valid j andalso valid j' then j' - j
  else if valid k andalso valid k' then k' - k
  else 0;


(* make position *)

val none = Pos ((0, 0, 0), []);
val start = Pos ((1, 1, 1), []);


fun file_name "" = []
  | file_name name = [(Markup.fileN, name)];

fun file name = Pos ((1, 1, 1), file_name name);

fun line_file i name = Pos ((i, 0, 0), file_name name);
fun line i = line_file i "";


fun id id = Pos ((0, 0, 1), [(Markup.idN, id)]);

fun get_id (Pos (_, props)) = Properties.get props Markup.idN;
fun put_id id (Pos (count, props)) = Pos (count, Properties.put (Markup.idN, id) props);


(* markup properties *)

fun of_properties props =
  let
    fun get name =
      (case Properties.get props name of
        NONE => 0
      | SOME s => the_default 0 (Int.fromString s));
    val count = (get Markup.lineN, get Markup.columnN, get Markup.offsetN);
    fun property name = the_list (find_first (fn (x: string, _) => x = name) props);
  in Pos (count, maps property Markup.position_properties') end;

fun properties_of (Pos ((i, j, k), props)) =
  value Markup.lineN i @ value Markup.columnN j @ value Markup.offsetN k @ props;

fun default_properties default props =
  if exists (member (op =) Markup.position_properties o #1) props then props
  else properties_of default @ props;

fun report_text markup (pos as Pos (count, _)) txt =
  if invalid_count count then ()
  else Output.status (Markup.markup (Markup.properties (properties_of pos) markup) txt);

fun report markup pos = report_text markup pos "";


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

fun encode_range (Pos (count, props), Pos ((i, j, k), _)) =
  let val props' = props |> fold_rev Properties.put
    (value Markup.end_lineN i @ value Markup.end_columnN j @ value Markup.end_offsetN k)
  in Pos (count, props') end;

fun reset_range (Pos (count, props)) =
  let val props' = props |> fold Properties.remove
    [Markup.end_lineN, Markup.end_columnN, Markup.end_offsetN]
  in Pos (count, props') end;

fun range pos pos' = (encode_range (pos, pos'), pos');


(* thread data *)

local val tag = Universal.tag () : T Universal.tag in

fun thread_data () = the_default none (Thread.getLocal tag);

fun setmp_thread_data pos f x =
  if ! Output.debugging then f x
  else Library.setmp_thread_data tag (thread_data ()) pos f x;

fun setmp_thread_data_seq pos f x =
  setmp_thread_data pos f x |> Seq.wrap (fn pull => setmp_thread_data pos pull ());

end;

end;
