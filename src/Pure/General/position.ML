(*  Title:      Pure/General/position.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Source positions.
*)

signature POSITION =
sig
  type T
  val advance: Symbol.symbol -> T -> T
  val line_of: T -> int option
  val column_of: T -> int option
  val file_of: T -> string option
  val none: T
  val start: T
  val file: string -> T
  val line: int -> T
  val line_file: int -> string -> T
  val get_id: T -> string option
  val put_id: string -> T -> T
  val of_properties: Markup.property list -> T
  val properties_of: T -> Markup.property list
  val default_properties: T -> Markup.property list -> Markup.property list
  val report: Markup.T -> T -> unit
  val str_of: T -> string
  type range = T * T
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

datatype T = Pos of (int * int) * Markup.property list;

fun valid (m: int) = m > 0;
fun value k m = if valid m then [(k, string_of_int m)] else [];


(* advance *)

fun advance_count "\n" (m: int, n: int) = (m + 1, if valid n then 1 else n)
  | advance_count s (m, n) =
      if valid n andalso Symbol.is_regular s andalso not (Symbol.is_utf8_trailer s)
      then (m, n + 1) else (m, n);

fun advance sym (pos as (Pos ((m, n), props))) =
  if valid m then Pos (advance_count sym (m, n), props) else pos;


(* fields *)

fun line_of (Pos ((m, _), _)) = if valid m then SOME m else NONE;
fun column_of (Pos ((_, n), _)) = if valid n then SOME n else NONE;

fun file_of (Pos (_, props)) = AList.lookup (op =) props Markup.fileN;

fun file_name "" = []
  | file_name name = [(Markup.fileN, name)];


(* make position *)

val none = Pos ((0, 0), []);
val start = Pos ((1, 1), []);

fun file name = Pos ((1, 1), file_name name);

fun line_file m name = Pos ((m, 0), file_name name);
fun line m = line_file m "";


(* markup properties *)

fun get_id (Pos (_, props)) = AList.lookup (op =) props Markup.idN;
fun put_id id (Pos (count, props)) = Pos (count, AList.update (op =) (Markup.idN, id) props);

fun get_int props (name: string) =
  (case AList.lookup (op =) props name of
    NONE => 0
  | SOME s => the_default 0 (Int.fromString s));

fun of_properties props =
  let
    val count = (get_int props Markup.lineN, get_int props Markup.columnN);
    fun property name = the_list (find_first (fn (x: string, _) => x = name) props);
  in Pos (count, maps property Markup.position_properties') end;

fun properties_of (Pos ((m, n), props)) =
  value Markup.lineN m @ value Markup.columnN n @ props;

fun default_properties default props =
  if exists (member (op =) Markup.position_properties o #1) props then props
  else properties_of default @ props;

fun report markup pos =
  if is_none (line_of pos) then ()
  else Output.status (Markup.markup (Markup.properties (properties_of pos) markup) "");


(* str_of *)

fun str_of pos =
  let
    val props = properties_of pos;
    val s =
      (case (line_of pos, file_of pos) of
        (SOME m, NONE) => "(line " ^ string_of_int m ^ ")"
      | (SOME m, SOME name) => "(line " ^ string_of_int m ^ " of " ^ quote name ^ ")"
      | _ => "");
  in
    if null props then ""
    else (if s = "" then "" else " ") ^ Markup.markup (Markup.properties props Markup.position) s
  end;


(* range *)

type range = T * T;

fun encode_range (Pos (count, props), Pos ((m, n), _)) =
  Pos (count,
    fold_rev (AList.update op =) (value Markup.end_lineN m @ value Markup.end_columnN n) props);

fun reset_range (Pos (count, props)) =
  Pos (count, filter_out (fn (k, _) => k = Markup.end_lineN orelse k = Markup.end_columnN) props);

fun range pos pos' = (encode_range (pos, pos'), pos');


(* thread data *)

local val tag = Universal.tag () : T Universal.tag in

fun thread_data () = the_default none (Multithreading.get_data tag);

fun setmp_thread_data pos f x =
  if ! Output.debugging then f x
  else Library.setmp_thread_data tag (thread_data ()) pos f x;

fun setmp_thread_data_seq pos f x =
  setmp_thread_data pos f x |> Seq.wrap (fn pull => setmp_thread_data pos pull ());

end;

end;
