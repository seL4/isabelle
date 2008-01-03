(*  Title:      Pure/General/position.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Source positions.
*)

signature POSITION =
sig
  type T
  val line_of: T -> int option
  val file_of: T -> string option
  val inc: T -> T
  val none: T
  val line: int -> T
  val file: string -> T
  val path: Path.T -> T
  val of_properties: Markup.property list -> T
  val properties_of: T -> Markup.property list
  val thread_data: unit -> T
  val setmp_thread_data: T -> ('a -> 'b) -> 'a -> 'b
  val str_of: T -> string
end;

structure Position: POSITION =
struct

(* datatype position *)

datatype T = Pos of int option * Markup.property list;

fun line_of (Pos (opt_n, _)) = opt_n;
fun file_of (Pos (_, props)) = AList.lookup (op =) props Markup.fileN ;

fun inc (pos as Pos (NONE, _)) = pos
  | inc (Pos (SOME n, props)) = Pos (SOME (n + 1), props);

val none = Pos (NONE, []);
fun line n = Pos (SOME n, []);
fun file s = Pos (SOME 1, [(Markup.fileN, s)]);

val path = file o Path.implode o Path.expand;


(* markup properties *)

fun of_properties props =
  let
    val opt_n =
      (case AList.lookup (op =) props Markup.lineN of
        SOME s => Int.fromString s
      | NONE => NONE);
    fun get name = the_list (find_first (fn (x: string, _) => x = name) props);
  in (Pos (opt_n, get Markup.fileN @ get Markup.idN)) end;

fun properties_of (Pos (opt_n, props)) =
  (case opt_n of SOME n => [(Markup.lineN, string_of_int n)] | NONE => []) @ props;


(* thread data *)

local val tag = Universal.tag () : T Universal.tag in

fun thread_data () = the_default none (Multithreading.get_data tag);
fun setmp_thread_data pos = Library.setmp_thread_data tag (thread_data ()) pos;

end;


(* str_of *)

fun print (SOME n, NONE) = "(line " ^ string_of_int n ^ ")"
  | print (NONE, SOME s) = "(" ^ s ^ ")"
  | print (SOME n, SOME s) = "(line " ^ string_of_int n ^ " of " ^ quote s ^ ")";

fun str_of pos =
  (case (line_of pos, file_of pos) of
    (NONE, NONE) => ""
  | res => " " ^ Markup.markup (Markup.properties (properties_of pos) Markup.position) (print res));

end;
