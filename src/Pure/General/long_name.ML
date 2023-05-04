(*  Title:      Pure/General/long_name.ML
    Author:     Makarius

Long names.
*)

signature LONG_NAME =
sig
  val separator: string
  val append: string -> string -> string
  val qualify: string -> string -> string
  val is_qualified: string -> bool
  val qualifier: string -> string
  val base_name: string -> string
  val map_base_name: (string -> string) -> string -> string
  val count: string -> int
  val hidden: string -> string
  val is_hidden: string -> bool
  val dest_hidden: string -> string option
  val localN: string
  val dest_local: string -> string option
  val implode: string list -> string
  val explode: string -> string list
  type chunks
  val count_chunks: chunks -> int
  val size_chunks: chunks -> int
  val empty_chunks: chunks
  val is_empty_chunks: chunks -> bool
  val base_chunks: string -> chunks
  val suppress_chunks: int -> bool list -> string -> chunks
  val make_chunks: string -> chunks
  val explode_chunks: chunks -> string list
  val implode_chunks: chunks -> string
  val compare_chunks: chunks * chunks -> order
  val eq_chunks: chunks * chunks -> bool
  structure Chunks: CHANGE_TABLE
end;

structure Long_Name: LONG_NAME =
struct

(* long names separated by "." *)

val separator = ".";
val separator_char = String.nth separator 0;

fun append name1 "" = name1
  | append "" name2 = name2
  | append name1 name2 = name1 ^ separator ^ name2;

fun qualify qual name =
  if qual = "" orelse name = "" then name
  else qual ^ separator ^ name;

fun last_separator name =
  let fun last i = if i < 0 orelse String.nth name i = separator_char then i else last (i - 1)
  in last (size name - 1) end;

fun is_qualified name = last_separator name >= 0;

fun qualifier name =
  let val i = last_separator name
  in if i < 0 then "" else String.substring (name, 0, i) end;

fun base_name name =
  let
    val i = last_separator name;
    val j = i + 1;
  in if i < 0 then name else String.substring (name, j, size name - j) end;

fun map_base_name f name =
  if name = "" then ""
  else qualify (qualifier name) (f (base_name name));

fun count "" = 0
  | count name = String.fold (fn c => c = separator_char ? Integer.add 1) name 1;

val hidden_prefix = "??."
val hidden = prefix hidden_prefix;
val is_hidden = String.isPrefix hidden_prefix;
val dest_hidden = try (unprefix hidden_prefix);

val localN = "local";
val dest_local = try (unprefix "local.");

val implode = space_implode separator;
val explode = space_explode separator;


(* compact representation of chunks *)

local

fun failure string msg =
  raise Fail ("Malformed qualified name " ^ quote string ^ ":\n  " ^ msg);

val range_limit = 32768;

val _ =
  if ML_Heap.sizeof1 (range_limit * (range_limit - 1)) = 0 then ()
  else raise Fail ("Bad Long_Name.range_limit for ML platform " ^ ML_System.platform);

fun range string index len =
  if len < range_limit then index * range_limit + len
  else failure string ("chunk length beyond " ^ string_of_int range_limit);

fun range_index r = r div range_limit;
fun range_length r = r mod range_limit;
fun range_string s r = String.substring (s, range_index r, range_length r);

val range_empty = 0;
val ranges_empty: int vector = Vector.fromList [];

in

abstype chunks = Chunks of {range0: int, ranges: int list (*reverse*), string: string}
with

val empty_chunks = Chunks {range0 = range_empty, ranges = [], string = ""};

fun is_empty_chunks (Chunks {range0, ranges, ...}) =
  range0 = range_empty andalso null ranges;

fun count_chunks (chunks as Chunks {ranges, ...}) =
  if is_empty_chunks chunks then 0
  else length ranges + 1;

fun size_chunks (chunks as Chunks {range0, ranges, ...}) =
  if is_empty_chunks chunks then 0
  else fold (fn r => fn n => n + range_length r + 1) ranges (range_length range0);

fun base_chunks name =
  let
    val i = last_separator name;
    val j = i + 1;
  in
    if i < 0 then empty_chunks
    else Chunks {range0 = range name j (size name - j), ranges = [], string = name}
  end;

fun suppress_chunks suppress1 suppress2 string =
  let
    val n = size string;

    fun suppr_chunks suppr1 suppr2 i j rs =
      let
        val string_end = i >= n;
        val chunk_end = string_end orelse String.nth string i = separator_char;

        val suppr =
          if suppr1 > 0 then true
          else if suppr1 < 0 then false
          else if null suppr2 then false
          else hd suppr2;
        val suppr1' =
          if chunk_end andalso suppr1 > 0 then suppr1 - 1
          else if chunk_end andalso suppr1 < 0 then suppr1 + 1
          else suppr1;
        val suppr2' =
          if chunk_end andalso suppr1 = 0 andalso not (null suppr2)
          then tl suppr2 else suppr2;

        val i' = i + 1;
        val j' = if chunk_end then i' else j;
        val rs' = if chunk_end andalso not suppr then range string j (i - j) :: rs else rs;
      in
        if not string_end then suppr_chunks suppr1' suppr2' i' j' rs'
        else if not (suppr1' = 0 andalso null suppr2') then
          failure string ("cannot suppress chunks beyond " ^ string_of_int (length rs'))
        else
          (case rs' of
            [] => empty_chunks
          | r0 :: rest => Chunks {range0 = r0, ranges = rest, string = string})
      end;
  in suppr_chunks suppress1 suppress2 0 0 [] end;

val make_chunks = suppress_chunks 0 [];

fun explode_chunks (chunks as Chunks {range0, ranges, string}) =
  if is_empty_chunks chunks then []
  else fold (cons o range_string string) ranges [range_string string range0];

fun implode_chunks (chunks as Chunks {range0, ranges, string}) =
  if size_chunks chunks = size string then string
  else if null ranges then range_string string range0
  else implode (explode_chunks chunks);

val compare_chunks = pointer_eq_ord (fn (chunks1, chunks2) =>
  let
    val Chunks {range0 = range01, ranges = ranges1, string = string1} = chunks1;
    val Chunks {range0 = range02, ranges = ranges2, string = string2} = chunks2;
    val count1 = count_chunks chunks1;
    val count2 = count_chunks chunks2;

    val range_length_ord = int_ord o apply2 range_length;
    fun range_substring_ord arg =
      let
        val (i, j) = apply2 range_index arg;
        val (m, n) = apply2 range_length arg;

        fun substring_ord k =
          if k < n then
            (case Char.compare (String.nth string1 (i + k), String.nth string2 (j + k)) of
              EQUAL => substring_ord (k + 1)
            | ord => ord)
          else EQUAL;
      in (case int_ord (m, n) of EQUAL => substring_ord 0 | ord => ord) end;
  in
    if count1 = 0 andalso count2 = 0 then EQUAL
    else
      (case int_ord (count1, count2) of
        EQUAL =>
          (case range_length_ord (range01, range02) of
            EQUAL =>
              (case dict_ord range_length_ord (ranges1, ranges2) of
                EQUAL =>
                  (case range_substring_ord (range01, range02) of
                    EQUAL => dict_ord range_substring_ord (ranges1, ranges2)
                  | ord => ord)
              | ord => ord)
          | ord => ord)
      | ord => ord)
  end);

val eq_chunks = is_equal o compare_chunks;

end;

end;

structure Chunks = Change_Table(type key = chunks val ord = compare_chunks);

end;
