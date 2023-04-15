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
  val make_chunks: bool list -> string -> chunks
  val chunks: string -> chunks
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

fun mask_bad s = s = 0w0;
fun mask_set s m = Word.orb (m, s);
fun mask_push s = Word.<< (s, 0w1);
fun mask_next m = Word.>> (m, 0w1);
fun mask_keep m = Word.andb (m, 0w1) = 0w0;

fun string_ops string =
  let
    val n = size string;
    val char = String.nth string;
    fun string_end i = i >= n;
    fun chunk_end i = string_end i orelse char i = separator_char;
  in {string_end = string_end, chunk_end = chunk_end} end;

in

abstype chunks = Chunks of {count: int, size: int, mask: word, string: string}
with

fun count_chunks (Chunks {count, ...}) = count;
fun size_chunks (Chunks {size, ...}) = size;

val empty_chunks = Chunks {count = 0, size = 0, mask = 0w0, string = ""};

fun make_chunks suppress string =
  let
    val {string_end, chunk_end, ...} = string_ops string;

    fun err msg = raise Fail ("Malformed qualified name " ^ quote string ^ ":\n  " ^ msg);

    fun make suppr i k l m s =
      let
        val is_end = chunk_end i;
        val keep = null suppr orelse not (hd suppr);

        val suppr' = if is_end andalso not (null suppr) then tl suppr else suppr;
        val l' = if keep then l + 1 else l;
        val k' = if is_end andalso keep andalso l' > 0 then k + 1 else k;
        val m' =
          if not is_end orelse keep then m
          else if mask_bad s then
            err ("cannot suppress chunks beyond word size " ^ string_of_int Word.wordSize)
          else mask_set s m;
        val s' = if is_end then mask_push s else s;
      in
        if not (string_end i) then make suppr' (i + 1) k' l' m' s'
        else if not (null suppr') then err ("cannot suppress chunks beyond " ^ string_of_int k')
        else if k' = 0 then empty_chunks
        else Chunks {count = k', size = Int.max (0, l' - 1), mask = m', string = string}
      end;
  in make suppress 0 0 0 0w0 0w1 end;

val chunks = make_chunks [];

fun expand_chunks f (Chunks {count, size, mask, string}) =
  let
    val {string_end, chunk_end, ...} = string_ops string;

    fun explode bg en m acc =
      let
        val is_end = chunk_end en;

        val en' = en + 1;
        val bg' = if is_end then en' else bg;
        val m' = if is_end then mask_next m else m;
        val acc' = if is_end andalso mask_keep m then f (string, bg, en - bg) :: acc else acc;
      in if string_end en then rev acc' else explode bg' en' m' acc' end;
  in
    if count = 0 then []
    else if count = 1 andalso size = String.size string then [f (string, 0, size)]
    else explode 0 0 mask []
  end;

val explode_chunks = expand_chunks String.substring;
val implode_chunks = implode o explode_chunks;

val compare_chunks =
  pointer_eq_ord (fn (chunks1, chunks2) =>
    let
      val Chunks args1 = chunks1;
      val Chunks args2 = chunks2;
      val ord1 =
        int_ord o apply2 #size |||
        int_ord o apply2 #count;
      val ord2 =
        dict_ord int_ord o apply2 (expand_chunks #3) |||
        dict_ord Substring.compare o apply2 (expand_chunks Substring.substring);
    in
      (case ord1 (args1, args2) of
        EQUAL =>
          if #mask args1 = #mask args2 andalso #string args1 = #string args2 then EQUAL
          else ord2 (chunks1, chunks2)
      | ord => ord)
    end);

val eq_chunks = is_equal o compare_chunks;

end;

end;

structure Chunks = Change_Table(type key = chunks val ord = compare_chunks);

end;
