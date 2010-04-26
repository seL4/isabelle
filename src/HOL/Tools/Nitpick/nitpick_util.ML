(*  Title:      HOL/Tools/Nitpick/nitpick_util.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

General-purpose functions used by the Nitpick modules.
*)

signature NITPICK_UTIL =
sig
  type styp = string * typ
  datatype polarity = Pos | Neg | Neut

  exception ARG of string * string
  exception BAD of string * string
  exception TOO_SMALL of string * string
  exception TOO_LARGE of string * string
  exception NOT_SUPPORTED of string
  exception SAME of unit

  val nitpick_prefix : string
  val curry3 : ('a * 'b * 'c -> 'd) -> 'a -> 'b -> 'c -> 'd
  val pairf : ('a -> 'b) -> ('a -> 'c) -> 'a -> 'b * 'c
  val pair_from_fun : (bool -> 'a) -> 'a * 'a
  val fun_from_pair : 'a * 'a -> bool -> 'a
  val int_from_bool : bool -> int
  val nat_minus : int -> int -> int
  val reasonable_power : int -> int -> int
  val exact_log : int -> int -> int
  val exact_root : int -> int -> int
  val offset_list : int list -> int list
  val index_seq : int -> int -> int list
  val filter_indices : int list -> 'a list -> 'a list
  val filter_out_indices : int list -> 'a list -> 'a list
  val fold1 : ('a -> 'a -> 'a) -> 'a list -> 'a
  val replicate_list : int -> 'a list -> 'a list
  val n_fold_cartesian_product : 'a list list -> 'a list list
  val all_distinct_unordered_pairs_of : ''a list -> (''a * ''a) list
  val nth_combination : (int * int) list -> int -> int list
  val all_combinations : (int * int) list -> int list list
  val all_permutations : 'a list -> 'a list list
  val batch_list : int -> 'a list -> 'a list list
  val chunk_list_unevenly : int list -> 'a list -> 'a list list
  val map3 : ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
  val double_lookup :
    ('a * 'a -> bool) -> ('a option * 'b) list -> 'a -> 'b option
  val triple_lookup :
    (''a * ''a -> bool) -> (''a option * 'b) list -> ''a -> 'b option
  val is_substring_of : string -> string -> bool
  val plural_s : int -> string
  val plural_s_for_list : 'a list -> string
  val serial_commas : string -> string list -> string list
  val timestamp : unit -> string
  val parse_bool_option : bool -> string -> string -> bool option
  val parse_time_option : string -> string -> Time.time option
  val flip_polarity : polarity -> polarity
  val prop_T : typ
  val bool_T : typ
  val nat_T : typ
  val int_T : typ
  val nat_subscript : int -> string
  val time_limit : Time.time option -> ('a -> 'b) -> 'a -> 'b
  val DETERM_TIMEOUT : Time.time option -> tactic -> tactic
  val setmp_show_all_types : ('a -> 'b) -> 'a -> 'b
  val indent_size : int
  val pstrs : string -> Pretty.T list
  val unyxml : string -> string
  val maybe_quote : string -> string
  val hashw : word * word -> word
  val hashw_string : string * word -> word
end;

structure Nitpick_Util : NITPICK_UTIL =
struct

type styp = string * typ

datatype polarity = Pos | Neg | Neut

exception ARG of string * string
exception BAD of string * string
exception TOO_SMALL of string * string
exception TOO_LARGE of string * string
exception NOT_SUPPORTED of string
exception SAME of unit

val nitpick_prefix = "Nitpick."

fun curry3 f = fn x => fn y => fn z => f (x, y, z)

fun pairf f g x = (f x, g x)

fun pair_from_fun f = (f false, f true)
fun fun_from_pair (f, t) b = if b then t else f

fun int_from_bool b = if b then 1 else 0
fun nat_minus i j = if i > j then i - j else 0

val max_exponent = 16384

fun reasonable_power _ 0 = 1
  | reasonable_power a 1 = a
  | reasonable_power 0 _ = 0
  | reasonable_power 1 _ = 1
  | reasonable_power a b =
    if b < 0 then
      raise ARG ("Nitpick_Util.reasonable_power",
                 "negative exponent (" ^ signed_string_of_int b ^ ")")
    else if b > max_exponent then
      raise TOO_LARGE ("Nitpick_Util.reasonable_power",
                       "too large exponent (" ^ signed_string_of_int b ^ ")")
    else
      let val c = reasonable_power a (b div 2) in
        c * c * reasonable_power a (b mod 2)
      end

fun exact_log m n =
  let
    val r = Math.ln (Real.fromInt n) / Math.ln (Real.fromInt m) |> Real.round
  in
    if reasonable_power m r = n then
      r
    else
      raise ARG ("Nitpick_Util.exact_log",
                 commas (map signed_string_of_int [m, n]))
  end

fun exact_root m n =
  let val r = Math.pow (Real.fromInt n, 1.0 / (Real.fromInt m)) |> Real.round in
    if reasonable_power r m = n then
      r
    else
      raise ARG ("Nitpick_Util.exact_root",
                 commas (map signed_string_of_int [m, n]))
  end

fun fold1 f = foldl1 (uncurry f)

fun replicate_list 0 _ = []
  | replicate_list n xs = xs @ replicate_list (n - 1) xs

fun offset_list ns = rev (tl (fold (fn x => fn xs => (x + hd xs) :: xs) ns [0]))
fun index_seq j0 n = if j0 < 0 then j0 downto j0 - n + 1 else j0 upto j0 + n - 1

fun filter_indices js xs =
  let
    fun aux _ [] _ = []
      | aux i (j :: js) (x :: xs) =
        if i = j then x :: aux (i + 1) js xs else aux (i + 1) (j :: js) xs
      | aux _ _ _ = raise ARG ("Nitpick_Util.filter_indices",
                               "indices unordered or out of range")
  in aux 0 js xs end
fun filter_out_indices js xs =
  let
    fun aux _ [] xs = xs
      | aux i (j :: js) (x :: xs) =
        if i = j then aux (i + 1) js xs else x :: aux (i + 1) (j :: js) xs
      | aux _ _ _ = raise ARG ("Nitpick_Util.filter_out_indices",
                               "indices unordered or out of range")
  in aux 0 js xs end

fun cartesian_product [] _ = []
  | cartesian_product (x :: xs) yss =
    map (cons x) yss @ cartesian_product xs yss
fun n_fold_cartesian_product xss = fold_rev cartesian_product xss [[]]
fun all_distinct_unordered_pairs_of [] = []
  | all_distinct_unordered_pairs_of (x :: xs) =
    map (pair x) xs @ all_distinct_unordered_pairs_of xs

val nth_combination =
  let
    fun aux [] n = ([], n)
      | aux ((k, j0) :: xs) n =
        let val (js, n) = aux xs n in ((n mod k) + j0 :: js, n div k) end
  in fst oo aux end

val all_combinations = n_fold_cartesian_product o map (uncurry index_seq o swap)

fun all_permutations [] = [[]]
  | all_permutations xs =
    maps (fn j => map (cons (nth xs j)) (all_permutations (nth_drop j xs)))
         (index_seq 0 (length xs))

fun batch_list _ [] = []
  | batch_list k xs =
    if length xs <= k then [xs]
    else List.take (xs, k) :: batch_list k (List.drop (xs, k))

fun chunk_list_unevenly _ [] = []
  | chunk_list_unevenly [] ys = map single ys
  | chunk_list_unevenly (k :: ks) ys =
    let val (ys1, ys2) = chop k ys in ys1 :: chunk_list_unevenly ks ys2 end

fun map3 _ [] [] [] = []
  | map3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: map3 f xs ys zs
  | map3 _ _ _ _ = raise UnequalLengths

fun double_lookup eq ps key =
  case AList.lookup (fn (SOME x, SOME y) => eq (x, y) | _ => false) ps
                    (SOME key) of
    SOME z => SOME z
  | NONE => ps |> find_first (is_none o fst) |> Option.map snd
fun triple_lookup _ [(NONE, z)] _ = SOME z
  | triple_lookup eq ps key =
    case AList.lookup (op =) ps (SOME key) of
      SOME z => SOME z
    | NONE => double_lookup eq ps key

fun is_substring_of needle stack =
  not (Substring.isEmpty (snd (Substring.position needle
                                                  (Substring.full stack))))

val plural_s = Sledgehammer_Util.plural_s
fun plural_s_for_list xs = plural_s (length xs)

val serial_commas = Sledgehammer_Util.serial_commas

val timestamp = Sledgehammer_Util.timestamp
val parse_bool_option = Sledgehammer_Util.parse_bool_option
val parse_time_option = Sledgehammer_Util.parse_time_option

fun flip_polarity Pos = Neg
  | flip_polarity Neg = Pos
  | flip_polarity Neut = Neut

val prop_T = @{typ prop}
val bool_T = @{typ bool}
val nat_T = @{typ nat}
val int_T = @{typ int}

val subscript = implode o map (prefix "\<^isub>") o explode
fun nat_subscript n =
  (* cheap trick to ensure proper alphanumeric ordering for one- and two-digit
     numbers *)
  if n <= 9 then "\<^bsub>" ^ signed_string_of_int n ^ "\<^esub>"
  else subscript (string_of_int n)

fun time_limit NONE = I
  | time_limit (SOME delay) = TimeLimit.timeLimit delay

fun DETERM_TIMEOUT delay tac st =
  Seq.of_list (the_list (time_limit delay (fn () => SINGLE tac st) ()))

fun setmp_show_all_types f =
  setmp_CRITICAL show_all_types
                 (! show_types orelse ! show_sorts orelse ! show_all_types) f

val indent_size = 2

val pstrs = Pretty.breaks o map Pretty.str o space_explode " "

fun plain_string_from_xml_tree t =
  Buffer.empty |> XML.add_content t |> Buffer.content
val unyxml = plain_string_from_xml_tree o YXML.parse

val is_long_identifier = forall Syntax.is_identifier o space_explode "."
fun maybe_quote y =
  let val s = unyxml y in
    y |> ((not (is_long_identifier (perhaps (try (unprefix "'")) s)) andalso
           not (is_long_identifier (perhaps (try (unprefix "?")) s))) orelse
           OuterKeyword.is_keyword s) ? quote
  end

(* This hash function is recommended in Compilers: Principles, Techniques, and
   Tools, by Aho, Sethi and Ullman. The hashpjw function, which they
   particularly recommend, triggers a bug in versions of Poly/ML up to 4.2.0. *)
fun hashw (u, w) = Word.+ (u, Word.* (0w65599, w))
fun hashw_char (c, w) = hashw (Word.fromInt (Char.ord c), w)
fun hashw_string (s:string, w) = CharVector.foldl hashw_char w s

end;
