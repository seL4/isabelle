(*  Title:      HOL/Tools/Nitpick/nitpick_util.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009

General-purpose functions used by the Nitpick modules.
*)

signature NITPICK_UTIL =
sig
  type styp = string * typ
  datatype polarity = Pos | Neg | Neut

  exception ARG of string * string
  exception BAD of string * string
  exception LIMIT of string * string
  exception NOT_SUPPORTED of string
  exception SAME of unit

  val nitpick_prefix : string
  val curry3 : ('a * 'b * 'c -> 'd) -> 'a -> 'b -> 'c -> 'd
  val pairf : ('a -> 'b) -> ('a -> 'c) -> 'a -> 'b * 'c
  val int_for_bool : bool -> int
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
  val serial_commas : string -> string list -> string list
  val plural_s : int -> string
  val plural_s_for_list : 'a list -> string
  val flip_polarity : polarity -> polarity
  val prop_T : typ
  val bool_T : typ
  val nat_T : typ
  val int_T : typ
  val subscript : string -> string
  val nat_subscript : int -> string
  val time_limit : Time.time option -> ('a -> 'b) -> 'a -> 'b
  val DETERM_TIMEOUT : Time.time option -> tactic -> tactic
  val setmp_show_all_types : ('a -> 'b) -> 'a -> 'b
  val indent_size : int
  val pstrs : string -> Pretty.T list
  val plain_string_from_yxml : string -> string
  val maybe_quote : string -> string
end

structure Nitpick_Util : NITPICK_UTIL =
struct

type styp = string * typ

datatype polarity = Pos | Neg | Neut

exception ARG of string * string
exception BAD of string * string
exception LIMIT of string * string
exception NOT_SUPPORTED of string
exception SAME of unit

val nitpick_prefix = "Nitpick."

(* ('a * 'b * 'c -> 'd) -> 'a -> 'b -> 'c -> 'd *)
fun curry3 f = fn x => fn y => fn z => f (x, y, z)

(* ('a -> 'b) -> ('a -> 'c) -> 'a -> 'b * 'c *)
fun pairf f g x = (f x, g x)

(* bool -> int *)
fun int_for_bool b = if b then 1 else 0
(* int -> int -> int *)
fun nat_minus i j = if i > j then i - j else 0

val max_exponent = 16384

(* int -> int -> int *)
fun reasonable_power a 0 = 1
  | reasonable_power a 1 = a
  | reasonable_power 0 _ = 0
  | reasonable_power 1 _ = 1
  | reasonable_power a b =
    if b < 0 orelse b > max_exponent then
      raise LIMIT ("Nitpick_Util.reasonable_power",
                   "too large exponent (" ^ signed_string_of_int b ^ ")")
    else
      let
        val c = reasonable_power a (b div 2) in
          c * c * reasonable_power a (b mod 2)
        end

(* int -> int -> int *)
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

(* int -> int -> int *)
fun exact_root m n =
  let val r = Math.pow (Real.fromInt n, 1.0 / (Real.fromInt m)) |> Real.round in
    if reasonable_power r m = n then
      r
    else
      raise ARG ("Nitpick_Util.exact_root",
                 commas (map signed_string_of_int [m, n]))
  end

(* ('a -> 'a -> 'a) -> 'a list -> 'a *)
fun fold1 f = foldl1 (uncurry f)

(* int -> 'a list -> 'a list *)
fun replicate_list 0 _ = []
  | replicate_list n xs = xs @ replicate_list (n - 1) xs

(* int list -> int list *)
fun offset_list ns = rev (tl (fold (fn x => fn xs => (x + hd xs) :: xs) ns [0]))
(* int -> int -> int list *)
fun index_seq j0 n = if j0 < 0 then j0 downto j0 - n + 1 else j0 upto j0 + n - 1

(* int list -> 'a list -> 'a list *)
fun filter_indices js xs =
  let
    (* int -> int list -> 'a list -> 'a list *)
    fun aux _ [] _ = []
      | aux i (j :: js) (x :: xs) =
        if i = j then x :: aux (i + 1) js xs else aux (i + 1) (j :: js) xs
      | aux _ _ _ = raise ARG ("Nitpick_Util.filter_indices",
                               "indices unordered or out of range")
  in aux 0 js xs end
fun filter_out_indices js xs =
  let
    (* int -> int list -> 'a list -> 'a list *)
    fun aux _ [] xs = xs
      | aux i (j :: js) (x :: xs) =
        if i = j then aux (i + 1) js xs else x :: aux (i + 1) (j :: js) xs
      | aux _ _ _ = raise ARG ("Nitpick_Util.filter_out_indices",
                               "indices unordered or out of range")
  in aux 0 js xs end

(* 'a list -> 'a list list -> 'a list list *)
fun cartesian_product [] _ = []
  | cartesian_product (x :: xs) yss =
    map (cons x) yss @ cartesian_product xs yss
(* 'a list list -> 'a list list *)
fun n_fold_cartesian_product xss = fold_rev cartesian_product xss [[]]
(* ''a list -> (''a * ''a) list *)
fun all_distinct_unordered_pairs_of [] = []
  | all_distinct_unordered_pairs_of (x :: xs) =
    map (pair x) xs @ all_distinct_unordered_pairs_of xs

(* (int * int) list -> int -> int list *)
val nth_combination =
  let
    (* (int * int) list -> int -> int list * int *)
    fun aux [] n = ([], n)
      | aux ((k, j0) :: xs) n =
        let val (js, n) = aux xs n in ((n mod k) + j0 :: js, n div k) end
  in fst oo aux end

(* (int * int) list -> int list list *)
val all_combinations = n_fold_cartesian_product o map (uncurry index_seq o swap)

(* 'a list -> 'a list list *)
fun all_permutations [] = [[]]
  | all_permutations xs =
    maps (fn j => map (cons (nth xs j)) (all_permutations (nth_drop j xs)))
         (index_seq 0 (length xs))

(* int -> 'a list -> 'a list list *)
fun batch_list _ [] = []
  | batch_list k xs =
    if length xs <= k then [xs]
    else List.take (xs, k) :: batch_list k (List.drop (xs, k))

(* int list -> 'a list -> 'a list list *)
fun chunk_list_unevenly _ [] = []
  | chunk_list_unevenly [] ys = map single ys
  | chunk_list_unevenly (k :: ks) ys =
    let val (ys1, ys2) = chop k ys in ys1 :: chunk_list_unevenly ks ys2 end

(* ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list *)
fun map3 _ [] [] [] = []
  | map3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: map3 f xs ys zs
  | map3 _ _ _ _ = raise UnequalLengths

(* ('a * 'a -> bool) -> ('a option * 'b) list -> 'a -> 'b option *)
fun double_lookup eq ps key =
  case AList.lookup (fn (SOME x, SOME y) => eq (x, y) | _ => false) ps
                    (SOME key) of
    SOME z => SOME z
  | NONE => ps |> find_first (is_none o fst) |> Option.map snd
(* (''a * ''a -> bool) -> (''a option * 'b) list -> ''a -> 'b option *)
fun triple_lookup eq ps key =
  case AList.lookup (op =) ps (SOME key) of
    SOME z => SOME z
  | NONE => double_lookup eq ps key

(* string -> string -> bool *)
fun is_substring_of needle stack =
  not (Substring.isEmpty (snd (Substring.position needle
                                                  (Substring.full stack))))

(* string -> string list -> string list *)
fun serial_commas _ [] = ["??"]
  | serial_commas _ [s] = [s]
  | serial_commas conj [s1, s2] = [s1, conj, s2]
  | serial_commas conj [s1, s2, s3] = [s1 ^ ",", s2 ^ ",", conj, s3]
  | serial_commas conj (s :: ss) = s ^ "," :: serial_commas conj ss

(* int -> string *)
fun plural_s n = if n = 1 then "" else "s"
(* 'a list -> string *)
fun plural_s_for_list xs = plural_s (length xs)

(* polarity -> polarity *)
fun flip_polarity Pos = Neg
  | flip_polarity Neg = Pos
  | flip_polarity Neut = Neut

val prop_T = @{typ prop}
val bool_T = @{typ bool}
val nat_T = @{typ nat}
val int_T = @{typ int}

(* string -> string *)
val subscript = implode o map (prefix "\<^isub>") o explode
(* int -> string *)
val nat_subscript = subscript o signed_string_of_int

(* Time.time option -> ('a -> 'b) -> 'a -> 'b *)
fun time_limit NONE f = f
  | time_limit (SOME delay) f = TimeLimit.timeLimit delay f

(* Time.time option -> tactic -> tactic *)
fun DETERM_TIMEOUT delay tac st =
  Seq.of_list (the_list (time_limit delay (fn () => SINGLE tac st) ()))

(* ('a -> 'b) -> 'a -> 'b *)
fun setmp_show_all_types f =
  setmp_CRITICAL show_all_types
                 (! show_types orelse ! show_sorts orelse ! show_all_types) f

val indent_size = 2

(* string -> Pretty.T list *)
val pstrs = Pretty.breaks o map Pretty.str o space_explode " "

(* XML.tree -> string *)
fun plain_string_from_xml_tree t =
  Buffer.empty |> XML.add_content t |> Buffer.content
(* string -> string *)
val plain_string_from_yxml = plain_string_from_xml_tree o YXML.parse

(* string -> bool *)
val is_long_identifier = forall Syntax.is_identifier o space_explode "."
(* string -> string *)
fun maybe_quote y =
  let val s = plain_string_from_yxml y in
    y |> (not (is_long_identifier (perhaps (try (unprefix "'")) s))
          orelse OuterKeyword.is_keyword s) ? quote
  end

end;
