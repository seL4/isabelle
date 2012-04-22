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
  val pretty_serial_commas : string -> Pretty.T list -> Pretty.T list
  val parse_bool_option : bool -> string -> string -> bool option
  val parse_time_option : string -> string -> Time.time option
  val string_from_time : Time.time -> string
  val nat_subscript : int -> string
  val flip_polarity : polarity -> polarity
  val prop_T : typ
  val bool_T : typ
  val nat_T : typ
  val int_T : typ
  val simple_string_of_typ : typ -> string
  val is_real_constr : theory -> string * typ -> bool
  val typ_of_dtyp : Datatype.descr -> (Datatype.dtyp * typ) list -> Datatype.dtyp -> typ
  val varify_type : Proof.context -> typ -> typ
  val instantiate_type : theory -> typ -> typ -> typ -> typ
  val varify_and_instantiate_type : Proof.context -> typ -> typ -> typ -> typ
  val is_of_class_const : theory -> string * typ -> bool
  val get_class_def : theory -> string -> (string * term) option
  val monomorphic_term : Type.tyenv -> term -> term
  val specialize_type : theory -> string * typ -> term -> term
  val eta_expand : typ list -> term -> int -> term
  val time_limit : Time.time option -> ('a -> 'b) -> 'a -> 'b
  val DETERM_TIMEOUT : Time.time option -> tactic -> tactic
  val set_show_all_types : Proof.context -> Proof.context
  val indent_size : int
  val pstrs : string -> Pretty.T list
  val unyxml : string -> string
  val pretty_maybe_quote : Pretty.T -> Pretty.T
  val hash_term : term -> int
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

val nitpick_prefix = "Nitpick" ^ Long_Name.separator

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
                       "too large exponent (" ^ signed_string_of_int a ^ " ^ " ^
                       signed_string_of_int b ^ ")")
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
  | map3 _ _ _ _ = raise ListPair.UnequalLengths

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

val serial_commas = Try.serial_commas

fun pretty_serial_commas _ [] = []
  | pretty_serial_commas _ [p] = [p]
  | pretty_serial_commas conj [p1, p2] =
    [p1, Pretty.brk 1, Pretty.str conj, Pretty.brk 1, p2]
  | pretty_serial_commas conj [p1, p2, p3] =
    [p1, Pretty.str ",", Pretty.brk 1, p2, Pretty.str ",", Pretty.brk 1,
     Pretty.str conj, Pretty.brk 1, p3]
  | pretty_serial_commas conj (p :: ps) =
    p :: Pretty.str "," :: Pretty.brk 1 :: pretty_serial_commas conj ps

val parse_bool_option = Sledgehammer_Util.parse_bool_option
val parse_time_option = Sledgehammer_Util.parse_time_option
val string_from_time = ATP_Util.string_from_time

val i_subscript = implode o map (prefix "\<^isub>") o raw_explode  (* FIXME Symbol.explode (?) *)
fun be_subscript s = "\<^bsub>" ^ s ^ "\<^esub>"
fun nat_subscript n =
  let val s = signed_string_of_int n in
    if print_mode_active Symbol.xsymbolsN then
      (* cheap trick to ensure proper alphanumeric ordering for one- and
         two-digit numbers *)
      (if n <= 9 then be_subscript else i_subscript) s
    else
      s
  end

fun flip_polarity Pos = Neg
  | flip_polarity Neg = Pos
  | flip_polarity Neut = Neut

val prop_T = @{typ prop}
val bool_T = @{typ bool}
val nat_T = @{typ nat}
val int_T = @{typ int}

val simple_string_of_typ = Refute.string_of_typ
val is_real_constr = Refute.is_IDT_constructor
val typ_of_dtyp = ATP_Util.typ_of_dtyp
val varify_type = ATP_Util.varify_type
val instantiate_type = ATP_Util.instantiate_type
val varify_and_instantiate_type = ATP_Util.varify_and_instantiate_type
val is_of_class_const = Refute.is_const_of_class
val get_class_def = Refute.get_classdef
val monomorphic_term = ATP_Util.monomorphic_term
val specialize_type = ATP_Util.specialize_type
val eta_expand = ATP_Util.eta_expand

fun time_limit NONE = I
  | time_limit (SOME delay) = TimeLimit.timeLimit delay

fun DETERM_TIMEOUT delay tac st =
  Seq.of_list (the_list (time_limit delay (fn () => SINGLE tac st) ()))

fun set_show_all_types ctxt =
  Config.put show_all_types
    (Config.get ctxt show_types orelse Config.get ctxt show_sorts
      orelse Config.get ctxt show_all_types) ctxt

val indent_size = 2

val pstrs = Pretty.breaks o map Pretty.str o space_explode " "

val unyxml = ATP_Util.unyxml

val maybe_quote = ATP_Util.maybe_quote
fun pretty_maybe_quote pretty =
  let val s = Pretty.str_of pretty in
    if maybe_quote s = s then pretty else Pretty.enum "" "\"" "\"" [pretty]
  end

val hash_term = ATP_Util.hash_term

end;
