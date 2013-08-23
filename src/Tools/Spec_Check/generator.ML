(*  Title:      Tools/Spec_Check/generator.ML
    Author:     Lukas Bulwahn and Nicolai Schaffroth, TU Muenchen
    Author:     Christopher League

Random generators for Isabelle/ML's types.
*)

signature GENERATOR = sig
  include BASE_GENERATOR
  (* text generators *)
  val char : char gen
  val charRange : char * char -> char gen
  val charFrom : string -> char gen
  val charByType : (char -> bool) -> char gen
  val string : (int gen * char gen) -> string gen
  val substring : string gen -> substring gen
  val cochar : (char, 'b) co
  val costring : (string, 'b) co
  val cosubstring : (substring, 'b) co
  (* integer generators *)
  val int : int gen
  val int_pos : int gen
  val int_neg : int gen
  val int_nonpos : int gen
  val int_nonneg : int gen
  val coint : (int, 'b) co
  (* real generators *)
  val real : real gen
  val real_frac : real gen
  val real_pos : real gen
  val real_neg : real gen
  val real_nonpos : real gen
  val real_nonneg : real gen
  val real_finite : real gen
  (* function generators *)
  val function_const : 'c * 'b gen -> ('a -> 'b) gen
  val function_strict : int -> ''a gen * 'b gen -> (''a -> 'b) gen
  val function_lazy : ''a gen * 'b gen -> (''a -> 'b) gen
  val unit : unit gen
  val ref' : 'a gen -> 'a Unsynchronized.ref gen
  (* more generators *)
  val term : int -> term gen
  val typ : int -> typ gen

  val stream : stream
end

structure Generator : GENERATOR =
struct

open Base_Generator

val stream = start (new())

type 'a gen = rand -> 'a * rand
type ('a, 'b) co = 'a -> 'b gen -> 'b gen

(* text *)

type char = Char.char
type string = String.string
type substring = Substring.substring


val char = map Char.chr (range (0, Char.maxOrd))
fun charRange (lo, hi) = map Char.chr (range (Char.ord lo, Char.ord hi))

fun charFrom s =
  choose (Vector.tabulate (String.size s, fn i => lift (String.sub (s, i))))

fun charByType p = filter p char

val string = vector CharVector.tabulate

fun substring gen r =
  let
    val (s, r') = gen r
    val (i, r'') = range (0, String.size s) r'
    val (j, r''') = range (0, String.size s - i) r''
  in
    (Substring.substring (s, i, j), r''')
  end

fun cochar c =
  if Char.ord c = 0 then variant 0
  else variant 1 o cochar (Char.chr (Char.ord c div 2))

fun cosubstring s = Substring.foldr (fn (c,v) => cochar c o v) (variant 0) s

fun costring s = cosubstring (Substring.full s)

(* integers *)
val digit = charRange (#"0", #"9")
val nonzero = string (lift 1, charRange (#"1", #"9"))
fun digits' n = string (range (0, n-1), digit)
fun digits n = map2 op^ (nonzero, digits' n)

val maxDigits = 64
val ratio = 49

fun pos_or_neg f r =
  let
    val (s, r') = digits maxDigits r
  in (f (the (Int.fromString s)), r') end

val int_pos = pos_or_neg I
val int_neg = pos_or_neg Int.~
val zero = lift 0

val int_nonneg = chooseL' [(1, zero), (ratio, int_pos)]
val int_nonpos = chooseL' [(1, zero), (ratio, int_neg)]
val int = chooseL [int_nonneg, int_nonpos]

fun coint n =
  if n = 0 then variant 0
  else if n < 0 then variant 1 o coint (~ n)
  else variant 2 o coint (n div 2)

(* reals *)
val digits = string (range(1, Real.precision), charRange(#"0", #"9"))

fun real_frac r =
  let val (s, r') = digits r
  in (the (Real.fromString s), r') end

val {exp=minExp,...} = Real.toManExp Real.minPos
val {exp=maxExp,...} = Real.toManExp Real.posInf

val ratio = 99

fun mk r =
  let
    val (a, r') = digits r
    val (b, r'') = digits r'
    val (e, r''') = range (minExp div 4, maxExp div 4) r''
    val x = String.concat [a, ".", b, "E", Int.toString e]
  in
    (the (Real.fromString x), r''')
  end

val real_pos = chooseL' (List.map ((pair 1) o lift)
    [Real.posInf, Real.maxFinite, Real.minPos, Real.minNormalPos] @ [(ratio, mk)])

val real_neg = map Real.~ real_pos

val real_zero = Real.fromInt 0
val real_nonneg = chooseL' [(1, lift real_zero), (ratio, real_pos)]
val real_nonpos = chooseL' [(1, lift real_zero), (ratio, real_neg)]

val real = chooseL [real_nonneg, real_nonpos]

val real_finite = filter Real.isFinite real

(*alternate list generator - uses an integer generator to determine list length*)
fun list' int gen = vector List.tabulate (int, gen);

(* more function generators *)

fun function_const (_, gen2) r =
  let
    val (v, r') = gen2 r
  in (fn _ => v, r') end;

fun function_strict size (gen1, gen2) r =
  let
    val (def, r') = gen2 r
    val (table, r'') = list' (fn s => (size, s)) (zip (gen1, gen2)) r'
  in (fn v1 => the_default def (AList.lookup (op =) table v1), r'') end;

fun function_lazy (gen1, gen2) r =
  let
    val (initial1, r') = gen1 r
    val (initial2, internal) = gen2 r'
    val seed = Unsynchronized.ref internal
    val table = Unsynchronized.ref [(initial1, initial2)]
    fun new_entry k =
      let
        val (new_val, new_seed) = gen2 (!seed)
        val _ =  seed := new_seed
        val _ = table := AList.update (op =) (k, new_val) (!table)
      in new_val end
  in
    (fn v1 =>
      case AList.lookup (op =) (!table) v1 of
        NONE => new_entry v1
      | SOME v2 => v2, r')
  end;

(* unit *)

fun unit r = ((), r);

(* references *)

fun ref' gen r =
  let val (value, r') = gen r
  in (Unsynchronized.ref value, r') end;

(* types and terms *)

val sort_string = selectL ["sort1", "sort2", "sort3"];
val type_string = selectL ["TCon1", "TCon2", "TCon3"];
val tvar_string = selectL ["a", "b", "c"];

val const_string = selectL ["c1", "c2", "c3"];
val var_string = selectL ["x", "y", "z"];
val index = selectL [0, 1, 2, 3];
val bound_index = selectL [0, 1, 2, 3];

val sort = list (flip' (1, 2)) sort_string;

fun typ n =
  let
    fun type' m = map Type (zip (type_string, list (flip' (1, 3)) (typ m)))
    val tfree = map TFree (zip (tvar_string, sort))
    val tvar = map TVar (zip (zip (tvar_string, index), sort))
  in
    if n = 0 then chooseL [tfree, tvar]
    else chooseL [type' (n div 2), tfree, tvar]
  end;

fun term n =
  let
    val const = map Const (zip (const_string, typ 10))
    val free = map Free (zip (var_string, typ 10))
    val var = map Var (zip (zip (var_string, index), typ 10))
    val bound = map Bound bound_index
    fun abs m = map Abs (zip3 (var_string, typ 10, term m))
    fun app m = map (op $) (zip (term m, term m))
  in
    if n = 0 then chooseL [const, free, var, bound]
    else chooseL [const, free, var, bound, abs (n - 1), app (n div 2)]
  end;

end
