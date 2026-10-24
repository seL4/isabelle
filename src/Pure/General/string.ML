(*  Title:      Pure/General/string.ML
    Author:     Makarius

Additional operations for structure String, following Isabelle/ML conventions.

NB: Isabelle normally works with Symbol.symbol, which is represented as a
small string fragment. Raw type char is rarely useful.
*)

signature STRING =
sig
  include STRING
  val nth: string -> int -> char
  val nth_str: string -> int -> string
  val exists: (char -> bool) -> string -> bool
  val forall: (char -> bool) -> string -> bool
  val exists_str: (string -> bool) -> string -> bool
  val forall_str: (string -> bool) -> string -> bool
  val member: string -> char -> bool
  val member_str: string -> string -> bool
  val fold: (char -> 'a -> 'a) -> string -> 'a -> 'a
  val fold_rev: (char -> 'a -> 'a) -> string -> 'a -> 'a
  val fold_str: (string -> 'a -> 'a) -> string -> 'a -> 'a
  val fold_rev_str: (string -> 'a -> 'a) -> string -> 'a -> 'a
  val explode_str: string -> string list
  val translate_str: (string -> string) -> string -> string
end;

structure String: STRING =
struct

open String;

fun nth str i = String.sub (str, i);
fun nth_str str = String.str o nth str;

fun exists pred str =
  let
    val n = size str;
    fun ex i = Int.< (i, n) andalso (pred (nth str i) orelse ex (i + 1));
  in ex 0 end;

fun forall pred = not o exists (not o pred);

fun exists_str pred = exists (pred o String.str);
fun forall_str pred = forall (pred o String.str);

fun member str c = exists (fn c' => c = c') str;
fun member_str str s = exists_str (fn s' => s = s') str;

fun fold f str x0 =
  let
    val n = size str;
    fun iter (x, i) = if Int.< (i, n) then iter (f (nth str i) x, i + 1) else x;
  in iter (x0, 0) end;

fun fold_rev f str x0 =
  let
    val n = size str;
    fun iter (x, i) = if Int.>= (i, 0) then iter (f (nth str i) x, i - 1) else x;
  in iter (x0, n - 1) end;

fun fold_str f = fold (f o String.str);
fun fold_rev_str f = fold_rev (f o String.str);

fun explode_str str = fold_rev_str (fn c => fn cs => c :: cs) str [];

fun translate_str f = String.translate (f o String.str);

end;
