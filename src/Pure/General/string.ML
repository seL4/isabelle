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
  val exists: (char -> bool) -> string -> bool
  val forall: (char -> bool) -> string -> bool
  val member: string -> char -> bool
  val fold: (char -> 'a -> 'a) -> string -> 'a -> 'a
  val fold_rev: (char -> 'a -> 'a) -> string -> 'a -> 'a
end;

structure String: STRING =
struct

open String;

fun nth str i = sub (str, i);

fun exists pred str =
  let
    val n = size str;
    fun ex i = Int.< (i, n) andalso (pred (nth str i) orelse ex (i + 1));
  in ex 0 end;

fun forall pred = not o exists (not o pred);

fun member str c = exists (fn c' => c = c') str;

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

end;
