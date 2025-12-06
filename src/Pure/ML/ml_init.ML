(*  Title:      Pure/ML/ml_init.ML
    Author:     Makarius

Initial ML environment.
*)

val seconds = Time.fromReal;

val _ =
  List.app ML_Name_Space.forget_val
    ["isSome", "getOpt", "valOf", "foldl", "foldr", "print", "explode", "concat", "Interrupt"];

val ord = SML90.ord;
val chr = SML90.chr;
val raw_explode = SML90.explode;
val implode = String.concat;

val pointer_eq = PolyML.pointerEq;

val error_depth = PolyML.error_depth;

structure Basic_Exn: BASIC_EXN = Exn;
open Basic_Exn;

structure String =
struct
  open String;
  fun substring (s, i, n) =
    if n = 1 then String.str (String.sub (s, i))
    else String.substring (s, i, n);
end;

structure Substring =
struct
  open Substring;
  val empty = full "";

local
  val chars = Vector.tabulate (Char.maxOrd, Substring.full o String.str o Char.chr);
in
  fun full str =
    (case String.size str of
      0 => empty
    | 1 => Vector.sub (chars, Char.ord (String.sub (str, 0)))
    | _ => Substring.full str);
end;

end;

structure IntInf =
struct
  open IntInf;

  (*workaround for https://github.com/polyml/polyml/issues/243*)
  (*see also https://github.com/polyml/polyml/commit/ed1ff06d7b53*)
  local
    val max_shift = Word.fromInt Word.wordSize;
    val full_shift = pow (2, Word.wordSize);

    fun shift_left (i: int, j: Word.word) =
      if Word.< (j, max_shift)
      then i * Word.toLargeInt (Word.<< (0w1, j))
      else shift_left (i * full_shift, Word.- (j, max_shift));

    fun shift_right (i: int, j: Word.word) =
      if RunCall.isShort i
      then Word.toLargeIntX (Word.~>> (Word.fromLargeInt i, j))
      else LargeInt.div (i, pow (2, Word.toInt j));
  in
    val op << = shift_left;
    val op ~>> = shift_right;
  end
end;
