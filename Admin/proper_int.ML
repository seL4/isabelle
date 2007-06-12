(*  Title:      Pure/ML-Systems/proper_int.ML
    ID:         $Id$
    Author:     Makarius

SML basis with type int representing proper integers, not machine
words.
*)

local

val mk = IntInf.fromInt: Int.int -> IntInf.int;
val dest = IntInf.toInt: IntInf.int -> Int.int;

in

(* Int *)

structure OrigInt = Int;
structure OrigIntInf = IntInf;
type int = IntInf.int;

structure IntInf =
struct
  open IntInf;
  fun fromInt (a: int) = a;
  fun toInt (a: int) = a;
end;

structure Int = IntInf;


(* List *)

structure List =
struct
  open List;
  fun length a = mk (List.length a);
  fun nth (a, b) = List.nth (a, dest b);
  fun take (a, b) = List.take (a, dest b);
  fun drop (a, b) = List.drop (a, dest b);
  fun tabulate (a, b) = List.tabulate (dest a, b o mk);
end;

val length = List.length;


(* Array *)

structure Array =
struct
  open Array;
  val maxLen = mk Array.maxLen;
  fun array (a, b) = Array.array (dest a, b);
  fun tabulate (a, b) = Array.tabulate (dest a, b o mk);
  fun length a = mk (Array.length a);
  fun sub (a, b) = Array.sub (a, dest b);
  fun update (a, b, c) = Array.update (a, dest b, c);
  fun copy {src, dst, di} = Array.copy {src = src, dst = dst, di = dest di};
  fun copyVec {src, dst, di} = Array.copyVec {src = src, dst = dst, di = dest di};
  fun appi a b = Array.appi (fn (x, y) => a (mk x, y)) b;
  fun modifyi a b = Array.modifyi (fn (x, y) => a (mk x, y)) b;
  fun foldli a b c = Array.foldli (fn (x, y, z) => a (mk x, y, z)) b c;
  fun foldri a b c = Array.foldri (fn (x, y, z) => a (mk x, y, z)) b c;
  fun findi a b =
    (case Array.findi (fn (x, y) => a (mk x, y)) b of
      NONE => NONE
    | SOME (c, d) => SOME (mk c, d));
end;


(* Vector *)

structure Vector =
struct
  open Vector;
  val maxLen = mk Vector.maxLen;
  fun tabulate (a, b) = Vector.tabulate (dest a, b o mk);
  fun length a = mk (Vector.length a);
  fun sub (a, b) = Vector.sub (a, dest b);
  fun update (a, b, c) = Vector.update (a, dest b, c);
  fun appi a b = Vector.appi (fn (x, y) => a (mk x, y)) b;
  fun mapi a b = Vector.mapi (fn (x, y) => a (mk x, y)) b;
  fun foldli a b c = Vector.foldli (fn (x, y, z) => a (mk x, y, z)) b c;
  fun foldri a b c = Vector.foldri (fn (x, y, z) => a (mk x, y, z)) b c;
  fun findi a b =
    (case Vector.findi (fn (x, y) => a (mk x, y)) b of
      NONE => NONE
    | SOME (c, d) => SOME (mk c, d));
end;


(* Char *)

structure Char =
struct
  open Char;
  val maxOrd = mk Char.maxOrd;
  val chr = Char.chr o dest;
  val ord = mk o Char.ord;
end;

val chr = Char.chr;
val ord = Char.ord;


(* String *)

structure String =
struct
  open String;
  val maxSize = mk String.maxSize;
  val size = mk o String.size;
  fun sub (a, b) = String.sub (a, dest b);
  fun extract (a, b, c) = String.extract (a, dest b, Option.map dest c);
  fun substring (a, b, c) = String.substring (a, dest b, dest c);
end;

val size = String.size;
val substring = String.substring;


(* Substring *)

structure Substring =
struct
  open Substring;
  fun sub (a, b) = Substring.sub (a, dest b);
  val size = mk o Substring.size;
  fun base a = let val (b, c, d) = Substring.base a in (b, mk c, mk d) end;
  fun extract (a, b, c) = Substring.extract (a, dest b, Option.map dest c);
  fun substring (a, b, c) = Substring.substring (a, dest b, dest c);
  fun triml a b = Substring.triml (dest a) b;
  fun trimr a b = Substring.trimr (dest a) b;
  fun slice (a, b, c) = Substring.slice (a, dest b, Option.map dest c);
  fun splitAt (a, b) = Substring.splitAt (a, dest b);
end;


(* Word *)

structure Word =
struct
  open Word;
  val wordSize = mk Word.wordSize;
  val toInt = mk o Word.toInt;
  val toIntX = mk o Word.toIntX;
  val fromInt = Word.fromInt o dest;
end;


(* Real *)

structure Real =
struct
  open Real;
  val radix = mk Real.radix;
  val precision = mk Real.precision;
  fun sign a = mk (Real.sign a);
  fun toManExp a = let val {man, exp} = Real.toManExp a in {man = man, exp = mk exp} end;
  fun fromManExp {man, exp} = Real.fromManExp {man = man, exp = dest exp};
  val ceil = mk o Real.ceil;
  val floor = mk o Real.floor;
  val real = Real.fromInt o dest;
  val round = mk o Real.round;
  val trunc = mk o Real.trunc;
  fun toInt a b = mk (Real.toInt a b);
  fun fromInt a = Real.fromInt (dest a);
end;

val ceil = Real.ceil;
val floor = Real.floor;
val real = Real.real;
val round = Real.round;
val trunc = Real.trunc;


(* TextIO *)

structure TextIO =
struct
  open TextIO;
  fun inputN (a, b) = TextIO.inputN (a, dest b);
  fun canInput (a, b) = Option.map mk (TextIO.canInput (a, dest b));
end;


(* Time *)

structure Time =
struct
  open Time;
  fun fmt a b = Time.fmt (dest a) b;
end;

end;
