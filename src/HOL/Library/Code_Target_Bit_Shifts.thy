(*  Title:      HOL/Library/Code_Target_Bit_Shifts.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Implementation of bit-shifts on target-language integers by built-in operations\<close>

theory Code_Target_Bit_Shifts
imports Main
begin

context
begin

qualified definition push_bit :: \<open>integer \<Rightarrow> integer \<Rightarrow> integer\<close>
  where \<open>push_bit i k = Bit_Operations.push_bit (nat_of_integer \<bar>i\<bar>) k\<close>

qualified lemma push_bit_code [code]:
  \<open>push_bit i k = k * 2 ^ nat_of_integer \<bar>i\<bar>\<close>
  by (simp add: push_bit_def push_bit_eq_mult)

lemma push_bit_integer_code [code]:
  \<open>Bit_Operations.push_bit n k = push_bit (of_nat n) k\<close>
  by (simp add: push_bit_def)

qualified definition drop_bit :: \<open>integer \<Rightarrow> integer \<Rightarrow> integer\<close>
  where \<open>drop_bit i k = Bit_Operations.drop_bit (nat_of_integer \<bar>i\<bar>) k\<close>

qualified lemma drop_bit_code [code]:
  \<open>drop_bit i k = k div 2 ^ nat_of_integer \<bar>i\<bar>\<close>
  by (simp add: drop_bit_def drop_bit_eq_div)

lemma drop_bit_integer_code [code]:
  \<open>Bit_Operations.drop_bit n k = drop_bit (of_nat n) k\<close>
  by (simp add: drop_bit_def)

end

code_printing code_module Bit_Shifts \<rightharpoonup>
    (SML) \<open>
structure Bit_Shifts : sig
  type int = IntInf.int
  val push : int -> int -> int
  val drop : int -> int -> int
end = struct

type int = IntInf.int;

fun curry f x y = f (x, y);

fun fold _ [] y = y
  | fold f (x :: xs) y = fold f xs (f x y);

fun replicate n x = (if n <= 0 then [] else x :: replicate (n - 1) x);

val exp = curry IntInf.pow 2;

val div_mod = curry IntInf.divMod;

val max_index = exp (Word.wordSize - 3) - 1; (*experimentally determined*)

val word_of_int = Word.fromLargeInt o IntInf.toLarge;

val word_max_index = word_of_int max_index;

fun words_of_int k = case div_mod k max_index
  of (b, s) => word_of_int s :: (replicate b word_max_index);

fun push' i k = IntInf.<< (k, i);

fun drop' i k = IntInf.~>> (k, i);

(* The implementations are formally total, though indices >~ max_index will produce heavy computation load *)

fun push i = fold push' (words_of_int (IntInf.abs i));

fun drop i = fold drop' (words_of_int (IntInf.abs i));

end;\<close> for constant Code_Target_Bit_Shifts.push_bit Code_Target_Bit_Shifts.drop_bit
    and (OCaml) \<open>
module Bit_Shifts : sig
  val push : Z.t -> Z.t -> Z.t
  val drop : Z.t -> Z.t -> Z.t
end = struct

let curry f x y = f (x, y);;

let rec fold f xs y = match xs with
  [] -> y
  | (x :: xs) -> fold f xs (f x y);;

let rec replicate n x = (if Z.leq n Z.zero then [] else x :: replicate (Z.pred n) x);;

let max_index = Z.of_int max_int;;

let splitIndex i = let (b, s) = Z.div_rem i max_index
  in Z.to_int s :: (replicate b max_int);;

let push' i k = Z.shift_left k i;;

let drop' i k = Z.shift_right k i;;

(* The implementations are formally total, though indices >~ max_index will produce heavy computation load *)

let push i = fold push' (splitIndex (Z.abs i));;

let drop i = fold drop' (splitIndex (Z.abs i));;

end;;
\<close> for constant Code_Target_Bit_Shifts.push_bit Code_Target_Bit_Shifts.drop_bit
    and (Haskell) \<open>
module Bit_Shifts where

import Prelude (Int, Integer, toInteger, fromInteger, maxBound, divMod, (-), (<=), abs, flip)
import GHC.Bits (Bits)
import Data.Bits (shiftL, shiftR)

fold :: (a -> b -> b) -> [a] -> b -> b
fold _ [] y = y
fold f (x : xs) y = fold f xs (f x y)

replicate :: Integer -> a -> [a]
replicate k x = if k <= 0 then [] else x : replicate (k - 1) x

maxIndex :: Integer
maxIndex = toInteger (maxBound :: Int)

splitIndex :: Integer -> [Int]
splitIndex i = fromInteger s : replicate (fromInteger b) maxBound
  where (b, s) = i `divMod` maxIndex

{- The implementations are formally total, though indices >~ maxIndex will produce heavy computation load -}

push' :: Int -> Int -> Int
push' i = flip shiftL (abs i)

push :: Integer -> Integer -> Integer
push i = fold (flip shiftL) (splitIndex (abs i))

drop' :: Int -> Int -> Int
drop' i = flip shiftR (abs i)

drop :: Integer -> Integer -> Integer
drop i = fold (flip shiftR) (splitIndex (abs i))
\<close> for constant Code_Target_Bit_Shifts.push_bit Code_Target_Bit_Shifts.drop_bit
    and (Scala) \<open>
object Bit_Shifts {

private val maxIndex : BigInt = BigInt(Int.MaxValue);

private def replicate[A](i : BigInt, x : A) : List[A] =
  i <= 0 match {
    case true => Nil
    case false => x :: replicate[A](i - 1, x)
  }

private def splitIndex(i : BigInt) : List[Int] = {
  val (b, s) = i /% maxIndex
  return s.intValue :: replicate(b, Int.MaxValue)
}

/* The implementations are formally total, though indices >~ maxIndex will produce heavy computation load */

def push(i: BigInt, k: BigInt) : BigInt =
  splitIndex(i).foldLeft(k) { (l, j) => l << j }

def drop(i: BigInt, k: BigInt) : BigInt =
  splitIndex(i).foldLeft(k) { (l, j) => l >> j }

}
\<close> for constant Code_Target_Bit_Shifts.push_bit Code_Target_Bit_Shifts.drop_bit
| constant Code_Target_Bit_Shifts.push_bit \<rightharpoonup>
    (SML) "Bit'_Shifts.push"
    and (OCaml) "Bit'_Shifts.push"
    and (Haskell) "Bit'_Shifts.push"
    and (Haskell_Quickcheck) "Bit'_Shifts.push'"
    and (Scala) "Bit'_Shifts.push"
| constant Code_Target_Bit_Shifts.drop_bit \<rightharpoonup>
    (SML) "Bit'_Shifts.drop"
    and (OCaml) "Bit'_Shifts.drop"
    and (Haskell) "Bit'_Shifts.drop"
    and (Haskell_Quickcheck) "Bit'_Shifts.drop'"
    and (Scala) "Bit'_Shifts.drop"

code_reserved
  (SML) Bit_Shifts
  and (Haskell) Bit_Shifts
  and (Scala) Bit_Shifts

end
