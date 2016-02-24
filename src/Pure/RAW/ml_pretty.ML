(*  Title:      Pure/RAW/ml_pretty.ML
    Author:     Makarius

Minimal support for raw ML pretty printing -- for boot-strapping only.
*)

structure ML_Pretty =
struct

datatype pretty =
  Block of (string * string) * bool * FixedInt.int * pretty list |
  String of string * FixedInt.int |
  Break of bool * FixedInt.int * FixedInt.int;

fun block prts = Block (("", ""), false, 2, prts);
fun str s = String (s, FixedInt.fromInt (size s));
fun brk width = Break (false, width, 0);

fun pair pretty1 pretty2 ((x, y), depth: FixedInt.int) =
  block [str "(", pretty1 (x, depth), str ",", brk 1, pretty2 (y, depth - 1), str ")"];

fun enum sep lpar rpar pretty (args, depth: FixedInt.int) =
  let
    fun elems _ [] = []
      | elems 0 _ = [str "..."]
      | elems d [x] = [pretty (x, d)]
      | elems d (x :: xs) = pretty (x, d) :: str sep :: brk 1 :: elems (d - 1) xs;
  in block (str lpar :: (elems (FixedInt.max (depth, 0)) args @ [str rpar])) end;

end;
