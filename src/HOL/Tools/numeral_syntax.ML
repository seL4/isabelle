(*  Title:      HOL/Tools/numeral_syntax.ML
    ID:         $Id$
    Authors:    Markus Wenzel, TU Muenchen

Concrete syntax for generic numerals.  Assumes consts and syntax of
theory HOL/Numeral.
*)

signature NUMERAL_SYNTAX =
sig
  val setup: theory -> theory
end;

structure NumeralSyntax: NUMERAL_SYNTAX =
struct


(* bit strings *)   (*we try to handle superfluous leading digits nicely*)

fun prefix_len _ [] = 0
  | prefix_len pred (x :: xs) =
      if pred x then 1 + prefix_len pred xs else 0;

fun dest_bin_str tm =
  let
    val rev_digs = HOLogic.bin_of tm handle TERM _ => raise Match
    val (sign, zs) =
      (case rev rev_digs of
        ~1 :: bs => ("-", prefix_len (equal 1) bs)
      | bs => ("", prefix_len (equal 0) bs));
    val i = HOLogic.int_of rev_digs;
    val num = IntInf.toString (IntInf.abs i);
  in
    if i = IntInf.fromInt 0 orelse i = IntInf.fromInt 1 then raise Match
    else sign ^ implode (replicate zs "0") ^ num
  end;

(* translation of integer numeral tokens to and from bitstrings *)

(*additional translations of binary and hex numbers to normal numbers*)
local

(*get A => ord"0" + 10, etc*)
fun remap_hex c =
  let 
    val zero = ord"0"; 
    val a  = ord"a";
    val ca = ord"A";
    val x  = ord c;
  in
    if x >= a then chr (x - a + zero + 10)
    else if x >= ca then chr (x - ca + zero + 10) 
    else c
  end;

fun str_to_int' ("0" :: "x" :: ds) = read_radixint (16, map remap_hex ds) |> #1
  | str_to_int' ("0" :: "b" :: ds) = read_radixint (2, ds) |> #1
  | str_to_int' ds = implode ds |> IntInf.fromString |> valOf; 

in

val str_to_int = str_to_int' o explode;

end;

fun numeral_tr (*"_Numeral"*) [t as Const (str, _)] =
      (Syntax.const "Numeral.number_of" $ (HOLogic.mk_binum (str_to_int str)))
  | numeral_tr (*"_Numeral"*) ts = raise TERM ("numeral_tr", ts);

fun numeral_tr' show_sorts (*"number_of"*) (Type ("fun", [_, T])) (t :: ts) =
      let val t' = Syntax.const "_Numeral" $ Syntax.free (dest_bin_str t) in
        if not (! show_types) andalso can Term.dest_Type T then t'
        else Syntax.const Syntax.constrainC $ t' $ Syntax.term_of_typ show_sorts T
      end
  | numeral_tr' _ (*"number_of"*) T (t :: ts) =
      if T = dummyT then Syntax.const "_Numeral" $ Syntax.free (dest_bin_str t)
      else raise Match
  | numeral_tr' _ (*"number_of"*) _ _ = raise Match;


(* theory setup *)

val setup =
  Theory.add_trfuns ([], [("_Numeral", numeral_tr)], [], []) #>
  Theory.add_trfunsT [("number_of", numeral_tr'), ("Numeral.number_of", numeral_tr')];

end;
